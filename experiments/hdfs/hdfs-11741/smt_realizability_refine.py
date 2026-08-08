#!/usr/bin/env python3
"""Realizability refinement at the SMT layer (T5).

Takes a composed candidate query (`candidate.smt2`) plus the reachability
report the pipeline solved it with (`z3-result.json`), adds refinement
constraints, and re-solves.  The original artifacts are never modified: every
run writes a fresh `<label>.smt2` and `<label>.result.json`.

Two refinement modes exist, and they are not equally useful.

  --block-point   Negate the model point by point:
                    (assert (not (and (= root_i v_i) ...)))
                  This is the naive baseline.  It removes exactly one point
                  from the search space per round, so over unbounded integer
                  roots it cannot converge.  It is implemented so that the
                  non-convergence is a measurement rather than a claim.

  --assume FILE   Inject environment axioms: facts about the environment the
                  program runs in, never facts about what the program
                  computes.  Blocking the *reason* a model is implausible
                  removes a whole region of the space at once.  The axioms
                  live in a data file (see environment-axioms.smt2), each
                  carrying the basis on which it counts as an environment
                  fact.

The hard rule, enforced by review of the axiom file and not by this script:
an axiom may constrain the environment (clock domain, non-negative
lifetimes, epoch anchoring); it may never constrain program causality.
Asserting what the program computes in order to reach a desired answer is
forging a summary, not refining a model.  Axioms that beg the question are
allowed in the file only if marked `@kind control`, and those are never
selected by default -- they exist so that a control experiment can be run
and reported as a control.

Selectors are derived from the engine's own vocabulary, never from
application names.  `clock-read` matches the composer's environment oracle
naming (`environment__<scope>__currentTimeMills_<n>__<hash>`, see
ConcolicSmtComposer, PlaceholderExpression handling); the existential roots
come from the reachability report.

Usage
-----
  smt_realizability_refine.py --smt <candidate.smt2> \\
      --z3-result <z3-result.json> --label baseline
  smt_realizability_refine.py ... --block-point --rounds 3
  smt_realizability_refine.py ... --assume environment-axioms.smt2 \\
      --axioms clock-read-nonnegative,timeline-root-nonnegative
"""

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time

CLOCK_DECL = re.compile(
    r'^\(declare-const (environment__\S*__currentTimeMills_\d+__\S+) Int\)$')
DECL = re.compile(r'^\(declare-const (\S+) (.*)\)$')
ORDER_OPS = {'<', '>', '<=', '>='}


# ---------------------------------------------------------------- s-expr ---

def sexpr_tokens(text):
    """Yield tokens of an SMT-LIB term, honouring strings and |quoting|."""
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c in ' \t\r\n':
            i += 1
        elif c == ';':
            j = text.find('\n', i)
            i = n if j < 0 else j + 1
        elif c in '()':
            yield c
            i += 1
        elif c == '"':
            j = i + 1
            while j < n:
                if text[j] == '"':
                    if j + 1 < n and text[j + 1] == '"':
                        j += 2
                        continue
                    break
                j += 1
            yield text[i:j + 1]
            i = j + 1
        elif c == '|':
            j = text.find('|', i + 1)
            j = n - 1 if j < 0 else j
            yield text[i:j + 1]
            i = j + 1
        else:
            j = i
            while j < n and text[j] not in ' \t\r\n();':
                j += 1
            yield text[i:j]
            i = j


def parse_sexpr(text):
    """Parse a whole assertion line into nested lists of atoms."""
    stack = [[]]
    for tok in sexpr_tokens(text):
        if tok == '(':
            stack.append([])
        elif tok == ')':
            done = stack.pop()
            if not stack:
                raise ValueError('unbalanced ")"')
            stack[-1].append(done)
        else:
            stack[-1].append(tok)
    if len(stack) != 1:
        raise ValueError('unbalanced "("')
    return stack[0]


def walk(node):
    yield node
    if isinstance(node, list):
        for child in node:
            yield from walk(child)


# ----------------------------------------------------------------- model ---

class Query(object):
    """A composed candidate query and the facts a selector needs."""

    def __init__(self, smt_path, report_path):
        self.smt_path = os.path.abspath(smt_path)
        self.report_path = os.path.abspath(report_path)
        with open(self.smt_path, 'r') as handle:
            self.lines = handle.read().splitlines()
        with open(self.report_path, 'r') as handle:
            self.report = json.load(handle)
        self.check_sat_index = self._find_check_sat()
        self.declared = {}
        self.clock_reads = []
        for line in self.lines:
            decl = DECL.match(line)
            if decl:
                self.declared[decl.group(1)] = decl.group(2)
            clock = CLOCK_DECL.match(line)
            if clock:
                self.clock_reads.append(clock.group(1))
        self.roots = self._roots()
        self.witness = self._witness()
        self._timeline_pairs = None

    def _find_check_sat(self):
        for index in range(len(self.lines) - 1, -1, -1):
            if self.lines[index].strip() == '(check-sat)':
                return index
        raise SystemExit('no (check-sat) in %s' % self.smt_path)

    def _roots(self):
        roots = []
        existential = self.report.get('roots', {}).get('existentialInputs', [])
        for entry in existential:
            roots.append({
                'solverTerm': entry['solverTerm'],
                'portId': entry.get('portId'),
                'javaTypeDescriptor': entry.get('javaTypeDescriptor'),
                'regionInstanceId': entry.get('regionInstanceId'),
            })
        return roots

    def _witness(self):
        """Last recorded model point over the existential roots, if any."""
        if 'existentialWitness' in self.report:
            entries = self.report['existentialWitness']
        else:
            entries = []
            for valuation in self.report.get('valuations', []):
                if valuation.get('existentialWitness'):
                    entries = valuation['existentialWitness']
        return [(e['solverTerm'], e['value']) for e in entries
                if e.get('value') is not None]

    def timeline_pairs(self):
        """(root, clock) pairs measured to share an ordering comparison.

        A root that is compared `<`/`>`/`<=`/`>=` against an environment
        clock read denotes a point on the same wall-clock timeline as that
        read.  This is read off the composed query, not assumed.
        """
        if self._timeline_pairs is not None:
            return self._timeline_pairs
        root_names = set(r['solverTerm'] for r in self.roots)
        clock_names = set(self.clock_reads)
        pairs = set()
        for line in self.lines:
            if not line.startswith('(assert'):
                continue
            if not any(name in line for name in root_names):
                continue
            if not any(name in line for name in clock_names):
                continue
            for node in walk(parse_sexpr(line)):
                if not isinstance(node, list) or len(node) != 3:
                    continue
                if node[0] not in ORDER_OPS:
                    continue
                left, right = node[1], node[2]
                if not isinstance(left, str) or not isinstance(right, str):
                    continue
                if left in root_names and right in clock_names:
                    pairs.add((left, right))
                elif right in root_names and left in clock_names:
                    pairs.add((right, left))
        self._timeline_pairs = sorted(pairs)
        return self._timeline_pairs

    def timeline_roots(self):
        seen, out = set(), []
        for root, _clock in self.timeline_pairs():
            if root not in seen:
                seen.add(root)
                out.append(root)
        return out

    def select(self, name, argument):
        if name == 'existential-root':
            terms = []
            for root in self.roots:
                if argument and root.get('javaTypeDescriptor') != argument:
                    continue
                terms.append(root['solverTerm'])
            return [{'term': t} for t in terms]
        if name == 'clock-read':
            return [{'term': t} for t in self.clock_reads]
        if name == 'existential-root-on-clock-timeline':
            return [{'term': t} for t in self.timeline_roots()]
        if name == 'existential-root-clock-pair':
            return [{'root': r, 'clock': c, 'term': r}
                    for r, c in self.timeline_pairs()]
        if name == 'none':
            return [{}]
        raise SystemExit('unknown selector: %s' % name)


# ------------------------------------------------------------ axiom file ---

def parse_axioms(path):
    """Parse the axiom data file into ordered axiom blocks.

    Directives live in comments so that the file stays valid SMT-LIB text:
      ; @axiom <id>          start a block
      ; @kind <environment|control>
      ; @basis <free text>   why this counts as an environment fact
      ; @declare <name> <sort>
      ; @select <selector> [argument]
      ; @emit <template>     rendered once per current selection
    """
    axioms, current = [], None
    with open(path, 'r') as handle:
        for lineno, raw in enumerate(handle, 1):
            line = raw.strip()
            if not line.startswith(';'):
                if line:
                    raise SystemExit(
                        '%s:%d: axiom files carry directives in comments only'
                        % (path, lineno))
                continue
            body = line.lstrip(';').strip()
            if not body.startswith('@'):
                continue
            parts = body[1:].split(None, 1)
            directive = parts[0]
            rest = parts[1].strip() if len(parts) > 1 else ''
            if directive == 'axiom':
                current = {'id': rest, 'kind': 'environment', 'basis': [],
                           'steps': [], 'selector': ('none', None),
                           'line': lineno}
                axioms.append(current)
                continue
            if current is None:
                raise SystemExit('%s:%d: @%s before any @axiom'
                                 % (path, lineno, directive))
            if directive == 'kind':
                current['kind'] = rest
            elif directive == 'basis':
                current['basis'].append(rest)
            elif directive == 'select':
                bits = rest.split(None, 1)
                current['selector'] = (bits[0],
                                       bits[1].strip() if len(bits) > 1
                                       else None)
                current['steps'].append(('select', current['selector']))
            elif directive == 'declare':
                current['steps'].append(('declare', rest))
            elif directive == 'emit':
                current['steps'].append(('emit', rest))
            else:
                raise SystemExit('%s:%d: unknown directive @%s'
                                 % (path, lineno, directive))
    for axiom in axioms:
        if not axiom['id']:
            raise SystemExit('%s: an @axiom block has no id' % path)
        if not axiom['basis']:
            raise SystemExit('%s: axiom %s states no @basis'
                             % (path, axiom['id']))
    return axioms


def render(axiom, query):
    """Render one axiom into (declarations, assertions)."""
    declarations, assertions = [], []
    selector = ('none', None)
    for kind, payload in axiom['steps']:
        if kind == 'select':
            selector = payload
        elif kind == 'declare':
            declarations.append('(declare-const %s)' % payload)
        elif kind == 'emit':
            for binding in query.select(selector[0], selector[1]):
                text = payload
                for key, value in binding.items():
                    text = text.replace('${%s}' % key, value)
                if '${' in text:
                    raise SystemExit(
                        'axiom %s: unbound placeholder in %r (selector %s)'
                        % (axiom['id'], payload, selector[0]))
                assertions.append(text)
    return declarations, assertions


# ------------------------------------------------------------------ z3 -----

def run_z3(binary, path, timeout_ms):
    seconds = max(1, int(round(timeout_ms / 1000.0)))
    started = time.time()
    proc = subprocess.run(
        [binary, '-T:%d' % seconds, path],
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        universal_newlines=True)
    elapsed_ms = int(round((time.time() - started) * 1000))
    text = proc.stdout
    answer = 'unknown'
    for line in text.splitlines():
        token = line.strip()
        if token in ('sat', 'unsat', 'unknown', 'timeout'):
            answer = 'unknown' if token == 'timeout' else token
            break
        if token.startswith('(error'):
            continue
    return answer, elapsed_ms, text


def parse_get_value(text, terms):
    """Pull `((term value) ...)` out of z3 output, tolerating errors."""
    start = text.find('\n((')
    if start < 0:
        return {}
    try:
        parsed = parse_sexpr(text[start:])
    except ValueError:
        return {}
    values = {}
    wanted = set(terms)
    for node in walk(parsed):
        if (isinstance(node, list) and len(node) == 2
                and isinstance(node[0], str) and node[0] in wanted):
            values[node[0]] = flatten(node[1])
    return values


def flatten(node):
    if isinstance(node, str):
        return node
    return '(' + ' '.join(flatten(child) for child in node) + ')'


def sha256(path):
    digest = hashlib.sha256()
    with open(path, 'rb') as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b''):
            digest.update(chunk)
    return digest.hexdigest()


# ------------------------------------------------------------------ main ---

def build(query, blocks, declarations, assertions, observed):
    """Splice refinement text in front of (check-sat) and ask for values."""
    head = list(query.lines[:query.check_sat_index])
    tail = list(query.lines[query.check_sat_index:])
    head.append('')
    head.append('; ---- T5 realizability refinement (added, nothing removed)')
    head.extend(declarations)
    for name, text in blocks:
        head.append('(assert (! %s :named %s))' % (text, name))
    for index, text in enumerate(assertions):
        head.append('(assert (! %s :named t5_axiom_%d))' % (text, index))
    tail.append('(get-value (%s))' % ' '.join(observed))
    return '\n'.join(head + tail) + '\n'


def main(argv=None):
    parser = argparse.ArgumentParser(
        description='T5 realizability refinement over a composed candidate.')
    parser.add_argument('--smt', required=True,
                        help='composed candidate query (candidate.smt2)')
    parser.add_argument('--z3-result', required=True,
                        help='reachability report carrying the roots and '
                             'the model point to refine away')
    parser.add_argument('--assume', action='append', default=[],
                        metavar='FILE',
                        help='environment axiom data file (repeatable)')
    parser.add_argument('--axioms', default=None,
                        help='comma separated axiom ids to apply; default is '
                             'every axiom of kind "environment"')
    parser.add_argument('--block-point', action='store_true',
                        help='negate the recorded model point by point')
    parser.add_argument('--rounds', type=int, default=1,
                        help='with --block-point, keep blocking each newly '
                             'found point this many times (default 1)')
    parser.add_argument('--label', default=None,
                        help='name for the generated artifacts')
    parser.add_argument('--output-dir', default=None,
                        help='default: <candidate dir>/realizability')
    parser.add_argument('--z3', default='z3')
    parser.add_argument('--solver-timeout-ms', type=int, default=180000)
    args = parser.parse_args(argv)

    query = Query(args.smt, args.z3_result)

    selected, axioms = [], []
    for path in args.assume:
        axioms.extend(parse_axioms(path))
    wanted = None
    if args.axioms:
        wanted = [a.strip() for a in args.axioms.split(',') if a.strip()]
        known = set(a['id'] for a in axioms)
        for name in wanted:
            if name not in known:
                raise SystemExit('no axiom %r in %s' % (name, args.assume))
    for axiom in axioms:
        if wanted is None:
            if axiom['kind'] != 'environment':
                continue
        elif axiom['id'] not in wanted:
            continue
        selected.append(axiom)

    declarations, assertions, applied = [], [], []
    for axiom in selected:
        decls, asserts = render(axiom, query)
        declarations.extend(decls)
        assertions.extend(asserts)
        applied.append({'id': axiom['id'], 'kind': axiom['kind'],
                        'basis': axiom['basis'], 'assertionCount':
                        len(asserts), 'assertions': asserts})

    label = args.label
    if label is None:
        parts = []
        if args.block_point:
            parts.append('blockpoint')
        parts.extend(a['id'] for a in selected)
        label = '-'.join(parts) or 'baseline'
    out_dir = args.output_dir or os.path.join(
        os.path.dirname(query.smt_path), 'realizability')
    os.makedirs(out_dir, exist_ok=True)

    root_terms = [r['solverTerm'] for r in query.roots]
    observed = root_terms + query.clock_reads + [
        d.split()[1] for d in declarations]

    blocks, rounds = [], []
    point = query.witness
    total = max(1, args.rounds) if args.block_point else 1
    smt_path = os.path.join(out_dir, label + '.smt2')
    for round_index in range(total):
        if args.block_point:
            if not point:
                rounds.append({'round': round_index + 1,
                               'note': 'no model point available to block'})
                break
            equalities = ' '.join('(= %s %s)' % (term, value)
                                  for term, value in point)
            blocks.append(('t5_block_point_%d' % round_index,
                           '(not (and %s))' % equalities))
        text = build(query, blocks, declarations, assertions, observed)
        with open(smt_path, 'w') as handle:
            handle.write(text)
        answer, elapsed_ms, output = run_z3(
            args.z3, smt_path, args.solver_timeout_ms)
        values = parse_get_value(output, observed) if answer == 'sat' else {}
        rounds.append({
            'round': round_index + 1,
            'blockedPoints': len(blocks),
            'answer': answer,
            'elapsedMs': elapsed_ms,
            'values': values,
        })
        print('[%s] round %d blocked=%d -> %s in %d ms'
              % (label, round_index + 1, len(blocks), answer, elapsed_ms),
              file=sys.stderr)
        if answer != 'sat':
            break
        point = [(t, values[t]) for t in root_terms if t in values]

    final = rounds[-1]
    result = {
        'schemaVersion': 1,
        'kind': 'T5_REALIZABILITY_REFINEMENT',
        'label': label,
        'input': {
            'smt': query.smt_path,
            'smtSha256': sha256(query.smt_path),
            'z3Result': query.report_path,
        },
        'refinement': {
            'blockPoint': bool(args.block_point),
            'rounds': args.rounds if args.block_point else 1,
            'axiomFiles': [os.path.abspath(p) for p in args.assume],
            'axiomsApplied': applied,
            'blockedPointAssertions': [text for _name, text in blocks],
        },
        'model': {
            'existentialRoots': query.roots,
            'clockReads': query.clock_reads,
            'timelinePairs': [{'root': r, 'clock': c}
                              for r, c in query.timeline_pairs()],
        },
        'answer': final.get('answer', 'unknown'),
        'elapsedMs': final.get('elapsedMs'),
        'rounds': rounds,
        'existentialWitness': [
            {'solverTerm': term, 'value': final.get('values', {})[term]}
            for term in root_terms if term in final.get('values', {})],
        'refinedSmtArtifact': {'path': smt_path, 'sha256': sha256(smt_path)},
        'solver': {'binary': args.z3,
                   'timeoutMs': args.solver_timeout_ms},
    }
    result_path = os.path.join(out_dir, label + '.result.json')
    with open(result_path, 'w') as handle:
        json.dump(result, handle, indent=2)
        handle.write('\n')
    print(result_path)
    return 0


if __name__ == '__main__':
    sys.exit(main())
