#!/usr/bin/env python3
"""cone.py <case> <case-dir> <work-dir>

THE CAUSAL CONE of the claim's witness path, read off the formula the composer
published (schedule/final/candidate.smt2).  It checks the composition; it is
not a second one.

The fatal condition of anchor path p is the assert path_fatal__i, stated as
(=> sel_p ...).  Every declared constant it names -- define-funs expanded, let
and parameter names bound -- is something the fatal on p depends on.  A
boundary variable v_H among them is bound by the message families asserted
under the same selector: each arm states v_H = e_q together with the producer
path's own condition, so the constants of the arm are causes of v_H, and the
cone is that closure.  This is the paper's causality, in the formula: values
cross a thread or process boundary as the producer's expression, and the
composer merges the producers one arm each.

Two facts are published for report.py, which gates on both:

  moved      -- every root the witness moved, and whether it is in the cone of
                the path the claim selected.  A mechanism whose root the fatal
                does not depend on is a mechanism the formula cannot carry.
  unbound    -- boundary variables a fatal condition the verdict rests on
                names that no family binds, and those an arm the witness chose
                holds FREE or HELD (concrete[] rows naming the arm).  A v_H no
                family binds is a broken causal chain, whatever COMPOSE stated
                of it (concrete[]: FREE, or held at its recorded value because
                no row states its producer): a value the engine invented or
                held, not one a producer made.  A SAT is judged on the path it
                claims, an UNSAT on every path it rests on (PIPELINE §8, the
                claim): a SAT's other paths' unbound variables are reported in
                unboundOffWitness, never hidden, and gate nothing.  COMPOSE
                names the same set (compose.Cone, the claim's openChain).
                A store content leaf a producer refused by rule settles is
                no open link, listed by how: constantByRefusedProducer,
                exportedByRefusedProducer, boundedByTick (concrete[] kinds
                CONSTANT, EXPORTED, BOUNDED).

A root is named by its rootId in result.json and by its symbol in the
formula; the session rows (roots.jsonl) state both.  Writes <work>/cone.json.
"""
import glob
import json
import os
import re
import sys

sys.setrecursionlimit(100000)


def load(path):
    with open(path) as handle:
        return json.load(handle)


def forms(text):
    """The top-level s-expressions of an SMT-LIB file, as nested lists."""
    out, stack, token = [], [], []
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        if ch == ';':
            j = text.find('\n', i)
            i = n if j < 0 else j
            continue
        if ch == '|':
            j = text.index('|', i + 1)
            token.append(text[i:j + 1])
            i = j + 1
            continue
        if ch == '(' or ch == ')' or ch.isspace():
            if token:
                stack[-1].append(''.join(token))
                token = []
            if ch == '(':
                stack.append([])
            elif ch == ')':
                done = stack.pop()
                (stack[-1] if stack else out).append(done)
        else:
            token.append(ch)
        i += 1
    return out


class Formula:
    def __init__(self, text):
        self.consts, self.defs, self.asserts = set(), {}, []
        for form in forms(text):
            head = form[0] if form else ''
            if head == 'declare-const' or (head == 'declare-fun'
                                           and form[2] == []):
                self.consts.add(form[1])
            elif head == 'define-fun':
                self.defs[form[1]] = ({p[0] for p in form[2]}, form[4])
            elif head == 'assert':
                body, name = form[1], ''
                if isinstance(body, list) and body and body[0] == '!':
                    name = body[body.index(':named') + 1] \
                        if ':named' in body else ''
                    body = body[1]
                self.asserts.append((name, body))
        self._memo = {}

    def names(self, expr, bound=frozenset()):
        """The declared constants an expression depends on."""
        found, pending = set(), [(expr, bound)]
        while pending:
            e, scope = pending.pop()
            if isinstance(e, str):
                if e in scope:
                    continue
                if e in self.consts:
                    found.add(e)
                elif e in self.defs:
                    found |= self._defined(e)
                continue
            if not e:
                continue
            if e[0] == 'let':
                inner = set(scope)
                for binding in e[1]:
                    pending.append((binding[1], scope))
                    inner.add(binding[0])
                pending.append((e[2], frozenset(inner)))
            elif e[0] in ('forall', 'exists'):
                pending.append((e[2], scope | {b[0] for b in e[1]}))
            else:
                pending.extend((x, scope) for x in e)
        return found

    def _defined(self, name):
        if name not in self._memo:
            self._memo[name] = set()
            params, body = self.defs[name]
            self._memo[name] = self.names(body, frozenset(params))
        return self._memo[name]


def selector_of(body):
    if (isinstance(body, list) and len(body) == 3 and body[0] == '=>'
            and isinstance(body[1], str)
            and body[1].startswith('path_selector__')):
        return body[1]
    return None


def is_boundary(name):
    return '_field_HOFF.' in name


def main():
    case_id, case_dir, work = sys.argv[1:4]
    final = os.path.join(case_dir, 'schedule', 'final')
    out = {'case': case_id, 'moved': {}, 'unbound': [], 'selector': ''}
    result = load(os.path.join(final, 'result.json'))
    manifest = load(os.path.join(final, 'candidate_composition_manifest.json'))
    formula = Formula(open(os.path.join(final, 'candidate.smt2')).read())

    fatal, families = {}, {}
    for name, body in formula.asserts:
        selector = selector_of(body)
        if not selector:
            continue
        if name.startswith('path_fatal'):
            fatal[selector] = formula.names(body[2])
        elif name.startswith('message_family'):
            families.setdefault(selector, []).append(formula.names(body[2]))

    ordinal = result.get('valuationOrdinal')
    chosen = next((v for v in result.get('valuations') or []
                   if v.get('ordinal') == ordinal), {})
    path = next((p for p in manifest.get('paths') or []
                 if p.get('pathId') == chosen.get('selectedPathId')), {})
    selector = path.get('selector', '')
    out['selector'] = selector
    out['selectedPathId'] = chosen.get('selectedPathId', '')
    # A SAT stands on its witness's path; an UNSAT on every path.
    sat = result.get('claim') == 'SAT_CANDIDATE' and bool(selector)
    out['unboundOffWitness'] = []
    # A store content leaf a producer the closure refuses by rule settles
    # (compose.Composer#refusedByRule, SmtLowering#settled): concrete[] kind
    # CONSTANT (its export a constant), EXPORTED (bound by its export) or
    # BOUNDED (held past the daemon tick bound): named, and no open link.
    path_of = {p.get('selector', ''): p.get('pathId', '')
               for p in manifest.get('paths') or []}
    named = {'CONSTANT': 'constantByRefusedProducer',
             'EXPORTED': 'exportedByRefusedProducer',
             'BOUNDED': 'boundedByTick'}
    settled, by_kind = {}, {kind: set() for kind in named}
    for row in result.get('concrete') or []:
        if row.get('kind') in named:
            settled.setdefault(row.get('pathId', ''), set()).add(
                row.get('subject', ''))
            by_kind[row['kind']].add(row.get('subject', ''))
    for kind, key in named.items():
        out[key] = sorted(by_kind[kind])
    for each, own in sorted(fatal.items()):
        bound = set()
        for family in families.get(each, []):
            bound |= family
        for subject in settled.get(path_of.get(each, ''), set()):
            bound |= {subject, '|' + subject + '|'}
        open_links = sorted(c for c in own if is_boundary(c) and c not in bound)
        if sat and each != selector:
            out['unboundOffWitness'] += open_links
        else:
            out['unbound'] += open_links
    # A handoff an arm the witness chose holds FREE or HELD (concrete[], its
    # "arm") is no family's binding either: the family states it, but as a
    # value no producer made, so the chain breaks there as it does at a
    # fatal condition's unbound v_H.
    arms = {arm.get('selector') for arm in chosen.get('selectedArms') or []}
    out['unbound'] += sorted(
        row.get('subject', '') for row in result.get('concrete') or []
        if row.get('kind') in ('HELD', 'FREE') and row.get('arm') in arms
        and row.get('pathId') == out['selectedPathId']
        and is_boundary(row.get('subject', '')))
    cone = set(fatal.get(selector, set()))
    grew = True
    while grew:
        grew = False
        for family in families.get(selector, []):
            if family & cone and not family <= cone:
                cone |= family
                grew = True

    symbols = {}
    rows = glob.glob(os.path.join(case_dir, 'schedule', '**', 'sessions',
                                  '*', 'roots.jsonl'), recursive=True)
    for rows_path in rows:
        for line in open(rows_path):
            if line.strip():
                row = json.loads(line)
                symbols.setdefault(row.get('rootId', ''), set()).add(
                    row.get('symbol', ''))
    for moved in result.get('movedRoots') or {}:
        named = {moved} if moved in formula.consts else symbols.get(moved, set())
        out['moved'][moved] = bool(named & cone)
    out['coneRoots'] = sorted(c for c in cone
                              if re.search(r'_field_(REGION|SRC)\.', c))
    with open(os.path.join(work, 'cone.json'), 'w') as handle:
        json.dump(out, handle, indent=1)
    print('%s: selected %s, moved roots in cone %s, unbound boundary '
          'variables %d' % (case_id, selector or '-',
                            json.dumps(out['moved']), len(out['unbound'])))


if __name__ == '__main__':
    main()
