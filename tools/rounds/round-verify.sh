#!/usr/bin/env bash
# round-verify.sh <round> [case...]: per finished case, how EXPLORE ended, the claim, z3 on the exported candidate.smt2,
# the blocking gaps, whether a SAT moved roots, and the formula's leaf symbols (roots, reads, handoffs: every declared
# constant but the formula's own selectors and named identities); an UNSAT over none (NO-SYMBOL) decided nothing that
# moves, a scope hole to read before it counts. No case: every finished case of the round.
out=${GC_OUT:-/bigtemp/vnr3ne/gc-out/hdfs-study}; round=$1; shift
want=" $* "
while IFS=$'\t' read -r n c; do
  [[ $# -eq 0 || "$want" == *" $c "* ]] || continue
  d=$out/accept-$round-$n; s=$d/summary.tsv
  [[ -f $s ]] && (( $(wc -l < "$s") >= 2 )) || continue
  f=$d/out/$c/schedule/final
  stop=$(grep -ho 'exploration stopped ([A-Z_]*)' "$d/logs/$c.log" 2>/dev/null | head -1 | sed 's/exploration stopped //')
  claim=$(tail -1 "$s" | cut -f4); secs=$(tail -1 "$s" | cut -f3)
  z=$( [[ -f $f/candidate.smt2 ]] && timeout 300 ~/.local/bin/z3 -smt2 "$f/candidate.smt2" 2>/dev/null | head -1)
  extra=$(python3 - "$f" <<'PY'
import json,sys,os
f=sys.argv[1]; out=[]
try:
    g=json.load(open(os.path.join(f,'gaps.json')))
    b=[r for r in g.get('gaps',[]) if r.get('class')=='BLOCKING']
    if b: out.append('BLOCKING:'+','.join(sorted(set(r.get('code','?') for r in b))))
except Exception: pass
def find(o,k):
    if isinstance(o,dict):
        if k in o: return o[k]
        for v in o.values():
            r=find(v,k)
            if r is not None: return r
    if isinstance(o,list):
        for v in o:
            r=find(v,k)
            if r is not None: return r
try:
    c=json.load(open(os.path.join(f,'claim.json')))
    mr=find(c,'movedRoots') or []; pd=find(c,'polarityDecides')
    if mr or pd is not None: out.append(f'moved={len(mr)} polarityDecides={pd}')
except Exception: pass
try:
    import re
    names=re.findall(r'\(declare-const (\|[^|]*\||\S+)', open(os.path.join(f,'candidate.smt2')).read())
    own=re.compile(r'^\|?(path_selector|writer_arm|message_arm|state_arm|observed_arm|decided|wchoice|identity__|nullRef)')
    leaves=sum(1 for n in names if not own.match(n))
    out.append(f'leaves={leaves}' + (' NO-SYMBOL' if leaves == 0 else ''))
except Exception: pass
try:
    cf=json.load(open(os.path.join(f,'confirm.json'))); out.append('confirmed' if cf.get('confirmed') else ('refutes' if cf.get('refutes') else 'confirm?'))
except Exception: pass
print(' '.join(out))
PY
)
  printf "%-24s %-15s %6ss  end=%-24s z3=%-6s %s\n" "$c" "$claim" "$secs" "${stop:--}" "${z:--}" "$extra"
done < "$out/sweep-$round-cases.tsv"
