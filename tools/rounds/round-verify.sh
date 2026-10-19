#!/usr/bin/env bash
# shellcheck source=../lib/gc-env.sh
source "$(dirname "${BASH_SOURCE[0]}")/../lib/gc-env.sh"
# shellcheck source=../lib/z3-race.sh
source "$(dirname "${BASH_SOURCE[0]}")/../lib/z3-race.sh"
out=${GC_OUT}; round=$1; shift
want=" $* "; cases=0; bounded=0; unbound=0; held=0
while IFS=$'\t' read -r n c; do
  [[ $# -eq 0 || "$want" == *" $c "* ]] || continue
  d=$out/accept-$round-$n; s=$d/summary.tsv
  [[ -f $s ]] && (( $(wc -l < "$s") >= 2 )) || continue
  f=$d/out/$c/schedule/final
  stop=$(grep -ho 'exploration stopped ([A-Z_]*)' "$d/logs/$c.log" 2>/dev/null | head -1 | sed 's/exploration stopped //')
  claim=$(tail -1 "$s" | cut -f4); secs=$(tail -1 "$s" | cut -f3)
  z=$( [[ -f $f/candidate.smt2 ]] && z3_race "$f/candidate.smt2" 300 | head -1)
  extra=$(python3 - "$f" "$d/report/$c" <<'PY'
import json,sys,os
f=sys.argv[1]; out=[]
try:
    b=json.load(open(os.path.join(f,'result.json'))).get('bounded')
    if b: out.append('BOUNDED:'+','.join(b['by']))
except Exception: pass
try:
    u=set(json.load(open(os.path.join(sys.argv[2],'cone.json'))).get('unbound') or [])
    if u: out.append(f'UNBOUND:{len(u)}')
except Exception: pass
try:
    g=json.load(open(os.path.join(f,'gaps.json')))
    b=[r for r in g.get('gaps',[]) if r.get('class')=='BLOCKING']
    if b: out.append('BLOCKING:'+','.join(sorted(set(r.get('code','?') for r in b))))
    h={r.get('detail') for r in g.get('gaps',[])+g.get('telemetryGaps',[])
       if 'whose arm states nothing' in (r.get('detail') or '')}
    if h: out.append(f'HOLD:{len(h)}')
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
  cases=$((cases + 1)); [[ $extra != BOUNDED:* ]] || bounded=$((bounded + 1))
  [[ $extra != *UNBOUND:* ]] || unbound=$((unbound + 1))
  [[ $extra != *HOLD:* ]] || held=$((held + 1))
done < <(round_runs "$round")
echo "# $round: $cases case(s), $bounded BOUNDED, $unbound UNBOUND, $held HOLD"
