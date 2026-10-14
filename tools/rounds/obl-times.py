#!/usr/bin/env python3
"""obl-times.py <case schedule dir>: per obligation verdict, queue wait and run time (start = stderr.log, end = result),
and how many were asked again in a solver JVM of their own (alone-host.txt: an ALONE start; hard-host.txt: the hard lane)."""
import os,glob,json,collections,sys
it=os.path.join(sys.argv[1],'iteration-0000')
rows=[]
for d in glob.glob(os.path.join(it,'obligations-*/*/')):
    r=os.path.join(d,'obligation_result.jsonl'); e=os.path.join(d,'stderr.log'); p=os.path.join(d,'execution_task_plan.jsonl')
    if not os.path.exists(r) or not os.path.exists(e): continue
    try: res=json.loads(open(r).readline())
    except Exception: continue
    v=res.get('verdict'); s=os.stat(e).st_mtime if os.path.getsize(e)==0 else os.stat(e).st_ctime
    q=os.stat(p).st_mtime if os.path.exists(p) else s
    rows.append((q,s,os.stat(r).st_mtime,v,res.get('detail',''),
                 os.path.exists(os.path.join(d,'alone-host.txt')),os.path.exists(os.path.join(d,'hard-host.txt'))))
if not rows: sys.exit('no obligations')
t0=min(r[0] for r in rows); t1=max(r[2] for r in rows)
print('%d obligations over %.0f min'%(len(rows),(t1-t0)/60))
byv=collections.defaultdict(list)
for q,s,e,v,*_ in rows: byv[v].append((e-s,s-q))
for v,l in sorted(byv.items()):
    run=sorted(x for x,_ in l); wait=sorted(y for _,y in l)
    print('%-13s %4d run med/p90/max %5.0f %5.0f %5.0f s  sum %4.0f min | wait med/max %5.0f %5.0f s'%(v,len(l),run[len(run)//2],run[int(len(run)*.9)],run[-1],sum(run)/60,wait[len(wait)//2],wait[-1]))
ev=[]
for q,s,e,*_ in rows: ev+=[(s,1),(e,-1)]
ev.sort(); cur=0; hist=collections.Counter(); last=ev[0][0]
for t,dd in ev: hist[cur]+=t-last; last=t; cur+=dd
print('running at once (min):',{k:round(v/60) for k,v in sorted(hist.items()) if v>60})
det=collections.Counter()
print('asked again in a solver JVM of their own: %d ALONE, %d HARD'%(sum(1 for r in rows if r[5]),sum(1 for r in rows if r[6])))
for *_,v,dt,_,_ in rows:
    if v!='ADMITTED': det[(v,dt.split(':')[0][:60] if dt else '')]+=1
for k,c in det.most_common(8): print(c,k)
