"""Stage A: score blind calibration (A1), compare first/second screens (A2), build adjudication packets (A3).
python3 fast-screen/stage_a.py compare   # after A1/A2 outputs exist
python3 fast-screen/stage_a.py report    # after A3 adjudication outputs exist
"""
import sys,json,difflib,random
from pathlib import Path
from collections import Counter
BASE=Path(__file__).resolve().parent.parent;ST=BASE/'fast-screen/stage-a'
REPO=BASE.parents[2]/'proof-quality'
o=[json.loads(l) for l in (REPO/'data/mathlibpr/pairs.jsonl').read_text().splitlines()]
fs={s['source_line_1based']:s for s in map(json.loads,(BASE/'FAST-SCREENING.jsonl').read_text().splitlines())}
def load(pattern):
 d={}
 for f in sorted(ST.glob(pattern)):d.update(json.loads(f.read_text()))
 return d
def first(n):
 # First-screen verdict before any stage-A layer; human rows never enter stage A.
 s=fs[n];return s.get('first_screen') or {'decision':s['decision'],'direction':s['preference_direction'],'reason':s['reason'],'assessor':s['assessor']}
def same(a,b):return a['decision']==b['decision'] and a['direction']==b['direction']
def a1():
 key=json.loads((ST/'a1-key.json').read_text());out=load('a1-out-*.json');hd={}
 for l in (BASE/'human-decisions.jsonl').read_text().splitlines():d=json.loads(l);hd[d['source_line_1based']]=d
 rows=[]
 for lab,n in key['label_to_row'].items():
  d=hd[n];h='unresolved' if d.get('decision_status')=='deferred_pending_meeting' else d['structured_interpretation']['direction']
  hdec={'final_better':'retain','earlier_better':'retain','no_material_preference':'exclude','unresolved':'unresolved'}[h]
  a=out.get(lab,{});ad=a.get('decision')
  kind='match' if ad==hdec and (hdec!='retain' or a.get('direction')==h) else 'conservative' if ad=='unresolved' else 'over_cautious_vs_deferral' if hdec=='unresolved' and ad=='exclude' else 'error'
  rows.append({'row':n,'label':lab,'human':h,'agent_decision':ad,'agent_direction':a.get('direction'),'agent_reason':a.get('reason'),'outcome':kind})
 return rows
def compare():
 sel=json.loads((ST/'a2-selection.json').read_text());second=load('a2-out-*.json')
 strata={int(n):[k for k,v in sel['strata'].items() if int(n) in v] for n in second}
 res=[];dis=[]
 for k,v in second.items():
  n=int(k);f=first(n);agree=same(f,v)
  res.append({'row':n,'strata':strata[n],'first':f,'second':v,'agree':agree})
  if not agree:dis.append(n)
 (ST/'a2-comparison.jsonl').write_text(''.join(json.dumps(r,ensure_ascii=False)+'\n' for r in sorted(res,key=lambda r:r['row'])))
 # Adjudication packets: screens shown as X/Y in random order so the adjudicator cannot tell which came first.
 random.seed(11);blocks=[]
 for n in sorted(dis):
  f=first(n);s=second[str(n)];pair=[('X',f),('Y',s)] if random.random()<.5 else [('X',s),('Y',f)]
  r=o[n-1];d=''.join(difflib.unified_diff(r['rejected'].splitlines(True),r['chosen'].splitlines(True),'earlier','final',n=2))
  if len(d)>6000:d=d[:6000]+f'\n...[truncated; full bodies at line {n} of pairs.jsonl]\n'
  views=''.join(f"Screen {lab}: {v['decision']} / {v['direction']} — {v['reason']}\n" for lab,v in pair)
  blocks.append(f"=== ROW {n} | {r['metadata']['declaration_name']}\n{views}{d}\n")
 k=max(1,-(-len(blocks)//60))
 for i in range(k):(ST/f'a3-packet-{i}.txt').write_text(''.join(blocks[i::k]))
 a1rows=a1();(ST/'a1-results.jsonl').write_text(''.join(json.dumps(r,ensure_ascii=False)+'\n' for r in a1rows))
 print('A1',Counter(r['outcome'] for r in a1rows))
 for r in a1rows:
  if r['outcome']!='match':print(' ',r['row'],r['human'],'->',r['agent_decision'],r['agent_direction'],'|',(r['agent_reason'] or '')[:140])
 print('A2 rows',len(res),'agree',sum(r['agree'] for r in res))
 for s in sel['strata']:
  rs=[r for r in res if s in r['strata']];print(' ',s,len(rs),'agree',sum(r['agree'] for r in rs))
 print('A2 transition',Counter((r['first']['decision'],r['second']['decision']) for r in res if not r['agree']))
 print('A3 packets',k,'disagreements',len(dis))

def finalize():
 """Agreeing screens keep their verdict; disagreements take the adjudicator's. Writes final.json and the A4 cluster input."""
 comp=[json.loads(l) for l in (ST/'a2-comparison.jsonl').read_text().splitlines()];adj=load('a3-out-*.json');final={}
 for c in comp:
  n=c['row'];sec={k:c['second'].get(k) for k in ('decision','direction','reason')}
  if c['agree']:v=c['first'];final[str(n)]={'decision':v['decision'],'direction':v['direction'],'category':fs[n]['quality_classification'] if fs[n]['decision']==v['decision'] else c['second']['category'],'reason':v['reason'],'outcome':'two_screens_agree','second_screen':sec,'strata':c['strata']}
  else:
   a=adj[str(n)];final[str(n)]={'decision':a['decision'],'direction':a['direction'],'category':a['category'],'reason':a['reason'],'outcome':'adjudicated','adjudicator_chose':a.get('chose'),'open_question':a.get('open_question'),'second_screen':sec,'strata':c['strata']}
 (ST/'final.json').write_text(json.dumps(final,ensure_ascii=False,indent=1))
 un=[]
 for n,s in fs.items():
  if s['human_decision_id']:continue
  f=final.get(str(n));dec=f['decision'] if f else s['decision']
  if dec!='unresolved':continue
  q=(f or {}).get('open_question') or ((s.get('discussion') or {}).get('question'))
  un.append({'row':n,'decl':s['source_key'].get('declaration_name') or n,'reason':f['reason'] if f else s['reason'],'second_screen_reason':(f or {}).get('second_screen',{}).get('reason'),'open_question':q,'usability':s['usability_flags']})
 (ST/'a4-input.json').write_text(json.dumps(un,ensure_ascii=False,indent=1))
 print('final',Counter(v['outcome'] for v in final.values()),'unresolved for clustering',len(un))
 print('decisions after stage A',Counter((final.get(str(n)) or {'decision':s['decision']})['decision'] for n,s in fs.items()))
def clusters():
 c=json.loads((ST/'a4-out.json').read_text())['clusters'];out={};seen=Counter()
 for cl in c:
  for m in cl['members']:
   seen[m]+=1;out[str(m)]={'cluster_id':cl['cluster_id'],'question':cl.get('question'),'summary':cl['summary'],'size':len(cl['members']),'representative_row':cl.get('representative') if cl['cluster_id']!='needs_context' else None,'representative':m==cl.get('representative') and cl['cluster_id']!='needs_context'}
 inp={r['row'] for r in json.loads((ST/'a4-input.json').read_text())}
 assert set(map(int,out))==inp and max(seen.values())==1,(inp-set(map(int,out)),[k for k,v in seen.items() if v>1])
 (ST/'clusters.json').write_text(json.dumps(out,ensure_ascii=False,indent=1));print(len(c),'clusters',len(out),'rows')
if __name__=='__main__':
 {'compare':compare,'finalize':finalize,'clusters':clusters}[sys.argv[1]]()
