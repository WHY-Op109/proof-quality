"""Rebuild FAST-DISCUSSION.md: user-flagged cases verbatim, then agent suggestions with grouped questions."""
import json,re,difflib
from pathlib import Path
BASE=Path(__file__).resolve().parent.parent
REPO=BASE.parents[2]/'proof-quality'
orig=[json.loads(l) for l in (REPO/'data/mathlibpr/pairs.jsonl').read_text().splitlines()]
fs=[json.loads(l) for l in (BASE/'FAST-SCREENING.jsonl').read_text().splitlines()]
src=(BASE/'fast-screen/archive-initial-pass/FAST-DISCUSSION.round1.md').read_text()
# Split the preserved round-1 file into its per-example sections.
head,*parts=re.split(r'\n(?=## Original example )',src)
sections={int(re.match(r'## Original example (\d+)',p).group(1)):p.rstrip()+'\n' for p in parts}
user=[s for s in fs if (s['discussion'] or {}).get('source')=='user_flagged']
agent=[s for s in fs if (s['discussion'] or {}).get('source') in ('agent_suggestion','agent_cluster')]
def url(s):return s['original_viewer_url'].replace('http://127.0.0.1:8737/','http://127.0.0.1:8740/'+('' if s['decision']=='retain' else s['decision']+'/'))
out=['# Fast-pass discussion cases\n\n2026-10-30. These are discussion records, not new human judgments. Viewer: `python3 tools/screening_view/serve.py` from the fork, then open `/discussion/`. Links below assume port 8740.\n']
out.append(f'\n## Part A — Cases you flagged as difficult ({len(user)})\n\nPreserved from the round-1 file without changing their recorded text. Each row stays as you recorded it: deferred cases remain **unresolved**, and 1381 keeps your no-material-preference verdict while still flagged for the meeting.\n\n**Why these are hard to judge.** In every one of them both scripts encode the same mathematics, and they differ in how much of the argument is explicit:\n- 1574: `simp only [...]`→`simp [...]` inside a grind witness. This is only simp-set visibility.\n- 1617: explicit witness transport→`cat_disch`. The automation is opaque and its search is undocumented for the reader.\n- 1587: split_ifs/rw→`by_cases <;> simp`. There is no mathematical difference, so any quality claim has to rest on readability or maintenance evidence that the code alone does not provide.\n- 1128: a calc split into more steps. It is a small presentation gain whose materiality is unclear.\n- 1381: an explicit finiteness proof→`aesop`. You judged it neutral but kept it as an automation example.\n')
for s in sorted(user,key=lambda s:s['source_line_1based']):
    n=s['source_line_1based']
    sec=sections.get(n)
    if sec:out.append('\n'+sec.replace('## Original example','### Original example',1))
    else:out.append(f"\n### Original example {n}\nYour note: {s['discussion']['why']}\n")
reps=sorted(agent,key=lambda s:-(s['discussion'].get('cluster_size') or 0))
members={}
for s in fs:
    if s.get('cluster'):members.setdefault(s['cluster']['cluster_id'],[]).append(s['source_line_1based'])
out.append(f"\n## Part B: Your question sheet ({len(reps)} questions covering {sum(len(v) for k,v in members.items() if k!='needs_context')} unresolved pairs)\n\nAgents screened every pair twice and adjudicated each disagreement. These are the only open questions left. Each one is asked once, on a representative pair, and your answer would be applied to that cluster only, after you see which rows it changes. A one-word answer is enough: **final / earlier / same / depends**. Open each representative in the viewer under *Hard cases*.\n\n| # | Question | Pairs | Representative |\n| --- | --- | ---: | --- |\n")
for i,s in enumerate(reps,1):
    d=s['discussion'];out.append(f"| {i} | {d['question']} | {d['cluster_size']} | [row {s['source_line_1based']}](http://127.0.0.1:8740/#r{s['source_line_1based']}) |\n")
out.append("\nThe cluster *automation hides routine steps* includes the same kinds of change as your deferred cases 1574, 1617 and 1587. Your answer would **not** be applied to those three automatically.\n")
nc=members.get('needs_context',[])
if nc:out.append(f"\nNot a question: row(s) {', '.join(map(str,sorted(nc)))} cannot be judged from the stored pair: {next(x for x in fs if x.get('cluster') and x['cluster']['cluster_id']=='needs_context')['cluster']['summary']}\n")
for i,s in enumerate(reps,1):
    n=s['source_line_1based'];r=orig[n-1];m=r['metadata'];cid=s['discussion']['cluster_id']
    d=''.join(difflib.unified_diff(r['rejected'].splitlines(True),r['chosen'].splitlines(True),'earlier','final',n=2))
    if len(d)>2500:d=d[:2500]+'\n… (truncated; full bodies in the viewer)\n'
    out.append(f"\n### Q{i}. {cid}: row {n}, {m['declaration_name']}\n{s['discussion']['question']}\n\nAll pairs in this cluster: {', '.join(map(str,sorted(members[cid])))}.\n\n```diff\n{d}```\n")
(BASE/'FAST-DISCUSSION.md').write_text(''.join(out))
print(len(user),len(reps))
