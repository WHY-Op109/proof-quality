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
answers=[json.loads(l) for l in (BASE/'fast-screen/human-cluster-answers.jsonl').read_text().splitlines()]
reps=sorted(agent,key=lambda s:-(s['discussion'].get('cluster_size') or 0))
def diff_of(n,limit=2500):
    r=orig[n-1];d=''.join(difflib.unified_diff(r['rejected'].splitlines(True),r['chosen'].splitlines(True),'earlier','final',n=2))
    return d[:limit]+'\n… (truncated; full bodies in the viewer)\n' if len(d)>limit else d
out.append("\n## Part B: Your answers to the question sheet\n\nYour answers are recorded verbatim in `fast-screen/human-cluster-answers.jsonl`, kept separate from your per-pair verdicts. Each answer applies only to its own cluster.\n\n| Q | Cluster | Pairs | Your answer | Effect |\n| --- | --- | ---: | --- | --- |\n")
for a in answers:
    it=a['interpretation']
    eff=('**Pending your confirmation**: would mark the pairs *no meaningful difference*' if a['application_status']=='pending_user_confirmation' else 'Applied' if a['application_status']=='confirmed' else 'Kept unresolved')
    if it['discussion_topic']:eff+=f"; listed for discussion under *{it['discussion_topic']}*"
    out.append(f"| {a['question_id']} | {a['cluster_id']} ([example row {a['representative_row']}](http://127.0.0.1:8740/#r{a['representative_row']})) | {len(a['member_rows'])} | “{a['user_answer_verbatim']}” | {eff} |\n")
if reps:
    out.append("\n**Still awaiting your answer** (viewer tab *Awaiting your answer*):\n\n")
    for s in reps:
        d=s['discussion'];out.append(f"- Row [{s['source_line_1based']}](http://127.0.0.1:8740/#r{s['source_line_1based']}) ({d['cluster_size']} pair): {d['question']}\n")
nc=sorted(x['source_line_1based'] for x in fs if x.get('cluster') and x['cluster']['cluster_id']=='needs_context' and x['decision']=='unresolved')
if nc:out.append(f"\nNot a question: row(s) {', '.join(map(str,nc))} cannot be judged from the stored pair (the argument moved into a helper lemma that the pair does not contain).\n")
topics={}
for x in fs:
    if x.get('meeting'):topics.setdefault(x['meeting']['topic'],[]).append(x)
notes={'Automated tactics: Mathlib convention for grind':"""**Online check (2026-10-30).** I found no official Mathlib style rule on when to prefer `grind` over `simp`, other automation or explicit steps.
- The closest discussion is an informal Zulip thread on `@[grind]` *annotations*, not on using `grind` to close goals. It suggests passing one-off lemmas explicitly (`grind [lemma]`) instead of adding global annotations: [Zulip: Good practices for grind annotation](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Good.20practices.20for.20grind.20annotation.html).
- The Lean reference documents how `grind` works (E-matching, congruence closure, case splits), but it gives no style guidance: [Lean reference: the grind tactic](https://lean-lang.org/doc/reference/latest/The--grind--tactic/Bigger-Examples/).
- A 2025 Mathlib tooling talk still lists `grind` as automation that is "in progress": [LeanTogether 2025 slides](https://scanner-eg.ipv4.math.uni-bonn.de/people/rothgang/slides_LeanTogether2025_mathlib_tooling.pdf).
- The data contain one concrete reason a revision moved *away* from `grind`. In row [740](http://127.0.0.1:8740/#r740), the final proof's comment cites heartbeat variance, so the motivation was performance stability, not readability.

**Question for the meeting.** Does current Mathlib review practice treat `grind` as preferred, neutral or discouraged for closing goals? The Mathlib style guide and the #mathlib4 Zulip stream are where to confirm this.""",
'Automated tactics':"Includes your earlier meeting cases 1381 (`aesop`), 1574 (simp set inside `grind`), 1587 (`by_cases <;> simp`) and 1617 (`cat_disch`). Q1 covers routine steps folded into automation, and Q3 covers automation that hides the main step.",
'Convention: helper-lemma call vs direct proof':"You judged these to be a convention change with no difference (pending confirmation), but still worth mentioning at the meeting.",
'Mathematical taste: different valid routes':"Your note: the preference depends on the mathematician's taste.",
'Presentation detail: calc granularity':"Your earlier deferral: a small presentation gain, but no clear meaningful difference."}
out.append("\n## Part C: Meeting agenda by topic\n\nThis matches the viewer tab *For discussion*, where you can filter by topic.\n")
for tp in sorted(topics,key=lambda t:-len(topics[t])):
    xs=sorted(topics[tp],key=lambda x:x['source_line_1based']);ex=[x for x in xs if x['meeting'].get('example_row')==x['source_line_1based']]
    out.append(f"\n### {tp} ({len(xs)} pair{"s" if len(xs)!=1 else ""})\n\n{notes.get(tp,'')}\n\nRows: {', '.join(f'[{x['source_line_1based']}](http://127.0.0.1:8740/#r{x['source_line_1based']})' for x in xs)}.\n")
    for x in ex:
        n=x['source_line_1based'];out.append(f"\nExample, row {n} `{orig[n-1]['metadata']['declaration_name']}` ({x['meeting']['question_id']}):\n\n```diff\n{diff_of(n,1800)}```\n")
(BASE/'FAST-DISCUSSION.md').write_text(''.join(out))
print(len(user),len(reps),{k:len(v) for k,v in topics.items()})
