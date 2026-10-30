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
agent=[s for s in fs if (s['discussion'] or {}).get('source')=='agent_suggestion']
def url(s):return s['original_viewer_url'].replace('http://127.0.0.1:8737/','http://127.0.0.1:8740/'+('' if s['decision']=='retain' else s['decision']+'/'))
out=['# Fast-pass discussion cases\n\n2026-10-30. These are discussion records, not new human judgments. Viewer: `python3 tools/screening_view/serve.py` from the fork, then open `/discussion/`. Links below assume port 8740.\n']
out.append(f'\n## Part A — Cases you flagged as difficult ({len(user)})\n\nPreserved from the round-1 file without changing their recorded text. Each row stays as you recorded it: deferred cases remain **unresolved**, and 1381 keeps your no-material-preference verdict while still flagged for the meeting.\n\n**Why these are hard to judge.** In every one of them both scripts encode the same mathematics, and they differ in how much of the argument is explicit:\n- 1574: `simp only [...]`→`simp [...]` inside a grind witness. This is only simp-set visibility.\n- 1617: explicit witness transport→`cat_disch`. The automation is opaque and its search is undocumented for the reader.\n- 1587: split_ifs/rw→`by_cases <;> simp`. There is no mathematical difference, so any quality claim has to rest on readability or maintenance evidence that the code alone does not provide.\n- 1128: a calc split into more steps. It is a small presentation gain whose materiality is unclear.\n- 1381: an explicit finiteness proof→`aesop`. You judged it neutral but kept it as an automation example.\n')
for s in sorted(user,key=lambda s:s['source_line_1based']):
    n=s['source_line_1based']
    sec=sections.get(n)
    if sec:out.append('\n'+sec.replace('## Original example','### Original example',1))
    else:out.append(f"\n### Original example {n}\nYour note: {s['discussion']['why']}\n")
old_agent=[n for n in sections if n not in {s['source_line_1based'] for s in user}]
out.append(f'\n## Part B — Agent suggestions (not flagged by you; {len(agent)})\n\nThe agents decided routine cases themselves. The cases below are ones where an agent judged the quality direction genuinely ambiguous and a decision from you would settle a whole class of cases. All of them remain **unresolved**. They are distinct from rows that were never individually examined (there are none after round 2; see FAST-SCREENING.md).\n')
qs={}
for s in agent:
    q=(s['discussion'] or {}).get('question') or 'Earlier Codex pass example; no specific question recorded.'
    qs.setdefault(q,[]).append(s['source_line_1based'])
out.append('\n### Grouped questions for you\n')
groups={'Automation versus explicit proof':[],'Reuse direction / dependency reversal':[],'Other':[]}
for q,rows in qs.items():
    g='Automation versus explicit proof' if re.search(r'grind|simp|aesop|automat|cat_disch|linear_combination|explicit',q,re.I) else 'Reuse direction / dependency reversal' if re.search(r'reuse|lemma|sibling|library',q,re.I) else 'Other'
    groups[g].append((rows,q))
for g,items in groups.items():
    if not items:continue
    out.append(f'\n**{g}**\n')
    for rows,q in items:out.append(f"- Rows {', '.join(map(str,sorted(rows)))}: {q}\n")
out.append('\nA single answer to the first group would also calibrate the many round-2 rows marked unresolved for automation reasons. Those rows are not listed here individually; filter `FAST-SCREENING.jsonl` with `decision=unresolved` and `rule=R8`.\n')
for s in sorted(agent,key=lambda s:s['source_line_1based']):
    n=s['source_line_1based']
    if n in sections:
        out.append('\n'+sections[n].replace('## Original example','### Original example',1));continue
    r=orig[n-1];m=r['metadata']
    d=''.join(difflib.unified_diff(r['rejected'].splitlines(True),r['chosen'].splitlines(True),'earlier','final',n=2))
    if len(d)>2500:d=d[:2500]+'\n… (truncated; full bodies in the viewer)\n'
    out.append(f"\n### Original example {n}: {m['declaration_name']}\nSpencer: {'retain' if s['spencer_retained'] else 'exclude'} ({s['spencer_class']}); fast: **unresolved**. Assessor: {s['assessor']}. [Viewer]({url(s)}).\n\n{s['reason']}\n\n```diff\n{d}```\n")
(BASE/'FAST-DISCUSSION.md').write_text(''.join(out))
print(len(user),len(agent))
