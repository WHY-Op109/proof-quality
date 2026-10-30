"""Review-only, reproducible fast screening. Does not write into the fork."""
import sys,json,re,hashlib,difflib
from pathlib import Path
from collections import Counter
from datetime import datetime,timezone
BASE=Path(__file__).resolve().parent.parent
REPO=BASE.parents[2]/'proof-quality'
sys.path.insert(0,str(REPO/'src'))
from proof_quality.dataset_generation.lean_source import split_comments

def read(p):return [json.loads(s) for s in p.read_text().splitlines() if s.strip()]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,rs):p.write_text(''.join(json.dumps(r,ensure_ascii=False)+'\n' for r in rs))
raw=REPO/'data/mathlibpr/pairs.jsonl'; original=read(raw); idx=read(BASE/'sample-index.jsonl'); old=read(REPO/'data/mathlibpr/pairs.substantive.jsonl')
identity=digest(raw)
assert len(original)==len(idx) and all(x['dataset_sha256']==identity for x in idx)
def key(r):return (r['prompt'],r['chosen'],r['rejected'],json.dumps({k:v for k,v in r['metadata'].items() if k!='diff_class'},sort_keys=True,ensure_ascii=False))
oldkeys={key(r) for r in old}; assert len(oldkeys)==len(old)
assert oldkeys.issubset({key(r) for r in original})
humans=read(BASE/'human-decisions.jsonl');latest={d['sample_id']:d for d in humans}
manual=json.loads((BASE/'fast-screen/individual-assessments.json').read_text())
manual.update({'1291':'Uses cancellation and functoriality instead of unfolding the affine-open isomorphism and delicate definitional rewriting.','1345':'Specialises the multivariate power-series theorem instead of repeating the coefficient-order estimate.','1479':'Uses Big-O addition and polynomial-growth monotonicity instead of separately choosing and bounding growth constants.'})
neutral={611:'The same extensionality argument is written as a term instead of tactics.',1019:'The same implication proof moves intro into a lambda and combines rewrites.'}
uncertain={106:'A helper-lemma proof becomes a direct proof. The helper may have been removed or changed; earlier simplicity versus final self-containment is unsettled.',1095:'Earlier specialises a helper, final gives the argument directly. No evidence establishes whether the helper remains available or whether its removal improves organisation.',1128:'The same determinant identities are expanded into more intermediate equations; human clarity judgment pending.',884:'The same induction remains but branch detail disappears behind simp; presentation versus hidden detail is unsettled.',939:'The same reflected-sum calculation is reorganised and shorter; a meaningful preference is not established.',1046:'An explicitly stated intermediate goal is omitted; simp and abel carry the same calculation. Reader preference is unsettled.',1243:'Explicit set-membership witness construction becomes simp/grind; the user has deferred related cases.',1515:'Tensor-induction additive branches become grind; the mathematical induction remains.',1589:'The same stopping-time case analysis uses shorter simp proofs and a changed untop API.',1664:'The same diagonal-operator upper/lower bound argument is reorganised; reuse and presentation changes are mixed.',1802:'Named angle lemmas and automated sign-case analysis replace explicit representative calculations; reuse versus hidden detail is mixed.',1803:'Changes to real-representative/divisibility reasoning are mixed with grind; preference requires mathematical/context review.',2017:'The long induction step is largely hidden in grind; related automation policy is deferred.',2020:'The same Chebyshev induction and parity cases remain with shorter simp_all branches.',2021:'The same Chebyshev induction and parity cases remain with shorter simp_all branches.',2045:'The same exceptional-base split and logarithm formula remain, with shorter simplification.',2048:'Explicit doubly-stochastic row/column-sum transport is replaced by grind; mathematical content is hidden rather than shown changed.',2218:'A grind proof becomes explicit membership witnesses; user has not settled a general automation-versus-explicit preference.',2219:'A grind proof becomes explicit dependent-index cases and membership witnesses; preference remains unsettled.',2220:'A grind proof becomes explicit permutation cases; no speed or reliability measurement establishes a preference.',2260:'The same height-product estimates are reorganised through gcongr rather than calc; a direction is not established.',2287:'The same exponential bound and multiplication argument is compressed; presentation preference is unsettled.',2288:'The same determinant sign cases use longer default simplification; tactic economy alone does not settle quality.',2303:'A named interval-equality characterization is reused together with grind; contribution of reuse versus hidden detail needs review.'}
uncertain.update({int(k):v for k,v in json.loads((BASE/'fast-screen/expansion-assessments.json').read_text()).items()})
AUTO={'aesop','aesop_cat','cat_disch','grind','omega','lia','linarith','nlinarith','ring','ring_nf','field','field_simp','tauto','decide','native_decide','simp_all','fun_prop','positivity','norm_num'}
def tokens(s):return re.findall(r'\w+[\w\'.]*|<;>|:=|=>|↦|[^\s]',s)
def safe_norm(ts):
 return [({'↦':'=>','λ':'fun'}.get(t,t)) for t in ts if t not in {'(',')',';', '·','<;>'}]
round2={}
for f in sorted((BASE/'fast-screen/round2').glob('out-*.json')):
 round2.update(json.loads(f.read_text()))
for k,v in round2.items():
 assert (v['decision'],v['direction'])in{('retain','final_better'),('retain','earlier_better'),('exclude','no_material_preference'),('unresolved','unresolved')},(k,v)
stage_a_path=BASE/'fast-screen/stage-a/final.json';stage_a=json.loads(stage_a_path.read_text()) if stage_a_path.exists() else {}
clusters_path=BASE/'fast-screen/stage-a/clusters.json';clusters=json.loads(clusters_path.read_text()) if clusters_path.exists() else {}
answers_path=BASE/'fast-screen/human-cluster-answers.jsonl'
answers={a['cluster_id']:a for a in map(json.loads,answers_path.read_text().splitlines())} if answers_path.exists() else {}
# The user's own earlier meeting cases, grouped under the topics of the 2026-10-30 answers.
EARLIER_TOPICS={1574:'Automated tactics',1587:'Automated tactics',1617:'Automated tactics',1381:'Automated tactics',1128:'Presentation detail: calc granularity'}
flags={d['source_line_1based']:d for d in map(json.loads,(BASE/'human-review/meeting-flags.jsonl').read_text().splitlines())}
disagree={}
for c in map(json.loads,(BASE/'comparison.jsonl').read_text().splitlines()):
 disagree[c['source_line_1based']]=c
results=[]
for pos,(r,inv) in enumerate(zip(original,idx),1):
 assert inv['source_line_1based']==pos
 for field in ('prompt','chosen','rejected'):
  assert hashlib.sha256(r[field].encode()).hexdigest()==inv['source_key'][field+'_sha256']
 a,ac=split_comments(r['rejected']);z,zc=split_comments(r['chosen']);at=tokens(a);zt=tokens(z)
 ratio=(len(zt)+1)/(len(at)+1); sim=difflib.SequenceMatcher(None,at,zt,autojunk=False).ratio()
 direction='unresolved';decision='unresolved';category='difficult_preference';mode='automated_rule_application';rule='R7';reason='Changed code; no conservative rule establishes either a meaningful difference or its absence. Individual examination remains needed.'
 if at==zt:
  decision='exclude';category='little_apparent_mathematical_effect';direction='no_material_preference';rule='R1';reason='Code tokens unchanged; comments differ only in placement, removal, spelling/capitalisation or spacing under a word-multiset check. This fast-pass interpretation is not a universal claim that comments never matter.'
  if Counter(re.findall(r'\w+',zc.lower())) - Counter(re.findall(r'\w+',ac.lower())):
   decision='unresolved';category='difficult_preference';direction='unresolved';reason='Code tokens unchanged but comment wording adds or substitutes words; explanatory value requires reading, not blanket exclusion.'
 elif safe_norm(at)==safe_norm(zt):
  decision='exclude';category='little_apparent_mathematical_effect';direction='no_material_preference';rule='R2';reason='Only grouping/layout/lambda-arrow spelling differs under limited lexical normalization; no quality advantage demonstrated.'
 elif re.sub(r'\s+','',a) in ('byrfl','rfl') and re.sub(r'\s+','',z) in ('byrfl','rfl'):
  decision='exclude';category='little_apparent_mathematical_effect';direction='no_material_preference';rule='R2';reason='Direct rfl versus tactic-wrapped rfl; no mathematical argument change. Library metadata effects not assessed.'
 elif (set(at)^set(zt)) & AUTO:
  category='difficult_preference';rule='R3';reason='Automation vocabulary changes; code alone does not justify a quality direction. No timing/robustness comparison performed.'
 elif min(ratio,1/ratio)<.68 and max(len(at),len(zt))>=35:
  category='mixed_changes';rule='R4';reason='Substantial code-size/organisation change is a candidate for examination, not evidence by itself of improvement. Named-lemma availability and mathematical effect remain unchecked.'
 # A single alpha-renaming of a binder declared inside the proof.
 elif len(at)==len(zt):
  pairs={(x,y) for x,y in zip(at,zt) if x!=y}
  if len(pairs)==1:
   x,y=next(iter(pairs));binder=re.compile(r'\b(?:have|let|intro|rintro|rename_i)\s+'+re.escape(x)+r'(?=\s|:)')
   if binder.search(a) and re.fullmatch(r'\w+',x) and re.fullmatch(r'\w+',y):
    decision='exclude';category='little_apparent_mathematical_effect';direction='no_material_preference';rule='R2';reason='One consistently substituted locally declared binder name; no substantive advantage identified by this lexical rule.'
 if str(pos) in manual:
  decision='retain';category='clear_quality_difference';direction='final_better';mode='individual_code_examination';rule='R5';reason=manual[str(pos)]
 if pos in neutral:
  decision='exclude';category='little_apparent_mathematical_effect';direction='no_material_preference';mode='individual_code_examination';rule='R5';reason=neutral[pos]
 if pos in uncertain:
  decision='unresolved';category='mixed_changes' if pos in (106,1095,1664,1802,1803,2303) else 'difficult_preference';direction='unresolved';mode='individual_code_examination';rule='R5';reason=uncertain[pos]
 continuation_path=BASE/'fast-screen/continuation-assessments.json'
 continuation=json.loads(continuation_path.read_text()) if continuation_path.exists() else {}
 if str(pos) in continuation:
  individual=continuation[str(pos)]
  assert all(hashlib.sha256(r[k].encode()).hexdigest()==v for k,v in individual['proof_hashes'].items())
  decision=individual['decision'];category=individual['category'];direction=individual['direction'];reason=individual['reason'];mode='individual_diff_examination';rule='R6'
 assessor='codex' if mode!='automated_rule_application' else None;dims=[];flag=None
 if str(pos) in round2:
  individual=round2[str(pos)];assert mode=='automated_rule_application',pos
  decision=individual['decision'];category=individual['category'];direction=individual['direction'];reason=individual['reason'];mode='individual_diff_examination';rule='R8';assessor='claude-code-round2';dims=individual.get('dimensions',[])
  if individual.get('difficult_for_user'):flag={'source':'agent_suggestion','why':individual['reason'],'question':individual.get('question')}
 if clusters:flag=None
 first_screen=None;stage=None
 if str(pos) in stage_a:
  first_screen={'decision':decision,'direction':direction,'reason':reason,'assessor':assessor};stage=stage_a[str(pos)]
  decision,direction,category,reason=stage['decision'],stage['direction'],stage['category'],stage['reason'];rule='R9'
  if stage['outcome']=='adjudicated':assessor='claude-code-adjudicator'
 cluster=clusters.get(str(pos))
 if cluster and decision=='unresolved':
  if cluster.get('representative'):flag={'source':'agent_cluster','why':cluster['summary'],'question':cluster['question'],'cluster_id':cluster['cluster_id'],'cluster_size':cluster['size']}
 meeting=None;answer=None
 if cluster and decision=='unresolved' and cluster['cluster_id'] in answers:
  ans=answers[cluster['cluster_id']];it=ans['interpretation']
  answer={'answer_id':ans['answer_id'],'question_id':ans['question_id'],'verbatim':ans['user_answer_verbatim'],'status':ans['application_status'],'proposed_direction':it['proposed_direction']}
  if ans['application_status']=='confirmed' and it['proposed_direction']=='no_material_preference':
   decision,direction,category,reason='exclude','no_material_preference','little_apparent_mathematical_effect',f"Your answer to {ans['question_id']} ({ans['cluster_id']}): no meaningful difference. {reason}";rule='R0c'
  if it['discussion_topic']:meeting={'topic':it['discussion_topic'],'note':ans['user_answer_verbatim'],'question_id':ans['question_id'],'example_row':ans['representative_row']}
  flag=None
 automated_proposal={'decision':decision,'direction':direction,'rule':rule}
 human=latest.get(inv['sample_id']);human_disagreement=None
 if human:
  mode='recorded_human_judgment';rule='R0';interp=human['structured_interpretation'];direction=interp['direction'];reason=interp['rationale']
  if human.get('decision_status')=='deferred_pending_meeting':decision='unresolved';category='difficult_preference';direction='unresolved'
  elif direction in ('final_better','earlier_better'):decision='retain';category='clear_quality_difference'
  elif direction=='no_material_preference':decision='exclude';category='little_apparent_mathematical_effect'
  else:decision='unresolved';category='difficult_preference'
  if automated_proposal['decision']!=decision or (automated_proposal['direction'] not in ('unresolved',direction)):
   human_disagreement={'codex_pre_override_proposal':automated_proposal,'resolution':'Actual human judgment preserved; this mismatch is not a human-label error.'}
 usability=[];path=r['metadata'].get('file_path','');earlierpath=r['metadata'].get('earlier_file_path','')
 if path.startswith('MathlibTest/') or earlierpath.startswith('MathlibTest/'):usability.append('test_fixture_path')
 if re.search(r'\b(sorry|admit)\b',a+'\n'+z):usability.append('explicit_admission_in_code')
 if re.search(r'\bletI\s*:=\s*$',r['prompt']):usability.append('statement_proof_boundary_defect')
 if any(re.fullmatch(r'\s*(by)?\s*',x) for x in (r['chosen'],r['rejected'])):usability.append('empty_proof_body')
 # Individually observed extraction defects that no generic check catches.
 if pos in {86}:usability.append('truncated_proof_body')
 quality_decision=decision
 if usability:
  decision='unresolved' if 'statement_proof_boundary_defect' in usability and human else 'exclude';category='usability_problem';reason+=' Separately: '+', '.join(usability)+'. Original data not repaired.'
 if human and human.get('decision_status')=='deferred_pending_meeting':flag={'source':'user_flagged','why':human['user_decision_verbatim']}
 elif pos in flags:flag={'source':'user_flagged','why':flags[pos]['user_instruction_verbatim']}
 if pos in EARLIER_TOPICS and human:meeting={'topic':EARLIER_TOPICS[pos],'note':human['user_decision_verbatim'],'question_id':'earlier flag','example_row':None}
 if not flag and not clusters and pos in (106,1095,2218):flag={'source':'agent_suggestion','why':'Earlier Codex pass: '+reason}
 agent_dis=[]
 if pos in disagree:
  dp=disagree[pos]['direction_patterns']
  for agent,pattern in dp.items():
   implied={'final_only':'final_better','earlier_only':'earlier_better','none_directional':'no_material_preference'}.get(pattern,pattern)
   if (direction!='unresolved' and implied!=direction) or disagree[pos]['disagreement_types']!=['agreement']:agent_dis.append({'agent':agent+'-checkpoint-01','view':pattern,'fast_direction':direction,'disagreement_types':disagree[pos]['disagreement_types']})
 res={'schema_version':'fast-screen-1.1','sample_id':inv['sample_id'],'dataset_sha256':identity,'source_line_1based':pos,'source_key':inv['source_key'],'spencer_retained':key(r) in oldkeys,'spencer_class':inv['historical_filter_class'],'decision':decision,'quality_classification':category,'preference_direction':direction,'quality_decision_before_usability_gate':quality_decision,'reason':reason,'assessment_method':mode,'assessor':'user' if human else assessor,'dimensions':dims,'discussion':flag,'meeting':meeting,'cluster_answer':answer,'cluster':cluster if decision=='unresolved' else None,'first_screen':first_screen,'stage_a':{k:v for k,v in stage.items() if k in ('outcome','second_screen','strata')} if stage else None,'agent_disagreements':agent_dis,'rule':rule,'human_decision_id':human['decision_id'] if human else None,'human_verbatim':human['user_decision_verbatim'] if human else None,'human_disagreement':human_disagreement,'usability_flags':usability,'features':{'earlier_tokens':len(at),'final_tokens':len(zt),'final_to_earlier_token_ratio':round(ratio,4),'token_similarity':round(sim,4)},'verification':{'compiled':False,'profiled':False,'earlier_lemma_availability':'not_newly_verified_in_fast_pass','scope':'Extracted scripts in their respective snapshot roles; underlying environments may differ'},'assessment_scope':continuation.get(str(pos),{}).get('assessment_scope','See assessment_method and verification scope'),'training_inclusion':'not_decided','original_viewer_url':'http://127.0.0.1:8737/#'+__import__('urllib.parse',fromlist=['quote']).quote(str(r['metadata']['pr_number'])+'/'+r['metadata']['declaration_name'],safe='')}
 results.append(res)
save(BASE/'FAST-SCREENING.jsonl',results)
for choice,fn in [('retain','fast-retained.pairs.jsonl'),('unresolved','fast-unresolved.pairs.jsonl'),('exclude','fast-excluded.pairs.jsonl')]:save(BASE/fn,[r for r,s in zip(original,results) if s['decision']==choice])
# Each exported row is exactly the original object. Direction is in the sidecar, never swapped.
nav=[]
for choice in ('retain','unresolved','exclude'):
 for j,s in enumerate([s for s in results if s['decision']==choice],1):nav.append({'sample_id':s['sample_id'],'dataset_sha256':identity,'original_full_file_row':s['source_line_1based'],'view':choice,'viewer_row':j,'url':f'http://127.0.0.1:8740/'+('' if choice=='retain' else choice+'/')+s['original_viewer_url'].split('/',3)[3],'explanation_url':f'http://127.0.0.1:8740/explanation/{s["source_line_1based"]}'})
save(BASE/'fast-navigation.jsonl',nav)
counts=Counter(s['decision'] for s in results);cross={str(k):sum(s['spencer_retained']==k[0] and s['decision']==k[1] for s in results) for k in [(o,c) for o in (True,False) for c in ('retain','exclude','unresolved')]}
manifest={'created_utc':datetime.now(timezone.utc).isoformat(),'population':len(original),'spencer_retained':len(old),'counts':dict(counts),'method_counts':dict(Counter(s['assessment_method'] for s in results)),'cross_table':cross,'unprocessed_rows':0,'agent_disagreement_rows':sum(bool(s['agent_disagreements']) for s in results),'discussion_rows':sum(bool(s['discussion']) for s in results),'meeting_rows':sum(bool(s['meeting']) for s in results),'individually_unexamined_rows':sum(s['assessment_method']=='automated_rule_application' for s in results),'human_record_lines':len(humans),'human_unique_cases':len(latest),'human_finalized':sum(d.get('decision_status')!='deferred_pending_meeting' for d in latest.values()),'inputs':{str(p.relative_to(BASE)) if p.is_relative_to(BASE) else str(p):digest(p) for p in [raw,REPO/'data/mathlibpr/pairs.substantive.jsonl',BASE/'human-decisions.jsonl',BASE/'sample-index.jsonl',BASE/'fast-screen/individual-assessments.json',BASE/'fast-screen/expansion-assessments.json',BASE/'fast-screen/continuation-assessments.json',*sorted((BASE/'fast-screen/round2').glob('out-*.json')),*[x for x in (stage_a_path,clusters_path,answers_path) if x.exists()],Path(__file__)]},'output_hashes':{f:digest(BASE/f) for f in ['FAST-SCREENING.jsonl','fast-retained.pairs.jsonl','fast-unresolved.pairs.jsonl','fast-excluded.pairs.jsonl','fast-navigation.jsonl']}}
(BASE/'fast-screen/manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({k:v for k,v in manifest.items() if k not in ('inputs','output_hashes')},indent=2))
