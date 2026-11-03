# Weighted-query guard evidence

The same Monad-parametric guard forwards accepted queries, including markers, and freezes
effects after overflow. Its source287 is an exact prefix of the current395-line owner.
The added108 lines prove one exact event-filtered ProbComp law with one private invariant:
from zero counters/false flag, guarded joint event AND non-abort has the same mass as the
counted-source joint event AND final coordinate caps. The event retains output, both counts
and cache; initial cache may be arbitrarily mixed. This needs no whole-source AE cap.

The previous constructor, all-path cap and full mixed-source AE-law checks remain unchanged.
FreeGuardInterpretation88 and InterpretationAudit are byte-identical: algebraic interpretation
still retains all output/cache/counters/flag for arbitrary lawful m and all initial states.
The new event law itself keeps ZERO initial counts and false flag; arbitrary starts are not
silently generalized. Abort cannot be treated as raw output success. Neither input-only cost
nor the event is certified seed-independent, and no SLH win-local affordability, disjointness,
guarded-byte/source/seed/fill/full127 application is established by this archive.

Prototype acceptance cf689 and the exact395 source are separate from archive replay. The
original9c8 receipts remain historical for guard287/old audit, not validation of these new bytes.
The original interpretation dependency-namespace typo remains a provenance note; no frozen
receipt is rewritten. Old complete GuardAudit targets remain a byte-exact prefix; only the
new full literal event-law application is appended PRIVATE. BOTH auditTXT files keep their
existing MODULE convention with genuine public target definitions. All FOUR files emit FIVE
artifacts each (20total); neither audit is a NONMODULE/one-artifact script.

## Replay

Use immutable already-built b63 and all twelve manifest-locked clean packages. Set the actual
committed research receipt SHA and a NEW ABSENT output path. No Lake build/cache download or
repository write occurs. Copy all four source streams byte-exactly into fresh sources; audits
are renamed only. The finite recipe pins compilerbf8d and sixStd files, sourceGitblobs/semantic
indices, normal source+artifacts and all12 locks before EACH compiler/after. Before EVERY consumer it hashes
all FIVE artifacts of each fresh transitive module, including the new guard. Current replay
is UNRUN until separately granted at a clean committed HEAD. Require four0 exits, no warnings,
standard-only reports and identical frames; default proof limits/j2/240s apply. Index records
are semantic `git ls-files --stage -z` hashes, not raw index-file byte claims.

```bash
research=$(GIT_OPTIONAL_LOCKS=0 git rev-parse --show-toplevel)
artifact=/tmp/vcvio-slhdsa-integration
recorded_head=REPLACE_WITH_ACTUAL_FULL_COMMIT_SHA
out=/tmp/slhdsa-event-guard-REPLACE_WITH_NEW_ABSENT_LABEL
python3 - "$research" "$artifact" "$out" "$recorded_head" <<'PYREPLAY'
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
os.environ['GIT_OPTIONAL_LOCKS']='0';os.environ['GIT_NO_LAZY_FETCH']='1'
research,base,out=map(Path,sys.argv[1:4]);head=sys.argv[4]
evidence=research/'docs/design/slh-dsa-weighted-guard-evidence'
m=json.loads((evidence/'manifest.json').read_text());compiler=Path(m['compiler_path'])
assert re.fullmatch('[0-9a-f]{40}',head) and out.is_absolute()
out.mkdir(exist_ok=False);(out/'src').mkdir();order=m['current_replay']['moduleOrder']
local={n:evidence/m['current_replay']['moduleFiles'][n]for n in order}
suffixes=m['current_replay']['artifactSuffixes']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def put(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def git(p,*args):return subprocess.check_output(['git','-C',str(p),*args]).decode().strip()
def state(p):
 raw=subprocess.check_output(['git','-C',str(p),'ls-files','--stage','-z']);index={r.split(b'\t',1)[1].decode():r.split()[1].decode()for r in raw.split(b'\0')if r}
 return {'head':git(p,'rev-parse','HEAD'),'tree':git(p,'rev-parse','HEAD^{tree}'),
  'status':git(p,'status','--porcelain'),'semanticIndex':hashlib.sha256(raw).hexdigest()},index
def bound(p,repo,index,rev):
 oid=blob(p.read_bytes());rel=str(p.relative_to(repo));assert index[rel]==oid and git(repo,'rev-parse',rev+':'+rel)==oid
 return {'sha256':sha(p),'gitBlob':oid}
def imports(p):
 text=re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S)
 return [match.group(1)for line in text.splitlines()for match in [re.match(
  r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.]+)',line)]if match]
closure={};external=set();todo=list(local)
while todo:
 name=todo.pop()
 if name in closure or name in external:continue
 p=local.get(name,base/(name.replace('.','/')+'.lean'))
 if not p.exists():external.add(name);continue
 closure[name]={'source':str(p),'imports':imports(p)};todo+=imports(p)
assert not any(n.startswith('HashSig.')for n in closure)
put(out/'closure.json',{'modules':closure,'externalPackageCompilerLeaves':sorted(external)})
def frame():
 rs,ri=state(research);bs,bi=state(base)
 r={'research':rs,'canonical':bs,
  'compiler':{'path':str(compiler),'sha256':sha(compiler)},
  'stdRoots':{p:sha(p)for p in m['std_root_sha256']},'manifest':bound(evidence/'manifest.json',research,ri,head),
  'archiveFiles':{},'canonicalSourcesAndArtifacts':{},'dependencies':{}}
 assert r['research']['head']==head and r['canonical']['head']==m['canonical_commit']
 assert not r['research']['status']and not r['canonical']['status']
 assert r['compiler']['sha256']==m['compiler_sha256']and r['stdRoots']==m['std_root_sha256']
 assert len(r['stdRoots'])==6 and sha(base/'lake-manifest.json')==m['lake_manifest_sha256']
 for name,expected in m['files'].items():
  p=evidence/name;assert sha(p)==expected;rel=str(p.relative_to(research))
  r['archiveFiles'][name]=bound(p,research,ri,head)
 for name,entry in closure.items():
  if name in local:continue
  p=Path(entry['source']);artifact=base/'.lake/build/lib/lean'/name.replace('.','/')
  assert artifact.with_suffix('.olean').is_file()
  r['canonicalSourcesAndArtifacts'][name]={'source':bound(p,base,bi,m['canonical_commit']),'artifacts':{
   str(q):sha(q)for q in sorted(artifact.parent.glob(artifact.name+'.*'))if q.is_file()}}
 assert len(m['actual_dependency_revisions'])==12
 for name,rev in m['actual_dependency_revisions'].items():
  s,_=state(base/'.lake/packages'/name);assert s['head']==rev and not s['status'];r['dependencies'][name]=s
 return r
before=frame();put(out/'before.json',before);results=[];done={};totalReports=0;env=os.environ.copy()
env.update(LEAN_NUM_THREADS='2',LEAN_PATH=':'.join([str(out),str(base/'.lake/build/lib/lean')]+[
 str(base/'.lake/packages'/n/'.lake/build/lib/lean')for n in m['actual_dependency_revisions']]))
try:
 for name in order:
  needed=set();pending=[x for x in imports(local[name])if x in local]
  while pending:
   dep=pending.pop()
   if dep in needed:continue
   needed.add(dep);pending += [x for x in imports(local[dep])if x in local]
  assert needed<=done.keys()
  assert all(not(out/(dep+'.'+s)).is_symlink()for dep in needed for s in suffixes)
  consumed={str(out/(dep+'.'+s)):sha(out/(dep+'.'+s))for dep in sorted(needed)for s in suffixes}
  assert all(consumed[str(out/(dep+'.'+s))]==done[dep][str(out/(dep+'.'+s))]for dep in needed for s in suffixes)
  source=out/'src'/(name+'.lean');source.write_bytes(local[name].read_bytes())
  assert sha(source)==m['files'][m['current_replay']['moduleFiles'][name]]
  argv=[str(compiler),'-j2','-DautoImplicit=false','-DrelaxedAutoImplicit=false',
   '-Dweak.linter.mathlibStandardSet=true','-Dweak.linter.redundantVisibility=true',
   '--root='+str(source.parent),'-o',str(out/(name+'.olean')),str(source)]
  current=frame();assert current==before;put(out/(name+'-before.json'),current)
  put(out/(name+'-input.json'),{'frameSHA256':sha(out/(name+'-before.json')),'argv':argv,'cwd':str(research),'LEAN_PATH':env['LEAN_PATH'],
   'sourceSHA256':sha(source),'freshImportedArtifacts':consumed,'jobs':2,'defaultProofLimits':True,
   'environment':{'GIT_OPTIONAL_LOCKS':'0','LEAN_NUM_THREADS':'2'},'wallCapSeconds':240})
  start=time.monotonic()
  with (out/(name+'.log')).open('w')as log:
   try:child=subprocess.run(argv,cwd=research,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=240)
   except subprocess.TimeoutExpired:
    put(out/'timeout.json',{'module':name,'wallCapSeconds':240,'acceptance':False});raise
  row={'module':name,'exit':child.returncode,'seconds':time.monotonic()-start,'outputs':{},
   'sourceSHA256':sha(source),'inputSHA256':sha(out/(name+'-input.json')),'logSHA256':sha(out/(name+'.log'))}
  results.append(row);put(out/'results.json',results);assert child.returncode==0
  row['outputs']={str(out/(name+'.'+s)):sha(out/(name+'.'+s))for s in suffixes};put(out/'results.json',results)
  assert not re.search(r'\b(warning|error):',(out/(name+'.log')).read_text())
  reports=re.findall(r'depends on axioms: \[([^\]]*)\]|does not depend on any axioms',(out/(name+'.log')).read_text(),re.S);assert len(reports)==m['current_replay']['printedAxiomReports'][name];totalReports+=len(reports)
  for values in reports:
   assert {x.strip()for x in values.replace('\n','').split(',')if x.strip()}<=set(m['allowed_axioms'])
  assert all(sha(p)==v for p,v in consumed.items());done[name]=row['outputs']
finally:
 after=frame();put(out/'after.json',after);assert before==after
assert len(results)==4 and sum(len(x['outputs'])for x in results)==20 and totalReports==m['current_replay']['expectedStandardReports']==12
PYREPLAY
```
