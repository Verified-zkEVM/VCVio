# Native actual-key thinning and tracked-class causality

The original single/pair firing laws use the generated actual public key, pure deterministic
`kappa`, arbitrary fixed tapes with `L.other=[]`, and no added budget or signer-history premise.
Their eight source files and historical proof/replay references are unchanged.

`NativeCausality.prEvent_cnt_overwrite` now quantifies every `TapeClass`, an arbitrary native
role program and current `RoleState`. Overwriting cell `cell>=index` preserves the probability
of crossing the tracked counter's current value plus `index`; the program, cache and metadata
remain fixed. Cache hits count as calls independently of fresh tape consumption. The same
three proof owners establish this law; there is no second signer engine. The full concrete
forger statement is retained. The closed audit also specializes signer index1 to `cnt>=2`.

The three current sources are the exact accepted468-line prototype (review379a22fb). The
previous442-line versions and commit074c's validation remain explicitly historical in the
manifest. They did not validate these new bytes or record five imported artifact pins.
The current eleven modules total1932 physical Lean lines; the private audit adds73 lines.
There is no production, axiom-reduction, bound-improvement or LOC-saving claim.

This evidence does not prove source signing-attempt caps, load/run factorization, used-prefix
coverage, joint-budget/guard/policy transport, byte/weak-seed assembly, filling or full127.
The audit's NONMODULE/private packaging and the updated whole archive await a fresh committed
replay; the existing external proof acceptance is not relabelled as that replay.

## Replay

Use immutable already-built `b63fede7…` and all twelve manifest-locked clean dependencies.
Run from a clean committed research checkout. Set `recorded_head` to its actual full receipt SHA
and choose a NEW ABSENT output path. No Lake build/cache download or repository write occurs.
The finite recipe compiles all eleven modules in one fresh output, then copies the TXT audit
byte-exactly to a temporary Lean script. It pins the explicit compiler, six Std files, source
Git blobs/indices, ordinary+meta closure and canonical artifacts before/after. Before every
consumer it hashes all five artifacts of each fresh transitive imported module; it makes no
such claim about historical recordings. The private audit emits one artifact. Require twelve
zero exits, no warnings, standard-only printed axioms and identical frames. Default proof
limits and a240s per-process watchdog apply; legacy8 usej4 and new3/audit usej2.

```bash
research=$(GIT_OPTIONAL_LOCKS=0 git rev-parse --show-toplevel)
artifact=/tmp/vcvio-slhdsa-integration
recorded_head=REPLACE_WITH_ACTUAL_FULL_COMMIT_SHA
out=/tmp/slhdsa-native-tracked-REPLACE_WITH_NEW_ABSENT_LABEL
python3 - "$research" "$artifact" "$out" "$recorded_head" <<'PYREPLAY'
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
os.environ['GIT_OPTIONAL_LOCKS']='0'
research,base,out=map(Path,sys.argv[1:4]);head=sys.argv[4]
evidence=research/'docs/design/slh-dsa-native-thinning-evidence'
m=json.loads((evidence/'manifest.json').read_text());compiler=Path(m['compiler']['path'])
out.mkdir(exist_ok=False);(out/'audit').mkdir();suffixes=['olean','olean.private','olean.server','ir','ir.sig']
order=m['currentArchiveReplay']['moduleOrder'];local={n:evidence/(n+'.lean')for n in order[:-1]}
local['ImportAudit']=evidence/'ImportAudit.lean.txt'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def put(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def git(p,*args):return subprocess.check_output(['git','-C',str(p),*args]).decode().strip()
def state(p):
 return {'head':git(p,'rev-parse','HEAD'),'tree':git(p,'rev-parse','HEAD^{tree}'),
  'status':git(p,'status','--porcelain'),'index':hashlib.sha256(subprocess.check_output(
   ['git','-C',str(p),'ls-files','--stage','-z'])).hexdigest()}
def imports(p):
 text=re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S)
 return [v for line in text.splitlines()for match in [re.match(
  r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.]+)',line)]
  if match for v in [match.group(1)]]
closure={};external=set();todo=list(local)
while todo:
 name=todo.pop()
 if name in closure or name in external:continue
 p=local.get(name,base/(name.replace('.','/')+'.lean'))
 if not p.exists():external.add(name);continue
 closure[name]={'source':str(p),'imports':imports(p)};todo+=imports(p)
for name in closure:
 assert not any(name==p or name.startswith(p+'.')for p in m['excludedPositiveEndpoints'])
put(out/'closure.json',{'modules':closure,'externalPackageCompilerLeaves':sorted(external)})
def frame():
 r={'research':state(research),'canonical':state(base),'compiler':{'path':str(compiler),'sha256':sha(compiler)},
  'stdRoots':{p:sha(p)for p in m['stdRoots']},'manifest':sha(evidence/'manifest.json'),
  'readme':sha(evidence/'README.md'),'archiveSources':{},'canonicalSourcesAndArtifacts':{},'dependencies':{}}
 assert r['research']['head']==head and r['canonical']['head']==m['baseCommit']
 assert not r['research']['status']and not r['canonical']['status']
 assert r['compiler']==m['compiler']and r['stdRoots']==m['stdRoots']and len(r['stdRoots'])==6
 assert sha(base/'lake-manifest.json')==m['lakeManifestSha256']
 assert (base/'lean-toolchain').read_text().strip()==m['toolchain']
 for name,entry in {**m['sourceFiles'],**m['auditFiles']}.items():
  p=evidence/name;assert sha(p)==entry['sha256'];rel=str(p.relative_to(research))
  r['archiveSources'][name]={'sha256':sha(p),'gitBlob':git(research,'rev-parse',head+':'+rel)}
 for name,entry in closure.items():
  if name in local:continue
  p=Path(entry['source']);artifact=base/'.lake/build/lib/lean'/name.replace('.','/')
  assert artifact.with_suffix('.olean').is_file()
  r['canonicalSourcesAndArtifacts'][name]={'source':sha(p),'artifacts':{
   str(q):sha(q)for q in sorted(artifact.parent.glob(artifact.name+'.*'))if q.is_file()}}
 assert len(m['dependencyRevisions'])==12
 for name,rev in m['dependencyRevisions'].items():
  s=state(base/'.lake/packages'/name);assert s['head']==rev and not s['status'];r['dependencies'][name]=s
 return r
before=frame();put(out/'before.json',before);results=[];done=set();env=os.environ.copy()
env['LEAN_PATH']=':'.join([str(out),str(base/'.lake/build/lib/lean')]+[
 str(p/'.lake/build/lib/lean')for p in sorted((base/'.lake/packages').iterdir())])
try:
 for name in order:
  needed=set();pending=[x for x in imports(local[name])if x in local]
  while pending:
   dep=pending.pop()
   if dep in needed:continue
   needed.add(dep);pending += [x for x in imports(local[dep])if x in local]
  assert needed<=done
  assert all(not(out/(dep+'.'+s)).is_symlink()for dep in needed for s in suffixes)
  consumed={str(out/(dep+'.'+s)):sha(out/(dep+'.'+s))for dep in sorted(needed)for s in suffixes}
  jobs=4 if order.index(name)<8 else 2;env['LEAN_NUM_THREADS']=str(jobs);source=local[name]
  if name=='ImportAudit':source=out/'audit/ImportAudit.lean';source.write_bytes(local[name].read_bytes())
  assert sha(source)==({**m['sourceFiles'],**m['auditFiles']}[name+'.lean.txt'if name=='ImportAudit'else name+'.lean']['sha256'])
  argv=[str(compiler),'-j'+str(jobs),'-DautoImplicit=false','-DrelaxedAutoImplicit=false',
   '-Dweak.linter.mathlibStandardSet=true','-Dweak.linter.redundantVisibility=true',
   '--root='+str(source.parent),'-o',str(out/(name+'.olean')),str(source)]
  put(out/(name+'-input.json'),{'argv':argv,'cwd':str(research),'LEAN_PATH':env['LEAN_PATH'],
   'sourceSHA256':sha(source),'environment':{'GIT_OPTIONAL_LOCKS':'0','LEAN_NUM_THREADS':str(jobs)},
   'freshImportedArtifacts':consumed,'jobs':jobs,'defaultProofLimits':True,'wallCapSeconds':240})
  start=time.monotonic()
  with (out/(name+'.log')).open('w')as log:
   try:child=subprocess.run(argv,cwd=research,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=240)
   except subprocess.TimeoutExpired:
    put(out/'timeout.json',{'module':name,'wallCapSeconds':240,'acceptance':False});raise
  row={'module':name,'exit':child.returncode,'seconds':time.monotonic()-start,'outputs':{},
   'sourceSHA256':sha(source),'inputSHA256':sha(out/(name+'-input.json')),
   'logSHA256':sha(out/(name+'.log'))}
  results.append(row);put(out/'results.json',results);assert child.returncode==0
  emitted={str(out/(name+'.'+s)):sha(out/(name+'.'+s))for s in (['olean']if name=='ImportAudit'else suffixes)}
  if name=='ImportAudit':assert all(not(out/(name+'.'+s)).exists()for s in suffixes[1:])
  row['outputs']=emitted;put(out/'results.json',results)
  assert child.returncode==0 and not re.search(r'\b(warning|error):',(out/(name+'.log')).read_text())
  for values in re.findall(r'depends on axioms: \[([^\]]*)\]',(out/(name+'.log')).read_text(),re.S):
   assert {x.strip()for x in values.replace('\n','').split(',')if x.strip()}<=set(m['allowedAxioms'])
  assert all(sha(p)==v for p,v in consumed.items());done.add(name)
finally:
 after=frame();put(out/'after.json',after);assert before==after
assert len(results)==12
PYREPLAY
```
