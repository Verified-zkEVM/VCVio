# Marked source: erasure, native discipline, counts and joint cost

The reviewed `MarkedLab.lean` has 1,471 lines: the original 686 plus 602 for counts and
183 for observation. Its four laws cover marker erasure, deterministic relative-suffix query
discipline, guarded signer/forger call bounds, and an equality retaining the actual inner key
pair, transcript, cache and cost for an arbitrary lawful target monad. Counts include cache
hits and losing verification. Existing construction and counter engines are reused.

This is research evidence, excluded from the planned selective production integration. It
establishes no wire/None/per-context bridge, guarded private-byte/fill/seed assembly or full127
bound. Retain the abort flag: fallback raw verification is not a winning event. The manifest
pins accepted external proofs/reviews; this package's committed replay is UNRUN. The private
NONMODULE audit checks all four complete public types.

The recipe extracts six existing owners from their EXACT frozen faeb Git blobs, even if later
commits append guard laws. No basis sources are stored in this archive. Run from a CLEAN
committed research checkout with its actual `recorded_head` and a NEW ABSENT `/tmp` output.
Use immutable b63 normal libraries and all 12 locked clean dependencies. The eight commands
use strict options, default proof limits, j2 and a 240s process watchdog. Require eight zero
exits, 36 outputs, 56 standard-only axiom reports (including empty reports) and no warnings. All five fresh sidecars of
every imported local owner are pinned BEFORE its consumer and checked afterward. Compiler,
six Std files, source/Git blobs, semantic indices, ordinary/meta closure and canonical artifacts
must match immediately before EACH compiler and afterward; each input receipt binds its frame. No Lake/cache operation or older local-owner fallback is permitted.

```bash
research=$(GIT_OPTIONAL_LOCKS=0 git rev-parse --show-toplevel)
base=/tmp/vcvio-slhdsa-integration
recorded_head=REPLACE_WITH_ACTUAL_FULL_COMMIT_SHA
out=/tmp/slhdsa-marked-source-REPLACE_WITH_NEW_ABSENT_LABEL
python3 - "$research" "$base" "$out" "$recorded_head" <<'PYREPLAY'
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
os.environ['GIT_OPTIONAL_LOCKS']='0';os.environ['GIT_NO_LAZY_FETCH']='1'
research,base,out=map(Path,sys.argv[1:4]);head=sys.argv[4]
evidence=research/'docs/design/slh-dsa-marked-source-evidence'
m=json.loads((evidence/'manifest.json').read_text());compiler=Path(m['compiler']['path'])
assert re.fullmatch('[0-9a-f]{40}',head) and out.is_absolute()
out.mkdir(exist_ok=False);src=out/'src';src.mkdir();suffixes=m['replay']['moduleArtifacts']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def put(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def git(p,*a):return subprocess.check_output(['git','-C',str(p),*a])
def state(p):
 raw=git(p,'ls-files','--stage','-z');index={r.split(b'\t',1)[1].decode():r.split()[1].decode()for r in raw.split(b'\0')if r}
 return {'head':git(p,'rev-parse','HEAD').decode().strip(),'tree':git(p,'rev-parse','HEAD^{tree}').decode().strip(),
  'status':git(p,'status','--porcelain').decode(),'index':hashlib.sha256(raw).hexdigest()},index
specs={n:{**v,'commit':m['frozenBasisCommit']}for n,v in m['basisSources'].items()}
for n,f in [('MarkedLab','MarkedLab.lean'),('ImportAudit','ImportAudit.lean.txt')]:
 specs[n]={**{**m['sourceFiles'],**m['auditFiles']}[f],'path':str((evidence/f).relative_to(research)),'commit':head}
local={}
for n,v in specs.items():
 b=git(research,'show',v['commit']+':'+v['path']);assert blob(b)==v['gitBlob'] and hashlib.sha256(b).hexdigest()==v['sha256']
 p=src/(n+'.lean');p.write_bytes(b);local[n]=p
assert len(m['replay']['moduleOrder'])==8 and set(m['replay']['moduleOrder'])==set(local)
# Strip nested comments and strings before recognizing ordinary/public/meta/import-all lines.
def imports(p):
 t=p.read_text();c=[];i=depth=0;quoted=False
 while i<len(t):
  if depth:
   if t.startswith('/-',i):depth+=1;i+=2
   elif t.startswith('-/',i):depth-=1;i+=2
   else:c.append('\n'if t[i]=='\n'else ' ');i+=1
  elif quoted:
   if t[i]=='\\':i+=2
   elif t[i]=='"':quoted=False;i+=1
   else:c.append('\n'if t[i]=='\n'else ' ');i+=1
  elif t.startswith('/-',i):depth=1;i+=2
  elif t.startswith('--',i):j=t.find('\n',i);i=len(t)if j<0 else j
  elif t[i]=='"':quoted=True;i+=1
  else:c.append(t[i]);i+=1
 return [n for line in ''.join(c).splitlines()for x in [re.match(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.*)',line)]if x for n in x.group(1).split()]
roots=[base]+[base/'.lake/packages'/n for n in m['dependencyRevisions']];closure={};leaves=set();todo=list(local)
while todo:
 n=todo.pop()
 if n in closure or n in leaves:continue
 p=local.get(n)or next((r/(n.replace('.','/')+'.lean')for r in roots if(r/(n.replace('.','/')+'.lean')).is_file()),None)
 if p is None:leaves.add(n);continue
 assert not any(n==s or n.startswith(s+'.')for s in m['excludedImportPrefixes'])
 closure[n]={'source':str(p),'imports':imports(p)};todo+=imports(p)
assert all(n.split('.')[0]in['Lean','Init','Std','Lake']for n in leaves)
assert len(closure)==m['replay']['expectedSourceModules']and len(leaves)==m['replay']['expectedCompilerLeaves']
put(out/'closure.json',{'modules':closure,'compilerLibraryLeaves':sorted(leaves)})
def frame():
 f={'repos':{},'compiler':{'path':str(compiler),'sha256':sha(compiler)},'stdRoots':{p:sha(p)for p in m['stdRoots']},'archive':{},'sources':{},'canonicalArtifacts':{}};indices={}
 expected={research:head,base:m['baseCommit'],**{base/'.lake/packages'/n:r for n,r in m['dependencyRevisions'].items()}}
 assert len(m['dependencyRevisions'])==12 and f['compiler']==m['compiler']and f['stdRoots']==m['stdRoots']and len(f['stdRoots'])==6
 assert sha(base/'lake-manifest.json')==m['lakeManifestSha256']and(base/'lean-toolchain').read_text().strip()==m['toolchain']
 assert sha(evidence/'README.md')==m['readmeSha256']
 for p,rev in expected.items():
  s,index=state(p);assert s['head']==rev and not s['status'];f['repos'][str(p)]=s;indices[p]=index
 for filename in ['MarkedLab.lean','ImportAudit.lean.txt','README.md','manifest.json']:
  p=evidence/filename;b=p.read_bytes();oid=blob(b);rel=str(p.relative_to(research));assert indices[research][rel]==oid and git(research,'rev-parse',head+':'+rel).decode().strip()==oid
  f['archive'][filename]={'sha256':sha(p),'gitBlob':oid}
 for n,v in specs.items():
  assert sha(local[n])==v['sha256']and git(research,'rev-parse',v['commit']+':'+v['path']).decode().strip()==v['gitBlob']
  assert hashlib.sha256(git(research,'show',v['gitBlob'])).hexdigest()==v['sha256']
  f['sources'][n]={**v,'actualSourceSHA256':sha(local[n])}
 for n,v in closure.items():
  if n in local:continue
  p=Path(v['source']);r=next(r for r in reversed(roots)if p.is_relative_to(r));b=p.read_bytes();oid=blob(b);assert indices[r][str(p.relative_to(r))]==oid
  f['sources'][n]={'sha256':sha(p),'gitBlob':oid}
  if r==base:
   a=base/'.lake/build/lib/lean'/n.replace('.','/');f['canonicalArtifacts'][n]={str(q):sha(q)for q in sorted(a.parent.glob(a.name+'.*'))if q.is_file()};assert a.with_suffix('.olean').is_file()
 return f
before=frame();put(out/'before.json',before);results=[];done={};totalReports=0;env=os.environ.copy();env['LEAN_NUM_THREADS']='2'
env['LEAN_PATH']=':'.join([str(out),str(base/'.lake/build/lib/lean')]+[str(p/'.lake/build/lib/lean')for p in roots[1:]])
try:
 for n in m['replay']['moduleOrder']:
  needed=set();todo=[d for d in imports(local[n])if d in local]
  while todo:
   d=todo.pop()
   if d in needed:continue
   needed.add(d);todo += [v for v in imports(local[d])if v in local]
  assert needed<=done.keys();consumed={str(out/(d+'.'+s)):sha(out/(d+'.'+s))for d in sorted(needed)for s in suffixes}
  assert all(not Path(p).is_symlink()and done[d][str(out/(d+'.'+s))]==consumed[str(out/(d+'.'+s))]for d in needed for s in suffixes for p in [str(out/(d+'.'+s))])
  assert sha(local[n])==specs[n]['sha256']
  argv=[str(compiler),'-j2','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-Dweak.linter.mathlibStandardSet=true','-Dweak.linter.redundantVisibility=true','--root='+str(src),'-o',str(out/(n+'.olean')),str(local[n])]
  current=frame();assert current==before;put(out/(n+'-before.json'),current)
  put(out/(n+'-input.json'),{'frameSHA256':sha(out/(n+'-before.json')),'argv':argv,'cwd':str(research),'LEAN_PATH':env['LEAN_PATH'],'sourceGitRef':specs[n],'sourceSHA256':sha(local[n]),'freshImportedArtifacts':consumed,'defaultProofLimits':True,'wallCapSeconds':240})
  start=time.monotonic()
  with(out/(n+'.log')).open('w')as log:
   try:child=subprocess.run(argv,cwd=research,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=240)
   except subprocess.TimeoutExpired:put(out/'timeout.json',{'module':n,'wallCapSeconds':240,'acceptance':False});raise
  row={'module':n,'exit':child.returncode,'seconds':time.monotonic()-start,'sourceSHA256':sha(local[n]),'inputSHA256':sha(out/(n+'-input.json')),'logSHA256':sha(out/(n+'.log')),'outputs':{}};results.append(row);put(out/'results.json',results);assert child.returncode==0
  emitted={str(out/(n+'.'+s)):sha(out/(n+'.'+s))for s in(['olean']if n=='ImportAudit'else suffixes)};row['outputs']=emitted;put(out/'results.json',results)
  assert not re.search(r'\b(warning|error):',(out/(n+'.log')).read_text())
  reports=re.findall(r'depends on axioms: \[([^\]]*)\]|does not depend on any axioms',(out/(n+'.log')).read_text(),re.S);assert len(reports)==m['replay']['printedAxiomReports'][n];totalReports+=len(reports)
  assert all({x.strip()for x in a.replace('\n','').split(',')if x.strip()}<=set(m['allowedAxioms'])for a in reports)
  assert all(sha(p)==v for p,v in consumed.items());done[n]=emitted
  if n=='ImportAudit':assert all(not(out/(n+'.'+s)).exists()for s in suffixes[1:])
finally:
 after=frame();put(out/'after.json',after);assert before==after
assert len(results)==8 and sum(len(r['outputs'])for r in results)==36 and totalReports==m['replay']['expectedPrintedAxiomReports']==56
PYREPLAY
```
