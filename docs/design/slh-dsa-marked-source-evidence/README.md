# Shared signature observation, actual source caps and native construction replay

The live generic observer retains actual keys and the existing raw outcome with arbitrary
additive cost and cache. The live Enforcement owner supplies one generic absorbing guard
and its four proved laws. The real-FIPS Joint theorem applies its actual signing-lifetime
and joint adversary-work hypotheses to the SAME full byte-source execution, retaining keys,
raw replies, candidate/verdict, actual counts and physical cache jointly.

The Marked602 count/observer conclusions and C0 construction171 fixtures remain exact.
The generic relative audit retains its arbitrary result and independent event interface.
The two unchanged weak-key theorem owners are rebuilt first from their separately accepted
source bytes; this integration does not modify or re-prove their keygen/continuation results.
The consolidated ordinary guard audit covers all four generic laws, their full original
Nat-pair conclusions, scalar/vector probability clients and arbitrary incoming runtime state.

CURRENT replay selects the guard/free archives as current reexport shims, never the old
frozen395/88 bodies. One fresh live Enforcement producer precedes every direct/transitive
consumer. Counted, both weak owners, Joint, both shims, RelativeKernel and MarkedLab are rebuilt
from source; every producer contributes all five fresh variants before each consumer.
Historical56697 receipts remain tied to their exact old sources/dependencies and are unchanged.

The guard/B/Marked/shim working-owner transfer is +89 physical lines (+436 Enforce,
+113 Joint, +1 Marked, -384/-77 archive modules). This is not a main-to-final-PR compression claim. Current integration
recorded replay is UNRUN. No byte/partial-native coupling, win-local policy affordability,
security-bound improvement or final127 result follows from this replay.

Run only from a CLEAN recorded private candidate or adopted checkout with its full commit
and a NEW ABSENT output. Require 16 scoped commands (12 modules/4 ordinary NONMODULE audits),
64 fresh outputs, 84 standard-only reports including exactly 2 empty reports, no warnings,
and identical protected frames before EACH command and afterward. Default proof limits,
-j2 and 240-second watchdogs apply. No Lake/cache update or repository write is performed.

```bash
research=$(GIT_OPTIONAL_LOCKS=0 GIT_NO_LAZY_FETCH=1 git rev-parse --show-toplevel)
base=/tmp/vcvio-slhdsa-integration
recorded_head=REPLACE_WITH_ACTUAL_FULL_COMMIT_SHA
out=/tmp/slhdsa-live-guard-B-REPLACE_WITH_NEW_ABSENT_LABEL
python3 - "$research" "$base" "$out" "$recorded_head" <<'PYREPLAY'
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
os.environ.update(GIT_OPTIONAL_LOCKS='0',GIT_NO_LAZY_FETCH='1')
research,base,out=map(Path,sys.argv[1:4]);head=sys.argv[4]
evidence=research/'docs/design/slh-dsa-marked-source-evidence';m=json.loads((evidence/'manifest.json').read_text());compiler=Path(m['compiler']['path'])
assert re.fullmatch('[0-9a-f]{40}',head)and out.is_absolute();out.mkdir(exist_ok=False);src=out/'src';src.mkdir();lib=out/'lib';lib.mkdir()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def put(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
def git(p,*a):return subprocess.check_output(['git','--no-optional-locks','-C',str(p),*a])
def state(p):
 raw=git(p,'ls-files','--stage','-z');index={r.split(b'\t',1)[1].decode():r.split()[1].decode()for r in raw.split(b'\0')if r}
 return {'head':git(p,'rev-parse','HEAD').decode().strip(),'tree':git(p,'rev-parse','HEAD^{tree}').decode().strip(),'status':git(p,'status','--porcelain').decode(),'semanticIndex':hashlib.sha256(raw).hexdigest(),'rawIndex':sha(git(p,'rev-parse','--path-format=absolute','--git-path','index').decode().strip())},index
specs={n:{**v,'commit':m['frozenBasisCommit']if v['basis']else head}for n,v in m['sources'].items()};local={}
for n,v in specs.items():
 b=git(research,'show',v['commit']+':'+v['path']);assert blob(b)==v['gitBlob']and hashlib.sha256(b).hexdigest()==v['sha256'];p=src/(n.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);local[n]=p
order=m['replay']['order'];assert len(order)==len(specs)and set(order)==set(specs);suffixes=m['replay']['moduleArtifacts'];owned=[n.replace('.','/')for n in specs]
def union(p,q,rel):
 if p.is_dir():
  if any(n.startswith(rel+'/')for n in owned):
   q.mkdir()
   for child in sorted(p.iterdir()):union(child,q/child.name,rel+'/'+child.name)
  else:q.symlink_to(p,target_is_directory=True)
 elif not any(rel.startswith(n+'.')for n in owned):q.symlink_to(p)
for p in sorted((base/'.lake/build/lib/lean').iterdir()):union(p,lib/p.name,p.name)
packages=[base/'.lake/packages'/n for n in m['dependencyRevisions']];libs=[lib]+[p/'.lake/build/lib/lean'for p in packages]
for p in libs[1:]+[compiler.parent.parent/'lib/lean']:
 for n in owned:
  assert all(not(p/(n+'.'+s)).exists()for s in suffixes)
for n in owned:
 assert not(lib/n).parent.is_symlink()and all(not(lib/(n+'.'+s)).exists()for s in suffixes)
links={str(p.relative_to(lib)):str(p.readlink())for p in lib.rglob('*')if p.is_symlink()}
def imports(p):
 t=p.read_text();c=[];i=depth=0;quoted=False
 while i<len(t):
  if depth:
   if t.startswith('/-',i):depth+=1;i+=2
   elif t.startswith('-/',i):depth-=1;i+=2
   else:c.append('\n'if t[i]=='\n'else' ');i+=1
  elif quoted:
   if t[i]=='\\':i+=2
   elif t[i]=='"':quoted=False;i+=1
   else:c.append('\n'if t[i]=='\n'else' ');i+=1
  elif t.startswith('/-',i):depth=1;i+=2
  elif t.startswith('--',i):j=t.find('\n',i);i=len(t)if j<0 else j
  elif t[i]=='"':quoted=True;i+=1
  else:c.append(t[i]);i+=1
 return[n for line in''.join(c).splitlines()for x in[re.match(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.*)',line)]if x for n in x.group(1).split()]
roots=[base,*packages];closure={};leaves=set();todo=list(specs)
while todo:
 n=todo.pop()
 if n in closure or n in leaves:continue
 p=local.get(n)or next((r/(n.replace('.','/')+'.lean')for r in roots if(r/(n.replace('.','/')+'.lean')).is_file()),None)
 if p is None:leaves.add(n);continue
 assert not any(n==s or n.startswith(s+'.')for s in m['excludedImports']);closure[n]={'path':str(p),'imports':imports(p)};todo+=imports(p)
assert all(n.split('.')[0]in['Lean','Init','Std','Lake']for n in leaves);put(out/'closure.json',{'modules':closure,'compilerLeaves':sorted(leaves)})
def bound(p,repo,index,rev):
 b=p.read_bytes();oid=blob(b);rel=str(p.relative_to(repo));assert index[rel]==oid and git(repo,'rev-parse',rev+':'+rel).decode().strip()==oid
 return{'sha256':sha(p),'gitBlob':oid}
def frame():
 f={'repos':{},'compiler':{'path':str(compiler),'sha256':sha(compiler)},'stdRoots':{p:sha(p)for p in m['stdRoots']},'payload':{},'sources':{},'normalArtifacts':{}};indices={}
 expected={research:head,base:m['canonicalCommit'],**{base/'.lake/packages'/n:v for n,v in m['dependencyRevisions'].items()}}
 assert len(expected)==14 and f['compiler']==m['compiler']and f['stdRoots']==m['stdRoots']and len(f['stdRoots'])==6
 assert sha(base/'lake-manifest.json')==m['lakeManifestSHA256']
 for repo,rev in expected.items():
  s,index=state(repo);assert s['head']==rev and not s['status'];f['repos'][str(repo)]=s;indices[repo]=index
 for rel,expectedSha in m['payloadFiles'].items():
  p=research/rel;assert sha(p)==expectedSha;f['payload'][rel]=bound(p,research,indices[research],head)
 rel=str((evidence/'manifest.json').relative_to(research));f['payload'][rel]=bound(evidence/'manifest.json',research,indices[research],head)
 assert all(not(research/rel).exists()for rel in m['retiredPaths'])
 for n,v in specs.items():
  assert sha(local[n])==v['sha256']and git(research,'rev-parse',v['commit']+':'+v['path']).decode().strip()==v['gitBlob'];f['sources'][n]={**v,'actualSourceSHA256':sha(local[n])}
 for n,v in closure.items():
  if n in local:continue
  p=Path(v['path']);repo=next(r for r in reversed(roots)if p.is_relative_to(r));f['sources'][n]=bound(p,repo,indices[repo],expected[repo])
  if repo==base:
   a=base/'.lake/build/lib/lean'/n.replace('.','/');assert Path(str(a)+'.olean').is_file();f['normalArtifacts'][n]={str(q):sha(q)for q in sorted(a.parent.glob(a.name+'.*'))if q.is_file()}
 assert links=={str(p.relative_to(lib)):str(p.readlink())for p in lib.rglob('*')if p.is_symlink()};return f
before=frame();put(out/'before.json',before);done={};results=[];total=0;empty=0;env={**os.environ,'LEAN_NUM_THREADS':'2','LEAN_PATH':':'.join(map(str,libs))}
try:
 for n in order:
  needed=set();todo=list(closure[n]['imports'])
  while todo:
   dep=todo.pop()
   if dep in needed:continue
   needed.add(dep);todo+=closure[dep]['imports']if dep in closure else[]
  needed&=set(local);assert needed<=done.keys();consumed={p:h for dep in needed for p,h in done[dep].items()}
  assert all(not Path(p).is_symlink()and sha(p)==h for p,h in consumed.items());assert len(consumed)==5*len(needed)
  current=frame();assert current==before;tag=n.rsplit('.',1)[-1];put(out/(tag+'-before.json'),current)
  target=lib/(n.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True);assert all(not Path(str(target)[:-6]+'.'+s).exists()for s in suffixes)
  argv=[str(compiler),'-j2','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-Dweak.linter.mathlibStandardSet=true','-Dweak.linter.redundantVisibility=true','--root='+str(src),'-o',str(target),str(local[n])]
  put(out/(tag+'-input.json'),{'argv':argv,'cwd':str(research),'LEAN_PATH':env['LEAN_PATH'],'sourceSHA256':sha(local[n]),'sourceGitRef':specs[n],'beforeFrameSHA256':sha(out/(tag+'-before.json')),'freshImportedArtifacts':consumed,'defaultProofLimits':True,'wallCapSeconds':240})
  start=time.monotonic()
  with(out/(tag+'.log')).open('w')as log:
   try:child=subprocess.run(argv,cwd=research,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=240)
   except subprocess.TimeoutExpired:put(out/'timeout.json',{'module':n,'acceptance':False});raise
  row={'module':n,'exit':child.returncode,'seconds':time.monotonic()-start,'sourceSHA256':sha(local[n]),'inputSHA256':sha(out/(tag+'-input.json')),'logSHA256':sha(out/(tag+'.log'))};results.append(row);put(out/'results.json',results);assert child.returncode==0
  text=(out/(tag+'.log')).read_text();assert not re.search(r'\b(warning|error):',text);reports=re.findall(r'depends on axioms: \[([^\]]*)\]|does not depend on any axioms',text,re.S);assert len(reports)==specs[n]['axiomReports'];total+=len(reports);empty+=sum(not a.strip()for a in reports)
  assert all({v.strip()for v in a.replace('\n','').split(',')if v.strip()}<=set(m['allowedAxioms'])for a in reports)
  emitted={str(Path(str(target)[:-6]+'.'+s)):sha(Path(str(target)[:-6]+'.'+s))for s in(suffixes if specs[n]['module']else['olean'])};row['outputs']=emitted;put(out/'results.json',results)
  assert specs[n]['module']or all(not Path(str(target)[:-6]+'.'+s).exists()for s in suffixes[1:]);assert all(sha(p)==h for p,h in consumed.items());done[n]=emitted
  finished=frame();put(out/(tag+'-after.json'),finished);assert before==finished
finally:
 after=frame();put(out/'after.json',after);assert before==after
assert len(results)==m['replay']['commands']and sum(len(x['outputs'])for x in results)==m['replay']['outputs']and total==m['replay']['axiomReports']and empty==m['replay']['emptyReports']
PYREPLAY
```
