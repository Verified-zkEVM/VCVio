/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public meta import HashSigTest.SLHDSA.Refactor.Capture
public import HashSigTest.SLHDSA.Refactor.Recovery.AuditInputs
public import HashSig
import Lean.Data.Json

/-! # Literal signature recovery contracts

The archive retains complete quantified expressions and the finite response/index universe map.
The runtime audit checks the actual file, the whole original object and every structural control.
-/

open Lean

public section

-- Expand one loader expression in each execution phase without a local phase-crossing edge.
local macro "recoveryValidatedBundle%(" mode:term ")" : term => `(do
  let result ← IO.Process.output { cmd := "python3", args :=
    #["-I", "-B", "-c", r####"
"""Finite structural audit embedded in Contracts.lean; no standalone production owner."""
import ast, copy, hashlib, json, sys
from pathlib import Path
FIXTURE_SHA = 'e6a473abe098c171c38611de7e4f421c43fb7db9f272e8b99fac2d9d36283537'
DECODER_SHA = '0a866bf14558b77a7aecbb646bdbd0c0d03ceb2e9b99f1fa544b7b4b8468d632'
ORIGINAL_CANONICAL_SHA = 'e5a39b2361776594310fea5be2f1bb7ebfc1e70addfa69935974954a1d5638bf'

def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()

def materialize(value):
    return json.loads(json.dumps(value, ensure_ascii=False))

def at(value, path):
    for index in path:
        value = value[index]
    return value

def name_of(value):
    if value == ['anonymous']:
        return ''
    assert value[0] in ['str', 'num'] and len(value) == 3
    prefix = name_of(value[1])
    return (prefix + '.' if prefix else '') + str(value[2])

def walk(value, path=()):
    if isinstance(value, list):
        if len(value) == 3 and value[0] == 'const':
            yield (path, value)
        for index, child in enumerate(value):
            yield from walk(child, path + (index,))

def prepare(fixture, decode):
    assert (
        set(fixture) == {'format', 'originalFileSHA256', 'originalTopMetadata', 'nodes',
        'contracts', 'exactEventProtocol'}
    )
    assert fixture['format'] == 'f6-original-goals-json-dag-storage-proposal-v1'
    assert (
        fixture['originalFileSHA256'] ==
        'a2d2fd815ca8a4f9d025c7a8039167dbedf1517aea2fff02467befa893bd2b96'
    )
    expanded = decode(fixture)
    original = copy.deepcopy(fixture['originalTopMetadata'])
    original['entries'] = []
    assert len(fixture['contracts']) == 42
    for number, contract in enumerate(fixture['contracts'], 1):
        entry = copy.deepcopy(contract)
        root = entry.pop('typeRoot')
        source = entry.pop('source')
        kind = entry.pop('kind')
        assert (
            type(root) is int and 0 <= root < len(expanded) and (source == entry['original'])
            and (kind == 'theorem')
        )
        assert entry['contract'] == f'P5Continuation.ConcreteGoal.goal{number}'
        entry['closedGoal'] = materialize(expanded[root])
        original['entries'].append(entry)
    assert hashlib.sha256(canonical(original)).hexdigest() == ORIGINAL_CANONICAL_SHA
    protocol = fixture['exactEventProtocol']
    sites = protocol['sites']
    assert (
        len(sites) == 39 and protocol['schemaCount'] == 42 and (protocol['changedConstSiteCount'
        ] == 39)
    )
    assert (
        protocol['retainedRowsWithoutAnyConstChange'] == [36, 37, 38] and protocol[
        'normalizationOrAlphaOrTermRewrite'] is False
    )
    role = protocol['namedMaps']
    assert len(role) == 1 and role[0]['name'] == 'SignatureAlg.SigningView.Event'
    assert (
        canonical(role[0]['oldLevelOrder']) == canonical(['u_1']) and canonical(role[0][
        'newLevelOrder']) == canonical(['r', 'idx']) and (canonical(role[0]['preservedRole'])
        == canonical({'old:u_1': 'new:r'})) and (canonical(role[0]['insertedIndex']) ==
        canonical(['zero']))
    )
    assert (
        canonical(role[0]['actualOccurrenceOldVector']) == canonical([['zero']]) and canonical(
        role[0]['actualOccurrenceNewVector']) == canonical([['zero'], ['zero']])
    )
    actual = []
    for number, entry in enumerate(original['entries'], 1):
        for path, node in walk(entry['closedGoal']):
            if name_of(node[1]) == 'SignatureAlg.SigningView.Event':
                (
                    actual.append({'row': number, 'contract': entry['contract'], 'original':
                    entry['original'], 'path': list(path), 'oldConst': node, 'newConst': [
                    'const', copy.deepcopy(node[1]), [['zero'], ['zero']]]})
                )
    assert canonical(actual) == canonical(sites)
    for entry in original['entries']:
        assert (
            hashlib.sha256(canonical(entry['closedGoal'])).hexdigest() == entry[
            'closedGoalSHA256']
        )
    return (original, sites)

def forward(original, sites):
    out = copy.deepcopy(original)
    for site in sites:
        goal = out['entries'][site['row'] - 1]['closedGoal']
        assert canonical(at(goal, site['path'])) == canonical(site['oldConst'])
        at(goal, site['path'][:-1])[site['path'][-1]] = copy.deepcopy(site['newConst'])
    return out

def validate(candidate, original, sites):
    """Pure finite validator shared by the unchanged positive and every schema mutant."""
    assert isinstance(candidate, dict) and set(candidate) == set(original)
    assert len(candidate['entries']) == 42
    out = copy.deepcopy(candidate)
    actual = []
    for number, entry in enumerate(out['entries'], 1):
        for path, node in walk(entry['closedGoal']):
            if name_of(node[1]) == 'SignatureAlg.SigningView.Event':
                actual.append((number, list(path), node))
    assert (
        canonical(actual) == canonical([(s['row'], s['path'], s['newConst']) for s in sites])
    ), 'Changed/extra/missing/moved/named/arity/role site'
    for site in sites:
        goal = out['entries'][site['row'] - 1]['closedGoal']
        assert canonical(at(goal, site['path'])) == canonical(site['newConst'])
        at(goal, site['path'][:-1])[site['path'][-1]] = copy.deepcopy(site['oldConst'])
    assert (
        canonical(out) == canonical(original)
    ), 'Original AST/levels/name/binder/budget/hypothesis/RHS changed'
    return out

def schema_negatives(transformed, original, sites):
    labels = []

    def reject(label, mutation):
        candidate = copy.deepcopy(transformed)
        mutation(candidate)
        try:
            validate(candidate, original, sites)
        except (AssertionError, KeyError, IndexError, TypeError, ValueError):
            labels.append(label)
            return
        raise ValueError('F6 schema negative accepted: ' + label)
    for site in sites:
        row, path = (site['row'], site['path'])
        (
            reject(f'row{row}-wrong-inserted-index', lambda x, row=row, path=path: at(x[
            'entries'][row - 1]['closedGoal'], path)[2].__setitem__(1, ['succ', ['zero']]))
        )
        (
            reject(f'row{row}-wrong-retained-response-role', lambda x, row=row, path=path: at(x[
            'entries'][row - 1]['closedGoal'], path)[2].__setitem__(0, ['succ', ['zero']]))
        )
    site = sites[0]

    def node(x):
        return at(x['entries'][0]['closedGoal'], site['path'])
    reject('missing-new-index-arity', lambda x: node(x)[2].pop())
    reject('extra-duplicate-index-arity', lambda x: node(x)[2].append(['zero']))
    reject('renamed-target-constant', lambda x: node(x)[1].__setitem__(2, 'WrongEvent'))
    reject('missing-occurrence', lambda x: node(x).__setitem__(0, 'not_const'))
    (
        reject('duplicate-extra-occurrence', lambda x: x['entries'][0].__setitem__('closedGoal'
        , ['app', x['entries'][0]['closedGoal'], copy.deepcopy(site['newConst'])]))
    )
    (
        reject('moved-occurrence', lambda x: x['entries'][0].__setitem__('closedGoal', ['app', [
        'bvar', 0], x['entries'][0]['closedGoal']]))
    )
    (
        reject('unknown-new-level-parameter', lambda x: node(x)[2].__setitem__(1, ['param', [
        'str', ['anonymous'], 'unexpected']]))
    )
    (
        reject('changed-original-level-names', lambda x: x['entries'][35]['levelNames'].append([
        'str', ['anonymous'], 'unexpected']))
    )
    (
        reject('changed-original-forall-binder', lambda x: x['entries'][0]['closedGoal'][1].
        __setitem__(2, 'renamedVp'))
    )
    (
        reject('changed-original-goal-body', lambda x: x['entries'][35].__setitem__('closedGoal'
        , ['sort', ['zero']]))
    )
    assert len(labels) == len(set(labels)) == 88
    return labels

def main():
    fixturePath, decoderPath, mode = sys.argv[1:]
    assert mode in ['load', 'audit']
    raw = Path(fixturePath).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == FIXTURE_SHA, 'actual fixture SHA256'
    decoderSource = Path(decoderPath).read_bytes()
    assert hashlib.sha256(decoderSource).hexdigest() == DECODER_SHA, 'existing decoder SHA256'
    tree = ast.parse(decoderSource)
    matches = (
        [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'decode_dag']
    )
    assert len(matches) == 1
    scope = {}
    (
        exec(compile(ast.Module(body=matches, type_ignores=[]), 'existing-pinned-decode_dag',
        'exec'), scope)
    )
    original, sites = prepare(json.loads(raw), scope['decode_dag'])
    transformed = forward(original, sites)
    assert canonical(validate(transformed, original, sites)) == canonical(original)
    for number in [36, 37, 38]:
        assert (
            canonical(transformed['entries'][number - 1]) == canonical(original['entries'][
            number - 1])
        )
    labels = schema_negatives(transformed, original, sites) if mode == 'audit' else []
    result = (
        {'status': 'F6_FULL_FIXTURE_STRUCTURAL_AND_88_NEGATIVES_PASS' if mode == 'audit' else
        'F6_LITERAL_SCHEMA_LOAD_PASS', 'schemas': 42, 'sites': 39, 'negativeCount': len(labels)
        , 'negativeLabels': labels, 'originalCanonicalSHA256': ORIGINAL_CANONICAL_SHA}
    )
    if mode == 'load':
        result['entries'] = transformed['entries']
    print(json.dumps(result, separators=(',', ':'), ensure_ascii=False))
if __name__ == '__main__':
    main()
"####,
      "docs/design/slh-dsa-reuse-evidence/f6/goal-contracts.json",
      "scripts/check-slh-dsa-r0.py", $mode] }
  unless result.exitCode == 0 do
    throw (IO.userError s!"F6 fixture integrity mismatch: {result.stderr}")
  match Json.parse result.stdout with
  | .ok bundle => return bundle
  | .error reason => throw (IO.userError s!"F6 fixture integrity mismatch: {reason}"))

private def validatedBundle (mode : String) : IO Json := recoveryValidatedBundle%(mode)

namespace SLHDSA.Refactor.Recovery.Contracts

/-- Check the literal archive and structural controls before recording completion. -/
def auditFixture (complete : String → IO Unit) : IO Unit := do
  let result ← validatedBundle "audit"
  let .ok status := result.getObjValAs? String "status" |
    throw (IO.userError "F6 fixture integrity mismatch: missing audit status")
  let .ok schemas := result.getObjValAs? Nat "schemas" |
    throw (IO.userError "F6 fixture integrity mismatch: missing schema count")
  let .ok sites := result.getObjValAs? Nat "sites" |
    throw (IO.userError "F6 fixture integrity mismatch: missing event count")
  let .ok controls := result.getObjValAs? Nat "negativeCount" |
    throw (IO.userError "F6 fixture integrity mismatch: missing control count")
  unless status == "F6_FULL_FIXTURE_STRUCTURAL_AND_88_NEGATIVES_PASS" &&
      schemas == 42 && sites == 39 && controls == 88 do
    throw (IO.userError "F6 fixture integrity mismatch: incomplete audit")
  complete "f6-fixture"

end SLHDSA.Refactor.Recovery.Contracts

public meta section

open Elab Command Meta SLHDSA.Refactor.R0

namespace SLHDSA.Refactor.Recovery.Contracts

/-- Decode complete literal types and original universes after archive validation. -/
def readGoals : CommandElabM (Array (Name × List Name × Expr)) := do
  let result ← (recoveryValidatedBundle%("load") : IO Json)
  let status ← ofExcept (result.getObjValAs? String "status")
  unless status == "F6_LITERAL_SCHEMA_LOAD_PASS" do
    throwError "Incomplete canonical type validation"
  let entries ← ofExcept (result.getObjValAs? (Array Json) "entries")
  unless entries.size == 42 do throwError "Expected exactly42 literal recovery types"
  let mut goals := #[]
  for index in [:entries.size] do
    let entry := entries[index]!
    let contract ← ofExcept (entry.getObjValAs? String "contract")
    unless contract == s!"P5Continuation.ConcreteGoal.goal{index + 1}" do
      throwError "Recovery contract order changed"
    let encoded ← ofExcept (entry.getObjVal? "closedGoal")
    let type ← ofExcept (decodeExpr encoded)
    unless (← ofExcept (encodeExpr type)) == encoded do throwError "Literal type roundtrip changed"
    let rawLevels ← ofExcept (entry.getObjValAs? (Array Json) "levelNames")
    let levels ← ofExcept (rawLevels.toList.mapM decodeName)
    if type.hasLooseBVars || type.hasFVar || type.hasMVar || type.hasLevelMVar then
      throwError "Recovery type is not closed"
    goals := goals.push (contract.toName, levels, type)
  return goals

end SLHDSA.Refactor.Recovery.Contracts

run_cmd do
  let goals ← SLHDSA.Refactor.Recovery.Contracts.readGoals
  let mainModule ← getMainModule
  for index in [:goals.size] do
    let (_, levels, value) := goals[index]!
    let userName := Name.str `SLHDSA.Refactor.Recovery.Contracts s!"checkedGoal{index + 1}"
    let name := mkPrivateNameCore mainModule userName
    if ((← getEnv).find? name).isSome then throwError "Duplicate internal schema check"
    liftCoreM <| addAndCompile (.defnDecl
      { name, levelParams := levels, type := mkSort .zero, value,
        hints := .opaque, safety := .safe })
  logInfo "ALL42_PRIVATE_SAFE_PROP_DATA_TYPES_CHECKED_NO42_PROOF_CLAIM"
