/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Traversal
public import HashSig.SLHDSA.SHAKE128s.Proof.GraphFreshSampling
meta import VCVio.Algorithms.Sha2
import all HashSigTest.SLHDSA.Refactor.Capture
import all HashSig.SLHDSA.SHAKE128s.Proof.GraphFreshSampling
import all HashSig.SLHDSA.SHAKE128s.Statement.Game
import all HashSig.SLHDSA.SHAKE128s.Statement.RandomOracleModel
import all HashSig.SLHDSA.SHAKE128s.Statement.Scheme
import all VCVio.EvalDist.Defs.Measure.Core
import all VCVio.EvalDist.EvalDistEq
import all VCVio.EvalDist.PFunctorMeasure.Core
import all VCVio.EvalDist.ProbabilityNotation
import all VCVio.OracleComp.Constructions.SampleableType.Basic
import all VCVio.OracleComp.EvalDist.AnswerMeasure
import all VCVio.OracleComp.OracleComp
import all VCVio.OracleComp.OracleQuery
import all VCVio.OracleComp.OracleSpec
import all VCVio.OracleComp.ProbComp.Basic
import all VCVio.OracleComp.QueryTracking.CachingOracle
import all VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import all VCVio.OracleComp.QueryTracking.RandomOracle.Traversal
import all VCVio.OracleComp.QueryTracking.Structures
import all VCVio.OracleComp.SimSemantics.QueryImpl.Basic
import all VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Byte-oracle specializations of stateful coordinate traversal

The generic traversal recovers the five concrete byte-oracle definitions and their five
complete state/cache laws. The theorem witnesses use the generic owner at exactly the concrete
input/output types, with the same coordinate lists and hypotheses.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.GraphSamplerCompatibility

variable {Index State : Type}

/-- The byte-oracle traversal has the generic free-program definition. -/
theorem evaluate_eq_byteTraversal (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (nodes : List Index) (state : State) :
    RandomOracleTraversal.evaluate input step nodes state =
      GraphFreshSampling.evaluate input step nodes state := by
  exact (GraphFreshSampling.evaluate_eq_traversal input step nodes state).symm

/-- Independent byte-oracle sampling retains the same entire state and cache. -/
theorem sample_eq_byteTraversal (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (nodes : List Index) (state : State)
    (cache : QueryCache HashSpec) :
    RandomOracleTraversal.sample input step nodes state cache =
      GraphFreshSampling.sample input step nodes state cache := by
  induction nodes generalizing state cache with
  | nil => rfl
  | cons node nodes ih =>
      simp only [RandomOracleTraversal.sample, GraphFreshSampling.sample]
      exact bind_congr fun output => ih (step node state output)
        (cache.cacheQuery (input node state) output)

/-- Programming a complete byte-answer table retains the same entire state and cache. -/
theorem program_eq_byteTraversal (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (outputs : Index → HashOutput)
    (nodes : List Index) (state : State) (cache : QueryCache HashSpec) :
    RandomOracleTraversal.program input step outputs nodes state cache =
      GraphFreshSampling.program input step outputs nodes state cache := by
  induction nodes generalizing state cache with
  | nil => rfl
  | cons node nodes ih =>
      exact ih (step node state (outputs node)) (cache.cacheQuery (input node state) (outputs node))

/-- The namespace-separation condition has the same quantifiers over all payload states. -/
theorem separated_iff_byteTraversal (input : Index → State → Bytes) :
    RandomOracleTraversal.Separated input ↔ GraphFreshSampling.Separated input := Iff.rfl

/-- Cache freshness ranges over every possible payload state at each remaining coordinate. -/
theorem freshFor_iff_byteTraversal (input : Index → State → Bytes) (nodes : List Index)
    (cache : QueryCache HashSpec) :
    RandomOracleTraversal.FreshFor input nodes cache ↔
      GraphFreshSampling.FreshFor input nodes cache := Iff.rfl

/-- The generic full-state/cache sampling law has the exact concrete byte-oracle type. -/
theorem evaluate_eq_sample (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (hseparated : GraphFreshSampling.Separated input)
    (nodes : List Index) (hnodup : nodes.Nodup) (state : State) (cache : QueryCache HashSpec)
    (hfresh : GraphFreshSampling.FreshFor input nodes cache) :
    (simulateQ randomOracle (GraphFreshSampling.evaluate input step nodes state)).run cache =
      GraphFreshSampling.sample input step nodes state cache := by
  simpa only [evaluate_eq_byteTraversal, sample_eq_byteTraversal] using
    RandomOracleTraversal.evaluate_eq_sample input step hseparated nodes hnodup state cache hfresh

/-- The generic table-locality law has the exact concrete byte-oracle type. -/
theorem program_congr (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (left right : Index → HashOutput)
    (nodes : List Index) (hagrees : ∀ node ∈ nodes, left node = right node)
    (state : State) (cache : QueryCache HashSpec) :
    GraphFreshSampling.program input step left nodes state cache =
      GraphFreshSampling.program input step right nodes state cache := by
  simpa only [program_eq_byteTraversal] using
    RandomOracleTraversal.program_congr input step left right nodes hagrees state cache

variable [DecidableEq Index]

/-- The generic outside-coordinate law has the exact concrete byte-oracle type. -/
theorem program_update_outside (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (outputs : Index → HashOutput)
    (nodes : List Index) (node : Index) (hnot : node ∉ nodes) (output : HashOutput)
    (state : State) (cache : QueryCache HashSpec) :
    GraphFreshSampling.program input step (Function.update outputs node output) nodes state cache =
      GraphFreshSampling.program input step outputs nodes state cache := by
  simpa only [program_eq_byteTraversal] using
    RandomOracleTraversal.program_update_outside
      input step outputs nodes node hnot output state cache

variable [Fintype Index]

/-- The generic full-table sampling law has the exact concrete byte-oracle type. -/
theorem evalDist_sample_eq_uniform_program (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (nodes : List Index)
    (hnodup : nodes.Nodup) (state : State) (cache : QueryCache HashSpec) :
    GraphFreshSampling.sample input step nodes state cache =ᵈ
      ((fun outputs => GraphFreshSampling.program input step outputs nodes state cache) <$>
        ($ᵗ (Index → HashOutput) : ProbComp (Index → HashOutput))) := by
  simpa only [sample_eq_byteTraversal, program_eq_byteTraversal] using
    RandomOracleTraversal.evalDist_sample_eq_uniform_program input step nodes hnodup state cache

/-- The generic lazy-oracle full-table law has the exact concrete byte-oracle type. -/
theorem evalDist_evaluate_eq_uniform_program (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (hseparated : GraphFreshSampling.Separated input)
    (nodes : List Index) (hnodup : nodes.Nodup) (state : State) (cache : QueryCache HashSpec)
    (hfresh : GraphFreshSampling.FreshFor input nodes cache) :
    (simulateQ randomOracle (GraphFreshSampling.evaluate input step nodes state)).run cache =ᵈ
      ((fun outputs => GraphFreshSampling.program input step outputs nodes state cache) <$>
        ($ᵗ (Index → HashOutput) : ProbComp (Index → HashOutput))) := by
  simpa only [evaluate_eq_byteTraversal, program_eq_byteTraversal] using
    RandomOracleTraversal.evalDist_evaluate_eq_uniform_program
      input step hseparated nodes hnodup state cache hfresh

end SLHDSA.SHAKE128s.GraphSamplerCompatibility

namespace SLHDSA.SHAKE128s.GraphSamplerCompatibility

/-! ## Closed construction contracts -/

open Lean Elab Command Meta SLHDSA.Refactor.R0

/-- Structural kernel contracts for the byte-oracle construction. -/
private meta def frozenConstruction : String :=
  String.join (#[
    "[[[1,\"name\"],[1,\"module\"],[1,\"levels\"],[1,\"levelNames\"],[1,\"shape\"],[1,\"type",
    "\"],[1,\"values\"],[1,\"dependencies\"],[1,\"axioms\"],[0,0,1,2,3,4,5,6,7,8],[1,\"expose",
    "dBody\"],[1,\"privateName\"],[1,\"protected\"],[1,\"meta\"],[1,\"noncomputable\"],[1,\"r",
    "educibility\"],[1,\"inline\"],[1,\"defeq\"],[1,\"backwardDefeq\"],[1,\"simpLemma\"],[1,",
    "\"simpUnfold\"],[1,\"matchPattern\"],[1,\"csimp\"],[1,\"extern\"],[0,10,11,12,13,14,15,1",
    "6,17,18,19,20,21,22,23],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.evaluate\"],[1,\"HashSi",
    "g.SLHDSA.SHAKE128s.Proof.GraphFreshSampling\"],[0],[1,\"definition\"],[1,\"Lean.Definiti",
    "onSafety.safe\"],[1,\"regular\"],[2,5],[0,30,31],[0,28,29,32],[1,\"forall\"],[1,\"str\"]",
    ",[1,\"anonymous\"],[0,36],[1,\"Index\"],[0,35,37,38],[1,\"implicit\"],[1,\"sort\"],[1,\"",
    "succ\"],[1,\"zero\"],[0,43],[0,42,44],[0,41,45],[1,\"State\"],[0,35,37,47],[1,\"input\"]",
    ",[0,35,37,49],[1,\"explicit\"],[1,\"num\"],[1,\"a\"],[0,35,37,53],[1,\"_@\"],[0,35,54,55",
    "],[1,\"_internal\"],[0,35,56,57],[1,\"_hyg\"],[0,35,58,59],[2,0],[0,52,60,61],[1,\"bvar",
    "\"],[2,1],[0,63,64],[1,\"const\"],[1,\"SLHDSA\"],[0,35,37,67],[1,\"SHAKE128s\"],[0,35,68",
    ",69],[1,\"Bytes\"],[0,35,70,71],[0,66,72,27],[0,34,62,51,65,73],[0,34,62,51,65,74],[1,\"",
    "step\"],[0,35,37,76],[2,2],[0,63,78],[1,\"HashOutput\"],[0,35,70,80],[0,66,81,27],[2,4],",
    "[0,63,83],[0,34,62,51,82,84],[0,34,62,51,79,85],[0,34,62,51,79,86],[1,\"app\"],[1,\"List",
    "\"],[0,35,37,89],[0,44],[0,66,90,91],[2,3],[0,63,93],[0,88,92,94],[1,\"OracleComp\"],[0,",
    "35,37,96],[0,44,44,44],[0,66,97,98],[0,88,99,73],[1,\"HashSpec\"],[0,35,70,101],[0,66,10",
    "2,27],[0,88,100,103],[0,88,104,84],[0,34,62,51,94,105],[0,34,62,51,95,106],[0,34,77,51,8",
    "7,107],[0,34,50,51,75,108],[0,34,48,40,46,109],[0,34,39,40,46,110],[0,25,26,27,27,33,111",
    "],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.sample\"],[2,10],[0,30,114],[0,28,29,115],[1,",
    "\"OracleSpec\"],[0,35,37,117],[1,\"QueryCache\"],[0,35,118,119],[0,44,44],[0,66,120,121]",
    ",[0,88,122,73],[0,88,123,103],[1,\"ProbComp\"],[0,35,37,125],[0,66,126,27],[1,\"Prod\"],",
    "[0,35,37,128],[0,66,129,121],[0,63,31],[0,88,130,131],[0,88,132,124],[0,88,127,133],[0,3",
    "4,62,51,124,134],[0,34,62,51,94,135],[0,34,62,51,95,136],[0,34,77,51,87,137],[0,34,50,51",
    ",75,138],[0,34,48,40,46,139],[0,34,39,40,46,140],[0,113,26,27,27,116,141],[1,\"SLHDSA.SH",
    "AKE128s.GraphFreshSampling.program\"],[2,9],[0,30,144],[0,28,29,145],[1,\"outputs\"],[0,",
    "35,37,147],[0,34,62,51,94,82],[0,88,92,84],[2,6],[0,63,151],[0,88,130,152],[0,88,153,124",
    "],[0,34,62,51,124,154],[0,34,62,51,84,155],[0,34,62,51,150,156],[0,34,148,51,149,157],[0",
    ",34,77,51,87,158],[0,34,50,51,75,159],[0,34,48,40,46,160],[0,34,39,40,46,161],[0,143,26,",
    "27,27,146,162],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.Separated\"],[0,30,93],[0,28,29,",
    "165],[0,41,44],[0,34,50,51,75,167],[0,34,48,40,46,168],[0,34,39,40,46,169],[0,164,26,27,",
    "27,166,170],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.FreshFor\"],[0,30,78],[0,28,29,173]",
    ",[1,\"nodes\"],[0,35,37,175],[0,88,92,79],[1,\"cache\"],[0,35,37,178],[0,34,179,51,124,1",
    "67],[0,34,176,51,177,180],[0,34,50,51,75,181],[0,34,48,40,46,182],[0,34,39,40,46,183],[0",
    ",172,26,27,27,174,184],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.evaluate_eq_sample\"],[1",
    ",\"theorem\"],[0,187],[1,\"hseparated\"],[0,35,37,189],[1,\"GraphFreshSampling\"],[0,35,",
    "70,191],[1,\"Separated\"],[0,35,192,193],[0,66,194,27],[0,88,195,94],[0,88,196,79],[0,88",
    ",197,65],[1,\"hnodup\"],[0,35,37,199],[1,\"Nodup\"],[0,35,90,201],[0,66,202,91],[0,88,20",
    "3,131],[0,63,61],[0,88,204,205],[1,\"state\"],[0,35,37,207],[1,\"hfresh\"],[0,35,37,209]",
    ",[1,\"FreshFor\"],[0,35,192,211],[0,66,212,27],[2,8],[0,63,214],[0,88,213,215],[2,7],[0,",
    "63,217],[0,88,216,218],[0,88,219,152],[0,88,220,94],[0,88,221,205],[1,\"Eq\"],[0,35,37,2",
    "23],[0,45],[0,66,224,225],[0,88,130,215],[0,88,227,124],[0,88,127,228],[0,88,226,229],[1",
    ",\"StateT\"],[0,35,37,231],[1,\"run\"],[0,35,232,233],[0,66,234,121],[0,88,235,124],[0,8",
    "8,236,127],[0,88,237,215],[1,\"simulateQ\"],[0,35,37,239],[0,66,240,98],[0,88,241,73],[0",
    ",88,242,103],[0,66,232,121],[0,88,244,124],[0,88,245,127],[0,88,243,246],[1,\"instMonad",
    "\"],[0,35,232,248],[0,66,249,121],[0,88,250,124],[0,88,251,127],[1,\"PFunctor\"],[0,35,3",
    "7,253],[1,\"FreeM\"],[0,35,254,255],[0,35,256,248],[0,66,257,98],[1,\"toPFunctor\"],[0,3",
    "5,118,259],[0,66,260,121],[1,\"Nat\"],[0,35,37,262],[0,66,263,27],[0,88,261,264],[1,\"un",
    "ifSpec\"],[0,35,37,266],[0,66,267,27],[0,88,265,268],[0,88,258,269],[0,88,252,270],[0,88",
    ",247,271],[1,\"randomOracle\"],[0,35,118,273],[0,66,274,27],[0,88,275,73],[1,\"lam\"],[1",
    ",\"b\"],[0,35,37,278],[1,\"instDecidableEqList\"],[0,35,37,280],[0,66,281,91],[1,\"UInt8",
    "\"],[0,35,37,283],[0,66,284,27],[0,88,282,285],[1,\"instDecidableEqUInt8\"],[0,35,37,287",
    "],[0,66,288,27],[0,88,286,289],[0,88,290,65],[0,88,291,205],[0,277,279,51,73,292],[0,277",
    ",54,51,73,293],[0,88,276,294],[0,88,295,103],[1,\"t\"],[0,35,37,297],[1,\"Domain\"],[0,3",
    "5,118,299],[0,66,300,121],[0,88,301,73],[0,88,302,103],[1,\"FinEnum\"],[0,35,37,304],[1,",
    "\"SampleableType\"],[0,35,305,306],[0,66,307,27],[1,\"Range\"],[0,35,118,309],[0,66,310,",
    "121],[0,88,311,73],[0,88,312,103],[0,88,313,205],[0,88,308,314],[1,\"instBitVec\"],[0,35",
    ",305,316],[0,66,317,27],[1,\"HMul\"],[0,35,37,319],[1,\"hMul\"],[0,35,320,321],[0,66,322",
    ",98],[0,88,323,264],[0,88,324,264],[0,88,325,264],[1,\"instHMul\"],[0,35,37,327],[0,66,3",
    "28,91],[0,88,329,264],[1,\"instMulNat\"],[0,35,37,331],[0,66,332,27],[0,88,330,333],[0,8",
    "8,326,334],[1,\"OfNat\"],[0,35,37,336],[1,\"ofNat\"],[0,35,337,338],[0,66,339,91],[0,88,",
    "340,264],[1,\"nat\"],[0,342,214],[0,88,341,343],[1,\"instOfNatNat\"],[0,35,37,345],[0,66",
    ",346,27],[0,88,347,343],[0,88,344,348],[0,88,335,349],[1,\"messageDigestBytes\"],[0,35,7",
    "0,351],[0,66,352,27],[0,88,350,353],[0,88,318,354],[0,88,315,355],[1,\"instNonemptyOfInh",
    "abited\"],[0,35,37,357],[0,66,358,225],[0,88,359,314],[1,\"BitVec\"],[0,35,37,361],[1,\"",
    "instInhabited\"],[0,35,362,363],[0,66,364,27],[0,88,365,354],[0,88,360,366],[0,88,356,36",
    "7],[0,277,298,51,303,368],[0,88,296,369],[0,88,272,370],[0,88,371,215],[1,\"evaluate\"],",
    "[0,35,192,373],[0,66,374,27],[0,63,144],[0,88,375,376],[0,88,377,215],[0,88,378,218],[0,",
    "88,379,152],[0,88,380,84],[0,88,381,79],[0,88,372,382],[0,88,238,383],[0,88,384,65],[0,8",
    "8,230,385],[1,\"sample\"],[0,35,192,387],[0,66,388,27],[0,88,389,376],[0,88,390,215],[0,",
    "88,391,218],[0,88,392,152],[0,88,393,84],[0,88,394,79],[0,88,395,65],[0,88,386,396],[0,3",
    "4,210,51,222,397],[0,34,179,51,124,398],[0,34,208,51,131,399],[0,34,200,51,206,400],[0,3",
    "4,176,51,150,401],[0,34,190,51,198,402],[0,34,77,51,87,403],[0,34,50,51,75,404],[0,34,48",
    ",40,46,405],[0,34,39,40,46,406],[0,186,26,27,27,188,407],[1,\"SLHDSA.SHAKE128s.GraphFres",
    "hSampling.program_congr\"],[1,\"left\"],[0,35,37,410],[1,\"right\"],[0,35,37,412],[0,34,",
    "62,51,84,82],[0,88,92,131],[1,\"hagrees\"],[0,35,37,416],[1,\"node\"],[0,35,37,418],[1,",
    "\"Membership\"],[0,35,37,420],[1,\"mem\"],[0,35,421,422],[0,66,423,121],[0,88,424,218],[",
    "0,88,92,218],[0,88,425,426],[1,\"instMembership\"],[0,35,90,428],[0,66,429,91],[0,88,430",
    ",218],[0,88,427,431],[0,88,432,65],[0,88,433,205],[0,88,226,82],[0,88,84,65],[0,88,435,4",
    "36],[0,88,94,65],[0,88,437,438],[0,34,62,51,434,439],[0,34,419,51,152,440],[0,88,226,228",
    "],[1,\"program\"],[0,35,192,443],[0,66,444,27],[0,88,445,376],[0,88,446,215],[0,88,447,2",
    "18],[0,88,448,152],[0,88,449,131],[0,88,450,94],[0,88,451,65],[0,88,452,205],[0,88,442,4",
    "53],[0,88,449,84],[0,88,455,94],[0,88,456,65],[0,88,457,205],[0,88,454,458],[0,34,179,51",
    ",124,459],[0,34,208,51,152,460],[0,34,417,51,441,461],[0,34,176,51,415,462],[0,34,413,51",
    ",414,463],[0,34,411,51,149,464],[0,34,77,51,87,465],[0,34,50,51,75,466],[0,34,48,40,46,4",
    "67],[0,34,39,40,46,468],[0,409,26,27,27,188,469],[1,\"SLHDSA.SHAKE128s.GraphFreshSamplin",
    "g.program_update_outside\"],[1,\"inst\"],[0,35,37,472],[0,35,473,55],[1,\"HashSig\"],[0,",
    "35,474,475],[0,35,476,67],[0,35,477,69],[1,\"Proof\"],[0,35,478,479],[0,35,480,191],[2,1",
    "738780461],[0,52,481,482],[1,\"_hygCtx\"],[0,35,483,484],[0,35,485,59],[0,52,486,83],[1,",
    "\"instance\"],[1,\"DecidableEq\"],[0,35,37,489],[0,66,490,225],[0,88,491,65],[0,34,62,51",
    ",79,73],[0,34,62,51,79,493],[0,34,62,51,82,131],[0,34,62,51,94,495],[0,34,62,51,94,496],",
    "[1,\"hnot\"],[0,35,37,498],[1,\"Not\"],[0,35,37,500],[0,66,501,27],[0,88,502,434],[1,\"o",
    "utput\"],[0,35,37,504],[0,63,114],[0,88,130,506],[0,88,507,124],[0,88,226,508],[2,11],[0",
    ",63,510],[0,88,445,511],[0,88,512,506],[0,88,513,215],[0,88,514,218],[1,\"Function\"],[0",
    ",35,37,516],[1,\"update\"],[0,35,517,518],[0,45,45],[0,66,519,520],[0,88,521,511],[0,277",
    ",62,51,511,82],[0,88,522,523],[0,88,524,376],[0,88,525,152],[0,88,526,84],[0,88,527,79],",
    "[0,88,515,528],[0,88,529,131],[0,88,530,65],[0,88,531,205],[0,88,509,532],[0,88,515,152]",
    ",[0,88,534,131],[0,88,535,65],[0,88,536,205],[0,88,533,537],[0,34,179,51,124,538],[0,34,",
    "208,51,215,539],[0,34,505,51,82,540],[0,34,499,51,503,541],[0,34,419,51,152,542],[0,34,1",
    "76,51,415,543],[0,34,148,51,414,544],[0,34,77,51,497,545],[0,34,50,51,494,546],[0,34,487",
    ",488,492,547],[0,34,48,40,46,548],[0,34,39,40,46,549],[0,471,26,27,27,188,550],[1,\"SLHD",
    "SA.SHAKE128s.GraphFreshSampling.evalDist_sample_eq_uniform_program\"],[2,350024673],[0,5",
    "2,481,553],[0,35,554,484],[0,35,555,59],[0,52,556,83],[0,52,556,217],[1,\"Fintype\"],[0,",
    "35,37,559],[0,66,560,91],[0,88,561,79],[0,34,62,51,94,73],[0,34,62,51,94,563],[0,34,62,5",
    "1,82,152],[0,34,62,51,84,565],[0,34,62,51,84,566],[0,88,203,152],[0,88,568,205],[1,\"Eva",
    "lDistEq\"],[0,35,37,570],[0,66,571,121],[0,88,572,127],[0,88,573,127],[1,\"instEvalDistS",
    "emantics\"],[0,35,97,575],[0,66,576,121],[0,88,577,264],[0,88,578,268],[1,\"UniformAnswe",
    "rMeasure\"],[0,35,118,580],[1,\"toAnswerMeasure\"],[0,35,581,582],[0,66,583,121],[0,88,5",
    "84,264],[0,88,585,268],[0,35,581,266],[0,66,587,27],[0,88,586,588],[0,88,579,589],[0,88,",
    "574,590],[0,88,591,590],[0,88,592,270],[0,88,593,270],[0,88,594,228],[0,88,391,131],[0,8",
    "8,596,84],[0,88,597,94],[0,88,598,65],[0,88,599,205],[0,88,595,600],[1,\"Functor\"],[0,3",
    "5,37,602],[1,\"map\"],[0,35,603,604],[0,66,605,121],[0,88,606,127],[1,\"instFunctor\"],[",
    "0,35,256,608],[0,66,609,98],[0,88,610,269],[0,88,607,611],[0,34,62,51,376,82],[0,88,612,",
    "613],[0,88,614,228],[0,88,445,506],[0,88,616,376],[0,88,617,152],[0,88,618,131],[0,88,61",
    "9,205],[0,88,620,84],[0,88,621,79],[0,88,622,65],[0,277,148,51,613,623],[0,88,615,624],[",
    "1,\"uniformSample\"],[0,35,37,626],[0,66,627,27],[0,88,628,613],[1,\"instSampleableTypeP",
    "iFintype\"],[0,35,37,630],[0,66,631,27],[0,88,632,376],[0,88,633,152],[0,88,634,218],[0,",
    "88,635,82],[0,88,308,82],[0,88,637,355],[0,88,359,82],[0,88,639,366],[0,88,638,640],[0,8",
    "8,636,641],[0,88,629,642],[0,88,625,643],[0,88,601,644],[0,34,179,51,124,645],[0,34,208,",
    "51,152,646],[0,34,200,51,569,647],[0,34,176,51,415,648],[0,34,77,51,567,649],[0,34,50,51",
    ",564,650],[0,34,558,488,562,651],[0,34,557,488,492,652],[0,34,48,40,46,653],[0,34,39,40,",
    "46,654],[0,552,26,27,27,188,655],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.evalDist_evalu",
    "ate_eq_uniform_program\"],[2,2582705967],[0,52,481,658],[0,35,659,484],[0,35,660,59],[0,",
    "52,661,83],[0,52,661,217],[0,88,195,131],[0,88,664,84],[0,88,665,65],[0,88,92,152],[0,88",
    ",203,218],[0,88,668,205],[0,88,213,506],[0,88,670,376],[0,88,671,152],[0,88,672,94],[0,8",
    "8,673,205],[0,88,594,508],[0,88,237,506],[0,88,371,506],[0,88,375,511],[0,88,678,506],[0",
    ",88,679,218],[0,88,680,152],[0,88,681,84],[0,88,682,79],[0,88,677,683],[0,88,676,684],[0",
    ",88,685,65],[0,88,675,686],[0,34,62,51,511,82],[0,88,612,688],[0,88,689,508],[2,12],[0,6",
    "3,691],[0,88,445,692],[0,88,693,511],[0,88,694,215],[0,88,695,218],[0,88,696,205],[0,88,",
    "697,131],[0,88,698,94],[0,88,699,79],[0,277,148,51,688,700],[0,88,690,701],[0,88,628,688",
    "],[0,88,632,511],[0,88,704,215],[0,88,705,376],[0,88,706,82],[0,88,707,641],[0,88,703,70",
    "8],[0,88,702,709],[0,88,687,710],[0,34,210,51,674,711],[0,34,179,51,124,712],[0,34,208,5",
    "1,218,713],[0,34,200,51,669,714],[0,34,176,51,667,715],[0,34,190,51,666,716],[0,34,77,51",
    ",567,717],[0,34,50,51,564,718],[0,34,663,488,562,719],[0,34,662,488,492,720],[0,34,48,40",
    ",46,721],[0,34,39,40,46,722],[0,657,26,27,27,188,723],[1,\"SLHDSA.SHAKE128s.GraphSampler",
    "Compatibility.evaluate_eq_byteTraversal\"],[1,\"HashSigTest.SLHDSA.Refactor.GraphSampler",
    "\"],[1,\"ofFn\"],[0,35,118,727],[0,66,728,121],[0,88,729,73],[1,\"x\"],[0,35,37,731],[0,",
    "35,732,55],[1,\"VCVio\"],[0,35,733,734],[0,35,735,96],[1,\"QueryTracking\"],[0,35,736,73",
    "7],[1,\"RandomOracle\"],[0,35,738,739],[1,\"Traversal\"],[0,35,740,741],[2,2612511948],[",
    "0,52,742,743],[0,35,744,484],[0,35,745,59],[2,34],[0,52,746,747],[0,277,748,51,73,82],[0",
    ",88,730,749],[0,88,100,750],[0,88,751,84],[0,88,226,752],[1,\"RandomOracleTraversal\"],[",
    "0,35,97,754],[0,35,755,373],[0,66,756,27],[0,88,757,131],[0,88,758,84],[0,88,759,73],[0,",
    "88,760,82],[0,88,761,94],[0,88,762,79],[0,88,763,65],[0,88,764,205],[0,88,753,765],[0,88",
    ",375,131],[0,88,767,84],[0,88,768,94],[0,88,769,79],[0,88,770,65],[0,88,771,205],[0,88,7",
    "66,772],[0,34,208,51,94,773],[0,34,176,51,95,774],[0,34,77,51,87,775],[0,34,50,51,75,776",
    "],[0,34,48,40,46,777],[0,34,39,40,46,778],[0,725,726,27,27,188,779],[1,\"SLHDSA.SHAKE128",
    "s.GraphSamplerCompatibility.sample_eq_byteTraversal\"],[2,2855699827],[0,52,742,782],[0,",
    "35,783,484],[0,35,784,59],[2,62],[0,52,785,786],[0,277,787,51,73,82],[0,88,730,788],[0,8",
    "8,123,789],[0,88,132,790],[0,88,127,791],[0,88,226,792],[0,35,755,387],[0,66,794,27],[0,",
    "88,795,152],[0,88,796,131],[0,88,797,73],[0,88,798,82],[0,88,799,294],[0,88,800,641],[0,",
    "88,801,84],[0,88,802,94],[0,88,803,79],[0,88,804,65],[0,88,805,205],[0,88,793,806],[0,88",
    ",389,152],[0,88,808,131],[0,88,809,84],[0,88,810,94],[0,88,811,79],[0,88,812,65],[0,88,8",
    "13,205],[0,88,807,814],[0,34,179,51,124,815],[0,34,208,51,94,816],[0,34,176,51,95,817],[",
    "0,34,77,51,87,818],[0,34,50,51,75,819],[0,34,48,40,46,820],[0,34,39,40,46,821],[0,781,72",
    "6,27,27,188,822],[1,\"SLHDSA.SHAKE128s.GraphSamplerCompatibility.program_eq_byteTraversa",
    "l\"],[2,840915418],[0,52,742,825],[0,35,826,484],[0,35,827,59],[2,59],[0,52,828,829],[0,",
    "277,830,51,73,82],[0,88,730,831],[0,88,123,832],[0,88,153,833],[0,88,226,834],[0,35,755,",
    "443],[0,66,836,27],[0,88,837,218],[0,88,838,152],[0,88,839,73],[0,88,840,82],[0,88,841,2",
    "94],[0,88,842,131],[0,88,843,84],[0,88,844,94],[0,88,845,79],[0,88,846,65],[0,88,847,205",
    "],[0,88,835,848],[0,88,445,218],[0,88,850,152],[0,88,851,131],[0,88,852,84],[0,88,853,94",
    "],[0,88,854,79],[0,88,855,65],[0,88,856,205],[0,88,849,857],[0,34,179,51,124,858],[0,34,",
    "208,51,84,859],[0,34,176,51,150,860],[0,34,148,51,149,861],[0,34,77,51,87,862],[0,34,50,",
    "51,75,863],[0,34,48,40,46,864],[0,34,39,40,46,865],[0,824,726,27,27,188,866],[1,\"SLHDSA",
    ".SHAKE128s.GraphSamplerCompatibility.separated_iff_byteTraversal\"],[1,\"Iff\"],[0,35,37",
    ",869],[0,66,870,27],[0,35,755,193],[0,66,872,27],[0,88,873,79],[0,88,874,65],[0,88,875,7",
    "3],[0,88,876,205],[0,88,871,877],[0,88,195,79],[0,88,879,65],[0,88,880,205],[0,88,878,88",
    "1],[0,34,50,51,75,882],[0,34,48,40,46,883],[0,34,39,40,46,884],[0,868,726,27,27,188,885]",
    ",[1,\"SLHDSA.SHAKE128s.GraphSamplerCompatibility.freshFor_iff_byteTraversal\"],[0,35,755",
    ",211],[0,66,888,27],[0,88,889,84],[0,88,890,94],[0,88,891,73],[0,66,362,27],[0,88,893,35",
    "4],[0,88,892,894],[0,88,895,79],[0,88,896,65],[0,88,897,205],[0,88,871,898],[0,88,213,84",
    "],[0,88,900,94],[0,88,901,79],[0,88,902,65],[0,88,903,205],[0,88,899,904],[0,34,179,51,1",
    "24,905],[0,34,176,51,177,906],[0,34,50,51,75,907],[0,34,48,40,46,908],[0,34,39,40,46,909",
    "],[0,887,726,27,27,188,910],[1,\"SLHDSA.SHAKE128s.GraphSamplerCompatibility.evaluate_eq_",
    "sample\"],[0,912,726,27,27,188,407],[1,\"SLHDSA.SHAKE128s.GraphSamplerCompatibility.prog",
    "ram_congr\"],[0,914,726,27,27,188,469],[1,\"SLHDSA.SHAKE128s.GraphSamplerCompatibility.p",
    "rogram_update_outside\"],[1,\"HashSigTest\"],[0,35,474,917],[0,35,918,67],[1,\"Refactor",
    "\"],[0,35,919,920],[1,\"GraphSampler\"],[0,35,921,922],[0,52,923,482],[0,35,924,484],[0,",
    "35,925,59],[0,52,926,83],[0,34,927,488,492,547],[0,34,48,40,46,928],[0,34,39,40,46,929],",
    "[0,916,726,27,27,188,930],[1,\"SLHDSA.SHAKE128s.GraphSamplerCompatibility.evalDist_sampl",
    "e_eq_uniform_program\"],[0,52,923,553],[0,35,933,484],[0,35,934,59],[0,52,935,83],[0,52,",
    "935,217],[0,34,937,488,562,651],[0,34,936,488,492,938],[0,34,48,40,46,939],[0,34,39,40,4",
    "6,940],[0,932,726,27,27,188,941],[1,\"SLHDSA.SHAKE128s.GraphSamplerCompatibility.evalDis",
    "t_evaluate_eq_uniform_program\"],[0,52,923,658],[0,35,944,484],[0,35,945,59],[0,52,946,8",
    "3],[0,52,946,217],[0,34,948,488,562,719],[0,34,947,488,492,949],[0,34,48,40,46,950],[0,3",
    "4,39,40,46,951],[0,943,726,27,27,188,952],[0,112,142,163,171,185,408,470,551,656,724,780",
    ",823,867,886,911,913,915,931,942,953],[1,\"e1ba59d102d9d554b44bc4fd8ba1753ee1bfc0df52c64",
    "e1aec747184dca2d5e5\"],[0,943,955],[1,\"860ea2ebd796dea7419d437715ecb420f13328bb1bc5b99a",
    "ca6ca412cc51cf10\"],[0,143,957],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.program._f\"],[",
    "1,\"4321139292c97497dbc1e9a11a4286c84a71ef09e4a3066a0a6c4bf86daa6037\"],[0,959,960],[1,",
    "\"SLHDSA.SHAKE128s.GraphFreshSampling.sample.match_1\"],[1,\"139d66f0a7e3323dafd3d3dcabe",
    "abf5be89bc2bbc28b71c379cd64fa152a2119\"],[0,962,963],[1,\"SLHDSA.SHAKE128s.HashSpec\"],[",
    "1,\"7f45f3b6d88c5bbc06b945b0958d642e89513f7e1e6bab24924551d0d0555b7a\"],[0,965,966],[1,",
    "\"SLHDSA.SHAKE128s.RandomOracleModel.HashSpec\"],[1,\"2bb0a5bfabd924b49077f8669024a96740",
    "6736370fd370078fd5702ad31223e6\"],[0,968,969],[1,\"OracleSpec.ofFn\"],[1,\"7cfa1749d4ad1",
    "26ced04652f7fe17e85e68ad10d2f747531a9a66b1eb753bd6a\"],[0,971,972],[1,\"9b20089354b9a04e",
    "f0daee36f04a96290be1038a3cae8fe960f667293d717a58\"],[0,117,974],[1,\"SLHDSA.SHAKE128s.Ha",
    "shOutput\"],[1,\"e77abd4e5c903f1829a0d3297537a270d12da0f50c5f402776c5c988057d9847\"],[0,",
    "976,977],[1,\"SLHDSA.SHAKE128s.messageDigestBytes\"],[1,\"686db93a560bcbe2be7d050499c21b",
    "286554dea6aa4d76314d40eecb870e97b3\"],[0,979,980],[1,\"SLHDSA.SHAKE128s.Bytes\"],[1,\"1a",
    "0c5b814c573e4106a07a8b5ec08ce053973c5455156c726c4a9f29363b8d50\"],[0,982,983],[1,\"Oracl",
    "eSpec.QueryCache\"],[1,\"73e4a41967e835774ec0ced6919f9fcb55621088fe967dfa84b149b0fec949e",
    "6\"],[0,985,986],[1,\"OracleSpec.QueryCache.mk\"],[1,\"6aa880dd72bc8e3be3908e9deacf70fe8",
    "be7311f718e5b17b622814cc33ed14c\"],[0,988,989],[1,\"OracleSpec.Range\"],[1,\"702af5aaf08",
    "27247a43fd3159e13d9920992ae7a3003cb9c20a8a00cb599a6a4\"],[0,991,992],[1,\"OracleSpec.Dom",
    "ain\"],[1,\"019aedea08c2f4168f5c2cae117ed11500d2a5ef2c271668524bc4ddd024c35b\"],[0,994,9",
    "95],[1,\"OracleSpec.QueryCache.cacheQuery\"],[1,\"6017c1ee570c2492c80e2cc5dbb0adf66cf0f7",
    "fe9f621a983806f57f838695a7\"],[0,997,998],[1,\"OracleSpec.QueryCache.toFn\"],[1,\"e3eced",
    "7bde2a15092090bbe0e15fb92e0bdc99d02ef4941e4301e7d19ee58b48\"],[0,1000,1001],[1,\"OracleS",
    "pec.QueryCache.ofFn\"],[1,\"1bfa341e22b9ea1ee279754fb2647e05c22489a5a1015dd7611d35f12674",
    "2219\"],[0,1003,1004],[1,\"a738ea5a60b8854061f83f65c24b3cdad64ffb6139e108fb8baf7abcb2d41",
    "265\"],[0,25,1006],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.evaluate._f\"],[1,\"bcf853e4",
    "4d0e4969098a131fe0ba8ff5d24833d09cb6c8e4ef5d0902945c76c8\"],[0,1008,1009],[1,\"SLHDSA.SH",
    "AKE128s.GraphFreshSampling.evaluate.match_1\"],[1,\"1d5713f72bf5baca9a1a75d088c98a726a40",
    "fc3014fe2246d81289cc2de2755f\"],[0,1011,1012],[1,\"OracleSpec.toPFunctor\"],[1,\"245af7d",
    "492e70a0dd22da792d870b137d5b8bc830b013a90c51056e21fbedf03\"],[0,1014,1015],[1,\"OracleSp",
    "ec.query\"],[1,\"5be53c3cbaa4b5fce36ab0cf9bb7d5212e80e81b04f382ce154bffc4d525bf21\"],[0,",
    "1017,1018],[1,\"OracleQuery.mk\"],[1,\"d26ecf61a757780c753c3f0bca0caa4b1b7f495a5b8a25599",
    "7199b40e3948795\"],[0,1020,1021],[1,\"OracleQuery\"],[1,\"2269eed6e055aa1ef1de04cdac63d0",
    "96c80010b199a728665d6a9a362d541153\"],[0,1023,1024],[1,\"e54a226c7d4f698c216009f383cfd7f",
    "39da2f35d550c9074fd532218a71fda7b\"],[0,96,1026],[1,\"77291775e90a8409413b9623ebfc57ff16",
    "4acef16a6afa9e4fb4e86ed75c0346\"],[0,164,1028],[1,\"0b6f36cd41b3d7f3151f6615dd6bd92cbad6",
    "949e93bf64d592b99f15ac1806ec\"],[0,172,1030],[1,\"OracleSpec.UniformAnswerMeasure.unifSp",
    "ec\"],[1,\"57c422e2e5a5c38e2f0b192b4eb11bb8a215c4fa2cabd9df6ca724c64a7ffee0\"],[0,1032,1",
    "033],[1,\"_private.VCVio.OracleComp.EvalDist.AnswerMeasure.0.OracleSpec.UniformAnswerMea",
    "sure.unifSpec._proof_2\"],[1,\"ded497215aa44363e1a266757389c6ed3a3f528c0d718a83ec817e77f",
    "073bd3e\"],[0,1035,1036],[1,\"2a3374dc2f6089dfbc52c3d1ba33c17c386a9f8ced1dff179ac9ed9292",
    "abbd51\"],[0,266,1038],[1,\"_private.VCVio.OracleComp.EvalDist.AnswerMeasure.0.OracleSpe",
    "c.UniformAnswerMeasure.unifSpec._proof_1\"],[1,\"ae91e3c51c078a2bb34fe6c686cd8f951462353",
    "0efcaeee9560646bd796b8d65\"],[0,1040,1041],[1,\"OracleSpec.UniformAnswerMeasure.ofFinite",
    "Nonempty\"],[1,\"df3d5aa3acc5062f19fc1e4ed8d830bbc2028bcba427e318e3154b03d557ca9d\"],[0,",
    "1043,1044],[1,\"OracleSpec.UniformAnswerMeasure.ofFiniteNonempty._proof_2\"],[1,\"9e8862",
    "f9b065be397f8e6d94171b0f78dff69f90ef87531ae06fff18ce921392\"],[0,1046,1047],[1,\"OracleS",
    "pec.UniformAnswerMeasure.ofFiniteNonempty._proof_1\"],[1,\"bcc6c198ab04ec56985b3421d5648",
    "257a7ad78e2d0b5220f62799e5f1a134303\"],[0,1049,1050],[1,\"PFunctor.AnswerMeasure.mk\"],[",
    "1,\"0a1b3ea83ad72875817413778b4440b84731575f97e9400e0e20a0f20c460115\"],[0,1052,1053],[1",
    ",\"PFunctor.AnswerMeasure\"],[1,\"b122c2186acd9a416f7348a00b551ff394ba744a6f074bbae44620",
    "1652fe999e\"],[0,1055,1056],[1,\"OracleSpec.UniformAnswerMeasure.mk\"],[1,\"c5ba898ce8fa",
    "964cb0df350a14dac987a023f2c21ac3ad1302680fbe36a0285a\"],[0,1058,1059],[1,\"PFunctor.Answ",
    "erMeasure.toMeasure\"],[1,\"02f35abc4760a6a7ccc34389f8f0e6185e483e1f51d31091208e8273dcd1",
    "09cf\"],[0,1061,1062],[1,\"OracleSpec.UniformAnswerMeasure\"],[1,\"df838cef3ab5f7692e0fd",
    "5255f3d681cce0ad9c7a4a701eec61bc4b011279638\"],[0,1064,1065],[1,\"OracleSpec.UniformAnsw",
    "erMeasure.toAnswerMeasure\"],[1,\"94cf295244433291a88806359f1123a8b90dcfadf8a1b7348546d4",
    "c7b8201daa\"],[0,1067,1068],[1,\"OracleSpec.randomOracle\"],[1,\"972fb551a7bfdffdde20cfb",
    "07076d5bd2c8ab9c88e6196c536b61bc5e0a5326c\"],[0,1070,1071],[1,\"QueryImpl.withCaching\"]",
    ",[1,\"85c313f91ceeab801fa66b68efe5afd39825fb0542fb50fbe9862d12f54ff57b\"],[0,1073,1074],",
    "[1,\"QueryImpl.withCaching.match_1\"],[1,\"aedcce58e6cd15d06d58560e6dc10eddf3c33f61a1c1a",
    "ab1dcd4cf8245c84baa\"],[0,1076,1077],[1,\"QueryImpl\"],[1,\"4e7b50dc035843217f6b3857e5bb",
    "74c43d4cfa85441694f6b59cc99aa013d133\"],[0,1079,1080],[1,\"uniformSampleImpl\"],[1,\"955",
    "9838c047920d9b00b894d44dba54ac2c1590c4f58e870ca1955c38202fe62\"],[0,1082,1083],[1,\"fd60",
    "c2433d773a42f1f065ecdb60577ea49cd0091c58c634383ee565258d9816\"],[0,626,1085],[1,\"Sample",
    "ableType.selectElem\"],[1,\"84f6047286f58e7afb703bf1deb1413b1c06c17e251c47e3dd337ee58ec7",
    "1855\"],[0,1087,1088],[1,\"43f1f42bba065fedefe83a6bfd668ebe16ac20244198ca89c89523b931a31",
    "e28\"],[0,306,1090],[1,\"SampleableType.mk\"],[1,\"46a194de72c5265938c9cf22da0054b2bb614",
    "630eaf9c65ac78e1041a9982572\"],[0,1092,1093],[1,\"OracleComp.instEvalDistSemantics\"],[1",
    ",\"e79d3f35ab80c56df24f53765f54cce146e39a8823bbb36ca7c53bedda9d61be\"],[0,1095,1096],[1,",
    "\"PFunctor.FreeM.instEvalDistSemanticsFreeM\"],[1,\"2c3edfee55b77f72e55622699a3997c746e3",
    "bb8a0be5fb8007c97fd3a2c58e62\"],[0,1098,1099],[1,\"PFunctor.FreeM.denote_apply_univ_le_o",
    "ne\"],[1,\"b8431f1d290eed9c92c10ab087a92c4eaa43a701eef5cf1dc50454453b432ab9\"],[0,1101,1",
    "102],[1,\"PFunctor.FreeM.denote\"],[1,\"db9e0c14bb5ba78be4180000b097a4166455fe192bb85717",
    "341ec2ea2cc00307\"],[0,1104,1105],[1,\"PFunctor.FreeM.denote._f\"],[1,\"f6a24520728e1e60",
    "891acb4d1cd8295baa9bd85369e1f627cd9339769726e66b\"],[0,1107,1108],[1,\"PFunctor.FreeM.de",
    "note.match_1\"],[1,\"06f818637c4b1e8080fa6937014b9a8b5e7a4d0cd17b35c6386cc18c8483cff2\"]",
    ",[0,1110,1111],[1,\"EvalDistSemantics.mk\"],[1,\"cea68612a6de5259f026be104524eb62fe183aa",
    "96e40823159762b699b439d80\"],[0,1113,1114],[1,\"EvalDistSemantics\"],[1,\"96e64817d4b6f0",
    "f038f004ad819fa7c8fac4ba76ff1cef11adafd10ee900f283\"],[0,1116,1117],[1,\"OracleSpec.Answ",
    "erMeasure\"],[1,\"90071bdedf17844b1e40235258f67e8584681f5d91bcd9b333f539d9a968d205\"],[0",
    ",1119,1120],[1,\"evalDist\"],[1,\"0722dbd13adcc36221d1fd871e433002bc70526fbdcb84c45e175a",
    "06e76f4656\"],[0,1122,1123],[1,\"EvalDistSemantics.denote\"],[1,\"53741659a57d7f5a82bc75",
    "543ba3f2e8f1d4ccd741319a73a5bce8220bcc826d\"],[0,1125,1126],[1,\"b532f76f8d7aff19352ed27",
    "38601672908a96765ca1bc432a3051350e7aefec6\"],[0,125,1128],[1,\"FinEnum.SampleableType\"]",
    ",[1,\"c626ce019339908c7ce668ed19ad03cfa4fa6a16e7bb04f005dae954e5b8a3aa\"],[0,1130,1131],",
    "[1,\"FinEnum.SampleableType._proof_1\"],[1,\"4e5a9b83c2a2a87a606d84b6f73740c77ece517d066",
    "6c733f94eb8094375306c\"],[0,1133,1134],[1,\"SampleableType.ofEquiv\"],[1,\"67aad3d274dc5",
    "5ebda4ebad7b1366240719d08ccf9afe810d985b27ccf13f994\"],[0,1136,1137],[1,\"SampleableType",
    ".ofEquiv._proof_1\"],[1,\"725d6f2cb9b2bb223f6c4e0fa1de70f4e88503d854c304a33fe200e7c9bc75",
    "61\"],[0,1139,1140],[1,\"instSampleableTypeFinOfNeZeroNat\"],[1,\"f45b5b8211fff25e717880",
    "809e429319c5a9021488f47f69d17d4db32c9d6b45\"],[0,1142,1143],[1,\"instSampleableTypeFinOf",
    "NeZeroNat.match_1\"],[1,\"93d4e0c4be1446e8dfef8f26fceb3bdb834785910f704d9ac9abeee1864de4",
    "f7\"],[0,1145,1146],[1,\"SampleableType.Fin\"],[1,\"3f192dba088925eb0053b4d4553878ca2948",
    "06530ac9c748d99169ecf974cf0a\"],[0,1148,1149],[1,\"SampleableType.Fin._proof_1\"],[1,\"d",
    "9517fbca760ad94b6bb851964971152a2161b95530722ec8f30fbc641ccd5f4\"],[0,1151,1152],[1,\"Pr",
    "obComp.uniformFin\"],[1,\"a6f4c4ebf1abad8a135f9a5e9526275fcfbded2ac468e1b77f59c31c2617b7",
    "86\"],[0,1154,1155],[1,\"ec7ce1730a8d184198057e889a765c53288434d17ff4d231cce357ee6f99b7b",
    "9\"],[0,239,1157],[1,\"5d06f7ea8c6fe9d6e09fffaae7049e62dfb5d9057e1ecd3c35054d5d895cc361",
    "\"],[0,630,1159],[1,\"instSampleableTypeFinFunc\"],[1,\"c2a803cc4160343aa5aff2cb13aa1bda",
    "6279dff07d5d4bd51b999b6ea60f8b55\"],[0,1161,1162],[1,\"instSampleableTypeVector\"],[1,\"",
    "f34cc81bd5190cd2f4159e8f3082ca3a8f5fc9760d8cbaa2ad6cfe2b90d1f34a\"],[0,1164,1165],[1,\"S",
    "ampleableType.vector\"],[1,\"927f7e6131004e96c64f19f6b5e3637d2cb7b93e03c8013026eb3a59a66",
    "a229c\"],[0,1167,1168],[1,\"SampleableType.vector._f\"],[1,\"14d66afe7bb809e823c8081656f",
    "5851f088bb5ed9c0ea20ba3dfbe437a24fd11\"],[0,1170,1171],[1,\"_private.VCVio.OracleComp.Co",
    "nstructions.SampleableType.Basic.0.SampleableType.vector.match_1\"],[1,\"2626c08a546f4bf",
    "031d0279c5a1c39c3dfb2370aaa8f0ab4b1f4dbe0c90052d4\"],[0,1173,1174],[1,\"SampleableType.e",
    "valDist_vector\"],[1,\"79e4937a72aea943194864d356b692cc668b11d0f087b43cb1cb898ee8e372fa",
    "\"],[0,1176,1177],[1,\"arrayVectorEquivFin\"],[1,\"1ed72062db45ace6cee8e6e0a9e0e4f3717e2",
    "a0febb3e742e435e3f6aba63cda\"],[0,1179,1180],[1,\"arrayVectorEquivFin._proof_5\"],[1,\"6",
    "1ef158918c169a6e142ec127185d329090b472751126100337a0fd219c0de19\"],[0,1182,1183],[1,\"ar",
    "rayVectorEquivFin._proof_2\"],[1,\"4988a7e2d8ad28025468b8633858fb2eb5132bbbd658ac9157ee1",
    "e2ef6dc78f5\"],[0,1185,1186],[1,\"arrayVectorEquivFin._proof_3\"],[1,\"bcee631a42442f556",
    "1fdef9743abd98a904890bcefd114c95adba106202716eb\"],[0,1188,1189],[1,\"a089cd66f448ac6747",
    "b84a9e8d64226474b172bd4100d7584ccb60339d72c06d\"],[0,570,1191],[1,\"prEvent\"],[1,\"4e8a",
    "8142cc7fd28be2c557623baee838c665d278ca7b0bd0f95d840a64a8517d\"],[0,1193,1194],[1,\"c7800",
    "10c65760746408016c4d49fe10464b5963628cd1ffaa161180d92239b21\"],[0,932,1196],[1,\"174d5d1",
    "ff81c3e04847fa69d485968a4189860ec4debb45b76189043fa2be3d9\"],[0,113,1198],[1,\"SLHDSA.SH",
    "AKE128s.GraphFreshSampling.sample._f\"],[1,\"e16bd3c2faf75857813994fd26cc4a9291a55f54f80",
    "e2b33c1d93d3905fdb300\"],[0,1200,1201],[1,\"ad0d6eb138d23f5a99afa5b6c98b7de1cec8e9c93536",
    "c3cf1f61e41012d282ae\"],[0,916,1203],[1,\"75be9bc77d17918117af2a0be674d4c90f437cf34813f7",
    "5ee84bf071bfa6d8cb\"],[0,914,1205],[1,\"e3cb1d0a763e690f68ddf5502de201df8da81f3d74699ebb",
    "a569cb87a884818e\"],[0,912,1207],[1,\"3183a5a44afa8f1ba55f1066e096e3b842ec3cc842421798f4",
    "079ce864de4611\"],[0,887,1209],[1,\"OracleComp.RandomOracleTraversal.FreshFor\"],[1,\"7b",
    "9ddd14ace3b83917562e1e94c6aeb5c5aa2d5a051bf2e1d426ceb02beb0768\"],[0,1211,1212],[1,\"ce3",
    "ddd5e3b0447eb4c2994a03c4d77eb39afee7abeca3d911be4522639c0109e\"],[0,868,1214],[1,\"Oracl",
    "eComp.RandomOracleTraversal.Separated\"],[1,\"0930afbf09c313ffbd2271b0d3cb9b4cb176ad48fe",
    "8a772533034d52854a4e4f\"],[0,1216,1217],[1,\"05154298748cd0d0486336778218d613d9220570f97",
    "8d620514d4f82b6a8e1be\"],[0,824,1219],[1,\"OracleComp.RandomOracleTraversal.program\"],[",
    "1,\"4f5cd27f950deec8348982e53e4d9e637af554aca7a69e6818f192a2fe7a8284\"],[0,1221,1222],[1",
    ",\"OracleComp.RandomOracleTraversal.program._f\"],[1,\"4909c246af248ccd227dfd4254cb999f4",
    "2eb8c0df58dbb7b167b311a51ee79f7\"],[0,1224,1225],[1,\"OracleComp.RandomOracleTraversal.p",
    "rogram.match_1\"],[1,\"71ec59206596d87fd003d7da2420c781f4c7374f04eb77e71e4b0a992b91b361",
    "\"],[0,1227,1228],[1,\"d86192e79fb525b034f3dabcc8beba41a84cec86212f497bbbe8c6e8e42a9e24",
    "\"],[0,781,1230],[1,\"OracleComp.RandomOracleTraversal.sample\"],[1,\"702de1f60a2901279a",
    "593ebdf1e1d7460e8bc57d3367931485ff21c61b894ee4\"],[0,1232,1233],[1,\"OracleComp.RandomOr",
    "acleTraversal.sample._f\"],[1,\"5829009fe6137bad5bd38421e611937e4234017053b066c680b1e952",
    "0b8f2eec\"],[0,1235,1236],[1,\"4c0281c50f6090be3529f86f7f1a4f767d84cf78ea711884051c21cdd",
    "da65100\"],[0,725,1238],[1,\"OracleComp.RandomOracleTraversal.evaluate\"],[1,\"a397555fc",
    "7ab252928ec53d3d7a457dc976461f0ab0b1c2cb04afde3df264f70\"],[0,1240,1241],[1,\"OracleComp",
    ".RandomOracleTraversal.evaluate._f\"],[1,\"c270438105b1438c4312618777954a63f59957a820694",
    "095bec273d472ed98e0\"],[0,1243,1244],[1,\"OracleComp.RandomOracleTraversal.evaluate.matc",
    "h_1\"],[1,\"37429992630b3f32c49a47ed752dd29aecac29e9200d42445115f21251f0724f\"],[0,1246,",
    "1247],[1,\"6f364d3a7dfeabd238658487c641c7e8b26778332c5567aeb1275a54dd06029a\"],[0,657,12",
    "49],[1,\"55f5cfe0014241f9c18baaa678809a86037a5451d0446564ab58c88cd4dfad41\"],[0,552,1251",
    "],[1,\"0080173801fc343c0fd28d21befae7b489e7155aa1add158b42f642be8940700\"],[0,471,1253],",
    "[1,\"bef7e7d0f29fbbb6b9b6fa575120410a011e52a624c242e74201a6a9563990e0\"],[0,409,1255],[1",
    ",\"298636c1ffb1cfc8cd059eb5fd860a319789e6605a1139c8bf95219ca4efdf4d\"],[0,186,1257],[0,9",
    "56,958,961,964,967,970,973,975,978,981,984,987,990,993,996,999,1002,1005,1007,1010,1013,",
    "1016,1019,1022,1025,1027,1029,1031,1034,1037,1039,1042,1045,1048,1051,1054,1057,1060,106",
    "3,1066,1069,1072,1075,1078,1081,1084,1086,1089,1091,1094,1097,1100,1103,1106,1109,1112,1",
    "115,1118,1121,1124,1127,1129,1132,1135,1138,1141,1144,1147,1150,1153,1156,1158,1160,1163",
    ",1166,1169,1172,1175,1178,1181,1184,1187,1190,1192,1195,1197,1199,1202,1204,1206,1208,12",
    "10,1213,1215,1218,1220,1223,1226,1229,1231,1234,1237,1239,1242,1245,1248,1250,1252,1254,",
    "1256,1258],[1,\"d1d2c70dfe46d77102f79cf6424a00c742f418fdae42405a0cd2fbb84a0e10d8\"],[0,1",
    "72,1260],[1,\"992124c9fc9b58d759b31dfd28758de099d1246f8cd041e87a086c7332a0450c\"],[0,164",
    ",1262],[1,\"b8fab7df03890cee6cfa8582f503347584053566bf14d1757ec6937154a53a1b\"],[0,657,1",
    "264],[1,\"ad8510bd4d093e983d6ab8f525faa49cefe7e1e0e22d06bf480474e702638a25\"],[0,552,126",
    "6],[1,\"516809a22d851ba69bfa36368a3442323fc40a697bff0607f1abe9da2ef98270\"],[0,25,1268],",
    "[1,\"0a7a5498f00179ab96d540a227f976fe07d856173403fc0f03ac600f2c03a35a\"],[0,186,1270],[1",
    ",\"31e2401531f09ed9e5ab4a1bde98ddf67288f3d6e4c9c3f45551726a1f18af44\"],[0,143,1272],[1,",
    "\"7b664ce7c6de1b2b9a7f459372cca6b93287133ed3ac5f7253966b4dd8478b10\"],[0,409,1274],[1,\"",
    "af7d935fe6aaf7c94357da65a0c0fbbbebd34e4a53fe5a9427fd2bf5e6b680fd\"],[0,471,1276],[1,\"0a",
    "760d80d13a150e1774270970ed99b339d3461767bb35b04d26ddd566e4ac42\"],[0,113,1278],[1,\"7b19",
    "13e65a20f826cd46806dd237286cc03b7eb6636cb4e922acf9e2c6b6bc11\"],[0,943,1280],[1,\"4bab3f",
    "c212cc513f578bad255718755a92f76a2ce43674632661db7195caa925\"],[0,932,1282],[1,\"20bac71f",
    "55ea8e4ca89d850e04065a0927ac10910dc3e3701005e0dd81a63cb6\"],[0,725,1284],[1,\"98bee95593",
    "291bd8f6e961ea1f1e40e0e744b767ffef200795d6b424279d0372\"],[0,912,1286],[1,\"938a4e3ecf5c",
    "71cf45bdb5d324d9fb919cabe98702b7623ec33a6bb0ac67982a\"],[0,887,1288],[1,\"b295e37dcbb59a",
    "d64f812eb534988c95726dbc9c2e6fd1ffad627811a38d8db5\"],[0,914,1290],[1,\"01243695b45fcdc3",
    "840e0613c2748559928cf47677c4f9bd9601ed731eef8f97\"],[0,824,1292],[1,\"414a302cde4daff0c6",
    "b6942ee8ba191fc2d036eb8ff3201082560d47733a87a0\"],[0,916,1294],[1,\"c29c3e22ff8b8c0b7b9f",
    "9b3e8ea59aa903f3540479a75fd483237f0dcebb8b10\"],[0,781,1296],[1,\"953680f2f781fe6ffe488a",
    "c3c004fe4522f4b13a364a0d68bb0fcfb78e67b345\"],[0,868,1298],[1,\"65e6b03d839b3e754200a51a",
    "24c0908cd04f11a6488c90c788ac2621c0a9dde1\"],[0,1008,1300],[1,\"SLHDSA.SHAKE128s.GraphFre",
    "shSampling.evaluate._sunfold\"],[1,\"3cdbadc41e66009005254d0ced045f9d3ea7125335969252523",
    "ef3d314584718\"],[0,1302,1303],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.evaluate._unsafe",
    "_rec\"],[1,\"7a449d5190487c8267744fb398d063a568f3ef02e458e752f551c56c9d65d189\"],[0,1305",
    ",1306],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.evaluate.eq_1\"],[1,\"4cae42270c07f7b21e",
    "9913a17a4129c0944b8ba259e54a1c3608ed55909e6db4\"],[0,1308,1309],[1,\"SLHDSA.SHAKE128s.Gr",
    "aphFreshSampling.evaluate.eq_2\"],[1,\"1699a72d511f222f0eac2cbdc8e7137d2b5e8e7c13017a960",
    "7366ba2997d796b\"],[0,1311,1312],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.evaluate.eq_de",
    "f\"],[1,\"0c98e10664c27639dfb158327e2ecfd0fc081b52900c05d655e9508f4d36c2a1\"],[0,1314,13",
    "15],[1,\"47ec792a556ef227ab4eadacade720246b616ec1ee705d350fffa2b855afb1fb\"],[0,1011,131",
    "7],[1,\"d454fec4f07c95503072a3a9bd1cefa063f5d37779b72b3bf94e7cd905afccbb\"],[0,959,1319]",
    ",[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.program._sunfold\"],[1,\"51ad05241875ff79b91b0",
    "1bd9988dc1cedffd9d8ff912e85a9651c891f53cdf4\"],[0,1321,1322],[1,\"SLHDSA.SHAKE128s.Graph",
    "FreshSampling.program._unsafe_rec\"],[1,\"40784027bbb671556317c564a952e4d5662ef78e481369",
    "828d08a48d12c51ba8\"],[0,1324,1325],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.program.eq_",
    "1\"],[1,\"2e7f6f2ea170c20424f3dede5866caffa2ea62ec4733729988f2eab8b5bdeba1\"],[0,1327,13",
    "28],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.program.eq_2\"],[1,\"dedba49d7f1d63699e30b2",
    "77fc7854e4479496d46d727aaa94ef68b0816ff81c\"],[0,1330,1331],[1,\"SLHDSA.SHAKE128s.GraphF",
    "reshSampling.program.eq_def\"],[1,\"b236b7125b04722c4e2278fd8b95e3dfc839028ae16b38d048f0",
    "c1ca8d15cc88\"],[0,1333,1334],[1,\"25b3a7bcaf30702ead31afc29cb1c7b0298b5e73f62f3d739b244",
    "6e513b00438\"],[0,1200,1336],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.sample._proof_1\"]",
    ",[1,\"0901349942c74e1fc427f79f9e72d9b91eab61f27ca1411f4cd46a0ac350860a\"],[0,1338,1339],",
    "[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.sample._sunfold\"],[1,\"1a3fafc7c4026f183c29050",
    "ced6eb740a99f97c6ce32ff6485c9178650752e2a\"],[0,1341,1342],[1,\"SLHDSA.SHAKE128s.GraphFr",
    "eshSampling.sample._unsafe_rec\"],[1,\"6a4776834838f1e1eaef910e19faaa06b42cd300794e1e202",
    "e971aee4f37906f\"],[0,1344,1345],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.sample.eq_1\"]",
    ",[1,\"6e728092fa70180e5249e4a645f4880b1f2d668af4f4bafc8d66ec6274683886\"],[0,1347,1348],",
    "[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.sample.eq_2\"],[1,\"c32fe6e4416bf66d73caee27e27",
    "ffc4b12f761aba305feb7b37f8d3d820b5519\"],[0,1350,1351],[1,\"SLHDSA.SHAKE128s.GraphFreshS",
    "ampling.sample.eq_def\"],[1,\"76126d809aced467264dad339be840388918a8cbe133eaba0cb5eaa285",
    "8431f8\"],[0,1353,1354],[1,\"2cb684543a3f398b711c769988e735d81412b10e3720cefa520d7c2ecc3",
    "1a61f\"],[0,962,1356],[1,\"_private.HashSig.SLHDSA.SHAKE128s.Proof.GraphFreshSampling.0.",
    "SLHDSA.SHAKE128s.GraphFreshSampling.evaluate.match_1.eq_1\"],[1,\"ec326ed4bf0281db1b0a09",
    "b9ca3c990417938b0edd9a944577e04dbd229f00c8\"],[0,1358,1359],[1,\"_private.HashSig.SLHDSA",
    ".SHAKE128s.Proof.GraphFreshSampling.0.SLHDSA.SHAKE128s.GraphFreshSampling.evaluate.match",
    "_1.eq_2\"],[1,\"aa02be20a5d6e17c94c67f63d9746f78f1685333453ef68a7af082cf565ee246\"],[0,1",
    "361,1362],[1,\"_private.HashSig.SLHDSA.SHAKE128s.Proof.GraphFreshSampling.0.SLHDSA.SHAKE",
    "128s.GraphFreshSampling.evaluate.match_1.splitter\"],[1,\"e5be6e51407fe318a5fe4e6cdd42d5",
    "647a035b5e5b37a1e636a2359a78b901f9\"],[0,1364,1365],[1,\"_private.HashSig.SLHDSA.SHAKE12",
    "8s.Proof.GraphFreshSampling.0.SLHDSA.SHAKE128s.GraphFreshSampling.sample.match_1.eq_1\"]",
    ",[1,\"5594666728daedd749a2e8465c3080df14f1cc72eabb6c84025fc0ed12e1cdb8\"],[0,1367,1368],",
    "[1,\"_private.HashSig.SLHDSA.SHAKE128s.Proof.GraphFreshSampling.0.SLHDSA.SHAKE128s.Graph",
    "FreshSampling.sample.match_1.eq_2\"],[1,\"064b2ff535f6fa1567d4cb32732dca8d1b2bdf9841237e",
    "02f1aadbfc3cd8ba24\"],[0,1370,1371],[1,\"_private.HashSig.SLHDSA.SHAKE128s.Proof.GraphFr",
    "eshSampling.0.SLHDSA.SHAKE128s.GraphFreshSampling.sample.match_1.splitter\"],[1,\"0ef09a",
    "d8c867f7d434655bb3cb6024334d94949649a3863ca941cf5e2b71818c\"],[0,1373,1374],[0,1261,1263",
    ",1265,1267,1269,1271,1273,1275,1277,1279,1281,1283,1285,1287,1289,1291,1293,1295,1297,12",
    "99,1301,1304,1307,1310,1313,1316,1318,1320,1323,1326,1329,1332,1335,1337,1340,1343,1346,",
    "1349,1352,1355,1357,1360,1363,1366,1369,1372,1375],[1,\"AEMeasurable\"],[1,\"Mathlib.Mea",
    "sureTheory.Measure.MeasureSpaceDef\"],[0,1377,1378],[1,\"Init.Prelude\"],[0,361,1380],[0",
    ",489,1380],[1,\"ENNReal\"],[1,\"Mathlib.Basic.ENNReal.Basic\"],[0,1383,1384],[0,223,1380",
    "],[1,\"Equiv\"],[1,\"Mathlib.Logic.Equiv.Defs\"],[0,1387,1388],[1,\"False\"],[0,1390,138",
    "0],[1,\"Fin\"],[0,1392,1380],[1,\"Mathlib.Data.FinEnum\"],[0,304,1394],[1,\"Finite\"],[1",
    ",\"Mathlib.Basic.Finite.Defs\"],[0,1396,1397],[1,\"Mathlib.Data.Fintype.Defs\"],[0,559,1",
    "399],[1,\"Init.Core\"],[0,869,1401],[0,89,1380],[1,\"MeasurableSingletonClass\"],[1,\"Ma",
    "thlib.MeasureTheory.MeasurableSpace.Defs\"],[0,1404,1405],[1,\"MeasurableSpace\"],[0,140",
    "7,1405],[1,\"Monad\"],[0,1409,1380],[0,262,1380],[1,\"Ne\"],[0,1412,1401],[1,\"NeZero\"]",
    ",[1,\"Init.Data.NeZero\"],[0,1414,1415],[1,\"Nonempty\"],[0,1417,1380],[0,500,1380],[1,",
    "\"Option\"],[0,1420,1380],[1,\"Mathlib.Data.PFunctor.Univariate.Basic\"],[0,253,1422],[1",
    ",\"PProd\"],[0,1424,1380],[0,128,1380],[1,\"Set\"],[1,\"Mathlib.Data.Set.Defs\"],[0,1427",
    ",1428],[1,\"Init.Control.State\"],[0,231,1430],[1,\"True\"],[0,1432,1380],[0,283,1380],[",
    "1,\"Unit\"],[0,1435,1380],[1,\"Vector\"],[1,\"Init.Data.Vector.Basic\"],[0,1437,1438],[1",
    ",\"absurd\"],[0,1440,1380],[1,\"id\"],[0,1442,1380],[1,\"instAddNat\"],[0,1444,1380],[0,",
    "280,1380],[0,287,1380],[1,\"instHAdd\"],[0,1448,1380],[0,327,1380],[1,\"instLTNat\"],[0,",
    "1451,1380],[1,\"instMonadLiftT\"],[0,1453,1380],[1,\"instMonadLiftTOfMonadLift\"],[0,145",
    "5,1380],[1,\"instMonadStateOfMonadStateOf\"],[0,1457,1380],[1,\"instMonadStateOfStateTOf",
    "Monad\"],[0,1459,1430],[0,331,1380],[0,357,1380],[0,345,1380],[1,\"ite\"],[0,1464,1380],",
    "[1,\"liftM\"],[0,1466,1380],[1,\"rfl\"],[0,1468,1380],[1,\"Applicative.toFunctor\"],[0,1",
    "470,1380],[1,\"Applicative.toPure\"],[0,1472,1380],[1,\"Applicative.toSeq\"],[0,1474,138",
    "0],[1,\"Array.size\"],[0,1476,1380],[1,\"Bind.bind\"],[0,1478,1380],[1,\"BitVec.instInha",
    "bited\"],[1,\"Init.Data.BitVec.Basic\"],[0,1480,1481],[1,\"BoundedOrder.toOrderTop\"],[1",
    ",\"Mathlib.Order.BoundedOrder.Basic\"],[0,1483,1484],[1,\"Classical.propDecidable\"],[1,",
    "\"Init.Classical\"],[0,1486,1487],[1,\"CompleteLattice.toBoundedOrder\"],[1,\"Mathlib.Or",
    "der.CompleteLattice.Defs\"],[0,1489,1490],[1,\"CompleteLattice.toLattice\"],[0,1492,1490",
    "],[1,\"DFunLike.coe\"],[1,\"Mathlib.Basic.FunLike.Basic\"],[0,1494,1495],[1,\"ENNReal.in",
    "stLE\"],[0,1497,1384],[1,\"ENNReal.instOne\"],[0,1499,1384],[1,\"Eq.refl\"],[0,1501,1380",
    "],[1,\"Equiv.arrowCongr\"],[0,1503,1388],[1,\"Equiv.instEquivLike\"],[0,1505,1388],[1,\"",
    "Equiv.mk\"],[0,1507,1388],[1,\"Equiv.refl\"],[0,1509,1388],[1,\"Equiv.symm\"],[0,1511,13",
    "88],[1,\"EquivLike.toFunLike\"],[1,\"Mathlib.Basic.FunLike.Equiv\"],[0,1513,1514],[1,\"F",
    "alse.elim\"],[0,1516,1380],[1,\"Fin.val\"],[0,1518,1380],[1,\"FinEnum.card\"],[0,1520,13",
    "94],[1,\"FinEnum.equiv\"],[0,1522,1394],[1,\"FinEnum.instBitVec\"],[0,1524,1394],[1,\"Fi",
    "ntype.card\"],[1,\"Mathlib.Data.Fintype.Card\"],[0,1526,1527],[1,\"Fintype.equivFin\"],[",
    "1,\"Mathlib.Data.Fintype.EquivFin\"],[0,1529,1530],[1,\"Function.update\"],[1,\"Mathlib.",
    "Logic.Function.Basic\"],[0,1532,1533],[1,\"Functor.map\"],[0,1535,1380],[1,\"GetElem.get",
    "Elem\"],[1,\"Init.GetElem\"],[0,1537,1538],[1,\"HAdd.hAdd\"],[0,1540,1380],[1,\"HMul.hMu",
    "l\"],[0,1542,1380],[1,\"LE.le\"],[0,1544,1380],[1,\"LT.lt\"],[0,1546,1380],[1,\"Lattice.",
    "toSemilatticeSup\"],[1,\"Mathlib.Order.Defs.Lattice\"],[0,1548,1549],[1,\"List.Nodup\"],",
    "[1,\"Init.Data.List.Basic\"],[0,1551,1552],[1,\"List.below\"],[0,1554,1380],[1,\"List.br",
    "ecOn\"],[0,1556,1380],[1,\"List.casesOn\"],[0,1558,1380],[1,\"List.cons\"],[0,1560,1380]",
    ",[1,\"List.instMembership\"],[0,1562,1552],[1,\"List.nil\"],[0,1564,1380],[1,\"List.toAr",
    "ray\"],[0,1566,1380],[1,\"MeasurableSpace.instCompleteLattice\"],[0,1568,1405],[1,\"Meas",
    "ureTheory.IsProbabilityMeasure\"],[1,\"Mathlib.MeasureTheory.Measure.Typeclasses.Probabi",
    "lity\"],[0,1570,1571],[1,\"MeasureTheory.Measure\"],[0,1573,1378],[1,\"Membership.mem\"]",
    ",[0,1575,1380],[1,\"Monad.toApplicative\"],[0,1577,1380],[1,\"Monad.toBind\"],[0,1579,13",
    "80],[1,\"MonadState.get\"],[0,1581,1380],[1,\"MonadState.modifyGet\"],[0,1583,1380],[1,",
    "\"MulZeroClass.toZero\"],[1,\"Mathlib.Algebra.GroupWithZero.Defs\"],[0,1585,1586],[1,\"N",
    "at.below\"],[0,1588,1380],[1,\"Nat.brecOn\"],[0,1590,1380],[1,\"Nat.casesOn\"],[0,1592,1",
    "380],[1,\"Nat.instMulZeroClass\"],[1,\"Mathlib.Algebra.GroupWithZero.Nat\"],[0,1594,1595",
    "],[1,\"Nat.succ\"],[0,1597,1380],[1,\"Nat.zero\"],[0,1599,1380],[1,\"NeZero.casesOn\"],[",
    "0,1601,1415],[1,\"OfNat.ofNat\"],[0,1603,1380],[1,\"One.toOfNat1\"],[1,\"Init.Data.Zero",
    "\"],[0,1605,1606],[1,\"Option.casesOn\"],[0,1608,1380],[1,\"Option.none\"],[0,1610,1380]",
    ",[1,\"Option.some\"],[0,1612,1380],[1,\"OrderTop.toTop\"],[0,1614,1484],[1,\"PFunctor.A",
    "\"],[0,1616,1422],[1,\"PFunctor.B\"],[0,1618,1422],[1,\"PFunctor.FreeM\"],[1,\"Cslib.Fou",
    "ndations.Data.PFunctor.Free\"],[0,1620,1621],[1,\"PFunctor.Obj\"],[0,1623,1422],[1,\"PFu",
    "nctor.mk\"],[0,1625,1422],[1,\"PartialOrder.toPreorder\"],[1,\"Mathlib.Order.Defs.Partia",
    "lOrder\"],[0,1627,1628],[1,\"Preorder.toLE\"],[0,1630,1628],[1,\"ProbabilityTheory.unifo",
    "rmOn\"],[1,\"Mathlib.Probability.UniformOn\"],[0,1632,1633],[1,\"Prod.mk\"],[0,1635,1380",
    "],[1,\"Prop.instMeasurableSpace\"],[1,\"Mathlib.MeasureTheory.MeasurableSpace.Instances",
    "\"],[0,1637,1638],[1,\"Pure.pure\"],[0,1640,1380],[1,\"SemilatticeSup.toPartialOrder\"],",
    "[0,1642,1549],[1,\"Seq.seq\"],[0,1644,1380],[1,\"Set.instSingletonSet\"],[0,1646,1428],[",
    "1,\"Set.univ\"],[0,1648,1428],[1,\"Singleton.singleton\"],[0,1650,1401],[1,\"StateT.inst",
    "Monad\"],[0,1652,1430],[1,\"StateT.instMonadLift\"],[0,1654,1430],[1,\"StateT.run\"],[0,",
    "1656,1430],[1,\"Top.top\"],[1,\"Mathlib.Order.Notation\"],[0,1658,1659],[1,\"Unit.unit\"",
    "],[0,1661,1380],[1,\"Vector.instGetElemNatLt\"],[0,1663,1438],[1,\"Vector.mk\"],[0,1665,",
    "1438],[1,\"Vector.ofFn\"],[0,1667,1438],[1,\"Vector.push\"],[0,1669,1438],[1,\"Zero.toOf",
    "Nat0\"],[0,1671,1606],[1,\"MeasureTheory.Measure.bind\"],[1,\"Mathlib.MeasureTheory.Meas",
    "ure.GiryMonad\"],[0,1673,1674],[1,\"MeasureTheory.Measure.dirac\"],[1,\"Mathlib.MeasureT",
    "heory.Measure.Dirac.Def\"],[0,1676,1677],[1,\"MeasureTheory.Measure.instFunLike\"],[0,16",
    "79,1378],[1,\"MeasureTheory.Measure.instMeasurableSpace\"],[0,1681,1674],[1,\"MeasureThe",
    "ory.Measure.instZero\"],[1,\"Mathlib.MeasureTheory.Measure.Module\"],[0,1683,1684],[1,\"",
    "PFunctor.FreeM.below\"],[0,1686,1621],[1,\"PFunctor.FreeM.brecOn\"],[0,1688,1621],[1,\"P",
    "Functor.FreeM.casesOn\"],[0,1690,1621],[1,\"PFunctor.FreeM.instBind\"],[0,1692,1621],[1,",
    "\"PFunctor.FreeM.instFunctor\"],[0,1694,1621],[1,\"PFunctor.FreeM.instMonad\"],[0,1696,1",
    "621],[1,\"PFunctor.FreeM.instMonadLiftObj\"],[0,1698,1621],[1,\"PFunctor.FreeM.instPure",
    "\"],[0,1700,1621],[1,\"PFunctor.FreeM.liftBind\"],[0,1702,1621],[1,\"PFunctor.FreeM.lift",
    "M\"],[0,1704,1621],[1,\"PFunctor.FreeM.pure\"],[0,1706,1621],[1,\"PFunctor.Obj.mk\"],[0,",
    "1708,1422],[0,1379,1381,1382,1385,1386,1389,1391,1393,1395,1398,1400,1402,1403,1406,1408",
    ",1410,1411,1413,1416,1418,1419,1421,1423,1425,1426,1429,1431,1433,1434,1436,1439,1441,14",
    "43,1445,1446,1447,1449,1450,1452,1454,1456,1458,1460,1461,1462,1463,1465,1467,1469,1471,",
    "1473,1475,1477,1479,1482,1485,1488,1491,1493,1496,1498,1500,1502,1504,1506,1508,1510,151",
    "2,1515,1517,1519,1521,1523,1525,1528,1531,1534,1536,1539,1541,1543,1545,1547,1550,1553,1",
    "555,1557,1559,1561,1563,1565,1567,1569,1572,1574,1576,1578,1580,1582,1584,1587,1589,1591",
    ",1593,1596,1598,1600,1602,1604,1607,1609,1611,1613,1615,1617,1619,1622,1624,1626,1629,16",
    "31,1634,1636,1639,1641,1643,1645,1647,1649,1651,1653,1655,1657,1660,1662,1664,1666,1668,",
    "1670,1672,1675,1678,1680,1682,1685,1687,1689,1691,1693,1695,1697,1699,1701,1703,1705,170",
    "7,1709],[1,\"_private.HashSig.SLHDSA.SHAKE128s.Proof.GraphFreshSampling.0.SLHDSA.SHAKE12",
    "8s.GraphFreshSampling.sample.match_1.splitter._redArg\"],[1,\"_private.HashSig.SLHDSA.SH",
    "AKE128s.Proof.GraphFreshSampling.0.SLHDSA.SHAKE128s.GraphFreshSampling.evaluate.match_1.",
    "splitter._redArg\"],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.program._redArg\"],[1,\"Ora",
    "cleSpec.QueryCache.cacheQuery._at_.SLHDSA.SHAKE128s.GraphFreshSampling.sample.spec_0\"],",
    "[1,\"Function.update._at_.OracleSpec.QueryCache.cacheQuery._at_.SLHDSA.SHAKE128s.GraphFr",
    "eshSampling.sample.spec_0.spec_0._boxed\"],[1,\"Function.update._at_.OracleSpec.QueryCac",
    "he.cacheQuery._at_.SLHDSA.SHAKE128s.GraphFreshSampling.sample.spec_0.spec_0\"],[1,\"SLHD",
    "SA.SHAKE128s.GraphFreshSampling.sample._redArg._lam_2\"],[1,\"SLHDSA.SHAKE128s.GraphFres",
    "hSampling.sample._redArg\"],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.sample._redArg._clo",
    "sed_7\"],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.sample._redArg._closed_6\"],[1,\"SLHDS",
    "A.SHAKE128s.GraphFreshSampling.sample._redArg._closed_5\"],[1,\"SLHDSA.SHAKE128s.GraphFr",
    "eshSampling.sample._redArg._closed_4\"],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.sample.",
    "_redArg._closed_0\"],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.sample._redArg._closed_1\"",
    "],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.sample._redArg._closed_3\"],[1,\"SLHDSA.SHAKE",
    "128s.GraphFreshSampling.sample._redArg._closed_2\"],[1,\"SLHDSA.SHAKE128s.GraphFreshSamp",
    "ling.sample._redArg._lam_3\"],[1,\"OracleSpec.QueryCache.cacheQuery._at_.SLHDSA.SHAKE128",
    "s.GraphFreshSampling.sample.spec_0._redArg\"],[1,\"OracleSpec.QueryCache.cacheQuery._at_",
    ".SLHDSA.SHAKE128s.GraphFreshSampling.sample.spec_0._redArg._lam_0._boxed\"],[1,\"OracleS",
    "pec.QueryCache.cacheQuery._at_.SLHDSA.SHAKE128s.GraphFreshSampling.sample.spec_0._redArg",
    "._lam_0\"],[1,\"Function.update._at_.OracleSpec.QueryCache.cacheQuery._at_.SLHDSA.SHAKE1",
    "28s.GraphFreshSampling.sample.spec_0.spec_0._redArg._boxed\"],[1,\"Function.update._at_.",
    "OracleSpec.QueryCache.cacheQuery._at_.SLHDSA.SHAKE128s.GraphFreshSampling.sample.spec_0.",
    "spec_0._redArg\"],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.sample._redArg._lam_1._boxed",
    "\"],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.sample._redArg._lam_1\"],[1,\"SLHDSA.SHAKE1",
    "28s.GraphFreshSampling.sample._redArg._lam_0._boxed\"],[1,\"SLHDSA.SHAKE128s.GraphFreshS",
    "ampling.sample._redArg._lam_0\"],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.evaluate._redA",
    "rg._lam_0\"],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.evaluate._redArg\"],[0,1373,1711,1",
    "364,1712,1713,1714,1715,1716,1717,1718,1719,1720,1721,1722,1723,1724,1725,1726,1727,1728",
    ",1729,1730,1731,1732,1733,1734,1735,1736,1737,1738],[0,88,226,105],[0,88,1740,772],[0,88",
    ",1741,765],[0,34,208,51,94,1742],[0,34,176,51,95,1743],[0,34,77,51,87,1744],[0,34,50,51,",
    "75,1745],[0,34,48,40,46,1746],[0,34,39,40,46,1747],[1,\"symm\"],[0,35,224,1749],[0,66,17",
    "50,225],[0,88,1751,105],[0,88,1752,772],[0,88,1753,765],[1,\"evaluate_eq_traversal\"],[0",
    ",35,192,1755],[0,66,1756,27],[0,88,1757,131],[0,88,1758,84],[0,88,1759,94],[0,88,1760,79",
    "],[0,88,1761,65],[0,88,1762,205],[0,88,1754,1763],[0,277,208,51,94,1764],[0,277,176,51,9",
    "5,1765],[0,277,77,51,87,1766],[0,277,50,51,75,1767],[0,277,48,40,46,1768],[0,277,39,40,4",
    "6,1769],[0,9,24,954,1259,1376,1710,1739,1748,1770]],1771]",
  ] : Array String).toList

/-- Exact import-view measurements for the byte-oracle contracts. -/
private meta def frozenView : String :=
  String.join (#[
    "[[[1,\"{\\\"ambientOptions\\\":\\\"[(Elab.async, true), (linter.mathlibStandardSet, true",
    "), (pp.proofs.withType, false), (internal.cmdlineSnapshots, true), (linter.redundantVisi",
    "bility, true), (linter.style.longFile, 1500), (experimental.vcgen, true), (relaxedAutoIm",
    "plicit, false), (pp.unicode.fun, true), (autoImplicit, false)]\\\",\\\"captureOptions\\",
    "\":\\\"[(Elab.async, true), (pp.fullNames, true), (pp.proofs, true), (linter.mathlibStan",
    "dardSet, true), (pp.proofs.withType, false), (internal.cmdlineSnapshots, true), (linter.",
    "redundantVisibility, true), (linter.style.longFile, 1500), (pp.universes, true), (experi",
    "mental.vcgen, true), (relaxedAutoImplicit, false), (pp.unicode.fun, true), (autoImplicit",
    ", false), (pp.explicit, false)]\\\",\\\"imports\\\":[{\\\"importAll\\\":false,\\\"isExpo",
    "rted\\\":true,\\\"isMeta\\\":false,\\\"module\\\":\\\"Init\\\"},{\\\"importAll\\\":false",
    ",\\\"isExported\\\":true,\\\"isMeta\\\":true,\\\"module\\\":\\\"Init\\\"},{\\\"importAll",
    "\\\":false,\\\"isExported\\\":true,\\\"isMeta\\\":false,\\\"module\\\":\\\"VCVio.OracleC",
    "omp.QueryTracking.RandomOracle.Traversal\\\"},{\\\"importAll\\\":false,\\\"isExported\\",
    "\":true,\\\"isMeta\\\":false,\\\"module\\\":\\\"HashSig.SLHDSA.SHAKE128s.Proof.GraphFres",
    "hSampling\\\"},{\\\"importAll\\\":false,\\\"isExported\\\":false,\\\"isMeta\\\":true,\\",
    "\"module\\\":\\\"VCVio.Algorithms.Sha2\\\"},{\\\"importAll\\\":true,\\\"isExported\\\":f",
    "alse,\\\"isMeta\\\":false,\\\"module\\\":\\\"HashSigTest.SLHDSA.Refactor.Capture\\\"},{",
    "\\\"importAll\\\":true,\\\"isExported\\\":false,\\\"isMeta\\\":false,\\\"module\\\":\\\"",
    "HashSig.SLHDSA.SHAKE128s.Proof.GraphFreshSampling\\\"},{\\\"importAll\\\":true,\\\"isExp",
    "orted\\\":false,\\\"isMeta\\\":false,\\\"module\\\":\\\"HashSig.SLHDSA.SHAKE128s.Stateme",
    "nt.Game\\\"},{\\\"importAll\\\":true,\\\"isExported\\\":false,\\\"isMeta\\\":false,\\\"m",
    "odule\\\":\\\"HashSig.SLHDSA.SHAKE128s.Statement.RandomOracleModel\\\"},{\\\"importAll\\",
    "\":true,\\\"isExported\\\":false,\\\"isMeta\\\":false,\\\"module\\\":\\\"HashSig.SLHDSA.",
    "SHAKE128s.Statement.Scheme\\\"},{\\\"importAll\\\":true,\\\"isExported\\\":false,\\\"isM",
    "eta\\\":false,\\\"module\\\":\\\"VCVio.EvalDist.Defs.Measure.Core\\\"},{\\\"importAll\\",
    "\":true,\\\"isExported\\\":false,\\\"isMeta\\\":false,\\\"module\\\":\\\"VCVio.EvalDist.",
    "EvalDistEq\\\"},{\\\"importAll\\\":true,\\\"isExported\\\":false,\\\"isMeta\\\":false,\\",
    "\"module\\\":\\\"VCVio.EvalDist.PFunctorMeasure.Core\\\"},{\\\"importAll\\\":true,\\\"is",
    "Exported\\\":false,\\\"isMeta\\\":false,\\\"module\\\":\\\"VCVio.EvalDist.ProbabilityNot",
    "ation\\\"},{\\\"importAll\\\":true,\\\"isExported\\\":false,\\\"isMeta\\\":false,\\\"mod",
    "ule\\\":\\\"VCVio.OracleComp.Constructions.SampleableType.Basic\\\"},{\\\"importAll\\\":",
    "true,\\\"isExported\\\":false,\\\"isMeta\\\":false,\\\"module\\\":\\\"VCVio.OracleComp.E",
    "valDist.AnswerMeasure\\\"},{\\\"importAll\\\":true,\\\"isExported\\\":false,\\\"isMeta\\",
    "\":false,\\\"module\\\":\\\"VCVio.OracleComp.OracleComp\\\"},{\\\"importAll\\\":true,\\",
    "\"isExported\\\":false,\\\"isMeta\\\":false,\\\"module\\\":\\\"VCVio.OracleComp.OracleQu",
    "ery\\\"},{\\\"importAll\\\":true,\\\"isExported\\\":false,\\\"isMeta\\\":false,\\\"modul",
    "e\\\":\\\"VCVio.OracleComp.OracleSpec\\\"},{\\\"importAll\\\":true,\\\"isExported\\\":fa",
    "lse,\\\"isMeta\\\":false,\\\"module\\\":\\\"VCVio.OracleComp.ProbComp.Basic\\\"},{\\\"im",
    "portAll\\\":true,\\\"isExported\\\":false,\\\"isMeta\\\":false,\\\"module\\\":\\\"VCVio.",
    "OracleComp.QueryTracking.CachingOracle\\\"},{\\\"importAll\\\":true,\\\"isExported\\\":f",
    "alse,\\\"isMeta\\\":false,\\\"module\\\":\\\"VCVio.OracleComp.QueryTracking.RandomOracle",
    ".Basic\\\"},{\\\"importAll\\\":true,\\\"isExported\\\":false,\\\"isMeta\\\":false,\\\"mo",
    "dule\\\":\\\"VCVio.OracleComp.QueryTracking.RandomOracle.Traversal\\\"},{\\\"importAll\\",
    "\":true,\\\"isExported\\\":false,\\\"isMeta\\\":false,\\\"module\\\":\\\"VCVio.OracleCom",
    "p.QueryTracking.Structures\\\"},{\\\"importAll\\\":true,\\\"isExported\\\":false,\\\"isM",
    "eta\\\":false,\\\"module\\\":\\\"VCVio.OracleComp.SimSemantics.QueryImpl.Basic\\\"},{\\",
    "\"importAll\\\":true,\\\"isExported\\\":false,\\\"isMeta\\\":false,\\\"module\\\":\\\"VC",
    "Vio.OracleComp.SimSemantics.SimulateQ\\\"}],\\\"mainModule\\\":[\\\"str\\\",[\\\"str\\\"",
    ",[\\\"str\\\",[\\\"str\\\",[\\\"anonymous\\\"],\\\"HashSigTest\\\"],\\\"SLHDSA\\\"],\\\"",
    "Refactor\\\"],\\\"GraphSampler\\\"],\\\"namespace\\\":[\\\"str\\\",[\\\"str\\\",[\\\"str",
    "\\\",[\\\"anonymous\\\"],\\\"SLHDSA\\\"],\\\"SHAKE128s\\\"],\\\"GraphSamplerCompatibilit",
    "y\\\"],\\\"openDecls\\\":[[\\\"simple\\\",[\\\"str\\\",[\\\"str\\\",[\\\"str\\\",[\\\"an",
    "onymous\\\"],\\\"SLHDSA\\\"],\\\"Refactor\\\"],\\\"R0\\\"],[]],[\\\"simple\\\",[\\\"str",
    "\\\",[\\\"str\\\",[\\\"anonymous\\\"],\\\"Lean\\\"],\\\"Meta\\\"],[]],[\\\"simple\\\",[",
    "\\\"str\\\",[\\\"str\\\",[\\\"str\\\",[\\\"anonymous\\\"],\\\"Lean\\\"],\\\"Elab\\\"],\\",
    "\"Command\\\"],[]],[\\\"simple\\\",[\\\"str\\\",[\\\"str\\\",[\\\"anonymous\\\"],\\\"Lea",
    "n\\\"],\\\"Elab\\\"],[]],[\\\"simple\\\",[\\\"str\\\",[\\\"anonymous\\\"],\\\"Lean\\\"],",
    "[]],[\\\"simple\\\",[\\\"str\\\",[\\\"anonymous\\\"],\\\"OracleSpec\\\"],[]],[\\\"simple",
    "\\\",[\\\"str\\\",[\\\"anonymous\\\"],\\\"OracleComp\\\"],[]]]}\"],[1,\"SLHDSA.SHAKE128s",
    ".GraphFreshSampling.FreshFor\"],[3,false],[3,true],[0,1,2,3],[1,\"SLHDSA.SHAKE128s.Graph",
    "FreshSampling.Separated\"],[0,5,2,3],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.evaluate\"",
    "],[0,7,2,3],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.program\"],[0,9,2,3],[1,\"SLHDSA.SH",
    "AKE128s.GraphFreshSampling.sample\"],[0,11,2,3],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling",
    ".evaluate._f\"],[0,13,2,3],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.evaluate._sunfold\"]",
    ",[0,15,2,3],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.evaluate._unsafe_rec\"],[0,17,2,3],",
    "[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.evaluate.match_1\"],[0,19,2,3],[1,\"SLHDSA.SHAK",
    "E128s.GraphFreshSampling.program._f\"],[0,21,2,3],[1,\"SLHDSA.SHAKE128s.GraphFreshSampli",
    "ng.program._sunfold\"],[0,23,2,3],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.program._unsa",
    "fe_rec\"],[0,25,2,3],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.sample._f\"],[0,27,2,3],[1",
    ",\"SLHDSA.SHAKE128s.GraphFreshSampling.sample._sunfold\"],[0,29,2,3],[1,\"SLHDSA.SHAKE12",
    "8s.GraphFreshSampling.sample._unsafe_rec\"],[0,31,2,3],[1,\"SLHDSA.SHAKE128s.GraphFreshS",
    "ampling.sample.match_1\"],[0,33,2,3],[1,\"_private.HashSig.SLHDSA.SHAKE128s.Proof.GraphF",
    "reshSampling.0.SLHDSA.SHAKE128s.GraphFreshSampling.evaluate.match_1.splitter\"],[0,35,2,",
    "3],[1,\"_private.HashSig.SLHDSA.SHAKE128s.Proof.GraphFreshSampling.0.SLHDSA.SHAKE128s.Gr",
    "aphFreshSampling.sample.match_1.splitter\"],[0,37,2,3],[0,4,6,8,10,12,14,16,18,20,22,24,",
    "26,28,30,32,34,36,38],[1,\"261fbcc3b8fb7eba1262beaba74612ee8617714255df4489830437bdfef75",
    "c8a\"],[0,1,40,40],[1,\"4773ef921cb6019321f276d6d77414b2da0f655ca18cccb5b400658f78dba2c6",
    "\"],[0,5,42,42],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.evalDist_evaluate_eq_uniform_pr",
    "ogram\"],[1,\"f67f56f1e3ad83baddbc5cddc6017de63ac08f494feb9377f4ba002bf2d48727\"],[1,\"6",
    "fdf39004f4570dac55473640ce4939cc646af6499939fb47b9c407b4a1bf736\"],[0,44,45,46],[1,\"SLH",
    "DSA.SHAKE128s.GraphFreshSampling.evalDist_sample_eq_uniform_program\"],[1,\"854affa65cc5",
    "d7218ca46178b71086743b8224e6d1dece5c69be5ee7b336bcba\"],[1,\"be9cf0db28990617f2133e390d1",
    "c033d082690feef3bb8f3d1c398345264f85f\"],[0,48,49,50],[1,\"4b14d17ecb943e38762a816432245",
    "000f94f8e7364a1f438448e56e1d24a6d1e\"],[0,7,52,52],[1,\"SLHDSA.SHAKE128s.GraphFreshSampl",
    "ing.evaluate_eq_sample\"],[1,\"84be8dcc96a00bfb457ea546e52ef48c49f9f3f0af440a9a66ab99831",
    "f5a9297\"],[0,54,55,55],[1,\"b460bf4ab068eb10c2552797d1e7758bdef72870325bd9c767f1f66d3d6",
    "c7709\"],[0,9,57,57],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.program_congr\"],[1,\"25f0",
    "8fbc692a89115eddae7c05fec958b2bc2c583f8c3a2ff1af026981adc9c6\"],[0,59,60,60],[1,\"SLHDSA",
    ".SHAKE128s.GraphFreshSampling.program_update_outside\"],[1,\"35a5a887e36f2dd265282985c5f",
    "9eba8b411765235780aa15212d8eed766358d\"],[0,62,63,63],[1,\"6ae0510ec3094268d0c9dc3ae4cd9",
    "7f91a185238f115c0f467c14fec72f567e3\"],[0,11,65,65],[1,\"SLHDSA.SHAKE128s.GraphSamplerCo",
    "mpatibility.evalDist_evaluate_eq_uniform_program\"],[0,67,45,46],[1,\"SLHDSA.SHAKE128s.G",
    "raphSamplerCompatibility.evalDist_sample_eq_uniform_program\"],[0,69,49,50],[1,\"SLHDSA.",
    "SHAKE128s.GraphSamplerCompatibility.evaluate_eq_byteTraversal\"],[1,\"4ade9bdb3bad1107cb",
    "c139db7a19da56f7ef77b44b283f468b9ec66589c07c16\"],[0,71,72,72],[1,\"SLHDSA.SHAKE128s.Gra",
    "phSamplerCompatibility.evaluate_eq_sample\"],[0,74,55,55],[1,\"SLHDSA.SHAKE128s.GraphSam",
    "plerCompatibility.freshFor_iff_byteTraversal\"],[1,\"fb0986fbdf9122abb37cd84cd505582b015",
    "3ebed0df03baccf1444472ca0ffb9\"],[0,76,77,77],[1,\"SLHDSA.SHAKE128s.GraphSamplerCompatib",
    "ility.program_congr\"],[0,79,60,60],[1,\"SLHDSA.SHAKE128s.GraphSamplerCompatibility.prog",
    "ram_eq_byteTraversal\"],[1,\"ca7c905f51b1b844d470f088766351798b1536bdb103c1f973546e39896",
    "e21c0\"],[0,81,82,82],[1,\"SLHDSA.SHAKE128s.GraphSamplerCompatibility.program_update_out",
    "side\"],[0,84,63,63],[1,\"SLHDSA.SHAKE128s.GraphSamplerCompatibility.sample_eq_byteTrave",
    "rsal\"],[1,\"05d3d0301bd3cd7380163eea1ca5eb4092d989b4c878e9594b16819247cb5cea\"],[0,86,8",
    "7,87],[1,\"SLHDSA.SHAKE128s.GraphSamplerCompatibility.separated_iff_byteTraversal\"],[1,",
    "\"9d0d6f759711d21ce2b1f917b5068ddebd377069eab1be569a204646346956e1\"],[0,89,90,90],[1,\"",
    "d2914f387853c01efe3bdb727eab62d2078a50b676958e0cda20a7ed706677e6\"],[1,\"d187f19e43a5779",
    "ff432f8459e1e07c3aee3da3e47660ba3e41d1df06f71d8cf\"],[0,13,92,93],[0,15,52,52],[0,17,52,",
    "52],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.evaluate.eq_1\"],[1,\"258df47c1bf409bcc6ed4",
    "29a931b5ab36860aa291b0b9311dcfe532e7e5c690f\"],[0,97,98,98],[1,\"SLHDSA.SHAKE128s.GraphF",
    "reshSampling.evaluate.eq_2\"],[1,\"eea24650b63e64c7be0012abb1d2434b7b9885f9abb83135b66f4",
    "908c6177006\"],[0,100,101,101],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.evaluate.eq_def",
    "\"],[1,\"b85cc99a6afbd9b24b50c36d9d45b29c2a8a7ae7b48d4201ebd96fc08f0597a2\"],[0,103,104,",
    "104],[1,\"359c52e53852446892f565f581c4df92568f15b183bd4e33aacfcf79d4924397\"],[0,19,106,",
    "106],[1,\"2844715594febb210073141a7b8dc6fa7b095d2ef0a907f5c8c03edb94f7e3d2\"],[1,\"7e6c9",
    "86565bf253f95dc54371ea14f48de088e74aaf04dace4bd7cc0985644c4\"],[0,21,108,109],[0,23,57,5",
    "7],[0,25,57,57],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.program.eq_1\"],[1,\"9af185783c",
    "8de4888a01366847a6bcd6e78b75afa86c362d4850ad9421f4778b\"],[0,113,114,114],[1,\"SLHDSA.SH",
    "AKE128s.GraphFreshSampling.program.eq_2\"],[1,\"7464dec46e8bc930dde61d9d885cd9192ca405fe",
    "c0c914563e018cc988d188a7\"],[0,116,117,117],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.pro",
    "gram.eq_def\"],[1,\"046916da98eab95fb4561be0b1d782b0472bf719d273c495dbe48087ff7b5f24\"],",
    "[0,119,120,120],[1,\"9deb30b98a4314ac3f7758f81b9434ed8955bb11c79480a6b0c518f24b5eb0fb\"]",
    ",[1,\"c92599e82e5b8f752c506311e10b9648df13e94c334f9e2af4e6375b3824cdd9\"],[0,27,122,123]",
    ",[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.sample._proof_1\"],[1,\"409a49ec50f3f93ee258d4",
    "4d3664d75d80a3650a06138ef6be97c4c1aec07e3d\"],[0,125,126,126],[0,29,65,65],[0,31,65,65],",
    "[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.sample.eq_1\"],[1,\"746e9bdc8101c8fc18db441263c",
    "637afef25c0185cd3ba92f0fe9d540a1d93a6\"],[0,130,131,131],[1,\"SLHDSA.SHAKE128s.GraphFres",
    "hSampling.sample.eq_2\"],[1,\"50c0a425f3d6e2c35b2b98f8848837bd08662af3a1a3c217451ceae71e",
    "698b0a\"],[0,133,134,134],[1,\"SLHDSA.SHAKE128s.GraphFreshSampling.sample.eq_def\"],[1,",
    "\"6ddf9147f537483fd0624000412288ef5e4877d7cab351eafa0132522584ecf4\"],[0,136,137,137],[1",
    ",\"631cc996defc7a9b388e9b572f30b24219ea4a3acde770c4e64dda2a89c08c4a\"],[0,33,139,139],[1",
    ",\"_private.HashSig.SLHDSA.SHAKE128s.Proof.GraphFreshSampling.0.SLHDSA.SHAKE128s.GraphFr",
    "eshSampling.evaluate.match_1.eq_1\"],[1,\"9a3d4d79484d7f0b559b336bfea6553e2f3723d682bccb",
    "d6e1b758cfbe7ef1d3\"],[0,141,142,142],[1,\"_private.HashSig.SLHDSA.SHAKE128s.Proof.Graph",
    "FreshSampling.0.SLHDSA.SHAKE128s.GraphFreshSampling.evaluate.match_1.eq_2\"],[1,\"e4ea34",
    "d5c02d5b576484e367b9e00977be96eb3302ab8f2a35ecce78461eaebb\"],[0,144,145,145],[0,35,106,",
    "106],[1,\"_private.HashSig.SLHDSA.SHAKE128s.Proof.GraphFreshSampling.0.SLHDSA.SHAKE128s.",
    "GraphFreshSampling.sample.match_1.eq_1\"],[1,\"02ae7020b9db69844219325de8e9a25f56bb3da62",
    "62324a91795ef592499f3eb\"],[0,148,149,149],[1,\"_private.HashSig.SLHDSA.SHAKE128s.Proof.",
    "GraphFreshSampling.0.SLHDSA.SHAKE128s.GraphFreshSampling.sample.match_1.eq_2\"],[1,\"d5e",
    "ee51ff3b3abdb3cabe043768746f16d4d4943aed9ff1e14e0e43fb6493b13\"],[0,151,152,152],[0,37,1",
    "39,139],[0,41,43,47,51,53,56,58,61,64,66,68,70,73,75,78,80,83,85,88,91,94,95,96,99,102,1",
    "05,107,110,111,112,115,118,121,124,127,128,129,132,135,138,140,143,146,147,150,153,154],",
    "[1,\"SLHDSA.SHAKE128s.HashSpec\"],[1,\"261961a874db1afad26b06823983a8c11319d5598d51b0808",
    "92c68b165954cb4\"],[0,156,157,157],[1,\"SLHDSA.SHAKE128s.RandomOracleModel.HashSpec\"],[",
    "1,\"d8495e9d9212e098f3aa31f88c038abe1a37de7706046f1408d48efaec0095d6\"],[0,159,160,160],",
    "[1,\"OracleSpec.ofFn\"],[1,\"1c4490c772562cf754194d75bfdf20f8469a4a3fbeb94d4c1b8ef8e1dca",
    "6290c\"],[0,162,163,163],[1,\"OracleSpec\"],[1,\"e72b2d41f7a3dc52504b38589837175015fc4e1",
    "78a8c8725f4f2ea6e1d8f9616\"],[0,165,166,166],[1,\"SLHDSA.SHAKE128s.HashOutput\"],[1,\"c4",
    "4f7ab8bbd24858d1bd1ab995f21c5f52c6a671907b29ed3a4b094345f70b21\"],[0,168,169,169],[1,\"S",
    "LHDSA.SHAKE128s.messageDigestBytes\"],[1,\"112278faf8ba77ee5ec02ca84556e29d3bb1b56bbc117",
    "bee16fbca2231b06ab9\"],[0,171,172,172],[1,\"SLHDSA.SHAKE128s.Bytes\"],[0,174,169,169],[1",
    ",\"OracleSpec.QueryCache\"],[1,\"c140091d993bdf82d0851bd2c0b4d13c85870da9a37b58ac7ad1420",
    "03e973db9\"],[0,176,177,177],[1,\"OracleSpec.QueryCache.mk\"],[1,\"45a5b39bfe490044d6415",
    "96e13ed6d51c9a07f20a53ce0fa1a5703dbb3c97e13\"],[0,179,180,180],[1,\"OracleSpec.Range\"],",
    "[1,\"cc55e113b69c23d75b0247fc959b191757b417e574f4a331129f990a789c7d41\"],[0,182,183,183]",
    ",[1,\"OracleSpec.Domain\"],[1,\"16c92baa1e40d22c758be021e18639534164af6be9d2b00a2bf0a7fc",
    "921823e4\"],[0,185,186,186],[1,\"OracleSpec.QueryCache.cacheQuery\"],[1,\"f2a9d0bbacd587",
    "40c412f3fdc606e19c8d173bd8edce89c6289fe0964eedc561\"],[0,188,189,189],[1,\"OracleSpec.Qu",
    "eryCache.toFn\"],[1,\"ed136a4d1b7f65d72c2b6149cc0718d1544ce68c2602525e2d601573354112f7\"",
    "],[0,191,192,192],[1,\"OracleSpec.QueryCache.ofFn\"],[1,\"66f8665635c55372ee72f8d3bb2761",
    "b7dfd358333eb54ce32e97556a23f17c46\"],[0,194,195,195],[1,\"OracleSpec.toPFunctor\"],[1,",
    "\"3319425a765048951c3832ace497087aedee332671bdd33ded18b33c0395a1be\"],[0,197,198,198],[1",
    ",\"OracleSpec.query\"],[1,\"ce9df30a8b15af789738db7a1f640ff6c833aebe323141302e2c6b4108f6",
    "9478\"],[0,200,201,201],[1,\"OracleQuery.mk\"],[1,\"edb1a5bc81822b33f15b5685e952e75da46f",
    "ba08f987c1c630dbd941ab8dad4f\"],[0,203,204,204],[1,\"OracleQuery\"],[1,\"99826a778851916",
    "643b1799ba92ee06fe386439cd7029732b77d307d37d23794\"],[0,206,207,207],[1,\"OracleComp\"],",
    "[0,209,207,207],[1,\"OracleSpec.UniformAnswerMeasure.unifSpec\"],[1,\"9752a63fe5ba68a31b",
    "bf762a976460253ec4bc0025d38fc83353a72c11337698\"],[0,211,212,212],[1,\"_private.VCVio.Or",
    "acleComp.EvalDist.AnswerMeasure.0.OracleSpec.UniformAnswerMeasure.unifSpec._proof_2\"],[",
    "1,\"7f32f9d3bd5a2409d13c3bd5e6bee170039440aa506fd876f57ee618d6d9e2b3\"],[0,214,215,215],",
    "[1,\"unifSpec\"],[1,\"d3d3c586ef2610250e59e097d488ad3c260641084bbac21574ada2ad47a650c7\"",
    "],[0,217,218,218],[1,\"_private.VCVio.OracleComp.EvalDist.AnswerMeasure.0.OracleSpec.Uni",
    "formAnswerMeasure.unifSpec._proof_1\"],[1,\"c9d06d94e7f425076170e6e611ae81e699a9977d3bdf",
    "e02ead8e4c8a960b7923\"],[0,220,221,221],[1,\"OracleSpec.UniformAnswerMeasure.ofFiniteNon",
    "empty\"],[1,\"0677e3a69706f17826c40920c7895fc95142762c9ba805c86d231ced666a3b2c\"],[0,223",
    ",224,224],[1,\"OracleSpec.UniformAnswerMeasure.ofFiniteNonempty._proof_2\"],[1,\"1c1aa46",
    "d03e4f59c193c396ed82e8fc0220accc671319a28fc4c45d7b036f884\"],[0,226,227,227],[1,\"Oracle",
    "Spec.UniformAnswerMeasure.ofFiniteNonempty._proof_1\"],[1,\"1dc153df28d94002f353426f3739",
    "867f45c14f0fa2746c2dbb1470404f936369\"],[0,229,230,230],[1,\"PFunctor.AnswerMeasure.mk\"",
    "],[1,\"3c563ab28971de8933f5fcb44bc6adb2b28387310721fc90fab2e49c3f342665\"],[0,232,233,23",
    "3],[1,\"PFunctor.AnswerMeasure\"],[1,\"fdbb540ca4103ba1e4c84a9e889ef07dffa86fbbbd86f830a",
    "5d18f8b00e0439d\"],[0,235,236,236],[1,\"OracleSpec.UniformAnswerMeasure.mk\"],[1,\"60854",
    "0f0d1c9d6735c6c53fe8cbc9adbcb462ff028909e80cbcbea5ea7ce8ade\"],[0,238,239,239],[1,\"PFun",
    "ctor.AnswerMeasure.toMeasure\"],[1,\"4382015f1691dc3c585b18d51ad4351a01e18d7ba940bb1ad4f",
    "521ea1390ae69\"],[0,241,242,242],[1,\"OracleSpec.UniformAnswerMeasure\"],[0,244,177,177]",
    ",[1,\"OracleSpec.UniformAnswerMeasure.toAnswerMeasure\"],[1,\"22293aec90e5c7dd86128a9482",
    "5398917ed7fd1f01f3d53e42d14ed8c71de7bf\"],[0,246,247,247],[1,\"OracleSpec.randomOracle\"",
    "],[1,\"064d30ba01c33f9543cf72b7e4895e61c5f798ad2ec087a9bfd602d1ea9932c4\"],[0,249,250,25",
    "0],[1,\"QueryImpl.withCaching\"],[1,\"3d1bd0fcc2ef95e60fd47b980f401d0e9e9fe8dd2680adba2a",
    "ee541e3a4724a5\"],[0,252,253,253],[1,\"QueryImpl.withCaching.match_1\"],[1,\"e61c4a49774",
    "b99c7b4d405909d68c444a3abb833f9d3730dcbd4634e6f54b356\"],[0,255,256,256],[1,\"QueryImpl",
    "\"],[1,\"b5b1905940e6b4b9b47d88e6876aa073f3261a684ade780d9507c6db0bff351c\"],[0,258,259,",
    "259],[1,\"uniformSampleImpl\"],[1,\"746e84bca890408ea6813bc018030f8e8aba357a718a50817d40",
    "c64dd6917eec\"],[0,261,262,262],[1,\"uniformSample\"],[1,\"61fe05c1ceb6739c92cc267c196be",
    "1560d8ae6fa06e87c7281db2c6e17b301d0\"],[0,264,265,265],[1,\"SampleableType.selectElem\"]",
    ",[1,\"038be6c3385c3ce9af89be59fe41541d56961a7c30cc4c2866fc091bb9906a2a\"],[0,267,268,268",
    "],[1,\"SampleableType\"],[1,\"dd1ae3dd61bdd453e49159f6db096b9351cecff881e8fa1ad8d7d0c50e",
    "ba7dc7\"],[0,270,271,271],[1,\"SampleableType.mk\"],[1,\"0a90fdd780ed7e1d0bd673a805d72c0",
    "115f4b2a7d2bb48818fd1095f4e933c9e\"],[0,273,274,274],[1,\"OracleComp.instEvalDistSemanti",
    "cs\"],[1,\"949d2958f229f39c799429c34a48faac5b82e47d737228734c615d1f95dfd578\"],[0,276,27",
    "7,277],[1,\"PFunctor.FreeM.instEvalDistSemanticsFreeM\"],[1,\"5d4a9cd6f18eed0f5f269d3105",
    "43061ec596d562dae3fc8964282d6269944625\"],[0,279,280,280],[1,\"PFunctor.FreeM.denote_app",
    "ly_univ_le_one\"],[1,\"157acc98429ac01ab9ae10bde353aabbcb1528656207999534705e53fbf57c37",
    "\"],[0,282,283,283],[1,\"PFunctor.FreeM.denote\"],[1,\"3e8aa85063cff160d9c884e37d792d367",
    "090f3c5531abab89e6024ec466572e4\"],[0,285,286,286],[1,\"PFunctor.FreeM.denote._f\"],[1,",
    "\"9188e01c4aa4de731a0b2e4e53ee96dfadf12722c1c79bacdd53a06b2e09d584\"],[0,288,289,289],[1",
    ",\"PFunctor.FreeM.denote.match_1\"],[1,\"ad29abf490b16de3b47c5d6936ed84a464b8ac9531633e9",
    "364a1ffd6b45d66df\"],[0,291,292,292],[1,\"EvalDistSemantics.mk\"],[1,\"bb511301906e47e9a",
    "b67dcecde06b24041b51bed78b925e76564e2fa4532705d\"],[0,294,295,295],[1,\"EvalDistSemantic",
    "s\"],[1,\"09648f7e790e96a4b70886a8b1b208d8633e117c72b3b2b6623257397182e202\"],[0,297,298",
    ",298],[1,\"OracleSpec.AnswerMeasure\"],[1,\"ad62e7330b91bdbfdedc6de1699dff9e4c50469e9574",
    "4de065e38c7b4d00b3a6\"],[0,300,301,301],[1,\"evalDist\"],[1,\"cd3092704f7006f66f179f8509",
    "fff923926ec6e76ca348945219135051185142\"],[0,303,304,304],[1,\"EvalDistSemantics.denote",
    "\"],[1,\"1020f913b91329e523c29ec78510211bafc673cf7bfbd084b07bf03e38579023\"],[0,306,307,",
    "307],[1,\"ProbComp\"],[0,309,271,271],[1,\"FinEnum.SampleableType\"],[1,\"fd6e27f16f6b02",
    "4961996e5f3c4af7bdcd22da621e6d3ef92fd75efa03da644e\"],[0,311,312,312],[1,\"FinEnum.Sampl",
    "eableType._proof_1\"],[1,\"0d73f9cb9d6fbdfb4d407026a2f0be30f08508b0024214b6f4f1ee54f08e8",
    "af3\"],[0,314,315,315],[1,\"SampleableType.ofEquiv\"],[1,\"fbe0b8ddbbcc88c1aefae4e24a7a0",
    "86f96fa53cf6e9e35958e268ff2a2bd4a44\"],[0,317,318,318],[1,\"SampleableType.ofEquiv._proo",
    "f_1\"],[1,\"ebd38366a0259e542139109f151ebafdcf5fd4b02f4b7e55f88f65b91569a606\"],[0,320,3",
    "21,321],[1,\"instSampleableTypeFinOfNeZeroNat\"],[1,\"ccb040625e60cd9091f44491a83f645386",
    "91decb737ea3617ccd6f9f20a3014b\"],[0,323,324,324],[1,\"instSampleableTypeFinOfNeZeroNat.",
    "match_1\"],[1,\"680087c6f981f8b236cc1f9c6705a30f4a0cd89ebfffe5926d9ca1610a505a96\"],[0,3",
    "26,327,327],[1,\"SampleableType.Fin\"],[1,\"d8dc408365d2978b0385616c06398f764b0fb49f41f1",
    "79838929025e3b54f440\"],[0,329,330,330],[1,\"SampleableType.Fin._proof_1\"],[1,\"7ae83e1",
    "4fc13c8fa90e5a00904410537018508e7d80d70dc4b0d8c845a842a8c\"],[0,332,333,333],[1,\"ProbCo",
    "mp.uniformFin\"],[1,\"fab781bce279b1ac98321efb7ffd0a5279a95c677653d6698b78eb63c7d38005\"",
    "],[0,335,336,336],[1,\"simulateQ\"],[1,\"ae143b5652d31474dc8e4a653314826df767f8e7254ef73",
    "02e40f89bf649c40a\"],[0,338,339,339],[1,\"instSampleableTypePiFintype\"],[1,\"9ee3c1d416",
    "10e45db489869c62b07397b8e918dc1aa51625cf7b09a96da2b428\"],[0,341,342,342],[1,\"instSampl",
    "eableTypeFinFunc\"],[1,\"271bccfe4ed37fb494be88166cc997c1311146c6200060af024490f72048d64",
    "3\"],[0,344,345,345],[1,\"instSampleableTypeVector\"],[1,\"91d15375975a4423d79fbc000e05d",
    "96d0c6320d37b4cb787cc522fcec16d4080\"],[0,347,348,348],[1,\"SampleableType.vector\"],[1,",
    "\"aa11c181839368e722a09ef430b7d338dbe316b9f1da68489babb48408fa3004\"],[0,350,351,351],[1",
    ",\"SampleableType.vector._f\"],[1,\"80936504429f3a31b6603cb2613f818f1baf036087042f88ea3d",
    "cadac4b74cd1\"],[0,353,354,354],[1,\"_private.VCVio.OracleComp.Constructions.SampleableT",
    "ype.Basic.0.SampleableType.vector.match_1\"],[1,\"f4ff6894edf0eaebc37c4e41e033b482aca388",
    "ff052bcfb4f6d00e3bd872ad8d\"],[0,356,357,357],[1,\"SampleableType.evalDist_vector\"],[1,",
    "\"6e3441c61ddc7032febf1470c20c12017af9b78d109e3e6dd168da75982ebec7\"],[0,359,360,360],[1",
    ",\"arrayVectorEquivFin\"],[1,\"0196d35d3dee235b64b5b144bf394f8d143dbe528b75aa4c114e91f0f",
    "d00da7b\"],[0,362,363,363],[1,\"arrayVectorEquivFin._proof_5\"],[1,\"3c5429a4f2efb3da83b",
    "223fea2ab3e4722fb9011d1c5fe22acad5b849f17aadf\"],[1,\"e35375e9285ec87ccc30b901355cbe6d57",
    "f84de4f6595cc4ac085bd028086f03\"],[0,365,366,367],[1,\"arrayVectorEquivFin._proof_2\"],[",
    "1,\"9072213e1984444b619ee28d5701b108067b8be55b410d2c967f73b475b0134f\"],[0,369,370,370],",
    "[1,\"arrayVectorEquivFin._proof_3\"],[1,\"fe0fcf23a7eca20282aa78a50b51e21b9476f6719652f3",
    "353f97d8c90c27ac0d\"],[1,\"fd3c466eef6d43cb6da37f1c6d30bdb1521f9d825638bedc3f92a2cbe0302",
    "d52\"],[0,372,373,374],[1,\"EvalDistEq\"],[1,\"54e34e8b87cbb3bbec412e79c7162532168818456",
    "006e10585caa12ecbe67cc2\"],[0,376,377,377],[1,\"prEvent\"],[1,\"63d38d88b37938066d86867e",
    "55d45f3d2c51b2213a9f47239f1074805ea27abd\"],[0,379,380,380],[1,\"OracleComp.RandomOracle",
    "Traversal.FreshFor\"],[1,\"d8de9d1daafbbac9f71e2f28f2c4cb313a01cb0d655633100899ff170d19b",
    "3e0\"],[1,\"c533080147d10751d1a36fcfbf48b2bf1088bf0d682ea89a01bb205ecd012965\"],[0,382,3",
    "83,384],[1,\"OracleComp.RandomOracleTraversal.Separated\"],[1,\"4d84541985adb883c75e347e",
    "99759ed6028074998e71726b291790f59956a45d\"],[0,386,387,387],[1,\"OracleComp.RandomOracle",
    "Traversal.program\"],[1,\"18ba8170b76735b52f94d7475cd9b15ae515bf8ca313018473292d40c91e92",
    "8b\"],[1,\"28ea366116ea121c679f22227c69591bc95dd1d8ab1e57bac930fdd6b2a6b048\"],[0,389,39",
    "0,391],[1,\"OracleComp.RandomOracleTraversal.program._f\"],[1,\"ef58e1cf3d07da6644f20ce5",
    "47b1936fa17299602eeb77b3699e276c9b2424aa\"],[1,\"583386160a5f8719a4ce9a14abf3c28aad0a21c",
    "10980975124aea7214b278c3d\"],[0,393,394,395],[1,\"OracleComp.RandomOracleTraversal.progr",
    "am.match_1\"],[1,\"593c0d73d48908588a209f6be76908643001bc870b7d4b9eec3577bd7351e1b3\"],[",
    "1,\"5843c5c84d655e3853f2706e401fb554d7305ec073d39d0140764eec17e5bfb6\"],[0,397,398,399],",
    "[1,\"OracleComp.RandomOracleTraversal.sample\"],[1,\"7d997ca8e30d6f4fa7fe18995bbd5e85976",
    "d90d79610e9c6e03b27381643b810\"],[1,\"86fbad012e21b3b31af6fbba30675e1cd77ae8ca8fec1de56c",
    "eef72cd2d9d4d9\"],[0,401,402,403],[1,\"OracleComp.RandomOracleTraversal.sample._f\"],[1,",
    "\"5450fbed847863f251eeeac434c0d52cbd6c4c3dbbef413372060ba33c27ecb1\"],[1,\"f0d173573f7e8",
    "3a1b52d88b079fabd443bb565bdfd2dcd87fc248f0ec369c15f\"],[0,405,406,407],[1,\"OracleComp.R",
    "andomOracleTraversal.evaluate\"],[1,\"abe24f2a091de8c48e6fbe88cd6c848d634462406357e8e57c",
    "77d59bce6b27f6\"],[1,\"25cead9f6ca9f428f80cf36eb9f47ec0eea75935246b8d1cec025b579f75c643",
    "\"],[0,409,410,411],[1,\"OracleComp.RandomOracleTraversal.evaluate._f\"],[1,\"1ed0888911",
    "0ff593c6dabf9f3a46102165c3b410f24aaba9dcf8fcf237782269\"],[1,\"a6d50c20c75df7c4838701bcd",
    "c724c94c7183fbb2644e3ab4753857188c112b0\"],[0,413,414,415],[1,\"OracleComp.RandomOracleT",
    "raversal.evaluate.match_1\"],[0,417,106,106],[0,68,58,110,140,158,161,164,167,170,173,17",
    "5,178,181,184,187,190,193,196,53,94,107,199,202,205,208,210,43,41,213,216,219,222,225,22",
    "8,231,234,237,240,243,245,248,251,254,257,260,263,266,269,272,275,278,281,284,287,290,29",
    "3,296,299,302,305,308,310,313,316,319,322,325,328,331,334,337,340,343,346,349,352,355,35",
    "8,361,364,368,371,375,378,381,70,66,124,85,80,75,78,385,91,388,83,392,396,400,88,404,408",
    ",73,412,416,418,47,51,64,61,56],[0,7,13,19,156,159,162,165,168,171,174,197,200,182,185,2",
    "03,206,209],[1,\"propext\"],[1,\"Quot.sound\"],[0,421,422],[0,1,3],[0,5,3],[0,44,3],[0,4",
    "8,3],[0,7,3],[0,54,3],[0,9,3],[0,59,3],[0,62,3],[0,11,3],[0,67,3],[0,69,3],[0,71,3],[0,7",
    "4,3],[0,76,3],[0,79,3],[0,81,3],[0,84,3],[0,86,3],[0,89,3],[0,13,3],[0,15,3],[0,17,3],[0",
    ",97,3],[0,100,3],[0,103,3],[0,19,3],[0,21,3],[0,23,3],[0,25,3],[0,113,3],[0,116,3],[0,11",
    "9,3],[0,27,3],[0,125,3],[0,29,3],[0,31,3],[0,130,3],[0,133,3],[0,136,3],[0,33,3],[0,141,",
    "3],[0,144,3],[0,35,3],[0,148,3],[0,151,3],[0,37,3],[0,424,425,426,427,428,429,430,431,43",
    "2,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,45",
    "4,455,456,457,458,459,460,461,462,463,464,465,466,467,468,469,470],[0,0,39,155,419,420,4",
    "23,471]],472]",
  ] : Array String).toList

/-- Check closed types, exact computation, and the public construction witness together. -/
private meta def checkConstruction : CommandElabM Unit := do
  let packed ← Lean.ofExcept ((← Lean.ofExcept (Json.parse frozenConstruction)).getArr?)
  let expanded ← Lean.ofExcept (expandDag (← Lean.ofExcept packed[0]!.getArr?))
  let root ← Lean.ofExcept packed[1]!.getNat?
  let parts ← Lean.ofExcept expanded[root]!.getArr?
  let fields ← Lean.ofExcept (fromJson? parts[0]! : Except String (Array String))
  let attributes ← Lean.ofExcept (fromJson? parts[1]! : Except String (Array String))
  let types ← Lean.ofExcept parts[2]!.getArr?
  let records ← Lean.ofExcept parts[3]!.getArr?
  let owners ← Lean.ofExcept parts[4]!.getArr?
  let boundary ← Lean.ofExcept parts[5]!.getArr?
  let extras ← Lean.ofExcept parts[6]!.getArr?
  unless types.size == 20 && records.size == 111 && owners.size == 47 &&
      boundary.size == 157 && extras.size == 30 do throwError "Construction coverage changed"
  let viewPacked ← Lean.ofExcept ((← Lean.ofExcept (Json.parse frozenView)).getArr?)
  let viewNodes ← Lean.ofExcept (expandDag (← Lean.ofExcept viewPacked[0]!.getArr?))
  let viewRoot ← Lean.ofExcept viewPacked[1]!.getNat?
  let view ← Lean.ofExcept viewNodes[viewRoot]!.getArr?
  let expectedContext ← Lean.ofExcept
    (Json.parse (← Lean.ofExcept view[0]!.getStr?))
  let exposures ← Lean.ofExcept view[1]!.getArr?
  let ownerPretty ← Lean.ofExcept view[2]!.getArr?
  let semanticPretty ← Lean.ofExcept view[3]!.getArr?
  let permittedData ← Lean.ofExcept (fromJson? view[4]! : Except String (Array String))
  let expectedAxioms ← Lean.ofExcept (fromJson? view[5]! : Except String (Array String))
  let publicNames ← Lean.ofExcept view[6]!.getArr?
  unless exposures.size == 18 && ownerPretty.size == 47 && semanticPretty.size == 111 &&
      publicNames.size == 47 do throwError "Construction view coverage changed"
  let env := (← getEnv).setExporting false
  let namespaceName ← getCurrNamespace
  let openDecls ← getOpenDecls
  let opens := openDecls.map fun entry => match entry with
    | .simple ns except => node "simple" [encodeName ns, toJson (except.map encodeName)]
    | .explicit id decl => node "explicit" [encodeName id, encodeName decl]
  let ambient ← getOptions
  let captureOptions := ambient.setBool `pp.fullNames true |>.setBool `pp.universes true
    |>.setBool `pp.explicit false |>.setBool `pp.proofs true
  let actualContext := Json.mkObj [("namespace", encodeName namespaceName),
    ("openDecls", toJson opens), ("imports", toJson env.header.imports),
    ("ambientOptions", toJson (toString ambient)),
    ("captureOptions", toJson (toString captureOptions)),
    ("mainModule", encodeName env.header.mainModule)]
  unless actualContext == expectedContext do
    throwError "Construction capture context changed: {actualContext}"
  let localNames := env.constants.map₂.foldl (init := #[]) fun names name _ => names.push name
  let helperScope := (``frozenConstruction).getPrefix
  unless isPrivateName ``frozenConstruction do throwError "Construction guard is not private"
  let helperSuffixes : Array String := #[
    "frozenView",
    "checkConstruction.match_1",
    "checkConstruction.match_13",
    "frozenConstruction",
    "checkConstruction.match_10",
    "checkConstruction.match_6",
    "checkConstruction",
    "checkConstruction._sparseCasesOn_10",
    "checkConstruction.match_15",
    "checkConstruction.match_8",
    "checkConstruction._sparseCasesOn_1",
    "checkConstruction.match_4",
  ]
  let helpers := helperSuffixes.map fun suffix => helperScope ++ suffix.toName
  let oldLocal := types.filterMap fun value => do
    let row ← value.getArr?.toOption
    let moduleName ← row[1]!.getStr?.toOption
    let name ← row[0]!.getStr?.toOption
    if moduleName == env.header.mainModule.toString then some name.toName else none
  unless oldLocal.size == 10 && localNames.qsort Name.lt ==
      (oldLocal ++ helpers).qsort Name.lt do
    throwError "Unexpected local construction guard declarations: {localNames}"
  let resolveOwner := fun name =>
    if let some imported := owner env name then some imported
    else if env.constants.map₂.contains name then some env.header.mainModule else none
  let values := fun (record : Json) (name : Name) =>
    (show CommandElabM (Array Json) from fields.mapM fun field =>
      if field == "module" then pure (toJson ((resolveOwner name).map Name.toString))
      else Lean.ofExcept (record.getObjVal? field))
  let digest := fun (v : Json) =>
    String.join ((VCVio.Algorithms.Sha2.sha256 v.compress.toUTF8).data.toList.map
      fun byte => String.ofList [Nat.digitChar (byte.toNat / 16), Nat.digitChar (byte.toNat % 16)])
  let newName := `SLHDSA.SHAKE128s.GraphFreshSampling.evaluate_eq_traversal
  let actualNew ← getConstInfo newName
  unless (← Lean.ofExcept (encodeExpr actualNew.type)) == parts[7]! do
    throwError "Frozen construction public header changed"
  let trustedExternalRoots : Array Name := #[`Init, `Cslib, `Mathlib]
  let trustedExternal := fun root => trustedExternalRoots.contains root
  unless !trustedExternal `HashSigTest && !trustedExternal `VCVioTest &&
      !trustedExternal `FutureUnlistedExecutable do
    throwError "Construction owner policy must reject unknown roots"
  let mut pending := #[newName]
  let mut seen : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | throwError "Missing construction proof dependency"
    let some moduleName := owner env name
      | throwError "Unowned construction proof dependency {name}"
    let root := moduleName.getRoot
    let recurse ← if root == `HashSig then do
      unless name == newName || permittedData.contains name.toString do
        throwError "Forbidden proof dependency outside frozen DATA closure {name}"
      pure true
    else if #[`VCVio, `ToMathlib].contains root then pure true
    else if trustedExternal root then pure false
    else
      throwError "Unapproved construction proof owner {moduleName} at {name}"
    if recurse then
      pending := pending ++ info.getUsedConstantsAsSet.toArray
  let axioms ← collectAxioms newName
  unless toJson (axioms.qsort Name.lt |>.map Name.toString) == toJson expectedAxioms do
    throwError "Construction proof axioms changed"
  let testName := `SLHDSA.SHAKE128s.GraphSamplerCompatibility.evaluate_eq_byteTraversal
  let .thmInfo testInfo ← getConstInfo testName | throwError "Construction witness is not a theorem"
  unless (← Lean.ofExcept (encodeExpr testInfo.value)) == parts[8]! do
    throwError "Construction witness must be exactly the public bridge symmetry; \
            actual dependencies: {testInfo.value.getUsedConstants.toList.map Name.toString}"
  let mut names : Array Name := #[]
  for row in types do
    let row ← Lean.ofExcept row.getArr?
    let name ← Lean.ofExcept row[0]!.getStr?
    names := names.push name.toName
    let expected ← Lean.ofExcept (decodeExpr row[5]!)
    let levels ← Lean.ofExcept ((← Lean.ofExcept row[3]!.getArr?).toList.mapM decodeName)
    if expected.hasLooseBVars || expected.hasFVar || expected.hasMVar || expected.hasLevelMVar then
      throwError "Open frozen construction type"
    let actual ← getConstInfo name.toName
    unless (← Lean.ofExcept (encodeExpr actual.type)) == row[5]! && actual.levelParams == levels do
      throwError "Frozen construction type changed at {name}"
    let kind ← Lean.ofExcept ((← Lean.ofExcept row[4]!.getArr?)[0]!.getStr?)
    let witness := Name.str ``frozenConstruction s!"witness{names.size}"
    let value := Expr.const name.toName (levels.map Level.param)
    let decl ← match kind with
      | "theorem" => pure (Declaration.thmDecl {
          name := witness, levelParams := levels, type := expected, value })
      | "definition" => pure (Declaration.defnDecl {
          name := witness, levelParams := levels, type := expected, value,
          hints := .opaque, safety := .safe })
      | _ => throwError "Unsupported frozen construction kind"
    if kind == "definition" then
      liftCoreM <| addDecl decl
      modifyEnv fun current => addNoncomputable current witness
    else liftCoreM <| addAndCompile decl
  let finalLocal := (← getEnv).constants.map₂.foldl (init := #[]) fun result name _ =>
    result.push name
  let witnessNames := (List.range 20).toArray.map fun index =>
    Name.str ``frozenConstruction s!"witness{index + 1}"
  unless finalLocal.qsort Name.lt == (oldLocal ++ helpers ++ witnessNames).qsort Name.lt do
    throwError "Unexpected local construction witness declarations: {finalLocal}"
  let semantic ← capture names #["VCVio", "ToMathlib", "HashSig", "HashSigTest", "VCVioCslib"]
  let actualRecords ← Lean.ofExcept (semantic.getObjValAs? (Array Json) "records")
  unless actualRecords.size == records.size do throwError "Construction closure size changed"
  for actual in actualRecords do
    let name ← Lean.ofExcept (actual.getObjValAs? String "name")
    let expected ← records.findM? fun (record : Json) => do
      let pair ← Lean.ofExcept record.getArr?
      pure ((← Lean.ofExcept pair[0]!.getStr?) == name)
    let some expected := expected | throwError "Unknown construction dependency {name}"
    let pair ← Lean.ofExcept expected.getArr?
    let expectedHash ← Lean.ofExcept pair[1]!.getStr?
    let actualValues ← values actual name.toName
    let prettyRow ← semanticPretty.findM? fun (row : Json) => do
      let pair ← Lean.ofExcept row.getArr?
      pure ((← Lean.ofExcept pair[0]!.getStr?) == name)
    let some prettyRow := prettyRow | throwError "Unknown semantic diagnostic name"
    let prettyParts ← Lean.ofExcept prettyRow.getArr?
    let pretty ← Lean.ofExcept (actual.getObjVal? "typePretty")
    unless digest pretty == (← Lean.ofExcept prettyParts[2]!.getStr?) do
      throwError "Construction semantic pretty view changed at {name}"
    unless digest (toJson actualValues) == expectedHash do
      throwError "Frozen construction semantic record changed at {name}: {Json.arr actualValues}"
  let actualBoundary ← Lean.ofExcept (semantic.getObjValAs? (Array Json) "externalBoundary")
  let actualBoundary ← actualBoundary.mapM fun (row : Json) => do
    pure (toJson #[← Lean.ofExcept (row.getObjVal? "name"),
      ← Lean.ofExcept (row.getObjVal? "module")])
  unless actualBoundary == boundary do throwError "Frozen construction boundary changed"
  let simp ← liftTermElabM getSimpTheorems
  for row in owners do
    let row ← Lean.ofExcept row.getArr?
    let text ← Lean.ofExcept row[0]!.getStr?
    let name := text.toName
    let expectedHash ← Lean.ofExcept row[1]!.getStr?
    let info ← getConstInfo name
    let record ← captureConstant env name
    let reduction ← liftTermElabM (getReducibilityStatus name)
    let attr := Json.mkObj [
      ("exposedBody", toJson (env.hasExposedBody name)),
      ("privateName", toJson (isPrivateName name)),
      ("protected", toJson (isProtected env name)), ("meta", toJson (isMarkedMeta env name)),
      ("noncomputable", toJson (isNoncomputable env name)),
      ("reducibility", toJson (reprStr reduction)),
      ("inline", toJson ((Lean.Compiler.getInlineAttribute? env name).map fun k =>
        match k with
        | .inline => "inline" | .noinline => "noinline" | .macroInline => "macro_inline"
        | .inlineIfReduce => "inline_if_reduce" | .alwaysInline => "always_inline")),
      ("defeq", toJson (defeqAttr.hasTag env name)),
      ("backwardDefeq", toJson (backwardDefeqAttr.hasTag env name)),
      ("simpLemma", toJson (simp.isLemma (.decl name))),
      ("simpUnfold", toJson (simp.isDeclToUnfold name)),
      ("matchPattern", toJson (hasMatchPatternAttribute env name)),
      ("csimp", toJson (Lean.Compiler.hasCSimpAttribute env name)),
      ("extern", toJson (isExtern env name))]
    let publicRow ← publicNames.findM? fun (row : Json) => do
      let pair ← Lean.ofExcept row.getArr?
      pure ((← Lean.ofExcept pair[0]!.getStr?) == text)
    let some publicRow := publicRow | throwError "Missing public-view name"
    let publicParts ← Lean.ofExcept publicRow.getArr?
    unless toJson ((env.setExporting true).find? name |>.isSome) == publicParts[1]! do
      throwError "Construction public name visibility changed at {name}"
    let prettyRow ← ownerPretty.findM? fun (row : Json) => do
      let pair ← Lean.ofExcept row.getArr?
      pure ((← Lean.ofExcept pair[0]!.getStr?) == text)
    let some prettyRow := prettyRow | throwError "Unknown owner diagnostic name"
    let prettyParts ← Lean.ofExcept prettyRow.getArr?
    unless digest (← Lean.ofExcept (record.getObjVal? "typePretty")) ==
        (← Lean.ofExcept prettyParts[2]!.getStr?) do
      throwError "Construction owner pretty view changed at {name}"
    let exposure ← exposures.findM? fun (row : Json) => do
      let pair ← Lean.ofExcept row.getArr?
      pure ((← Lean.ofExcept pair[0]!.getStr?) == text)
    let historicalAttr ← if let some exposure := exposure then do
      let pair ← Lean.ofExcept exposure.getArr?
      unless pair[1]! == toJson false && pair[2]! == toJson true &&
          (← Lean.ofExcept (attr.getObjVal? "exposedBody")) == pair[2]! do
        throwError "Named construction exposure view changed at {name}"
      pure (attr.setObjVal! "exposedBody" pair[1]!)
    else pure attr
    let actualAttrs ← attributes.mapM fun field =>
      Lean.ofExcept (historicalAttr.getObjVal? field)
    let mut actual := #[toJson (← values record name), toJson actualAttrs]
    if name != testName then
      let proof ← match info with
        | .thmInfo value => Lean.ofExcept (encodeExpr value.value)
        | _ => pure Json.null
      actual := actual ++ #[proof,
        toJson (info.getUsedConstantsAsSet.toArray.qsort Name.lt |>.map Name.toString)]
    unless digest (toJson actual) == expectedHash do
      throwError "Frozen construction owner record changed at {name}: {Json.arr actual}"
  let library := `HashSig.SLHDSA.SHAKE128s.Proof.GraphFreshSampling
  let mut actualExtras : Array Name := #[]
  let mut libraryNames : Array Name := #[]
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == library then
      actualExtras := actualExtras ++ env.header.moduleData[i]!.extraConstNames
      libraryNames := libraryNames ++ env.header.moduleData[i]!.constNames
  unless toJson (actualExtras.map Name.toString) == toJson extras do
    throwError "Frozen construction compiler extras changed"
  let oldLibrary := owners.filterMap fun row => do
    let fields ← row.getArr?.toOption
    let name ← (fields[0]!.getStr?).toOption
    if (resolveOwner name.toName) == some library then some name.toName else none
  unless libraryNames.size == oldLibrary.size + 1 &&
      libraryNames.all (fun name => oldLibrary.contains name || name == newName) do
    throwError "Unexpected byte-oracle library declaration"
  logInfo "C1E_FROZEN20_TYPES_47_OWNERS_111_DATA_157_BOUNDARY_30_EXTRAS_EXACT_SYMMETRY_PASS"

run_cmd checkConstruction

end SLHDSA.SHAKE128s.GraphSamplerCompatibility
