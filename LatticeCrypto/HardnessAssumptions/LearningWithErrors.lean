/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.NoisyLearning

/-!
# Learning With Errors

LWE-style experiments for the lattice schemes. The definitions live in
`VCVio.CryptoFoundations.HardnessAssumptions.NoisyLearning` as the generic
noisy-learning problem family (`NoisyLearning.Problem` covers LWE, module-LWE,
ring-LWE, and LPN); this module re-exports them under the historical
`LearningWithErrors` namespace used by the lattice schemes' security
statements.
-/

@[expose] public section

namespace LearningWithErrors

export NoisyLearning (Problem distr uniformDistr Adversary experiment advantage
  game0 game1 SearchAdversary searchExperiment searchAdvantage
  matrixProblem zmodMatrixProblem moduleMatrixProblem ringProblem lpnProblem)

end LearningWithErrors
