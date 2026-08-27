/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedRootedSourceOrders
import ErdosProblems.Erdos207.LocalizedPairSourceOrders
import ErdosProblems.Erdos207.LocalizedCommonSelectedTail
import ErdosProblems.Erdos207.LocalizedGainSourceOrders
import ErdosProblems.Erdos207.CrudeStatisticIndex
import ErdosProblems.Erdos207.LocalizedSourceOrderCover

/-! # Explicit source-family error expressions for the four exact crude statistics -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceMomentTailExpression (d s : ℕ) (A epsilon kappa countBound K : ℝ≥0) : ℝ≥0 :=
  A * (((boundedIntersectionMomentCoefficient d s : ℝ≥0) * kappa) / K) ^ s +
    epsilon * (countBound / K) ^ s

def sourceCrudeWitnessCount {I : Type*} [Fintype I] (order : I → ℕ) (N : ℕ) : ℝ≥0 :=
  ∑ i, (2 : ℝ≥0) ^ order i * (N + 1 : ℝ≥0) ^ (3 * order i)

def sourceCrudeRootCoefficient {I : Type*} [Fintype I]
    (order : I → ℕ) (z : I → ℝ≥0) (ell n j c : ℕ) (w : ℝ≥0) : ℝ≥0 :=
  ∑ i : {i : I // j ≤ order i},
    ((((order i.1 - j + c + 1) ^ ell : ℕ) : ℝ≥0) * ((2 : ℝ≥0) ^ (order i.1 - 2) * z i.1) *
      w ^ (order i.1 - j + c) * (n : ℝ≥0) ^ (j - c - 5))

def sourceCrudeTailBound
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] {ell q : ℕ}
    (W : Vortex V ell) (order : I → ℕ) (z : I → ℝ≥0) (s : ℕ)
    (w A epsilon : ℝ≥0) (K : CrudeThresholds) : CrudeStatisticIndex V q → ℝ≥0
  | .inl (i, _) => sourceMomentTailExpression (q - i.order + i.chosen) s A epsilon
      (sourceCrudeRootCoefficient order z ell W.terminalSize i.order i.chosen w)
      (sourceCrudeWitnessCount (fun u : {u : I // i.order ≤ order u} ↦ order u.1) (Fintype.card V))
      (K.rooted i.order i.chosen)
  | .inr (.inl _) => sourceMomentTailExpression (q - 4) s A epsilon
      (∑ i, sourceNibbleMomentCoefficient ell (order i) w * z i)
      (sourceCrudeWitnessCount order (Fintype.card V)) K.pair
  | .inr (.inr (.inl _)) => sourceMomentTailExpression (2 * q) s A epsilon
      (∑ i, ∑ i', sourceCommonMomentCoefficient ell q (order i) w (z i) (z i'))
      ((Fintype.card I : ℝ≥0) ^ 2 * (q + 1 : ℝ≥0) * (Fintype.card V + 1 : ℝ≥0) ^ (6 * q)) K.common
  | .inr (.inr (.inr (i, _))) => sourceMomentTailExpression (2 * q) s A epsilon
      (∑ j, ∑ j', sourceGainMomentCoefficient ell q (order j) w (z j) (z j') *
        (W.terminalSize : ℝ≥0) ^ (i.order - i.chosen - 4))
      ((Fintype.card I : ℝ≥0) ^ 2 * (2 : ℝ≥0) ^ q * (Fintype.card V + 1 : ℝ≥0) ^ (6 * q))
      (K.gain i.order i.chosen)

end

end Erdos207
