/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperAsymptoticAssembly
import ErdosProblems.Erdos446.UpperClusterMass

/-!
# Erdős Problem 446: exact interface between the two upper estimates

Ford's upper proof has two genuinely analytic inputs.  The upper-bound sieve
reduces the finite divisor count to the smooth squarefree cluster mass, and
the prime-block/order-statistics argument bounds that cluster mass by the
depth-indexed combinatorial model.  This file records those two inputs with
their exact normalizations and proves that their conjunction is precisely
enough to produce `DyadicPrefixUpperBound`.

No number-theoretic estimate is hidden in the bridge: the proof below is only
positivity, multiplication, division by `log(y)^2`, and the already proved
Theta comparison between `fordUpperDensityModel` and `growth446`.
-/

namespace Erdos446

open Filter Real Asymptotics
open scoped Topology

/-- Ford's dyadic upper-bound sieve reduction (equation (28) in the
mathematical writeup), with an explicit uniform constant. -/
def DyadicUpperSieveClusterReduction (A : ℝ) (Y : ℕ) : Prop :=
  ∀ y : ℕ, Y ≤ y → ∀ X : ℕ, y * y ≤ X →
    (divisorPrefixCount X y (2 * y) : ℝ) ≤
      A * (X : ℝ) * squarefreeClusterMass (2 * y) /
        Real.log (y : ℝ) ^ 2

/-- The output of the prime-block/order-statistics argument (equations
(30)--(34) in the writeup), before conversion of the selected depth to
logarithms. -/
def SmoothSquarefreeClusterModelUpper
    (M : ℕ) (D : ℝ) (Y : ℕ) : Prop :=
  ∀ y : ℕ, Y ≤ y →
    squarefreeClusterMass (2 * y) ≤
      D * fordCombinatorialWeight (fordScaleDepth M y)

/-- The sieve reduction and the sharp cluster-mass estimate assemble into
the exact finite-prefix upper bound required by the density theorem. -/
theorem exists_dyadicPrefixUpperBound_of_sieveCluster
    {M : ℕ} {A D : ℝ} {YSieve YCluster : ℕ}
    (hA : 0 < A) (hD : 0 < D)
    (hSieve : DyadicUpperSieveClusterReduction A YSieve)
    (hCluster : SmoothSquarefreeClusterModelUpper M D YCluster) :
    ∃ C : ℝ, ∃ Y : ℕ, 0 < C ∧ 1 ≤ Y ∧
      DyadicPrefixUpperBound C Y := by
  rcases (fordUpperDensityModel_isTheta_growth446 M).1.bound with
    ⟨c, hc⟩
  rw [eventually_atTop] at hc
  obtain ⟨YModel, hYModel⟩ := hc
  obtain ⟨YPositive, hYPositive⟩ :=
    (eventually_atTop.1 eventually_growthDenominator446_pos)
  let E : ℝ := |c| + 1
  let C : ℝ := A * D * E
  let Y : ℕ := max 2 (max YSieve (max YCluster (max YModel YPositive)))
  have hE : 0 < E := by
    dsimp [E]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, Y, hC, (by omega), ?_⟩
  intro y hy X hX
  have hySieve : YSieve ≤ y := by
    dsimp [Y] at hy
    omega
  have hyCluster : YCluster ≤ y := by
    dsimp [Y] at hy
    omega
  have hyModel : YModel ≤ y := by
    dsimp [Y] at hy
    omega
  have hyPositive : YPositive ≤ y := by
    dsimp [Y] at hy
    omega
  have hyTwo : 2 ≤ y := by
    dsimp [Y] at hy
    omega
  have hlog : 0 < Real.log (y : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hden : 0 < Real.log (y : ℝ) ^ 2 := sq_pos_of_pos hlog
  have hXR : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
  have hweight : 0 ≤ fordCombinatorialWeight (fordScaleDepth M y) := by
    dsimp [fordCombinatorialWeight]
    positivity
  have hmodelNorm := hYModel y hyModel
  have hmodel : fordUpperDensityModel M y ≤
      E * growth446 y := by
    have hgrowthPos : 0 < growth446 y := by
      exact inv_pos.mpr (hYPositive y hyPositive)
    have hcE : c ≤ E := by
      dsimp [E]
      linarith [le_abs_self c]
    have hraw : fordUpperDensityModel M y ≤ c * growth446 y := by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (fordUpperDensityModel_nonneg M y),
        abs_of_pos hgrowthPos] using hmodelNorm
    exact hraw.trans (mul_le_mul_of_nonneg_right hcE hgrowthPos.le)
  calc
    (divisorPrefixCount X y (2 * y) : ℝ) ≤
        A * (X : ℝ) * squarefreeClusterMass (2 * y) /
          Real.log (y : ℝ) ^ 2 := hSieve y hySieve X hX
    _ ≤ A * (X : ℝ) *
          (D * fordCombinatorialWeight (fordScaleDepth M y)) /
            Real.log (y : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hCluster y hyCluster)
          (mul_nonneg hA.le hXR)) hden.le
    _ = A * D * (X : ℝ) * fordUpperDensityModel M y := by
      dsimp [fordUpperDensityModel]
      ring
    _ ≤ A * D * (X : ℝ) * (E * growth446 y) := by
      exact mul_le_mul_of_nonneg_left hmodel
        (mul_nonneg (mul_nonneg hA.le hD.le) hXR)
    _ = C * (X : ℝ) * growth446 y := by
      dsimp [C]
      ring

/-- End-to-end upper assembly: once Ford's two analytic estimates are
available in the normalizations above, the already proved lower bound gives
the sharp growth theorem for the literal open interval. -/
theorem delta_isTheta_growth446_of_sieveCluster
    {M : ℕ} {A D : ℝ} {YSieve YCluster : ℕ}
    (hA : 0 < A) (hD : 0 < D)
    (hSieve : DyadicUpperSieveClusterReduction A YSieve)
    (hCluster : SmoothSquarefreeClusterModelUpper M D YCluster) :
    delta =Θ[atTop] growth446 := by
  obtain ⟨C, Y, hC, hY, hPrefix⟩ :=
    exists_dyadicPrefixUpperBound_of_sieveCluster
      hA hD hSieve hCluster
  exact delta_isTheta_growth446_of_dyadicPrefixUpperBound hY hPrefix

end Erdos446
