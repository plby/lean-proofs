/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos721.ImprovedParameters
import ErdosProblems.Erdos721.RelativeAlmostPeriodicity
import ErdosProblems.Erdos721.ContainedAlmostPeriodicity
import ErdosProblems.Erdos721.SharpLocalChangSanders

/-!
# The improved local density increment

This file connects the improved Bloom--Sisask test function to the localized
Croot--Sisask theorem and the regularized density-increment tail.  Negated
finite sets are kept behind a small named predicate; this also records
explicitly the coercion from a negated finset to a negated set.
-/

namespace Erdos721

open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ENNReal Indicator mu NNReal Pointwise

namespace CyclicImprovedLocalDensityIteration

variable {N : ℕ} [NeZero N]

/-- The exact cardinality lower bound for the improved Croot--Sisask shift
set in a local Bohr carrier. -/
noncomputable def improvedCrootLowerBound
    (H : CyclicBohr.Set N) (A₂ U : Finset (ZMod N))
    (zeta alpha epsilon beta : ℝ) : ℝ :=
  (11 / (10 * alpha)) ^ (-4096 *
      ((⌈1 + Real.log
        (min 1 ((A₂.card : ℝ) / (U.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
      (CyclicImprovedParameters.improvedExponent epsilon beta : ℝ) ^ 2 /
        (epsilon / 32) ^ 2) *
      ((H.dilate zeta).carrier.card : ℝ)

/-- Canonical integer cutoff for the rank-free local Chang--Sanders entropy.
It is defined directly from the exact Croot--Sisask cardinality lower bound;
later quantitative bookkeeping bounds this ceiling by a polynomial in the
current logarithmic density and rank. -/
noncomputable def rankFreeEntropy
    (H : CyclicBohr.Set N) (A₂ U : Finset (ZMod N))
    (zeta alpha epsilon beta : ℝ) : ℕ :=
  ⌈max 0 (2 * (Real.log
      (((H.dilate (2 * zeta)).carrier.card : ℝ) /
        improvedCrootLowerBound H A₂ U zeta alpha epsilon beta) +
      Real.log 4) / (1 / 2 : ℝ) ^ 2)⌉₊ + 1

lemma rankFreeEntropy_pos
    (H : CyclicBohr.Set N) (A₂ U : Finset (ZMod N))
    (zeta alpha epsilon beta : ℝ) :
    0 < rankFreeEntropy H A₂ U zeta alpha epsilon beta := by
  unfold rankFreeEntropy
  omega

/-- The exact cardinality bound implies the strict entropy cutoff required by
the local Chang--Sanders generator. -/
lemma rankFreeEntropy_cutoff_of_lowerBound
    (H : CyclicBohr.Set N) (A₂ U T : Finset (ZMod N))
    {zeta alpha epsilon beta : ℝ}
    (halpha : 0 < alpha)
    (hbound : improvedCrootLowerBound H A₂ U zeta alpha epsilon beta ≤ T.card)
    (hT : T.Nonempty) :
    2 * (Real.log
        (((H.dilate (2 * zeta)).carrier.card : ℝ) / T.card) +
      Real.log 4) / (1 / 2 : ℝ) ^ 2 <
      rankFreeEntropy H A₂ U zeta alpha epsilon beta := by
  let L := improvedCrootLowerBound H A₂ U zeta alpha epsilon beta
  let E : ℝ := 2 * (Real.log
      (((H.dilate (2 * zeta)).carrier.card : ℝ) / L) +
      Real.log 4) / (1 / 2 : ℝ) ^ 2
  have hL : 0 < L := by
    dsimp only [L, improvedCrootLowerBound]
    have hK : 0 < 11 / (10 * alpha) := by positivity
    have hcard : (0 : ℝ) < (H.dilate zeta).carrier.card := by
      exact_mod_cast (H.dilate zeta).carrier_nonempty.card_pos
    exact mul_pos (Real.rpow_pos_of_pos hK _) hcard
  have hTcard : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hOuter : (0 : ℝ) < (H.dilate (2 * zeta)).carrier.card := by
    exact_mod_cast (H.dilate (2 * zeta)).carrier_nonempty.card_pos
  have hratio :
      ((H.dilate (2 * zeta)).carrier.card : ℝ) / T.card ≤
        ((H.dilate (2 * zeta)).carrier.card : ℝ) / L := by
    exact div_le_div_of_nonneg_left hOuter.le hL hbound
  have hlog :
      Real.log (((H.dilate (2 * zeta)).carrier.card : ℝ) / T.card) ≤
        Real.log (((H.dilate (2 * zeta)).carrier.card : ℝ) / L) :=
    Real.log_le_log (div_pos hOuter hTcard) hratio
  have hEbound :
      2 * (Real.log
          (((H.dilate (2 * zeta)).carrier.card : ℝ) / T.card) +
        Real.log 4) / (1 / 2 : ℝ) ^ 2 ≤ E := by
    dsimp only [E]
    gcongr
  calc
    2 * (Real.log
        (((H.dilate (2 * zeta)).carrier.card : ℝ) / T.card) +
      Real.log 4) / (1 / 2 : ℝ) ^ 2 ≤ E := hEbound
    _ ≤ max 0 E := le_max_right _ _
    _ ≤ (⌈max 0 E⌉₊ : ℝ) := Nat.le_ceil _
    _ < (⌈max 0 E⌉₊ + 1 : ℕ) := by
      exact_mod_cast Nat.lt_succ_self ⌈max 0 E⌉₊
    _ = rankFreeEntropy H A₂ U zeta alpha epsilon beta := by
      rfl

/-- Accuracy parameter for the auxiliary narrow spectrum. -/
noncomputable def rankFreeAuxiliaryAccuracy (epsilon beta : ℝ) : ℕ :=
  512 * (⌈(epsilon * beta)⁻¹⌉₊ + 1)

lemma rankFreeAuxiliaryAccuracy_pos (epsilon beta : ℝ) :
    0 < rankFreeAuxiliaryAccuracy epsilon beta := by
  unfold rankFreeAuxiliaryAccuracy
  positivity

lemma rankFreeAuxiliary_error_le
    {epsilon beta : ℝ} (hepsilon : 0 < epsilon) (hbeta : 0 < beta) :
    3 / (5 * rankFreeAuxiliaryAccuracy epsilon beta) ≤
      epsilon * beta / 512 := by
  let q : ℕ := ⌈(epsilon * beta)⁻¹⌉₊ + 1
  have heb : 0 < epsilon * beta := mul_pos hepsilon hbeta
  have hq : 0 < q := by dsimp only [q]; omega
  have hqLower : (epsilon * beta)⁻¹ ≤ (q : ℝ) := by
    dsimp only [q]
    calc
      (epsilon * beta)⁻¹ ≤ (⌈(epsilon * beta)⁻¹⌉₊ : ℝ) :=
        Nat.le_ceil _
      _ ≤ (⌈(epsilon * beta)⁻¹⌉₊ + 1 : ℕ) := by
        exact_mod_cast Nat.le_succ _
  have hqInv : (q : ℝ)⁻¹ ≤ epsilon * beta := by
    calc
      (q : ℝ)⁻¹ ≤ ((epsilon * beta)⁻¹)⁻¹ :=
        inv_anti₀ (inv_pos.mpr heb) hqLower
      _ = epsilon * beta := inv_inv _
  have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  calc
    3 / (5 * rankFreeAuxiliaryAccuracy epsilon beta) =
        (3 / 2560 : ℝ) * (q : ℝ)⁻¹ := by
      dsimp only [rankFreeAuxiliaryAccuracy, q]
      push_cast
      field_simp
      ring
    _ ≤ (3 / 2560 : ℝ) * (epsilon * beta) := by gcongr
    _ ≤ epsilon * beta / 512 := by
      nlinarith [heb]

/-- Radius assigned to each extracted local Chang frequency. -/
noncomputable def rankFreeExtractedRadius
    (epsilon beta : ℝ) (entropy : ℕ) : ℝ :=
  epsilon * beta / (512 * entropy)

lemma rankFreeExtractedRadius_pos
    {epsilon beta : ℝ} {entropy : ℕ}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta) (hentropy : 0 < entropy) :
    0 < rankFreeExtractedRadius epsilon beta entropy := by
  unfold rankFreeExtractedRadius
  positivity

/-- The canonical local-controller parameters fit the complete boosted
smoothing error budget. -/
lemma explicit_rankFree_smoothing_error_bound
    {epsilon beta : ℝ} (A : Finset (ZMod N)) (scale entropy : ℕ)
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta)
    (hentropy : 0 < entropy) (hA : A.Nonempty)
    (hdensity : beta * scale = A.card) :
    scale *
        ((((entropy : ℝ) *
            rankFreeExtractedRadius epsilon beta entropy +
          3 / (5 * rankFreeAuxiliaryAccuracy epsilon beta)) +
          2 * (1 / 2 : ℝ) ^
            CyclicImprovedParameters.improvedExponent epsilon beta) *
          (A.card : ℝ)⁻¹) ≤ epsilon / 64 := by
  have hentropyReal : (entropy : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hentropy
  have hsigma :
      (entropy : ℝ) * rankFreeExtractedRadius epsilon beta entropy =
        epsilon * beta / 512 := by
    unfold rankFreeExtractedRadius
    field_simp
  have haux := rankFreeAuxiliary_error_le hepsilon hbeta
  have htail :=
    CyclicImprovedParameters.improvedExponent_tail hepsilon hbeta
  have htwotail :
      2 * (1 / 2 : ℝ) ^
          CyclicImprovedParameters.improvedExponent epsilon beta ≤
        epsilon * beta / 256 := by
    linarith
  have herr :
      ((entropy : ℝ) * rankFreeExtractedRadius epsilon beta entropy +
          3 / (5 * rankFreeAuxiliaryAccuracy epsilon beta)) +
        2 * (1 / 2 : ℝ) ^
          CyclicImprovedParameters.improvedExponent epsilon beta ≤
        epsilon * beta / 128 := by
    rw [hsigma]
    linarith
  have hcard : 0 < (A.card : ℝ) := by
    exact_mod_cast card_pos.mpr hA
  have hratio : (scale : ℝ) * (A.card : ℝ)⁻¹ = beta⁻¹ := by
    field_simp [hbeta.ne', hcard.ne']
    nlinarith [hdensity]
  calc
    (scale : ℝ) *
        (((((entropy : ℝ) * rankFreeExtractedRadius epsilon beta entropy +
            3 / (5 * rankFreeAuxiliaryAccuracy epsilon beta)) +
          2 * (1 / 2 : ℝ) ^
            CyclicImprovedParameters.improvedExponent epsilon beta) *
          (A.card : ℝ)⁻¹)) =
        (((entropy : ℝ) * rankFreeExtractedRadius epsilon beta entropy +
            3 / (5 * rankFreeAuxiliaryAccuracy epsilon beta)) +
          2 * (1 / 2 : ℝ) ^
            CyclicImprovedParameters.improvedExponent epsilon beta) *
          beta⁻¹ := by
      rw [← hratio]
      ring
    _ ≤ (epsilon * beta / 128) * beta⁻¹ := by
      exact mul_le_mul_of_nonneg_right herr (inv_nonneg.mpr hbeta.le)
    _ = epsilon / 128 := by field_simp
    _ ≤ epsilon / 64 := by linarith

private noncomputable def rawImprovedCrootLowerBound
    (S A₂ U : Finset (ZMod N)) (alpha epsilon beta : ℝ) : ℝ :=
  (11 / (10 * alpha)) ^ (-4096 *
      ((⌈1 + Real.log
        (min 1 (((-A₂).card : ℝ) / ((-U).card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
      (CyclicImprovedParameters.improvedExponent epsilon beta : ℝ) ^ 2 /
        (epsilon / 32) ^ 2) * (S.card : ℝ)

/-- The Croot--Sisask lower bound in the reflected orientation used by the
local Chang--Sanders argument.  The small-doubling set is `-A₂`; consequently
the shift set lies in `A₂ - A₂`, while the Hölder logarithm involves the
ratio `|A₁| / |U|`. -/
noncomputable def reflectedImprovedCrootLowerBound
    (S A₁ U : Finset (ZMod N)) (K epsilon beta : ℝ) : ℝ :=
  K ^ (-4096 *
      ((⌈1 + Real.log
        (min 1 ((A₁.card : ℝ) / (U.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
      (CyclicImprovedParameters.improvedExponent epsilon beta : ℝ) ^ 2 /
      (epsilon / 32) ^ 2) * (S.card : ℝ)

/-- The exact exponent in the reflected Croot--Sisask cardinality bound.
It depends only on the two relative densities and the approximation
parameters, not on the ambient Bohr rank. -/
noncomputable def reflectedCrootCost
    (A₁ U : Finset (ZMod N)) (epsilon beta : ℝ) : ℝ :=
  4096 *
      ((⌈1 + Real.log
        (min 1 ((A₁.card : ℝ) / (U.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
      (CyclicImprovedParameters.improvedExponent epsilon beta : ℝ) ^ 2 /
        (epsilon / 32) ^ 2

lemma reflectedImprovedCrootLowerBound_eq_rpow
    (S A₁ U : Finset (ZMod N)) (K epsilon beta : ℝ) :
    reflectedImprovedCrootLowerBound S A₁ U K epsilon beta =
      K ^ (-reflectedCrootCost A₁ U epsilon beta) * (S.card : ℝ) := by
  unfold reflectedImprovedCrootLowerBound reflectedCrootCost
  congr 2
  ring

/-- Rank-independent entropy cutoff used once a stable carrier has already
been selected.  The cancellation of `|S|` between Croot--Sisask's lower
bound and the local Chang density is built into this definition. -/
noncomputable def reflectedStableEntropy
    (A₁ U : Finset (ZMod N)) (alpha epsilon beta : ℝ) : ℕ :=
  ⌈max 0 (2 *
      (reflectedCrootCost A₁ U epsilon beta *
          Real.log (11 / (10 * alpha)) + Real.log 4) /
        (1 / 2 : ℝ) ^ 2)⌉₊ + 1

lemma reflectedStableEntropy_pos
    (A₁ U : Finset (ZMod N)) (alpha epsilon beta : ℝ) :
    0 < reflectedStableEntropy A₁ U alpha epsilon beta := by
  unfold reflectedStableEntropy
  omega

/-- The reflected Croot--Sisask cardinality lower bound implies the strict
relative entropy cutoff against the same stable carrier. -/
lemma reflectedStableEntropy_cutoff_of_lowerBound
    (S A₁ U T : Finset (ZMod N)) {alpha epsilon beta : ℝ}
    (halpha : 0 < alpha) (hS : S.Nonempty) (hT : T.Nonempty)
    (hbound : reflectedImprovedCrootLowerBound S A₁ U
      (11 / (10 * alpha)) epsilon beta ≤ T.card) :
    2 * (Real.log ((S.card : ℝ) / T.card) + Real.log 4) /
        (1 / 2 : ℝ) ^ 2 <
      reflectedStableEntropy A₁ U alpha epsilon beta := by
  let K : ℝ := 11 / (10 * alpha)
  let cost : ℝ := reflectedCrootCost A₁ U epsilon beta
  let E : ℝ := 2 * (cost * Real.log K + Real.log 4) /
    (1 / 2 : ℝ) ^ 2
  have hK : 0 < K := by dsimp only [K]; positivity
  have hScard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hTcard : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hpow : 0 < K ^ (-cost) := Real.rpow_pos_of_pos hK _
  have hlower : 0 < K ^ (-cost) * (S.card : ℝ) :=
    mul_pos hpow hScard
  have hbound' : K ^ (-cost) * (S.card : ℝ) ≤ T.card := by
    simpa only [K, cost, reflectedImprovedCrootLowerBound_eq_rpow] using hbound
  have hlog := Real.log_le_log hlower hbound'
  rw [Real.log_mul hpow.ne' hScard.ne', Real.log_rpow hK] at hlog
  have hquotient :
      Real.log ((S.card : ℝ) / T.card) ≤ cost * Real.log K := by
    rw [Real.log_div hScard.ne' hTcard.ne']
    linarith
  have hleft :
      2 * (Real.log ((S.card : ℝ) / T.card) + Real.log 4) /
          (1 / 2 : ℝ) ^ 2 ≤ E := by
    dsimp only [E]
    gcongr
  calc
    2 * (Real.log ((S.card : ℝ) / T.card) + Real.log 4) /
        (1 / 2 : ℝ) ^ 2 ≤ E := hleft
    _ ≤ max 0 E := le_max_right _ _
    _ ≤ (⌈max 0 E⌉₊ : ℝ) := Nat.le_ceil _
    _ < (⌈max 0 E⌉₊ + 1 : ℕ) := by
      exact_mod_cast Nat.lt_succ_self ⌈max 0 E⌉₊
    _ = reflectedStableEntropy A₁ U alpha epsilon beta := by
      rfl

/-- Exact reflected Croot--Sisask lower bound at the small regular Bohr
scale.  Both logarithmic factors now come from the two sifted relative
densities, as in Bloom--Sisask Lemma 8. -/
noncomputable def reflectedLocalCrootLowerBound
    (R : CyclicBohr.Set N) (A₁ U : Finset (ZMod N))
    (eta alpha epsilon beta : ℝ) : ℝ :=
  reflectedImprovedCrootLowerBound (R.dilate eta).carrier A₁ U
    (11 / (10 * alpha)) epsilon beta

/-- Canonical local Chang--Sanders entropy for the reflected orientation. -/
noncomputable def reflectedRankFreeEntropy
    (R : CyclicBohr.Set N) (A₁ U : Finset (ZMod N))
    (eta alpha epsilon beta : ℝ) : ℕ :=
  ⌈max 0 (2 * (Real.log
      (((R.dilate (2 * eta)).carrier.card : ℝ) /
        reflectedLocalCrootLowerBound R A₁ U eta alpha epsilon beta) +
      Real.log 4) / (1 / 2 : ℝ) ^ 2)⌉₊ + 1

lemma reflectedRankFreeEntropy_pos
    (R : CyclicBohr.Set N) (A₁ U : Finset (ZMod N))
    (eta alpha epsilon beta : ℝ) :
    0 < reflectedRankFreeEntropy R A₁ U eta alpha epsilon beta := by
  unfold reflectedRankFreeEntropy
  omega

lemma reflectedRankFreeEntropy_cutoff_of_lowerBound
    (R : CyclicBohr.Set N) (A₁ U T : Finset (ZMod N))
    {eta alpha epsilon beta : ℝ}
    (halpha : 0 < alpha)
    (hbound : reflectedLocalCrootLowerBound
      R A₁ U eta alpha epsilon beta ≤ T.card)
    (hT : T.Nonempty) :
    2 * (Real.log
        (((R.dilate (2 * eta)).carrier.card : ℝ) / T.card) +
      Real.log 4) / (1 / 2 : ℝ) ^ 2 <
      reflectedRankFreeEntropy R A₁ U eta alpha epsilon beta := by
  let L := reflectedLocalCrootLowerBound R A₁ U eta alpha epsilon beta
  let E : ℝ := 2 * (Real.log
      (((R.dilate (2 * eta)).carrier.card : ℝ) / L) +
      Real.log 4) / (1 / 2 : ℝ) ^ 2
  have hL : 0 < L := by
    dsimp only [L, reflectedLocalCrootLowerBound,
      reflectedImprovedCrootLowerBound]
    have hK : 0 < 11 / (10 * alpha) := by positivity
    have hcard : (0 : ℝ) < (R.dilate eta).carrier.card := by
      exact_mod_cast (R.dilate eta).carrier_nonempty.card_pos
    exact mul_pos (Real.rpow_pos_of_pos hK _) hcard
  have hTcard : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hOuter : (0 : ℝ) < (R.dilate (2 * eta)).carrier.card := by
    exact_mod_cast (R.dilate (2 * eta)).carrier_nonempty.card_pos
  have hratio :
      ((R.dilate (2 * eta)).carrier.card : ℝ) / T.card ≤
        ((R.dilate (2 * eta)).carrier.card : ℝ) / L :=
    div_le_div_of_nonneg_left hOuter.le hL hbound
  have hlog := Real.log_le_log (div_pos hOuter hTcard) hratio
  have hEbound :
      2 * (Real.log
          (((R.dilate (2 * eta)).carrier.card : ℝ) / T.card) +
        Real.log 4) / (1 / 2 : ℝ) ^ 2 ≤ E := by
    dsimp only [E]
    gcongr
  calc
    2 * (Real.log
        (((R.dilate (2 * eta)).carrier.card : ℝ) / T.card) +
      Real.log 4) / (1 / 2 : ℝ) ^ 2 ≤ E := hEbound
    _ ≤ max 0 E := le_max_right _ _
    _ ≤ (⌈max 0 E⌉₊ : ℝ) := Nat.le_ceil _
    _ < (⌈max 0 E⌉₊ + 1 : ℕ) := by
      exact_mod_cast Nat.lt_succ_self ⌈max 0 E⌉₊
    _ = reflectedRankFreeEntropy R A₁ U eta alpha epsilon beta := rfl

private lemma rawImprovedCrootLowerBound_eq
    (H : CyclicBohr.Set N) (A₂ U : Finset (ZMod N))
    (zeta alpha epsilon beta : ℝ) :
    rawImprovedCrootLowerBound (H.dilate zeta).carrier A₂ U alpha epsilon beta =
      improvedCrootLowerBound H A₂ U zeta alpha epsilon beta := by
  simp only [rawImprovedCrootLowerBound, improvedCrootLowerBound,
    Finset.card_neg]

/-- The precise complex-valued approximation returned by Croot--Sisask in
the sign convention used by the tested-correlation identity. -/
def IsBoostedApproximation
    (X A₁ A₂ U : Finset (ZMod N)) (k : ℕ) (error : ℝ) : Prop :=
  ‖(μ_[ℂ] X ∗ᵈ^ k ∗ᵈ
      (μ_[ℂ] A₁ ∗ᵈ 𝟭_[(↑(-U) : Set (ZMod N)), ℂ] ∗ᵈ μ_[ℂ] (-A₂))) -
    (μ_[ℂ] A₁ ∗ᵈ 𝟭_[(↑(-U) : Set (ZMod N)), ℂ] ∗ᵈ μ_[ℂ] (-A₂))‖_[∞] ≤ error

/-- Croot--Sisask in the orientation needed for rank-free local spectral
control.  The kernel is unchanged by commutativity, but the sampled set is
`-A₂`; hence the returned shifts lie in `A₂ - A₂`. -/
theorem exists_reflected_specialized_boosted_approximation
    (A₁ A₂ S U : Finset (ZMod N)) {K epsilon beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hK2 : 2 ≤ K)
    (hK : (((-A₂).addConst S : ℝ)) ≤ K)
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (hS : S.Nonempty) (hU : U.Nonempty) :
    ∃ X : Finset (ZMod N),
      reflectedImprovedCrootLowerBound S A₁ U K epsilon beta ≤ X.card ∧
      X ⊆ A₂ - A₂ ∧
      X.Nonempty ∧
      IsBoostedApproximation X A₁ A₂ U
        (CyclicImprovedParameters.improvedExponent epsilon beta)
        (epsilon / 32) := by
  obtain ⟨X, hXcard, hXsub, hXapprox⟩ :=
    AlmostPeriodicity.linfty_almost_periodicity_boosted_contained
      (A := -A₂) (S := S) (K := K)
      (epsilon / 32) (by positivity) (by linarith)
      (CyclicImprovedParameters.improvedExponent epsilon beta)
      (CyclicImprovedParameters.improvedExponent_ne_zero
        hepsilon0 hepsilon1 hbeta0 hbeta1)
      hK2 hK hA₂.neg hS (-U) A₁ hU.neg hA₁
  have hX : X.Nonempty := by
    have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK2
    have hScard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    have hXcardpos : (0 : ℝ) < X.card :=
      (mul_pos (Real.rpow_pos_of_pos hKpos _) hScard).trans_le hXcard
    rw [← Finset.card_pos]
    exact_mod_cast hXcardpos
  refine ⟨X, ?_, ?_, hX, ?_⟩
  · simpa only [reflectedImprovedCrootLowerBound, Finset.card_neg] using hXcard
  · intro x hx
    have hx' := hXsub hx
    rw [Finset.mem_sub] at hx' ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_neg.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_neg.mp hb
    refine ⟨b₀, hb₀, a₀, ha₀, ?_⟩
    abel
  · simpa only [IsBoostedApproximation, ddconv_assoc, ddconv_comm,
      ddconv_left_comm] using hXapprox

/-- Base-contained reflected orientation of Croot--Sisask.  This is the
orientation used in Bloom--Sisask Lemma 8: the sampled set is `-A₂`, so the
Hölder logarithm is `log(|U|/|A₁|)`, while the untranslated dense base
remains inside the prescribed small regular Bohr carrier. -/
theorem exists_reflected_specialized_boosted_approximation_with_base
    (A₁ A₂ S U : Finset (ZMod N)) {K epsilon beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hK2 : 2 ≤ K)
    (hK : (((-A₂).addConst S : ℝ)) ≤ K)
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (hS : S.Nonempty) (hU : U.Nonempty) :
    ∃ (T : Finset (ZMod N)) (z : ZMod N) (X : Finset (ZMod N)),
      reflectedImprovedCrootLowerBound S A₁ U K epsilon beta ≤ T.card ∧
      T ⊆ S ∧ z ∈ T ∧ X = (-z) +ᵥ T ∧ X.Nonempty ∧
      IsBoostedApproximation X A₁ A₂ U
        (CyclicImprovedParameters.improvedExponent epsilon beta)
        (epsilon / 32) := by
  obtain ⟨T, z, X, hTcard, hTsub, hz, hXeq, hXapprox⟩ :=
    AlmostPeriodicity.linfty_almost_periodicity_boosted_base_contained
      (A := -A₂) (S := S) (K := K)
      (epsilon / 32) (by positivity) (by linarith)
      (CyclicImprovedParameters.improvedExponent epsilon beta)
      (CyclicImprovedParameters.improvedExponent_ne_zero
        hepsilon0 hepsilon1 hbeta0 hbeta1)
      hK2 hK hA₂.neg hS (-U) A₁ hU.neg hA₁
  have hX : X.Nonempty := by
    rw [hXeq]
    refine ⟨(-z) +ᵥ z, ?_⟩
    exact Finset.vadd_mem_vadd_finset hz
  refine ⟨T, z, X, ?_, hTsub, hz, hXeq, hX, ?_⟩
  · simpa only [reflectedImprovedCrootLowerBound,
      Finset.card_neg] using hTcard
  · simpa only [IsBoostedApproximation, ddconv_assoc, ddconv_comm,
      ddconv_left_comm] using hXapprox

/-- The published base-set form of the specialized Croot--Sisask theorem.
The dense set `T` remains inside the perturbation carrier; the convolution
set is its translate `X = -z + T`. -/
theorem exists_specialized_boosted_approximation_with_base
    (A₁ S A₂ U : Finset (ZMod N)) {alpha epsilon beta : ℝ}
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hK : (A₁.addConst S : ℝ) ≤ 11 / (10 * alpha))
    (hA₁ : A₁.Nonempty) (hS : S.Nonempty)
    (hU : U.Nonempty) (hA₂ : A₂.Nonempty) :
    ∃ (T : Finset (ZMod N)) (z : ZMod N) (X : Finset (ZMod N)),
      rawImprovedCrootLowerBound S A₂ U alpha epsilon beta ≤ T.card ∧
      T ⊆ S ∧ z ∈ T ∧ X = (-z) +ᵥ T ∧ X.Nonempty ∧
      IsBoostedApproximation X A₁ A₂ U
        (CyclicImprovedParameters.improvedExponent epsilon beta)
        (epsilon / 32) := by
  have hK2 : 2 ≤ 11 / (10 * alpha) := by
    have hden : 0 < 10 * alpha := mul_pos (by norm_num) halpha0
    rw [le_div_iff₀ hden]
    nlinarith
  obtain ⟨T, z, X, hTcard, hTsub, hz, hXeq, hXapprox⟩ :=
    AlmostPeriodicity.linfty_almost_periodicity_boosted_base_contained
      (A := A₁) (S := S) (K := 11 / (10 * alpha))
      (epsilon / 32) (by positivity) (by linarith)
      (CyclicImprovedParameters.improvedExponent epsilon beta)
      (CyclicImprovedParameters.improvedExponent_ne_zero
        hepsilon0 hepsilon1 hbeta0 hbeta1)
      hK2 hK hA₁ hS (-U) (-A₂) hU.neg hA₂.neg
  have hX : X.Nonempty := by
    rw [hXeq]
    refine ⟨(-z) +ᵥ z, ?_⟩
    exact Finset.vadd_mem_vadd_finset hz
  refine ⟨T, z, X, ?_, hTsub, hz, hXeq, hX, ?_⟩
  · simpa only [rawImprovedCrootLowerBound, Finset.card_neg] using hTcard
  · simpa only [IsBoostedApproximation, ddconv_assoc] using hXapprox

private theorem exists_specialized_boosted_approximation
    (A₁ S A₂ U : Finset (ZMod N)) {alpha epsilon beta : ℝ}
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hK : (A₁.addConst S : ℝ) ≤ 11 / (10 * alpha))
    (hS : S.Nonempty) (hU : U.Nonempty) (hA₂ : A₂.Nonempty) :
    ∃ X : Finset (ZMod N),
      rawImprovedCrootLowerBound S A₂ U alpha epsilon beta ≤ X.card ∧
      X.Nonempty ∧
      IsBoostedApproximation X A₁ A₂ U
        (CyclicImprovedParameters.improvedExponent epsilon beta) (epsilon / 32) := by
  have hK2 : 2 ≤ 11 / (10 * alpha) := by
    have hden : 0 < 10 * alpha := mul_pos (by norm_num) halpha0
    rw [le_div_iff₀ hden]
    nlinarith
  obtain ⟨X, hXcard, hX, happrox⟩ :=
    CyclicImprovedDensityIncrement.exists_large_nonempty_boosted_approximation
      A₁ S (-U) (-A₂)
      (K := 11 / (10 * alpha)) (epsilon := epsilon / 32)
      (CyclicImprovedParameters.improvedExponent epsilon beta)
      (by positivity) (by linarith)
      (CyclicImprovedParameters.improvedExponent_ne_zero
        hepsilon0 hepsilon1 hbeta0 hbeta1)
      hK2 hK hS hU.neg hA₂.neg
  exact ⟨X, hXcard, hX, happrox⟩

/-- Total tested mass of the improved, boosted self-correlation. -/
noncomputable def boostedMass
    (X A₁ A₂ U : Finset (ZMod N)) (epsilon beta : ℝ) : ℝ :=
  ∑ x ∈ U,
    (iterConv (μ_[ℝ] X)
        (CyclicImprovedParameters.improvedExponent epsilon beta) ∗ᵈ
      (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂)) x

lemma boostedMass_error
    (X A₁ A₂ U : Finset (ZMod N)) {epsilon beta error : ℝ}
    (happrox : IsBoostedApproximation X A₁ A₂ U
      (CyclicImprovedParameters.improvedExponent epsilon beta) error) :
    |boostedMass X A₁ A₂ U epsilon beta -
      ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x| ≤ error := by
  have happrox' :
      ‖(μ_[ℂ] X ∗ᵈ^ CyclicImprovedParameters.improvedExponent epsilon beta ∗ᵈ
          (μ_[ℂ] A₁ ∗ᵈ 𝟭_[-U] ∗ᵈ μ_[ℂ] (-A₂))) -
        (μ_[ℂ] A₁ ∗ᵈ 𝟭_[-U] ∗ᵈ μ_[ℂ] (-A₂))‖_[∞] ≤ error := by
    simpa only [IsBoostedApproximation, ← Finset.coe_neg] using happrox
  simpa only [boostedMass, ddconv_dddconv_assoc] using
    (CyclicImprovedDensityIncrement.boosted_tested_correlation_error_of_dLinfty
      X (CyclicImprovedParameters.improvedExponent epsilon beta) A₁ A₂ U happrox')

/-- Croot--Sisask transfers the large unboosted mass supplied by sifting to
the improved boosted self-correlation. -/
theorem exists_large_boosted_mass
    (H : CyclicBohr.Set N) (A₁ A₂ U : Finset (ZMod N))
    {u zeta alpha epsilon beta : ℝ}
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hzeta : 0 ≤ zeta) (hzetau : zeta ≤ u)
    (hA₁inner : A₁ ⊆ (H.dilate (u - zeta)).carrier)
    (hA₁dense : alpha * (H.dilate (u - zeta)).carrier.card ≤ A₁.card)
    (hregular :
      10 * (H.dilate (u + zeta)).carrier.card ≤
        11 * (H.dilate (u - zeta)).carrier.card)
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (hmass :
      1 - epsilon / 32 ≤
        ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) :
    ∃ X : Finset (ZMod N),
      improvedCrootLowerBound H A₂ U zeta alpha epsilon beta ≤ X.card ∧
      X.Nonempty ∧
      1 - epsilon / 16 ≤ boostedMass X A₁ A₂ U epsilon beta := by
  obtain ⟨X, hXcard, hX, happrox⟩ :=
    exists_specialized_boosted_approximation A₁ (H.dilate zeta).carrier A₂ U
      halpha0 halphahalf hbeta0 hbeta1 hepsilon0 hepsilon1
      (CyclicRelativeAlmostPeriodicity.addConst_inner_le H A₁ halpha0
        hzeta hzetau hA₁inner hA₁dense hregular)
      (H.dilate zeta).carrier_nonempty hU hA₂
  have herror := boostedMass_error X A₁ A₂ U happrox
  refine ⟨X, ?_, hX, ?_⟩
  · rw [← rawImprovedCrootLowerBound_eq H A₂ U zeta alpha epsilon beta]
    exact hXcard
  · calc
      1 - epsilon / 16 = 1 - epsilon / 32 - epsilon / 32 := by ring
      _ ≤ (∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
          |boostedMass X A₁ A₂ U epsilon beta -
            ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x| := by
        linarith
      _ ≤ (∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
          -(boostedMass X A₁ A₂ U epsilon beta -
            ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) := by
        gcongr
        exact neg_le_abs _
      _ = boostedMass X A₁ A₂ U epsilon beta := by
        ring

/-- The base-set form of `exists_large_boosted_mass`.  In addition to the
boosted mass it retains the dense Croot--Sisask base `T` inside the narrow
Bohr carrier and the precise translate `X = -z + T` used for convolution.
This is the interface needed for the rank-free local Chang--Sanders step.
-/
theorem exists_large_boosted_mass_with_base
    (H : CyclicBohr.Set N) (A₁ A₂ U : Finset (ZMod N))
    {u zeta alpha epsilon beta : ℝ}
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hzeta : 0 ≤ zeta) (hzetau : zeta ≤ u)
    (hA₁inner : A₁ ⊆ (H.dilate (u - zeta)).carrier)
    (hA₁dense : alpha * (H.dilate (u - zeta)).carrier.card ≤ A₁.card)
    (hregular :
      10 * (H.dilate (u + zeta)).carrier.card ≤
        11 * (H.dilate (u - zeta)).carrier.card)
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (hmass :
      1 - epsilon / 32 ≤
        ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) :
    ∃ (T : Finset (ZMod N)) (z : ZMod N) (X : Finset (ZMod N)),
      improvedCrootLowerBound H A₂ U zeta alpha epsilon beta ≤ T.card ∧
      T ⊆ (H.dilate zeta).carrier ∧ z ∈ T ∧ X = (-z) +ᵥ T ∧
      X.Nonempty ∧
      1 - epsilon / 16 ≤ boostedMass X A₁ A₂ U epsilon beta := by
  obtain ⟨T, z, X, hTcard, hTsub, hz, hXeq, hX, happrox⟩ :=
    exists_specialized_boosted_approximation_with_base
      A₁ (H.dilate zeta).carrier A₂ U
      halpha0 halphahalf hbeta0 hbeta1 hepsilon0 hepsilon1
      (CyclicRelativeAlmostPeriodicity.addConst_inner_le H A₁ halpha0
        hzeta hzetau hA₁inner hA₁dense hregular)
      hA₁ (H.dilate zeta).carrier_nonempty hU hA₂
  have herror := boostedMass_error X A₁ A₂ U happrox
  refine ⟨T, z, X, ?_, hTsub, hz, hXeq, hX, ?_⟩
  · rw [← rawImprovedCrootLowerBound_eq H A₂ U zeta alpha epsilon beta]
    exact hTcard
  · calc
      1 - epsilon / 16 = 1 - epsilon / 32 - epsilon / 32 := by ring
      _ ≤ (∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
          |boostedMass X A₁ A₂ U epsilon beta -
            ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x| := by
        linarith
      _ ≤ (∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
          -(boostedMass X A₁ A₂ U epsilon beta -
            ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) := by
        gcongr
        exact neg_le_abs _
      _ = boostedMass X A₁ A₂ U epsilon beta := by ring

/-- Bloom--Sisask's reflected small-regular-scale orientation.  The first
sifted set controls the Hölder logarithm, the second controls the addition
constant, and the dense untranslated base lies in `R.dilate eta`. -/
theorem exists_large_boosted_mass_with_reflected_base
    (R : CyclicBohr.Set N) (A₁ A₂ U : Finset (ZMod N)) (x : ZMod N)
    {v eta alpha epsilon beta : ℝ}
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (heta : 0 ≤ eta) (hetav : eta ≤ v)
    (hA₂inner : A₂ ⊆ x +ᵥ -(R.dilate (v - eta)).carrier)
    (hA₂dense : alpha * (R.dilate (v - eta)).carrier.card ≤ A₂.card)
    (hregular :
      10 * (R.dilate (v + eta)).carrier.card ≤
        11 * (R.dilate (v - eta)).carrier.card)
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (hmass :
      1 - epsilon / 32 ≤
        ∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y) :
    ∃ (T : Finset (ZMod N)) (z : ZMod N) (X : Finset (ZMod N)),
      reflectedLocalCrootLowerBound R A₁ U eta alpha epsilon beta ≤
        T.card ∧
      T ⊆ (R.dilate eta).carrier ∧ z ∈ T ∧ X = (-z) +ᵥ T ∧
      X.Nonempty ∧
      1 - epsilon / 16 ≤ boostedMass X A₁ A₂ U epsilon beta := by
  have hK2 : 2 ≤ 11 / (10 * alpha) := by
    have hden : 0 < 10 * alpha := mul_pos (by norm_num) halpha0
    rw [le_div_iff₀ hden]
    nlinarith
  obtain ⟨T, z, X, hTcard, hTsub, hz, hXeq, hX, happrox⟩ :=
    exists_reflected_specialized_boosted_approximation_with_base
      A₁ A₂ (R.dilate eta).carrier U
      hbeta0 hbeta1 hepsilon0 hepsilon1 hK2
      (CyclicRelativeAlmostPeriodicity.addConst_neg_reflectedTranslate_inner_le
        R A₂ x halpha0 heta hetav hA₂inner hA₂dense hregular)
      hA₁ hA₂ (R.dilate eta).carrier_nonempty hU
  have herror := boostedMass_error X A₁ A₂ U happrox
  refine ⟨T, z, X, ?_, hTsub, hz, hXeq, hX, ?_⟩
  · simpa only [reflectedLocalCrootLowerBound] using hTcard
  · calc
      1 - epsilon / 16 = 1 - epsilon / 32 - epsilon / 32 := by ring
      _ ≤ (∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y) -
          |boostedMass X A₁ A₂ U epsilon beta -
            ∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y| := by
        linarith
      _ ≤ (∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y) -
          -(boostedMass X A₁ A₂ U epsilon beta -
            ∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y) := by
        gcongr
        exact neg_le_abs _
      _ = boostedMass X A₁ A₂ U epsilon beta := by ring

/-- Shrinking the right summand can only decrease the real-valued addition
constant. -/
lemma addConst_cast_mono_right
    (A S B : Finset (ZMod N)) (hSB : S ⊆ B) :
    (A.addConst S : ℝ) ≤ (A.addConst B : ℝ) := by
  rw [Finset.cast_addConst, Finset.cast_addConst]
  gcongr

/-- Source-ordered reflected Croot--Sisask construction.

First a translation-stable carrier `S` is selected inside the small regular
Bohr scale, and only then is Croot--Sisask applied with base `S`.  Thus the
relative entropy `log (|S|/|T|)` cancels the carrier cardinality appearing in
the shift-set lower bound. -/
theorem exists_large_boosted_mass_with_stable_reflected_base
    (R : CyclicBohr.Set N) (A₁ A₂ U : Finset (ZMod N)) (x : ZMod N)
    {v eta alpha epsilon beta : ℝ}
    (hRradius : 0 < R.radius) (hRrank : 0 < R.rank)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (heta : 0 < eta) (hetav : eta ≤ v)
    (hA₂inner : A₂ ⊆ x +ᵥ -(R.dilate (v - eta)).carrier)
    (hA₂dense : alpha * (R.dilate (v - eta)).carrier.card ≤ A₂.card)
    (hregular :
      10 * (R.dilate (v + eta)).carrier.card ≤
        11 * (R.dilate (v - eta)).carrier.card)
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (hmass :
      1 - epsilon / 32 ≤
        ∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y) :
    let entropy := reflectedStableEntropy A₁ U alpha epsilon beta
    let B := R.dilate eta
    ∃ (S T : Finset (ZMod N)) (z : ZMod N)
        (X : Finset (ZMod N)) (delta : ℝ),
      S.Nonempty ∧ S ⊆ B.carrier ∧
      reflectedImprovedCrootLowerBound S A₁ U
          (11 / (10 * alpha)) epsilon beta ≤ T.card ∧
      T ⊆ S ∧ z ∈ T ∧ X = (-z) +ᵥ T ∧ X.Nonempty ∧
      delta = (400 * ((2 ^ entropy : ℕ) : ℝ) * (B.rank : ℝ))⁻¹ ∧
      0 < delta ∧
      (∀ w ∈ B.dilate delta,
        (Finset.expect Finset.univ fun y : ZMod N ↦
          |CyclicBohr.uniformWeight S (y - w) -
            CyclicBohr.uniformWeight S y|) ≤
          1 / (5 * ((2 ^ entropy : ℕ) : ℝ))) ∧
      2 * (Real.log ((S.card : ℝ) / T.card) + Real.log 4) /
          (1 / 2 : ℝ) ^ 2 < entropy ∧
      1 - epsilon / 16 ≤ boostedMass X A₁ A₂ U epsilon beta := by
  dsimp only
  let entropy := reflectedStableEntropy A₁ U alpha epsilon beta
  let B : CyclicBohr.Set N := R.dilate eta
  have hentropy : 0 < entropy := by
    simpa only [entropy] using
      reflectedStableEntropy_pos A₁ U alpha epsilon beta
  have hBRadius : 0 < B.radius := by
    dsimp only [B]
    simp only [CyclicBohr.Set.radius_dilate, abs_of_pos heta]
    positivity
  have hBRank : 0 < B.rank := by
    simpa only [B, CyclicBohr.Set.rank_dilate] using hRrank
  have hpow : 0 < (2 ^ entropy : ℕ) := pow_pos (by norm_num) _
  obtain ⟨t, delta, htlow, hthigh, hdeltaFormula, hdelta, hdeltat,
      hstable⟩ :=
    CyclicBohr.exists_uniformWeight_translation_stable_dilate_fine
      B (2 ^ entropy) hBRadius hBRank hpow
  let S : Finset (ZMod N) := (B.dilate t).carrier
  have hS : S.Nonempty := (B.dilate t).carrier_nonempty
  have hSsub : S ⊆ B.carrier := by
    have hmono := CyclicBohr.Set.dilate_mono B
      (by linarith : 0 ≤ t) hthigh
    simpa only [S, CyclicBohr.carrier_dilate_one] using hmono
  have hKlarge :
      (((-A₂).addConst B.carrier : ℝ)) ≤ 11 / (10 * alpha) := by
    simpa only [B] using
      (CyclicRelativeAlmostPeriodicity.addConst_neg_reflectedTranslate_inner_le
        R A₂ x halpha0 heta.le hetav hA₂inner hA₂dense hregular)
  have hKsmall :
      (((-A₂).addConst S : ℝ)) ≤ 11 / (10 * alpha) :=
    (addConst_cast_mono_right (-A₂) S B.carrier hSsub).trans hKlarge
  have hK2 : 2 ≤ 11 / (10 * alpha) := by
    have hden : 0 < 10 * alpha := mul_pos (by norm_num) halpha0
    rw [le_div_iff₀ hden]
    nlinarith
  obtain ⟨T, z, X, hTcard, hTsub, hz, hXeq, hX, happrox⟩ :=
    exists_reflected_specialized_boosted_approximation_with_base
      A₁ A₂ S U hbeta0 hbeta1 hepsilon0 hepsilon1 hK2 hKsmall
      hA₁ hA₂ hS hU
  have herror := boostedMass_error X A₁ A₂ U happrox
  have hboosted :
      1 - epsilon / 16 ≤ boostedMass X A₁ A₂ U epsilon beta := by
    calc
      1 - epsilon / 16 = 1 - epsilon / 32 - epsilon / 32 := by ring
      _ ≤ (∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y) -
          |boostedMass X A₁ A₂ U epsilon beta -
            ∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y| := by
        linarith
      _ ≤ (∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y) -
          -(boostedMass X A₁ A₂ U epsilon beta -
            ∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y) := by
        gcongr
        exact neg_le_abs _
      _ = boostedMass X A₁ A₂ U epsilon beta := by ring
  have hcutoff := reflectedStableEntropy_cutoff_of_lowerBound
    S A₁ U T halpha0 hS ⟨z, hz⟩ hTcard
  refine ⟨S, T, z, X, delta, hS, hSsub, hTcard, hTsub, hz, hXeq, hX,
    ?_, hdelta, ?_, ?_, hboosted⟩
  · simpa only [entropy, B] using hdeltaFormula
  · simpa only [S, entropy] using hstable
  · simpa only [entropy] using hcutoff

/-- Sharp source-ordered reflected Croot--Sisask construction.

Here the base is the inner member of a fixed regular pair.  No exponentially
accurate translation scale is selected: the sharp Chang--Sanders smoothing
will use the outer member of this same pair after Croot--Sisask has produced
the shift set. -/
theorem exists_large_boosted_mass_with_sharp_reflected_base
    (R : CyclicBohr.Set N) (A₁ A₂ U : Finset (ZMod N)) (x : ZMod N)
    {v eta alpha epsilon beta : ℝ}
    (hRradius : 0 < R.radius) (hRrank : 0 < R.rank)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (heta : 0 < eta) (hetav : eta ≤ v)
    (hA₂inner : A₂ ⊆ x +ᵥ -(R.dilate (v - eta)).carrier)
    (hA₂dense : alpha * (R.dilate (v - eta)).carrier.card ≤ A₂.card)
    (hregular :
      10 * (R.dilate (v + eta)).carrier.card ≤
        11 * (R.dilate (v - eta)).carrier.card)
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (hmass :
      1 - epsilon / 32 ≤
        ∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y) :
    let entropy := reflectedStableEntropy A₁ U alpha epsilon beta
    let B := R.dilate eta
    ∃ (t delta : ℝ) (S T : Finset (ZMod N))
        (z : ZMod N) (X : Finset (ZMod N)),
      1 / 2 ≤ t ∧ t ≤ 1 ∧
      delta = (400 * (B.rank : ℝ))⁻¹ ∧
      0 < delta ∧ delta < t ∧
      10 * (B.dilate (t + delta)).carrier.card ≤
        11 * (B.dilate (t - delta)).carrier.card ∧
      S = (B.dilate (t - delta)).carrier ∧
      S.Nonempty ∧ S ⊆ B.carrier ∧
      reflectedImprovedCrootLowerBound S A₁ U
          (11 / (10 * alpha)) epsilon beta ≤ T.card ∧
      T ⊆ S ∧ z ∈ T ∧ X = (-z) +ᵥ T ∧ X.Nonempty ∧
      2 * (Real.log ((S.card : ℝ) / T.card) + Real.log 4) /
          (1 / 2 : ℝ) ^ 2 < entropy ∧
      1 - epsilon / 16 ≤ boostedMass X A₁ A₂ U epsilon beta := by
  dsimp only
  let entropy := reflectedStableEntropy A₁ U alpha epsilon beta
  let B : CyclicBohr.Set N := R.dilate eta
  have hBRadius : 0 < B.radius := by
    dsimp only [B]
    simp only [CyclicBohr.Set.radius_dilate, abs_of_pos heta]
    positivity
  have hBRank : 0 < B.rank := by
    simpa only [B, CyclicBohr.Set.rank_dilate] using hRrank
  obtain ⟨t, delta, htlow, hthigh, hdeltaFormula, hdelta, hdeltat,
      hregularB⟩ :=
    CyclicBohr.exists_fixed_regular_scale_fine
      B 1 hBRadius hBRank (by norm_num)
  let S : Finset (ZMod N) := (B.dilate (t - delta)).carrier
  have hS : S.Nonempty := (B.dilate (t - delta)).carrier_nonempty
  have hSsub : S ⊆ B.carrier := by
    have hmono := CyclicBohr.Set.dilate_mono B
      (by linarith : 0 ≤ t - delta) (by linarith : t - delta ≤ 1)
    simpa only [S, CyclicBohr.carrier_dilate_one] using hmono
  have hKlarge :
      (((-A₂).addConst B.carrier : ℝ)) ≤ 11 / (10 * alpha) := by
    simpa only [B] using
      (CyclicRelativeAlmostPeriodicity.addConst_neg_reflectedTranslate_inner_le
        R A₂ x halpha0 heta.le hetav hA₂inner hA₂dense hregular)
  have hKsmall :
      (((-A₂).addConst S : ℝ)) ≤ 11 / (10 * alpha) :=
    (addConst_cast_mono_right (-A₂) S B.carrier hSsub).trans hKlarge
  have hK2 : 2 ≤ 11 / (10 * alpha) := by
    have hden : 0 < 10 * alpha := mul_pos (by norm_num) halpha0
    rw [le_div_iff₀ hden]
    nlinarith
  obtain ⟨T, z, X, hTcard, hTsub, hz, hXeq, hX, happrox⟩ :=
    exists_reflected_specialized_boosted_approximation_with_base
      A₁ A₂ S U hbeta0 hbeta1 hepsilon0 hepsilon1 hK2 hKsmall
      hA₁ hA₂ hS hU
  have herror := boostedMass_error X A₁ A₂ U happrox
  have hboosted :
      1 - epsilon / 16 ≤ boostedMass X A₁ A₂ U epsilon beta := by
    calc
      1 - epsilon / 16 = 1 - epsilon / 32 - epsilon / 32 := by ring
      _ ≤ (∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y) -
          |boostedMass X A₁ A₂ U epsilon beta -
            ∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y| := by
        linarith
      _ ≤ (∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y) -
          -(boostedMass X A₁ A₂ U epsilon beta -
            ∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y) := by
        gcongr
        exact neg_le_abs _
      _ = boostedMass X A₁ A₂ U epsilon beta := by ring
  have hcutoff := reflectedStableEntropy_cutoff_of_lowerBound
    S A₁ U T halpha0 hS ⟨z, hz⟩ hTcard
  refine ⟨t, delta, S, T, z, X, htlow, hthigh, ?_, hdelta, hdeltat,
    ?_, rfl, hS, hSsub, hTcard, hTsub, hz, hXeq, hX, ?_, hboosted⟩
  · simpa only [B, Nat.cast_one, mul_one] using hdeltaFormula
  · simpa using hregularB
  · simpa only [entropy] using hcutoff

/-- Fourier/controller tail over an already selected stable carrier.  This
version invokes `exists_localSpectrum_controller_of_stableCarrier`, so the
rank increment is exactly the relative entropy cutoff for `T ⊆ S`. -/
theorem exists_local_improved_density_increment_of_stable_boosted_base
    (B : CyclicBohr.Set N)
    (A A₁ A₂ U S T X : Finset (ZMod N)) (z : ZMod N)
    (scale regularM entropy ell : ℕ) {beta epsilon sigma delta lower : ℝ}
    (hBradius : 0 < B.radius) (hBrank : 0 < B.rank)
    (hregularM : 0 < regularM) (hentropy0 : 0 < entropy) (hell : 0 < ell)
    (hbeta0 : 0 < beta) (hdensity : beta * scale = A.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hsigma : 0 < sigma) (hdelta : 0 < delta)
    (hA : A.Nonempty) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (hTcard : lower ≤ T.card) (hTsubS : T ⊆ S)
    (hz : z ∈ T) (hXeq : X = (-z) +ᵥ T) (hX : X.Nonempty)
    (hboosted : 1 - epsilon / 16 ≤ boostedMass X A₁ A₂ U epsilon beta)
    (hhigh : ∀ x ∈ U,
      1 + epsilon / 8 ≤ scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x)
    (hstable : ∀ w ∈ B.dilate delta,
      (Finset.expect Finset.univ fun y : ZMod N ↦
        |CyclicBohr.uniformWeight S (y - w) -
          CyclicBohr.uniformWeight S y|) ≤
        1 / (5 * ((2 ^ entropy : ℕ) : ℝ)))
    (hentropy :
      2 * (Real.log ((S.card : ℝ) / T.card) + Real.log 4) /
        (1 / 2 : ℝ) ^ 2 < entropy)
    (hsmall :
      scale *
          ((((entropy : ℝ) * sigma + 3 / (5 * ell)) +
            2 * (1 / 2 : ℝ) ^
              CyclicImprovedParameters.improvedExponent epsilon beta) *
            (A.card : ℝ)⁻¹) ≤ epsilon / 64) :
    ∃ (D : CyclicBohr.Set N) (v xi : ℝ),
      lower ≤ T.card ∧ T ⊆ S ∧ z ∈ T ∧ X = (-z) +ᵥ T ∧ X.Nonempty ∧
      D.radius = min B.radius
        (CyclicLocalChangSanders.stableCarrierControllerRadius
          B entropy ell delta sigma) ∧
      0 < D.radius ∧ B.rank ≤ D.rank ∧
      D.rank ≤ B.rank + entropy ∧
      1 / 2 ≤ v ∧ v ≤ 1 ∧
      xi = (400 * (regularM : ℝ) * (D.rank : ℝ))⁻¹ ∧
      0 < xi ∧ xi < v ∧
      (10 * regularM) * (D.dilate (v + xi)).carrier.card ≤
        (10 * regularM + 1) * (D.dilate (v - xi)).carrier.card ∧
      (D.dilate v).carrier ⊆ B.carrier ∧
      (1 + epsilon / 64) * beta ≤
        ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ
          μ_[ℝ] (D.dilate v).carrier‖_[∞] := by
  have hT : T.Nonempty := ⟨z, hz⟩
  obtain ⟨C, hCrank, hBfreqC, hCradius, hCpos, hCcontrolT⟩ :=
    CyclicLocalChangSanders.exists_localSpectrum_controller_of_stableCarrier
      B T S entropy ell hBradius hBrank hentropy0 hell hdelta hT hTsubS
      (by norm_num) (by norm_num) hsigma hstable hentropy
  have hCcontrolX :
      ∀ r ∈ CyclicChang.relativeLargeSpectrum X (1 / 2), ∀ x ∈ C,
        ‖1 - CyclicBohr.character r x‖ ≤
          (entropy : ℝ) * sigma + 3 / (5 * ell) := by
    intro r hr x hx
    apply hCcontrolT r
    · have hspec :=
        CyclicLocalChangSanders.relativeLargeSpectrum_vadd_finset
          T hT (-z) (1 / 2)
      rw [← hspec, ← hXeq]
      exact hr
    · exact hx
  obtain ⟨D, v, xi, hDradius, hDpos, hBrankD, hDrank,
      hvlow, hvhigh, hxiFormula, hxipos, hxiv, hDregular, hDsub, hinc⟩ :=
    CyclicImprovedDensityIncrement.exists_regular_boosted_density_increment_of_tested_mass_of_controller_subset
      B C A A₁ A₂ U X scale
      (CyclicImprovedParameters.improvedExponent epsilon beta) regularM
      hBradius hBrank hregularM hCpos hBfreqC hbeta0 hdensity
      hepsilon0 hepsilon1 hA hA₁ hA₂ hU hX (by norm_num)
      (by positivity) hCcontrolX (by simpa only [boostedMass] using hboosted)
      hhigh hsmall
  refine ⟨D, v, xi, hTcard, hTsubS, hz, hXeq, hX, ?_, hDpos,
    hBrankD, ?_, hvlow, hvhigh, hxiFormula, hxipos, hxiv, hDregular,
    hDsub, hinc⟩
  · simpa only [hCradius] using hDradius
  · exact hDrank.trans hCrank

/-- Fourier/controller tail for the sharp regular carrier.  Setting
`k = entropy - 1` makes the sharp generator add at most `entropy`
frequencies, while its auxiliary error is even smaller than the common
`3/(5 ell)` density-increment budget. -/
theorem exists_local_improved_density_increment_of_sharp_boosted_base
    (B : CyclicBohr.Set N)
    (A A₁ A₂ U S T X : Finset (ZMod N)) (z : ZMod N)
    (scale regularM entropy ell : ℕ)
    {t delta beta epsilon sigma lower : ℝ}
    (hBradius : 0 < B.radius) (hBrank : 0 < B.rank)
    (hregularM : 0 < regularM) (hentropy0 : 0 < entropy) (hell : 0 < ell)
    (htlow : 1 / 2 ≤ t) (hthigh : t ≤ 1)
    (hdeltaFormula : delta = (400 * (B.rank : ℝ))⁻¹)
    (hdelta : 0 < delta) (hdeltat : delta < t)
    (hregular :
      10 * (B.dilate (t + delta)).carrier.card ≤
        11 * (B.dilate (t - delta)).carrier.card)
    (hSeq : S = (B.dilate (t - delta)).carrier)
    (hbeta0 : 0 < beta) (hdensity : beta * scale = A.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hsigma : 0 < sigma)
    (hA : A.Nonempty) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (hTcard : lower ≤ T.card) (hTsubS : T ⊆ S)
    (hz : z ∈ T) (hXeq : X = (-z) +ᵥ T) (hX : X.Nonempty)
    (hboosted : 1 - epsilon / 16 ≤ boostedMass X A₁ A₂ U epsilon beta)
    (hhigh : ∀ x ∈ U,
      1 + epsilon / 8 ≤ scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x)
    (hentropy :
      2 * (Real.log ((S.card : ℝ) / T.card) + Real.log 4) /
        (1 / 2 : ℝ) ^ 2 < entropy)
    (hsmall :
      scale *
          ((((entropy : ℝ) * sigma + 3 / (5 * ell)) +
            2 * (1 / 2 : ℝ) ^
              CyclicImprovedParameters.improvedExponent epsilon beta) *
            (A.card : ℝ)⁻¹) ≤ epsilon / 64) :
    ∃ (D : CyclicBohr.Set N) (v xi : ℝ),
      lower ≤ T.card ∧ T ⊆ S ∧ z ∈ T ∧ X = (-z) +ᵥ T ∧ X.Nonempty ∧
      D.radius = min B.radius
        (CyclicSharpLocalChangSanders.sharpControllerRadius
          B (entropy - 1) ell sigma) ∧
      0 < D.radius ∧ B.rank ≤ D.rank ∧
      D.rank ≤ B.rank + entropy ∧
      1 / 2 ≤ v ∧ v ≤ 1 ∧
      xi = (400 * (regularM : ℝ) * (D.rank : ℝ))⁻¹ ∧
      0 < xi ∧ xi < v ∧
      (10 * regularM) * (D.dilate (v + xi)).carrier.card ≤
        (10 * regularM + 1) * (D.dilate (v - xi)).carrier.card ∧
      (D.dilate v).carrier ⊆ B.carrier ∧
      (1 + epsilon / 64) * beta ≤
        ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ
          μ_[ℝ] (D.dilate v).carrier‖_[∞] := by
  have hT : T.Nonempty := ⟨z, hz⟩
  have hEntropySucc : entropy - 1 + 1 = entropy := by omega
  have hTsub : T ⊆ (B.dilate (t - delta)).carrier := by
    simpa only [hSeq] using hTsubS
  have hcutoff :
      2 * (Real.log
          (((B.dilate (t - delta)).carrier.card : ℝ) / T.card) +
        Real.log 4) / (1 / 2 : ℝ) ^ 2 <
          ((entropy - 1) + 1 : ℕ) := by
    simpa only [hSeq, hEntropySucc] using hentropy
  obtain ⟨C, hCrank, hBfreqC, hCradius, hCpos, hCcontrolT⟩ :=
    CyclicSharpLocalChangSanders.exists_sharp_localSpectrum_controller_of_regularCarrier
      B T (entropy - 1) ell hBradius hBrank hell htlow hthigh
      hdeltaFormula hdelta hdeltat hregular hT hTsub
      (by norm_num) (by norm_num) hsigma hcutoff
  have haux : (2 : ℝ) / (5 * ell) ≤ 3 / (5 * ell) := by
    have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
    apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 5 * ell)).2
    norm_num
  have hCcontrolX :
      ∀ r ∈ CyclicChang.relativeLargeSpectrum X (1 / 2), ∀ x ∈ C,
        ‖1 - CyclicBohr.character r x‖ ≤
          (entropy : ℝ) * sigma + 3 / (5 * ell) := by
    intro r hr x hx
    have hrT : r ∈ CyclicChang.relativeLargeSpectrum T (1 / 2) := by
      have hspec :=
        CyclicLocalChangSanders.relativeLargeSpectrum_vadd_finset
          T hT (-z) (1 / 2)
      rw [← hspec, ← hXeq]
      exact hr
    calc
      ‖1 - CyclicBohr.character r x‖ ≤
          (((entropy - 1) + 1 : ℕ) : ℝ) * sigma + 2 / (5 * ell) :=
        hCcontrolT r hrT x hx
      _ ≤ (entropy : ℝ) * sigma + 3 / (5 * ell) := by
        rw [hEntropySucc]
        gcongr
  obtain ⟨D, v, xi, hDradius, hDpos, hBrankD, hDrank,
      hvlow, hvhigh, hxiFormula, hxipos, hxiv, hDregular, hDsub, hinc⟩ :=
    CyclicImprovedDensityIncrement.exists_regular_boosted_density_increment_of_tested_mass_of_controller_subset
      B C A A₁ A₂ U X scale
      (CyclicImprovedParameters.improvedExponent epsilon beta) regularM
      hBradius hBrank hregularM hCpos hBfreqC hbeta0 hdensity
      hepsilon0 hepsilon1 hA hA₁ hA₂ hU hX (by norm_num)
      (by positivity) hCcontrolX (by simpa only [boostedMass] using hboosted)
      hhigh hsmall
  refine ⟨D, v, xi, hTcard, hTsubS, hz, hXeq, hX, ?_, hDpos,
    hBrankD, ?_, hvlow, hvhigh, hxiFormula, hxipos, hxiv, hDregular,
    hDsub, hinc⟩
  · simpa only [hCradius] using hDradius
  · exact hDrank.trans (by simpa only [hEntropySucc] using hCrank)

/-- Fully explicit, source-ordered reflected density increment.  The stable
carrier is chosen before Croot--Sisask, and the returned rank increment is
the rank-independent entropy `reflectedStableEntropy`. -/
theorem exists_local_improved_density_increment_stable_reflected_explicit
    (R : CyclicBohr.Set N) (A A₁ A₂ U : Finset (ZMod N))
    (x : ZMod N) (scale regularM : ℕ)
    {v eta alpha beta epsilon : ℝ}
    (hRradius : 0 < R.radius) (hRrank : 0 < R.rank)
    (hregularM : 0 < regularM)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hdensity : beta * scale = A.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (heta : 0 < eta) (hetav : eta ≤ v)
    (hA₂inner : A₂ ⊆ x +ᵥ -(R.dilate (v - eta)).carrier)
    (hA₂dense : alpha * (R.dilate (v - eta)).carrier.card ≤ A₂.card)
    (hregular :
      10 * (R.dilate (v + eta)).carrier.card ≤
        11 * (R.dilate (v - eta)).carrier.card)
    (hA : A.Nonempty) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (hmass :
      1 - epsilon / 32 ≤
        ∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y)
    (hhigh : ∀ y ∈ U,
      1 + epsilon / 8 ≤ scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) y) :
    let entropy := reflectedStableEntropy A₁ U alpha epsilon beta
    let ell := rankFreeAuxiliaryAccuracy epsilon beta
    let sigma := rankFreeExtractedRadius epsilon beta entropy
    ∃ (S T : Finset (ZMod N)) (z : ZMod N) (X : Finset (ZMod N))
        (delta : ℝ) (D : CyclicBohr.Set N) (w xi : ℝ),
      S.Nonempty ∧ S ⊆ (R.dilate eta).carrier ∧
      reflectedImprovedCrootLowerBound S A₁ U
          (11 / (10 * alpha)) epsilon beta ≤ T.card ∧
      T ⊆ S ∧ z ∈ T ∧ X = (-z) +ᵥ T ∧ X.Nonempty ∧
      delta = (400 * ((2 ^ entropy : ℕ) : ℝ) * (R.rank : ℝ))⁻¹ ∧
      0 < delta ∧
      D.radius = min (R.dilate eta).radius
        (CyclicLocalChangSanders.stableCarrierControllerRadius
          (R.dilate eta) entropy ell delta sigma) ∧
      0 < D.radius ∧ R.rank ≤ D.rank ∧
      D.rank ≤ R.rank + entropy ∧
      1 / 2 ≤ w ∧ w ≤ 1 ∧
      xi = (400 * (regularM : ℝ) * (D.rank : ℝ))⁻¹ ∧
      0 < xi ∧ xi < w ∧
      (10 * regularM) * (D.dilate (w + xi)).carrier.card ≤
        (10 * regularM + 1) * (D.dilate (w - xi)).carrier.card ∧
      (D.dilate w).carrier ⊆ (R.dilate eta).carrier ∧
      (1 + epsilon / 64) * beta ≤
        ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ
          μ_[ℝ] (D.dilate w).carrier‖_[∞] := by
  dsimp only
  let entropy := reflectedStableEntropy A₁ U alpha epsilon beta
  let ell := rankFreeAuxiliaryAccuracy epsilon beta
  let sigma := rankFreeExtractedRadius epsilon beta entropy
  obtain ⟨S, T, z, X, delta, hS, hSsub, hTcard, hTsubS, hz, hXeq,
      hX, hdeltaFormula, hdelta, hstable, hentropy, hboosted⟩ :=
    exists_large_boosted_mass_with_stable_reflected_base
      R A₁ A₂ U x hRradius hRrank halpha0 halphahalf hbeta0 hbeta1
      hepsilon0 hepsilon1 heta hetav hA₂inner hA₂dense hregular
      hA₁ hA₂ hU hmass
  have hBRadius : 0 < (R.dilate eta).radius := by
    simp only [CyclicBohr.Set.radius_dilate, abs_of_pos heta]
    positivity
  have hBRank : 0 < (R.dilate eta).rank := by
    simpa only [CyclicBohr.Set.rank_dilate] using hRrank
  obtain ⟨D, w, xi, hTcard', hTsubS', hz', hXeq', hX', hDradius,
      hDpos, hBRankD, hDrank, hwlow, hwhigh, hxiFormula, hxipos, hxiw,
      hDregular, hDsub, hinc⟩ :=
    exists_local_improved_density_increment_of_stable_boosted_base
      (R.dilate eta) A A₁ A₂ U S T X z scale regularM entropy ell
      (beta := beta) (epsilon := epsilon) (sigma := sigma)
      (delta := delta)
      (lower := reflectedImprovedCrootLowerBound S A₁ U
        (11 / (10 * alpha)) epsilon beta)
      hBRadius hBRank hregularM
      (by simpa only [entropy] using
        reflectedStableEntropy_pos A₁ U alpha epsilon beta)
      (by simpa only [ell] using
        rankFreeAuxiliaryAccuracy_pos epsilon beta)
      hbeta0 hdensity hepsilon0 hepsilon1
      (by
        dsimp only [sigma]
        exact rankFreeExtractedRadius_pos hepsilon0 hbeta0
          (by simpa only [entropy] using
            reflectedStableEntropy_pos A₁ U alpha epsilon beta))
      hdelta hA hA₁ hA₂ hU hTcard hTsubS hz hXeq hX hboosted hhigh
      hstable hentropy
      (explicit_rankFree_smoothing_error_bound A scale entropy
        hepsilon0 hbeta0
        (by simpa only [entropy] using
          reflectedStableEntropy_pos A₁ U alpha epsilon beta)
        hA hdensity)
  refine ⟨S, T, z, X, delta, D, w, xi, hS, hSsub, hTcard', hTsubS',
    hz', hXeq', hX', ?_, hdelta, hDradius, hDpos, ?_, ?_, hwlow,
    hwhigh, hxiFormula, hxipos, hxiw, hDregular, hDsub, hinc⟩
  · simpa only [entropy, CyclicBohr.Set.rank_dilate] using hdeltaFormula
  · simpa only [CyclicBohr.Set.rank_dilate] using hBRankD
  · simpa only [CyclicBohr.Set.rank_dilate] using hDrank

/-- Fully explicit reflected density increment using the sharp
Chang--Sanders controller.  Its radius loses only the linear smoothing
length `4 * entropy`, and its rank increment is the same rank-independent
entropy as in the stable-carrier formulation. -/
theorem exists_local_improved_density_increment_sharp_reflected_explicit
    (R : CyclicBohr.Set N) (A A₁ A₂ U : Finset (ZMod N))
    (x : ZMod N) (scale regularM : ℕ)
    {v eta alpha beta epsilon : ℝ}
    (hRradius : 0 < R.radius) (hRrank : 0 < R.rank)
    (hregularM : 0 < regularM)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hdensity : beta * scale = A.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (heta : 0 < eta) (hetav : eta ≤ v)
    (hA₂inner : A₂ ⊆ x +ᵥ -(R.dilate (v - eta)).carrier)
    (hA₂dense : alpha * (R.dilate (v - eta)).carrier.card ≤ A₂.card)
    (hregular :
      10 * (R.dilate (v + eta)).carrier.card ≤
        11 * (R.dilate (v - eta)).carrier.card)
    (hA : A.Nonempty) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (hmass :
      1 - epsilon / 32 ≤
        ∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y)
    (hhigh : ∀ y ∈ U,
      1 + epsilon / 8 ≤ scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) y) :
    let entropy := reflectedStableEntropy A₁ U alpha epsilon beta
    let ell := rankFreeAuxiliaryAccuracy epsilon beta
    let sigma := rankFreeExtractedRadius epsilon beta entropy
    ∃ (S T : Finset (ZMod N)) (z : ZMod N) (X : Finset (ZMod N))
        (D : CyclicBohr.Set N) (w xi : ℝ),
      S.Nonempty ∧ S ⊆ (R.dilate eta).carrier ∧
      reflectedImprovedCrootLowerBound S A₁ U
          (11 / (10 * alpha)) epsilon beta ≤ T.card ∧
      T ⊆ S ∧ z ∈ T ∧ X = (-z) +ᵥ T ∧ X.Nonempty ∧
      D.radius = min (R.dilate eta).radius
        (CyclicSharpLocalChangSanders.sharpControllerRadius
          (R.dilate eta) (entropy - 1) ell sigma) ∧
      0 < D.radius ∧ R.rank ≤ D.rank ∧
      D.rank ≤ R.rank + entropy ∧
      1 / 2 ≤ w ∧ w ≤ 1 ∧
      xi = (400 * (regularM : ℝ) * (D.rank : ℝ))⁻¹ ∧
      0 < xi ∧ xi < w ∧
      (10 * regularM) * (D.dilate (w + xi)).carrier.card ≤
        (10 * regularM + 1) * (D.dilate (w - xi)).carrier.card ∧
      (D.dilate w).carrier ⊆ (R.dilate eta).carrier ∧
      (1 + epsilon / 64) * beta ≤
        ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ
          μ_[ℝ] (D.dilate w).carrier‖_[∞] := by
  dsimp only
  let entropy := reflectedStableEntropy A₁ U alpha epsilon beta
  let ell := rankFreeAuxiliaryAccuracy epsilon beta
  let sigma := rankFreeExtractedRadius epsilon beta entropy
  obtain ⟨t, delta, S, T, z, X, htlow, hthigh, hdeltaFormula,
      hdelta, hdeltat, hregularB, hSeq, hS, hSsub, hTcard, hTsubS,
      hz, hXeq, hX, hentropy, hboosted⟩ :=
    exists_large_boosted_mass_with_sharp_reflected_base
      R A₁ A₂ U x hRradius hRrank halpha0 halphahalf hbeta0 hbeta1
      hepsilon0 hepsilon1 heta hetav hA₂inner hA₂dense hregular
      hA₁ hA₂ hU hmass
  have hBRadius : 0 < (R.dilate eta).radius := by
    simp only [CyclicBohr.Set.radius_dilate, abs_of_pos heta]
    positivity
  have hBRank : 0 < (R.dilate eta).rank := by
    simpa only [CyclicBohr.Set.rank_dilate] using hRrank
  obtain ⟨D, w, xi, hTcard', hTsubS', hz', hXeq', hX', hDradius,
      hDpos, hBRankD, hDrank, hwlow, hwhigh, hxiFormula, hxipos, hxiw,
      hDregular, hDsub, hinc⟩ :=
    exists_local_improved_density_increment_of_sharp_boosted_base
      (R.dilate eta) A A₁ A₂ U S T X z scale regularM entropy ell
      (t := t) (delta := delta) (beta := beta) (epsilon := epsilon)
      (sigma := sigma)
      (lower := reflectedImprovedCrootLowerBound S A₁ U
        (11 / (10 * alpha)) epsilon beta)
      hBRadius hBRank hregularM
      (by simpa only [entropy] using
        reflectedStableEntropy_pos A₁ U alpha epsilon beta)
      (by simpa only [ell] using
        rankFreeAuxiliaryAccuracy_pos epsilon beta)
      htlow hthigh hdeltaFormula hdelta hdeltat hregularB hSeq
      hbeta0 hdensity hepsilon0 hepsilon1
      (by
        dsimp only [sigma]
        exact rankFreeExtractedRadius_pos hepsilon0 hbeta0
          (by simpa only [entropy] using
            reflectedStableEntropy_pos A₁ U alpha epsilon beta))
      hA hA₁ hA₂ hU hTcard hTsubS hz hXeq hX hboosted hhigh
      hentropy
      (explicit_rankFree_smoothing_error_bound A scale entropy
        hepsilon0 hbeta0
        (by simpa only [entropy] using
          reflectedStableEntropy_pos A₁ U alpha epsilon beta)
        hA hdensity)
  refine ⟨S, T, z, X, D, w, xi, hS, hSsub, hTcard', hTsubS', hz',
    hXeq', hX', hDradius, hDpos, ?_, ?_, hwlow, hwhigh, hxiFormula,
    hxipos, hxiw, hDregular, hDsub, hinc⟩
  · simpa only [CyclicBohr.Set.rank_dilate] using hBRankD
  · simpa only [CyclicBohr.Set.rank_dilate] using hDrank

/-- The Fourier/controller tail of the rank-free argument, starting from an
already constructed contained boosted base.  This separates the common
bootstrapping algebra from the two possible Croot--Sisask orientations. -/
theorem exists_local_improved_density_increment_rankFree_of_boosted_base
    (H : CyclicBohr.Set N)
    (A A₁ A₂ U T X : Finset (ZMod N)) (z : ZMod N)
    (scale regularM entropy ell : ℕ) {zeta beta epsilon sigma lower : ℝ}
    (hHradius : 0 < H.radius) (hHrank : 0 < H.rank)
    (hregularM : 0 < regularM) (hentropy0 : 0 < entropy) (hell : 0 < ell)
    (hbeta0 : 0 < beta) (hdensity : beta * scale = A.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta)
    (hA : A.Nonempty) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (hTcard : lower ≤ T.card) (hTsub : T ⊆ (H.dilate zeta).carrier)
    (hz : z ∈ T) (hXeq : X = (-z) +ᵥ T) (hX : X.Nonempty)
    (hboosted : 1 - epsilon / 16 ≤ boostedMass X A₁ A₂ U epsilon beta)
    (hhigh : ∀ x ∈ U,
      1 + epsilon / 8 ≤ scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x)
    (hentropy :
      2 * (Real.log
          (((H.dilate (2 * zeta)).carrier.card : ℝ) / T.card) +
        Real.log 4) / (1 / 2 : ℝ) ^ 2 < entropy)
    (hsmall :
      scale *
          ((((entropy : ℝ) * sigma + 3 / (5 * ell)) +
            2 * (1 / 2 : ℝ) ^
              CyclicImprovedParameters.improvedExponent epsilon beta) *
            (A.card : ℝ)⁻¹) ≤ epsilon / 64) :
    ∃ (D : CyclicBohr.Set N) (v xi : ℝ),
      lower ≤ T.card ∧ T ⊆ (H.dilate zeta).carrier ∧ z ∈ T ∧
      X = (-z) +ᵥ T ∧ X.Nonempty ∧
      D.radius = min (H.dilate zeta).radius
        (CyclicLocalChangSanders.rankFreeControllerRadius
          H entropy ell zeta sigma) ∧
      0 < D.radius ∧ H.rank ≤ D.rank ∧
      D.rank ≤ H.rank + entropy ∧
      1 / 2 ≤ v ∧ v ≤ 1 ∧
      xi = (400 * (regularM : ℝ) * (D.rank : ℝ))⁻¹ ∧
      0 < xi ∧ xi < v ∧
      (10 * regularM) * (D.dilate (v + xi)).carrier.card ≤
        (10 * regularM + 1) * (D.dilate (v - xi)).carrier.card ∧
      (D.dilate v).carrier ⊆ (H.dilate zeta).carrier ∧
      (1 + epsilon / 64) * beta ≤
        ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ
          μ_[ℝ] (D.dilate v).carrier‖_[∞] := by
  have hT : T.Nonempty := ⟨z, hz⟩
  obtain ⟨C, hCrank, hHfreqC, hCradius, hCpos, hCcontrolT⟩ :=
    CyclicLocalChangSanders.exists_rankFree_localSpectrum_controller
      H T entropy ell hHradius hHrank hentropy0 hell hzeta hT hTsub
      (by norm_num) (by norm_num) hsigma hentropy
  have hCcontrolX :
      ∀ r ∈ CyclicChang.relativeLargeSpectrum X (1 / 2), ∀ x ∈ C,
        ‖1 - CyclicBohr.character r x‖ ≤
          (entropy : ℝ) * sigma + 3 / (5 * ell) := by
    intro r hr x hx
    apply hCcontrolT r
    · have hspec :=
        CyclicLocalChangSanders.relativeLargeSpectrum_vadd_finset
          T hT (-z) (1 / 2)
      rw [← hspec, ← hXeq]
      exact hr
    · exact hx
  have hRradius : 0 < (H.dilate zeta).radius := by
    simp only [CyclicBohr.Set.radius_dilate, abs_of_pos hzeta]
    positivity
  have hRrank : 0 < (H.dilate zeta).rank := by
    simpa only [CyclicBohr.Set.rank_dilate] using hHrank
  have hRfreqC : (H.dilate zeta).frequencies ⊆ C.frequencies := by
    simpa only [CyclicBohr.Set.frequencies_dilate] using hHfreqC
  obtain ⟨D, v, xi, hDradius, hDpos, hRrankD, hDrank,
      hvlow, hvhigh, hxiFormula, hxipos, hxiv, hDregular, hDsub, hinc⟩ :=
    CyclicImprovedDensityIncrement.exists_regular_boosted_density_increment_of_tested_mass_of_controller_subset
      (H.dilate zeta) C A A₁ A₂ U X scale
      (CyclicImprovedParameters.improvedExponent epsilon beta) regularM
      hRradius hRrank hregularM hCpos hRfreqC hbeta0 hdensity
      hepsilon0 hepsilon1 hA hA₁ hA₂ hU hX (by norm_num)
      (by positivity) hCcontrolX (by simpa only [boostedMass] using hboosted)
      hhigh hsmall
  refine ⟨D, v, xi, hTcard, hTsub, hz, hXeq, hX, ?_, hDpos, ?_, ?_,
    hvlow, hvhigh, hxiFormula, hxipos, hxiv, hDregular, hDsub, hinc⟩
  · simpa only [hCradius] using hDradius
  · simpa only [CyclicBohr.Set.rank_dilate] using hRrankD
  · exact hDrank.trans hCrank

/-- Fully explicit reflected specialization of Bloom--Sisask Lemma 8.  Its
rank increment depends on the two sifted relative densities, not on the
ambient Bohr rank. -/
theorem exists_local_improved_density_increment_rankFree_reflected_explicit
    (R : CyclicBohr.Set N) (A A₁ A₂ U : Finset (ZMod N))
    (x : ZMod N) (scale regularM : ℕ)
    {v eta alpha beta epsilon : ℝ}
    (hRradius : 0 < R.radius) (hRrank : 0 < R.rank)
    (hregularM : 0 < regularM)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hdensity : beta * scale = A.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (heta : 0 < eta) (hetav : eta ≤ v)
    (hA₂inner : A₂ ⊆ x +ᵥ -(R.dilate (v - eta)).carrier)
    (hA₂dense : alpha * (R.dilate (v - eta)).carrier.card ≤ A₂.card)
    (hregular :
      10 * (R.dilate (v + eta)).carrier.card ≤
        11 * (R.dilate (v - eta)).carrier.card)
    (hA : A.Nonempty) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (hmass :
      1 - epsilon / 32 ≤
        ∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y)
    (hhigh : ∀ y ∈ U,
      1 + epsilon / 8 ≤ scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) y) :
    let entropy := reflectedRankFreeEntropy R A₁ U eta alpha epsilon beta
    let ell := rankFreeAuxiliaryAccuracy epsilon beta
    let sigma := rankFreeExtractedRadius epsilon beta entropy
    ∃ (T : Finset (ZMod N)) (z : ZMod N) (X : Finset (ZMod N))
        (D : CyclicBohr.Set N) (w xi : ℝ),
      reflectedLocalCrootLowerBound R A₁ U eta alpha epsilon beta ≤
        T.card ∧
      T ⊆ (R.dilate eta).carrier ∧ z ∈ T ∧ X = (-z) +ᵥ T ∧
      X.Nonempty ∧
      D.radius = min (R.dilate eta).radius
        (CyclicLocalChangSanders.rankFreeControllerRadius
          R entropy ell eta sigma) ∧
      0 < D.radius ∧ R.rank ≤ D.rank ∧
      D.rank ≤ R.rank + entropy ∧
      1 / 2 ≤ w ∧ w ≤ 1 ∧
      xi = (400 * (regularM : ℝ) * (D.rank : ℝ))⁻¹ ∧
      0 < xi ∧ xi < w ∧
      (10 * regularM) * (D.dilate (w + xi)).carrier.card ≤
        (10 * regularM + 1) * (D.dilate (w - xi)).carrier.card ∧
      (D.dilate w).carrier ⊆ (R.dilate eta).carrier ∧
      (1 + epsilon / 64) * beta ≤
        ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ
          μ_[ℝ] (D.dilate w).carrier‖_[∞] := by
  dsimp only
  let entropy := reflectedRankFreeEntropy R A₁ U eta alpha epsilon beta
  let ell := rankFreeAuxiliaryAccuracy epsilon beta
  let sigma := rankFreeExtractedRadius epsilon beta entropy
  obtain ⟨T, z, X, hTcard, hTsub, hz, hXeq, hX, hboosted⟩ :=
    exists_large_boosted_mass_with_reflected_base
      R A₁ A₂ U x halpha0 halphahalf hbeta0 hbeta1
      hepsilon0 hepsilon1 heta.le hetav hA₂inner hA₂dense hregular
      hA₁ hA₂ hU hmass
  refine ⟨T, z, X, ?_⟩
  apply exists_local_improved_density_increment_rankFree_of_boosted_base
    R A A₁ A₂ U T X z scale regularM entropy ell
      hRradius hRrank hregularM
      (reflectedRankFreeEntropy_pos R A₁ U eta alpha epsilon beta)
      (rankFreeAuxiliaryAccuracy_pos epsilon beta)
      hbeta0 hdensity hepsilon0 hepsilon1
      (rankFreeExtractedRadius_pos hepsilon0 hbeta0
        (reflectedRankFreeEntropy_pos R A₁ U eta alpha epsilon beta))
      heta hA hA₁ hA₂ hU hTcard hTsub hz hXeq hX hboosted hhigh
  · exact reflectedRankFreeEntropy_cutoff_of_lowerBound
      R A₁ U T halpha0 hTcard ⟨z, hz⟩
  · exact explicit_rankFree_smoothing_error_bound A scale entropy
      hepsilon0 hbeta0
      (reflectedRankFreeEntropy_pos R A₁ U eta alpha epsilon beta)
      hA hdensity

/-- The complete local density increment with the rank-free local
Chang--Sanders controller.  The two explicit numerical hypotheses isolate
the remaining bookkeeping: `entropy` must dominate the relative spectrum
entropy forced by the Croot--Sisask lower bound, and the chosen controller
error must fit the density-increment budget. -/
theorem exists_local_improved_density_increment_rankFree
    (H : CyclicBohr.Set N) (A A₁ A₂ U : Finset (ZMod N))
    (scale regularM entropy ell : ℕ) {u zeta alpha beta epsilon sigma : ℝ}
    (hHradius : 0 < H.radius) (hHrank : 0 < H.rank)
    (hregularM : 0 < regularM) (hentropy0 : 0 < entropy) (hell : 0 < ell)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hdensity : beta * scale = A.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hsigma : 0 < sigma)
    (hzeta : 0 < zeta) (hzetau : zeta ≤ u)
    (hA₁inner : A₁ ⊆ (H.dilate (u - zeta)).carrier)
    (hA₁dense : alpha * (H.dilate (u - zeta)).carrier.card ≤ A₁.card)
    (hregular :
      10 * (H.dilate (u + zeta)).carrier.card ≤
        11 * (H.dilate (u - zeta)).carrier.card)
    (hA : A.Nonempty) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (hmass :
      1 - epsilon / 32 ≤
        ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x)
    (hhigh : ∀ x ∈ U,
      1 + epsilon / 8 ≤ scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x)
    (hentropy : ∀ T : Finset (ZMod N),
      improvedCrootLowerBound H A₂ U zeta alpha epsilon beta ≤ T.card →
      T.Nonempty →
      2 * (Real.log
          (((H.dilate (2 * zeta)).carrier.card : ℝ) / T.card) +
        Real.log 4) / (1 / 2 : ℝ) ^ 2 < entropy)
    (hsmall :
      scale *
          ((((entropy : ℝ) * sigma + 3 / (5 * ell)) +
            2 * (1 / 2 : ℝ) ^
              CyclicImprovedParameters.improvedExponent epsilon beta) *
            (A.card : ℝ)⁻¹) ≤ epsilon / 64) :
    ∃ (T : Finset (ZMod N)) (z : ZMod N) (X : Finset (ZMod N))
        (D : CyclicBohr.Set N) (v xi : ℝ),
      improvedCrootLowerBound H A₂ U zeta alpha epsilon beta ≤ T.card ∧
      T ⊆ (H.dilate zeta).carrier ∧ z ∈ T ∧ X = (-z) +ᵥ T ∧
      X.Nonempty ∧
      D.radius = min (H.dilate zeta).radius
        (CyclicLocalChangSanders.rankFreeControllerRadius
          H entropy ell zeta sigma) ∧
      0 < D.radius ∧
      H.rank ≤ D.rank ∧ D.rank ≤ H.rank + entropy ∧
      1 / 2 ≤ v ∧ v ≤ 1 ∧
      xi = (400 * (regularM : ℝ) * (D.rank : ℝ))⁻¹ ∧
      0 < xi ∧ xi < v ∧
      (10 * regularM) * (D.dilate (v + xi)).carrier.card ≤
        (10 * regularM + 1) * (D.dilate (v - xi)).carrier.card ∧
      (D.dilate v).carrier ⊆ (H.dilate zeta).carrier ∧
      (1 + epsilon / 64) * beta ≤
        ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ
          μ_[ℝ] (D.dilate v).carrier‖_[∞] := by
  obtain ⟨T, z, X, hTcard, hTsub, hz, hXeq, hX, hboosted⟩ :=
    exists_large_boosted_mass_with_base H A₁ A₂ U
      halpha0 halphahalf hbeta0 hbeta1 hepsilon0 hepsilon1 hzeta.le
      hzetau hA₁inner hA₁dense hregular hA₁ hA₂ hU hmass
  have hT : T.Nonempty := ⟨z, hz⟩
  obtain ⟨C, hCrank, hHfreqC, hCradius, hCpos, hCcontrolT⟩ :=
    CyclicLocalChangSanders.exists_rankFree_localSpectrum_controller
      H T entropy ell hHradius hHrank hentropy0 hell hzeta hT hTsub
      (by norm_num) (by norm_num) hsigma (hentropy T hTcard hT)
  have hCcontrolX :
      ∀ r ∈ CyclicChang.relativeLargeSpectrum X (1 / 2), ∀ x ∈ C,
        ‖1 - CyclicBohr.character r x‖ ≤
          (entropy : ℝ) * sigma + 3 / (5 * ell) := by
    intro r hr x hx
    apply hCcontrolT r
    · have hspec :=
        CyclicLocalChangSanders.relativeLargeSpectrum_vadd_finset
          T hT (-z) (1 / 2)
      rw [← hspec, ← hXeq]
      exact hr
    · exact hx
  have hRradius : 0 < (H.dilate zeta).radius := by
    simp only [CyclicBohr.Set.radius_dilate, abs_of_pos hzeta]
    positivity
  have hRrank : 0 < (H.dilate zeta).rank := by
    simpa only [CyclicBohr.Set.rank_dilate] using hHrank
  have hRfreqC : (H.dilate zeta).frequencies ⊆ C.frequencies := by
    simpa only [CyclicBohr.Set.frequencies_dilate] using hHfreqC
  obtain ⟨D, v, xi, hDradius, hDpos, hRrankD, hDrank,
      hvlow, hvhigh, hxiFormula, hxipos, hxiv, hDregular, hDsub, hinc⟩ :=
    CyclicImprovedDensityIncrement.exists_regular_boosted_density_increment_of_tested_mass_of_controller_subset
      (H.dilate zeta) C A A₁ A₂ U X scale
      (CyclicImprovedParameters.improvedExponent epsilon beta) regularM
      hRradius hRrank hregularM hCpos hRfreqC hbeta0 hdensity
      hepsilon0 hepsilon1 hA hA₁ hA₂ hU hX (by norm_num)
      (by positivity) hCcontrolX (by simpa only [boostedMass] using hboosted)
      hhigh hsmall
  refine ⟨T, z, X, D, v, xi, hTcard, hTsub, hz, hXeq, hX, ?_,
    hDpos, ?_, ?_, hvlow, hvhigh, hxiFormula, hxipos, hxiv, hDregular,
    hDsub, hinc⟩
  · simpa only [hCradius] using hDradius
  · simpa only [CyclicBohr.Set.rank_dilate] using hRrankD
  · exact hDrank.trans hCrank

/-- Canonical parameter specialization of the rank-free local density
increment.  Unlike the older global-Chang theorem below, every entropy and
smoothing hypothesis has now been discharged by explicit definitions. -/
theorem exists_local_improved_density_increment_rankFree_explicit
    (H : CyclicBohr.Set N) (A A₁ A₂ U : Finset (ZMod N))
    (scale regularM : ℕ) {u zeta alpha beta epsilon : ℝ}
    (hHradius : 0 < H.radius) (hHrank : 0 < H.rank)
    (hregularM : 0 < regularM)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hdensity : beta * scale = A.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hzeta : 0 < zeta) (hzetau : zeta ≤ u)
    (hA₁inner : A₁ ⊆ (H.dilate (u - zeta)).carrier)
    (hA₁dense : alpha * (H.dilate (u - zeta)).carrier.card ≤ A₁.card)
    (hregular :
      10 * (H.dilate (u + zeta)).carrier.card ≤
        11 * (H.dilate (u - zeta)).carrier.card)
    (hA : A.Nonempty) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (hmass :
      1 - epsilon / 32 ≤
        ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x)
    (hhigh : ∀ x ∈ U,
      1 + epsilon / 8 ≤ scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x) :
    let entropy := rankFreeEntropy H A₂ U zeta alpha epsilon beta
    let ell := rankFreeAuxiliaryAccuracy epsilon beta
    let sigma := rankFreeExtractedRadius epsilon beta entropy
    ∃ (T : Finset (ZMod N)) (z : ZMod N) (X : Finset (ZMod N))
        (D : CyclicBohr.Set N) (v xi : ℝ),
      improvedCrootLowerBound H A₂ U zeta alpha epsilon beta ≤ T.card ∧
      T ⊆ (H.dilate zeta).carrier ∧ z ∈ T ∧ X = (-z) +ᵥ T ∧
      X.Nonempty ∧
      D.radius = min (H.dilate zeta).radius
        (CyclicLocalChangSanders.rankFreeControllerRadius
          H entropy ell zeta sigma) ∧
      0 < D.radius ∧
      H.rank ≤ D.rank ∧ D.rank ≤ H.rank + entropy ∧
      1 / 2 ≤ v ∧ v ≤ 1 ∧
      xi = (400 * (regularM : ℝ) * (D.rank : ℝ))⁻¹ ∧
      0 < xi ∧ xi < v ∧
      (10 * regularM) * (D.dilate (v + xi)).carrier.card ≤
        (10 * regularM + 1) * (D.dilate (v - xi)).carrier.card ∧
      (D.dilate v).carrier ⊆ (H.dilate zeta).carrier ∧
      (1 + epsilon / 64) * beta ≤
        ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ
          μ_[ℝ] (D.dilate v).carrier‖_[∞] := by
  dsimp only
  apply exists_local_improved_density_increment_rankFree
    H A A₁ A₂ U scale regularM
      (rankFreeEntropy H A₂ U zeta alpha epsilon beta)
      (rankFreeAuxiliaryAccuracy epsilon beta)
      hHradius hHrank hregularM
      (rankFreeEntropy_pos H A₂ U zeta alpha epsilon beta)
      (rankFreeAuxiliaryAccuracy_pos epsilon beta)
      halpha0 halphahalf hbeta0 hbeta1 hdensity hepsilon0 hepsilon1
      (rankFreeExtractedRadius_pos hepsilon0 hbeta0
        (rankFreeEntropy_pos H A₂ U zeta alpha epsilon beta))
      hzeta hzetau hA₁inner hA₁dense hregular hA hA₁ hA₂ hU hmass hhigh
  · intro T hTbound hT
    exact rankFreeEntropy_cutoff_of_lowerBound H A₂ U T
      halpha0 hTbound hT
  · exact explicit_rankFree_smoothing_error_bound A scale
      (rankFreeEntropy H A₂ U zeta alpha epsilon beta)
      hepsilon0 hbeta0
      (rankFreeEntropy_pos H A₂ U zeta alpha epsilon beta) hA hdensity

/-- The complete improved local density increment with explicit parameters.
It retains the Croot--Sisask cardinality lower bound, puts the new Bohr
carrier at a fine regular scale, and gains the fixed multiplicative factor
`1 + epsilon / 64`. -/
theorem exists_local_improved_density_increment
    (H : CyclicBohr.Set N) (A A₁ A₂ U : Finset (ZMod N))
    (scale m : ℕ) {u zeta alpha beta epsilon : ℝ}
    (hHradius : 0 < H.radius) (hHrank : 0 < H.rank) (hm : 0 < m)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hdensity : beta * scale = A.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hzeta : 0 < zeta) (hzetau : zeta ≤ u)
    (hA₁inner : A₁ ⊆ (H.dilate (u - zeta)).carrier)
    (hA₁dense : alpha * (H.dilate (u - zeta)).carrier.card ≤ A₁.card)
    (hregular :
      10 * (H.dilate (u + zeta)).carrier.card ≤
        11 * (H.dilate (u - zeta)).carrier.card)
    (hA : A.Nonempty) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (hmass :
      1 - epsilon / 32 ≤
        ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x)
    (hhigh : ∀ x ∈ U,
      1 + epsilon / 8 ≤ scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x) :
    ∃ (X : Finset (ZMod N)) (D : CyclicBohr.Set N) (v xi : ℝ),
      improvedCrootLowerBound H A₂ U zeta alpha epsilon beta ≤ X.card ∧
      X.Nonempty ∧
      D.radius = min (H.dilate zeta).radius
        (CyclicImprovedParameters.improvedRho epsilon beta X) ∧
      0 < D.radius ∧
      H.rank ≤ D.rank ∧
      D.rank ≤ H.rank + CyclicChang.changRankBound X (1 / 2) ∧
      1 / 2 ≤ v ∧ v ≤ 1 ∧
      xi = (400 * (m : ℝ) * (D.rank : ℝ))⁻¹ ∧
      0 < xi ∧ xi < v ∧
      (10 * m) * (D.dilate (v + xi)).carrier.card ≤
        (10 * m + 1) * (D.dilate (v - xi)).carrier.card ∧
      (D.dilate v).carrier ⊆ (H.dilate zeta).carrier ∧
      (1 + epsilon / 64) * beta ≤
        ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ
          μ_[ℝ] (D.dilate v).carrier‖_[∞] := by
  obtain ⟨X, hXcard, hX, hboosted⟩ :=
    exists_large_boosted_mass H A₁ A₂ U
      halpha0 halphahalf hbeta0 hbeta1 hepsilon0 hepsilon1
      hzeta.le hzetau hA₁inner hA₁dense hregular hA₁ hA₂ hU hmass
  have hRradius : 0 < (H.dilate zeta).radius := by
    simp only [CyclicBohr.Set.radius_dilate, abs_of_pos hzeta]
    positivity
  have hRrank : 0 < (H.dilate zeta).rank := by
    simpa only [CyclicBohr.Set.rank_dilate] using hHrank
  obtain ⟨D, v, xi, hDradius, hDpos, hHrankD, hDrank,
      hvlow, hvhigh, hxiFormula, hxipos, hxiv, hDregular, hDsub, hinc⟩ :=
    CyclicImprovedDensityIncrement.exists_regular_boosted_density_increment_of_tested_mass
      (H.dilate zeta) A A₁ A₂ U X scale
      (CyclicImprovedParameters.improvedExponent epsilon beta) m
      hRradius hRrank hm hbeta0 hdensity hepsilon0 hepsilon1
      hA hA₁ hA₂ hU hX (by norm_num)
      (CyclicImprovedParameters.improvedRho_pos X hepsilon0 hbeta0)
      hboosted hhigh
      (CyclicImprovedParameters.explicit_improved_smoothing_error_bound
        A X scale hepsilon0 hbeta0 hA hdensity)
  refine ⟨X, D, v, xi, hXcard, hX, hDradius, hDpos, ?_, ?_, hvlow,
    hvhigh, hxiFormula, hxipos, hxiv, hDregular, hDsub, hinc⟩
  · simpa only [CyclicBohr.Set.rank_dilate] using hHrankD
  · simpa only [CyclicBohr.Set.rank_dilate] using hDrank

end CyclicImprovedLocalDensityIteration

end Erdos721
