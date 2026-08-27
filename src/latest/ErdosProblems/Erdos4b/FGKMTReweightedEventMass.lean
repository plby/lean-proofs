/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTNormalizerConcentration
import ErdosProblems.Erdos4b.FGKMTProbabilityNormalizationAlgebra

/-! # Raw and reweighted masses of arbitrary finite outcome events -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

def rawEventMass (F : FiniteEdgeFamily I Ω α) (P : α → ℝ) (W : Finset α)
    (i : I) (T : Finset Ω) : ℝ := ∑ w ∈ T, F.rawReweightMass P W i w

def reweightedEventMass (F : FiniteEdgeFamily I Ω α) (P : α → ℝ) (W : Finset α)
    (τ : ℝ) (i : I) (T : Finset Ω) : ℝ := ∑ w ∈ T, F.reweightedMass P W τ i (some w)

theorem rawEventMass_nonneg (F : FiniteEdgeFamily I Ω α) {P : α → ℝ}
    (hP : ∀ v ∈ F.vertices, 0 < P v) (W : Finset α) (i : I) (T : Finset Ω) :
    0 ≤ F.rawEventMass P W i T :=
  Finset.sum_nonneg fun w _hw => F.rawReweightMass_nonneg hP W i w

theorem reweightedEventMass_nonneg (F : FiniteEdgeFamily I Ω α) {P : α → ℝ}
    (hP : ∀ v ∈ F.vertices, 0 < P v) (W : Finset α) {τ : ℝ} (hτ : τ < 1)
    (i : I) (T : Finset Ω) : 0 ≤ F.reweightedEventMass P W τ i T :=
  Finset.sum_nonneg fun w _hw => F.reweightedMass_nonneg hP W hτ i (some w)

theorem reweightedEventMass_eq (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (W : Finset α) (τ : ℝ) (i : I) (T : Finset Ω) :
    F.reweightedEventMass P W τ i T =
      if |F.reweightNormalizer P W i - 1| ≤ τ
      then F.rawEventMass P W i T / F.reweightNormalizer P W i else 0 := by
  by_cases hgood : |F.reweightNormalizer P W i - 1| ≤ τ
  · simp only [reweightedEventMass, reweightedMass, if_pos hgood, ← Finset.sum_div, rawEventMass]
  · simp only [reweightedEventMass, reweightedMass, if_neg hgood, Finset.sum_const_zero]

theorem rawReweightMass_le (F : FiniteEdgeFamily I Ω α) {P : α → ℝ} {κ : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hP : ∀ v ∈ F.vertices, κ ≤ P v)
    (W : Finset α) (i : I) (w : Ω) :
    F.rawReweightMass P W i w ≤ (1 / κ ^ F.rank) * F.mass i w := by
  have hprod := survivalProduct_ge_pow hκ0.le hκ1
    (fun v hv => hP v (F.edge_subset i w hv)) (F.edge_card_le i w)
  by_cases hsub : F.edge i w ⊆ W
  · rw [rawReweightMass, if_pos hsub]
    have hdiv := div_le_div_of_nonneg_left (F.mass_nonneg i w) (pow_pos hκ0 F.rank) hprod
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm] using hdiv
  · rw [rawReweightMass, if_neg hsub]
    exact mul_nonneg (one_div_nonneg.mpr (pow_pos hκ0 F.rank).le) (F.mass_nonneg i w)

theorem rawEventMass_le (F : FiniteEdgeFamily I Ω α) {P : α → ℝ} {κ : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hP : ∀ v ∈ F.vertices, κ ≤ P v)
    (W : Finset α) (i : I) (T : Finset Ω) :
    F.rawEventMass P W i T ≤ (1 / κ ^ F.rank) * ∑ w ∈ T, F.mass i w := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun w _hw => F.rawReweightMass_le hκ0 hκ1 hP W i w

theorem reweightedEventMass_good_error (F : FiniteEdgeFamily I Ω α) {P : α → ℝ}
    (hP : ∀ v ∈ F.vertices, 0 < P v) (W : Finset α) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) (i : I) (T : Finset Ω)
    (hgood : |F.reweightNormalizer P W i - 1| ≤ τ) :
    |F.reweightedEventMass P W τ i T - F.rawEventMass P W i T| ≤
      2 * τ * F.rawEventMass P W i T := by
  rw [F.reweightedEventMass_eq, if_pos hgood]
  have h := normalized_atom_error (F.rawEventMass_nonneg hP W i T)
    (T := 1) (by norm_num) hτ0 hτ (by simpa only [mul_one] using hgood)
  simpa only [div_one] using h

theorem reweightedEventMass_le (F : FiniteEdgeFamily I Ω α) {P : α → ℝ} {κ τ : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hP : ∀ v ∈ F.vertices, κ ≤ P v)
    (W : Finset α) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) (i : I) (T : Finset Ω) :
    F.reweightedEventMass P W τ i T ≤
      2 * (1 / κ ^ F.rank) * ∑ w ∈ T, F.mass i w := by
  have hraw := F.rawEventMass_nonneg (fun v hv => hκ0.trans_le (hP v hv)) W i T
  have hbound := F.rawEventMass_le hκ0 hκ1 hP W i T
  by_cases hgood : |F.reweightNormalizer P W i - 1| ≤ τ
  · have herror := (abs_le.mp (F.reweightedEventMass_good_error
      (fun v hv => hκ0.trans_le (hP v hv)) W hτ0 hτ i T hgood)).2
    have hhalf := mul_le_mul_of_nonneg_right hτ hraw
    nlinarith
  · rw [F.reweightedEventMass_eq, if_neg hgood]
    exact mul_nonneg (mul_nonneg (by norm_num) (by positivity))
      (Finset.sum_nonneg fun w _hw => F.mass_nonneg i w)

theorem reweightedEventMass_error (F : FiniteEdgeFamily I Ω α) {P : α → ℝ} {κ τ : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hP : ∀ v ∈ F.vertices, κ ≤ P v)
    (W : Finset α) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) (i : I) (T : Finset Ω) :
    |F.reweightedEventMass P W τ i T - F.rawEventMass P W i T| ≤
      ((if |F.reweightNormalizer P W i - 1| ≤ τ then 0 else 1) + 2 * τ) *
        ((1 / κ ^ F.rank) * ∑ w ∈ T, F.mass i w) := by
  have hraw := F.rawEventMass_nonneg (fun v hv => hκ0.trans_le (hP v hv)) W i T
  have hbound := F.rawEventMass_le hκ0 hκ1 hP W i T
  by_cases hgood : |F.reweightNormalizer P W i - 1| ≤ τ
  · rw [if_pos hgood, zero_add]
    exact (F.reweightedEventMass_good_error
      (fun v hv => hκ0.trans_le (hP v hv)) W hτ0 hτ i T hgood).trans
      (mul_le_mul_of_nonneg_left hbound (by positivity))
  · rw [if_neg hgood, F.reweightedEventMass_eq, if_neg hgood,
      zero_sub, abs_neg, abs_of_nonneg hraw]
    have hB : 0 ≤ (1 / κ ^ F.rank) * ∑ w ∈ T, F.mass i w := hraw.trans hbound
    nlinarith [mul_nonneg hτ0 hB]

theorem reweightedFamily_vertexMass_eq_event (F : FiniteEdgeFamily I Ω α)
    (P : α → ℝ) (W : Finset α) (τ : ℝ) (hP : ∀ v ∈ F.vertices, 0 < P v)
    (hτ : τ < 1) (i : I) (v : α) :
    (F.reweightedFamily P W τ hP hτ).vertexMass i v =
      F.reweightedEventMass P W τ i (Finset.univ.filter fun w => v ∈ F.edge i w) := by
  rw [vertexMass, Fintype.sum_option]
  simp only [reweightedFamily, optionalEdge, Finset.notMem_empty, if_false, zero_add,
    reweightedEventMass, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w _hw
  by_cases hv : v ∈ F.edge i w <;> simp only [hv, if_true, if_false]

end

end Erdos4b.FGKMT.FiniteEdgeFamily
