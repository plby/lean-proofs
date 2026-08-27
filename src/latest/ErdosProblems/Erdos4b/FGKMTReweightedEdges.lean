/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTIndependentEdgeIntersection

/-! # The genuine reweighted edge distribution with an empty fallback -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

def survivalProduct (P : α → ℝ) (A : Finset α) : ℝ := ∏ v ∈ A, P v

omit [DecidableEq α] in
theorem survivalProduct_pos {P : α → ℝ} {A : Finset α} (hP : ∀ v ∈ A, 0 < P v) :
    0 < survivalProduct P A := Finset.prod_pos hP

def rawReweightMass (F : FiniteEdgeFamily I Ω α) (P : α → ℝ) (W : Finset α)
    (i : I) (w : Ω) : ℝ :=
  if F.edge i w ⊆ W then F.mass i w / survivalProduct P (F.edge i w) else 0

def reweightNormalizer (F : FiniteEdgeFamily I Ω α) (P : α → ℝ) (W : Finset α) (i : I) : ℝ :=
  ∑ w, F.rawReweightMass P W i w

def reweightedMass (F : FiniteEdgeFamily I Ω α) (P : α → ℝ) (W : Finset α) (τ : ℝ)
    (i : I) : Option Ω → ℝ
  | none => if |F.reweightNormalizer P W i - 1| ≤ τ then 0 else 1
  | some w => if |F.reweightNormalizer P W i - 1| ≤ τ then
      F.rawReweightMass P W i w / F.reweightNormalizer P W i else 0

def optionalEdge (F : FiniteEdgeFamily I Ω α) (i : I) : Option Ω → Finset α
  | none => ∅
  | some w => F.edge i w

theorem rawReweightMass_nonneg (F : FiniteEdgeFamily I Ω α) {P : α → ℝ}
    (hP : ∀ v ∈ F.vertices, 0 < P v) (W : Finset α) (i : I) (w : Ω) :
    0 ≤ F.rawReweightMass P W i w := by
  have hprod := survivalProduct_pos (fun v hv => hP v (F.edge_subset i w hv))
  unfold rawReweightMass
  split_ifs
  · exact div_nonneg (F.mass_nonneg i w) hprod.le
  · exact le_rfl

theorem reweightNormalizer_pos_of_good (F : FiniteEdgeFamily I Ω α)
    (P : α → ℝ) (W : Finset α) {τ : ℝ} (hτ : τ < 1) (i : I)
    (hgood : |F.reweightNormalizer P W i - 1| ≤ τ) :
    0 < F.reweightNormalizer P W i := by linarith [(abs_le.mp hgood).1]

theorem reweightedMass_nonneg (F : FiniteEdgeFamily I Ω α) {P : α → ℝ}
    (hP : ∀ v ∈ F.vertices, 0 < P v) (W : Finset α) {τ : ℝ} (hτ : τ < 1)
    (i : I) (o : Option Ω) : 0 ≤ F.reweightedMass P W τ i o := by
  by_cases hgood : |F.reweightNormalizer P W i - 1| ≤ τ
  · cases o with
    | none => simp only [reweightedMass, if_pos hgood, le_refl]
    | some w =>
      simp only [reweightedMass, if_pos hgood]
      exact div_nonneg (F.rawReweightMass_nonneg hP W i w)
        (F.reweightNormalizer_pos_of_good P W hτ i hgood).le
  · cases o <;> simp only [reweightedMass, if_neg hgood] <;> norm_num

theorem reweightedMass_sum_one (F : FiniteEdgeFamily I Ω α)
    (P : α → ℝ) (W : Finset α) {τ : ℝ} (hτ : τ < 1) (i : I) :
    (∑ o : Option Ω, F.reweightedMass P W τ i o) = 1 := by
  by_cases hgood : |F.reweightNormalizer P W i - 1| ≤ τ
  · have hpos := F.reweightNormalizer_pos_of_good P W hτ i hgood
    rw [Fintype.sum_option]
    simp only [reweightedMass, if_pos hgood, zero_add, ← Finset.sum_div]
    exact div_self hpos.ne'
  · simp [reweightedMass, hgood, Fintype.sum_option]

def reweightedFamily (F : FiniteEdgeFamily I Ω α) (P : α → ℝ) (W : Finset α) (τ : ℝ)
    (hP : ∀ v ∈ F.vertices, 0 < P v) (hτ : τ < 1) : FiniteEdgeFamily I (Option Ω) α where
  vertices := F.vertices
  rank := F.rank
  edge := F.optionalEdge
  mass := F.reweightedMass P W τ
  mass_nonneg := F.reweightedMass_nonneg hP W hτ
  mass_sum_one := F.reweightedMass_sum_one P W hτ
  edge_subset := by
    intro i o
    cases o with
    | none => exact Finset.empty_subset _
    | some w => exact F.edge_subset i w
  edge_card_le := by
    intro i o
    cases o with
    | none => simp only [optionalEdge, Finset.card_empty, Nat.zero_le]
    | some w => exact F.edge_card_le i w

theorem reweightedMass_some_pos_imp (F : FiniteEdgeFamily I Ω α) {P : α → ℝ}
    (hP : ∀ v ∈ F.vertices, 0 < P v) (W : Finset α) {τ : ℝ} (hτ : τ < 1)
    (i : I) (w : Ω) (hpos : 0 < F.reweightedMass P W τ i (some w)) :
    F.edge i w ⊆ W ∧ 0 < F.mass i w := by
  by_cases hgood : |F.reweightNormalizer P W i - 1| ≤ τ
  · have hX := F.reweightNormalizer_pos_of_good P W hτ i hgood
    have hraw : 0 < F.rawReweightMass P W i w := by
      apply (div_pos_iff_of_pos_right hX).mp
      simpa only [reweightedMass, if_pos hgood] using hpos
    by_cases hsub : F.edge i w ⊆ W
    · refine ⟨hsub, ?_⟩
      have hprod := survivalProduct_pos (fun v hv => hP v (F.edge_subset i w hv))
      apply (div_pos_iff_of_pos_right hprod).mp
      simpa only [rawReweightMass, if_pos hsub] using hraw
    · simp only [rawReweightMass, if_neg hsub, lt_self_iff_false] at hraw
  · simp only [reweightedMass, if_neg hgood, lt_self_iff_false] at hpos

theorem reweightedMass_pos_support (F : FiniteEdgeFamily I Ω α) {P : α → ℝ}
    (hP : ∀ v ∈ F.vertices, 0 < P v) (W : Finset α) {τ : ℝ} (hτ : τ < 1)
    (i : I) (o : Option Ω) (hpos : 0 < F.reweightedMass P W τ i o) :
    F.optionalEdge i o = ∅ ∨
      ∃ w, 0 < F.mass i w ∧ F.optionalEdge i o = F.edge i w ∧ F.edge i w ⊆ W := by
  cases o with
  | none => exact Or.inl rfl
  | some w =>
    have h := F.reweightedMass_some_pos_imp hP W hτ i w hpos
    exact Or.inr ⟨w, h.2, rfl, h.1⟩

end

end Erdos4b.FGKMT.FiniteEdgeFamily
