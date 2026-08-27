/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSurvivalProduct

/-! # Exact finite-state first and second moments of the edge normalizer -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α Ξ : Type*} [Fintype I] [Fintype Ω] [Fintype Ξ] [DecidableEq α]

def containmentMass (ρ : Ξ → ℝ) (W : Ξ → Finset α) (A : Finset α) : ℝ :=
  ∑ s, if A ⊆ W s then ρ s else 0

theorem containmentMass_nonneg {ρ : Ξ → ℝ} (hρ : ∀ s, 0 ≤ ρ s)
    (W : Ξ → Finset α) (A : Finset α) : 0 ≤ containmentMass ρ W A := by
  apply Finset.sum_nonneg
  intro s _hs
  split_ifs
  · exact hρ s
  · exact le_rfl

theorem containmentMass_le_one {ρ : Ξ → ℝ} (hρ : ∀ s, 0 ≤ ρ s)
    (hρsum : ∑ s, ρ s = 1) (W : Ξ → Finset α) (A : Finset α) :
    containmentMass ρ W A ≤ 1 := by
  rw [← hρsum]
  apply Finset.sum_le_sum
  intro s _hs
  split_ifs
  · exact le_rfl
  · exact hρ s

theorem rawReweightMass_mean (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (i : I) (w : Ω) :
    (∑ s, ρ s * F.rawReweightMass P (W s) i w) =
      F.mass i w / survivalProduct P (F.edge i w) * containmentMass ρ W (F.edge i w) := by
  rw [containmentMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases h : F.edge i w ⊆ W s
  · simp only [rawReweightMass, if_pos h, mul_comm]
  · simp only [rawReweightMass, if_neg h, mul_zero]

theorem reweightNormalizer_mean (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (i : I) :
    (∑ s, ρ s * F.reweightNormalizer P (W s) i) =
      ∑ w, F.mass i w / survivalProduct P (F.edge i w) *
        containmentMass ρ W (F.edge i w) := by
  simp only [reweightNormalizer, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun w _hw => F.rawReweightMass_mean P ρ W i w

theorem rawReweightMass_pair_mean (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (i j : I) (w z : Ω) :
    (∑ s, ρ s * (F.rawReweightMass P (W s) i w * F.rawReweightMass P (W s) j z)) =
      F.mass i w * F.mass j z /
        (survivalProduct P (F.edge i w) * survivalProduct P (F.edge j z)) *
        containmentMass ρ W (F.edge i w ∪ F.edge j z) := by
  rw [containmentMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases ha : F.edge i w ⊆ W s <;> by_cases hb : F.edge j z ⊆ W s
  · simp only [rawReweightMass, Finset.union_subset_iff,
      ha, hb, and_self, if_true]
    ring
  · simp [rawReweightMass, ha, hb, Finset.union_subset_iff]
  · simp [rawReweightMass, ha, hb, Finset.union_subset_iff]
  · simp [rawReweightMass, ha, hb, Finset.union_subset_iff]

theorem reweightNormalizer_second_moment (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (i : I) :
    (∑ s, ρ s * F.reweightNormalizer P (W s) i ^ 2) =
      ∑ w, ∑ z, F.mass i w * F.mass i z /
        (survivalProduct P (F.edge i w) * survivalProduct P (F.edge i z)) *
        containmentMass ρ W (F.edge i w ∪ F.edge i z) := by
  calc
    _ = ∑ s, ∑ w, ∑ z,
        ρ s * (F.rawReweightMass P (W s) i w * F.rawReweightMass P (W s) i z) := by
      simp only [reweightNormalizer, pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _hs
      apply Finset.sum_congr rfl
      intro w _hw
      apply Finset.sum_congr rfl
      intro z _hz
      ring
    _ = ∑ w, ∑ z, ∑ s,
        ρ s * (F.rawReweightMass P (W s) i w * F.rawReweightMass P (W s) i z) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun w _hw => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun w _hw =>
      Finset.sum_congr rfl fun z _hz => F.rawReweightMass_pair_mean P ρ W i i w z

end

end Erdos4b.FGKMT.FiniteEdgeFamily
