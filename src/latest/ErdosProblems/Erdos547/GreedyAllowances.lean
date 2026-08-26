import ErdosProblems.Erdos547.GreedyReverse

/-!
# Residual allowances and preservation of the anchor constraints
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ δ : ℝ}

open scoped Classical in
def tailAllowance (w : EdgeWeights G) (c : V) (l : V → ℝ) (A : Finset V) (u : V) : ℝ :=
  if u ∈ A then max 0 (w.weight c u - l u) else 0

omit [Fintype V] in
theorem tailAllowance_nonneg (w : EdgeWeights G) (c : V) (l : V → ℝ) (A : Finset V) (u : V) :
    0 ≤ tailAllowance w c l A u := by
  classical
  rw [tailAllowance]
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

omit [Fintype V] in
theorem tailAllowance_le_capacity (w : EdgeWeights G) (c : V) (l : V → ℝ)
    (hl : ∀ u, l u ≤ 1) (A : Finset V) (u : V) :
    tailAllowance w c l A u ≤ 1 - l u := by
  classical
  rw [tailAllowance]
  split_ifs
  · exact max_le (sub_nonneg.mpr (hl u)) (sub_le_sub_right (w.at_most_one c u) _)
  · exact sub_nonneg.mpr (hl u)

omit [Fintype V] in
theorem tailAllowance_le (w : EdgeWeights G) (c : V) (l : V → ℝ) (A : Finset V) (u : V) :
    tailAllowance w c l A u ≤ max 0 (w.weight c u - l u) := by
  classical
  rw [tailAllowance]
  split_ifs
  · exact le_rfl
  · exact le_max_left _ _

omit [Fintype V] in
theorem degreeOn_sub_load_le_allowance_sum (w : EdgeWeights G) (c : V) (l : V → ℝ)
    (A S : Finset V) (hSA : S ⊆ A) :
    w.degreeOn S c - (∑ u ∈ S, l u) ≤ ∑ u ∈ S, tailAllowance w c l A u := by
  classical
  rw [EdgeWeights.degreeOn, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro u hu
  rw [tailAllowance, if_pos (hSA hu)]
  exact le_max_right _ _

theorem tailAllowance_sum_ge (w : EdgeWeights G) (c : V) (l : V → ℝ)
    (A : Finset V) (κ : ℝ) (hκ : κ + (∑ u ∈ A, l u) ≤ w.degreeOn A c) :
    κ ≤ ∑ u, tailAllowance w c l A u := by
  classical
  have hh := degreeOn_sub_load_le_allowance_sum w c l A A (fun _ h ↦ h)
  have hsum : (∑ u, tailAllowance w c l A u) = ∑ u ∈ A, tailAllowance w c l A u := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro u _ hu
    exact if_neg hu
  rw [hsum]
  linarith

omit [Fintype V] in
theorem residual_capacity_sum_ge (l : V → ℝ) (hl : ∀ u, 0 ≤ l u)
    (S B : Finset V) (hSB : S ⊆ B) (r : ℝ)
    (h : r + (∑ u ∈ B, l u) ≤ (S.card : ℝ)) :
    r ≤ ∑ u ∈ S, (1 - l u) := by
  have hs : (∑ u ∈ S, l u) ≤ ∑ u ∈ B, l u :=
    Finset.sum_le_sum_of_subset_of_nonneg hSB (fun u _ _ ↦ hl u)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  linarith

theorem AnchoredPair.add_with_allowance {σ ρ : SkewMatching G γ} {τ : SkewMatching G δ}
    {w : EdgeWeights G} {c d : V} (h : AnchoredPair σ τ w c d)
    (hc : ∀ u, σ.load u + τ.load u + ρ.load u ≤ 1)
    (ha : ∀ u, ρ.outLoad u ≤ max 0 (w.weight c u - (σ.load u + τ.load u))) :
    ∃ hs : ∀ u, σ.load u + ρ.load u ≤ 1, AnchoredPair (σ.add ρ hs) τ w c d := by
  have hs (u : V) : σ.load u + ρ.load u ≤ 1 := by linarith [hc u, τ.load_nonneg u]
  refine ⟨hs, h.adjacent, ?_, ?_, h.fits_right, ?_⟩
  · intro u
    rw [SkewMatching.add_load]
    linarith [hc u]
  · intro u
    rw [SkewMatching.add_outLoad]
    apply add_le_of_le_truncated (h.fits_left u) _ (ha u)
    exact (σ.outLoad_le_load u).trans (le_add_of_nonneg_right (τ.load_nonneg u))
  · intro u
    rw [SkewMatching.add_outLoad]
    have hold : σ.outLoad u + τ.outLoad u ≤ σ.load u + τ.load u :=
      add_le_add (σ.outLoad_le_load u) (τ.outLoad_le_load u)
    have hnew : ρ.outLoad u ≤ max 0
        (max (w.weight c u) (w.weight d u) - (σ.load u + τ.load u)) :=
      (ha u).trans (max_le_max_left _ (sub_le_sub_right (le_max_left _ _) _))
    have hh := add_le_of_le_truncated (h.joint u) hold hnew
    linarith

end Erdos547.DPRS

#print axioms Erdos547.DPRS.AnchoredPair.add_with_allowance
