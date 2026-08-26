import ErdosProblems.Erdos1148.GaussLiftBoxes

/-! # A lift cover from grids in all three Gauss parameters -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_gauss_lift_cover_of_parameter_grids {δ T : ℝ} (hδ : 0 ≤ δ) (hT : 0 ≤ T)
    (g : SL(2, ℝ)) (R : Set BoundedGaussParameters) {Nr Nx Nh : ℕ}
    (a : Fin Nr → ℝ) (b : Fin Nx → ℝ) (c : Fin Nh → ℝ)
    (hrcov : ∀ p ∈ R, ∃ i, p.val.1 ∈ Set.Icc (a i) (a i + δ * Real.exp (-T)))
    (hxcov : ∀ p ∈ R, ∃ j, p.val.2.1 ∈ Set.Icc (b j) (b j + δ))
    (hhcov : ∀ p ∈ R, ∃ k, p.val.2.2 ∈ Set.Icc (c k) (c k + δ)) :
    ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
      N = Nr * Nx * Nh ∧ (∀ i, IsCompact (B i)) ∧
      gaussParameterFrame g '' R ⊆ ⋃ i, B i ∧ ∀ i, LiftForwardClose (8 * δ) T (B i) := by
  let ι := Fin Nr × Fin Nx × Fin Nh
  let B : ι → Set SL(2, ℝ) := fun i =>
    gaussLiftBox g (a i.1) (b i.2.1) (c i.2.2) (δ * Real.exp (-T)) δ δ
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => B (e.symm i), ?_, ?_, ?_, ?_⟩
  · simp only [ι, Fintype.card_prod, Fintype.card_fin, Nat.mul_assoc]
  · intro i
    exact isCompact_gaussLiftBox _ _ _ _ _ _ _
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨i, hi⟩ := hrcov p hp
    obtain ⟨j, hj⟩ := hxcov p hp
    obtain ⟨k, hk⟩ := hhcov p hp
    refine Set.mem_iUnion.mpr ⟨e (i, j, k), ?_⟩
    have he : e.symm (e (i, j, k)) = (i, j, k) := e.symm_apply_apply _
    rw [he]
    exact ⟨p, ⟨hi, hj, hk⟩, rfl⟩
  · intro i
    exact gaussLiftBox_forward_close g _ _ _ hδ hT

end Erdos1148.DukeArithmetic
