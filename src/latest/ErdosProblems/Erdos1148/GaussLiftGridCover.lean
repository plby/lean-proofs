import ErdosProblems.Erdos1148.GaussLiftBoxes

/-! # Completing an unstable parameter grid to a compact forward lift cover -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_gauss_lift_cover_of_unstable_grid {δ S : ℝ} (hδ : 0 < δ) (hS : 0 ≤ S)
    (g : SL(2, ℝ)) (R : Set BoundedGaussParameters) {Nr : ℕ} (a : Fin Nr → ℝ)
    (hrcov : ∀ p ∈ R, ∃ i, p.val.1 ∈ Set.Icc (a i) (a i + δ * Real.exp (-S))) :
    ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
      (N : ℝ) ≤ (Nr : ℝ) * (2 / δ + 1) ^ 2 ∧ (∀ i, IsCompact (B i)) ∧
      gaussParameterFrame g '' R ⊆ ⋃ i, B i ∧ ∀ i, LiftForwardClose (8 * δ) S (B i) := by
  obtain ⟨Nx, b, hNx₀, _, hxcov⟩ := exists_real_interval_grid
    (a := (-1 : ℝ)) (b := 1) (by norm_num) hδ
  obtain ⟨Nh, c, hNh₀, _, hhcov⟩ := exists_real_interval_grid
    (a := (1 / 2 : ℝ)) (b := 2) (by norm_num) hδ
  have hNx : (Nx : ℝ) ≤ 2 / δ + 1 := by norm_num at hNx₀ ⊢; exact hNx₀
  have hNh : (Nh : ℝ) ≤ 2 / δ + 1 := by
    apply hNh₀.trans
    exact add_le_add (div_le_div_of_nonneg_right (by norm_num) hδ.le) le_rfl
  let ι := Fin Nr × Fin Nx × Fin Nh
  let B : ι → Set SL(2, ℝ) := fun i =>
    gaussLiftBox g (a i.1) (b i.2.1) (c i.2.2) (δ * Real.exp (-S)) δ δ
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => B (e.symm i), ?_, ?_, ?_, ?_⟩
  · have hprod : (Nx : ℝ) * Nh ≤ (2 / δ + 1) ^ 2 := by
      simpa only [pow_two] using mul_le_mul hNx hNh (Nat.cast_nonneg _) (by positivity)
    have hbound := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg Nr : (0 : ℝ) ≤ _)
    change (Fintype.card (Fin Nr × Fin Nx × Fin Nh) : ℝ) ≤ _
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using hbound
  · intro i
    exact isCompact_gaussLiftBox _ _ _ _ _ _ _
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨i, hi⟩ := hrcov p hp
    obtain ⟨j, hj⟩ := hxcov p.val.2.1 (abs_le.mp p.property.2.1)
    obtain ⟨k, hk⟩ := hhcov p.val.2.2 ⟨p.property.2.2.1, p.property.2.2.2⟩
    refine Set.mem_iUnion.mpr ⟨e (i, j, k), ?_⟩
    have he : e.symm (e (i, j, k)) = (i, j, k) := e.symm_apply_apply _
    rw [he]
    exact ⟨p, ⟨hi, hj, hk⟩, rfl⟩
  · intro i
    exact gaussLiftBox_forward_close g _ _ _ hδ.le hS

end Erdos1148.DukeArithmetic
