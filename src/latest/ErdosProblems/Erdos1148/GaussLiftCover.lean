import ErdosProblems.Erdos1148.GaussLiftBoxes

/-! # Ordinary Gauss neighborhoods have compact forward covers of size exp(S) -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_gauss_lift_cover {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (g : SL(2, ℝ)) (S : ℝ), 0 ≤ S →
      ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
        (N : ℝ) ≤ K * Real.exp S ∧ (∀ i, IsCompact (B i)) ∧
        Set.range (gaussParameterFrame g) ⊆ ⋃ i, B i ∧
        ∀ i, LiftForwardClose (8 * δ) S (B i) := by
  obtain ⟨Nx, b, _, _, hxcov⟩ := exists_real_interval_grid
    (a := (-1 : ℝ)) (b := 1) (by norm_num) hδ
  obtain ⟨Nh, c₀, _, _, hhcov⟩ := exists_real_interval_grid
    (a := (1 / 2 : ℝ)) (b := 2) (by norm_num) hδ
  refine ⟨(2 / δ + 1) * ((Nx : ℝ) + 1) * ((Nh : ℝ) + 1), by positivity, ?_⟩
  intro g S hS
  obtain ⟨Nr, a, hNr₀, _, hrcov⟩ := exists_real_interval_grid
    (a := (-1 : ℝ)) (b := 1) (by norm_num) (mul_pos hδ (Real.exp_pos (-S)))
  have heq : 2 / (δ * Real.exp (-S)) = (2 / δ) * Real.exp S := by
    rw [Real.exp_neg, div_mul_eq_div_mul_one_div, one_div, inv_inv]
  have hNr : (Nr : ℝ) ≤ (2 / δ + 1) * Real.exp S := by
    have h1 : 1 ≤ Real.exp S := Real.one_le_exp_iff.mpr hS
    norm_num only [show (1 : ℝ) - -1 = 2 by norm_num] at hNr₀
    rw [heq] at hNr₀
    nlinarith
  let ι := Fin Nr × Fin Nx × Fin Nh
  let B : ι → Set SL(2, ℝ) := fun i =>
    gaussLiftBox g (a i.1) (b i.2.1) (c₀ i.2.2) (δ * Real.exp (-S)) δ δ
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => B (e.symm i), ?_, ?_, ?_, ?_⟩
  · have hprod : (Nx : ℝ) * Nh ≤ ((Nx : ℝ) + 1) * ((Nh : ℝ) + 1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) Nx, Nat.cast_nonneg (α := ℝ) Nh]
    have hbound := mul_le_mul hNr hprod
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by positivity)
    change (Fintype.card (Fin Nr × Fin Nx × Fin Nh) : ℝ) ≤ _
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    calc
      _ ≤ ((2 / δ + 1) * Real.exp S) * (((Nx : ℝ) + 1) * ((Nh : ℝ) + 1)) := hbound
      _ = _ := by ring
  · intro i
    exact isCompact_gaussLiftBox _ _ _ _ _ _ _
  · rintro x ⟨p, rfl⟩
    obtain ⟨i, hi⟩ := hrcov p.val.1 (abs_le.mp p.property.1)
    obtain ⟨j, hj⟩ := hxcov p.val.2.1 (abs_le.mp p.property.2.1)
    obtain ⟨k, hk⟩ := hhcov p.val.2.2 ⟨p.property.2.2.1, p.property.2.2.2⟩
    refine Set.mem_iUnion.mpr ⟨e (i, j, k), ?_⟩
    have he : e.symm (e (i, j, k)) = (i, j, k) := e.symm_apply_apply _
    rw [he]
    exact ⟨p, ⟨hi, hj, hk⟩, rfl⟩
  · intro i
    exact gaussLiftBox_forward_close g _ _ _ hδ.le hS

end Erdos1148.DukeArithmetic
