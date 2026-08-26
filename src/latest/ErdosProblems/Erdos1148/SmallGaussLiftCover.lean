import ErdosProblems.Erdos1148.GaussParameterGridCover

/-! # A radius-independent forward cover for a small Gauss neighborhood -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

def smallGaussParameters (η : ℝ) : Set BoundedGaussParameters :=
  {p | |p.val.1| ≤ 2 * η ∧ |p.val.2.1| ≤ 2 * η ∧ |p.val.2.2 - 1| ≤ η}

theorem exists_small_gauss_lift_cover {η : ℝ} (hη : 0 < η) (g : SL(2, ℝ))
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
      (N : ℝ) ≤ 33 ^ 3 * Real.exp T ∧ (∀ i, IsCompact (B i)) ∧
      gaussParameterFrame g '' smallGaussParameters η ⊆ ⋃ i, B i ∧
      ∀ i, LiftForwardClose η T (B i) := by
  let δ := η / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hwidth : 0 < δ * Real.exp (-T) := mul_pos hδ (Real.exp_pos _)
  obtain ⟨Nr, a, hNr, _, hrcov⟩ := exists_real_interval_grid
    (a := -(2 * η)) (b := 2 * η) (by linarith) hwidth
  obtain ⟨Nx, b, hNx, _, hxcov⟩ := exists_real_interval_grid
    (a := -(2 * η)) (b := 2 * η) (by linarith) hδ
  obtain ⟨Nh, c, hNh, _, hhcov⟩ := exists_real_interval_grid
    (a := 1 - η) (b := 1 + η) (by linarith) hδ
  have hexp : 1 ≤ Real.exp T := Real.one_le_exp_iff.mpr hT
  have hratio : (2 * η - -(2 * η)) / (δ * Real.exp (-T)) = 32 * Real.exp T := by
    dsimp only [δ]
    rw [Real.exp_neg]
    field_simp [hη.ne', Real.exp_ne_zero]
    <;> ring
  have hNr' : (Nr : ℝ) ≤ 33 * Real.exp T := by
    rw [hratio] at hNr
    linarith
  have hNx' : (Nx : ℝ) ≤ 33 := by
    have heq : (2 * η - -(2 * η)) / δ + 1 = 33 := by
      dsimp only [δ]
      field_simp [hη.ne']
      <;> ring
    exact hNx.trans_eq heq
  have hNh' : (Nh : ℝ) ≤ 33 := by
    have heq : (1 + η - (1 - η)) / δ + 1 = 17 := by
      dsimp only [δ]
      field_simp [hη.ne']
      <;> ring
    linarith [hNh.trans_eq heq]
  obtain ⟨N, B, hN, hBcompact, hcover, hclose⟩ :=
    exists_gauss_lift_cover_of_parameter_grids hδ.le hT g (smallGaussParameters η) a b c
      (fun p hp => hrcov _ (abs_le.mp hp.1))
      (fun p hp => hxcov _ (abs_le.mp hp.2.1))
      (fun p hp => hhcov _ (by
        have hh := abs_le.mp hp.2.2
        constructor <;> linarith))
  refine ⟨N, B, ?_, hBcompact, hcover, ?_⟩
  · rw [hN, Nat.cast_mul, Nat.cast_mul]
    have hprod := mul_le_mul (mul_le_mul hNr' hNx' (Nat.cast_nonneg _) (by positivity))
      hNh' (Nat.cast_nonneg _) (by positivity)
    nlinarith
  · have hscale : 8 * δ = η := by dsimp [δ]; ring
    simpa only [hscale] using hclose

end Erdos1148.DukeArithmetic
