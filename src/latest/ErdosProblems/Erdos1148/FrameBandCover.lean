import ErdosProblems.Erdos1148.FrameBoxes
import ErdosProblems.Erdos1148.FiniteCoverPairMass

/-! # A quantitative cover of one height band by small modular frame boxes -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory

noncomputable def modularFrameBand (H : ℝ) (hH : 0 < H) : Set ModularOrbitSpace :=
  frameBox (-(1 / 2)) H (-Real.pi) 1 H (2 * Real.pi) hH

theorem exists_frameBand_cover {H δ : ℝ} (hH : 0 < H) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (N : ℕ) (s : Fin N → Set ModularOrbitSpace),
      (N : ℝ) ≤ 2 * (2 * Real.pi + 1) * (1 / (δ ^ 3 * H ^ 2) + 1 / δ ^ 2) ∧
      (∀ i, MeasurableSet (s i)) ∧ modularFrameBand H hH ⊆ ⋃ i, s i ∧
      ∀ i, s i ×ˢ s i ⊆ modularClosePairs (5 * δ) := by
  obtain ⟨Nx, cx, hNx, hcx, hxcov⟩ := exists_real_interval_grid
    (a := -(1 / 2 : ℝ)) (b := 1 / 2) (by norm_num) (mul_pos hδ (sq_pos_of_pos hH))
  obtain ⟨Nh, ch, hNh, hch, hhcov⟩ := exists_real_interval_grid
    (a := H) (b := 2 * H) (by linarith) (mul_pos hδ hH)
  obtain ⟨Nt, ct, hNt, hct, htcov⟩ := exists_real_interval_grid
    (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos]) hδ
  let ι := Fin Nx × Fin Nh × Fin Nt
  let B : ι → Set ModularOrbitSpace := fun i =>
    frameBox (cx i.1) (ch i.2.1) (ct i.2.2) (δ * H ^ 2) (δ * H) δ (hH.trans_le (hch i.2.1))
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => B (e.symm i), ?_, ?_, ?_, ?_⟩
  · have hNx' : (Nx : ℝ) ≤ 1 / (δ * H ^ 2) + 1 := by norm_num at hNx ⊢; exact hNx
    have hNh' : (Nh : ℝ) ≤ 2 / δ := by
      have heq : (2 * H - H) / (δ * H) = 1 / δ := by field_simp; ring
      rw [heq] at hNh
      have hunit : (1 : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by simpa using hδ1)
      calc
        _ ≤ 1 / δ + 1 := hNh
        _ ≤ 1 / δ + 1 / δ := add_le_add le_rfl hunit
        _ = _ := by ring
    have hNt' : (Nt : ℝ) ≤ (2 * Real.pi + 1) / δ := by
      have heq : (Real.pi - -Real.pi) / δ + 1 = (2 * Real.pi + δ) / δ := by field_simp; ring
      apply hNt.trans
      rw [heq]
      exact div_le_div_of_nonneg_right (by linarith) hδ.le
    have hbound := mul_le_mul hNx'
      (mul_le_mul hNh' hNt' (Nat.cast_nonneg _) (by positivity))
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by positivity)
    change (Fintype.card (Fin Nx × Fin Nh × Fin Nt) : ℝ) ≤ _
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    apply hbound.trans_eq
    field_simp
  · intro i
    exact measurableSet_frameBox _ _ _ _ _ _ _
  · rintro x ⟨p, rfl⟩
    obtain ⟨i, hi⟩ := hxcov p.val.1 ⟨p.prop.1.1, by linarith [p.prop.1.2]⟩
    obtain ⟨j, hj⟩ := hhcov p.val.2.1 ⟨p.prop.2.1.1, by linarith [p.prop.2.1.2]⟩
    obtain ⟨k, hk⟩ := htcov p.val.2.2 ⟨p.prop.2.2.1, by linarith [p.prop.2.2.2]⟩
    refine Set.mem_iUnion.mpr ⟨e (i, j, k), ?_⟩
    rw [Equiv.symm_apply_apply]
    exact ⟨⟨p.val, hi, hj, hk⟩, rfl⟩
  · intro i
    exact frameBox_prod_subset_close hH (hch _) hδ.le

theorem frameBand_mass_sq_le_pair_mass (μ : Measure ModularOrbitSpace) [IsFiniteMeasure μ]
    {H δ : ℝ} (hH : 0 < H) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    μ.real (modularFrameBand H hH) ^ 2 ≤
      (2 * (2 * Real.pi + 1) * (1 / (δ ^ 3 * H ^ 2) + 1 / δ ^ 2)) *
        (μ.prod μ).real (modularClosePairs (5 * δ)) := by
  obtain ⟨N, s, hN, hs, hcover, hpair⟩ := exists_frameBand_cover hH hδ hδ1
  exact (finite_cover_mass_sq_le_pair_mass μ s hs hcover hpair).trans
    (mul_le_mul_of_nonneg_right hN measureReal_nonneg)

end Erdos1148.DukeArithmetic
