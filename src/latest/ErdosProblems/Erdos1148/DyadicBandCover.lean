import ErdosProblems.Erdos1148.FrameBandCover

/-! # Summing quantitative frame covers over dyadic height bands -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Finset

lemma sum_inverse_dyadic_height_sq_le {H : ℝ} (hH : 0 < H) (J : ℕ) :
    (∑ j : Fin J, 1 / (((2 : ℝ) ^ j.val * H) ^ 2)) ≤ (4 / 3) / H ^ 2 := by
  have hterm (j : ℕ) : 1 / (((2 : ℝ) ^ j * H) ^ 2) = (1 / H ^ 2) * (1 / 4 : ℝ) ^ j := by
    rw [mul_pow, pow_right_comm]
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
    simp only [one_div, mul_inv_rev, inv_pow]
  simp_rw [hterm]
  rw [← mul_sum, Fin.sum_univ_eq_sum_range]
  have hgeo := geom_sum_mul_neg (1 / 4 : ℝ) J
  have hsum : (∑ j ∈ range J, (1 / 4 : ℝ) ^ j) ≤ 4 / 3 := by
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) J]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring)

theorem exists_dyadicBand_cover {H δ : ℝ} (hH : 0 < H) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (J : ℕ) :
    ∃ (N : ℕ) (s : Fin N → Set ModularOrbitSpace),
      (N : ℝ) ≤ 2 * (2 * Real.pi + 1) * ((4 / 3) / (δ ^ 3 * H ^ 2) + J / δ ^ 2) ∧
      (∀ i, MeasurableSet (s i)) ∧
      (⋃ j : Fin J, modularFrameBand ((2 : ℝ) ^ j.val * H) (by positivity)) ⊆ ⋃ i, s i ∧
      ∀ i, s i ×ˢ s i ⊆ modularClosePairs (5 * δ) := by
  classical
  have hHj (j : Fin J) : 0 < (2 : ℝ) ^ j.val * H := by positivity
  choose Nj Sj hNj hSj hcoverj hpairj using fun j : Fin J =>
    exists_frameBand_cover (hHj j) hδ hδ1
  let ι := (j : Fin J) × Fin (Nj j)
  let B : ι → Set ModularOrbitSpace := fun i => Sj i.1 i.2
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => B (e.symm i), ?_, ?_, ?_, ?_⟩
  · have hcard : (Fintype.card ι : ℝ) = ∑ j : Fin J, (Nj j : ℝ) := by
      simp only [ι, Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    rw [hcard]
    apply (sum_le_sum (fun j _ => hNj j)).trans
    have heq : (∑ j : Fin J, 2 * (2 * Real.pi + 1) *
        (1 / (δ ^ 3 * ((2 : ℝ) ^ j.val * H) ^ 2) + 1 / δ ^ 2)) =
      2 * (2 * Real.pi + 1) * ((1 / δ ^ 3) *
        (∑ j : Fin J, 1 / (((2 : ℝ) ^ j.val * H) ^ 2)) + J / δ ^ 2) := by
      simp only [mul_add, sum_add_distrib, ← mul_sum, ← div_div]
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
    rw [heq]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add _ le_rfl
    have hsum := mul_le_mul_of_nonneg_left (sum_inverse_dyadic_height_sq_le hH J)
      (by positivity : 0 ≤ 1 / δ ^ 3)
    convert hsum using 1 <;> ring
  · intro i
    exact hSj _ _
  · intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcoverj j hj)
    exact Set.mem_iUnion.mpr ⟨e ⟨j, i⟩, by simpa only [Equiv.symm_apply_apply] using hi⟩
  · intro i
    exact hpairj _ _

theorem dyadicBand_mass_sq_le_pair_mass (μ : Measure ModularOrbitSpace) [IsFiniteMeasure μ]
    {H δ : ℝ} (hH : 0 < H) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (J : ℕ) :
    μ.real (⋃ j : Fin J, modularFrameBand ((2 : ℝ) ^ j.val * H) (by positivity)) ^ 2 ≤
      (2 * (2 * Real.pi + 1) * ((4 / 3) / (δ ^ 3 * H ^ 2) + J / δ ^ 2)) *
        (μ.prod μ).real (modularClosePairs (5 * δ)) := by
  obtain ⟨N, s, hN, hs, hcover, hpair⟩ := exists_dyadicBand_cover hH hδ hδ1 J
  exact (finite_cover_mass_sq_le_pair_mass μ s hs hcover hpair).trans
    (mul_le_mul_of_nonneg_right hN measureReal_nonneg)

end Erdos1148.DukeArithmetic
