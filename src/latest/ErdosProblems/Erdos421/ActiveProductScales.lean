import ErdosProblems.Erdos421.ProductWindowSupport

/-! # Restricting the dyadic cofactor decomposition to rectangles at the relevant scale -/

namespace Erdos421

noncomputable def activeProductScales (K H : ℕ) (X : ℝ) : Finset ℕ :=
  (Finset.range K).filter (fun j ↦ X < 4 * ((2 ^ j * H : ℕ) : ℝ) ∧
    ((2 ^ j * H : ℕ) : ℝ) < 3 * X)

theorem activeProductScales_card_le (K H : ℕ) (X : ℝ) :
    (activeProductScales K H X).card ≤ K := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range K)

theorem activeProductScales_bounds {K H j : ℕ} {X : ℝ} (hj : j ∈ activeProductScales K H X) :
    j < K ∧ X / 4 < (2 ^ j * H : ℕ) ∧ (2 ^ j * H : ℕ) < 3 * X := by
  obtain ⟨hjK, hlo, hhi⟩ := Finset.mem_filter.mp hj
  exact ⟨Finset.mem_range.mp hjK, by linarith, hhi⟩

theorem activeProductScales_span {K H i j : ℕ} {X : ℝ} (hX : 0 < X)
    (hi : i ∈ activeProductScales K H X) (hj : j ∈ activeProductScales K H X) : j < i + 4 := by
  by_contra h
  have hij : i + 4 ≤ j := by omega
  have hp := Nat.mul_le_mul_right H (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hij)
  have hscale : 16 * (2 ^ i * H) ≤ 2 ^ j * H := by
    calc
      _ = 2 ^ (i + 4) * H := by rw [pow_add]; norm_num; ring
      _ ≤ _ := hp
  have hscaleR : 16 * ((2 ^ i * H : ℕ) : ℝ) ≤ ((2 ^ j * H : ℕ) : ℝ) := by
    exact_mod_cast hscale
  have hlo := (activeProductScales_bounds hi).2.1
  have hhi := (activeProductScales_bounds hj).2.2
  linarith

theorem activeProductScales_card_le_four (K H : ℕ) {X : ℝ} (hX : 0 < X) :
    (activeProductScales K H X).card ≤ 4 := by
  classical
  by_cases hs : (activeProductScales K H X).Nonempty
  · let i := (activeProductScales K H X).min' hs
    have hi : i ∈ activeProductScales K H X := Finset.min'_mem _ hs
    have hsub : activeProductScales K H X ⊆ Finset.Ico i (i + 4) := by
      intro j hj
      exact Finset.mem_Ico.mpr ⟨Finset.min'_le _ j hj, activeProductScales_span hX hi hj⟩
    have hc := Finset.card_le_card hsub
    simpa only [Nat.card_Ico, Nat.add_sub_cancel_left] using hc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.card_empty]
    exact Nat.zero_le _

theorem scaledProductWindow_active_dyadic (T : Finset ℕ) (a b : ℕ → ℂ)
    {B K H : ℕ} (hB : B < 2 ^ K) (hH : 0 < H)
    (hT : ∀ n ∈ T, H ≤ n ∧ n ≤ 2 * H) {X δ y : ℝ}
    (hX : 0 < X) (hδ : 0 < δ) (hδmax : δ ≤ Real.log (3 / 2))
    (hylo : Real.log X ≤ y) (hyhi : y ≤ Real.log (2 * X)) :
    scaledProductWindow (Finset.Icc 1 B) T a b 1 oneSidedSchwartzWindow δ y =
      ∑ j ∈ activeProductScales K H X,
        scaledProductWindow (dyadicCofactorSupport B j) T a b 1 oneSidedSchwartzWindow δ y := by
  rw [scaledProductWindow_dyadic T a b 1 oneSidedSchwartzWindow hB δ y]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j hj hjnot
  apply scaledProductWindow_eq_zero_of_inactive _ T a b
    (pow_pos (by decide : 0 < (2 : ℕ)) j) hH
    (fun m hm ↦ ⟨(dyadicCofactorSupport_bounds B j hm).1,
      (dyadicCofactorSupport_bounds B j hm).2.1⟩) hT hX hδ hδmax hylo hyhi
  have hnot : ¬ (X < 4 * ((2 ^ j * H : ℕ) : ℝ) ∧ ((2 ^ j * H : ℕ) : ℝ) < 3 * X) :=
    fun h ↦ hjnot (Finset.mem_filter.mpr ⟨hj, h⟩)
  by_cases hlo : X < 4 * ((2 ^ j * H : ℕ) : ℝ)
  · exact Or.inr (le_of_not_gt (fun hhi ↦ hnot ⟨hlo, hhi⟩))
  · exact Or.inl (le_of_not_gt hlo)

end Erdos421
