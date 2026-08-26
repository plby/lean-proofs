import ErdosProblems.Erdos1148.UniformOrdinaryRefinement
import ErdosProblems.Erdos1148.EntryNeighborhoodAlgebra
import ErdosProblems.Erdos1148.SpecialLinearHaar

/-! # Lower Haar volume of forward Bowen tubes from finite covers -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure
open scoped MatrixGroups ENNReal

def forwardHaarTube (η S : ℝ) : Set SL(2, ℝ) :=
  {g | EntryForwardBowenTube η (η * Real.exp (-S)) g}

lemma liftForwardClose_subset_haarTube {η S : ℝ} (hS : 0 ≤ S)
    {E : Set SL(2, ℝ)} (hE : LiftForwardClose η S E) {g : SL(2, ℝ)} (hg : g ∈ E) :
    E ⊆ (fun h : SL(2, ℝ) => g⁻¹ * h) ⁻¹' forwardHaarTube η S := by
  intro h hh
  apply (entryForwardBowenTube_iff_flow_closeness hS (g⁻¹ * h)).mpr
  intro t ht
  have heq : diagonalFlow (-t) * (g⁻¹ * h) * diagonalFlow t =
      (g * diagonalFlow t)⁻¹ * (h * diagonalFlow t) := by
    rw [mul_inv_rev, diagonalFlow_neg]
    group
  rw [heq]
  exact hE g hg h hh t ht

lemma liftForwardClose_haar_mass_le {η S : ℝ} (hS : 0 ≤ S)
    {E : Set SL(2, ℝ)} (hE : LiftForwardClose η S E) :
    (Measure.haar (G := SL(2, ℝ))) E ≤
      (Measure.haar (G := SL(2, ℝ))) (forwardHaarTube η S) := by
  by_cases hne : E.Nonempty
  · obtain ⟨g, hg⟩ := hne
    exact (measure_mono (liftForwardClose_subset_haarTube hS hE hg)).trans_eq
      (measure_preimage_mul _ g⁻¹ _)
  · simp [Set.not_nonempty_iff_eq_empty.mp hne]

lemma exists_open_liftForwardClose_zero {η : ℝ} (hη : 0 < η) :
    ∃ E : Set SL(2, ℝ), IsOpen E ∧ (1 : SL(2, ℝ)) ∈ E ∧ LiftForwardClose η 0 E := by
  let δ := min (η / 8) (1 / 2 : ℝ)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδη : δ ≤ η / 8 := min_le_left _ _
  have hδone : δ ≤ 1 / 2 := min_le_right _ _
  let E : Set SL(2, ℝ) := {g | ∀ i j : Fin 2,
    |g i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| < δ}
  have hopen : IsOpen E := by
    simp only [E, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt ((continuous_realMatrixEntry i j).sub continuous_const).abs continuous_const
  refine ⟨E, hopen, ?_, ?_⟩
  · intro i j
    simpa only [Matrix.SpecialLinearGroup.coe_one, sub_self, abs_zero] using hδ
  · intro g hg h hh t ht
    have htzero : t = 0 := le_antisymm ht.2 ht.1
    subst t
    simp only [diagonalFlow_zero, mul_one]
    have hg' := (entryCloseOne_iff_entries δ g).mpr (fun i j => (hg i j).le)
    have hh' := (entryCloseOne_iff_entries δ h).mpr (fun i j => (hh i j).le)
    have hp := entryCloseOne_mul hδ.le hδ.le (entryCloseOne_inv hg') hh'
    apply entryCloseOne_mono hp
    have := mul_nonneg hδ.le (sub_nonneg.mpr hδone)
    nlinarith

theorem forwardHaarTube_mass_lower {η : ℝ} (hηpos : 0 < η) (hη : η ≤ 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ S : ℝ, 0 ≤ S →
      ENNReal.ofReal (c * Real.exp (-S)) ≤
        (Measure.haar (G := SL(2, ℝ))) (forwardHaarTube η S) := by
  obtain ⟨E, hopen, hmem, hclose⟩ := exists_open_liftForwardClose_zero hηpos
  have hpos := IsOpen.measure_pos (Measure.haar (G := SL(2, ℝ))) hopen ⟨1, hmem⟩
  obtain ⟨r, hrpos, hrE⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hpos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hrpos
  refine ⟨(r : ℝ) / 33 ^ 3, by positivity, ?_⟩
  intro S hS
  obtain ⟨N, B, hN, hcov, hB⟩ := exists_uniform_ordinary_lift_refinement
    hηpos hη (le_refl 0) hS E hclose
  have hB' : ∀ i, LiftForwardClose η S (B i) := by simpa only [zero_add] using hB
  have hN' : (N : ℝ≥0∞) ≤ ENNReal.ofReal (33 ^ 3 * Real.exp S) := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hN
  have hmass : (r : ℝ≥0∞) ≤ ENNReal.ofReal (33 ^ 3 * Real.exp S) *
      (Measure.haar (G := SL(2, ℝ))) (forwardHaarTube η S) := by
    calc
      (r : ℝ≥0∞) ≤ (Measure.haar (G := SL(2, ℝ))) E := hrE.le
      _ ≤ ∑' i : Fin N, (Measure.haar (G := SL(2, ℝ))) (B i) := by
        rw [← hcov]
        exact measure_iUnion_le _
      _ ≤ (N : ℝ≥0∞) * (Measure.haar (G := SL(2, ℝ))) (forwardHaarTube η S) := by
        simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul] using ENNReal.tsum_le_tsum (fun i => liftForwardClose_haar_mass_le hS (hB' i))
      _ ≤ _ := mul_le_mul_left hN' _
  have hcancel : (Real.exp (-S) / 33 ^ 3) * (33 ^ 3 * Real.exp S) = 1 := by
    calc
      _ = Real.exp (-S) * Real.exp S := by ring
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    ENNReal.ofReal ((r : ℝ) / 33 ^ 3 * Real.exp (-S)) =
        ENNReal.ofReal (Real.exp (-S) / 33 ^ 3) * (r : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (Real.exp (-S) / 33 ^ 3) *
        (ENNReal.ofReal (33 ^ 3 * Real.exp S) *
          (Measure.haar (G := SL(2, ℝ))) (forwardHaarTube η S)) := mul_le_mul_right hmass _
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hcancel, ENNReal.ofReal_one, one_mul]

end Erdos1148.DukeArithmetic
