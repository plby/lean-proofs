import ErdosProblems.Erdos633.VRegions

/-!
# The three triangular pieces in the normalized V construction

The region descriptions are identified with actual convex hulls of their
vertices. These identities are the geometric input for transporting the
construction to the exceptional family.
-/

namespace Erdos633

noncomputable def vQ (b : ℝ) : ℂ := ⟨b ^ 2 / (1 + b), b / (1 + b)⟩
noncomputable def vE (b : ℝ) : ℂ := ⟨1 / (1 + b), b / (1 + b)⟩

theorem vQ_re_eq (b : ℝ) : (vQ b).re = b * (vQ b).im := by
  dsimp [vQ]
  ring

theorem vQ_sum (b : ℝ) (hb : 0 < b) : (vQ b).re + (vQ b).im = b := by
  have hd : 1 + b ≠ 0 := by linarith
  dsimp [vQ]
  field_simp
  ring

theorem vQ_slanted (b : ℝ) (hb : 0 < b) : (vQ b).re + b ^ 2 * (vQ b).im = b ^ 2 := by
  have hd : 1 + b ≠ 0 := by linarith
  dsimp [vQ]
  field_simp

theorem vE_sum (b : ℝ) (hb : 0 < b) : (vE b).re + (vE b).im = 1 := by
  have hd : 1 + b ≠ 0 := by linarith
  dsimp [vE]
  field_simp

theorem vE_slanted (b : ℝ) (hb : 0 < b) :
    (vE b).re + b ^ 2 * (vE b).im = 1 - b + b ^ 2 := by
  have hd : 1 + b ≠ 0 := by linarith
  dsimp [vE]
  field_simp
  ring

noncomputable def vLowerTriangle (b : ℝ) (hb : 0 < b) : Triangle where
  a := 0
  b := (b : ℂ)
  c := vQ b
  nondegenerate := by
    have heq : orientedDoubleArea 0 (b : ℂ) (vQ b) = b ^ 2 / (1 + b) := by
      simp [orientedDoubleArea, vQ]
      ring
    change orientedDoubleArea 0 (b : ℂ) (vQ b) ≠ 0
    rw [heq]
    exact div_ne_zero (pow_ne_zero 2 (ne_of_gt hb)) (by linarith)

noncomputable def vLeftTriangle (b : ℝ) (hb : 0 < b) : Triangle where
  a := 0
  b := vQ b
  c := Complex.I
  nondegenerate := by
    change orientedDoubleArea 0 (vQ b) Complex.I ≠ 0
    simpa [orientedDoubleArea, vQ] using
      div_ne_zero (pow_ne_zero 2 (ne_of_gt hb)) (show 1 + b ≠ 0 by linarith)

noncomputable def vUpperTriangle (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) : Triangle where
  a := Complex.I
  b := vQ b
  c := vE b
  nondegenerate := by
    have hd : 1 + b ≠ 0 := by linarith
    have heq : orientedDoubleArea Complex.I (vQ b) (vE b) = (1 - b) / (1 + b) := by
      simp [orientedDoubleArea, vQ, vE]
      field_simp
      ring
    change orientedDoubleArea Complex.I (vQ b) (vE b) ≠ 0
    rw [heq]
    exact div_ne_zero (by linarith) hd

theorem mem_convexHull_three_of_weights (a b c z : ℂ) (r s t : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (hw : r + s + t = 1)
    (hz : r • a + s • b + t • c = z) : z ∈ convexHull ℝ {a, b, c} := by
  apply mem_convexHull_of_exists_fintype (![r, s, t] : Fin 3 → ℝ) (![a, b, c] : Fin 3 → ℂ)
  · intro i
    fin_cases i <;> assumption
  · simpa [Fin.sum_univ_succ, add_assoc] using hw
  · intro i
    fin_cases i <;> simp
  · simpa [Fin.sum_univ_succ, add_assoc] using hz

theorem vLowerTriangle_carrier (b : ℝ) (hb : 0 < b) :
    (vLowerTriangle b hb).carrier = vLowerRegion b := by
  have hd : 0 < 1 + b := by linarith
  have hbne := ne_of_gt hb
  have hdne := ne_of_gt hd
  have hzero : (0 : ℂ) ∈ vLowerRegion b := by
    change 0 ≤ 0 ∧ 0 ≤ 0 - b * 0 ∧ 0 + 0 ≤ b
    exact ⟨le_rfl, by ring_nf; rfl, by linarith⟩
  have hbase : (b : ℂ) ∈ vLowerRegion b := by
    change 0 ≤ 0 ∧ 0 ≤ b - b * 0 ∧ b + 0 ≤ b
    simp [hb.le]
  have hQ : vQ b ∈ vLowerRegion b := by
    exact ⟨div_nonneg hb.le hd.le, by rw [vQ_re_eq]; simp, (vQ_sum b hb).le⟩
  apply Set.Subset.antisymm
  · apply convexHull_min _ (vLowerRegion_convex b)
    intro z hz
    change z ∈ ({0, (b : ℂ), vQ b} : Set ℂ) at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  · intro z hz
    apply mem_convexHull_three_of_weights 0 (b : ℂ) (vQ b) z
      ((b - z.re - z.im) / b) ((z.re - b * z.im) / b) ((1 + b) * z.im / b)
    · exact div_nonneg (by linarith [hz.2.2]) hb.le
    · exact div_nonneg hz.2.1 hb.le
    · exact div_nonneg (mul_nonneg hd.le hz.1) hb.le
    · field_simp
      ring
    · apply Complex.ext
      all_goals simp only [Complex.add_re, Complex.add_im, Complex.smul_re,
        Complex.smul_im, Complex.zero_re, Complex.zero_im, Complex.ofReal_re,
        Complex.ofReal_im, smul_eq_mul]
      all_goals dsimp [vQ]
      all_goals field_simp
      all_goals ring

theorem vLeftTriangle_carrier (b : ℝ) (hb : 0 < b) :
    (vLeftTriangle b hb).carrier = vLeftRegion b := by
  have hd : 0 < 1 + b := by linarith
  have hbne := ne_of_gt hb
  have hdne := ne_of_gt hd
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hzero : (0 : ℂ) ∈ vLeftRegion b := by
    change 0 ≤ 0 ∧ 0 - b * 0 ≤ 0 ∧ 0 + b ^ 2 * 0 ≤ b ^ 2
    simp [hb2.le]
  have htop : Complex.I ∈ vLeftRegion b := by
    change 0 ≤ 0 ∧ 0 - b * 1 ≤ 0 ∧ 0 + b ^ 2 * 1 ≤ b ^ 2
    simp [hb.le]
  have hQ : vQ b ∈ vLeftRegion b := by
    exact ⟨div_nonneg hb2.le hd.le, by rw [vQ_re_eq]; simp, (vQ_slanted b hb).le⟩
  apply Set.Subset.antisymm
  · apply convexHull_min _ (vLeftRegion_convex b)
    intro z hz
    change z ∈ ({0, vQ b, Complex.I} : Set ℂ) at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  · intro z hz
    apply mem_convexHull_three_of_weights 0 (vQ b) Complex.I z
      ((b ^ 2 - z.re - b ^ 2 * z.im) / b ^ 2) ((1 + b) * z.re / b ^ 2)
      ((b * z.im - z.re) / b)
    · exact div_nonneg (by linarith [hz.2.2]) hb2.le
    · exact div_nonneg (mul_nonneg hd.le hz.1) hb2.le
    · exact div_nonneg (by linarith [hz.2.1]) hb.le
    · field_simp
      ring
    · apply Complex.ext
      all_goals simp only [Complex.add_re, Complex.add_im, Complex.smul_re,
        Complex.smul_im, Complex.zero_re, Complex.zero_im, Complex.I_re,
        Complex.I_im, smul_eq_mul]
      all_goals dsimp [vQ]
      all_goals field_simp
      all_goals ring

theorem vUpperTriangle_carrier (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    (vUpperTriangle b hb0 hb1).carrier = vUpperRegion b := by
  have hd : 0 < 1 + b := by linarith
  have hsmall : 0 < 1 - b := by linarith
  have hdne := ne_of_gt hd
  have hsne := ne_of_gt hsmall
  have hq1 : b / (1 + b) ≤ 1 := (div_le_one hd).mpr (by linarith)
  have htop : Complex.I ∈ vUpperRegion b := by
    change b / (1 + b) ≤ 1 ∧ b ^ 2 ≤ 0 + b ^ 2 * 1 ∧ 0 + 1 ≤ 1
    simpa using hq1
  have hQ : vQ b ∈ vUpperRegion b := by
    refine ⟨le_rfl, (vQ_slanted b hb0).ge, ?_⟩
    rw [vQ_sum b hb0]
    exact hb1.le
  have hE : vE b ∈ vUpperRegion b := by
    refine ⟨le_rfl, ?_, (vE_sum b hb0).le⟩
    rw [vE_slanted b hb0]
    linarith
  apply Set.Subset.antisymm
  · apply convexHull_min _ (vUpperRegion_convex b)
    intro z hz
    change z ∈ ({Complex.I, vQ b, vE b} : Set ℂ) at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  · intro z hz
    apply mem_convexHull_three_of_weights Complex.I (vQ b) (vE b) z
      ((1 + b) * z.im - b) ((1 - z.re - z.im) / (1 - b))
      ((z.re + b ^ 2 * z.im - b ^ 2) / (1 - b))
    · have hy := (div_le_iff₀ hd).mp hz.1
      nlinarith
    · exact div_nonneg (by linarith [hz.2.2]) hsmall.le
    · exact div_nonneg (by linarith [hz.2.1]) hsmall.le
    · field_simp
      ring
    · apply Complex.ext
      all_goals simp only [Complex.add_re, Complex.add_im, Complex.smul_re,
        Complex.smul_im, Complex.I_re, Complex.I_im, smul_eq_mul]
      all_goals dsimp [vQ, vE]
      all_goals field_simp
      all_goals ring

end Erdos633
