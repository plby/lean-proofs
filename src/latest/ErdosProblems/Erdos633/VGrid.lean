import ErdosProblems.Erdos633.VPieces

/-!
# The parallelogram grid in the V construction

The affine grid map is explicit. The equations `m * ε = 1 - b` and
`n * ε = b` ensure that its rectangle image is exactly the fourth region.
-/

namespace Erdos633

noncomputable def vGridTriangle (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε) : Triangle where
  a := 1
  b := ((1 - ε : ℝ) : ℂ)
  c := ⟨1 - ε / (1 + b), ε / (1 + b)⟩
  nondegenerate := by
    have hd : 1 + b ≠ 0 := by linarith
    have he : ε ≠ 0 := ne_of_gt hε
    change orientedDoubleArea 1 ((1 - ε : ℝ) : ℂ)
      ⟨1 - ε / (1 + b), ε / (1 + b)⟩ ≠ 0
    have heq : orientedDoubleArea 1 ((1 - ε : ℝ) : ℂ)
        ⟨1 - ε / (1 + b), ε / (1 + b)⟩ = -(ε ^ 2 / (1 + b)) := by
      simp [orientedDoubleArea]
      ring
    rw [heq]
    exact neg_ne_zero.mpr (div_ne_zero (pow_ne_zero 2 he) hd)

theorem vGridTriangle_coordinateEquiv (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε) (z : ℂ) :
    (vGridTriangle b ε hb hε).coordinateEquiv z =
      ⟨1 - ε * z.re - ε * z.im / (1 + b), ε * z.im / (1 + b)⟩ := by
  apply Complex.ext
  all_goals simp only [Triangle.coordinateEquiv_apply, vGridTriangle,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.smul_re, Complex.smul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, smul_eq_mul]
  all_goals ring

theorem vGridTriangle_image_rectangle (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε)
    (m n : ℕ) (hm : (m : ℝ) * ε = 1 - b) (hn : (n : ℝ) * ε = b) :
    (vGridTriangle b ε hb hε).coordinateEquiv '' closedRectangle m n =
      vParallelogramRegion b := by
  have hd : 0 < 1 + b := by linarith
  have hdne := ne_of_gt hd
  have hεne := ne_of_gt hε
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [vGridTriangle_coordinateEquiv]
    change 0 ≤ ε * w.im / (1 + b) ∧ ε * w.im / (1 + b) ≤ b / (1 + b) ∧
      b ≤ 1 - ε * w.re - ε * w.im / (1 + b) + ε * w.im / (1 + b) ∧
      1 - ε * w.re - ε * w.im / (1 + b) + ε * w.im / (1 + b) ≤ 1
    refine ⟨div_nonneg (mul_nonneg hε.le hw.2.2.1) hd.le, ?_, ?_, ?_⟩
    · apply div_le_div_of_nonneg_right _ hd.le
      nlinarith [mul_le_mul_of_nonneg_left hw.2.2.2 hε.le]
    · nlinarith [mul_le_mul_of_nonneg_left hw.2.1 hε.le]
    · nlinarith [mul_nonneg hε.le hw.1]
  · intro hz
    refine ⟨⟨(1 - z.re - z.im) / ε, (1 + b) * z.im / ε⟩, ?_, ?_⟩
    · change 0 ≤ (1 - z.re - z.im) / ε ∧ (1 - z.re - z.im) / ε ≤ m ∧
        0 ≤ (1 + b) * z.im / ε ∧ (1 + b) * z.im / ε ≤ n
      refine ⟨div_nonneg (by linarith [hz.2.2.2]) hε.le, ?_,
        div_nonneg (mul_nonneg hd.le hz.1) hε.le, ?_⟩
      · apply (div_le_iff₀ hε).mpr
        linarith [hz.2.2.1]
      · apply (div_le_iff₀ hε).mpr
        have hy := (le_div_iff₀ hd).mp hz.2.1
        nlinarith
    · rw [vGridTriangle_coordinateEquiv]
      apply Complex.ext <;> dsimp
      all_goals field_simp
      all_goals ring

/-- A genuine congruent grid of the normalized parallelogram region. -/
noncomputable def vParallelogram_grid (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε)
    (m n : ℕ) (hm0 : 0 < m) (hn0 : 0 < n)
    (hm : (m : ℝ) * ε = 1 - b) (hn : (n : ℝ) * ε = b) :
    RegionTiling (vParallelogramRegion b) (vGridTriangle b ε hb hε)
      ((Fin m × Fin n) × Bool) := by
  have T := parallelogramGrid (vGridTriangle b ε hb hε).coordinateEquiv m n hm0 hn0
  rw [Triangle.standard_map_coordinateEquiv] at T
  exact T.of_region_eq (vGridTriangle_image_rectangle b ε hb hε m n hm hn)

/-- The grid remains congruent after arbitrary affine transport because every
cell consists of translates or half-turns of its reference triangle. -/
noncomputable def vParallelogram_affine_grid (e : ℂ ≃ᵃ[ℝ] ℂ)
    (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε)
    (m n : ℕ) (hm0 : 0 < m) (hn0 : 0 < n)
    (hm : (m : ℝ) * ε = 1 - b) (hn : (n : ℝ) * ε = b) :
    RegionTiling (e '' vParallelogramRegion b)
      ((vGridTriangle b ε hb hε).mapAffineEquiv e) ((Fin m × Fin n) × Bool) := by
  have T := parallelogramGrid ((vGridTriangle b ε hb hε).coordinateEquiv.trans e)
    m n hm0 hn0
  rw [← Triangle.mapAffineEquiv_comp, Triangle.standard_map_coordinateEquiv] at T
  apply T.of_region_eq
  change (fun z => e ((vGridTriangle b ε hb hε).coordinateEquiv z)) ''
    closedRectangle m n = e '' vParallelogramRegion b
  rw [← Set.image_image, vGridTriangle_image_rectangle b ε hb hε m n hm hn]

end Erdos633
