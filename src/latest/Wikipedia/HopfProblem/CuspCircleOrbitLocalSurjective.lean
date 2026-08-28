import Wikipedia.HopfProblem.CuspCircleOrbitLocalAlgebra

/-!
# Every opposite-weight invariant occurs

The two normal radii are recovered from the invariant by real square
roots. A nonzero first coordinate gives a representative by division;
the remaining axis and the origin are handled separately. This proves
surjectivity without a classification of circle actions.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit

/-- Explicit radii and a phase representative realize every invariant. -/
theorem hopfMap_surjective : Function.Surjective hopfMap := by
  rintro ⟨β, s⟩
  let r : ℝ := Real.sqrt (Complex.normSq β + s ^ 2)
  have hr₀ : 0 ≤ r := Real.sqrt_nonneg _
  have hr₂ : r ^ 2 = Complex.normSq β + s ^ 2 :=
    Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg β) (sq_nonneg s))
  have hsabs : |s| ≤ r := by
    apply (sq_le_sq₀ (abs_nonneg s) hr₀).mp
    rw [sq_abs, hr₂]
    exact le_add_of_nonneg_left (Complex.normSq_nonneg β)
  have hsneg : -s ≤ r := (neg_le_abs s).trans hsabs
  have hplus : 0 ≤ r + s := by linarith
  by_cases hzero : r + s = 0
  · have hβ : β = 0 := Complex.normSq_eq_zero.mp (by nlinarith [hr₂])
    have hs : 0 ≤ -s := by linarith
    refine ⟨(0, (Real.sqrt (-s) : ℂ)), ?_⟩
    apply Prod.ext
    · simp [hopfMap, hβ]
    · change Complex.normSq (0 : ℂ) - Complex.normSq (Real.sqrt (-s) : ℂ) = s
      rw [Complex.normSq_zero, Complex.normSq_ofReal, Real.mul_self_sqrt hs]
      ring
  · have hpos : 0 < r + s := lt_of_le_of_ne hplus (Ne.symm hzero)
    let a : ℝ := Real.sqrt ((r + s) / 2)
    have ha₀ : 0 < a := Real.sqrt_pos.mpr (by linarith)
    have ha₂ : a ^ 2 = (r + s) / 2 := Real.sq_sqrt (by positivity)
    have ha : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha₀.ne'
    have hβ : Complex.normSq β = (r + s) * (r - s) := by nlinarith [hr₂]
    have hden : 4 * (a * a) = (r + s) * 2 := by nlinarith [ha₂]
    have hw : Complex.normSq (β / (2 * (a : ℂ))) = (r - s) / 2 := by
      calc
        _ = Complex.normSq β / (4 * (a * a)) := by
          norm_num [Complex.normSq_mul, Complex.normSq_ofReal]
        _ = (r - s) / 2 := by
          rw [hβ, hden]
          field_simp [hzero]
    refine ⟨((a : ℂ), β / (2 * (a : ℂ))), ?_⟩
    apply Prod.ext
    · change 2 * (a : ℂ) * (β / (2 * (a : ℂ))) = β
      field_simp
    · change Complex.normSq (a : ℂ) - Complex.normSq (β / (2 * (a : ℂ))) = s
      rw [hw, Complex.normSq_ofReal]
      nlinarith [ha₂]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
