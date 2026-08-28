import Wikipedia.HopfProblem.CuspRetractionPolar
import Wikipedia.HopfProblem.ToricProperAction

/-!
# The positive real twist of the toric cusp action

Replacing a constant period correction by its purely imaginary part keeps
the real logarithmic drift unchanged and replaces its exponential
multipliers by their positive real moduli.  The resulting action commutes
with the genuine modulus retraction on the glued toric space, including
the boundary strata, and preserves the actual nonnegative real part.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.CuspPositive

open ToricCharts ToricFan Triangle ToricSpace

/-- The constant purely imaginary correction with the same real
logarithmic drift as the supplied constant correction. -/
def positiveTwist (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (_t : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => Complex.I * ((C₀ i j).im : ℂ)

@[simp] theorem positiveTwist_apply (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (t : ℂ) (i j : Fin 2) :
    positiveTwist C₀ t i j = Complex.I * ((C₀ i j).im : ℂ) := rfl

theorem positiveTwist_holomorphic (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    ContDiff ℂ ω (fun t => positiveTwist C₀ t i j) := contDiff_const

@[simp] theorem driftMatrix_positiveTwist (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    driftMatrix (positiveTwist C₀) t = driftMatrix (fun _ => C₀) 0 := by
  ext i j
  simp [driftMatrix, positiveTwist, Complex.mul_im]

/-- The normalization displayed in §7.7: the positive correction is
`(2πi)⁻¹` times the frozen real logarithmic drift. -/
theorem positiveTwist_eq_inverse_two_pi_I_mul_drift
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) (i j : Fin 2) :
    positiveTwist C₀ t i j = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (driftMatrix (fun _ => C₀) 0 i j : ℂ) := by
  rw [eq_inv_mul_iff_mul_eq₀ CuspUniformization.exponential_factor_ne_zero,
    positiveTwist_apply]
  change (2 * (Real.pi : ℂ) * Complex.I) * (Complex.I * ((C₀ i j).im : ℂ)) =
    ((-2 * Real.pi * (C₀ i j).im : ℝ) : ℂ)
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
  calc
    _ = (2 * (Real.pi : ℂ)) * (Complex.I * Complex.I) * ((C₀ i j).im : ℂ) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

theorem smallDrift_positiveTwist_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    SmallDrift (positiveTwist C₀) ε ↔ SmallDrift (fun _ => C₀) ε := by
  simp only [SmallDrift, driftMatrix_positiveTwist]
  rfl

theorem smallDrift_positiveTwist (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ}
    (hR : SmallDrift (fun _ => C₀) ε) : SmallDrift (positiveTwist C₀) ε :=
  (smallDrift_positiveTwist_iff C₀ ε).mpr hR

/-- Every frozen correction has a genuine positive small-drift radius;
no bound on the input matrix is assumed. -/
theorem positiveTwist_exists_smallDrift_radius (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ SmallDrift (positiveTwist C₀) ε := by
  obtain ⟨ε, hε, hε1, hR⟩ :=
    exists_smallDrift_radius (fun _ => C₀) (fun _ _ => continuousAt_const)
  exact ⟨ε, hε, hε1, smallDrift_positiveTwist C₀ hR⟩

/-- Every positive-twist multiplier is the modulus of the corresponding
multiplier of the original constant correction. -/
theorem exponentialMultiplier_positiveTwist_eq_norm
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (t : ℂ) (i : Fin 2) :
    (exponentialMultiplier (positiveTwist C₀) v t i : ℂ) =
      (‖(exponentialMultiplier (fun _ => C₀) v 0 i : ℂ)‖ : ℂ) := by
  simp only [exponentialMultiplier, Units.val_mk0, Complex.norm_exp, Complex.ofReal_exp]
  congr 1
  apply Complex.ext <;>
    simp [positiveTwist, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im]

theorem exponentialMultiplier_positiveTwist_norm
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (t : ℂ) (i : Fin 2) :
    ‖(exponentialMultiplier (positiveTwist C₀) v t i : ℂ)‖ =
      ‖(exponentialMultiplier (fun _ => C₀) v 0 i : ℂ)‖ := by
  rw [exponentialMultiplier_positiveTwist_eq_norm]
  simp

theorem exponentialMultiplier_positiveTwist_ofReal_norm
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (t : ℂ) (i : Fin 2) :
    (‖(exponentialMultiplier (positiveTwist C₀) v t i : ℂ)‖ : ℂ) =
      (exponentialMultiplier (positiveTwist C₀) v t i : ℂ) := by
  rw [exponentialMultiplier_positiveTwist_norm, exponentialMultiplier_positiveTwist_eq_norm]

theorem exponentialMultiplier_positiveTwist_im
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (t : ℂ) (i : Fin 2) :
    (exponentialMultiplier (positiveTwist C₀) v t i : ℂ).im = 0 := by
  rw [exponentialMultiplier_positiveTwist_eq_norm]
  rfl

theorem exponentialMultiplier_positiveTwist_re_pos
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (t : ℂ) (i : Fin 2) :
    0 < (exponentialMultiplier (positiveTwist C₀) v t i : ℂ).re := by
  rw [exponentialMultiplier_positiveTwist_eq_norm]
  exact norm_pos_iff.mpr (exponentialMultiplier (fun _ => C₀) v 0 i).ne_zero

theorem exponentialMultiplier_positiveTwist_const
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (t : ℂ) :
    exponentialMultiplier (positiveTwist C₀) v t =
      exponentialMultiplier (positiveTwist C₀) v 0 := rfl

theorem fibreMultiplier_positiveTwist_ofReal_norm
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (t : ℂ) (i : Fin 3) :
    (‖(fibreMultiplier (exponentialMultiplier (positiveTwist C₀) v t) i : ℂ)‖ : ℂ) =
      (fibreMultiplier (exponentialMultiplier (positiveTwist C₀) v t) i : ℂ) := by
  fin_cases i
  · exact exponentialMultiplier_positiveTwist_ofReal_norm C₀ v t 0
  · exact exponentialMultiplier_positiveTwist_ofReal_norm C₀ v t 1
  · simp [fibreMultiplier]

/-- The modulus respects every integral translation, before twisting. -/
@[simp] theorem modulus_translate (v : Fin 2 → ℤ) (x : Space) :
    modulus (translate v x) = translate v (modulus x) := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp only [translate_inclusion, modulus_inclusion]

theorem coordinateModulus_mul {d : ℕ} (z w : CoordinateSpace d) :
    coordinateModulus (z * w) = coordinateModulus z * coordinateModulus w := by
  funext i
  simp [coordinateModulus]

/-- Positive real acting-torus values give positive real monomial factors,
even when the exponent matrix has negative entries. -/
theorem coordinateModulus_factors_of_nonnegative (s : Triangle) (u : ActingTorus)
    (hu : ∀ i, (‖(u i : ℂ)‖ : ℂ) = (u i : ℂ)) :
    coordinateModulus (factors s u) = factors s u := by
  change coordinateModulus (monomial s.dual (fun i => (u i : ℂ))) = _
  rw [← monomial_coordinateModulus]
  have he : coordinateModulus (fun i => (u i : ℂ)) = fun i => (u i : ℂ) := by
    funext i
    exact hu i
  rw [he]
  rfl

theorem coordinateModulus_scale_of_nonnegative (s : Triangle) (u : ActingTorus)
    (hu : ∀ i, (‖(u i : ℂ)‖ : ℂ) = (u i : ℂ)) (z : CoordinateSpace 3) :
    coordinateModulus (scale s u z) = scale s u (coordinateModulus z) := by
  rw [scale, coordinateModulus_mul, coordinateModulus_factors_of_nonnegative s u hu]
  rfl

theorem modulus_torusAction_of_nonnegative (u : ActingTorus)
    (hu : ∀ i, (‖(u i : ℂ)‖ : ℂ) = (u i : ℂ)) (x : Space) :
    modulus (torusAction u x) = torusAction u (modulus x) := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp only [torusAction_inclusion, modulus_inclusion,
    coordinateModulus_scale_of_nonnegative s u hu]

/-- The positive correction is constant in the base parameter, so the
torus multiplier may be evaluated once at zero. -/
theorem twistedTranslate_positiveTwist_eq
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (x : Space) :
    twistedTranslate (positiveTwist C₀) v x =
      torusAction (fibreMultiplier (exponentialMultiplier (positiveTwist C₀) v 0))
        (translate (cuspVector v) x) := rfl

/-- The actual positive-twist action commutes with the global modulus
retraction, including all toric boundary strata. -/
theorem modulus_twistedTranslate_positiveTwist
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (x : Space) :
    modulus (twistedTranslate (positiveTwist C₀) v x) =
      twistedTranslate (positiveTwist C₀) v (modulus x) := by
  rw [twistedTranslate_positiveTwist_eq,
    modulus_torusAction_of_nonnegative _ (fibreMultiplier_positiveTwist_ofReal_norm C₀ v 0),
    modulus_translate, twistedTranslate_positiveTwist_eq]

theorem twistedTranslate_positiveTwist_preserves_positivePart
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) :
    MapsTo (twistedTranslate (positiveTwist C₀) v) positivePart positivePart := by
  intro x hx
  change modulus (twistedTranslate (positiveTwist C₀) v x) = _
  rw [modulus_twistedTranslate_positiveTwist]
  exact congrArg (twistedTranslate (positiveTwist C₀) v) hx

@[simp] theorem twistedTranslate_positiveTwist_mem_positivePart_iff
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (x : Space) :
    twistedTranslate (positiveTwist C₀) v x ∈ positivePart ↔ x ∈ positivePart := by
  constructor
  · intro hx
    have h := twistedTranslate_positiveTwist_preserves_positivePart C₀ (-v) hx
    simpa only [twistedTranslate_add, neg_add_cancel, twistedTranslate_zero] using h
  · intro hx
    exact twistedTranslate_positiveTwist_preserves_positivePart C₀ v hx

end Wikipedia.HopfProblem.CuspPositive
