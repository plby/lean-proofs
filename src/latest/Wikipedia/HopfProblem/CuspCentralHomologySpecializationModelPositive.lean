import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelBasic

/-!
# Explicit normalized coordinates on a positive real toric fibre

Positive real torus characters are recovered from their logarithmic
positions by exponentiation. Composing these actual coordinates with the
inverse of the small-drift normalization gives a homeomorphism from the
ordinary real plane to the original positive fibre. Its inverse is the
previously constructed normalized position, not a newly chosen coordinate.

The parameter here is a positive real number. No identification of an
arbitrary complex fibre, or omission of its base phase, is asserted.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricCharts ToricSpace CuspUniformization CuspControlledRetraction CuspPositive

local notation "Plane" => CuspHoneycombTiling.Plane

@[simp] theorem modulus_torusPoint (w : CoordinateSpace 3) :
    modulus (torusPoint w) = torusPoint (coordinateModulus w) := by
  simp only [torusPoint, modulus_inclusion, monomial_coordinateModulus]

theorem torusCoordinates_modulus {x : Space} (hx : x ∈ openTorus) :
    torusCoordinates (modulus x) = coordinateModulus (torusCoordinates x) := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [modulus_inclusion,
    torusCoordinates_inclusion _ ((coordinateModulus_mem_torus_iff z).mpr hz),
    torusCoordinates_inclusion _ hz, monomial_coordinateModulus]

theorem positivePart_torusCoordinates_eq_norm (q : PositivePart)
    (ht : time (q : Space) ≠ 0) (i : Fin 3) :
    torusCoordinates (q : Space) i = (‖torusCoordinates (q : Space) i‖ : ℂ) := by
  have hx : (q : Space) ∈ openTorus := (mem_openTorus_iff _).mpr ht
  have hq : modulus (q : Space) = (q : Space) := q.2
  simpa only [hq, coordinateModulus_apply] using congrFun (torusCoordinates_modulus hx) i

theorem positivePart_torusCoordinates_norm_pos (q : PositivePart)
    (ht : time (q : Space) ≠ 0) (i : Fin 3) :
    0 < ‖torusCoordinates (q : Space) i‖ :=
  norm_pos_iff.mpr (torusCoordinates_nonzero ((mem_openTorus_iff _).mpr ht) i)

theorem positiveFibre_time_ne_zero (ρ : ℝ) (hρ : 0 < ρ) (q : PositiveFibre ρ) :
    time (q.1 : Space) ≠ 0 := by
  rw [q.2]
  exact Complex.ofReal_ne_zero.mpr hρ.ne'

/-- The original dense-torus characters with prescribed positive time and
prescribed logarithmic position. -/
def positiveLogCoordinates (ρ : ℝ) (r : Plane) : CoordinateSpace 3 :=
  ![(Real.exp (Real.log ρ * r 0) : ℂ),
    (Real.exp (Real.log ρ * r 1) : ℂ), (ρ : ℂ)]

theorem positiveLogCoordinates_mem {ρ : ℝ} (hρ : 0 < ρ) (r : Plane) :
    positiveLogCoordinates ρ r ∈ torus := by
  intro i
  fin_cases i
  · exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  · exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  · exact Complex.ofReal_ne_zero.mpr hρ.ne'

theorem torusCoordinates_positiveLogPoint {ρ : ℝ} (hρ : 0 < ρ) (r : Plane) :
    torusCoordinates (torusPoint (positiveLogCoordinates ρ r)) =
      positiveLogCoordinates ρ r :=
  torusCoordinates_torusPoint (positiveLogCoordinates_mem hρ r)

theorem time_positiveLogPoint {ρ : ℝ} (hρ : 0 < ρ) (r : Plane) :
    time (torusPoint (positiveLogCoordinates ρ r)) = (ρ : ℂ) := by
  simpa [positiveLogCoordinates] using
    congrFun (torusCoordinates_positiveLogPoint hρ r) 2

theorem position_positiveLogPoint {ρ : ℝ} (hρ : 0 < ρ)
    (hlog : Real.log ρ ≠ 0) (r : Plane) :
    position (torusPoint (positiveLogCoordinates ρ r)) = r := by
  funext i
  rw [position, logCoordinates, torusCoordinates_positiveLogPoint hρ r,
    time_positiveLogPoint hρ r, Complex.norm_of_nonneg hρ.le]
  fin_cases i
  · change Real.log ‖(Real.exp (Real.log ρ * r 0) : ℂ)‖ / Real.log ρ = r 0
    rw [Complex.norm_of_nonneg (Real.exp_nonneg _), Real.log_exp]
    exact mul_div_cancel_left₀ _ hlog
  · change Real.log ‖(Real.exp (Real.log ρ * r 1) : ℂ)‖ / Real.log ρ = r 1
    rw [Complex.norm_of_nonneg (Real.exp_nonneg _), Real.log_exp]
    exact mul_div_cancel_left₀ _ hlog

theorem positiveLogCoordinates_continuous (ρ : ℝ) :
    Continuous (positiveLogCoordinates ρ) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul (continuous_apply 0)))
  · exact Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul (continuous_apply 1)))
  · exact continuous_const

theorem positiveLogPoint_continuous {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous (fun r : Plane => torusPoint (positiveLogCoordinates ρ r)) :=
  torusChart.symm.continuousOn.comp_continuous (positiveLogCoordinates_continuous ρ)
    (fun r => positiveLogCoordinates_mem hρ r)

theorem positiveLogPoint_mem_positivePart {ρ : ℝ} (hρ : 0 < ρ) (r : Plane) :
    torusPoint (positiveLogCoordinates ρ r) ∈ positivePart := by
  change modulus (torusPoint (positiveLogCoordinates ρ r)) = _
  rw [modulus_torusPoint]
  apply congrArg torusPoint
  funext i
  fin_cases i
  · change (‖(Real.exp (Real.log ρ * r 0) : ℂ)‖ : ℂ) =
      (Real.exp (Real.log ρ * r 0) : ℂ)
    rw [Complex.norm_of_nonneg (Real.exp_nonneg _)]
  · change (‖(Real.exp (Real.log ρ * r 1) : ℂ)‖ : ℂ) =
      (Real.exp (Real.log ρ * r 1) : ℂ)
    rw [Complex.norm_of_nonneg (Real.exp_nonneg _)]
  · change (‖(ρ : ℂ)‖ : ℂ) = (ρ : ℂ)
    rw [Complex.norm_of_nonneg hρ.le]

/-- The explicit point of the actual positive fibre with a given position. -/
def positivePositionPoint (ρ : ℝ) (hρ : 0 < ρ) (r : Plane) : PositiveFibre ρ :=
  ⟨⟨torusPoint (positiveLogCoordinates ρ r), positiveLogPoint_mem_positivePart hρ r⟩,
    time_positiveLogPoint hρ r⟩

@[simp] theorem positivePositionPoint_coe (ρ : ℝ) (hρ : 0 < ρ) (r : Plane) :
    ((positivePositionPoint ρ hρ r).1 : Space) = torusPoint (positiveLogCoordinates ρ r) := rfl

@[simp] theorem position_positivePositionPoint (ρ : ℝ) (hρ : 0 < ρ)
    (hlog : Real.log ρ ≠ 0) (r : Plane) :
    position ((positivePositionPoint ρ hρ r).1 : Space) = r :=
  position_positiveLogPoint hρ hlog r

theorem positivePositionPoint_continuous (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (positivePositionPoint ρ hρ) := by
  apply Continuous.subtype_mk
  exact (positiveLogPoint_continuous hρ).subtype_mk _

/-- On the positive fibre the first two logarithmic norms and the fixed
time recover all three actual torus characters. -/
theorem position_positiveFibre_injective (ρ : ℝ) (hρ : 0 < ρ) (hlog : Real.log ρ ≠ 0) :
    Function.Injective (fun q : PositiveFibre ρ => position (q.1 : Space)) := by
  intro q r he
  have hq := positiveFibre_time_ne_zero ρ hρ q
  have hr := positiveFibre_time_ne_zero ρ hρ r
  have hcoord (i : Fin 2) :
      torusCoordinates (q.1 : Space) i.castSucc = torusCoordinates (r.1 : Space) i.castSucc := by
    have hl : Real.log ‖torusCoordinates (q.1 : Space) i.castSucc‖ =
        Real.log ‖torusCoordinates (r.1 : Space) i.castSucc‖ := by
      have hi := congrFun he i
      change Real.log ‖torusCoordinates (q.1 : Space) i.castSucc‖ / Real.log ‖time (q.1 : Space)‖ =
        Real.log ‖torusCoordinates (r.1 : Space) i.castSucc‖ / Real.log ‖time (r.1 : Space)‖ at hi
      rw [norm_time_positiveFibre ρ hρ.le q, norm_time_positiveFibre ρ hρ.le r] at hi
      have hm := congrArg (fun z : ℝ => z * Real.log ρ) hi
      simpa only [div_mul_cancel₀ _ hlog] using hm
    have hn := congrArg Real.exp hl
    rw [Real.exp_log (positivePart_torusCoordinates_norm_pos q.1 hq i.castSucc),
      Real.exp_log (positivePart_torusCoordinates_norm_pos r.1 hr i.castSucc)] at hn
    rw [positivePart_torusCoordinates_eq_norm q.1 hq i.castSucc,
      positivePart_torusCoordinates_eq_norm r.1 hr i.castSucc, hn]
  apply Subtype.ext
  apply Subtype.ext
  apply torusCoordinates_injective ((mem_openTorus_iff _).mpr hq) ((mem_openTorus_iff _).mpr hr)
  funext i
  fin_cases i
  · exact hcoord 0
  · exact hcoord 1
  · change torusCoordinates (q.1 : Space) 2 = torusCoordinates (r.1 : Space) 2
    rw [torusCoordinates_time, torusCoordinates_time, q.2, r.2]

@[simp] theorem positivePositionPoint_position (ρ : ℝ) (hρ : 0 < ρ)
    (hlog : Real.log ρ ≠ 0) (q : PositiveFibre ρ) :
    positivePositionPoint ρ hρ (position (q.1 : Space)) = q := by
  apply position_positiveFibre_injective ρ hρ hlog
  exact position_positivePositionPoint ρ hρ hlog _

theorem positiveFibre_position_continuous (ρ : ℝ) (hρ : 0 < ρ) (hlog : Real.log ρ ≠ 0) :
    Continuous (fun q : PositiveFibre ρ => position (q.1 : Space)) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  have hqlog : Real.log ‖time (q.1 : Space)‖ ≠ 0 := by
    rw [norm_time_positiveFibre ρ hρ.le q]
    exact hlog
  exact ContinuousAt.comp (f := fun r : PositiveFibre ρ => (r.1 : Space))
    (g := position) (position_continuousAt (positiveFibre_time_ne_zero ρ hρ q) hqlog)
    (positiveFibreInclusion ρ).continuous.continuousAt

/-- The positive fibre has its inherited topology, identified by the
explicit exponential coordinates and actual logarithmic position. -/
def positivePositionHomeomorph (ρ : ℝ) (hρ : 0 < ρ) (hlog : Real.log ρ ≠ 0) :
    Plane ≃ₜ PositiveFibre ρ where
  toFun := positivePositionPoint ρ hρ
  invFun q := position (q.1 : Space)
  left_inv := position_positivePositionPoint ρ hρ hlog
  right_inv := positivePositionPoint_position ρ hρ hlog
  continuous_toFun := positivePositionPoint_continuous ρ hρ
  continuous_invFun := positiveFibre_position_continuous ρ hρ hlog

theorem realCuspVector_neg_realCuspVector (y : Plane) :
    realCuspVector (-realCuspVector y) = y := by
  ext i
  fin_cases i <;> simp [realCuspVector]

theorem neg_realCuspVector_realCuspVector (y : Plane) :
    -realCuspVector (realCuspVector y) = y := by
  rw [← map_neg, realCuspVector_neg_realCuspVector]

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)

/-- Undo the actual normalization before exponentiating the torus
characters. The inverse quarter-turn is exactly `-realCuspVector`. -/
def normalizedPositivePoint (y : Plane) : PositiveFibre ρ :=
  positivePositionPoint ρ hρ
    (displacement (positiveTwist C₀) (ρ : ℂ) (-realCuspVector y))

@[simp] theorem normalizedPositivePoint_coe (y : Plane) :
    ((normalizedPositivePoint C₀ ρ hρ y).1 : Space) =
      torusPoint (positiveLogCoordinates ρ
        (displacement (positiveTwist C₀) (ρ : ℂ) (-realCuspVector y))) := rfl

theorem normalizedPositivePoint_continuous : Continuous (normalizedPositivePoint C₀ ρ hρ) :=
  (positivePositionPoint_continuous ρ hρ).comp
    ((displacement (positiveTwist C₀) (ρ : ℂ)).continuous_of_finiteDimensional.comp
      realCuspVector_continuous.neg)

theorem position_normalizedPositivePoint (hlog : Real.log ρ ≠ 0) (y : Plane) :
    position ((normalizedPositivePoint C₀ ρ hρ y).1 : Space) =
      displacement (positiveTwist C₀) (ρ : ℂ) (-realCuspVector y) :=
  position_positivePositionPoint ρ hρ hlog _

variable (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε) (hR : SmallDrift (positiveTwist C₀) ε)

include hρ hε1 hρε hR

theorem normalizedPosition_normalizedPositivePoint (y : Plane) :
    normalizedPosition C₀ ((normalizedPositivePoint C₀ ρ hρ y).1 : Space) = y := by
  have hlog : Real.log ρ < 0 := Real.log_neg hρ (hρε.trans hε1)
  have hlogC : Real.log ‖(ρ : ℂ)‖ < 0 := by
    simpa only [Complex.norm_of_nonneg hρ.le] using hlog
  rw [normalizedPosition, time_positiveFibre,
    position_normalizedPositivePoint C₀ ρ hρ hlog.ne,
    inverseDisplacement_displacement (positiveTwist C₀) hlogC
      (hR _ (by simpa only [Complex.norm_of_nonneg hρ.le] using hρ)
        (by simpa only [Complex.norm_of_nonneg hρ.le] using hρε))]
  exact realCuspVector_neg_realCuspVector y

theorem normalizedPositivePoint_normalizedPosition (q : PositiveFibre ρ) :
    normalizedPositivePoint C₀ ρ hρ (normalizedPosition C₀ (q.1 : Space)) = q := by
  have hlog : Real.log ρ < 0 := Real.log_neg hρ (hρε.trans hε1)
  have hlogC : Real.log ‖(ρ : ℂ)‖ < 0 := by
    simpa only [Complex.norm_of_nonneg hρ.le] using hlog
  apply position_positiveFibre_injective ρ hρ hlog.ne
  change position ((normalizedPositivePoint C₀ ρ hρ (normalizedPosition C₀ (q.1 : Space))).1 :
    Space) = position (q.1 : Space)
  rw [position_normalizedPositivePoint C₀ ρ hρ hlog.ne, normalizedPosition, q.2,
    neg_realCuspVector_realCuspVector]
  exact displacement_inverseDisplacement (positiveTwist C₀) hlogC
    (hR _ (by simpa only [Complex.norm_of_nonneg hρ.le] using hρ)
      (by simpa only [Complex.norm_of_nonneg hρ.le] using hρε)) _

theorem normalizedPosition_positiveFibre_continuous :
    Continuous (fun q : PositiveFibre ρ => normalizedPosition C₀ (q.1 : Space)) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  have ht : ‖time (q.1 : Space)‖ < ε := by
    rw [norm_time_positiveFibre ρ hρ.le q]
    exact hρε
  exact ContinuousAt.comp (f := fun r : PositiveFibre ρ => (r.1 : Space))
    (g := normalizedPosition C₀) (normalizedPosition_continuousAt C₀ hε1 hR
      (positiveFibre_time_ne_zero ρ hρ q) ht)
    (positiveFibreInclusion ρ).continuous.continuousAt

/-- The actual normalized positive-fibre homeomorphism. Both inverse
identities follow from the original small-drift displacement identities. -/
def normalizedPositiveHomeomorph : Plane ≃ₜ PositiveFibre ρ where
  toFun := normalizedPositivePoint C₀ ρ hρ
  invFun q := normalizedPosition C₀ (q.1 : Space)
  left_inv := normalizedPosition_normalizedPositivePoint C₀ ρ hρ ε hε1 hρε hR
  right_inv := normalizedPositivePoint_normalizedPosition C₀ ρ hρ ε hε1 hρε hR
  continuous_toFun := normalizedPositivePoint_continuous C₀ ρ hρ
  continuous_invFun := normalizedPosition_positiveFibre_continuous C₀ ρ hρ ε hε1 hρε hR

@[simp] theorem normalizedPositiveHomeomorph_apply (y : Plane) :
    normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR y = normalizedPositivePoint C₀ ρ hρ y := rfl

@[simp] theorem normalizedPositiveHomeomorph_coe (y : Plane) :
    ((normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR y).1 : Space) =
      torusPoint (positiveLogCoordinates ρ
        (displacement (positiveTwist C₀) (ρ : ℂ) (-realCuspVector y))) := rfl

@[simp] theorem normalizedPositiveHomeomorph_symm_apply (q : PositiveFibre ρ) :
    (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR).symm q =
      normalizedPosition C₀ (q.1 : Space) := rfl

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
