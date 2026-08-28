import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelProduct
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelVaryingProduct
import Wikipedia.HopfProblem.CuspFibreFundamentalGroup

/-!
# The original period marking of the positive-level product model

The marked phase and base coordinates represent the actual vector
`α + Z(s) β` in the original exponential uniformization, where
`s = log(ρ)/(2πi)` and `Z(s) = s B₀ + C₀`.  The equality is proved on
the original toric space before passing to its cusp quotient.  In
particular the two product factors are the integer and logarithmic
periods in that order, not just abstractly isomorphic tori.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricCharts ToricSpace CuspRetraction CuspUniformization CuspPositive
open CuspHoneycomb PeriodTorusHigherHomology

local notation "Plane" => CuspHoneycombTiling.Plane

theorem markedExponential_eq_phase_mul_modulus (z : ℂ) :
    exponential z = (Circle.exp (2 * Real.pi * z.re) : ℂ) *
      (Real.exp (-2 * Real.pi * z.im) : ℂ) := by
  simp only [exponential, Circle.coe_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im]

theorem markedExponential_real (a : ℝ) :
    exponential (a : ℂ) = (Circle.exp (2 * Real.pi * a) : ℂ) := by
  simpa using markedExponential_eq_phase_mul_modulus (a : ℂ)

/-- At a positive real level the base exponential is an ordinary
positive real power, with no omitted compact base phase. -/
theorem markedExponential_logarithm_mul (ρ : ℝ) (hρ : 0 < ρ) (b : ℝ) :
    exponential (logarithm (ρ : ℂ) * (b : ℂ)) =
      (Real.exp (Real.log ρ * b) : ℂ) := by
  unfold exponential logarithm
  rw [← mul_assoc, mul_div_cancel₀ _ exponential_factor_ne_zero,
    ← Complex.ofReal_log hρ.le, ← Complex.ofReal_mul, ← Complex.ofReal_exp]

/-- The existing logarithmic period matrix acts on real coefficients
by the same quarter-turn that marks the source deck lattice. -/
theorem logarithmicPeriod_realToComplex_apply
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ) (β : Plane) (i : Fin 2) :
    (logarithmicPeriod C s *ᵥ realToComplex β) i =
      s * (realCuspVector β i : ℂ) + (C (exponential s) *ᵥ realToComplex β) i := by
  fin_cases i <;>
    simp [logarithmicPeriod, B₀, realCuspVector, realToComplex,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, smul_eq_mul] <;> ring

theorem sourcePhaseArgument_realCuspVector (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (β : Plane) (i : Fin 2) :
    sourcePhaseArgument C₀ (realCuspVector β) i = ((C₀ *ᵥ realToComplex β) i).re := by
  rw [sourcePhaseArgument, neg_realCuspVector_realCuspVector]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, realToComplex, Complex.mul_re]

@[simp] theorem sourcePhaseCharacter_realCuspVector
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (β : Plane) (i : Fin 2) :
    sourcePhaseCharacter C₀ (realCuspVector β) i =
      Circle.exp (2 * Real.pi * ((C₀ *ᵥ realToComplex β) i).re) := by
  rw [sourcePhaseCharacter, sourcePhaseArgument_realCuspVector]

/-- The logarithmic norm of the actual normalized positive point is
the imaginary part of the original complex period vector. -/
theorem positivePeriod_logCharacter (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (hlog : Real.log ρ ≠ 0) (β : Plane) (i : Fin 2) :
    Real.log ρ * displacement (positiveTwist C₀) (ρ : ℂ) β i =
      Real.log ρ * realCuspVector β i - 2 * Real.pi * ((C₀ *ᵥ realToComplex β) i).im := by
  change Real.log ρ * (realCuspVector β i +
    (Real.log ‖(ρ : ℂ)‖)⁻¹ * (driftMatrix (positiveTwist C₀) (ρ : ℂ) *ᵥ β) i) = _
  rw [Complex.norm_of_nonneg hρ.le, mul_add, ← mul_assoc,
    mul_inv_cancel₀ hlog, one_mul, driftMatrix_positiveTwist]
  simp [driftMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    realToComplex, Complex.mul_im]
  ring

theorem frozenMarkedExponential_coordinate
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hlog : Real.log ρ ≠ 0) (a β : Plane) (i : Fin 2) :
    ((Circle.exp (2 * Real.pi * a i) *
      sourcePhaseCharacter C₀ (realCuspVector β) i : Circle) : ℂ) *
        (Real.exp (Real.log ρ * displacement (positiveTwist C₀) (ρ : ℂ) β i) : ℂ) =
      exponential ((realToComplex a +
        logarithmicPeriod (fun _ => C₀) (logarithm (ρ : ℂ)) *ᵥ realToComplex β) i) := by
  rw [Pi.add_apply, realToComplex_apply, logarithmicPeriod_realToComplex_apply,
    exponential_add, exponential_add, markedExponential_real,
    markedExponential_logarithm_mul ρ hρ,
    markedExponential_eq_phase_mul_modulus,
    sourcePhaseCharacter_realCuspVector, Circle.coe_mul,
    positivePeriod_logCharacter C₀ ρ hρ hlog,
    sub_eq_add_neg, Real.exp_add, Complex.ofReal_mul]
  simp only [neg_mul]
  ring

theorem torusCoordinates_compactFibreAction_fibre (u : CompactFibreTorus)
    {x : Space} (hx : x ∈ openTorus) (i : Fin 2) :
    torusCoordinates (compactFibreAction u x) i.castSucc =
      (u i : ℂ) * torusCoordinates x i.castSucc := by
  rw [compactFibreAction, torusCoordinates_action _ hx]
  fin_cases i <;> rfl

/-- The raw marked phase point equals the original exponential point
at the full complex period vector.  No small-drift assumption is needed
for this equality of concrete points. -/
theorem frozenMarkedPoint_eq_exponentialPoint
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hlog : Real.log ρ ≠ 0) (a β : Plane) :
    compactFibreAction
        ((fun i => Circle.exp (2 * Real.pi * a i)) *
          sourcePhaseCharacter C₀ (realCuspVector β))
        ((normalizedPositivePoint C₀ ρ hρ (realCuspVector β)).1 : Space) =
      exponentialPoint (ρ : ℂ) (realToComplex a +
        logarithmicPeriod (fun _ => C₀) (logarithm (ρ : ℂ)) *ᵥ realToComplex β) := by
  have ht : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
  have hx : ((normalizedPositivePoint C₀ ρ hρ (realCuspVector β)).1 : Space) ∈ openTorus :=
    (mem_openTorus_iff _).mpr (by rw [time_positiveFibre]; exact ht)
  apply torusCoordinates_injective
    ((mem_openTorus_iff _).mpr (by rw [time_compactFibreAction, time_positiveFibre]; exact ht))
    (exponentialPoint_mem ht _)
  rw [torusCoordinates_exponentialPoint ht]
  have hi (i : Fin 2) :
      torusCoordinates
        (compactFibreAction
          ((fun j => Circle.exp (2 * Real.pi * a j)) *
            sourcePhaseCharacter C₀ (realCuspVector β))
          ((normalizedPositivePoint C₀ ρ hρ (realCuspVector β)).1 : Space)) i.castSucc =
        exponential ((realToComplex a +
          logarithmicPeriod (fun _ => C₀) (logarithm (ρ : ℂ)) *ᵥ realToComplex β) i) := by
    rw [torusCoordinates_compactFibreAction_fibre _ hx,
      normalizedPositivePoint_coe, neg_realCuspVector_realCuspVector,
      torusCoordinates_positiveLogPoint hρ]
    convert frozenMarkedExponential_coordinate C₀ ρ hρ hlog a β i using 1
    fin_cases i <;> rfl
  funext i
  fin_cases i
  · exact hi 0
  · exact hi 1
  · change torusCoordinates _ 2 = (ρ : ℂ)
    rw [torusCoordinates_time, time_compactFibreAction, time_positiveFibre]

/-- In the source's ordered dual lattice, the positive phase shear is
the literal `M₀`, not its inverse. -/
theorem sourcePeriodCoordinates_M₀ (v : Wikipedia.HopfProblem.Lattice) :
    sourcePeriodCoordinates (M₀ *ᵥ v) =
      ((sourcePeriodCoordinates v).1 + cuspVector (sourcePeriodCoordinates v).2,
        (sourcePeriodCoordinates v).2) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [sourcePeriodCoordinates, M₀, cuspVector, dotProduct,
      Fin.sum_univ_four, add_comm]

theorem expFibreAction_exponentialPoint (w : Fin 2 → ℂ) {t : ℂ}
    (ht : t ≠ 0) (z : ComplexPlane₂) :
    expFibreAction w (exponentialPoint t z) = exponentialPoint t (w + z) := by
  have hx := exponentialPoint_mem ht z
  have hx' : expFibreAction w (exponentialPoint t z) ∈ openTorus := by
    apply (mem_openTorus_iff _).mpr
    rw [time_expFibreAction, time_exponentialPoint ht]
    exact ht
  apply torusCoordinates_injective hx' (exponentialPoint_mem ht _)
  rw [expFibreAction, torusCoordinates_action _ hx,
    torusCoordinates_exponentialPoint ht, torusCoordinates_exponentialPoint ht]
  ext i
  fin_cases i <;>
    simp [fibreMultiplier, expFibreUnits_coe, exponentialCoordinates, exponential_add]

theorem position_exponentialPoint {t : ℂ} (ht : t ≠ 0) (z : ComplexPlane₂) :
    position (exponentialPoint t z) =
      fun i => (-2 * Real.pi * (z i).im) / Real.log ‖t‖ := by
  ext i
  simp only [position, time_exponentialPoint ht, logCoordinates, logNorm,
    torusCoordinates_exponentialPoint ht]
  have he : exponentialCoordinates t z i.castSucc = exponential (z i) := by
    fin_cases i <;> rfl
  rw [he, log_norm_exponential]

theorem markedCoordinate_im (Z : Matrix (Fin 2) (Fin 2) ℂ)
    (a β : Plane) (i : Fin 2) :
    ((realToComplex a + Z *ᵥ realToComplex β) i).im =
      (Z.map Complex.im *ᵥ β) i := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_im]

theorem position_markedExponentialPoint (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : ℂ) (hlog : Real.log ‖exponential s‖ ≠ 0) (a β : Plane) :
    position (exponentialPoint (exponential s)
      (realToComplex a + logarithmicPeriod C s *ᵥ realToComplex β)) =
      displacement C (exponential s) β := by
  rw [position_exponentialPoint (exponential_ne_zero s)]
  ext i
  rw [markedCoordinate_im]
  apply (div_eq_iff hlog).mpr
  have h := congrFun (imaginary_displacement C s hlog β) i
  simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using h.symm

/-- The actual change of twist preserves both marked real period
coefficients, replacing only the original period matrix. -/
theorem changeTwist_markedExponentialPoint
    (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ)
    (hlog : Real.log ‖exponential s‖ < 0)
    (hR : entryNorm (driftMatrix C (exponential s)) ≤ -Real.log ‖exponential s‖ / 4)
    (a β : Plane) :
    changeTwist C D (exponentialPoint (exponential s)
      (realToComplex a + logarithmicPeriod C s *ᵥ realToComplex β)) =
      exponentialPoint (exponential s)
        (realToComplex a + logarithmicPeriod D s *ᵥ realToComplex β) := by
  unfold changeTwist correction
  rw [time_exponentialPoint (exponential_ne_zero s),
    position_markedExponentialPoint C s hlog.ne,
    inverseDisplacement_displacement C hlog hR,
    expFibreAction_exponentialPoint _ (exponential_ne_zero s)]
  congr 1
  simp only [logarithmicPeriod, Matrix.add_mulVec, Matrix.sub_mulVec]
  abel

theorem changeTwist_markedExponentialPoint_logarithm
    (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) (ht : t ≠ 0)
    (hlog : Real.log ‖t‖ < 0)
    (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4)
    (a β : Plane) :
    changeTwist C D (exponentialPoint t
      (realToComplex a + logarithmicPeriod C (logarithm t) *ᵥ realToComplex β)) =
      exponentialPoint t
        (realToComplex a + logarithmicPeriod D (logarithm t) *ᵥ realToComplex β) := by
  have hlog' : Real.log ‖exponential (logarithm t)‖ < 0 := by
    rwa [exponential_logarithm ht]
  have hR' : entryNorm (driftMatrix C (exponential (logarithm t))) ≤
      -Real.log ‖exponential (logarithm t)‖ / 4 := by
    rwa [exponential_logarithm ht]
  simpa only [exponential_logarithm ht] using
    changeTwist_markedExponentialPoint C D (logarithm t) hlog' hR' a β

section FrozenFibre

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε) (hR : SmallDrift (positiveTwist C₀) ε)

/-- The genuine frozen phase homeomorphism has the original full period marking. -/
theorem frozenPhaseHomeomorph_periods (a β : Plane) :
    (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR
      ((fun i => Circle.exp (2 * Real.pi * a i)) *
        sourcePhaseCharacter C₀ (realCuspVector β), realCuspVector β) : Space) =
      exponentialPoint (ρ : ℂ) (realToComplex a +
        logarithmicPeriod (fun _ => C₀) (logarithm (ρ : ℂ)) *ᵥ realToComplex β) := by
  rw [frozenPhaseHomeomorph_coe]
  exact frozenMarkedPoint_eq_exponentialPoint C₀ ρ hρ
    (Real.log_neg hρ (hρε.trans hε1)).ne a β

/-- Marked product coordinates give the original exponential point
in the literal frozen quotient fibre. -/
theorem frozenProductFibreHomeomorph_periods (a β : Plane) :
    frozenProductFibreHomeomorph ε C₀ ρ hρ hε1 hρε hR
        (fun i => Circle.exp (2 * Real.pi * a i), coordinateProjection 2 β) =
      fibreProjection (fun _ => C₀) ε (ρ : ℂ) (positiveLevel_norm_lt ρ hρ.le ε hρε)
        ⟨exponentialPoint (ρ : ℂ) (realToComplex a +
            logarithmicPeriod (fun _ => C₀) (logarithm (ρ : ℂ)) *ᵥ realToComplex β),
          time_exponentialPoint (Complex.ofReal_ne_zero.mpr hρ.ne') _⟩ := by
  rw [frozenProductFibreHomeomorph_coordinateProjection]
  apply congrArg (fibreProjection (fun _ => C₀) ε (ρ : ℂ)
    (positiveLevel_norm_lt ρ hρ.le ε hρε))
  exact Subtype.ext (frozenPhaseHomeomorph_periods C₀ ρ hρ ε hε1 hρε hR a β)

end FrozenFibre

section VaryingFibre

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : SmallDrift C ε) (hRD : SmallDrift (frozen C) ε)

/-- Inverse straightening retains the actual `α, β` period coefficients. -/
theorem varyingPhaseHomeomorph_periods (a β : Plane) :
    (varyingPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD
      ((fun i => Circle.exp (2 * Real.pi * a i)) *
        sourcePhaseCharacter (C 0) (realCuspVector β), realCuspVector β) : Space) =
      exponentialPoint (ρ : ℂ) (realToComplex a +
        logarithmicPeriod C (logarithm (ρ : ℂ)) *ᵥ realToComplex β) := by
  rw [varyingPhaseHomeomorph_coe, frozenPhaseHomeomorph_periods]
  apply changeTwist_markedExponentialPoint_logarithm (frozen C) C (ρ : ℂ)
    (Complex.ofReal_ne_zero.mpr hρ.ne')
  · rw [Complex.norm_of_nonneg hρ.le]
    exact Real.log_neg hρ (hρε.trans hε1)
  · exact hRD (ρ : ℂ) (by rwa [Complex.norm_of_nonneg hρ.le])
      (by rwa [Complex.norm_of_nonneg hρ.le])

/-- The product model of the original varying quotient fibre has the
original full complex period marking, not only a topological marking. -/
theorem varyingProductFibreHomeomorph_periods (a β : Plane) :
    varyingProductFibreHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD
        (fun i => Circle.exp (2 * Real.pi * a i), coordinateProjection 2 β) =
      fibreProjection C ε (ρ : ℂ) (positiveLevel_norm_lt ρ hρ.le ε hρε)
        ⟨exponentialPoint (ρ : ℂ) (realToComplex a +
            logarithmicPeriod C (logarithm (ρ : ℂ)) *ᵥ realToComplex β),
          time_exponentialPoint (Complex.ofReal_ne_zero.mpr hρ.ne') _⟩ := by
  rw [varyingProductFibreHomeomorph_coordinateProjection]
  apply congrArg (fibreProjection C ε (ρ : ℂ) (positiveLevel_norm_lt ρ hρ.le ε hρε))
  exact Subtype.ext (varyingPhaseHomeomorph_periods C ρ hρ ε hε hε1 hρε hC hRC hRD a β)

end VaryingFibre

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
