import Wikipedia.HopfProblem.CuspExponentials
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusPolar
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusTopology

/-!
# The literal toric disc times the two compact period circles

The reference triangle has time coordinate `z₀ z₁ z₂`.  Thus the
extension preserving the original base parameter `q` has affine
coordinates `(q/(u v), u, v)`, where `u` and `v` are the actual positive
unit phases of the two real integer-period coordinates.  This formula
is continuous at `q = 0` and takes values in the original radius-`r`
toric tube before passing to its original cusp quotient.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap Matrix

namespace Wikipedia.HopfProblem.CuspBoundaryToricExtension

open ToricCharts ToricFan ToricSpace CuspQuotient CuspUniformization
open PeriodTorusHigherHomology
open ThreefoldOverlapMappingTorus (phase phase_continuous phase_real)

/-- The actual reference-chart coordinates, with the original base unchanged. -/
def referenceCoordinates (q : ℂ) (y : ProductTorus 2) : CoordinateSpace 3 :=
  ![q / ((phase (y 0) : ℂ) * (phase (y 1) : ℂ)),
    (phase (y 0) : ℂ), (phase (y 1) : ℂ)]

/-- Multiplying the three affine coordinates recovers the original parameter. -/
@[simp] theorem referenceCoordinates_time (q : ℂ) (y : ProductTorus 2) :
    Triangle.time (referenceCoordinates q y) = q := by
  change q / ((phase (y 0) : ℂ) * (phase (y 1) : ℂ)) *
    (phase (y 0) : ℂ) * (phase (y 1) : ℂ) = q
  rw [mul_assoc]
  exact div_mul_cancel₀ q (mul_ne_zero (phase (y 0)).coe_ne_zero (phase (y 1)).coe_ne_zero)

/-- The same formula on the original real two-period representatives. -/
theorem referenceCoordinates_real (q : ℂ) (x : Fin 2 → ℝ) :
    referenceCoordinates q (coordinateProjection 2 x) =
      ![q / (exponential (x 0 : ℂ) * exponential (x 1 : ℂ)),
        exponential (x 0 : ℂ), exponential (x 1 : ℂ)] := by
  ext i
  fin_cases i <;> simp [referenceCoordinates, coordinateProjection, phase_real]

/-- Joint continuity includes the central parameter; the only denominators
are the two nowhere-zero compact unit phases. -/
theorem referenceCoordinates_continuous :
    Continuous (fun p : ℂ × ProductTorus 2 => referenceCoordinates p.1 p.2) := by
  have hphase (i : Fin 2) :
      Continuous (fun p : ℂ × ProductTorus 2 => (phase (p.2 i) : ℂ)) :=
    continuous_subtype_val.comp (phase_continuous.comp ((continuous_apply i).comp continuous_snd))
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_fst.div (hphase 0 |>.mul (hphase 1))
      (fun p => mul_ne_zero (phase (p.2 0)).coe_ne_zero (phase (p.2 1)).coe_ne_zero)
  · exact hphase 0
  · exact hphase 1

/-- On nonzero parameters this is the original toric exponential.
The coordinate identity itself also remains valid at zero. -/
theorem exponentialPoint_real_reference (q : ℂ) (x : Fin 2 → ℝ) :
    exponentialPoint q (fun i => (x i : ℂ)) =
      inclusion referenceTriangle (referenceCoordinates q (coordinateProjection 2 x)) := by
  change inclusion referenceTriangle
    (monomial referenceTriangle.dual (exponentialCoordinates q (fun i => (x i : ℂ)))) = _
  rw [referenceCoordinates_real]
  apply congrArg (inclusion referenceTriangle)
  ext i
  fin_cases i <;>
    simp [monomial, referenceTriangle, Triangle.dual, exponentialCoordinates,
      Fin.prod_univ_succ, div_eq_mul_inv, mul_comm, mul_left_comm]

/-- The actual extension into the original open toric tube. -/
def discLift (r : ℝ) (p : disc r × ProductTorus 2) : Tube (disc r) :=
  ⟨inclusion referenceTriangle (referenceCoordinates p.1 p.2), by
    change time (inclusion referenceTriangle (referenceCoordinates p.1 p.2)) ∈ disc r
    rw [time_inclusion, referenceCoordinates_time]
    exact p.1.2⟩

@[simp] theorem discLift_coe (r : ℝ) (p : disc r × ProductTorus 2) :
    (discLift r p : Space) = inclusion referenceTriangle (referenceCoordinates p.1 p.2) := rfl

theorem discLift_continuous (r : ℝ) : Continuous (discLift r) :=
  ((inclusion_openEmbedding referenceTriangle).continuous.comp
    (referenceCoordinates_continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))).subtype_mk _

/-- The literal disc-times-two-torus map into the original full cusp cap. -/
def discExtension (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) :
    C(disc r × ProductTorus 2, QuotientSpace C r) :=
  ⟨fun p => quotientMap C r (discLift r p),
    (quotientMap_continuous C r).comp (discLift_continuous r)⟩

@[simp] theorem discExtension_apply
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (p : disc r × ProductTorus 2) :
    discExtension C r p = quotientMap C r (discLift r p) := rfl

/-- The extension lies over precisely the original disc coordinate. -/
@[simp] theorem discExtension_projection
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (p : disc r × ProductTorus 2) :
    projection C r (discExtension C r p) = (p.1 : ℂ) := by
  change time (inclusion referenceTriangle (referenceCoordinates p.1 p.2)) = _
  rw [time_inclusion, referenceCoordinates_time]

end Wikipedia.HopfProblem.CuspBoundaryToricExtension
