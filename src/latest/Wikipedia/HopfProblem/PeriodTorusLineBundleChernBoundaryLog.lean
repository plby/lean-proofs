import Wikipedia.HopfProblem.PeriodTorusLineBundleChernWinding
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLogCocycle
import Mathlib.Analysis.Convex.PathConnected

/-!
# Winding of the actual logarithmic factor boundary

Three fibre-coordinate paths are assembled from the actual entire factor
logarithms.  The first joins the selected initial and intermediate frames,
the second follows a genuine lifted middle edge, and the last traverses
the reverse final edge.  The endpoint is defined by the literal logarithm
values, not by an assigned integer.  The actual exponential-cover winding
then computes its sign as the negative integer logarithmic defect.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassification unitInterval

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

/-- The literal endpoint discrepancy between the two compositions of actual factor logarithms. -/
def factorBoundaryLogEndpoint (l m : p.lattice) (z : ComplexPlane₂) : ℂ :=
  factorLog F l (z + m) + factorLog F m z - factorLog F (l + m) z

theorem factorBoundaryLogEndpoint_eq_neg_defect (l m : p.lattice) (z : ComplexPlane₂) :
    factorBoundaryLogEndpoint F l m z = -factorLogDefect F l m z := by
  simp only [factorBoundaryLogEndpoint, factorLogDefect]
  ring

/-- The actual factor cocycle makes the endpoint discrepancy an exponential period. -/
theorem factorBoundaryLogEndpoint_exp (l m : p.lattice) (z : ComplexPlane₂) :
    Complex.exp (factorBoundaryLogEndpoint F l m z) = 1 := by
  rw [factorBoundaryLogEndpoint_eq_neg_defect, Complex.exp_neg, factorLogDefect_exp, inv_one]

/-- The integer, and its sign, follow from the already proved genuine logarithmic defect. -/
theorem factorBoundaryLogEndpoint_eq_neg_integer (l m : p.lattice) (z : ComplexPlane₂) :
    factorBoundaryLogEndpoint F l m z =
      (-factorLogIntegerCocycle F l m : ℤ) * (2 * Real.pi * Complex.I) := by
  rw [factorBoundaryLogEndpoint_eq_neg_defect, factorLogIntegerCocycle_spec]
  simp only [Int.cast_neg, neg_mul]

/-- The continuous logarithmic middle-edge coordinate, in the first lifted frame. -/
def factorBoundaryMiddleLog (l m : p.lattice) (z₁ z₂ : ComplexPlane₂)
    (γ : Path z₁ (z₂ + (m : ComplexPlane₂))) :
    Path (factorLog F l z₁) (factorLog F l (z₂ + m) + factorLog F m z₂) where
  toFun t := factorLog F l (γ t) + (t : ℝ) • factorLog F m z₂
  continuous_toFun := ((factorLog_holomorphic F l).continuous.comp γ.continuous).add
    (continuous_subtype_val.smul continuous_const)
  source' := by simp
  target' := by simp

/-- The three actual logarithmic pieces, with the boundary order `01,12,20`. -/
def factorBoundaryLogPath (l m : p.lattice) (z₁ z₂ : ComplexPlane₂)
    (γ : Path z₁ (z₂ + (m : ComplexPlane₂))) :
    Path (0 : ℂ) (factorBoundaryLogEndpoint F l m z₂) :=
  ((Path.segment 0 (factorLog F l z₁)).trans (factorBoundaryMiddleLog F l m z₁ z₂ γ)).trans
    (Path.segment (factorLog F l (z₂ + m) + factorLog F m z₂)
      (factorBoundaryLogEndpoint F l m z₂))

/-- The exponentials of these actual coordinate paths form a genuine loop in `ℂ \ {0}`. -/
def factorBoundaryScalarLoop (l m : p.lattice) (z₁ z₂ : ComplexPlane₂)
    (γ : Path z₁ (z₂ + (m : ComplexPlane₂))) : BasedLoop where
  toFun t := ⟨Complex.exp (factorBoundaryLogPath F l m z₁ z₂ γ t), Complex.exp_ne_zero _⟩
  continuous_toFun :=
    (Complex.continuous_exp.comp (factorBoundaryLogPath F l m z₁ z₂ γ).continuous).subtype_mk _
  source' := by
    apply Subtype.ext
    change Complex.exp (factorBoundaryLogPath F l m z₁ z₂ γ 0) = 1
    rw [Path.source, Complex.exp_zero]
  target' := by
    apply Subtype.ext
    change Complex.exp (factorBoundaryLogPath F l m z₁ z₂ γ 1) = 1
    rw [Path.target, factorBoundaryLogEndpoint_exp]

/-- The winding is computed through the actual exponential covering, not assigned to this loop. -/
theorem windingNumber_factorBoundaryScalarLoop (l m : p.lattice) (z₁ z₂ : ComplexPlane₂)
    (γ : Path z₁ (z₂ + (m : ComplexPlane₂))) :
    windingNumber (factorBoundaryScalarLoop F l m z₁ z₂ γ) = -factorLogIntegerCocycle F l m := by
  apply windingNumber_of_logPath (factorBoundaryScalarLoop F l m z₁ z₂ γ)
    (factorBoundaryLogPath F l m z₁ z₂ γ)
    (factorBoundaryLogPath F l m z₁ z₂ γ).continuous
    (factorBoundaryLogPath F l m z₁ z₂ γ).source (fun _ => rfl)
    (-factorLogIntegerCocycle F l m)
  rw [Path.target, factorBoundaryLogEndpoint_eq_neg_integer]

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
