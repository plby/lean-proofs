import Wikipedia.HopfProblem.PeriodTorusExponentialChernLocalLifts
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernLogBasic

/-!
# Literal local logarithm differences for the original factor bundle

Using the actual local lift relative to the fixed vertex representative,
the original coordinate logarithm is a difference of pointwise local
logarithms minus the original integer factor defect times `2πi`.
The local logarithm functions need not be continuous; they are the
literal zero-cochain values used in the singular cochain resolution.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusExponentialChern

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassification
  PeriodTorusLineBundle.ChernCover PeriodTorusLineBundleChernLog

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

/-- The actual entire factor logarithm evaluated on the local lattice
displacement and the fixed representative of each point. -/
def localLogValue (i : p.Torus) (x : chartCover p i) : ℂ :=
  factorLog F (liftDisplacement p i x) (vertexLift p x)

/-- The original integral factor defect on the actual overlap data. -/
def overlapInteger (i j : p.Torus) (x : ↥(chartCover p i ⊓ chartCover p j)) : ℤ :=
  factorCocycle F (Core.deck p i j x) (liftDisplacement p i ⟨x, x.property.1⟩)

/-- This equality follows from the original factor-log defect equation;
in particular the minus sign is not assigned by a Chern-class convention. -/
theorem coordinateLog_eq_local_difference (i j : p.Torus)
    (x : ↥(chartCover p i ⊓ chartCover p j)) :
    coordinateLogSection F i j x =
      localLogValue F j ⟨x, x.property.2⟩ - localLogValue F i ⟨x, x.property.1⟩ -
        (overlapInteger F i j x : ℂ) * logPeriod := by
  have h := factorCocycle_spec F (Core.deck p i j x)
    (liftDisplacement p i ⟨x, x.property.1⟩) (vertexLift p x)
  rw [factorLogDefect, ← liftDisplacement_overlap p i j x,
    ← chartLift_eq_vertex_add p i ⟨x, x.property.1⟩] at h
  change factorLog F (Core.deck p i j x) (Core.lift p i x) =
    factorLog F (liftDisplacement p j ⟨x, x.property.2⟩) (vertexLift p x) -
      factorLog F (liftDisplacement p i ⟨x, x.property.1⟩) (vertexLift p x) -
        (factorCocycle F (Core.deck p i j x)
          (liftDisplacement p i ⟨x, x.property.1⟩) : ℂ) * logPeriod
  change _ - factorLog F (Core.deck p i j x) (Core.lift p i x) - _ = _ at h
  linear_combination -h

end Wikipedia.HopfProblem.PeriodTorusExponentialChern
