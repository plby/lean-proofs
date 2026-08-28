import Wikipedia.HopfProblem.CuspNormalizationSheafCuspTerms
import Wikipedia.HopfProblem.CuspNormalizationSheafReducedAmbient
import Wikipedia.HopfProblem.HolomorphicFunctionSheafStalkChartSections

/-!
# The actual normalization pullback on ambient section extensions

Restrict an ambient holomorphic section to the reduced central fibre
and apply the actual normalization-sheaf pullback.  Its extension by zero
is literally the ambient zero extension composed with the original
component projection.  The inverse-image domains agree exactly, including
outside the open set, so this is a global function equality.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafNormalizationStalk

open CuspQuotient ToricCharts ToricSpace SheafResolution

local notation "I₂" => 𝓘(ℂ, CoordinateSpace 2)
local notation "I₃" => 𝓘(ℂ, CoordinateSpace 3)

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual two-stage preimage is the component projection's preimage
of the original ambient open set. -/
@[simp] theorem normalization_mem_preimage_ambientOpen
    (V : Opens (QuotientSpace C ε)) (y : rayDivisor 0) :
    y ∈ (Opens.map (normalizationMap C ε hε)).obj
        (SheafReduced.ambientOpen (centralSet C ε) V) ↔
      componentProjection C ε hε y ∈ V := Iff.rfl

/-- The actual first sheaf arrow on an ambient section has precisely
the literal component-projection pullback as its zero extension. -/
theorem normalizationPullback_ambient_extend (V : Opens (QuotientSpace C ε)) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ∀ g : HolomorphicFunctionSheaf.Section I₃ (QuotientSpace C ε) V,
    HolomorphicFunctionSheaf.extendManifoldSection I₂
      ((Opens.map (normalizationMap C ε hε)).obj
        (SheafReduced.ambientOpen (centralSet C ε) V))
      ((normalizationPullback C ε hε hε1 hC hR).hom.app
        (op (SheafReduced.ambientOpen (centralSet C ε) V))
        (SheafReduced.ambientRestriction I₃ (centralSet C ε) V g)) =
      fun y : rayDivisor 0 => HolomorphicFunctionSheaf.extendManifoldSection I₃ V g
        (componentProjection C ε hε y) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  intro g
  rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafNormalizationStalk
