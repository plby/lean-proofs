import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsCompact
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsBiproduct
import Wikipedia.HopfProblem.CuspNormalizationSheafCuspTerms
import Wikipedia.HopfProblem.ToricComponentTopology
import Wikipedia.HopfProblem.CuspComponentProper

/-!
# Global sections of the actual normalization direct image

The inverse image of the actual top open set is the top open set on
the actual toric component. Its proved compactness and connectedness
therefore identify these genuine sections with constants by evaluation.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections

open SheafResolution ToricCharts ToricSpace HolomorphicFunctionSheaf

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The actual pushforward sections retain the original pointwise scalar action. -/
instance normalizationSections_module :
    Module ℂ (Sections (normalizationSheaf C ε hε)) :=
  inferInstanceAs (Module ℂ (GlobalSections 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)))

/-- The actual direct-image global-section identification is literally the identity. -/
def normalizationSectionsLinearEquiv : Sections (normalizationSheaf C ε hε) ≃ₗ[ℂ]
    GlobalSections 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0) :=
  LinearEquiv.refl ℂ _

/-- A specified actual point of the normalization surface. -/
def normalizationBasePoint : rayDivisor 0 :=
  ToricComponent.affineInclusion (ToricComponent.baseChart 0) 0

/-- The value of a genuine direct-image global section at an actual
point of the normalization. -/
def normalizationValue (s : Sections (normalizationSheaf C ε hε)) (x : rayDivisor 0) : ℂ :=
  normalizationSectionsLinearEquiv C ε hε s (toTopOpen (rayDivisor 0) x)

/-- The compact maximum principle applies to the actual toric surface. -/
theorem normalizationValue_eq (s : Sections (normalizationSheaf C ε hε))
    (x y : rayDivisor 0) : normalizationValue C ε hε s x = normalizationValue C ε hε s y :=
  compact_global_apply_eq 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)
    (normalizationSectionsLinearEquiv C ε hε s) x y

/-- Evaluation identifies the actual normalization global sections
with the complex numbers, complex linearly. -/
def normalizationGlobalLinearEquiv : Sections (normalizationSheaf C ε hε) ≃ₗ[ℂ] ℂ :=
  (normalizationSectionsLinearEquiv C ε hε).trans
    (compactGlobalEvalEquiv 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)
      normalizationBasePoint).toLinearEquiv

@[simp] theorem normalizationGlobalLinearEquiv_apply
    (s : Sections (normalizationSheaf C ε hε)) :
    normalizationGlobalLinearEquiv C ε hε s =
      normalizationValue C ε hε s normalizationBasePoint := rfl

/-- The inverse equivalence is the actual constant section. -/
def normalizationConstantSection (c : ℂ) : Sections (normalizationSheaf C ε hε) :=
  algebraMap ℂ (GlobalSections 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)) c

@[simp] theorem normalizationGlobalLinearEquiv_symm_apply (c : ℂ) :
    (normalizationGlobalLinearEquiv C ε hε).symm c = normalizationConstantSection C ε hε c :=
  compactGlobalEvalEquiv_symm_apply 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0) normalizationBasePoint c

/-- This dimension is that of the actual direct-image global-section space. -/
theorem normalizationGlobal_finrank :
    Module.finrank ℂ (Sections (normalizationSheaf C ε hε)) = 1 :=
  (normalizationGlobalLinearEquiv C ε hε).finrank_eq.trans (Module.finrank_self ℂ)

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections
