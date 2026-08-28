import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBlowupH1Charts
import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZeroBasic

/-!
# Actual holomorphic-function sections on the incidence blowup

Sections are the existing analytic-order manifold maps, with pointwise
operations and literal restriction. Extension by zero is used only as an
ambient representative on its original open domain.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupH1

open AffineBlowup ToricCharts

abbrev blowupSheaf :=
  HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) Space

def sectionExtension (U : Opens Space)
    (s : HolomorphicFunctionSheaf.Section 𝓘(ℂ, CoordinateSpace 2) Space U) (x : Space) : ℂ := by
  classical
  exact if hx : x ∈ U then s ⟨x, hx⟩ else 0

@[simp] theorem sectionExtension_apply (U : Opens Space)
    (s : HolomorphicFunctionSheaf.Section 𝓘(ℂ, CoordinateSpace 2) Space U)
    (x : Space) (hx : x ∈ U) : sectionExtension U s x = s ⟨x, hx⟩ := by
  classical
  simp only [sectionExtension, dif_pos hx]

theorem sectionExtension_comp_val (U : Opens Space)
    (s : HolomorphicFunctionSheaf.Section 𝓘(ℂ, CoordinateSpace 2) Space U) :
    (fun x : U => sectionExtension U s x) = (s : U → ℂ) :=
  funext (fun x => sectionExtension_apply U s x x.property)

theorem sectionExtension_holomorphic (U : Opens Space)
    (s : HolomorphicFunctionSheaf.Section 𝓘(ℂ, CoordinateSpace 2) Space U) :
    ContMDiffOn 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ) ω (sectionExtension U s) U := by
  intro x hx
  have hg : ContMDiffAt 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ) ω (sectionExtension U s) x := by
    apply (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp
    rw [sectionExtension_comp_val]
    exact s.contMDiff _
  exact hg.contMDiffWithinAt

def sectionOfHolomorphic (U : Opens Space) (f : Space → ℂ)
    (hf : ContMDiffOn 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ) ω f U) :
    HolomorphicFunctionSheaf.Section 𝓘(ℂ, CoordinateSpace 2) Space U :=
  ⟨fun x => f x, fun x => contMDiffAt_subtype_iff.mpr
    (hf.contMDiffAt (U.isOpen.mem_nhds x.property))⟩

@[simp] theorem sectionOfHolomorphic_apply (U : Opens Space) (f : Space → ℂ)
    (hf : ContMDiffOn 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ) ω f U) (x : U) :
    sectionOfHolomorphic U f hf x = f x := rfl

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupH1
