import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyZeroRayCoverTransitions
import Wikipedia.HopfProblem.HolomorphicFunctionSheafStalkSections

/-!
# Actual holomorphic sections in the proved intersection coordinates

Pullback uses the literal coordinate biholomorphisms. Extension by zero
is used solely as an ambient analytic representative on the original
open domain. Analytic coefficients conversely define actual holomorphic
sections through the proved inverse coordinate maps.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayCover

open ToricCharts

abbrev Section (W : Opens component) :=
  HolomorphicFunctionSheaf.Section 𝓘(ℂ, CoordinateSpace 2) component W

variable {Ω : Opens (ℂ × ℂ)} {W : Opens component}
  (e : Diffeomorph 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, CoordinateSpace 2) Ω W ω)

def pullbackSection (s : Section W) : ContMDiffMap 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) Ω ℂ ω :=
  ⟨fun q => s (e q), s.contMDiff.comp e.contMDiff⟩

def coefficient (s : Section W) : ℂ × ℂ → ℂ :=
  HolomorphicFunctionSheaf.extendSection Ω (pullbackSection e s)

theorem coefficient_analytic (s : Section W) : AnalyticOnNhd ℂ (coefficient e s) Ω :=
  fun q hq => HolomorphicFunctionSheaf.extendSection_analyticAt Ω (pullbackSection e s) q hq

@[simp] theorem coefficient_apply (s : Section W) (q : Ω) : coefficient e s q = s (e q) :=
  HolomorphicFunctionSheaf.extendSection_apply Ω (pullbackSection e s) q q.property

theorem coefficient_apply_symm (s : Section W) (x : W) :
    coefficient e s (e.symm x) = s x := by
  rw [coefficient_apply, e.apply_symm_apply]

/-- An actual analytic coefficient becomes an actual holomorphic section. -/
def sectionFromCoefficient (f : ℂ × ℂ → ℂ) (hf : AnalyticOnNhd ℂ f Ω) : Section W :=
  ⟨fun x => f (e.symm x), by
    have h : ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) ω (fun q : Ω => f q) :=
      fun q => contMDiffAt_subtype_iff.mpr (hf q q.property).contDiffAt.contMDiffAt
    exact h.comp e.symm.contMDiff⟩

@[simp] theorem sectionFromCoefficient_apply (f : ℂ × ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f Ω) (x : W) : sectionFromCoefficient e f hf x = f (e.symm x) := rfl

/-- An entire chart function pulled back through actual blowdown coordinates. -/
def entireSection (k : Fin 3) (f : ℂ × ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ) :
    Section (cover k) :=
  ⟨fun x => f (coordinates k x), fun x =>
    (hf _ (mem_univ _)).contDiffAt.contMDiffAt.comp x
      (((coordinates_holomorphicOn k).contMDiffAt
        ((cover k).isOpen.mem_nhds x.property)).comp x contMDiff_subtype_val.contMDiffAt)⟩

@[simp] theorem entireSection_apply (k : Fin 3) (f : ℂ × ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f univ) (x : cover k) :
    entireSection k f hf x = f (coordinates k x) := rfl

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayCover
