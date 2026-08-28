import Wikipedia.HopfProblem.CuspNormalizationGermsBasic
import Mathlib.Geometry.Manifold.ContMDiffMap

/-!
# Local holomorphic sections and actual analytic germs

A holomorphic section on an open subset of a complex normed space has
an analytic ambient representative at each point of that subset.  We
use its literal extension by zero, making no assertion of analyticity
at the boundary.  Conversely, the analytic locus of an actual analytic
representative is an open neighbourhood carrying a holomorphic section
with that representative's germ.

No completeness assumption on the source space is needed.  The target
is the complete normed field `ℂ`.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf

open CuspNormalization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The actual extension by zero of a holomorphic section.  Only its
values and analyticity inside the given open set are used. -/
def extendSection (U : Opens E) (f : ContMDiffMap 𝓘(ℂ, E) 𝓘(ℂ) U ℂ ω) (x : E) : ℂ := by
  classical
  exact if hx : x ∈ U then f ⟨x, hx⟩ else 0

@[simp] theorem extendSection_apply (U : Opens E)
    (f : ContMDiffMap 𝓘(ℂ, E) 𝓘(ℂ) U ℂ ω) (x : E) (hx : x ∈ U) :
    extendSection U f x = f ⟨x, hx⟩ := by
  classical
  simp only [extendSection, dif_pos hx]

theorem extendSection_comp_val (U : Opens E)
    (f : ContMDiffMap 𝓘(ℂ, E) 𝓘(ℂ) U ℂ ω) :
    (fun x : U => extendSection U f x) = (f : U → ℂ) :=
  funext fun x => extendSection_apply U f x x.property

/-- Extension by zero is analytic at every point of the original open
domain, by the actual induced manifold charts on that domain. -/
theorem extendSection_analyticAt (U : Opens E)
    (f : ContMDiffMap 𝓘(ℂ, E) 𝓘(ℂ) U ℂ ω) (a : E) (ha : a ∈ U) :
    AnalyticAt ℂ (extendSection U f) a := by
  have hd : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ) ω (extendSection U f) a := by
    apply (contMDiffAt_subtype_iff (x := (⟨a, ha⟩ : U))).mp
    rw [extendSection_comp_val U f]
    exact f.contMDiff _
  exact hd.contDiffAt.analyticAt

/-- Equality with an ambient function on the section domain gives
equality of actual neighbourhood germs at every point of that domain. -/
theorem extendSection_eventuallyEq (U : Opens E)
    (s : ContMDiffMap 𝓘(ℂ, E) 𝓘(ℂ) U ℂ ω) (a : E) (ha : a ∈ U)
    (f : E → ℂ) (hs : ∀ x (hx : x ∈ U), s ⟨x, hx⟩ = f x) :
    extendSection U s =ᶠ[𝓝 a] f := by
  filter_upwards [U.isOpen.mem_nhds ha] with x hx
  rw [extendSection_apply U s x hx]
  exact hs x hx

/-- An analytic ambient function is an actual holomorphic section on
an open neighbourhood, with literal equality throughout that domain. -/
theorem exists_section_of_analyticAt {a : E} {f : E → ℂ} (hf : AnalyticAt ℂ f a) :
    ∃ (U : Opens E) (_ha : a ∈ U) (s : ContMDiffMap 𝓘(ℂ, E) 𝓘(ℂ) U ℂ ω),
      ∀ x (hx : x ∈ U), s ⟨x, hx⟩ = f x := by
  let U : Opens E := ⟨{x | AnalyticAt ℂ f x}, isOpen_analyticAt ℂ f⟩
  have hs : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ) ω (fun x : U => f x) := by
    intro x
    have hx : AnalyticAt ℂ f (x : E) := x.property
    exact contMDiffAt_subtype_iff.mpr hx.contDiffAt.contMDiffAt
  exact ⟨U, hf, ⟨fun x => f x, hs⟩, fun _ _ => rfl⟩

/-- Every actual analytic germ is represented by a holomorphic section
on an actual open neighbourhood of its base point. -/
theorem exists_section_representative (a : E) (φ : Germs.AnalyticGerm a) :
    ∃ (U : Opens E) (ha : a ∈ U) (s : ContMDiffMap 𝓘(ℂ, E) 𝓘(ℂ) U ℂ ω),
      Germs.ofAnalytic (extendSection U s) (extendSection_analyticAt U s a ha) = φ := by
  obtain ⟨f, hf, hφ⟩ := Germs.exists_representative φ
  obtain ⟨U, ha, s, hs⟩ := exists_section_of_analyticAt hf
  refine ⟨U, ha, s, Eq.trans ?_ hφ⟩
  exact (Germs.ofAnalytic_eq_iff _ _ _ _).mpr (extendSection_eventuallyEq U s a ha f hs)

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf
