import Wikipedia.HopfProblem.CuspNormalizationSheafReduced
import Wikipedia.HopfProblem.HolomorphicFunctionSheafStalkSections

/-!
# Analytic representatives of actual relative sections

The literal extension by zero of a relative section has, near each point
of its domain and along the actual subset, the same values as an ambient
function analytic at that point. No analyticity of the zero extension
away from the relative open domain is asserted.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafReduced

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The literal extension by zero outside the relative open domain. -/
def extendRelativeSection (S : Set E) (U : Opens S)
    (f : Section 𝓘(ℂ, E) S U) (y : E) : ℂ := by
  classical
  exact if hyS : y ∈ S then
    if hyU : (⟨y, hyS⟩ : S) ∈ U then f ⟨⟨y, hyS⟩, hyU⟩ else 0
  else 0

@[simp] theorem extendRelativeSection_apply (S : Set E) (U : Opens S)
    (f : Section 𝓘(ℂ, E) S U) (y : E) (hyS : y ∈ S)
    (hyU : (⟨y, hyS⟩ : S) ∈ U) :
    extendRelativeSection S U f y = f ⟨⟨y, hyS⟩, hyU⟩ := by
  classical
  simp only [extendRelativeSection, dif_pos hyS, dif_pos hyU]

omit [NormedSpace ℂ E] in
/-- A relative open neighbourhood contains all sufficiently nearby
points of the actual subset. -/
theorem eventually_mem_relativeOpen (S : Set E) (x : S) (U : Opens S)
    (hx : x ∈ U) :
    ∀ᶠ y in 𝓝[S] x.val, ∃ hyS : y ∈ S, (⟨y, hyS⟩ : S) ∈ U := by
  obtain ⟨V, hV⟩ := exists_ambient_open S U
  have hxV : x.val ∈ V := by
    change x ∈ Subtype.val ⁻¹' (V : Set E)
    rw [hV]
    exact hx
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (V.isOpen.mem_nhds hxV)] with y hyS hyV
  refine ⟨hyS, ?_⟩
  change (⟨y, hyS⟩ : S) ∈ (U : Set S)
  rw [← hV]
  exact hyV

/-- Every actual relative section has an ambient analytic representative
for its germ along the subset at each point of its relative open domain. -/
theorem exists_analytic_representative (S : Set E) (x : S) (U : Opens S)
    (hx : x ∈ U) (f : Section 𝓘(ℂ, E) S U) :
    ∃ g : E → ℂ, AnalyticAt ℂ g x.val ∧
      extendRelativeSection S U f =ᶠ[𝓝[S] x.val] g := by
  obtain ⟨V, hxV, g, hg⟩ := f.property ⟨x, hx⟩
  refine ⟨HolomorphicFunctionSheaf.extendSection V g,
    HolomorphicFunctionSheaf.extendSection_analyticAt V g x.val hxV, ?_⟩
  filter_upwards [eventually_mem_relativeOpen S x U hx,
    mem_nhdsWithin_of_mem_nhds (V.isOpen.mem_nhds hxV)] with y hyU hyV
  obtain ⟨hyS, hyU⟩ := hyU
  rw [extendRelativeSection_apply S U f y hyS hyU,
    HolomorphicFunctionSheaf.extendSection_apply V g y hyV]
  exact hg ⟨⟨y, hyS⟩, hyU⟩ hyV

end Wikipedia.HopfProblem.CuspNormalization.SheafReduced
