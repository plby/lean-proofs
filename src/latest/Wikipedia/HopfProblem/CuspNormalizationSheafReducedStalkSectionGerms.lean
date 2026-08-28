import Wikipedia.HopfProblem.CuspNormalizationSheafReducedStalkImage
import Wikipedia.HopfProblem.CuspNormalizationSheafReducedStalkSections

/-!
# Actual reduced sections give actual restricted analytic germs

Local ambient representatives show that the ordinary within-subset
function germ of every reduced section lies in the literal analytic
restriction image. The resulting ring maps commute with actual
restriction, with equality precisely equality of the actual germs.
-/

noncomputable section

open Set Filter Topology TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafReduced

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (S : Set E) (x : S)

/-- The germ of an actual reduced holomorphic section, in the actual
image of ambient analytic-germ restriction. -/
def modelSectionGerm (U : Opens S) (hx : x ∈ U) :
    Section 𝓘(ℂ, E) S U →+* RestrictedAnalyticGermImage S x where
  toFun f := ⟨(extendRelativeSection S U f : Filter.Germ (𝓝[S] x.val) ℂ), by
    obtain ⟨g, hg, he⟩ := exists_analytic_representative S x U hx f
    exact ⟨Germs.ofAnalytic g hg, Filter.Germ.coe_eq.mpr he.symm⟩⟩
  map_zero' := by
    apply Subtype.ext
    change (extendRelativeSection S U 0 : Filter.Germ (𝓝[S] x.val) ℂ) =
      ((fun _ : E => (0 : ℂ)) : Filter.Germ (𝓝[S] x.val) ℂ)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [eventually_mem_relativeOpen S x U hx] with y hy
    obtain ⟨hyS, hyU⟩ := hy
    rw [extendRelativeSection_apply S U 0 y hyS hyU]
    rfl
  map_one' := by
    apply Subtype.ext
    change (extendRelativeSection S U 1 : Filter.Germ (𝓝[S] x.val) ℂ) =
      ((fun _ : E => (1 : ℂ)) : Filter.Germ (𝓝[S] x.val) ℂ)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [eventually_mem_relativeOpen S x U hx] with y hy
    obtain ⟨hyS, hyU⟩ := hy
    rw [extendRelativeSection_apply S U 1 y hyS hyU]
    rfl
  map_add' f g := by
    apply Subtype.ext
    change (extendRelativeSection S U (f + g) : Filter.Germ (𝓝[S] x.val) ℂ) =
      ((fun y => extendRelativeSection S U f y + extendRelativeSection S U g y) :
        Filter.Germ (𝓝[S] x.val) ℂ)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [eventually_mem_relativeOpen S x U hx] with y hy
    obtain ⟨hyS, hyU⟩ := hy
    rw [extendRelativeSection_apply S U (f + g) y hyS hyU,
      extendRelativeSection_apply S U f y hyS hyU,
      extendRelativeSection_apply S U g y hyS hyU]
    rfl
  map_mul' f g := by
    apply Subtype.ext
    change (extendRelativeSection S U (f * g) : Filter.Germ (𝓝[S] x.val) ℂ) =
      ((fun y => extendRelativeSection S U f y * extendRelativeSection S U g y) :
        Filter.Germ (𝓝[S] x.val) ℂ)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [eventually_mem_relativeOpen S x U hx] with y hy
    obtain ⟨hyS, hyU⟩ := hy
    rw [extendRelativeSection_apply S U (f * g) y hyS hyU,
      extendRelativeSection_apply S U f y hyS hyU,
      extendRelativeSection_apply S U g y hyS hyU]
    rfl

@[simp] theorem modelSectionGerm_coe (U : Opens S) (hx : x ∈ U)
    (f : Section 𝓘(ℂ, E) S U) :
    (modelSectionGerm S x U hx f : Filter.Germ (𝓝[S] x.val) ℂ) =
      (extendRelativeSection S U f : Filter.Germ (𝓝[S] x.val) ℂ) := rfl

/-- Equality in the actual image ring is exactly equality of the
actual within-subset germs of the represented functions. -/
theorem modelSectionGerm_eq_iff (U V : Opens S) (hxU : x ∈ U) (hxV : x ∈ V)
    (f : Section 𝓘(ℂ, E) S U) (g : Section 𝓘(ℂ, E) S V) :
    modelSectionGerm S x U hxU f = modelSectionGerm S x V hxV g ↔
      extendRelativeSection S U f =ᶠ[𝓝[S] x.val] extendRelativeSection S V g :=
  Subtype.ext_iff.trans Filter.Germ.coe_eq

/-- Actual restriction of a reduced section preserves its actual germ. -/
theorem modelSectionGerm_restrict (U V : Opens S) (h : U ≤ V) (hx : x ∈ U)
    (f : Section 𝓘(ℂ, E) S V) :
    modelSectionGerm S x U hx (restriction 𝓘(ℂ, E) S h f) =
      modelSectionGerm S x V (h hx) f := by
  apply (modelSectionGerm_eq_iff S x U V hx (h hx) _ f).mpr
  filter_upwards [eventually_mem_relativeOpen S x U hx] with y hy
  obtain ⟨hyS, hyU⟩ := hy
  rw [extendRelativeSection_apply S U _ y hyS hyU,
    extendRelativeSection_apply S V f y hyS (h hyU)]
  rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafReduced
