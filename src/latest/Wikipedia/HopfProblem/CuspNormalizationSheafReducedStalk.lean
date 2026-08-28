import Wikipedia.HopfProblem.CuspNormalizationSheafReducedStalkSectionGerms
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Topology.Sheaves.Stalks

/-!
# The genuine reduced stalk is the actual analytic restriction image

The source is the categorical colimit stalk of the independently defined
reduced holomorphic-function sheaf. The target is the literal image of
ambient analytic germs in the actual within-subset function-germ ring.
The comparison is constructed by the colimit universal property, and
actual representatives prove its injectivity and surjectivity.
-/

noncomputable section

open Set Filter Topology TopologicalSpace Opposite CategoryTheory Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafReduced

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (S : Set E) (x : S)

/-- The genuine compatible cocone of section-to-analytic-image maps. -/
def modelStalkCocone :
    Cocone ((OpenNhds.inclusion (X := TopCat.of S) x).op ⋙ presheaf 𝓘(ℂ, E) S) where
  pt := CommRingCat.of (RestrictedAnalyticGermImage S x)
  ι :=
    { app := fun U => CommRingCat.ofHom (modelSectionGerm S x U.unop.1 U.unop.2)
      naturality := by
        intro U V i
        ext f
        exact modelSectionGerm_restrict S x V.unop.1 U.unop.1
          (leOfHom i.unop) V.unop.2 f }

/-- The actual categorical colimit comparison morphism. -/
def modelStalkToImageHom : (presheaf 𝓘(ℂ, E) S).stalk x ⟶
    CommRingCat.of (RestrictedAnalyticGermImage S x) :=
  colimit.desc _ (modelStalkCocone S x)

/-- The actual ring homomorphism underlying the colimit comparison. -/
def modelStalkToImage : (presheaf 𝓘(ℂ, E) S).stalk x →+*
    RestrictedAnalyticGermImage S x := (modelStalkToImageHom S x).hom

@[simp] theorem modelStalkToImage_germ (U : Opens S) (hx : x ∈ U)
    (f : Section 𝓘(ℂ, E) S U) :
    modelStalkToImage S x ((presheaf 𝓘(ℂ, E) S).germ U x hx f) =
      modelSectionGerm S x U hx f := by
  exact congrArg (fun h => h f) (colimit.ι_desc (modelStalkCocone S x) (op ⟨U, hx⟩))

/-- Equality of actual within-subset germs gives equality on a smaller
relative open neighbourhood, hence equality in the categorical stalk. -/
theorem modelStalkToImage_injective : Function.Injective (modelStalkToImage S x) := by
  intro φ ψ hφψ
  obtain ⟨U, hxU, f, rfl⟩ := (presheaf 𝓘(ℂ, E) S).exists_germ_eq φ
  obtain ⟨V, hxV, g, rfl⟩ := (presheaf 𝓘(ℂ, E) S).exists_germ_eq ψ
  have hfg : modelSectionGerm S x U hxU f = modelSectionGerm S x V hxV g :=
    (modelStalkToImage_germ S x U hxU f).symm.trans
      (hφψ.trans (modelStalkToImage_germ S x V hxV g))
  have he := (modelSectionGerm_eq_iff S x U V hxU hxV f g).mp hfg
  have hv : Tendsto (Subtype.val : S → E) (𝓝 x) (𝓝[S] x.val) :=
    (map_nhds_subtype_val x).le
  have heS := he.comp_tendsto hv
  have hnbhd : {z : S | z ∈ U ∧ z ∈ V ∧
      extendRelativeSection S U f z.val = extendRelativeSection S V g z.val} ∈ 𝓝 x :=
    Filter.Eventually.and (U.isOpen.mem_nhds hxU)
      (Filter.Eventually.and (V.isOpen.mem_nhds hxV) heS)
  obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp hnbhd
  let W' : Opens S := ⟨W, hWo⟩
  have hWU : W' ≤ U := fun z hz => (hW hz).1
  have hWV : W' ≤ V := fun z hz => (hW hz).2.1
  apply (presheaf 𝓘(ℂ, E) S).germ_ext W' hxW (homOfLE hWU) (homOfLE hWV)
  apply Section.ext 𝓘(ℂ, E) S
  intro z
  have hz := (hW z.property).2.2
  rw [extendRelativeSection_apply S U f z.val.val z.val.property (hWU z.property),
    extendRelativeSection_apply S V g z.val.val z.val.property (hWV z.property)] at hz
  exact hz

/-- Every element of the actual analytic restriction image is represented
by a genuine reduced section on a relative open neighbourhood. -/
theorem modelStalkToImage_surjective : Function.Surjective (modelStalkToImage S x) := by
  intro φ
  obtain ⟨ψ, hψ⟩ := φ.property
  obtain ⟨F, hF, rfl⟩ := Germs.exists_representative ψ
  obtain ⟨V, hxV, g, hg⟩ := HolomorphicFunctionSheaf.exists_section_of_analyticAt hF
  let U : Opens S := ambientOpen S V
  have hxU : x ∈ U := hxV
  let f : Section 𝓘(ℂ, E) S U := ambientRestriction 𝓘(ℂ, E) S V g
  refine ⟨(presheaf 𝓘(ℂ, E) S).germ U x hxU f, ?_⟩
  rw [modelStalkToImage_germ]
  apply Subtype.ext
  change (extendRelativeSection S U f : Filter.Germ (𝓝[S] x.val) ℂ) = φ.val
  refine Eq.trans ?_ hψ
  change (extendRelativeSection S U f : Filter.Germ (𝓝[S] x.val) ℂ) =
    (F : Filter.Germ (𝓝[S] x.val) ℂ)
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [eventually_mem_relativeOpen S x U hxU] with y hy
  obtain ⟨hyS, hyU⟩ := hy
  rw [extendRelativeSection_apply S U f y hyS hyU]
  exact hg y hyU

/-- The actual categorical reduced holomorphic stalk is the literal
image of actual ambient analytic-germ restriction to the subset. -/
def modelStalkEquiv : (presheaf 𝓘(ℂ, E) S).stalk x ≃+*
    RestrictedAnalyticGermImage S x :=
  RingEquiv.ofBijective (modelStalkToImage S x)
    ⟨modelStalkToImage_injective S x, modelStalkToImage_surjective S x⟩

@[simp] theorem modelStalkEquiv_germ (U : Opens S) (hx : x ∈ U)
    (f : Section 𝓘(ℂ, E) S U) :
    modelStalkEquiv S x ((presheaf 𝓘(ℂ, E) S).germ U x hx f) =
      modelSectionGerm S x U hx f := modelStalkToImage_germ S x U hx f

/-- The comparison on a represented germ is its actual within-subset
function germ, not an unrelated abstract ring isomorphism. -/
@[simp] theorem modelStalkEquiv_germ_coe (U : Opens S) (hx : x ∈ U)
    (f : Section 𝓘(ℂ, E) S U) :
    (modelStalkEquiv S x ((presheaf 𝓘(ℂ, E) S).germ U x hx f) :
      Filter.Germ (𝓝[S] x.val) ℂ) =
        (extendRelativeSection S U f : Filter.Germ (𝓝[S] x.val) ℂ) := by
  rw [modelStalkEquiv_germ]
  rfl

/-- Restricting an actual ambient holomorphic section and then taking
its sheaf germ agrees with restricting its actual ambient analytic germ. -/
theorem modelStalkEquiv_ambient (V : Opens E) (hxV : x.val ∈ V)
    (g : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E) E V) :
    modelStalkEquiv S x ((presheaf 𝓘(ℂ, E) S).germ (ambientOpen S V) x hxV
      (ambientRestriction 𝓘(ℂ, E) S V g)) =
      (restrictAnalyticGerm S x).rangeRestrict
        (Germs.ofAnalytic (HolomorphicFunctionSheaf.extendSection V g)
          (HolomorphicFunctionSheaf.extendSection_analyticAt V g x.val hxV)) := by
  apply Subtype.ext
  refine (modelStalkEquiv_germ_coe S x (ambientOpen S V) hxV
    (ambientRestriction 𝓘(ℂ, E) S V g)).trans ?_
  change (extendRelativeSection S (ambientOpen S V)
    (ambientRestriction 𝓘(ℂ, E) S V g) : Filter.Germ (𝓝[S] x.val) ℂ) =
      (HolomorphicFunctionSheaf.extendSection V g : Filter.Germ (𝓝[S] x.val) ℂ)
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [eventually_mem_relativeOpen S x (ambientOpen S V) hxV] with y hy
  obtain ⟨hyS, hyU⟩ := hy
  rw [extendRelativeSection_apply S (ambientOpen S V) _ y hyS hyU,
    HolomorphicFunctionSheaf.extendSection_apply V g y hyU]
  rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafReduced
