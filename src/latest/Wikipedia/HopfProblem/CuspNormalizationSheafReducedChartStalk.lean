import Wikipedia.HopfProblem.CuspNormalizationSheafReducedChartStalkSectionGerms
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Topology.Sheaves.Stalks

/-!
# Genuine reduced holomorphic stalks in actual manifold charts

The source is the categorical stalk of the intrinsically defined
reduced holomorphic-function sheaf on the actual subset of the manifold.
The target is the literal ambient analytic-germ restriction image for
the actual chart subset. The chart comparison is built on representatives
and the genuine colimit universal property; its bijectivity follows from
the actual inverse chart and actual local analytic representatives.
-/

noncomputable section

open Set Filter Topology TopologicalSpace Opposite CategoryTheory Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafReduced

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  (e : OpenPartialHomeomorph M E) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω M)
  (S : Set M) (x : S) (hx : x.val ∈ e.source)

/-- The genuine cocone on the actual relative-neighbourhood diagram. -/
def chartStalkCocone :
    Cocone ((OpenNhds.inclusion (X := TopCat.of S) x).op ⋙ presheaf 𝓘(ℂ, E) S) where
  pt := CommRingCat.of (RestrictedAnalyticGermImage (chartSubset e S) (chartPoint e S x hx))
  ι :=
    { app := fun U => CommRingCat.ofHom (chartSectionGerm e he S x hx U.unop.1 U.unop.2)
      naturality := by
        intro U V i
        ext f
        exact chartSectionGerm_restrict e he S x hx V.unop.1 U.unop.1
          (leOfHom i.unop) V.unop.2 f }

/-- The actual colimit comparison morphism for the chosen genuine chart. -/
def chartStalkToImageHom : (presheaf 𝓘(ℂ, E) S).stalk x ⟶
    CommRingCat.of (RestrictedAnalyticGermImage (chartSubset e S) (chartPoint e S x hx)) :=
  colimit.desc _ (chartStalkCocone e he S x hx)

/-- The ring map underlying the genuine categorical chart comparison. -/
def chartStalkToImage : (presheaf 𝓘(ℂ, E) S).stalk x →+*
    RestrictedAnalyticGermImage (chartSubset e S) (chartPoint e S x hx) :=
  (chartStalkToImageHom e he S x hx).hom

@[simp] theorem chartStalkToImage_germ (U : Opens S) (hxU : x ∈ U)
    (f : Section 𝓘(ℂ, E) S U) :
    chartStalkToImage e he S x hx ((presheaf 𝓘(ℂ, E) S).germ U x hxU f) =
      chartSectionGerm e he S x hx U hxU f := by
  exact congrArg (fun h => h f)
    (colimit.ι_desc (chartStalkCocone e he S x hx) (op ⟨U, hxU⟩))

/-- Equal actual chart germs give equality after a genuine smaller
relative-open restriction on the original manifold. -/
theorem chartStalkToImage_injective : Function.Injective (chartStalkToImage e he S x hx) := by
  intro φ ψ hφψ
  obtain ⟨U, hxU, f, rfl⟩ := (presheaf 𝓘(ℂ, E) S).exists_germ_eq φ
  obtain ⟨V, hxV, g, rfl⟩ := (presheaf 𝓘(ℂ, E) S).exists_germ_eq ψ
  have hfg : chartSectionGerm e he S x hx U hxU f =
      chartSectionGerm e he S x hx V hxV g :=
    (chartStalkToImage_germ e he S x hx U hxU f).symm.trans
      (hφψ.trans (chartStalkToImage_germ e he S x hx V hxV g))
  have hlocal := (chartSectionGerm_eq_iff e he S x hx U V hxU hxV f g).mp hfg
  have hv : Tendsto (Subtype.val : S → M) (𝓝 x) (𝓝[S] x.val) :=
    (map_nhds_subtype_val x).le
  have hlocalS := hlocal.comp_tendsto hv
  have hnbhd : {z : S | z ∈ U ∧ z ∈ V ∧
      relativeExtension S U f.val z.val = relativeExtension S V g.val z.val} ∈ 𝓝 x :=
    inter_mem (U.isOpen.mem_nhds hxU) (inter_mem (V.isOpen.mem_nhds hxV) hlocalS)
  obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp hnbhd
  let W' : Opens S := ⟨W, hWo⟩
  have hWU : W' ≤ U := fun z hz => (hW hz).1
  have hWV : W' ≤ V := fun z hz => (hW hz).2.1
  apply (presheaf 𝓘(ℂ, E) S).germ_ext W' hxW (homOfLE hWU) (homOfLE hWV)
  apply Section.ext 𝓘(ℂ, E) S
  intro z
  have hz := (hW z.property).2.2
  rw [relativeExtension_apply S U f.val z.val.val z.val.property (hWU z.property),
    relativeExtension_apply S V g.val z.val.val z.val.property (hWV z.property)] at hz
  exact hz

variable [IsManifold 𝓘(ℂ, E) ω M]

/-- Actual analytic chart representatives pull back to actual reduced
sections near the original point. -/
theorem chartStalkToImage_surjective : Function.Surjective (chartStalkToImage e he S x hx) := by
  intro φ
  obtain ⟨ψ, hψ⟩ := φ.property
  obtain ⟨F, hF, rfl⟩ := Germs.exists_representative ψ
  obtain ⟨U, hxU, f, hf⟩ := exists_reduced_section_of_chart_analyticAt e he S x hx hF
  refine ⟨(presheaf 𝓘(ℂ, E) S).germ U x hxU f, ?_⟩
  refine (chartStalkToImage_germ e he S x hx U hxU f).trans ?_
  apply Subtype.ext
  change (chartReducedRepresentative e S U f :
    Filter.Germ (𝓝[chartSubset e S] (e x.val)) ℂ) = φ.val
  exact (Filter.Germ.coe_eq.mpr hf).trans hψ

/-- The genuine categorical reduced stalk, expressed in the given
actual holomorphic chart, is the literal analytic restriction image. -/
def chartStalkEquiv : (presheaf 𝓘(ℂ, E) S).stalk x ≃+*
    RestrictedAnalyticGermImage (chartSubset e S) (chartPoint e S x hx) :=
  RingEquiv.ofBijective (chartStalkToImage e he S x hx)
    ⟨chartStalkToImage_injective e he S x hx, chartStalkToImage_surjective e he S x hx⟩

@[simp] theorem chartStalkEquiv_germ (U : Opens S) (hxU : x ∈ U)
    (f : Section 𝓘(ℂ, E) S U) :
    chartStalkEquiv e he S x hx ((presheaf 𝓘(ℂ, E) S).germ U x hxU f) =
      chartSectionGerm e he S x hx U hxU f := chartStalkToImage_germ e he S x hx U hxU f

/-- The comparison sends each actual represented sheaf germ to its
actual function expressed through the inverse chart. -/
@[simp] theorem chartStalkEquiv_germ_coe (U : Opens S) (hxU : x ∈ U)
    (f : Section 𝓘(ℂ, E) S U) :
    (chartStalkEquiv e he S x hx ((presheaf 𝓘(ℂ, E) S).germ U x hxU f)).val =
        (chartReducedRepresentative e S U f :
          Filter.Germ (𝓝[chartSubset e S] (e x.val)) ℂ) := by
  rw [chartStalkEquiv_germ]
  rfl

/-- The chart-stalk comparison commutes with actual ambient holomorphic
restriction and the actual inverse-chart analytic representative. -/
theorem chartStalkEquiv_ambient (V : Opens M) (hxV : x.val ∈ V)
    (g : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E) M V) :
    chartStalkEquiv e he S x hx ((presheaf 𝓘(ℂ, E) S).germ (ambientOpen S V) x hxV
      (ambientRestriction 𝓘(ℂ, E) S V g)) =
      (restrictAnalyticGerm (chartSubset e S) (chartPoint e S x hx)).rangeRestrict
        (Germs.ofAnalytic (chartAmbientRepresentative e V g)
          (chartAmbientRepresentative_analyticAt e he x.val hx V hxV g)) := by
  apply Subtype.ext
  refine (chartStalkEquiv_germ_coe e he S x hx (ambientOpen S V) hxV
    (ambientRestriction 𝓘(ℂ, E) S V g)).trans ?_
  change (chartReducedRepresentative e S (ambientOpen S V)
    (ambientRestriction 𝓘(ℂ, E) S V g) :
      Filter.Germ (𝓝[chartSubset e S] (e x.val)) ℂ) =
        (chartAmbientRepresentative e V g :
          Filter.Germ (𝓝[chartSubset e S] (e x.val)) ℂ)
  exact Filter.Germ.coe_eq.mpr
    (chartReducedRepresentative_ambientRestriction_eventuallyEq e S x hx V hxV g)

end Wikipedia.HopfProblem.CuspNormalization.SheafReduced
