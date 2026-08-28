import Wikipedia.HopfProblem.HolomorphicFunctionSheafBasic
import Wikipedia.HopfProblem.HolomorphicFunctionSheafStalkSections
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Topology.Sheaves.Stalks

/-!
# The categorical holomorphic stalk is the ring of actual analytic germs

The stalk used here is mathlib's colimit of the actual ring presheaf over
open neighbourhoods.  A holomorphic section determines its ordinary
neighbourhood germ, independently of the values of its extension outside
its domain.  This compatible family gives a ring map out of the colimit.

Equality of ordinary germs is exactly equality after restricting sections
to a smaller open neighbourhood; every analytic germ has such a section
representative.  These two facts prove that the colimit map is a ring
isomorphism, with an explicit formula on the canonical germ maps.
-/

noncomputable section

open Set Filter Topology TopologicalSpace Opposite CategoryTheory Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf

open CuspNormalization

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A genuine holomorphic section gives its actual analytic neighbourhood
germ at any point of its domain. -/
def modelSectionGerm (a : E) (U : Opens E) (ha : a ∈ U) :
    Section 𝓘(ℂ, E) E U →+* Germs.AnalyticGerm a where
  toFun f := Germs.ofAnalytic (extendSection U f)
    (extendSection_analyticAt U f a ha)
  map_zero' := by
    apply Germs.ext
    change (extendSection U 0 : Filter.Germ (𝓝 a) ℂ) =
      ((fun _ : E => (0 : ℂ)) : Filter.Germ (𝓝 a) ℂ)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [U.isOpen.mem_nhds ha] with x hx
    rw [extendSection_apply U 0 x hx]
    rfl
  map_one' := by
    apply Germs.ext
    change (extendSection U 1 : Filter.Germ (𝓝 a) ℂ) =
      ((fun _ : E => (1 : ℂ)) : Filter.Germ (𝓝 a) ℂ)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [U.isOpen.mem_nhds ha] with x hx
    rw [extendSection_apply U 1 x hx]
    rfl
  map_add' f g := by
    apply Germs.ext
    change (extendSection U (f + g) : Filter.Germ (𝓝 a) ℂ) =
      ((fun x => extendSection U f x + extendSection U g x) : Filter.Germ (𝓝 a) ℂ)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [U.isOpen.mem_nhds ha] with x hx
    rw [extendSection_apply U (f + g) x hx, extendSection_apply U f x hx,
      extendSection_apply U g x hx]
    rfl
  map_mul' f g := by
    apply Germs.ext
    change (extendSection U (f * g) : Filter.Germ (𝓝 a) ℂ) =
      ((fun x => extendSection U f x * extendSection U g x) : Filter.Germ (𝓝 a) ℂ)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [U.isOpen.mem_nhds ha] with x hx
    rw [extendSection_apply U (f * g) x hx, extendSection_apply U f x hx,
      extendSection_apply U g x hx]
    rfl

@[simp] theorem modelSectionGerm_apply (a : E) (U : Opens E) (ha : a ∈ U)
    (f : Section 𝓘(ℂ, E) E U) :
    modelSectionGerm a U ha f = Germs.ofAnalytic (extendSection U f)
      (extendSection_analyticAt U f a ha) := rfl

/-- Comparing section germs is comparing their actual functions near the point. -/
theorem modelSectionGerm_eq_iff (a : E) (U V : Opens E) (haU : a ∈ U) (haV : a ∈ V)
    (f : Section 𝓘(ℂ, E) E U) (g : Section 𝓘(ℂ, E) E V) :
    modelSectionGerm a U haU f = modelSectionGerm a V haV g ↔
      extendSection U f =ᶠ[𝓝 a] extendSection V g :=
  Germs.ofAnalytic_eq_iff _ _ (extendSection_analyticAt U f a haU)
    (extendSection_analyticAt V g a haV)

/-- Literal restriction does not change the actual analytic germ. -/
theorem modelSectionGerm_restrict (a : E) (U V : Opens E) (h : U ≤ V) (ha : a ∈ U)
    (f : Section 𝓘(ℂ, E) E V) :
    modelSectionGerm a U ha ((presheaf 𝓘(ℂ, E) E).map (homOfLE h).op f) =
      modelSectionGerm a V (h ha) f := by
  apply (modelSectionGerm_eq_iff _ _ _ _ _ _ _).mpr
  filter_upwards [U.isOpen.mem_nhds ha] with x hx
  change extendSection U (ContMDiffMap.restrictRingHom 𝓘(ℂ, E) 𝓘(ℂ) ℂ h f) x =
    extendSection V f x
  rw [extendSection_apply U _ x hx, extendSection_apply V f x (h hx)]
  rfl

/-- The compatible family of actual analytic-germ maps on the genuine
open-neighbourhood diagram. -/
def modelStalkCocone (a : E) :
    Cocone ((OpenNhds.inclusion (X := TopCat.of E) a).op ⋙ presheaf 𝓘(ℂ, E) E) where
  pt := CommRingCat.of (Germs.AnalyticGerm a)
  ι :=
    { app := fun U => CommRingCat.ofHom
        (modelSectionGerm a U.unop.1 U.unop.2)
      naturality := by
        intro U V i
        ext f
        exact modelSectionGerm_restrict a V.unop.1 U.unop.1
          (leOfHom i.unop) V.unop.2 f }

/-- The comparison morphism is defined by the actual stalk colimit's
universal property in the category of commutative rings. -/
def modelStalkToAnalyticGermHom (a : E) :
    (presheaf 𝓘(ℂ, E) E).stalk a ⟶ CommRingCat.of (Germs.AnalyticGerm a) :=
  colimit.desc _ (modelStalkCocone a)

/-- The ring map underlying the categorical colimit comparison. -/
def modelStalkToAnalyticGerm (a : E) :
    (presheaf 𝓘(ℂ, E) E).stalk a →+* Germs.AnalyticGerm a :=
  (modelStalkToAnalyticGermHom a).hom

/-- The universal-property comparison computes on each canonical
categorical germ as the actual neighbourhood germ of the section. -/
@[simp] theorem modelStalkToAnalyticGerm_germ (a : E) (U : Opens E) (ha : a ∈ U)
    (f : Section 𝓘(ℂ, E) E U) :
    modelStalkToAnalyticGerm a ((presheaf 𝓘(ℂ, E) E).germ U a ha f) =
      modelSectionGerm a U ha f := by
  exact congrArg (fun h => h f)
    (colimit.ι_desc (modelStalkCocone a) (op ⟨U, ha⟩))

/-- Equal analytic germs become equal after a genuine smaller-open
restriction, hence already define the same element of the categorical stalk. -/
theorem modelStalkToAnalyticGerm_injective (a : E) :
    Function.Injective (modelStalkToAnalyticGerm a) := by
  intro x y hxy
  obtain ⟨U, haU, f, rfl⟩ := (presheaf 𝓘(ℂ, E) E).exists_germ_eq x
  obtain ⟨V, haV, g, rfl⟩ := (presheaf 𝓘(ℂ, E) E).exists_germ_eq y
  have hfg : modelSectionGerm a U haU f = modelSectionGerm a V haV g :=
    (modelStalkToAnalyticGerm_germ a U haU f).symm.trans
      (hxy.trans (modelStalkToAnalyticGerm_germ a V haV g))
  have he := (modelSectionGerm_eq_iff a U V haU haV f g).mp hfg
  have hnbhd : {z : E | z ∈ U ∧ z ∈ V ∧ extendSection U f z =
      extendSection V g z} ∈ 𝓝 a :=
    inter_mem (U.isOpen.mem_nhds haU) (inter_mem (V.isOpen.mem_nhds haV) he)
  obtain ⟨W, hW, hWo, haW⟩ := mem_nhds_iff.mp hnbhd
  let W' : Opens E := ⟨W, hWo⟩
  have hWU : W' ≤ U := fun z hz => (hW hz).1
  have hWV : W' ≤ V := fun z hz => (hW hz).2.1
  apply (presheaf 𝓘(ℂ, E) E).germ_ext W' haW (homOfLE hWU) (homOfLE hWV)
  apply ContMDiffMap.ext
  intro z
  have hz := (hW z.property).2.2
  rw [extendSection_apply U f z (hWU z.property),
    extendSection_apply V g z (hWV z.property)] at hz
  exact hz

/-- Every actual analytic neighbourhood germ comes from a holomorphic
section on a sufficiently small open neighbourhood. -/
theorem modelStalkToAnalyticGerm_surjective (a : E) :
    Function.Surjective (modelStalkToAnalyticGerm a) := by
  intro φ
  obtain ⟨f, hf, rfl⟩ := Germs.exists_representative φ
  obtain ⟨U, ha, s, hs⟩ := exists_section_of_analyticAt hf
  refine ⟨(presheaf 𝓘(ℂ, E) E).germ U a ha s, ?_⟩
  rw [modelStalkToAnalyticGerm_germ]
  apply (Germs.ofAnalytic_eq_iff _ _ (extendSection_analyticAt U s a ha) hf).mpr
  filter_upwards [U.isOpen.mem_nhds ha] with z hz
  exact (extendSection_apply U s z hz).trans (hs z hz)

/-- The stalk of the actual holomorphic ring sheaf, defined as a
categorical colimit, is the ring of actual analytic neighbourhood germs. -/
def modelStalkEquiv (a : E) :
    (presheaf 𝓘(ℂ, E) E).stalk a ≃+* Germs.AnalyticGerm a :=
  RingEquiv.ofBijective (modelStalkToAnalyticGerm a)
    ⟨modelStalkToAnalyticGerm_injective a, modelStalkToAnalyticGerm_surjective a⟩

@[simp] theorem modelStalkEquiv_germ (a : E) (U : Opens E) (ha : a ∈ U)
    (f : Section 𝓘(ℂ, E) E U) :
    modelStalkEquiv a ((presheaf 𝓘(ℂ, E) E).germ U a ha f) =
      Germs.ofAnalytic (extendSection U f) (extendSection_analyticAt U f a ha) :=
  modelStalkToAnalyticGerm_germ a U ha f

/-- Evaluating an actual sheaf germ agrees with the value of every
section representing it. -/
@[simp] theorem eval_modelStalkEquiv_germ (a : E) (U : Opens E) (ha : a ∈ U)
    (f : Section 𝓘(ℂ, E) E U) :
    Germs.eval a (modelStalkEquiv a ((presheaf 𝓘(ℂ, E) E).germ U a ha f)) =
      f ⟨a, ha⟩ := by
  rw [modelStalkEquiv_germ, Germs.eval_ofAnalytic, extendSection_apply U f a ha]

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf
