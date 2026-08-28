import Wikipedia.NoExoticSixSphere.SimplicialCoefficientChains
import Wikipedia.NoExoticSixSphere.RelativeCoefficientPairMaps

/-!
# The actual singular subcomplex of a subset

The range of the native singular-set inclusion consists exactly of the
singular simplices whose image lies in the subset. Intersections of subsets
therefore give intersections of these actual subcomplexes. No topological
union or excision assertion is used in this identification.
-/

noncomputable section

open CategoryTheory Limits Simplicial
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.SingularSubcomplex

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

abbrev singular (X : Type) [TopologicalSpace X] : SSet.{0} := TopCat.toSSet.obj (TopCat.of X)

/-- The literal singular simplicial-set map of the original subtype inclusion. -/
abbrev inclusion (U : Set X) : singular U ⟶ singular X :=
  TopCat.toSSet.map (TopCat.ofHom (subtypeInclusion U))

instance inclusion_mono (U : Set X) : Mono (inclusion U) := by
  have : Mono (TopCat.ofHom (subtypeInclusion U)) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  exact inferInstanceAs (Mono (TopCat.toSSet.map (TopCat.ofHom (subtypeInclusion U))))

/-- All actual singular simplices lying in the specified subset. -/
abbrev support (U : Set X) : (singular X).Subcomplex := SSet.Subcomplex.range (inclusion U)

/-- The native singular set of the subspace is isomorphic to its actual range subcomplex. -/
def supportIso (U : Set X) : singular U ≅ (support U : SSet) :=
  asIso (SSet.Subcomplex.toRange (inclusion U))

@[reassoc]
theorem supportIso_hom_inclusion (U : Set X) :
    (supportIso U).hom ≫ (support U).ι = inclusion U := rfl

/-- The standard simplex identification retains the original continuous postcomposition. -/
theorem simplexMap_naturality (f : C(X, Y)) (n : SimplexCategoryᵒᵖ)
    (s : (singular X).obj n) :
    (TopCat.of Y).toSSetObjEquiv n ((TopCat.toSSet.map (TopCat.ofHom f)).app n s) =
      f.comp ((TopCat.of X).toSSetObjEquiv n s) := rfl

/-- Membership in the actual range subcomplex is exactly geometric simplex support. -/
theorem mem_support_iff (U : Set X) (n : SimplexCategoryᵒᵖ) (s : (singular X).obj n) :
    s ∈ (support U).obj n ↔ Set.range ((TopCat.of X).toSSetObjEquiv n s) ⊆ U := by
  change (∃ t, (inclusion U).app n t = s) ↔ _
  constructor
  · rintro ⟨t, rfl⟩
    rw [simplexMap_naturality]
    rintro x ⟨p, rfl⟩
    exact (((TopCat.of U).toSSetObjEquiv n t) p).property
  · intro hs
    let f := (TopCat.of X).toSSetObjEquiv n s
    let g : C(stdSimplex ℝ (Fin (n.unop.len + 1)), U) :=
      ⟨fun p => ⟨f p, hs ⟨p, rfl⟩⟩, f.continuous.subtype_mk _⟩
    refine ⟨((TopCat.of U).toSSetObjEquiv n).symm g, ?_⟩
    apply ((TopCat.of X).toSSetObjEquiv n).injective
    rw [simplexMap_naturality, Equiv.apply_symm_apply]
    ext p
    rfl

theorem support_inter (U V : Set X) : support (U ∩ V) = support U ⊓ support V := by
  apply Subfunctor.ext
  funext n
  ext s
  change s ∈ (support (U ∩ V)).obj n ↔ s ∈ (support U).obj n ∩ (support V).obj n
  simp only [Set.mem_inter_iff, mem_support_iff, Set.subset_inter_iff]

theorem support_mono {U V : Set X} (h : U ⊆ V) : support U ≤ support V := by
  intro n s hs
  exact (mem_support_iff V n s).mpr (((mem_support_iff U n s).mp hs).trans h)

end NoExoticSixSphere.SingularSubcomplex
