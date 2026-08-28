import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenRestrictionExact
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Cech
import Mathlib.Topology.Sheaves.Functors

/-!
# Literal restriction along an actual open embedding

The image-open functor sends an original open to its actual image.
The restricted sheaf is literal precomposition by this functor, with
the original ambient sections and restriction maps. For an original
open-subspace inclusion this is the existing open restriction itself.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction.Embedding

open HolomorphicFunctionSheaf.SphereH1 HolomorphicSheafCohomology

variable {T X : TopCat.{0}} (f : T ⟶ X) (hf : Topology.IsOpenEmbedding f)

/-- The functor of actual image opens under the given open embedding. -/
abbrev openImage : Opens T ⥤ Opens X := hf.functor

/-- The literal inverse image of an original ambient open. -/
abbrev preimageOpen (V : Opens X) : Opens T := (Opens.map f).obj V

@[simp] theorem mem_openImage_obj (V : Opens T) (x : X) :
    x ∈ (openImage f hf).obj V ↔ ∃ t : T, t ∈ V ∧ f t = x := Iff.rfl

@[simp] theorem mem_preimageOpen (V : Opens X) (t : T) :
    t ∈ preimageOpen f V ↔ f t ∈ V := Iff.rfl

/-- The actual image of an inverse image stays in the original open. -/
theorem imagePreimage_le (V : Opens X) :
    (openImage f hf).obj (preimageOpen f V) ≤ V := by
  rintro x ⟨t, ht, rfl⟩
  exact ht

/-- Injectivity gives the original domain inclusion when an ambient
open lies in the actual image of a domain open. -/
theorem preimage_le_of_le_image {V : Opens X} {W : Opens T}
    (h : V ≤ (openImage f hf).obj W) : preimageOpen f V ≤ W := by
  intro t ht
  obtain ⟨s, hs, hst⟩ := h ht
  exact hf.injective hst ▸ hs

/-- The actual image-open functor is continuous as a functor of sites. -/
instance openImage_continuous :
    (openImage f hf).IsContinuous (Opens.grothendieckTopology T)
      (Opens.grothendieckTopology X) := hf.functor_isContinuous

/-- Restriction is the actual precomposition functor on original abelian sheaves. -/
abbrev restriction : TopCat.Sheaf AddCommGrpCat.{0} X ⥤ TopCat.Sheaf AddCommGrpCat.{0} T :=
  (openImage f hf).sheafPushforwardContinuous AddCommGrpCat
    (Opens.grothendieckTopology T) (Opens.grothendieckTopology X)

/-- This is also Mathlib's original naive pullback for an open embedding. -/
theorem restriction_eq_sheafPullback : restriction f hf = hf.sheafPullback AddCommGrpCat := rfl

/-- The section object is literally the original ambient section object. -/
theorem restriction_obj_obj (F : TopCat.Sheaf AddCommGrpCat.{0} X) (V : Opens T) :
    ((restriction f hf).obj F).obj.obj (op V) =
      F.obj.obj (op ((openImage f hf).obj V)) := rfl

/-- Restriction of a section uses the same original ambient restriction map. -/
theorem restriction_res (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {V W : Opens T} (h : V ≤ W) (s : Section ((restriction f hf).obj F) W) :
    res ((restriction f hf).obj F) h s =
      res F ((openImage f hf).map (homOfLE h)).le s := rfl

/-- Coefficient morphisms act by their original components on image opens. -/
@[simp] theorem restriction_map_app {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (φ : F ⟶ G) (V : Opens T) (s : Section F ((openImage f hf).obj V)) :
    ((restriction f hf).map φ).hom.app (op V) s =
      φ.hom.app (op ((openImage f hf).obj V)) s := rfl

instance restriction_additive : (restriction f hf).Additive where
  map_add := by intros; rfl

/-- For the actual inclusion of an open subspace, the image functor
is exactly the original image-open functor. -/
theorem openImage_inclusion (A : Opens X) :
    openImage (OpenRestriction.inclusion A) (OpenRestriction.inclusion_isOpenEmbedding A) =
      OpenRestriction.openImage A := rfl

/-- For the original open-subspace inclusion there is no replacement
restriction functor: the two constructions are definitionally equal. -/
theorem restriction_inclusion (A : Opens X) :
    restriction (OpenRestriction.inclusion A) (OpenRestriction.inclusion_isOpenEmbedding A) =
      OpenRestriction.restriction A := rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction.Embedding
