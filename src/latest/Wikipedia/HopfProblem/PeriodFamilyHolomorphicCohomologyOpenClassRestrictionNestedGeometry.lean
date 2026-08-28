import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbedding

/-!
# Literal geometry and sheaf restriction for nested opens

For original opens `U ≤ W`, the inclusion is the actual map from `U`
to `W`, not an identification with a nested subtype. Its composite with
the original ambient inclusion is literally the inclusion of `U`.
The canonical open-embedding composition isomorphism therefore compares
the original restriction functors, with their actual ambient section maps.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open HolomorphicSheafCohomology

variable {X : TopCat.{0}} {U W Z : Opens X}

/-- The original inclusion between the two actual open subspaces. -/
def nestedInclusion (h : U ≤ W) : TopCat.of U ⟶ TopCat.of W :=
  TopCat.ofHom ⟨Opens.inclusion h, (Opens.isOpenEmbedding_of_le h).continuous⟩

@[simp] theorem nestedInclusion_apply (h : U ≤ W) (x : U) :
    nestedInclusion h x = Opens.inclusion h x := rfl

/-- This is the original functorial topological inclusion of opens. -/
theorem nestedInclusion_eq_toTopCat_map (h : U ≤ W) :
    nestedInclusion h = (Opens.toTopCat X).map (homOfLE h) := rfl

/-- The literal nested inclusion is genuinely an open embedding. -/
theorem nestedEmbedding (h : U ≤ W) : Topology.IsOpenEmbedding (nestedInclusion h) :=
  Opens.isOpenEmbedding_of_le h

/-- The inclusion square into the original ambient space commutes literally. -/
@[simp] theorem nestedInclusion_comp_inclusion (h : U ≤ W) :
    nestedInclusion h ≫ OpenRestriction.inclusion W = OpenRestriction.inclusion U := rfl

@[simp] theorem nestedInclusion_refl (U : Opens X) :
    nestedInclusion (le_refl U) = 𝟙 (TopCat.of U) := rfl

/-- Successive actual nested inclusions have the literal original composite. -/
@[simp] theorem nestedInclusion_trans (hUW : U ≤ W) (hWZ : W ≤ Z) :
    nestedInclusion hUW ≫ nestedInclusion hWZ = nestedInclusion (hUW.trans hWZ) := rfl

/-- The actual image in `W` of an original open in `U`. -/
abbrev nestedImageOpen (h : U ≤ W) (A : Opens U) : Opens W :=
  (Embedding.openImage (nestedInclusion h) (nestedEmbedding h)).obj A

/-- The image of the entire smaller open is its actual ambient inverse image in `W`. -/
theorem nestedImageOpen_top (h : U ≤ W) :
    nestedImageOpen h ⊤ = OpenRestriction.preimageOpen W U := by
  apply Opens.ext
  ext x
  constructor
  · rintro ⟨y, _, rfl⟩
    exact y.property
  · intro hx
    refine ⟨⟨x.val, hx⟩, trivial, ?_⟩
    exact Subtype.ext rfl

/-- Taking the two actual images gives the original image in the ambient space. -/
theorem nestedImageOpen_ambient (h : U ≤ W) (A : Opens U) :
    (OpenRestriction.openImage W).obj (nestedImageOpen h A) =
      (OpenRestriction.openImage U).obj A :=
  Embedding.openImage_comp_obj (OpenRestriction.inclusion W)
    (OpenRestriction.inclusion_isOpenEmbedding W) (nestedInclusion h) (nestedEmbedding h) A

/-- The original image-open functors themselves compose by the literal inclusion. -/
theorem nestedOpenImage_comp (h : U ≤ W) :
    Embedding.openImage (nestedInclusion h) (nestedEmbedding h) ⋙ OpenRestriction.openImage W =
      OpenRestriction.openImage U :=
  Embedding.openImage_comp (OpenRestriction.inclusion W)
    (OpenRestriction.inclusion_isOpenEmbedding W) (nestedInclusion h) (nestedEmbedding h)

/-- The original ambient restriction followed by actual `U → W` restriction
is canonically the original restriction to `U`. -/
def nestedRestrictionIso (h : U ≤ W) :
    OpenRestriction.restriction W ⋙
        Embedding.restriction (nestedInclusion h) (nestedEmbedding h) ≅
      OpenRestriction.restriction U :=
  Embedding.restrictionCompIso (OpenRestriction.inclusion W)
    (OpenRestriction.inclusion_isOpenEmbedding W) (nestedInclusion h) (nestedEmbedding h)

/-- On every original open of `U`, the forward comparison uses the original
ambient sheaf map along the actual equality of image opens. -/
@[simp] theorem nestedRestrictionIso_hom_app (h : U ≤ W)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (A : Opens U) :
    ((nestedRestrictionIso h).hom.app F).hom.app (op A) =
      F.obj.map (eqToHom (nestedImageOpen_ambient h A).symm).op :=
  Embedding.restrictionCompIso_hom_app (OpenRestriction.inclusion W)
    (OpenRestriction.inclusion_isOpenEmbedding W) (nestedInclusion h) (nestedEmbedding h) F A

/-- The inverse comparison uses the same original ambient sheaf and the
opposite equality map, again on every original open of `U`. -/
@[simp] theorem nestedRestrictionIso_inv_app (h : U ≤ W)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (A : Opens U) :
    ((nestedRestrictionIso h).inv.app F).hom.app (op A) =
      F.obj.map (eqToHom (nestedImageOpen_ambient h A)).op :=
  Embedding.restrictionCompIso_inv_app (OpenRestriction.inclusion W)
    (OpenRestriction.inclusion_isOpenEmbedding W) (nestedInclusion h) (nestedEmbedding h) F A

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
