import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbeddingBasic

/-!
# Composition of literal open-embedding restriction

Images under two original open embeddings agree with the image under
their actual composite. This equality of image-open functors induces the
canonical composition isomorphism of the original sheaf restrictions.
Its components are the original ambient sheaf maps along that equality.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction.Embedding

variable {S T X : TopCat.{0}}

/-- The iterated actual image is the actual image under the composite. -/
theorem openImage_comp_obj (f : T ⟶ X) (hf : Topology.IsOpenEmbedding f)
    (g : S ⟶ T) (hg : Topology.IsOpenEmbedding g) (V : Opens S) :
    (openImage f hf).obj ((openImage g hg).obj V) =
      (openImage (g ≫ f) (hf.comp hg)).obj V := by
  apply Opens.ext
  exact Set.image_image f g (V : Set S)

/-- Literal image-open functors compose by taking the original composite map. -/
theorem openImage_comp (f : T ⟶ X) (hf : Topology.IsOpenEmbedding f)
    (g : S ⟶ T) (hg : Topology.IsOpenEmbedding g) :
    openImage g hg ⋙ openImage f hf = openImage (g ≫ f) (hf.comp hg) :=
  CategoryTheory.Functor.ext (openImage_comp_obj f hf g hg)
    (fun _ _ _ => Subsingleton.elim _ _)

/-- The genuine canonical composition isomorphism for literal restriction. -/
def restrictionCompIso (f : T ⟶ X) (hf : Topology.IsOpenEmbedding f)
    (g : S ⟶ T) (hg : Topology.IsOpenEmbedding g) :
    restriction f hf ⋙ restriction g hg ≅ restriction (g ≫ f) (hf.comp hg) :=
  Functor.sheafPushforwardContinuousComp' (eqToIso (openImage_comp f hf g hg))
    AddCommGrpCat (Opens.grothendieckTopology S) (Opens.grothendieckTopology T)
      (Opens.grothendieckTopology X)

/-- The forward component uses the original ambient section map along
the equality of the composite image and the iterated image. -/
@[simp] theorem restrictionCompIso_hom_app (f : T ⟶ X) (hf : Topology.IsOpenEmbedding f)
    (g : S ⟶ T) (hg : Topology.IsOpenEmbedding g)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (V : Opens S) :
    ((restrictionCompIso f hf g hg).hom.app F).hom.app (op V) =
      F.obj.map (eqToHom (openImage_comp_obj f hf g hg V).symm).op := by
  exact (CategoryTheory.Functor.sheafPushforwardContinuousComp'_hom_app_hom_app
    (eqToIso (openImage_comp f hf g hg)) AddCommGrpCat
    (Opens.grothendieckTopology S) (Opens.grothendieckTopology T)
    (Opens.grothendieckTopology X) F (op V)).trans
      (congrArg F.obj.map (Subsingleton.elim _ _))

/-- The inverse component is the opposite equality map in the same
original ambient sheaf. -/
@[simp] theorem restrictionCompIso_inv_app (f : T ⟶ X) (hf : Topology.IsOpenEmbedding f)
    (g : S ⟶ T) (hg : Topology.IsOpenEmbedding g)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (V : Opens S) :
    ((restrictionCompIso f hf g hg).inv.app F).hom.app (op V) =
      F.obj.map (eqToHom (openImage_comp_obj f hf g hg V)).op := by
  exact (CategoryTheory.Functor.sheafPushforwardContinuousComp'_inv_app_hom_app
    (eqToIso (openImage_comp f hf g hg)) AddCommGrpCat
    (Opens.grothendieckTopology S) (Opens.grothendieckTopology T)
    (Opens.grothendieckTopology X) F (op V)).trans
      (congrArg F.obj.map (Subsingleton.elim _ _))

/-- The actual identity map leaves every original open unchanged. -/
theorem openImage_id_obj (X : TopCat.{0}) (V : Opens X) :
    (openImage (𝟙 X) Topology.IsOpenEmbedding.id).obj V = V := by
  apply Opens.ext
  exact Set.image_id (V : Set X)

/-- The literal image-open functor of the identity is the identity functor. -/
theorem openImage_id (X : TopCat.{0}) :
    openImage (𝟙 X) Topology.IsOpenEmbedding.id = 𝟭 (Opens X) :=
  CategoryTheory.Functor.ext (openImage_id_obj X) (fun _ _ _ => Subsingleton.elim _ _)

/-- Restriction along the original identity map identifies canonically
with the original sheaf itself. -/
def restrictionIdIso (X : TopCat.{0}) :
    restriction (𝟙 X) Topology.IsOpenEmbedding.id ≅
      𝟭 (TopCat.Sheaf AddCommGrpCat.{0} X) := by
  letI := openImage_continuous (𝟙 X) Topology.IsOpenEmbedding.id
  exact Functor.sheafPushforwardContinuousId' (eqToIso (openImage_id X))
    AddCommGrpCat (Opens.grothendieckTopology X)

/-- The identity comparison acts by the original ambient equality map. -/
@[simp] theorem restrictionIdIso_hom_app (X : TopCat.{0})
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (V : Opens X) :
    ((restrictionIdIso X).hom.app F).hom.app (op V) =
      F.obj.map (eqToHom (openImage_id_obj X V).symm).op := by
  let := openImage_continuous (𝟙 X) Topology.IsOpenEmbedding.id
  exact (CategoryTheory.Functor.sheafPushforwardContinuousId'_hom_app_hom_app
    (eqToIso (openImage_id X)) AddCommGrpCat (Opens.grothendieckTopology X) F (op V)).trans
      (congrArg F.obj.map (Subsingleton.elim _ _))

/-- The inverse identity comparison uses the original reverse equality map. -/
@[simp] theorem restrictionIdIso_inv_app (X : TopCat.{0})
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (V : Opens X) :
    ((restrictionIdIso X).inv.app F).hom.app (op V) =
      F.obj.map (eqToHom (openImage_id_obj X V)).op := by
  let := openImage_continuous (𝟙 X) Topology.IsOpenEmbedding.id
  exact (CategoryTheory.Functor.sheafPushforwardContinuousId'_inv_app_hom_app
    (eqToIso (openImage_id X)) AddCommGrpCat (Opens.grothendieckTopology X) F (op V)).trans
      (congrArg F.obj.map (Subsingleton.elim _ _))

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction.Embedding
