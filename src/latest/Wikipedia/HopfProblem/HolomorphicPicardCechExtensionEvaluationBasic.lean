import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionMaps

/-!
# Literal intersection sheaves and extension coordinates

For an actual additive sheaf `F` and an open set `W`, the sections of
the intersection sheaf on `V` are literally `F(V ⊓ W)`. Its sheaf
condition is proved by gluing the actual sections on the intersections
of a covering family with `W`. The coordinate maps of the cocycle
extension are genuine presheaf maps into these sheaves.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}}

/-- The presheaf whose sections are literally sections on intersection
with the specified open set. -/
def intersectionPresheaf (F : TopCat.Sheaf AddCommGrpCat.{0} X) (W : Opens X) :
    TopCat.Presheaf AddCommGrpCat.{0} X where
  obj V := F.obj.obj (op (V.unop ⊓ W))
  map f := F.obj.map (homOfLE (inf_le_inf_right W (leOfHom f.unop))).op
  map_id V := by
    apply ConcreteCategory.hom_ext
    intro s
    exact res_refl F (V.unop ⊓ W) s
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (res_trans F _ _ s).symm

@[simp] theorem intersectionPresheaf_map
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (W : Opens X)
    {V T : Opens X} (hTV : T ≤ V) (s : Section F (V ⊓ W)) :
    (intersectionPresheaf F W).map (homOfLE hTV).op s =
      res F (inf_le_inf_right W hTV) s := rfl

/-- Actual gluing in `F` proves the sheaf condition for the literal
intersection presheaf. -/
theorem intersectionPresheaf_isSheaf
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (W : Opens X) :
    (intersectionPresheaf F W).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro ι V sf hsf
  have hcompat : TopCat.Presheaf.IsCompatible F.obj (fun i : ι => V i ⊓ W) sf := by
    intro i j
    change res F inf_le_left (sf i) = res F inf_le_right (sf j)
    have hij := hsf i j
    change res F (inf_le_inf_right W (show V i ⊓ V j ≤ V i from inf_le_left)) (sf i) =
      res F (inf_le_inf_right W (show V i ⊓ V j ≤ V j from inf_le_right)) (sf j) at hij
    have hcommon : (V i ⊓ W) ⊓ (V j ⊓ W) ≤ (V i ⊓ V j) ⊓ W := by
      intro x hx
      exact ⟨⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
    have h := congrArg (res F hcommon) hij
    exact (res_trans F _ hcommon (sf i)).symm.trans
      (h.trans (res_trans F _ hcommon (sf j)))
  have hcover : (⨆ i : ι, V i) ⊓ W ≤ ⨆ i : ι, V i ⊓ W := by
    intro x hx
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx.1
    exact Opens.mem_iSup.mpr ⟨i, hxi, hx.2⟩
  obtain ⟨s, hs, huniq⟩ := F.existsUnique_gluing' (fun i : ι => V i ⊓ W)
    ((⨆ i : ι, V i) ⊓ W)
    (fun i => homOfLE (inf_le_inf_right W (le_iSup V i))) hcover sf hcompat
  exact ⟨s, hs, huniq⟩

/-- The genuine sheaf with literal sections `F(V ⊓ W)`. -/
def intersectionSheaf (F : TopCat.Sheaf AddCommGrpCat.{0} X) (W : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{0} X :=
  ⟨intersectionPresheaf F W, intersectionPresheaf_isSheaf F W⟩

@[simp] theorem intersectionSheaf_restrict
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (W : Opens X)
    {V T : Opens X} (hTV : T ≤ V) (s : Section F (V ⊓ W)) :
    res (intersectionSheaf F W) hTV s = res F (inf_le_inf_right W hTV) s := rfl

/-- The actual restriction map from `F` to sections on intersection
with `W`, as a morphism of sheaves. -/
def intersectionRestriction (F : TopCat.Sheaf AddCommGrpCat.{0} X) (W : Opens X) :
    F ⟶ intersectionSheaf F W where
  hom := {
    app V := F.obj.map (homOfLE (show V.unop ⊓ W ≤ V.unop from inf_le_left)).op
    naturality V T f := by
      apply ConcreteCategory.hom_ext
      intro s
      change res F _ (res F _ s) = res F _ (res F _ s)
      rw [res_trans, res_trans] }

@[simp] theorem intersectionRestriction_app
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (W V : Opens X) (s : Section F V) :
    (intersectionRestriction F W).hom.app (op V) s = res F inf_le_left s := rfl

variable {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U)

/-- Literal evaluation at a local coordinate is a natural presheaf
map into the actual intersection sheaf. -/
def evaluationPre (i : ι) : presheaf c ⟶ (intersectionSheaf F (U i)).obj where
  app V := AddCommGrpCat.ofHom (coordinateHom c V.unop i)
  naturality V T f := by
    apply ConcreteCategory.hom_ext
    intro s
    rfl

@[simp] theorem evaluationPre_app (i : ι) (V : Opens X) (s : ExtensionSection c V) :
    (evaluationPre c i).app (op V) s = coordinateHom c V i s := rfl

/-- On the original sheaf, evaluating the included family is precisely
the original restriction map. -/
theorem inclusionPre_evaluationPre (i : ι) :
    inclusionPre c ≫ evaluationPre c i = (intersectionRestriction F (U i)).hom := by
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro s
  rfl

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
