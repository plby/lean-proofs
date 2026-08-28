import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionSheafBasic
import Wikipedia.HopfProblem.HolomorphicPicardCechSheafMap

/-!
# Maps of genuine Čech extensions induced by sheaf morphisms

An actual map of additive sheaves acts on compatible extension data
by preserving the lifted integer and applying its section maps to all
local coordinates. This induces a map of the genuine sheafifications,
with the original sheaf map and the identity as its endpoint maps.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X}

/-- Apply the actual sheaf morphism to every local coordinate, while
preserving the lifted integer coordinate. -/
def mapSectionHom (f : F ⟶ G) (c : CechOneCocycle F U) (V : Opens X) :
    ExtensionSection c V →+ ExtensionSection (Cech.mapCocycle f c) V where
  toFun s := ⟨⟨s.1.1, fun i => f.hom.app (op (V ⊓ U i)) (s.1.2 i)⟩, by
    intro i j
    change res G _ (f.hom.app _ (s.1.2 i)) - res G _ (f.hom.app _ (s.1.2 j)) =
      s.1.1.down • res G _ ((Cech.mapCocycle f c).value i j)
    rw [res_map, res_map, Cech.mapCocycle_value, res_map,
      ← map_sub, ← map_zsmul, s.2 i j]⟩
  map_zero' := by
    apply extensionSection_ext
    · rfl
    · intro i
      exact map_zero _
  map_add' s t := by
    apply extensionSection_ext
    · rfl
    · intro i
      exact map_add _ _ _

@[simp] theorem mapSectionHom_degree (f : F ⟶ G) (c : CechOneCocycle F U)
    (V : Opens X) (s : ExtensionSection c V) :
    degreeHom (Cech.mapCocycle f c) V (mapSectionHom f c V s) = degreeHom c V s := rfl

@[simp] theorem mapSectionHom_coordinate (f : F ⟶ G) (c : CechOneCocycle F U)
    (V : Opens X) (i : ι) (s : ExtensionSection c V) :
    coordinateHom (Cech.mapCocycle f c) V i (mapSectionHom f c V s) =
      f.hom.app (op (V ⊓ U i)) (coordinateHom c V i s) := rfl

theorem restrict_mapSectionHom (f : F ⟶ G) (c : CechOneCocycle F U)
    {V W : Opens X} (hWV : W ≤ V) (s : ExtensionSection c V) :
    restrict (Cech.mapCocycle f c) hWV (mapSectionHom f c V s) =
      mapSectionHom f c W (restrict c hWV s) := by
  apply extensionSection_ext
  · rfl
  · intro i
    exact res_map f (inf_le_inf_right (U i) hWV) (s.1.2 i)

@[simp] theorem mapSectionHom_includeHom (f : F ⟶ G) (c : CechOneCocycle F U)
    (V : Opens X) (a : Section F V) :
    mapSectionHom f c V (includeHom c V a) =
      includeHom (Cech.mapCocycle f c) V (f.hom.app (op V) a) := by
  apply extensionSection_ext
  · rfl
  · intro i
    exact (res_map f inf_le_left a).symm

/-- The actual map of compatible-data presheaves induced by a sheaf map. -/
def mapPre (f : F ⟶ G) (c : CechOneCocycle F U) :
    presheaf c ⟶ presheaf (Cech.mapCocycle f c) where
  app V := AddCommGrpCat.ofHom (mapSectionHom f c V.unop)
  naturality V W h := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (restrict_mapSectionHom f c (leOfHom h.unop) s).symm

@[simp] theorem mapPre_app (f : F ⟶ G) (c : CechOneCocycle F U)
    (V : Opens X) (s : ExtensionSection c V) :
    (mapPre f c).app (op V) s = mapSectionHom f c V s := rfl

theorem inclusionPre_mapPre (f : F ⟶ G) (c : CechOneCocycle F U) :
    inclusionPre c ≫ mapPre f c = f.hom ≫ inclusionPre (Cech.mapCocycle f c) := by
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro a
  exact mapSectionHom_includeHom f c V.unop a

theorem mapPre_projectionPre (f : F ⟶ G) (c : CechOneCocycle F U) :
    mapPre f c ≫ projectionPre (Cech.mapCocycle f c) = projectionPre c := by
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- The genuine sheaf map obtained by actual sheafification of the
coordinatewise map of compatible-data presheaves. -/
def map (f : F ⟶ G) (c : CechOneCocycle F U) :
    extensionSheaf c ⟶ extensionSheaf (Cech.mapCocycle f c) where
  hom := CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) (mapPre f c)

theorem unit_map (f : F ⟶ G) (c : CechOneCocycle F U) :
    unit c ≫ (map f c).hom = mapPre f c ≫ unit (Cech.mapCocycle f c) :=
  (CategoryTheory.toSheafify_naturality
    (Opens.grothendieckTopology X) (mapPre f c)).symm

@[simp] theorem map_app_unit (f : F ⟶ G) (c : CechOneCocycle F U)
    (V : Opens X) (s : ExtensionSection c V) :
    (map f c).hom.app (op V) ((unit c).app (op V) s) =
      (unit (Cech.mapCocycle f c)).app (op V) (mapSectionHom f c V s) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (unit_map f c) (op V)) s

/-- The left endpoint square commutes with the given sheaf morphism. -/
theorem inclusion_map (f : F ⟶ G) (c : CechOneCocycle F U) :
    inclusion c ≫ map f c = f ≫ inclusion (Cech.mapCocycle f c) := by
  apply CategoryTheory.Sheaf.hom_ext
  change (inclusionPre c ≫ unit c) ≫ (map f c).hom =
    f.hom ≫ (inclusionPre (Cech.mapCocycle f c) ≫ unit (Cech.mapCocycle f c))
  rw [Category.assoc, unit_map, ← Category.assoc, inclusionPre_mapPre, Category.assoc]

/-- The right endpoint square commutes with the identity on the
actual native constant lifted-integer sheaf. -/
theorem map_projection (f : F ⟶ G) (c : CechOneCocycle F U) :
    map f c ≫ projection (Cech.mapCocycle f c) = projection c := by
  apply extensionHom_ext c
  change unit c ≫ ((map f c).hom ≫ (projection (Cech.mapCocycle f c)).hom) =
    unit c ≫ (projection c).hom
  rw [← Category.assoc, unit_map, Category.assoc, unit_projection,
    ← Category.assoc, mapPre_projectionPre, unit_projection]

/-- A genuine map of the actual extension complexes, with endpoint
maps exactly the given morphism and the identity. -/
def complexMap (f : F ⟶ G) (c : CechOneCocycle F U) :
    complex c ⟶ complex (Cech.mapCocycle f c) where
  τ₁ := f
  τ₂ := map f c
  τ₃ := 𝟙 (degreeSheaf X)
  comm₁₂ := (inclusion_map f c).symm
  comm₂₃ := by
    change map f c ≫ projection (Cech.mapCocycle f c) = projection c ≫ 𝟙 (degreeSheaf X)
    rw [Category.comp_id]
    exact map_projection f c

@[simp] theorem complexMap_τ₁ (f : F ⟶ G) (c : CechOneCocycle F U) :
    (complexMap f c).τ₁ = f := rfl

@[simp] theorem complexMap_τ₂ (f : F ⟶ G) (c : CechOneCocycle F U) :
    (complexMap f c).τ₂ = map f c := rfl

@[simp] theorem complexMap_τ₃ (f : F ⟶ G) (c : CechOneCocycle F U) :
    (complexMap f c).τ₃ = 𝟙 (degreeSheaf X) := rfl

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
