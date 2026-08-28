import Wikipedia.HopfProblem.HolomorphicPicardCechAlgebra
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionSheafBasic

/-!
# An actual change of local splitting for cocycle extensions

An actual zero cochain with `c - d = δb` sends the compatible coordinates
`(n,sᵢ)` to `(n,sᵢ-n bᵢ)`. The resulting morphism of genuine sheafified
extensions fixes the original kernel and constant-integer quotient.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    {ι : Type} {U : ι → Opens X} (c d : CechOneCocycle F U)
    (b : Cech.ZeroCochain F U) (hb : c - d = Cech.coboundary F U b)

/-- The literal compatible-data map for a change of local splitting. -/
def coboundaryHom (V : Opens X) : ExtensionSection c V →+ ExtensionSection d V where
  toFun s := ⟨⟨s.1.1, fun i => s.1.2 i - s.1.1.down • res F inf_le_right (b i)⟩, by
    intro i j
    have hij := congrArg (fun t : CechOneCocycle F U => t.value i j) hb
    have h := congrArg (res F (V := V ⊓ (U i ⊓ U j)) inf_le_right) hij
    simp only [Cech.sub_value, Cech.coboundary_value, map_sub, res_trans] at h
    simp only [map_sub, map_zsmul, res_trans]
    calc
      _ = (res F (inf_le_inf_left V inf_le_left) (s.1.2 i) -
          res F (inf_le_inf_left V inf_le_right) (s.1.2 j)) -
          s.1.1.down • (res F (inf_le_right.trans inf_le_left) (b i) -
            res F (inf_le_right.trans inf_le_right) (b j)) := by
        rw [smul_sub]
        abel
      _ = s.1.1.down • res F inf_le_right (c.value i j) -
          s.1.1.down • (res F inf_le_right (c.value i j) -
            res F inf_le_right (d.value i j)) := by rw [s.2 i j, ← h]
      _ = _ := by rw [smul_sub]; abel⟩
  map_zero' := by
    apply extensionSection_ext
    · rfl
    · intro i
      change (0 : Section F (V ⊓ U i)) - (0 : ℤ) • _ = 0
      simp only [zero_zsmul, sub_zero]
  map_add' s t := by
    apply extensionSection_ext
    · rfl
    · intro i
      change (s.1.2 i + t.1.2 i) - (s.1.1.down + t.1.1.down) • _ =
        (s.1.2 i - s.1.1.down • _) + (t.1.2 i - t.1.1.down • _)
      rw [add_zsmul]
      abel

@[simp] theorem coboundaryHom_degree (V : Opens X) (s : ExtensionSection c V) :
    degreeHom d V (coboundaryHom c d b hb V s) = degreeHom c V s := rfl

@[simp] theorem coboundaryHom_coordinate (V : Opens X) (i : ι)
    (s : ExtensionSection c V) :
    coordinateHom d V i (coboundaryHom c d b hb V s) =
      coordinateHom c V i s - (degreeHom c V s).down • res F inf_le_right (b i) := rfl

theorem restrict_coboundaryHom {V W : Opens X} (hWV : W ≤ V)
    (s : ExtensionSection c V) :
    restrict d hWV (coboundaryHom c d b hb V s) =
      coboundaryHom c d b hb W (restrict c hWV s) := by
  apply extensionSection_ext
  · rfl
  · intro i
    change res F _ (s.1.2 i - s.1.1.down • res F _ (b i)) =
      res F _ (s.1.2 i) - s.1.1.down • res F _ (b i)
    rw [map_sub, map_zsmul, res_trans]

theorem coboundaryHom_include (V : Opens X) (s : Section F V) :
    coboundaryHom c d b hb V (includeHom c V s) = includeHom d V s := by
  apply extensionSection_ext
  · rfl
  · intro i
    change res F inf_le_left s - (0 : ℤ) • _ = res F inf_le_left s
    rw [zero_zsmul, sub_zero]

def coboundaryPre : presheaf c ⟶ presheaf d where
  app V := AddCommGrpCat.ofHom (coboundaryHom c d b hb V.unop)
  naturality V W h := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (restrict_coboundaryHom c d b hb (leOfHom h.unop) s).symm

theorem inclusionPre_coboundaryPre :
    inclusionPre c ≫ coboundaryPre c d b hb = inclusionPre d := by
  ext V s
  exact coboundaryHom_include c d b hb V.unop s

theorem coboundaryPre_projectionPre :
    coboundaryPre c d b hb ≫ projectionPre d = projectionPre c := by
  ext V s
  rfl

def coboundaryMap : extensionSheaf c ⟶ extensionSheaf d where
  hom := CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) (coboundaryPre c d b hb)

theorem unit_coboundaryMap :
    unit c ≫ (coboundaryMap c d b hb).hom = coboundaryPre c d b hb ≫ unit d :=
  (CategoryTheory.toSheafify_naturality
    (Opens.grothendieckTopology X) (coboundaryPre c d b hb)).symm

@[simp] theorem coboundaryMap_app_unit (V : Opens X) (s : ExtensionSection c V) :
    (coboundaryMap c d b hb).hom.app (op V) ((unit c).app (op V) s) =
      (unit d).app (op V) (coboundaryHom c d b hb V s) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (unit_coboundaryMap c d b hb) (op V)) s

theorem inclusion_coboundaryMap :
    inclusion c ≫ coboundaryMap c d b hb = inclusion d := by
  apply CategoryTheory.Sheaf.hom_ext
  change (inclusionPre c ≫ unit c) ≫ (coboundaryMap c d b hb).hom = inclusionPre d ≫ unit d
  rw [Category.assoc, unit_coboundaryMap, ← Category.assoc, inclusionPre_coboundaryPre]

theorem coboundaryMap_projection :
    coboundaryMap c d b hb ≫ projection d = projection c := by
  apply extensionHom_ext c
  change unit c ≫ ((coboundaryMap c d b hb).hom ≫ (projection d).hom) =
    unit c ≫ (projection c).hom
  rw [← Category.assoc, unit_coboundaryMap, Category.assoc, unit_projection,
    ← Category.assoc, coboundaryPre_projectionPre, unit_projection]

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
