import Wikipedia.HopfProblem.ConstantSheafFirstCohomologyExtensionBasic
import Wikipedia.HopfProblem.ConstantSheafFirstCohomologyConstantLocal
import Mathlib.Topology.Connected.LocallyConnected

/-!
# A native extension of constant sheaves is locally constant

For an actual extension of a constant abelian sheaf by the constant integer
sheaf, a local lift of the integer one lifts every integer. On a connected
open neighborhood both endpoint germ maps are bijective, so the genuine
short five lemma makes the middle germ map bijective as well.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Wikipedia.HopfProblem.ConstantSheafFirstCohomology.Extension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}}

/-- The original lifted integer one in the native constant integer sheaf. -/
def integerOne (X : TopCat.{0}) (U : Opens X) :
    (Constant.sheaf X (AddCommGrpCat.of (ULift.{0} ℤ))).obj.obj (op U) :=
  (Constant.unit X (AddCommGrpCat.of (ULift.{0} ℤ))).app (op U) (ULift.up 1)

@[simp]
theorem integerOne_restrict (X : TopCat.{0}) {U V : Opens X} (i : V ⟶ U) :
    (Constant.sheaf X (AddCommGrpCat.of (ULift.{0} ℤ))).obj.map i.op (integerOne X U) =
      integerOne X V :=
  Constant.unit_restrict X (AddCommGrpCat.of (ULift.{0} ℤ)) i (ULift.up 1)

/-- A lift of one lifts every section of the constant integer sheaf on a
connected open set; the lift is the actual integer multiple of that section. -/
theorem integer_sections_surjective_of_one_lift
    {E : TopCat.Sheaf AddCommGrpCat.{0} X}
    (π : E ⟶ Constant.sheaf X (AddCommGrpCat.of (ULift.{0} ℤ)))
    (U : Opens X) (hU : IsPreconnected (U : Set X))
    (t : E.obj.obj (op U)) (ht : π.hom.app (op U) t = integerOne X U) :
    Function.Surjective (π.hom.app (op U)) := by
  intro q
  obtain ⟨n, rfl⟩ := Constant.unit_app_surjective X
    (AddCommGrpCat.of (ULift.{0} ℤ)) U hU q
  change ULift.{0} ℤ at n
  refine ⟨n.down • t, ?_⟩
  rw [map_zsmul, ht]
  let c : ULift.{0} ℤ →+
      (Constant.sheaf X (AddCommGrpCat.of (ULift.{0} ℤ))).obj.obj (op U) :=
    ((Constant.unit X (AddCommGrpCat.of (ULift.{0} ℤ))).app (op U)).hom
  change n.down • c (ULift.up 1) = c n
  rw [← c.map_zsmul]
  congr 1
  apply ULift.ext
  simp

/-- The original middle sheaf of an extension of native constant sheaves
has locally bijective actual germ maps. -/
theorem locally_germ_bijective [LocallyConnectedSpace X]
    (A : AddCommGrpCat.{0}) {E : TopCat.Sheaf AddCommGrpCat.{0} X}
    (ι : Constant.sheaf X A ⟶ E)
    (π : E ⟶ Constant.sheaf X (AddCommGrpCat.of (ULift.{0} ℤ)))
    (hzero : ι ≫ π = 0) (hS : (ShortComplex.mk ι π hzero).ShortExact) :
    ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      ∀ (y : X) (hy : y ∈ U), Function.Bijective (TopCat.Presheaf.germ E.obj U y hy) := by
  let : Epi π := hS.epi_g
  obtain ⟨U, t, hmem, hlift⟩ := exists_local_lifts π (integerOne X ⊤)
  intro x
  obtain ⟨V, ⟨hVo, hxV, hVc⟩, hVU⟩ :=
    (LocallyConnectedSpace.open_connected_basis x).mem_iff.mp
      ((U x).isOpen.mem_nhds (hmem x))
  let W : Opens X := ⟨V, hVo⟩
  have hWU : W ≤ U x := hVU
  let r : E.obj.obj (op W) := E.obj.map (homOfLE hWU).op (t x)
  have hπr : π.hom.app (op W) r = integerOne X W := by
    calc
      π.hom.app (op W) r =
          (Constant.sheaf X (AddCommGrpCat.of (ULift.{0} ℤ))).obj.map
            (homOfLE hWU).op (π.hom.app (op (U x)) (t x)) :=
        ConcreteCategory.congr_hom (π.hom.naturality (homOfLE hWU).op) (t x)
      _ = integerOne X W := by rw [hlift, integerOne_restrict, integerOne_restrict]
  refine ⟨W, hxV, fun y hy => ?_⟩
  exact middle_germ_bijective hS W y hy
    (integer_sections_surjective_of_one_lift π W hVc.isPreconnected r hπr)
    (Constant.germ_bijective X A W hVc y hy)
    (Constant.germ_bijective X (AddCommGrpCat.of (ULift.{0} ℤ)) W hVc y hy)

end Wikipedia.HopfProblem.ConstantSheafFirstCohomology.Extension
