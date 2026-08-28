import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Topology.Maps.Basic

/-!
# The canonical map from a pushforward stalk to the fibre stalks

The components of the map below are Mathlib's actual `stalkPushforward`
maps, with the equality defining a point of the fibre used only to identify
their sources.  No assertion about proper base change is assumed.

For a closed continuous map, inverse images of open neighbourhoods of a
point are cofinal among open sets containing its entire fibre.  The proof
uses the complement of the image of the complementary closed set.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped AlgebraicGeometry

namespace Wikipedia.HopfProblem.CuspNormalization.SheafFiniteStalk

variable {X Y : TopCat.{0}}

/-- Every point of the fibre lies in the inverse image of a neighbourhood
of its image point. -/
theorem fiber_mem_preimage (f : X ⟶ Y) (y : Y) (x : f ⁻¹' {y})
    (U : Opens Y) (hy : y ∈ U) : x.val ∈ (Opens.map f).obj U := by
  change f x.val ∈ U
  exact (show f x.val = y from x.property).symm ▸ hy

/-- A closed map provides a saturated neighbourhood inside any open set
containing its whole fibre. -/
theorem exists_open_preimage_subset (f : X ⟶ Y) (hf : IsClosedMap f)
    (y : Y) (U : Opens X) (hU : f ⁻¹' {y} ⊆ U) :
    ∃ V : Opens Y, y ∈ V ∧ (Opens.map f).obj V ≤ U := by
  let V : Opens Y :=
    ⟨(f '' (U : Set X)ᶜ)ᶜ, (hf _ U.isOpen.isClosed_compl).isOpen_compl⟩
  refine ⟨V, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    exact hx (hU hxy)
  · intro x hx
    by_contra hxU
    exact hx ⟨x, hxU, rfl⟩

/-- The canonical pushforward-stalk component at an actual point of the
fibre.  This is the ordinary `stalkPushforward` map after identifying the
base points by their supplied equality. -/
def pushforwardStalkComponent (f : X ⟶ Y)
    (F : TopCat.Presheaf AddCommGrpCat.{0} X) (y : Y)
    (x : f ⁻¹' {y}) : (f _* F).stalk y ⟶ F.stalk x.val := by
  have hx : f x.val = y := x.property
  exact eqToHom (congrArg (fun z => (f _* F).stalk z) hx.symm) ≫
    F.stalkPushforward AddCommGrpCat f x.val

/-- On an actual section over an inverse image, the canonical component
is precisely its usual germ at the selected point of the fibre. -/
@[simp] theorem pushforwardStalkComponent_germ (f : X ⟶ Y)
    (F : TopCat.Presheaf AddCommGrpCat.{0} X) (y : Y)
    (x : f ⁻¹' {y}) (U : Opens Y) (hy : y ∈ U)
    (s : F.obj (op ((Opens.map f).obj U))) :
    pushforwardStalkComponent f F y x ((f _* F).germ U y hy s) =
      F.germ ((Opens.map f).obj U) x.val (fiber_mem_preimage f y x U hy) s := by
  rcases x with ⟨x, hx⟩
  have hxy : f x = y := hx
  subst y
  simp only [pushforwardStalkComponent, eqToHom_refl, Category.id_comp]
  exact TopCat.Presheaf.stalkPushforward_germ_apply AddCommGrpCat f F U x hy s

/-- The canonical additive map from the pushforward stalk to the product
of the actual stalks at every point of the fibre. -/
def pushforwardStalkHom (f : X ⟶ Y)
    (F : TopCat.Presheaf AddCommGrpCat.{0} X) (y : Y) :
    (f _* F).stalk y →+ ∀ x : f ⁻¹' {y}, F.stalk x.val :=
  AddMonoidHom.pi fun x => (pushforwardStalkComponent f F y x).hom

@[simp] theorem pushforwardStalkHom_apply (f : X ⟶ Y)
    (F : TopCat.Presheaf AddCommGrpCat.{0} X) (y : Y)
    (s : (f _* F).stalk y) (x : f ⁻¹' {y}) :
    pushforwardStalkHom f F y s x = pushforwardStalkComponent f F y x s := rfl

/-- The product map is computed entirely by the actual section germ maps. -/
@[simp] theorem pushforwardStalkHom_germ (f : X ⟶ Y)
    (F : TopCat.Presheaf AddCommGrpCat.{0} X) (y : Y)
    (U : Opens Y) (hy : y ∈ U)
    (s : F.obj (op ((Opens.map f).obj U))) (x : f ⁻¹' {y}) :
    pushforwardStalkHom f F y ((f _* F).germ U y hy s) x =
      F.germ ((Opens.map f).obj U) x.val (fiber_mem_preimage f y x U hy) s :=
  pushforwardStalkComponent_germ f F y x U hy s

end Wikipedia.HopfProblem.CuspNormalization.SheafFiniteStalk
