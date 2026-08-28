import Wikipedia.HopfProblem.CuspNormalizationSheafFiniteStalkInjective
import Wikipedia.HopfProblem.CuspNormalizationSheafFiniteStalkGluing

/-!
# Pushforward stalks of closed maps with finite fibres

For a closed continuous map from a Hausdorff space, the stalk of the
pushforward of an additive sheaf is the product of the stalks at the
points of any finite fibre. Surjectivity is proved by choosing and gluing
actual representatives on disjoint neighbourhoods, then shrinking with
closedness. In particular, the empty-fibre case is included.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped AlgebraicGeometry

namespace Wikipedia.HopfProblem.CuspNormalization.SheafFiniteStalk

variable {X Y : TopCat.{0}} [T2Space X]

/-- Actual representatives on disjoint source neighbourhoods give a
pushforward-germ representative for every tuple of fibre germs. -/
theorem pushforwardStalkHom_surjective (f : X ⟶ Y) (hf : IsClosedMap f)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (y : Y)
    (hfinite : (f ⁻¹' {y}).Finite) :
    Function.Surjective (pushforwardStalkHom f F.presheaf y) := by
  intro t
  obtain ⟨U, hU, s, hs⟩ := exists_section_germ_eq_of_finite F hfinite t
  obtain ⟨V, hyV, hV⟩ := exists_open_preimage_subset f hf y U hU
  refine ⟨(f _* F.presheaf).germ V y hyV
    (F.presheaf.map (homOfLE hV).op s), ?_⟩
  funext x
  rw [pushforwardStalkHom_germ, F.presheaf.germ_res_apply]
  exact hs x

/-- The canonical map to the actual fibre stalks is bijective for a
closed map with finite fibre and Hausdorff source. -/
theorem pushforwardStalkHom_bijective (f : X ⟶ Y) (hf : IsClosedMap f)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (y : Y)
    (hfinite : (f ⁻¹' {y}).Finite) :
    Function.Bijective (pushforwardStalkHom f F.presheaf y) :=
  ⟨pushforwardStalkHom_injective f hf F y,
    pushforwardStalkHom_surjective f hf F y hfinite⟩

/-- The genuine pushforward stalk is canonically the product of the
genuine stalks at the points of a finite fibre. Its forward map consists
of the actual `stalkPushforward` maps, not a choice of an abstract group
isomorphism. -/
def pushforwardStalkEquiv (f : X ⟶ Y) (hf : IsClosedMap f)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (y : Y)
    (hfinite : (f ⁻¹' {y}).Finite) :
    (f _* F.presheaf).stalk y ≃+ ∀ x : f ⁻¹' {y}, F.presheaf.stalk x.val :=
  AddEquiv.ofBijective (pushforwardStalkHom f F.presheaf y)
    (pushforwardStalkHom_bijective f hf F y hfinite)

@[simp] theorem pushforwardStalkEquiv_apply (f : X ⟶ Y) (hf : IsClosedMap f)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (y : Y)
    (hfinite : (f ⁻¹' {y}).Finite) (s : (f _* F.presheaf).stalk y)
    (x : f ⁻¹' {y}) :
    pushforwardStalkEquiv f hf F y hfinite s x =
      pushforwardStalkComponent f F.presheaf y x s := rfl

/-- The canonical equivalence sends an actual inverse-image section
germ to its actual germs at all points of the fibre. -/
@[simp] theorem pushforwardStalkEquiv_germ (f : X ⟶ Y) (hf : IsClosedMap f)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (y : Y)
    (hfinite : (f ⁻¹' {y}).Finite) (U : Opens Y) (hy : y ∈ U)
    (s : F.presheaf.obj (op ((Opens.map f).obj U))) (x : f ⁻¹' {y}) :
    pushforwardStalkEquiv f hf F y hfinite ((f _* F.presheaf).germ U y hy s) x =
      F.presheaf.germ ((Opens.map f).obj U) x.val (fiber_mem_preimage f y x U hy) s :=
  pushforwardStalkHom_germ f F.presheaf y U hy s x

end Wikipedia.HopfProblem.CuspNormalization.SheafFiniteStalk
