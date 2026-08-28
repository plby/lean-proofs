import Wikipedia.NoExoticSixSphere.ModTwoDualFunctor
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainHomotopy

/-!
# Actual mod-two duality transports chain homotopies

The additive module-dual functor uses literal precomposition with values
in `ZMod 2`. It transports a genuine chain homotopy to the original
mod-two cochain complexes, and a chain homotopy equivalence gives a
cochain homotopy equivalence in the opposite direction.
-/

noncomputable section

open CategoryTheory Opposite
open Wikipedia.HopfProblem

namespace NoExoticSixSphere.ModTwoDualComplex

/-- The actual additive mod-two module dual, with its compatible integer scalars. -/
def moduleDualFunctor : (ModuleCat.{0} ℤ)ᵒᵖ ⥤ ModuleCat.{0} ℤ where
  obj M := ModuleCat.of ℤ (M.unop →+ ZMod 2)
  map f := ModuleCat.ofHom (ConstantSheafSingularComparison.addHomToIntLinearMap
    (ConstantSheafSingularComparison.precompose (AddCommGrpCat.of (ZMod 2))
      f.unop.hom.toAddMonoidHom))
  map_id _ := by
    apply ModuleCat.hom_ext
    ext φ c
    rfl
  map_comp _ _ := by
    apply ModuleCat.hom_ext
    ext φ c
    rfl

instance moduleDualFunctor_additive : moduleDualFunctor.Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply AddMonoidHom.ext
    intro c
    exact φ.map_add (f.unop.hom c) (g.unop.hom c)

variable {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}

/-- Original chain homotopies act by literal precomposition on mod-two cochains. -/
def mapHomotopy {f g : K ⟶ L} (h : Homotopy f g) : Homotopy (map f) (map g) :=
  moduleDualFunctor.mapHomotopy h.op

theorem mapHomotopy_hom_apply {f g : K ⟶ L} (h : Homotopy f g) (i j : ℕ)
    (α : L.X i →+ ZMod 2) :
    ((mapHomotopy h).hom i j).hom α = α.comp (h.hom j i).hom.toAddMonoidHom := rfl

theorem mapHomotopy_homologyMap_eq {f g : K ⟶ L} (h : Homotopy f g) (n : ℕ) :
    HomologicalComplex.homologyMap (map f) n = HomologicalComplex.homologyMap (map g) n :=
  (mapHomotopy h).homologyMap_eq n

/-- A genuine chain homotopy equivalence gives the original contravariant cochain equivalence. -/
def mapHomotopyEquiv (e : HomotopyEquiv K L) : HomotopyEquiv (complex L) (complex K) where
  hom := map e.hom
  inv := map e.inv
  homotopyHomInvId := by
    simpa only [map_comp, map_id] using mapHomotopy e.homotopyInvHomId
  homotopyInvHomId := by
    simpa only [map_comp, map_id] using mapHomotopy e.homotopyHomInvId

/-- The resulting equivalence on actual cohomology retains the original pullback map. -/
def homotopyCohomologyEquiv (e : HomotopyEquiv K L) (n : ℕ) :
    (complex L).homology n ≃ₗ[ℤ] (complex K).homology n :=
  ((mapHomotopyEquiv e).toHomologyIso n).toLinearEquiv

theorem homotopyCohomologyEquiv_toLinearMap (e : HomotopyEquiv K L) (n : ℕ) :
    (homotopyCohomologyEquiv e n).toLinearMap =
      (HomologicalComplex.homologyMap (map e.hom) n).hom := rfl

end NoExoticSixSphere.ModTwoDualComplex
