import Wikipedia.HopfProblem.HolomorphicPicardCechRefinement

/-!
# Maps of actual sheaves on literal Čech cocycles

The construction uses the original section maps and their naturality.
It is additive in both the cocycle and the sheaf morphism, and commutes
with genuine restriction and local coboundaries.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.Cech

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}}
    {F G K : TopCat.Sheaf AddCommGrpCat.{0} X}
    {ι κ : Type} {U : ι → Opens X} {V : κ → Opens X}

def mapCocycle (f : F ⟶ G) : CechOneCocycle F U →+ CechOneCocycle G U where
  toFun c :=
    { value := fun i j => f.hom.app (op (U i ⊓ U j)) (c.value i j)
      condition := by
        intro i j k
        simp only [res_map, ← map_add, c.condition] }
  map_zero' := by
    apply cocycle_ext
    intro i j
    simp
  map_add' c d := by
    apply cocycle_ext
    intro i j
    simp

@[simp] theorem mapCocycle_value (f : F ⟶ G) (c : CechOneCocycle F U) (i j : ι) :
    (mapCocycle f c).value i j = f.hom.app (op (U i ⊓ U j)) (c.value i j) := rfl

def mapZeroCochain (f : F ⟶ G) : ZeroCochain F U →+ ZeroCochain G U where
  toFun b i := f.hom.app (op (U i)) (b i)
  map_zero' := by ext i; exact map_zero _
  map_add' b d := by ext i; exact map_add _ _ _

@[simp] theorem mapZeroCochain_apply (f : F ⟶ G) (b : ZeroCochain F U) (i : ι) :
    mapZeroCochain f b i = f.hom.app (op (U i)) (b i) := rfl

theorem mapCocycle_coboundary (f : F ⟶ G) (b : ZeroCochain F U) :
    mapCocycle f (coboundary F U b) = coboundary G U (mapZeroCochain f b) := by
  apply cocycle_ext
  intro i j
  simp only [mapCocycle_value, coboundary_value, mapZeroCochain_apply, res_map, map_sub]

@[simp] theorem mapCocycle_id (c : CechOneCocycle F U) : mapCocycle (𝟙 F) c = c := by
  apply cocycle_ext
  intro i j
  rfl

@[simp] theorem mapCocycle_comp (f : F ⟶ G) (g : G ⟶ K) (c : CechOneCocycle F U) :
    mapCocycle (f ≫ g) c = mapCocycle g (mapCocycle f c) := by
  apply cocycle_ext
  intro i j
  rfl

@[simp] theorem mapCocycle_zero (c : CechOneCocycle F U) :
    mapCocycle (0 : F ⟶ G) c = 0 := by
  apply cocycle_ext
  intro i j
  rfl

@[simp] theorem mapCocycle_add (f g : F ⟶ G) (c : CechOneCocycle F U) :
    mapCocycle (f + g) c = mapCocycle f c + mapCocycle g c := by
  apply cocycle_ext
  intro i j
  rfl

theorem mapCocycle_refinement (f : F ⟶ G) (r : κ → ι)
    (h : ∀ a, V a ≤ U (r a)) (c : CechOneCocycle F U) :
    mapCocycle f (refinement F r h c) = refinement G r h (mapCocycle f c) := by
  apply cocycle_ext
  intro a b
  exact (res_map f _ _).symm

/-- The map on actual cover cohomology comes from the actual sheaf map. -/
def cohomologyMap (f : F ⟶ G) : CoverCohomology F U →+ CoverCohomology G U :=
  QuotientAddGroup.map (coboundary F U).range (coboundary G U).range
    (mapCocycle f) (by
      rintro c ⟨b, rfl⟩
      exact ⟨mapZeroCochain f b, (mapCocycle_coboundary f b).symm⟩)

@[simp] theorem cohomologyMap_classOf (f : F ⟶ G) (c : CechOneCocycle F U) :
    cohomologyMap f (classOf F U c) = classOf G U (mapCocycle f c) := rfl

end Wikipedia.HopfProblem.HolomorphicPicard.Cech
