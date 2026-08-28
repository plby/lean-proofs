import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainSingular
import Mathlib.Algebra.Homology.Opposite

/-!
# Actual cochain homotopies for arbitrary abelian coefficients

Additive duality reverses the original integer chain homotopy, with each
component given by literal precomposition.  Thus a genuine chain homotopy
equivalence induces a genuine cochain homotopy equivalence for every
abelian coefficient group, without a universal-coefficient assumption.
-/

noncomputable section

open CategoryTheory Opposite

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

variable (A : AddCommGrpCat.{0})

/-- The contravariant additive dual of an actual integer module. -/
def moduleDualFunctor : (ModuleCat.{0} ℤ)ᵒᵖ ⥤ AddCommGrpCat.{0} where
  obj M := AddCommGrpCat.of (M.unop →+ A)
  map f := AddCommGrpCat.ofHom (precompose A f.unop.hom.toAddMonoidHom)
  map_id M := by
    apply AddCommGrpCat.hom_ext
    ext φ c
    rfl
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    ext φ c
    rfl

instance moduleDualFunctor_additive : (moduleDualFunctor A).Additive where
  map_add := by
    intro M N f g
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    apply AddMonoidHom.ext
    intro c
    exact φ.map_add (f.unop.hom c) (g.unop.hom c)

variable {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}

/-- The original chain homotopy acts on cochains by actual precomposition. -/
def dualHomotopy {f g : K ⟶ L} (h : Homotopy f g) :
    Homotopy (dualMap A f) (dualMap A g) :=
  (moduleDualFunctor A).mapHomotopy h.op

@[simp]
theorem dualHomotopy_hom_apply {f g : K ⟶ L} (h : Homotopy f g)
    (i j : ℕ) (φ : L.X i →+ A) (c : K.X j) :
    (dualHomotopy A h).hom i j φ c = φ ((h.hom j i).hom c) := rfl

/-- Actual chain-homotopic maps induce the same native cohomology map. -/
theorem dualHomotopy_homologyMap_eq {f g : K ⟶ L} (h : Homotopy f g) (n : ℕ) :
    HomologicalComplex.homologyMap (dualMap A f) n =
      HomologicalComplex.homologyMap (dualMap A g) n :=
  (dualHomotopy A h).homologyMap_eq n

/-- A native integer chain homotopy equivalence dualizes for every coefficient group. -/
def dualHomotopyEquiv (e : HomotopyEquiv K L) :
    HomotopyEquiv (dualComplex L A) (dualComplex K A) where
  hom := dualMap A e.hom
  inv := dualMap A e.inv
  homotopyHomInvId := by
    simpa only [dualMap_comp, dualMap_id] using dualHomotopy A e.homotopyInvHomId
  homotopyInvHomId := by
    simpa only [dualMap_comp, dualMap_id] using dualHomotopy A e.homotopyHomInvId

@[simp]
theorem dualHomotopyEquiv_hom (e : HomotopyEquiv K L) :
    (dualHomotopyEquiv A e).hom = dualMap A e.hom := rfl

@[simp]
theorem dualHomotopyEquiv_inv (e : HomotopyEquiv K L) :
    (dualHomotopyEquiv A e).inv = dualMap A e.inv := rfl

/-- The resulting isomorphism concerns the actual homology objects of the
original additive cochain complexes. -/
def dualHomotopyEquiv_homologyIso (e : HomotopyEquiv K L) (n : ℕ) :
    (dualComplex L A).homology n ≅ (dualComplex K A).homology n :=
  (dualHomotopyEquiv A e).toHomologyIso n

@[simp]
theorem dualHomotopyEquiv_homologyIso_hom (e : HomotopyEquiv K L) (n : ℕ) :
    (dualHomotopyEquiv_homologyIso A e n).hom =
      HomologicalComplex.homologyMap (dualMap A e.hom) n := rfl

@[simp]
theorem dualHomotopyEquiv_homologyIso_inv (e : HomotopyEquiv K L) (n : ℕ) :
    (dualHomotopyEquiv_homologyIso A e n).inv =
      HomologicalComplex.homologyMap (dualMap A e.inv) n := rfl

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
