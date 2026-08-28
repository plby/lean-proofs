import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZeroBasic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Global lifting and actual degree-zero cohomology maps

On the small open-set site of a topological space, surjectivity on actual
global sections gives surjectivity on morphisms from the constant integer
sheaf.  The bridge is mathlib's genuine degree-zero cohomology comparison
and its naturality, not a comparison with a separate cochain construction.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

/-- Abelian sheaves on the actual small open-set site. -/
abbrev AbelianSheaf (X : TopCat.{0}) :=
  CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}

/-- The actual constant integer sheaf used in the definition of sheaf cohomology. -/
abbrev constantIntegerSheaf (X : TopCat.{0}) : AbelianSheaf X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
    (AddCommGrpCat.of (ULift.{0} ℤ))

variable {X : TopCat.{0}}

/-- The small `Ext` instance supplied by the actual Grothendieck sheaf category. -/
instance abelianSheaf_hasExt : HasExt.{0} (AbelianSheaf X) :=
  IsGrothendieckAbelian.hasExt _

/-- The group structure is exactly mathlib's existing `Ext` group structure. -/
instance sheafHAddCommGroup (F : AbelianSheaf X) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} F n) :=
  Ext.instAddCommGroup

/-- Every short exact sequence beginning in `F` lifts actual global
sections across its second arrow. -/
def GlobalLifting (F : AbelianSheaf X) : Prop :=
  ∀ {G Q : AbelianSheaf X} (ι : F ⟶ G) (π : G ⟶ Q) (h : ι ≫ π = 0),
    (ShortComplex.mk ι π h).ShortExact →
      Function.Surjective (π.hom.app (op (⊤ : Opens X)))

/-- Lifting actual global sections gives lifting of the corresponding
morphisms from the constant integer sheaf. -/
theorem hom_surjective_of_global_surjective {G Q : AbelianSheaf X} (π : G ⟶ Q)
    (hπ : Function.Surjective (π.hom.app (op (⊤ : Opens X)))) :
    Function.Surjective (fun f : constantIntegerSheaf X ⟶ G => f ≫ π) := by
  intro f
  let x : CategoryTheory.Sheaf.H.{0} Q 0 := Ext.mk₀.{0} f
  let eG := CategoryTheory.Sheaf.H.equiv₀.{0} G
    (show Limits.IsTerminal (⊤ : Opens X) from Limits.isTerminalTop)
  let eQ := CategoryTheory.Sheaf.H.equiv₀.{0} Q
    (show Limits.IsTerminal (⊤ : Opens X) from Limits.isTerminalTop)
  obtain ⟨y, hy⟩ := hπ (eQ x)
  let z : CategoryTheory.Sheaf.H.{0} G 0 := eG.symm y
  have hz : CategoryTheory.Sheaf.H.map.{0} π 0 z = x := by
    apply eQ.injective
    calc
      eQ (CategoryTheory.Sheaf.H.map.{0} π 0 z) =
          π.hom.app (op (⊤ : Opens X)) (eG z) :=
        (CategoryTheory.Sheaf.H.equiv₀_naturality
          (hT := (show Limits.IsTerminal (⊤ : Opens X) from Limits.isTerminalTop)) π z).symm
      _ = eQ x := (congrArg (π.hom.app (op (⊤ : Opens X)))
        (eG.apply_symm_apply y)).trans hy
  refine ⟨Ext.addEquiv₀.{0} z, ?_⟩
  calc
    Ext.addEquiv₀.{0} z ≫ π = Ext.addEquiv₀.{0} (CategoryTheory.Sheaf.H.map.{0} π 0 z) :=
      (CategoryTheory.Sheaf.H.addEquiv₀_map π z).symm
    _ = Ext.addEquiv₀.{0} x := congrArg Ext.addEquiv₀.{0} hz
    _ = f := (Ext.addEquiv₀.{0} (X := constantIntegerSheaf X) (Y := Q)).apply_symm_apply f

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
