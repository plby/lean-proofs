import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupRowBasic
import Wikipedia.HopfProblem.SheafCupProductResolutionGlobal
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Literal global cocycle classes in the native torus row

These classes are the canonical homology projections of the original
global short complexes. No Haar coordinates or native cohomology
comparison enters their definitions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Row

open PeriodTorusHolomorphicCohomology
open CuspNormalization.SheafCohomologyResolution

variable (p : PeriodDomain)

/-- The actual global smooth-function, pair, and top-coefficient complex. -/
abbrev oneComplex : ShortComplex AddCommGrpCat := (partialResolution p).globalOneComplex

/-- The actual global pair, top-coefficient, and zero-sheaf complex. -/
abbrev twoComplex : ShortComplex AddCommGrpCat := (partialResolution p).globalTwoComplex

theorem oneComplex_eq_original : oneComplex p = (Dolbeault.resolution p).globalComplex := rfl

theorem twoComplex_g_zero : (twoComplex p).g = 0 :=
  (globalSectionsFunctor (TopCat.of p.Torus)).map_zero _ _

/-- A closed original smooth pair gives its canonical actual global cycle. -/
def oneCycle (s : Dolbeault.PairSection p ⊤) (hs : Dolbeault.topSection p ⊤ s = 0) :
    (oneComplex p).cycles :=
  (oneComplex p).abCyclesIso.inv ⟨s, hs⟩

/-- Its cycle inclusion retains exactly the two original coefficient functions. -/
theorem oneCycle_i (s : Dolbeault.PairSection p ⊤) (hs : Dolbeault.topSection p ⊤ s = 0) :
    (oneComplex p).iCycles (oneCycle p s hs) = s :=
  (oneComplex p).abCyclesIso_inv_apply_iCycles ⟨s, hs⟩

/-- The actual homology class of an original closed smooth pair. -/
def oneClass (s : Dolbeault.PairSection p ⊤) (hs : Dolbeault.topSection p ⊤ s = 0) :
    (oneComplex p).homology :=
  (oneComplex p).homologyπ (oneCycle p s hs)

/-- Every original top coefficient is a cycle, through the canonical kernel of zero. -/
def twoCycle : Dolbeault.SmoothSection p ⊤ →+ (twoComplex p).cycles :=
  ((twoComplex p).cyclesIsoX₂ (twoComplex_g_zero p)).inv.hom

theorem twoCycle_i (s : Dolbeault.SmoothSection p ⊤) :
    (twoComplex p).iCycles (twoCycle p s) = s :=
  ConcreteCategory.congr_hom
    ((twoComplex p).cyclesIsoX₂ (twoComplex_g_zero p)).inv_hom_id s

/-- The canonical actual homology class of an original smooth top coefficient. -/
def twoClass : Dolbeault.SmoothSection p ⊤ →+ (twoComplex p).homology :=
  (twoComplex p).homologyπ.hom.comp (twoCycle p)

theorem twoClass_apply (s : Dolbeault.SmoothSection p ⊤) :
    twoClass p s = (twoComplex p).homologyπ (twoCycle p s) := rfl

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Row
