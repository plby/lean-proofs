import Wikipedia.HopfProblem.PeriodTorusLineBundleChernLogAlgebra
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernLogCanonical
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCocycleBasic

/-!
# Actual factor-log defects as integral group two-cocycles

The normalized entire logarithms already constructed for genuine factors
are packaged in the group-cocycle interface used by actual singular
cochains.  The explicit canonical Appell--Humbert logarithm gives the
literal upper-triangular cocycle.  It is not identified with the
principal-normalized logarithm without an integer branch correction.

The sign remains the positive factor-log defect; no Chern class is defined.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleChernLog

open PeriodTorusLineBundleClassification PeriodTorusAppellHumbert PeriodTorusTypeOneOne
open PeriodTorusLineBundle.ChernCocycle

variable {p : PeriodDomain} {b c : p.lattice → ComplexPlane₂ → ℂ}
  {n n' : p.lattice → p.lattice → ℤ}

/-- A proved actual logarithmic defect gives the required integral group two-cocycle. -/
def integerCocycleOfLogDefect (h : HasIntegerLogDefect p b n) :
    IntegralTwoCocycle p.lattice where
  toFun := n
  cocycle l m k := (h.cocycle l m k).trans (add_comm _ _)

@[simp] theorem integerCocycleOfLogDefect_apply (h : HasIntegerLogDefect p b n)
    (l m : p.lattice) : integerCocycleOfLogDefect h l m = n l m := rfl

theorem integerCocycleOfLogDefect_add (h : HasIntegerLogDefect p b n)
    (h' : HasIntegerLogDefect p c n') :
    integerCocycleOfLogDefect (logDefect_add h h') =
      integerCocycleOfLogDefect h + integerCocycleOfLogDefect h' := by
  ext l m
  rfl

theorem integerCocycleOfLogDefect_neg (h : HasIntegerLogDefect p b n) :
    integerCocycleOfLogDefect (logDefect_neg h) = -integerCocycleOfLogDefect h := by
  ext l m
  rfl

theorem integerCocycleOfLogDefect_gauge (h : HasIntegerLogDefect p b n)
    (u : ComplexPlane₂ → ℂ) :
    integerCocycleOfLogDefect (logDefect_gauge h u) = integerCocycleOfLogDefect h := by
  ext l m
  rfl

/-- Integer changes of logarithmic branches add the negative standard coboundary. -/
theorem integerCocycleOfLogDefect_integerShift (h : HasIntegerLogDefect p b n)
    (t : p.lattice → ℤ) :
    integerCocycleOfLogDefect (logDefect_integerShift h t) =
      integerCocycleOfLogDefect h + -IntegralTwoCocycle.coboundary t := by
  ext l m
  exact congrArg (fun a : ℤ => n l m + a) (logCoboundary_eq_neg_standard t l m)

/-- The actual normalized integer defect of the chosen entire logarithms of a factor. -/
def factorCocycle (F : FactorOfAutomorphy p) : IntegralTwoCocycle p.lattice :=
  integerCocycleOfLogDefect (factorLog_hasIntegerLogDefect F)

@[simp] theorem factorCocycle_apply (F : FactorOfAutomorphy p) (l m : p.lattice) :
    factorCocycle F l m = factorLogIntegerCocycle F l m := rfl

/-- Its integer is the actual defect at every point of the covering plane. -/
theorem factorCocycle_spec (F : FactorOfAutomorphy p) (l m : p.lattice)
    (z : ComplexPlane₂) :
    factorLogDefect F l m z = (factorCocycle F l m : ℂ) * logPeriod :=
  factorLogIntegerCocycle_spec F l m z

@[simp] theorem factorCocycle_zero_left (F : FactorOfAutomorphy p) (l : p.lattice) :
    factorCocycle F 0 l = 0 := factorLogIntegerCocycle_zero_left F l

@[simp] theorem factorCocycle_zero_right (F : FactorOfAutomorphy p) (l : p.lattice) :
    factorCocycle F l 0 = 0 := factorLogIntegerCocycle_zero_right F l

/-- Antisymmetrization is precisely the positive alternating form of the actual logarithms. -/
theorem factorCocycle_antisymm (F : FactorOfAutomorphy p) (l m : p.lattice) :
    factorCocycle F l m - factorCocycle F m l = factorLogAlternatingForm F l m := rfl

/-- The same actual cocycle in the original four integer period coordinates. -/
def factorCoordinateCocycle (F : FactorOfAutomorphy p) : IntegralTwoCocycle Lattice :=
  (factorCocycle F).comap p.latticeEquiv.symm.toAddMonoidHom

@[simp] theorem factorCoordinateCocycle_apply (F : FactorOfAutomorphy p) (x y : Lattice) :
    factorCoordinateCocycle F x y =
      factorCocycle F (p.latticeEquiv.symm x) (p.latticeEquiv.symm y) := rfl

/-- The explicit upper-triangular formula is a cocycle for every integer coefficient vector. -/
def canonicalCocycle (p : PeriodDomain) (E : Fin 6 → ℤ) : IntegralTwoCocycle p.lattice where
  toFun := canonicalIntegerCocycle p E
  cocycle l m k := by
    simp only [canonicalIntegerCocycle, map_add, Pi.add_apply, mul_add, add_mul,
      Finset.sum_add_distrib]
    ring

@[simp] theorem canonicalCocycle_apply (p : PeriodDomain) (E : Fin 6 → ℤ)
    (l m : p.lattice) : canonicalCocycle p E l m = canonicalIntegerCocycle p E l m := rfl

@[simp] theorem canonicalCocycle_zero_left (p : PeriodDomain) (E : Fin 6 → ℤ)
    (l : p.lattice) : canonicalCocycle p E 0 l = 0 := by
  simp [canonicalCocycle_apply, canonicalIntegerCocycle]

@[simp] theorem canonicalCocycle_zero_right (p : PeriodDomain) (E : Fin 6 → ℤ)
    (l : p.lattice) : canonicalCocycle p E l 0 = 0 := by
  simp [canonicalCocycle_apply, canonicalIntegerCocycle]

/-- This cocycle comes from the displayed logarithm of the actual canonical factor. -/
theorem canonicalCocycle_spec (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) (l m : p.lattice) (z : ComplexPlane₂) :
    canonicalLog p E hType (l + m) z - canonicalLog p E hType l (z + m) -
      canonicalLog p E hType m z = (canonicalCocycle p E l m : ℂ) * logPeriod :=
  canonicalLog_hasIntegerLogDefect p E hType l m z

theorem canonicalCocycle_antisymm (p : PeriodDomain) (E : Fin 6 → ℤ)
    (l m : p.lattice) :
    canonicalCocycle p E l m - canonicalCocycle p E m l =
      coordinateForm E (p.latticeEquiv l) (p.latticeEquiv m) :=
  canonicalIntegerCocycle_antisymm p E l m

theorem canonicalCocycle_add (p : PeriodDomain) (E F : Fin 6 → ℤ) :
    canonicalCocycle p (E + F) = canonicalCocycle p E + canonicalCocycle p F := by
  ext l m
  exact canonicalIntegerCocycle_add p E F l m

/-- The chosen principal-normalized logarithm has the same positive antisymmetrization. -/
theorem factorCocycle_canonical_antisymm (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) (l m : p.lattice) :
    factorCocycle (integralFactor p E hType) l m -
        factorCocycle (integralFactor p E hType) m l =
      coordinateForm E (p.latticeEquiv l) (p.latticeEquiv m) := by
  rw [factorCocycle_antisymm, canonicalFactorLogAlternatingForm_apply]

end Wikipedia.HopfProblem.PeriodTorusLineBundleChernLog
