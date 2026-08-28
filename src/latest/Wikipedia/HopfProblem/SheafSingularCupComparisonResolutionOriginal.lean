import Wikipedia.HopfProblem.SheafSingularCupComparisonResolutionTruncation
import Wikipedia.HopfProblem.SheafSingularCupComparisonResolutionCokernel
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowExtTwo

/-!
# Exact agreement with the original cochain-resolution comparisons

The comparison from a partial resolution to the full cochain complex uses
the original standard three-term window isomorphisms. With these maps,
the acyclic partial-resolution comparisons equal the already defined
degree-one and degree-two comparisons, not merely some isomorphisms
between the same groups.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.Resolution

open SheafCupProductResolution ConstantSheafSingularComparison.LowExt
open CuspNormalization.SheafCohomologyResolution

variable {X : TopCat.{0}} (R : CochainResolution (TopCat.Sheaf AddCommGrpCat.{0} X))

@[simp] theorem ofCochain_globalOneComplex :
    (ofCochain R).globalOneComplex = R.globalCochainComplex.sc' 0 1 2 := rfl

@[simp] theorem ofCochain_globalTwoComplex :
    (ofCochain R).globalTwoComplex = R.globalCochainComplex.sc' 1 2 3 := rfl

@[simp] theorem ofCochain_globalTruncationInclusion :
    (ofCochain R).globalTruncationInclusion = R.globalShortInclusion := rfl

/-- The same standard degree-one window isomorphism used by the original comparison. -/
def oneWindowIso : (ofCochain R).globalOneComplex.homology ≅
    R.globalCochainComplex.homology 1 :=
  (ShortComplex.homologyMapIso
    (R.globalCochainComplex.isoSc' 0 1 2
      ((ComplexShape.up ℕ).prev_eq' (by rfl))
      ((ComplexShape.up ℕ).next_eq' (by rfl)))).symm

/-- The same standard degree-two window isomorphism used by the original comparison. -/
def twoWindowIso : (ofCochain R).globalTwoComplex.homology ≅
    R.globalCochainComplex.homology 2 :=
  (CycleCokernel.windowHomologyIso₂ R.globalCochainComplex).symm

/-- Exact equality to the original native degree-one comparison. -/
theorem ofCochain_h1IsoAcyclic [h0 : Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)] :
    (ofCochain R).h1IsoAcyclic (h0 := h0) ≪≫ oneWindowIso R = R.h1Iso := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₁ 1) := h0
  change (R.truncation.h1Iso ≪≫ asIso (ShortComplex.homologyMap R.globalShortInclusion)) ≪≫
    oneWindowIso R = R.truncation.h1Iso ≪≫
      (asIso (ShortComplex.homologyMap R.globalShortInclusion) ≪≫ oneWindowIso R)
  exact Iso.trans_assoc _ _ _

/-- The actual partial-resolution cokernel map, followed by the original
window map, is exactly the original full-complex cokernel comparison. -/
theorem ofCochain_globalTwoCokernelIso :
    (ofCochain R).globalTwoCokernelIso ≪≫ twoWindowIso R =
      R.globalSecondHomologyIso := by
  exact congrArg (fun e => e ≪≫ twoWindowIso R)
    (ofCochain R).globalTwoCokernelIso_eq_shortCokernelIsoHomology

/-- Exact equality to the original native degree-two comparison. -/
theorem ofCochain_h2IsoAcyclic
    [h01 : Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)]
    [h02 : Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 2)]
    [h11 : Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 1) 1)] :
    (ofCochain R).h2IsoAcyclic (h01 := h01) (h02 := h02) (h11 := h11) ≪≫
      twoWindowIso R = R.h2Iso := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₁ 1) := h01
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₁ 2) := h02
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₂ 1) := h11
  change (R.truncation.h2Iso ≪≫ (ofCochain R).globalTwoCokernelIso) ≪≫ twoWindowIso R =
    R.truncation.h2Iso ≪≫ R.globalSecondHomologyIso
  exact (Iso.trans_assoc _ _ _).trans
    (congrArg (fun e => R.truncation.h2Iso ≪≫ e) (ofCochain_globalTwoCokernelIso R))

end Wikipedia.HopfProblem.SheafSingularCupComparison.Resolution
