/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma54CanonicalThresholdOrientation
import ErdosProblems.Erdos547b.Lemma54AppendixA
import ErdosProblems.Erdos547b.Lemma54ThresholdSourceNumerics

/-!
# Source certificates for one oriented matching fiber

This is the common output shape of the threshold and Appendix-A orientation
arguments.  It records only a chosen orientation, root-side admissibility,
and the scalar side-load margin needed by the coordinate hierarchy.
-/

open scoped BigOperators
noncomputable section

namespace Erdos547b.ZhaoLemma58FiberOrientationCertificate

open Finset Fintype
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma54ThresholdOrientation
open Erdos547b.ZhaoLemma54ThresholdNumerics
open Erdos547b.ZhaoLemma54CanonicalThresholdOrientation
open Erdos547b.ZhaoLemma54ThresholdSourceNumerics
open Erdos547b.ZhaoLemma54AppendixA

/-- Exact orientation output consumed by one coordinate matching fiber. -/
structure FiberOrientationCertificate {b : ℕ}
    (F : OrderedRootedForest b) (rootGood : Fin 2 → Prop)
    (small : ℕ) (removal : ℝ) (rhs : Fin 2 → ℝ) : Type where
  orient : Fin b → Fin 2 ≃ Fin 2
  root_good : ∀ i, rootGood (orient i 0)
  capacity : ∀ c,
    (sideLoad F orient c : ℝ) + small + 1 + removal + 1 ≤ rhs c

/-- The canonical maximal-cutoff threshold orientation supplies a fiber
certificate.  A low-side root fact is needed only when its integral budget
is nonzero; at zero budget the canonical cutoff is zero and every root is
sent to the high side. -/
noncomputable def thresholdCertificate
    {b : ℕ} (F : OrderedRootedForest b) (rootGood : Fin 2 → Prop)
    (small lowBudget highBudget : ℕ) (removal : ℝ) (rhs : Fin 2 → ℝ)
    (lowSide highSide : Fin 2)
    (hsmall : ∀ i, F.size i ≤ small)
    (hsides : highSide ≠ lowSide)
    (hfinal : ∀ (base : Fin b → Fin 2 ≃ Fin 2),
      (∀ t c,
        2 * sideLoadPrefix F base t c ≤ prefixOrder F t + small) →
      ∀ c,
        lowBudget + fixedSuffixLoad F
            (maximalFittingCutoff F base lowBudget) highSide c ≤
          highBudget)
    (hhigh : rootGood highSide)
    (hlow : lowBudget ≠ 0 → rootGood lowSide)
    (hmargin : ∀ c,
      (highBudget : ℝ) + small + 1 + removal + 1 ≤ rhs c) :
    FiberOrientationCertificate F rootGood small removal rhs := by
  let O := canonicalActualThresholdSwitchOrientation F small lowBudget
    highBudget lowSide highSide hsmall hsides hfinal
  refine {
    orient := O.orient
    root_good := ?_
    capacity := ?_
  }
  · intro i
    by_cases hzero : lowBudget = 0
    · have hcut : O.cutoff = 0 := by
        change maximalFittingCutoff F
          (canonicalPrefixBalancedOrientation F small hsmall) lowBudget = 0
        rw [hzero]
        exact maximalFittingCutoff_eq_zero_of_budget_zero F _
      have hne : branchRootSide F O.orient i ≠ lowSide :=
        O.late_root_high i (by rw [hcut]; exact Nat.zero_le _)
      have heq : branchRootSide F O.orient i = highSide := by
        have hneVal : (branchRootSide F O.orient i).val ≠ lowSide.val := by
          intro h
          exact hne (Fin.ext h)
        have hsidesVal : highSide.val ≠ lowSide.val := by
          intro h
          exact hsides (Fin.ext h)
        apply Fin.ext
        omega
      change O.orient i 0 = highSide at heq
      rw [heq]
      exact hhigh
    · by_cases hroot : branchRootSide F O.orient i = lowSide
      · change O.orient i 0 = lowSide at hroot
        rw [hroot]
        exact hlow hzero
      · have heq : branchRootSide F O.orient i = highSide := by
          have hrootVal : (branchRootSide F O.orient i).val ≠ lowSide.val := by
            intro h
            exact hroot (Fin.ext h)
          have hsidesVal : highSide.val ≠ lowSide.val := by
            intro h
            exact hsides (Fin.ext h)
          apply Fin.ext
          omega
        change O.orient i 0 = highSide at heq
        rw [heq]
        exact hhigh
  · intro c
    have hload : (sideLoad F O.orient c : ℝ) ≤ highBudget := by
      exact_mod_cast O.final_load c
    linarith [hmargin c]

/-- The checked classified Parts-1/2 source numerics directly instantiate
the canonical threshold certificate. -/
noncomputable def classifiedThresholdCertificate
    {b : ℕ} (F : OrderedRootedForest b) (rootGood : Fin 2 → Prop)
    (ratio dx dy gamma epsilon N : ℝ) (small : ℕ)
    (removal : ℝ) (rhs : Fin 2 → ℝ)
    (lowSide highSide : Fin 2)
    (D : ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N small)
    (hsides : highSide ≠ lowSide)
    (hhigh : rootGood highSide)
    (hlow : thresholdLowBudget dx gamma N ≠ 0 → rootGood lowSide)
    (hmargin : ∀ c,
      (thresholdHighBudget dy gamma N : ℝ) + small + 1 + removal + 1 ≤
        rhs c) :
    FiberOrientationCertificate F rootGood small removal rhs :=
  thresholdCertificate F rootGood small
    (thresholdLowBudget dx gamma N) (thresholdHighBudget dy gamma N)
    removal rhs lowSide highSide D.small hsides
    (D.suffix_display highSide) hhigh hlow hmargin

/-- Appendix A.2 supplies the orientation for a Part-3 fiber.  Both physical
root sides are admissible in that case; its two side capacities are converted
to the common coordinate margin. -/
noncomputable def appendixCertificate
    {b : ℕ} (F : OrderedRootedForest b) (rootGood : Fin 2 → Prop)
    (small rootReserve sideReserve X Y P Q : ℕ)
    (gamma epsilon N removal : ℝ) (rhs : Fin 2 → ℝ)
    (O : AppendixA2Orientation F small rootReserve sideReserve
      X Y P Q gamma epsilon N)
    (hroot : ∀ c, rootGood c)
    (hsideNonneg : 0 ≤ (gamma + 3 * epsilon) * N)
    (hmargin0 : (X : ℝ) + small + 1 + removal + 1 ≤ rhs 0)
    (hmargin1 : (Y : ℝ) + small + 1 + removal + 1 ≤ rhs 1) :
    FiberOrientationCertificate F rootGood small removal rhs := by
  refine {
    orient := O.orient
    root_good := fun i ↦ hroot (O.orient i 0)
    capacity := ?_
  }
  intro c
  rcases OrderedRootedForest.fin_two_eq_zero_or_one c with rfl | rfl
  · have hload : (sideLoad F O.orient 0 : ℝ) ≤ X := by
      linarith [O.capacity.side_zero]
    linarith
  · have hload : (sideLoad F O.orient 1 : ℝ) ≤ Y := by
      linarith [O.capacity.side_one]
    linarith

/-- The checked Appendix-A numeric record chooses its orientation internally
and returns the common fiber certificate. -/
noncomputable def appendixCertificateOfNumericData
    {b : ℕ} (F : OrderedRootedForest b) (rootGood : Fin 2 → Prop)
    (small rootReserve sideReserve X Y P Q : ℕ)
    (gamma epsilon N removal : ℝ) (rhs : Fin 2 → ℝ)
    (D : AppendixA2NumericData F small rootReserve sideReserve
      X Y P Q gamma epsilon N)
    (hroot : ∀ c, rootGood c)
    (hsideNonneg : 0 ≤ (gamma + 3 * epsilon) * N)
    (hmargin0 : (X : ℝ) + small + 1 + removal + 1 ≤ rhs 0)
    (hmargin1 : (Y : ℝ) + small + 1 + removal + 1 ≤ rhs 1) :
    FiberOrientationCertificate F rootGood small removal rhs :=
  appendixCertificate F rootGood small rootReserve sideReserve X Y P Q
    gamma epsilon N removal rhs
    (Classical.choice (exists_appendixA2Orientation F small rootReserve
      sideReserve X Y P Q gamma epsilon N D))
    hroot hsideNonneg hmargin0 hmargin1

end Erdos547b.ZhaoLemma58FiberOrientationCertificate

#print axioms Erdos547b.ZhaoLemma58FiberOrientationCertificate.thresholdCertificate
#print axioms Erdos547b.ZhaoLemma58FiberOrientationCertificate.classifiedThresholdCertificate
#print axioms Erdos547b.ZhaoLemma58FiberOrientationCertificate.appendixCertificate
#print axioms Erdos547b.ZhaoLemma58FiberOrientationCertificate.appendixCertificateOfNumericData
