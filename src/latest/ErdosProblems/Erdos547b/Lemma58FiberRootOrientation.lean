/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma54CanonicalThresholdOrientation
import ErdosProblems.Erdos547b.Lemma54AppendixA
import ErdosProblems.Erdos547b.Lemma54ThresholdSourceNumerics

/-!
# Root-admissible orientations without a static endpoint-load cap

The orientation part of Zhao Lemma 5.4 is independent of the later dynamic
regular-pair realization.  This small certificate deliberately records only
that orientation and the admissibility of every branch-root side.  It avoids
the stronger `FiberOrientationCertificate.capacity` field, which is not a
conclusion of Lemma 5.8.
-/

open scoped BigOperators
noncomputable section

namespace Erdos547b.ZhaoLemma58FiberRootOrientation

open Finset Fintype
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma54ThresholdOrientation
open Erdos547b.ZhaoLemma54ThresholdNumerics
open Erdos547b.ZhaoLemma54CanonicalThresholdOrientation
open Erdos547b.ZhaoLemma54ThresholdSourceNumerics
open Erdos547b.ZhaoLemma54AppendixA

/-- An orientation whose branch roots all use admissible physical sides. -/
structure FiberRootOrientation {b : ℕ}
    (F : OrderedRootedForest b) (rootGood : Fin 2 → Prop) : Type where
  orient : Fin b → Fin 2 ≃ Fin 2
  root_good : ∀ i, rootGood (orient i 0)

/-- A root-admissible orientation together with one honest complete-fiber
side-load bound.  Unlike the older static fiber certificate, this record says
nothing about a host pair or a fixed endpoint capacity. -/
structure FiberRootOrientationWithLoad {b : ℕ}
    (F : OrderedRootedForest b) (rootGood : Fin 2 → Prop) : Type where
  orient : Fin b → Fin 2 ≃ Fin 2
  root_good : ∀ i, rootGood (orient i 0)
  loadBound : ℕ
  load_le : ∀ c, sideLoad F orient c ≤ loadBound

/-- Add a separately proved complete-fiber load bound to a root-only
orientation. -/
def FiberRootOrientation.withLoad {b : ℕ}
    {F : OrderedRootedForest b} {rootGood : Fin 2 → Prop}
    (D : FiberRootOrientation F rootGood) (loadBound : ℕ)
    (hload : ∀ c, sideLoad F D.orient c ≤ loadBound) :
    FiberRootOrientationWithLoad F rootGood where
  orient := D.orient
  root_good := D.root_good
  loadBound := loadBound
  load_le := hload

/-- The canonical maximal-cutoff orientation needs the low-side root fact
only when its integral low budget is nonzero. -/
noncomputable def thresholdRootOrientation
    {b : ℕ} (F : OrderedRootedForest b) (rootGood : Fin 2 → Prop)
    (small lowBudget highBudget : ℕ)
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
    (hlow : lowBudget ≠ 0 → rootGood lowSide) :
    FiberRootOrientation F rootGood := by
  let O := canonicalActualThresholdSwitchOrientation F small lowBudget
    highBudget lowSide highSide hsmall hsides hfinal
  refine { orient := O.orient, root_good := ?_ }
  intro i
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

/-- Classified Parts-1/2 source numerics instantiate the root-only
threshold certificate. -/
noncomputable def classifiedThresholdRootOrientation
    {b : ℕ} (F : OrderedRootedForest b) (rootGood : Fin 2 → Prop)
    (ratio dx dy gamma epsilon N : ℝ) (small : ℕ)
    (lowSide highSide : Fin 2)
    (D : ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N small)
    (hsides : highSide ≠ lowSide)
    (hhigh : rootGood highSide)
    (hlow : thresholdLowBudget dx gamma N ≠ 0 → rootGood lowSide) :
    FiberRootOrientation F rootGood :=
  thresholdRootOrientation F rootGood small
    (thresholdLowBudget dx gamma N) (thresholdHighBudget dy gamma N)
    lowSide highSide D.small hsides (D.suffix_display highSide) hhigh hlow

/-- Although `classifiedThresholdRootOrientation` deliberately omits a
static host-capacity field, its literal complete-fiber side loads still obey
the high integral source budget.  This is the load estimate needed by the
synchronized online realization, where owner batches are processed against
changing residual host sets. -/
theorem classifiedThresholdRootOrientation_sideLoad_le
    {b : ℕ} (F : OrderedRootedForest b) (rootGood : Fin 2 → Prop)
    (ratio dx dy gamma epsilon N : ℝ) (small : ℕ)
    (lowSide highSide : Fin 2)
    (D : ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N small)
    (hsides : highSide ≠ lowSide)
    (hhigh : rootGood highSide)
    (hlow : thresholdLowBudget dx gamma N ≠ 0 → rootGood lowSide)
    (c : Fin 2) :
    sideLoad F
        (classifiedThresholdRootOrientation F rootGood ratio dx dy gamma
          epsilon N small lowSide highSide D hsides hhigh hlow).orient c ≤
      thresholdHighBudget dy gamma N := by
  let O := canonicalActualThresholdSwitchOrientation F small
    (thresholdLowBudget dx gamma N) (thresholdHighBudget dy gamma N)
    lowSide highSide D.small hsides (D.suffix_display highSide)
  change sideLoad F O.orient c ≤ thresholdHighBudget dy gamma N
  exact O.final_load c

/-- Package the classified threshold orientation with its exact high-side
source budget, still without asserting a static host capacity. -/
noncomputable def classifiedThresholdRootOrientationWithLoad
    {b : ℕ} (F : OrderedRootedForest b) (rootGood : Fin 2 → Prop)
    (ratio dx dy gamma epsilon N : ℝ) (small : ℕ)
    (lowSide highSide : Fin 2)
    (D : ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N small)
    (hsides : highSide ≠ lowSide)
    (hhigh : rootGood highSide)
    (hlow : thresholdLowBudget dx gamma N ≠ 0 → rootGood lowSide) :
    FiberRootOrientationWithLoad F rootGood where
  orient := (classifiedThresholdRootOrientation F rootGood ratio dx dy gamma
    epsilon N small lowSide highSide D hsides hhigh hlow).orient
  root_good := (classifiedThresholdRootOrientation F rootGood ratio dx dy
    gamma epsilon N small lowSide highSide D hsides hhigh hlow).root_good
  loadBound := thresholdHighBudget dy gamma N
  load_le := classifiedThresholdRootOrientation_sideLoad_le F rootGood ratio
    dx dy gamma epsilon N small lowSide highSide D hsides hhigh hlow

/-- Appendix A.2 chooses its orientation and both sides are root-admissible. -/
noncomputable def appendixRootOrientation
    {b : ℕ} (F : OrderedRootedForest b) (rootGood : Fin 2 → Prop)
    (small rootReserve sideReserve X Y P Q : ℕ)
    (gamma epsilon N : ℝ)
    (D : AppendixA2NumericData F small rootReserve sideReserve
      X Y P Q gamma epsilon N)
    (hroot : ∀ c, rootGood c) :
    FiberRootOrientation F rootGood := by
  let O := Classical.choice (exists_appendixA2Orientation F small rootReserve
    sideReserve X Y P Q gamma epsilon N D)
  exact { orient := O.orient, root_good := fun i ↦ hroot (O.orient i 0) }

end Erdos547b.ZhaoLemma58FiberRootOrientation

#print axioms Erdos547b.ZhaoLemma58FiberRootOrientation.thresholdRootOrientation
#print axioms Erdos547b.ZhaoLemma58FiberRootOrientation.classifiedThresholdRootOrientation
#print axioms Erdos547b.ZhaoLemma58FiberRootOrientation.classifiedThresholdRootOrientation_sideLoad_le
#print axioms Erdos547b.ZhaoLemma58FiberRootOrientation.classifiedThresholdRootOrientationWithLoad
#print axioms Erdos547b.ZhaoLemma58FiberRootOrientation.appendixRootOrientation
