/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58GroupedSmallForest

/-!
# The source threshold orientation in Zhao Lemma 5.4

This file contains only the finite source-side argument.  Small rooted trees
are oriented greedily so every prefix is balanced.  At a supplied numerical
threshold the construction stops balancing and sends every later branch root
to the high side.  A `ThresholdMassBudget` is the integral form of the two
scalar estimates which the real-valued displays in Parts 1 and 2 provide.
-/

open scoped BigOperators

noncomputable section

namespace Erdos547b.ZhaoLemma54ThresholdOrientation

open Finset Fintype
open Erdos547b.RegularPair
open Erdos547b.ForestMatching
open Erdos547b.ZhaoLemma58GroupedSmallForest

/-- Total order of the branches strictly before the position `t`.  The extra
position in `Fin (b+1)` allows `t=b`, meaning the whole forest. -/
def prefixOrder {b : ℕ} (F : OrderedRootedForest b) (t : Fin (b + 1)) : ℕ :=
  ∑ i, if i.val < t.val then F.size i else 0

/-- Load on one physical side strictly before position `t`. -/
def sideLoadPrefix {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) (t : Fin (b + 1)) (c : Fin 2) : ℕ :=
  ∑ i, if i.val < t.val then orientedClassSize F orient i c else 0

@[simp] theorem prefixOrder_zero {b : ℕ} (F : OrderedRootedForest b) :
    prefixOrder F 0 = 0 := by
  simp [prefixOrder]

@[simp] theorem sideLoadPrefix_zero {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) (c : Fin 2) :
    sideLoadPrefix F orient 0 c = 0 := by
  simp [sideLoadPrefix]

@[simp] theorem prefixOrder_last {b : ℕ} (F : OrderedRootedForest b) :
    prefixOrder F (Fin.last b) = F.order := by
  simp [prefixOrder, OrderedRootedForest.order, Fin.isLt]

@[simp] theorem sideLoadPrefix_last {b : ℕ}
    (F : OrderedRootedForest b) (orient : Fin b → Fin 2 ≃ Fin 2)
    (c : Fin 2) :
    sideLoadPrefix F orient (Fin.last b) c = sideLoad F orient c := by
  simp [sideLoadPrefix, sideLoad, Fin.isLt]

theorem prefixOrder_mono {b : ℕ} (F : OrderedRootedForest b)
    {s t : Fin (b + 1)} (hst : s.val ≤ t.val) :
    prefixOrder F s ≤ prefixOrder F t := by
  unfold prefixOrder
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i.val < s.val
  · have hit : i.val < t.val := hi.trans_le hst
    simp [hi, hit]
  · simp [hi]

theorem sideLoadPrefix_zero_add_one {b : ℕ}
    (F : OrderedRootedForest b) (orient : Fin b → Fin 2 ≃ Fin 2)
    (t : Fin (b + 1)) :
    sideLoadPrefix F orient t 0 + sideLoadPrefix F orient t 1 =
      prefixOrder F t := by
  classical
  rw [sideLoadPrefix, sideLoadPrefix, prefixOrder,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < t.val
  · simp only [hi, if_pos]
    exact orientedClassSize_zero_add_one F orient i
  · simp [hi]

theorem sideLoadBefore_eq_sideLoadPrefix {b : ℕ}
    (F : OrderedRootedForest b) (orient : Fin b → Fin 2 ≃ Fin 2)
    (i : Fin b) (c : Fin 2) :
    sideLoadBefore F orient i c =
      sideLoadPrefix F orient i.castSucc c := by
  classical
  simp only [sideLoadBefore, sideLoadPrefix, ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext j
    simp
  · intro j _
    rfl

@[simp] theorem prefixOrder_succ {b : ℕ}
    (F : OrderedRootedForest (b + 1)) (t : Fin (b + 1)) :
    prefixOrder F t.succ = F.size 0 + prefixOrder F.tail t := by
  rw [prefixOrder, prefixOrder, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Nat.zero_lt_succ, if_pos]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hlt : i.val < t.val
  · have hlt' : i.val + 1 < t.val + 1 := by omega
    simp only [hlt, hlt', if_true]
    rfl
  · have hlt' : ¬ (i.val + 1 < t.val + 1) := by omega
    simp only [hlt, hlt', if_false]

@[simp] theorem sideLoadPrefix_succ {b : ℕ}
    (F : OrderedRootedForest (b + 1))
    (orient : Fin (b + 1) → Fin 2 ≃ Fin 2)
    (t : Fin (b + 1)) (c : Fin 2) :
    sideLoadPrefix F orient t.succ c =
      orientedClassSize F orient 0 c +
        sideLoadPrefix F.tail (tailOrient orient) t c := by
  rw [sideLoadPrefix, sideLoadPrefix, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Nat.zero_lt_succ, if_pos]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hlt : i.val < t.val
  · have hlt' : i.val + 1 < t.val + 1 := by omega
    simp only [hlt, hlt', if_true]
    rfl
  · have hlt' : ¬ (i.val + 1 < t.val + 1) := by omega
    simp only [hlt, hlt', if_false]

/-- Prefix-strengthened balancing.  The usual balancing invariant is
preserved from arbitrary initial loads `x,y`, not merely at the end. -/
theorem exists_prefix_balanced_orientation_from
    {b : ℕ} (F : OrderedRootedForest b) (slack x y : ℕ)
    (hxy : x ≤ y + slack) (hyx : y ≤ x + slack)
    (hsmall : ∀ i, F.size i ≤ slack) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2, ∀ t : Fin (b + 1),
      x + sideLoadPrefix F orient t 0 ≤
          y + sideLoadPrefix F orient t 1 + slack ∧
        y + sideLoadPrefix F orient t 1 ≤
          x + sideLoadPrefix F orient t 0 + slack := by
  classical
  induction b generalizing x y with
  | zero =>
      let orient : Fin 0 → Fin 2 ≃ Fin 2 := fun i ↦ Fin.elim0 i
      refine ⟨orient, ?_⟩
      intro t
      have ht : t = 0 := by
        apply Fin.ext
        omega
      subst t
      simpa using And.intro hxy hyx
  | succ b ih =>
      let a := #(colourClass F 0 0)
      let d := #(colourClass F 0 1)
      have had : a + d ≤ slack := by
        have hsum := orientedClassSize_zero_add_one F
          (fun _ ↦ Equiv.refl (Fin 2)) 0
        simp only [orientedClassSize_refl] at hsum
        rw [hsum]
        exact hsmall 0
      have hsmallTail : ∀ i, F.tail.size i ≤ slack := fun i ↦ hsmall i.succ
      rcases balanced_orientation_step x y a d slack hxy hyx had with hkeep | hswap
      · obtain ⟨orientTail, htail⟩ :=
          ih F.tail (x + a) (y + d) hkeep.1 hkeep.2 hsmallTail
        let orient : Fin (b + 1) → Fin 2 ≃ Fin 2 :=
          Fin.cases (Equiv.refl (Fin 2)) orientTail
        refine ⟨orient, ?_⟩
        intro t
        rcases Fin.eq_zero_or_eq_succ t with rfl | ⟨t, rfl⟩
        · simpa using And.intro hxy hyx
        · have ht := htail t
          have h0 : orientedClassSize F orient 0 0 = a := by
            change orientedClassSize F
              (fun _ ↦ Equiv.refl (Fin 2)) 0 0 = a
            simpa only [a] using orientedClassSize_refl F 0 0
          have h1 : orientedClassSize F orient 0 1 = d := by
            change orientedClassSize F
              (fun _ ↦ Equiv.refl (Fin 2)) 0 1 = d
            simpa only [d] using orientedClassSize_refl F 0 1
          have htailOrient : tailOrient orient = orientTail := by
            funext i
            rfl
          simp only [sideLoadPrefix_succ, h0, h1, htailOrient] at ⊢
          omega
      · obtain ⟨orientTail, htail⟩ :=
          ih F.tail (x + d) (y + a) hswap.1 hswap.2 hsmallTail
        let orient : Fin (b + 1) → Fin 2 ≃ Fin 2 :=
          Fin.cases (Equiv.swap (0 : Fin 2) 1) orientTail
        refine ⟨orient, ?_⟩
        intro t
        rcases Fin.eq_zero_or_eq_succ t with rfl | ⟨t, rfl⟩
        · simpa using And.intro hxy hyx
        · have ht := htail t
          have h0 : orientedClassSize F orient 0 0 = d := by
            change orientedClassSize F
              (fun _ ↦ Equiv.swap (0 : Fin 2) 1) 0 0 = d
            simpa only [d] using orientedClassSize_swap_zero F 0
          have h1 : orientedClassSize F orient 0 1 = a := by
            change orientedClassSize F
              (fun _ ↦ Equiv.swap (0 : Fin 2) 1) 0 1 = a
            simpa only [a] using orientedClassSize_swap_one F 0
          have htailOrient : tailOrient orient = orientTail := by
            funext i
            rfl
          simp only [sideLoadPrefix_succ, h0, h1, htailOrient] at ⊢
          omega

/-- Capacity form of prefix balancing. -/
theorem exists_prefix_balanced_orientation
    {b : ℕ} (F : OrderedRootedForest b) (slack : ℕ)
    (hsmall : ∀ i, F.size i ≤ slack) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2, ∀ t c,
      2 * sideLoadPrefix F orient t c ≤ prefixOrder F t + slack := by
  obtain ⟨orient, hbalanced⟩ :=
    exists_prefix_balanced_orientation_from F slack 0 0
      (by omega) (by omega) hsmall
  refine ⟨orient, ?_⟩
  intro t c
  have htotal := sideLoadPrefix_zero_add_one F orient t
  rcases OrderedRootedForest.fin_two_eq_zero_or_one c with rfl | rfl
  · have h := (hbalanced t).1
    omega
  · have h := (hbalanced t).2
    omega

/-- The unique orientation of a two-point set which sends source colour zero
to the requested physical side. -/
def rootToSide (side : Fin 2) : Fin 2 ≃ Fin 2 :=
  if side = 0 then Equiv.refl (Fin 2) else Equiv.swap (0 : Fin 2) 1

@[simp] theorem rootToSide_zero (side : Fin 2) : rootToSide side 0 = side := by
  rcases OrderedRootedForest.fin_two_eq_zero_or_one side with rfl | rfl <;>
    simp [rootToSide]

/-- Load contributed by the fixed-root-orientation suffix. -/
def fixedSuffixLoad {b : ℕ} (F : OrderedRootedForest b)
    (cutoff : Fin (b + 1)) (highSide c : Fin 2) : ℕ :=
  ∑ i, if cutoff.val ≤ i.val then
    orientedClassSize F (fun _ ↦ rootToSide highSide) i c else 0

@[simp] theorem fixedSuffixLoad_last {b : ℕ}
    (F : OrderedRootedForest b) (highSide c : Fin 2) :
    fixedSuffixLoad F (Fin.last b) highSide c = 0 := by
  simp [fixedSuffixLoad, Fin.isLt]

/-- Integral source thresholds.  `prefixThreshold` is obtained by the low
density display; `finalThreshold` is obtained from the colour-class ratio
bounds and the total-mass display. -/
structure ThresholdMassBudget {b : ℕ}
    (F : OrderedRootedForest b) (slack lowBudget highBudget : ℕ)
    (highSide : Fin 2) where
  cutoff : Fin (b + 1)
  prefixThreshold : prefixOrder F cutoff + slack ≤ 2 * lowBudget
  finalThreshold : ∀ c,
    lowBudget + fixedSuffixLoad F cutoff highSide c ≤ highBudget

/-- Keep the prefix-balanced orientation before the cutoff and orient every
later root toward the high side. -/
def thresholdOrientation {b : ℕ} (F : OrderedRootedForest b)
    (base : Fin b → Fin 2 ≃ Fin 2) (cutoff : Fin (b + 1))
    (highSide : Fin 2) (i : Fin b) : Fin 2 ≃ Fin 2 :=
  if i.val < cutoff.val then base i else rootToSide highSide

theorem sideLoadBefore_thresholdOrientation_of_lt {b : ℕ}
    (F : OrderedRootedForest b) (base : Fin b → Fin 2 ≃ Fin 2)
    (cutoff : Fin (b + 1)) (highSide : Fin 2) (i : Fin b)
    (hi : i.val < cutoff.val) (c : Fin 2) :
    sideLoadBefore F (thresholdOrientation F base cutoff highSide) i c =
      sideLoadBefore F base i c := by
  classical
  unfold sideLoadBefore
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j.val < i.val := by simpa using hj
  simp [orientedClassSize, thresholdOrientation, hji.trans hi]

/-- Exact load identity for the switched orientation. -/
theorem sideLoad_thresholdOrientation {b : ℕ}
    (F : OrderedRootedForest b) (base : Fin b → Fin 2 ≃ Fin 2)
    (cutoff : Fin (b + 1)) (highSide c : Fin 2) :
    sideLoad F (thresholdOrientation F base cutoff highSide) c =
      sideLoadPrefix F base cutoff c +
        fixedSuffixLoad F cutoff highSide c := by
  classical
  rw [sideLoad, sideLoadPrefix, fixedSuffixLoad,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < cutoff.val
  · simp [hi, orientedClassSize, thresholdOrientation]
  · have hilate : cutoff.val ≤ i.val := Nat.le_of_not_gt hi
    simp [hi, hilate, orientedClassSize, thresholdOrientation]

/-- Pure combinatorial threshold-switch theorem used in Parts 1 and 2 of
Zhao Lemma 5.4. -/
theorem exists_thresholdSwitchOrientation
    {b : ℕ} (F : OrderedRootedForest b)
    (slack lowBudget highBudget : ℕ) (lowSide highSide : Fin 2)
    (hsmall : ∀ i, F.size i ≤ slack)
    (hsides : highSide ≠ lowSide)
    (D : ThresholdMassBudget F slack lowBudget highBudget highSide) :
    Nonempty (ThresholdSwitchOrientation F lowSide lowBudget highBudget) := by
  obtain ⟨base, hbase⟩ :=
    exists_prefix_balanced_orientation F slack hsmall
  let orient := thresholdOrientation F base D.cutoff highSide
  refine ⟨{
    orient := orient
    cutoff := D.cutoff
    early_prefix := ?_
    late_root_high := ?_
    final_load := ?_
  }⟩
  · intro i hi c
    rw [show orient = thresholdOrientation F base D.cutoff highSide from rfl,
      sideLoadBefore_thresholdOrientation_of_lt F base D.cutoff highSide i hi c,
      sideLoadBefore_eq_sideLoadPrefix F base i c]
    have hcap := hbase i.castSucc c
    have hmono : prefixOrder F i.castSucc ≤ prefixOrder F D.cutoff :=
      prefixOrder_mono F (Nat.le_of_lt hi)
    have htwo : 2 * sideLoadPrefix F base i.castSucc c ≤
        2 * lowBudget :=
      hcap.trans ((Nat.add_le_add_right hmono slack).trans D.prefixThreshold)
    exact Nat.le_of_mul_le_mul_left htwo (by omega)
  · intro i hi
    have hnot : ¬i.val < D.cutoff.val := Nat.not_lt.mpr hi
    rw [show orient = thresholdOrientation F base D.cutoff highSide from rfl]
    simp only [branchRootSide, thresholdOrientation, hnot, if_false,
      rootToSide_zero]
    exact hsides
  · intro c
    rw [show orient = thresholdOrientation F base D.cutoff highSide from rfl,
      sideLoad_thresholdOrientation]
    have hcap := hbase D.cutoff c
    have hpref : sideLoadPrefix F base D.cutoff c ≤ lowBudget := by
      have htwo : 2 * sideLoadPrefix F base D.cutoff c ≤
          2 * lowBudget := hcap.trans D.prefixThreshold
      exact Nat.le_of_mul_le_mul_left htwo (by omega)
    exact (Nat.add_le_add_right hpref
      (fixedSuffixLoad F D.cutoff highSide c)).trans
        (D.finalThreshold c)

/-- Part 1 is the degenerate switch after the last branch: all prefixes and
the final load are controlled by the same balanced-capacity estimate. -/
theorem exists_balancedThresholdSwitchOrientation
    {b : ℕ} (F : OrderedRootedForest b)
    (slack lowBudget highBudget : ℕ) (lowSide highSide : Fin 2)
    (hsmall : ∀ i, F.size i ≤ slack)
    (hsides : highSide ≠ lowSide)
    (hcapacity : F.order + slack ≤ 2 * lowBudget)
    (hlowHigh : lowBudget ≤ highBudget) :
    Nonempty (ThresholdSwitchOrientation F lowSide lowBudget highBudget) := by
  let D : ThresholdMassBudget F slack lowBudget highBudget highSide :=
    { cutoff := Fin.last b
      prefixThreshold := by simpa using hcapacity
      finalThreshold := by
        intro c
        simpa using hlowHigh }
  exact exists_thresholdSwitchOrientation F slack lowBudget highBudget
    lowSide highSide hsmall hsides D

#print axioms exists_prefix_balanced_orientation
#print axioms exists_thresholdSwitchOrientation
#print axioms exists_balancedThresholdSwitchOrientation

end Erdos547b.ZhaoLemma54ThresholdOrientation
