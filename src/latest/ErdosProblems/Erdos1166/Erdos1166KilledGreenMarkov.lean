/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166KilledGreen

namespace Erdos1166.KilledGreen

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- Finite increment-block form of first entrance to a point. -/
def blockFirstEntrance (D : Set Site) (x y : Site) (m : ℕ) :
    Set (Fin m → Direction) :=
  {η | (∀ r : Fin (m + 1), blockWalkFrom x η r ∈ D) ∧
    blockWalkFrom x η ⟨m, by omega⟩ = y ∧
    ∀ r : Fin m, blockWalkFrom x η r.castSucc ≠ y}

theorem measurableSet_blockFirstEntrance (D : Set Site) (x y : Site) (m : ℕ) :
    MeasurableSet (blockFirstEntrance D x y m) :=
  MeasurableSet.of_discrete

theorem iidBlock_zero_preimage_blockFirstEntrance
    (D : Set Site) (x y : Site) (m : ℕ) :
    iidBlock (X := Direction) 0 m ⁻¹' blockFirstEntrance D x y m =
      firstEntranceEvent D x y m := by
  ext ω
  simp only [Set.mem_preimage, blockFirstEntrance, Set.mem_ofPred_eq,
    firstEntranceEvent]
  constructor
  · rintro ⟨hstay, hend, havoid⟩
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      let r' : Fin (m + 1) := ⟨r, by omega⟩
      rw [← blockWalkFrom_iidBlock_zero_eq_walkFrom x m ω r']
      exact hstay r'
    · rw [← blockWalkFrom_iidBlock_zero_eq_walkFrom x m ω ⟨m, by omega⟩]
      exact hend
    · intro r hr
      let r' : Fin m := ⟨r, hr⟩
      have hne := havoid r'
      rw [blockWalkFrom_iidBlock_zero_eq_walkFrom x m ω r'.castSucc] at hne
      simpa [r'] using hne
  · rintro ⟨hstay, hend, havoid⟩
    refine ⟨?_, ?_, ?_⟩
    · intro r
      rw [blockWalkFrom_iidBlock_zero_eq_walkFrom x m ω r]
      exact hstay r (Nat.le_of_lt_succ r.isLt)
    · rw [blockWalkFrom_iidBlock_zero_eq_walkFrom x m ω ⟨m, by omega⟩]
      exact hend
    · intro r
      rw [blockWalkFrom_iidBlock_zero_eq_walkFrom x m ω r.castSucc]
      exact havoid r (by omega)

theorem finitePi_blockFirstEntrance_eq
    (D : Set Site) (x y : Site) (m : ℕ) :
    (Measure.infinitePi fun _ : Fin m ↦ directionLaw)
        (blockFirstEntrance D x y m) =
      entranceWeight D x y m := by
  rw [← iidBlock_map directionLaw 0 m]
  rw [Measure.map_apply (measurable_iidBlock 0 m)
    (measurableSet_blockFirstEntrance D x y m)]
  exact congrArg incrementLaw
    (iidBlock_zero_preimage_blockFirstEntrance D x y m)

/-- First entrance to a finite barrier `B` at `z`, before any visit to the
target `y`. -/
def barrierPrefixEvent (D : Set Site) (x y : Site) (B : Finset Site)
    (j : ℕ) (z : Site) : Set (ℕ → Direction) :=
  {ω | (∀ r, r ≤ j → walkFrom x ω r ∈ D) ∧
    walkFrom x ω j = z ∧ z ∈ B ∧
    (∀ r, r < j → walkFrom x ω r ∉ B) ∧
    ∀ r, r < j → walkFrom x ω r ≠ y}

noncomputable def barrierPrefixWeight (D : Set Site) (x y : Site)
    (B : Finset Site) (j : ℕ) (z : Site) : ℝ≥0∞ :=
  incrementLaw (barrierPrefixEvent D x y B j z)

noncomputable def barrierEntranceWeight (D : Set Site) (x y : Site)
    (B : Finset Site) (z : Site) : ℝ≥0∞ :=
  ∑' j : ℕ, barrierPrefixWeight D x y B j z

theorem measurableSet_barrierPrefixEvent_iidHistory
    (D : Set Site) (x y : Site) (B : Finset Site) (j : ℕ) (z : Site) :
    MeasurableSet[iidHistory (X := Direction) j]
      (barrierPrefixEvent D x y B j z) := by
  have hstay : MeasurableSet[iidHistory (X := Direction) j]
      {ω : ℕ → Direction | ∀ r, r ≤ j → walkFrom x ω r ∈ D} := by
    have heq : {ω : ℕ → Direction | ∀ r, r ≤ j → walkFrom x ω r ∈ D} =
        ⋂ r : ℕ, ⋂ (_ : r ≤ j), {ω | walkFrom x ω r ∈ D} := by
      ext ω
      simp
    rw [heq]
    exact MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun hr ↦
      (Set.to_countable D).measurableSet.preimage
        (measurable_walkFrom_iidHistory x hr)
  have hend : MeasurableSet[iidHistory (X := Direction) j]
      {ω : ℕ → Direction | walkFrom x ω j = z} :=
    measurableSet_eq_fun (measurable_walkFrom_iidHistory x le_rfl) measurable_const
  have havoidB : MeasurableSet[iidHistory (X := Direction) j]
      {ω : ℕ → Direction | ∀ r, r < j → walkFrom x ω r ∉ B} := by
    have heq : {ω : ℕ → Direction | ∀ r, r < j → walkFrom x ω r ∉ B} =
        ⋂ r : ℕ, ⋂ (_ : r < j), {ω | walkFrom x ω r ∉ B} := by
      ext ω
      simp
    rw [heq]
    exact MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun hr ↦
      ((B.countable_toSet.measurableSet).preimage
        (measurable_walkFrom_iidHistory x hr.le)).compl
  have havoidY : MeasurableSet[iidHistory (X := Direction) j]
      {ω : ℕ → Direction | ∀ r, r < j → walkFrom x ω r ≠ y} := by
    have heq : {ω : ℕ → Direction | ∀ r, r < j → walkFrom x ω r ≠ y} =
        ⋂ r : ℕ, ⋂ (_ : r < j), {ω | walkFrom x ω r ≠ y} := by
      ext ω
      simp
    rw [heq]
    exact MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun hr ↦
      (measurableSet_eq_fun (measurable_walkFrom_iidHistory x hr.le)
        measurable_const).compl
  exact hstay.inter (hend.inter
    (MeasurableSet.const (z ∈ B) |>.inter (havoidB.inter havoidY)))

def barrierThenTargetEvent (D : Set Site) (x y : Site) (B : Finset Site)
    (n j : ℕ) (z : Site) : Set (ℕ → Direction) :=
  barrierPrefixEvent D x y B j z ∩
    iidBlock (X := Direction) j (n - j) ⁻¹'
      blockFirstEntrance D z y (n - j)

theorem measure_barrierThenTargetEvent
    {D : Set Site} {x y : Site} {B : Finset Site} {n j : ℕ} {z : Site}
    (_hjn : j ≤ n) :
    incrementLaw (barrierThenTargetEvent D x y B n j z) =
      barrierPrefixWeight D x y B j z * entranceWeight D z y (n - j) := by
  have h := measure_inter_iidBlock_eq_mul directionLaw j (n - j)
    (measurableSet_barrierPrefixEvent_iidHistory D x y B j z)
    (measurableSet_blockFirstEntrance D z y (n - j))
  rw [finitePi_blockFirstEntrance_eq] at h
  simpa [incrementLaw, barrierThenTargetEvent, barrierPrefixWeight] using h

theorem barrierThenTargetEvent_disjoint_of_ne
    {D : Set Site} {x y : Site} {B : Finset Site} {n j k : ℕ} {z w : Site}
    (hpair : (j, z) ≠ (k, w)) :
    Disjoint (barrierThenTargetEvent D x y B n j z)
      (barrierThenTargetEvent D x y B n k w) := by
  rw [Set.disjoint_left]
  intro ω hj hk
  rcases hj.1 with ⟨hstayj, hjz, hzB, havoidBj, havoidYj⟩
  rcases hk.1 with ⟨hstayk, hkw, hwB, havoidBk, havoidYk⟩
  rcases lt_trichotomy j k with hjk | hjk | hkj
  · exact havoidBk j hjk (hjz ▸ hzB)
  · subst k
    apply hpair
    simp only [Prod.mk.injEq, true_and]
    exact hjz.symm.trans hkw
  · exact havoidBj k hkj (hkw ▸ hwB)

theorem pairwiseDisjoint_barrierThenTargetEvent
    (D : Set Site) (x y : Site) (B : Finset Site) (n : ℕ) :
    Set.PairwiseDisjoint
      (↑((Finset.range (n + 1)).product B))
      (fun p : ℕ × Site ↦ barrierThenTargetEvent D x y B n p.1 p.2) := by
  intro p hp q hq hpq
  exact barrierThenTargetEvent_disjoint_of_ne hpq

/-- Every killed first entrance to `y` from `x` crosses `B`.  This is the
purely pathwise separator hypothesis used by the strong Markov decomposition. -/
def BarrierSeparatesFirstEntrance (D : Set Site) (x y : Site)
    (B : Finset Site) : Prop :=
  ∀ ω n, ω ∈ firstEntranceEvent D x y n →
    ∃ j, j ≤ n ∧ walkFrom x ω j ∈ B

theorem iUnion_barrierThenTargetEvent
    (D : Set Site) (x y : Site) (B : Finset Site)
    (hsep : BarrierSeparatesFirstEntrance D x y B) (n : ℕ) :
    (⋃ p ∈ (Finset.range (n + 1)).product B,
      barrierThenTargetEvent D x y B n p.1 p.2) =
      firstEntranceEvent D x y n := by
  ext ω
  constructor
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨p, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hpMem, hp⟩
    have hjn : p.1 ≤ n := by
      exact Nat.le_of_lt_succ
        (Finset.mem_range.mp (Finset.mem_product.mp hpMem).1)
    rcases hp with ⟨hprefix, hsuffix⟩
    rcases hprefix with ⟨hstayPrefix, hjz, hzB, havoidB, havoidY⟩
    rcases hsuffix with ⟨hstaySuffix, hendSuffix, havoidSuffix⟩
    refine ⟨?_, ?_, ?_⟩
    · intro r hrn
      by_cases hrj : r ≤ p.1
      · exact hstayPrefix r hrj
      · let q : Fin (n - p.1 + 1) := ⟨r - p.1, by omega⟩
        have heq := blockWalkFrom_iidBlock_eq_walkFrom x p.1 (n - p.1) ω q
        rw [hjz] at heq
        have ht : p.1 + (q : ℕ) = r := by
          dsimp only [q]
          omega
        rw [ht] at heq
        exact heq ▸ hstaySuffix q
    · let q : Fin (n - p.1 + 1) := ⟨n - p.1, by omega⟩
      have heq := blockWalkFrom_iidBlock_eq_walkFrom x p.1 (n - p.1) ω q
      rw [hjz] at heq
      have ht : p.1 + (q : ℕ) = n := by
        dsimp only [q]
        omega
      rw [ht] at heq
      exact heq ▸ hendSuffix
    · intro r hrn hry
      by_cases hrj : r < p.1
      · exact havoidY r hrj hry
      · let q : Fin (n - p.1) := ⟨r - p.1, by omega⟩
        have heq := blockWalkFrom_iidBlock_eq_walkFrom x p.1 (n - p.1) ω q.castSucc
        rw [hjz] at heq
        have ht : p.1 + (q.castSucc : ℕ) = r := by
          change p.1 + (r - p.1) = r
          omega
        rw [ht] at heq
        exact havoidSuffix q (heq.trans hry)
  · intro hω
    rcases hω with ⟨hstay, hny, havoidY⟩
    rcases hsep ω n ⟨hstay, hny, havoidY⟩ with ⟨j0, hj0n, hj0B⟩
    let J := (Finset.range (n + 1)).filter fun j ↦ walkFrom x ω j ∈ B
    have hJ : J.Nonempty := by
      refine ⟨j0, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (by omega), hj0B⟩
    let j := J.min' hJ
    have hjJ : j ∈ J := J.min'_mem hJ
    have hjn : j ≤ n :=
      Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hjJ).1)
    let z := walkFrom x ω j
    have hzB : z ∈ B := (Finset.mem_filter.mp hjJ).2
    have havoidB : ∀ r, r < j → walkFrom x ω r ∉ B := by
      intro r hrj hrB
      have hrJ : r ∈ J := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_range.mpr (by omega), hrB⟩
      exact (not_le_of_gt hrj) (J.min'_le r hrJ)
    apply Set.mem_iUnion.mpr
    refine ⟨(j, z), Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · apply Finset.mem_product.mpr
      exact ⟨Finset.mem_range.mpr (by omega), hzB⟩
    · constructor
      · exact ⟨fun r hr ↦ hstay r (hr.trans hjn), rfl, hzB,
          havoidB, fun r hr ↦ havoidY r (hr.trans_le hjn)⟩
      · refine ⟨?_, ?_, ?_⟩
        · intro q
          have ht : j + (q : ℕ) ≤ n := by omega
          have heq := blockWalkFrom_iidBlock_eq_walkFrom x j (n - j) ω q
          change blockWalkFrom z (iidBlock j (n - j) ω) q ∈ D
          exact heq ▸ hstay (j + q) ht
        · let q : Fin (n - j + 1) := ⟨n - j, by omega⟩
          have heq := blockWalkFrom_iidBlock_eq_walkFrom x j (n - j) ω q
          have ht : j + (q : ℕ) = n := by
            dsimp only [q]
            omega
          change blockWalkFrom z (iidBlock j (n - j) ω) q = y
          rw [heq, ht]
          exact hny
        · intro q
          have ht : j + (q : ℕ) < n := by omega
          have heq := blockWalkFrom_iidBlock_eq_walkFrom x j (n - j) ω q.castSucc
          change blockWalkFrom z (iidBlock j (n - j) ω) q.castSucc ≠ y
          rw [heq]
          exact havoidY (j + q) ht

theorem measurableSet_barrierThenTargetEvent
    (D : Set Site) (x y : Site) (B : Finset Site)
    (n j : ℕ) (z : Site) :
    MeasurableSet (barrierThenTargetEvent D x y B n j z) := by
  exact (ProbabilityTheory.iidHistory_le j _
      (measurableSet_barrierPrefixEvent_iidHistory D x y B j z)).inter
    ((measurable_iidBlock j (n - j))
      (measurableSet_blockFirstEntrance D z y (n - j)))

theorem entranceWeight_eq_barrier_convolution
    (D : Set Site) (x y : Site) (B : Finset Site)
    (hsep : BarrierSeparatesFirstEntrance D x y B) (n : ℕ) :
    entranceWeight D x y n =
      ∑ p ∈ (Finset.range (n + 1)).product B,
        barrierPrefixWeight D x y B p.1 p.2 *
          entranceWeight D p.2 y (n - p.1) := by
  calc
    entranceWeight D x y n = incrementLaw
        (⋃ p ∈ (Finset.range (n + 1)).product B,
          barrierThenTargetEvent D x y B n p.1 p.2) := by
      rw [iUnion_barrierThenTargetEvent D x y B hsep]
      rfl
    _ = ∑ p ∈ (Finset.range (n + 1)).product B,
        incrementLaw (barrierThenTargetEvent D x y B n p.1 p.2) := by
      exact measure_biUnion_finset
        (pairwiseDisjoint_barrierThenTargetEvent D x y B n)
        (fun p _ ↦ measurableSet_barrierThenTargetEvent D x y B n p.1 p.2)
    _ = ∑ p ∈ (Finset.range (n + 1)).product B,
        barrierPrefixWeight D x y B p.1 p.2 *
          entranceWeight D p.2 y (n - p.1) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact measure_barrierThenTargetEvent
        (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hp).1))

theorem ennreal_tsum_finset_sum {α : Type*} (s : Finset α)
    (f : ℕ → α → ℝ≥0∞) :
    (∑' n : ℕ, ∑ a ∈ s, f n a) = ∑ a ∈ s, ∑' n : ℕ, f n a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [ENNReal.tsum_add, ih]

/-- Exact finite-boundary strong Markov decomposition.  The coefficient at
`z` is the probability mass of first crossing `B` at `z`, before the target
or the killing boundary. -/
theorem hittingWeight_eq_sum_barrierEntrance_mul
    (D : Set Site) (x y : Site) (B : Finset Site)
    (hsep : BarrierSeparatesFirstEntrance D x y B) :
    hittingWeight D x y =
      ∑ z ∈ B, barrierEntranceWeight D x y B z * hittingWeight D z y := by
  unfold hittingWeight barrierEntranceWeight
  calc
    (∑' n : ℕ, entranceWeight D x y n) =
        ∑' n : ℕ, ∑ p ∈ (Finset.range (n + 1)).product B,
          barrierPrefixWeight D x y B p.1 p.2 *
            entranceWeight D p.2 y (n - p.1) := by
      apply tsum_congr
      exact entranceWeight_eq_barrier_convolution D x y B hsep
    _ = ∑' n : ℕ, ∑ z ∈ B, ∑ j ∈ Finset.range (n + 1),
          barrierPrefixWeight D x y B j z * entranceWeight D z y (n - j) := by
      apply tsum_congr
      intro n
      calc
        (∑ p ∈ (Finset.range (n + 1)).product B,
            barrierPrefixWeight D x y B p.1 p.2 *
              entranceWeight D p.2 y (n - p.1)) =
            ∑ j ∈ Finset.range (n + 1), ∑ z ∈ B,
              barrierPrefixWeight D x y B j z *
                entranceWeight D z y (n - j) :=
          Finset.sum_product _ _ _
        _ = ∑ z ∈ B, ∑ j ∈ Finset.range (n + 1),
              barrierPrefixWeight D x y B j z *
                entranceWeight D z y (n - j) := Finset.sum_comm
    _ = ∑ z ∈ B, ∑' n : ℕ, ∑ j ∈ Finset.range (n + 1),
          barrierPrefixWeight D x y B j z * entranceWeight D z y (n - j) := by
      exact ennreal_tsum_finset_sum B
        (fun n z ↦ ∑ j ∈ Finset.range (n + 1),
          barrierPrefixWeight D x y B j z * entranceWeight D z y (n - j))
    _ = ∑ z ∈ B, (∑' j : ℕ, barrierPrefixWeight D x y B j z) *
          (∑' k : ℕ, entranceWeight D z y k) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact (ennreal_tsum_mul_tsum_eq_tsum_sum_range
        (fun j ↦ barrierPrefixWeight D x y B j z)
        (fun k ↦ entranceWeight D z y k)).symm

theorem killedGreen_eq_sum_barrierEntrance_mul
    (D : Set Site) (x y : Site) (B : Finset Site)
    (hsep : BarrierSeparatesFirstEntrance D x y B) :
    killedGreen D x y =
      ∑ z ∈ B, barrierEntranceWeight D x y B z * killedGreen D z y := by
  calc
    killedGreen D x y = hittingWeight D x y * killedGreen D y y :=
      killedGreen_eq_hittingWeight_mul_diagonal D x y
    _ = (∑ z ∈ B,
          barrierEntranceWeight D x y B z * hittingWeight D z y) *
          killedGreen D y y := by
      rw [hittingWeight_eq_sum_barrierEntrance_mul D x y B hsep]
    _ = ∑ z ∈ B,
          (barrierEntranceWeight D x y B z * hittingWeight D z y) *
            killedGreen D y y := by
      rw [Finset.sum_mul]
    _ = ∑ z ∈ B,
          barrierEntranceWeight D x y B z * killedGreen D z y := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [killedGreen_eq_hittingWeight_mul_diagonal D z y]
      exact mul_assoc _ _ _

theorem walkFrom_succ (x : Site) (ω : ℕ → Direction) (n : ℕ) :
    walkFrom x ω (n + 1) = walkFrom x ω n + directionStep (ω n) := by
  simp [walkFrom, simpleRandomWalk, Finset.sum_range_succ, add_assoc]

/-- Points of a finite set that can be entered in one canonical walk step
from outside the set. -/
def finiteEntranceBoundary (A : Finset Site) : Finset Site :=
  A.filter fun z ↦ ∃ d : Direction, z - directionStep d ∉ A

theorem finiteEntranceBoundary_separates
    (D : Set Site) (x y : Site) (A : Finset Site)
    (hx : x ∉ A) (hy : y ∈ A) :
    BarrierSeparatesFirstEntrance D x y (finiteEntranceBoundary A) := by
  intro ω n hω
  let J := (Finset.range (n + 1)).filter fun j ↦ walkFrom x ω j ∈ A
  have hJ : J.Nonempty := by
    refine ⟨n, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (by omega), hω.2.1 ▸ hy⟩
  let j := J.min' hJ
  have hjJ : j ∈ J := J.min'_mem hJ
  have hjn : j ≤ n :=
    Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hjJ).1)
  have hjA : walkFrom x ω j ∈ A := (Finset.mem_filter.mp hjJ).2
  have hjpos : 0 < j := by
    by_contra hj0
    have hjzero : j = 0 := Nat.eq_zero_of_not_pos hj0
    apply hx
    simpa [hjzero, walkFrom, simpleRandomWalk] using hjA
  refine ⟨j, hjn, ?_⟩
  rw [finiteEntranceBoundary, Finset.mem_filter]
  refine ⟨hjA, ⟨ω (j - 1), ?_⟩⟩
  have hprev : walkFrom x ω (j - 1) ∉ A := by
    intro hprevA
    have hprevJ : j - 1 ∈ J := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (by omega), hprevA⟩
    exact (not_le_of_gt (by omega : j - 1 < j)) (J.min'_le (j - 1) hprevJ)
  have hstep := walkFrom_succ x ω (j - 1)
  have htime : j - 1 + 1 = j := by omega
  rw [htime] at hstep
  have heq : walkFrom x ω j - directionStep (ω (j - 1)) =
      walkFrom x ω (j - 1) := by
    rw [hstep]
    abel
  rwa [heq]

noncomputable def squareEntranceBoundary (r : ℕ) : Finset Site :=
  finiteEntranceBoundary (squareDisk r)

theorem squareEntranceBoundary_separates
    (D : Set Site) (x y : Site) (r : ℕ)
    (hx : x ∉ squareDisk r) (hy : y ∈ squareDisk r) :
    BarrierSeparatesFirstEntrance D x y (squareEntranceBoundary r) :=
  finiteEntranceBoundary_separates D x y (squareDisk r) hx hy

/-- Strong Markov decomposition across an intermediate square.  This is the
exact annular identity used before inserting any Green-function asymptotics. -/
theorem hittingWeight_eq_sum_squareEntranceBoundary
    (D : Set Site) (x y : Site) (r : ℕ)
    (hx : x ∉ squareDisk r) (hy : y ∈ squareDisk r) :
    hittingWeight D x y =
      ∑ z ∈ squareEntranceBoundary r,
        barrierEntranceWeight D x y (squareEntranceBoundary r) z *
          hittingWeight D z y :=
  hittingWeight_eq_sum_barrierEntrance_mul D x y (squareEntranceBoundary r)
    (squareEntranceBoundary_separates D x y r hx hy)

/-- The nested finite-disk specialization. -/
theorem diskHittingWeight_eq_sum_squareEntranceBoundary
    {r R : ℕ} (x y : Site) (hx : x ∉ squareDisk r)
    (hy : y ∈ squareDisk r) :
    diskHittingWeight R x y =
      ∑ z ∈ squareEntranceBoundary r,
        barrierEntranceWeight (squareDisk R : Set Site) x y
            (squareEntranceBoundary r) z *
          diskHittingWeight R z y :=
  hittingWeight_eq_sum_squareEntranceBoundary
    (squareDisk R : Set Site) x y r hx hy

theorem diskGreen_eq_sum_squareEntranceBoundary
    {r R : ℕ} (x y : Site) (hx : x ∉ squareDisk r)
    (hy : y ∈ squareDisk r) :
    diskGreen R x y =
      ∑ z ∈ squareEntranceBoundary r,
        barrierEntranceWeight (squareDisk R : Set Site) x y
            (squareEntranceBoundary r) z *
          diskGreen R z y :=
  killedGreen_eq_sum_barrierEntrance_mul
    (squareDisk R : Set Site) x y (squareEntranceBoundary r)
    (squareEntranceBoundary_separates (squareDisk R : Set Site) x y r hx hy)

end Erdos1166.KilledGreen
