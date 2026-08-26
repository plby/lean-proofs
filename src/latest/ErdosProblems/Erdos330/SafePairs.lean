/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 330, positive upper density formulation.
Informal authors: GPT-5.5 Pro, David Turturean.
Formal authors: Codex, GPT-5.5 Pro, Allen Graham Hart.
Source: https://www.erdosproblems.com/forum/thread/330#post-6271
https://github.com/AllenGrahamHart/FormalConjectures-Bench/tree/6160036caab0dcee80395ba3beb7b6ef2731604e/formalizations/erdos330
Original Lean/Mathlib version: 4.27.0.
-/
import ErdosProblems.Erdos330.FiniteChoice

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Safe-pair lemmas for Erdős Problem 330

This file contains the finite-coordinate choices used in the two-safe-pairs
part of the CRT gadget.
-/

namespace Erdos330

open scoped Pointwise

structure SafePairData (α : Type*) [Zero α] [Add α] (e : α) where
  c1 : α
  d1 : α
  c2 : α
  d2 : α
  c1_ne_zero : c1 ≠ 0
  d1_ne_zero : d1 ≠ 0
  c2_ne_zero : c2 ≠ 0
  d2_ne_zero : d2 ≠ 0
  sum1 : c1 + d1 = e
  sum2 : c2 + d2 = e
  c1_ne_d1 : c1 ≠ d1
  c2_ne_d2 : c2 ≠ d2
  c1_ne_c2 : c1 ≠ c2
  c1_ne_d2 : c1 ≠ d2
  d1_ne_c2 : d1 ≠ c2
  d1_ne_d2 : d1 ≠ d2

namespace SafePairData

variable {α : Type*} [Zero α] [Add α] {e : α} (data : SafePairData α e)

def c : Bool → α
  | true => data.c1
  | false => data.c2

def d : Bool → α
  | true => data.d1
  | false => data.d2

@[simp] lemma c_true : data.c true = data.c1 := rfl
@[simp] lemma c_false : data.c false = data.c2 := rfl
@[simp] lemma d_true : data.d true = data.d1 := rfl
@[simp] lemma d_false : data.d false = data.d2 := rfl

lemma c_ne_zero (ν : Bool) : data.c ν ≠ 0 := by
  cases ν <;> simp [c, data.c1_ne_zero, data.c2_ne_zero]

lemma d_ne_zero (ν : Bool) : data.d ν ≠ 0 := by
  cases ν <;> simp [d, data.d1_ne_zero, data.d2_ne_zero]

lemma c_add_d (ν : Bool) : data.c ν + data.d ν = e := by
  cases ν <;> simp [c, d, data.sum1, data.sum2]

lemma c_ne_d (ν : Bool) : data.c ν ≠ data.d ν := by
  cases ν <;> simp [c, d, data.c1_ne_d1, data.c2_ne_d2]

end SafePairData

structure NonzeroAddPair (α : Type*) [Zero α] [Add α] (z : α) where
  left : α
  right : α
  left_ne_zero : left ≠ 0
  right_ne_zero : right ≠ 0
  sum_eq : left + right = z

lemma zmod_natCast_ne_zero_of_pos_lt {p k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    ((k : ℕ) : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hle : p ≤ k := Nat.le_of_dvd hk0 h
  omega

lemma zmod_two_ne_zero_of_ge_seven (p : ℕ) (hp7 : 7 ≤ p) : (2 : ZMod p) ≠ 0 := by
  change ((2 : ℕ) : ZMod p) ≠ 0
  exact zmod_natCast_ne_zero_of_pos_lt (by omega) (by omega)

lemma zmod_three_ne_zero_of_ge_seven (p : ℕ) (hp7 : 7 ≤ p) : (3 : ZMod p) ≠ 0 := by
  change ((3 : ℕ) : ZMod p) ≠ 0
  exact zmod_natCast_ne_zero_of_pos_lt (by omega) (by omega)

lemma zmod_four_ne_zero_of_ge_seven (p : ℕ) (hp7 : 7 ≤ p) : (4 : ZMod p) ≠ 0 := by
  change ((4 : ℕ) : ZMod p) ≠ 0
  exact zmod_natCast_ne_zero_of_pos_lt (by omega) (by omega)

lemma zmod_five_ne_zero_of_ge_seven (p : ℕ) (hp7 : 7 ≤ p) : (5 : ZMod p) ≠ 0 := by
  change ((5 : ℕ) : ZMod p) ≠ 0
  exact zmod_natCast_ne_zero_of_pos_lt (by omega) (by omega)

theorem exists_two_disjoint_nonzero_add_pairs_zmod (p : ℕ) [Fact p.Prime]
    (hp7 : 7 ≤ p) (e : ZMod p) :
    ∃ c1 d1 c2 d2 : ZMod p,
      c1 ≠ 0 ∧ d1 ≠ 0 ∧ c2 ≠ 0 ∧ d2 ≠ 0 ∧
      c1 + d1 = e ∧ c2 + d2 = e ∧
      c1 ≠ c2 ∧ c1 ≠ d2 ∧ d1 ≠ c2 ∧ d1 ≠ d2 := by
  by_cases he : e = 0
  · refine ⟨1, -1, 2, -2, one_ne_zero, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact neg_ne_zero.mpr one_ne_zero
    · exact zmod_two_ne_zero_of_ge_seven p hp7
    · exact neg_ne_zero.mpr (zmod_two_ne_zero_of_ge_seven p hp7)
    · rw [he]
      ring
    · rw [he]
      ring
    · intro h
      have h1 : (1 : ZMod p) = 0 := by
        linear_combination -h
      exact one_ne_zero h1
    · intro h
      have h3 : (3 : ZMod p) = 0 := by
        linear_combination h
      exact (zmod_three_ne_zero_of_ge_seven p hp7) h3
    · intro h
      have h3 : (3 : ZMod p) = 0 := by
        linear_combination -h
      exact (zmod_three_ne_zero_of_ge_seven p hp7) h3
    · intro h
      have h1 : (1 : ZMod p) = 0 := by
        linear_combination h
      exact one_ne_zero h1
  · refine ⟨(2 : ZMod p) * e, -e, (3 : ZMod p) * e, (-2 : ZMod p) * e,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact mul_ne_zero (zmod_two_ne_zero_of_ge_seven p hp7) he
    · exact neg_ne_zero.mpr he
    · exact mul_ne_zero (zmod_three_ne_zero_of_ge_seven p hp7) he
    · exact mul_ne_zero (neg_ne_zero.mpr (zmod_two_ne_zero_of_ge_seven p hp7)) he
    · ring
    · ring
    · intro h
      have hzero : e = 0 := by
        linear_combination -h
      exact he hzero
    · intro h
      have hzero : (4 : ZMod p) * e = 0 := by
        linear_combination h
      exact (mul_ne_zero (zmod_four_ne_zero_of_ge_seven p hp7) he) hzero
    · intro h
      have hzero : (4 : ZMod p) * e = 0 := by
        linear_combination -h
      exact (mul_ne_zero (zmod_four_ne_zero_of_ge_seven p hp7) he) hzero
    · intro h
      have hzero : e = 0 := by
        linear_combination h
      exact he hzero

theorem exists_two_distinct_disjoint_nonzero_add_pairs_zmod (p : ℕ) [Fact p.Prime]
    (hp7 : 7 ≤ p) (e : ZMod p) :
    ∃ c1 d1 c2 d2 : ZMod p,
      c1 ≠ 0 ∧ d1 ≠ 0 ∧ c2 ≠ 0 ∧ d2 ≠ 0 ∧
      c1 + d1 = e ∧ c2 + d2 = e ∧
      c1 ≠ d1 ∧ c2 ≠ d2 ∧
      c1 ≠ c2 ∧ c1 ≠ d2 ∧ d1 ≠ c2 ∧ d1 ≠ d2 := by
  by_cases he : e = 0
  · refine ⟨1, -1, 2, -2, one_ne_zero, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact neg_ne_zero.mpr one_ne_zero
    · exact zmod_two_ne_zero_of_ge_seven p hp7
    · exact neg_ne_zero.mpr (zmod_two_ne_zero_of_ge_seven p hp7)
    · rw [he]
      ring
    · rw [he]
      ring
    · intro h
      have h2 : (2 : ZMod p) = 0 := by
        linear_combination h
      exact (zmod_two_ne_zero_of_ge_seven p hp7) h2
    · intro h
      have h4 : (4 : ZMod p) = 0 := by
        linear_combination h
      exact (zmod_four_ne_zero_of_ge_seven p hp7) h4
    · intro h
      have h1 : (1 : ZMod p) = 0 := by
        linear_combination -h
      exact one_ne_zero h1
    · intro h
      have h3 : (3 : ZMod p) = 0 := by
        linear_combination h
      exact (zmod_three_ne_zero_of_ge_seven p hp7) h3
    · intro h
      have h3 : (3 : ZMod p) = 0 := by
        linear_combination -h
      exact (zmod_three_ne_zero_of_ge_seven p hp7) h3
    · intro h
      have h1 : (1 : ZMod p) = 0 := by
        linear_combination h
      exact one_ne_zero h1
  · refine ⟨(2 : ZMod p) * e, -e, (3 : ZMod p) * e, (-2 : ZMod p) * e,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact mul_ne_zero (zmod_two_ne_zero_of_ge_seven p hp7) he
    · exact neg_ne_zero.mpr he
    · exact mul_ne_zero (zmod_three_ne_zero_of_ge_seven p hp7) he
    · exact mul_ne_zero (neg_ne_zero.mpr (zmod_two_ne_zero_of_ge_seven p hp7)) he
    · ring
    · ring
    · intro h
      have hzero : (3 : ZMod p) * e = 0 := by
        linear_combination h
      exact (mul_ne_zero (zmod_three_ne_zero_of_ge_seven p hp7) he) hzero
    · intro h
      have hzero : (5 : ZMod p) * e = 0 := by
        linear_combination h
      exact (mul_ne_zero (zmod_five_ne_zero_of_ge_seven p hp7) he) hzero
    · intro h
      have hzero : e = 0 := by
        linear_combination -h
      exact he hzero
    · intro h
      have hzero : (4 : ZMod p) * e = 0 := by
        linear_combination h
      exact (mul_ne_zero (zmod_four_ne_zero_of_ge_seven p hp7) he) hzero
    · intro h
      have hzero : (4 : ZMod p) * e = 0 := by
        linear_combination -h
      exact (mul_ne_zero (zmod_four_ne_zero_of_ge_seven p hp7) he) hzero
    · intro h
      have hzero : e = 0 := by
        linear_combination h
      exact he hzero

theorem safePairDataZMod_nonempty (p : ℕ) [Fact p.Prime]
    (hp7 : 7 ≤ p) (e : ZMod p) :
    Nonempty (SafePairData (ZMod p) e) := by
  obtain ⟨c1, d1, c2, d2, hc1, hd1, hc2, hd2, hsum1, hsum2,
      hc1d1, hc2d2, hcc, hcd, hdc, hdd⟩ :=
    exists_two_distinct_disjoint_nonzero_add_pairs_zmod p hp7 e
  exact ⟨{
    c1 := c1
    d1 := d1
    c2 := c2
    d2 := d2
    c1_ne_zero := hc1
    d1_ne_zero := hd1
    c2_ne_zero := hc2
    d2_ne_zero := hd2
    sum1 := hsum1
    sum2 := hsum2
    c1_ne_d1 := hc1d1
    c2_ne_d2 := hc2d2
    c1_ne_c2 := hcc
    c1_ne_d2 := hcd
    d1_ne_c2 := hdc
    d1_ne_d2 := hdd
  }⟩

noncomputable def safePairDataZMod (p : ℕ) [Fact p.Prime]
    (hp7 : 7 ≤ p) (e : ZMod p) : SafePairData (ZMod p) e :=
  (safePairDataZMod_nonempty p hp7 e).some

theorem nonzeroAddPairZMod_nonempty (p : ℕ) [Fact p.Prime]
    (hp7 : 7 ≤ p) (z : ZMod p) :
    Nonempty (NonzeroAddPair (ZMod p) z) := by
  by_cases hz : z = 0
  · refine ⟨{
      left := 1
      right := -1
      left_ne_zero := one_ne_zero
      right_ne_zero := ?_
      sum_eq := ?_
    }⟩
    · exact neg_ne_zero.mpr one_ne_zero
    · rw [hz]
      ring
  · refine ⟨{
      left := (2 : ZMod p) * z
      right := -z
      left_ne_zero := ?_
      right_ne_zero := ?_
      sum_eq := ?_
    }⟩
    · exact mul_ne_zero (zmod_two_ne_zero_of_ge_seven p hp7) hz
    · exact neg_ne_zero.mpr hz
    · ring

noncomputable def nonzeroAddPairZMod (p : ℕ) [Fact p.Prime]
    (hp7 : 7 ≤ p) (z : ZMod p) : NonzeroAddPair (ZMod p) z :=
  (nonzeroAddPairZMod_nonempty p hp7 z).some

def nonzeroBox {ι : Type*} (p : ι → ℕ) : Set (∀ i : ι, ZMod (p i)) :=
  {x | ∀ i, x i ≠ 0}

def coordinateTarget {ι : Type*} (p : ι → ℕ) (e : ∀ i : ι, ZMod (p i)) :
    Set (∀ i : ι, ZMod (p i)) :=
  {z | ∃ i, z i = e i}

def leftSafeSet {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) (ν : Bool) (threshold : ℕ) :
    Set (∀ i : ι, ZMod (p i)) :=
  {x | x ∈ nonzeroBox p ∧
    threshold ≤ (Finset.univ.filter fun i => x i = (data i).c ν).card}

def rightSafeSet {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) (ν : Bool) (threshold : ℕ) :
    Set (∀ i : ι, ZMod (p i)) :=
  {y | y ∈ nonzeroBox p ∧
    threshold ≤ (Finset.univ.filter fun i => y i = (data i).d ν).card}

def safeLeftThreshold (ι : Type*) [Fintype ι] : ℕ :=
  (Fintype.card ι + 1) / 2

def safeRightThreshold (ι : Type*) [Fintype ι] : ℕ :=
  Fintype.card ι - safeLeftThreshold ι + 1

theorem safeLeftThreshold_le_card (ι : Type*) [Fintype ι] :
    safeLeftThreshold ι ≤ Fintype.card ι := by
  unfold safeLeftThreshold
  rw [Nat.div_le_iff_le_mul_add_pred (by norm_num : 0 < 2)]
  omega

theorem safeThreshold_sum_gt (ι : Type*) [Fintype ι] :
    Fintype.card ι < safeLeftThreshold ι + safeRightThreshold ι := by
  have hs := safeLeftThreshold_le_card ι
  unfold safeRightThreshold
  omega

theorem two_mul_safeLeftThreshold_le_card_add_one (ι : Type*) [Fintype ι] :
    2 * safeLeftThreshold ι ≤ Fintype.card ι + 1 := by
  unfold safeLeftThreshold
  exact Nat.mul_div_le _ _

theorem card_le_two_mul_safeLeftThreshold (ι : Type*) [Fintype ι] :
    Fintype.card ι ≤ 2 * safeLeftThreshold ι := by
  have h := Nat.lt_mul_div_succ (Fintype.card ι + 1) (by norm_num : 0 < 2)
  unfold safeLeftThreshold
  omega

theorem leftSafeSet_subset_nonzeroBox {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) (ν : Bool) (threshold : ℕ) :
    leftSafeSet p e data ν threshold ⊆ nonzeroBox p := by
  intro x hx
  exact hx.1

theorem rightSafeSet_subset_nonzeroBox {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) (ν : Bool) (threshold : ℕ) :
    rightSafeSet p e data ν threshold ⊆ nonzeroBox p := by
  intro x hx
  exact hx.1

theorem safePair_sum_subset_coordinateTarget {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) (ν : Bool)
    (leftThreshold rightThreshold : ℕ)
    (hthreshold : Fintype.card ι < leftThreshold + rightThreshold) :
    (leftSafeSet p e data ν leftThreshold + rightSafeSet p e data ν rightThreshold) ⊆
      coordinateTarget p e := by
  classical
  rintro z ⟨x, hx, y, hy, hxy⟩
  by_contra hz
  have hz_forall : ∀ i, x i + y i ≠ e i := by
    intro i hsum
    apply hz
    refine ⟨i, ?_⟩
    have hcoord : x i + y i = z i := by
      simpa using congrFun hxy i
    exact hcoord.symm.trans hsum
  let Lmatch : Finset ι := Finset.univ.filter fun i => x i = (data i).c ν
  let Rmatch : Finset ι := Finset.univ.filter fun i => y i = (data i).d ν
  have hLcard : leftThreshold ≤ Lmatch.card := by
    simpa [leftSafeSet, Lmatch] using hx.2
  have hRcard : rightThreshold ≤ Rmatch.card := by
    simpa [rightSafeSet, Rmatch] using hy.2
  have hdisj : Disjoint Lmatch Rmatch := by
    rw [Finset.disjoint_left]
    intro i hiL hiR
    have hxi : x i = (data i).c ν := by simpa [Lmatch] using hiL
    have hyi : y i = (data i).d ν := by simpa [Rmatch] using hiR
    exact hz_forall i (by rw [hxi, hyi, (data i).c_add_d ν])
  have hcard_union : (Lmatch ∪ Rmatch).card = Lmatch.card + Rmatch.card := by
    exact Finset.card_union_of_disjoint hdisj
  have hcard_le : Lmatch.card + Rmatch.card ≤ Fintype.card ι := by
    rw [← hcard_union]
    simpa using Finset.card_le_univ (Lmatch ∪ Rmatch)
  omega

theorem safePair_sum_subset_coordinateTarget_thresholds {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) (ν : Bool) :
    (leftSafeSet p e data ν (safeLeftThreshold ι) +
        rightSafeSet p e data ν (safeRightThreshold ι)) ⊆
      coordinateTarget p e :=
  safePair_sum_subset_coordinateTarget p e data ν
    (safeLeftThreshold ι) (safeRightThreshold ι) (safeThreshold_sum_gt ι)

theorem safePair_mem_sum_of_disjoint_auxiliary_sets {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (hp7 : ∀ i, 7 ≤ p i) (e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) (ν : Bool)
    (leftThreshold rightThreshold : ℕ) (z : ∀ i : ι, ZMod (p i))
    (S T : Finset ι)
    (hS_not_target : ∀ i ∈ S, z i ≠ e i)
    (hS_ne_c : ∀ i ∈ S, z i ≠ (data i).c ν)
    (hT_not_target : ∀ i ∈ T, z i ≠ e i)
    (hT_ne_d : ∀ i ∈ T, z i ≠ (data i).d ν)
    (hST : Disjoint S T)
    (hleft : leftThreshold ≤ (Finset.univ.filter fun i => z i = e i).card + S.card)
    (hright : rightThreshold ≤ (Finset.univ.filter fun i => z i = e i).card + T.card) :
    z ∈ leftSafeSet p e data ν leftThreshold + rightSafeSet p e data ν rightThreshold := by
  classical
  let x : ∀ i : ι, ZMod (p i) := fun i =>
    if z i = e i then (data i).c ν
    else if i ∈ S then (data i).c ν
    else if i ∈ T then z i - (data i).d ν
    else (nonzeroAddPairZMod (p i) (hp7 i) (z i)).left
  let y : ∀ i : ι, ZMod (p i) := fun i =>
    if z i = e i then (data i).d ν
    else if i ∈ S then z i - (data i).c ν
    else if i ∈ T then (data i).d ν
    else (nonzeroAddPairZMod (p i) (hp7 i) (z i)).right
  refine ⟨x, ?_, y, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro i
      dsimp [x]
      by_cases hZ : z i = e i
      · simp [hZ, (data i).c_ne_zero ν]
      · simp [hZ]
        by_cases hS : i ∈ S
        · simp [hS, (data i).c_ne_zero ν]
        · simp [hS]
          by_cases hT : i ∈ T
          · simp [hT]
            intro hzsub
            exact hT_ne_d i hT (sub_eq_zero.mp hzsub)
          · simp [hT, (nonzeroAddPairZMod (p i) (hp7 i) (z i)).left_ne_zero]
    · let Z : Finset ι := Finset.univ.filter fun i => z i = e i
      let Lmatch : Finset ι := Finset.univ.filter fun i => x i = (data i).c ν
      have hsub : Z ∪ S ⊆ Lmatch := by
        intro i hi
        rw [Finset.mem_union] at hi
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ i, ?_⟩
        rcases hi with hiZ | hiS
        · have hzi : z i = e i := by simpa [Z] using hiZ
          simp [x, hzi]
        · have hzi : z i ≠ e i := hS_not_target i hiS
          simp [x, hzi, hiS]
      have hdisj : Disjoint Z S := by
        rw [Finset.disjoint_left]
        intro i hiZ hiS
        have hzi : z i = e i := by simpa [Z] using hiZ
        exact hS_not_target i hiS hzi
      have hcard_union : (Z ∪ S).card = Z.card + S.card :=
        Finset.card_union_of_disjoint hdisj
      have hle : Z.card + S.card ≤ Lmatch.card := by
        rw [← hcard_union]
        exact Finset.card_le_card hsub
      exact hleft.trans (by simpa [Z, Lmatch] using hle)
  · refine ⟨?_, ?_⟩
    · intro i
      dsimp [y]
      by_cases hZ : z i = e i
      · simp [hZ, (data i).d_ne_zero ν]
      · simp [hZ]
        by_cases hS : i ∈ S
        · simp [hS]
          intro hzsub
          exact hS_ne_c i hS (sub_eq_zero.mp hzsub)
        · simp [hS]
          by_cases hT : i ∈ T
          · simp [hT, (data i).d_ne_zero ν]
          · simp [hT, (nonzeroAddPairZMod (p i) (hp7 i) (z i)).right_ne_zero]
    · let Z : Finset ι := Finset.univ.filter fun i => z i = e i
      let Rmatch : Finset ι := Finset.univ.filter fun i => y i = (data i).d ν
      have hsub : Z ∪ T ⊆ Rmatch := by
        intro i hi
        rw [Finset.mem_union] at hi
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ i, ?_⟩
        rcases hi with hiZ | hiT
        · have hzi : z i = e i := by simpa [Z] using hiZ
          simp [y, hzi]
        · have hzi : z i ≠ e i := hT_not_target i hiT
          by_cases hiS : i ∈ S
          · exact False.elim ((Finset.disjoint_left.mp hST hiS hiT))
          · simp [y, hzi, hiS, hiT]
      have hdisj : Disjoint Z T := by
        rw [Finset.disjoint_left]
        intro i hiZ hiT
        have hzi : z i = e i := by simpa [Z] using hiZ
        exact hT_not_target i hiT hzi
      have hcard_union : (Z ∪ T).card = Z.card + T.card :=
        Finset.card_union_of_disjoint hdisj
      have hle : Z.card + T.card ≤ Rmatch.card := by
        rw [← hcard_union]
        exact Finset.card_le_card hsub
      exact hright.trans (by simpa [Z, Rmatch] using hle)
  · funext i
    dsimp [x, y]
    by_cases hZ : z i = e i
    · simp [hZ]
      exact (data i).c_add_d ν
    · simp [hZ]
      by_cases hS : i ∈ S
      · simp [hS]
      · simp [hS]
        by_cases hT : i ∈ T
        · simp [hT]
        · simp [hT, (nonzeroAddPairZMod (p i) (hp7 i) (z i)).sum_eq]

theorem safePair_mem_sum_of_side_card_conditions {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (hp7 : ∀ i, 7 ≤ p i) (e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) (ν : Bool)
    (leftThreshold rightThreshold : ℕ) (z : ∀ i : ι, ZMod (p i))
    (Z U C0 D0 : Finset ι)
    (hZ : Z = Finset.univ.filter fun i => z i = e i)
    (hU : U = Finset.univ.filter fun i => z i ≠ e i)
    (hC0 : C0 = U.filter fun i => z i = (data i).c ν)
    (hD0 : D0 = U.filter fun i => z i = (data i).d ν)
    (ha : leftThreshold - Z.card ≤ (U \ C0).card)
    (hb : rightThreshold - Z.card ≤ (U \ D0).card)
    (hab : (leftThreshold - Z.card) + (rightThreshold - Z.card) ≤ U.card) :
    z ∈ leftSafeSet p e data ν leftThreshold + rightSafeSet p e data ν rightThreshold := by
  classical
  have hCsub : C0 ⊆ U := by
    intro i hi
    rw [hC0] at hi
    exact (Finset.mem_filter.mp hi).1
  have hDsub : D0 ⊆ U := by
    intro i hi
    rw [hD0] at hi
    exact (Finset.mem_filter.mp hi).1
  have hCDdisj : Disjoint C0 D0 := by
    rw [Finset.disjoint_left]
    intro i hiC hiD
    have hzc : z i = (data i).c ν := by
      rw [hC0] at hiC
      exact (Finset.mem_filter.mp hiC).2
    have hzd : z i = (data i).d ν := by
      rw [hD0] at hiD
      exact (Finset.mem_filter.mp hiD).2
    exact (data i).c_ne_d ν (hzc.symm.trans hzd)
  obtain ⟨S, T, hSsub, hTsub, hST, hScard, hTcard⟩ :=
    choose_disjoint_avoiding_two_forbidden_sets U C0 D0 hCsub hDsub hCDdisj
      (leftThreshold - Z.card) (rightThreshold - Z.card) ha hb hab
  refine safePair_mem_sum_of_disjoint_auxiliary_sets p hp7 e data ν leftThreshold rightThreshold z
    S T ?_ ?_ ?_ ?_ hST ?_ ?_
  · intro i hiS
    have hiU : i ∈ U := (Finset.mem_sdiff.mp (hSsub hiS)).1
    rw [hU] at hiU
    exact (Finset.mem_filter.mp hiU).2
  · intro i hiS
    have hiNotC : i ∉ C0 := (Finset.mem_sdiff.mp (hSsub hiS)).2
    intro hzc
    exact hiNotC (by
      rw [hC0]
      exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp (hSsub hiS)).1, hzc⟩)
  · intro i hiT
    have hiU : i ∈ U := (Finset.mem_sdiff.mp (hTsub hiT)).1
    rw [hU] at hiU
    exact (Finset.mem_filter.mp hiU).2
  · intro i hiT
    have hiNotD : i ∉ D0 := (Finset.mem_sdiff.mp (hTsub hiT)).2
    intro hzd
    exact hiNotD (by
      rw [hD0]
      exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp (hTsub hiT)).1, hzd⟩)
  · rw [← hZ, hScard]
    omega
  · rw [← hZ, hTcard]
    omega

theorem exists_bool_card_twice_le_of_disjoint_subsets {ι : Type*} [DecidableEq ι]
    (U badTrue badFalse : Finset ι)
    (hTrue : badTrue ⊆ U) (hFalse : badFalse ⊆ U)
    (hdisj : Disjoint badTrue badFalse) :
    ∃ ν : Bool, 2 * (if ν then badTrue.card else badFalse.card) ≤ U.card := by
  classical
  have hsum : badTrue.card + badFalse.card ≤ U.card := by
    have hcard_union : (badTrue ∪ badFalse).card = badTrue.card + badFalse.card :=
      Finset.card_union_of_disjoint hdisj
    rw [← hcard_union]
    exact Finset.card_le_card (Finset.union_subset hTrue hFalse)
  by_cases h : 2 * badTrue.card ≤ U.card
  · exact ⟨true, by simp [h]⟩
  · have hFalseHalf : 2 * badFalse.card ≤ U.card := by omega
    exact ⟨false, by simp [hFalseHalf]⟩

def sideBadSet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) (ν : Bool)
    (z : ∀ i : ι, ZMod (p i)) (U : Finset ι) : Finset ι :=
  (U.filter fun i => z i = (data i).c ν) ∪
    (U.filter fun i => z i = (data i).d ν)

theorem sideBadSet_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) (ν : Bool)
    (z : ∀ i : ι, ZMod (p i)) (U : Finset ι) :
    sideBadSet p e data ν z U ⊆ U := by
  intro i hi
  rw [sideBadSet, Finset.mem_union] at hi
  rcases hi with hi | hi <;> exact (Finset.mem_filter.mp hi).1

theorem sideBadSet_true_disjoint_false {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (z : ∀ i : ι, ZMod (p i)) (U : Finset ι) :
    Disjoint (sideBadSet p e data true z U) (sideBadSet p e data false z U) := by
  rw [Finset.disjoint_left]
  intro i hiT hiF
  rw [sideBadSet, Finset.mem_union] at hiT hiF
  rcases hiT with hiTc | hiTd
  · have hzTc : z i = (data i).c true := (Finset.mem_filter.mp hiTc).2
    rcases hiF with hiFc | hiFd
    · have hzFc : z i = (data i).c false := (Finset.mem_filter.mp hiFc).2
      exact (data i).c1_ne_c2 (by simpa using hzTc.symm.trans hzFc)
    · have hzFd : z i = (data i).d false := (Finset.mem_filter.mp hiFd).2
      exact (data i).c1_ne_d2 (by simpa using hzTc.symm.trans hzFd)
  · have hzTd : z i = (data i).d true := (Finset.mem_filter.mp hiTd).2
    rcases hiF with hiFc | hiFd
    · have hzFc : z i = (data i).c false := (Finset.mem_filter.mp hiFc).2
      exact (data i).d1_ne_c2 (by simpa using hzTd.symm.trans hzFc)
    · have hzFd : z i = (data i).d false := (Finset.mem_filter.mp hiFd).2
      exact (data i).d1_ne_d2 (by simpa using hzTd.symm.trans hzFd)

theorem exists_side_badSet_card_twice_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (z : ∀ i : ι, ZMod (p i)) (U : Finset ι) :
    ∃ ν : Bool, 2 * (sideBadSet p e data ν z U).card ≤ U.card := by
  simpa using exists_bool_card_twice_le_of_disjoint_subsets U
    (sideBadSet p e data true z U) (sideBadSet p e data false z U)
    (sideBadSet_subset p e data true z U) (sideBadSet_subset p e data false z U)
    (sideBadSet_true_disjoint_false p e data z U)

theorem safePair_side_card_conditions_of_bad_half {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Z U C0 D0 : Finset ι)
    (hZUcard : Z.card + U.card = Fintype.card ι)
    (hZpos : 0 < Z.card)
    (hCsub : C0 ⊆ U) (hDsub : D0 ⊆ U)
    (hbadhalf : 2 * (C0 ∪ D0).card ≤ U.card) :
    safeLeftThreshold ι - Z.card ≤ (U \ C0).card ∧
      safeRightThreshold ι - Z.card ≤ (U \ D0).card ∧
      (safeLeftThreshold ι - Z.card) + (safeRightThreshold ι - Z.card) ≤ U.card := by
  classical
  have h2s_le : 2 * safeLeftThreshold ι ≤ Fintype.card ι + 1 :=
    two_mul_safeLeftThreshold_le_card_add_one ι
  have hk_le_2s : Fintype.card ι ≤ 2 * safeLeftThreshold ι :=
    card_le_two_mul_safeLeftThreshold ι
  have hC_le_bad : C0.card ≤ (C0 ∪ D0).card := by
    exact Finset.card_le_card (by intro x hx; simp [hx])
  have hD_le_bad : D0.card ≤ (C0 ∪ D0).card := by
    exact Finset.card_le_card (by intro x hx; simp [hx])
  have h2C : 2 * C0.card ≤ U.card := by omega
  have h2D : 2 * D0.card ≤ U.card := by omega
  have hCcard : C0.card ≤ U.card := Finset.card_le_card hCsub
  have hDcard : D0.card ≤ U.card := Finset.card_le_card hDsub
  rw [Finset.card_sdiff_of_subset hCsub, Finset.card_sdiff_of_subset hDsub]
  constructor
  · omega
  constructor
  · unfold safeRightThreshold
    omega
  · unfold safeRightThreshold
    omega

theorem coordinateTarget_subset_safePair_sum_union {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (hp7 : ∀ i, 7 ≤ p i) (e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) :
    coordinateTarget p e ⊆
      ((leftSafeSet p e data true (safeLeftThreshold ι) +
          rightSafeSet p e data true (safeRightThreshold ι)) ∪
        (leftSafeSet p e data false (safeLeftThreshold ι) +
          rightSafeSet p e data false (safeRightThreshold ι))) := by
  classical
  intro z hz
  let Z : Finset ι := Finset.univ.filter fun i => z i = e i
  let U : Finset ι := Finset.univ.filter fun i => z i ≠ e i
  have hZpos : 0 < Z.card := by
    rcases hz with ⟨i, hi⟩
    exact Finset.card_pos.mpr ⟨i, by simp [Z, hi]⟩
  have hZUcard : Z.card + U.card = Fintype.card ι := by
    have hdisj : Disjoint Z U := by
      rw [Finset.disjoint_left]
      intro i hiZ hiU
      have hzi : z i = e i := by simpa [Z] using hiZ
      have hzne : z i ≠ e i := by simpa [U] using hiU
      exact hzne hzi
    have hunion : Z ∪ U = (Finset.univ : Finset ι) := by
      ext i
      by_cases h : z i = e i <;> simp [Z, U, h]
    have hcard : (Z ∪ U).card = Z.card + U.card :=
      Finset.card_union_of_disjoint hdisj
    rw [hunion] at hcard
    exact hcard.symm
  obtain ⟨ν, hνbad⟩ := exists_side_badSet_card_twice_le p e data z U
  let C0 : Finset ι := U.filter fun i => z i = (data i).c ν
  let D0 : Finset ι := U.filter fun i => z i = (data i).d ν
  have hCsub : C0 ⊆ U := by
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  have hDsub : D0 ⊆ U := by
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  have hbadhalf : 2 * (C0 ∪ D0).card ≤ U.card := by
    simpa [sideBadSet, C0, D0] using hνbad
  obtain ⟨ha, hb, hab⟩ :=
    safePair_side_card_conditions_of_bad_half Z U C0 D0 hZUcard hZpos hCsub hDsub
      hbadhalf
  have hmem : z ∈ leftSafeSet p e data ν (safeLeftThreshold ι) +
      rightSafeSet p e data ν (safeRightThreshold ι) := by
    exact safePair_mem_sum_of_side_card_conditions p hp7 e data ν
      (safeLeftThreshold ι) (safeRightThreshold ι) z Z U C0 D0
      (by rfl) (by rfl) (by rfl) (by rfl) ha hb hab
  cases ν
  · exact Or.inr hmem
  · exact Or.inl hmem

theorem safePair_sum_union_eq_coordinateTarget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (hp7 : ∀ i, 7 ≤ p i) (e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) :
    ((leftSafeSet p e data true (safeLeftThreshold ι) +
        rightSafeSet p e data true (safeRightThreshold ι)) ∪
      (leftSafeSet p e data false (safeLeftThreshold ι) +
        rightSafeSet p e data false (safeRightThreshold ι))) =
      coordinateTarget p e := by
  apply Set.Subset.antisymm
  · intro z hz
    rcases hz with hz | hz
    · exact safePair_sum_subset_coordinateTarget_thresholds p e data true hz
    · exact safePair_sum_subset_coordinateTarget_thresholds p e data false hz
  · exact coordinateTarget_subset_safePair_sum_union p hp7 e data

end Erdos330
