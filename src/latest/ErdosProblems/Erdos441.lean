/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 441.
https://www.erdosproblems.com/forum/thread/441

Informal authors:
- Yong-Gao Chen
- Li-Xia Dai

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos441.md
-/
import Mathlib

/-!
# Erdős Problem 441

For `N : ℕ`, let `g N` be the largest cardinality of a finite subset of
`{1, ..., N}` whose pairwise least common multiples do not exceed `N`.

Erdős proposed the union of the integers at most `sqrt (N / 2)` and the even
integers at most `sqrt (2 * N)`.  We use the equivalent square-only definition
`erdosConstruction` below.  The construction is always admissible, but it is not
eventually extremal: at every `N = 2 * (6*t + 4)^2`, the new element
`2 * (6*t + 6)` may be adjoined.

The latter is an elementary infinite-family strengthening of a single
counterexample and gives the exact negative answer to Erdős's proposed extremal
description.  Chen's separate sharp asymptotic theorem is discussed, together
with its sieve-theoretic dependency chain, in `tex/441.tex`.
-/

namespace Erdos441

open scoped BigOperators

/-- A finite set of positive integers at most `N`, every two of whose least
common multiples are at most `N`. -/
def LcmBounded (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    ∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N

instance (N : ℕ) (A : Finset ℕ) : Decidable (LcmBounded N A) := by
  unfold LcmBounded
  infer_instance

/-- The finite collection of all admissible subsets of `{1, ..., N}`. -/
def candidates (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter (LcmBounded N)

/-- The exact extremal function in Erdős Problem 441. -/
def g (N : ℕ) : ℕ :=
  (candidates N).sup Finset.card

@[simp] lemma mem_candidates {N : ℕ} {A : Finset ℕ} :
    A ∈ candidates N ↔ LcmBounded N A := by
  constructor
  · intro hA
    exact (Finset.mem_filter.mp hA).2
  · intro hA
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA.1, hA⟩

@[simp] lemma empty_lcmBounded (N : ℕ) : LcmBounded N ∅ := by
  simp [LcmBounded]

lemma card_le_g {N : ℕ} {A : Finset ℕ} (hA : LcmBounded N A) :
    A.card ≤ g N := by
  exact Finset.le_sup (f := Finset.card) (mem_candidates.mpr hA)

/-- The supremum defining `g` is attained by an admissible finite set. -/
theorem exists_extremal (N : ℕ) :
    ∃ A : Finset ℕ, LcmBounded N A ∧ A.card = g N := by
  have hne : (candidates N).Nonempty :=
    ⟨∅, mem_candidates.mpr (empty_lcmBounded N)⟩
  obtain ⟨A, hA, hcard⟩ :=
    Finset.exists_mem_eq_sup (candidates N) hne Finset.card
  exact ⟨A, mem_candidates.mp hA, hcard.symm⟩

/-- `g N` really is the least universal cardinality upper bound for admissible
sets. -/
theorem g_le_iff {N m : ℕ} :
    g N ≤ m ↔ ∀ A : Finset ℕ, LcmBounded N A → A.card ≤ m := by
  constructor
  · intro h A hA
    exact (card_le_g hA).trans h
  · intro h
    obtain ⟨A, hA, hcard⟩ := exists_extremal N
    simpa [← hcard] using h A hA

/-- Erdős's proposed construction, written without real square roots. -/
def erdosConstruction (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun a ↦
    2 * a ^ 2 ≤ N ∨ (2 ∣ a ∧ a ^ 2 ≤ 2 * N)

@[simp] lemma mem_erdosConstruction {N a : ℕ} :
    a ∈ erdosConstruction N ↔
      1 ≤ a ∧ a ≤ N ∧
        (2 * a ^ 2 ≤ N ∨ (2 ∣ a ∧ a ^ 2 ≤ 2 * N)) := by
  simp [erdosConstruction, and_assoc]

lemma lcm_le_mul {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Nat.lcm a b ≤ a * b := by
  exact Nat.le_of_dvd (Nat.mul_pos ha hb) (Nat.lcm_dvd_mul a b)

private lemma mul_le_of_two_mul_sq_le_sq_le {N x y : ℕ}
    (hx : 2 * x ^ 2 ≤ N) (hy : y ^ 2 ≤ 2 * N) :
    x * y ≤ N := by
  nlinarith [sq_nonneg (2 * (x : ℤ) - y)]

private lemma two_mul_le_of_two_mul_sq_le {N u v : ℕ}
    (hu : 2 * u ^ 2 ≤ N) (hv : 2 * v ^ 2 ≤ N) :
    2 * (u * v) ≤ N := by
  nlinarith [sq_nonneg ((u : ℤ) - v)]

/-- Erdős's proposed set is admissible for every `N`. -/
theorem erdosConstruction_lcmBounded (N : ℕ) :
    LcmBounded N (erdosConstruction N) := by
  constructor
  · intro a ha
    exact Finset.mem_Icc.mpr ⟨(mem_erdosConstruction.mp ha).1,
      (mem_erdosConstruction.mp ha).2.1⟩
  · intro a ha b hb
    have ha' := mem_erdosConstruction.mp ha
    have hb' := mem_erdosConstruction.mp hb
    rcases ha'.2.2 with haLow | ⟨haEven, haHigh⟩
    · rcases hb'.2.2 with hbLow | ⟨_hbEven, hbHigh⟩
      · have hbHigh : b ^ 2 ≤ 2 * N := by omega
        exact (lcm_le_mul ha'.1 hb'.1).trans
          (mul_le_of_two_mul_sq_le_sq_le haLow hbHigh)
      · exact (lcm_le_mul ha'.1 hb'.1).trans
          (mul_le_of_two_mul_sq_le_sq_le haLow hbHigh)
    · rcases hb'.2.2 with hbLow | ⟨hbEven, hbHigh⟩
      · rw [Nat.lcm_comm]
        exact (lcm_le_mul hb'.1 ha'.1).trans
          (mul_le_of_two_mul_sq_le_sq_le hbLow haHigh)
      · rcases haEven with ⟨u, rfl⟩
        rcases hbEven with ⟨v, rfl⟩
        have hu : 2 * u ^ 2 ≤ N := by nlinarith
        have hv : 2 * v ^ 2 ≤ N := by nlinarith
        have huPos : 1 ≤ u := by omega
        have hvPos : 1 ≤ v := by omega
        have hdvd : Nat.lcm (2 * u) (2 * v) ∣ 2 * (u * v) := by
          apply Nat.lcm_dvd
          · exact ⟨v, by ring⟩
          · exact ⟨u, by ring⟩
        calc
          Nat.lcm (2 * u) (2 * v) ≤ 2 * (u * v) :=
            Nat.le_of_dvd (by positivity) hdvd
          _ ≤ N := two_mul_le_of_two_mul_sq_le hu hv

/-! ## An infinite family on which Erdős's construction is not maximal -/

/-- The square-root parameter in the elementary counterexample family. -/
def familyK (t : ℕ) : ℕ := 6 * t + 4

/-- The ambient bound `N = 2 k²` in the elementary counterexample family. -/
def familyN (t : ℕ) : ℕ := 2 * familyK t ^ 2

/-- The element which can be adjoined to Erdős's construction. -/
def extra (t : ℕ) : ℕ := 2 * (familyK t + 2)

/-- A disjoint enumeration of the odd part below `k` and the even part below
`2k` at `N = 2k²`. -/
def familyListing (t : ℕ) : Finset ℕ :=
  (Finset.range (3 * t + 2)).image (fun i ↦ 2 * i + 1) ∪
    (Finset.range (familyK t)).image (fun i ↦ 2 * (i + 1))

@[simp] lemma familyK_pos (t : ℕ) : 1 ≤ familyK t := by
  simp [familyK]

lemma familyK_even (t : ℕ) : 2 ∣ familyK t := by
  refine ⟨3 * t + 2, ?_⟩
  simp [familyK]
  ring

lemma three_dvd_familyK_sub_one (t : ℕ) : 3 ∣ familyK t - 1 := by
  refine ⟨2 * t + 1, ?_⟩
  simp [familyK]
  ring

lemma three_dvd_familyK_add_two (t : ℕ) : 3 ∣ familyK t + 2 := by
  refine ⟨2 * t + 2, ?_⟩
  simp [familyK]
  ring

private lemma lcm_le_commonMultiple {a b m : ℕ} (hm : 0 < m)
    (ha : a ∣ m) (hb : b ∣ m) :
    Nat.lcm a b ≤ m := by
  exact Nat.le_of_dvd hm (Nat.lcm_dvd ha hb)

private lemma low_member_le_familyK {t b : ℕ}
    (hb : 2 * b ^ 2 ≤ familyN t) : b ≤ familyK t := by
  simp only [familyN] at hb
  nlinarith [sq_nonneg ((b : ℤ) - familyK t)]

private lemma high_half_le_familyK {t h : ℕ}
    (hh : (2 * h) ^ 2 ≤ 2 * familyN t) : h ≤ familyK t := by
  simp only [familyN] at hh
  nlinarith [sq_nonneg ((h : ℤ) - familyK t)]

/-- At the counterexample parameters, Erdős's construction is precisely the
odd integers at most `k` together with the even integers at most `2k`. -/
lemma familyListing_eq_erdosConstruction (t : ℕ) :
    familyListing t = erdosConstruction (familyN t) := by
  ext a
  simp only [familyListing, Finset.mem_union, Finset.mem_image,
    Finset.mem_range, mem_erdosConstruction]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · constructor
      · omega
      constructor
      · simp [familyN, familyK]
        nlinarith
      · left
        simp [familyN, familyK]
        nlinarith
    · constructor
      · omega
      constructor
      · have hi1 : i + 1 ≤ familyK t := by omega
        calc
          2 * (i + 1) ≤ 2 * familyK t := Nat.mul_le_mul_left 2 hi1
          _ ≤ familyN t := by
            simp [familyN, familyK]
            nlinarith
      · right
        constructor
        · exact ⟨i + 1, by ring⟩
        · have hi1 : i + 1 ≤ familyK t := by omega
          have hsquare := Nat.pow_le_pow_left hi1 2
          simp only [familyN]
          nlinarith
  · rintro ⟨hapos, _haN, haLow | ⟨haEven, haHigh⟩⟩
    · have hak : a ≤ familyK t := low_member_le_familyK haLow
      obtain ⟨i, hi | hi⟩ := Nat.even_or_odd' a
      · right
        have hipos : 1 ≤ i := by omega
        refine ⟨i - 1, ?_, ?_⟩
        · omega
        · omega
      · left
        refine ⟨i, ?_, hi.symm⟩
        simp [familyK] at hak
        omega
    · rcases haEven with ⟨h, rfl⟩
      have hh : h ≤ familyK t := high_half_le_familyK haHigh
      have hhpos : 1 ≤ h := by omega
      right
      refine ⟨h - 1, ?_, ?_⟩
      · omega
      · omega

lemma familyListing_disjoint (t : ℕ) :
    Disjoint
      ((Finset.range (3 * t + 2)).image (fun i ↦ 2 * i + 1))
      ((Finset.range (familyK t)).image (fun i ↦ 2 * (i + 1))) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_image, Finset.mem_range] at ha hb
  obtain ⟨i, _hi, rfl⟩ := ha
  obtain ⟨j, _hj, hij⟩ := hb
  omega

/-- The proposed construction has its expected exact size on the family
`N = 2 * (6t+4)²`. -/
lemma card_erdosConstruction_familyN (t : ℕ) :
    (erdosConstruction (familyN t)).card = 9 * t + 6 := by
  rw [← familyListing_eq_erdosConstruction, familyListing,
    Finset.card_union_of_disjoint (familyListing_disjoint t),
    Finset.card_image_of_injective _ (by intro i j h; dsimp at h; omega),
    Finset.card_image_of_injective _ (by intro i j h; dsimp at h; omega)]
  simp [familyK]
  omega

private lemma extra_lcm_low_le (t b : ℕ) (hbpos : 1 ≤ b)
    (hb : b ≤ familyK t) :
    Nat.lcm (extra t) b ≤ familyN t := by
  by_cases hinterior : b ≤ familyK t - 2
  · have hb2 : b + 2 ≤ familyK t := by
      have hk : 2 ≤ familyK t := by simp [familyK]
      omega
    exact (lcm_le_mul (by simp [extra, familyK]; omega) hbpos).trans (by
      simp only [extra, familyN, familyK] at *
      nlinarith)
  · have hcases : b = familyK t - 1 ∨ b = familyK t := by omega
    rcases hcases with hprev | htop
    · subst b
      let m := 12 * (t + 1) * (2 * t + 1)
      have hm : 0 < m := by positivity
      have he : extra t ∣ m := by
        refine ⟨2 * t + 1, ?_⟩
        simp [extra, familyK, m]
        ring
      have hb : familyK t - 1 ∣ m := by
        refine ⟨4 * (t + 1), ?_⟩
        simp [familyK, m]
        ring
      exact (lcm_le_commonMultiple hm he hb).trans (by
        simp [familyN, familyK, m]
        nlinarith)
    · subst b
      let m := familyK t * (familyK t + 2)
      have hm : 0 < m := by positivity
      have he : extra t ∣ m := by
        refine ⟨3 * t + 2, ?_⟩
        simp [extra, familyK, m]
        ring
      have hb : familyK t ∣ m := dvd_mul_right _ _
      exact (lcm_le_commonMultiple hm he hb).trans (by
        simp [familyN, familyK, m]
        nlinarith)

private lemma extra_lcm_even_le (t h : ℕ) (hhpos : 1 ≤ h)
    (hh : h ≤ familyK t) :
    Nat.lcm (extra t) (2 * h) ≤ familyN t := by
  by_cases hinterior : h ≤ familyK t - 2
  · have hdvd : Nat.lcm (extra t) (2 * h) ∣
        2 * (familyK t + 2) * h := by
      apply Nat.lcm_dvd
      · exact dvd_mul_right _ _
      · refine ⟨familyK t + 2, ?_⟩
        ring
    have hh2 : h + 2 ≤ familyK t := by
      have hk : 2 ≤ familyK t := by simp [familyK]
      omega
    exact (Nat.le_of_dvd (by positivity) hdvd).trans (by
      simp only [familyN, familyK] at *
      nlinarith)
  · have hcases : h = familyK t - 1 ∨ h = familyK t := by omega
    rcases hcases with hprev | htop
    · subst h
      let m := 12 * (t + 1) * (2 * t + 1)
      have hm : 0 < m := by positivity
      have he : extra t ∣ m := by
        refine ⟨2 * t + 1, ?_⟩
        simp [extra, familyK, m]
        ring
      have hb : 2 * (familyK t - 1) ∣ m := by
        refine ⟨2 * (t + 1), ?_⟩
        simp [familyK, m]
        ring
      exact (lcm_le_commonMultiple hm he hb).trans (by
        simp [familyN, familyK, m]
        nlinarith)
    · subst h
      let m := familyK t * (familyK t + 2)
      have hm : 0 < m := by positivity
      have he : extra t ∣ m := by
        refine ⟨3 * t + 2, ?_⟩
        simp [extra, familyK, m]
        ring
      have hb : 2 * familyK t ∣ m := by
        refine ⟨3 * t + 3, ?_⟩
        simp [familyK, m]
        ring
      exact (lcm_le_commonMultiple hm he hb).trans (by
        simp [familyN, familyK, m]
        nlinarith)

/-- Every member of Erdős's construction at `familyN t` has small LCM with
the extra element. -/
lemma extra_lcm_construction_le (t : ℕ) {b : ℕ}
    (hb : b ∈ erdosConstruction (familyN t)) :
    Nat.lcm (extra t) b ≤ familyN t := by
  have hb' := mem_erdosConstruction.mp hb
  rcases hb'.2.2 with hbLow | ⟨hbEven, hbHigh⟩
  · exact extra_lcm_low_le t b hb'.1 (low_member_le_familyK hbLow)
  · rcases hbEven with ⟨h, rfl⟩
    have hhpos : 1 ≤ h := by omega
    exact extra_lcm_even_le t h hhpos (high_half_le_familyK hbHigh)

lemma extra_le_familyN (t : ℕ) : extra t ≤ familyN t := by
  simp [extra, familyN, familyK]
  nlinarith

/-- The added element lies strictly beyond the upper endpoint `2k` of the
even part of Erdős's construction. -/
lemma extra_not_mem_erdosConstruction (t : ℕ) :
    extra t ∉ erdosConstruction (familyN t) := by
  intro he
  have he' := mem_erdosConstruction.mp he
  rcases he'.2.2 with heLow | ⟨_, heHigh⟩
  · simp [extra, familyN, familyK] at heLow
    norm_num [pow_two] at heLow
    nlinarith
  · simp [extra, familyN, familyK] at heHigh
    norm_num [pow_two] at heHigh
    nlinarith

/-- The enlarged construction is admissible for every member of the infinite
counterexample family. -/
theorem augmentedConstruction_lcmBounded (t : ℕ) :
    LcmBounded (familyN t)
      (insert (extra t) (erdosConstruction (familyN t))) := by
  have hB := erdosConstruction_lcmBounded (familyN t)
  constructor
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_Icc.mpr ⟨by simp [extra, familyK]; omega, extra_le_familyN t⟩
    · exact hB.1 ha
  · intro a ha b hb
    rcases Finset.mem_insert.mp ha with rfl | ha
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · simpa using extra_le_familyN t
      · exact extra_lcm_construction_le t hb
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · simpa [Nat.lcm_comm] using extra_lcm_construction_le t ha
      · exact hB.2 a ha b hb

/-- At every parameter in the family, the exact extremal size is strictly
larger than the size of Erdős's proposed construction. -/
theorem erdosConstruction_card_lt_g (t : ℕ) :
    (erdosConstruction (familyN t)).card < g (familyN t) := by
  have hle := card_le_g (augmentedConstruction_lcmBounded t)
  rw [Finset.card_insert_of_notMem (extra_not_mem_erdosConstruction t)] at hle
  omega

/-- The strict improvement has the explicit cardinality from the mathematical
writeup: `|B| = 9t+6`, so `g ≥ 9t+7`. -/
theorem nine_mul_add_seven_le_g_familyN (t : ℕ) :
    9 * t + 7 ≤ g (familyN t) := by
  have hle := card_le_g (augmentedConstruction_lcmBounded t)
  rw [Finset.card_insert_of_notMem (extra_not_mem_erdosConstruction t),
    card_erdosConstruction_familyN] at hle
  omega

/-- There are arbitrarily large `N` for which Erdős's proposed construction is
not extremal. -/
theorem erdosConstruction_not_eventually_extremal :
    ∀ M : ℕ, ∃ N ≥ M,
      (erdosConstruction N).card < g N := by
  intro M
  refine ⟨familyN M, ?_, erdosConstruction_card_lt_g M⟩
  simp [familyN, familyK]
  nlinarith

/-- An equivalent direct negation of eventual extremality. -/
theorem not_eventually_erdosConstruction_extremal :
    ¬ ∃ M : ℕ, ∀ N ≥ M,
      (erdosConstruction N).card = g N := by
  rintro ⟨M, hM⟩
  obtain ⟨N, hNM, hstrict⟩ := erdosConstruction_not_eventually_extremal M
  exact (ne_of_lt hstrict) (hM N hNM)

/-- **Erdős Problem 441 (negative resolution).** Erdős's proposed set is
always admissible, but it fails to attain the exact maximum for arbitrarily
large bounds. -/
theorem not_erdos_441 :
    (∀ N : ℕ, LcmBounded N (erdosConstruction N)) ∧
      ∀ M : ℕ, ∃ N ≥ M,
        (erdosConstruction N).card < g N := by
  exact ⟨erdosConstruction_lcmBounded,
    erdosConstruction_not_eventually_extremal⟩

#print axioms not_erdos_441

end Erdos441

alias _root_.Erdos441.erdos_441 := _root_.Erdos441.not_erdos_441
