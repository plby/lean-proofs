/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 179.
https://www.erdosproblems.com/forum/thread/179

Informal authors:
- Jacob Fox
- Cosmin Pohoata

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos179.md
-/
import Mathlib
import AddCombi.BSG
import ErdosProblems.Erdos179.CyclicModel
import ErdosProblems.Erdos179.SzemerediFour

/-!
# Erdős Problem 179

For a finite set of natural numbers, this file defines the exact number of
nontrivial, unoriented arithmetic progressions and Erdős's least forcing
threshold.  It then formalizes the two affirmative conclusions proved by
Fox and Pohoata:

* `F 3 n 4 = o(n²)`;
* for every fixed `k > 3`, `log (F 3 n k) / log n → 2`.

The source reconstruction and the Leanization details are in `tex/179.tex`.
-/

open Filter Finset Set
open scoped BigOperators Pointwise Topology Combinatorics.Additive'

namespace Erdos179

/-- `IsAPPair k A (a,b)` says that `a` and `b` are the first two terms of a
nontrivial `k`-term arithmetic progression contained in `A`.

For `k ≥ 2`, first two terms are a canonical code for an unoriented
progression: requiring `a < b` fixes the positive orientation. -/
def IsAPPair (k : ℕ) (A : Finset ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 < p.2 ∧ ∀ i ∈ Finset.range k, p.1 + i * (p.2 - p.1) ∈ A

/-- The finite set of canonical first-two-term codes of the `k`-APs in `A`. -/
noncomputable def apPairs (k : ℕ) (A : Finset ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (A ×ˢ A).filter (IsAPPair k A)

/-- The number of nontrivial, unoriented `k`-term APs in `A`.

The branch at `k = 1` implements the usual singleton convention.  Length
zero is irrelevant to Problem 179 and is assigned count zero. -/
noncomputable def apCount : ℕ → Finset ℕ → ℕ
  | 0, _ => 0
  | 1, A => #A
  | Nat.succ (Nat.succ k), A => #(apPairs (k + 2) A)

/-- A finite set contains a `k`-term arithmetic progression. -/
def HasAP : ℕ → Finset ℕ → Prop
  | 0, _ => True
  | 1, A => A.Nonempty
  | Nat.succ (Nat.succ k), A => (apPairs (k + 2) A).Nonempty

/-- A finite set contains no `k`-term arithmetic progression. -/
def APFree (k : ℕ) (A : Finset ℕ) : Prop := ¬HasAP k A

@[simp] lemma mem_apPairs {k : ℕ} {A : Finset ℕ} {a b : ℕ} :
    (a, b) ∈ apPairs k A ↔
      a ∈ A ∧ b ∈ A ∧ a < b ∧
        ∀ i < k, a + i * (b - a) ∈ A := by
  classical
  simp [apPairs, IsAPPair, and_assoc]

lemma apCount_le_sq (k : ℕ) (A : Finset ℕ) : apCount k A ≤ #A ^ 2 := by
  classical
  rcases k with _ | k
  · simp [apCount]
  rcases k with _ | k
  · simp only [apCount]
    have h : (#A : ℤ) ≤ (#A : ℤ) ^ 2 := by
      by_cases hA : #A = 0
      · simp [hA]
      · have : (1 : ℤ) ≤ #A := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hA)
        nlinarith
    exact_mod_cast h
  · change #(apPairs (k + 2) A) ≤ #A ^ 2
    exact (Finset.card_filter_le _ _).trans_eq (by simp [apPairs, pow_two])

/-- `ForcesLongAP s n k m` is the literal forcing property in Problem 179. -/
def ForcesLongAP (s n k m : ℕ) : Prop :=
  ∀ A : Finset ℕ, #A = n → m ≤ apCount s A → HasAP k A

lemma forcesLongAP_sq_add_one (s n k : ℕ) : ForcesLongAP s n k (n ^ 2 + 1) := by
  intro A hA hm
  exfalso
  have hcount := apCount_le_sq s A
  rw [hA] at hcount
  omega

lemma exists_forcing_threshold (s n k : ℕ) : ∃ m, ForcesLongAP s n k m :=
  ⟨n ^ 2 + 1, forcesLongAP_sq_add_one s n k⟩

/-- Erdős's threshold: the least number of short progressions forcing a long
progression in every `n`-element subset of `ℕ`. -/
noncomputable def F (s n k : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_forcing_threshold s n k)

lemma F_spec (s n k : ℕ) : ForcesLongAP s n k (F s n k) := by
  classical
  exact Nat.find_spec (exists_forcing_threshold s n k)

lemma F_minimal {s n k m : ℕ} (hm : ForcesLongAP s n k m) : F s n k ≤ m :=
  by
    classical
    exact Nat.find_min' (exists_forcing_threshold s n k) hm

lemma F_le_sq_add_one (s n k : ℕ) : F s n k ≤ n ^ 2 + 1 :=
  F_minimal (forcesLongAP_sq_add_one s n k)

lemma not_hasAP_of_lt_F {s n k m : ℕ} (hm : m < F s n k) :
    ∃ A : Finset ℕ, #A = n ∧ m ≤ apCount s A ∧ APFree k A := by
  by_contra! h
  have hforce : ForcesLongAP s n k m := by
    intro A hA hmA
    exact not_not.mp (h A hA hmA)
  exact (not_lt_of_ge (F_minimal hforce)) hm

lemma apCount_lt_F_of_APFree {s n k : ℕ} {A : Finset ℕ}
    (hcard : #A = n) (hfree : APFree k A) : apCount s A < F s n k := by
  by_contra h
  exact hfree (F_spec s n k A hcard (by omega))

lemma F_le_of_APFree_bound {s n k C : ℕ}
    (hbound : ∀ A : Finset ℕ, #A = n → APFree k A → apCount s A ≤ C) :
    F s n k ≤ C + 1 := by
  apply F_minimal
  intro A hcard hcount
  by_contra hfree
  have := hbound A hcard hfree
  omega

lemma hasAP_iff {k : ℕ} (hk : 2 ≤ k) (A : Finset ℕ) :
    HasAP k A ↔ ∃ a ∈ A, ∃ b ∈ A, a < b ∧
      ∀ i < k, a + i * (b - a) ∈ A := by
  rcases k with _ | _ | k
  · omega
  · omega
  · change (apPairs (k + 2) A).Nonempty ↔ _
    constructor
    · rintro ⟨⟨a, b⟩, hab⟩
      rw [mem_apPairs] at hab
      exact ⟨a, hab.1, b, hab.2.1, hab.2.2.1, fun i hi ↦ hab.2.2.2 i (by omega)⟩
    · rintro ⟨a, ha, b, hb, hab, hp⟩
      exact ⟨(a, b), mem_apPairs.mpr
        ⟨ha, hb, hab, fun i hi ↦ hp i (by omega)⟩⟩

/-- A concrete point beyond twice the largest member of `A`. -/
def nextPoint (A : Finset ℕ) : ℕ := 2 * A.sup id + 1

lemma lt_nextPoint_of_mem {A : Finset ℕ} {a : ℕ} (ha : a ∈ A) : a < nextPoint A := by
  have ha' : a ≤ A.sup id := by simpa using (Finset.le_sup (f := id) ha)
  unfold nextPoint
  omega

lemma nextPoint_not_mem (A : Finset ℕ) : nextPoint A ∉ A :=
  fun h ↦ (lt_nextPoint_of_mem h).false

/-- Adjoining `nextPoint A` cannot create an AP of length at least three.
The last three terms of a hypothetical new AP would force the new point to
be at most twice an old point, contradicting its definition. -/
lemma apFree_insert_nextPoint {k : ℕ} (hk : 3 ≤ k) {A : Finset ℕ}
    (hA : APFree k A) : APFree k (insert (nextPoint A) A) := by
  intro hnew
  rw [hasAP_iff (by omega)] at hnew
  obtain ⟨a, ha, b, hb, hab, hp⟩ := hnew
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  let d := b - a
  let x := nextPoint A
  have hd : 0 < d := Nat.sub_pos_of_lt hab
  have hlast_mem : a + (m + 2) * d ∈ insert x A := by
    apply hp
    omega
  have hnot_old : ∃ i < m + 3, a + i * d ∉ A := by
    by_contra! hall
    apply hA
    rw [hasAP_iff (by omega)]
    refine ⟨a, ?_, b, ?_, hab, ?_⟩
    · simpa [d] using hall 0 (by omega)
    · have := hall 1 (by omega)
      convert this using 1 <;> simp only [d, one_mul] <;> omega
    · intro j hj
      exact hall j (by omega)
  obtain ⟨i, hi, hiA⟩ := hnot_old
  have hix : a + i * d = x := by
    exact (Finset.mem_insert.mp (hp i (by omega))).resolve_right hiA
  have hlast_ge : x ≤ a + (m + 2) * d := by
    rw [← hix]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right d (by omega)) a
  have hlast : a + (m + 2) * d = x := by
    rcases Finset.mem_insert.mp hlast_mem with h | h
    · exact h
    · have := lt_nextPoint_of_mem h
      omega
  have hy_mem : a + (m + 1) * d ∈ insert x A := hp (m + 1) (by omega)
  have hz_mem : a + m * d ∈ insert x A := hp m (by omega)
  have hy_lt : a + (m + 1) * d < x := by
    rw [← hlast]
    dsimp [d] at hd ⊢
    nlinarith
  have hz_lt : a + m * d < x := by
    rw [← hlast]
    dsimp [d] at hd ⊢
    nlinarith
  have hyA : a + (m + 1) * d ∈ A :=
    (Finset.mem_insert.mp hy_mem).resolve_left (by omega)
  have hzA : a + m * d ∈ A :=
    (Finset.mem_insert.mp hz_mem).resolve_left (by omega)
  have hy_le : a + (m + 1) * d ≤ A.sup id := by
    simpa using (Finset.le_sup (f := id) hyA)
  have hthree : (a + m * d) + x =
      (a + (m + 1) * d) + (a + (m + 1) * d) := by
    rw [← hlast]
    ring
  unfold x nextPoint at hthree
  omega

/-- Any finite AP-free set can be padded to any larger cardinality without
creating a progression of length at least three. -/
lemma exists_APFree_superset_card {k n : ℕ} (hk : 3 ≤ k) {A : Finset ℕ}
    (hA : APFree k A) (hcard : #A ≤ n) :
    ∃ B : Finset ℕ, A ⊆ B ∧ #B = n ∧ APFree k B := by
  suffices h : ∀ d : ℕ, ∃ B : Finset ℕ,
      A ⊆ B ∧ #B = #A + d ∧ APFree k B by
    obtain ⟨B, hAB, hBcard, hBfree⟩ := h (n - #A)
    exact ⟨B, hAB, by omega, hBfree⟩
  intro d
  induction d with
  | zero => exact ⟨A, Finset.Subset.rfl, by simp, hA⟩
  | succ d ih =>
      obtain ⟨B, hAB, hBcard, hBfree⟩ := ih
      refine ⟨insert (nextPoint B) B, hAB.trans (Finset.subset_insert _ _), ?_,
        apFree_insert_nextPoint hk hBfree⟩
      rw [Finset.card_insert_of_notMem (nextPoint_not_mem B), hBcard]
      omega

lemma apFree_three_iff_threeAPFree (A : Finset ℕ) :
    APFree 3 A ↔ ThreeAPFree (A : Set ℕ) := by
  rw [threeAPFree_iff_eq_right]
  constructor
  · intro hfree a ha b hb c hc hac
    have ha' : a ∈ A := by simpa using ha
    have hb' : b ∈ A := by simpa using hb
    have hc' : c ∈ A := by simpa using hc
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · apply hfree
      rw [hasAP_iff (by omega)]
      have hsecond : a + (b - a) = b := by omega
      have hthird : a + 2 * (b - a) = c := by omega
      refine ⟨a, ha', b, hb', ?_, ?_⟩
      · omega
      · intro i hi
        interval_cases i <;> simp [hsecond, hthird, ha', hb', hc']
    · apply hfree
      rw [hasAP_iff (by omega)]
      have hsecond : c + (b - c) = b := by omega
      have hthird : c + 2 * (b - c) = a := by omega
      refine ⟨c, hc', b, hb', ?_, ?_⟩
      · omega
      · intro i hi
        interval_cases i <;> simp [hsecond, hthird, ha', hb', hc']
  · intro hthree hAP
    rw [hasAP_iff (by omega)] at hAP
    obtain ⟨a, ha, b, hb, hab, hp⟩ := hAP
    let c := a + 2 * (b - a)
    have hc : c ∈ A := hp 2 (by omega)
    have hac : a + c = b + b := by
      dsimp [c]
      omega
    have := hthree ha hb hc hac
    dsimp [c] at this
    omega

/-! ### The popular-second-difference construction -/

/-- The integer second difference of a triple of natural numbers. -/
def secondDiff (p : ℕ × (ℕ × ℕ)) : ℤ :=
  (p.1 : ℤ) - 2 * (p.2.1 : ℤ) + (p.2.2 : ℤ)

/-- Triples from `S³` with a prescribed integer second difference. -/
noncomputable def secondDiffFiber (S : Finset ℕ) (q : ℤ) :
    Finset (ℕ × (ℕ × ℕ)) := by
  classical
  exact (S ×ˢ (S ×ˢ S)).filter fun p ↦ secondDiff p = q

@[simp] lemma mem_secondDiffFiber {S : Finset ℕ} {q : ℤ}
    {x y z : ℕ} : (x, (y, z)) ∈ secondDiffFiber S q ↔
      x ∈ S ∧ y ∈ S ∧ z ∈ S ∧ (x : ℤ) - 2 * y + z = q := by
  classical
  rw [secondDiffFiber]
  constructor
  · intro h
    have hf := Finset.mem_filter.mp h
    have hp := Finset.mem_product.mp hf.1
    have hp' := Finset.mem_product.mp hp.2
    exact ⟨hp.1, hp'.1, hp'.2, by simpa [secondDiff] using hf.2⟩
  · rintro ⟨hx, hy, hz, hq⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hx, Finset.mem_product.mpr ⟨hy, hz⟩⟩, ?_⟩
    simpa [secondDiff] using hq

/-- Pigeonholing the integer second difference over its interval of possible
values.  This division-form estimate is the quantitative core of the lower
construction. -/
lemma exists_popular_secondDiff {S : Finset ℕ} {M : ℕ} (hSM : S ⊆ range M) :
    ∃ q : ℤ, q ∈ Finset.Icc (-(2 * M : ℤ)) (2 * M : ℤ) ∧
      #S ^ 3 / (4 * M + 1) ≤ #(secondDiffFiber S q) := by
  classical
  let D : Finset (ℕ × (ℕ × ℕ)) := S ×ˢ (S ×ˢ S)
  let Q : Finset ℤ := Finset.Icc (-(2 * M : ℤ)) (2 * M : ℤ)
  have hmap : ∀ p ∈ D, secondDiff p ∈ Q := by
    rintro ⟨x, y, z⟩ hp
    simp only [D, mem_product] at hp
    have hx := mem_range.mp (hSM hp.1)
    have hy := mem_range.mp (hSM hp.2.1)
    have hz := mem_range.mp (hSM hp.2.2)
    simp only [Q, Finset.mem_Icc, secondDiff]
    constructor <;> norm_num at * <;> omega
  have hQ : Q.Nonempty := by
    refine ⟨0, ?_⟩
    simp [Q]
  have hQcard : #Q = 4 * M + 1 := by
    simp [Q, Int.card_Icc]
    omega
  have hDcard : #D = #S ^ 3 := by
    simp [D, pow_succ]
    ring
  have hmul : #Q * (#S ^ 3 / (4 * M + 1)) ≤ #D := by
    rw [hQcard, hDcard]
    exact Nat.mul_div_le _ _
  obtain ⟨q, hqQ, hqcard⟩ :=
    exists_le_card_fiber_of_mul_le_card_of_maps_to hmap hQ hmul
  refine ⟨q, hqQ, ?_⟩
  simpa [secondDiffFiber, D] using hqcard

/-- The offset of the third block.  The first two offsets are `0` and
`10M`; the identity `thirdOffset = 20M-q` makes a triple of second
difference `q` into an arithmetic progression across the blocks. -/
def thirdOffset (M : ℕ) (q : ℤ) : ℕ :=
  Int.toNat (20 * (M : ℤ) - q)

def blockOffset (M : ℕ) (q : ℤ) (i : ℕ) : ℕ :=
  if i = 0 then 0 else if i = 1 then 10 * M else thirdOffset M q

lemma thirdOffset_bounds {M : ℕ} {q : ℤ}
    (hq : q ∈ Finset.Icc (-(2 * M : ℤ)) (2 * M : ℤ)) :
    18 * M ≤ thirdOffset M q ∧ thirdOffset M q ≤ 22 * M := by
  simp only [Finset.mem_Icc] at hq
  have hnonneg : 0 ≤ 20 * (M : ℤ) - q := by omega
  have hoff : (thirdOffset M q : ℤ) = 20 * (M : ℤ) - q := by
    simp [thirdOffset, Int.toNat_of_nonneg hnonneg]
  constructor
  · have hlo : ((18 * M : ℕ) : ℤ) ≤ (thirdOffset M q : ℤ) := by
      rw [hoff]
      norm_num
      omega
    exact_mod_cast hlo
  · have hhi : (thirdOffset M q : ℤ) ≤ ((22 * M : ℕ) : ℤ) := by
      rw [hoff]
      norm_num
      omega
    exact_mod_cast hhi

lemma thirdOffset_cast {M : ℕ} {q : ℤ}
    (hq : q ∈ Finset.Icc (-(2 * M : ℤ)) (2 * M : ℤ)) :
    (thirdOffset M q : ℤ) = 20 * (M : ℤ) - q := by
  simp only [Finset.mem_Icc] at hq
  have hnonneg : 0 ≤ 20 * (M : ℤ) - q := by omega
  simp [thirdOffset, Int.toNat_of_nonneg hnonneg]

/-- The three separated translates used in the deterministic lower bound. -/
noncomputable def threeBlockSet (S : Finset ℕ) (M : ℕ) (q : ℤ) : Finset ℕ := by
  classical
  exact ((range 3) ×ˢ S).image fun p ↦ p.2 + blockOffset M q p.1

lemma mem_threeBlockSet {S : Finset ℕ} {M : ℕ} {q : ℤ} {a : ℕ} :
    a ∈ threeBlockSet S M q ↔
      ∃ i < 3, ∃ x ∈ S, x + blockOffset M q i = a := by
  classical
  rw [threeBlockSet, Finset.mem_image]
  constructor
  · rintro ⟨⟨i, x⟩, hp, rfl⟩
    have hp := Finset.mem_product.mp hp
    exact ⟨i, mem_range.mp hp.1, x, hp.2, rfl⟩
  · rintro ⟨i, hi, x, hx, rfl⟩
    exact ⟨(i, x), Finset.mem_product.mpr ⟨mem_range.mpr hi, hx⟩, rfl⟩

lemma blockIndex_le_of_lt {M : ℕ} {q : ℤ}
    (hq : q ∈ Finset.Icc (-(2 * M : ℤ)) (2 * M : ℤ))
    {i j x y : ℕ} (hi : i < 3) (hj : j < 3) (hx : x < M) (hy : y < M)
    (hxy : x + blockOffset M q i < y + blockOffset M q j) : i ≤ j := by
  have hoff := thirdOffset_bounds hq
  interval_cases i <;> interval_cases j <;> simp [blockOffset] at hxy ⊢ <;> omega

lemma blockIndex_eq_of_small_step {M : ℕ} {q : ℤ}
    (hq : q ∈ Finset.Icc (-(2 * M : ℤ)) (2 * M : ℤ))
    {i j x y d : ℕ} (hi : i < 3) (hj : j < 3) (hx : x < M) (hy : y < M)
    (hstep : x + blockOffset M q i + d = y + blockOffset M q j)
    (hd : d < M) : i = j := by
  have hoff := thirdOffset_bounds hq
  interval_cases i <;> interval_cases j <;> simp [blockOffset] at hstep ⊢ <;> omega

lemma threeBlockSet_card {S : Finset ℕ} {M : ℕ} {q : ℤ}
    (hSM : S ⊆ range M)
    (hq : q ∈ Finset.Icc (-(2 * M : ℤ)) (2 * M : ℤ)) :
    #(threeBlockSet S M q) = 3 * #S := by
  classical
  rw [threeBlockSet, Finset.card_image_of_injOn]
  · simp
  · rintro ⟨i, x⟩ hp ⟨j, y⟩ hp' heq
    have hp := Finset.mem_product.mp hp
    have hp' := Finset.mem_product.mp hp'
    have hi := mem_range.mp hp.1
    have hj := mem_range.mp hp'.1
    have hx := mem_range.mp (hSM hp.2)
    have hy := mem_range.mp (hSM hp'.2)
    have hoff := thirdOffset_bounds hq
    apply Prod.ext
    · interval_cases i <;> interval_cases j <;>
        simp [blockOffset] at heq ⊢ <;> omega
    · interval_cases i <;> interval_cases j <;>
        simp [blockOffset] at heq ⊢ <;> omega

lemma hasAP_of_hasAP_of_le {j k : ℕ} (hj : 2 ≤ j) (hjk : j ≤ k)
    {A : Finset ℕ} (hA : HasAP k A) : HasAP j A := by
  rw [hasAP_iff hj]
  rw [hasAP_iff (hj.trans hjk)] at hA
  obtain ⟨a, ha, b, hb, hab, hp⟩ := hA
  exact ⟨a, ha, b, hb, hab, fun i hi ↦ hp i (hi.trans_le hjk)⟩

lemma apFree_of_four_free {k : ℕ} (hk : 4 ≤ k) {A : Finset ℕ}
    (hA : APFree 4 A) : APFree k A :=
  fun h ↦ hA (hasAP_of_hasAP_of_le (by omega) hk h)

/-- Four terms cannot fit into the three separated blocks.  If two
consecutive terms lie in one block, the common difference is less than
`M`; that small step cannot cross either gap, so all four terms lie in one
translate of the three-AP-free set `S`. -/
lemma threeBlockSet_four_free {S : Finset ℕ} {M : ℕ} {q : ℤ}
    (hSM : S ⊆ range M) (hS : ThreeAPFree (S : Set ℕ))
    (hq : q ∈ Finset.Icc (-(2 * M : ℤ)) (2 * M : ℤ)) :
    APFree 4 (threeBlockSet S M q) := by
  intro hAP
  rw [hasAP_iff (by omega)] at hAP
  obtain ⟨a, ha, b, hb, hab, hp⟩ := hAP
  let d := b - a
  have hd : 0 < d := Nat.sub_pos_of_lt hab
  have ht0 : a ∈ threeBlockSet S M q := by simpa using hp 0 (by omega)
  have ht1 : a + d ∈ threeBlockSet S M q := by simpa [d] using hp 1 (by omega)
  have ht2 : a + 2 * d ∈ threeBlockSet S M q := hp 2 (by omega)
  have ht3 : a + 3 * d ∈ threeBlockSet S M q := hp 3 (by omega)
  obtain ⟨i0, hi0, x0, hx0S, e0⟩ := mem_threeBlockSet.mp ht0
  obtain ⟨i1, hi1, x1, hx1S, e1⟩ := mem_threeBlockSet.mp ht1
  obtain ⟨i2, hi2, x2, hx2S, e2⟩ := mem_threeBlockSet.mp ht2
  obtain ⟨i3, hi3, x3, hx3S, e3⟩ := mem_threeBlockSet.mp ht3
  have hx0 := mem_range.mp (hSM hx0S)
  have hx1 := mem_range.mp (hSM hx1S)
  have hx2 := mem_range.mp (hSM hx2S)
  have hx3 := mem_range.mp (hSM hx3S)
  have hv01 : x0 + blockOffset M q i0 < x1 + blockOffset M q i1 := by omega
  have hv12 : x1 + blockOffset M q i1 < x2 + blockOffset M q i2 := by omega
  have hv23 : x2 + blockOffset M q i2 < x3 + blockOffset M q i3 := by omega
  have hi01 : i0 ≤ i1 := blockIndex_le_of_lt hq hi0 hi1 hx0 hx1 hv01
  have hi12 : i1 ≤ i2 := blockIndex_le_of_lt hq hi1 hi2 hx1 hx2 hv12
  have hi23 : i2 ≤ i3 := blockIndex_le_of_lt hq hi2 hi3 hx2 hx3 hv23
  have hsibling : i0 = i1 ∨ i1 = i2 ∨ i2 = i3 := by omega
  have hdM : d < M := by
    rcases hsibling with h01 | h12 | h23
    · subst i1
      omega
    · subst i2
      omega
    · subst i3
      omega
  have ei01 : i0 = i1 := blockIndex_eq_of_small_step hq hi0 hi1 hx0 hx1 (by omega) hdM
  have ei12 : i1 = i2 := blockIndex_eq_of_small_step hq hi1 hi2 hx1 hx2 (by omega) hdM
  have ei23 : i2 = i3 := blockIndex_eq_of_small_step hq hi2 hi3 hx2 hx3 (by omega) hdM
  subst i1
  subst i2
  subst i3
  rw [threeAPFree_iff_eq_right] at hS
  have hxsum : x0 + x2 = x1 + x1 := by omega
  have hx02 : x0 = x2 := hS hx0S hx1S hx2S hxsum
  omega

lemma threeBlockSet_APFree {k : ℕ} (hk : 4 ≤ k) {S : Finset ℕ} {M : ℕ} {q : ℤ}
    (hSM : S ⊆ range M) (hS : ThreeAPFree (S : Set ℕ))
    (hq : q ∈ Finset.Icc (-(2 * M : ℤ)) (2 * M : ℤ)) :
    APFree k (threeBlockSet S M q) :=
  apFree_of_four_free hk (threeBlockSet_four_free hSM hS hq)

/-- A popular triple is encoded by the first two terms of its cross-block
three-term progression. -/
def popularTriplePair (M : ℕ) (p : ℕ × (ℕ × ℕ)) : ℕ × ℕ :=
  (p.1, p.2.1 + 10 * M)

lemma popularTriplePair_injOn (S : Finset ℕ) (M : ℕ) (q : ℤ) :
    Set.InjOn (popularTriplePair M) (secondDiffFiber S q : Set (ℕ × (ℕ × ℕ))) := by
  rintro ⟨x, y, z⟩ hp ⟨x', y', z'⟩ hp' heq
  change (x, (y, z)) ∈ secondDiffFiber S q at hp
  change (x', (y', z')) ∈ secondDiffFiber S q at hp'
  rw [mem_secondDiffFiber] at hp hp'
  have hxy : x = x' ∧ y = y' := by
    simpa [popularTriplePair] using heq
  rcases hxy with ⟨rfl, rfl⟩
  have hzz : z = z' := by exact_mod_cast (by omega : (z : ℤ) = z')
  subst z'
  rfl

noncomputable def popularAPPairs (S : Finset ℕ) (M : ℕ) (q : ℤ) :
    Finset (ℕ × ℕ) := by
  classical
  exact (secondDiffFiber S q).image (popularTriplePair M)

lemma popularAPPairs_card (S : Finset ℕ) (M : ℕ) (q : ℤ) :
    #(popularAPPairs S M q) = #(secondDiffFiber S q) := by
  classical
  rw [popularAPPairs, Finset.card_image_of_injOn]
  exact popularTriplePair_injOn S M q

lemma popularAPPairs_subset {S : Finset ℕ} {M : ℕ} {q : ℤ}
    (hSM : S ⊆ range M)
    (hq : q ∈ Finset.Icc (-(2 * M : ℤ)) (2 * M : ℤ)) :
    popularAPPairs S M q ⊆ apPairs 3 (threeBlockSet S M q) := by
  classical
  intro pair hpair
  rw [popularAPPairs, Finset.mem_image] at hpair
  obtain ⟨⟨x, y, z⟩, hp, rfl⟩ := hpair
  rw [mem_secondDiffFiber] at hp
  have hxM := mem_range.mp (hSM hp.1)
  have hyM := mem_range.mp (hSM hp.2.1)
  have hzM := mem_range.mp (hSM hp.2.2.1)
  have hxy : x < y + 10 * M := by omega
  have hxA : x ∈ threeBlockSet S M q := by
    apply mem_threeBlockSet.mpr
    exact ⟨0, by omega, x, hp.1, by simp [blockOffset]⟩
  have hyA : y + 10 * M ∈ threeBlockSet S M q := by
    apply mem_threeBlockSet.mpr
    exact ⟨1, by omega, y, hp.2.1, by simp [blockOffset]⟩
  have hzA : z + thirdOffset M q ∈ threeBlockSet S M q := by
    apply mem_threeBlockSet.mpr
    exact ⟨2, by omega, z, hp.2.2.1, by simp [blockOffset]⟩
  have hthird : x + 2 * (y + 10 * M - x) = z + thirdOffset M q := by
    have hsub : x ≤ y + 10 * M := hxy.le
    have hoff := thirdOffset_cast hq
    have hZ : ((x + 2 * (y + 10 * M - x) : ℕ) : ℤ) =
        ((z + thirdOffset M q : ℕ) : ℤ) := by
      push_cast
      rw [Int.ofNat_sub hsub, hoff]
      norm_num at *
      omega
    exact_mod_cast hZ
  have hsecond : x + (y + 10 * M - x) = y + 10 * M := by omega
  rw [mem_apPairs]
  refine ⟨hxA, hyA, hxy, ?_⟩
  intro i hi
  interval_cases i
  · simpa [popularTriplePair] using hxA
  · simpa [popularTriplePair, hsecond] using hyA
  · simpa [popularTriplePair, hthird] using hzA

lemma secondDiffFiber_card_le_apCount {S : Finset ℕ} {M : ℕ} {q : ℤ}
    (hSM : S ⊆ range M)
    (hq : q ∈ Finset.Icc (-(2 * M : ℤ)) (2 * M : ℤ)) :
    #(secondDiffFiber S q) ≤ apCount 3 (threeBlockSet S M q) := by
  change #(secondDiffFiber S q) ≤ #(apPairs 3 (threeBlockSet S M q))
  rw [← popularAPPairs_card S M q]
  exact Finset.card_le_card (popularAPPairs_subset hSM hq)

lemma threeBlock_lower_bound {k M : ℕ} (hk : 4 ≤ k) {S : Finset ℕ}
    (hSM : S ⊆ range M) (hS : ThreeAPFree (S : Set ℕ)) :
    ∃ A : Finset ℕ, #A = 3 * #S ∧ APFree k A ∧
      #S ^ 3 / (4 * M + 1) ≤ apCount 3 A := by
  obtain ⟨q, hq, hpopular⟩ := exists_popular_secondDiff hSM
  refine ⟨threeBlockSet S M q, threeBlockSet_card hSM hq,
    threeBlockSet_APFree hk hSM hS hq, ?_⟩
  exact hpopular.trans (secondDiffFiber_card_le_apCount hSM hq)

lemma apCount_three_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    apCount 3 A ≤ apCount 3 B := by
  change #(apPairs 3 A) ≤ #(apPairs 3 B)
  apply Finset.card_le_card
  intro p hp
  rcases p with ⟨a, b⟩
  rw [mem_apPairs] at hp ⊢
  exact ⟨hAB hp.1, hAB hp.2.1, hp.2.2.1,
    fun i hi ↦ hAB (hp.2.2.2 i hi)⟩

lemma eventually_three_mul_roth_le :
    ∀ᶠ n : ℕ in atTop, 3 * rothNumberNat n ≤ n := by
  have h := rothNumberNat_isLittleO_id.def
    (show (0 : ℝ) < 1 / 3 by norm_num)
  filter_upwards [h] with n hn
  have hrnonneg : 0 ≤ (rothNumberNat n : ℝ) := Nat.cast_nonneg _
  have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hrnonneg,
    Real.norm_eq_abs, abs_of_nonneg hnnonneg] at hn
  norm_num at hn
  have hn' : 3 * (rothNumberNat n : ℝ) ≤ n := by nlinarith
  exact_mod_cast hn'

/-- A division-form lower bound for the actual forcing threshold.  It is
already sufficient for the logarithmic exponent after Behrend's estimate. -/
lemma F_three_lower_eventually {k : ℕ} (hk : 4 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      rothNumberNat n ^ 3 / (4 * n + 1) < F 3 n k := by
  filter_upwards [eventually_three_mul_roth_le] with n hn
  obtain ⟨S, hSn, hScard, hSfree⟩ := rothNumberNat_spec n
  obtain ⟨A, hAcard, hAfree, hAcount⟩ :=
    threeBlock_lower_bound hk hSn hSfree
  have hAcard_le : #A ≤ n := by omega
  obtain ⟨B, hAB, hBcard, hBfree⟩ :=
    exists_APFree_superset_card (by omega) hAfree hAcard_le
  have hcount : rothNumberNat n ^ 3 / (4 * n + 1) ≤ apCount 3 B := by
    rw [← hScard]
    exact hAcount.trans (apCount_three_mono hAB)
  exact hcount.trans_lt (apCount_lt_F_of_APFree hBcard hBfree)

/-! ### Analytic form of the lower bound -/

lemma natCast_half_quotient_le_div {a b : ℕ} (hb : 0 < b) (hab : 2 * b ≤ a) :
    (a : ℝ) / (2 * b) ≤ (a / b : ℕ) := by
  have hg : 1 ≤ a / b := by
    apply (Nat.le_div_iff_mul_le hb).mpr
    omega
  have hmod : a % b ≤ b := (Nat.mod_lt a hb).le
  have ha : a ≤ 2 * b * (a / b) := by
    calc
      a = b * (a / b) + a % b := (Nat.div_add_mod a b).symm
      _ ≤ b * (a / b) + b := Nat.add_le_add_left hmod _
      _ ≤ 2 * b * (a / b) := by nlinarith
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * b)]
  have ha' : a ≤ (a / b) * (2 * b) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using ha
  exact_mod_cast ha'

lemma behrend_real_quotient_lower {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ 2 / 5 * Real.exp (-12 * √(Real.log n)) ≤
      (rothNumberNat n : ℝ) ^ 3 / (4 * n + 1) := by
  have hr := Behrend.roth_lower_bound (N := n)
  have hcub : ((n : ℝ) * Real.exp (-4 * √(Real.log n))) ^ 3 ≤
      (rothNumberNat n : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hr 3
  have hden : (4 * (n : ℝ) + 1) ≤ 5 * n := by
    exact_mod_cast (by omega : 4 * n + 1 ≤ 5 * n)
  have hcore : 0 ≤ (n : ℝ) ^ 2 / 5 * Real.exp (-12 * √(Real.log n)) := by
    positivity
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * n + 1)]
  calc
    (n : ℝ) ^ 2 / 5 * Real.exp (-12 * √(Real.log n)) * (4 * n + 1)
        ≤ (n : ℝ) ^ 2 / 5 * Real.exp (-12 * √(Real.log n)) * (5 * n) :=
          mul_le_mul_of_nonneg_left hden hcore
    _ = ((n : ℝ) * Real.exp (-4 * √(Real.log n))) ^ 3 := by
      rw [show -12 * √(Real.log n) = (3 : ℕ) * (-4 * √(Real.log n)) by ring,
        Real.exp_nat_mul]
      ring
    _ ≤ (rothNumberNat n : ℝ) ^ 3 := hcub

lemma eventually_behrend_core_ge_two :
    ∀ᶠ n : ℕ in atTop,
      2 ≤ (n : ℝ) ^ 2 / 5 * Real.exp (-12 * √(Real.log n)) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog144 : ∀ᶠ n : ℕ in atTop, (144 : ℝ) ≤ Real.log n :=
    (tendsto_atTop.1 hlog) 144
  filter_upwards [eventually_ge_atTop 10, hlog144] with n hn hln
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlognonneg : 0 ≤ Real.log (n : ℝ) := by linarith
  have hsqrt : 12 * √(Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by
    have hs := Real.sq_sqrt hlognonneg
    have hsnonneg := Real.sqrt_nonneg (Real.log (n : ℝ))
    have hs12 : 12 ≤ √(Real.log (n : ℝ)) := by nlinarith
    nlinarith
  have hexp : Real.exp (-Real.log (n : ℝ)) ≤
      Real.exp (-12 * √(Real.log (n : ℝ))) :=
    Real.exp_le_exp.mpr (by linarith)
  have hexplog : Real.exp (-Real.log (n : ℝ)) = 1 / n := by
    rw [Real.exp_neg, Real.exp_log hnR, one_div]
  have hmain : (n : ℝ) / 5 ≤
      (n : ℝ) ^ 2 / 5 * Real.exp (-12 * √(Real.log n)) := by
    calc
      (n : ℝ) / 5 = (n : ℝ) ^ 2 / 5 * Real.exp (-Real.log n) := by
        rw [hexplog]
        field_simp
      _ ≤ (n : ℝ) ^ 2 / 5 * Real.exp (-12 * √(Real.log n)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
  have hnreal : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have htwo : (2 : ℝ) ≤ n / 5 := by linarith
  exact htwo.trans hmain

lemma behrend_nat_quotient_lower_eventually :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 / 10 * Real.exp (-12 * √(Real.log n)) ≤
        (rothNumberNat n ^ 3 / (4 * n + 1) : ℕ) := by
  filter_upwards [eventually_ge_atTop 1, eventually_behrend_core_ge_two] with n hn htwo
  let a := rothNumberNat n ^ 3
  let b := 4 * n + 1
  have hb : 0 < b := by dsimp [b]; omega
  have hquot := behrend_real_quotient_lower hn
  have hquot' : (n : ℝ) ^ 2 / 5 * Real.exp (-12 * √(Real.log n)) ≤
      (a : ℝ) / b := by
    dsimp [a, b]
    push_cast
    exact hquot
  have htwoquot : (2 : ℝ) ≤ (a : ℝ) / b := by
    exact htwo.trans hquot'
  have hab : 2 * b ≤ a := by
    have : (2 * b : ℝ) ≤ a := (le_div_iff₀ (by positivity : (0 : ℝ) < b)).mp htwoquot
    exact_mod_cast this
  calc
    (n : ℝ) ^ 2 / 10 * Real.exp (-12 * √(Real.log n)) =
        ((n : ℝ) ^ 2 / 5 * Real.exp (-12 * √(Real.log n))) / 2 := by ring
    _ ≤ (((a : ℝ) / b) / 2) := div_le_div_of_nonneg_right hquot' (by norm_num)
    _ = (a : ℝ) / (2 * b) := by ring
    _ ≤ (a / b : ℕ) := natCast_half_quotient_le_div hb hab

lemma F_behrend_lower_eventually {k : ℕ} (hk : 4 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 / 10 * Real.exp (-12 * √(Real.log n)) ≤ (F 3 n k : ℝ) := by
  filter_upwards [behrend_nat_quotient_lower_eventually,
    F_three_lower_eventually hk] with n hreal hF
  exact hreal.trans (by exact_mod_cast hF.le)

noncomputable def lowerLogEnvelope (n : ℕ) : ℝ :=
  (2 * Real.log (n : ℝ) - Real.log 10 - 12 * √(Real.log n)) / Real.log n

noncomputable def upperLogEnvelope (n : ℕ) : ℝ :=
  (Real.log 2 + 2 * Real.log (n : ℝ)) / Real.log n

lemma tendsto_sqrt_log_div_log :
    Tendsto (fun n : ℕ ↦ √(Real.log (n : ℝ)) / Real.log n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun n : ℕ ↦ √(Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  have hinv : Tendsto (fun n : ℕ ↦ (√(Real.log (n : ℝ)))⁻¹) atTop (𝓝 0) :=
    hsqrt.inv_tendsto_atTop
  convert hinv using 1
  funext n
  exact Real.sqrt_div_self

lemma tendsto_inv_log :
    Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ))⁻¹) atTop (𝓝 0) := by
  exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop

lemma tendsto_lowerLogEnvelope :
    Tendsto lowerLogEnvelope atTop (𝓝 2) := by
  have h1 : Tendsto (fun n : ℕ ↦ Real.log 10 * (Real.log (n : ℝ))⁻¹)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul tendsto_inv_log
  have h2 : Tendsto (fun n : ℕ ↦ 12 * (√(Real.log (n : ℝ)) / Real.log n))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul tendsto_sqrt_log_div_log
  have hmain : Tendsto
      (fun n : ℕ ↦ 2 - Real.log 10 * (Real.log (n : ℝ))⁻¹ -
        12 * (√(Real.log (n : ℝ)) / Real.log n)) atTop (𝓝 2) := by
    simpa using (tendsto_const_nhds.sub h1).sub h2
  apply hmain.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  unfold lowerLogEnvelope
  field_simp

lemma tendsto_upperLogEnvelope :
    Tendsto upperLogEnvelope atTop (𝓝 2) := by
  have h1 : Tendsto (fun n : ℕ ↦ Real.log 2 * (Real.log (n : ℝ))⁻¹)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul tendsto_inv_log
  have hmain : Tendsto (fun n : ℕ ↦ Real.log 2 * (Real.log (n : ℝ))⁻¹ + 2)
      atTop (𝓝 2) := by
    simpa using h1.add tendsto_const_nhds
  apply hmain.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  unfold upperLogEnvelope
  field_simp

lemma eventually_log_ratio_between {k : ℕ} (hk : 4 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      lowerLogEnvelope n ≤ Real.log (F 3 n k) / Real.log n ∧
        Real.log (F 3 n k) / Real.log n ≤ upperLogEnvelope n := by
  filter_upwards [eventually_ge_atTop 2, F_behrend_lower_eventually hk] with n hn hlower
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  let core : ℝ := (n : ℝ) ^ 2 / 10 * Real.exp (-12 * √(Real.log n))
  have hcorepos : 0 < core := by dsimp [core]; positivity
  have hFpos : 0 < (F 3 n k : ℝ) := hcorepos.trans_le hlower
  have hloglower : Real.log core ≤ Real.log (F 3 n k) :=
    Real.log_le_log hcorepos hlower
  have hlogcore : Real.log core =
      2 * Real.log (n : ℝ) - Real.log 10 - 12 * √(Real.log n) := by
    dsimp [core]
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
      Real.log_div (by positivity) (by norm_num), Real.log_pow, Real.log_exp]
    norm_num
    ring
  have hlowerRatio : lowerLogEnvelope n ≤
      Real.log (F 3 n k) / Real.log n := by
    unfold lowerLogEnvelope
    rw [← hlogcore]
    exact div_le_div_of_nonneg_right hloglower hlogpos.le
  have hFsq : (F 3 n k : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
    have hF := F_le_sq_add_one 3 n k
    have hcast : (F 3 n k : ℝ) ≤ (n ^ 2 + 1 : ℕ) := by exact_mod_cast hF
    calc
      (F 3 n k : ℝ) ≤ (n ^ 2 + 1 : ℕ) := hcast
      _ ≤ 2 * (n : ℝ) ^ 2 := by
        push_cast
        have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hlogupper : Real.log (F 3 n k) ≤ Real.log (2 * (n : ℝ) ^ 2) :=
    Real.log_le_log hFpos hFsq
  have hlogtwo : Real.log (2 * (n : ℝ) ^ 2) =
      Real.log 2 + 2 * Real.log (n : ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
  have hupperRatio : Real.log (F 3 n k) / Real.log n ≤ upperLogEnvelope n := by
    unfold upperLogEnvelope
    rw [← hlogtwo]
    exact div_le_div_of_nonneg_right hlogupper hlogpos.le
  exact ⟨hlowerRatio, hupperRatio⟩

theorem tendsto_log_F_three {k : ℕ} (hk : 4 ≤ k) :
    Tendsto (fun n : ℕ ↦ Real.log (F 3 n k) / Real.log n) atTop (𝓝 2) := by
  have hbetween := eventually_log_ratio_between hk
  exact tendsto_lowerLogEnvelope.squeeze' tendsto_upperLogEnvelope
    (hbetween.mono fun _ h ↦ h.1)
    (hbetween.mono fun _ h ↦ h.2)

namespace UpperBound

noncomputable def castFinset (p : ℕ) (A : Finset ℕ) : Finset (ZMod p) :=
  A.image fun a : ℕ ↦ (a : ZMod p)

noncomputable def doubleFinset {p : ℕ} (B : Finset (ZMod p)) : Finset (ZMod p) :=
  B.image fun b ↦ b + b

lemma cast_injOn {p : ℕ} [NeZero p] {A : Finset ℕ}
    (hA : ∀ a ∈ A, a < p) : Set.InjOn (fun a : ℕ ↦ (a : ZMod p)) A := by
  intro a ha b hb hab
  have hval := congrArg ZMod.val hab
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (hA a ha),
    Nat.mod_eq_of_lt (hA b hb)] using hval

lemma card_castFinset {p : ℕ} [NeZero p] {A : Finset ℕ}
    (hA : ∀ a ∈ A, a < p) : (castFinset p A).card = A.card := by
  unfold castFinset
  exact card_image_of_injOn (cast_injOn hA)

lemma card_doubleFinset_le {p : ℕ} (B : Finset (ZMod p)) :
    (doubleFinset B).card ≤ B.card := card_image_le

lemma ap_endpoint_mem {p : ℕ} [NeZero p] {A : Finset ℕ}
    {a b : ℕ} (hab : (a, b) ∈ apPairs 3 A) :
    ((a : ZMod p), ((a + 2 * (b - a) : ℕ) : ZMod p)) ∈
      castFinset p A ×ˢ castFinset p A := by
  rw [mem_product]
  constructor
  · exact mem_image.mpr ⟨a, (mem_apPairs.mp hab).1, rfl⟩
  · apply mem_image.mpr
    refine ⟨a + 2 * (b - a), ?_, rfl⟩
    exact (mem_apPairs.mp hab).2.2.2 2 (by omega)

lemma ap_endpoint_sum_mem_double {p : ℕ} [NeZero p] {A : Finset ℕ}
    {a b : ℕ} (hab : (a, b) ∈ apPairs 3 A) :
    (a : ZMod p) + ((a + 2 * (b - a) : ℕ) : ZMod p) ∈
      doubleFinset (castFinset p A) := by
  apply mem_image.mpr
  refine ⟨(b : ZMod p), ?_, ?_⟩
  · exact mem_image.mpr ⟨b, (mem_apPairs.mp hab).2.1, rfl⟩
  · have hablt := (mem_apPairs.mp hab).2.2.1
    push_cast
    rw [Nat.cast_sub hablt.le]
    ring

lemma ap_endpoint_injOn {p : ℕ} [NeZero p] {A : Finset ℕ}
    (hA : ∀ a ∈ A, a < p) :
    Set.InjOn (fun ab : ℕ × ℕ ↦
      ((ab.1 : ZMod p), ((ab.1 + 2 * (ab.2 - ab.1) : ℕ) : ZMod p)))
      (apPairs 3 A) := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd heq
  have hfst : (a : ZMod p) = (c : ZMod p) := congrArg Prod.fst heq
  have hac : a = c := cast_injOn hA (mem_apPairs.mp hab).1
    (mem_apPairs.mp hcd).1 hfst
  subst c
  have hsnd : ((a + 2 * (b - a) : ℕ) : ZMod p) =
      ((a + 2 * (d - a) : ℕ) : ZMod p) := congrArg Prod.snd heq
  have hbmem := (mem_apPairs.mp hab).2.2.2 2 (by omega)
  have hdmem := (mem_apPairs.mp hcd).2.2.2 2 (by omega)
  have hnat : a + 2 * (b - a) = a + 2 * (d - a) :=
    cast_injOn hA hbmem hdmem hsnd
  have hablt := (mem_apPairs.mp hab).2.2.1
  have hadlt := (mem_apPairs.mp hcd).2.2.1
  apply Prod.ext
  · rfl
  · omega

lemma apCount_le_restrictedPairs {p : ℕ} [NeZero p] {A : Finset ℕ}
    (hA : ∀ a ∈ A, a < p) :
    apCount 3 A ≤
      #{xy ∈ castFinset p A ×ˢ castFinset p A |
        xy.1 + xy.2 ∈ doubleFinset (castFinset p A)} := by
  change (apPairs 3 A).card ≤ _
  apply Finset.card_le_card_of_injOn
    (fun ab : ℕ × ℕ ↦
      ((ab.1 : ZMod p), ((ab.1 + 2 * (ab.2 - ab.1) : ℕ) : ZMod p)))
  · intro ab hab
    change (fun ab : ℕ × ℕ ↦
      ((ab.1 : ZMod p), ((ab.1 + 2 * (ab.2 - ab.1) : ℕ) : ZMod p))) ab ∈
        {xy ∈ castFinset p A ×ˢ castFinset p A |
          xy.1 + xy.2 ∈ doubleFinset (castFinset p A)}
    rw [Finset.mem_filter]
    exact ⟨ap_endpoint_mem hab, ap_endpoint_sum_mem_double hab⟩
  · exact ap_endpoint_injOn hA

lemma energy_lower_of_many_threeAPs {p : ℕ} [NeZero p] {A : Finset ℕ}
    (hA : ∀ a ∈ A, a < p) (hAne : A.Nonempty) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hmany : epsilon * (A.card : ℝ) ^ 2 ≤ apCount 3 A) :
    epsilon ^ 2 * (castFinset p A).dens ^ 3 ≤ E[castFinset p A] := by
  let B := castFinset p A
  let U := doubleFinset B
  let P := {xy ∈ B ×ˢ B | xy.1 + xy.2 ∈ U}
  have hBcard : B.card = A.card := card_castFinset hA
  have hPcardNat : apCount 3 A ≤ P.card := by
    simpa [B, U, P] using apCount_le_restrictedPairs hA
  have hPcard : epsilon * (A.card : ℝ) ^ 2 ≤ (P.card : ℝ) := by
    exact hmany.trans (by exact_mod_cast hPcardNat)
  have hUcardNat : U.card ≤ A.card := by
    exact (card_doubleFinset_le B).trans_eq hBcard
  have hUcard : (U.card : ℝ) ≤ A.card := by exact_mod_cast hUcardNat
  have henergy := Finset.card_sq_le_card_mul_addEnergy' B B U
  have hp : (0 : ℝ) < p := by
    have : 0 < p := NeZero.pos p
    exact_mod_cast this
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hAne.card_pos
  simp only [Finset.dens, Fintype.card_prod, ZMod.card, Nat.cast_mul] at henergy ⊢
  push_cast at henergy ⊢
  rw [hBcard]
  have henergyR : ((P.card : ℝ) / ((p : ℝ) * p)) ^ 2 ≤
      ((U.card : ℝ) / p) * (E[B] : ℝ) := by
    have henergy' :
        ((P.card : ℚ≥0) / ((p : ℚ≥0) * p)) ^ 2 ≤
          ((U.card : ℚ≥0) / p) * E[B] := by
      simpa [P] using henergy
    have hcoerced :
        ((((P.card : ℚ≥0) / ((p : ℚ≥0) * p)) ^ 2 : ℚ≥0) : ℝ) ≤
          ((((U.card : ℚ≥0) / p) * E[B] : ℚ≥0) : ℝ) :=
      (NNRat.cast_le (K := ℝ)).mpr henergy'
    push_cast at hcoerced
    exact hcoerced
  have hPscaled : epsilon * ((A.card : ℝ) / p) ^ 2 ≤
      (P.card : ℝ) / ((p : ℝ) * p) := by
    calc
      epsilon * ((A.card : ℝ) / p) ^ 2 =
          (epsilon * (A.card : ℝ) ^ 2) / ((p : ℝ) * p) := by field_simp
      _ ≤ (P.card : ℝ) / ((p : ℝ) * p) := by gcongr
  have hUscaled : (U.card : ℝ) / p ≤ (A.card : ℝ) / p := by gcongr
  have hleft : (epsilon * ((A.card : ℝ) / p) ^ 2) ^ 2 ≤
      ((A.card : ℝ) / p) * E[B] := by
    calc
      _ ≤ ((P.card : ℝ) / ((p : ℝ) * p)) ^ 2 := by gcongr
      _ ≤ ((U.card : ℝ) / p) * E[B] := henergyR
      _ ≤ ((A.card : ℝ) / p) * E[B] := by
        gcongr
  have hdenpos : 0 < (A.card : ℝ) / p := div_pos hApos hp
  have hmul : ((A.card : ℝ) / p) *
        (epsilon ^ 2 * ((A.card : ℝ) / p) ^ 3) ≤
      ((A.card : ℝ) / p) * E[B] := by
    calc
      ((A.card : ℝ) / p) *
          (epsilon ^ 2 * ((A.card : ℝ) / p) ^ 3) =
        (epsilon * ((A.card : ℝ) / p) ^ 2) ^ 2 := by ring
      _ ≤ ((A.card : ℝ) / p) * E[B] := hleft
  simpa [B] using le_of_mul_le_mul_left hmul hdenpos

lemma exists_bsg_pluennecke_subset {p : ℕ} [NeZero p] {B : Finset (ZMod p)}
    (hB : B.Nonempty) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (henergy : epsilon ^ 2 * B.dens ^ 3 ≤ E[B])
    (C : ℕ) (hC : 2 ^ 14 * (((epsilon ^ 2)⁻¹) ^ 6) ≤ (C : ℝ)) :
    ∃ S ⊆ B, epsilon ^ 2 * (B.card : ℝ) ≤ 16 * S.card ∧
      (CyclicModel.pairDiff S).card ≤ C ^ 4 * S.card := by
  let K : ℝ := (epsilon ^ 2)⁻¹
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hKinv : K⁻¹ = epsilon ^ 2 := by
    dsimp [K]
    rw [inv_inv]
  obtain ⟨S, hSB, hsize, hsmall⟩ :=
    BSG_self' hK hB (by simpa [hKinv] using henergy)
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hsize' : epsilon ^ 2 * (B.card : ℝ) ≤ 16 * S.card := by
    simp only [Finset.dens, ZMod.card] at hsize
    push_cast at hsize
    rw [hKinv] at hsize
    have hraw : (2 ^ 4 : ℝ)⁻¹ * epsilon ^ 2 * B.card ≤ S.card := by
      apply (div_le_div_iff_of_pos_right hp).mp
      simpa only [div_eq_mul_inv, mul_assoc] using hsize
    norm_num at hraw ⊢
    nlinarith
  have hSposR : (0 : ℝ) < S.card := by
    have hBposR : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
    nlinarith [sq_pos_of_pos hepsilon]
  have hSne : S.Nonempty := card_pos.mp (by exact_mod_cast hSposR)
  have hdiffR : ((S - S).card : ℝ) ≤ C * S.card := by
    simp only [Finset.dens, ZMod.card] at hsmall
    push_cast at hsmall
    have hsmall' : ((S - S).card : ℝ) ≤
        (2 ^ 14 * K ^ 6) * S.card := by
      apply (div_le_div_iff_of_pos_right hp).mp
      simpa only [div_eq_mul_inv, mul_assoc] using hsmall
    calc
      ((S - S).card : ℝ) ≤ (2 ^ 14 * K ^ 6) * S.card := hsmall'
      _ ≤ C * S.card := by
        exact mul_le_mul_of_nonneg_right (by simpa [K] using hC) (by positivity)
  have hdiff : (S - S).card ≤ C * S.card := by exact_mod_cast hdiffR
  have hratio : ((S - S).card : ℚ≥0) / S.card ≤ C := by
    apply (div_le_iff₀ (by exact_mod_cast hSne.card_pos : (0 : ℚ≥0) < S.card)).mpr
    exact_mod_cast hdiff
  have hpl := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub hSne S 2 2
  have hpairNN : ((CyclicModel.pairDiff S).card : ℚ≥0) ≤
      (C : ℚ≥0) ^ 4 * S.card := by
    calc
      ((CyclicModel.pairDiff S).card : ℚ≥0) =
          ((2 • S - 2 • S).card : ℚ≥0) := by
            congr 2
            simp [CyclicModel.pairDiff, two_nsmul]
      _ ≤ (((S - S).card : ℚ≥0) / S.card) ^ (2 + 2) * S.card := hpl
      _ ≤ (C : ℚ≥0) ^ 4 * S.card := by norm_num; gcongr
  refine ⟨S, hSB, hsize', ?_⟩
  exact_mod_cast hpairNN

lemma exists_dense_cyclic_model {p : ℕ} [NeZero p] (hpprime : p.Prime)
    {A : Finset ℕ} (hAne : A.Nonempty) (hA : ∀ a ∈ A, a < p)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hmany : epsilon * (A.card : ℝ) ^ 2 ≤ apCount 3 A)
    (C : ℕ) (hC : 2 ^ 14 * (((epsilon ^ 2)⁻¹) ^ 6) ≤ (C : ℝ))
    (hp_large : 16 * (C ^ 4 * A.card) < p) :
    ∃ (S R : Finset (ZMod p)) (lambda : ZMod p),
      S ⊆ castFinset p A ∧ R ⊆ S ∧
      let D := CyclicModel.pairDiff S
      let q := 16 * (D.card + 1)
      CyclicModel.PairFreimanOn R (CyclicModel.modelMap q lambda) ∧
        epsilon ^ 2 * (A.card : ℝ) ≤
          32 * ((R.image (CyclicModel.modelMap q lambda)).card : ℝ) ∧
        q ≤ 16 * (C ^ 4 + 1) * A.card := by
  let B := castFinset p A
  have hBne : B.Nonempty := by
    obtain ⟨a, ha⟩ := hAne
    exact ⟨(a : ZMod p), mem_image.mpr ⟨a, ha, rfl⟩⟩
  have henergy := energy_lower_of_many_threeAPs hA hAne hepsilon.le hmany
  obtain ⟨S, hSB, hsize, hD⟩ :=
    exists_bsg_pluennecke_subset hBne hepsilon henergy C hC
  let D := CyclicModel.pairDiff S
  have hBcard : B.card = A.card := card_castFinset hA
  have hScard : S.card ≤ A.card := by
    calc S.card ≤ B.card := card_le_card hSB
      _ = A.card := hBcard
  have hDlarge : 16 * D.card < p := by
    have hD' : D.card ≤ C ^ 4 * A.card := by
      calc
        D.card ≤ C ^ 4 * S.card := by simpa [D] using hD
        _ ≤ C ^ 4 * A.card := by gcongr
    omega
  obtain ⟨lambda, R, hRS, hhalf, hfrei⟩ :=
    CyclicModel.exists_cyclic_model hpprime S (by simpa [D] using hDlarge)
  let q := 16 * (D.card + 1)
  let T := R.image (CyclicModel.modelMap q lambda)
  have hTcard : T.card = R.card := by
    apply card_image_of_injOn
    exact hfrei.injOn
  have hTlarge : epsilon ^ 2 * (A.card : ℝ) ≤ 32 * T.card := by
    have hhalfR : (S.card : ℝ) ≤ 2 * R.card := by exact_mod_cast hhalf
    rw [hBcard] at hsize
    rw [hTcard]
    nlinarith
  have hq : q ≤ 16 * (C ^ 4 + 1) * A.card := by
    have hAcard : 1 ≤ A.card := hAne.card_pos
    have hD' : D.card ≤ C ^ 4 * A.card := by
      calc
        D.card ≤ C ^ 4 * S.card := by simpa [D] using hD
        _ ≤ C ^ 4 * A.card := by gcongr
    dsimp [q]
    nlinarith
  refine ⟨S, R, lambda, hSB, hRS, ?_⟩
  dsimp only
  exact ⟨hfrei, by simpa [T] using hTlarge, by simpa [q] using hq⟩

lemma nat_add_eq_of_zmod_add_eq {p : ℕ} [NeZero p]
    {a b c d : ℕ} (ha : 2 * a < p) (hb : 2 * b < p)
    (hc : 2 * c < p) (hd : 2 * d < p)
    (h : (a : ZMod p) + b = (c : ZMod p) + d) : a + b = c + d := by
  have hab : a + b < p := by omega
  have hcd : c + d < p := by omega
  have hval := congrArg ZMod.val h
  simpa [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd,
    Nat.mod_eq_of_lt hab, Nat.mod_eq_of_lt hcd] using hval

lemma hasAP_four_of_model {p : ℕ} [NeZero p] {A : Finset ℕ}
    (hA2 : ∀ a ∈ A, 2 * a < p)
    {S R : Finset (ZMod p)} (hSB : S ⊆ castFinset p A) (hRS : R ⊆ S)
    {q : ℕ} (hq : 0 < q) {lambda : ZMod p}
    (hfrei : CyclicModel.PairFreimanOn R (CyclicModel.modelMap q lambda))
    (hfour : ContainsFourAP
      ((R.image (CyclicModel.modelMap q lambda)).image ZMod.val)) :
    HasAP 4 A := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let phi := CyclicModel.modelMap q lambda
  obtain ⟨x, e, he, hxe⟩ := hfour
  have hv (i : ℕ) (hi : i < 4) : x + i * e ∈ (R.image phi).image ZMod.val :=
    hxe i hi
  have hvlt (i : ℕ) (hi : i < 4) : x + i * e < q := by
    obtain ⟨t, -, ht⟩ := mem_image.mp (hv i hi)
    rw [← ht]
    exact t.val_lt
  have lift (i : ℕ) (hi : i < 4) :
      ∃ r ∈ R, phi r = ((x + i * e : ℕ) : ZMod q) := by
    obtain ⟨t, htT, htval⟩ := mem_image.mp (hv i hi)
    obtain ⟨r, hrR, hrt⟩ := mem_image.mp htT
    refine ⟨r, hrR, ?_⟩
    rw [hrt, ← htval]
    exact (ZMod.natCast_zmod_val t).symm
  obtain ⟨r0, hr0, hphi0⟩ := lift 0 (by omega)
  obtain ⟨r1, hr1, hphi1⟩ := lift 1 (by omega)
  obtain ⟨r2, hr2, hphi2⟩ := lift 2 (by omega)
  obtain ⟨r3, hr3, hphi3⟩ := lift 3 (by omega)
  have source (r : ZMod p) (hr : r ∈ R) : ∃ a ∈ A, (a : ZMod p) = r := by
    exact mem_image.mp (hSB (hRS hr))
  obtain ⟨a0, ha0, hcast0⟩ := source r0 hr0
  obtain ⟨a1, ha1, hcast1⟩ := source r1 hr1
  obtain ⟨a2, ha2, hcast2⟩ := source r2 hr2
  obtain ⟨a3, ha3, hcast3⟩ := source r3 hr3
  have ht0 : phi r0 = (x : ZMod q) := by simpa using hphi0
  have ht1 : phi r1 = ((x + e : ℕ) : ZMod q) := by simpa using hphi1
  have ht2 : phi r2 = ((x + 2 * e : ℕ) : ZMod q) := by simpa using hphi2
  have ht3 : phi r3 = ((x + 3 * e : ℕ) : ZMod q) := by simpa using hphi3
  have htarget02 : phi r0 + phi r2 = phi r1 + phi r1 := by
    rw [ht0, ht1, ht2]
    push_cast
    ring
  have htarget13 : phi r1 + phi r3 = phi r2 + phi r2 := by
    rw [ht1, ht2, ht3]
    push_cast
    ring
  have hsource02 : r0 + r2 = r1 + r1 := (hfrei hr0 hr2 hr1 hr1).mp htarget02
  have hsource13 : r1 + r3 = r2 + r2 := (hfrei hr1 hr3 hr2 hr2).mp htarget13
  have hnat02 : a0 + a2 = a1 + a1 := by
    apply nat_add_eq_of_zmod_add_eq (hA2 a0 ha0) (hA2 a2 ha2)
      (hA2 a1 ha1) (hA2 a1 ha1)
    simpa [hcast0, hcast1, hcast2] using hsource02
  have hnat13 : a1 + a3 = a2 + a2 := by
    apply nat_add_eq_of_zmod_add_eq (hA2 a1 ha1) (hA2 a3 ha3)
      (hA2 a2 ha2) (hA2 a2 ha2)
    simpa [hcast1, hcast2, hcast3] using hsource13
  have ha01 : a0 ≠ a1 := by
    intro hae
    have hr01 : r0 = r1 := by
      rw [← hcast0, ← hcast1, hae]
    have hcastEq : (x : ZMod q) = ((x + e : ℕ) : ZMod q) := by
      rw [← ht0, ← ht1, hr01]
    have hval := congrArg ZMod.val hcastEq
    have hxq : x < q := by simpa using hvlt 0 (by omega)
    have hxeq : x + e < q := by simpa using hvlt 1 (by omega)
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hxq,
      Nat.mod_eq_of_lt hxeq] at hval
    omega
  rw [hasAP_iff (by omega)]
  rcases lt_or_gt_of_ne ha01 with hinc | hdec
  · refine ⟨a0, ha0, a1, ha1, hinc, ?_⟩
    intro i hi
    interval_cases i
    · simpa using ha0
    · convert ha1 using 1 <;> omega
    · convert ha2 using 1 <;> omega
    · convert ha3 using 1 <;> omega
  · refine ⟨a3, ha3, a2, ha2, ?_, ?_⟩
    · omega
    · intro i hi
      interval_cases i
      · simpa using ha3
      · convert ha2 using 1 <;> omega
      · convert ha1 using 1 <;> omega
      · convert ha0 using 1 <;> omega

lemma eventually_many_threeAPs_force_four (hSz : FiniteSzemerediFour)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ, A.card = n →
      epsilon * (n : ℝ) ^ 2 ≤ apCount 3 A → HasAP 4 A := by
  obtain ⟨C0 : ℕ, hC0⟩ := exists_nat_ge
    (2 ^ 14 * (((epsilon ^ 2)⁻¹) ^ 6))
  let C := C0 + 1
  have hC : 2 ^ 14 * (((epsilon ^ 2)⁻¹) ^ 6) ≤ (C : ℝ) := by
    exact hC0.trans (by norm_num [C])
  let delta : ℝ := epsilon ^ 2 / (1024 * (C ^ 4 + 1))
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨N, hN⟩ := hSz delta hdelta
  obtain ⟨M : ℕ, hM⟩ : ∃ M : ℕ, (32 * N : ℝ) < epsilon ^ 2 * M := by
    obtain ⟨M : ℕ, hM⟩ := exists_nat_gt ((32 * N : ℝ) / epsilon ^ 2)
    refine ⟨M, ?_⟩
    have he2 : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
    have := mul_lt_mul_of_pos_right hM he2
    field_simp at this
    nlinarith
  filter_upwards [eventually_ge_atTop (max M 1)] with n hn A hAn hmany
  have hnM : M ≤ n := le_trans (le_max_left _ _) hn
  have hnpos : 0 < n := lt_of_lt_of_le (by omega) (le_trans (le_max_right _ _) hn)
  have hnlarge : (32 * N : ℝ) < epsilon ^ 2 * n := by
    calc
      (32 * N : ℝ) < epsilon ^ 2 * M := hM
      _ ≤ epsilon ^ 2 * n := by gcongr
  let bound := max (2 * A.sup id + 1) (16 * (C ^ 4 * n) + 1)
  obtain ⟨p, hpbound, hpprime⟩ := Nat.exists_infinite_primes bound
  have hp0 : 0 < p := hpprime.pos
  letI : NeZero p := ⟨hpprime.ne_zero⟩
  have hA2 : ∀ a ∈ A, 2 * a < p := by
    intro a ha
    have hasup : a ≤ A.sup id := by simpa using Finset.le_sup (f := id) ha
    have hleft : 2 * A.sup id + 1 ≤ bound := le_max_left _ _
    omega
  have hA : ∀ a ∈ A, a < p := by
    intro a ha
    have := hA2 a ha
    omega
  have hp_large : 16 * (C ^ 4 * A.card) < p := by
    rw [hAn]
    have hright : 16 * (C ^ 4 * n) + 1 ≤ bound := le_max_right _ _
    omega
  have hAne : A.Nonempty := card_pos.mp (by omega)
  obtain ⟨S, R, lambda, hSB, hRS, hfrei, hTlarge, hqbound⟩ :=
    exists_dense_cyclic_model hpprime hAne hA hepsilon
      (by simpa [hAn] using hmany) C hC hp_large
  let D := CyclicModel.pairDiff S
  let q := 16 * (D.card + 1)
  let phi := CyclicModel.modelMap q lambda
  let T := R.image phi
  let V := T.image ZMod.val
  have hqpos : 0 < q := by simp [q]
  letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  have hTcard_le : T.card ≤ q := by
    calc T.card ≤ (Finset.univ : Finset (ZMod q)).card := card_le_univ _
      _ = q := by simp [ZMod.card]
  have hVcard : V.card = T.card := by
    apply card_image_of_injOn
    exact (ZMod.val_injective q).injOn
  have hVsub : V ⊆ range q := by
    intro v hv
    obtain ⟨t, -, rfl⟩ := mem_image.mp hv
    exact mem_range.mpr t.val_lt
  have hNq : N ≤ q := by
    have hlarge : epsilon ^ 2 * (n : ℝ) ≤ 32 * T.card := by
      simpa [hAn, T, phi, q, D] using hTlarge
    have hTq : (T.card : ℝ) ≤ q := by exact_mod_cast hTcard_le
    have : (N : ℝ) < q := by nlinarith
    exact_mod_cast this.le
  have hdeltaV : delta * (q : ℝ) ≤ V.card := by
    rw [hVcard]
    have hqR : (q : ℝ) ≤ 16 * (C ^ 4 + 1) * n := by
      have hqNat : q ≤ 16 * (C ^ 4 + 1) * n := by
        simpa [hAn, q, D] using hqbound
      exact_mod_cast hqNat
    have hlarge : epsilon ^ 2 * (n : ℝ) ≤ 32 * T.card := by
      simpa [hAn, T, phi, q, D] using hTlarge
    dsimp [delta]
    have hden : (0 : ℝ) < 1024 * (C ^ 4 + 1) := by positivity
    have hz : (0 : ℝ) ≤ C ^ 4 + 1 := by positivity
    have htarget : epsilon ^ 2 * (q : ℝ) ≤
        (T.card : ℝ) * (1024 * (C ^ 4 + 1)) := by
      calc
        epsilon ^ 2 * (q : ℝ) ≤
            epsilon ^ 2 * (16 * (C ^ 4 + 1) * n) := by gcongr
        _ = 16 * (C ^ 4 + 1) * (epsilon ^ 2 * n) := by ring
        _ ≤ 16 * (C ^ 4 + 1) * (32 * T.card) := by gcongr
        _ ≤ (T.card : ℝ) * (1024 * (C ^ 4 + 1)) := by
          have hTnonneg : (0 : ℝ) ≤ T.card := by positivity
          nlinarith [mul_nonneg hz hTnonneg]
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hden).mpr htarget
  have hfour := hN q hNq V hVsub hdeltaV
  exact hasAP_four_of_model hA2 hSB hRS hqpos
    (by simpa [phi, q, D] using hfrei) (by simpa [V, T, phi] using hfour)

lemma eventually_F_three_four_le_ceil (hSz : FiniteSzemerediFour)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      F 3 n 4 ≤ ⌈epsilon * (n : ℝ) ^ 2⌉₊ := by
  filter_upwards [eventually_many_threeAPs_force_four hSz hepsilon] with n hn
  apply F_minimal
  intro A hcard hcount
  apply hn A hcard
  calc
    epsilon * (n : ℝ) ^ 2 ≤ (⌈epsilon * (n : ℝ) ^ 2⌉₊ : ℝ) :=
      Nat.le_ceil _
    _ ≤ apCount 3 A := by exact_mod_cast hcount

theorem isLittleO_F_three_four_of_finiteSzemeredi (hSz : FiniteSzemerediFour) :
    (fun n : ℕ ↦ (F 3 n 4 : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ 2) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro c hc
  let epsilon : ℝ := c / 4
  have hepsilon : 0 < epsilon := div_pos hc (by norm_num)
  obtain ⟨M : ℕ, hM⟩ := exists_nat_gt (4 / (3 * c))
  filter_upwards [eventually_F_three_four_le_ceil hSz hepsilon,
    eventually_ge_atTop (max M 1)] with n hF hn
  have hnM : M ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hmargin : 1 < 3 * c / 4 * (n : ℝ) ^ 2 := by
    have h3c : 0 < 3 * c := mul_pos (by norm_num) hc
    have hscaled := mul_lt_mul_of_pos_right hM h3c
    have hMn : (M : ℝ) ≤ n := by exact_mod_cast hnM
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have hscaled' : (4 : ℝ) < (M : ℝ) * (3 * c) := by
      calc
        (4 : ℝ) = 4 / (3 * c) * (3 * c) := by field_simp
        _ < (M : ℝ) * (3 * c) := hscaled
    have hMn' : (M : ℝ) * (3 * c) ≤ (n : ℝ) ^ 2 * (3 * c) :=
      mul_le_mul_of_nonneg_right (hMn.trans hnn) h3c.le
    nlinarith
  have hceil : (⌈epsilon * (n : ℝ) ^ 2⌉₊ : ℝ) <
      epsilon * (n : ℝ) ^ 2 + 1 := by
    exact Nat.ceil_lt_add_one (mul_nonneg hepsilon.le (sq_nonneg _))
  have hbound : (F 3 n 4 : ℝ) ≤ c * (n : ℝ) ^ 2 := by
    have hF' : (F 3 n 4 : ℝ) ≤ ⌈epsilon * (n : ℝ) ^ 2⌉₊ := by
      exact_mod_cast hF
    dsimp [epsilon] at hceil
    nlinarith
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ F 3 n 4),
    abs_of_nonneg (sq_nonneg (n : ℝ))] using hbound


end UpperBound

/-- The affirmative answer to the first question in Erdős Problem 179:
the forcing threshold for three-term progressions to force a four-term
progression is little-o of the trivial quadratic scale. -/
theorem isLittleO_F_three_four :
    (fun n : ℕ ↦ (F 3 n 4 : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ 2) :=
  UpperBound.isLittleO_F_three_four_of_finiteSzemeredi
    SzemerediFour.finiteSzemerediFour

/-- Erdős Problem 179: the four-term forcing threshold is little-o of
the quadratic scale, while for every fixed target length greater than
three its logarithmic exponent tends to two. -/
theorem erdos_179 :
    (fun n : ℕ ↦ (F 3 n 4 : ℝ)) =o[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ 2) ∧
      ∀ k : ℕ, 3 < k →
        Tendsto (fun n : ℕ ↦ Real.log (F 3 n k) / Real.log n)
          atTop (𝓝 2) := by
  refine ⟨isLittleO_F_three_four, ?_⟩
  intro k hk
  exact tendsto_log_F_three (by omega)

#print axioms erdos_179

end Erdos179
