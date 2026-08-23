/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 825.
https://www.erdosproblems.com/forum/thread/825

Informal authors:
- Daniel Larsen

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos825.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/825.lean
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos469
import UnitFractions.Fourier
import Util.ListSorted

/-!
# Erdős Problem 825

Benkoski and Erdős asked whether sufficiently large abundancy forces an
integer to be a sum of distinct proper divisors.  Larsen proved this by a
rough-number reduction, a controlled greedy construction, and a weighted
unit-fraction circle method.

The detailed mathematical proof and its Leanization map are in `tex/825.tex`.
-/

open scoped ArithmeticFunction.sigma BigOperators List

namespace Erdos825

noncomputable section

/-- The exact proper-divisor conclusion occurring in the formal conjecture. -/
def Pseudoperfect (n : ℕ) : Prop :=
  ∃ s ⊆ n.properDivisors, n = s.sum id

lemma pseudoperfect_iff_isSumDivisors {n : ℕ} :
    Pseudoperfect n ↔ n.IsSumDivisors := by
  constructor
  · rintro ⟨s, hs, hsum⟩
    exact ⟨s, hs, hsum.symm⟩
  · rintro ⟨s, hs, hsum⟩
    exact ⟨s, hs, hsum.symm⟩

/-- Pseudoperfectness is inherited by positive multiples. -/
lemma Pseudoperfect.of_dvd {m n : ℕ} (hm : Pseudoperfect m)
    (hmn : m ∣ n) (hn : 0 < n) : Pseudoperfect n := by
  obtain ⟨k, rfl⟩ := hmn
  have hk : 0 < k := by
    by_contra hk
    simp only [Nat.not_lt, Nat.le_zero] at hk
    subst k
    simp at hn
  obtain ⟨D, hD, hsum⟩ := hm
  refine ⟨D.image (fun d => k * d), ?_, ?_⟩
  · intro x hx
    obtain ⟨d, hdD, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hdvd, hdlt⟩ := Nat.mem_properDivisors.mp (hD hdD)
    apply Nat.mem_properDivisors.mpr
    constructor
    · simpa [Nat.mul_comm] using Nat.mul_dvd_mul_left k hdvd
    · simpa [Nat.mul_comm] using (Nat.mul_lt_mul_left hk).mpr hdlt
  · rw [Finset.sum_image]
    · simp only [id_eq]
      have hsum' : m = ∑ d ∈ D, d := by simpa using hsum
      rw [← Finset.mul_sum, ← hsum', Nat.mul_comm]
    · intro a ha b hb hab
      exact Nat.eq_of_mul_eq_mul_left hk hab

/-- Positive divisors other than `1`; these are the denominators in the
unit-fraction form of pseudoperfectness. -/
def nontrivialDivisors (n : ℕ) : Finset ℕ := n.divisors.erase 1

lemma complementDivisor_injOn {n : ℕ} (hn : 0 < n) :
    Set.InjOn (fun d : ℕ => n / d) {d : ℕ | d ∣ n} := by
  intro a ha b hb hab
  change n / a = n / b at hab
  have hqpos : 0 < n / a := Nat.div_pos (Nat.le_of_dvd hn ha) (Nat.pos_of_dvd_of_pos ha hn)
  apply Nat.eq_of_mul_eq_mul_left hqpos
  calc
    (n / a) * a = n := Nat.div_mul_cancel ha
    _ = (n / b) * b := (Nat.div_mul_cancel hb).symm
    _ = (n / a) * b := by rw [← hab]

/-- A reciprocal representation by nontrivial divisors gives the required
proper-divisor representation after applying `d ↦ n / d`. -/
lemma Pseudoperfect.of_reciprocal {n : ℕ} (hn : 0 < n) {A : Finset ℕ}
    (hA : A ⊆ nontrivialDivisors n) (hrec : UnitFractions.rec_sum A = 1) :
    Pseudoperfect n := by
  have hdiv : ∀ d ∈ A, d ∣ n := by
    intro d hd
    exact (Nat.mem_divisors.mp (Finset.mem_of_mem_erase (hA hd))).1
  have hinj : Set.InjOn (fun d : ℕ => n / d) A := by
    intro a ha b hb
    exact complementDivisor_injOn hn (hdiv a ha) (hdiv b hb)
  refine ⟨A.image (fun d => n / d), ?_, ?_⟩
  · intro q hq
    obtain ⟨d, hdA, rfl⟩ := Finset.mem_image.mp hq
    have hdDiv := hdiv d hdA
    have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hdDiv hn
    have hdNeOne : d ≠ 1 := Finset.ne_of_mem_erase (hA hdA)
    have hdOne : 1 < d := lt_of_le_of_ne hdPos hdNeOne.symm
    exact Nat.mem_properDivisors.mpr
      ⟨Nat.div_dvd_of_dvd hdDiv, Nat.div_lt_self hn hdOne⟩
  · rw [Finset.sum_image hinj]
    have hcast :
        ((∑ d ∈ A, n / d : ℕ) : ℚ) = n * UnitFractions.rec_sum A := by
      rw [UnitFractions.rec_sum, Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.cast_div (hdiv d hd) (by exact_mod_cast (Nat.pos_of_dvd_of_pos (hdiv d hd) hn).ne')]
      ring
    rw [hrec, mul_one] at hcast
    exact_mod_cast hcast.symm

/-! ## Translated subset sums of lists

Hisamoto's dense-block argument repeatedly replaces disjoint pairs by their
difference.  A list, rather than a finset, records the multiplicities of the
virtual summands produced by those replacements. -/

/-- `ListSubsetSum A x` means that `x` is the sum of a sublist of `A`.  Thus
occurrences, rather than values, are the available summands. -/
def ListSubsetSum (A : List ℕ) (x : ℕ) : Prop :=
  ∃ T : List ℕ, T.Sublist A ∧ T.sum = x

/-- Every subset sum of `B`, after one fixed translation, is a subset sum of
`A`.  This is Hisamoto's multiset compression relation. -/
def RepresentsTranslate (A B : List ℕ) : Prop :=
  ∃ e : ℕ, ∀ x : ℕ, ListSubsetSum B x → ListSubsetSum A (e + x)

lemma ListSubsetSum.zero (A : List ℕ) : ListSubsetSum A 0 := by
  exact ⟨[], List.nil_sublist _, rfl⟩

lemma ListSubsetSum.self (A : List ℕ) : ListSubsetSum A A.sum := by
  exact ⟨A, .refl _, rfl⟩

lemma ListSubsetSum.append {A B : List ℕ} {x y : ℕ}
    (hx : ListSubsetSum A x) (hy : ListSubsetSum B y) :
    ListSubsetSum (A ++ B) (x + y) := by
  obtain ⟨S, hSA, rfl⟩ := hx
  obtain ⟨T, hTB, rfl⟩ := hy
  exact ⟨S ++ T, hSA.append hTB, by simp⟩

lemma ListSubsetSum.of_append {A B : List ℕ} {x : ℕ}
    (hx : ListSubsetSum (A ++ B) x) :
    ∃ y z, ListSubsetSum A y ∧ ListSubsetSum B z ∧ x = y + z := by
  obtain ⟨T, hT, rfl⟩ := hx
  rw [List.sublist_append_iff] at hT
  obtain ⟨S, U, rfl, hSA, hUB⟩ := hT
  exact ⟨S.sum, U.sum, ⟨S, hSA, rfl⟩, ⟨U, hUB, rfl⟩, by simp⟩

lemma ListSubsetSum.perm {A B : List ℕ} (hAB : A.Perm B) {x : ℕ}
    (hx : ListSubsetSum A x) : ListSubsetSum B x := by
  obtain ⟨T, hTA, hsum⟩ := hx
  obtain ⟨U, hUT, hUB⟩ := List.exists_perm_sublist hTA hAB
  exact ⟨U, hUB, hUT.sum_nat.trans hsum⟩

lemma listSubsetSum_perm_iff {A B : List ℕ} (hAB : A.Perm B) {x : ℕ} :
    ListSubsetSum A x ↔ ListSubsetSum B x := by
  exact ⟨ListSubsetSum.perm hAB, ListSubsetSum.perm hAB.symm⟩

lemma RepresentsTranslate.refl (A : List ℕ) : RepresentsTranslate A A := by
  exact ⟨0, by simpa using fun x (hx : ListSubsetSum A x) => hx⟩

lemma RepresentsTranslate.to_nil (A : List ℕ) : RepresentsTranslate A [] := by
  exact ⟨A.sum, fun x hx => by
    have hx0 : x = 0 := by
      obtain ⟨T, hT, hsum⟩ := hx
      have : T = [] := List.sublist_nil.mp hT
      subst T
      simpa using hsum.symm
    subst x
    simpa using ListSubsetSum.self A⟩

lemma RepresentsTranslate.of_sublist {A B : List ℕ} (hBA : B.Sublist A) :
    RepresentsTranslate A B := by
  refine ⟨0, ?_⟩
  intro x hx
  obtain ⟨T, hTB, hsum⟩ := hx
  exact ⟨T, hTB.trans hBA, by simpa using hsum⟩

/-- A duplicate-free list contained elementwise in another list can be
selected after permuting the latter. -/
lemma RepresentsTranslate.of_nodup_subset {A B : List ℕ}
    (hB : B.Nodup) (hBA : ∀ b ∈ B, b ∈ A) :
    RepresentsTranslate A B := by
  have hsubperm : B.Subperm A := hB.subperm hBA
  rw [List.subperm_iff] at hsubperm
  obtain ⟨A', hperm, hsub⟩ := hsubperm
  obtain ⟨e, he⟩ := RepresentsTranslate.of_sublist hsub
  exact ⟨e, fun z hz => (he z hz).perm hperm⟩

lemma RepresentsTranslate.trans {A B C : List ℕ}
    (hAB : RepresentsTranslate A B) (hBC : RepresentsTranslate B C) :
    RepresentsTranslate A C := by
  obtain ⟨e, he⟩ := hAB
  obtain ⟨f, hf⟩ := hBC
  refine ⟨e + f, ?_⟩
  intro x hx
  simpa [Nat.add_assoc] using he (f + x) (hf x hx)

lemma RepresentsTranslate.perm_left {A A' B : List ℕ}
    (hAA' : A.Perm A') (hAB : RepresentsTranslate A B) :
    RepresentsTranslate A' B := by
  obtain ⟨e, he⟩ := hAB
  exact ⟨e, fun x hx => (he x hx).perm hAA'⟩

lemma RepresentsTranslate.perm_right {A B B' : List ℕ}
    (hBB' : B.Perm B') (hAB : RepresentsTranslate A B) :
    RepresentsTranslate A B' := by
  obtain ⟨e, he⟩ := hAB
  exact ⟨e, fun x hx => he x (hx.perm hBB'.symm)⟩

lemma RepresentsTranslate.append_right {A B : List ℕ}
    (hAB : RepresentsTranslate A B) (C : List ℕ) :
    RepresentsTranslate (A ++ C) (B ++ C) := by
  obtain ⟨e, he⟩ := hAB
  refine ⟨e, ?_⟩
  intro x hx
  obtain ⟨y, z, hy, hz, rfl⟩ := hx.of_append
  simpa [Nat.add_assoc] using (he y hy).append hz

lemma RepresentsTranslate.append_left (C : List ℕ) {A B : List ℕ}
    (hAB : RepresentsTranslate A B) :
    RepresentsTranslate (C ++ A) (C ++ B) := by
  obtain ⟨e, he⟩ := hAB
  refine ⟨e, ?_⟩
  intro x hx
  obtain ⟨y, z, hy, hz, rfl⟩ := hx.of_append
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    hy.append (he z hz)

lemma RepresentsTranslate.append {A B C D : List ℕ}
    (hAB : RepresentsTranslate A B) (hCD : RepresentsTranslate C D) :
    RepresentsTranslate (A ++ C) (B ++ D) := by
  exact (hAB.append_right C).trans (hCD.append_left B)

/-- The elementary pair-difference compression
`{a,b} ↝ a + {0,b-a}`. -/
lemma representsTranslate_pair_diff {a b : ℕ} (hab : a ≤ b) :
    RepresentsTranslate [a, b] [b - a] := by
  refine ⟨a, ?_⟩
  intro x hx
  obtain ⟨T, hT, rfl⟩ := hx
  have hcases : T = [] ∨ T = [b - a] := by
    exact List.sublist_singleton.mp hT
  rcases hcases with rfl | rfl
  · exact ⟨[a], by simp, by simp⟩
  · exact ⟨[b], by simp, by simp [Nat.add_sub_of_le hab]⟩

/-- The pair-merge compression `{a,b} ↝ {a+b}`. -/
lemma representsTranslate_pair_add (a b : ℕ) :
    RepresentsTranslate [a, b] [a + b] := by
  refine ⟨0, ?_⟩
  intro x hx
  obtain ⟨T, hT, rfl⟩ := hx
  have hcases : T = [] ∨ T = [a + b] := by
    exact List.sublist_singleton.mp hT
  rcases hcases with rfl | rfl
  · exact ⟨[], by simp, by simp⟩
  · exact ⟨[a, b], by simp, by simp⟩

lemma representsTranslate_sum (A : List ℕ) :
    RepresentsTranslate A [A.sum] := by
  refine ⟨0, ?_⟩
  intro x hx
  obtain ⟨T, hT, rfl⟩ := hx
  rcases List.sublist_singleton.mp hT with rfl | rfl
  · exact ListSubsetSum.zero A
  · simpa using ListSubsetSum.self A

/-- Consecutive chunks with prescribed lengths. -/
def chunksBy : List ℕ → List α → List (List α)
  | [], _ => []
  | u :: us, A => A.take u :: chunksBy us (A.drop u)

lemma flatten_chunksBy_sublist (us : List ℕ) (A : List α) :
    (chunksBy us A).flatten.Sublist A := by
  induction us generalizing A with
  | nil => simp [chunksBy]
  | cons u us ih =>
      simp only [chunksBy, List.flatten_cons]
      have htail := ih (A.drop u)
      simpa using (List.Sublist.refl (A.take u)).append htail

lemma chunksBy_represents_sums (us : List ℕ) (A : List ℕ) :
    RepresentsTranslate (chunksBy us A).flatten ((chunksBy us A).map List.sum) := by
  induction us generalizing A with
  | nil => exact RepresentsTranslate.refl []
  | cons u us ih =>
      simp only [chunksBy, List.flatten_cons, List.map_cons]
      exact (representsTranslate_sum (A.take u)).append (ih (A.drop u))

lemma RepresentsTranslate.chunkSums (us : List ℕ) (A : List ℕ) :
    RepresentsTranslate A ((chunksBy us A).map List.sum) := by
  exact (RepresentsTranslate.of_sublist (flatten_chunksBy_sublist us A)).trans
    (chunksBy_represents_sums us A)

lemma map_length_chunksBy {us : List ℕ} {A : List α} (h : us.sum ≤ A.length) :
    (chunksBy us A).map List.length = us := by
  induction us generalizing A with
  | nil => simp [chunksBy]
  | cons u us ih =>
      have hu : u ≤ A.length := le_trans (by omega : u ≤ u + us.sum) h
      have htail : us.sum ≤ (A.drop u).length := by
        have h' : u + us.sum ≤ A.length := by simpa using h
        have h'' : us.sum + u ≤ A.length := by omega
        simpa [List.length_drop] using Nat.le_sub_of_add_le h''
      simp [chunksBy, List.length_take, min_eq_left hu, ih htail]

lemma mem_chunk_of_mem_chunksBy {us : List ℕ} {A : List α} {C : List α}
    (hC : C ∈ chunksBy us A) : ∀ a ∈ C, a ∈ A := by
  induction us generalizing A with
  | nil => simp [chunksBy] at hC
  | cons u us ih =>
      simp only [chunksBy, List.mem_cons] at hC
      rcases hC with rfl | hC
      · intro a ha
        exact List.mem_of_mem_take ha
      · intro a ha
        exact List.mem_of_mem_drop (ih hC a ha)

lemma sum_le_length_mul_of_bound {A : List ℕ} {B : ℕ}
    (hA : ∀ a ∈ A, a ≤ B) : A.sum ≤ A.length * B := by
  induction A with
  | nil => simp
  | cons a A ih =>
      have ha : a ≤ B := hA a (by simp)
      have htail : A.sum ≤ A.length * B := ih fun b hb => hA b (by simp [hb])
      simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
      omega

lemma sum_mod_eq_length_mul_mod {A : List ℕ} {μ w : ℕ}
    (hA : ∀ a ∈ A, a % μ = w) :
    A.sum % μ = (A.length * w) % μ := by
  induction A with
  | nil => simp
  | cons a A ih =>
      rw [List.sum_cons, List.length_cons, Nat.succ_mul,
        Nat.add_mod, hA a (by simp), ih (fun b hb => hA b (by simp [hb]))]
      calc
        (w + A.length * w % μ) % μ = (A.length * w % μ + w) % μ := by
          rw [Nat.add_comm]
        _ = (A.length * w + w) % μ := Nat.mod_add_mod _ _ _

lemma chunk_sum_mod {us : List ℕ} {A : List ℕ} {μ w : ℕ}
    (hA : ∀ a ∈ A, a % μ = w) {i : ℕ} (hi : i < (chunksBy us A).length) :
    (chunksBy us A)[i].sum % μ =
      ((chunksBy us A)[i].length * w) % μ := by
  apply sum_mod_eq_length_mul_mod
  intro a ha
  exact hA a (mem_chunk_of_mem_chunksBy (List.getElem_mem hi) a ha)

/-- Differences of the fixed disjoint adjacent pairs of a list. -/
def adjacentPairDiffs : List ℕ → List ℕ
  | a :: b :: rest => (b - a) :: adjacentPairDiffs rest
  | _ => []

lemma adjacentPairDiffs_represents {A : List ℕ} (hA : A.Sorted (· ≤ ·)) :
    RepresentsTranslate A (adjacentPairDiffs A) := by
  induction A using List.twoStepInduction with
  | nil => exact RepresentsTranslate.to_nil []
  | singleton a => exact RepresentsTranslate.to_nil [a]
  | cons_cons a b rest ih _ =>
      have hab : a ≤ b := (List.pairwise_cons.mp hA).1 b (by simp)
      have hrest : rest.Sorted (· ≤ ·) := hA.tail.tail
      change RepresentsTranslate ([a, b] ++ rest)
        ([b - a] ++ adjacentPairDiffs rest)
      exact (representsTranslate_pair_diff hab).append (ih hrest)

/-- All consecutive gaps, used to bound the mass of the disjoint gaps. -/
def consecutiveGaps : List ℕ → List ℕ
  | a :: b :: rest => (b - a) :: consecutiveGaps (b :: rest)
  | _ => []

lemma adjacentPairDiffs_sublist_consecutiveGaps (A : List ℕ) :
    (adjacentPairDiffs A).Sublist (consecutiveGaps A) := by
  induction A using List.twoStepInduction with
  | nil => simp [adjacentPairDiffs, consecutiveGaps]
  | singleton a => simp [adjacentPairDiffs, consecutiveGaps]
  | cons_cons a b rest ih _ =>
      cases rest with
      | nil => simp [adjacentPairDiffs, consecutiveGaps]
      | cons c rest =>
          simp only [adjacentPairDiffs, consecutiveGaps]
          exact (ih.cons (c - b)).cons_cons (b - a)

lemma sum_consecutiveGaps_add_head {a : ℕ} {A : List ℕ}
    (hA : (a :: A).Sorted (· ≤ ·)) :
    (consecutiveGaps (a :: A)).sum + a = (a :: A).getLast (by simp) := by
  induction A generalizing a with
  | nil => simp [consecutiveGaps]
  | cons b A ih =>
      have hab : a ≤ b := (List.pairwise_cons.mp hA).1 b (by simp)
      have htail : (b :: A).Sorted (· ≤ ·) := hA.tail
      have hih := ih htail
      simp only [consecutiveGaps, List.sum_cons]
      rw [List.getLast_cons (by simp : b :: A ≠ [])]
      omega

lemma sum_adjacentPairDiffs_le_span {a : ℕ} {A : List ℕ}
    (hA : (a :: A).Sorted (· ≤ ·)) :
    (adjacentPairDiffs (a :: A)).sum ≤ (a :: A).getLast (by simp) - a := by
  have hsub := adjacentPairDiffs_sublist_consecutiveGaps (a :: A)
  have hsum : (adjacentPairDiffs (a :: A)).sum ≤
      (consecutiveGaps (a :: A)).sum :=
    List.Sublist.sum_le_sum hsub (fun _ _ => Nat.zero_le _)
  have htel := sum_consecutiveGaps_add_head hA
  omega

lemma length_adjacentPairDiffs (A : List ℕ) :
    (adjacentPairDiffs A).length = A.length / 2 := by
  induction A using List.twoStepInduction with
  | nil => simp [adjacentPairDiffs]
  | singleton a => simp [adjacentPairDiffs]
  | cons_cons a b rest ih _ =>
      simp only [adjacentPairDiffs, List.length_cons, ih]
      omega

lemma mul_countP_le_sum (H : ℕ) (D : List ℕ) :
    H * D.countP (fun d => H ≤ d) ≤ D.sum := by
  induction D with
  | nil => simp
  | cons d D ih =>
      by_cases hd : H ≤ d
      · rw [List.countP_cons_of_pos (by simpa using hd), List.sum_cons, Nat.mul_add]
        simpa [Nat.add_comm] using Nat.add_le_add hd ih
      · rw [List.countP_cons_of_neg (by simpa using hd), List.sum_cons]
        exact ih.trans (Nat.le_add_left _ _)

lemma many_lt_of_sum_le {D : List ℕ} {H q x : ℕ} (hH : 0 < H)
    (hsum : D.sum ≤ x) (hroom : x + H * q ≤ H * D.length) :
    q ≤ (D.filter fun d => d < H).length := by
  let large := D.countP (fun d => H ≤ d)
  let small := D.countP (fun d => ¬H ≤ d)
  have hlarge : H * large ≤ x := (mul_countP_le_sum H D).trans hsum
  have hmul : H * (large + q) ≤ H * D.length := by
    rw [Nat.mul_add]
    exact (Nat.add_le_add_right hlarge _).trans hroom
  have hcancel : large + q ≤ D.length :=
    Nat.le_of_mul_le_mul_left hmul hH
  have hparts : D.length = large + small := by
    simpa [large, small] using List.length_eq_countP_add_countP (fun d => H ≤ d)
  have hq : q ≤ small := by omega
  simpa [small, List.countP_eq_length_filter] using hq

lemma exists_frequent_lt {D : List ℕ} {H q : ℕ} (hH : 0 < H)
    (hcard : H * q ≤ (D.filter fun d => d < H).length) :
    ∃ μ : ℕ, μ < H ∧ q ≤ D.count μ := by
  let small := D.filter fun d => d < H
  let s : Finset ℕ := small.toFinset
  have hsmap : ∀ a ∈ s, a ∈ Finset.range H := by
    intro a ha
    have ha' : a ∈ small := by simpa [s] using ha
    exact Finset.mem_range.mpr (of_decide_eq_true (List.mem_filter.mp ha').2)
  have ht : (Finset.range H).Nonempty := ⟨0, Finset.mem_range.mpr hH⟩
  have htotal :
      (Finset.range H).card • q ≤ ∑ a ∈ s, (small : Multiset ℕ).count a := by
    calc
      (Finset.range H).card • q = H * q := by simp
      _ ≤ small.length := by simpa [small] using hcard
      _ = ∑ a ∈ s, (small : Multiset ℕ).count a := by
        simpa [s] using (Multiset.toFinset_sum_count_eq (small : Multiset ℕ)).symm
  obtain ⟨μ, hμ, hfreq⟩ :=
    Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
      (M := ℕ) (s := s) (t := Finset.range H) (f := fun a : ℕ => a)
      (w := fun a : ℕ => (small : Multiset ℕ).count a) (b := q)
      hsmap ht htotal
  refine ⟨μ, Finset.mem_range.mp hμ, ?_⟩
  have hsmallCountM : q ≤ (small : Multiset ℕ).count μ := by
    have hsumEq :
        (∑ x ∈ s with x = μ, (small : Multiset ℕ).count x) =
          (small : Multiset ℕ).count μ := by
      classical
      rw [Finset.sum_filter, Finset.sum_eq_single μ]
      · simp
      · intro b hb hne
        simp [hne]
      · intro hμs
        have hμsmall : μ ∉ small := by simpa [s] using hμs
        simp [hμsmall]
    exact hfreq.trans_eq hsumEq
  have hsmallCount : q ≤ small.count μ := by simpa using hsmallCountM
  exact hsmallCount.trans (List.filter_sublist.count_le μ)

lemma two_le_of_mem_adjacentPairDiffs {A : List ℕ}
    (hA : A.Sorted (· < ·)) (hodd : ∀ a ∈ A, Odd a) {d : ℕ}
    (hd : d ∈ adjacentPairDiffs A) : 2 ≤ d := by
  induction A using List.twoStepInduction with
  | nil => simp [adjacentPairDiffs] at hd
  | singleton a => simp [adjacentPairDiffs] at hd
  | cons_cons a b rest ih _ =>
      simp only [adjacentPairDiffs, List.mem_cons] at hd
      rcases hd with rfl | hd
      · have hab : a < b := (List.pairwise_cons.mp hA).1 b (by simp)
        obtain ⟨u, hu⟩ := hodd a (by simp)
        obtain ⟨v, hv⟩ := hodd b (by simp)
        omega
      · exact ih hA.tail.tail (fun c hc => hodd c (by simp [hc])) hd

/-- The fixed-adjacent-pair version of the first pigeonhole step in the
dense-block argument.  Its numerical hypothesis is deliberately exposed. -/
lemma adjacent_pairs_compress {a H q x : ℕ} {A : List ℕ}
    (hA : (a :: A).Sorted (· < ·))
    (hodd : ∀ r ∈ a :: A, Odd r)
    (hq : 0 < q) (hH : 0 < H)
    (hspan : (a :: A).getLast (by simp) - a ≤ x)
    (hroom : x + H * (H * q) ≤ H * ((a :: A).length / 2)) :
    ∃ μ : ℕ, 2 ≤ μ ∧ μ < H ∧
      RepresentsTranslate (a :: A) (List.replicate q μ) := by
  let D := adjacentPairDiffs (a :: A)
  have hsortedLe : (a :: A).Sorted (· ≤ ·) := hA.imp Nat.le_of_lt
  have hDsum : D.sum ≤ x :=
    (sum_adjacentPairDiffs_le_span hsortedLe).trans hspan
  have hDlen : D.length = (a :: A).length / 2 := length_adjacentPairDiffs _
  have hsmall : H * q ≤ (D.filter fun d => d < H).length := by
    apply many_lt_of_sum_le hH hDsum
    simpa [hDlen, Nat.mul_assoc]
  obtain ⟨μ, hμH, hqμ⟩ := exists_frequent_lt hH hsmall
  have hμmem : μ ∈ D := List.count_pos_iff.mp (hq.trans_le hqμ)
  have hμ2 : 2 ≤ μ := two_le_of_mem_adjacentPairDiffs hA hodd hμmem
  have hsub : (List.replicate q μ).Sublist D :=
    List.replicate_sublist_iff.mpr hqμ
  refine ⟨μ, hμ2, hμH, ?_⟩
  exact (adjacentPairDiffs_represents hsortedLe).trans
    (RepresentsTranslate.of_sublist hsub)

lemma exists_large_residue_class {S : Finset ℕ} {μ M : ℕ}
    (hμ : 0 < μ) (hcard : μ * M ≤ S.card) :
    ∃ w : ℕ, w < μ ∧
      M ≤ (S.filter fun s => s % μ = w).card := by
  have hmaps : ∀ s ∈ S, s % μ ∈ Finset.range μ := by
    intro s hs
    exact Finset.mem_range.mpr (Nat.mod_lt s hμ)
  obtain ⟨w, hw, hfiber⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := S) (t := Finset.range μ) (f := fun s => s % μ)
      hmaps ⟨0, Finset.mem_range.mpr hμ⟩ (by simpa using hcard)
  exact ⟨w, Finset.mem_range.mp hw, by simpa using hfiber⟩

lemma residue_coprime_of_prime {p μ w : ℕ} (hp : p.Prime)
    (hμpos : 0 < μ) (hμp : μ < p) (hmod : p % μ = w) :
    w.Coprime μ := by
  have hpμ : p.Coprime μ := hp.coprime_iff_not_dvd.mpr fun hpdvd =>
    (not_le_of_gt hμp) (Nat.le_of_dvd hμpos hpdvd)
  have hgcd : Nat.gcd w μ = Nat.gcd p μ := by
    rw [← hmod]
    exact (Nat.gcd_rec μ p).symm.trans (Nat.gcd_comm μ p)
  rw [Nat.Coprime, hgcd]
  exact hpμ

noncomputable def inverseCount {μ w : ℕ} (hcop : w.Coprime μ)
    (hμ : μ ≠ 0) (r : ℕ) : ℕ :=
  Classical.choose (Nat.exists_mul_mod_eq_of_coprime r hcop hμ)

lemma inverseCount_lt {μ w : ℕ} (hcop : w.Coprime μ)
    (hμ : μ ≠ 0) (r : ℕ) : inverseCount hcop hμ r < μ :=
  (Classical.choose_spec (Nat.exists_mul_mod_eq_of_coprime r hcop hμ)).1

lemma inverseCount_mul_mod {μ w : ℕ} (hcop : w.Coprime μ)
    (hμ : μ ≠ 0) (r : ℕ) :
    w * inverseCount hcop hμ r % μ = r % μ :=
  (Classical.choose_spec (Nat.exists_mul_mod_eq_of_coprime r hcop hμ)).2

/-- A whole list of small terms can be absorbed into one larger term. -/
lemma representsTranslate_sum_diff (S : List ℕ) {b : ℕ} (hSb : S.sum ≤ b) :
    RepresentsTranslate (S ++ [b]) [b - S.sum] := by
  refine ⟨S.sum, ?_⟩
  intro x hx
  obtain ⟨T, hT, rfl⟩ := hx
  rcases List.sublist_singleton.mp hT with rfl | rfl
  · exact ⟨S, List.sublist_append_left S [b], by simp⟩
  · exact ⟨[b], by simp, by simp [Nat.add_sub_of_le hSb]⟩

/-- `q` copies of `μ` remove the quotient from a number of the form
`q * μ + r`. -/
lemma representsTranslate_replicate_add (μ q r : ℕ) :
    RepresentsTranslate (List.replicate q μ ++ [q * μ + r]) [r] := by
  simpa using
    (representsTranslate_sum_diff (List.replicate q μ)
      (b := q * μ + r) (by simp [List.sum_replicate]))

/-- Blocks used in the quotient-removal stage of the dense-block proof. -/
def correctionBlocks (μ : ℕ) : List ℕ → List ℕ → List ℕ
  | q :: qs, r :: rs => List.replicate q μ ++ (q * μ + r) :: correctionBlocks μ qs rs
  | _, _ => []

lemma correctionBlocks_represents (μ : ℕ) {qs rs : List ℕ}
    (hlen : qs.length = rs.length) :
    RepresentsTranslate (correctionBlocks μ qs rs) rs := by
  induction qs generalizing rs with
  | nil =>
      have : rs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst rs
      exact RepresentsTranslate.refl []
  | cons q qs ih =>
      cases rs with
      | nil => simp at hlen
      | cons r rs =>
          have hlenTail : qs.length = rs.length := by simpa using hlen
          simp only [correctionBlocks]
          have htail : RepresentsTranslate (correctionBlocks μ qs rs) rs := ih hlenTail
          simpa [List.append_assoc] using
            (representsTranslate_replicate_add μ q r).append htail

/-- Interleaving each target with the consecutive small terms assigned to
it by the greedy subtraction. -/
def subtractionBlocks : List (List ℕ) → List ℕ → List ℕ
  | S :: Ss, t :: ts => S ++ t :: subtractionBlocks Ss ts
  | _, _ => []

def subtractionResiduals : List (List ℕ) → List ℕ → List ℕ
  | S :: Ss, t :: ts => (t - S.sum) :: subtractionResiduals Ss ts
  | _, _ => []

lemma length_subtractionResiduals {Ss : List (List ℕ)} {ts : List ℕ}
    (hlen : Ss.length = ts.length) :
    (subtractionResiduals Ss ts).length = ts.length := by
  induction Ss generalizing ts with
  | nil =>
      have : ts = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst ts
      rfl
  | cons S Ss ih =>
      cases ts with
      | nil => simp at hlen
      | cons t ts =>
          have hlenTail : Ss.length = ts.length := by simpa using hlen
          simp [subtractionResiduals, ih hlenTail]

lemma subtractionBlocks_represents {Ss : List (List ℕ)} {ts : List ℕ}
    (hlen : Ss.length = ts.length)
    (hle : ∀ i (hi : i < Ss.length), Ss[i].sum ≤ ts[i]) :
    RepresentsTranslate (subtractionBlocks Ss ts) (subtractionResiduals Ss ts) := by
  induction Ss generalizing ts with
  | nil =>
      have : ts = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst ts
      exact RepresentsTranslate.refl []
  | cons S Ss ih =>
      cases ts with
      | nil => simp at hlen
      | cons t ts =>
          have hlenTail : Ss.length = ts.length := by simpa using hlen
          simp only [subtractionBlocks, subtractionResiduals]
          have hSt : S.sum ≤ t := by
            have hhead := hle 0 (by simp)
            change S.sum ≤ t at hhead
            exact hhead
          have htail :
              RepresentsTranslate (subtractionBlocks Ss ts)
                (subtractionResiduals Ss ts) := by
            apply ih hlenTail
            intro i hi
            have hi' : i + 1 < (S :: Ss).length := by simp; omega
            simpa using hle (i + 1) hi'
          simpa [List.append_assoc] using
            (representsTranslate_sum_diff S hSt).append htail

/-- Longest initial segment whose sum stays below the budget. -/
def takeUnder (b : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: A => if a ≤ b then a :: takeUnder (b - a) A else []

def dropUnder (b : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: A => if a ≤ b then dropUnder (b - a) A else a :: A

lemma takeUnder_append_dropUnder (b : ℕ) (A : List ℕ) :
    takeUnder b A ++ dropUnder b A = A := by
  induction A generalizing b with
  | nil => simp [takeUnder, dropUnder]
  | cons a A ih =>
      by_cases ha : a ≤ b
      · simp [takeUnder, dropUnder, ha, ih]
      · simp [takeUnder, dropUnder, ha]

lemma sum_takeUnder_le (b : ℕ) (A : List ℕ) : (takeUnder b A).sum ≤ b := by
  induction A generalizing b with
  | nil => simp [takeUnder]
  | cons a A ih =>
      by_cases ha : a ≤ b
      · simp only [takeUnder, if_pos ha, List.sum_cons]
        have := ih (b - a)
        omega
      · simp [takeUnder, ha]

lemma sum_dropUnder (b : ℕ) (A : List ℕ) :
    (dropUnder b A).sum = A.sum - (takeUnder b A).sum := by
  have happ := congrArg List.sum (takeUnder_append_dropUnder b A)
  rw [List.sum_append] at happ
  omega

lemma residual_lt_head_dropUnder {b : ℕ} {A : List ℕ} (hlarge : b < A.sum) :
    ∃ a B, dropUnder b A = a :: B ∧ b - (takeUnder b A).sum < a := by
  induction A generalizing b with
  | nil => simp at hlarge
  | cons a A ih =>
      by_cases ha : a ≤ b
      · have hsum : (a :: A).sum = a + A.sum := by simp
        have htail : b - a < A.sum := by
          rw [hsum] at hlarge
          omega
        obtain ⟨c, C, hdrop, hres⟩ := ih htail
        refine ⟨c, C, ?_, ?_⟩
        · simpa [dropUnder, ha] using hdrop
        · simp only [takeUnder, if_pos ha, List.sum_cons]
          omega
      · refine ⟨a, A, by simp [dropUnder, ha], ?_⟩
        simp [takeUnder, ha]
        omega

/-- Greedily allocate a consecutive epsilon segment below each target. -/
def allocateUnder : List ℕ → List ℕ → List (List ℕ)
  | [], _ => []
  | t :: ts, A => takeUnder t A :: allocateUnder ts (dropUnder t A)

def remainderUnder : List ℕ → List ℕ → List ℕ
  | [], A => A
  | t :: ts, A => remainderUnder ts (dropUnder t A)

lemma flatten_allocateUnder_append_remainder (ts A : List ℕ) :
    (allocateUnder ts A).flatten ++ remainderUnder ts A = A := by
  induction ts generalizing A with
  | nil => simp [allocateUnder, remainderUnder]
  | cons t ts ih =>
      simp only [allocateUnder, remainderUnder, List.flatten_cons, List.append_assoc]
      rw [ih, takeUnder_append_dropUnder]

lemma length_allocateUnder (ts A : List ℕ) :
    (allocateUnder ts A).length = ts.length := by
  induction ts generalizing A with
  | nil => rfl
  | cons t ts ih => simp [allocateUnder, ih]

lemma allocateUnder_sum_le (ts A : List ℕ) {i : ℕ}
    (hi : i < (allocateUnder ts A).length) :
    (allocateUnder ts A)[i].sum ≤ ts.getD i 0 := by
  induction ts generalizing A i with
  | nil => simp [allocateUnder] at hi
  | cons t ts ih =>
      cases i with
      | zero => simpa [allocateUnder] using sum_takeUnder_le t A
      | succ i =>
          have hi' : i < (allocateUnder ts (dropUnder t A)).length := by
            simpa only [allocateUnder, List.length_cons, Nat.succ_lt_succ_iff] using hi
          simpa [allocateUnder] using ih (A := dropUnder t A) (i := i) hi'

lemma remainderUnder_long {ts A : List ℕ} {R : ℕ}
    (hmass : ts.sum + R < A.sum) : R < (remainderUnder ts A).sum := by
  induction ts generalizing A with
  | nil => simpa [remainderUnder] using hmass
  | cons t ts ih =>
      have htake := sum_takeUnder_le t A
      have hdrop := sum_dropUnder t A
      apply ih (A := dropUnder t A)
      simp only [List.sum_cons] at hmass
      omega

lemma allocation_residuals_bounded {ts A : List ℕ} {R H : ℕ}
    (hmass : ts.sum + R < A.sum)
    (hbound : ∀ a ∈ A, a ≤ H) :
    (∀ i (hi : i < (allocateUnder ts A).length),
        (allocateUnder ts A)[i].sum ≤ ts.getD i 0) ∧
      (∀ r ∈ subtractionResiduals (allocateUnder ts A) ts, r < H) ∧
      R < (remainderUnder ts A).sum := by
  induction ts generalizing A with
  | nil =>
      simp only [allocateUnder, subtractionResiduals, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true, true_and, remainderUnder]
      simpa using hmass
  | cons t ts ih =>
      have htA : t < A.sum := by
        simp only [List.sum_cons] at hmass
        omega
      obtain ⟨a, B, hdrop, hres⟩ := residual_lt_head_dropUnder htA
      have haH : a ≤ H := by
        apply hbound a
        have haDrop : a ∈ dropUnder t A := by simp [hdrop]
        rw [← takeUnder_append_dropUnder t A]
        simp [haDrop]
      have htailMass : ts.sum + R < (dropUnder t A).sum := by
        have htake := sum_takeUnder_le t A
        have hdropSum := sum_dropUnder t A
        simp only [List.sum_cons] at hmass
        omega
      have htailBound : ∀ c ∈ dropUnder t A, c ≤ H := by
        intro c hc
        apply hbound c
        rw [← takeUnder_append_dropUnder t A]
        simp [hc]
      obtain ⟨hchunks, hresiduals, hrem⟩ := ih htailMass htailBound
      refine ⟨?_, ?_, hrem⟩
      · intro i hi
        cases i with
        | zero => simpa [allocateUnder] using sum_takeUnder_le t A
        | succ i =>
            have hi' : i < (allocateUnder ts (dropUnder t A)).length := by
              simpa only [allocateUnder, List.length_cons, Nat.succ_lt_succ_iff] using hi
            simpa [allocateUnder] using hchunks i hi'
      · intro r hr
        simp only [allocateUnder, subtractionResiduals, List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact hres.trans_le haH
        · exact hresiduals r hr

lemma subtractionBlocks_append_perm {Ss : List (List ℕ)} {ts rem : List ℕ}
    (hlen : Ss.length = ts.length) :
    (subtractionBlocks Ss ts ++ rem).Perm (Ss.flatten ++ rem ++ ts) := by
  induction Ss generalizing ts with
  | nil =>
      have : ts = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst ts
      simp [subtractionBlocks]
  | cons S Ss ih =>
      obtain ⟨t, ts, rfl⟩ := List.exists_cons_of_length_eq_add_one (by
        simpa using hlen.symm)
      simp only [subtractionBlocks, List.flatten_cons]
      have htail := ih (ts := ts) (by simpa using hlen)
      calc
        (S ++ t :: subtractionBlocks Ss ts) ++ rem =
            S ++ (t :: (subtractionBlocks Ss ts ++ rem)) := by simp [List.append_assoc]
        _ ~ S ++ (t :: (Ss.flatten ++ rem ++ ts)) :=
          (List.Perm.refl S).append (htail.cons t)
        _ ~ S ++ Ss.flatten ++ rem ++ t :: ts := by
          simpa [List.append_assoc] using
            (List.perm_middle (l₁ := Ss.flatten ++ rem) (l₂ := ts)).symm.append_left S

lemma allocation_represents {ts A : List ℕ} :
    RepresentsTranslate (A ++ ts)
      (subtractionResiduals (allocateUnder ts A) ts ++ remainderUnder ts A) := by
  let Ss := allocateUnder ts A
  let rem := remainderUnder ts A
  have hlen : Ss.length = ts.length := length_allocateUnder ts A
  have hle : ∀ i (hi : i < Ss.length), Ss[i].sum ≤ ts[i] := by
    intro i hi
    have hiTs : i < ts.length := by simpa [hlen] using hi
    have hiAlloc : i < (allocateUnder ts A).length := by simpa [Ss] using hi
    have hraw := allocateUnder_sum_le ts A hiAlloc
    rw [← List.getElem_eq_getD (l := ts) (i := i) (h := hiTs) 0] at hraw
    simpa [Ss] using hraw
  have hblocks := (subtractionBlocks_represents hlen hle).append_right rem
  have hp : (subtractionBlocks Ss ts ++ rem).Perm (A ++ ts) := by
    have hperm := subtractionBlocks_append_perm (rem := rem) hlen
    have hflat := flatten_allocateUnder_append_remainder ts A
    simpa [Ss, rem, hflat, List.append_assoc] using hperm
  exact hblocks.perm_left hp

lemma dvd_list_sum {μ : ℕ} {A : List ℕ} (hA : ∀ a ∈ A, μ ∣ a) : μ ∣ A.sum := by
  induction A with
  | nil => simp
  | cons a A ih =>
      exact dvd_add (hA a (by simp)) (ih fun b hb => hA b (by simp [hb]))

lemma allocation_residual_mod {μ : ℕ} {ts A rs : List ℕ}
    (hlen : ts.length = rs.length)
    (hmod : ∀ i (hi : i < ts.length), ts[i] % μ = rs[i] % μ)
    (hdiv : ∀ a ∈ A, μ ∣ a) :
    (subtractionResiduals (allocateUnder ts A) ts).map (fun r => r % μ) =
      rs.map (fun r => r % μ) := by
  induction ts generalizing A rs with
  | nil =>
      have : rs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst rs
      rfl
  | cons t ts ih =>
      obtain ⟨r, rs, rfl⟩ := List.exists_cons_of_length_eq_add_one (by
        simpa using hlen.symm)
      have htakeLe := sum_takeUnder_le t A
      have htakeDvd : μ ∣ (takeUnder t A).sum := by
        apply dvd_list_sum
        intro a ha
        apply hdiv a
        rw [← takeUnder_append_dropUnder t A]
        exact List.mem_append_left _ ha
      have hheadMod : (t - (takeUnder t A).sum) % μ = r % μ := by
        have htmod : t ≡ r [MOD μ] := hmod 0 (by simp)
        have htakemod : (takeUnder t A).sum ≡ 0 [MOD μ] := by
          exact Nat.modEq_zero_iff_dvd.mpr htakeDvd
        change t - (takeUnder t A).sum ≡ r [MOD μ]
        exact htmod.sub htakeLe (Nat.zero_le _) htakemod
      have htailDiv : ∀ a ∈ dropUnder t A, μ ∣ a := by
        intro a ha
        apply hdiv a
        rw [← takeUnder_append_dropUnder t A]
        exact List.mem_append_right _ ha
      simp only [allocateUnder, subtractionResiduals, List.map_cons,
        List.cons.injEq]
      refine ⟨hheadMod, ?_⟩
      have hlenTail : ts.length = rs.length := by simpa using hlen
      have hmodTail : ∀ i (hi : i < ts.length), ts[i] % μ = rs[i] % μ := by
        intro i hi
        have hi' : i + 1 < (t :: ts).length := by simp; omega
        simpa using hmod (i + 1) hi'
      exact ih (A := dropUnder t A) (rs := rs) hlenTail hmodTail htailDiv

lemma zip_quotient_residue_eq {μ : ℕ} {R rs : List ℕ}
    (hmods : R.map (fun r => r % μ) = rs)
    (hrs : ∀ r ∈ rs, r < μ) :
    List.zipWith (fun q r => q * μ + r) (R.map fun r => r / μ) rs = R := by
  induction R generalizing rs with
  | nil =>
      have : rs = [] := by simpa using hmods.symm
      subst rs
      rfl
  | cons a R ih =>
      obtain ⟨r, rs, rfl⟩ := List.exists_cons_of_length_eq_add_one (by
        have := congrArg List.length hmods
        simpa using this.symm)
      simp only [List.map_cons, List.cons.injEq] at hmods
      rcases hmods with ⟨hhead, htail⟩
      simp only [List.map_cons, List.zipWith_cons_cons, List.cons.injEq]
      constructor
      · rw [← hhead, Nat.div_add_mod']
      · exact ih htail (fun s hs => hrs s (by simp [hs]))

lemma correctionBlocks_append_perm (μ rem : ℕ) {qs rs tail : List ℕ}
    (hlen : qs.length = rs.length) :
    (correctionBlocks μ qs rs ++ List.replicate rem μ ++ tail).Perm
      (List.replicate (qs.sum + rem) μ ++
        List.zipWith (fun q r => q * μ + r) qs rs ++ tail) := by
  induction qs generalizing rs with
  | nil =>
      have : rs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst rs
      simp [correctionBlocks]
  | cons q qs ih =>
      obtain ⟨r, rs, rfl⟩ := List.exists_cons_of_length_eq_add_one (by
        simpa using hlen.symm)
      have htail := ih (rs := rs) (by simpa using hlen)
      let v := q * μ + r
      let M := List.replicate (qs.sum + rem) μ
      let V := List.zipWith (fun q r => q * μ + r) qs rs
      calc
        correctionBlocks μ (q :: qs) (r :: rs) ++ List.replicate rem μ ++ tail =
            List.replicate q μ ++ [v] ++
              (correctionBlocks μ qs rs ++ List.replicate rem μ ++ tail) := by
                simp [correctionBlocks, v, List.append_assoc]
        _ ~ List.replicate q μ ++ [v] ++ (M ++ V ++ tail) :=
          (List.Perm.refl (List.replicate q μ ++ [v])).append htail
        _ ~ List.replicate q μ ++ M ++ [v] ++ V ++ tail := by
          have hmove : ([v] ++ M).Perm (M ++ [v]) := List.perm_append_comm
          simpa [List.append_assoc] using
            (List.Perm.refl (List.replicate q μ)).append
              (hmove.append (List.Perm.refl (V ++ tail)))
        _ = List.replicate ((q :: qs).sum + rem) μ ++
              List.zipWith (fun q r => q * μ + r) (q :: qs) (r :: rs) ++ tail := by
          simp only [List.sum_cons, List.zipWith_cons_cons, v, V, M]
          rw [← List.replicate_add]
          rw [show q + (qs.sum + rem) = q + qs.sum + rem by omega]
          simp [List.append_assoc]

/-- A list represents every integer from zero through `F`. -/
def ListCoversTo (A : List ℕ) (F : ℕ) : Prop :=
  ∀ x : ℕ, x ≤ F → ListSubsetSum A x

lemma ListCoversTo.nil : ListCoversTo [] 0 := by
  intro x hx
  have : x = 0 := Nat.eq_zero_of_le_zero hx
  subst x
  exact ListSubsetSum.zero []

lemma ListCoversTo.singleton_one : ListCoversTo [1] 1 := by
  intro x hx
  interval_cases x <;> simp [ListSubsetSum]

lemma ListCoversTo.append_one {A : List ℕ} {F d : ℕ}
    (hA : ListCoversTo A F) (hd : d ≤ F + 1) :
    ListCoversTo (A ++ [d]) (F + d) := by
  intro x hx
  by_cases hxF : x ≤ F
  · simpa using (hA x hxF).append (ListSubsetSum.zero [d])
  · have hdx : d ≤ x := by omega
    have hsub : x - d ≤ F := by omega
    have hrepr := (hA (x - d) hsub).append (ListSubsetSum.self [d])
    simpa [Nat.sub_add_cancel hdx] using hrepr

/-- Coverage passes backwards through a translated representation. -/
lemma RepresentsTranslate.covers {A B : List ℕ} {F : ℕ}
    (hAB : RepresentsTranslate A B) (hB : ListCoversTo B F) :
    ∃ E : ℕ, ∀ x : ℕ, x ≤ F → ListSubsetSum A (E + x) := by
  obtain ⟨E, hE⟩ := hAB
  exact ⟨E, fun x hx => hE x (hB x hx)⟩

lemma ListSubsetSum.mem_subsetSum {A : List ℕ} (hA : A.Nodup) {x : ℕ}
    (hx : ListSubsetSum A x) : x ∈ A.toFinset.subsetSum := by
  obtain ⟨T, hTA, hsum⟩ := hx
  have hT : T.Nodup := hA.sublist hTA
  apply Finset.mem_subsetSum_iff.mpr
  refine ⟨T.toFinset, ?_, ?_⟩
  · intro d hd
    simp only [List.mem_toFinset] at hd ⊢
    exact hTA.subset hd
  · calc
      ∑ b ∈ T.toFinset, b = (T.map id).sum := List.sum_toFinset id hT
      _ = T.sum := by simp
      _ = x := hsum

lemma ListSubsetSum.le_sum {A : List ℕ} {x : ℕ}
    (hx : ListSubsetSum A x) : x ≤ A.sum := by
  obtain ⟨T, hTA, rfl⟩ := hx
  exact List.Sublist.sum_le_sum hTA (fun _ _ => Nat.zero_le _)

/-! ## Finite subset-sum intervals -/

/-- `D` represents every integer in the inclusive interval from `E` through
`E + F` as a sum of distinct members. -/
def CoversInterval (D : Finset ℕ) (E F : ℕ) : Prop :=
  ∀ x : ℕ, E ≤ x → x ≤ E + F → x ∈ D.subsetSum

lemma RepresentsTranslate.coversInterval {A B : List ℕ} {F : ℕ}
    (hA : A.Nodup) (hAB : RepresentsTranslate A B)
    (hB : ListCoversTo B F) :
    ∃ E : ℕ, E ≤ A.sum ∧ CoversInterval A.toFinset E F := by
  obtain ⟨E, hE⟩ := hAB
  have hE0 : ListSubsetSum A E := by
    simpa using hE 0 (ListSubsetSum.zero B)
  refine ⟨E, hE0.le_sum, ?_⟩
  intro y hyE hyTop
  have hsub : y - E ≤ F := by omega
  have hrepr := hE (y - E) (hB (y - E) hsub)
  have heq : E + (y - E) = y := Nat.add_sub_of_le hyE
  rw [heq] at hrepr
  exact hrepr.mem_subsetSum hA

lemma CoversInterval.mono {D D' : Finset ℕ} {E F : ℕ}
    (h : CoversInterval D E F) (hDD' : D ⊆ D') :
    CoversInterval D' E F := by
  intro x hxE hxF
  exact Finset.subsetSum_mono hDD' (h x hxE hxF)

lemma mem_subsetSum_image_mul {D : Finset ℕ} {x p : ℕ} (hp : 0 < p)
    (hx : x ∈ D.subsetSum) :
    p * x ∈ (D.image fun d => p * d).subsetSum := by
  obtain ⟨S, hSD, hsum⟩ := Finset.mem_subsetSum_iff.mp hx
  apply Finset.mem_subsetSum_iff.mpr
  refine ⟨S.image (fun d => p * d), ?_, ?_⟩
  · intro y hy
    obtain ⟨d, hdS, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨d, hSD hdS, rfl⟩
  · rw [Finset.sum_image]
    · rw [← Finset.mul_sum, hsum]
    · intro a ha b hb hab
      exact Nat.eq_of_mul_eq_mul_left hp hab

lemma mem_subsetSum_union_add {A B : Finset ℕ} (hAB : Disjoint A B)
    {x y : ℕ} (hx : x ∈ A.subsetSum) (hy : y ∈ B.subsetSum) :
    x + y ∈ (A ∪ B).subsetSum := by
  obtain ⟨S, hSA, hSsum⟩ := Finset.mem_subsetSum_iff.mp hx
  obtain ⟨T, hTB, hTsum⟩ := Finset.mem_subsetSum_iff.mp hy
  have hST : Disjoint S T := hAB.mono hSA hTB
  apply Finset.mem_subsetSum_iff.mpr
  refine ⟨S ∪ T, Finset.union_subset_union hSA hTB, ?_⟩
  rw [Finset.sum_union hST]
  omega

/-- Minkowski addition of an interval and a `p`-dilated interval. -/
lemma CoversInterval.union_image_mul {A B : Finset ℕ} {E₁ F₁ E₂ F₂ p : ℕ}
    (hA : CoversInterval A E₁ F₁) (hB : CoversInterval B E₂ F₂)
    (hp : 0 < p) (hpF : p ≤ F₁ + 1)
    (hdisj : Disjoint A (B.image fun d => p * d)) :
    CoversInterval (A ∪ B.image fun d => p * d)
      (E₁ + p * E₂) (F₁ + p * F₂) := by
  intro y hyLow hyTop
  let z := y - (E₁ + p * E₂)
  have hz : y = E₁ + p * E₂ + z := by
    dsimp [z]
    omega
  have hzTop : z ≤ F₁ + p * F₂ := by
    dsimp [z]
    omega
  let b := min (z / p) F₂
  let a := z - p * b
  have hb : b ≤ F₂ := min_le_right _ _
  have hpbz : p * b ≤ z := by
    dsimp [b]
    simpa [Nat.mul_comm] using
      Nat.mul_le_of_le_div p (min (z / p) F₂) z (min_le_left _ _)
  have ha : a ≤ F₁ := by
    by_cases hquot : z / p ≤ F₂
    · have hbEq : b = z / p := min_eq_left hquot
      have hrem : a = z % p := by
        dsimp [a]
        rw [hbEq]
        have hdecomp := Nat.div_add_mod z p
        omega
      rw [hrem]
      have hremLt := Nat.mod_lt z hp
      omega
    · have hF : F₂ ≤ z / p := Nat.le_of_lt (Nat.lt_of_not_ge hquot)
      have hbEq : b = F₂ := min_eq_right hF
      have hpb : p * F₂ ≤ z := by
        simpa [Nat.mul_comm] using Nat.mul_le_of_le_div p F₂ z hF
      dsimp [a]
      rw [hbEq]
      change z - p * F₂ ≤ F₁
      omega
  have hza : z = a + p * b := by
    dsimp [a]
    exact (Nat.sub_add_cancel hpbz).symm
  have hxA := hA (E₁ + a) (Nat.le_add_right _ _) (Nat.add_le_add_left ha _)
  have hxB := hB (E₂ + b) (Nat.le_add_right _ _) (Nat.add_le_add_left hb _)
  have hxScale := mem_subsetSum_image_mul hp hxB
  have hsum := mem_subsetSum_union_add hdisj hxA hxScale
  have hyEq : (E₁ + a) + p * (E₂ + b) = y := by
    calc
      (E₁ + a) + p * (E₂ + b) = E₁ + p * E₂ + (a + p * b) := by
        rw [Nat.mul_add]
        omega
      _ = E₁ + p * E₂ + z := by rw [← hza]
      _ = y := hz.symm
  rw [← hyEq]
  exact hsum

/-- A finset of odd primes in the half-open dyadic block `[x,2x)`. -/
def PrimeBlock (x : ℕ) (P : Finset ℕ) : Prop :=
  ∀ p ∈ P, p.Prime ∧ x ≤ p ∧ p < 2 * x

def WeakDenseBlock (x : ℕ) (P : Finset ℕ) : Prop :=
  ∃ E F : ℕ, E ≤ ∑ p ∈ P, p ∧ 4 * x < F ∧ CoversInterval P E F

/-- The doubled dense block used as the seed in the divisor completion. -/
def strongBlockDivisors (p : ℕ) (Q : Finset ℕ) : Finset ℕ :=
  Q ∪ (Q.erase p).image (fun q => p * q)

lemma strongBlockDivisors_cover {x p : ℕ} {Q : Finset ℕ}
    (hx : 3 ≤ x) (hblock : PrimeBlock x Q) (hpQ : p ∈ Q)
    (hQ : WeakDenseBlock x Q) (hQerase : WeakDenseBlock x (Q.erase p)) :
    ∃ E F : ℕ, 4 * x ^ 2 < F ∧
      CoversInterval (strongBlockDivisors p Q) E F := by
  obtain ⟨E₁, F₁, hE₁, hF₁, hcover₁⟩ := hQ
  obtain ⟨E₂, F₂, hE₂, hF₂, hcover₂⟩ := hQerase
  have hpData := hblock p hpQ
  have hpPos : 0 < p := hpData.1.pos
  have hpF : p ≤ F₁ + 1 := by omega
  have hdisj : Disjoint Q ((Q.erase p).image fun q => p * q) := by
    rw [Finset.disjoint_left]
    intro y hyQ hyImage
    obtain ⟨q, hqErase, rfl⟩ := Finset.mem_image.mp hyImage
    have hqQ : q ∈ Q := Finset.mem_of_mem_erase hqErase
    have hyData := hblock (p * q) hyQ
    have hqData := hblock q hqQ
    have hprodLower : x * x ≤ p * q := Nat.mul_le_mul hpData.2.1 hqData.2.1
    have hxx : 2 * x ≤ x * x := by nlinarith
    omega
  have hcover := hcover₁.union_image_mul hcover₂ hpPos hpF hdisj
  refine ⟨E₁ + p * E₂, F₁ + p * F₂, ?_, ?_⟩
  · have hpLower : x ≤ p := hpData.2.1
    nlinarith
  · simpa [strongBlockDivisors] using hcover

lemma strongBlockDivisors_cover_bounded {x p : ℕ} {Q : Finset ℕ}
    (hx : 3 ≤ x) (hblock : PrimeBlock x Q) (hpQ : p ∈ Q)
    (hQ : WeakDenseBlock x Q) (hQerase : WeakDenseBlock x (Q.erase p)) :
    ∃ E F : ℕ, E ≤ ∑ d ∈ strongBlockDivisors p Q, d ∧
      4 * x ^ 2 < F ∧ CoversInterval (strongBlockDivisors p Q) E F := by
  obtain ⟨E₁, F₁, hE₁, hF₁, hcover₁⟩ := hQ
  obtain ⟨E₂, F₂, hE₂, hF₂, hcover₂⟩ := hQerase
  have hpData := hblock p hpQ
  have hpPos : 0 < p := hpData.1.pos
  have hpF : p ≤ F₁ + 1 := by omega
  have hdisj : Disjoint Q ((Q.erase p).image fun q ↦ p * q) := by
    rw [Finset.disjoint_left]
    intro y hyQ hyImage
    obtain ⟨q, hqErase, rfl⟩ := Finset.mem_image.mp hyImage
    have hqQ : q ∈ Q := Finset.mem_of_mem_erase hqErase
    have hyData := hblock (p * q) hyQ
    have hqData := hblock q hqQ
    have hprodLower : x * x ≤ p * q := Nat.mul_le_mul hpData.2.1 hqData.2.1
    have hxx : 2 * x ≤ x * x := by nlinarith
    omega
  have hcover := hcover₁.union_image_mul hcover₂ hpPos hpF hdisj
  have himage : ∑ d ∈ (Q.erase p).image (fun q ↦ p * q), d =
      p * ∑ q ∈ Q.erase p, q := by
    rw [Finset.sum_image]
    · rw [Finset.mul_sum]
    · intro a ha b hb hab
      exact Nat.eq_of_mul_eq_mul_left hpPos hab
  have hEsum : E₁ + p * E₂ ≤ ∑ d ∈ strongBlockDivisors p Q, d := by
    rw [strongBlockDivisors, Finset.sum_union hdisj, himage]
    exact Nat.add_le_add hE₁ (Nat.mul_le_mul_left p hE₂)
  refine ⟨E₁ + p * E₂, F₁ + p * F₂, hEsum, ?_, ?_⟩
  · have hpLower : x ≤ p := hpData.2.1
    nlinarith
  · simpa [strongBlockDivisors] using hcover

/-- Adjoining a fresh summand no larger than the current interval length plus
one extends the covered interval by exactly that summand. -/
lemma CoversInterval.insert {D : Finset ℕ} {E F d : ℕ}
    (h : CoversInterval D E F) (hdD : d ∉ D) (hd : d ≤ F + 1) :
    CoversInterval (Insert.insert d D) E (F + d) := by
  intro x hxE hxTop
  by_cases hx : x ≤ E + F
  · exact Finset.subsetSum_mono (Finset.subset_insert d D) (h x hxE hx)
  have hEx : E + F + 1 ≤ x := Nat.succ_le_iff.mpr (lt_of_not_ge hx)
  have hdx : d ≤ x := hd.trans (by omega)
  have hlow : E ≤ x - d := by omega
  have hupp : x - d ≤ E + F := by omega
  obtain ⟨S, hSD, hsum⟩ := Finset.mem_subsetSum_iff.mp (h (x - d) hlow hupp)
  apply Finset.mem_subsetSum_iff.mpr
  refine ⟨Insert.insert d S, ?_, ?_⟩
  · rw [Finset.insert_subset_iff]
    exact ⟨Finset.mem_insert_self _ _, hSD.trans (Finset.subset_insert d D)⟩
  · rw [Finset.sum_insert]
    · simpa [hsum] using Nat.add_sub_of_le hdx
    · exact fun hdS => hdD (hSD hdS)

/-- A list can be appended to an already covered interval when each new term
is at most one plus the length available at that stage. -/
def SlowExtension (F : ℕ) : List ℕ → Prop
  | [] => True
  | d :: ds => d ≤ F + 1 ∧ SlowExtension (F + d) ds

lemma slowExtension_append {F : ℕ} {A B : List ℕ} :
    SlowExtension F (A ++ B) ↔
      SlowExtension F A ∧ SlowExtension (F + A.sum) B := by
  induction A generalizing F with
  | nil => simp [SlowExtension]
  | cons a A ih =>
      simp only [List.cons_append, List.sum_cons, SlowExtension]
      rw [ih]
      simp only [Nat.add_assoc, and_assoc]

lemma slowExtension_of_bounded {F H : ℕ} {ds : List ℕ}
    (hFH : H ≤ F + 1) (hds : ∀ d ∈ ds, d ≤ H) :
    SlowExtension F ds := by
  induction ds generalizing F with
  | nil => trivial
  | cons d ds ih =>
      constructor
      · exact (hds d (by simp)).trans hFH
      · apply ih
        · omega
        · intro e he
          exact hds e (by simp [he])

lemma ListCoversTo.append_slow {A ds : List ℕ} {F : ℕ}
    (hA : ListCoversTo A F) (hslow : SlowExtension F ds) :
    ListCoversTo (A ++ ds) (F + ds.sum) := by
  induction ds generalizing A F with
  | nil => simpa using hA
  | cons d ds ih =>
      have hstep := hA.append_one hslow.1
      have htail := ih hstep hslow.2
      simpa [List.append_assoc, Nat.add_assoc] using htail

/-- Binary place values `[1,2,...,2^(m-1)]`. -/
def binaryWeights : ℕ → List ℕ
  | 0 => []
  | m + 1 => binaryWeights m ++ [2 ^ m]

@[simp] lemma binaryWeights_zero : binaryWeights 0 = [] := rfl

@[simp] lemma binaryWeights_succ (m : ℕ) :
    binaryWeights (m + 1) = binaryWeights m ++ [2 ^ m] := rfl

lemma binaryWeights_eq_map_range (m : ℕ) :
    binaryWeights m = (List.range m).map (fun i => 2 ^ i) := by
  induction m with
  | zero => simp [binaryWeights]
  | succ m ih => simp [binaryWeights, ih, List.range_succ]

@[simp] lemma length_binaryWeights (m : ℕ) : (binaryWeights m).length = m := by
  simp [binaryWeights_eq_map_range]

lemma binaryWeights_lt_clog (μ : ℕ) :
    ∀ r ∈ binaryWeights (Nat.clog 2 μ), r < μ := by
  intro r hr
  rw [binaryWeights_eq_map_range, List.mem_map] at hr
  obtain ⟨i, hi, rfl⟩ := hr
  exact (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).mp
    (List.mem_range.mp hi)

lemma le_two_pow_clog (μ : ℕ) : μ ≤ 2 ^ Nat.clog 2 μ := by
  exact Nat.le_pow_clog (by norm_num : 1 < 2) μ

lemma getElem_binaryWeights {m i : ℕ} (hi : i < (binaryWeights m).length) :
    (binaryWeights m)[i] = 2 ^ i := by
  simpa [binaryWeights_eq_map_range] using congrArg (fun j : ℕ => 2 ^ j)
    (List.getElem_range (by simpa [binaryWeights_eq_map_range] using hi))

lemma sum_binaryWeights (m : ℕ) : (binaryWeights m).sum = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [binaryWeights_succ, List.sum_append, ih]
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
      have hpow : 1 ≤ 2 ^ m := one_le_pow₀ (by norm_num)
      rw [pow_succ]
      omega

noncomputable def binaryInverseCounts {μ w m : ℕ} (hcop : w.Coprime μ)
    (hμ : μ ≠ 0) : List ℕ :=
  (binaryWeights m).map (inverseCount hcop hμ)

lemma length_binaryInverseCounts {μ w m : ℕ} (hcop : w.Coprime μ)
    (hμ : μ ≠ 0) :
    (binaryInverseCounts (m := m) hcop hμ).length = m := by
  simp [binaryInverseCounts]

lemma getElem_binaryInverseCounts {μ w m i : ℕ} (hcop : w.Coprime μ)
    (hμ : μ ≠ 0) (hi : i < (binaryInverseCounts (m := m) hcop hμ).length) :
    (binaryInverseCounts (m := m) hcop hμ)[i] =
      inverseCount hcop hμ (2 ^ i) := by
  simp only [binaryInverseCounts, List.length_map] at hi
  simp [binaryInverseCounts, getElem_binaryWeights hi]

lemma sum_binaryInverseCounts_le {μ w m : ℕ} (hcop : w.Coprime μ)
    (hμ : μ ≠ 0) :
    (binaryInverseCounts (m := m) hcop hμ).sum ≤ m * μ := by
  calc
    (binaryInverseCounts (m := m) hcop hμ).sum ≤
        (binaryInverseCounts (m := m) hcop hμ).length * μ := by
      apply sum_le_length_mul_of_bound
      intro u hu
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hu
      exact (inverseCount_lt hcop hμ r).le
    _ = m * μ := by rw [length_binaryInverseCounts]

noncomputable def tauChunks {μ w m : ℕ} (hcop : w.Coprime μ)
    (hμ : μ ≠ 0) (A : List ℕ) : List (List ℕ) :=
  chunksBy (binaryInverseCounts (m := m) hcop hμ) A

noncomputable def tauSums {μ w m : ℕ} (hcop : w.Coprime μ)
    (hμ : μ ≠ 0) (A : List ℕ) : List ℕ :=
  (tauChunks (m := m) hcop hμ A).map List.sum

lemma tauSums_represents {μ w m : ℕ} (hcop : w.Coprime μ)
    (hμ : μ ≠ 0) (A : List ℕ) :
    RepresentsTranslate A (tauSums (m := m) hcop hμ A) := by
  exact RepresentsTranslate.chunkSums _ _

lemma length_tauSums {μ w m : ℕ} (hcop : w.Coprime μ)
    (hμ : μ ≠ 0) {A : List ℕ}
    (henough : m * μ ≤ A.length) :
    (tauSums (m := m) hcop hμ A).length = m := by
  have hsum : (binaryInverseCounts (m := m) hcop hμ).sum ≤ A.length :=
    (sum_binaryInverseCounts_le hcop hμ).trans henough
  rw [tauSums, tauChunks, List.length_map,
    ← List.length_map (f := List.length), map_length_chunksBy hsum,
    length_binaryInverseCounts]

lemma length_tauChunk {μ w m : ℕ} (hcop : w.Coprime μ)
    (hμ : μ ≠ 0) {A : List ℕ}
    (henough : m * μ ≤ A.length) {i : ℕ}
    (hi : i < (tauChunks (m := m) hcop hμ A).length)
    (hiCounts : i < (binaryInverseCounts (m := m) hcop hμ).length) :
    (tauChunks (m := m) hcop hμ A)[i].length =
      (binaryInverseCounts (m := m) hcop hμ)[i]'hiCounts := by
  have hsum : (binaryInverseCounts (m := m) hcop hμ).sum ≤ A.length :=
    (sum_binaryInverseCounts_le hcop hμ).trans henough
  have hlens := map_length_chunksBy hsum
  have hiMap : i < ((tauChunks (m := m) hcop hμ A).map List.length).length := by
    simpa using hi
  have hiMap' : i <
      ((chunksBy (binaryInverseCounts (m := m) hcop hμ) A).map List.length).length := by
    simpa [tauChunks] using hiMap
  have hgetD := congrArg (fun L : List ℕ => L.getD i 0) hlens
  rw [List.getD_eq_getElem
        (l := (chunksBy (binaryInverseCounts (m := m) hcop hμ) A).map List.length)
        (d := 0) hiMap',
      List.getD_eq_getElem
        (l := binaryInverseCounts (m := m) hcop hμ) (d := 0) hiCounts] at hgetD
  simpa [tauChunks] using hgetD

lemma tauSums_mod {μ w m : ℕ} (hcop : w.Coprime μ)
    (hμ : μ ≠ 0) {A : List ℕ}
    (hresidue : ∀ a ∈ A, a % μ = w)
    (henough : m * μ ≤ A.length) {i : ℕ}
    (hi : i < (tauSums (m := m) hcop hμ A).length) :
    (tauSums (m := m) hcop hμ A)[i] % μ = 2 ^ i % μ := by
  have hiChunks : i < (tauChunks (m := m) hcop hμ A).length := by
    simpa [tauSums] using hi
  have hchunk := chunk_sum_mod hresidue hiChunks
  have hchunk' :
      (tauChunks (m := m) hcop hμ A)[i].sum % μ =
        (tauChunks (m := m) hcop hμ A)[i].length * w % μ := by
    unfold tauChunks
    exact hchunk
  have hiCounts : i < (binaryInverseCounts (m := m) hcop hμ).length := by
    rw [length_binaryInverseCounts]
    have hlen := length_tauSums hcop hμ henough
    simpa [hlen] using hi
  have htauEq : (tauSums (m := m) hcop hμ A)[i] =
      (tauChunks (m := m) hcop hμ A)[i].sum := by
    simp [tauSums]
  rw [htauEq, hchunk']
  have hlenAt := length_tauChunk hcop hμ henough hiChunks hiCounts
  rw [hlenAt, getElem_binaryInverseCounts hcop hμ hiCounts, Nat.mul_comm,
    inverseCount_mul_mod hcop hμ]

lemma tauSums_le {μ w m B : ℕ} (hcop : w.Coprime μ)
    (hμ : μ ≠ 0) {A : List ℕ}
    (hbound : ∀ a ∈ A, a ≤ B)
    (henough : m * μ ≤ A.length) {i : ℕ}
    (hi : i < (tauSums (m := m) hcop hμ A).length) :
    (tauSums (m := m) hcop hμ A)[i] ≤ (μ - 1) * B := by
  have hiChunks : i < (tauChunks (m := m) hcop hμ A).length := by
    simpa [tauSums] using hi
  have hchunkBound : ∀ a ∈ (tauChunks (m := m) hcop hμ A)[i], a ≤ B := by
    intro a ha
    exact hbound a (mem_chunk_of_mem_chunksBy (List.getElem_mem hiChunks) a ha)
  have hsum := sum_le_length_mul_of_bound hchunkBound
  have hiCounts : i < (binaryInverseCounts (m := m) hcop hμ).length := by
    rw [length_binaryInverseCounts]
    have hlen := length_tauSums hcop hμ henough
    simpa [hlen] using hi
  have hinvlt : (binaryInverseCounts (m := m) hcop hμ)[i] < μ := by
    rw [getElem_binaryInverseCounts hcop hμ hiCounts]
    exact inverseCount_lt hcop hμ _
  have htauEq : (tauSums (m := m) hcop hμ A)[i] =
      (tauChunks (m := m) hcop hμ A)[i].sum := by
    simp [tauSums]
  rw [htauEq]
  have hlenAt := length_tauChunk hcop hμ henough hiChunks hiCounts
  calc
    (tauChunks (m := m) hcop hμ A)[i].sum ≤
        (tauChunks (m := m) hcop hμ A)[i].length * B := hsum
    _ ≤ (μ - 1) * B := Nat.mul_le_mul_right B (by omega)

/-! ### Extreme-pair compression

The second half of the dense-block argument pairs the lower and upper halves
of a short increasing list.  Besides producing differences divisible by the
chosen modulus, this pairing has quadratic total mass. -/

/-- Coordinatewise differences of two lists. -/
def zipDiffs : List ℕ → List ℕ → List ℕ
  | a :: as, b :: bs => (b - a) :: zipDiffs as bs
  | _, _ => []

@[simp] lemma length_zipDiffs {A B : List ℕ} (h : A.length = B.length) :
    (zipDiffs A B).length = A.length := by
  induction A generalizing B with
  | nil =>
      have : B = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
      subst B
      rfl
  | cons a A ih =>
      obtain ⟨b, B, rfl⟩ := List.exists_cons_of_length_eq_add_one (by
        simpa using h.symm)
      simp [zipDiffs, ih (by simpa using h)]

lemma getElem_zipDiffs {A B : List ℕ} (hlen : A.length = B.length) {i : ℕ}
    (hiA : i < A.length) (hiB : i < B.length) :
    (zipDiffs A B)[i]'(by rw [length_zipDiffs hlen]; exact hiA) =
      B[i] - A[i] := by
  induction A generalizing B i with
  | nil => simp at hiA
  | cons a A ih =>
      cases B with
      | nil => simp at hiB
      | cons b B =>
          cases i with
          | zero => rfl
          | succ i =>
              simpa [zipDiffs] using ih (B := B) (by simpa using hlen)
                (i := i) (by simpa using hiA)
                (by simpa using hiB)

/-- Pairwise difference compression, with the original lists kept in their
two consecutive blocks. -/
lemma zipDiffs_represents {A B : List ℕ}
    (hlen : A.length = B.length)
    (hle : ∀ i (hi : i < A.length), A[i] ≤ B[i]'(by simpa [hlen] using hi)) :
    RepresentsTranslate (A ++ B) (zipDiffs A B) := by
  induction A generalizing B with
  | nil =>
      have : B = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst B
      exact RepresentsTranslate.refl []
  | cons a A ih =>
      obtain ⟨b, B, rfl⟩ := List.exists_cons_of_length_eq_add_one (by
        simpa using hlen.symm)
      have hab : a ≤ b := by
        have hhead := hle 0 (by simp)
        change a ≤ b at hhead
        exact hhead
      have hlenTail : A.length = B.length := by simpa using hlen
      have hleTail : ∀ i (hi : i < A.length),
          A[i] ≤ B[i]'(by simpa [hlenTail] using hi) := by
        intro i hi
        have hi' : i + 1 < (a :: A).length := by simp; omega
        simpa using hle (i + 1) hi'
      have htail := ih hlenTail hleTail
      have hperm : (a :: A ++ b :: B).Perm ([a, b] ++ (A ++ B)) := by
        simpa [List.append_assoc] using (List.perm_middle (l₁ := A) (l₂ := B)).symm.cons a
      exact ((representsTranslate_pair_diff hab).append htail).perm_left hperm.symm

lemma zipDiffs_dvd {A B : List ℕ} {μ w : ℕ}
    (hA : ∀ a ∈ A, a % μ = w) (hB : ∀ b ∈ B, b % μ = w) :
    ∀ d ∈ zipDiffs A B, μ ∣ d := by
  induction A generalizing B with
  | nil => simp [zipDiffs]
  | cons a A ih =>
      cases B with
      | nil => simp [zipDiffs]
      | cons b B =>
          intro d hd
          simp only [zipDiffs, List.mem_cons] at hd
          rcases hd with rfl | hd
          · have hmod : a ≡ b [MOD μ] := by
              change a % μ = b % μ
              rw [hA a (by simp), hB b (by simp)]
            exact hmod.dvd'
          · exact ih (B := B) (fun c hc => hA c (by simp [hc]))
              (fun c hc => hB c (by simp [hc])) d hd

lemma zipDiffs_le_of_bounds {A B : List ℕ} {lo hi : ℕ}
    (hA : ∀ a ∈ A, lo ≤ a) (hB : ∀ b ∈ B, b ≤ hi) :
    ∀ d ∈ zipDiffs A B, d ≤ hi - lo := by
  induction A generalizing B with
  | nil => simp [zipDiffs]
  | cons a A ih =>
      cases B with
      | nil => simp [zipDiffs]
      | cons b B =>
          intro d hd
          simp only [zipDiffs, List.mem_cons] at hd
          rcases hd with rfl | hd
          · exact (Nat.sub_le_sub_right (hB b (by simp)) a).trans
              (Nat.sub_le_sub_left (hA a (by simp)) hi)
          · exact ih (B := B) (fun c hc => hA c (by simp [hc]))
              (fun c hc => hB c (by simp [hc])) d hd

/-- Two numbers in the same quotient cell of width `H` differ by less than
`H`. -/
lemma sub_lt_of_sub_div_eq {x a b H : ℕ} (hH : 0 < H)
    (hxa : x ≤ a) (hab : a ≤ b)
    (hcell : (a - x) / H = (b - x) / H) :
    b - a < H := by
  have haDecomp := Nat.div_add_mod (a - x) H
  have hbDecomp := Nat.div_add_mod (b - x) H
  rw [← hcell] at hbDecomp
  have haRem := Nat.mod_lt (a - x) hH
  have hbRem := Nat.mod_lt (b - x) hH
  have hxb : x ≤ b := hxa.trans hab
  have haSub : a - x + x = a := Nat.sub_add_cancel hxa
  have hbSub : b - x + x = b := Nat.sub_add_cancel hxb
  omega

lemma zipDiffs_lt_of_same_cell {A B : List ℕ} {x H c : ℕ}
    (hH : 0 < H)
    (hAcell : ∀ a ∈ A, x ≤ a ∧ (a - x) / H = c)
    (hBcell : ∀ b ∈ B, x ≤ b ∧ (b - x) / H = c)
    (hlen : A.length = B.length)
    (hle : ∀ i (hi : i < A.length),
      A[i] ≤ B[i]'(by simpa [hlen] using hi)) :
    ∀ d ∈ zipDiffs A B, d < H := by
  induction A generalizing B with
  | nil => simp [zipDiffs]
  | cons a A ih =>
      cases B with
      | nil => simp [zipDiffs]
      | cons b B =>
          intro d hd
          simp only [zipDiffs, List.mem_cons] at hd
          rcases hd with rfl | hd
          · have hab : a ≤ b := by
              have hhead := hle 0 (by simp)
              change a ≤ b at hhead
              exact hhead
            apply sub_lt_of_sub_div_eq hH (hAcell a (by simp)).1 hab
            rw [(hAcell a (by simp)).2, (hBcell b (by simp)).2]
          · exact ih (B := B)
              (fun z hz => hAcell z (by simp [hz]))
              (fun z hz => hBcell z (by simp [hz]))
              (by simpa using hlen)
              (fun i hi => by
                have hi' : i + 1 < (a :: A).length := by simp; omega
                simpa using hle (i + 1) hi') d hd

lemma clog_two_le_self (n : ℕ) : Nat.clog 2 n ≤ n := by
  apply Nat.clog_le_of_le_pow
  induction n with
  | zero => simp
  | succ n ih =>
      have hp : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      rw [pow_succ]
      omega

/-- A strictly increasing natural list rises by at least the increase in its
index. -/
lemma sortedLT_getElem_add_le {A : List ℕ} (hA : A.Sorted (· < ·))
    {i j : ℕ} (hi : i < A.length) (hj : j < A.length) (hij : i ≤ j) :
    j - i + A[i] ≤ A[j] := by
  have hstep : ∀ k : ℕ, ∀ hk : i + k < A.length,
      k + A[i] ≤ A[i + k] := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hk' : i + k < A.length := by omega
        have hlt : A[i + k] < A[i + k + 1] := by
          exact (List.pairwise_iff_getElem.mp hA) (i + k) (i + k + 1)
            hk' (by omega) (by omega)
        have hind := ih hk'
        have hnext : k + 1 + A[i] ≤ A[i + k + 1] := by omega
        simpa [Nat.add_assoc] using hnext
  have hjEq : i + (j - i) = j := Nat.add_sub_of_le hij
  simpa [hjEq] using hstep (j - i) (by simpa [hjEq] using hj)

/-- Pairing two consecutive blocks of `s` entries in a strictly increasing
list gives total difference at least `s²`. -/
lemma sq_le_sum_zipDiffs_take_drop {C : List ℕ} (hC : C.Sorted (· < ·))
    {s : ℕ} (hlen : 2 * s ≤ C.length) :
    s ^ 2 ≤ (zipDiffs (C.take s) ((C.drop s).take s)).sum := by
  let A := C.take s
  let B := (C.drop s).take s
  have hsC : s ≤ C.length := by omega
  have hsDrop : s ≤ C.length - s := by omega
  have hlenA : A.length = s := by simp [A, hsC]
  have hlenB : B.length = s := by simp [B, List.length_drop, hsDrop]
  have hlenAB : A.length = B.length := hlenA.trans hlenB.symm
  have hpoint : ∀ i (hi : i < A.length), s ≤ B[i] - A[i] := by
    intro i hi
    have hiS : i < s := by simpa [hlenA] using hi
    have hiC : i < C.length := hiS.trans_le (by omega)
    have hisC : i + s < C.length := by omega
    have hgap := sortedLT_getElem_add_le hC hiC hisC (by omega)
    have hAi : A[i] = C[i] := by simp [A, hiS]
    have hBi : B[i] = C[i + s] := by
      simp [B, hiS, Nat.add_comm]
    rw [hAi, hBi]
    omega
  have hterm : ∀ d ∈ zipDiffs A B, s ≤ d := by
    intro d hd
    have hlenZ : (zipDiffs A B).length = s := by rw [length_zipDiffs hlenAB, hlenA]
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
    have hiA : i < A.length := by simpa [hlenZ, hlenA] using hi
    have hiB : i < B.length := by simpa [hlenA, hlenB] using hiA
    simpa [getElem_zipDiffs hlenAB hiA hiB] using hpoint i hiA
  calc
    s ^ 2 = (zipDiffs A B).length * s := by
      rw [length_zipDiffs hlenAB, hlenA, pow_two]
    _ ≤ (zipDiffs A B).sum := by
      have hlower : ∀ L : List ℕ, (∀ d ∈ L, s ≤ d) → L.length * s ≤ L.sum := by
        intro L hL
        induction L with
        | nil => simp
        | cons d D ih =>
            have hd : s ≤ d := hL d (by simp)
            have hD : ∀ e ∈ D, s ≤ e := by
              intro e he
              exact hL e (by simp [he])
            simp only [List.length_cons, Nat.succ_mul, List.sum_cons]
            simpa [Nat.add_comm] using Nat.add_le_add (ih hD) hd
      exact hlower _ hterm

lemma binaryWeights_covers (m : ℕ) :
    ListCoversTo (binaryWeights m) (2 ^ m - 1) := by
  induction m with
  | zero => simpa using ListCoversTo.nil
  | succ m ih =>
      rw [binaryWeights_succ]
      have hpow : 1 ≤ 2 ^ m := one_le_pow₀ (by norm_num)
      have hstep := ih.append_one (d := 2 ^ m) (by omega)
      convert hstep using 1
      rw [pow_succ]
      omega

lemma slowExtension_replicate {F μ q : ℕ} (hμ : μ ≤ F + 1) :
    SlowExtension F (List.replicate q μ) := by
  apply slowExtension_of_bounded hμ
  intro d hd
  exact (List.eq_of_mem_replicate hd).le

/-- Binary weights, sufficiently many copies of `μ`, and a bounded tail form
a complete sequence. -/
lemma binary_replicate_tail_covers {m μ q H : ℕ} {tail : List ℕ}
    (hμ : μ ≤ 2 ^ m)
    (hH : H ≤ (2 ^ m - 1) + q * μ + 1)
    (htail : ∀ e ∈ tail, e ≤ H) :
    ListCoversTo
      (binaryWeights m ++ List.replicate q μ ++ tail)
      ((2 ^ m - 1) + q * μ + tail.sum) := by
  have hbase := binaryWeights_covers m
  have hrepSlow : SlowExtension (2 ^ m - 1) (List.replicate q μ) := by
    apply slowExtension_replicate
    omega
  have hrep := hbase.append_slow hrepSlow
  have htailSlow :
      SlowExtension ((2 ^ m - 1) + (List.replicate q μ).sum) tail := by
    apply slowExtension_of_bounded
    · simpa [List.sum_replicate] using hH
    · exact htail
  have hall := hrep.append_slow htailSlow
  simpa [List.sum_replicate, List.append_assoc, Nat.add_assoc] using hall

/-- The exact finite certificate produced by Hisamoto's pairing and greedy
subtraction argument.  Keeping this structure separate makes all
multiplicity and disjointness obligations explicit. -/
structure DenseCompressionCertificate (source : List ℕ) (x : ℕ) where
  bits : ℕ
  μ : ℕ
  q : ℕ
  H : ℕ
  quotients : List ℕ
  tail : List ℕ
  quotient_length : quotients.length = (binaryWeights bits).length
  represents : RepresentsTranslate source
    (correctionBlocks μ quotients (binaryWeights bits) ++
      List.replicate q μ ++ tail)
  mu_le : μ ≤ 2 ^ bits
  tail_bound : ∀ e ∈ tail, e ≤ H
  enough_mu : H ≤ (2 ^ bits - 1) + q * μ + 1
  long_tail : 4 * x < tail.sum

lemma map_mod_eq_self_of_lt {A : List ℕ} {μ : ℕ}
    (hA : ∀ a ∈ A, a < μ) : A.map (fun a => a % μ) = A := by
  induction A with
  | nil => rfl
  | cons a A ih =>
      have ha : a < μ := hA a (by simp)
      have htail : ∀ b ∈ A, b < μ := by
        intro b hb
        exact hA b (by simp [hb])
      simp [Nat.mod_eq_of_lt ha, ih htail]

/-- Package the greedy subtraction and quotient-removal stages into the exact
certificate consumed by `DenseCompressionCertificate.coversInterval`.  This
is the formal bookkeeping core of Hisamoto's dense-block lemma. -/
noncomputable def denseCompressionCertificate_of_allocation
    {source eps ts : List ℕ} {x m μ qTotal H : ℕ}
    (hlen : ts.length = (binaryWeights m).length)
    (hmod : ∀ i (hi : i < ts.length),
      ts[i] % μ = (binaryWeights m)[i] % μ)
    (hepsDiv : ∀ e ∈ eps, μ ∣ e)
    (hepsBound : ∀ e ∈ eps, e ≤ H)
    (hmass : ts.sum + 4 * x < eps.sum)
    (hsource : RepresentsTranslate source
      (List.replicate qTotal μ ++ (eps ++ ts)))
    (hweights : ∀ r ∈ binaryWeights m, r < μ)
    (hmu : μ ≤ 2 ^ m)
    (hquotients :
      ((subtractionResiduals (allocateUnder ts eps) ts).map
        (fun r => r / μ)).sum ≤ qTotal)
    (henough : H ≤ (2 ^ m - 1) +
      (qTotal - ((subtractionResiduals (allocateUnder ts eps) ts).map
        (fun r => r / μ)).sum) * μ + 1) :
    DenseCompressionCertificate source x := by
  let Ss := allocateUnder ts eps
  let R := subtractionResiduals Ss ts
  let tail := remainderUnder ts eps
  let qs := R.map (fun r => r / μ)
  let q := qTotal - qs.sum
  have hSsLen : Ss.length = ts.length := by
    simpa [Ss] using length_allocateUnder ts eps
  have hRLen : R.length = ts.length := by
    exact length_subtractionResiduals hSsLen
  have hqLen : qs.length = (binaryWeights m).length := by
    simp [qs, hRLen, hlen]
  have hRmodRaw : R.map (fun r => r % μ) =
      (binaryWeights m).map (fun r => r % μ) := by
    simpa [Ss, R] using allocation_residual_mod hlen hmod hepsDiv
  have hweightsMod : (binaryWeights m).map (fun r => r % μ) = binaryWeights m := by
    exact map_mod_eq_self_of_lt hweights
  have hRmod : R.map (fun r => r % μ) = binaryWeights m :=
    hRmodRaw.trans hweightsMod
  have hzip : List.zipWith (fun a r => a * μ + r) qs (binaryWeights m) = R := by
    simpa [qs] using zip_quotient_residue_eq hRmod hweights
  have hqsum : qs.sum ≤ qTotal := by simpa [qs, R, Ss] using hquotients
  have hsplit : qs.sum + q = qTotal := by
    dsimp [q]
    exact Nat.add_sub_of_le hqsum
  have hperm :
      (correctionBlocks μ qs (binaryWeights m) ++
        List.replicate q μ ++ tail).Perm
      (List.replicate qTotal μ ++ R ++ tail) := by
    have hp := correctionBlocks_append_perm μ q (tail := tail) hqLen
    simpa only [hsplit, hzip] using hp
  have halloc : RepresentsTranslate (eps ++ ts) (R ++ tail) := by
    simpa [Ss, R, tail] using allocation_represents (ts := ts) (A := eps)
  have hleft : RepresentsTranslate
      (List.replicate qTotal μ ++ (eps ++ ts))
      (List.replicate qTotal μ ++ (R ++ tail)) :=
    halloc.append_left (List.replicate qTotal μ)
  have hpermRep : RepresentsTranslate
      (List.replicate qTotal μ ++ (R ++ tail))
      (correctionBlocks μ qs (binaryWeights m) ++
        List.replicate q μ ++ tail) := by
    have hsame : List.replicate qTotal μ ++ (R ++ tail) =
        List.replicate qTotal μ ++ R ++ tail := by simp [List.append_assoc]
    rw [hsame]
    exact (RepresentsTranslate.refl _).perm_right hperm.symm
  obtain ⟨_, _, htailLong⟩ := allocation_residuals_bounded hmass hepsBound
  have htailBound : ∀ e ∈ tail, e ≤ H := by
    intro e he
    apply hepsBound e
    have hmem : e ∈ (allocateUnder ts eps).flatten ++ remainderUnder ts eps := by
      exact List.mem_append_right _ (by simpa [tail] using he)
    rw [flatten_allocateUnder_append_remainder] at hmem
    exact hmem
  refine
    { bits := m
      μ := μ
      q := q
      H := H
      quotients := qs
      tail := tail
      quotient_length := hqLen
      represents := hsource.trans (hleft.trans hpermRep)
      mu_le := hmu
      tail_bound := htailBound
      enough_mu := by simpa [q, qs, R, Ss] using henough
      long_tail := by simpa [tail] using htailLong }

lemma DenseCompressionCertificate.coversInterval {source : List ℕ} {x : ℕ}
    (hsource : source.Nodup) (c : DenseCompressionCertificate source x) :
    ∃ E F : ℕ, E ≤ source.sum ∧ 4 * x < F ∧
      CoversInterval source.toFinset E F := by
  have hcorr := correctionBlocks_represents c.μ c.quotient_length
  have hreduce : RepresentsTranslate
      (correctionBlocks c.μ c.quotients (binaryWeights c.bits) ++
        List.replicate c.q c.μ ++ c.tail)
      (binaryWeights c.bits ++ List.replicate c.q c.μ ++ c.tail) := by
    exact (hcorr.append_right (List.replicate c.q c.μ)).append_right c.tail
  have hrep := c.represents.trans hreduce
  have hcover : ListCoversTo
      (binaryWeights c.bits ++ List.replicate c.q c.μ ++ c.tail)
      ((2 ^ c.bits - 1) + c.q * c.μ + c.tail.sum) :=
    binary_replicate_tail_covers c.mu_le c.enough_mu c.tail_bound
  obtain ⟨E, hEsum, hinterval⟩ := hrep.coversInterval hsource hcover
  exact ⟨E, (2 ^ c.bits - 1) + c.q * c.μ + c.tail.sum,
    hEsum, c.long_tail.trans_le (Nat.le_add_left _ _), hinterval⟩

lemma weakDenseBlock_of_certificate {x : ℕ} {P : Finset ℕ}
    (c : DenseCompressionCertificate (P.sort (· ≤ ·)) x) :
    WeakDenseBlock x P := by
  have hnodup : (P.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
  obtain ⟨E, F, hE, hF, hcover⟩ := c.coversInterval hnodup
  refine ⟨E, F, ?_, hF, ?_⟩
  · calc
      E ≤ (P.sort (· ≤ ·)).sum := hE
      _ = ∑ p ∈ P, p := by
        symm
        simpa using List.sum_toFinset id hnodup
  · simpa using hcover

/-! ### The parameterized dense-block theorem

All floors and logarithms in the published dense-block lemma are isolated in
the numerical hypotheses below.  This version is what the dyadic extraction
will use: its proof is purely finite. -/

lemma weakDenseBlock_of_parameters
    {x G qTotal M K H s : ℕ} {P : Finset ℕ}
    (hblock : PrimeBlock x P)
    (hx : 3 ≤ x)
    (hG : 2 ≤ G) (hGx : G ≤ x) (hq : 0 < qTotal)
    (hroom : x + G * (G * qTotal) ≤ G * ((P.card / 2) / 2))
    (hresidueRoom : G * M ≤ P.card - P.card / 2)
    (hselectionRoom : G * G + K * (2 * s) ≤ M)
    (hK : 0 < K) (hH : 0 < H) (hxKH : x ≤ K * H)
    (hs : 0 < s)
    (hmassNumerical : 2 * x * (G * G) + 4 * x < s ^ 2)
    (hqRoom : (G + 1) * H ≤ qTotal) :
    WeakDenseBlock x P := by
  let L := P.sort (· ≤ ·)
  let k := P.card / 2
  let P₁ := L.take k
  let P₂ := L.drop k
  have hlenL : L.length = P.card := by simp [L]
  have hkcard : k ≤ P.card := by
    dsimp [k]
    exact Nat.div_le_self _ _
  have hlenP₁ : P₁.length = k := by simp [P₁, hlenL, hkcard]
  have hlenP₂ : P₂.length = P.card - k := by simp [P₂, hlenL]
  have hLnodup : L.Nodup := Finset.sort_nodup _ _
  have hLsortedLe : L.Sorted (· ≤ ·) := Finset.pairwise_sort _ _
  have hLsorted : L.Sorted (· < ·) :=
    hLsortedLe.sortedLE.sortedLT_of_nodup hLnodup |>.pairwise
  have hP₁sorted : P₁.Sorted (· < ·) :=
    hLsorted.sublist (List.take_sublist k L)
  have hP₂nodup : P₂.Nodup := hLnodup.sublist (List.drop_sublist k L)
  have hmemL : ∀ p ∈ L, p ∈ P := by
    intro p hp
    simpa [L] using hp
  have hmemP₁ : ∀ p ∈ P₁, p ∈ P := by
    intro p hp
    exact hmemL p (List.mem_of_mem_take hp)
  have hmemP₂ : ∀ p ∈ P₂, p ∈ P := by
    intro p hp
    exact hmemL p (List.mem_of_mem_drop hp)
  have hkhalfPos : 0 < k / 2 := by
    have hrightPos : 0 < G * (k / 2) := by
      have hxpos : 0 < x := by omega
      exact hxpos.trans_le (le_trans (Nat.le_add_right _ _) hroom)
    exact Nat.pos_of_mul_pos_left hrightPos
  have hkpos : 0 < k := by omega
  cases hP₁eq : P₁ with
  | nil =>
      simp [hP₁eq] at hlenP₁
      omega
  | cons a A =>
      have hAstrict : (a :: A).Sorted (· < ·) := by
        simpa [hP₁eq] using hP₁sorted
      have hAodd : ∀ r ∈ a :: A, Odd r := by
        intro r hr
        have hrP : r ∈ P := hmemP₁ r (by simpa [hP₁eq] using hr)
        have hrData := hblock r hrP
        exact hrData.1.odd_of_ne_two (by omega)
      have hspan : (a :: A).getLast (by simp) - a ≤ x := by
        have haP : a ∈ P := hmemP₁ a (by simp [hP₁eq])
        have hlastMem : (a :: A).getLast (by simp) ∈ a :: A :=
          List.getLast_mem (l := a :: A) (by simp)
        have hlastP : (a :: A).getLast (by simp) ∈ P :=
          hmemP₁ _ (by simpa [hP₁eq] using hlastMem)
        have haBound := (hblock a haP).2.1
        have hlastBound := (hblock _ hlastP).2.2
        omega
      have hroomA : x + G * (G * qTotal) ≤ G * ((a :: A).length / 2) := by
        have hlenAk : (a :: A).length = k := by
          simpa [hP₁eq] using hlenP₁
        simpa [k, hlenAk] using hroom
      obtain ⟨μ, hμ2, hμG, hP₁rep⟩ :=
        adjacent_pairs_compress hAstrict hAodd hq (by omega) hspan hroomA
      have hμpos : 0 < μ := lt_of_lt_of_le (by omega) hμ2
      have hμM : μ * M ≤ P₂.length := by
        calc
          μ * M ≤ G * M := Nat.mul_le_mul_right M hμG.le
          _ ≤ P.card - P.card / 2 := hresidueRoom
          _ = P₂.length := hlenP₂.symm
      let S₂ := P₂.toFinset
      have hcardS₂ : S₂.card = P₂.length := by
        simpa [S₂] using List.toFinset_card_of_nodup hP₂nodup
      have hμM' : μ * M ≤ S₂.card := by simpa [hcardS₂] using hμM
      obtain ⟨w, hwμ, hwCard⟩ := exists_large_residue_class hμpos hμM'
      let R := S₂.filter (fun p => p % μ = w)
      have hRcard : M ≤ R.card := by simpa [R] using hwCard
      have hselPos : 0 < K * (2 * s) :=
        Nat.mul_pos hK (Nat.mul_pos (by norm_num) hs)
      have hMpos : 0 < M := hselPos.trans_le
        (le_trans (Nat.le_add_left _ _) hselectionRoom)
      have hRnonempty : R.Nonempty := Finset.card_pos.mp (hMpos.trans_le hRcard)
      obtain ⟨p, hpR⟩ := hRnonempty
      have hpS₂ : p ∈ S₂ := (Finset.mem_filter.mp hpR).1
      have hpP₂ : p ∈ P₂ := by simpa [S₂] using hpS₂
      have hpP : p ∈ P := hmemP₂ p hpP₂
      have hpData := hblock p hpP
      have hμp : μ < p := hμG.trans_le hGx |>.trans_le hpData.2.1
      have hpmod : p % μ = w := (Finset.mem_filter.mp hpR).2
      have hcop : w.Coprime μ :=
        residue_coprime_of_prime hpData.1 hμpos hμp hpmod
      have hμne : μ ≠ 0 := hμpos.ne'
      let m := Nat.clog 2 μ
      have hmμ : m ≤ μ := clog_two_le_self μ
      have hmG : m < G := hmμ.trans_lt hμG
      have hmμSq : m * μ ≤ G * G :=
        Nat.mul_le_mul hmG.le hμG.le
      let Ares := R.sort (· ≤ ·)
      have hlenAres : Ares.length = R.card := by simp [Ares]
      have hAresNodup : Ares.Nodup := Finset.sort_nodup _ _
      have hAresSortedLe : Ares.Sorted (· ≤ ·) := Finset.pairwise_sort _ _
      have hAresSorted : Ares.Sorted (· < ·) :=
        hAresSortedLe.sortedLE.sortedLT_of_nodup hAresNodup |>.pairwise
      have hTlenEnough : m * μ ≤ Ares.length := by
        calc
          m * μ ≤ G * G := hmμSq
          _ ≤ M := (Nat.le_add_right _ _).trans hselectionRoom
          _ ≤ R.card := hRcard
          _ = Ares.length := hlenAres.symm
      let Tsrc := Ares.take (m * μ)
      let Rest := Ares.drop (m * μ)
      have hlenTsrc : Tsrc.length = m * μ := by
        simp [Tsrc, Nat.min_eq_left hTlenEnough]
      have hlenRest : Rest.length = Ares.length - m * μ := by simp [Rest]
      have hRestEnough : K * (2 * s) ≤ Rest.length := by
        rw [hlenRest]
        have hmain : m * μ + K * (2 * s) ≤ Ares.length := by
          calc
            m * μ + K * (2 * s) ≤ G * G + K * (2 * s) :=
              Nat.add_le_add_right hmμSq _
            _ ≤ M := hselectionRoom
            _ ≤ R.card := hRcard
            _ = Ares.length := hlenAres.symm
        omega
      have hRestNodup : Rest.Nodup :=
        hAresNodup.sublist (List.drop_sublist (m * μ) Ares)
      let Srest := Rest.toFinset
      have hcardSrest : Srest.card = Rest.length := by
        simpa [Srest] using List.toFinset_card_of_nodup hRestNodup
      have hmaps : ∀ z ∈ Srest, (z - x) / H ∈ Finset.range K := by
        intro z hz
        have hzRest : z ∈ Rest := by simpa [Srest] using hz
        have hzAres : z ∈ Ares := List.mem_of_mem_drop hzRest
        have hzR : z ∈ R := by simpa [Ares] using hzAres
        have hzS₂ : z ∈ S₂ := (Finset.mem_filter.mp hzR).1
        have hzP₂ : z ∈ P₂ := by simpa [S₂] using hzS₂
        have hzP : z ∈ P := hmemP₂ z hzP₂
        have hzBounds := (hblock z hzP).2
        apply Finset.mem_range.mpr
        rw [Nat.div_lt_iff_lt_mul hH]
        have hzSub : z - x < x := by omega
        exact hzSub.trans_le hxKH
      have hfiberTotal : (Finset.range K).card • (2 * s) ≤ Srest.card := by
        simpa [hcardSrest] using hRestEnough
      obtain ⟨c, hcK, hcCard⟩ :=
        Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
          (s := Srest) (t := Finset.range K)
          (f := fun z : ℕ => (z - x) / H) (n := 2 * s)
          hmaps ⟨0, Finset.mem_range.mpr hK⟩ hfiberTotal
      let Cell := Srest.filter (fun z => (z - x) / H = c)
      have hCellCard : 2 * s ≤ Cell.card := by simpa [Cell] using hcCard
      let Cfull := Cell.sort (· ≤ ·)
      let C := Cfull.take (2 * s)
      have hlenCfull : Cfull.length = Cell.card := by simp [Cfull]
      have hlenC : C.length = 2 * s := by
        simp [C, hlenCfull, Nat.min_eq_left hCellCard]
      have hCfullNodup : Cfull.Nodup := Finset.sort_nodup _ _
      have hCfullSortedLe : Cfull.Sorted (· ≤ ·) := Finset.pairwise_sort _ _
      have hCfullSorted : Cfull.Sorted (· < ·) :=
        hCfullSortedLe.sortedLE.sortedLT_of_nodup hCfullNodup |>.pairwise
      have hCNodup : C.Nodup :=
        hCfullNodup.sublist (List.take_sublist (2 * s) Cfull)
      have hCsorted : C.Sorted (· < ·) :=
        hCfullSorted.sublist (List.take_sublist (2 * s) Cfull)
      have hCcell : ∀ z ∈ C, x ≤ z ∧ (z - x) / H = c := by
        intro z hz
        have hzFull : z ∈ Cfull := List.mem_of_mem_take hz
        have hzCell : z ∈ Cell := by simpa [Cfull] using hzFull
        have hzRest : z ∈ Rest := by
          have hzSrest := (Finset.mem_filter.mp hzCell).1
          simpa [Srest] using hzSrest
        have hzAres : z ∈ Ares := List.mem_of_mem_drop hzRest
        have hzR : z ∈ R := by simpa [Ares] using hzAres
        have hzS₂ : z ∈ S₂ := (Finset.mem_filter.mp hzR).1
        have hzP₂ : z ∈ P₂ := by simpa [S₂] using hzS₂
        have hzP : z ∈ P := hmemP₂ z hzP₂
        exact ⟨(hblock z hzP).2.1, (Finset.mem_filter.mp hzCell).2⟩
      let Low := C.take s
      let High := (C.drop s).take s
      have hsC : s ≤ C.length := by rw [hlenC]; omega
      have hsDrop : s ≤ C.length - s := by rw [hlenC]; omega
      have hlenLow : Low.length = s := by simp [Low, hsC]
      have hlenHigh : High.length = s := by simp [High, List.length_drop, hsDrop]
      have hlenLH : Low.length = High.length := hlenLow.trans hlenHigh.symm
      have hleLH : ∀ i (hi : i < Low.length),
          Low[i] ≤ High[i]'(by simpa [hlenLH] using hi) := by
        intro i hi
        have hiS : i < s := by simpa [hlenLow] using hi
        have hiC : i < C.length := hiS.trans_le hsC
        have hisC : i + s < C.length := by rw [hlenC]; omega
        have hgap := sortedLT_getElem_add_le hCsorted hiC hisC (by omega)
        have hlow : Low[i] = C[i] := by simp [Low]
        have hhigh : High[i] = C[i + s] := by simp [High, Nat.add_comm]
        rw [hlow, hhigh]
        omega
      let eps := zipDiffs Low High
      have hepsMass : s ^ 2 ≤ eps.sum := by
        simpa [eps, Low, High] using
          sq_le_sum_zipDiffs_take_drop hCsorted (by rw [hlenC])
      have hLowCell : ∀ z ∈ Low, x ≤ z ∧ (z - x) / H = c := by
        intro z hz
        exact hCcell z (List.mem_of_mem_take hz)
      have hHighCell : ∀ z ∈ High, x ≤ z ∧ (z - x) / H = c := by
        intro z hz
        have hzDrop : z ∈ C.drop s := List.mem_of_mem_take hz
        exact hCcell z (List.mem_of_mem_drop hzDrop)
      have hepsLt : ∀ e ∈ eps, e < H := by
        exact zipDiffs_lt_of_same_cell hH hLowCell hHighCell hlenLH hleLH
      have hepsBound : ∀ e ∈ eps, e ≤ H :=
        fun e he => (hepsLt e he).le
      have hLowResidue : ∀ z ∈ Low, z % μ = w := by
        intro z hz
        have hzC := List.mem_of_mem_take hz
        have hzFull := List.mem_of_mem_take hzC
        have hzCell : z ∈ Cell := by simpa [Cfull] using hzFull
        have hzRest : z ∈ Rest := by
          simpa [Srest] using (Finset.mem_filter.mp hzCell).1
        have hzAres : z ∈ Ares := List.mem_of_mem_drop hzRest
        have hzR : z ∈ R := by simpa [Ares] using hzAres
        exact (Finset.mem_filter.mp hzR).2
      have hHighResidue : ∀ z ∈ High, z % μ = w := by
        intro z hz
        have hzDrop : z ∈ C.drop s := List.mem_of_mem_take hz
        have hzC := List.mem_of_mem_drop hzDrop
        have hzFull := List.mem_of_mem_take hzC
        have hzCell : z ∈ Cell := by simpa [Cfull] using hzFull
        have hzRest : z ∈ Rest := by
          simpa [Srest] using (Finset.mem_filter.mp hzCell).1
        have hzAres : z ∈ Ares := List.mem_of_mem_drop hzRest
        have hzR : z ∈ R := by simpa [Ares] using hzAres
        exact (Finset.mem_filter.mp hzR).2
      have hepsDiv : ∀ e ∈ eps, μ ∣ e :=
        zipDiffs_dvd hLowResidue hHighResidue
      have hTResidue : ∀ z ∈ Tsrc, z % μ = w := by
        intro z hz
        have hzAres := List.mem_of_mem_take hz
        have hzR : z ∈ R := by simpa [Ares] using hzAres
        exact (Finset.mem_filter.mp hzR).2
      have hTBound : ∀ z ∈ Tsrc, z ≤ 2 * x := by
        intro z hz
        have hzAres := List.mem_of_mem_take hz
        have hzR : z ∈ R := by simpa [Ares] using hzAres
        have hzS₂ := (Finset.mem_filter.mp hzR).1
        have hzP₂ : z ∈ P₂ := by simpa [S₂] using hzS₂
        exact (hblock z (hmemP₂ z hzP₂)).2.2.le
      let ts := tauSums (m := m) hcop hμne Tsrc
      have hlenTs : ts.length = (binaryWeights m).length := by
        rw [length_binaryWeights]
        simpa [ts, hlenTsrc] using
          length_tauSums (m := m) hcop hμne (A := Tsrc) (by rw [hlenTsrc])
      have hmodTs : ∀ i (hi : i < ts.length),
          ts[i] % μ = (binaryWeights m)[i] % μ := by
        intro i hi
        have hpow := tauSums_mod (m := m) hcop hμne hTResidue
          (by rw [hlenTsrc]) hi
        rw [getElem_binaryWeights (by simpa [hlenTs] using hi)]
        exact hpow
      have htsTerm : ∀ z ∈ ts, z ≤ (μ - 1) * (2 * x) := by
        intro z hz
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
        exact tauSums_le (m := m) hcop hμne hTBound
          (by rw [hlenTsrc]) hi
      have htsSum₁ : ts.sum ≤ ts.length * ((μ - 1) * (2 * x)) :=
        sum_le_length_mul_of_bound htsTerm
      have htsLen : ts.length = m := by simpa using hlenTs
      have hmMuPred : m * (μ - 1) ≤ G * G := by
        exact Nat.mul_le_mul hmG.le (by omega)
      have htsSum : ts.sum ≤ 2 * x * (G * G) := by
        rw [htsLen] at htsSum₁
        calc
          ts.sum ≤ m * ((μ - 1) * (2 * x)) := htsSum₁
          _ = 2 * x * (m * (μ - 1)) := by ring
          _ ≤ 2 * x * (G * G) := Nat.mul_le_mul_left _ hmMuPred
      have hmass : ts.sum + 4 * x < eps.sum := by
        exact lt_of_le_of_lt (Nat.add_le_add_right htsSum _) <|
          hmassNumerical.trans_le hepsMass
      have hCsplit : Low ++ High = C := by
        have htakeDrop := List.take_append_drop s C
        have hdropLen : (C.drop s).length = s := by
          rw [List.length_drop, hlenC, two_mul, Nat.add_sub_cancel_left]
        have htakeDropEq : (C.drop s).take s = C.drop s := by
          exact (List.take_eq_self_iff _).2 (by rw [hdropLen])
        simpa [Low, High, htakeDropEq] using htakeDrop
      have hepsRep : RepresentsTranslate C eps := by
        rw [← hCsplit]
        exact zipDiffs_represents hlenLH hleLH
      have hCsubsetRest : ∀ z ∈ C, z ∈ Rest := by
        intro z hz
        have hzFull := List.mem_of_mem_take hz
        have hzCell : z ∈ Cell := by simpa [Cfull] using hzFull
        simpa [Srest] using (Finset.mem_filter.mp hzCell).1
      have hCsubperm : C.Subperm Rest := hCNodup.subperm hCsubsetRest
      have hTCsubperm : (Tsrc ++ C).Subperm (Tsrc ++ Rest) :=
        (List.Subperm.refl Tsrc).append hCsubperm
      have hTCRsubperm : (Tsrc ++ C).Subperm Ares := by
        simpa [Tsrc, Rest] using hTCsubperm
      have hTCnodup : (Tsrc ++ C).Nodup := by
        rw [List.subperm_iff] at hTCRsubperm
        obtain ⟨Z, hZAres, hTCZ⟩ := hTCRsubperm
        have hZnodup : Z.Nodup := hAresNodup.perm hZAres.symm
        exact hZnodup.sublist hTCZ
      have hAresP₂ : ∀ z ∈ Ares, z ∈ P₂ := by
        intro z hz
        have hzR : z ∈ R := by simpa [Ares] using hz
        have hzS₂ := (Finset.mem_filter.mp hzR).1
        simpa [S₂] using hzS₂
      have hTCsubsetP₂ : ∀ z ∈ Tsrc ++ C, z ∈ P₂ := by
        intro z hz
        rcases List.mem_append.mp hz with hzT | hzC
        · exact hAresP₂ z (List.mem_of_mem_take hzT)
        · exact hAresP₂ z (List.mem_of_mem_drop (hCsubsetRest z hzC))
      have hselectRep : RepresentsTranslate P₂ (Tsrc ++ C) :=
        RepresentsTranslate.of_nodup_subset hTCnodup hTCsubsetP₂
      have htauRep : RepresentsTranslate Tsrc ts := by
        simpa [ts] using tauSums_represents (m := m) hcop hμne Tsrc
      have hP₂rep : RepresentsTranslate P₂ (eps ++ ts) := by
        have hforward : RepresentsTranslate (Tsrc ++ C) (ts ++ eps) :=
          htauRep.append hepsRep
        exact (hselectRep.trans hforward).perm_right List.perm_append_comm
      have hLsplit : P₁ ++ P₂ = L := by
        simpa [P₁, P₂] using List.take_append_drop k L
      have hsourceRep : RepresentsTranslate L
          (List.replicate qTotal μ ++ (eps ++ ts)) := by
        rw [← hLsplit]
        have hP₁rep' : RepresentsTranslate P₁ (List.replicate qTotal μ) := by
          simpa [hP₁eq] using hP₁rep
        exact hP₁rep'.append hP₂rep
      let residuals := subtractionResiduals (allocateUnder ts eps) ts
      let qs := residuals.map (fun r => r / μ)
      have hresLen : residuals.length = ts.length := by
        exact length_subtractionResiduals (length_allocateUnder ts eps)
      have hresBound : ∀ r ∈ residuals, r < H := by
        exact (allocation_residuals_bounded hmass hepsBound).2.1
      have hqsTerm : ∀ z ∈ qs, z ≤ H := by
        intro z hz
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
        exact (Nat.div_le_self r μ).trans (hresBound r hr).le
      have hqsLen : qs.length = m := by simp [qs, hresLen, htsLen]
      have hqsSum₁ : qs.sum ≤ qs.length * H :=
        sum_le_length_mul_of_bound hqsTerm
      have hqsSum : qs.sum ≤ G * H := by
        rw [hqsLen] at hqsSum₁
        exact hqsSum₁.trans (Nat.mul_le_mul_right H hmG.le)
      have hqsTotal : qs.sum ≤ qTotal := by
        apply hqsSum.trans
        have : G * H ≤ (G + 1) * H := Nat.mul_le_mul_right H (by omega)
        exact this.trans hqRoom
      have henough : H ≤ (2 ^ m - 1) + (qTotal - qs.sum) * μ + 1 := by
        have hGHplus : G * H + H = (G + 1) * H := by ring
        have hHrem : H ≤ qTotal - qs.sum := by omega
        have hmul : H ≤ (qTotal - qs.sum) * μ := by
          calc
            H ≤ (qTotal - qs.sum) * 1 := by simpa using hHrem
            _ ≤ (qTotal - qs.sum) * μ := Nat.mul_le_mul_left _ (by omega)
        omega
      let cert : DenseCompressionCertificate L x :=
        denseCompressionCertificate_of_allocation
          hlenTs hmodTs hepsDiv hepsBound hmass hsourceRep
          (binaryWeights_lt_clog μ) (le_two_pow_clog μ)
          (by simpa [qs, residuals] using hqsTotal)
          (by simpa [qs, residuals] using henough)
      exact weakDenseBlock_of_certificate cert

/-! The concrete dyadic parameters.  Exponents are chosen with generous
slack; no explicit optimization is needed for an existence theorem. -/

def denseG (t : ℕ) : ℕ := t ^ 2
def denseK (t : ℕ) : ℕ := 2 ^ (t / 4)
def denseH (t : ℕ) : ℕ := 2 ^ (t - t / 4)
def denseS (t : ℕ) : ℕ := 2 ^ (t / 2) * t ^ 3
def denseQ (t : ℕ) : ℕ := (denseG t + 1) * denseH t
def denseM (t : ℕ) : ℕ :=
  denseG t * denseG t + denseK t * (2 * denseS t)

def denseCardThreshold (t : ℕ) : ℕ :=
  let x := 2 ^ t
  let a := x + denseG t * (denseG t * denseQ t)
  4 * (a / denseG t + 1) + 2 * denseG t * denseM t

/-- The completion stage also needs quadratically many unused pairs.  This
extra sublinear term guarantees that reserve while retaining a summable
dyadic density. -/
def richCardThreshold (t : ℕ) : ℕ :=
  max (denseCardThreshold t + 1) (8 * 2 ^ (3 * (t / 4)) + 4)

lemma div_roundup_mul_ge {a g : ℕ} (hg : 0 < g) :
    a ≤ g * (a / g + 1) := by
  have hdecomp := Nat.div_add_mod a g
  have hmod := Nat.mod_lt a hg
  calc
    a = g * (a / g) + a % g := hdecomp.symm
    _ ≤ g * (a / g) + g := Nat.add_le_add_left hmod.le _
    _ = g * (a / g + 1) := by ring

lemma dense_card_inequalities {t : ℕ} {P : Finset ℕ}
    (hG : 0 < denseG t)
    (hcard : denseCardThreshold t < P.card) :
    2 ^ t + denseG t * (denseG t * denseQ t) ≤
        denseG t * ((P.card / 2) / 2) ∧
      denseG t * denseM t ≤ P.card - P.card / 2 := by
  let a := 2 ^ t + denseG t * (denseG t * denseQ t)
  let b := a / denseG t + 1
  have hthreshold : denseCardThreshold t =
      4 * b + 2 * denseG t * denseM t := by
    simp [denseCardThreshold, a, b]
  have h4b : 4 * b < P.card := by
    rw [hthreshold] at hcard
    exact (Nat.le_add_right _ _).trans_lt hcard
  have hb : b ≤ P.card / 4 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
    simpa [Nat.mul_comm] using h4b.le
  have ha : a ≤ denseG t * b := div_roundup_mul_ge hG
  have hfirst4 : a ≤ denseG t * (P.card / 4) :=
    ha.trans (Nat.mul_le_mul_left _ hb)
  have hfirst : a ≤ denseG t * ((P.card / 2) / 2) := by
    have hdivEq : (P.card / 2) / 2 = P.card / 4 := by
      rw [Nat.div_div_eq_div_mul]
    rw [hdivEq]
    exact hfirst4
  have h2gm : 2 * (denseG t * denseM t) < P.card := by
    rw [hthreshold] at hcard
    have hle : 2 * (denseG t * denseM t) ≤
        4 * b + 2 * denseG t * denseM t := by
      simpa [Nat.mul_assoc] using
        (Nat.le_add_left (2 * denseG t * denseM t) (4 * b))
    simpa [Nat.mul_assoc] using hle.trans_lt hcard
  have hhalf : denseG t * denseM t ≤ P.card / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h2gm.le
  have hceil : P.card / 2 ≤ P.card - P.card / 2 := by omega
  exact ⟨hfirst, hhalf.trans hceil⟩

/-- A block exceeding the explicit threshold is weakly dense once the six
parameter-only inequalities hold. -/
lemma weakDenseBlock_of_card_threshold {t : ℕ} {P : Finset ℕ}
    (hblock : PrimeBlock (2 ^ t) P)
    (htwo : 3 ≤ 2 ^ t)
    (hG2 : 2 ≤ denseG t) (hGx : denseG t ≤ 2 ^ t)
    (hxKH : 2 ^ t ≤ denseK t * denseH t)
    (hs : 0 < denseS t)
    (hmass : 2 * 2 ^ t * (denseG t * denseG t) + 4 * 2 ^ t <
      denseS t ^ 2)
    (hcard : denseCardThreshold t < P.card) :
    WeakDenseBlock (2 ^ t) P := by
  have hGpos : 0 < denseG t := by omega
  obtain ⟨hroom, hresidue⟩ := dense_card_inequalities hGpos hcard
  have hKpos : 0 < denseK t := by
    exact pow_pos (by norm_num) _
  have hHpos : 0 < denseH t := by
    exact pow_pos (by norm_num) _
  have hQpos : 0 < denseQ t := by
    rw [denseQ]
    exact Nat.mul_pos (by omega) hHpos
  apply weakDenseBlock_of_parameters hblock htwo hG2 hGx
    hQpos hroom hresidue
    (by simp [denseM]) hKpos hHpos hxKH hs hmass
  simp [denseQ]

/-- The elementary estimate `t² ≤ 2ᵗ` from the first useful dyadic
scale onward. -/
lemma sq_le_two_pow {t : ℕ} (ht : 4 ≤ t) : t ^ 2 ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
      have hmul : 4 * t ≤ t * t := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left t ht
      have hsmall : 2 * t + 1 ≤ t ^ 2 := by
        have hlin : 2 * t + 1 ≤ 4 * t := by omega
        exact hlin.trans (by simpa [pow_two, Nat.mul_comm] using hmul)
      calc
        (t + 1) ^ 2 = t ^ 2 + (2 * t + 1) := by ring
        _ ≤ t ^ 2 + t ^ 2 := Nat.add_le_add_left hsmall _
        _ ≤ 2 ^ t + 2 ^ t := Nat.add_le_add ih ih
        _ = 2 ^ (t + 1) := by rw [Nat.pow_succ]; ring

lemma denseK_mul_denseH (t : ℕ) : denseK t * denseH t = 2 ^ t := by
  rw [denseK, denseH, ← Nat.pow_add]
  congr 1
  omega

lemma two_pow_le_twice_half_pow (t : ℕ) :
    2 ^ t ≤ 2 * 2 ^ (2 * (t / 2)) := by
  have he : t ≤ 2 * (t / 2) + 1 := by omega
  have hp := Nat.pow_le_pow_right (by norm_num : 0 < 2) he
  rw [Nat.pow_add, pow_one] at hp
  simpa [Nat.mul_comm] using hp

/-- The quadratic-error budget in the dense-block construction is dominated
by the chosen square-root-scale reservoir. -/
lemma dense_mass_inequality {t : ℕ} (ht : 4 ≤ t) :
    2 * 2 ^ t * (denseG t * denseG t) + 4 * 2 ^ t < denseS t ^ 2 := by
  have hp := two_pow_le_twice_half_pow t
  have hpoly : 4 * t ^ 4 + 8 < t ^ 6 := by
    have ht2 : 16 ≤ t ^ 2 := by
      exact Nat.pow_le_pow_left ht 2
    have htpos : 0 < t := by omega
    have ht4 : 1 ≤ t ^ 4 := pow_pos htpos _
    have h16 : 16 * t ^ 4 ≤ t ^ 6 := by
      calc
        16 * t ^ 4 = t ^ 4 * 16 := by ring
        _ ≤ t ^ 4 * t ^ 2 := Nat.mul_le_mul_left _ ht2
        _ = t ^ 6 := by ring
    omega
  have hbase : 0 < 2 ^ (2 * (t / 2)) := pow_pos (by norm_num) _
  rw [denseG, denseS, mul_pow]
  have hpowSq : (2 ^ (t / 2)) ^ 2 = 2 ^ (2 * (t / 2)) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hpowSq]
  calc
    2 * 2 ^ t * (t ^ 2 * t ^ 2) + 4 * 2 ^ t =
        2 ^ t * (2 * t ^ 4 + 4) := by ring
    _ ≤ (2 * 2 ^ (2 * (t / 2))) * (2 * t ^ 4 + 4) :=
      Nat.mul_le_mul_right _ hp
    _ = 2 ^ (2 * (t / 2)) * (4 * t ^ 4 + 8) := by ring
    _ < 2 ^ (2 * (t / 2)) * t ^ 6 :=
      Nat.mul_lt_mul_of_pos_left hpoly hbase
    _ = 2 ^ (2 * (t / 2)) * (t ^ 3) ^ 2 := by ring

/-- No asymptotic side condition remains in the dense-block lemma after the
fourth dyadic scale. -/
lemma weakDenseBlock_of_card_threshold_ge_four {t : ℕ} {P : Finset ℕ}
    (ht : 4 ≤ t) (hblock : PrimeBlock (2 ^ t) P)
    (hcard : denseCardThreshold t < P.card) :
    WeakDenseBlock (2 ^ t) P := by
  apply weakDenseBlock_of_card_threshold hblock
  · exact (Nat.pow_le_pow_right (by norm_num : 0 < 2) ht).trans' (by norm_num)
  · rw [denseG]
    nlinarith
  · simpa [denseG] using sq_le_two_pow ht
  · rw [denseK_mul_denseH]
  · rw [denseS]
    exact Nat.mul_pos (pow_pos (by norm_num) _) (pow_pos (by omega) _)
  · exact dense_mass_inequality ht
  · exact hcard

/-- One extra point above the weak threshold leaves both a block and any
one-point deletion above that threshold. -/
lemma strongBlockDivisors_cover_of_card_threshold {t p : ℕ} {P : Finset ℕ}
    (ht : 4 ≤ t) (hblock : PrimeBlock (2 ^ t) P) (hp : p ∈ P)
    (hcard : denseCardThreshold t + 1 < P.card) :
    ∃ E F : ℕ, 4 * (2 ^ t) ^ 2 < F ∧
      CoversInterval (strongBlockDivisors p P) E F := by
  have hweak : WeakDenseBlock (2 ^ t) P :=
    weakDenseBlock_of_card_threshold_ge_four ht hblock (by omega)
  have heraseBlock : PrimeBlock (2 ^ t) (P.erase p) := by
    intro q hq
    exact hblock q (Finset.mem_of_mem_erase hq)
  have hcardErase : denseCardThreshold t < (P.erase p).card := by
    rw [Finset.card_erase_of_mem hp]
    omega
  have hweakErase : WeakDenseBlock (2 ^ t) (P.erase p) :=
    weakDenseBlock_of_card_threshold_ge_four ht heraseBlock hcardErase
  exact strongBlockDivisors_cover
    (by exact (Nat.pow_le_pow_right (by norm_num : 0 < 2) ht).trans' (by norm_num))
    hblock hp hweak hweakErase

lemma strongBlockDivisors_cover_of_rich_card {t p : ℕ} {P : Finset ℕ}
    (ht : 4 ≤ t) (hblock : PrimeBlock (2 ^ t) P) (hp : p ∈ P)
    (hcard : richCardThreshold t < P.card) :
    ∃ E F : ℕ, 4 * (2 ^ t) ^ 2 < F ∧
      CoversInterval (strongBlockDivisors p P) E F := by
  apply strongBlockDivisors_cover_of_card_threshold ht hblock hp
  exact (le_max_left _ _).trans_lt hcard

lemma strongBlockDivisors_cover_bounded_of_rich_card {t p : ℕ} {P : Finset ℕ}
    (ht : 4 ≤ t) (hblock : PrimeBlock (2 ^ t) P) (hp : p ∈ P)
    (hcard : richCardThreshold t < P.card) :
    ∃ E F : ℕ, E ≤ ∑ d ∈ strongBlockDivisors p P, d ∧
      4 * (2 ^ t) ^ 2 < F ∧
        CoversInterval (strongBlockDivisors p P) E F := by
  have hdense : denseCardThreshold t < P.card := by
    have h := (le_max_left (denseCardThreshold t + 1)
      (8 * 2 ^ (3 * (t / 4)) + 4)).trans_lt hcard
    omega
  have hweak : WeakDenseBlock (2 ^ t) P :=
    weakDenseBlock_of_card_threshold_ge_four ht hblock hdense
  have heraseBlock : PrimeBlock (2 ^ t) (P.erase p) := by
    intro q hq
    exact hblock q (Finset.mem_of_mem_erase hq)
  have hcardErase : denseCardThreshold t < (P.erase p).card := by
    rw [Finset.card_erase_of_mem hp]
    have := (le_max_left (denseCardThreshold t + 1)
      (8 * 2 ^ (3 * (t / 4)) + 4)).trans_lt hcard
    omega
  have hweakErase : WeakDenseBlock (2 ^ t) (P.erase p) :=
    weakDenseBlock_of_card_threshold_ge_four ht heraseBlock hcardErase
  exact strongBlockDivisors_cover_bounded
    (by exact (Nat.pow_le_pow_right (by norm_num : 0 < 2) ht).trans' (by norm_num))
    hblock hp hweak hweakErase

/-- The extra rich-block term leaves at least `2x` pairs even after deleting
the prime used in the strong seed. -/
lemma choose_two_erase_ge_two_pow {t p : ℕ} {P : Finset ℕ}
    (ht : 12 ≤ t) (hp : p ∈ P)
    (hcard : richCardThreshold t < P.card) :
    8 * 2 ^ t ≤ (P.erase p).card.choose 2 := by
  let y := 2 ^ (3 * (t / 4))
  have hq : 3 ≤ t / 4 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2 (by omega)
  have htexp : t ≤ 6 * (t / 4) := by
    have hrem := Nat.mod_lt t (by norm_num : 0 < 4)
    have hdecomp := Nat.div_add_mod t 4
    omega
  have hxy : 2 ^ t ≤ y ^ 2 := by
    have hpw := Nat.pow_le_pow_right (by norm_num : 0 < 2) htexp
    change 2 ^ t ≤ (2 ^ (3 * (t / 4))) ^ 2
    rw [← pow_mul]
    convert hpw using 1 <;> ring
  have hlarge : 8 * y + 4 < P.card := by
    exact (le_max_right (denseCardThreshold t + 1)
      (8 * 2 ^ (3 * (t / 4)) + 4)).trans_lt hcard
  have hn : 8 * y + 4 ≤ (P.erase p).card := by
    rw [Finset.card_erase_of_mem hp]
    omega
  rw [Nat.choose_two_right]
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
  have hypos : 0 < y := pow_pos (by norm_num) _
  have hmul : (8 * y + 4) * (8 * y + 3) ≤
      (P.erase p).card * ((P.erase p).card - 1) := by
    apply Nat.mul_le_mul hn
    omega
  have hbase : (8 * 2 ^ t) * 2 ≤ (8 * y + 4) * (8 * y + 3) := by
    nlinarith
  exact hbase.trans hmul

/-- Binomial coefficients between the pair and co-pair layers dominate the
pair layer. -/
lemma choose_two_le_choose_of_two_le_of_le_half {n k : ℕ}
    (h2 : 2 ≤ k) (hk : k ≤ n / 2) :
    n.choose 2 ≤ n.choose k := by
  induction k, h2 using Nat.le_induction with
  | base => rfl
  | succ k hk2 ih =>
      exact (ih (by omega)).trans
        (Nat.choose_le_succ_of_lt_half_left (by omega))

lemma choose_two_le_choose_of_two_le_of_le_sub_two {n k : ℕ}
    (h2 : 2 ≤ k) (hk : k ≤ n - 2) :
    n.choose 2 ≤ n.choose k := by
  have hkn : k ≤ n := hk.trans (Nat.sub_le n 2)
  by_cases hhalf : k ≤ n / 2
  · exact choose_two_le_choose_of_two_le_of_le_half h2 hhalf
  · have hcomp2 : 2 ≤ n - k := by omega
    have hcomphalf : n - k ≤ n / 2 := by omega
    rw [← Nat.choose_symm hkn]
    exact choose_two_le_choose_of_two_le_of_le_half hcomp2 hcomphalf

/-! ### Squarefree product layers in one dyadic block -/

/-- Products of exactly `r` members of `P`. -/
def productLayer (P : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (P.powersetCard r).image (fun S => ∏ p ∈ S, p)

/-- Products distinguish subsets of a finite set of primes. -/
lemma prod_injOn_prime_subsets {P : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) {S | S ⊆ P} := by
  intro A hA B hB hprod
  change (∏ p ∈ A, p) = (∏ p ∈ B, p) at hprod
  ext p
  constructor
  · intro hpA
    have pp := hprime p (hA hpA)
    have hpdvd : p ∣ ∏ q ∈ B, q := by
      rw [← hprod]
      exact Finset.dvd_prod_of_mem (fun q => q) hpA
    obtain ⟨q, hqB, hpq⟩ :=
      (Prime.dvd_finsetProd_iff pp.prime (fun q : ℕ => q)).mp hpdvd
    have pq : q.Prime := hprime q (hB hqB)
    have : p = q := (Nat.prime_dvd_prime_iff_eq pp pq).mp hpq
    simpa [this] using hqB
  · intro hpB
    have pp := hprime p (hB hpB)
    have hpdvd : p ∣ ∏ q ∈ A, q := by
      rw [hprod]
      exact Finset.dvd_prod_of_mem (fun q => q) hpB
    obtain ⟨q, hqA, hpq⟩ :=
      (Prime.dvd_finsetProd_iff pp.prime (fun q : ℕ => q)).mp hpdvd
    have pq : q.Prime := hprime q (hA hqA)
    have : p = q := (Nat.prime_dvd_prime_iff_eq pp pq).mp hpq
    simpa [this] using hqA

lemma card_productLayer {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime) (r : ℕ) :
    (productLayer P r).card = P.card.choose r := by
  rw [productLayer, Finset.card_image_iff.mpr]
  · exact Finset.card_powersetCard r P
  · intro A hA B hB h
    apply prod_injOn_prime_subsets hprime
    · exact (Finset.mem_powersetCard.mp hA).1
    · exact (Finset.mem_powersetCard.mp hB).1
    · exact h

lemma card_productLayer_ge_choose_two_of_interior {P : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) {r : ℕ}
    (h2 : 2 ≤ r) (hr : r ≤ P.card - 2) :
    P.card.choose 2 ≤ (productLayer P r).card := by
  rw [card_productLayer hprime]
  exact choose_two_le_choose_of_two_le_of_le_sub_two h2 hr

lemma card_productLayer_ge_rich_reserve {t p : ℕ} {P : Finset ℕ}
    (ht : 12 ≤ t) (hprime : ∀ q ∈ P, q.Prime) (hp : p ∈ P)
    (hcard : richCardThreshold t < P.card) {r : ℕ}
    (h2 : 2 ≤ r) (hr : r ≤ P.card - 2) :
    8 * 2 ^ t ≤ (productLayer P r).card := by
  exact (choose_two_erase_ge_two_pow ht hp hcard).trans
    ((Nat.choose_le_choose 2 (Finset.card_le_card (Finset.erase_subset p P))).trans
      (card_productLayer_ge_choose_two_of_interior hprime h2 hr))

lemma productLayer_bounds {P : Finset ℕ} {x r d : ℕ}
    (hP : ∀ p ∈ P, x ≤ p ∧ p ≤ 2 * x)
    (hd : d ∈ productLayer P r) : x ^ r ≤ d ∧ d ≤ (2 * x) ^ r := by
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hd
  have hScard := (Finset.mem_powersetCard.mp hS).2
  constructor
  · calc
      x ^ r = ∏ _p ∈ S, x := by simp [hScard]
      _ ≤ ∏ p ∈ S, p := by
        apply Finset.prod_le_prod
        · intro p hp; omega
        · intro p hp
          exact (hP p ((Finset.mem_powersetCard.mp hS).1 hp)).1
  · calc
      (∏ p ∈ S, p) ≤ ∏ _p ∈ S, 2 * x := by
        apply Finset.prod_le_prod
        · intro p hp; omega
        · intro p hp
          exact (hP p ((Finset.mem_powersetCard.mp hS).1 hp)).2
      _ = (2 * x) ^ r := by simp [hScard]

/-- If two equal-cardinality positive finsets have ordered products, one
factor can be exchanged for a strictly larger factor. -/
lemma exists_swap_gt_of_prod_lt {A B : Finset ℕ}
    (hcard : A.card = B.card) (hposA : ∀ a ∈ A, 0 < a)
    (hprod : (∏ a ∈ A, a) < ∏ b ∈ B, b) :
    ∃ a ∈ A \ B, ∃ b ∈ B \ A, a < b := by
  let C := A ∩ B
  have hCA : C ⊆ A := Finset.inter_subset_left
  have hCB : C ⊆ B := Finset.inter_subset_right
  have hdecompA : (∏ a ∈ A \ B, a) * ∏ c ∈ C, c = ∏ a ∈ A, a := by
    have h := Finset.prod_sdiff hCA (f := fun a : ℕ => a)
    simpa [C, Finset.sdiff_inter_self] using h
  have hdecompB : (∏ b ∈ B \ A, b) * ∏ c ∈ C, c = ∏ b ∈ B, b := by
    have h := Finset.prod_sdiff hCB (f := fun a : ℕ => a)
    simpa [C, Finset.sdiff_inter_self, Finset.inter_comm] using h
  have hCpos : 0 < ∏ c ∈ C, c := by
    apply Finset.prod_pos
    intro c hc
    exact hposA c (hCA hc)
  have hdiff : (∏ a ∈ A \ B, a) < ∏ b ∈ B \ A, b := by
    apply (Nat.mul_lt_mul_right hCpos).mp
    rw [hdecompA, hdecompB]
    exact hprod
  have hcardDiff : (A \ B).card = (B \ A).card := by
    rw [Finset.card_sdiff, Finset.card_sdiff, Finset.inter_comm]
    omega
  let e : ↑(A \ B) ≃ ↑(B \ A) := Fintype.equivOfCardEq (by simpa using hcardDiff)
  by_contra hnot
  push Not at hnot
  have heLe : ∀ a : ↑(A \ B), (e a : ℕ) ≤ a := by
    intro a
    exact hnot a a.2 (e a) (e a).2
  have hprodLe : (∏ b ∈ B \ A, b) ≤ ∏ a ∈ A \ B, a := by
    calc
      (∏ b ∈ B \ A, b) = ∏ b : ↑(B \ A), (b : ℕ) := by
        simpa using (Finset.prod_attach (B \ A) (fun b : ℕ => b)).symm
      _ = ∏ a : ↑(A \ B), (e a : ℕ) := by
        exact (e.prod_comp (fun b : ↑(B \ A) => (b : ℕ))).symm
      _ ≤ ∏ a : ↑(A \ B), (a : ℕ) := by
        apply Finset.prod_le_prod
        · intro a ha
          exact Nat.zero_le _
        · intro a ha
          exact heLe a
      _ = ∏ a ∈ A \ B, a := by
        simpa using Finset.prod_attach (A \ B) (fun a : ℕ => a)
  omega

/-- Above any product in a fixed layer there is another layer product less
than twice as large. -/
lemma exists_productLayer_gt_lt_two {P : Finset ℕ} {x r d e : ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hP : ∀ p ∈ P, x ≤ p ∧ p < 2 * x)
    (hd : d ∈ productLayer P r) (he : e ∈ productLayer P r)
    (hde : d < e) :
    ∃ c ∈ productLayer P r, d < c ∧ c < 2 * d := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨B, hB, hprodB⟩ := Finset.mem_image.mp he
  have hASub := (Finset.mem_powersetCard.mp hA).1
  have hBSub := (Finset.mem_powersetCard.mp hB).1
  have hACard := (Finset.mem_powersetCard.mp hA).2
  have hBCard := (Finset.mem_powersetCard.mp hB).2
  have hlt : (∏ p ∈ A, p) < ∏ p ∈ B, p := by simpa [hprodB] using hde
  obtain ⟨a, haDiff, b, hbDiff, hab⟩ :=
    exists_swap_gt_of_prod_lt (hACard.trans hBCard.symm)
      (fun p hp => (hprime p (hASub hp)).pos) hlt
  have haA : a ∈ A := (Finset.mem_sdiff.mp haDiff).1
  have hbB : b ∈ B := (Finset.mem_sdiff.mp hbDiff).1
  have hbA : b ∉ A := (Finset.mem_sdiff.mp hbDiff).2
  have hrpos : 0 < r := by
    rw [← hACard]
    exact Finset.card_pos.mpr ⟨a, haA⟩
  let C := Insert.insert b (A.erase a)
  have hbErase : b ∉ A.erase a := by simp [hbA]
  have hCSub : C ⊆ P := by
    intro p hp
    change p ∈ Insert.insert b (A.erase a) at hp
    rw [Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · exact hBSub hbB
    · exact hASub (Finset.mem_of_mem_erase hp)
  have hCCard : C.card = r := by
    dsimp [C]
    rw [Finset.card_insert_of_notMem hbErase, Finset.card_erase_of_mem haA,
      hACard]
    omega
  have hCmem : C ∈ P.powersetCard r :=
    Finset.mem_powersetCard.mpr ⟨hCSub, hCCard⟩
  have hrestPos : 0 < ∏ p ∈ A.erase a, p := by
    apply Finset.prod_pos
    intro p hp
    exact (hprime p (hASub (Finset.mem_of_mem_erase hp))).pos
  have hprodA : ∏ p ∈ A, p = a * ∏ p ∈ A.erase a, p := by
    rw [← Finset.prod_erase_mul _ _ haA]
    ring
  have hprodC : ∏ p ∈ C, p = b * ∏ p ∈ A.erase a, p := by
    dsimp [C]
    rw [Finset.prod_insert hbErase]
  have hbTwoA : b < 2 * a :=
    (hP b (hBSub hbB)).2.trans_le (Nat.mul_le_mul_left 2 (hP a (hASub haA)).1)
  refine ⟨∏ p ∈ C, p, Finset.mem_image.mpr ⟨C, hCmem, rfl⟩, ?_, ?_⟩
  · rw [hprodA, hprodC]
    exact Nat.mul_lt_mul_right hrestPos |>.mpr hab
  · rw [hprodA, hprodC]
    calc
      b * ∏ p ∈ A.erase a, p < (2 * a) * ∏ p ∈ A.erase a, p :=
        Nat.mul_lt_mul_right hrestPos |>.mpr hbTwoA
      _ = 2 * (a * ∏ p ∈ A.erase a, p) := by ring

/-- Adjacent entries of a list differ by a factor below two. -/
def FactorTwoChain (L : List ℕ) : Prop :=
  ∀ i (hi : i + 1 < L.length), L[i + 1] < 2 * L[i]'(by omega)

def productLayerList (P : Finset ℕ) (r : ℕ) : List ℕ :=
  (productLayer P r).sort (· ≤ ·)

lemma productLayerList_nodup (P : Finset ℕ) (r : ℕ) :
    (productLayerList P r).Nodup := Finset.sort_nodup _ _

lemma mem_productLayerList {P : Finset ℕ} {r d : ℕ} :
    d ∈ productLayerList P r ↔ d ∈ productLayer P r := by
  simp [productLayerList]

/-- Sorting a fixed-cardinality layer of a dyadic prime block produces a
factor-two chain. -/
lemma productLayerList_factorTwo {P : Finset ℕ} {x r : ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hP : ∀ p ∈ P, x ≤ p ∧ p < 2 * x) :
    FactorTwoChain (productLayerList P r) := by
  intro i hi
  let L := productLayerList P r
  change i + 1 < L.length at hi
  have hi0 : i < L.length := by omega
  have hi1 : i + 1 < L.length := hi
  have hmem0 : L[i] ∈ productLayer P r := by
    have hm : L[i] ∈ L := List.getElem_mem hi0
    change L[i] ∈ (productLayer P r).sort (· ≤ ·) at hm
    exact (Finset.mem_sort (· ≤ ·)).mp hm
  have hmem1 : L[i + 1] ∈ productLayer P r := by
    have hm : L[i + 1] ∈ L := List.getElem_mem hi1
    change L[i + 1] ∈ (productLayer P r).sort (· ≤ ·) at hm
    exact (Finset.mem_sort (· ≤ ·)).mp hm
  have hsortedLe : L.Pairwise (· ≤ ·) := by
    simpa [L, productLayerList] using
      (Finset.pairwise_sort (productLayer P r) (· ≤ ·))
  have hnodup : L.Nodup := by
    simpa [L, productLayerList] using
      (Finset.sort_nodup (productLayer P r) (· ≤ ·))
  have hsorted : L.Pairwise (· < ·) :=
    hsortedLe.sortedLE.sortedLT_of_nodup hnodup |>.pairwise
  have h01 : L[i] < L[i + 1] :=
    (List.pairwise_iff_getElem.mp hsorted) i (i + 1) hi0 hi1 (by omega)
  obtain ⟨c, hcLayer, hc0, hc2⟩ :=
    exists_productLayer_gt_lt_two hprime hP hmem0 hmem1 h01
  have hcL : c ∈ L := by simpa [L, productLayerList] using hcLayer
  obtain ⟨j, hj, hcj⟩ := List.getElem_of_mem hcL
  have hij : i + 1 ≤ j := by
    by_contra hnot
    have hji : j ≤ i := by omega
    have hjle : L[j] ≤ L[i] := by
      rcases hji.eq_or_lt with rfl | hlt
      · exact le_rfl
      · exact (List.pairwise_iff_getElem.mp hsorted) j i hj hi0 hlt |>.le
    rw [hcj] at hjle
    omega
  have hle : L[i + 1] ≤ c := by
    rcases hij.eq_or_lt with heq | hlt
    · subst j
      simpa [hcj]
    · have hbc := (List.pairwise_iff_getElem.mp hsorted) (i + 1) j hi1 hj hlt
      simpa [hcj] using hbc.le
  exact hle.trans_lt hc2

/-- The condition needed at the first entry of a factor-two chain. -/
def FirstLe (F : ℕ) : List ℕ → Prop
  | [] => True
  | a :: _ => a ≤ F + 1

/-- A factor-two chain whose first term fits the current interval is a slow
extension. -/
lemma slowExtension_of_factorTwo {F : ℕ} {L : List ℕ}
    (hfirst : FirstLe F L) (hchain : FactorTwoChain L) :
    SlowExtension F L := by
  induction L generalizing F with
  | nil => trivial
  | cons a L ih =>
      constructor
      · exact hfirst
      · cases L with
        | nil => trivial
        | cons b L =>
            apply ih
            · change b ≤ F + a + 1
              have ha : a ≤ F + 1 := hfirst
              have hab : b < 2 * a := by simpa using hchain 0 (by simp)
              omega
            · intro i hi
              have hall := hchain (i + 1) (by simp at hi ⊢; omega)
              simpa [Nat.add_assoc] using hall

lemma FactorTwoChain.map_mul_left {L : List ℕ} {k : ℕ}
    (hk : 0 < k) (hL : FactorTwoChain L) :
    FactorTwoChain (L.map (fun d => k * d)) := by
  intro i hi
  have hi' : i + 1 < L.length := by simpa using hi
  have h := hL i hi'
  simp only [List.length_map, List.getElem_map] at hi ⊢
  nlinarith

lemma FirstLe.map_mul_left {F : ℕ} {L : List ℕ} {k : ℕ}
    (hfirst : FirstLe F L) (hk : ∀ a ∈ L, k * a ≤ F + 1) :
    FirstLe F (L.map (fun d => k * d)) := by
  cases L with
  | nil => trivial
  | cons a L =>
      exact hk a (by simp)

lemma card_mul_le_sum_of_le {S : Finset ℕ} {a : ℕ}
    (hS : ∀ s ∈ S, a ≤ s) : S.card * a ≤ ∑ s ∈ S, s := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
      have hxLower : a ≤ x := hS x (by simp)
      have htail : S.card * a ≤ ∑ s ∈ S, s := by
        apply ih
        intro s hs
        exact hS s (by simp [hs])
      simp only [Finset.card_insert_of_notMem hx, Finset.sum_insert hx, Nat.succ_mul]
      omega

def baseProductLayers (P : Finset ℕ) : Finset ℕ :=
  productLayer P 1 ∪ productLayer P 2

@[simp] lemma productLayer_one (P : Finset ℕ) : productLayer P 1 = P := by
  ext d
  constructor
  · intro hd
    obtain ⟨S, hS, hdS⟩ := Finset.mem_image.mp hd
    obtain ⟨q, hSq⟩ := Finset.card_eq_one.mp
      (Finset.mem_powersetCard.mp hS).2
    have hqP : q ∈ P := (Finset.mem_powersetCard.mp hS).1 (by rw [hSq]; simp)
    have hqd : q = d := by simpa [hSq] using hdS
    simpa [← hqd] using hqP
  · intro hd
    apply Finset.mem_image.mpr
    exact ⟨{d}, Finset.mem_powersetCard.mpr ⟨by simpa using hd, by simp⟩, by simp⟩

def baseLayerRest (p : ℕ) (P : Finset ℕ) : Finset ℕ :=
  baseProductLayers P \ strongBlockDivisors p P

lemma strongBlockDivisors_subset_baseProductLayers {p : ℕ} {P : Finset ℕ}
    (hp : p ∈ P) : strongBlockDivisors p P ⊆ baseProductLayers P := by
  intro d hd
  rcases Finset.mem_union.mp hd with hdP | hdProd
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨{d}, Finset.mem_powersetCard.mpr ⟨?_, by simp⟩, by simp⟩
    simpa using hdP
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hdProd
    have hqP := Finset.mem_of_mem_erase hq
    have hqp : q ≠ p := by exact fun h => Finset.ne_of_mem_erase hq h
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨{p, q}, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hp
      · exact hqP
    · have hpq : p ≠ q := hqp.symm
      simp [hpq]
    · have hpq : p ≠ q := hqp.symm
      simp [hpq]

/-- Pairs avoiding the distinguished prime are untouched by the strong seed. -/
lemma productLayer_erase_two_subset_baseLayerRest {p : ℕ} {P : Finset ℕ}
    (hprime : ∀ q ∈ P, q.Prime) (hp : p ∈ P) :
    productLayer (P.erase p) 2 ⊆ baseLayerRest p P := by
  intro d hd
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hd
  have hSsubErase := (Finset.mem_powersetCard.mp hS).1
  have hScard := (Finset.mem_powersetCard.mp hS).2
  have hSsubP : S ⊆ P := hSsubErase.trans (Finset.erase_subset _ _)
  apply Finset.mem_sdiff.mpr
  constructor
  · apply Finset.mem_union_right
    exact Finset.mem_image.mpr
      ⟨S, Finset.mem_powersetCard.mpr ⟨hSsubP, hScard⟩, rfl⟩
  · intro hseed
    rcases Finset.mem_union.mp hseed with hsingle | hpair
    · have hdP : (∏ q ∈ S, q) ∈ P := hsingle
      let T : Finset ℕ := {∏ q ∈ S, q}
      have hTsub : T ⊆ P := by simpa [T] using hdP
      have heq := prod_injOn_prime_subsets hprime hSsubP hTsub (by simp [T])
      have hcardEq := congrArg Finset.card heq
      simp [T, hScard] at hcardEq
    · obtain ⟨q, hqErase, hqEq⟩ := Finset.mem_image.mp hpair
      have hqP := Finset.mem_of_mem_erase hqErase
      have hqp : q ≠ p := fun h => Finset.ne_of_mem_erase hqErase h
      have hpq : p ≠ q := hqp.symm
      let T : Finset ℕ := {p, q}
      have hTsub : T ⊆ P := by
        intro z hz
        simp only [T, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hp
        · exact hqP
      have hprodT : (∏ z ∈ T, z) = p * q := by simp [T, hpq]
      have heq : S = T := by
        apply prod_injOn_prime_subsets hprime hSsubP hTsub
        change (∏ z ∈ S, z) = ∏ z ∈ T, z
        rw [hprodT]
        exact hqEq.symm
      have hpS : p ∈ S := by rw [heq]; simp [T]
      have := hSsubErase hpS
      simp at this

lemma card_baseLayerRest_ge_choose_erase {p : ℕ} {P : Finset ℕ}
    (hprime : ∀ q ∈ P, q.Prime) (hp : p ∈ P) :
    (P.erase p).card.choose 2 ≤ (baseLayerRest p P).card := by
  rw [← card_productLayer (fun q hq => hprime q (Finset.mem_of_mem_erase hq)) 2]
  exact Finset.card_le_card (productLayer_erase_two_subset_baseLayerRest hprime hp)

lemma sum_baseLayerRest_ge {x p : ℕ} {P : Finset ℕ}
    (hprime : ∀ q ∈ P, q.Prime)
    (hblock : ∀ q ∈ P, x ≤ q ∧ q < 2 * x) (hp : p ∈ P) :
    (P.erase p).card.choose 2 * x ^ 2 ≤ ∑ d ∈ baseLayerRest p P, d := by
  have hcard := card_baseLayerRest_ge_choose_erase hprime hp
  have hlower : (baseLayerRest p P).card * x ^ 2 ≤
      ∑ d ∈ baseLayerRest p P, d := by
    apply card_mul_le_sum_of_le
    intro d hd
    have hdData := Finset.mem_sdiff.mp hd
    have hdBase := hdData.1
    rcases Finset.mem_union.mp hdBase with hd1 | hd2
    · exfalso
      apply hdData.2
      apply Finset.mem_union_left
      simpa using hd1
    · exact (productLayer_bounds
          (P := P) (r := 2) (d := d)
          (fun q hq => ⟨(hblock q hq).1, (hblock q hq).2.le⟩) hd2).1
  exact (Nat.mul_le_mul_right (x ^ 2) hcard).trans hlower

lemma sum_baseLayerRest_sort {p : ℕ} {P : Finset ℕ} :
    ((baseLayerRest p P).sort (· ≤ ·)).sum =
      ∑ d ∈ baseLayerRest p P, d := by
  calc
    ((baseLayerRest p P).sort (· ≤ ·)).sum =
        (↑((baseLayerRest p P).sort (· ≤ ·)) : Multiset ℕ).sum := rfl
    _ = (baseLayerRest p P).val.sum := by rw [Finset.sort_eq]
    _ = ∑ d ∈ baseLayerRest p P, d := by simp

lemma baseLayerRest_le_four_sq {x p : ℕ} {P : Finset ℕ}
    (hx : 0 < x) (hP : ∀ q ∈ P, x ≤ q ∧ q < 2 * x) :
    ∀ d ∈ baseLayerRest p P, d ≤ 4 * x ^ 2 := by
  intro d hd
  have hdBase := (Finset.mem_sdiff.mp hd).1
  rcases Finset.mem_union.mp hdBase with hd1 | hd2
  · have hdP : d ∈ P := by simpa using hd1
    have hdx := (hP d hdP).2
    have : 2 * x ≤ 4 * x ^ 2 := by nlinarith
    omega
  · have hb := (productLayer_bounds
        (P := P) (r := 2) (d := d)
        (fun q hq => ⟨(hP q hq).1, (hP q hq).2.le⟩) hd2).2
    calc
      d ≤ (2 * x) ^ 2 := hb
      _ = 4 * x ^ 2 := by ring

lemma productLayer_nonempty {P : Finset ℕ} {r : ℕ} (hr : r ≤ P.card) :
    (productLayer P r).Nonempty := by
  obtain ⟨S, hS⟩ := Finset.powersetCard_nonempty.mpr hr
  exact ⟨∏ p ∈ S, p, Finset.mem_image.mpr ⟨S, hS, rfl⟩⟩

/-- The least product in a fixed layer, with the harmless value zero for an
empty layer. -/
def layerMin (P : Finset ℕ) (r : ℕ) : ℕ :=
  (productLayerList P r).headD 0

lemma layerMin_mem {P : Finset ℕ} {r : ℕ} (hr : r ≤ P.card) :
    layerMin P r ∈ productLayer P r := by
  have hne := productLayer_nonempty (P := P) hr
  cases hL : productLayerList P r with
  | nil =>
      obtain ⟨d, hd⟩ := hne
      have : d ∈ productLayerList P r := by
        simpa [productLayerList] using hd
      simp [hL] at this
  | cons a L =>
      have ha : a ∈ productLayerList P r := by simp [hL]
      have haLayer : a ∈ productLayer P r := by
        simpa [productLayerList] using ha
      have hmin : layerMin P r = a := by simp [layerMin, hL]
      rw [hmin]
      exact haLayer

lemma layerMin_le_of_mem {P : Finset ℕ} {r d : ℕ}
    (hd : d ∈ productLayer P r) : layerMin P r ≤ d := by
  cases hL : productLayerList P r with
  | nil =>
      have : d ∈ productLayerList P r := by simpa [productLayerList] using hd
      simp [hL] at this
  | cons a L =>
      have hdL : d ∈ a :: L := by
        rw [← hL]
        simpa [productLayerList] using hd
      have hsorted : (a :: L).Pairwise (· ≤ ·) := by
        rw [← hL]
        exact Finset.pairwise_sort _ _
      rcases (List.mem_cons.mp hdL) with rfl | hdTail
      · simp [layerMin, hL]
      · have ha := (List.pairwise_cons.mp hsorted).1 d hdTail
        simpa [layerMin, hL] using ha

lemma layerMin_le_dyadic_pow {P : Finset ℕ} {x r : ℕ}
    (hP : ∀ p ∈ P, x ≤ p ∧ p < 2 * x) (hr : r ≤ P.card) :
    layerMin P r ≤ (2 * x) ^ r := by
  exact (productLayer_bounds
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.le⟩)
    (layerMin_mem hr)).2

lemma sum_productLayerList (P : Finset ℕ) (r : ℕ) :
    (productLayerList P r).sum = ∑ d ∈ productLayer P r, d := by
  calc
    (productLayerList P r).sum =
        (↑(productLayerList P r) : Multiset ℕ).sum := rfl
    _ = (productLayer P r).val.sum := by
      rw [productLayerList, Finset.sort_eq]
    _ = ∑ d ∈ productLayer P r, d := by simp

lemma card_mul_layerMin_le_sum {P : Finset ℕ} {r : ℕ} :
    (productLayer P r).card * layerMin P r ≤ (productLayerList P r).sum := by
  rw [sum_productLayerList]
  exact card_mul_le_sum_of_le fun d hd => layerMin_le_of_mem hd

/-- The first entry of the next layer is at most `2x` times the first entry
of the current layer. -/
lemma layerMin_succ_le {P : Finset ℕ} {x r : ℕ}
    (hP : ∀ p ∈ P, p < 2 * x) (hr : r < P.card) :
    layerMin P (r + 1) ≤ 2 * x * layerMin P r := by
  have hm := layerMin_mem (P := P) hr.le
  obtain ⟨S, hS, hprod⟩ := Finset.mem_image.mp hm
  have hSsub := (Finset.mem_powersetCard.mp hS).1
  have hScard := (Finset.mem_powersetCard.mp hS).2
  have hnotSub : ¬ P ⊆ S := by
    intro hPS
    have hc := Finset.card_le_card hPS
    rw [hScard] at hc
    omega
  have hsdiff : (P \ S).Nonempty := Finset.sdiff_nonempty.mpr hnotSub
  obtain ⟨q, hq⟩ := hsdiff
  have hqP' := (Finset.mem_sdiff.mp hq).1
  have hqS' := (Finset.mem_sdiff.mp hq).2
  let T := Insert.insert q S
  have hTsub : T ⊆ P := by
    intro z hz
    change z ∈ Insert.insert q S at hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hqP'
    · exact hSsub hz
  have hTcard : T.card = r + 1 := by
    dsimp [T]
    rw [Finset.card_insert_of_notMem hqS', hScard]
  have hTmem : T ∈ P.powersetCard (r + 1) :=
    Finset.mem_powersetCard.mpr ⟨hTsub, hTcard⟩
  have hprodT : (∏ z ∈ T, z) = q * layerMin P r := by
    dsimp [T]
    rw [Finset.prod_insert hqS', hprod]
  calc
    layerMin P (r + 1) ≤ ∏ z ∈ T, z :=
      layerMin_le_of_mem (Finset.mem_image.mpr ⟨T, hTmem, rfl⟩)
    _ = q * layerMin P r := hprodT
    _ ≤ 2 * x * layerMin P r := Nat.mul_le_mul_right _ (hP q hqP').le

lemma slowExtension_scaled_productLayer {P : Finset ℕ} {x r k F : ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hP : ∀ p ∈ P, x ≤ p ∧ p < 2 * x)
    (hk : 0 < k) (hfirst : k * layerMin P r ≤ F + 1) :
    SlowExtension F ((productLayerList P r).map (fun d => k * d)) := by
  apply slowExtension_of_factorTwo
  · cases hL : productLayerList P r with
    | nil => trivial
    | cons a L =>
        simpa [FirstLe, layerMin, hL] using hfirst
  · exact (productLayerList_factorTwo hprime hP).map_mul_left hk

lemma slowExtension_scaled_productLayer_succ {P : Finset ℕ}
    {x r k F : ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hP : ∀ p ∈ P, x ≤ p ∧ p < 2 * x)
    (hk : 0 < k) (hr : r < P.card)
    (hcard : 2 * x ≤ (productLayer P r).card)
    (hprev : k * (productLayerList P r).sum ≤ F + 1) :
    SlowExtension F
      ((productLayerList P (r + 1)).map (fun d => k * d)) := by
  apply slowExtension_scaled_productLayer hprime hP hk
  have hmin := layerMin_succ_le (fun p hp => (hP p hp).2) hr
  have hmass := card_mul_layerMin_le_sum (P := P) (r := r)
  calc
    k * layerMin P (r + 1) ≤ k * (2 * x * layerMin P r) :=
      Nat.mul_le_mul_left k hmin
    _ ≤ k * ((productLayer P r).card * layerMin P r) := by
      apply Nat.mul_le_mul_left
      exact Nat.mul_le_mul_right _ hcard
    _ ≤ k * (productLayerList P r).sum := Nat.mul_le_mul_left k hmass
    _ ≤ F + 1 := hprev

/-- The consecutive fixed-cardinality layers strictly above `r`, each
scaled by the same multiplier. -/
def productLayerRun (P : Finset ℕ) (k r : ℕ) : ℕ → List ℕ
  | 0 => []
  | m + 1 =>
      (productLayerList P (r + 1)).map (fun d => k * d) ++
        productLayerRun P k (r + 1) m

lemma disjoint_productLayer_of_ne {P : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) {r s : ℕ} (hrs : r ≠ s) :
    Disjoint (productLayer P r) (productLayer P s) := by
  rw [Finset.disjoint_left]
  intro d hdr hds
  obtain ⟨A, hA, hAd⟩ := Finset.mem_image.mp hdr
  obtain ⟨B, hB, hBd⟩ := Finset.mem_image.mp hds
  have hAsub := (Finset.mem_powersetCard.mp hA).1
  have hBsub := (Finset.mem_powersetCard.mp hB).1
  have hAB : A = B := by
    apply prod_injOn_prime_subsets hprime hAsub hBsub
    exact hAd.trans hBd.symm
  apply hrs
  rw [← (Finset.mem_powersetCard.mp hA).2,
    ← (Finset.mem_powersetCard.mp hB).2, hAB]

lemma mem_productLayerRun {P : Finset ℕ} {k r m d : ℕ}
    (hd : d ∈ productLayerRun P k r m) :
    ∃ j, r < j ∧ j ≤ r + m ∧
      ∃ e ∈ productLayer P j, d = k * e := by
  induction m generalizing r with
  | zero => simp [productLayerRun] at hd
  | succ m ih =>
      simp only [productLayerRun, List.mem_append, List.mem_map] at hd
      rcases hd with ⟨e, he, rfl⟩ | hd
      · exact ⟨r + 1, by omega, by omega, e,
          mem_productLayerList.mp he, rfl⟩
      · obtain ⟨j, hj1, hj2, e, he, rfl⟩ := ih hd
        exact ⟨j, by omega, by omega, e, he, rfl⟩

lemma productLayerRun_nodup {P : Finset ℕ} {k r m : ℕ}
    (hk : 0 < k) (hprime : ∀ p ∈ P, p.Prime) :
    (productLayerRun P k r m).Nodup := by
  induction m generalizing r with
  | zero => simp [productLayerRun]
  | succ m ih =>
      rw [productLayerRun, List.nodup_append]
      have hhead :
          (List.map (fun d ↦ k * d) (productLayerList P (r + 1))).Nodup :=
        (productLayerList_nodup P (r + 1)).map fun a b hab ↦
          Nat.eq_of_mul_eq_mul_left hk hab
      refine ⟨hhead, ih (r := r + 1), ?_⟩
      intro d hd e he hde
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
      obtain ⟨j, hj1, hj2, b, hb, hbe⟩ := mem_productLayerRun he
      rw [hbe] at hde
      have hab : a = b := Nat.eq_of_mul_eq_mul_left hk hde
      subst b
      have haLayer := mem_productLayerList.mp ha
      exact (Finset.disjoint_left.mp
        (disjoint_productLayer_of_ne hprime (by omega))) haLayer hb

lemma productLayerRun_lower {P : Finset ℕ} {x k r m d : ℕ}
    (hP : ∀ p ∈ P, x ≤ p ∧ p < 2 * x)
    (hd : d ∈ productLayerRun P k r m) :
    k * x ^ (r + 1) ≤ d := by
  by_cases hx0 : x = 0
  · subst x
    simp
  obtain ⟨j, hj1, hj2, e, he, rfl⟩ := mem_productLayerRun hd
  have heLower := (productLayer_bounds
    (fun p hp ↦ ⟨(hP p hp).1, (hP p hp).2.le⟩) he).1
  have hx : 0 < x := Nat.pos_of_ne_zero hx0
  exact Nat.mul_le_mul_left k
    ((Nat.pow_le_pow_right hx hj1).trans heLower)

lemma mem_productLayerRun_of_mem {P : Finset ℕ} {k r m j d : ℕ}
    (hrj : r < j) (hjm : j ≤ r + m) (hd : d ∈ productLayer P j) :
    k * d ∈ productLayerRun P k r m := by
  induction m generalizing r with
  | zero => omega
  | succ m ih =>
      simp only [productLayerRun, List.mem_append, List.mem_map]
      by_cases hj : j = r + 1
      · left
        exact ⟨d, by simpa [productLayerList, hj] using hd, rfl⟩
      · right
        apply ih (r := r + 1)
        · omega
        · omega

lemma slowExtension_productLayerRun {P : Finset ℕ}
    {x k r m F : ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hP : ∀ p ∈ P, x ≤ p ∧ p < 2 * x)
    (hk : 0 < k) (hr : r + m ≤ P.card)
    (hcard : ∀ j, r ≤ j → j < r + m →
      2 * x ≤ (productLayer P j).card)
    (hprev : k * (productLayerList P r).sum ≤ F + 1) :
    SlowExtension F (productLayerRun P k r m) := by
  induction m generalizing r F with
  | zero => simp [productLayerRun, SlowExtension]
  | succ m ih =>
      rw [productLayerRun, slowExtension_append]
      constructor
      · apply slowExtension_scaled_productLayer_succ hprime hP hk
        · omega
        · exact hcard r (by omega) (by omega)
        · exact hprev
      · apply ih (r := r + 1)
        · omega
        · intro j hjLow hjHigh
          exact hcard j (by omega) (by omega)
        · rw [List.sum_map_mul_left]
          rw [List.map_id']
          omega

lemma slowExtension_productLayerRun_from_first {P : Finset ℕ}
    {x k r m F : ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hP : ∀ p ∈ P, x ≤ p ∧ p < 2 * x)
    (hk : 0 < k) (hr : r + m ≤ P.card)
    (hcard : ∀ j, r + 1 ≤ j → j < r + m →
      2 * x ≤ (productLayer P j).card)
    (hfirst : k * layerMin P (r + 1) ≤ F + 1) :
    SlowExtension F (productLayerRun P k r m) := by
  cases m with
  | zero => simp [productLayerRun, SlowExtension]
  | succ m =>
      rw [productLayerRun, slowExtension_append]
      constructor
      · exact slowExtension_scaled_productLayer hprime hP hk hfirst
      · apply slowExtension_productLayerRun hprime hP hk (r := r + 1)
        · omega
        · intro j hjLow hjHigh
          exact hcard j hjLow (by omega)
        · rw [List.sum_map_mul_left, List.map_id']
          omega

/-- One fixed product layer, multiplied successively by the nonempty prefix
products of a list. -/
def prefixLayerRun (P : Finset ℕ) (r a : ℕ) : List ℕ → List ℕ
  | [] => []
  | q :: qs =>
      (productLayerList P r).map (fun d => (a * q) * d) ++
        prefixLayerRun P r (a * q) qs

lemma prefixLayerRun_lower {P : Finset ℕ} {x r a q : ℕ} {qs : List ℕ}
    (hP : ∀ p ∈ P, x ≤ p ∧ p < 2 * x)
    (hqs : ∀ z ∈ q :: qs, 0 < z) :
    ∀ d ∈ prefixLayerRun P r a (q :: qs), a * q * x ^ r ≤ d := by
  intro d hd
  simp only [prefixLayerRun, List.mem_append, List.mem_map] at hd
  rcases hd with ⟨e, he, rfl⟩ | hd
  · have heLayer := mem_productLayerList.mp he
    have heLower := (productLayer_bounds
      (fun p hp ↦ ⟨(hP p hp).1, (hP p hp).2.le⟩) heLayer).1
    exact Nat.mul_le_mul_left _ heLower
  · cases qs with
    | nil => simp [prefixLayerRun] at hd
    | cons z zs =>
        have htail := prefixLayerRun_lower hP
          (fun y hy ↦ hqs y (by simp [hy])) d hd
        calc
          a * q * x ^ r ≤ (a * q) * z * x ^ r := by
            have hz := hqs z (by simp)
            have hb : a * q ≤ (a * q) * z := by
              calc
                a * q = (a * q) * 1 := by simp
                _ ≤ (a * q) * z := Nat.mul_le_mul_left _ (by omega)
            exact Nat.mul_le_mul_right (x ^ r) hb
          _ ≤ d := htail

lemma prefixLayerRun_upper {P : Finset ℕ} {x r a : ℕ} {qs : List ℕ}
    (hP : ∀ p ∈ P, x ≤ p ∧ p < 2 * x)
    (hqs : ∀ z ∈ qs, 0 < z) :
    ∀ d ∈ prefixLayerRun P r a qs,
      d ≤ a * qs.prod * (2 * x) ^ r := by
  induction qs generalizing a with
  | nil => simp [prefixLayerRun]
  | cons q qs ih =>
      intro d hd
      simp only [prefixLayerRun, List.mem_append, List.mem_map] at hd
      rcases hd with ⟨e, he, rfl⟩ | hd
      · have heUpper := (productLayer_bounds
          (fun p hp ↦ ⟨(hP p hp).1, (hP p hp).2.le⟩)
          (mem_productLayerList.mp he)).2
        have hprod : 1 ≤ qs.prod := List.one_le_prod (fun z hz ↦ hqs z (by simp [hz]))
        calc
          a * q * e ≤ a * q * (2 * x) ^ r := Nat.mul_le_mul_left _ heUpper
          _ ≤ a * (q * qs.prod) * (2 * x) ^ r := by
            apply Nat.mul_le_mul_right
            calc
              a * q = a * (q * 1) := by simp
              _ ≤ a * (q * qs.prod) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hprod)
          _ = a * (q :: qs).prod * (2 * x) ^ r := by simp
      · have ht := ih (a := a * q)
          (fun z hz ↦ hqs z (by simp [hz])) d hd
        simpa [Nat.mul_assoc] using ht

lemma primeFactors_list_prod {L : List ℕ} (hL : L.Nodup)
    (hprime : ∀ p ∈ L, p.Prime) :
    L.prod.primeFactors = L.toFinset := by
  have hprod : L.toFinset.prod id = L.prod := by
    calc
      L.toFinset.prod id = (L.map id).prod := List.prod_toFinset id hL
      _ = L.prod := by simp
  rw [← hprod]
  exact Nat.primeFactors_prod fun p hp ↦ hprime p (by simpa using hp)

lemma blockPrimeFactors_mul_productLayer {P : Finset ℕ} {k r d : ℕ}
    (hk : 0 < k) (hprime : ∀ p ∈ P, p.Prime)
    (hdisj : Disjoint k.primeFactors P) (hd : d ∈ productLayer P r) :
    ((k * d).primeFactors ∩ P).card = r := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hd
  have hAsub := (Finset.mem_powersetCard.mp hA).1
  have hAcard := (Finset.mem_powersetCard.mp hA).2
  have hAprime : ∀ p ∈ A, p.Prime := fun p hp ↦ hprime p (hAsub hp)
  have hApos : 0 < ∏ p ∈ A, p := Finset.prod_pos fun p hp ↦ (hAprime p hp).pos
  have hinter :
      (k.primeFactors ∪ (∏ p ∈ A, p).primeFactors) ∩ P = A := by
    rw [Nat.primeFactors_prod hAprime]
    ext p
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hp | hp, hpP⟩
      · exact (Finset.disjoint_left.mp hdisj hp hpP).elim
      · exact hp
    · intro hp
      exact ⟨Or.inr hp, hAsub hp⟩
  rw [Nat.primeFactors_mul hk.ne' hApos.ne', hinter, hAcard]

lemma mem_prefixLayerRun_rep {P : Finset ℕ} {r a d : ℕ} {qs : List ℕ}
    (hqs : qs.Nodup) (hd : d ∈ prefixLayerRun P r a qs) :
    ∃ K ⊆ qs.toFinset, ∃ e ∈ productLayer P r,
      d = a * (∏ q ∈ K, q) * e := by
  induction qs generalizing a with
  | nil => simp [prefixLayerRun] at hd
  | cons q qs ih =>
      simp only [prefixLayerRun, List.mem_append, List.mem_map] at hd
      rcases hd with ⟨e, he, rfl⟩ | hd
      · refine ⟨{q}, ?_, e, mem_productLayerList.mp he, ?_⟩
        · simp
        · simp
      · obtain ⟨K, hK, e, he, hde⟩ := ih hqs.tail hd
        have hqK : q ∉ K := by
          intro hq
          have hqqs : q ∈ qs.toFinset := hK hq
          exact (List.nodup_cons.mp hqs).1 (by simpa using hqqs)
        refine ⟨insert q K, ?_, e, he, ?_⟩
        · intro z hz
          simp only [Finset.mem_insert] at hz
          simp only [List.toFinset_cons, Finset.mem_insert]
          rcases hz with rfl | hz
          · exact Or.inl rfl
          · exact Or.inr (by simpa using hK hz)
        · rw [Finset.prod_insert hqK]
          rw [hde]
          ring

lemma prefixLayerRun_nodup {P : Finset ℕ} {x a : ℕ} {qs : List ℕ}
    (hx : 0 < x) (ha : 0 < a) (hP : ∀ p ∈ P, x ≤ p ∧ p < 2 * x)
    (hqs : qs.Nodup) (hqLarge : ∀ q ∈ qs, 4 < q) :
    (prefixLayerRun P 2 a qs).Nodup := by
  induction qs generalizing a with
  | nil => simp [prefixLayerRun]
  | cons q qs ih =>
      rw [prefixLayerRun, List.nodup_append]
      have hq : 0 < q := by have := hqLarge q (by simp); omega
      have hhead :
          (List.map (fun d ↦ a * q * d) (productLayerList P 2)).Nodup :=
        (productLayerList_nodup P 2).map fun u v huv ↦
          Nat.eq_of_mul_eq_mul_left (Nat.mul_pos ha hq) huv
      have htail := ih (a := a * q) (Nat.mul_pos ha hq)
        hqs.tail (fun z hz ↦ hqLarge z (by simp [hz]))
      refine ⟨hhead, htail, ?_⟩
      intro d hd e he hde
      subst e
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hd
      cases qs with
      | nil => simp [prefixLayerRun] at he
      | cons z zs =>
          have huUpper := (productLayer_bounds
            (fun p hp ↦ ⟨(hP p hp).1, (hP p hp).2.le⟩)
            (mem_productLayerList.mp hu)).2
          have heLower := prefixLayerRun_lower hP
            (fun y hy ↦ by have := hqLarge y (by simp [hy]); omega) _ he
          have hz : 4 < z := hqLarge z (by simp)
          have : a * q * u < (a * q) * z * x ^ 2 := by
            calc
              a * q * u ≤ a * q * (2 * x) ^ 2 :=
                Nat.mul_le_mul_left _ huUpper
              _ = 4 * (a * q * x ^ 2) := by ring
              _ < z * (a * q * x ^ 2) := by
                exact (Nat.mul_lt_mul_right
                  (Nat.mul_pos (Nat.mul_pos ha hq) (pow_pos hx 2))).2 hz
              _ = (a * q) * z * x ^ 2 := by ring
          omega

lemma slowExtension_prefixPairRun {P : Finset ℕ}
    {x a F : ℕ} {qs : List ℕ}
    (hx : 0 < x) (ha : 0 < a)
    (hprime : ∀ p ∈ P, p.Prime)
    (hP : ∀ p ∈ P, x ≤ p ∧ p < 2 * x)
    (hcard : 8 * x ≤ (productLayer P 2).card)
    (hqs : ∀ q ∈ qs, 0 < q ∧ q ≤ x)
    (hroom : 4 * a * x ^ 3 ≤ F + 1) :
    SlowExtension F (prefixLayerRun P 2 a qs) := by
  have htwoCard : 2 ≤ P.card := by
    have hc : 8 ≤ (productLayer P 2).card := by nlinarith
    rw [card_productLayer hprime] at hc
    by_contra hnot
    have : P.card ≤ 1 := by omega
    interval_cases P.card <;> simp at hc
  have hminUpper : layerMin P 2 ≤ (2 * x) ^ 2 :=
    (productLayer_bounds
      (fun p hp => ⟨(hP p hp).1, (hP p hp).2.le⟩)
      (layerMin_mem htwoCard)).2
  have hsumLower : 8 * x * x ^ 2 ≤ (productLayerList P 2).sum := by
    have hlower : (productLayer P 2).card * x ^ 2 ≤
        (productLayerList P 2).sum := by
      rw [sum_productLayerList]
      apply card_mul_le_sum_of_le
      intro d hd
      exact (productLayer_bounds
        (fun p hp => ⟨(hP p hp).1, (hP p hp).2.le⟩) hd).1
    exact (Nat.mul_le_mul_right (x ^ 2) hcard).trans hlower
  induction qs generalizing a F with
  | nil => simp [prefixLayerRun, SlowExtension]
  | cons q qs ih =>
      have hq := hqs q (by simp)
      rw [prefixLayerRun, slowExtension_append]
      constructor
      · apply slowExtension_scaled_productLayer hprime hP
        · exact Nat.mul_pos ha hq.1
        · calc
            (a * q) * layerMin P 2 ≤ (a * q) * (2 * x) ^ 2 :=
              Nat.mul_le_mul_left _ hminUpper
            _ = (4 * a * x ^ 2) * q := by ring
            _ ≤ (4 * a * x ^ 2) * x := Nat.mul_le_mul_left _ hq.2
            _ = 4 * a * x ^ 3 := by ring
            _ ≤ F + 1 := hroom
      · apply ih (a := a * q)
        · exact Nat.mul_pos ha hq.1
        · intro z hz
          exact hqs z (by simp [hz])
        · rw [List.sum_map_mul_left, List.map_id']
          have hscaled := Nat.mul_le_mul_left (a * q) hsumLower
          have hbase : 4 * x ^ 3 ≤ 8 * x * x ^ 2 := by
            calc
              4 * x ^ 3 ≤ 8 * x ^ 3 := Nat.mul_le_mul_right _ (by norm_num)
              _ = 8 * x * x ^ 2 := by ring
          calc
            4 * (a * q) * x ^ 3 = (a * q) * (4 * x ^ 3) := by ring
            _ ≤ (a * q) * (8 * x * x ^ 2) := Nat.mul_le_mul_left _ hbase
            _ ≤ (a * q) * (productLayerList P 2).sum := hscaled
            _ ≤ F + (a * q) * (productLayerList P 2).sum + 1 := by omega

lemma prefixLayerRun_sum_reserve {P : Finset ℕ} {x a B : ℕ}
    {qs : List ℕ}
    (hsumLower : 8 * x * x ^ 2 ≤ (productLayerList P 2).sum)
    (hB : 8 * a * x ^ 3 ≤ B) :
    8 * (a * qs.prod) * x ^ 3 ≤ B + (prefixLayerRun P 2 a qs).sum := by
  induction qs generalizing a B with
  | nil => simpa [prefixLayerRun]
  | cons q qs ih =>
      simp only [List.prod_cons, prefixLayerRun, List.sum_append]
      have hsumMap :
          (List.map (fun d => a * q * d) (productLayerList P 2)).sum =
            (a * q) * (productLayerList P 2).sum := by
        simpa [id_eq] using
          (List.sum_map_mul_left (productLayerList P 2) id (a * q))
      rw [hsumMap]
      have hnext : 8 * (a * q) * x ^ 3 ≤
          B + (a * q) * (productLayerList P 2).sum := by
        have hscaled := Nat.mul_le_mul_left (a * q) hsumLower
        have hbase : 8 * x * x ^ 2 = 8 * x ^ 3 := by ring
        rw [hbase] at hscaled
        calc
          8 * (a * q) * x ^ 3 = (a * q) * (8 * x ^ 3) := by ring
          _ ≤ (a * q) * (productLayerList P 2).sum := hscaled
          _ ≤ B + (a * q) * (productLayerList P 2).sum := by omega
      simpa only [Nat.mul_assoc, Nat.add_assoc] using
        (ih (a := a * q) (B := B + (a * q) * (productLayerList P 2).sum) hnext)

def coreExtension (p : ℕ) (P : Finset ℕ) (qs : List ℕ) : List ℕ :=
  (baseLayerRest p P).sort (· ≤ ·) ++
    prefixLayerRun P 2 1 qs ++
      productLayerRun P qs.prod 2 (P.card - 3)

lemma coreExtension_nodup {t p : ℕ} {P : Finset ℕ} {qs : List ℕ}
    (ht : 12 ≤ t) (hblock : PrimeBlock (2 ^ t) P)
    (hqsNodup : qs.Nodup) (hqs : ∀ q ∈ qs, 0 < q ∧ 4 < q) :
    (coreExtension p P qs).Nodup := by
  let x := 2 ^ t
  let B := (baseLayerRest p P).sort (· ≤ ·)
  let M := prefixLayerRun P 2 1 qs
  let H := productLayerRun P qs.prod 2 (P.card - 3)
  have hx : 0 < x := pow_pos (by norm_num) _
  have hx4 : 4 < x := by
    dsimp [x]
    have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 2) ht
    exact (by norm_num : 4 < 2 ^ 12).trans_le hpow
  have hP : ∀ q ∈ P, x ≤ q ∧ q < 2 * x := fun q hq ↦
    (hblock q hq).2
  have hprime : ∀ q ∈ P, q.Prime := fun q hq ↦ (hblock q hq).1
  have hk : 0 < qs.prod := List.prod_pos fun q hq ↦ (hqs q hq).1
  have hBnodup : B.Nodup := Finset.sort_nodup _ _
  have hMnodup : M.Nodup := by
    exact prefixLayerRun_nodup hx (by norm_num) hP hqsNodup
      (fun q hq ↦ (hqs q hq).2)
  have hHnodup : H.Nodup := productLayerRun_nodup hk hprime
  have hBupper : ∀ d ∈ B, d ≤ 4 * x ^ 2 := by
    intro d hd
    apply baseLayerRest_le_four_sq hx hP d
    simpa [B] using hd
  have hMupper : ∀ d ∈ M, d ≤ qs.prod * (2 * x) ^ 2 := by
    intro d hd
    simpa [M] using prefixLayerRun_upper hP
      (fun q hq ↦ (hqs q hq).1) d hd
  have hHlower : ∀ d ∈ H, qs.prod * x ^ 3 ≤ d := by
    intro d hd
    simpa [H] using productLayerRun_lower hP hd
  have hBM : ∀ d ∈ B, ∀ e ∈ M, d ≠ e := by
    intro d hd e he hde
    subst e
    cases hq : qs with
    | nil => simp [M, hq, prefixLayerRun] at he
    | cons q rest =>
        have hqs' : ∀ z ∈ q :: rest, 0 < z := by
          intro z hz
          exact (hqs z (by rw [hq]; exact hz)).1
        have heLower := prefixLayerRun_lower hP
          hqs' d (by simpa [M, hq] using he)
        have hq4 := (hqs q (by simp [hq])).2
        have hx2 : 0 < x ^ 2 := pow_pos hx _
        have hsep : 4 * x ^ 2 < q * x ^ 2 :=
          (Nat.mul_lt_mul_right hx2).mpr hq4
        have heLower' : q * x ^ 2 ≤ d := by simpa using heLower
        exact (not_lt_of_ge heLower') ((hBupper d hd).trans_lt hsep)
  have hMH : ∀ d ∈ M, ∀ e ∈ H, d ≠ e := by
    intro d hd e he hde
    subst e
    have hdUpper := hMupper d hd
    have hdLower := hHlower d he
    have hpos : 0 < qs.prod * x ^ 2 := Nat.mul_pos hk (pow_pos hx _)
    have hsep : qs.prod * (2 * x) ^ 2 < qs.prod * x ^ 3 := by
      calc
        qs.prod * (2 * x) ^ 2 = 4 * (qs.prod * x ^ 2) := by ring
        _ < x * (qs.prod * x ^ 2) := (Nat.mul_lt_mul_right hpos).mpr hx4
        _ = qs.prod * x ^ 3 := by ring
    exact (not_lt_of_ge hdLower) (hdUpper.trans_lt hsep)
  have hBH : ∀ d ∈ B, ∀ e ∈ H, d ≠ e := by
    intro d hd e he hde
    subst e
    have hdUpper := hBupper d hd
    have hdLower := hHlower d he
    have hk1 : 1 ≤ qs.prod := Nat.one_le_iff_ne_zero.mpr hk.ne'
    have hx2 : 0 < x ^ 2 := pow_pos hx _
    have hsep : 4 * x ^ 2 < qs.prod * x ^ 3 := by
      calc
        4 * x ^ 2 < x * x ^ 2 := (Nat.mul_lt_mul_right hx2).mpr hx4
        _ = 1 * x ^ 3 := by ring
        _ ≤ qs.prod * x ^ 3 := Nat.mul_le_mul_right (x ^ 3) hk1
    exact (not_lt_of_ge hdLower) (hdUpper.trans_lt hsep)
  change (B ++ M ++ H).Nodup
  rw [List.nodup_append]
  refine ⟨?_, hHnodup, ?_⟩
  · rw [List.nodup_append]
    exact ⟨hBnodup, hMnodup, hBM⟩
  · intro d hd e he
    rcases List.mem_append.mp hd with hd | hd
    · exact hBH d hd e he
    · exact hMH d hd e he

lemma productLayer_dvd_prod {P : Finset ℕ} {r d : ℕ}
    (hd : d ∈ productLayer P r) : d ∣ ∏ p ∈ P, p := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hd
  exact Finset.prod_dvd_prod_of_subset A P id
    (Finset.mem_powersetCard.mp hA).1

lemma baseProductLayers_dvd_prod {P : Finset ℕ} {d : ℕ}
    (hd : d ∈ baseProductLayers P) : d ∣ ∏ p ∈ P, p := by
  rcases Finset.mem_union.mp hd with hd | hd
  · exact productLayer_dvd_prod hd
  · exact productLayer_dvd_prod hd

lemma finsetSubproduct_dvd_listProd {L : List ℕ} (hL : L.Nodup)
    {K : Finset ℕ} (hK : K ⊆ L.toFinset) :
    (∏ q ∈ K, q) ∣ L.prod := by
  have hprod : L.toFinset.prod id = L.prod := by
    calc
      L.toFinset.prod id = (L.map id).prod := List.prod_toFinset id hL
      _ = L.prod := by simp
  rw [← hprod]
  exact Finset.prod_dvd_prod_of_subset K L.toFinset id hK

lemma coreExtension_dvd_kernel {p : ℕ} {P : Finset ℕ} {qs : List ℕ}
    (hqs : qs.Nodup) {d : ℕ} (hd : d ∈ coreExtension p P qs) :
    d ∣ (∏ q ∈ P, q) * qs.prod := by
  simp only [coreExtension, List.mem_append] at hd
  rcases hd with hd | hd
  · rcases hd with hd | hd
    · have hdBase : d ∈ baseProductLayers P :=
        (Finset.mem_sdiff.mp
          ((Finset.mem_sort (s := baseLayerRest p P) (fun a b ↦ a ≤ b)).mp hd)).1
      exact (baseProductLayers_dvd_prod hdBase).mul_right qs.prod
    · obtain ⟨K, hK, e, he, rfl⟩ := mem_prefixLayerRun_rep hqs hd
      have hKd := finsetSubproduct_dvd_listProd hqs hK
      have hed := productLayer_dvd_prod he
      simpa only [one_mul, Nat.mul_comm] using Nat.mul_dvd_mul hKd hed
  · obtain ⟨j, hj1, hj2, e, he, rfl⟩ := mem_productLayerRun hd
    simpa only [Nat.mul_comm] using
      Nat.mul_dvd_mul_left qs.prod (productLayer_dvd_prod he)

lemma coreExtension_blockDegree_lt {p : ℕ} {P : Finset ℕ} {qs : List ℕ}
    (hPcard : 4 ≤ P.card) (hprime : ∀ q ∈ P, q.Prime)
    (hqsNodup : qs.Nodup) (hqsPrime : ∀ q ∈ qs, q.Prime)
    (hdisj : Disjoint qs.toFinset P) {d : ℕ}
    (hd : d ∈ coreExtension p P qs) :
    (d.primeFactors ∩ P).card < P.card := by
  simp only [coreExtension, List.mem_append] at hd
  rcases hd with hd | hd
  · rcases hd with hd | hd
    · have hdBase : d ∈ baseProductLayers P :=
        (Finset.mem_sdiff.mp
          ((Finset.mem_sort (s := baseLayerRest p P) (fun a b ↦ a ≤ b)).mp hd)).1
      rcases Finset.mem_union.mp hdBase with hdOne | hdTwo
      · have hdeg := blockPrimeFactors_mul_productLayer
            (k := 1) (P := P) (r := 1) (d := d) (by norm_num) hprime
            (by simp) hdOne
        simp only [one_mul] at hdeg
        omega
      · have hdeg := blockPrimeFactors_mul_productLayer
            (k := 1) (P := P) (r := 2) (d := d) (by norm_num) hprime
            (by simp) hdTwo
        simp only [one_mul] at hdeg
        omega
    · obtain ⟨K, hK, e, he, rfl⟩ := mem_prefixLayerRun_rep hqsNodup hd
      have hKprime : ∀ q ∈ K, q.Prime := by
        intro q hq
        exact hqsPrime q (by simpa using hK hq)
      have hk : 0 < ∏ q ∈ K, q :=
        Finset.prod_pos fun q hq ↦ (hKprime q hq).pos
      have hkFactors : (∏ q ∈ K, q).primeFactors = K :=
        Nat.primeFactors_prod hKprime
      have hKP : Disjoint K P := hdisj.mono_left hK
      have hdeg := blockPrimeFactors_mul_productLayer
        (k := ∏ q ∈ K, q) hk hprime (by simpa [hkFactors] using hKP) he
      have hlt : (((∏ q ∈ K, q) * e).primeFactors ∩ P).card < P.card := by
        omega
      simpa only [one_mul] using hlt
  · obtain ⟨j, hj1, hj2, e, he, rfl⟩ := mem_productLayerRun hd
    have hk : 0 < qs.prod := List.prod_pos fun q hq ↦ (hqsPrime q hq).pos
    have hkFactors := primeFactors_list_prod hqsNodup hqsPrime
    have hdeg := blockPrimeFactors_mul_productLayer
      (k := qs.prod) hk hprime (by simpa [hkFactors] using hdisj) he
    have hj : j < P.card := by omega
    omega

lemma kernel_blockDegree {P : Finset ℕ} {qs : List ℕ}
    (hprime : ∀ q ∈ P, q.Prime)
    (hqsNodup : qs.Nodup) (hqsPrime : ∀ q ∈ qs, q.Prime)
    (hdisj : Disjoint qs.toFinset P) :
    ((((∏ q ∈ P, q) * qs.prod).primeFactors ∩ P).card) = P.card := by
  have hk : 0 < qs.prod := List.prod_pos fun q hq ↦ (hqsPrime q hq).pos
  have hkFactors := primeFactors_list_prod hqsNodup hqsPrime
  have hLayer : (∏ q ∈ P, q) ∈ productLayer P P.card := by
    apply Finset.mem_image.mpr
    exact ⟨P, Finset.mem_powersetCard.mpr ⟨Finset.Subset.rfl, rfl⟩, rfl⟩
  have hdeg := blockPrimeFactors_mul_productLayer
    (k := qs.prod) hk hprime (by simpa [hkFactors] using hdisj) hLayer
  simpa [Nat.mul_comm] using hdeg

lemma properDivisor_of_kernel_degree {P : Finset ℕ} {N d : ℕ}
    (hN : 0 < N) (hdvd : d ∣ N)
    (hdDegree : (d.primeFactors ∩ P).card < P.card)
    (hNDegree : (N.primeFactors ∩ P).card = P.card) :
    d ∈ N.properDivisors := by
  apply Nat.mem_properDivisors.mpr
  refine ⟨hdvd, ?_⟩
  have hle : d ≤ N := Nat.le_of_dvd hN hdvd
  exact lt_of_le_of_ne hle fun hEq ↦ by
    subst d
    omega

lemma strongBlockDivisors_le_four_sq {x p : ℕ} {P : Finset ℕ}
    (hx : 0 < x) (hblock : PrimeBlock x P) (hp : p ∈ P) :
    ∀ d ∈ strongBlockDivisors p P, d ≤ 4 * x ^ 2 := by
  intro d hd
  rcases Finset.mem_union.mp hd with hd | hd
  · have hdUpper := (hblock d hd).2.2
    have hroom : 2 * x ≤ 4 * x ^ 2 := by nlinarith
    omega
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hd
    have hpUpper := (hblock p hp).2.2.le
    have hqUpper := (hblock q (Finset.mem_of_mem_erase hq)).2.2.le
    calc
      p * q ≤ (2 * x) * (2 * x) := Nat.mul_le_mul hpUpper hqUpper
      _ = 4 * x ^ 2 := by ring

lemma strongBlockDivisors_disjoint_core {t p : ℕ} {P : Finset ℕ}
    {qs : List ℕ} (ht : 12 ≤ t) (hblock : PrimeBlock (2 ^ t) P)
    (hp : p ∈ P) (hqs : ∀ q ∈ qs, 0 < q ∧ 4 < q) :
    Disjoint (strongBlockDivisors p P) (coreExtension p P qs).toFinset := by
  let x := 2 ^ t
  have hx : 0 < x := pow_pos (by norm_num) _
  have hx4 : 4 < x := by
    have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 2) ht
    exact (by norm_num : 4 < 2 ^ 12).trans_le hpow
  have hP : ∀ q ∈ P, x ≤ q ∧ q < 2 * x := fun q hq ↦
    (hblock q hq).2
  rw [Finset.disjoint_left]
  intro d hdSeed hdCore
  have hdCore' : d ∈ coreExtension p P qs := by simpa using hdCore
  simp only [coreExtension, List.mem_append] at hdCore'
  rcases hdCore' with hdCore' | hdHigh
  · rcases hdCore' with hdBase | hdMid
    · have hdRest : d ∈ baseLayerRest p P :=
        (Finset.mem_sort (s := baseLayerRest p P) (fun a b ↦ a ≤ b)).mp hdBase
      exact (Finset.mem_sdiff.mp hdRest).2 hdSeed
    · cases hq : qs with
      | nil => simp [hq, prefixLayerRun] at hdMid
      | cons q rest =>
          have hpos : ∀ z ∈ q :: rest, 0 < z := by
            intro z hz
            exact (hqs z (by rw [hq]; exact hz)).1
          have hlow := prefixLayerRun_lower hP hpos d
            (by simpa [hq] using hdMid)
          have hlow' : q * x ^ 2 ≤ d := by simpa using hlow
          have hupper := strongBlockDivisors_le_four_sq hx
            (by simpa [x] using hblock) hp d hdSeed
          have hq4 := (hqs q (by simp [hq])).2
          have hsep : 4 * x ^ 2 < q * x ^ 2 :=
            (Nat.mul_lt_mul_right (pow_pos hx 2)).mpr hq4
          omega
  · have hlow := productLayerRun_lower hP hdHigh
    have hlow' : qs.prod * x ^ 3 ≤ d := by simpa using hlow
    have hupper := strongBlockDivisors_le_four_sq hx
      (by simpa [x] using hblock) hp d hdSeed
    have hk : 1 ≤ qs.prod := List.one_le_prod fun q hq ↦ (hqs q hq).1
    have hsep : 4 * x ^ 2 < qs.prod * x ^ 3 := by
      calc
        4 * x ^ 2 < x * x ^ 2 :=
          (Nat.mul_lt_mul_right (pow_pos hx 2)).mpr hx4
        _ = 1 * x ^ 3 := by ring
        _ ≤ qs.prod * x ^ 3 := Nat.mul_le_mul_right (x ^ 3) hk
    omega

lemma strongBlockDivisors_mem_kernelProper {p : ℕ} {P : Finset ℕ}
    {qs : List ℕ} (hp : p ∈ P) (hPcard : 4 ≤ P.card)
    (hprime : ∀ q ∈ P, q.Prime)
    (hqsNodup : qs.Nodup) (hqsPrime : ∀ q ∈ qs, q.Prime)
    (hdisj : Disjoint qs.toFinset P) :
    ∀ d ∈ strongBlockDivisors p P,
      d ∈ ((∏ q ∈ P, q) * qs.prod).properDivisors := by
  intro d hd
  have hdBase := strongBlockDivisors_subset_baseProductLayers hp hd
  have hdvd : d ∣ (∏ q ∈ P, q) * qs.prod :=
    (baseProductLayers_dvd_prod hdBase).mul_right qs.prod
  have hdDegree : (d.primeFactors ∩ P).card < P.card := by
    rcases Finset.mem_union.mp hdBase with hdOne | hdTwo
    · have hdeg := blockPrimeFactors_mul_productLayer
        (k := 1) (P := P) (r := 1) (d := d) (by norm_num) hprime
        (by simp) hdOne
      simp only [one_mul] at hdeg
      omega
    · have hdeg := blockPrimeFactors_mul_productLayer
        (k := 1) (P := P) (r := 2) (d := d) (by norm_num) hprime
        (by simp) hdTwo
      simp only [one_mul] at hdeg
      omega
  have hN : 0 < (∏ q ∈ P, q) * qs.prod := Nat.mul_pos
    (Finset.prod_pos fun q hq ↦ (hprime q hq).pos)
    (List.prod_pos fun q hq ↦ (hqsPrime q hq).pos)
  exact properDivisor_of_kernel_degree hN hdvd hdDegree
    (kernel_blockDegree hprime hqsNodup hqsPrime hdisj)

lemma coreExtension_mem_kernelProper {p : ℕ} {P : Finset ℕ}
    {qs : List ℕ} (hPcard : 4 ≤ P.card)
    (hprime : ∀ q ∈ P, q.Prime)
    (hqsNodup : qs.Nodup) (hqsPrime : ∀ q ∈ qs, q.Prime)
    (hdisj : Disjoint qs.toFinset P) :
    ∀ d ∈ coreExtension p P qs,
      d ∈ ((∏ q ∈ P, q) * qs.prod).properDivisors := by
  intro d hd
  have hN : 0 < (∏ q ∈ P, q) * qs.prod := Nat.mul_pos
    (Finset.prod_pos fun q hq ↦ (hprime q hq).pos)
    (List.prod_pos fun q hq ↦ (hqsPrime q hq).pos)
  exact properDivisor_of_kernel_degree hN
    (coreExtension_dvd_kernel hqsNodup hd)
    (coreExtension_blockDegree_lt hPcard hprime hqsNodup hqsPrime hdisj hd)
    (kernel_blockDegree hprime hqsNodup hqsPrime hdisj)

lemma sum_strongBlockDivisors_lt_kernel {t p : ℕ} {P : Finset ℕ}
    {qs : List ℕ} (ht : 12 ≤ t) (hblock : PrimeBlock (2 ^ t) P)
    (hp : p ∈ P) (hPcard : 4 ≤ P.card)
    (hqsPos : ∀ q ∈ qs, 0 < q) :
    ∑ d ∈ strongBlockDivisors p P, d < (∏ q ∈ P, q) * qs.prod := by
  let x := 2 ^ t
  have hx : 0 < x := pow_pos (by norm_num) _
  have hx8 : 8 < x := by
    have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 2) ht
    exact (by norm_num : 8 < 2 ^ 12).trans_le hpow
  have hP : ∀ q ∈ P, x ≤ q ∧ q ≤ 2 * x := fun q hq ↦
    ⟨(hblock q hq).2.1, (hblock q hq).2.2.le⟩
  have hPsub : P ⊆ Finset.Ico x (2 * x) := by
    intro q hq
    exact Finset.mem_Ico.mpr ⟨(hblock q hq).2.1, (hblock q hq).2.2⟩
  have hPcardUpper : P.card ≤ x := by
    have hc := Finset.card_le_card hPsub
    have hIco : (Finset.Ico x (2 * x)).card = x := by
      simp
      omega
    rwa [hIco] at hc
  have hDcard : (strongBlockDivisors p P).card ≤ 2 * P.card := by
    calc
      (strongBlockDivisors p P).card ≤
          P.card + ((P.erase p).image (fun q ↦ p * q)).card :=
        by
          unfold strongBlockDivisors
          exact Finset.card_union_le P ((P.erase p).image (fun q ↦ p * q))
      _ ≤ P.card + (P.erase p).card :=
        Nat.add_le_add_left (Finset.card_image_le) _
      _ ≤ 2 * P.card := by
        have := Finset.card_erase_le (s := P) (a := p)
        omega
  have hDsum : ∑ d ∈ strongBlockDivisors p P, d ≤ 8 * x ^ 3 := by
    calc
      ∑ d ∈ strongBlockDivisors p P, d ≤
          (strongBlockDivisors p P).card * (4 * x ^ 2) := by
        simpa [nsmul_eq_mul, Nat.mul_comm] using
          (Finset.sum_le_card_nsmul (strongBlockDivisors p P) id
            (4 * x ^ 2) (strongBlockDivisors_le_four_sq hx
              (by simpa [x] using hblock) hp))
      _ ≤ (2 * P.card) * (4 * x ^ 2) := Nat.mul_le_mul_right _ hDcard
      _ ≤ (2 * x) * (4 * x ^ 2) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hPcardUpper)
      _ = 8 * x ^ 3 := by ring
  have hLayer : (∏ q ∈ P, q) ∈ productLayer P P.card := by
    apply Finset.mem_image.mpr
    exact ⟨P, Finset.mem_powersetCard.mpr ⟨Finset.Subset.rfl, rfl⟩, rfl⟩
  have hProdLower : x ^ P.card ≤ ∏ q ∈ P, q :=
    (productLayer_bounds hP hLayer).1
  have hxPow : x ^ 4 ≤ x ^ P.card := Nat.pow_le_pow_right hx hPcard
  have hsmall : 8 * x ^ 3 < x ^ 4 := by
    calc
      8 * x ^ 3 < x * x ^ 3 := (Nat.mul_lt_mul_right (pow_pos hx 3)).mpr hx8
      _ = x ^ 4 := by ring
  have hqprod : 1 ≤ qs.prod := List.one_le_prod hqsPos
  calc
    ∑ d ∈ strongBlockDivisors p P, d ≤ 8 * x ^ 3 := hDsum
    _ < x ^ 4 := hsmall
    _ ≤ x ^ P.card := hxPow
    _ ≤ ∏ q ∈ P, q := hProdLower
    _ ≤ (∏ q ∈ P, q) * qs.prod := by
      simpa only [mul_one] using Nat.mul_le_mul_left (∏ q ∈ P, q) hqprod

/-- A rich terminal dyadic block admits every product layer through the
co-singleton layer, after multiplying successively by all earlier primes. -/
lemma slowExtension_coreExtension {t p : ℕ} {P : Finset ℕ}
    {qs : List ℕ} {F : ℕ}
    (ht : 12 ≤ t) (hblock : PrimeBlock (2 ^ t) P) (hp : p ∈ P)
    (hcard : richCardThreshold t < P.card)
    (hqs : ∀ q ∈ qs, 0 < q ∧ q ≤ 2 ^ t)
    (hF : 4 * (2 ^ t) ^ 2 < F) :
    SlowExtension F (coreExtension p P qs) := by
  let x := 2 ^ t
  change 4 * x ^ 2 < F at hF
  have hx : 0 < x := pow_pos (by norm_num) _
  have hprime : ∀ q ∈ P, q.Prime := fun q hq => (hblock q hq).1
  have hP : ∀ q ∈ P, x ≤ q ∧ q < 2 * x :=
    fun q hq => (hblock q hq).2
  have hPcard : 4 ≤ P.card := by
    have hlarge : 8 * 2 ^ (3 * (t / 4)) + 4 < P.card :=
      (le_max_right (denseCardThreshold t + 1)
        (8 * 2 ^ (3 * (t / 4)) + 4)).trans_lt hcard
    omega
  have hreserve : 8 * x ≤ (productLayer P 2).card := by
    apply card_productLayer_ge_rich_reserve ht hprime hp hcard
    · omega
    · omega
  let B := (baseLayerRest p P).sort (· ≤ ·)
  have hBsum : 8 * x * x ^ 2 ≤ B.sum := by
    have hraw := sum_baseLayerRest_ge hprime hP hp
    have hchoose := choose_two_erase_ge_two_pow ht hp hcard
    have hscaled := Nat.mul_le_mul_right (x ^ 2) hchoose
    dsimp [B]
    rw [sum_baseLayerRest_sort]
    exact hscaled.trans hraw
  have hLayerSum : 8 * x * x ^ 2 ≤ (productLayerList P 2).sum := by
    have hlower : (productLayer P 2).card * x ^ 2 ≤
        (productLayerList P 2).sum := by
      rw [sum_productLayerList]
      apply card_mul_le_sum_of_le
      intro d hd
      exact (productLayer_bounds
        (fun q hq => ⟨(hP q hq).1, (hP q hq).2.le⟩) hd).1
    exact (Nat.mul_le_mul_right (x ^ 2) hreserve).trans hlower
  have hbaseSlow : SlowExtension F B := by
    apply slowExtension_of_bounded (H := 4 * x ^ 2)
    · omega
    · intro d hd
      have hd' : d ∈ baseLayerRest p P := by simpa [B] using hd
      exact baseLayerRest_le_four_sq hx hP d hd'
  have hB8 : 8 * x ^ 3 ≤ B.sum := by
    calc
      8 * x ^ 3 = 8 * x * x ^ 2 := by ring
      _ ≤ B.sum := hBsum
  have hprefixSlow :
      SlowExtension (F + B.sum) (prefixLayerRun P 2 1 qs) := by
    apply slowExtension_prefixPairRun hx (by norm_num) hprime hP hreserve hqs
    calc
      4 * 1 * x ^ 3 ≤ 8 * x ^ 3 := by
        exact Nat.mul_le_mul_right (x ^ 3) (by norm_num)
      _ ≤ B.sum := hB8
      _ ≤ F + B.sum + 1 := by omega
  have hRpos : 0 < qs.prod := List.prod_pos fun q hq => (hqs q hq).1
  have hprefixReserve :
      8 * qs.prod * x ^ 3 ≤ B.sum + (prefixLayerRun P 2 1 qs).sum := by
    have h := prefixLayerRun_sum_reserve
      (P := P) (x := x) (a := 1) (B := B.sum) (qs := qs)
      hLayerSum (by simpa using hB8)
    simpa using h
  have hminThree : layerMin P 3 ≤ (2 * x) ^ 3 :=
    layerMin_le_dyadic_pow hP (by omega)
  have hfirstHigh : qs.prod * layerMin P 3 ≤
      F + B.sum + (prefixLayerRun P 2 1 qs).sum + 1 := by
    calc
      qs.prod * layerMin P 3 ≤ qs.prod * (2 * x) ^ 3 :=
        Nat.mul_le_mul_left _ hminThree
      _ = 8 * qs.prod * x ^ 3 := by ring
      _ ≤ B.sum + (prefixLayerRun P 2 1 qs).sum := hprefixReserve
      _ ≤ F + B.sum + (prefixLayerRun P 2 1 qs).sum + 1 := by omega
  have hhighSlow : SlowExtension
      (F + B.sum + (prefixLayerRun P 2 1 qs).sum)
      (productLayerRun P qs.prod 2 (P.card - 3)) := by
    apply slowExtension_productLayerRun_from_first hprime hP hRpos
    · omega
    · intro j hjLow hjHigh
      have hjUpper : j ≤ P.card - 2 := by omega
      have hjReserve := card_productLayer_ge_rich_reserve
        ht hprime hp hcard (by omega) hjUpper
      exact (by omega : 2 * x ≤ 8 * x).trans hjReserve
    · exact hfirstHigh
  change SlowExtension F
    (B ++ prefixLayerRun P 2 1 qs ++
      productLayerRun P qs.prod 2 (P.card - 3))
  rw [slowExtension_append]
  constructor
  · rw [slowExtension_append]
    exact ⟨hbaseSlow, hprefixSlow⟩
  · simpa [List.sum_append, Nat.add_assoc] using hhighSlow

/-! ### A finite conormal block scan -/

def WeightedSlowExtension {A : Type*} (w : A → ℝ) (S : ℝ) : List A → Prop
  | [] => True
  | a :: as => w a ≤ S ∧ WeightedSlowExtension w (S + w a) as

lemma weightedSlowExtension_append {A : Type*} {w : A → ℝ}
    {S : ℝ} {L M : List A} :
    WeightedSlowExtension w S (L ++ M) ↔
      WeightedSlowExtension w S L ∧
        WeightedSlowExtension w (S + (L.map w).sum) M := by
  induction L generalizing S with
  | nil => simp [WeightedSlowExtension]
  | cons a L ih =>
      simp only [List.cons_append, List.map_cons, List.sum_cons,
        WeightedSlowExtension]
      rw [ih]
      constructor
      · rintro ⟨ha, hL, hM⟩
        exact ⟨⟨ha, hL⟩, by simpa [add_assoc] using hM⟩
      · rintro ⟨⟨ha, hL⟩, hM⟩
        exact ⟨ha, hL, by simpa [add_assoc] using hM⟩

lemma weightedSlowExtension_of_bounded {A : Type*} {w : A → ℝ}
    {S H : ℝ} {L : List A}
    (hw : ∀ a ∈ L, 0 ≤ w a) (hHS : H ≤ S)
    (hL : ∀ a ∈ L, w a ≤ H) :
    WeightedSlowExtension w S L := by
  induction L generalizing S with
  | nil => trivial
  | cons a L ih =>
      constructor
      · exact (hL a (by simp)).trans hHS
      · apply ih
        · intro b hb
          exact hw b (by simp [hb])
        · have ha0 := hw a (by simp)
          linarith
        · intro b hb
          exact hL b (by simp [hb])

/-- The first two entries are supplied by the dense terminal seed; every
later weight must fit the sum already accumulated. -/
def SeededSlow {A : Type*} (w : A → ℝ) : List A → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      w b ≤ 2 * w a ∧ WeightedSlowExtension w (w a + w b) rest

lemma SeededSlow.append_of_bounded {A : Type*} {w : A → ℝ}
    {L M : List A} (hlen : 2 ≤ L.length) (hslow : SeededSlow w L)
    (hw : ∀ a ∈ M, 0 ≤ w a)
    (hbound : ∀ a ∈ M, w a ≤ (L.map w).sum) :
    SeededSlow w (L ++ M) := by
  cases L with
  | nil => simp at hlen
  | cons a L =>
      cases L with
      | nil => simp at hlen
      | cons b rest =>
          change w b ≤ 2 * w a ∧
            WeightedSlowExtension w (w a + w b) (rest ++ M)
          constructor
          · exact hslow.1
          · rw [weightedSlowExtension_append]
            refine ⟨hslow.2, ?_⟩
            apply weightedSlowExtension_of_bounded hw
            · change w a + w b + (rest.map w).sum ≤
                w a + w b + (rest.map w).sum
              exact le_rfl
            · intro c hc
              simpa only [List.map_cons, List.sum_cons, add_assoc] using
                hbound c hc

def indexedBlockMass {A : Type*} (w : A → ℝ) (B : ℕ × List A) : ℝ :=
  (B.2.map w).sum

def indexedBlocksMass {A : Type*} (w : A → ℝ)
    (Bs : List (ℕ × List A)) : ℝ :=
  (Bs.map (indexedBlockMass w)).sum

def indexedBlocksUpper (u : ℕ → ℝ) (Bs : List (ℕ × List A)) : ℝ :=
  (Bs.map (fun B => u B.1)).sum

def flattenIndexedBlocks (Bs : List (ℕ × List A)) : List A :=
  Bs.flatMap Prod.snd

def conormalBlockStep {A : Type*} (w : A → ℝ) (u : ℕ → ℝ)
    (current : List (ℕ × List A)) (B : ℕ × List A) :
    List (ℕ × List A) :=
  if u B.1 ≤ ((flattenIndexedBlocks current).map w).sum then
    current ++ [B]
  else [B]

def conormalBlockScan {A : Type*} (w : A → ℝ) (u : ℕ → ℝ)
    (Bs : List (ℕ × List A)) : List (ℕ × List A) :=
  Bs.foldl (conormalBlockStep w u) []

lemma flattenIndexedBlocks_append (Cs Ds : List (ℕ × List A)) :
    flattenIndexedBlocks (Cs ++ Ds) =
      flattenIndexedBlocks Cs ++ flattenIndexedBlocks Ds := by
  simp [flattenIndexedBlocks, List.flatMap_append]

lemma indexedBlocksMass_eq_flatten {A : Type*} (w : A → ℝ)
    (Bs : List (ℕ × List A)) :
    indexedBlocksMass w Bs = ((flattenIndexedBlocks Bs).map w).sum := by
  induction Bs with
  | nil => simp [indexedBlocksMass, flattenIndexedBlocks]
  | cons B Bs ih =>
      calc
        indexedBlocksMass w (B :: Bs) =
            indexedBlockMass w B + indexedBlocksMass w Bs := by
          simp [indexedBlocksMass]
        _ = indexedBlockMass w B +
            ((flattenIndexedBlocks Bs).map w).sum := by rw [ih]
        _ = ((flattenIndexedBlocks (B :: Bs)).map w).sum := by
          simp [indexedBlockMass, flattenIndexedBlocks]

lemma conormalBlockFold_properties {A : Type*} (w : A → ℝ)
    (u : ℕ → ℝ) (current Bs : List (ℕ × List A))
    (hcurrent : current = [] ∨
      (2 ≤ (flattenIndexedBlocks current).length ∧
        SeededSlow w (flattenIndexedBlocks current)))
    (hblockLen : ∀ B ∈ Bs, 2 ≤ B.2.length)
    (hblockSlow : ∀ B ∈ Bs, SeededSlow w B.2)
    (hw0 : ∀ B ∈ Bs, ∀ a ∈ B.2, 0 ≤ w a)
    (hwUpper : ∀ B ∈ Bs, ∀ a ∈ B.2, w a ≤ u B.1) :
    let Cs := Bs.foldl (conormalBlockStep w u) current
    ((current ≠ [] ∨ Bs ≠ []) →
      2 ≤ (flattenIndexedBlocks Cs).length) ∧
    SeededSlow w (flattenIndexedBlocks Cs) ∧
    indexedBlocksMass w current + indexedBlocksMass w Bs ≤
      indexedBlocksMass w Cs + indexedBlocksUpper u Bs ∧
    (∀ B ∈ Cs, B ∈ current ∨ B ∈ Bs) := by
  classical
  induction Bs generalizing current with
  | nil =>
      have hseed : SeededSlow w (flattenIndexedBlocks current) := by
        rcases hcurrent with rfl | hc
        · trivial
        · exact hc.2
      dsimp
      refine ⟨?_, hseed, ?_, ?_⟩
      · intro hne
        rcases hne with hne | hfalse
        · exact hcurrent.resolve_left hne |>.1
        · exact (hfalse rfl).elim
      · simp [indexedBlocksMass, indexedBlocksUpper]
      · intro B hB
        exact Or.inl hB
  | cons B Bs ih =>
      have hBlen : 2 ≤ B.2.length := hblockLen B (by simp)
      have hBslow : SeededSlow w B.2 := hblockSlow B (by simp)
      have hB0 : ∀ a ∈ B.2, 0 ≤ w a := fun a ha => hw0 B (by simp) a ha
      have hBupper : ∀ a ∈ B.2, w a ≤ u B.1 :=
        fun a ha => hwUpper B (by simp) a ha
      have hBu0 : 0 ≤ u B.1 := by
        cases hL : B.2 with
        | nil => simp [hL] at hBlen
        | cons a as =>
            exact (hB0 a (by simp [hL])).trans (hBupper a (by simp [hL]))
      let massCurrent := ((flattenIndexedBlocks current).map w).sum
      let next := conormalBlockStep w u current B
      have hnext : next = current ++ [B] ∨ next = [B] := by
        by_cases hfit : u B.1 ≤ massCurrent
        · exact Or.inl (by simp [next, conormalBlockStep, massCurrent, hfit])
        · exact Or.inr (by simp [next, conormalBlockStep, massCurrent, hfit])
      have hnextCurrent : next = [] ∨
          (2 ≤ (flattenIndexedBlocks next).length ∧
            SeededSlow w (flattenIndexedBlocks next)) := by
        right
        rcases hnext with happ | hreset
        · rw [happ, flattenIndexedBlocks_append]
          simp only [flattenIndexedBlocks, List.flatMap_singleton,
            List.length_append]
          constructor
          · omega
          · rcases hcurrent with rfl | hc
            · simpa using hBslow
            · apply hc.2.append_of_bounded hc.1 hB0
              intro a ha
              have hfit : u B.1 ≤ massCurrent := by
                by_contra hn
                have : next = [B] := by
                  simp [next, conormalBlockStep, massCurrent, hn]
                rw [happ] at this
                have hlen := congrArg List.length this
                simp at hlen
                have hcne : current ≠ [] := by
                  intro hzero
                  rw [hzero] at hc
                  simp [flattenIndexedBlocks] at hc
                exact (hcne hlen).elim
              exact (hBupper a ha).trans hfit
        · rw [hreset]
          simpa [flattenIndexedBlocks] using ⟨hBlen, hBslow⟩
      have htailLen : ∀ C ∈ Bs, 2 ≤ C.2.length := by
        intro C hC; exact hblockLen C (by simp [hC])
      have htailSlow : ∀ C ∈ Bs, SeededSlow w C.2 := by
        intro C hC; exact hblockSlow C (by simp [hC])
      have htail0 : ∀ C ∈ Bs, ∀ a ∈ C.2, 0 ≤ w a := by
        intro C hC; exact hw0 C (by simp [hC])
      have htailUpper : ∀ C ∈ Bs, ∀ a ∈ C.2, w a ≤ u C.1 := by
        intro C hC; exact hwUpper C (by simp [hC])
      have hrec := ih next hnextCurrent htailLen htailSlow htail0 htailUpper
      simp only [List.foldl_cons]
      let Cs := Bs.foldl (conormalBlockStep w u) next
      change
        ((current ≠ [] ∨ B :: Bs ≠ []) →
          2 ≤ (flattenIndexedBlocks Cs).length) ∧
        SeededSlow w (flattenIndexedBlocks Cs) ∧
        indexedBlocksMass w current + indexedBlocksMass w (B :: Bs) ≤
          indexedBlocksMass w Cs + indexedBlocksUpper u (B :: Bs) ∧
        (∀ C ∈ Cs, C ∈ current ∨ C ∈ B :: Bs)
      have hnextNe : next ≠ [] := by
        rcases hnext with h | h <;> rw [h]
        · simp
        · simp
      have hlenFinal := hrec.1 (Or.inl hnextNe)
      refine ⟨fun _ => hlenFinal, hrec.2.1, ?_, ?_⟩
      · have hmassRec := hrec.2.2.1
        simp_rw [indexedBlocksMass_eq_flatten w] at hmassRec ⊢
        dsimp [Cs]
        by_cases hfit : u B.1 ≤ massCurrent
        · have hnextEq : next = current ++ [B] := by
            simp [next, conormalBlockStep, massCurrent, hfit]
          rw [hnextEq]
          rw [hnextEq, flattenIndexedBlocks_append] at hmassRec
          simp [indexedBlocksUpper, indexedBlockMass, flattenIndexedBlocks,
            massCurrent] at hmassRec ⊢
          linarith [hBu0]
        · have hnextEq : next = [B] := by
            simp [next, conormalBlockStep, massCurrent, hfit]
          rw [hnextEq]
          rw [hnextEq] at hmassRec
          simp [indexedBlocksUpper, indexedBlockMass, flattenIndexedBlocks,
            massCurrent] at hmassRec ⊢
          have hlt : massCurrent < u B.1 := lt_of_not_ge hfit
          have hlt' : ((flattenIndexedBlocks current).map w).sum < u B.1 := by
            simpa [massCurrent] using hlt
          simp [flattenIndexedBlocks] at hlt'
          linarith
      · intro C hC
        rcases hrec.2.2.2 C hC with hCn | hCBs
        · rcases hnext with happ | hreset
          · rw [happ] at hCn
            rcases List.mem_append.mp hCn with hCold | hsingle
            · exact Or.inl hCold
            · have : C = B := by simpa using hsingle
              subst C
              exact Or.inr (by simp)
          · rw [hreset] at hCn
            have : C = B := by simpa using hCn
            subst C
            exact Or.inr (by simp)
        · exact Or.inr (by simp [hCBs])

lemma conormalBlockScan_properties {A : Type*} (w : A → ℝ)
    (u : ℕ → ℝ) (Bs : List (ℕ × List A))
    (hblockLen : ∀ B ∈ Bs, 2 ≤ B.2.length)
    (hblockSlow : ∀ B ∈ Bs, SeededSlow w B.2)
    (hw0 : ∀ B ∈ Bs, ∀ a ∈ B.2, 0 ≤ w a)
    (hwUpper : ∀ B ∈ Bs, ∀ a ∈ B.2, w a ≤ u B.1) :
    let Cs := conormalBlockScan w u Bs
    (Bs ≠ [] → 2 ≤ (flattenIndexedBlocks Cs).length) ∧
    SeededSlow w (flattenIndexedBlocks Cs) ∧
    indexedBlocksMass w Bs ≤
      indexedBlocksMass w Cs + indexedBlocksUpper u Bs ∧
    (∀ B ∈ Cs, B ∈ Bs) := by
  simpa [conormalBlockScan, indexedBlocksMass] using
    (conormalBlockFold_properties w u [] Bs (Or.inl rfl)
      hblockLen hblockSlow hw0 hwUpper)

lemma conormalBlockScan_mass_gt_one {A : Type*} (w : A → ℝ)
    (u : ℕ → ℝ) (Bs : List (ℕ × List A))
    (hblockLen : ∀ B ∈ Bs, 2 ≤ B.2.length)
    (hblockSlow : ∀ B ∈ Bs, SeededSlow w B.2)
    (hw0 : ∀ B ∈ Bs, ∀ a ∈ B.2, 0 ≤ w a)
    (hwUpper : ∀ B ∈ Bs, ∀ a ∈ B.2, w a ≤ u B.1)
    (hmass : 1 + indexedBlocksUpper u Bs < indexedBlocksMass w Bs) :
    1 < indexedBlocksMass w (conormalBlockScan w u Bs) := by
  have h := (conormalBlockScan_properties w u Bs hblockLen hblockSlow hw0 hwUpper).2.2.1
  linarith

lemma conormalBlockFold_suffix {A : Type*} (w : A → ℝ) (u : ℕ → ℝ)
    (current Bs : List (ℕ × List A)) :
    ∃ pre, pre ++ Bs.foldl (conormalBlockStep w u) current = current ++ Bs := by
  induction Bs generalizing current with
  | nil => exact ⟨[], by simp⟩
  | cons B Bs ih =>
      let next := conormalBlockStep w u current B
      obtain ⟨pre, hpre⟩ := ih next
      by_cases hfit : u B.1 ≤ ((flattenIndexedBlocks current).map w).sum
      · have hnext : next = current ++ [B] := by
          simp [next, conormalBlockStep, hfit]
        refine ⟨pre, ?_⟩
        change pre ++ Bs.foldl (conormalBlockStep w u) next = current ++ B :: Bs
        calc
          pre ++ Bs.foldl (conormalBlockStep w u) next = next ++ Bs := hpre
          _ = current ++ B :: Bs := by rw [hnext]; simp [List.append_assoc]
      · have hnext : next = [B] := by
          simp [next, conormalBlockStep, hfit]
        refine ⟨current ++ pre, ?_⟩
        change (current ++ pre) ++ Bs.foldl (conormalBlockStep w u) next =
          current ++ B :: Bs
        calc
          (current ++ pre) ++ Bs.foldl (conormalBlockStep w u) next =
              current ++ (pre ++ Bs.foldl (conormalBlockStep w u) next) := by
                simp [List.append_assoc]
          _ = current ++ (next ++ Bs) := by rw [hpre]
          _ = current ++ B :: Bs := by rw [hnext]; simp

lemma conormalBlockScan_suffix {A : Type*} (w : A → ℝ) (u : ℕ → ℝ)
    (Bs : List (ℕ × List A)) :
    ∃ pre, pre ++ conormalBlockScan w u Bs = Bs := by
  simpa [conormalBlockScan] using conormalBlockFold_suffix w u [] Bs

def primeReciprocalWeight (p : ℕ) : ℝ := (p : ℝ)⁻¹

def dyadicReciprocalUpper (t : ℕ) : ℝ := ((2 ^ t : ℕ) : ℝ)⁻¹

lemma seededSlow_of_dyadic_list {x : ℕ} {L : List ℕ}
    (hx : 0 < x) (hlen : 2 ≤ L.length)
    (hL : ∀ p ∈ L, x ≤ p ∧ p < 2 * x) :
    SeededSlow primeReciprocalWeight L := by
  cases L with
  | nil => simp at hlen
  | cons a L =>
      cases L with
      | nil => simp at hlen
      | cons b rest =>
          have hxR : (0 : ℝ) < x := by exact_mod_cast hx
          have h2xR : (0 : ℝ) < 2 * x := by positivity
          have ha := hL a (by simp)
          have hb := hL b (by simp)
          have haNat : 0 < a := hx.trans_le ha.1
          have hbNat : 0 < b := hx.trans_le hb.1
          have haPos : (0 : ℝ) < a := by exact_mod_cast haNat
          have hbPos : (0 : ℝ) < b := by exact_mod_cast hbNat
          have haLower : ((2 * x : ℕ) : ℝ)⁻¹ ≤ (a : ℝ)⁻¹ := by
            have hcast : (a : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast ha.2.le
            simpa only [Nat.cast_mul, Nat.cast_ofNat] using
              (inv_le_inv₀ h2xR haPos).2 hcast
          have hbUpper : (b : ℝ)⁻¹ ≤ (x : ℝ)⁻¹ := by
            apply (inv_le_inv₀ hbPos hxR).2
            exact_mod_cast hb.1
          have hinvDouble : (x : ℝ)⁻¹ =
              2 * ((2 * x : ℕ) : ℝ)⁻¹ := by
            push_cast
            field_simp
          change (b : ℝ)⁻¹ ≤ 2 * (a : ℝ)⁻¹ ∧
            WeightedSlowExtension primeReciprocalWeight
              ((a : ℝ)⁻¹ + (b : ℝ)⁻¹) rest
          constructor
          · calc
              (b : ℝ)⁻¹ ≤ (x : ℝ)⁻¹ := hbUpper
              _ = 2 * ((2 * x : ℕ) : ℝ)⁻¹ := by
                exact hinvDouble
              _ ≤ 2 * (a : ℝ)⁻¹ :=
                mul_le_mul_of_nonneg_left haLower (by norm_num)
          · apply weightedSlowExtension_of_bounded
            · intro p hp
              exact inv_nonneg.mpr (by positivity)
            · have hbLower : ((2 * x : ℕ) : ℝ)⁻¹ ≤ (b : ℝ)⁻¹ := by
                have hcast : (b : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast hb.2.le
                simpa only [Nat.cast_mul, Nat.cast_ofNat] using
                  (inv_le_inv₀ h2xR hbPos).2 hcast
              calc
                (x : ℝ)⁻¹ =
                    2 * ((2 * x : ℕ) : ℝ)⁻¹ := by
                      exact hinvDouble
                _ ≤ (a : ℝ)⁻¹ + (b : ℝ)⁻¹ := by linarith
            · intro p hp
              have hpData := hL p (by simp [hp])
              unfold primeReciprocalWeight
              have hpNat : 0 < p := hx.trans_le hpData.1
              have hpR : (0 : ℝ) < p := by exact_mod_cast hpNat
              apply (inv_le_inv₀ hpR hxR).2
              exact_mod_cast hpData.1

lemma seededSlow_dyadic_primeBlock {t : ℕ} {P : Finset ℕ}
    (hblock : PrimeBlock (2 ^ t) P) (hcard : 2 ≤ P.card) :
    SeededSlow primeReciprocalWeight (P.sort (· ≥ ·)) := by
  apply seededSlow_of_dyadic_list
    (by exact pow_pos (by norm_num : 0 < 2) t) (by simpa)
  intro p hp
  exact (hblock p (by simpa using hp)).2

lemma SeededSlow.suffix_after_prefix {A : Type*} {w : A → ℝ}
    {P Q : List A} (hP : 2 ≤ P.length) (hslow : SeededSlow w (P ++ Q)) :
    WeightedSlowExtension w ((P.map w).sum) Q := by
  cases P with
  | nil => simp at hP
  | cons a P =>
      cases P with
      | nil => simp at hP
      | cons b rest =>
          change w b ≤ 2 * w a ∧
            WeightedSlowExtension w (w a + w b) (rest ++ Q) at hslow
          have htail := (weightedSlowExtension_append.mp hslow.2).2
          simpa [add_assoc] using htail

def complementList (N : ℕ) (L : List ℕ) : List ℕ :=
  L.map (fun p => N / p)

lemma cast_sum_complementList {N : ℕ} {L : List ℕ}
    (hdiv : ∀ p ∈ L, p ∣ N) :
    ((complementList N L).sum : ℝ) =
      (N : ℝ) * (L.map primeReciprocalWeight).sum := by
  induction L with
  | nil => simp [complementList]
  | cons p L ih =>
      have hpdiv := hdiv p (by simp)
      have htail : ∀ q ∈ L, q ∣ N := by
        intro q hq; exact hdiv q (by simp [hq])
      change ((N / p + (complementList N L).sum : ℕ) : ℝ) =
        (N : ℝ) *
          (primeReciprocalWeight p + (L.map primeReciprocalWeight).sum)
      rw [Nat.cast_add, Nat.cast_div_charZero hpdiv, ih htail]
      simp only [primeReciprocalWeight, div_eq_mul_inv]
      ring

lemma weightedSlow_reciprocal_to_complements {N F : ℕ} {S : ℝ}
    {L : List ℕ} (hN : 0 < N)
    (hpos : ∀ p ∈ L, 0 < p) (hdiv : ∀ p ∈ L, p ∣ N)
    (hFS : (F : ℝ) = (N : ℝ) * S)
    (hslow : WeightedSlowExtension primeReciprocalWeight S L) :
    SlowExtension F (complementList N L) := by
  induction L generalizing F S with
  | nil => trivial
  | cons p L ih =>
      have hp : 0 < p := hpos p (by simp)
      have hpdiv : p ∣ N := hdiv p (by simp)
      have hcast : ((N / p : ℕ) : ℝ) =
          (N : ℝ) * primeReciprocalWeight p := by
        rw [Nat.cast_div_charZero hpdiv]
        simp [primeReciprocalWeight, div_eq_mul_inv]
      change N / p ≤ F + 1 ∧
        SlowExtension (F + N / p) (complementList N L)
      constructor
      · have hNR : (0 : ℝ) ≤ N := by positivity
        have hdR : ((N / p : ℕ) : ℝ) ≤ (F : ℝ) := by
          rw [hcast, hFS]
          exact mul_le_mul_of_nonneg_left hslow.1 hNR
        have hd : N / p ≤ F := by exact_mod_cast hdR
        omega
      · apply ih (S := S + primeReciprocalWeight p)
        · intro q hq; exact hpos q (by simp [hq])
        · intro q hq; exact hdiv q (by simp [hq])
        · push_cast
          rw [hFS, hcast]
          ring
        · exact hslow.2

lemma SeededSlow.complement_tail {N : ℕ} {P Q : List ℕ}
    (hN : 0 < N) (hP : 2 ≤ P.length)
    (hpos : ∀ p ∈ P ++ Q, 0 < p)
    (hdiv : ∀ p ∈ P ++ Q, p ∣ N)
    (hslow : SeededSlow primeReciprocalWeight (P ++ Q)) :
    SlowExtension (complementList N P).sum (complementList N Q) := by
  apply weightedSlow_reciprocal_to_complements hN
  · intro q hq; exact hpos q (by simp [hq])
  · intro q hq; exact hdiv q (by simp [hq])
  · exact cast_sum_complementList fun p hp => hdiv p (by simp [hp])
  · exact hslow.suffix_after_prefix hP

lemma sum_complementList_gt_of_mass_gt_one {N : ℕ} {L : List ℕ}
    (hN : 0 < N) (hdiv : ∀ p ∈ L, p ∣ N)
    (hmass : 1 < (L.map primeReciprocalWeight).sum) :
    N < (complementList N L).sum := by
  have hcast := cast_sum_complementList hdiv
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have : (N : ℝ) < ((complementList N L).sum : ℝ) := by
    rw [hcast]
    nlinarith
  exact_mod_cast this

lemma SlowExtension.mono_start {F G : ℕ} {L : List ℕ}
    (hFG : F ≤ G) (hslow : SlowExtension F L) : SlowExtension G L := by
  induction L generalizing F G with
  | nil => trivial
  | cons d L ih =>
      change d ≤ G + 1 ∧ SlowExtension (G + d) L
      constructor
      · exact hslow.1.trans (Nat.add_le_add_right hFG 1)
      · exact ih (Nat.add_le_add_right hFG d) hslow.2

lemma complementList_nodup {N : ℕ} {L : List ℕ}
    (hN : 0 < N) (hL : L.Nodup) (hdiv : ∀ q ∈ L, q ∣ N) :
    (complementList N L).Nodup := by
  rw [complementList, List.nodup_map_iff_inj_on hL]
  intro a ha b hb hab
  exact complementDivisor_injOn hN (hdiv a ha) (hdiv b hb) hab

lemma complement_kernel_blockDegree {P : Finset ℕ} {qs : List ℕ} {q : ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hqsNodup : qs.Nodup) (hqsPrime : ∀ z ∈ qs, z.Prime)
    (hdisj : Disjoint qs.toFinset P) (hq : q ∈ qs) :
    (((((∏ p ∈ P, p) * qs.prod) / q).primeFactors ∩ P).card) = P.card := by
  let R := qs.erase q
  have hqpos : 0 < q := (hqsPrime q hq).pos
  have hRnodup : R.Nodup := hqsNodup.erase q
  have hRprime : ∀ z ∈ R, z.Prime := by
    intro z hz
    exact hqsPrime z (List.mem_of_mem_erase hz)
  have hRsub : R.toFinset ⊆ qs.toFinset := by
    intro z hz
    have hzR : z ∈ R := by simpa using hz
    simpa using List.mem_of_mem_erase hzR
  have hRdisj : Disjoint R.toFinset P := hdisj.mono_left hRsub
  have hRprod : 0 < R.prod := List.prod_pos fun z hz ↦ (hRprime z hz).pos
  have hRFactors := primeFactors_list_prod hRnodup hRprime
  have hLayer : (∏ p ∈ P, p) ∈ productLayer P P.card := by
    apply Finset.mem_image.mpr
    exact ⟨P, Finset.mem_powersetCard.mpr ⟨Finset.Subset.rfl, rfl⟩, rfl⟩
  have hdegree := blockPrimeFactors_mul_productLayer
    (k := R.prod) hRprod hprime (by simpa [hRFactors] using hRdisj) hLayer
  have hprodErase : q * R.prod = qs.prod := by
    simpa [R] using List.prod_erase hq
  have hkernel : (∏ p ∈ P, p) * qs.prod =
      q * (R.prod * (∏ p ∈ P, p)) := by
    rw [← hprodErase]
    ring
  have hquot : ((∏ p ∈ P, p) * qs.prod) / q =
      R.prod * (∏ p ∈ P, p) := by
    rw [hkernel, Nat.mul_div_cancel_left _ hqpos]
  rw [hquot]
  exact hdegree

lemma coreExtension_disjoint_complementList {p : ℕ} {P : Finset ℕ}
    {qs : List ℕ} (hPcard : 4 ≤ P.card)
    (hprime : ∀ z ∈ P, z.Prime)
    (hqsNodup : qs.Nodup) (hqsPrime : ∀ z ∈ qs, z.Prime)
    (hdisj : Disjoint qs.toFinset P) :
    ∀ d ∈ coreExtension p P qs,
      ∀ e ∈ complementList ((∏ z ∈ P, z) * qs.prod) qs, d ≠ e := by
  intro d hd e he hde
  have hdDegree := coreExtension_blockDegree_lt hPcard hprime
    hqsNodup hqsPrime hdisj hd
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
  have hqDegree := complement_kernel_blockDegree hprime hqsNodup
    hqsPrime hdisj hq
  rw [hde] at hdDegree
  omega

lemma strongBlockDivisors_disjoint_complementList {p : ℕ} {P : Finset ℕ}
    {qs : List ℕ} (hp : p ∈ P) (hPcard : 4 ≤ P.card)
    (hprime : ∀ z ∈ P, z.Prime)
    (hqsNodup : qs.Nodup) (hqsPrime : ∀ z ∈ qs, z.Prime)
    (hdisj : Disjoint qs.toFinset P) :
    ∀ d ∈ strongBlockDivisors p P,
      ∀ e ∈ complementList ((∏ z ∈ P, z) * qs.prod) qs, d ≠ e := by
  intro d hd e he hde
  have hdBase := strongBlockDivisors_subset_baseProductLayers hp hd
  have hdDegree : (d.primeFactors ∩ P).card < P.card := by
    rcases Finset.mem_union.mp hdBase with hdOne | hdTwo
    · have hdeg := blockPrimeFactors_mul_productLayer
        (k := 1) (P := P) (r := 1) (d := d) (by norm_num) hprime
        (by simp) hdOne
      simp only [one_mul] at hdeg
      omega
    · have hdeg := blockPrimeFactors_mul_productLayer
        (k := 1) (P := P) (r := 2) (d := d) (by norm_num) hprime
        (by simp) hdTwo
      simp only [one_mul] at hdeg
      omega
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
  have hqDegree := complement_kernel_blockDegree hprime hqsNodup
    hqsPrime hdisj hq
  rw [hde] at hdDegree
  omega

lemma complementList_mem_kernelProper {P : Finset ℕ} {qs : List ℕ}
    (hPpos : 0 < ∏ p ∈ P, p) (hqsNodup : qs.Nodup)
    (hqsLarge : ∀ q ∈ qs, 1 < q) :
    ∀ d ∈ complementList ((∏ p ∈ P, p) * qs.prod) qs,
      d ∈ ((∏ p ∈ P, p) * qs.prod).properDivisors := by
  intro d hd
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
  have hqDivQs : q ∣ qs.prod := by
    have hsingle := finsetSubproduct_dvd_listProd hqsNodup
      (K := {q}) (by simp [hq])
    simpa using hsingle
  have hqDivN : q ∣ (∏ p ∈ P, p) * qs.prod :=
    dvd_mul_of_dvd_right hqDivQs _
  have hN : 0 < (∏ p ∈ P, p) * qs.prod :=
    Nat.mul_pos hPpos (List.prod_pos fun q hq ↦ by have := hqsLarge q hq; omega)
  exact Nat.mem_properDivisors.mpr
    ⟨Nat.div_dvd_of_dvd hqDivN, Nat.div_lt_self hN (hqsLarge q hq)⟩

lemma complement_block_mem_core {p z : ℕ} {P : Finset ℕ} {qs : List ℕ}
    (hPcard : 4 ≤ P.card) (hz : z ∈ P) (hzPrime : z.Prime) :
    (((∏ q ∈ P, q) * qs.prod) / z) ∈ coreExtension p P qs := by
  let A := P.erase z
  have hAcard : A.card = P.card - 1 := by
    simp [A, Finset.card_erase_of_mem hz]
  have hAprod : z * (∏ q ∈ A, q) = ∏ q ∈ P, q := by
    simpa [A] using Finset.mul_prod_erase P id hz
  have hquotP : (∏ q ∈ P, q) / z = ∏ q ∈ A, q := by
    exact (Nat.eq_div_of_mul_eq_right hzPrime.ne_zero hAprod).symm
  have hLayer : (∏ q ∈ A, q) ∈ productLayer P (P.card - 1) := by
    apply Finset.mem_image.mpr
    refine ⟨A, Finset.mem_powersetCard.mpr ⟨Finset.erase_subset _ _, hAcard⟩, rfl⟩
  have hRun : qs.prod * (∏ q ∈ A, q) ∈
      productLayerRun P qs.prod 2 (P.card - 3) := by
    apply mem_productLayerRun_of_mem (j := P.card - 1)
    · omega
    · omega
    · exact hLayer
  have hzDiv : z ∣ ∏ q ∈ P, q := Finset.dvd_prod_of_mem id hz
  have hquot : ((∏ q ∈ P, q) * qs.prod) / z =
      qs.prod * (∏ q ∈ A, q) := by
    rw [Nat.mul_comm (∏ q ∈ P, q) qs.prod]
    rw [Nat.mul_div_assoc _ hzDiv, hquotP]
  rw [hquot]
  simp [coreExtension, hRun]

lemma sum_complement_block_le_core {t p : ℕ} {P : Finset ℕ}
    {qs : List ℕ} (ht : 12 ≤ t) (hblock : PrimeBlock (2 ^ t) P)
    (hp : p ∈ P) (hcard : 4 ≤ P.card)
    (hqsNodup : qs.Nodup) (hqs : ∀ q ∈ qs, 0 < q ∧ 4 < q) :
    (complementList ((∏ q ∈ P, q) * qs.prod)
        (P.sort (fun a b ↦ a ≥ b))).sum ≤ (coreExtension p P qs).sum := by
  let N := (∏ q ∈ P, q) * qs.prod
  let PL := P.sort (fun a b ↦ a ≥ b)
  let C := complementList N PL
  let K := coreExtension p P qs
  have hN : 0 < N := Nat.mul_pos
    (Finset.prod_pos fun q hq ↦ (hblock q hq).1.pos)
    (List.prod_pos fun q hq ↦ (hqs q hq).1)
  have hPLnodup : PL.Nodup := Finset.sort_nodup _ _
  have hPLdiv : ∀ q ∈ PL, q ∣ N := by
    intro q hq
    have hqP : q ∈ P := (Finset.mem_sort (s := P) (fun a b ↦ a ≥ b)).mp hq
    exact (Finset.dvd_prod_of_mem id hqP).mul_right qs.prod
  have hCnodup : C.Nodup := complementList_nodup hN hPLnodup hPLdiv
  have hKnodup : K.Nodup := coreExtension_nodup ht hblock hqsNodup hqs
  have hsubset : C.toFinset ⊆ K.toFinset := by
    intro d hd
    have hdC : d ∈ C := by simpa using hd
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hdC
    have hqP : q ∈ P :=
      (Finset.mem_sort (s := P) (fun a b ↦ a ≥ b)).mp hq
    have hmem := complement_block_mem_core (p := p) (qs := qs)
      hcard hqP (hblock q hqP).1
    simpa [N, K] using hmem
  calc
    C.sum = C.toFinset.sum id := by
      symm
      calc
        C.toFinset.sum id = (C.map id).sum := List.sum_toFinset id hCnodup
        _ = C.sum := by simp
    _ ≤ K.toFinset.sum id := Finset.sum_le_sum_of_subset hsubset
    _ = K.sum := by
      calc
        K.toFinset.sum id = (K.map id).sum := List.sum_toFinset id hKnodup
        _ = K.sum := by simp

/-! ## Finite dyadic blocks of prime divisors -/

/-- The prime divisors in the half-open dyadic block whose binary logarithm
is `t`.  Defining the block by `Nat.log` makes the finite partition literal;
the usual inequalities are recovered below. -/
def dyadicPrimePart (S : Finset ℕ) (t : ℕ) : Finset ℕ :=
  S.filter fun p => Nat.log 2 p = t

lemma mem_dyadicPrimePart {S : Finset ℕ} {t p : ℕ} :
    p ∈ dyadicPrimePart S t ↔ p ∈ S ∧ Nat.log 2 p = t := by
  simp [dyadicPrimePart]

lemma dyadicPrimePart_primeBlock {S : Finset ℕ} {t : ℕ}
    (hprime : ∀ p ∈ S, p.Prime) :
    PrimeBlock (2 ^ t) (dyadicPrimePart S t) := by
  intro p hp
  have hpData := mem_dyadicPrimePart.mp hp
  have hpPrime := hprime p hpData.1
  refine ⟨hpPrime, ?_, ?_⟩
  · simpa [hpData.2] using Nat.pow_log_le_self 2 hpPrime.ne_zero
  · have hu := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
    rw [hpData.2, Nat.pow_succ] at hu
    simpa [Nat.mul_comm] using hu

lemma dyadicPrimePart_mono {S T : Finset ℕ} (hST : S ⊆ T) (t : ℕ) :
    dyadicPrimePart S t ⊆ dyadicPrimePart T t := by
  intro p hp
  exact mem_dyadicPrimePart.mpr
    ⟨hST (mem_dyadicPrimePart.mp hp).1, (mem_dyadicPrimePart.mp hp).2⟩

lemma disjoint_dyadicPrimePart {S : Finset ℕ} {s t : ℕ} (hst : s ≠ t) :
    Disjoint (dyadicPrimePart S s) (dyadicPrimePart S t) := by
  rw [Finset.disjoint_left]
  intro p hps hpt
  exact hst ((mem_dyadicPrimePart.mp hps).2.symm.trans
    (mem_dyadicPrimePart.mp hpt).2)

/-- All rich dyadic indices above `T`.  The very coarse finite range is
enough: `log₂ p ≤ p ≤ ∑ S` for every prime `p ∈ S`. -/
def richDyadicIndices (S : Finset ℕ) (T : ℕ) : Finset ℕ :=
  (Finset.range (S.sum id + 1)).filter fun t =>
    T ≤ t ∧ richCardThreshold t < (dyadicPrimePart S t).card

lemma mem_richDyadicIndices {S : Finset ℕ} {T t : ℕ} :
    t ∈ richDyadicIndices S T ↔
      t < S.sum id + 1 ∧ T ≤ t ∧
        richCardThreshold t < (dyadicPrimePart S t).card := by
  simp [richDyadicIndices, and_assoc]

/-- Rich blocks, ordered from the largest scale down to the smallest. -/
def richDyadicBlocks (S : Finset ℕ) (T : ℕ) : List (ℕ × List ℕ) :=
  (richDyadicIndices S T).sort (· ≥ ·) |>.map fun t =>
    (t, (dyadicPrimePart S t).sort (· ≥ ·))

lemma mem_richDyadicBlocks {S : Finset ℕ} {T : ℕ} {B : ℕ × List ℕ} :
    B ∈ richDyadicBlocks S T ↔
      ∃ t ∈ richDyadicIndices S T,
        B = (t, (dyadicPrimePart S t).sort (· ≥ ·)) := by
  simp only [richDyadicBlocks, List.mem_map, Finset.mem_sort]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩

lemma richDyadicBlocks_length_two {S : Finset ℕ} {T : ℕ}
    {B : ℕ × List ℕ} (hB : B ∈ richDyadicBlocks S T) :
    2 ≤ B.2.length := by
  obtain ⟨t, ht, rfl⟩ := mem_richDyadicBlocks.mp hB
  have hc := (mem_richDyadicIndices.mp ht).2.2
  simp only [Finset.length_sort]
  have hfour : 4 ≤ 8 * 2 ^ (3 * (t / 4)) + 4 := by omega
  have : 4 ≤ richCardThreshold t :=
    hfour.trans (le_max_right _ _)
  omega

lemma richDyadicBlocks_seededSlow {S : Finset ℕ} {T : ℕ}
    (hprime : ∀ p ∈ S, p.Prime) {B : ℕ × List ℕ}
    (hB : B ∈ richDyadicBlocks S T) :
    SeededSlow primeReciprocalWeight B.2 := by
  obtain ⟨t, ht, rfl⟩ := mem_richDyadicBlocks.mp hB
  apply seededSlow_dyadic_primeBlock (dyadicPrimePart_primeBlock hprime)
  simpa using richDyadicBlocks_length_two hB

lemma richDyadicBlocks_weight_nonneg {S : Finset ℕ} {T : ℕ}
    {B : ℕ × List ℕ} (hB : B ∈ richDyadicBlocks S T)
    {p : ℕ} (hp : p ∈ B.2) :
    0 ≤ primeReciprocalWeight p := by
  simp [primeReciprocalWeight]

lemma richDyadicBlocks_weight_le_upper {S : Finset ℕ} {T : ℕ}
    (hprime : ∀ p ∈ S, p.Prime) {B : ℕ × List ℕ}
    (hB : B ∈ richDyadicBlocks S T) {p : ℕ} (hp : p ∈ B.2) :
    primeReciprocalWeight p ≤ dyadicReciprocalUpper B.1 := by
  obtain ⟨t, ht, rfl⟩ := mem_richDyadicBlocks.mp hB
  have hpFin : p ∈ dyadicPrimePart S t := by simpa using hp
  have hpLower := (dyadicPrimePart_primeBlock hprime p hpFin).2.1
  have hxpos : 0 < 2 ^ t := pow_pos (by norm_num) _
  have hppos : 0 < p := hxpos.trans_le hpLower
  exact (inv_le_inv₀ (by exact_mod_cast hppos) (by exact_mod_cast hxpos)).2
    (by exact_mod_cast hpLower)

lemma sum_map_finset_sort {A M : Type*} [DecidableEq A] [AddCommMonoid M]
    (s : Finset A) (r : A → A → Prop) [DecidableRel r]
    [IsTrans A r] [Std.Antisymm r] [Std.Total r] (f : A → M) :
    ((s.sort r).map f).sum = ∑ a ∈ s, f a := by
  rw [← List.sum_toFinset f (Finset.sort_nodup s r), Finset.sort_toFinset]

lemma indexedBlocksMass_richDyadicBlocks (S : Finset ℕ) (T : ℕ) :
    indexedBlocksMass primeReciprocalWeight (richDyadicBlocks S T) =
      ∑ t ∈ richDyadicIndices S T,
        ∑ p ∈ dyadicPrimePart S t, primeReciprocalWeight p := by
  rw [richDyadicBlocks, indexedBlocksMass, List.map_map,
    sum_map_finset_sort]
  apply Finset.sum_congr rfl
  intro t ht
  exact sum_map_finset_sort (dyadicPrimePart S t) (· ≥ ·)
    primeReciprocalWeight

lemma indexedBlocksUpper_richDyadicBlocks (S : Finset ℕ) (T : ℕ) :
    indexedBlocksUpper dyadicReciprocalUpper (richDyadicBlocks S T) =
      ∑ t ∈ richDyadicIndices S T, dyadicReciprocalUpper t := by
  rw [richDyadicBlocks, indexedBlocksUpper, List.map_map,
    sum_map_finset_sort]
  rfl

lemma richDyadicBlocks_pairwise_index (S : Finset ℕ) (T : ℕ) :
    (richDyadicBlocks S T).Pairwise (fun A B ↦ B.1 ≤ A.1) := by
  have hs := Finset.pairwise_sort (richDyadicIndices S T) (· ≥ ·)
  exact hs.map (fun t ↦ (t, (dyadicPrimePart S t).sort (· ≥ ·)))
    (fun a b hab ↦ hab)

lemma richDyadicBlocks_nodup (S : Finset ℕ) (T : ℕ) :
    (richDyadicBlocks S T).Nodup := by
  apply (Finset.sort_nodup (richDyadicIndices S T) (· ≥ ·)).map
  intro a b hab
  exact congrArg Prod.fst hab

lemma flatten_richDyadicBlocks_nodup (S : Finset ℕ) (T : ℕ) :
    (flattenIndexedBlocks (richDyadicBlocks S T)).Nodup := by
  rw [flattenIndexedBlocks, List.nodup_flatMap]
  constructor
  · intro B hB
    obtain ⟨t, ht, rfl⟩ := mem_richDyadicBlocks.mp hB
    exact Finset.sort_nodup _ _
  · apply (richDyadicBlocks_nodup S T).imp_of_mem
    intro A B hA hB hne
    obtain ⟨s, hs, rfl⟩ := mem_richDyadicBlocks.mp hA
    obtain ⟨t, ht, rfl⟩ := mem_richDyadicBlocks.mp hB
    have hst : s ≠ t := by
      intro h
      subst t
      exact hne rfl
    change List.Disjoint
      ((dyadicPrimePart S s).sort (· ≥ ·))
      ((dyadicPrimePart S t).sort (· ≥ ·))
    rw [List.disjoint_iff_ne]
    intro p hps q hqt hpq
    subst q
    have hps' : p ∈ dyadicPrimePart S s := by simpa using hps
    have hpt' : p ∈ dyadicPrimePart S t := by simpa using hqt
    exact (Finset.disjoint_left.mp (disjoint_dyadicPrimePart hst)) hps' hpt'

lemma richCardThreshold_nat_bound {t : ℕ} (ht : 1 ≤ t) :
    richCardThreshold t ≤
      4 * (2 ^ t / t ^ 2 +
        t ^ 2 * (t ^ 2 + 1) * 2 ^ (t - t / 4) + 2) +
      2 * t ^ 2 * (t ^ 4 + 2 * 2 ^ (t / 4 + t / 2) * t ^ 3) +
      8 * 2 ^ (3 * (t / 4)) + 5 := by
  let g := t ^ 2
  let x := 2 ^ t
  let q := (g + 1) * 2 ^ (t - t / 4)
  let a := x + g * (g * q)
  have hg : 0 < g := by
    exact pow_pos (by omega) _
  have hdiv : a / g ≤ x / g + g * q + 1 := by
    calc
      a / g ≤ x / g + (g * (g * q)) / g + 1 := by
        simpa [a] using Nat.add_div_le_div_add_div_add_one x (g * (g * q)) g
      _ = x / g + g * q + 1 := by rw [Nat.mul_div_cancel_left _ hg]
  have hdense : denseCardThreshold t ≤
      4 * (x / g + g * q + 2) +
        2 * g * (g ^ 2 + 2 * 2 ^ (t / 4 + t / 2) * t ^ 3) := by
    rw [denseCardThreshold]
    have hm : denseM t = g ^ 2 + 2 * 2 ^ (t / 4 + t / 2) * t ^ 3 := by
      simp only [denseM, denseG, denseK, denseS, g]
      rw [Nat.pow_add]
      ring
    rw [hm]
    change 4 * ((2 ^ t + g * (g * denseQ t)) / g + 1) +
        2 * g * (g ^ 2 + 2 * 2 ^ (t / 4 + t / 2) * t ^ 3) ≤ _
    have ha : 2 ^ t + g * (g * denseQ t) = a := by
      simp [a, x, q, denseQ, denseG, denseH, g]
    rw [ha]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 4 (by omega)) _
  have hmax : richCardThreshold t ≤
      (denseCardThreshold t + 1) + (8 * 2 ^ (3 * (t / 4)) + 4) := by
    rw [richCardThreshold]
    exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  calc
    richCardThreshold t ≤
        (denseCardThreshold t + 1) + (8 * 2 ^ (3 * (t / 4)) + 4) := hmax
    _ ≤ (4 * (x / g + g * q + 2) +
          2 * g * (g ^ 2 + 2 * 2 ^ (t / 4 + t / 2) * t ^ 3) + 1) +
        (8 * 2 ^ (3 * (t / 4)) + 4) := by omega
    _ = 4 * (2 ^ t / t ^ 2 +
          t ^ 2 * (t ^ 2 + 1) * 2 ^ (t - t / 4) + 2) +
        2 * t ^ 2 * (t ^ 4 + 2 * 2 ^ (t / 4 + t / 2) * t ^ 3) +
        8 * 2 ^ (3 * (t / 4)) + 5 := by
      simp only [x, g, q]
      ring

def richThresholdDensity (t : ℕ) : ℝ :=
  (richCardThreshold t : ℝ) * dyadicReciprocalUpper t

lemma pow_sub_ratio_eq_inv {q t : ℕ} (hqt : q ≤ t) :
    ((2 ^ (t - q) : ℕ) : ℝ) * (((2 ^ t : ℕ) : ℝ)⁻¹) =
      (((2 ^ q : ℕ) : ℝ)⁻¹) := by
  have hpow : (2 ^ t : ℕ) = 2 ^ (t - q) * 2 ^ q := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hqt]
  rw [hpow]
  push_cast
  field_simp

lemma pow_ratio_le_inv_floor_four {a t : ℕ}
    (ha : a + t / 4 ≤ t) :
    ((2 ^ a : ℕ) : ℝ) * (((2 ^ t : ℕ) : ℝ)⁻¹) ≤
      (((2 ^ (t / 4) : ℕ) : ℝ)⁻¹) := by
  have ha' : a ≤ t - t / 4 := by omega
  have hp : 2 ^ a ≤ 2 ^ (t - t / 4) :=
    Nat.pow_le_pow_right (by norm_num) ha'
  have hcast : ((2 ^ a : ℕ) : ℝ) ≤ (2 ^ (t - t / 4) : ℕ) := by
    exact_mod_cast hp
  calc
    ((2 ^ a : ℕ) : ℝ) * (((2 ^ t : ℕ) : ℝ)⁻¹) ≤
        ((2 ^ (t - t / 4) : ℕ) : ℝ) * (((2 ^ t : ℕ) : ℝ)⁻¹) := by
          gcongr
    _ = (((2 ^ (t / 4) : ℕ) : ℝ)⁻¹) :=
      pow_sub_ratio_eq_inv (Nat.div_le_self _ _)

lemma richThresholdDensity_le {t : ℕ} (ht : 1 ≤ t) :
    richThresholdDensity t ≤
      4 / (t : ℝ) ^ 2 +
        100 * ((t : ℝ) + 1) ^ 6 * (((2 ^ (t / 4) : ℕ) : ℝ)⁻¹) := by
  let q := t / 4
  let X : ℝ := ((2 ^ t : ℕ) : ℝ)
  let I : ℝ := (((2 ^ q : ℕ) : ℝ)⁻¹)
  let P : ℝ := ((t : ℝ) + 1) ^ 6
  have htR : (0 : ℝ) < t := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht)
  have hXR : 0 < X := by simp [X]
  have hIR : 0 < I := by simp [I]
  have hPR : 1 ≤ P := by
    dsimp [P]
    have hbase : (1 : ℝ) < (t : ℝ) + 1 := by linarith
    simpa only [pow_zero] using
      (pow_le_pow_iff_right₀ hbase).2 (by norm_num : 0 ≤ (6 : ℕ))
  have hdiv : (((2 ^ t / t ^ 2 : ℕ) : ℝ) * X⁻¹) ≤ 1 / (t : ℝ) ^ 2 := by
    have hc : ((2 ^ t / t ^ 2 : ℕ) : ℝ) ≤
        ((2 ^ t : ℕ) : ℝ) / ((t ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
    have hnon : 0 ≤ X⁻¹ := inv_nonneg.mpr hXR.le
    apply (mul_le_mul_of_nonneg_right hc hnon).trans_eq
    dsimp [X]
    push_cast
    field_simp
  have hqle : q ≤ t := by exact Nat.div_le_self _ _
  have hA : ((2 ^ (t - t / 4) : ℕ) : ℝ) * X⁻¹ = I := by
    simpa [q, X, I] using pow_sub_ratio_eq_inv hqle
  have hB : ((2 ^ (t / 4 + t / 2) : ℕ) : ℝ) * X⁻¹ ≤ I := by
    have he : t / 4 + t / 2 + t / 4 ≤ t := by omega
    simpa [q, X, I] using
      pow_ratio_le_inv_floor_four (a := t / 4 + t / 2) (t := t) he
  have hC : ((2 ^ (3 * (t / 4)) : ℕ) : ℝ) * X⁻¹ ≤ I := by
    have he : 3 * (t / 4) + t / 4 ≤ t := by
      have := Nat.mod_lt t (by norm_num : 0 < 4)
      have := Nat.div_add_mod t 4
      omega
    simpa [q, X, I] using
      pow_ratio_le_inv_floor_four (a := 3 * (t / 4)) (t := t) he
  have hOne : X⁻¹ ≤ I := by
    have he : 0 + t / 4 ≤ t := by omega
    simpa [X, I, q] using pow_ratio_le_inv_floor_four (a := 0) (t := t) he
  have hbase : (1 : ℝ) < (t : ℝ) + 1 := by linarith
  have hpow (k : ℕ) (hk : k ≤ 6) : (t : ℝ) ^ k ≤ P := by
    calc
      (t : ℝ) ^ k ≤ ((t : ℝ) + 1) ^ k :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ ((t : ℝ) + 1) ^ 6 :=
        (pow_le_pow_iff_right₀ hbase).2 hk
      _ = P := rfl
  have hpoly4 : ((t : ℝ) ^ 2 * ((t : ℝ) ^ 2 + 1)) ≤ 2 * P := by
    nlinarith [hpow 2 (by norm_num), hpow 4 (by norm_num)]
  have hpoly6 : (t : ℝ) ^ 6 ≤ P := hpow 6 le_rfl
  have hpoly5 : (t : ℝ) ^ 5 ≤ P := hpow 5 (by norm_num)
  have hnat := richCardThreshold_nat_bound ht
  have hcast : (richCardThreshold t : ℝ) ≤
      (4 * (2 ^ t / t ^ 2 + t ^ 2 * (t ^ 2 + 1) *
          2 ^ (t - t / 4) + 2) +
        2 * t ^ 2 * (t ^ 4 + 2 * 2 ^ (t / 4 + t / 2) * t ^ 3) +
        8 * 2 ^ (3 * (t / 4)) + 5 : ℕ) := by exact_mod_cast hnat
  have hmain := mul_le_mul_of_nonneg_right hcast (inv_nonneg.mpr hXR.le)
  change richThresholdDensity t ≤ _
  rw [richThresholdDensity, dyadicReciprocalUpper]
  change (richCardThreshold t : ℝ) * X⁻¹ ≤ _
  calc
    (richCardThreshold t : ℝ) * X⁻¹ ≤
        ((4 * (2 ^ t / t ^ 2 + t ^ 2 * (t ^ 2 + 1) *
            2 ^ (t - t / 4) + 2) +
          2 * t ^ 2 * (t ^ 4 + 2 * 2 ^ (t / 4 + t / 2) * t ^ 3) +
          8 * 2 ^ (3 * (t / 4)) + 5 : ℕ) : ℝ) * X⁻¹ := hmain
    _ ≤ 4 / (t : ℝ) ^ 2 + 100 * P * I := by
      push_cast
      have h0 : (0 : ℝ) ≤ X⁻¹ := inv_nonneg.mpr hXR.le
      have hPI : 0 ≤ P * I := mul_nonneg (zero_le_one.trans hPR) hIR.le
      calc
        (4 * ((2 ^ t / t ^ 2 : ℕ) +
              (t : ℝ) ^ 2 * ((t : ℝ) ^ 2 + 1) *
                (2 : ℝ) ^ (t - t / 4) + 2) +
            2 * (t : ℝ) ^ 2 * ((t : ℝ) ^ 4 +
              2 * (2 : ℝ) ^ (t / 4 + t / 2) * (t : ℝ) ^ 3) +
            8 * (2 : ℝ) ^ (3 * (t / 4)) + 5) * X⁻¹ =
            4 * (((2 ^ t / t ^ 2 : ℕ) : ℝ) * X⁻¹) +
            4 * ((t : ℝ) ^ 2 * ((t : ℝ) ^ 2 + 1)) *
              ((2 : ℝ) ^ (t - t / 4) * X⁻¹) +
            8 * X⁻¹ + 2 * (t : ℝ) ^ 6 * X⁻¹ +
            4 * (t : ℝ) ^ 5 *
              ((2 : ℝ) ^ (t / 4 + t / 2) * X⁻¹) +
            8 * ((2 : ℝ) ^ (3 * (t / 4)) * X⁻¹) +
            5 * X⁻¹ := by ring
        _ ≤ 4 * (1 / (t : ℝ) ^ 2) +
            8 * P * I + 8 * P * I + 2 * P * I +
            4 * P * I + 8 * P * I + 5 * P * I := by
          have hA' : (2 : ℝ) ^ (t - t / 4) * X⁻¹ = I := by
            simpa using hA
          have hB' : (2 : ℝ) ^ (t / 4 + t / 2) * X⁻¹ ≤ I := by
            simpa using hB
          have hC' : (2 : ℝ) ^ (3 * (t / 4)) * X⁻¹ ≤ I := by
            simpa using hC
          have hterm2 : ((t : ℝ) ^ 2 * ((t : ℝ) ^ 2 + 1)) *
              ((2 : ℝ) ^ (t - t / 4) * X⁻¹) ≤ 2 * P * I := by
            rw [hA']
            exact mul_le_mul_of_nonneg_right hpoly4 hIR.le
          have hterm3 : X⁻¹ ≤ P * I :=
            hOne.trans (by simpa using mul_le_mul_of_nonneg_right hPR hIR.le)
          have hterm4 : (t : ℝ) ^ 6 * X⁻¹ ≤ P * I := by
            exact mul_le_mul hpoly6 hOne h0 (zero_le_one.trans hPR)
          have hterm5 : (t : ℝ) ^ 5 *
              ((2 : ℝ) ^ (t / 4 + t / 2) * X⁻¹) ≤ P * I := by
            exact mul_le_mul hpoly5 hB' (by positivity) (zero_le_one.trans hPR)
          have hterm6 : (2 : ℝ) ^ (3 * (t / 4)) * X⁻¹ ≤ P * I :=
            hC'.trans (by simpa using mul_le_mul_of_nonneg_right hPR hIR.le)
          nlinarith
        _ ≤ 4 / (t : ℝ) ^ 2 + 100 * P * I := by
          ring_nf
          nlinarith [hPI]
    _ = 4 / (t : ℝ) ^ 2 +
        100 * ((t : ℝ) + 1) ^ 6 * (((2 ^ (t / 4) : ℕ) : ℝ)⁻¹) := by
      rfl

lemma inv_two_pow_div_four_le_geometric (t : ℕ) :
    (((2 ^ (t / 4) : ℕ) : ℝ)⁻¹) ≤
      2 * ((9 / 10 : ℝ) ^ t) := by
  let q := t / 4
  let r : ℝ := 9 / 10
  have hr0 : 0 ≤ r := by norm_num [r]
  have hr1 : r ≤ 1 := by norm_num [r]
  have hbase : (1 / 2 : ℝ) ≤ r ^ 4 := by norm_num [r]
  have hpow : (1 / 2 : ℝ) ^ q ≤ (r ^ 4) ^ q :=
    pow_le_pow_left₀ (by norm_num) hbase q
  have hfactor : (r ^ 4) ^ q ≤ 2 * r ^ (4 * q + 3) := by
    rw [← pow_mul, pow_add]
    have hcoef : (1 : ℝ) ≤ 2 * r ^ 3 := by norm_num [r]
    have hn : 0 ≤ r ^ (4 * q) := pow_nonneg hr0 _
    nlinarith [mul_le_mul_of_nonneg_left hcoef hn]
  have htq : t ≤ 4 * q + 3 := by
    dsimp [q]
    have hmod := Nat.mod_lt t (by norm_num : 0 < 4)
    have hdecomp := Nat.div_add_mod t 4
    omega
  have hanti : r ^ (4 * q + 3) ≤ r ^ t :=
    pow_le_pow_of_le_one hr0 hr1 htq
  calc
    (((2 ^ (t / 4) : ℕ) : ℝ)⁻¹) = (1 / 2 : ℝ) ^ q := by
      dsimp [q]
      push_cast
      rw [← inv_pow]
      norm_num
    _ ≤ (r ^ 4) ^ q := hpow
    _ ≤ 2 * r ^ (4 * q + 3) := hfactor
    _ ≤ 2 * r ^ t := mul_le_mul_of_nonneg_left hanti (by norm_num)
    _ = 2 * ((9 / 10 : ℝ) ^ t) := rfl

lemma summable_succ_pow_mul_nine_tenths :
    Summable (fun t : ℕ ↦ ((t : ℝ) + 1) ^ 6 * (9 / 10 : ℝ) ^ t) := by
  let r : ℝ := 9 / 10
  have hr : ‖r‖ < 1 := by norm_num [r, Real.norm_eq_abs]
  have hnorm := summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) 6 hr
  have hbase : Summable (fun t : ℕ ↦ (t : ℝ) ^ 6 * r ^ t) := by
    apply hnorm.congr
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg]
    positivity
  have hshift : Summable (fun t : ℕ ↦ ((t + 1 : ℕ) : ℝ) ^ 6 * r ^ (t + 1)) :=
    (summable_nat_add_iff 1).2 hbase
  have hscaled := hshift.mul_left (r⁻¹)
  apply hscaled.congr
  intro t
  dsimp [r]
  push_cast
  rw [pow_succ]
  field_simp
  ring

lemma summable_richThresholdDensity : Summable richThresholdDensity := by
  have hpNorm := summable_pow_div_add (1 : ℝ) 2 0 (by norm_num : 1 < (2 : ℕ))
  have hpOne : Summable (fun t : ℕ ↦ 1 / (t : ℝ) ^ 2) := by
    apply hpNorm.congr
    intro t
    simp only [Nat.cast_zero, add_zero, one_div, Real.norm_eq_abs]
    rw [abs_of_nonneg]
    positivity
  have hpseries : Summable (fun t : ℕ ↦ 4 / (t : ℝ) ^ 2) := by
    simpa [div_eq_mul_inv] using hpOne.mul_left 4
  have hgeom := summable_succ_pow_mul_nine_tenths.mul_left 200
  have hfloor : Summable (fun t : ℕ ↦
      100 * ((t : ℝ) + 1) ^ 6 * (((2 ^ (t / 4) : ℕ) : ℝ)⁻¹)) := by
    apply Summable.of_nonneg_of_le
      (fun t ↦ mul_nonneg (by positivity) (inv_nonneg.mpr (by positivity)))
      (fun t ↦ ?_) hgeom
    have hpow0 : 0 ≤ ((t : ℝ) + 1) ^ 6 := by positivity
    have h := inv_two_pow_div_four_le_geometric t
    calc
      100 * ((t : ℝ) + 1) ^ 6 * (((2 ^ (t / 4) : ℕ) : ℝ)⁻¹) ≤
          100 * ((t : ℝ) + 1) ^ 6 * (2 * (9 / 10 : ℝ) ^ t) := by
            gcongr
      _ = 200 * (((t : ℝ) + 1) ^ 6 * (9 / 10 : ℝ) ^ t) := by ring
  have hmajor := hpseries.add hfloor
  rw [← summable_nat_add_iff 1]
  apply Summable.of_nonneg_of_le
    (fun t ↦ mul_nonneg (by positivity) (by simp [dyadicReciprocalUpper]))
    (fun t ↦ richThresholdDensity_le (by omega))
  exact (summable_nat_add_iff 1).2 hmajor

def dyadicIndexRange (S : Finset ℕ) (T : ℕ) : Finset ℕ :=
  (Finset.range (S.sum id + 1)).filter fun t ↦ T ≤ t

def highPrimePart (S : Finset ℕ) (T : ℕ) : Finset ℕ :=
  S.filter fun p ↦ T ≤ Nat.log 2 p

lemma mem_dyadicIndexRange {S : Finset ℕ} {T t : ℕ} :
    t ∈ dyadicIndexRange S T ↔ t < S.sum id + 1 ∧ T ≤ t := by
  simp [dyadicIndexRange]

lemma dyadicIndex_of_mem {S : Finset ℕ} {T p : ℕ}
    (hp : p ∈ highPrimePart S T) :
    Nat.log 2 p ∈ dyadicIndexRange S T := by
  have hpData : p ∈ S ∧ T ≤ Nat.log 2 p := by
    simpa [highPrimePart] using hp
  have hpsum : p ≤ S.sum id := by
    simpa using Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) hpData.1
  apply mem_dyadicIndexRange.mpr
  exact ⟨(Nat.log_le_self 2 p).trans_lt (Nat.lt_succ_of_le hpsum), hpData.2⟩

lemma biUnion_dyadicPrimePart_eq_highPrimePart (S : Finset ℕ) (T : ℕ) :
    (dyadicIndexRange S T).biUnion (dyadicPrimePart S) = highPrimePart S T := by
  ext p
  constructor
  · intro hp
    obtain ⟨t, ht, hpt⟩ := Finset.mem_biUnion.mp hp
    have htData := mem_dyadicIndexRange.mp ht
    have hpData := mem_dyadicPrimePart.mp hpt
    exact Finset.mem_filter.mpr ⟨hpData.1, by simpa [hpData.2] using htData.2⟩
  · intro hp
    refine Finset.mem_biUnion.mpr ⟨Nat.log 2 p, dyadicIndex_of_mem hp, ?_⟩
    exact mem_dyadicPrimePart.mpr
      ⟨(Finset.mem_filter.mp hp).1, rfl⟩

lemma pairwiseDisjoint_dyadicPrimePart (S : Finset ℕ) (T : ℕ) :
    (↑(dyadicIndexRange S T) : Set ℕ).PairwiseDisjoint (dyadicPrimePart S) := by
  intro s hs t ht hst
  exact disjoint_dyadicPrimePart hst

lemma sum_highPrimePart_eq_blocks (S : Finset ℕ) (T : ℕ) :
    ∑ p ∈ highPrimePart S T, primeReciprocalWeight p =
      ∑ t ∈ dyadicIndexRange S T,
        ∑ p ∈ dyadicPrimePart S t, primeReciprocalWeight p := by
  rw [← biUnion_dyadicPrimePart_eq_highPrimePart S T,
    Finset.sum_biUnion (pairwiseDisjoint_dyadicPrimePart S T)]

lemma dyadic_block_mass_le_card_mul_upper {S : Finset ℕ} {t : ℕ}
    (hprime : ∀ p ∈ S, p.Prime) :
    (∑ p ∈ dyadicPrimePart S t, primeReciprocalWeight p) ≤
      (dyadicPrimePart S t).card * dyadicReciprocalUpper t := by
  have h := (dyadicPrimePart S t).sum_le_card_nsmul primeReciprocalWeight
    (dyadicReciprocalUpper t) (fun p hp ↦ by
      have hpLower := (dyadicPrimePart_primeBlock hprime p hp).2.1
      have hx : 0 < 2 ^ t := pow_pos (by norm_num) _
      have hppos : 0 < p := hx.trans_le hpLower
      exact (inv_le_inv₀ (by exact_mod_cast hppos) (by exact_mod_cast hx)).2
        (by exact_mod_cast hpLower))
  simpa [nsmul_eq_mul] using h

lemma richDyadicIndices_eq_filter (S : Finset ℕ) (T : ℕ) :
    richDyadicIndices S T =
      (dyadicIndexRange S T).filter fun t ↦
        richCardThreshold t < (dyadicPrimePart S t).card := by
  ext t
  simp [richDyadicIndices, dyadicIndexRange, and_assoc]

lemma highPrimeMass_le_rich_mass_add_density (S : Finset ℕ) (T : ℕ)
    (hprime : ∀ p ∈ S, p.Prime) :
    (∑ p ∈ highPrimePart S T, primeReciprocalWeight p) ≤
      indexedBlocksMass primeReciprocalWeight (richDyadicBlocks S T) +
        ∑ t ∈ dyadicIndexRange S T, richThresholdDensity t := by
  rw [sum_highPrimePart_eq_blocks,
    indexedBlocksMass_richDyadicBlocks,
    richDyadicIndices_eq_filter]
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t ht
  by_cases hr : richCardThreshold t < (dyadicPrimePart S t).card
  · simp only [hr, if_true]
    have hdens : 0 ≤ richThresholdDensity t := by
      exact mul_nonneg (by positivity) (by simp [dyadicReciprocalUpper])
    linarith
  · simp only [hr, if_false, zero_add]
    calc
      (∑ p ∈ dyadicPrimePart S t, primeReciprocalWeight p) ≤
          (dyadicPrimePart S t).card * dyadicReciprocalUpper t :=
        dyadic_block_mass_le_card_mul_upper hprime
      _ ≤ richCardThreshold t * dyadicReciprocalUpper t := by
        have hc : (dyadicPrimePart S t).card ≤ richCardThreshold t := by omega
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc)
          (by simp [dyadicReciprocalUpper])
      _ = richThresholdDensity t := rfl

lemma finite_density_sum_le_tsum (S : Finset ℕ) (T : ℕ) :
    (∑ t ∈ dyadicIndexRange S T, richThresholdDensity t) ≤
      ∑' t : ℕ, richThresholdDensity t := by
  apply summable_richThresholdDensity.sum_le_tsum
  intro t ht
  exact mul_nonneg (by positivity) (by simp [dyadicReciprocalUpper])

lemma summable_dyadicReciprocalUpper : Summable dyadicReciprocalUpper := by
  apply summable_geometric_two.congr
  intro t
  rw [dyadicReciprocalUpper]
  push_cast
  rw [← inv_pow]
  norm_num

lemma indexedBlocksUpper_le_tsum (S : Finset ℕ) (T : ℕ) :
    indexedBlocksUpper dyadicReciprocalUpper (richDyadicBlocks S T) ≤
      ∑' t : ℕ, dyadicReciprocalUpper t := by
  rw [indexedBlocksUpper_richDyadicBlocks]
  apply summable_dyadicReciprocalUpper.sum_le_tsum
  intro t ht
  simp [dyadicReciprocalUpper]

def thinMassBudget : ℝ := ∑' t : ℕ, richThresholdDensity t

def scanLossBudget : ℝ := ∑' t : ℕ, dyadicReciprocalUpper t

def roughMassTarget : ℝ := 1 + thinMassBudget + scanLossBudget

/-- Every prime divisor of `n` is at least `L`. -/
def Rough (L n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → L ≤ p

lemma highPrimePart_eq_of_rough {n T : ℕ} (hrough : Rough (2 ^ T) n) :
    highPrimePart n.primeFactors T = n.primeFactors := by
  apply Finset.filter_true_of_mem
  intro p hp
  apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
  exact hrough p (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp)

def selectedRichBlocks (S : Finset ℕ) (T : ℕ) : List (ℕ × List ℕ) :=
  conormalBlockScan primeReciprocalWeight dyadicReciprocalUpper
    (richDyadicBlocks S T)

lemma selectedRichBlocks_suffix (S : Finset ℕ) (T : ℕ) :
    ∃ pre, pre ++ selectedRichBlocks S T = richDyadicBlocks S T := by
  exact conormalBlockScan_suffix primeReciprocalWeight dyadicReciprocalUpper
    (richDyadicBlocks S T)

lemma selectedRichBlocks_pairwise_index (S : Finset ℕ) (T : ℕ) :
    (selectedRichBlocks S T).Pairwise (fun A B ↦ B.1 ≤ A.1) := by
  obtain ⟨pre, hpre⟩ := selectedRichBlocks_suffix S T
  have hall := richDyadicBlocks_pairwise_index S T
  rw [← hpre] at hall
  exact (List.pairwise_append.mp hall).2.1

lemma flatten_selectedRichBlocks_nodup (S : Finset ℕ) (T : ℕ) :
    (flattenIndexedBlocks (selectedRichBlocks S T)).Nodup := by
  obtain ⟨pre, hpre⟩ := selectedRichBlocks_suffix S T
  have hall := flatten_richDyadicBlocks_nodup S T
  rw [← hpre, flattenIndexedBlocks_append] at hall
  exact (List.nodup_append.mp hall).2.1

lemma selectedRichBlocks_nodup (S : Finset ℕ) (T : ℕ) :
    (selectedRichBlocks S T).Nodup := by
  obtain ⟨pre, hpre⟩ := selectedRichBlocks_suffix S T
  have hall := richDyadicBlocks_nodup S T
  rw [← hpre] at hall
  exact (List.nodup_append.mp hall).2.1

lemma mem_flattenIndexedBlocks {A : Type*} {a : A}
    {Bs : List (ℕ × List A)} :
    a ∈ flattenIndexedBlocks Bs ↔ ∃ B ∈ Bs, a ∈ B.2 := by
  simp [flattenIndexedBlocks]

lemma selectedRichBlocks_element_mem {S : Finset ℕ} {T p : ℕ}
    (hp : p ∈ flattenIndexedBlocks (selectedRichBlocks S T)) : p ∈ S := by
  obtain ⟨B, hB, hpB⟩ := mem_flattenIndexedBlocks.mp hp
  obtain ⟨pre, hpre⟩ := selectedRichBlocks_suffix S T
  have hBall : B ∈ richDyadicBlocks S T := by
    rw [← hpre]
    simp [hB]
  obtain ⟨t, ht, rfl⟩ := mem_richDyadicBlocks.mp hBall
  have hpPart : p ∈ dyadicPrimePart S t := by simpa using hpB
  exact (mem_dyadicPrimePart.mp hpPart).1

lemma selectedRichBlocks_properties {S : Finset ℕ} {T : ℕ}
    (hprime : ∀ p ∈ S, p.Prime) :
    let Cs := selectedRichBlocks S T
    SeededSlow primeReciprocalWeight (flattenIndexedBlocks Cs) ∧
      (∀ B ∈ Cs, B ∈ richDyadicBlocks S T) := by
  let Bs := richDyadicBlocks S T
  have h := conormalBlockScan_properties primeReciprocalWeight
    dyadicReciprocalUpper Bs
    (fun B hB ↦ richDyadicBlocks_length_two hB)
    (fun B hB ↦ richDyadicBlocks_seededSlow hprime hB)
    (fun B hB p hp ↦ richDyadicBlocks_weight_nonneg hB hp)
    (fun B hB p hp ↦ richDyadicBlocks_weight_le_upper hprime hB hp)
  exact ⟨h.2.1, h.2.2.2⟩

lemma CoversInterval.insertList {D : Finset ℕ} {E F : ℕ} {ds : List ℕ}
    (hcover : CoversInterval D E F) (hslow : SlowExtension F ds)
    (hnodup : ds.Nodup) (hdisj : Disjoint D ds.toFinset) :
    CoversInterval (D ∪ ds.toFinset) E (F + ds.sum) := by
  induction ds generalizing D F with
  | nil => simpa using hcover
  | cons d ds ih =>
      have hdD : d ∉ D := by
        intro hd
        exact (Finset.disjoint_left.mp hdisj hd) (by simp)
      have hdDs : d ∉ ds.toFinset := by
        have hdList : d ∉ ds := (List.nodup_cons.mp hnodup).1
        simpa using hdList
      have hstep : CoversInterval (Insert.insert d D) E (F + d) :=
        hcover.insert hdD hslow.1
      have htailDisj : Disjoint (Insert.insert d D) ds.toFinset := by
        rw [Finset.disjoint_insert_left]
        refine ⟨hdDs, hdisj.mono_right ?_⟩
        intro x hx
        simp [hx]
      have htail := ih hstep hslow.2 hnodup.tail htailDisj
      simpa [Finset.insert_union, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

lemma Pseudoperfect.of_cover_extension {n E F : ℕ} {D : Finset ℕ}
    {ds : List ℕ}
    (hD : D ⊆ n.properDivisors)
    (hds : ∀ d ∈ ds, d ∈ n.properDivisors)
    (hcover : CoversInterval D E F)
    (hslow : SlowExtension F ds)
    (hnodup : ds.Nodup)
    (hdisj : Disjoint D ds.toFinset)
    (hEn : E ≤ n) (hnTop : n ≤ E + (F + ds.sum)) :
    Pseudoperfect n := by
  have hfinal := hcover.insertList hslow hnodup hdisj
  have hall : D ∪ ds.toFinset ⊆ n.properDivisors := by
    intro d hd
    rcases Finset.mem_union.mp hd with hdD | hdl
    · exact hD hdD
    · exact hds d (by simpa using hdl)
  obtain ⟨S, hS, hsum⟩ :=
    Finset.mem_subsetSum_iff.mp (hfinal n hEn hnTop)
  exact ⟨S, hS.trans hall, by simpa using hsum.symm⟩

/-- A bound for all non-pseudoperfect integers immediately gives the public
form of Erdős 825.  The deep part of the development constructs `C`. -/
lemma conclusion_of_nonpseudoperfect_bound
    (C : ℝ)
    (hbound : ∀ n : ℕ, ¬Pseudoperfect n → (σ 1 n : ℝ) ≤ C * n) :
    ∀ n : ℕ, (σ 1 n : ℝ) > C * n → Pseudoperfect n := by
  intro n hn
  by_contra hnot
  exact (not_lt_of_ge (hbound n hnot)) hn

/-! ## Canonical smooth and rough parts -/

/-- The sub-factorization supported on primes at least `L`. -/
def roughFactorization (L n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.filter (fun p => L ≤ p)

/-- The sub-factorization supported on primes below `L`. -/
def smoothFactorization (L n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.filter (fun p => p < L)

/-- The factor of `n` supported on primes at least `L`. -/
def roughPart (L n : ℕ) : ℕ :=
  (roughFactorization L n).prod (fun p e => p ^ e)

/-- The factor of `n` supported on primes below `L`. -/
def smoothPart (L n : ℕ) : ℕ :=
  (smoothFactorization L n).prod (fun p e => p ^ e)

lemma roughFactorization_le (L n : ℕ) :
    roughFactorization L n ≤ n.factorization := by
  intro p
  simp only [roughFactorization, Finsupp.filter_apply]
  split <;> simp

lemma smoothFactorization_le (L n : ℕ) :
    smoothFactorization L n ≤ n.factorization := by
  intro p
  simp only [smoothFactorization, Finsupp.filter_apply]
  split <;> simp

lemma roughPart_mul_smoothPart {L n : ℕ} (hn : n ≠ 0) :
    roughPart L n * smoothPart L n = n := by
  rw [roughPart, smoothPart, roughFactorization, smoothFactorization]
  have hsplit := n.factorization.prod_filter_mul_prod_filter_not
    (fun p => L ≤ p) (fun p e => p ^ e)
  simpa only [not_le] using hsplit.trans (Nat.prod_factorization_pow_eq_self hn)

lemma roughPart_pos {L n : ℕ} (hn : 0 < n) : 0 < roughPart L n := by
  have hmul := roughPart_mul_smoothPart (L := L) hn.ne'
  exact pos_of_mul_pos_left (hmul ▸ hn) (Nat.zero_le _)

lemma smoothPart_pos {L n : ℕ} (hn : 0 < n) : 0 < smoothPart L n := by
  have hmul := roughPart_mul_smoothPart (L := L) hn.ne'
  exact pos_of_mul_pos_right (hmul ▸ hn) (Nat.zero_le _)

lemma roughPart_dvd {L n : ℕ} (hn : 0 < n) : roughPart L n ∣ n := by
  exact ⟨smoothPart L n, (roughPart_mul_smoothPart hn.ne').symm⟩

lemma smoothPart_dvd {L n : ℕ} (hn : 0 < n) : smoothPart L n ∣ n := by
  exact ⟨roughPart L n, by
    rw [Nat.mul_comm]
    exact (roughPart_mul_smoothPart hn.ne').symm⟩

lemma factorization_roughPart (L n : ℕ) :
    (roughPart L n).factorization = roughFactorization L n := by
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (roughFactorization_le L n)

lemma factorization_smoothPart (L n : ℕ) :
    (smoothPart L n).factorization = smoothFactorization L n := by
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (smoothFactorization_le L n)

lemma roughPart_rough {L n : ℕ} (hn : 0 < n) : Rough L (roughPart L n) := by
  intro p hp hpdvd
  have hmem : p ∈ (roughPart L n).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpdvd, (roughPart_pos hn).ne'⟩
  change p ∈ (roughPart L n).factorization.support at hmem
  rw [factorization_roughPart, roughFactorization, Finsupp.support_filter] at hmem
  exact (Finset.mem_filter.mp hmem).2

lemma roughPart_coprime_smoothPart {L n : ℕ} (hn : 0 < n) :
    (roughPart L n).Coprime (smoothPart L n) := by
  rw [← Nat.disjoint_primeFactors (roughPart_pos hn).ne' (smoothPart_pos hn).ne']
  change Disjoint (roughPart L n).factorization.support
    (smoothPart L n).factorization.support
  rw [factorization_roughPart, factorization_smoothPart, roughFactorization,
    smoothFactorization, Finsupp.support_filter, Finsupp.support_filter]
  simpa only [not_le] using
    Finset.disjoint_filter_filter_not n.factorization.support
      n.factorization.support (fun p => L ≤ p)

/-! ## Abundancy and the finite small-prime factor -/

/-- The real abundancy index used by the statement. -/
def abundancy (n : ℕ) : ℝ := (σ 1 n : ℝ) / n

lemma abundancy_mul_of_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hcop : m.Coprime n) :
    abundancy (m * n) = abundancy m * abundancy n := by
  rw [abundancy, abundancy, abundancy,
    (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop]
  push_cast
  field_simp [hm.ne', hn.ne']

lemma primePow_abundancy_le {p e : ℕ} (hp : p.Prime) :
    abundancy (p ^ e) ≤ (p : ℝ) / (p - 1) := by
  rw [abundancy, ArithmeticFunction.sigma_one_apply_prime_pow hp]
  push_cast
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [div_le_div_iff₀ (pow_pos (by positivity : (0 : ℝ) < p) e)
    (sub_pos.mpr hpR)]
  calc
    (∑ x ∈ Finset.range (e + 1), (p : ℝ) ^ x) * ((p : ℝ) - 1) =
        (p : ℝ) ^ (e + 1) - 1 := geom_sum_mul (p : ℝ) (e + 1)
    _ ≤ (p : ℝ) ^ (e + 1) := sub_le_self _ zero_le_one
    _ = (p : ℝ) ^ e * p := by rw [pow_succ]
    _ = (p : ℝ) * (p : ℝ) ^ e := by ring

lemma abundancy_le_primeEulerProduct {n : ℕ} (hn : 0 < n) :
    abundancy n ≤ ∏ p ∈ n.primeFactors, (p : ℝ) / (p - 1) := by
  have hsigmaNat :
      σ 1 n = ∏ p ∈ n.primeFactors, σ 1 (p ^ n.factorization p) := by
    exact ArithmeticFunction.IsMultiplicative.multiplicative_factorization
      (σ 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) hn.ne'
  have hnNat : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    exact Nat.prod_factorization_pow_eq_self hn.ne'
  have hsigma :
      (σ 1 n : ℝ) = ∏ p ∈ n.primeFactors, (σ 1 (p ^ n.factorization p) : ℝ) := by
    exact_mod_cast hsigmaNat
  have hnprod :
      (n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) := by
    exact_mod_cast hnNat.symm
  rw [abundancy, hsigma, hnprod, ← Finset.prod_div_distrib]
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    simpa [abundancy, ArithmeticFunction.sigma_one_apply_prime_pow hpPrime] using
      primePow_abundancy_le (p := p) (e := n.factorization p) hpPrime

/-- Reciprocal mass of the distinct prime divisors of `n`. -/
def primeReciprocalMass (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, (p : ℝ)⁻¹

lemma primeEulerFactor_le_one_add_two_div {p : ℕ} (hp : p.Prime) :
    (p : ℝ) / (p - 1) ≤ 1 + 2 / p := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hpR
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hinv : (1 : ℝ) / (p - 1) ≤ 2 / p := by
    rw [div_le_div_iff₀ (sub_pos.mpr hpR) hp0]
    nlinarith
  calc
    (p : ℝ) / (p - 1) = 1 + 1 / (p - 1) := by
      field_simp [(sub_pos.mpr hpR).ne']
      linarith
    _ ≤ 1 + 2 / p := by simpa [add_comm] using add_le_add_left hinv 1

/-- A deliberately coarse but uniform estimate.  It is strong enough for an
absolute constant and avoids carrying an infinite Euler product through the
rest of the proof. -/
lemma abundancy_le_exp_primeReciprocalMass {n : ℕ} (hn : 0 < n) :
    abundancy n ≤ Real.exp (2 * primeReciprocalMass n) := by
  calc
    abundancy n ≤ ∏ p ∈ n.primeFactors, (p : ℝ) / (p - 1) :=
      abundancy_le_primeEulerProduct hn
    _ ≤ ∏ p ∈ n.primeFactors, (1 + 2 / (p : ℝ)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hpR : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
        exact div_nonneg (by positivity) (sub_pos.mpr hpR).le
      · intro p hp
        exact primeEulerFactor_le_one_add_two_div
          (Nat.prime_of_mem_primeFactors hp)
    _ ≤ Real.exp (∑ p ∈ n.primeFactors, 2 / (p : ℝ)) := by
      exact Real.prod_one_add_le_exp_sum _ fun p => by positivity
    _ = Real.exp (2 * primeReciprocalMass n) := by
      congr 1
      rw [primeReciprocalMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      simp [div_eq_mul_inv]

lemma primeReciprocalMass_gt_of_exp_lt_abundancy {n : ℕ} (hn : 0 < n)
    {S : ℝ} (hlarge : Real.exp (2 * S) < abundancy n) :
    S < primeReciprocalMass n := by
  have hexp : Real.exp (2 * S) < Real.exp (2 * primeReciprocalMass n) :=
    hlarge.trans_le (abundancy_le_exp_primeReciprocalMass hn)
  have := (Real.exp_lt_exp).mp hexp
  linarith

lemma rich_mass_gt_one_add_scanLoss {n T : ℕ} (hn : 0 < n)
    (hrough : Rough (2 ^ T) n)
    (hmass : roughMassTarget < primeReciprocalMass n) :
    1 + indexedBlocksUpper dyadicReciprocalUpper
        (richDyadicBlocks n.primeFactors T) <
      indexedBlocksMass primeReciprocalWeight
        (richDyadicBlocks n.primeFactors T) := by
  have hprime : ∀ p ∈ n.primeFactors, p.Prime := fun p hp ↦
    Nat.prime_of_mem_primeFactors hp
  have hthin := highPrimeMass_le_rich_mass_add_density n.primeFactors T hprime
  rw [highPrimePart_eq_of_rough hrough] at hthin
  have hfinite := finite_density_sum_le_tsum n.primeFactors T
  have hupper := indexedBlocksUpper_le_tsum n.primeFactors T
  have hprimeEq :
      (∑ p ∈ n.primeFactors, primeReciprocalWeight p) =
        primeReciprocalMass n := by rfl
  rw [hprimeEq] at hthin
  dsimp [roughMassTarget, thinMassBudget, scanLossBudget] at hmass
  linarith

lemma selectedRichBlocks_mass_gt_one {n T : ℕ} (hn : 0 < n)
    (hrough : Rough (2 ^ T) n)
    (hmass : roughMassTarget < primeReciprocalMass n) :
    1 < indexedBlocksMass primeReciprocalWeight
      (selectedRichBlocks n.primeFactors T) := by
  let Bs := richDyadicBlocks n.primeFactors T
  have hprime : ∀ p ∈ n.primeFactors, p.Prime := fun p hp ↦
    Nat.prime_of_mem_primeFactors hp
  have hlarge := rich_mass_gt_one_add_scanLoss hn hrough hmass
  apply conormalBlockScan_mass_gt_one primeReciprocalWeight dyadicReciprocalUpper Bs
  · intro B hB
    exact richDyadicBlocks_length_two hB
  · intro B hB
    exact richDyadicBlocks_seededSlow hprime hB
  · intro B hB p hp
    exact richDyadicBlocks_weight_nonneg hB hp
  · intro B hB p hp
    exact richDyadicBlocks_weight_le_upper hprime hB hp
  · simpa [Bs, selectedRichBlocks] using hlarge

/-- Larsen's rough-number theorem at one explicit (very coarse) reciprocal
mass threshold.  The terminal selected rich block supplies the dense seed;
all earlier selected blocks are consumed by the complement tail. -/
lemma rough_pseudoperfect_of_mass {n : ℕ} (hn : 0 < n)
    (hrough : Rough (2 ^ 12) n)
    (hmass : roughMassTarget < primeReciprocalMass n) : Pseudoperfect n := by
  let Cs := selectedRichBlocks n.primeFactors 12
  have hprime : ∀ q ∈ n.primeFactors, q.Prime := fun q hq ↦
    Nat.prime_of_mem_primeFactors hq
  have hmassCs : 1 < indexedBlocksMass primeReciprocalWeight Cs := by
    simpa [Cs] using selectedRichBlocks_mass_gt_one hn hrough hmass
  have hCsne : Cs ≠ [] := by
    intro hnil
    rw [hnil] at hmassCs
    norm_num [indexedBlocksMass] at hmassCs
  obtain ⟨B, rest, hCs⟩ := List.exists_cons_of_ne_nil hCsne
  obtain ⟨t, PL⟩ := B
  let qs := flattenIndexedBlocks rest
  have hprops := selectedRichBlocks_properties (S := n.primeFactors)
    (T := 12) hprime
  have hheadRich : (t, PL) ∈ richDyadicBlocks n.primeFactors 12 := by
    apply hprops.2
    change (t, PL) ∈ Cs
    rw [hCs]
    simp
  obtain ⟨u, hu, hhead⟩ := mem_richDyadicBlocks.mp hheadRich
  have htu : t = u := congrArg Prod.fst hhead
  subst t
  have hPL : PL = (dyadicPrimePart n.primeFactors u).sort (fun a b ↦ a ≥ b) := by
    simpa using congrArg Prod.snd hhead
  subst PL
  let P := dyadicPrimePart n.primeFactors u
  have hblock : PrimeBlock (2 ^ u) P := dyadicPrimePart_primeBlock hprime
  have huData := mem_richDyadicIndices.mp hu
  have hu12 : 12 ≤ u := huData.2.1
  have hrich : richCardThreshold u < P.card := huData.2.2
  have hPcard : 4 ≤ P.card := by
    have hfour : 4 ≤ richCardThreshold u :=
      (by omega : 4 ≤ 8 * 2 ^ (3 * (u / 4)) + 4).trans
        (le_max_right _ _)
    omega
  have hPLlen : 2 ≤ (P.sort (fun a b ↦ a ≥ b)).length := by
    simpa using (show 2 ≤ P.card by omega)
  have hflatNodup :
      ((P.sort (fun a b ↦ a ≥ b)) ++ qs).Nodup := by
    have hall := flatten_selectedRichBlocks_nodup n.primeFactors 12
    change (flattenIndexedBlocks Cs).Nodup at hall
    rw [hCs] at hall
    simpa [qs, P, flattenIndexedBlocks] using hall
  have hPLnodup : (P.sort (fun a b ↦ a ≥ b)).Nodup :=
    (List.nodup_append.mp hflatNodup).1
  have hqsNodup : qs.Nodup := (List.nodup_append.mp hflatNodup).2.1
  have hcross := (List.nodup_append.mp hflatNodup).2.2
  have hdisj : Disjoint qs.toFinset P := by
    rw [Finset.disjoint_left]
    intro q hqQs hqP
    have hqPL : q ∈ P.sort (fun a b ↦ a ≥ b) :=
      (Finset.mem_sort (s := P) (fun a b ↦ a ≥ b)).mpr hqP
    exact hcross q hqPL q (by simpa using hqQs) rfl
  have hselectedNodup := selectedRichBlocks_nodup n.primeFactors 12
  change Cs.Nodup at hselectedNodup
  rw [hCs] at hselectedNodup
  have hheadNot : (u, P.sort (fun a b ↦ a ≥ b)) ∉ rest := by
    exact (List.nodup_cons.mp hselectedNodup).1
  have hpair := selectedRichBlocks_pairwise_index n.primeFactors 12
  change Cs.Pairwise (fun A B ↦ B.1 ≤ A.1) at hpair
  rw [hCs] at hpair
  have htailIndex : ∀ B ∈ rest, B.1 < u := by
    intro B hB
    have hle : B.1 ≤ u := (List.pairwise_cons.mp hpair).1 B hB
    have hBRich : B ∈ richDyadicBlocks n.primeFactors 12 := by
      apply hprops.2
      change B ∈ Cs
      rw [hCs]
      simp [hB]
    have hne : B.1 ≠ u := by
      intro heq
      obtain ⟨v, hv, hBeq⟩ := mem_richDyadicBlocks.mp hBRich
      have hvu : v = u := by
        have := congrArg Prod.fst hBeq
        simpa [heq] using this.symm
      subst v
      apply hheadNot
      have hBhead : B = (u, P.sort (fun a b ↦ a ≥ b)) := by
        simpa [P] using hBeq
      rw [← hBhead]
      exact hB
    omega
  have hqsPrime : ∀ q ∈ qs, q.Prime := by
    intro q hq
    have hqAll : q ∈ flattenIndexedBlocks Cs := by
      rw [hCs]
      simpa [qs, P, flattenIndexedBlocks] using
        (List.mem_append_right (P.sort (fun a b ↦ a ≥ b)) hq)
    exact hprime q (selectedRichBlocks_element_mem hqAll)
  have hqsData : ∀ q ∈ qs, 0 < q ∧ 4 < q ∧ q ≤ 2 ^ u := by
    intro q hq
    have hqPrime := hqsPrime q hq
    have hqDvdN : q ∣ n := by
      apply Nat.dvd_of_mem_primeFactors
      have hqAll : q ∈ flattenIndexedBlocks Cs := by
        rw [hCs]
        simpa [qs, P, flattenIndexedBlocks] using
          (List.mem_append_right (P.sort (fun a b ↦ a ≥ b)) hq)
      exact selectedRichBlocks_element_mem hqAll
    have hqLarge := hrough q hqPrime hqDvdN
    obtain ⟨B, hB, hqB⟩ := mem_flattenIndexedBlocks.mp hq
    have hBRich : B ∈ richDyadicBlocks n.primeFactors 12 := by
      apply hprops.2
      change B ∈ Cs
      rw [hCs]
      simp [hB]
    obtain ⟨v, hv, hBeq⟩ := mem_richDyadicBlocks.mp hBRich
    have hqPart : q ∈ dyadicPrimePart n.primeFactors v := by
      have : q ∈ (dyadicPrimePart n.primeFactors v).sort (fun a b ↦ a ≥ b) := by
        simpa [hBeq] using hqB
      exact (Finset.mem_sort (s := dyadicPrimePart n.primeFactors v)
        (fun a b ↦ a ≥ b)).mp this
    have hvu : v < u := by
      have := htailIndex B hB
      simpa [hBeq] using this
    have hqUpper := (dyadicPrimePart_primeBlock hprime q hqPart).2.2
    have hpow : 2 ^ (v + 1) ≤ 2 ^ u :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
    refine ⟨hqPrime.pos, ?_, ?_⟩
    · exact (by norm_num : 4 < 2 ^ 12).trans_le hqLarge
    · have : q < 2 ^ (v + 1) := by
        simpa [pow_succ, Nat.mul_comm] using hqUpper
      exact this.le.trans hpow
  have hqsCore : ∀ q ∈ qs, 0 < q ∧ q ≤ 2 ^ u := by
    intro q hq
    exact ⟨(hqsData q hq).1, (hqsData q hq).2.2⟩
  have hqsLarge : ∀ q ∈ qs, 0 < q ∧ 4 < q := by
    intro q hq
    exact ⟨(hqsData q hq).1, (hqsData q hq).2.1⟩
  have hseeded : SeededSlow primeReciprocalWeight
      ((P.sort (fun a b ↦ a ≥ b)) ++ qs) := by
    have := hprops.1
    change SeededSlow primeReciprocalWeight (flattenIndexedBlocks Cs) at this
    rw [hCs] at this
    simpa [qs, P, flattenIndexedBlocks] using this
  have hmassList : 1 <
      (((P.sort (fun a b ↦ a ≥ b)) ++ qs).map
        primeReciprocalWeight).sum := by
    have hmassFlat : 1 < ((flattenIndexedBlocks Cs).map
        primeReciprocalWeight).sum := by
      rw [← indexedBlocksMass_eq_flatten]
      exact hmassCs
    rw [hCs] at hmassFlat
    simpa [qs, P, flattenIndexedBlocks] using hmassFlat
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < P.card)
  obtain ⟨E, F, hEsum, hF, hcover⟩ :=
    strongBlockDivisors_cover_bounded_of_rich_card
      (show 4 ≤ u by omega) hblock hp hrich
  let N := (∏ q ∈ P, q) * qs.prod
  let core := coreExtension p P qs
  let tail := complementList N qs
  let D := strongBlockDivisors p P
  have hN : 0 < N := Nat.mul_pos
    (Finset.prod_pos fun q hq ↦ (hblock q hq).1.pos)
    (List.prod_pos fun q hq ↦ (hqsData q hq).1)
  have hdivAll : ∀ q ∈ (P.sort (fun a b ↦ a ≥ b)) ++ qs, q ∣ N := by
    intro q hq
    rcases List.mem_append.mp hq with hqP | hqQs
    · have hqP' : q ∈ P :=
        (Finset.mem_sort (s := P) (fun a b ↦ a ≥ b)).mp hqP
      exact (Finset.dvd_prod_of_mem id hqP').mul_right qs.prod
    · have hqDiv : q ∣ qs.prod := by
        have hsingle := finsetSubproduct_dvd_listProd hqsNodup
          (K := {q}) (by simp [hqQs])
        simpa using hsingle
      exact dvd_mul_of_dvd_right hqDiv _
  have hposAll : ∀ q ∈ (P.sort (fun a b ↦ a ≥ b)) ++ qs, 0 < q := by
    intro q hq
    rcases List.mem_append.mp hq with hqP | hqQs
    · exact (hblock q ((Finset.mem_sort (s := P)
        (fun a b ↦ a ≥ b)).mp hqP)).1.pos
    · exact (hqsData q hqQs).1
  have hcoreSlow : SlowExtension F core := by
    exact slowExtension_coreExtension hu12 hblock hp hrich hqsCore hF
  have htailSlow0 : SlowExtension
      (complementList N (P.sort (fun a b ↦ a ≥ b))).sum tail := by
    exact hseeded.complement_tail hN hPLlen hposAll hdivAll
  have hcompLe :
      (complementList N (P.sort (fun a b ↦ a ≥ b))).sum ≤ core.sum := by
    exact sum_complement_block_le_core hu12 hblock hp hPcard hqsNodup hqsLarge
  have htailSlow : SlowExtension (F + core.sum) tail :=
    htailSlow0.mono_start (hcompLe.trans (Nat.le_add_left _ _))
  have hslow : SlowExtension F (core ++ tail) := by
    rw [slowExtension_append]
    exact ⟨hcoreSlow, htailSlow⟩
  have hcoreNodup : core.Nodup := coreExtension_nodup hu12 hblock hqsNodup hqsLarge
  have htailNodup : tail.Nodup := by
    apply complementList_nodup hN hqsNodup
    intro q hq
    exact hdivAll q (by simp [hq])
  have hcoreTail : ∀ d ∈ core, ∀ e ∈ tail, d ≠ e := by
    exact coreExtension_disjoint_complementList hPcard
      (fun q hq ↦ (hblock q hq).1) hqsNodup hqsPrime hdisj
  have hlistNodup : (core ++ tail).Nodup := by
    rw [List.nodup_append]
    exact ⟨hcoreNodup, htailNodup, hcoreTail⟩
  have hDcore : Disjoint D core.toFinset := by
    exact strongBlockDivisors_disjoint_core hu12 hblock hp hqsLarge
  have hDtail : Disjoint D tail.toFinset := by
    rw [Finset.disjoint_left]
    intro d hdD heTail
    exact strongBlockDivisors_disjoint_complementList hp hPcard
      (fun q hq ↦ (hblock q hq).1) hqsNodup hqsPrime hdisj
      d hdD d (by simpa using heTail) rfl
  have hDlist : Disjoint D (core ++ tail).toFinset := by
    rw [List.toFinset_append, Finset.disjoint_union_right]
    exact ⟨hDcore, hDtail⟩
  have hDproper : D ⊆ N.properDivisors := by
    intro d hd
    exact strongBlockDivisors_mem_kernelProper hp hPcard
      (fun q hq ↦ (hblock q hq).1) hqsNodup hqsPrime hdisj d hd
  have hlistProper : ∀ d ∈ core ++ tail, d ∈ N.properDivisors := by
    intro d hd
    rcases List.mem_append.mp hd with hdCore | hdTail
    · exact coreExtension_mem_kernelProper hPcard
        (fun q hq ↦ (hblock q hq).1) hqsNodup hqsPrime hdisj d hdCore
    · exact complementList_mem_kernelProper
        (Finset.prod_pos fun q hq ↦ (hblock q hq).1.pos) hqsNodup
        (fun q hq ↦ by have := (hqsData q hq).2.1; omega) d hdTail
  have hEn : E ≤ N := by
    have hseedSum := sum_strongBlockDivisors_lt_kernel hu12 hblock hp hPcard
      (fun q hq ↦ (hqsData q hq).1)
    exact hEsum.trans hseedSum.le
  have htotal : N < (complementList N
      ((P.sort (fun a b ↦ a ≥ b)) ++ qs)).sum :=
    sum_complementList_gt_of_mass_gt_one hN hdivAll hmassList
  have hnTop : N ≤ E + (F + (core ++ tail).sum) := by
    have hsplit : (complementList N
        ((P.sort (fun a b ↦ a ≥ b)) ++ qs)).sum =
        (complementList N (P.sort (fun a b ↦ a ≥ b))).sum + tail.sum := by
      simp [complementList, tail]
    rw [hsplit] at htotal
    simp only [List.sum_append]
    omega
  have hPseudoN : Pseudoperfect N := by
    exact Pseudoperfect.of_cover_extension hDproper hlistProper hcover hslow
      hlistNodup hDlist hEn hnTop
  have hUsub : P ∪ qs.toFinset ⊆ n.primeFactors := by
    intro q hq
    rcases Finset.mem_union.mp hq with hqP | hqQs
    · exact (mem_dyadicPrimePart.mp hqP).1
    · have hqAll : q ∈ flattenIndexedBlocks Cs := by
        have hqQsList : q ∈ qs := by simpa using hqQs
        have hqRest : q ∈ flattenIndexedBlocks rest := by
          simpa [qs] using hqQsList
        rw [hCs]
        exact List.mem_append_right _ hqRest
      exact selectedRichBlocks_element_mem hqAll
  have hUprod : (P ∪ qs.toFinset).prod id = N := by
    rw [Finset.prod_union hdisj.symm]
    have hqsProd : qs.toFinset.prod id = qs.prod := by
      calc
        qs.toFinset.prod id = (qs.map id).prod := List.prod_toFinset id hqsNodup
        _ = qs.prod := by simp
    rw [hqsProd]
    rfl
  have hNdvd : N ∣ n := by
    rw [← hUprod]
    exact (Finset.prod_dvd_prod_of_subset _ _ id hUsub).trans
      (Nat.prod_primeFactors_dvd n)
  exact hPseudoN.of_dvd hNdvd hn

/-- The finite Euler factor contributed by primes below `L`. -/
def smallPrimeFactor (L : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range L).filter Nat.Prime, (p : ℝ) / (p - 1)

lemma smallPrimeFactor_pos (L : ℕ) : 0 < smallPrimeFactor L := by
  rw [smallPrimeFactor]
  apply Finset.prod_pos
  intro p hp
  have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
  have hpR : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
  exact div_pos (by positivity) (sub_pos.mpr hpR)

lemma primeFactors_smoothPart_subset {L n : ℕ} :
    (smoothPart L n).primeFactors ⊆ (Finset.range L).filter Nat.Prime := by
  intro p hp
  have hmem : p ∈ (smoothPart L n).factorization.support := hp
  rw [factorization_smoothPart, smoothFactorization, Finsupp.support_filter] at hmem
  have hpData := Finset.mem_filter.mp hmem
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpData.2,
    Nat.prime_of_mem_primeFactors hp⟩

lemma smoothPart_abundancy_le {L n : ℕ} (hn : 0 < n) :
    abundancy (smoothPart L n) ≤ smallPrimeFactor L := by
  apply (abundancy_le_primeEulerProduct (smoothPart_pos hn)).trans
  rw [smallPrimeFactor]
  apply Finset.prod_le_prod_of_subset_of_one_le primeFactors_smoothPart_subset
  · intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpR : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
    exact div_nonneg (by positivity) (sub_pos.mpr hpR).le
  · intro p hp hpnmem
    have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
    have hpR : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
    apply (one_le_div₀ (sub_pos.mpr hpR)).2
    linarith

lemma abundancy_nonneg (n : ℕ) : 0 ≤ abundancy n := by
  rw [abundancy]
  positivity

lemma abundancy_eq_roughPart_mul_smoothPart {L n : ℕ} (hn : 0 < n) :
    abundancy n = abundancy (roughPart L n) * abundancy (smoothPart L n) := by
  calc
    abundancy n = abundancy (roughPart L n * smoothPart L n) := by
      rw [roughPart_mul_smoothPart hn.ne']
    _ = abundancy (roughPart L n) * abundancy (smoothPart L n) :=
      abundancy_mul_of_coprime (roughPart_pos hn) (smoothPart_pos hn)
        (roughPart_coprime_smoothPart hn)

lemma roughPart_not_pseudoperfect {L n : ℕ} (hn : 0 < n)
    (hnot : ¬Pseudoperfect n) : ¬Pseudoperfect (roughPart L n) := by
  intro hrough
  exact hnot (hrough.of_dvd (roughPart_dvd hn) hn)

/-- The elementary finite-prime reduction in Larsen's proof.  Once all
`L`-rough non-pseudoperfect integers have abundancy at most `A`, every
non-pseudoperfect integer has abundancy at most the displayed finite Euler
factor. -/
lemma nonpseudoperfect_bound_of_rough_bound
    (L : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hrough : ∀ m : ℕ, 0 < m → Rough L m → ¬Pseudoperfect m → abundancy m ≤ A) :
    ∀ n : ℕ, ¬Pseudoperfect n →
      (σ 1 n : ℝ) ≤ (A * smallPrimeFactor L) * n := by
  intro n hnot
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hrle : abundancy (roughPart L n) ≤ A :=
    hrough (roughPart L n) (roughPart_pos hnpos) (roughPart_rough hnpos)
      (roughPart_not_pseudoperfect hnpos hnot)
  have hsle := smoothPart_abundancy_le (L := L) hnpos
  have hnle : abundancy n ≤ A * smallPrimeFactor L := by
    rw [abundancy_eq_roughPart_mul_smoothPart hnpos]
    exact mul_le_mul hrle hsle (abundancy_nonneg _) hA
  rw [abundancy, div_le_iff₀ (by exact_mod_cast hnpos : (0 : ℝ) < n)] at hnle
  exact hnle

/-- Fixed-threshold form of the final elementary reduction: a Larsen theorem
for one positive `A` produces the absolute constant required by Erdős 825. -/
lemma conclusion_of_rough_pseudoperfect
    (L : ℕ) (A : ℝ) (hA : 0 < A)
    (hrough : ∀ m : ℕ, 0 < m → Rough L m → A < abundancy m → Pseudoperfect m) :
    ∃ C : ℝ, C > 0 ∧
      ∀ n : ℕ, (σ 1 n : ℝ) > C * n → Pseudoperfect n := by
  let C := A * smallPrimeFactor L
  have hC : 0 < C := mul_pos hA (smallPrimeFactor_pos L)
  refine ⟨C, hC, conclusion_of_nonpseudoperfect_bound C ?_⟩
  apply nonpseudoperfect_bound_of_rough_bound L A hA.le
  intro m hmpos hmrough hmnot
  exact le_of_not_gt fun hmgt => hmnot (hrough m hmpos hmrough hmgt)

/-- Erdős Problem 825: sufficiently large abundancy forces a representation
as a sum of distinct proper divisors. -/
theorem erdos_825 :
    ∃ (C : ℝ) (_ : C > 0),
      ∀ (n) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id := by
  let A := Real.exp (2 * roughMassTarget)
  have hA : 0 < A := Real.exp_pos _
  have hroughA : ∀ m : ℕ, 0 < m → Rough (2 ^ 12) m →
      A < abundancy m → Pseudoperfect m := by
    intro m hm hmRough hmLarge
    apply rough_pseudoperfect_of_mass hm hmRough
    apply primeReciprocalMass_gt_of_exp_lt_abundancy hm
    simpa [A] using hmLarge
  obtain ⟨C, hC, hconclusion⟩ :=
    conclusion_of_rough_pseudoperfect (2 ^ 12) A hA hroughA
  exact ⟨C, hC, hconclusion⟩

end

end Erdos825
