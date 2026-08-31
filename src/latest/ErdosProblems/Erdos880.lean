/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 880.
https://www.erdosproblems.com/forum/thread/880

Informal authors:
- Norbert Hegyvári
- François Hennecart
- Alain Plagne

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos880.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Erdős Problem 880

Hegyvári, Hennecart, and Plagne proved that the sums of at most two
distinct elements of an additive basis of order two have eventual gaps at
most two, while for every order at least three there is an additive basis
whose corresponding restricted sumset has unbounded gaps.

The detailed mathematical reconstruction and Leanization plan are in
`tex/880.tex`.  The counterexample below is the linear-spike variant of
the block construction proved there.
-/

open Filter

namespace Erdos880

open scoped BigOperators

/-- `n` is a sum of at most `k` (not necessarily distinct) elements of `A`. -/
def UnrestrictedSum (A : Set ℕ) (k n : ℕ) : Prop :=
  ∃ l : List ℕ, l.length ≤ k ∧ (∀ a ∈ l, a ∈ A) ∧ l.sum = n

/-- Sums of at most `k` pairwise distinct elements of `A`. -/
def restrictedSums (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n | ∃ s : Finset ℕ, (s : Set ℕ) ⊆ A ∧ s.card ≤ k ∧ ∑ a ∈ s, a = n}

/-- An infinite asymptotic additive basis whose least unrestricted order is `k`. -/
def IsAdditiveBasisOfOrder (A : Set ℕ) (k : ℕ) : Prop :=
  A.Infinite ∧
    (∀ᶠ n in atTop, UnrestrictedSum A k n) ∧
    ∀ j < k, ¬∀ᶠ n in atTop, UnrestrictedSum A j n

/-- The increasing enumeration of a set of naturals.  It has its intended
meaning whenever the set is infinite. -/
noncomputable def enum (B : Set ℕ) (n : ℕ) : ℕ := Nat.nth (fun m ↦ m ∈ B) n

/-- The exact discrete meaning of `b_(n+1) - b_n = O(1)`. -/
def HasBoundedGaps (B : Set ℕ) : Prop :=
  ∃ C, ∀ n, enum B (n + 1) - enum B n ≤ C

/-- A sharp eventual bound for the consecutive gaps. -/
def EventuallyGapAtMost (B : Set ℕ) (C : ℕ) : Prop :=
  ∀ᶠ n in atTop, enum B (n + 1) - enum B n ≤ C

lemma singleton_mem_restrictedSums {A : Set ℕ} {k a : ℕ}
    (hk : 1 ≤ k) (ha : a ∈ A) : a ∈ restrictedSums A k := by
  refine ⟨{a}, ?_, by simpa using hk, by simp⟩
  intro x hx
  simp only [Finset.mem_coe, Finset.mem_singleton] at hx
  subst x
  exact ha

lemma restrictedSums_infinite {A : Set ℕ} {k : ℕ}
    (hA : A.Infinite) (hk : 1 ≤ k) : (restrictedSums A k).Infinite := by
  apply hA.mono
  intro a ha
  exact singleton_mem_restrictedSums hk ha

lemma exists_odd_between_of_two_lt_sub {x y : ℕ} (h : 2 < y - x) :
    ∃ z, Odd z ∧ x < z ∧ z < y := by
  obtain ⟨k, hx | hx⟩ := Nat.even_or_odd' x
  · refine ⟨x + 1, ?_, by omega, by omega⟩
    exact ⟨k, by omega⟩
  · refine ⟨x + 2, ?_, by omega, by omega⟩
    exact ⟨k + 1, by omega⟩

lemma odd_mem_restrictedSums_two {A : Set ℕ} {n : ℕ}
    (hn : Odd n) (hrep : UnrestrictedSum A 2 n) : n ∈ restrictedSums A 2 := by
  rcases hrep with ⟨l, hlen, hmem, hsum⟩
  cases l with
  | nil =>
      simp only [List.sum_nil] at hsum
      subst n
      exact (Nat.not_odd_zero hn).elim
  | cons a l =>
      cases l with
      | nil =>
          simp at hsum
          refine ⟨{a}, ?_, by simp, ?_⟩
          · intro x hx
            simp only [Finset.mem_coe, Finset.mem_singleton] at hx
            subst x
            exact hmem a (by simp)
          · simpa using hsum
      | cons b l =>
          cases l with
          | nil =>
              simp at hsum
              have ha : a ∈ A := hmem a (by simp)
              have hb : b ∈ A := hmem b (by simp)
              have hab : a ≠ b := by
                intro hab
                subst b
                rcases hn with ⟨t, ht⟩
                omega
              refine ⟨{a, b}, ?_, by simp [hab], ?_⟩
              · intro x hx
                simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl <;> assumption
              · simpa [hab, add_comm] using hsum
          | cons c l =>
              simp at hlen

private lemma enum_index_le {B : Set ℕ} (hB : B.Infinite) (n : ℕ) : n ≤ enum B n := by
  have hp : (Set.ofPred fun m ↦ m ∈ B).Infinite := by simpa using hB
  have hmono : StrictMono (Nat.nth fun m ↦ m ∈ B) := Nat.nth_strictMono hp
  induction n with
  | zero => omega
  | succ n ih =>
      have hs := hmono (Nat.lt_succ_self n)
      change Nat.succ n ≤ Nat.nth (fun m ↦ m ∈ B) (Nat.succ n)
      change n ≤ Nat.nth (fun m ↦ m ∈ B) n at ih
      omega

/-- The sharp affirmative part: for order two, all sufficiently late gaps are at most two. -/
theorem order_two_eventually_gap_le_two {A : Set ℕ}
    (hA : IsAdditiveBasisOfOrder A 2) :
    EventuallyGapAtMost (restrictedSums A 2) 2 := by
  rcases (eventually_atTop.1 hA.2.1) with ⟨M, hM⟩
  let B := restrictedSums A 2
  have hB : B.Infinite := restrictedSums_infinite hA.1 (by omega)
  have hp : (Set.ofPred fun m ↦ m ∈ B).Infinite := by simpa using hB
  filter_upwards [eventually_ge_atTop M] with n hn
  let x := enum B n
  let y := enum B (n + 1)
  have hxy : x < y := by
    exact (Nat.nth_strictMono hp) (Nat.lt_succ_self n)
  have hxM : M ≤ x := le_trans hn (enum_index_le hB n)
  by_contra hgap
  have hlarge : 2 < y - x := Nat.lt_of_not_ge hgap
  obtain ⟨z, hzodd, hxz, hzy⟩ := exists_odd_between_of_two_lt_sub hlarge
  have hzrep : UnrestrictedSum A 2 z := hM z (by omega)
  have hzB : z ∈ B := odd_mem_restrictedSums_two hzodd hzrep
  have hyz : y ≤ z := by
    have hleast := Nat.isLeast_nth_of_infinite hp (n + 1)
    have hzleast : z ∈ {i | (fun m ↦ m ∈ B) i ∧
        ∀ k < n + 1, Nat.nth (fun m ↦ m ∈ B) k < i} := by
      refine ⟨hzB, ?_⟩
      intro k hk
      have hkn : k ≤ n := by omega
      have hkx : Nat.nth (fun m ↦ m ∈ B) k ≤ x := by
        simpa [x, enum] using (Nat.nth_monotone hp hkn)
      exact hkx.trans_lt hxz
    simpa [y, enum] using hleast.2 hzleast
  exact (not_lt_of_ge hyz) hzy

lemma boundedGaps_of_eventually {B : Set ℕ} (hB : B.Infinite) {C : ℕ}
    (h : EventuallyGapAtMost B C) : HasBoundedGaps B := by
  rcases (eventually_atTop.1 h) with ⟨N, hN⟩
  refine ⟨max C (enum B N), fun n ↦ ?_⟩
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (le_max_left _ _)
  · have hn' : n + 1 ≤ N := by omega
    have hp : (Set.ofPred fun m ↦ m ∈ B).Infinite := by simpa using hB
    have hnext : enum B (n + 1) ≤ enum B N := by
      simpa [enum] using (Nat.nth_monotone hp hn')
    exact (Nat.sub_le _ _).trans (hnext.trans (le_max_right _ _))

/-- The affirmative half of Erdős Problem 880. -/
theorem order_two_bounded_gaps {A : Set ℕ} (hA : IsAdditiveBasisOfOrder A 2) :
    HasBoundedGaps (restrictedSums A 2) := by
  apply boundedGaps_of_eventually (restrictedSums_infinite hA.1 (by omega))
  exact order_two_eventually_gap_le_two hA

/-! ## The linear-spike counterexample -/

/-- The quadratic coefficient in the block recurrence. -/
def coeff (h : ℕ) : ℕ := (h - 1) ^ 2 + 1

/-- The rapidly increasing block scale. -/
def scale (h : ℕ) : ℕ → ℕ
  | 0 => h
  | n + 1 => coeff h * scale h n ^ 2 + h * scale h n

/-- The interval offsets and the `h-1` linear spikes in block `n`. -/
def offsetBlock (h n : ℕ) : Set ℕ :=
  {d | d < scale h n ^ 2 ∨ ∃ j, 1 ≤ j ∧ j ≤ h - 1 ∧ d = j * scale h n ^ 2}

/-- The explicit basis used for the negative answer. -/
def counterexample (h : ℕ) : Set ℕ :=
  {a | a = 0 ∨ ∃ n d, d ∈ offsetBlock h n ∧ a = scale h n + d}

lemma coeff_pos (h : ℕ) : 0 < coeff h := by
  simp [coeff]

lemma scale_pos {h : ℕ} (hh : 1 ≤ h) (n : ℕ) : 0 < scale h n := by
  induction n with
  | zero => simp [scale]; omega
  | succ n ih =>
      simp only [scale]
      positivity

lemma scale_ge {h : ℕ} (hh : 1 ≤ h) (n : ℕ) : h ≤ scale h n := by
  induction n with
  | zero => simp [scale]
  | succ n ih =>
      simp only [scale]
      have hmul : scale h n ≤ h * scale h n := by
        simpa [one_mul] using Nat.mul_le_mul_right (scale h n) hh
      omega

lemma scale_lt_succ {h : ℕ} (hh : 2 ≤ h) (n : ℕ) : scale h n < scale h (n + 1) := by
  rw [scale]
  have hx := scale_pos (show 1 ≤ h by omega) n
  have hmul : 2 * scale h n ≤ h * scale h n := Nat.mul_le_mul_right _ hh
  omega

lemma scale_strictMono {h : ℕ} (hh : 2 ≤ h) : StrictMono (scale h) := by
  exact strictMono_nat_of_lt_succ (scale_lt_succ hh)

lemma scale_add_le {h : ℕ} (hh : 2 ≤ h) (n : ℕ) : h + n ≤ scale h n := by
  induction n with
  | zero => simp [scale]
  | succ n ih =>
      have hs := scale_lt_succ hh n
      omega

lemma exists_scale_interval {h m : ℕ} (hh : 2 ≤ h) (hm : h ≤ m) :
    ∃ n, scale h n ≤ m ∧ m < scale h (n + 1) := by
  have hex : ∃ j, m < scale h j := by
    refine ⟨m + 1, ?_⟩
    have := scale_add_le hh (m + 1)
    omega
  let j := Nat.find hex
  have hj : m < scale h j := Nat.find_spec hex
  have hj0 : j ≠ 0 := by
    intro hj0
    rw [hj0] at hj
    simp [scale] at hj
    omega
  obtain ⟨n, hjEq⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  refine ⟨n, ?_, ?_⟩
  · by_contra hn
    have hlt : m < scale h n := Nat.lt_of_not_ge hn
    have hnfind : n < Nat.find hex := by omega
    exact (Nat.find_min hex hnfind) hlt
  · simpa [j, hjEq] using hj

lemma offsetBlock_zero {h : ℕ} (hh : 1 ≤ h) (n : ℕ) : 0 ∈ offsetBlock h n := by
  left
  exact pow_pos (scale_pos hh n) 2

lemma offsetBlock_le {h n d : ℕ} (hh : 2 ≤ h) (hd : d ∈ offsetBlock h n) :
    d ≤ (h - 1) * scale h n ^ 2 := by
  rcases hd with hd | ⟨j, hj1, hjh, rfl⟩
  · have hpow : 1 ≤ scale h n ^ 2 := pow_pos (scale_pos (by omega) n) 2
    have hm : 1 ≤ h - 1 := by omega
    nlinarith
  · exact Nat.mul_le_mul_right _ hjh

lemma block_lt_next {h n d : ℕ} (hh : 3 ≤ h) (hd : d ∈ offsetBlock h n) :
    scale h n + d < scale h (n + 1) := by
  have hdle := offsetBlock_le (show 2 ≤ h by omega) hd
  rw [scale]
  have hx := scale_pos (show 1 ≤ h by omega) n
  have hc : h - 1 < coeff h := by
    have hr : 1 ≤ h - 1 := by omega
    have hrsq : h - 1 ≤ (h - 1) ^ 2 := by
      simpa [pow_two, one_mul] using Nat.mul_le_mul_left (h - 1) hr
    simp only [coeff]
    omega
  nlinarith

lemma scale_mem_counterexample {h : ℕ} (hh : 1 ≤ h) (n : ℕ) :
    scale h n ∈ counterexample h := by
  right
  exact ⟨n, 0, offsetBlock_zero hh n, by simp⟩

lemma zero_mem_counterexample (h : ℕ) : 0 ∈ counterexample h := Or.inl rfl

lemma counterexample_infinite {h : ℕ} (hh : 3 ≤ h) : (counterexample h).Infinite := by
  have hinj : Function.Injective (scale h) := (scale_strictMono (by omega)).injective
  have hrange : (Set.range (scale h)).Infinite := Set.infinite_range_of_injective hinj
  apply hrange.mono
  rintro _ ⟨n, rfl⟩
  exact scale_mem_counterexample (by omega) n

lemma counterexample_prefix_le {h n a : ℕ} (hh : 3 ≤ h)
    (ha : a ∈ counterexample h) (halt : a < scale h (n + 1)) :
    a ≤ scale h n + (h - 1) * scale h n ^ 2 := by
  rcases ha with rfl | ⟨i, d, hd, rfl⟩
  · omega
  have hin : i ≤ n := by
    by_contra hnot
    have hni : n + 1 ≤ i := by omega
    have hscale : scale h (n + 1) ≤ scale h i :=
      (scale_strictMono (by omega)).monotone hni
    omega
  rcases hin.eq_or_lt with rfl | hin
  · exact Nat.add_le_add_left (offsetBlock_le (show 2 ≤ h by omega) hd) _
  · have hblock : scale h i + d < scale h (i + 1) := block_lt_next hh hd
    have hscale : scale h (i + 1) ≤ scale h n :=
      (scale_strictMono (by omega)).monotone hin
    omega

lemma counterexample_prefix_classify {h n a : ℕ} (hh : 3 ≤ h)
    (ha : a ∈ counterexample h) (halt : a < scale h (n + 1)) :
    a < scale h n + scale h n ^ 2 ∨
      ∃ j, 1 ≤ j ∧ j ≤ h - 1 ∧ a = scale h n + j * scale h n ^ 2 := by
  rcases ha with rfl | ⟨i, d, hd, rfl⟩
  · left
    have := scale_pos (show 1 ≤ h by omega) n
    positivity
  have hin : i ≤ n := by
    by_contra hnot
    have hni : n + 1 ≤ i := by omega
    have hscale : scale h (n + 1) ≤ scale h i :=
      (scale_strictMono (by omega)).monotone hni
    omega
  rcases hin.eq_or_lt with rfl | hin
  · rcases hd with hd | ⟨j, hj1, hjh, rfl⟩
    · exact Or.inl (Nat.add_lt_add_left hd _)
    · exact Or.inr ⟨j, hj1, hjh, rfl⟩
  · left
    have hblock : scale h i + d < scale h (i + 1) := block_lt_next hh hd
    have hscale : scale h (i + 1) ≤ scale h n :=
      (scale_strictMono (by omega)).monotone hin
    have hx := scale_pos (show 1 ≤ h by omega) n
    nlinarith

lemma exists_bounded_coefficients {r q : ℕ} (hr : 0 < r) (hq : q ≤ r ^ 2) :
    ∃ l : List ℕ, l.length = r ∧ (∀ a ∈ l, a ≤ r) ∧ l.sum = q := by
  let t := q / r
  let s := q % r
  let core := List.replicate t r ++ if s = 0 then [] else [s]
  have hslt : s < r := Nat.mod_lt _ hr
  have hdiv : t * r + s = q := by
    simpa [t, s, mul_comm] using Nat.div_add_mod q r
  have ht : t ≤ r := by
    by_contra htr
    have hrt : r + 1 ≤ t := by omega
    have hmul : (r + 1) * r ≤ t * r := Nat.mul_le_mul_right r hrt
    nlinarith
  have hcore : core.length ≤ r := by
    simp only [core, List.length_append, List.length_replicate]
    split_ifs with hs
    · simp [ht]
    · simp only [List.length_cons, List.length_nil, zero_add, Order.add_one_le_iff]
      have hts : t < r := by
        by_contra hnot
        have htr : r ≤ t := by omega
        have htEq : t = r := Nat.le_antisymm ht htr
        rw [htEq] at hdiv
        have hspos : 0 < s := Nat.pos_of_ne_zero hs
        have hq' : q ≤ r * r := by simpa [pow_two] using hq
        omega
      omega
  let l := core ++ List.replicate (r - core.length) 0
  refine ⟨l, ?_, ?_, ?_⟩
  · simp [l, Nat.add_sub_of_le hcore]
  · intro a ha
    simp only [l, List.mem_append, List.mem_replicate] at ha
    rcases ha with ha | ha
    · simp only [core, List.mem_append, List.mem_replicate] at ha
      rcases ha with (⟨_, rfl⟩ | ha)
      · exact le_rfl
      · split_ifs at ha with hs
        · simp at ha
        · simp only [List.mem_singleton] at ha
          subst a
          exact hslt.le
    · rcases ha with ⟨_, rfl⟩
      exact Nat.zero_le _
  · simp only [l, List.sum_append, List.sum_replicate, smul_eq_mul, mul_zero, add_zero]
    simp only [core, List.sum_append, List.sum_replicate, smul_eq_mul]
    split_ifs with hs
    · rw [hs, add_zero] at hdiv
      rw [List.sum_nil, add_zero]
      exact hdiv
    · simp only [List.sum_singleton]
      exact hdiv

lemma coeff_mul_mem_offsetBlock {h n q : ℕ} (hh : 3 ≤ h) (hq : q ≤ h - 1) :
    q * scale h n ^ 2 ∈ offsetBlock h n := by
  by_cases hq0 : q = 0
  · subst q
    simpa using offsetBlock_zero (show 1 ≤ h by omega) n
  · right
    exact ⟨q, Nat.pos_of_ne_zero hq0, hq, rfl⟩

lemma offset_coverage {h n d : ℕ} (hh : 3 ≤ h)
    (hd : d < coeff h * scale h n ^ 2) :
    ∃ l : List ℕ, l.length = h ∧
      (∀ a ∈ l, a ∈ offsetBlock h n) ∧ l.sum = d := by
  let X := scale h n ^ 2
  have hX : 0 < X := pow_pos (scale_pos (show 1 ≤ h by omega) n) 2
  let q := d / X
  let s := d % X
  have hq_lt : q < coeff h := by
    exact (Nat.div_lt_iff_lt_mul hX).2 (by simpa [mul_comm] using hd)
  have hq : q ≤ (h - 1) ^ 2 := by
    simpa [q, coeff] using Nat.le_of_lt_succ hq_lt
  have hs : s < X := Nat.mod_lt _ hX
  have hdiv : q * X + s = d := by
    simpa [q, s, mul_comm] using Nat.div_add_mod d X
  obtain ⟨c, hclen, hcbound, hcsum⟩ :=
    exists_bounded_coefficients (show 0 < h - 1 by omega) hq
  let l := s :: c.map (fun a ↦ a * X)
  refine ⟨l, ?_, ?_, ?_⟩
  · simp [l, hclen]
    omega
  · intro a ha
    simp only [l, List.mem_cons, List.mem_map] at ha
    rcases ha with rfl | ⟨b, hb, rfl⟩
    · exact Or.inl hs
    · exact coeff_mul_mem_offsetBlock hh (hcbound b hb)
  · simp only [l, List.sum_cons, List.sum_map_mul_right]
    have hid : c.map (fun b ↦ b) = c := by simp
    rw [hid]
    rw [hcsum]
    omega

private lemma sum_map_add_const (l : List ℕ) (x : ℕ) :
    (l.map (fun a ↦ x + a)).sum = l.length * x + l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      simp [Nat.succ_mul, add_assoc, add_comm, add_left_comm]

lemma unrestrictedSum_counterexample_of_ge {h m : ℕ} (hh : 3 ≤ h) (hm : h ≤ m) :
    UnrestrictedSum (counterexample h) h m := by
  obtain ⟨n, hnm, hmn⟩ := exists_scale_interval (show 2 ≤ h by omega) hm
  let x := scale h n
  let X := x ^ 2
  by_cases hsmall : m < h * x
  · have hdx : m - x < X := by
      have hx : h ≤ x := scale_ge (show 1 ≤ h by omega) n
      dsimp [x, X]
      nlinarith [Nat.sub_add_cancel hnm]
    have hmem : m ∈ counterexample h := by
      right
      refine ⟨n, m - x, Or.inl ?_, ?_⟩
      · simpa [x, X] using hdx
      · exact (Nat.add_sub_of_le hnm).symm
    exact ⟨[m], by simp; omega, by simpa using hmem, by simp⟩
  · have hxm : h * x ≤ m := Nat.le_of_not_gt hsmall
    let d := m - h * x
    have hdadd : h * x + d = m := Nat.add_sub_of_le hxm
    have hd : d < coeff h * X := by
      have hdadd' : h * scale h n + d = m := by simpa [x] using hdadd
      rw [show X = scale h n ^ 2 by simp [X, x]]
      rw [scale] at hmn
      omega
    obtain ⟨o, holen, homem, hosum⟩ := offset_coverage hh hd
    let l := o.map (fun a ↦ x + a)
    refine ⟨l, ?_, ?_, ?_⟩
    · simp [l, holen]
    · intro a ha
      simp only [l, List.mem_map] at ha
      rcases ha with ⟨b, hb, rfl⟩
      right
      exact ⟨n, b, homem b hb, rfl⟩
    · rw [show l = o.map (fun a ↦ x + a) by rfl, sum_map_add_const, holen, hosum]
      simpa [x, d, mul_comm] using hdadd

lemma counterexample_eventually_unrestricted {h : ℕ} (hh : 3 ≤ h) :
    ∀ᶠ m in atTop, UnrestrictedSum (counterexample h) h m := by
  filter_upwards [eventually_ge_atTop h] with m hm
  exact unrestrictedSum_counterexample_of_ge hh hm

private lemma list_sum_le_length_mul {l : List ℕ} {C : ℕ}
    (h : ∀ a ∈ l, a ≤ C) : l.sum ≤ l.length * C := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.sum_cons, List.length_cons]
      have ha : a ≤ C := h a (by simp)
      have hl : ∀ b ∈ l, b ≤ C := by
        intro b hb
        exact h b (by simp [hb])
      specialize ih hl
      calc
        a + l.sum ≤ C + l.length * C := Nat.add_le_add ha ih
        _ = (l.length + 1) * C := by
          simp [Nat.add_mul, add_comm]

/-- A cofinal sequence of integers missed by every unrestricted order below `h`. -/
def missed (h n : ℕ) : ℕ :=
  (h - 1) * scale h n + (h - 1) ^ 2 * scale h n ^ 2 + 1

lemma missed_lt_next {h n : ℕ} (hh : 3 ≤ h) : missed h n < scale h (n + 1) := by
  have hx := scale_pos (show 1 ≤ h by omega) n
  have hh' : h = (h - 1) + 1 := by omega
  have hgap : 1 < scale h n ^ 2 + scale h n := by nlinarith
  calc
    missed h n = (h - 1) ^ 2 * scale h n ^ 2 +
        (h - 1) * scale h n + 1 := by simp [missed, add_comm]
    _ < (h - 1) ^ 2 * scale h n ^ 2 + (h - 1) * scale h n +
        (scale h n ^ 2 + scale h n) := by omega
    _ = scale h (n + 1) := by
      calc
        _ = ((h - 1) ^ 2 + 1) * scale h n ^ 2 +
            ((h - 1) + 1) * scale h n := by ring
        _ = coeff h * scale h n ^ 2 + h * scale h n := by rw [← hh']; rfl
        _ = scale h (n + 1) := by rw [scale]

lemma missed_not_unrestricted {h j n : ℕ} (hh : 3 ≤ h) (hj : j < h) :
    ¬UnrestrictedSum (counterexample h) j (missed h n) := by
  rintro ⟨l, hlen, hmem, hsum⟩
  have hterm : ∀ a ∈ l, a ≤ scale h n + (h - 1) * scale h n ^ 2 := by
    intro a ha
    apply counterexample_prefix_le hh (hmem a ha)
    have hale : a ≤ l.sum := List.le_sum_of_mem ha
    rw [hsum] at hale
    exact hale.trans_lt (missed_lt_next hh)
  have hsum_le := list_sum_le_length_mul hterm
  rw [hsum] at hsum_le
  have hlen' : l.length ≤ h - 1 := by omega
  have hmul : l.length * (scale h n + (h - 1) * scale h n ^ 2) ≤
      (h - 1) * (scale h n + (h - 1) * scale h n ^ 2) :=
    Nat.mul_le_mul_right _ hlen'
  simp only [missed] at hsum_le
  nlinarith

lemma counterexample_exact_order {h : ℕ} (hh : 3 ≤ h) :
    IsAdditiveBasisOfOrder (counterexample h) h := by
  refine ⟨counterexample_infinite hh, counterexample_eventually_unrestricted hh, ?_⟩
  intro j hj hev
  rcases eventually_atTop.1 hev with ⟨N, hN⟩
  let n := N + 1
  have hlarge : N ≤ missed h n := by
    have hs := scale_add_le (show 2 ≤ h by omega) n
    have hsN : N ≤ scale h n := by
      dsimp [n] at hs ⊢
      omega
    have hr : 1 ≤ h - 1 := by omega
    have hfirst : scale h n ≤ (h - 1) * scale h n := by
      simpa [one_mul] using Nat.mul_le_mul_right (scale h n) hr
    have hadd : (h - 1) * scale h n ≤
        (h - 1) * scale h n + ((h - 1) ^ 2 * scale h n ^ 2 + 1) :=
      Nat.le_add_right _ _
    exact hsN.trans (hfirst.trans (by simp [missed, add_assoc] at hadd ⊢))
  exact missed_not_unrestricted hh hj (hN (missed h n) hlarge)

private lemma sum_Icc_one_add_one_le_sq {r : ℕ} (hr : 2 ≤ r) :
    (∑ j ∈ Finset.Icc 1 r, j) + 1 ≤ r ^ 2 := by
  induction r, hr using Nat.le_induction with
  | base => norm_num [Finset.sum_Icc_succ_top]
  | succ r hr ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      nlinarith

private lemma selected_coeff_bound {r q : ℕ} (hr : 2 ≤ r) (J : Finset ℕ)
    (hJ : J ⊆ Finset.Icc 1 r) (hcard : J.card + q ≤ r + 1) :
    (∑ j ∈ J, j) + q ≤ r ^ 2 := by
  let U := Finset.Icc 1 r
  let K := U \ J
  have hUcard : U.card = r := by simp [U]
  have hKcard : K.card = r - J.card := by
    rw [show K = U \ J by rfl, Finset.card_sdiff,
      Finset.inter_eq_left.mpr hJ, hUcard]
  have hq : q ≤ K.card + 1 := by omega
  have hKsum : K.card ≤ ∑ j ∈ K, j := by
    calc
      K.card = ∑ _j ∈ K, 1 := by simp
      _ ≤ ∑ j ∈ K, j := by
        apply Finset.sum_le_sum
        intro j hj
        have hjU : j ∈ U := (Finset.mem_sdiff.1 hj).1
        simpa [U] using (Finset.mem_Icc.1 hjU).1
  have hdis : Disjoint J K := by
    rw [Finset.disjoint_left]
    intro j hjJ hjK
    exact (Finset.mem_sdiff.1 hjK).2 hjJ
  have hunion : J ∪ K = U := by
    ext j
    simp only [Finset.mem_union, K, Finset.mem_sdiff, U]
    constructor
    · rintro (hj | ⟨hjU, _⟩)
      · exact hJ hj
      · exact hjU
    · intro hjU
      by_cases hj : j ∈ J
      · exact Or.inl hj
      · exact Or.inr ⟨hjU, hj⟩
  have hsum : (∑ j ∈ J, j) + ∑ j ∈ K, j = ∑ j ∈ U, j := by
    rw [← Finset.sum_union hdis, hunion]
  have hfull : (∑ j ∈ U, j) + 1 ≤ r ^ 2 := by
    simpa [U] using sum_Icc_one_add_one_le_sq hr
  omega

private lemma finset_sum_le_card_mul {s : Finset ℕ} {C : ℕ}
    (h : ∀ a ∈ s, a ≤ C) : ∑ a ∈ s, a ≤ s.card * C := by
  calc
    ∑ a ∈ s, a ≤ ∑ _a ∈ s, C := by
      apply Finset.sum_le_sum
      exact h
    _ = s.card * C := by simp

private lemma spike_injective {x X : ℕ} (hX : 0 < X) :
    Function.Injective (fun j : ℕ ↦ x + j * X) := by
  intro i j hij
  have hmul : i * X = j * X := Nat.add_left_cancel hij
  exact Nat.mul_right_cancel hX hmul

/-- Every restricted sum below the next block lies below the block's gap. -/
lemma restricted_prefix_bound {h n b : ℕ} (hh : 3 ≤ h)
    (hb : b ∈ restrictedSums (counterexample h) h)
    (hbnext : b < scale h (n + 1)) :
    b ≤ h * scale h n + (h - 1) ^ 2 * scale h n ^ 2 := by
  classical
  rcases hb with ⟨s, hsA, hscard, hssum⟩
  let x := scale h n
  let X := x ^ 2
  let r := h - 1
  let low := s.filter (fun a ↦ a < x + X)
  let high := s.filter (fun a ↦ ¬a < x + X)
  let U := Finset.Icc 1 r
  let spike := fun j : ℕ ↦ x + j * X
  let J := U.filter (fun j ↦ spike j ∈ s)
  have hX : 0 < X := pow_pos (scale_pos (show 1 ≤ h by omega) n) 2
  have hJsub : J ⊆ U := Finset.filter_subset _ _
  have hparts : low ∪ high = s := by
    ext a
    simp only [Finset.mem_union, low, high, Finset.mem_filter]
    constructor
    · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
    · intro ha
      by_cases hlt : a < x + X
      · exact Or.inl ⟨ha, hlt⟩
      · exact Or.inr ⟨ha, hlt⟩
  have hdis : Disjoint low high := by
    rw [Finset.disjoint_left]
    intro a hal hah
    exact (Finset.mem_filter.1 hah).2 (Finset.mem_filter.1 hal).2
  have hinj : Function.Injective spike := spike_injective hX
  have himage : J.image spike = high := by
    ext a
    constructor
    · intro ha
      rcases Finset.mem_image.1 ha with ⟨j, hjJ, rfl⟩
      have hjU : j ∈ U := (Finset.mem_filter.1 hjJ).1
      have hjS : spike j ∈ s := (Finset.mem_filter.1 hjJ).2
      have hj1 : 1 ≤ j := by simpa [U] using (Finset.mem_Icc.1 hjU).1
      apply Finset.mem_filter.2
      refine ⟨hjS, ?_⟩
      simp only [spike]
      have hjX : X ≤ j * X := by
        simpa [one_mul] using Nat.mul_le_mul_right X hj1
      omega
    · intro ha
      have haS : a ∈ s := (Finset.mem_filter.1 ha).1
      have hanot : ¬a < x + X := (Finset.mem_filter.1 ha).2
      have hale : a ≤ b := by
        have hsingle := Finset.single_le_sum (f := fun z : ℕ ↦ z)
          (fun _ _ ↦ Nat.zero_le _) haS
        simpa [hssum] using hsingle
      have halt : a < scale h (n + 1) := hale.trans_lt hbnext
      rcases counterexample_prefix_classify hh (hsA haS) halt with halow | hspike
      · exact (hanot (by simpa [x, X] using halow)).elim
      · rcases hspike with ⟨j, hj1, hjr, haj⟩
        apply Finset.mem_image.2
        refine ⟨j, ?_, ?_⟩
        · apply Finset.mem_filter.2
          refine ⟨?_, ?_⟩
          · exact Finset.mem_Icc.2 ⟨hj1, by simpa [r] using hjr⟩
          · have hsp : spike j = a := by simpa [spike, x, X] using haj.symm
            simpa [hsp] using haS
        · simpa [spike, x, X] using haj.symm
  have hhighcard : high.card = J.card := by
    rw [← himage, Finset.card_image_of_injective J hinj]
  have hcardparts : low.card + high.card = s.card := by
    rw [← Finset.card_union_of_disjoint hdis, hparts]
  have hcardJ : J.card + low.card ≤ r + 1 := by
    simp only [r]
    omega
  have hcoeff :=
    selected_coeff_bound (show 2 ≤ r by simp [r]; omega) J hJsub hcardJ
  have hlowsum : ∑ a ∈ low, a ≤ low.card * (x + X) := by
    apply finset_sum_le_card_mul
    intro a ha
    exact Nat.le_of_lt (Finset.mem_filter.1 ha).2
  have hhighsum : ∑ a ∈ high, a = J.card * x + (∑ j ∈ J, j) * X := by
    rw [← himage, Finset.sum_image]
    · simp only [spike, Finset.sum_add_distrib, Finset.sum_const_nat,
        Finset.sum_mul]
    · intro i hi j hj hij
      exact hinj hij
  have hsums : (∑ a ∈ low, a) + ∑ a ∈ high, a = b := by
    rw [← Finset.sum_union hdis, hparts, hssum]
  have htotalcard : J.card + low.card ≤ h := by omega
  simp only [r] at hcoeff
  have hcalc : (∑ a ∈ low, a) +
      (J.card * x + (∑ j ∈ J, j) * X) ≤
      h * x + (h - 1) ^ 2 * X := by
    nlinarith
  rw [← hsums, hhighsum]
  simpa [x, X] using hcalc

/-- The left endpoint of the empty interval forced in block `n`. -/
def gapCap (h n : ℕ) : ℕ :=
  h * scale h n + (h - 1) ^ 2 * scale h n ^ 2

lemma gapCap_add_square {h n : ℕ} :
    gapCap h n + scale h n ^ 2 = scale h (n + 1) := by
  rw [scale]
  simp only [gapCap, coeff]
  ring

/-- The negative half: for every order at least three the restricted gaps
of the explicit basis are unbounded. -/
theorem counterexample_unbounded_restricted_gaps {h : ℕ} (hh : 3 ≤ h) :
    ¬HasBoundedGaps (restrictedSums (counterexample h) h) := by
  classical
  rintro ⟨C, hC⟩
  let B := restrictedSums (counterexample h) h
  have hB : B.Infinite := restrictedSums_infinite (counterexample_infinite hh) (by omega)
  have hp : (Set.ofPred fun m ↦ m ∈ B).Infinite := by simpa using hB
  have hzero : 0 ∈ B := by
    refine ⟨∅, by simp, by simp, by simp⟩
  let n := C
  let t := scale h (n + 1)
  have htA : t ∈ counterexample h := by
    simpa [t] using scale_mem_counterexample (show 1 ≤ h by omega) (n + 1)
  have htB : t ∈ B := singleton_mem_restrictedSums (show 1 ≤ h by omega) htA
  let q := Nat.count (fun m ↦ m ∈ B) t
  have htpos : 0 < t := by
    simp only [t]
    exact scale_pos (show 1 ≤ h by omega) (n + 1)
  have hqpos : 0 < q := by
    apply Nat.pos_of_ne_zero
    exact Nat.count_ne_iff_exists.2 ⟨0, htpos, hzero⟩
  let i := q - 1
  have hiq : i + 1 = q := by dsimp [i]; omega
  have hiq_lt : i < q := by omega
  have htEnum : enum B q = t := by
    simpa [enum, q] using (Nat.nth_count htB)
  have hprevB : enum B i ∈ B := by
    simpa [enum] using Nat.nth_mem_of_infinite hp i
  have hprevlt : enum B i < t := by
    rw [← htEnum]
    simpa [enum] using (Nat.nth_strictMono hp hiq_lt)
  have hprevle : enum B i ≤ gapCap h n := by
    exact restricted_prefix_bound hh hprevB (by simpa [t] using hprevlt)
  have hgap : scale h n ^ 2 ≤ enum B (i + 1) - enum B i := by
    rw [hiq, htEnum]
    have hadd := gapCap_add_square (h := h) (n := n)
    simp only [t] at hadd ⊢
    omega
  have hscaleC : C < scale h n := by
    have hs := scale_add_le (show 2 ≤ h by omega) n
    dsimp [n] at hs ⊢
    omega
  have hsquareC : C < scale h n ^ 2 := by
    have hx := scale_pos (show 1 ≤ h by omega) n
    nlinarith
  exact (not_lt_of_ge (hC i)) (hsquareC.trans_le hgap)

/-- Complete formal resolution of Erdős Problem 880. -/
theorem not_erdos_880 :
    (∀ A : Set ℕ, IsAdditiveBasisOfOrder A 2 →
      HasBoundedGaps (restrictedSums A 2)) ∧
    (∀ h : ℕ, 3 ≤ h → ∃ A : Set ℕ,
      IsAdditiveBasisOfOrder A h ∧ ¬HasBoundedGaps (restrictedSums A h)) := by
  constructor
  · intro A hA
    exact order_two_bounded_gaps hA
  · intro h hh
    exact ⟨counterexample h, counterexample_exact_order hh,
      counterexample_unbounded_restricted_gaps hh⟩

#print axioms not_erdos_880

end Erdos880

alias _root_.Erdos880.erdos_880 := _root_.Erdos880.not_erdos_880
