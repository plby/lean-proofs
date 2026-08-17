/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.ModularDecomposition

/-!
# The Deshouillers--Freiman rough packing argument

This file formalizes the finite packing step in section 6 of
Deshouillers--Freiman (1995).  The structural theorem supplies a long
`q`-progression in one restricted layer of an exceptional set and puts the
remaining elements in a short `q`-progression.  Two complementary subsets of
the first `S` regular elements then have different cardinalities but sums
which differ by fewer than the number of terms of the long progression.  The
translated progressions consequently meet, contradicting admissibility.

All estimates in this file are finite.  The separate structure module applies
the packing criterion after discharging its explicit numerical hypotheses.
-/

open scoped BigOperators

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## A discrete crossing lemma -/

/-- If an integer-valued sequence starts below `L`, ends nonnegative, and
each of its positive jumps is smaller than `L`, one of its values has absolute
value smaller than `L`.  This is the exact intermediate-value argument used
for the complementary subset sums. -/
theorem exists_natAbs_lt_of_monotone_crossing
    {U L : ℕ} {z : ℕ → ℤ}
    (_hL : 0 < L) (hstart : z 0 < L) (hend : 0 ≤ z U)
    (hjump : ∀ j < U, z (j + 1) - z j < L) :
    ∃ j ≤ U, (z j).natAbs < L := by
  by_cases hz0 : 0 ≤ z 0
  · refine ⟨0, Nat.zero_le _, ?_⟩
    have hcast : (((z 0).natAbs : ℕ) : ℤ) < (L : ℤ) := by
      simpa [Int.natCast_natAbs, abs_of_nonneg hz0] using hstart
    exact_mod_cast hcast
  · let J : Finset ℕ := (Finset.range (U + 1)).filter fun j ↦ 0 ≤ z j
    have hUJ : U ∈ J := by
      simp [J, hend]
    let j := J.min' ⟨U, hUJ⟩
    have hjJ : j ∈ J := Finset.min'_mem J ⟨U, hUJ⟩
    have hjU : j ≤ U := by
      have := (Finset.mem_filter.mp hjJ).1
      simp only [Finset.mem_range] at this
      omega
    have hjpos : 0 < j := by
      by_contra h
      have hj0 : j = 0 := by omega
      have hjnonneg0 : 0 ≤ z 0 := by
        rw [← hj0]
        exact (Finset.mem_filter.mp hjJ).2
      exact hz0 hjnonneg0
    have hjprev : z (j - 1) < 0 := by
      by_contra h
      have hprevJ : j - 1 ∈ J := by
        simp only [J, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, le_of_not_gt h⟩
      have hmin := Finset.min'_le J (j - 1) hprevJ
      omega
    have hjnonneg : 0 ≤ z j := (Finset.mem_filter.mp hjJ).2
    refine ⟨j, hjU, ?_⟩
    have hstep := hjump (j - 1) (by omega)
    have hjform : j - 1 + 1 = j := by omega
    rw [hjform] at hstep
    have : z j < (L : ℤ) := by linarith
    have hcast : (((z j).natAbs : ℕ) : ℤ) < (L : ℤ) := by
      simpa [Int.natCast_natAbs, abs_of_nonneg hjnonneg] using this
    exact_mod_cast hcast

/-! ## Index sums for the complementary chain -/

/-- Sum of `len` consecutive terms of an integer sequence. -/
def chainIndexSum (b : ℕ → ℤ) (start len : ℕ) : ℤ :=
  ∑ i ∈ Finset.range len, b (start + i)

lemma chainIndexSum_succ_right (b : ℕ → ℤ) (start len : ℕ) :
    chainIndexSum b start (len + 1) =
      chainIndexSum b start len + b (start + len) := by
  simp [chainIndexSum, Finset.sum_range_succ]

lemma chainIndexSum_succ_left (b : ℕ → ℤ) (start len : ℕ) :
    chainIndexSum b start (len + 1) =
      b start + chainIndexSum b (start + 1) len := by
  rw [chainIndexSum, chainIndexSum, Finset.sum_range_succ']
  simp only [Nat.add_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  omega

/-- Moving a fixed-length window right exchanges its endpoints. -/
lemma chainIndexSum_shift (b : ℕ → ℤ) (start len : ℕ) :
    chainIndexSum b start len + b (start + len) =
      b start + chainIndexSum b (start + 1) len := by
  rw [← chainIndexSum_succ_right, chainIndexSum_succ_left]

lemma chainIndexSum_add (b : ℕ → ℤ) (start m n : ℕ) :
    chainIndexSum b start (m + n) =
      chainIndexSum b start m + chainIndexSum b (start + m) n := by
  simp only [chainIndexSum, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  omega

/-- Selected-minus-complementary index sum at stage `j`. -/
def chainValue (b : ℕ → ℤ) (S U j : ℕ) : ℤ :=
  chainIndexSum b 0 (U - j) + chainIndexSum b (S - j) j -
    chainIndexSum b (U - j) (S - U)

/-- Exact stage-to-stage identity. -/
lemma chainValue_succ_sub (b : ℕ → ℤ) {S U j : ℕ}
    (hj : j < U) (hUS : U ≤ S) :
    chainValue b S U (j + 1) - chainValue b S U j =
      2 * (b (S - j - 1) - b (U - j - 1)) := by
  have hUsub : U - j = (U - (j + 1)) + 1 := by omega
  have hSsub : S - j = (S - (j + 1)) + 1 := by omega
  have hidx : U - (j + 1) + (S - U) = S - (j + 1) := by omega
  have hpre := chainIndexSum_succ_right b 0 (U - (j + 1))
  have hsuf := chainIndexSum_succ_left b (S - (j + 1)) j
  have hmid := chainIndexSum_shift b (U - (j + 1)) (S - U)
  simp only [chainValue]
  rw [hUsub, hSsub, hpre, hsuf]
  rw [hidx] at hmid
  have hpred : U - (j + 1) = U - j - 1 := by omega
  have hsidx : S - (j + 1) = S - j - 1 := by omega
  rw [hpred, hsidx] at hmid ⊢
  have hbackU : U - j - 1 + 1 - 1 = U - j - 1 := by omega
  have hbackS : S - j - 1 + 1 - 1 = S - j - 1 := by omega
  rw [hbackU, hbackS]
  simp only [zero_add] at hpre ⊢
  linarith

/-- The terminal selected block has larger sum than its shorter
complement when all entries are positive and increasing. -/
lemma chainValue_terminal_pos (b : ℕ → ℤ) {S U : ℕ}
    (_hU : U ≤ S) (hUS : U < S) (hS2U : S < 2 * U)
    (hpos : ∀ i < S, 0 < b i)
    (hstrict : ∀ i < S, ∀ k < S, i < k → b i < b k) :
    0 < chainValue b S U U := by
  let V := S - U
  have hSV : S = U + V := by dsimp [V]; omega
  have hVU : V < U := by dsimp [V]; omega
  have hsplit := chainIndexSum_add b V V (U - V)
  have hlen : V + (U - V) = U := by omega
  rw [hlen] at hsplit
  have hpair : chainIndexSum b 0 V ≤ chainIndexSum b V V := by
    unfold chainIndexSum
    apply Finset.sum_le_sum
    intro i hi
    have hiV : i < V := Finset.mem_range.mp hi
    have hiS : i < S := by omega
    have hViS : V + i < S := by omega
    simpa using (hstrict i hiS (V + i) hViS (by omega)).le
  have htail : 0 < chainIndexSum b (V + V) (U - V) := by
    unfold chainIndexSum
    apply Finset.sum_pos
    · intro i hi
      have hiUV : i < U - V := Finset.mem_range.mp hi
      apply hpos
      omega
    · refine ⟨0, Finset.mem_range.mpr ?_⟩
      omega
  have hform :
      chainValue b S U U =
        chainIndexSum b V U - chainIndexSum b 0 V := by
    simp [chainValue, V, chainIndexSum]
  rw [hform, hsplit]
  linarith

/-- Coordinate version of the quotient-jump bounds. -/
lemma chain_coordinate_jump_bounds
    (c : ℕ → ℕ) {S U j M : ℕ} (hj : j < U) (hUS : U < S)
    (hc : ∀ i < S, c i < M) (hstrict : StrictMono c) :
    0 < 2 * ((c (S - j - 1) : ℤ) - c (U - j - 1)) ∧
      2 * ((c (S - j - 1) : ℤ) - c (U - j - 1)) < 2 * M := by
  have hiU : U - j - 1 < S := by omega
  have hiS : S - j - 1 < S := by omega
  have hcoordU := hc (U - j - 1) hiU
  have hcoordS := hc (S - j - 1) hiS
  have hidx : U - j - 1 < S - j - 1 := by omega
  have hcoordlt := hstrict hidx
  norm_num at *
  omega

/-- Localized coordinate jump bound; strictness is only needed below `S`. -/
lemma chain_coordinate_jump_bounds_on
    (c : ℕ → ℕ) {S U j M : ℕ} (hj : j < U) (hUS : U < S)
    (hc : ∀ i < S, c i < M)
    (hstrict : ∀ i < S, ∀ k < S, i < k → c i < c k) :
    0 < 2 * ((c (S - j - 1) : ℤ) - c (U - j - 1)) ∧
      2 * ((c (S - j - 1) : ℤ) - c (U - j - 1)) < 2 * M := by
  have hiU : U - j - 1 < S := by omega
  have hiS : S - j - 1 < S := by omega
  have hcoordU := hc (U - j - 1) hiU
  have hcoordS := hc (S - j - 1) hiS
  have hidx : U - j - 1 < S - j - 1 := by omega
  have hcoordlt := hstrict _ hiU _ hiS hidx
  norm_num at *
  omega

/-- Quotient jump after writing the ordered entries in progression
coordinates. -/
lemma chain_quotient_succ_sub
    (b : ℕ → ℤ) (c : ℕ → ℕ) {start : ℤ} {q S U j : ℕ}
    (hq : 0 < q) (hj : j < U) (hUS : U < S)
    (hcoord : ∀ i < S, b i = start + (c i : ℤ) * (q : ℤ))
    (z : ℕ → ℤ)
    (hsum : ∀ k ≤ U, chainValue b S U k = (q : ℤ) * z k) :
    z (j + 1) - z j =
      2 * ((c (S - j - 1) : ℤ) - c (U - j - 1)) := by
  have hiU : U - j - 1 < S := by omega
  have hiS : S - j - 1 < S := by omega
  have hrec := chainValue_succ_sub b hj hUS.le
  have hjU : j ≤ U := by omega
  have hjsU : j + 1 ≤ U := by omega
  have hmul :
      (q : ℤ) * (z (j + 1) - z j) =
        (q : ℤ) * (2 * ((c (S - j - 1) : ℤ) - c (U - j - 1))) := by
    calc
      (q : ℤ) * (z (j + 1) - z j) =
          (q : ℤ) * z (j + 1) - (q : ℤ) * z j := by ring
      _ = chainValue b S U (j + 1) - chainValue b S U j := by
        rw [hsum (j + 1) hjsU, hsum j hjU]
      _ = 2 * (b (S - j - 1) - b (U - j - 1)) := hrec
      _ = (q : ℤ) *
          (2 * ((c (S - j - 1) : ℤ) - c (U - j - 1))) := by
        rw [hcoord _ hiS, hcoord _ hiU]
        ring
  exact (mul_left_cancel₀
    (by exact_mod_cast (Nat.ne_of_gt hq) : (q : ℤ) ≠ 0)) hmul

/-! ## Consecutive blocks in the increasing enumeration -/

/-- The `len` consecutive members of `A` beginning at zero-based position
`start`. -/
def roughOrderedBlock (A : Finset ℤ) (start len : ℕ)
    (h : start + len ≤ A.card) : Finset ℤ :=
  Finset.univ.image fun j : Fin len ↦
    A.orderEmbOfFin rfl ⟨start + j, by omega⟩

@[simp]
lemma roughOrderedBlock_card (A : Finset ℤ) (start len : ℕ)
    (h : start + len ≤ A.card) :
    (roughOrderedBlock A start len h).card = len := by
  rw [roughOrderedBlock, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    exact Fin.ext (Nat.add_left_cancel
      (congrArg Fin.val ((A.orderEmbOfFin rfl).injective hij)))

lemma roughOrderedBlock_subset (A : Finset ℤ) (start len : ℕ)
    (h : start + len ≤ A.card) :
    roughOrderedBlock A start len h ⊆ A := by
  intro x hx
  simp only [roughOrderedBlock, Finset.mem_image, Finset.mem_univ,
    true_and] at hx
  obtain ⟨j, rfl⟩ := hx
  exact A.orderEmbOfFin_mem rfl _

lemma roughOrderedBlock_disjoint {A : Finset ℤ} {s₁ n₁ s₂ n₂ : ℕ}
    (h₁ : s₁ + n₁ ≤ A.card) (h₂ : s₂ + n₂ ≤ A.card)
    (hsep : s₁ + n₁ ≤ s₂) :
    Disjoint (roughOrderedBlock A s₁ n₁ h₁)
      (roughOrderedBlock A s₂ n₂ h₂) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [roughOrderedBlock, Finset.mem_image, Finset.mem_univ,
    true_and] at hx₁ hx₂
  obtain ⟨i, hi⟩ := hx₁
  obtain ⟨j, hj⟩ := hx₂
  have heq := (A.orderEmbOfFin rfl).injective (hi.trans hj.symm)
  have hind : s₁ + i.val = s₂ + j.val := congrArg Fin.val heq
  have hiend : s₁ + i.val < s₁ + n₁ := by omega
  have hjstart : s₂ ≤ s₂ + j.val := by omega
  omega

/-- Sum of a consecutive block, written on its index range. -/
lemma sum_roughOrderedBlock (A : Finset ℤ) (start len : ℕ)
    (h : start + len ≤ A.card) :
    ∑ x ∈ roughOrderedBlock A start len h, x =
      ∑ j : Fin len, A.orderEmbOfFin rfl ⟨start + j, by omega⟩ := by
  rw [roughOrderedBlock, Finset.sum_image]
  intro i hi j hj hij
  exact Fin.ext (Nat.add_left_cancel
    (congrArg Fin.val ((A.orderEmbOfFin rfl).injective hij)))

/-- Totalized increasing enumeration of a finset. -/
def roughEntry (B : Finset ℤ) (i : ℕ) : ℤ :=
  if hi : i < B.card then B.orderEmbOfFin rfl ⟨i, hi⟩ else 0

lemma roughEntry_eq_orderEmb (B : Finset ℤ) {i : ℕ} (hi : i < B.card) :
    roughEntry B i = B.orderEmbOfFin rfl ⟨i, hi⟩ := by
  simp [roughEntry, hi]

lemma roughEntry_strictMonoOn (B : Finset ℤ) {i j : ℕ}
    (hij : i < j) (hj : j < B.card) : roughEntry B i < roughEntry B j := by
  rw [roughEntry_eq_orderEmb B (hij.trans hj), roughEntry_eq_orderEmb B hj]
  exact (B.orderEmbOfFin rfl).strictMono hij

/-- Reindex an ordered-block sum by ordinary natural indices. -/
lemma sum_orderEmb_eq_chainIndexSum (B : Finset ℤ) (start len : ℕ)
    (h : start + len ≤ B.card) :
    (∑ j : Fin len, B.orderEmbOfFin rfl ⟨start + j, by omega⟩) =
      chainIndexSum (roughEntry B) start len := by
  rw [Finset.sum_fin_eq_sum_range, chainIndexSum]
  apply Finset.sum_congr rfl
  intro i hi
  have hil : i < len := Finset.mem_range.mp hi
  simp [roughEntry, hil, show start + i < B.card by omega]

lemma sum_roughOrderedBlock_eq_chainIndexSum (B : Finset ℤ)
    (start len : ℕ) (h : start + len ≤ B.card) :
    ∑ x ∈ roughOrderedBlock B start len h, x =
      chainIndexSum (roughEntry B) start len := by
  rw [sum_roughOrderedBlock B start len h,
    sum_orderEmb_eq_chainIndexSum B start len h]

/-- Progression coordinate of an ordered entry, totalized past the end. -/
def roughCoordinate {B : Finset ℤ} {start : ℤ} {q M : ℕ}
    (hB : ContainedInAP B start q M) (i : ℕ) : ℕ :=
  if hi : i < B.card then
    Classical.choose (hB.exists_coordinate (B.orderEmbOfFin_mem rfl ⟨i, hi⟩))
  else 0

lemma roughEntry_eq_coordinate
    {B : Finset ℤ} {start : ℤ} {q M i : ℕ}
    (hB : ContainedInAP B start q M) (hi : i < B.card) :
    roughEntry B i = start + (roughCoordinate hB i : ℤ) * (q : ℤ) := by
  rw [roughEntry, dif_pos hi, roughCoordinate, dif_pos hi]
  exact (Classical.choose_spec
    (hB.exists_coordinate (B.orderEmbOfFin_mem rfl ⟨i, hi⟩))).2

lemma roughCoordinate_lt
    {B : Finset ℤ} {start : ℤ} {q M i : ℕ}
    (hB : ContainedInAP B start q M) (hi : i < B.card) :
    roughCoordinate hB i < M := by
  rw [roughCoordinate, dif_pos hi]
  exact (Classical.choose_spec
    (hB.exists_coordinate (B.orderEmbOfFin_mem rfl ⟨i, hi⟩))).1

lemma roughCoordinate_strict
    {B : Finset ℤ} {start : ℤ} {q M i j : ℕ}
    (hB : ContainedInAP B start q M) (hi : i < B.card)
    (hj : j < B.card) (hij : i < j) :
    roughCoordinate hB i < roughCoordinate hB j := by
  have hent : B.orderEmbOfFin rfl ⟨i, hi⟩ < B.orderEmbOfFin rfl ⟨j, hj⟩ :=
    (B.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr hij)
  have hiEq := roughEntry_eq_coordinate hB hi
  have hjEq := roughEntry_eq_coordinate hB hj
  rw [roughEntry, dif_pos hi] at hiEq
  rw [roughEntry, dif_pos hj] at hjEq
  rw [hiEq, hjEq] at hent
  have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hB.step_pos
  have hcast : (roughCoordinate hB i : ℤ) < roughCoordinate hB j := by
    nlinarith
  exact_mod_cast hcast

/-- The coordinates of two ordered entries separated by `d` indices differ
by at least `d`.  This is the finite ``one empty coordinate per skipped
entry'' estimate behind the DF95 endpoint calculation. -/
lemma roughCoordinate_gap
    {B : Finset ℤ} {start : ℤ} {q M S i d : ℕ}
    (hB : ContainedInAP B start q M) (hS : S ≤ B.card)
    (hid : i + d < S) :
    d + roughCoordinate hB i ≤ roughCoordinate hB (i + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hprev : i + d < S := by omega
      have hcd := ih hprev
      have hstep := roughCoordinate_strict hB
        (show i + d < B.card by omega)
        (show i + (d + 1) < B.card by omega)
        (show i + d < i + (d + 1) by omega)
      omega

/-- Ordered entries in a common `q`-progression are separated by at least
`q` times their index separation. -/
lemma roughEntry_add_step_mul_le
    {B : Finset ℤ} {start : ℤ} {q M S i d : ℕ}
    (hB : ContainedInAP B start q M) (hS : S ≤ B.card)
    (hid : i + d < S) :
    roughEntry B i + (q : ℤ) * d ≤ roughEntry B (i + d) := by
  have hi : i < B.card := by omega
  have hj : i + d < B.card := by omega
  rw [roughEntry_eq_coordinate hB hi, roughEntry_eq_coordinate hB hj]
  have hc := roughCoordinate_gap hB hS hid
  have hcZ :
      (d : ℤ) + roughCoordinate hB i ≤ roughCoordinate hB (i + d) := by
    exact_mod_cast hc
  have hqZ : (0 : ℤ) ≤ q := by positivity
  have := mul_le_mul_of_nonneg_right hcZ hqZ
  nlinarith

/-- Pairing the first `V` entries with the block `U` indices later costs at
least `q * U * V` in their difference of sums. -/
lemma paired_chainIndexSum_sub_le
    {B : Finset ℤ} {start : ℤ} {q M S U V : ℕ}
    (hB : ContainedInAP B start q M) (hS : S ≤ B.card)
    (hSV : S = U + V) :
    chainIndexSum (roughEntry B) 0 V -
        chainIndexSum (roughEntry B) U V ≤
      -((q : ℤ) * U * V) := by
  unfold chainIndexSum
  simp only [zero_add]
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ i ∈ Finset.range V,
        (roughEntry B i - roughEntry B (U + i))) ≤
        ∑ _i ∈ Finset.range V, -((q : ℤ) * U) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiV : i < V := Finset.mem_range.mp hi
      have hgap := roughEntry_add_step_mul_le hB hS
        (i := i) (d := U) (by omega)
      rw [Nat.add_comm i U] at hgap
      linarith
    _ = -((q : ℤ) * U * V) := by simp; ring

/-- Twice the sum of the `q` descending index gaps immediately before `U`.
The factor two keeps the endpoint calculation integral. -/
lemma two_mul_sum_gap {U q : ℕ} (hqU : q ≤ U) :
    2 * (∑ r ∈ Finset.range q, ((U - 1 - r : ℕ) : ℤ)) =
      (q : ℤ) * (2 * (U : ℤ) - q - 1) := by
  by_cases hq0 : q = 0
  · subst q
    simp
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
  have hrewrite :
      (∑ r ∈ Finset.range q, ((U - 1 - r : ℕ) : ℤ)) =
        ∑ r ∈ Finset.range q, ((U : ℤ) - 1 - (r : ℤ)) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrq : r < q := Finset.mem_range.mp hr
    rw [Nat.cast_sub (by omega : r ≤ U - 1),
      Nat.cast_sub (by omega : 1 ≤ U)]
    norm_num
  rw [hrewrite, Finset.sum_sub_distrib]
  have hsumr := Finset.sum_range_id_mul_two q
  have hsumrZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hsumr
  push_cast at hsumrZ
  rw [Nat.cast_sub (by omega : 1 ≤ q)] at hsumrZ
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  norm_num at hsumrZ
  nlinarith

/-! ## Complementary blocks -/

/-- At stage `j`, the selected `U` indices consist of a prefix of length
`U-j` and a suffix of length `j` among the first `S` indices. -/
def roughSelected (B : Finset ℤ) (S U j : ℕ)
    (hS : S ≤ B.card) (hj : j ≤ U) (hU : U ≤ S) : Finset ℤ :=
  roughOrderedBlock B 0 (U - j) (by omega) ∪
    roughOrderedBlock B (S - j) j (by omega)

/-- The complementary middle block among the first `S` indices. -/
def roughComplement (B : Finset ℤ) (S U j : ℕ)
    (hS : S ≤ B.card) (hj : j ≤ U) (hU : U ≤ S) : Finset ℤ :=
  roughOrderedBlock B (U - j) (S - U) (by omega)

@[simp]
lemma roughSelected_card (B : Finset ℤ) (S U j : ℕ)
    (hS : S ≤ B.card) (hj : j ≤ U) (hU : U ≤ S) :
    (roughSelected B S U j hS hj hU).card = U := by
  rw [roughSelected, Finset.card_union_of_disjoint]
  · rw [roughOrderedBlock_card, roughOrderedBlock_card]
    omega
  · apply roughOrderedBlock_disjoint
    omega

@[simp]
lemma roughComplement_card (B : Finset ℤ) (S U j : ℕ)
    (hS : S ≤ B.card) (hj : j ≤ U) (hU : U ≤ S) :
    (roughComplement B S U j hS hj hU).card = S - U := by
  exact roughOrderedBlock_card _ _ _ _

lemma roughSelected_subset (B : Finset ℤ) (S U j : ℕ)
    (hS : S ≤ B.card) (hj : j ≤ U) (hU : U ≤ S) :
    roughSelected B S U j hS hj hU ⊆ B := by
  apply Finset.union_subset <;> apply roughOrderedBlock_subset

lemma roughComplement_subset (B : Finset ℤ) (S U j : ℕ)
    (hS : S ≤ B.card) (hj : j ≤ U) (hU : U ≤ S) :
    roughComplement B S U j hS hj hU ⊆ B :=
  roughOrderedBlock_subset _ _ _ _

/-! ## Congruence of the complementary sums -/

/-- A set contained in a `q`-progression has its sum congruent to its
cardinality times the initial term. -/
lemma ContainedInAP.dvd_sum_sub_card_mul_start
    {B X : Finset ℤ} {start : ℤ} {q M : ℕ}
    (hB : ContainedInAP B start q M) (hX : X ⊆ B) :
    (q : ℤ) ∣ (∑ x ∈ X, x) - (X.card : ℤ) * start := by
  have hterm : ∀ x ∈ X, (q : ℤ) ∣ x - start := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hB.exists_coordinate (hX hx)
    refine ⟨(i : ℤ), ?_⟩
    rw [hxi]
    ring
  have hsum : (q : ℤ) ∣ ∑ x ∈ X, (x - start) :=
    Finset.dvd_sum hterm
  have hid :
      ∑ x ∈ X, (x - start) =
        (∑ x ∈ X, x) - (X.card : ℤ) * start := by
    simp [Finset.sum_sub_distrib]
  rwa [hid] at hsum

/-- If two subsets of one `q`-progression have cardinalities differing by
`q`, the difference of their sums is divisible by `q`. -/
lemma ContainedInAP.dvd_sub_sum_of_card_eq_add_step
    {B X D : Finset ℤ} {start : ℤ} {q M : ℕ}
    (hB : ContainedInAP B start q M) (hX : X ⊆ B) (hD : D ⊆ B)
    (hcard : X.card = D.card + q) :
    (q : ℤ) ∣ (∑ x ∈ X, x) - ∑ x ∈ D, x := by
  have hXdiv := hB.dvd_sum_sub_card_mul_start hX
  have hDdiv := hB.dvd_sum_sub_card_mul_start hD
  have hsub := dvd_sub hXdiv hDdiv
  have hqstart : (q : ℤ) ∣ (q : ℤ) * start := dvd_mul_right _ _
  have hcardZ : (X.card : ℤ) = (D.card : ℤ) + (q : ℤ) := by
    exact_mod_cast hcard
  have heq :
      ((∑ x ∈ X, x) - (X.card : ℤ) * start -
          ((∑ x ∈ D, x) - (D.card : ℤ) * start)) + (q : ℤ) * start =
        (∑ x ∈ X, x) - ∑ x ∈ D, x := by
    rw [hcardZ]
    ring
  rw [← heq]
  exact dvd_add hsub hqstart

/-! ## The finite translated-layer contradiction -/

/-- **Deshouillers--Freiman complementary-chain packing.**

The families `X j` and `D j` are, respectively, the selected and
complementary subsets at stage `j`.  Their cardinalities differ by the
structural step `q`, and `z j` is the quotient of the difference of their
sums by `q`.  When the quotients cross zero in jumps shorter than the long
progression, a translated-layer collision contradicts admissibility. -/
theorem no_df95_complementary_chain
    {A C B : Finset ℤ} {t q L U : ℕ}
    (hA : IsAdmissible A) (hCA : C ⊆ A) (hB : B ⊆ A \ C)
    (ht : 0 < t) (hq : 0 < q) (hL : 0 < L)
    (hAP : ContainsAP (restrictedSumset t C) (q : ℤ) L)
    (X D : ℕ → Finset ℤ) (z : ℕ → ℤ)
    (hX : ∀ j ≤ U, X j ⊆ B) (hD : ∀ j ≤ U, D j ⊆ B)
    (hcardX : ∀ j ≤ U, (X j).card = U)
    (hcardD : ∀ j ≤ U, (D j).card + q = U)
    (hsum : ∀ j ≤ U,
      (∑ x ∈ X j, x) - ∑ x ∈ D j, x = (q : ℤ) * z j)
    (hstart : z 0 < L) (hend : 0 ≤ z U)
    (hjump : ∀ j < U, z (j + 1) - z j < L) : False := by
  obtain ⟨j, hjU, hjclose⟩ :=
    exists_natAbs_lt_of_monotone_crossing hL hstart hend hjump
  apply no_short_congruent_outside_subset_sums hA hCA ht hAP
    ((hX j hjU).trans hB) ((hD j hjU).trans hB)
  · rw [hcardX j hjU, ← hcardD j hjU]
    omega
  · exact hsum j hjU
  · exact hjclose

/-! ## Canonical chain interface -/

/-- Totalized form of `roughSelected`; values past `U` are irrelevant. -/
def roughSelectedAt (B : Finset ℤ) (S U : ℕ)
    (hS : S ≤ B.card) (hU : U ≤ S) (j : ℕ) : Finset ℤ :=
  if hj : j ≤ U then roughSelected B S U j hS hj hU else ∅

/-- Totalized form of `roughComplement`; values past `U` are irrelevant. -/
def roughComplementAt (B : Finset ℤ) (S U : ℕ)
    (hS : S ≤ B.card) (hU : U ≤ S) (j : ℕ) : Finset ℤ :=
  if hj : j ≤ U then roughComplement B S U j hS hj hU else ∅

@[simp]
lemma roughSelectedAt_eq (B : Finset ℤ) (S U : ℕ)
    (hS : S ≤ B.card) (hU : U ≤ S) {j : ℕ} (hj : j ≤ U) :
    roughSelectedAt B S U hS hU j = roughSelected B S U j hS hj hU := by
  simp [roughSelectedAt, hj]

@[simp]
lemma roughComplementAt_eq (B : Finset ℤ) (S U : ℕ)
    (hS : S ≤ B.card) (hU : U ≤ S) {j : ℕ} (hj : j ≤ U) :
    roughComplementAt B S U hS hU j = roughComplement B S U j hS hj hU := by
  simp [roughComplementAt, hj]

/-- Difference between the selected and complementary sums. -/
def roughDelta (B : Finset ℤ) (S U : ℕ)
    (hS : S ≤ B.card) (hU : U ≤ S) (j : ℕ) : ℤ :=
  (∑ x ∈ roughSelectedAt B S U hS hU j, x) -
    ∑ x ∈ roughComplementAt B S U hS hU j, x

/-- The integral quotient of `roughDelta` by the structural step. -/
def roughQuotient (B : Finset ℤ) (S U q : ℕ)
    (hS : S ≤ B.card) (hU : U ≤ S) (j : ℕ) : ℤ :=
  roughDelta B S U hS hU j / (q : ℤ)

/-- The finset definition of the complementary difference agrees with the
index-sum formula. -/
lemma roughDelta_eq_chainValue (B : Finset ℤ) (S U : ℕ)
    (hS : S ≤ B.card) (hU : U ≤ S) {j : ℕ} (hj : j ≤ U) :
    roughDelta B S U hS hU j = chainValue (roughEntry B) S U j := by
  have hp : 0 + (U - j) ≤ B.card := by omega
  have hs : S - j + j ≤ B.card := by omega
  have hm : U - j + (S - U) ≤ B.card := by omega
  rw [roughDelta, roughSelectedAt_eq _ _ _ _ _ hj,
    roughComplementAt_eq _ _ _ _ _ hj, roughSelected, roughComplement]
  rw [Finset.sum_union (roughOrderedBlock_disjoint _ _ (by omega))]
  change
    (∑ x ∈ roughOrderedBlock B 0 (U - j) hp, x) +
        (∑ x ∈ roughOrderedBlock B (S - j) j hs, x) -
      ∑ x ∈ roughOrderedBlock B (U - j) (S - U) hm, x = _
  rw [sum_roughOrderedBlock_eq_chainIndexSum,
    sum_roughOrderedBlock_eq_chainIndexSum,
    sum_roughOrderedBlock_eq_chainIndexSum]
  rfl

/-- The canonical selected and complementary blocks have the required
cardinality difference when `S + q = 2U`. -/
lemma roughSelectedAt_card_eq_add_step
    (B : Finset ℤ) (S U q : ℕ) (hS : S ≤ B.card) (hU : U ≤ S)
    (hSU : S + q = 2 * U) {j : ℕ} (hj : j ≤ U) :
    (roughSelectedAt B S U hS hU j).card =
      (roughComplementAt B S U hS hU j).card + q := by
  rw [roughSelectedAt_eq _ _ _ _ _ hj, roughComplementAt_eq _ _ _ _ _ hj,
    roughSelected_card, roughComplement_card]
  omega

/-- The quotient `roughQuotient` really represents the difference of sums.
This is where containment in one `q`-progression and the parity identity
`S+q=2U` enter. -/
lemma roughDelta_eq_step_mul_roughQuotient
    {B : Finset ℤ} {S U q M : ℕ} {start : ℤ}
    (hS : S ≤ B.card) (hU : U ≤ S) (_hq : 0 < q)
    (hSU : S + q = 2 * U) (hB : ContainedInAP B start q M)
    {j : ℕ} (hj : j ≤ U) :
    roughDelta B S U hS hU j =
      (q : ℤ) * roughQuotient B S U q hS hU j := by
  have hdiv : (q : ℤ) ∣ roughDelta B S U hS hU j := by
    apply hB.dvd_sub_sum_of_card_eq_add_step
    · rw [roughSelectedAt_eq _ _ _ _ _ hj]
      exact roughSelected_subset _ _ _ _ _ _ _
    · rw [roughComplementAt_eq _ _ _ _ _ hj]
      exact roughComplement_subset _ _ _ _ _ _ _
    · exact roughSelectedAt_card_eq_add_step B S U q hS hU hSU hj
  have hcancel := Int.ediv_mul_cancel hdiv
  dsimp [roughQuotient]
  rw [mul_comm]
  exact hcancel.symm

/-- Every canonical quotient jump is positive and smaller than twice the
number of terms in the short containing progression. -/
lemma roughQuotient_jump_bounds
    {B : Finset ℤ} {start : ℤ} {q M S U : ℕ}
    (hcontained : ContainedInAP B start q M)
    (hS : S ≤ B.card) (hU : U ≤ S) (hUS : U < S)
    (hq : 0 < q) (hSU : S + q = 2 * U) {j : ℕ} (hj : j < U) :
    0 < roughQuotient B S U q hS hU (j + 1) -
          roughQuotient B S U q hS hU j ∧
      roughQuotient B S U q hS hU (j + 1) -
          roughQuotient B S U q hS hU j < 2 * M := by
  let c : ℕ → ℕ := roughCoordinate hcontained
  have hcoord : ∀ i < S,
      roughEntry B i = start + (c i : ℤ) * (q : ℤ) := by
    intro i hi
    exact roughEntry_eq_coordinate hcontained (hi.trans_le hS)
  have hsum : ∀ k ≤ U,
      chainValue (roughEntry B) S U k =
        (q : ℤ) * roughQuotient B S U q hS hU k := by
    intro k hk
    rw [← roughDelta_eq_chainValue B S U hS hU hk]
    exact roughDelta_eq_step_mul_roughQuotient hS hU hq hSU hcontained hk
  have hrec := chain_quotient_succ_sub (roughEntry B) c hq hj hUS
    hcoord (roughQuotient B S U q hS hU) hsum
  have hbounds := chain_coordinate_jump_bounds_on c hj hUS
    (fun i hi ↦ roughCoordinate_lt hcontained (hi.trans_le hS))
    (fun i hi k hk hik ↦ roughCoordinate_strict hcontained
      (hi.trans_le hS) (hk.trans_le hS) hik)
  rw [hrec]
  exact hbounds

/-- Positivity of the terminal quotient for positive regular elements. -/
lemma roughQuotient_terminal_pos
    {B : Finset ℤ} {start : ℤ} {q M S U : ℕ}
    (hcontained : ContainedInAP B start q M)
    (hS : S ≤ B.card) (hU : U ≤ S) (hUS : U < S)
    (hq : 0 < q) (hSU : S + q = 2 * U)
    (hBpos : ∀ x ∈ B, 0 < x) :
    0 < roughQuotient B S U q hS hU U := by
  have hS2U : S < 2 * U := by omega
  have hchain : 0 < chainValue (roughEntry B) S U U := by
    apply chainValue_terminal_pos (_hU := hU) (hUS := hUS) (hS2U := hS2U)
    · intro i hi
      rw [roughEntry_eq_orderEmb B (hi.trans_le hS)]
      exact hBpos _ (B.orderEmbOfFin_mem rfl _)
    · intro i hi k hk hik
      exact roughEntry_strictMonoOn B hik (hk.trans_le hS)
  have hdelta : 0 < roughDelta B S U hS hU U := by
    rwa [roughDelta_eq_chainValue B S U hS hU (le_refl U)]
  have hfac := roughDelta_eq_step_mul_roughQuotient hS hU hq hSU
    hcontained (le_refl U)
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  nlinarith

/-! ## The initial endpoint estimate -/

/-- Every ordered entry of a subset of `[1,N]` is at most `N`. -/
lemma roughEntry_le_ambient
    {B : Finset ℤ} {N i : ℕ} (hBN : B ⊆ ambient N) (hi : i < B.card) :
    roughEntry B i ≤ (N : ℤ) := by
  rw [roughEntry_eq_orderEmb B hi]
  exact (mem_ambient.mp (hBN (B.orderEmbOfFin_mem rfl _))).2

/-- Upper bound for the `q` unpaired middle entries in the endpoint
comparison.  The descending gaps to the last of the first `S` entries form
the exact triangular sum recorded by `two_mul_sum_gap`. -/
lemma two_mul_leftover_chainIndexSum_le
    {B : Finset ℤ} {N : ℕ} {start : ℤ} {q M S U V : ℕ}
    (hBN : B ⊆ ambient N) (hB : ContainedInAP B start q M)
    (hS : S ≤ B.card) (hq : 0 < q)
    (hSV : S = U + V) (hUV : U = V + q) :
    2 * chainIndexSum (roughEntry B) V q ≤
      2 * (q : ℤ) * N - (q : ℤ) * q * (2 * (U : ℤ) - q - 1) := by
  have hqU : q ≤ U := by omega
  have hterm :
      ∀ r ∈ Finset.range q,
        roughEntry B (V + r) ≤
          (N : ℤ) - (q : ℤ) * (U - 1 - r : ℕ) := by
    intro r hr
    have hrq : r < q := Finset.mem_range.mp hr
    have hend : V + r + (U - 1 - r) = S - 1 := by omega
    have hgap := roughEntry_add_step_mul_le hB hS
      (i := V + r) (d := U - 1 - r) (by omega)
    rw [hend] at hgap
    have hlast := roughEntry_le_ambient hBN
      (show S - 1 < B.card by omega)
    linarith
  have hsum :
      chainIndexSum (roughEntry B) V q ≤
        ∑ r ∈ Finset.range q,
          ((N : ℤ) - (q : ℤ) * (U - 1 - r : ℕ)) := by
    unfold chainIndexSum
    apply Finset.sum_le_sum
    intro r hr
    exact hterm r hr
  have htri := two_mul_sum_gap (U := U) hqU
  have hformula :
      2 * (∑ r ∈ Finset.range q,
          ((N : ℤ) - (q : ℤ) * (U - 1 - r : ℕ))) =
        2 * (q : ℤ) * N -
          (q : ℤ) * q * (2 * (U : ℤ) - q - 1) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    nlinarith
  nlinarith

/-- Cleared-denominator form of the initial complementary-sum estimate:
`2 Δ₀ ≤ q (2N - 2U² + q² + q)`. -/
lemma two_mul_roughDelta_zero_le
    {B : Finset ℤ} {N : ℕ} {start : ℤ} {q M S U : ℕ}
    (hBN : B ⊆ ambient N) (hB : ContainedInAP B start q M)
    (hS : S ≤ B.card) (hU : U ≤ S) (hq : 0 < q)
    (hSU : S + q = 2 * U) :
    2 * roughDelta B S U hS hU 0 ≤
      (q : ℤ) *
        (2 * (N : ℤ) - 2 * (U : ℤ) ^ 2 + (q : ℤ) ^ 2 + q) := by
  let V := S - U
  have hSV : S = U + V := by dsimp [V]; omega
  have hUV : U = V + q := by dsimp [V]; omega
  have hpair := paired_chainIndexSum_sub_le hB hS hSV
  have hleft := two_mul_leftover_chainIndexSum_le hBN hB hS hq hSV hUV
  have hsplit := chainIndexSum_add (roughEntry B) 0 V q
  rw [← hUV] at hsplit
  have hform :
      roughDelta B S U hS hU 0 =
        (chainIndexSum (roughEntry B) 0 V -
          chainIndexSum (roughEntry B) U V) +
        chainIndexSum (roughEntry B) V q := by
    rw [roughDelta_eq_chainValue B S U hS hU (Nat.zero_le U)]
    simp only [chainValue, Nat.sub_zero]
    have hz : chainIndexSum (roughEntry B) S 0 = 0 := by
      simp [chainIndexSum]
    rw [hz, add_zero]
    change chainIndexSum (roughEntry B) 0 U -
        chainIndexSum (roughEntry B) U V = _
    rw [hsplit]
    simp only [zero_add]
    ring
  rw [hform]
  have hUVZ : (U : ℤ) = (V : ℤ) + q := by exact_mod_cast hUV
  rw [hUVZ] at hpair hleft ⊢
  nlinarith [hpair, hleft]

/-- The elementary square estimate in the published rough-bound proof.
If the first `S` regular elements span more than the ambient square permits,
then the initial complementary quotient is strictly negative. -/
lemma roughQuotient_zero_neg_of_four_mul_lt_sq
    {B : Finset ℤ} {N : ℕ} {start : ℤ} {q M S U : ℕ}
    (hBN : B ⊆ ambient N) (hB : ContainedInAP B start q M)
    (hS : S ≤ B.card) (hU : U ≤ S) (hUS : U < S) (hq : 0 < q)
    (hSU : S + q = 2 * U) (hSq : 4 * N < S ^ 2) :
    roughQuotient B S U q hS hU 0 < 0 := by
  have hbound := two_mul_roughDelta_zero_le hBN hB hS hU hq hSU
  have hfac := roughDelta_eq_step_mul_roughQuotient hS hU hq hSU hB
    (j := 0) (Nat.zero_le U)
  have hqU : q < U := by omega
  have hSqZ : (4 : ℤ) * N < (S : ℤ) ^ 2 := by exact_mod_cast hSq
  have hSUZ : (S : ℤ) + q = 2 * U := by exact_mod_cast hSU
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  have hgapNat : q + 1 ≤ U := by omega
  have hgapCast : (q : ℤ) + 1 ≤ U := by exact_mod_cast hgapNat
  have hgapZ : (0 : ℤ) ≤ (U : ℤ) - q - 1 := by linarith
  have hprod : (0 : ℤ) ≤ (q : ℤ) * ((U : ℤ) - q - 1) :=
    mul_nonneg hqZ.le hgapZ
  have hinside :
      2 * (N : ℤ) - 2 * (U : ℤ) ^ 2 + (q : ℤ) ^ 2 + q < 0 := by
    nlinarith
  rw [hfac] at hbound
  nlinarith

/-- Collision criterion specialized to the canonical complementary blocks.
The endpoint and jump estimates are explicit: in the published application
they follow from `S > 2 sqrt N`, positivity of the regular elements, and
`2 * shortLength < longLength`. -/
theorem no_df95_packing_window
    {A C B : Finset ℤ} {start : ℤ} {t q L M S U : ℕ}
    (hA : IsAdmissible A) (hCA : C ⊆ A) (hBsub : B ⊆ A \ C)
    (ht : 0 < t) (hq : 0 < q) (hL : 0 < L)
    (hAP : ContainsAP (restrictedSumset t C) (q : ℤ) L)
    (hcontained : ContainedInAP B start q M)
    (hS : S ≤ B.card) (hU : U ≤ S) (hSU : S + q = 2 * U)
    (hstart : roughQuotient B S U q hS hU 0 < L)
    (hend : 0 ≤ roughQuotient B S U q hS hU U)
    (hjump : ∀ j < U,
      roughQuotient B S U q hS hU (j + 1) -
        roughQuotient B S U q hS hU j < L) : False := by
  apply no_df95_complementary_chain hA hCA hBsub ht hq hL hAP
    (roughSelectedAt B S U hS hU) (roughComplementAt B S U hS hU)
    (roughQuotient B S U q hS hU)
  · intro j hj
    rw [roughSelectedAt_eq _ _ _ _ _ hj]
    exact roughSelected_subset _ _ _ _ _ _ _
  · intro j hj
    rw [roughComplementAt_eq _ _ _ _ _ hj]
    exact roughComplement_subset _ _ _ _ _ _ _
  · intro j hj
    rw [roughSelectedAt_eq _ _ _ _ _ hj]
    exact roughSelected_card _ _ _ _ _ _ _
  · intro j hj
    have hc := roughSelectedAt_card_eq_add_step B S U q hS hU hSU hj
    rw [roughSelectedAt_eq _ _ _ _ _ hj, roughSelected_card] at hc
    exact hc.symm
  · intro j hj
    exact roughDelta_eq_step_mul_roughQuotient hS hU hq hSU hcontained hj
  · exact hstart
  · exact hend
  · exact hjump

/-- Version of `no_df95_packing_window` in which the jump hypothesis is
discharged from the short-progression length. -/
theorem no_df95_packing_window_of_two_mul_short_lt_long
    {A C B : Finset ℤ} {start : ℤ} {t q L M S U : ℕ}
    (hA : IsAdmissible A) (hCA : C ⊆ A) (hBsub : B ⊆ A \ C)
    (ht : 0 < t) (hq : 0 < q) (hL : 0 < L)
    (hAP : ContainsAP (restrictedSumset t C) (q : ℤ) L)
    (hcontained : ContainedInAP B start q M)
    (hS : S ≤ B.card) (hU : U ≤ S) (hUS : U < S)
    (hSU : S + q = 2 * U) (hML : 2 * M ≤ L)
    (hstart : roughQuotient B S U q hS hU 0 < L)
    (hend : 0 ≤ roughQuotient B S U q hS hU U) : False := by
  apply no_df95_packing_window hA hCA hBsub ht hq hL hAP hcontained
    hS hU hSU hstart hend
  intro j hj
  have hbound := (roughQuotient_jump_bounds hcontained hS hU hUS hq hSU hj).2
  exact hbound.trans_le (by exact_mod_cast hML)

/-- Fully automatic terminal and jump estimates.  Only the initial endpoint
estimate remains, which is the elementary square calculation involving
`S > 2 sqrt N`. -/
theorem no_df95_packing_window_of_endpoint
    {A C B : Finset ℤ} {start : ℤ} {t q L M S U : ℕ}
    (hA : IsAdmissible A) (hCA : C ⊆ A) (hBsub : B ⊆ A \ C)
    (hBpos : ∀ x ∈ B, 0 < x)
    (ht : 0 < t) (hq : 0 < q) (hL : 0 < L)
    (hAP : ContainsAP (restrictedSumset t C) (q : ℤ) L)
    (hcontained : ContainedInAP B start q M)
    (hS : S ≤ B.card) (hU : U ≤ S) (hUS : U < S)
    (hSU : S + q = 2 * U) (hML : 2 * M ≤ L)
    (hstart : roughQuotient B S U q hS hU 0 < L) : False := by
  apply no_df95_packing_window_of_two_mul_short_lt_long hA hCA hBsub ht hq hL
    hAP hcontained hS hU hUS hSU hML hstart
  exact (roughQuotient_terminal_pos hcontained hS hU hUS hq hSU hBpos).le

/-- **Finite DF95 rough-upper packing criterion.**

This is the certificate-level form consumed by the structure theorem.  All
analytic notation has disappeared: one supplies an integer `S` of the same
parity as `q` whose square exceeds `4N`, and `U=(S+q)/2`.  If the regular
part still has at least `S` elements, the two translated restricted-sum
layers collide. -/
theorem no_df95_packing_window_of_square
    {A C B : Finset ℤ} {N : ℕ} {start : ℤ}
    {t q L M S U : ℕ}
    (hA : IsAdmissible A) (hCA : C ⊆ A) (hBsub : B ⊆ A \ C)
    (hBN : B ⊆ ambient N)
    (ht : 0 < t) (hq : 0 < q) (hL : 0 < L)
    (hAP : ContainsAP (restrictedSumset t C) (q : ℤ) L)
    (hcontained : ContainedInAP B start q M)
    (hS : S ≤ B.card) (hU : U ≤ S) (hUS : U < S)
    (hSU : S + q = 2 * U) (hML : 2 * M ≤ L)
    (hSq : 4 * N < S ^ 2) : False := by
  have hBpos : ∀ x ∈ B, 0 < x := by
    intro x hx
    exact lt_of_lt_of_le Int.zero_lt_one (mem_ambient.mp (hBN hx)).1
  apply no_df95_packing_window_of_endpoint hA hCA hBsub hBpos ht hq hL
    hAP hcontained hS hU hUS hSU hML
  have hneg := roughQuotient_zero_neg_of_four_mul_lt_sq
    hBN hcontained hS hU hUS hq hSU hSq
  have hLZ : (0 : ℤ) < L := by exact_mod_cast hL
  linarith

/-- Quantitative conclusion of the DF95 packing argument for the regular
part.  The `+3` is the complete finite cost of rounding `2 sqrt N` and
matching the parity of the structural difference. -/
theorem regular_card_le_two_sqrt_add_three
    {A C B : Finset ℤ} {N : ℕ} {start : ℤ} {t q L M : ℕ}
    (hA : IsAdmissible A) (hCA : C ⊆ A) (hBsub : B ⊆ A \ C)
    (hBN : B ⊆ ambient N)
    (ht : 0 < t) (hq : 0 < q) (hL : 0 < L)
    (hAP : ContainsAP (restrictedSumset t C) (q : ℤ) L)
    (hcontained : ContainedInAP B start q M) (hML : 2 * M ≤ L) :
    B.card ≤ 2 * Nat.sqrt N + 3 := by
  by_contra hcard
  let s := Nat.sqrt N
  let S := 2 * s + 2 + q % 2
  let U := (S + q) / 2
  have hmod : q % 2 < 2 := Nat.mod_lt _ (by omega)
  have hScard : S ≤ B.card := by
    dsimp [S, s]
    omega
  have hSpos : 2 ≤ S := by dsimp [S]; omega
  have heven : (S + q) % 2 = 0 := by
    dsimp [S]
    omega
  have hSU : S + q = 2 * U := by
    dsimp [U]
    omega
  have hroot : N < (s + 1) * (s + 1) := by
    simpa [s] using Nat.lt_succ_sqrt N
  have hbase : 2 * (s + 1) ≤ S := by dsimp [S]; omega
  have hsquare : (2 * (s + 1)) * (2 * (s + 1)) ≤ S * S :=
    Nat.mul_self_le_mul_self hbase
  have hSq : 4 * N < S ^ 2 := by
    rw [pow_two]
    calc
      4 * N < 4 * ((s + 1) * (s + 1)) :=
        (Nat.mul_lt_mul_left (by omega : 0 < 4)).2 hroot
      _ = (2 * (s + 1)) * (2 * (s + 1)) := by ring
      _ ≤ S * S := hsquare
  have hqS : q < S := by
    by_contra h
    have hSqZ : (4 : ℤ) * N < (S : ℤ) ^ 2 := by exact_mod_cast hSq
    have hqSle : (S : ℤ) ≤ q := by exact_mod_cast (le_of_not_gt h)
    have hfirst := (mem_ambient.mp
      (hBN (show roughEntry B 0 ∈ B by
        rw [roughEntry_eq_orderEmb B (by omega)]
        exact B.orderEmbOfFin_mem rfl _))).1
    have hlast := roughEntry_le_ambient hBN
      (show S - 1 < B.card by omega)
    have hgap := roughEntry_add_step_mul_le hcontained hScard
      (i := 0) (d := S - 1) (by omega)
    simp only [zero_add] at hgap
    have hS1Z : (1 : ℤ) ≤ S := by exact_mod_cast (show 1 ≤ S by omega)
    have hSm1 : (0 : ℤ) ≤ (S : ℤ) - 1 := by linarith
    have hmul : (S : ℤ) * ((S : ℤ) - 1) ≤
        (q : ℤ) * ((S : ℤ) - 1) :=
      mul_le_mul_of_nonneg_right hqSle hSm1
    have hcastSub : ((S - 1 : ℕ) : ℤ) = (S : ℤ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ S by omega)]
      norm_num
    rw [hcastSub] at hgap
    have hS2Z : (2 : ℤ) ≤ S := by exact_mod_cast hSpos
    nlinarith [sq_nonneg ((S : ℤ) - 2)]
  have hUS : U < S := by omega
  have hU : U ≤ S := hUS.le
  have hstart0 : roughQuotient B S U q hScard hU 0 < 0 :=
    roughQuotient_zero_neg_of_four_mul_lt_sq hBN hcontained hScard hU hUS
      hq hSU hSq
  have hstartL : roughQuotient B S U q hScard hU 0 < L := by
    have hLZ : (0 : ℤ) < L := by exact_mod_cast hL
    linarith
  have hBpos : ∀ x ∈ B, 0 < x := by
    intro x hx
    exact (mem_ambient.mp (hBN hx)).1
  exact no_df95_packing_window_of_endpoint hA hCA hBsub hBpos ht hq hL hAP
    hcontained hScard hU hUS hSU hML hstartL

end

end Erdos874
