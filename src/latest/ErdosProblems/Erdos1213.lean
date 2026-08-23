/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1213.
https://www.erdosproblems.com/forum/thread/1213

Informal authors:
- Norbert Hegyvári

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1213.md
-/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Erdős Problem 1213

Hegyvári proved that a strictly increasing finite sequence of positive integers
with bounded gaps cannot have all consecutive-interval sums distinct once its
last term is sufficiently large.  We prove the result with the explicit bound

`4^K * a + 2 * K * (4^K)^2`.

The proof is the sliding-window pigeonhole argument documented in
`tex/1213.tex`.
-/

namespace Erdos1213

/-- The sum of the entries of `A` on the half-open interval `[u, v)`. -/
def intervalSum (A : ℕ → ℕ) (u v : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico u v, A i

/-- Two distinct nonempty index intervals contained in `[0, s)` have equal sums. -/
def HasEqualIntervalSums (A : ℕ → ℕ) (s : ℕ) : Prop :=
  ∃ u v x y : ℕ,
    u < v ∧ v ≤ s ∧ x < y ∧ y ≤ s ∧ (u, v) ≠ (x, y) ∧
      intervalSum A u v = intervalSum A x y

/-- An explicit Hegyvári-type threshold. -/
def explicitBound (a K : ℕ) : ℕ :=
  4 ^ K * a + 2 * K * (4 ^ K) ^ 2

lemma self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp : 0 < 2 ^ n := by positivity
      rw [pow_succ]
      omega

/-- The explicit threshold has the advertised `a * exp(O(K))` shape. -/
lemma explicitBound_le (a K : ℕ) (ha : 1 ≤ a) :
    explicitBound a K ≤ 3 * a * 32 ^ K := by
  have hfour : 4 ^ K ≤ 32 ^ K := Nat.pow_le_pow_left (by omega) K
  have hfirst : 4 ^ K * a ≤ a * 32 ^ K := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right a hfour
  have hK : K ≤ a * 2 ^ K := by
    exact (self_le_two_pow K).trans <| by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right (2 ^ K) ha
  have hsecond0 : K * 16 ^ K ≤ a * 32 ^ K := by
    calc
      K * 16 ^ K ≤ (a * 2 ^ K) * 16 ^ K := Nat.mul_le_mul_right (16 ^ K) hK
      _ = a * (2 ^ K * 16 ^ K) := by ring
      _ = a * (2 * 16) ^ K := by rw [mul_pow]
      _ = a * 32 ^ K := by norm_num
  have hsecond : 2 * K * (4 ^ K) ^ 2 ≤ 2 * (a * 32 ^ K) := by
    have hsq : (4 ^ K) ^ 2 = 16 ^ K := by
      calc
        (4 ^ K) ^ 2 = 4 ^ (K * 2) := (pow_mul 4 K 2).symm
        _ = 4 ^ (2 * K) := by congr 1; omega
        _ = (4 ^ 2) ^ K := pow_mul 4 2 K
        _ = 16 ^ K := by norm_num
    rw [hsq, show 2 * K * 16 ^ K = 2 * (K * 16 ^ K) by ring]
    exact Nat.mul_le_mul_left 2 hsecond0
  unfold explicitBound
  calc
    4 ^ K * a + 2 * K * (4 ^ K) ^ 2 ≤ a * 32 ^ K + 2 * (a * 32 ^ K) :=
      Nat.add_le_add hfirst hsecond
    _ = 3 * a * 32 ^ K := by ring

lemma iterate_gap_bound {A : ℕ → ℕ} {K s i n : ℕ}
    (hgap : ∀ ⦃j : ℕ⦄, j + 1 < s → A (j + 1) ≤ A j + K)
    (hin : i + n < s) :
    A (i + n) ≤ A i + K * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprev : i + n < s := by omega
      calc
        A (i + (n + 1)) = A ((i + n) + 1) := by congr 1
        _ ≤ A (i + n) + K := hgap (by omega)
        _ ≤ (A i + K * n) + K := Nat.add_le_add_right (ih hprev) K
        _ = A i + K * (n + 1) := by simp [Nat.mul_succ, Nat.add_assoc]

lemma sum_range_le_mul (A : ℕ → ℕ) (C n : ℕ)
    (hA : ∀ i < n, A i ≤ C) :
    (∑ i ∈ Finset.range n, A i) ≤ n * C := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      exact (Nat.add_le_add (ih (fun i hi ↦ hA i (by omega))) (hA n (by omega))).trans_eq
        (by simp [Nat.succ_mul])

lemma intervalSum_zero_le_intervalSum_zero {A : ℕ → ℕ} {r M : ℕ} (hrM : r ≤ M) :
    intervalSum A 0 r ≤ intervalSum A 0 M := by
  have hsplit := Finset.sum_Ico_consecutive A (show 0 ≤ r by omega) hrM
  exact (Nat.le_add_right _ _).trans_eq hsplit

lemma last_le_final_intervalSum {A : ℕ → ℕ} {s r : ℕ}
    (hs : 0 < s) (hr : 0 < r) (hrs : r ≤ s) :
    A (s - 1) ≤ intervalSum A (s - r) s := by
  have hleft : s - r ≤ s - 1 := by omega
  have htop : s - 1 + 1 = s := by omega
  have hsum := Finset.sum_Ico_succ_top hleft A
  rw [htop] at hsum
  rw [intervalSum, hsum]
  exact Nat.le_add_left _ _

lemma intervalSum_slide (A : ℕ → ℕ) (i r : ℕ) :
    intervalSum A (i + 1) (i + 1 + r) + A i =
      intervalSum A i (i + r) + A (i + r) := by
  have h₁ := Finset.sum_Ico_consecutive A (show i ≤ i + 1 by omega)
    (show i + 1 ≤ i + r + 1 by omega)
  have h₂ := Finset.sum_Ico_consecutive A (show i ≤ i + r by omega)
    (show i + r ≤ i + r + 1 by omega)
  have hsingle : (∑ x ∈ Finset.Ico (i + r) (i + r + 1), A x) = A (i + r) := by
    rw [Finset.sum_Ico_succ_top (le_refl (i + r))]
    simp
  rw [hsingle] at h₂
  simpa [intervalSum, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₁.trans h₂.symm

lemma intervalSum_slide_le {A : ℕ → ℕ} {K s i r : ℕ}
    (hgap : ∀ ⦃j : ℕ⦄, j + 1 < s → A (j + 1) ≤ A j + K)
    (hir : i + r < s) :
    intervalSum A (i + 1) (i + 1 + r) ≤ intervalSum A i (i + r) + K * r := by
  have hAi := iterate_gap_bound hgap hir
  have hslide := intervalSum_slide A i r
  omega

lemma exists_window_in_bin {A : ℕ → ℕ} {K s X W r q : ℕ}
    (hK : 0 < K) (hr : 0 < r) (hrs : r ≤ s)
    (hfirst : intervalSum A 0 r ≤ X)
    (hlast : X + W < intervalSum A (s - r) s)
    (hgap : ∀ ⦃j : ℕ⦄, j + 1 < s → A (j + 1) ≤ A j + K)
    (hq : (q + 1) * (K * r) ≤ W) :
    ∃ i : ℕ, i + r ≤ s ∧
      X + q * (K * r) ≤ intervalSum A i (i + r) ∧
      intervalSum A i (i + r) < X + (q + 1) * (K * r) := by
  let T := X + q * (K * r)
  let p : ℕ → Prop := fun i ↦ i + r ≤ s ∧ T ≤ intervalSum A i (i + r)
  have hend : (s - r) + r = s := Nat.sub_add_cancel hrs
  have hp_exists : ∃ i, p i := by
    refine ⟨s - r, hend.le, ?_⟩
    rw [hend]
    have hTW : T ≤ X + W := by
      dsimp [T]
      have hqr : q * (K * r) ≤ (q + 1) * (K * r) :=
        Nat.mul_le_mul_right (K * r) (by omega)
      omega
    omega
  let i := Nat.find hp_exists
  have hi := Nat.find_spec hp_exists
  refine ⟨i, hi.1, hi.2, ?_⟩
  have hKr : 0 < K * r := Nat.mul_pos hK hr
  by_cases hi0 : i = 0
  · have htotal : 0 < (q + 1) * (K * r) := Nat.mul_pos (Nat.succ_pos q) hKr
    simpa [i, hi0] using hfirst.trans_lt (Nat.lt_add_of_pos_right htotal)
  · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
    have hpred_bound : (i - 1) + r ≤ s := by omega
    have hnot : ¬p (i - 1) := Nat.find_min hp_exists (by omega)
    have hprev : intervalSum A (i - 1) (i - 1 + r) < T := by
      dsimp [p] at hnot
      omega
    have hslide := intervalSum_slide_le (A := A) (K := K) (s := s)
      (i := i - 1) (r := r) hgap (by omega)
    have hslide' : intervalSum A i (i + r) ≤
        intervalSum A (i - 1) (i - 1 + r) + K * r := by
      simpa [Nat.sub_add_cancel hipos] using hslide
    dsimp [T] at hprev
    calc
      intervalSum A i (i + r) ≤
          intervalSum A (i - 1) (i - 1 + r) + K * r := hslide'
      _ < (X + q * (K * r)) + K * r := Nat.add_lt_add_right hprev _
      _ = X + (q + 1) * (K * r) := by simp [Nat.succ_mul, Nat.add_assoc]

lemma four_pow_eq_two_pow (K : ℕ) : 4 ^ K = 2 ^ (2 * K) := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]

lemma four_pow_sq_eq_two_pow (K : ℕ) : (4 ^ K) ^ 2 = 2 ^ (4 * K) := by
  rw [four_pow_eq_two_pow, ← pow_mul]
  congr 1
  omega

lemma twice_halfPower_eq_fourPow_sq (K : ℕ) (hK : 0 < K) :
    2 * 2 ^ (4 * K - 1) = (4 ^ K) ^ 2 := by
  rw [four_pow_sq_eq_two_pow]
  have he : 4 * K - 1 + 1 = 4 * K := by omega
  calc
    2 * 2 ^ (4 * K - 1) = 2 ^ (4 * K - 1) * 2 := by rw [Nat.mul_comm]
    _ = 2 ^ ((4 * K - 1) + 1) := by rw [pow_succ]
    _ = 2 ^ (4 * K) := by rw [he]

/-- Slots for the dyadic family of windows.  The left summand represents all
length-one bins.  In the right summand, the first coordinate selects a
dyadic length block and the second coordinate encodes a length/bin pair. -/
abbrev Slot (K : ℕ) :=
  Fin ((4 ^ K) ^ 2) ⊕ (Fin (2 * K) × Fin (2 ^ (4 * K - 1)))

def slotLength {K : ℕ} : Slot K → ℕ
  | Sum.inl _ => 1
  | Sum.inr z => 2 ^ z.1.val + 1 + z.2.val % (2 ^ z.1.val)

def slotBin {K : ℕ} : Slot K → ℕ
  | Sum.inl q => q.val
  | Sum.inr z => z.2.val / (2 ^ z.1.val)

lemma slot_spec {K : ℕ} (hK : 0 < K) (z : Slot K) :
    0 < slotLength z ∧ slotLength z ≤ 4 ^ K ∧
      (slotBin z + 1) * (K * slotLength z) ≤ K * (4 ^ K) ^ 2 := by
  rcases z with q | ⟨j, t⟩
  · simp only [slotLength, slotBin]
    have hq : q.val + 1 ≤ (4 ^ K) ^ 2 := by omega
    refine ⟨by omega, by simp [Nat.one_le_pow], ?_⟩
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_left K hq
  · let d := 2 ^ j.val
    let H := 2 ^ (4 * K - 1)
    have hd : 0 < d := by simp [d]
    have hmod : t.val % d < d := Nat.mod_lt _ hd
    have hlen_pos : 0 < d + 1 + t.val % d := by omega
    have hlen_le_two : d + 1 + t.val % d ≤ 2 * d := by omega
    have hj₂K : j.val + 1 ≤ 2 * K := by omega
    have hlen_le_M : d + 1 + t.val % d ≤ 4 ^ K := by
      calc
        d + 1 + t.val % d ≤ 2 * d := hlen_le_two
        _ = 2 ^ (j.val + 1) := by simp [d, pow_succ, Nat.mul_comm]
        _ ≤ 2 ^ (2 * K) := Nat.pow_le_pow_right (by omega) hj₂K
        _ = 4 ^ K := (four_pow_eq_two_pow K).symm
    have hjH : j.val ≤ 4 * K - 1 := by omega
    have hdvdH : d ∣ H := by
      dsimp [d, H]
      exact pow_dvd_pow 2 hjH
    have hq_lt : t.val / d < H / d := by
      apply Nat.lt_of_not_ge
      intro hbad
      have hmul := Nat.mul_le_mul_right d hbad
      have hlow : H ≤ t.val := by
        calc
          H = H / d * d := (Nat.div_mul_cancel hdvdH).symm
          _ ≤ t.val / d * d := hmul
          _ ≤ t.val := Nat.div_mul_le_self _ _
      exact (Nat.not_lt_of_ge hlow) t.isLt
    have hq_succ : t.val / d + 1 ≤ H / d := by omega
    have hpair : (t.val / d + 1) * (d + 1 + t.val % d) ≤ (4 ^ K) ^ 2 := by
      calc
        (t.val / d + 1) * (d + 1 + t.val % d) ≤ (H / d) * (2 * d) :=
          Nat.mul_le_mul hq_succ hlen_le_two
        _ = 2 * H := by
          rw [show (H / d) * (2 * d) = 2 * ((H / d) * d) by ring,
            Nat.div_mul_cancel hdvdH]
        _ = (4 ^ K) ^ 2 := twice_halfPower_eq_fourPow_sq K hK
    refine ⟨hlen_pos, hlen_le_M, ?_⟩
    change (t.val / d + 1) * (K * (d + 1 + t.val % d)) ≤ K * (4 ^ K) ^ 2
    rw [show (t.val / d + 1) * (K * (d + 1 + t.val % d)) =
      K * ((t.val / d + 1) * (d + 1 + t.val % d)) by ring]
    exact Nat.mul_le_mul_left K hpair

lemma card_slot {K : ℕ} (hK : 0 < K) :
    Fintype.card (Slot K) = (K + 1) * (4 ^ K) ^ 2 := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  have hhalf := twice_halfPower_eq_fourPow_sq K hK
  calc
    (4 ^ K) ^ 2 + 2 * K * 2 ^ (4 * K - 1) =
        (4 ^ K) ^ 2 + K * (2 * 2 ^ (4 * K - 1)) := by ring
    _ = (4 ^ K) ^ 2 + K * (4 ^ K) ^ 2 := by rw [hhalf]
    _ = (K + 1) * (4 ^ K) ^ 2 := by ring

lemma slot_length_bin_injective {K : ℕ} (_hK : 0 < K) :
    Function.Injective (fun z : Slot K ↦ (slotLength z, slotBin z)) := by
  intro z z' h
  rcases z with q | ⟨j, t⟩ <;> rcases z' with q' | ⟨j', t'⟩
  · simp only [slotLength, slotBin, Prod.mk.injEq] at h
    exact congrArg Sum.inl (Fin.ext h.2)
  · simp only [slotLength, slotBin, Prod.mk.injEq] at h
    have hd : 0 < 2 ^ j'.val := by positivity
    have hm := Nat.mod_lt t'.val hd
    omega
  · simp only [slotLength, slotBin, Prod.mk.injEq] at h
    have hd : 0 < 2 ^ j.val := by positivity
    have hm := Nat.mod_lt t.val hd
    omega
  · simp only [slotLength, slotBin, Prod.mk.injEq] at h
    have hd : 0 < 2 ^ j.val := by positivity
    have hd' : 0 < 2 ^ j'.val := by positivity
    have hm := Nat.mod_lt t.val hd
    have hm' := Nat.mod_lt t'.val hd'
    have hjval : j.val = j'.val := by
      rcases lt_trichotomy j.val j'.val with hj | hj | hj
      · have hp : 2 ^ (j.val + 1) ≤ 2 ^ j'.val :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hleft : 2 ^ j.val + 1 + t.val % 2 ^ j.val ≤ 2 ^ (j.val + 1) := by
          rw [pow_succ]
          omega
        omega
      · exact hj
      · have hp : 2 ^ (j'.val + 1) ≤ 2 ^ j.val :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hright : 2 ^ j'.val + 1 + t'.val % 2 ^ j'.val ≤ 2 ^ (j'.val + 1) := by
          rw [pow_succ]
          omega
        omega
    have hj : j = j' := Fin.ext hjval
    subst j'
    have hmod : t.val % 2 ^ j.val = t'.val % 2 ^ j.val := by omega
    have hdiv : t.val / 2 ^ j.val = t'.val / 2 ^ j.val := h.2
    have htval : t.val = t'.val := by
      calc
        t.val = t.val % 2 ^ j.val + 2 ^ j.val * (t.val / 2 ^ j.val) :=
          (Nat.mod_add_div _ _).symm
        _ = t'.val % 2 ^ j.val + 2 ^ j.val * (t'.val / 2 ^ j.val) := by
          rw [hmod, hdiv]
        _ = t'.val := Nat.mod_add_div _ _
    have ht : t = t' := Fin.ext htval
    subst t'
    rfl

/-- The exact affirmative assertion in Erdős Problem 1213, in zero-based notation. -/
def erdos_1213 : Prop :=
  ∀ a K : ℕ, 1 ≤ a → 1 ≤ K → ∃ f : ℕ, ∀ (s : ℕ) (A : ℕ → ℕ),
    0 < s →
    A 0 = a →
    (∀ ⦃i j : ℕ⦄, i < j → j < s → A i < A j) →
    (∀ ⦃i : ℕ⦄, i + 1 < s → A (i + 1) - A i ≤ K) →
    f < A (s - 1) →
    HasEqualIntervalSums A s

/-- The explicit form of Hegyvári's resolution: the concrete threshold
`explicitBound a K` forces two distinct intervals with equal sums. -/
theorem equal_interval_sums_of_last_gt_explicitBound
    (a K : ℕ) (_ha : 1 ≤ a) (hK : 1 ≤ K) (s : ℕ) (A : ℕ → ℕ)
    (hs : 0 < s)
    (hA0 : A 0 = a)
    (_hmono : ∀ ⦃i j : ℕ⦄, i < j → j < s → A i < A j)
    (hgap_sub : ∀ ⦃i : ℕ⦄, i + 1 < s → A (i + 1) - A i ≤ K)
    (hlast : explicitBound a K < A (s - 1)) :
    HasEqualIntervalSums A s := by
  have hgap : ∀ ⦃i : ℕ⦄, i + 1 < s → A (i + 1) ≤ A i + K := by
    intro i hi
    exact Nat.le_add_of_sub_le (hgap_sub hi) |>.trans_eq (Nat.add_comm _ _)
  let M := 4 ^ K
  let X := intervalSum A 0 M
  let W := K * M ^ 2
  have hKpos : 0 < K := by omega
  have hMpos : 0 < M := by simp [M]
  have hMone : 1 ≤ M := hMpos
  have hMs : M < s := by
    by_contra hnot
    have hsM : s ≤ M := by omega
    have hend := iterate_gap_bound (A := A) (K := K) (s := s)
      (i := 0) (n := s - 1) hgap (by omega)
    have haM : a ≤ M * a := by
      calc
        a = 1 * a := by simp
        _ ≤ M * a := Nat.mul_le_mul_right a hMone
    have hs₁M : s - 1 ≤ M := by omega
    have hMM : M ≤ M * M := by
      calc
        M = M * 1 := by simp
        _ ≤ M * M := Nat.mul_le_mul_left M hMone
    have hMtwo : M ≤ 2 * M ^ 2 := by
      calc
        M ≤ M * M := hMM
        _ ≤ 2 * M ^ 2 := by rw [pow_two]; omega
    have hgapPart : K * (s - 1) ≤ 2 * K * M ^ 2 := by
      calc
        K * (s - 1) ≤ K * M := Nat.mul_le_mul_left K hs₁M
        _ ≤ K * (2 * M ^ 2) := Nat.mul_le_mul_left K hMtwo
        _ = 2 * K * M ^ 2 := by ring
    have hsmall : a + K * (s - 1) ≤ explicitBound a K := by
      have hadd := Nat.add_le_add haM hgapPart
      simpa [explicitBound, M] using hadd
    have : A (s - 1) ≤ explicitBound a K := by
      rw [hA0] at hend
      simpa using hend.trans hsmall
    omega
  have hX : X ≤ M * (a + K * M) := by
    have hterm : ∀ i < M, A i ≤ a + K * M := by
      intro i hi
      have hiS : i < s := hi.trans hMs
      have hiA := iterate_gap_bound (A := A) (K := K) (s := s)
        (i := 0) (n := i) hgap (by simpa using hiS)
      have hKi : K * i ≤ K * M := Nat.mul_le_mul_left K (Nat.le_of_lt hi)
      rw [hA0] at hiA
      simpa using hiA.trans (Nat.add_le_add_left hKi a)
    have hsum := sum_range_le_mul A (a + K * M) M hterm
    simpa [X, intervalSum, Finset.sum_Ico_eq_sum_range] using hsum
  have hXW : X + W ≤ explicitBound a K := by
    calc
      X + W ≤ M * (a + K * M) + K * M ^ 2 := Nat.add_le_add_right hX W
      _ = explicitBound a K := by simp [explicitBound, M]; ring
  have hlastXW : X + W < A (s - 1) := hXW.trans_lt hlast
  have hcross : ∀ z : Slot K, ∃ i : ℕ, i + slotLength z ≤ s ∧
      X + slotBin z * (K * slotLength z) ≤
        intervalSum A i (i + slotLength z) ∧
      intervalSum A i (i + slotLength z) <
        X + (slotBin z + 1) * (K * slotLength z) := by
    intro z
    rcases slot_spec hKpos z with ⟨hlenpos, hlenM, hbinW⟩
    have hlens : slotLength z ≤ s := hlenM.trans hMs.le
    have hfirst : intervalSum A 0 (slotLength z) ≤ X := by
      exact intervalSum_zero_le_intervalSum_zero hlenM
    have hlastWindow : X + W <
        intervalSum A (s - slotLength z) s := by
      exact hlastXW.trans_le (last_le_final_intervalSum hs hlenpos hlens)
    exact exists_window_in_bin hKpos hlenpos hlens hfirst hlastWindow hgap hbinW
  let start : Slot K → ℕ := fun z ↦ Classical.choose (hcross z)
  have hstart : ∀ z : Slot K, start z + slotLength z ≤ s ∧
      X + slotBin z * (K * slotLength z) ≤
        intervalSum A (start z) (start z + slotLength z) ∧
      intervalSum A (start z) (start z + slotLength z) <
        X + (slotBin z + 1) * (K * slotLength z) := by
    intro z
    exact Classical.choose_spec (hcross z)
  let raw : Slot K → ℕ := fun z ↦
    intervalSum A (start z) (start z + slotLength z)
  have hraw : ∀ z : Slot K, X ≤ raw z ∧ raw z < X + W := by
    intro z
    rcases hstart z with ⟨_, hlower, hupper⟩
    have hbinW := (slot_spec hKpos z).2.2
    constructor
    · exact (Nat.le_add_right X _).trans hlower
    · exact hupper.trans_le (Nat.add_le_add_left hbinW X)
  let value : Slot K → Fin W := fun z ↦
    ⟨raw z - X, by have hz := hraw z; omega⟩
  have hcard : Fintype.card (Fin W) < Fintype.card (Slot K) := by
    rw [Fintype.card_fin, card_slot hKpos]
    have hM_sq_pos : 0 < M ^ 2 := pow_pos hMpos 2
    simpa [W, M] using Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self K) hM_sq_pos
  obtain ⟨z, z', hzz', hvalue⟩ := Fintype.exists_ne_map_eq_of_card_lt value hcard
  have hrawEq : raw z = raw z' := by
    have hv := congrArg Fin.val hvalue
    dsimp [value] at hv
    rcases hraw z with ⟨hzlow, _⟩
    rcases hraw z' with ⟨hz'low, _⟩
    omega
  have hpair : (start z, start z + slotLength z) ≠
      (start z', start z' + slotLength z') := by
    intro hp
    have hstartEq : start z = start z' := congrArg Prod.fst hp
    have hendEq : start z + slotLength z = start z' + slotLength z' :=
      congrArg Prod.snd hp
    have hlenEq : slotLength z = slotLength z' := by omega
    have hquot : ∀ w : Slot K,
        (raw w - X) / (K * slotLength w) = slotBin w := by
      intro w
      rcases hstart w with ⟨_, hlower, hupper⟩
      apply Nat.div_eq_of_lt_le
      · have hXraw := (hraw w).1
        dsimp [raw] at hXraw ⊢
        omega
      · have hXraw := (hraw w).1
        dsimp [raw] at hXraw ⊢
        omega
    have hbinEq : slotBin z = slotBin z' := by
      calc
        slotBin z = (raw z - X) / (K * slotLength z) := (hquot z).symm
        _ = (raw z' - X) / (K * slotLength z') := by rw [hrawEq, hlenEq]
        _ = slotBin z' := hquot z'
    exact hzz' (slot_length_bin_injective hKpos (Prod.ext hlenEq hbinEq))
  rcases slot_spec hKpos z with ⟨hzlen, _, _⟩
  rcases slot_spec hKpos z' with ⟨hz'len, _, _⟩
  refine ⟨start z, start z + slotLength z, start z', start z' + slotLength z',
    by omega, (hstart z).1, by omega, (hstart z').1, hpair, ?_⟩
  exact hrawEq

/-- Hegyvári's affirmative resolution of Erdős Problem 1213. -/
theorem erdos1213 : erdos_1213 := by
  intro a K ha hK
  refine ⟨explicitBound a K, ?_⟩
  intro s A hs hA0 hmono hgap hlast
  exact equal_interval_sums_of_last_gt_explicitBound
    a K ha hK s A hs hA0 hmono hgap hlast

#print axioms equal_interval_sums_of_last_gt_explicitBound
#print axioms erdos1213

end Erdos1213
