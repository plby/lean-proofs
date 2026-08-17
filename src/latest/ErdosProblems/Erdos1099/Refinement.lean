/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1099.Basic
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Refinement of divisor-chain energy

The complete increasing list of divisors refines every increasing chain of
divisors from `1` to `n`.  This file proves that, for exponent at least one,
such a refinement can only decrease the relative-gap energy.

The chain is represented by a monotone map into the indices of the full
ordered divisor sequence.  Thus every entry is automatically a divisor.
Allowing repeated indices is useful when concatenating chains: repetitions
merely contribute a zero gap.
-/

open Finset
open scoped BigOperators

namespace Erdos1099

noncomputable section

/-- Relative-gap energy of a chain selected from the ordered divisors of `n`. -/
def divisorChainEnergy (alpha : ℝ) (n : ℕ) {m : ℕ}
    (c : Fin (m + 1) → Fin n.divisors.card) : ℝ :=
  ∑ j : Fin m,
    Real.rpow
      (((orderedDivisor n (c ⟨j.1 + 1, by omega⟩) : ℕ) : ℝ) /
          ((orderedDivisor n (c ⟨j.1, by omega⟩) : ℕ) : ℝ) - 1)
      alpha

/-- Relative-gap energy of a finite sequence of positive integer values. -/
def valueChainEnergy (alpha : ℝ) {m : ℕ} (d : Fin (m + 1) → ℕ) : ℝ :=
  ∑ j : Fin m,
    Real.rpow
      (((d ⟨j.1 + 1, by omega⟩ : ℕ) : ℝ) /
          ((d ⟨j.1, by omega⟩ : ℕ) : ℝ) - 1)
      alpha

private def relativeGap (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  x (i + 1) / x i - 1

private lemma relativeGap_nonneg_of_monotone (x : ℕ → ℝ)
    (hxpos : ∀ i, 0 < x i) (hxmono : Monotone x) (i : ℕ) :
    0 ≤ relativeGap x i := by
  rw [relativeGap, sub_nonneg, one_le_div (hxpos i)]
  exact hxmono (Nat.le_succ i)

private lemma two_relativeGaps_le {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hbc : b ≤ c) :
    b / a - 1 + (c / b - 1) ≤ c / a - 1 := by
  have hba : 0 ≤ b / a - 1 := by
    rw [sub_nonneg, one_le_div ha]
    exact hab
  have hcb : 0 ≤ c / b - 1 := by
    rw [sub_nonneg, one_le_div hb]
    exact hbc
  have hmul : 0 ≤ (b / a - 1) * (c / b - 1) := mul_nonneg hba hcb
  have hratio : (b / a) * (c / b) = c / a := by
    field_simp
  rw [← hratio]
  nlinarith

/-- On an interval of a positive monotone sequence, the energy of all
successive relative gaps is bounded by the energy of the single endpoint
gap. -/
private lemma sum_Ico_relativeGap_rpow_le {alpha : ℝ} (halpha : 1 ≤ alpha)
    (x : ℕ → ℝ) (hxpos : ∀ i, 0 < x i) (hxmono : Monotone x)
    {p q : ℕ} (hpq : p ≤ q) :
    ∑ i ∈ Ico p q, Real.rpow (relativeGap x i) alpha ≤
      Real.rpow (x q / x p - 1) alpha := by
  induction q generalizing p with
  | zero =>
      have hp : p = 0 := Nat.eq_zero_of_le_zero hpq
      subst p
      simpa [hxpos 0 |>.ne'] using
        (Real.rpow_nonneg (show (0 : ℝ) ≤ 0 by rfl) alpha)
  | succ q ih =>
      by_cases hp : p = q + 1
      · subst p
        simpa [hxpos (q + 1) |>.ne'] using
          (Real.rpow_nonneg (show (0 : ℝ) ≤ 0 by rfl) alpha)
      · have hpq' : p ≤ q := by omega
        have hih := ih hpq'
        have hleft : 0 ≤ x q / x p - 1 := by
          rw [sub_nonneg, one_le_div (hxpos p)]
          exact hxmono hpq'
        have hright : 0 ≤ relativeGap x q :=
          relativeGap_nonneg_of_monotone x hxpos hxmono q
        have hadd :
            x q / x p - 1 + relativeGap x q ≤
              x (q + 1) / x p - 1 := by
          exact two_relativeGaps_le (hxpos p) (hxpos q) (hxmono hpq')
            (hxmono (Nat.le_succ q))
        calc
          (∑ i ∈ Ico p (q + 1), Real.rpow (relativeGap x i) alpha) =
              (∑ i ∈ Ico p q, Real.rpow (relativeGap x i) alpha) +
                Real.rpow (relativeGap x q) alpha := by
                  rw [sum_Ico_succ_top hpq']
          _ ≤ Real.rpow (x q / x p - 1) alpha +
                Real.rpow (relativeGap x q) alpha :=
              add_le_add hih le_rfl
          _ ≤ Real.rpow (x q / x p - 1 + relativeGap x q) alpha :=
              Real.add_rpow_le_rpow_add hleft hright halpha
          _ ≤ Real.rpow (x (q + 1) / x p - 1) alpha :=
              Real.rpow_le_rpow (add_nonneg hleft hright) hadd (by linarith)

private lemma sum_fin_consecutive_sub {m : ℕ} (x : Fin (m + 1) → ℝ) :
    (∑ i : Fin m, (x ⟨i.1 + 1, by omega⟩ - x ⟨i.1, by omega⟩)) =
      x ⟨m, by omega⟩ - x ⟨0, by omega⟩ := by
  let y : ℕ → ℝ := fun i ↦
    x ⟨min i m, Nat.lt_succ_of_le (min_le_right i m)⟩
  calc
    (∑ i : Fin m, (x ⟨i.1 + 1, by omega⟩ - x ⟨i.1, by omega⟩)) =
        ∑ i : Fin m, (y (i.1 + 1) - y i.1) := by
          apply sum_congr rfl
          intro i _
          have hi : i.1 ≤ m := i.isLt.le
          have his : i.1 + 1 ≤ m := i.isLt
          simp [y, hi, his]
    _ = ∑ i ∈ range m, (y (i + 1) - y i) :=
      Fin.sum_univ_eq_sum_range (fun i ↦ y (i + 1) - y i) m
    _ = y m - y 0 := sum_range_sub y m
    _ = x ⟨m, by omega⟩ - x ⟨0, by omega⟩ := by simp [y]

/-- Consecutive index intervals in an endpoint-normalized monotone chain
partition the full index interval. -/
private lemma sum_chain_Ico {m : ℕ} (c : Fin (m + 1) → ℕ)
    (hc : Monotone c) (hc0 : c ⟨0, by omega⟩ = 0) (f : ℕ → ℝ) :
    (∑ j : Fin m, ∑ i ∈ Ico (c ⟨j.1, by omega⟩) (c ⟨j.1 + 1, by omega⟩), f i) =
      ∑ i ∈ range (c ⟨m, by omega⟩), f i := by
  let s : Fin (m + 1) → ℝ := fun j ↦ ∑ i ∈ range (c j), f i
  calc
    (∑ j : Fin m, ∑ i ∈ Ico (c ⟨j.1, by omega⟩) (c ⟨j.1 + 1, by omega⟩), f i) =
        ∑ j : Fin m, (s ⟨j.1 + 1, by omega⟩ - s ⟨j.1, by omega⟩) := by
          apply sum_congr rfl
          intro j _
          exact sum_Ico_eq_sub f (hc (by simp))
    _ = s ⟨m, by omega⟩ - s ⟨0, by omega⟩ :=
      sum_fin_consecutive_sub s
    _ = ∑ i ∈ range (c ⟨m, by omega⟩), f i := by
      change (∑ i ∈ range (c ⟨m, by omega⟩), f i) -
          (∑ i ∈ range (c ⟨0, by omega⟩), f i) = _
      rw [hc0]
      simp

private def extendedDivisorValue (n : ℕ) (hn : n ≠ 0) (i : ℕ) : ℝ :=
  ((orderedDivisor n
      ⟨min i (n.divisors.card - 1), by
        have hcard : 0 < n.divisors.card :=
          Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hn)
        omega⟩ : ℕ) : ℝ)

private lemma extendedDivisorValue_eq (n : ℕ) (hn : n ≠ 0) {i : ℕ}
    (hi : i < n.divisors.card) :
    extendedDivisorValue n hn i = ((orderedDivisor n ⟨i, hi⟩ : ℕ) : ℝ) := by
  simp [extendedDivisorValue, Nat.min_eq_left (Nat.le_sub_one_of_lt hi)]

private lemma extendedDivisorValue_pos (n : ℕ) (hn : n ≠ 0) (i : ℕ) :
    0 < extendedDivisorValue n hn i := by
  unfold extendedDivisorValue
  exact_mod_cast orderedDivisor_pos n _

private lemma extendedDivisorValue_monotone (n : ℕ) (hn : n ≠ 0) :
    Monotone (extendedDivisorValue n hn) := by
  intro i j hij
  unfold extendedDivisorValue
  have hmin : min i (n.divisors.card - 1) ≤ min j (n.divisors.card - 1) :=
    min_le_min_right _ hij
  have hfin :
      (⟨min i (n.divisors.card - 1), by
          have hcard : 0 < n.divisors.card :=
            Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hn)
          omega⟩ : Fin n.divisors.card) ≤
        ⟨min j (n.divisors.card - 1), by
          have hcard : 0 < n.divisors.card :=
            Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hn)
          omega⟩ := hmin
  exact_mod_cast (orderedDivisor n).monotone hfin

private lemma hAlpha_eq_sum_range_extended (alpha : ℝ) (n : ℕ) (hn : n ≠ 0) :
    hAlpha alpha n =
      ∑ i ∈ range (n.divisors.card - 1),
        Real.rpow (relativeGap (extendedDivisorValue n hn) i) alpha := by
  calc
    hAlpha alpha n =
        ∑ i : Fin (n.divisors.card - 1),
          Real.rpow (relativeGap (extendedDivisorValue n hn) i.1) alpha := by
            unfold hAlpha
            apply sum_congr rfl
            intro i _
            simp only [relativeGap]
            rw [extendedDivisorValue_eq n hn (by omega),
              extendedDivisorValue_eq n hn (by omega)]
    _ = ∑ i ∈ range (n.divisors.card - 1),
          Real.rpow (relativeGap (extendedDivisorValue n hn) i) alpha :=
      Fin.sum_univ_eq_sum_range
        (fun i ↦ Real.rpow (relativeGap (extendedDivisorValue n hn) i) alpha)
        (n.divisors.card - 1)

/-- The full ordered divisor sequence has no greater relative-gap energy than
any strictly increasing chain of divisors from its first entry to its last.

The monotone map `c` selects the chain.  `hc0` and `hclast` say that its
endpoints are respectively `1` and `n`, expressed as indices in the complete
ordered divisor sequence. -/
theorem hAlpha_le_divisorChainEnergy {alpha : ℝ} (halpha : 1 ≤ alpha)
    {n m : ℕ} (hn : n ≠ 0)
    (c : Fin (m + 1) → Fin n.divisors.card) (hcmono : Monotone c)
    (hc0 : (c ⟨0, by omega⟩).1 = 0)
    (hclast : (c ⟨m, by omega⟩).1 = n.divisors.card - 1) :
    hAlpha alpha n ≤ divisorChainEnergy alpha n c := by
  let x : ℕ → ℝ := extendedDivisorValue n hn
  let cv : Fin (m + 1) → ℕ := fun j ↦ (c j).1
  have hcvmono : Monotone cv := fun _ _ hij ↦ by
    exact_mod_cast hcmono hij
  have hpartition :
      (∑ j : Fin m, ∑ i ∈ Ico (cv ⟨j.1, by omega⟩) (cv ⟨j.1 + 1, by omega⟩),
          Real.rpow (relativeGap x i) alpha) =
        ∑ i ∈ range (n.divisors.card - 1),
          Real.rpow (relativeGap x i) alpha := by
    rw [← hclast]
    exact sum_chain_Ico cv hcvmono hc0 _
  rw [hAlpha_eq_sum_range_extended alpha n hn, ← hpartition]
  unfold divisorChainEnergy
  apply sum_le_sum
  intro j _
  have hpq : cv ⟨j.1, by omega⟩ ≤ cv ⟨j.1 + 1, by omega⟩ :=
    hcvmono (by simp)
  have hblock := sum_Ico_relativeGap_rpow_le halpha x
    (extendedDivisorValue_pos n hn) (extendedDivisorValue_monotone n hn) hpq
  simpa [x, cv, relativeGap, extendedDivisorValue_eq] using hblock

/-- Strict-chain version of `hAlpha_le_divisorChainEnergy`. -/
theorem hAlpha_le_divisorChainEnergy_orderEmb {alpha : ℝ} (halpha : 1 ≤ alpha)
    {n m : ℕ} (hn : n ≠ 0)
    (c : Fin (m + 1) ↪o Fin n.divisors.card)
    (hc0 : (c ⟨0, by omega⟩).1 = 0)
    (hclast : (c ⟨m, by omega⟩).1 = n.divisors.card - 1) :
    hAlpha alpha n ≤ divisorChainEnergy alpha n c :=
  hAlpha_le_divisorChainEnergy halpha hn c c.monotone hc0 hclast

private lemma card_divisors_pos {n : ℕ} (hn : n ≠ 0) : 0 < n.divisors.card :=
  Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hn)

private lemma orderedDivisor_zero {n : ℕ} (hn : n ≠ 0) :
    orderedDivisor n ⟨0, card_divisors_pos hn⟩ = 1 := by
  rw [orderedDivisor, Finset.orderEmbOfFin_zero rfl (card_divisors_pos hn)]
  apply (Finset.min'_eq_iff _ _ _).2
  refine ⟨Nat.one_mem_divisors.mpr hn, ?_⟩
  intro d hd
  exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))

private lemma orderedDivisor_last {n : ℕ} (hn : n ≠ 0) :
    orderedDivisor n
      ⟨n.divisors.card - 1,
        Nat.sub_lt (card_divisors_pos hn) Nat.zero_lt_one⟩ = n := by
  rw [orderedDivisor, Finset.orderEmbOfFin_last rfl (card_divisors_pos hn)]
  apply (Finset.max'_eq_iff _ _ _).2
  exact ⟨Nat.mem_divisors_self n hn, fun d hd ↦ Nat.divisor_le hd⟩

/-- Value-level form of the refinement theorem.  A monotone finite sequence
of divisors beginning at `1` and ending at `n` bounds the energy of the full
ordered divisor sequence.  Repeated values are permitted and contribute
zero. -/
theorem hAlpha_le_valueChainEnergy {alpha : ℝ} (halpha : 1 ≤ alpha)
    {n m : ℕ} (hn : n ≠ 0) (d : Fin (m + 1) → ℕ)
    (hdmem : ∀ j, d j ∈ n.divisors) (hdmono : Monotone d)
    (hd0 : d ⟨0, by omega⟩ = 1) (hdlast : d ⟨m, by omega⟩ = n) :
    hAlpha alpha n ≤ valueChainEnergy alpha d := by
  let e : Fin n.divisors.card ≃o n.divisors := n.divisors.orderIsoOfFin rfl
  let c : Fin (m + 1) → Fin n.divisors.card := fun j ↦
    e.symm ⟨d j, hdmem j⟩
  have hc_value (j : Fin (m + 1)) : orderedDivisor n (c j) = d j := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨d j, hdmem j⟩)
  have hcmono : Monotone c := by
    intro i j hij
    apply e.symm.monotone
    exact hdmono hij
  have hc0 : (c ⟨0, by omega⟩).1 = 0 := by
    have heq : c ⟨0, by omega⟩ = ⟨0, card_divisors_pos hn⟩ := by
      apply (orderedDivisor n).injective
      rw [hc_value, hd0, orderedDivisor_zero hn]
    exact congrArg Fin.val heq
  have hclast : (c ⟨m, by omega⟩).1 = n.divisors.card - 1 := by
    have heq : c ⟨m, by omega⟩ =
        ⟨n.divisors.card - 1,
          Nat.sub_lt (card_divisors_pos hn) Nat.zero_lt_one⟩ := by
      apply (orderedDivisor n).injective
      rw [hc_value, hdlast, orderedDivisor_last hn]
    exact congrArg Fin.val heq
  calc
    hAlpha alpha n ≤ divisorChainEnergy alpha n c :=
      hAlpha_le_divisorChainEnergy halpha hn c hcmono hc0 hclast
    _ = valueChainEnergy alpha d := by
      unfold divisorChainEnergy valueChainEnergy
      apply sum_congr rfl
      intro j _
      rw [hc_value, hc_value]

end

end Erdos1099
