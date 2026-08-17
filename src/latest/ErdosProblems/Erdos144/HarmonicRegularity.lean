/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.HarmonicProb

/-!
# Tail regularity in the finite harmonic Bernoulli model

This file records the Chernoff and finite-union-bound part of the
Maier--Tenenbaum regularity argument.  The results are deliberately phrased
for an arbitrary finite family of tails.  The geometric choice of tails (for
example intervals whose endpoints differ by powers of eight) is therefore
kept separate from this purely probabilistic step.
-/

open scoped BigOperators

namespace Erdos144.HarmonicRegularity

noncomputable section

open HarmonicProb

attribute [local instance] Classical.propDecidable

/-- The lower-tail Chernoff estimate at half the mean, with its coefficient
simplified to `-1/12`. -/
theorem prob_card_lt_le_exp_neg_mean_div_twelve
    (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) {K : ℕ}
    (hK : (K : ℝ) ≤ (1 / 2 : ℝ) * ∑ n ∈ s, param n) :
    prob s (fun T => T.card < K) ≤
      Real.exp (-(∑ n ∈ s, param n) / 12) := by
  have h := Erdos697.Bernoulli.lower_tail_chernoff s param
    (fun n _ => param_nonneg n) (fun n hn => param_le_one (hs n hn))
    (hEW := rfl) (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hK
  have hcoeff :
      (1 / 2 : ℝ) * ((1 - (1 / 2 : ℝ)) / (2 * (1 / 2 : ℝ))) +
          (1 / (1 + ((1 - (1 / 2 : ℝ)) / (2 * (1 / 2 : ℝ)))) - 1) =
        -(1 / 12 : ℝ) := by
    norm_num
  rw [hcoeff] at h
  calc
    prob s (fun T => T.card < K) ≤
        Real.exp (-(1 / 12 : ℝ) * ∑ n ∈ s, param n) := by
      simpa [prob, weight] using h
    _ = Real.exp (-(∑ n ∈ s, param n) / 12) := by
      congr 1
      ring

private theorem weight_insert_not_selected
    (s : Finset ℕ) (p : ℕ → ℝ) {a : ℕ} (ha : a ∉ s)
    {T : Finset ℕ} (hT : T ⊆ s) :
    Erdos697.Bernoulli.weight (insert a s) p T =
      (1 - p a) * Erdos697.Bernoulli.weight s p T := by
  have haT : a ∉ T := fun haT => ha (hT haT)
  simp [Erdos697.Bernoulli.weight, ha, haT, Finset.insert_sdiff_of_notMem]
  ring

private theorem weight_insert_selected
    (s : Finset ℕ) (p : ℕ → ℝ) {a : ℕ} (ha : a ∉ s)
    {T : Finset ℕ} (hT : T ⊆ s) :
    Erdos697.Bernoulli.weight (insert a s) p (insert a T) =
      p a * Erdos697.Bernoulli.weight s p T := by
  have haT : a ∉ T := fun haT => ha (hT haT)
  have hdiff : insert a s \ insert a T = s \ T := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    aesop
  rw [Erdos697.Bernoulli.weight, Erdos697.Bernoulli.weight, hdiff]
  simp [haT]
  ring

private theorem marginal_insert
    (p : ℕ → ℝ) (F : Finset ℕ → ℝ)
    {a : ℕ} {s u : Finset ℕ} (has : a ∉ s) (hau : a ∉ u) :
    (∑ T ∈ (insert a s).powerset,
        Erdos697.Bernoulli.weight (insert a s) p T * F (T ∩ u)) =
      ∑ T ∈ s.powerset,
        Erdos697.Bernoulli.weight s p T * F (T ∩ u) := by
  rw [Finset.sum_powerset_insert has]
  calc
    (∑ T ∈ s.powerset,
        Erdos697.Bernoulli.weight (insert a s) p T * F (T ∩ u)) +
        ∑ T ∈ s.powerset,
          Erdos697.Bernoulli.weight (insert a s) p (insert a T) *
            F (insert a T ∩ u) =
        (∑ T ∈ s.powerset,
          ((1 - p a) * Erdos697.Bernoulli.weight s p T) * F (T ∩ u)) +
        ∑ T ∈ s.powerset,
          (p a * Erdos697.Bernoulli.weight s p T) * F (T ∩ u) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro T hT
        rw [weight_insert_not_selected s p has (Finset.mem_powerset.mp hT)]
      · apply Finset.sum_congr rfl
        intro T hT
        rw [weight_insert_selected s p has (Finset.mem_powerset.mp hT)]
        simp [hau]
    _ = ∑ T ∈ s.powerset,
        Erdos697.Bernoulli.weight s p T * F (T ∩ u) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T _
      ring

private theorem marginal_union
    (p : ℕ → ℝ) (F : Finset ℕ → ℝ) (u v : Finset ℕ)
    (huv : Disjoint u v) :
    (∑ T ∈ (u ∪ v).powerset,
        Erdos697.Bernoulli.weight (u ∪ v) p T * F (T ∩ u)) =
      ∑ A ∈ u.powerset, Erdos697.Bernoulli.weight u p A * F A := by
  induction v using Finset.induction_on with
  | empty =>
      simp only [Finset.union_empty]
      apply Finset.sum_congr rfl
      intro A hA
      rw [Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hA)]
  | @insert a v ha ih =>
      have hau : a ∉ u := by
        intro hau
        exact Finset.disjoint_left.mp huv hau (Finset.mem_insert_self a v)
      have huv' : Disjoint u v :=
        Finset.disjoint_left.mpr fun x hxu hxv =>
          Finset.disjoint_left.mp huv hxu (Finset.mem_insert_of_mem hxv)
      rw [Finset.union_insert]
      rw [marginal_insert p F (by simpa [hau] using ha) hau]
      exact ih huv'

/-- Marginalizing a harmonic Bernoulli sample to a subset preserves the
harmonic Bernoulli law on that subset. -/
theorem prob_inter_eq
    (s u : Finset ℕ) (P : Finset ℕ → Prop) [DecidablePred P]
    (hus : u ⊆ s) :
    prob s (fun T => P (T ∩ u)) = prob u P := by
  classical
  have hmarginal :
      (∑ T ∈ s.powerset,
          Erdos697.Bernoulli.weight s param T *
            (if P (T ∩ u) then 1 else 0)) =
        ∑ A ∈ u.powerset,
          Erdos697.Bernoulli.weight u param A * (if P A then 1 else 0) := by
    rw [← Finset.union_sdiff_of_subset hus]
    exact marginal_union param (fun A => if P A then 1 else 0) u (s \ u) <|
      Finset.disjoint_left.mpr fun a hau haDiff =>
        (Finset.mem_sdiff.mp haDiff).2 hau
  simpa only [prob, weight, Finset.sum_filter, mul_ite, mul_one, mul_zero]
    using hmarginal

/-- Chernoff bound for the number of selected points in a specified tail of
a larger harmonic Bernoulli sample. -/
theorem prob_inter_card_lt_le_exp_neg_mean_div_twelve
    (s u : Finset ℕ) (hus : u ⊆ s) (hu : ∀ n ∈ u, 1 ≤ n) {K : ℕ}
    (hK : (K : ℝ) ≤ (1 / 2 : ℝ) * ∑ n ∈ u, param n) :
    prob s (fun T => (T ∩ u).card < K) ≤
      Real.exp (-(∑ n ∈ u, param n) / 12) := by
  rw [prob_inter_eq s u (fun T => T.card < K) hus]
  exact prob_card_lt_le_exp_neg_mean_div_twelve u hu hK

/-- The lower-tail estimate with constants adapted to eight-adic tails.
Reciprocal mass `207 d / 100` is enough to make the chance of selecting fewer
than `2 d` points at most `exp (-d/2000)`.  The number `207/100` is chosen
strictly below `log 8`. -/
theorem prob_card_lt_two_mul_le_exp_neg_div_two_thousand
    (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (d : ℕ)
    (hmean : (207 / 100 : ℝ) * d ≤ ∑ n ∈ s, param n) :
    prob s (fun T => T.card < 2 * d) ≤
      Real.exp (-(d : ℝ) / 2000) := by
  have hK : ((2 * d : ℕ) : ℝ) ≤
      (200 / 207 : ℝ) * ∑ n ∈ s, param n := by
    push_cast
    nlinarith
  have h := Erdos697.Bernoulli.lower_tail_chernoff s param
    (fun n _ => param_nonneg n) (fun n hn => param_le_one (hs n hn))
    (hEW := rfl) (r := (200 / 207 : ℝ)) (by norm_num) (by norm_num) hK
  have hcoeff :
      (200 / 207 : ℝ) *
          ((1 - (200 / 207 : ℝ)) / (2 * (200 / 207 : ℝ))) +
          (1 / (1 + ((1 - (200 / 207 : ℝ)) /
            (2 * (200 / 207 : ℝ)))) - 1) =
        -(49 / 168498 : ℝ) := by
    norm_num
  rw [hcoeff] at h
  calc
    prob s (fun T => T.card < 2 * d) ≤
        Real.exp (-(49 / 168498 : ℝ) * ∑ n ∈ s, param n) := by
      simpa [prob, weight] using h
    _ ≤ Real.exp (-(d : ℝ) / 2000) := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-- The preceding eight-adic-strength estimate for a tail inside one ambient
harmonic Bernoulli sample. -/
theorem prob_inter_card_lt_two_mul_le_exp_neg_div_two_thousand
    (s u : Finset ℕ) (hus : u ⊆ s) (hu : ∀ n ∈ u, 1 ≤ n) (d : ℕ)
    (hmean : (207 / 100 : ℝ) * d ≤ ∑ n ∈ u, param n) :
    prob s (fun T => (T ∩ u).card < 2 * d) ≤
      Real.exp (-(d : ℝ) / 2000) := by
  rw [prob_inter_eq s u (fun T => T.card < 2 * d) hus]
  exact prob_card_lt_two_mul_le_exp_neg_div_two_thousand u hu d hmean

/-- Every indexed tail contains at least twice the number of selected points
specified by its distance from the base index.  In applications `tail r` is
an interval with endpoints on an eight-adic (or a grouped dyadic) scale. -/
def TailRegular (tail : ℕ → Finset ℕ) (base first last : ℕ)
    (T : Finset ℕ) : Prop :=
  ∀ r ∈ Finset.Icc first last,
    2 * (r - base) ≤ (T ∩ tail r).card

/-- The exact eight-adic tail with fixed right endpoint `8^depth * C`.
Increasing `r` by one moves the left endpoint down by a factor of eight.
At `r = base` the tail is empty, and at `r = base + depth` it is `(C,D]`.
-/
def eightAdicTail (C depth base r : ℕ) : Finset ℕ :=
  Finset.Ioc (8 ^ (depth - (r - base)) * C) (8 ^ depth * C)

theorem eightAdicTail_subset_Ioc (C depth base r : ℕ)
    (_hr : r - base ≤ depth) :
    eightAdicTail C depth base r ⊆ Finset.Ioc C (8 ^ depth * C) := by
  intro n hn
  rw [eightAdicTail] at hn
  rcases Finset.mem_Ioc.mp hn with ⟨hleft, hright⟩
  apply Finset.mem_Ioc.mpr
  refine ⟨?_, hright⟩
  have hp : 1 ≤ 8 ^ (depth - (r - base)) :=
    Nat.one_le_pow (depth - (r - base)) 8 (by norm_num)
  have hC : C ≤ 8 ^ (depth - (r - base)) * C := by
    simpa using Nat.mul_le_mul_right C hp
  exact lt_of_le_of_lt hC hleft

/-- A finite union bound for failure of tail regularity.  This is the direct
probabilistic form used in the Maier--Tenenbaum iteration: each tail is a
marginal of one ambient harmonic sample, and its bad lower tail is bounded by
`exp (-mean/12)`.

The parameter `first` need not equal `base`; taking `first > base` discards
the vacuous zero-length tail and gives a decaying geometric sum. -/
theorem prob_not_tailRegular_le_sum_exp
    (s : Finset ℕ) (tail : ℕ → Finset ℕ) (base first last : ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n)
    (hsub : ∀ r ∈ Finset.Icc first last, tail r ⊆ s)
    (hmean : ∀ r ∈ Finset.Icc first last,
      (4 : ℝ) * (r - base : ℕ) ≤ ∑ n ∈ tail r, param n) :
    prob s (fun T => ¬ TailRegular tail base first last T) ≤
      ∑ r ∈ Finset.Icc first last,
        Real.exp (-(∑ n ∈ tail r, param n) / 12) := by
  let bad : ℕ → Finset ℕ → Prop := fun r T =>
    (T ∩ tail r).card < 2 * (r - base)
  have hbad : ∀ T, ¬ TailRegular tail base first last T →
      ∃ r ∈ Finset.Icc first last, bad r T := by
    intro T hT
    simp only [TailRegular, not_forall, not_le] at hT
    rcases hT with ⟨r, hr, hlt⟩
    exact ⟨r, hr, hlt⟩
  calc
    prob s (fun T => ¬ TailRegular tail base first last T) ≤
        prob s (fun T => ∃ r ∈ Finset.Icc first last, bad r T) :=
      prob_mono s _ _ hs hbad
    _ ≤ ∑ r ∈ Finset.Icc first last, prob s (bad r) :=
      prob_exists_le_sum s (Finset.Icc first last) bad hs
    _ ≤ ∑ r ∈ Finset.Icc first last,
        Real.exp (-(∑ n ∈ tail r, param n) / 12) := by
      apply Finset.sum_le_sum
      intro r hr
      apply prob_inter_card_lt_le_exp_neg_mean_div_twelve s (tail r)
        (hsub r hr)
      · intro n hn
        exact hs n (hsub r hr hn)
      · have hm := hmean r hr
        push_cast
        nlinarith

/-- A readable geometric version of `prob_not_tailRegular_le_sum_exp`: if
each tail has reciprocal mass at least four times its index distance, then
the failure mass is bounded by a sum of `exp (-(r-base)/3)`. -/
theorem prob_not_tailRegular_le_geometric_sum
    (s : Finset ℕ) (tail : ℕ → Finset ℕ) (base first last : ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n)
    (hsub : ∀ r ∈ Finset.Icc first last, tail r ⊆ s)
    (hmean : ∀ r ∈ Finset.Icc first last,
      (4 : ℝ) * (r - base : ℕ) ≤ ∑ n ∈ tail r, param n) :
    prob s (fun T => ¬ TailRegular tail base first last T) ≤
      ∑ r ∈ Finset.Icc first last,
        Real.exp (-((r - base : ℕ) : ℝ) / 3) := by
  calc
    prob s (fun T => ¬ TailRegular tail base first last T) ≤
        ∑ r ∈ Finset.Icc first last,
          Real.exp (-(∑ n ∈ tail r, param n) / 12) :=
      prob_not_tailRegular_le_sum_exp s tail base first last hs hsub hmean
    _ ≤ ∑ r ∈ Finset.Icc first last,
        Real.exp (-((r - base : ℕ) : ℝ) / 3) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Real.exp_le_exp.mpr
      have hm := hmean r hr
      nlinarith

/-- The regularity union bound with constants that fit eight-adic tails.  If
the reciprocal mass of the tail at `r` is at least
`(207/100) * (r-base)`, failure of any requested tail count is bounded by the
displayed geometric sum. -/
theorem prob_not_tailRegular_le_eightAdic_geometric_sum
    (s : Finset ℕ) (tail : ℕ → Finset ℕ) (base first last : ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n)
    (hsub : ∀ r ∈ Finset.Icc first last, tail r ⊆ s)
    (hmean : ∀ r ∈ Finset.Icc first last,
      (207 / 100 : ℝ) * (r - base : ℕ) ≤ ∑ n ∈ tail r, param n) :
    prob s (fun T => ¬ TailRegular tail base first last T) ≤
      ∑ r ∈ Finset.Icc first last,
        Real.exp (-((r - base : ℕ) : ℝ) / 2000) := by
  let bad : ℕ → Finset ℕ → Prop := fun r T =>
    (T ∩ tail r).card < 2 * (r - base)
  have hbad : ∀ T, ¬ TailRegular tail base first last T →
      ∃ r ∈ Finset.Icc first last, bad r T := by
    intro T hT
    simp only [TailRegular, not_forall, not_le] at hT
    rcases hT with ⟨r, hr, hlt⟩
    exact ⟨r, hr, hlt⟩
  calc
    prob s (fun T => ¬ TailRegular tail base first last T) ≤
        prob s (fun T => ∃ r ∈ Finset.Icc first last, bad r T) :=
      prob_mono s _ _ hs hbad
    _ ≤ ∑ r ∈ Finset.Icc first last, prob s (bad r) :=
      prob_exists_le_sum s (Finset.Icc first last) bad hs
    _ ≤ ∑ r ∈ Finset.Icc first last,
        Real.exp (-((r - base : ℕ) : ℝ) / 2000) := by
      apply Finset.sum_le_sum
      intro r hr
      exact prob_inter_card_lt_two_mul_le_exp_neg_div_two_thousand
        s (tail r) (hsub r hr) (fun n hn => hs n (hsub r hr hn))
        (r - base) (hmean r hr)

/-- Fully specialized eight-adic regularity estimate.  The only analytic
input left visible is the deterministic reciprocal-mass estimate for each
tail; all probability and union-bound bookkeeping is discharged here. -/
theorem prob_not_eightAdicTailRegular_le_geometric_sum
    (C depth base first last : ℕ)
    (hrange : ∀ r ∈ Finset.Icc first last, r - base ≤ depth)
    (hmean : ∀ r ∈ Finset.Icc first last,
      (207 / 100 : ℝ) * (r - base : ℕ) ≤
        ∑ n ∈ eightAdicTail C depth base r, param n) :
    prob (Finset.Ioc C (8 ^ depth * C))
        (fun T => ¬ TailRegular (eightAdicTail C depth base)
          base first last T) ≤
      ∑ r ∈ Finset.Icc first last,
        Real.exp (-((r - base : ℕ) : ℝ) / 2000) := by
  apply prob_not_tailRegular_le_eightAdic_geometric_sum
  · intro n hn
    have hn0 := (Finset.mem_Ioc.mp hn).1
    omega
  · intro r hr
    exact eightAdicTail_subset_Ioc C depth base r (hrange r hr)
  · exact hmean

end


end Erdos144.HarmonicRegularity
