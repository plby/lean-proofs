/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import Mathlib

/-!
# Finite exceptions in prime-predicate counts

Changing a predicate at finitely many natural numbers changes its prime-counting
function by a bounded amount.  In particular, it does not change an asymptotic
of the form `c * x / log x`.
-/

namespace Erdos980.NaturalChebotarev

open scoped BigOperators
open Asymptotics Filter

/-- The number of primes `p < x` satisfying `P p`. -/
def primeCount (P : ℕ → Prop) [DecidablePred P] (x : ℕ) : ℕ :=
  ((Finset.range x).filter fun p ↦ p.Prime ∧ P p).card

/-- If two predicates agree away from `s`, their prime counts differ by at most
`s.card`.  The estimate deliberately does not require the members of `s` to be
prime. -/
theorem abs_primeCount_sub_primeCount_le_of_eq_outside
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (s : Finset ℕ) (h : ∀ n ∉ s, P n ↔ Q n) (x : ℕ) :
    |(primeCount P x : ℝ) - primeCount Q x| ≤ s.card := by
  let A := (Finset.range x).filter fun p ↦ p.Prime ∧ P p
  let B := (Finset.range x).filter fun p ↦ p.Prime ∧ Q p
  have hAB : A \ B ⊆ s := by
    intro p hp
    have hpA : p ∈ A := (Finset.mem_sdiff.mp hp).1
    have hpB : p ∉ B := (Finset.mem_sdiff.mp hp).2
    by_contra hps
    have hpdata := Finset.mem_filter.mp hpA
    apply hpB
    exact Finset.mem_filter.mpr
      ⟨hpdata.1, hpdata.2.1, (h p hps).mp hpdata.2.2⟩
  have hBA : B \ A ⊆ s := by
    intro p hp
    have hpB : p ∈ B := (Finset.mem_sdiff.mp hp).1
    have hpA : p ∉ A := (Finset.mem_sdiff.mp hp).2
    by_contra hps
    have hpdata := Finset.mem_filter.mp hpB
    apply hpA
    exact Finset.mem_filter.mpr
      ⟨hpdata.1, hpdata.2.1, (h p hps).mpr hpdata.2.2⟩
  have hAle : A.card ≤ s.card + B.card := by
    calc
      A.card ≤ (A \ B).card + B.card := Finset.card_le_card_sdiff_add_card
      _ ≤ s.card + B.card := Nat.add_le_add_right (Finset.card_le_card hAB) _
  have hBle : B.card ≤ s.card + A.card := by
    calc
      B.card ≤ (B \ A).card + A.card := Finset.card_le_card_sdiff_add_card
      _ ≤ s.card + A.card := Nat.add_le_add_right (Finset.card_le_card hBA) _
  change |(A.card : ℝ) - B.card| ≤ s.card
  rw [abs_le]
  constructor
  · rw [neg_le_sub_iff_le_add]
    have hBle' : (B.card : ℝ) ≤ s.card + A.card := by exact_mod_cast hBle
    simpa [add_comm] using hBle'
  · rw [sub_le_iff_le_add]
    exact_mod_cast hAle

/-- If the symmetric difference of two predicates is finite, the difference
of their prime counts is bounded by its cardinality. -/
theorem abs_primeCount_sub_primeCount_le_of_finite
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (hfinite : {n | ¬ (P n ↔ Q n)}.Finite) (x : ℕ) :
    |(primeCount P x : ℝ) - primeCount Q x| ≤
      {n | ¬ (P n ↔ Q n)}.ncard := by
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  apply abs_primeCount_sub_primeCount_le_of_eq_outside P Q hfinite.toFinset
  intro n hn
  by_contra hne
  exact hn (hfinite.mem_toFinset.mpr hne)

/-- A constant function is little-oh of the prime-number-theorem scale
`x / log x`, for natural endpoints. -/
theorem const_isLittleO_natCast_div_log (C : ℝ) :
    (fun _ : ℕ ↦ C) =o[atTop]
      (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ)) := by
  have hlog : (fun x : ℕ ↦ Real.log (x : ℝ)) =o[atTop] (fun x : ℕ ↦ (x : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hzero : ∀ᶠ x : ℕ in atTop,
      Real.log (x : ℝ) = 0 → (x : ℝ) = 0 := by
    filter_upwards [eventually_ge_atTop 2] with x hx hlogzero
    have hxreal : (1 : ℝ) < x := by exact_mod_cast hx
    exact (ne_of_gt (Real.log_pos hxreal) hlogzero).elim
  have hinv : (fun x : ℕ ↦ ((x : ℝ))⁻¹) =o[atTop]
      (fun x : ℕ ↦ (Real.log (x : ℝ))⁻¹) :=
    hlog.inv_rev hzero
  have hmul := hinv.mul_isBigO
    (isBigO_refl (fun x : ℕ ↦ (x : ℝ)) atTop)
  have hone : (fun _ : ℕ ↦ (1 : ℝ)) =o[atTop]
      (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ)) := by
    refine hmul.congr' ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with x hx
      simp [Nat.ne_of_gt hx]
    · exact Eventually.of_forall fun x ↦ by
        simp only [div_eq_mul_inv]
        ring
  exact (isBigO_const_const C one_ne_zero atTop).trans_isLittleO hone

/-- A finite exceptional set changes the prime count by little-oh of
`x / log x`. -/
theorem primeCount_sub_primeCount_isLittleO_of_eq_outside
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (s : Finset ℕ) (h : ∀ n ∉ s, P n ↔ Q n) :
    (fun x : ℕ ↦ (primeCount P x : ℝ) - primeCount Q x) =o[atTop]
      (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ)) := by
  have hbounded :
      (fun x : ℕ ↦ (primeCount P x : ℝ) - primeCount Q x) =O[atTop]
        (fun _ : ℕ ↦ (1 : ℝ)) := by
    apply IsBigO.of_bound (s.card : ℝ)
    exact Eventually.of_forall fun x ↦ by
      simpa [Real.norm_eq_abs] using
        abs_primeCount_sub_primeCount_le_of_eq_outside P Q s h x
  exact hbounded.trans_isLittleO (const_isLittleO_natCast_div_log 1)

/-- Set-theoretic version of
`primeCount_sub_primeCount_isLittleO_of_eq_outside`. -/
theorem primeCount_sub_primeCount_isLittleO_of_finite
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (hfinite : {n | ¬ (P n ↔ Q n)}.Finite) :
    (fun x : ℕ ↦ (primeCount P x : ℝ) - primeCount Q x) =o[atTop]
      (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ)) := by
  apply primeCount_sub_primeCount_isLittleO_of_eq_outside P Q hfinite.toFinset
  intro n hn
  by_contra hne
  exact hn (hfinite.mem_toFinset.mpr hne)

/-- Finite changes of the prime predicate preserve a `c * x / log x`
asymptotic. -/
theorem primeCount_isEquivalent_of_eq_outside
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (s : Finset ℕ) (h : ∀ n ∉ s, P n ↔ Q n) (c : ℝ) (hc : c ≠ 0)
    (hP : (fun x : ℕ ↦ (primeCount P x : ℝ)) ~[atTop]
      (fun x : ℕ ↦ c * ((x : ℝ) / Real.log (x : ℝ)))) :
    (fun x : ℕ ↦ (primeCount Q x : ℝ)) ~[atTop]
      (fun x : ℕ ↦ c * ((x : ℝ) / Real.log (x : ℝ))) := by
  have hdiff := primeCount_sub_primeCount_isLittleO_of_eq_outside P Q s h
  have hscale : (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ)) =O[atTop]
      (fun x : ℕ ↦ c * ((x : ℝ) / Real.log (x : ℝ))) :=
    (isBigO_refl (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ)) atTop).const_mul_right hc
  have hdiff' :
      (fun x : ℕ ↦ (primeCount P x : ℝ) - primeCount Q x) =o[atTop]
        (fun x : ℕ ↦ c * ((x : ℝ) / Real.log (x : ℝ))) :=
    hdiff.trans_isBigO hscale
  refine (hP.sub_isLittleO hdiff').congr_left ?_
  exact Eventually.of_forall fun x ↦ by
    simp only [Pi.sub_apply]
    ring

/-- Set-theoretic finite-exception version of
`primeCount_isEquivalent_of_eq_outside`. -/
theorem primeCount_isEquivalent_of_finite
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (hfinite : {n | ¬ (P n ↔ Q n)}.Finite) (c : ℝ) (hc : c ≠ 0)
    (hP : (fun x : ℕ ↦ (primeCount P x : ℝ)) ~[atTop]
      (fun x : ℕ ↦ c * ((x : ℝ) / Real.log (x : ℝ)))) :
    (fun x : ℕ ↦ (primeCount Q x : ℝ)) ~[atTop]
      (fun x : ℕ ↦ c * ((x : ℝ) / Real.log (x : ℝ))) := by
  apply primeCount_isEquivalent_of_eq_outside P Q hfinite.toFinset
  · intro n hn
    by_contra hne
    exact hn (hfinite.mem_toFinset.mpr hne)
  · exact hc
  · exact hP

end Erdos980.NaturalChebotarev
