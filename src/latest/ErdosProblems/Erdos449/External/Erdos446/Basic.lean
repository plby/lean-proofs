/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Analysis.Normed.Field.Lemmas
import Util.Density

/-!
# Erdős Problem 446: exact densities

This file fixes the literal open interval `(n, 2n)` from the problem and proves
that all of its divisor-count level sets have natural densities.  The proof is
elementary: the level sets are periodic modulo the least common multiple of the
integers in the interval, and a complete-period count has an error bounded by
one period.
-/

namespace Erdos446

open Filter Finset Set
open scoped Topology

/-! ## The divisor-count sets and their exact residue densities -/

/-- The number of divisors of `m` in the literal open interval `(n, 2n)`. -/
def divisorCount (n m : ℕ) : ℕ :=
  ((Finset.Ioo n (2 * n)).filter fun d ↦ d ∣ m).card

/-- Integers having exactly `r` divisors in `(n, 2n)`. -/
def exactDivisorSet (r n : ℕ) : Set ℕ :=
  {m | divisorCount n m = r}

/-- Integers having at least one divisor in `(n, 2n)`. -/
def divisorSet (n : ℕ) : Set ℕ :=
  {m | 0 < divisorCount n m}

/-- A common period for all divisibility predicates indexed by `(n, 2n)`. -/
def intervalLcm (n : ℕ) : ℕ :=
  (Finset.Ioo n (2 * n)).lcm id

theorem intervalLcm_pos (n : ℕ) : 0 < intervalLcm n := by
  apply Nat.pos_of_ne_zero
  rw [intervalLcm, Finset.lcm_ne_zero_iff]
  intro d hd
  have hnd : n < d := (Finset.mem_Ioo.mp hd).1
  simpa only [id_eq] using
    (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le n) hnd))

/-- Divisor count is periodic in the integer being tested. -/
theorem divisorCount_add_intervalLcm (n m : ℕ) :
    divisorCount n (m + intervalLcm n) = divisorCount n m := by
  simp only [divisorCount]
  congr 1
  refine filter_congr fun d hd ↦ ?_
  rw [add_comm]
  exact Nat.dvd_add_right (Finset.dvd_lcm hd)

theorem exactDivisorSet_periodic (r n : ℕ) :
    Function.Periodic (fun m ↦ m ∈ exactDivisorSet r n) (intervalLcm n) := by
  intro m
  simp only [exactDivisorSet, Set.mem_setOf_eq]
  exact congrArg (fun k ↦ k = r) (divisorCount_add_intervalLcm n m)

theorem divisorSet_periodic (n : ℕ) :
    Function.Periodic (fun m ↦ m ∈ divisorSet n) (intervalLcm n) := by
  intro m
  simp only [divisorSet, Set.mem_setOf_eq]
  exact congrArg (fun k ↦ 0 < k) (divisorCount_add_intervalLcm n m)

/-! ## A periodic-set density lemma over the natural numbers -/

private lemma abs_count_sub_mul_div_le_of_bounds {q M L c count : ℝ}
    (hL : 0 < L) (hc0 : 0 ≤ c) (hcL : c ≤ L)
    (hqle : q * L ≤ M) (hMlt : M < (q + 1) * L)
    (hlow : q * c ≤ count) (hup : count ≤ (q + 1) * c) :
    |count - M * c / L| ≤ L := by
  rw [abs_sub_le_iff]
  constructor
  · have hqc_le : q * c ≤ M * c / L := by
      have hq_le_div : q ≤ M / L := (le_div_iff₀ hL).2 hqle
      have hq_c := mul_le_mul_of_nonneg_right hq_le_div hc0
      simpa [div_mul_eq_mul_div] using hq_c
    have hcount_le : count ≤ M * c / L + L := by nlinarith
    linarith
  · have hM_le : M ≤ (q + 1) * L := le_of_lt hMlt
    have hM_sub_le : M - L ≤ q * L := by nlinarith
    have hleft_le : M * c / L - L ≤ q * c := by
      have haux : (M - L) * c / L ≤ q * c := by
        have hdiv_le : (M - L) / L ≤ q := (div_le_iff₀ hL).2 hM_sub_le
        have hmul := mul_le_mul_of_nonneg_right hdiv_le hc0
        simpa [div_mul_eq_mul_div] using hmul
      have hleft_aux : M * c / L - L ≤ (M - L) * c / L := by
        have hrewrite : (M - L) * c / L = M * c / L - c := by
          field_simp [hL.ne']
        rw [hrewrite]
        linarith
      exact hleft_aux.trans haux
    have hcount_ge : M * c / L - L ≤ count := by nlinarith
    linarith

private lemma periodic_nat_count_mul (p : ℕ → Prop) [DecidablePred p] (L : ℕ)
    (hp : Function.Periodic p L) :
    ∀ q, ((Finset.range (q * L)).filter p).card =
      q * ((Finset.range L).filter p).card := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.succ_mul, Finset.range_add_eq_union, Finset.filter_union]
      rw [Finset.card_union_of_disjoint]
      · rw [ih]
        have hblock := Nat.filter_Ico_card_eq_of_periodic (q * L) L p hp
        have hmap_set :
            (Finset.range L).map (addLeftEmbedding (q * L)) =
              Finset.Ico (q * L) (q * L + L) := by
          ext x
          constructor
          · intro hx
            rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
            simp [Finset.mem_Ico] at hy ⊢
            omega
          · intro hx
            rw [Finset.mem_Ico] at hx
            refine Finset.mem_map.mpr ⟨x - q * L, ?_, ?_⟩
            · simp
              omega
            · simp
              omega
        rw [hmap_set, hblock, Nat.count_eq_card_filter_range]
        ring
      · rw [Finset.disjoint_left]
        intro x hx hxl
        rcases Finset.mem_filter.mp hx with ⟨hx_range, _⟩
        rcases Finset.mem_filter.mp hxl with ⟨hxl_map, _⟩
        rcases Finset.mem_map.mp hxl_map with ⟨y, hy, rfl⟩
        simp only [Finset.mem_range, addLeftEmbedding_apply] at hx_range hy
        omega

private lemma periodic_nat_count_error (p : ℕ → Prop) [DecidablePred p]
    (L : ℕ) (hL : 0 < L) (hp : Function.Periodic p L) (M : ℕ) :
    |(((Finset.range M).filter p).card : ℝ) -
        (M : ℝ) * (((Finset.range L).filter p).card : ℝ) / (L : ℝ)| ≤ (L : ℝ) := by
  let c := ((Finset.range L).filter p).card
  let q := M / L
  let count := ((Finset.range M).filter p).card
  have hmul := periodic_nat_count_mul p L hp
  have hqL_le : q * L ≤ M := Nat.div_mul_le_self M L
  have hM_lt_succ : M < (q + 1) * L := by
    simpa [q, mul_comm] using Nat.lt_mul_div_succ M hL
  have hsubset_low : Finset.range (q * L) ⊆ Finset.range M := by
    intro x hx
    exact Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hx) hqL_le)
  have hsubset_high : Finset.range M ⊆ Finset.range ((q + 1) * L) := by
    intro x hx
    exact Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_of_lt hM_lt_succ))
  have hlow_nat : q * c ≤ count := by
    dsimp [count, c]
    rw [← hmul q]
    exact Finset.card_le_card (Finset.filter_subset_filter p hsubset_low)
  have hup_nat : count ≤ (q + 1) * c := by
    dsimp [count, c]
    calc
      ((Finset.range M).filter p).card ≤
          ((Finset.range ((q + 1) * L)).filter p).card :=
        Finset.card_le_card (Finset.filter_subset_filter p hsubset_high)
      _ = (q + 1) * ((Finset.range L).filter p).card := hmul (q + 1)
  have hc_le_L : c ≤ L := by
    simpa using Finset.card_filter_le (Finset.range L) p
  have hL_real : (0 : ℝ) < L := by exact_mod_cast hL
  have hqle_real : (q : ℝ) * (L : ℝ) ≤ (M : ℝ) := by exact_mod_cast hqL_le
  have hMlt_real : (M : ℝ) < ((q : ℝ) + 1) * (L : ℝ) := by
    exact_mod_cast hM_lt_succ
  have hlow_real : (q : ℝ) * (c : ℝ) ≤ (count : ℝ) := by exact_mod_cast hlow_nat
  have hup_real : (count : ℝ) ≤ ((q : ℝ) + 1) * (c : ℝ) := by
    exact_mod_cast hup_nat
  have hc0_real : (0 : ℝ) ≤ c := by positivity
  have hcL_real : (c : ℝ) ≤ L := by exact_mod_cast hc_le_L
  simpa [c, count] using
    abs_count_sub_mul_div_le_of_bounds hL_real hc0_real hcL_real
      hqle_real hMlt_real hlow_real hup_real

/-- A periodic subset of `ℕ` has density equal to its proportion in one period. -/
theorem hasDensity_of_periodic (p : ℕ → Prop) [DecidablePred p]
    (L : ℕ) (hL : 0 < L) (hp : Function.Periodic p L) :
    ({m | p m} : Set ℕ).HasDensity
      (((((Finset.range L).filter p).card : ℕ) : ℝ) / (L : ℝ)) := by
  let c := ((Finset.range L).filter p).card
  have hpartial (M : ℕ) :
      ({m | p m} : Set ℕ).partialDensity Set.univ M =
        (((((Finset.range M).filter p).card : ℕ) : ℝ) / (M : ℝ)) := by
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter,
      Set.ncard_Iio_nat]
    have hset : ({m | p m} : Set ℕ) ∩ Set.Iio M =
        ↑((Finset.range M).filter p) := by
      ext m
      simp [and_comm]
    rw [hset, Set.ncard_coe_finset]
  have hbound : ∀ᶠ M : ℕ in atTop,
      |({m | p m} : Set ℕ).partialDensity Set.univ M -
          (c : ℝ) / (L : ℝ)| ≤ (L : ℝ) / (M : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with M hM
    rw [hpartial]
    have herr := periodic_nat_count_error p L hL hp M
    have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
    have hrewrite :
        ((((Finset.range M).filter p).card : ℝ) / (M : ℝ)) -
            (c : ℝ) / (L : ℝ) =
          ((((Finset.range M).filter p).card : ℝ) -
            (M : ℝ) * (c : ℝ) / (L : ℝ)) / (M : ℝ) := by
      field_simp [hMreal.ne']
    rw [hrewrite, abs_div, abs_of_pos hMreal]
    exact div_le_div_of_nonneg_right (by simpa [c] using herr) hMreal.le
  have hmajor : Tendsto (fun M : ℕ ↦ (L : ℝ) / (M : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (L : ℝ)
  have habs : Tendsto
      (fun M : ℕ ↦ |({m | p m} : Set ℕ).partialDensity Set.univ M -
        (c : ℝ) / (L : ℝ)|) atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) hbound hmajor
  have hdiff : Tendsto
      (fun M : ℕ ↦ ({m | p m} : Set ℕ).partialDensity Set.univ M -
        (c : ℝ) / (L : ℝ)) atTop (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 habs
  rw [Set.HasDensity]
  simpa [c, sub_eq_add_neg, add_assoc] using
    hdiff.add_const ((c : ℝ) / (L : ℝ))

/-! ## The functions `δ_r(n)` and `δ(n)` -/

/-- The exact natural density of integers with exactly `r` divisors in `(n, 2n)`. -/
noncomputable def deltaR (r n : ℕ) : ℝ :=
  (((((Finset.range (intervalLcm n)).filter
    (fun m ↦ divisorCount n m = r)).card : ℕ) : ℝ) /
      (intervalLcm n : ℝ))

/-- The exact natural density of integers with a divisor in `(n, 2n)`. -/
noncomputable def delta (n : ℕ) : ℝ :=
  (((((Finset.range (intervalLcm n)).filter
    (fun m ↦ 0 < divisorCount n m)).card : ℕ) : ℝ) /
      (intervalLcm n : ℝ))

theorem exactDivisorSet_hasDensity (r n : ℕ) :
    (exactDivisorSet r n).HasDensity (deltaR r n) := by
  simpa [exactDivisorSet, deltaR] using
    hasDensity_of_periodic (fun m ↦ divisorCount n m = r)
      (intervalLcm n) (intervalLcm_pos n) (exactDivisorSet_periodic r n)

theorem divisorSet_hasDensity (n : ℕ) :
    (divisorSet n).HasDensity (delta n) := by
  simpa [divisorSet, delta] using
    hasDensity_of_periodic (fun m ↦ 0 < divisorCount n m)
      (intervalLcm n) (intervalLcm_pos n) (divisorSet_periodic n)

theorem exactDivisorSet_one_subset (n : ℕ) :
    exactDivisorSet 1 n ⊆ divisorSet n := by
  intro m hm
  simp only [exactDivisorSet, divisorSet, Set.mem_setOf_eq] at hm ⊢
  omega

end Erdos446
