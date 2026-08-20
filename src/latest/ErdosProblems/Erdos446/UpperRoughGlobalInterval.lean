/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperRoughUniformEnvelope
import ErdosProblems.Erdos446.External.Erdos69.RoughSelberg

/-!
# Erdős Problem 446: a uniform one-dimensional rough interval bound

The beta-sieve estimate for rough integers has a fixed-power endpoint term.
For ranges longer than that fixed power, the endpoint is absorbed by the
main scale `U / log z`.  For shorter ranges, the polynomial rough-harmonic
envelope proved in `UpperRoughUniformEnvelope` supplies the same bound.

This gives an unconditional, all-endpoint upper bound for the rough
intervals occurring after Ford's largest-prime-factor decomposition.
-/

namespace Erdos446

open Finset Real

/-- Every positive `p`-rough integer at most `U` is counted by the
`(p - 1)`-rough initial segment used by the beta sieve. -/
theorem roughPositiveIoc_subset_roughNumbers_pred
    {p A U : ℕ} :
    Erdos387.RoughHarmonic.roughPositiveIoc p A U ⊆
      Erdos69.roughNumbers (p - 1) U := by
  classical
  intro m hm
  rw [Erdos387.RoughHarmonic.mem_roughPositiveIoc] at hm
  rw [Erdos69.roughNumbers, Finset.mem_filter, Finset.mem_Icc]
  have hmPos : 0 < m := (Nat.zero_le A).trans_lt hm.1
  refine ⟨⟨hmPos, hm.2.1⟩, ?_⟩
  intro q hq hqp hqm
  have hpPos : 0 < p := by
    have hqTwo := hq.two_le
    omega
  exact hm.2.2 q hq ((Nat.le_sub_one_iff_lt hpPos).mp hqp) hqm

/-- The cardinality of a rough interval is trivially at most its upper
endpoint.  This handles the finite set of small roughness thresholds. -/
theorem card_roughPositiveIoc_le_upper (p A U : ℕ) :
    (Erdos387.RoughHarmonic.roughPositiveIoc p A U).card ≤ U := by
  classical
  unfold Erdos387.RoughHarmonic.roughPositiveIoc
  calc
    ((Finset.Ioc A U).filter (Erdos387.IsZRough p)).card ≤
        (Finset.Ioc A U).card := Finset.card_filter_le _ _
    _ ≤ U := by simp

/-- Uniform, endpoint-free upper-bound sieve for a one-dimensional rough
interval.  The constant is absolute and the result holds for every
roughness threshold `p ≥ 2` and every interval `(A,U]` with `A ≥ 1`. -/
theorem exists_uniform_roughPositiveIoc_card_le_div_log :
    ∃ B : ℝ, 0 < B ∧ ∀ (p A U : ℕ), 2 ≤ p → 1 ≤ A →
      ((Erdos387.RoughHarmonic.roughPositiveIoc p A U).card : ℝ) ≤
        B * (U : ℝ) / Real.log p := by
  obtain ⟨Cshort, hCshort, N, hshort⟩ :=
    exists_uniform_roughCount_le_polynomial
  obtain ⟨Bbeta, S, hBbeta, hS, hbeta⟩ :=
    Erdos69.RoughSelberg.exists_roughNumbers_log_upper_bound
  let M : ℕ := max N 4
  let B : ℝ :=
    Cshort * ((2 * S + 1 : ℕ) : ℝ) + 2 * Bbeta + Real.log M + 1
  have hMfour : 4 ≤ M := by simp [M]
  have hMN : N ≤ M := by simp [M]
  have hlogM : 0 < Real.log (M : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < M by omega)
  have hB : 0 < B := by
    dsimp [B]
    have hshortNonneg :
        0 ≤ Cshort * ((2 * S + 1 : ℕ) : ℝ) := by positivity
    have hbetaNonneg : 0 ≤ 2 * Bbeta := by positivity
    linarith
  refine ⟨B, hB, ?_⟩
  intro p A U hp hA
  have hlogp : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < p by omega)
  by_cases hpM : M ≤ p
  · have hpN : N ≤ p := hMN.trans hpM
    have hpFour : 4 ≤ p := hMfour.trans hpM
    by_cases hshortRange : U ≤ p ^ (2 * S + 1)
    · have hquotient : U / p ≤ p ^ (2 * S) := by
        apply Nat.div_le_of_le_mul
        simpa only [pow_succ, Nat.mul_comm] using hshortRange
      have hbase := hshort p A U (2 * S) hpN hp hA hquotient
      have hcoeff :
          Cshort * ((2 * S + 1 : ℕ) : ℝ) ≤ B := by
        dsimp [B]
        have hbetaNonneg : 0 ≤ 2 * Bbeta := by positivity
        linarith
      exact hbase.trans (by
        apply (div_le_div_iff_of_pos_right hlogp).2
        exact mul_le_mul_of_nonneg_right hcoeff (by positivity))
    · have hpPred : 3 ≤ p - 1 := by omega
      have hsubsetCard :
          ((Erdos387.RoughHarmonic.roughPositiveIoc p A U).card : ℝ) ≤
            ((Erdos69.roughNumbers (p - 1) U).card : ℝ) := by
        exact_mod_cast Finset.card_le_card
          (roughPositiveIoc_subset_roughNumbers_pred (p := p) (A := A) (U := U))
      have hbetaBase := hbeta U (p - 1) hpPred
      have hpredPos : (0 : ℝ) < (p - 1 : ℕ) := by positivity
      have hlogPred : 0 < Real.log (p - 1 : ℕ) := by
        apply Real.log_pos
        exact_mod_cast (show 1 < p - 1 by omega)
      have hpLePredSq : p ≤ (p - 1) ^ 2 := by
        calc
          p = (p - 1) + 1 := by omega
          _ ≤ (p - 1) ^ 2 := by nlinarith [hpPred]
      have hlogCompare :
          Real.log (p : ℝ) ≤ 2 * Real.log (p - 1 : ℕ) := by
        have hcast : (p : ℝ) ≤ ((p - 1 : ℕ) : ℝ) ^ 2 := by
          exact_mod_cast hpLePredSq
        have hlog := Real.log_le_log (by positivity) hcast
        rw [Real.log_pow] at hlog
        norm_num at hlog ⊢
        exact hlog
      have hmain :
          Bbeta * (U : ℝ) / Real.log (p - 1 : ℕ) ≤
            (2 * Bbeta) * (U : ℝ) / Real.log p := by
        apply (div_le_div_iff₀ hlogPred hlogp).2
        calc
          (Bbeta * (U : ℝ)) * Real.log p ≤
              (Bbeta * (U : ℝ)) *
                (2 * Real.log (p - 1 : ℕ)) :=
            mul_le_mul_of_nonneg_left hlogCompare (by positivity)
          _ = ((2 * Bbeta) * (U : ℝ)) *
                Real.log (p - 1 : ℕ) := by ring
      have hpowNat : ((p - 1) ^ S) ^ 2 ≤ p ^ (2 * S) := by
        calc
          ((p - 1) ^ S) ^ 2 ≤ (p ^ S) ^ 2 := by gcongr <;> omega
          _ = p ^ (2 * S) := by
            rw [← pow_mul]
            congr 1
            omega
      have hpow : ((((p - 1) ^ S : ℕ) : ℝ) ^ 2) ≤
          ((p ^ (2 * S) : ℕ) : ℝ) := by
        exact_mod_cast hpowNat
      have hlogLeP : Real.log (p : ℝ) ≤ (p : ℝ) := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < p by positivity)
        linarith
      have hlongNat : p ^ (2 * S + 1) ≤ U := by omega
      have hendpointMul :
          ((((p - 1) ^ S : ℕ) : ℝ) ^ 2) * Real.log p ≤ (U : ℝ) := by
        calc
          ((((p - 1) ^ S : ℕ) : ℝ) ^ 2) * Real.log p ≤
              ((p ^ (2 * S) : ℕ) : ℝ) * Real.log p :=
            mul_le_mul_of_nonneg_right hpow hlogp.le
          _ ≤ ((p ^ (2 * S) : ℕ) : ℝ) * (p : ℝ) :=
            mul_le_mul_of_nonneg_left hlogLeP (by positivity)
          _ = ((p ^ (2 * S + 1) : ℕ) : ℝ) := by
            rw [pow_succ]
            norm_num
          _ ≤ (U : ℝ) := by exact_mod_cast hlongNat
      have hendpoint : ((((p - 1) ^ S : ℕ) : ℝ) ^ 2) ≤
          (U : ℝ) / Real.log p := by
        exact (le_div_iff₀ hlogp).2 hendpointMul
      have hcombined :
          ((Erdos387.RoughHarmonic.roughPositiveIoc p A U).card : ℝ) ≤
            (2 * Bbeta + 1) * (U : ℝ) / Real.log p := by
        calc
          ((Erdos387.RoughHarmonic.roughPositiveIoc p A U).card : ℝ) ≤
              ((Erdos69.roughNumbers (p - 1) U).card : ℝ) := hsubsetCard
          _ ≤ Bbeta * (U : ℝ) / Real.log (p - 1 : ℕ) +
                ((((p - 1) ^ S : ℕ) : ℝ) ^ 2) := hbetaBase
          _ ≤ (2 * Bbeta) * (U : ℝ) / Real.log p +
                (U : ℝ) / Real.log p := add_le_add hmain hendpoint
          _ = (2 * Bbeta + 1) * (U : ℝ) / Real.log p := by ring
      have hcoeff : 2 * Bbeta + 1 ≤ B := by
        dsimp [B]
        have hshortNonneg :
            0 ≤ Cshort * ((2 * S + 1 : ℕ) : ℝ) := by positivity
        linarith
      exact hcombined.trans (by
        apply (div_le_div_iff_of_pos_right hlogp).2
        exact mul_le_mul_of_nonneg_right hcoeff (by positivity))
  · have hpLtM : p ≤ M := by omega
    have hcard :
        ((Erdos387.RoughHarmonic.roughPositiveIoc p A U).card : ℝ) ≤
          (U : ℝ) := by
      exact_mod_cast card_roughPositiveIoc_le_upper p A U
    have hlogCompare : Real.log (p : ℝ) ≤ Real.log (M : ℝ) := by
      exact Real.log_le_log (by positivity) (by exact_mod_cast hpLtM)
    have hscale : (U : ℝ) ≤ Real.log M * (U : ℝ) / Real.log p := by
      apply (le_div_iff₀ hlogp).2
      nlinarith [show (0 : ℝ) ≤ U by positivity]
    have hcoeff : Real.log M ≤ B := by
      dsimp [B]
      have hshortNonneg :
          0 ≤ Cshort * ((2 * S + 1 : ℕ) : ℝ) := by positivity
      have hbetaNonneg : 0 ≤ 2 * Bbeta := by positivity
      linarith
    exact hcard.trans (hscale.trans (by
      apply (div_le_div_iff_of_pos_right hlogp).2
      exact mul_le_mul_of_nonneg_right hcoeff (by positivity)))

end Erdos446
