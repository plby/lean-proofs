/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.EndpointMass
import BoundedGaps.BombieriVinogradov.Analytic.SiegelWalfisz

/-!
# The fixed-logarithmic-conductor part of the FLP endpoint mass

The Gallagher estimate required by Ford--Luca--Pomerance has two genuinely
different conductor ranges.  This file disposes of the small range using the
already formalized Siegel--Walfisz theorem.  The result is stated for the
single endpoint mass `primitiveEndpointMass`, not for a stronger endpoint
maximum.
-/

namespace Erdos48

open scoped BigOperators
open Filter

noncomputable section

open BoundedGaps.Maynard

/-- A common pointwise envelope for primitive twists aggregates with only a
quadratic loss in the conductor cutoff. -/
theorem sum_primitiveEndpointMass_Icc_le_sq_mul
    {x M : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hpoint : ∀ q ∈ Finset.Icc 2 M, ∀ ψ : primitiveCharacters q,
      ‖twistedChebyshevSum x q ψ.1‖ ≤ B) :
    (∑ q ∈ Finset.Icc 2 M, primitiveEndpointMass x q) ≤
      (M : ℝ) ^ 2 * B := by
  have hqmass : ∀ q ∈ Finset.Icc 2 M,
      primitiveEndpointMass x q ≤ (M : ℝ) * B := by
    intro q hq
    have hqBounds := Finset.mem_Icc.mp hq
    unfold primitiveEndpointMass
    calc
      (∑ ψ : primitiveCharacters q,
          ‖twistedChebyshevSum x q ψ.1‖) ≤
          ∑ _ψ : primitiveCharacters q, B := by
        apply Finset.sum_le_sum
        intro ψ _hψ
        exact hpoint q hq ψ
      _ = (Fintype.card (primitiveCharacters q) : ℝ) * B := by simp
      _ ≤ (q : ℝ) * B := by
        apply mul_le_mul_of_nonneg_right _ hB
        exact_mod_cast
          (card_primitiveCharacters_le_totient (by omega : 0 < q)).trans
            (Nat.totient_le q)
      _ ≤ (M : ℝ) * B := by
        apply mul_le_mul_of_nonneg_right _ hB
        exact_mod_cast hqBounds.2
  calc
    (∑ q ∈ Finset.Icc 2 M, primitiveEndpointMass x q) ≤
        ∑ _q ∈ Finset.Icc 2 M, (M : ℝ) * B := by
      apply Finset.sum_le_sum
      intro q hq
      exact hqmass q hq
    _ = ((Finset.Icc 2 M).card : ℝ) * ((M : ℝ) * B) := by simp
    _ ≤ (M : ℝ) * ((M : ℝ) * B) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast (show (Finset.Icc 2 M).card ≤ M by
          rw [Nat.card_Icc]
          omega)
      · positivity
    _ = (M : ℝ) ^ 2 * B := by ring

/-- Siegel--Walfisz, summed over every primitive character and every
conductor `2 ≤ q ≤ M`.  This is the complete small-conductor contribution to
FLP's source-exact endpoint mass. -/
theorem exists_siegelWalfisz_sum_primitiveEndpointMass_Icc_le :
    ∀ D : ℝ, 0 < D →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∃ X0 : ℕ, 4 ≤ X0 ∧
          ∀ x : ℕ, X0 ≤ x →
            ∀ M : ℕ, (M : ℝ) ≤ Real.log (x : ℝ) ^ D →
              (∑ q ∈ Finset.Icc 2 M, primitiveEndpointMass x q) ≤
                (M : ℝ) ^ 2 *
                  (C * ((x : ℝ) * Real.exp
                    (-c * Real.sqrt (Real.log (x : ℝ))))) := by
  intro D hD
  obtain ⟨C, c, hC, hc, X0, hX0, hSiegelWalfisz⟩ :=
    exists_siegelWalfisz_norm_twistedChebyshevSum_le D hD
  refine ⟨C, c, hC, hc, X0, hX0, ?_⟩
  intro x hx M hM
  apply sum_primitiveEndpointMass_Icc_le_sq_mul (by positivity)
  intro q hq ψ
  have hqBounds := Finset.mem_Icc.mp hq
  letI : NeZero q := ⟨by omega⟩
  apply hSiegelWalfisz x hx q ψ.1
  · exact primitiveCharacter_ne_one_of_one_lt (by omega) ψ
  · exact (by exact_mod_cast hqBounds.2 : (q : ℝ) ≤ (M : ℝ)).trans hM

/-- A fixed real power of `log x` is absorbed by the square-root-log
exponential decay in Siegel--Walfisz. -/
private theorem tendsto_log_rpow_mul_exp_neg_sqrt_log
    (s c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℕ ↦
      Real.log (x : ℝ) ^ s *
        Real.exp (-c * Real.sqrt (Real.log (x : ℝ))))
      atTop (nhds 0) := by
  have huTop : Tendsto
      (fun x : ℕ ↦ Real.sqrt (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hcore :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * s) c hc).comp huTop
  apply hcore.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hlogNonneg : 0 ≤ Real.log (x : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hx)
  have hsqrtNonneg : 0 ≤ Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_nonneg _
  change Real.sqrt (Real.log (x : ℝ)) ^ (2 * s) *
      Real.exp (-c * Real.sqrt (Real.log (x : ℝ))) = _
  congr 1
  calc
    Real.sqrt (Real.log (x : ℝ)) ^ (2 * s) =
        (Real.sqrt (Real.log (x : ℝ)) ^ (2 : ℝ)) ^ s := by
      rw [Real.rpow_mul hsqrtNonneg]
    _ = (Real.sqrt (Real.log (x : ℝ)) ^ 2) ^ s := by
      rw [Real.rpow_two]
    _ = Real.log (x : ℝ) ^ s := by
      rw [Real.sq_sqrt hlogNonneg]

/-- Consequently, the entire fixed-logarithmic conductor range contributes
less than any prescribed positive proportion of `x`, uniformly in the
cutoff. -/
theorem eventually_sum_primitiveEndpointMass_Icc_le_mul :
    ∀ D ε : ℝ, 0 < D → 0 < ε →
      ∀ᶠ x : ℕ in atTop,
        ∀ M : ℕ, (M : ℝ) ≤ Real.log (x : ℝ) ^ D →
          (∑ q ∈ Finset.Icc 2 M, primitiveEndpointMass x q) ≤
            ε * (x : ℝ) := by
  intro D ε hD hε
  obtain ⟨C, c, hC, hc, X0, hX0, haggregate⟩ :=
    exists_siegelWalfisz_sum_primitiveEndpointMass_Icc_le D hD
  have hlim :=
    (tendsto_log_rpow_mul_exp_neg_sqrt_log (2 * D) c hc).const_mul C
  have hlim' : Tendsto (fun x : ℕ ↦
      C * (Real.log (x : ℝ) ^ (2 * D) *
        Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))))
      atTop (nhds 0) := by
    simpa using hlim
  have hsmall : ∀ᶠ x : ℕ in atTop,
      C * (Real.log (x : ℝ) ^ (2 * D) *
        Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) < ε := by
    have hnorm := NormedAddGroup.tendsto_nhds_zero.mp hlim' ε hε
    filter_upwards [hnorm, eventually_ge_atTop 1] with x hxnorm hx
    rw [Real.norm_of_nonneg] at hxnorm
    · simpa only [mul_assoc] using hxnorm
    · exact mul_nonneg hC.le
        (mul_nonneg
          (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hx)) _)
          (Real.exp_pos _).le)
  filter_upwards [eventually_ge_atTop X0, hsmall,
      eventually_ge_atTop 4] with x hxX hxsmall hxFour
  intro M hM
  have hlogPos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hlogNonneg : 0 ≤ Real.log (x : ℝ) := hlogPos.le
  have hlogPowNonneg : 0 ≤ Real.log (x : ℝ) ^ D :=
    Real.rpow_nonneg hlogNonneg _
  have hMsq : (M : ℝ) ^ 2 ≤
      (Real.log (x : ℝ) ^ D) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hM 2
  have hpowIdentity :
      (Real.log (x : ℝ) ^ D) ^ 2 =
        Real.log (x : ℝ) ^ (2 * D) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hlogNonneg]
    congr 1
    ring
  have haggregate' := haggregate x hxX M hM
  calc
    (∑ q ∈ Finset.Icc 2 M, primitiveEndpointMass x q) ≤
        (M : ℝ) ^ 2 *
          (C * ((x : ℝ) * Real.exp
            (-c * Real.sqrt (Real.log (x : ℝ))))) := haggregate'
    _ ≤ (Real.log (x : ℝ) ^ D) ^ 2 *
          (C * ((x : ℝ) * Real.exp
            (-c * Real.sqrt (Real.log (x : ℝ))))) := by
      apply mul_le_mul_of_nonneg_right hMsq
      positivity
    _ = (x : ℝ) *
        (C * (Real.log (x : ℝ) ^ (2 * D) *
          Real.exp (-c * Real.sqrt (Real.log (x : ℝ))))) := by
      rw [hpowIdentity]
      ring
    _ ≤ (x : ℝ) * ε :=
      mul_le_mul_of_nonneg_left hxsmall.le (by positivity)
    _ = ε * (x : ℝ) := by ring

end

end Erdos48
