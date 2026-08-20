/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.EndpointFarZero
import ErdosProblems.Erdos48.EndpointExplicitFormula
import ErdosProblems.Erdos48.GallagherPowerDensity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The nonexceptional FLP endpoint aggregate

This file combines Page exclusion, the amplified power-form zero-density
estimate, sharp endpoint zero kernels, and the primitive explicit formula.
The middle zero bands form a genuine geometric series; all remaining
asymptotic choices are exposed as elementary scalar inequalities.
-/

namespace Erdos48

open scoped BigOperators
open BoundedGaps.Maynard

noncomputable section

/-- One density band is dominated by a shifted geometric sequence once the
zero-density growth scale is a quarter of the endpoint scale. -/
theorem densityKernelBand_le_geometric
    {B x C c eta : ℝ} {j : ℕ}
    (hB : 0 < B) (hx : 1 ≤ x) (hC : 0 ≤ C) (heta : 0 ≤ eta)
    (hscale : c * Real.log B ≤ Real.log x / 4)
    (hcontract : 2 * Real.log 2 ≤ eta * Real.log x) :
    8 * ((C * B ^ (c * (((j + 2 : ℕ) : ℝ) * eta))) *
      x ^ (1 - (((j + 1 : ℕ) : ℝ) * eta))) ≤
        8 * C * Real.exp
          (c * eta * Real.log B - eta * Real.log x / 4) * x *
            (1 / 2 : ℝ) ^ (j + 1) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hratio : Real.exp (-(eta * Real.log x) / 2) ≤ (1 / 2 : ℝ) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2), Real.exp_le_exp]
    have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    rw [hloghalf]
    linarith
  have hratioPow :
      Real.exp (-(eta * Real.log x) / 2) ^ (j + 1) ≤
        (1 / 2 : ℝ) ^ (j + 1) := by
    exact pow_le_pow_left₀ (Real.exp_pos _).le hratio _
  have hexponent :
      Real.log B * (c * (((j + 2 : ℕ) : ℝ) * eta)) +
          Real.log x * (1 - (((j + 1 : ℕ) : ℝ) * eta)) ≤
        Real.log x +
          (c * eta * Real.log B - eta * Real.log x / 4) +
            ((j + 1 : ℕ) : ℝ) * (-(eta * Real.log x) / 2) := by
    have hj : (0 : ℝ) ≤ (j + 1 : ℕ) := by positivity
    have hm := mul_le_mul_of_nonneg_left hscale (mul_nonneg hj heta)
    have hj0 : (0 : ℝ) ≤ j := by positivity
    have hnonneg : 0 ≤ (j : ℝ) * eta * Real.log x := by positivity
    have hm' :
        c * eta * Real.log B * ((j + 1 : ℕ) : ℝ) ≤
          ((j + 1 : ℕ) : ℝ) * eta * Real.log x / 2 -
            eta * Real.log x / 4 := by
      calc
        c * eta * Real.log B * ((j + 1 : ℕ) : ℝ) =
            ((j + 1 : ℕ) : ℝ) * eta * (c * Real.log B) := by ring
        _ ≤ ((j + 1 : ℕ) : ℝ) * eta * (Real.log x / 4) := hm
        _ ≤ ((j + 1 : ℕ) : ℝ) * eta * Real.log x / 2 -
            eta * Real.log x / 4 := by
          push_cast
          nlinarith [hnonneg]
    push_cast at hm' ⊢
    nlinarith [hm']
  rw [Real.rpow_def_of_pos hB, Real.rpow_def_of_pos hxpos]
  have hexp := Real.exp_le_exp.mpr hexponent
  have hrearrange :
      Real.exp (Real.log x +
          (c * eta * Real.log B - eta * Real.log x / 4) +
            ((j + 1 : ℕ) : ℝ) * (-(eta * Real.log x) / 2)) =
        x * Real.exp
          (c * eta * Real.log B - eta * Real.log x / 4) *
            Real.exp (-(eta * Real.log x) / 2) ^ (j + 1) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log hxpos, Real.exp_nat_mul]
  rw [hrearrange] at hexp
  calc
    8 * ((C * Real.exp
          (Real.log B * (c * (((j + 2 : ℕ) : ℝ) * eta)))) *
        Real.exp (Real.log x *
          (1 - (((j + 1 : ℕ) : ℝ) * eta)))) =
        8 * C * Real.exp
          (Real.log B * (c * (((j + 2 : ℕ) : ℝ) * eta)) +
            Real.log x * (1 - (((j + 1 : ℕ) : ℝ) * eta))) := by
      rw [Real.exp_add]
      ring
    _ ≤
        8 * C * (x * Real.exp
          (c * eta * Real.log B - eta * Real.log x / 4) *
            Real.exp (-(eta * Real.log x) / 2) ^ (j + 1)) := by
      exact mul_le_mul_of_nonneg_left hexp (mul_nonneg (by norm_num) hC)
    _ ≤ 8 * C * (x * Real.exp
          (c * eta * Real.log B - eta * Real.log x / 4) *
            (1 / 2 : ℝ) ^ (j + 1)) := by
      gcongr
    _ = _ := by ring

/-- The sharp middle-band estimate summed with the power-form density
bound.  All asymptotic choices have been reduced to two scalar inequalities. -/
theorem nonexcludedPrimitiveZeroKernelMass_le_powerDensity_geometric_add_far
    {Q T : ℕ} {B x C c eta : ℝ} {m₀ : ℕ}
    (hpage : ∀ d ∈ Finset.Ioc 1 Q, d ≠ m₀ →
      ∀ psi : primitiveCharacters d,
        primitiveHighZeroMassAt d psi eta T = 0)
    (hB : 0 < B) (hx : 1 ≤ x) (hC : 0 ≤ C)
    (heta : 0 < eta) (heta1 : eta < 1)
    (J : ℕ)
    (hwidth : ∀ j ∈ Finset.range J,
      (((j + 2 : ℕ) : ℝ) * eta) ≤ 1 / 8)
    (hdensity : ∀ j ∈ Finset.range J,
      (primitiveHighZeroMass Q
        (((j + 2 : ℕ) : ℝ) * eta) T : ℝ) ≤
          C * B ^ (c * (((j + 2 : ℕ) : ℝ) * eta)))
    (hscale : c * Real.log B ≤ Real.log x / 4)
    (hcontract : 2 * Real.log 2 ≤ eta * Real.log x) :
    nonexcludedPrimitiveZeroKernelMass Q m₀ x T ≤
      8 * C * Real.exp
          (c * eta * Real.log B - eta * Real.log x / 4) * x +
        primitiveFarZeroKernelMass Q x eta J T := by
  have hdecomp :=
    nonexcludedPrimitiveZeroKernelMass_le_sharpDensityBands_add_far
      hpage hx heta (by linarith) J
        (fun j hj ↦ (hwidth j hj).trans (by norm_num))
  apply hdecomp.trans
  apply add_le_add
  · calc
    (∑ j ∈ Finset.range J,
        8 * ((primitiveHighZeroMass Q
            (((j + 2 : ℕ) : ℝ) * eta) T : ℝ) *
          x ^ (1 - (((j + 1 : ℕ) : ℝ) * eta)))) ≤
      ∑ j ∈ Finset.range J,
        8 * ((C * B ^ (c * (((j + 2 : ℕ) : ℝ) * eta))) *
          x ^ (1 - (((j + 1 : ℕ) : ℝ) * eta))) := by
        apply Finset.sum_le_sum
        intro j hj
        gcongr
        exact hdensity j hj
    _ ≤ ∑ j ∈ Finset.range J,
        (8 * C * Real.exp
          (c * eta * Real.log B - eta * Real.log x / 4) * x) *
            (1 / 2 : ℝ) ^ (j + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [mul_assoc] using densityKernelBand_le_geometric
        hB hx hC heta.le hscale hcontract (j := j)
    _ ≤ (8 * C * Real.exp
          (c * eta * Real.log B - eta * Real.log x / 4) * x) * 1 := by
      let A : ℝ := 8 * C * Real.exp
        (c * eta * Real.log B - eta * Real.log x / 4) * x
      change (∑ j ∈ Finset.range J, A * (1 / 2 : ℝ) ^ (j + 1)) ≤ A * 1
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [show (∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ (j + 1)) =
          (1 / 2 : ℝ) * ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [pow_succ']]
      nlinarith [sum_geometric_two_le J]
    _ = _ := by ring
  · exact le_rfl

/-- The amplified Gallagher theorem inserted into the geometric endpoint
summation.  The remaining assumptions are elementary scale inequalities and
the Page-band exclusion. -/
theorem exists_nonexcludedPrimitiveZeroKernelMass_powerDensity_bound
    {lambda : ℝ} (hlambda : 0 < lambda) :
    ∃ K Camp C c : ℝ, 0 < K ∧ 0 < C ∧ 0 < c ∧
      ∀ (Q T : ℕ), 2 ≤ Q → 2 ≤ T →
        ∀ (eta : ℝ), 0 < eta → eta < 1 →
          let B := (Q : ℝ) * ((T : ℝ) + 2)
          lambda ≤ eta * Real.log B →
          let Amp := Q * (T + 2)
          2 ≤ Real.log Amp →
          20 * (K + (Real.log (Real.log Amp) + Camp + 2) + Real.log 2) ≤
            Real.log Amp →
          ∀ (m₀ : ℕ),
            (∀ d ∈ Finset.Ioc 1 Q, d ≠ m₀ →
              ∀ psi : primitiveCharacters d,
                primitiveHighZeroMassAt d psi eta T = 0) →
            ∀ (x : ℝ), 1 ≤ x →
              ∀ J : ℕ,
                (∀ j ∈ Finset.range J,
                  (((j + 2 : ℕ) : ℝ) * eta) ≤ 1 / 8) →
                c * Real.log B ≤ Real.log x / 4 →
                2 * Real.log 2 ≤ eta * Real.log x →
                nonexcludedPrimitiveZeroKernelMass Q m₀ x T ≤
                  8 * C * Real.exp
                      (c * eta * Real.log B - eta * Real.log x / 4) * x +
                    primitiveFarZeroKernelMass Q x eta J T := by
  obtain ⟨K, Camp, C, c, hK, hC, hc, hdensity⟩ :=
    exists_gallagher_logFreeDensity_power_bound hlambda
  refine ⟨K, Camp, C, c, hK, hC, hc, ?_⟩
  intro Q T hQ hT eta heta heta1
  dsimp only
  intro hlower hlogAmp hamp m₀ hpage x hx J hwidth hscale hcontract
  let B : ℝ := (Q : ℝ) * ((T : ℝ) + 2)
  have hB : 0 < B := by dsimp [B]; positivity
  apply nonexcludedPrimitiveZeroKernelMass_le_powerDensity_geometric_add_far
    hpage hB hx hC.le heta heta1 J hwidth
  · intro j hj
    let etaJ : ℝ := (((j + 2 : ℕ) : ℝ) * eta)
    have hetaJ : 0 < etaJ := by dsimp [etaJ]; positivity
    have hetaJ8 : etaJ ≤ 1 / 8 := by
      simpa only [etaJ] using hwidth j hj
    have hlogB : 0 < Real.log B := by
      apply Real.log_pos
      dsimp [B]
      have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
      have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
      nlinarith
    have hmult : eta * Real.log B ≤ etaJ * Real.log B := by
      apply mul_le_mul_of_nonneg_right _ hlogB.le
      dsimp [etaJ]
      have hjOne : (1 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ j + 2 by omega)
      nlinarith
    have hlowerJ : lambda ≤ etaJ * Real.log B := hlower.trans hmult
    simpa only [B, etaJ] using
      hdensity Q T hQ hT etaJ hetaJ hetaJ8 hlowerJ hlogAmp hamp
  · simpa only [B] using hscale
  · simpa only [B] using hcontract

/-- Summing the primitive explicit formula outside one conductor costs only
`Q²` copies of the common endpoint error, plus the zero-kernel mass already
controlled above. -/
theorem exists_nat_sum_nonexcluded_primitiveEndpointMass_le :
    ∃ K : ℕ, 1 ≤ K ∧
      ∀ (Q T x m₀ : ℕ), 2 ≤ T → 4 ≤ x → T ≤ x →
        (∑ q ∈ (Finset.Ioc 1 Q).filter (fun q ↦ q ≠ m₀),
            primitiveEndpointMass x q) ≤
          (Q : ℝ) ^ 2 *
              ((K : ℝ) * dirichletExplicitFormulaErrorScale x Q T) +
            nonexcludedPrimitiveZeroKernelMass Q m₀ x T := by
  obtain ⟨K, hK, hpoint⟩ :=
    exists_nat_primitiveEndpointMass_le_card_mul_error_add_zeroKernelMass
  refine ⟨K, hK, ?_⟩
  intro Q T x m₀ hT hx hTx
  let S := (Finset.Ioc 1 Q).filter (fun q ↦ q ≠ m₀)
  let E : ℝ := (K : ℝ) * dirichletExplicitFormulaErrorScale x Q T
  have hE : 0 ≤ E := by
    dsimp [E, dirichletExplicitFormulaErrorScale]
    positivity
  have herror (q : ℕ) (hq : q ∈ S) :
      (K : ℝ) * dirichletExplicitFormulaErrorScale x q T ≤ E := by
    have hqData := Finset.mem_filter.mp hq
    have hqBounds := Finset.mem_Ioc.mp hqData.1
    have hxR : (0 : ℝ) < x := by positivity
    have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hQR : (0 : ℝ) < Q := by
      exact_mod_cast (show 0 < Q by omega)
    have hprod : (x : ℝ) * q ≤ (x : ℝ) * Q := by
      gcongr
      exact hqBounds.2
    have hlog := Real.log_le_log (mul_pos hxR hqR) hprod
    have hlog0 : 0 ≤ Real.log ((x : ℝ) * q) := by
      apply Real.log_nonneg
      have hxOne : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
      have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
      nlinarith
    have hlogSq : Real.log ((x : ℝ) * q) ^ 2 ≤
        Real.log ((x : ℝ) * Q) ^ 2 := by
      nlinarith [sq_nonneg (Real.log ((x : ℝ) * Q) -
        Real.log ((x : ℝ) * q))]
    dsimp [E, dirichletExplicitFormulaErrorScale]
    gcongr
  have hmass (q : ℕ) (hq : q ∈ S) :
      primitiveEndpointMass x q ≤
        (Q : ℝ) * E +
          ∑ psi : primitiveCharacters q,
            ‖primitiveZeroKernelSumAt q psi x T‖ := by
    have hqData := Finset.mem_filter.mp hq
    have hqBounds := Finset.mem_Ioc.mp hqData.1
    have hqOne : 1 < q := hqBounds.1
    have hbase := hpoint q hqOne T (by exact_mod_cast hT) x hx
      (by exact_mod_cast hTx)
    have hzero := primitiveZeroKernelMass_eq_sum_norm_primitiveZeroKernelSumAt
      x hqOne T
    rw [hzero] at hbase
    calc
      primitiveEndpointMass x q ≤
          (Fintype.card (primitiveCharacters q) : ℝ) *
              ((K : ℝ) * dirichletExplicitFormulaErrorScale x q T) +
            ∑ psi : primitiveCharacters q,
              ‖primitiveZeroKernelSumAt q psi x T‖ := hbase
      _ ≤ (Q : ℝ) * E +
            ∑ psi : primitiveCharacters q,
              ‖primitiveZeroKernelSumAt q psi x T‖ := by
        have hcard : (Fintype.card (primitiveCharacters q) : ℝ) ≤ Q := by
          exact_mod_cast
            (card_primitiveCharacters_le_totient (by omega : 0 < q)).trans
              ((Nat.totient_le q).trans hqBounds.2)
        have hprod :
            (Fintype.card (primitiveCharacters q) : ℝ) *
                ((K : ℝ) * dirichletExplicitFormulaErrorScale x q T) ≤
              (Q : ℝ) * E := by
          calc
          (Fintype.card (primitiveCharacters q) : ℝ) *
              ((K : ℝ) * dirichletExplicitFormulaErrorScale x q T) ≤
            (Q : ℝ) *
              ((K : ℝ) * dirichletExplicitFormulaErrorScale x q T) :=
            mul_le_mul_of_nonneg_right hcard (by
              dsimp [dirichletExplicitFormulaErrorScale]
              positivity)
          _ ≤ (Q : ℝ) * E :=
            mul_le_mul_of_nonneg_left (herror q hq) (by positivity)
        exact add_le_add hprod le_rfl
  unfold nonexcludedPrimitiveZeroKernelMass
  change (∑ q ∈ S, primitiveEndpointMass x q) ≤ _
  calc
    (∑ q ∈ S, primitiveEndpointMass x q) ≤
        ∑ q ∈ S, ((Q : ℝ) * E +
          ∑ psi : primitiveCharacters q,
            ‖primitiveZeroKernelSumAt q psi x T‖) := by
      exact Finset.sum_le_sum hmass
    _ = ((S.card : ℕ) : ℝ) * ((Q : ℝ) * E) +
        ∑ q ∈ S, ∑ psi : primitiveCharacters q,
          ‖primitiveZeroKernelSumAt q psi x T‖ := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ (Q : ℝ) * ((Q : ℝ) * E) +
        ∑ q ∈ S, ∑ psi : primitiveCharacters q,
          ‖primitiveZeroKernelSumAt q psi x T‖ := by
      gcongr
      exact_mod_cast (show S.card ≤ Q by
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp))
    _ = (Q : ℝ) ^ 2 *
          ((K : ℝ) * dirichletExplicitFormulaErrorScale x Q T) +
        ∑ q ∈ S, ∑ psi : primitiveCharacters q,
          ‖primitiveZeroKernelSumAt q psi x T‖ := by
      dsimp [E]
      ring

end

end Erdos48
