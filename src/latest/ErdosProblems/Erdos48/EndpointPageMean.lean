/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.EndpointAggregate
import ErdosProblems.Erdos48.PageBandMonotonicity

/-!
# The Page-excluded endpoint mean

This is the finite, explicit form of the nonexceptional endpoint estimate
used by Ford--Luca--Pomerance.  Page uniqueness removes one conductor, the
amplified Gallagher density controls the middle zero bands geometrically,
and the primitive explicit formula and reciprocal-height estimate supply
the two remaining error terms.
-/

namespace Erdos48

open scoped BigOperators
open BoundedGaps.Maynard

noncomputable section

theorem exists_pageExcludedEndpointMass_explicit_bound_with_selection :
    ∃ cPage lambda₀ : ℝ,
      0 < cPage ∧ 0 < lambda₀ ∧ lambda₀ ≤ 1 / 16 ∧
      PageWindowIsQuadratic cPage ∧
      ∀ lambda : ℝ, 0 < lambda → lambda ≤ lambda₀ →
        ∃ K Camp C c : ℝ, ∃ Ke Afar : ℕ,
          0 < K ∧ 0 < C ∧ 0 < c ∧ 1 ≤ Ke ∧ 37 ≤ Afar ∧
          ∀ (Q T x J : ℕ), 3 ≤ Q → 2 ≤ T → 4 ≤ x → T ≤ x →
            let B := (Q : ℝ) * ((T : ℝ) + 2)
            let eta := lambda / Real.log B
            2 ≤ Real.log (((Q * (T + 2) : ℕ) : ℝ)) →
            20 * (K + (Real.log (Real.log (((Q * (T + 2) : ℕ) : ℝ))) + Camp + 2) +
                Real.log 2) ≤ Real.log (((Q * (T + 2) : ℕ) : ℝ)) →
            (∀ j ∈ Finset.range J,
              (((j + 2 : ℕ) : ℝ) * eta) ≤ 1 / 8) →
            c * Real.log B ≤ Real.log x / 4 →
            2 * Real.log 2 ≤ eta * Real.log x →
            1 / 2 ≤ 1 - (((J + 1 : ℕ) : ℝ) * eta) →
            ∃ m₀ : ℕ, m₀ ≤ Q ∧
              (∑ q ∈ (Finset.Ioc 1 Q).filter (fun q ↦ q ≠ m₀),
                  primitiveEndpointMass x q) ≤
                (Q : ℝ) ^ 2 *
                    ((Ke : ℝ) * dirichletExplicitFormulaErrorScale x Q T) +
                  8 * C * Real.exp
                    (c * eta * Real.log B - eta * Real.log x / 4) * x +
                  (Q : ℝ) ^ 2 *
                    (96 * (Afar : ℝ) *
                      x ^ (1 - (((J + 1 : ℕ) : ℝ) * eta)) *
                        Real.log B ^ 2) ∧
              (m₀ = 0 ∨ PageExceptionalWitness Q m₀ cPage) ∧
              PageConductorSelection Q m₀ cPage := by
  obtain ⟨cPage, lambda₀, hcPage, hlambda₀, hlambda₀Small,
      hquadratic, hPage⟩ :=
    exists_pageBand_excludedConductor_of_narrower_width_with_selection
  refine ⟨cPage, lambda₀, hcPage, hlambda₀, hlambda₀Small, hquadratic, ?_⟩
  intro lambda hlambda hlambdaLe
  obtain ⟨K, Camp, C, c, hK, hC, hc, hkernel⟩ :=
    exists_nonexcludedPrimitiveZeroKernelMass_powerDensity_bound hlambda
  obtain ⟨Ke, hKe, hendpoint⟩ :=
    exists_nat_sum_nonexcluded_primitiveEndpointMass_le
  obtain ⟨Afar, hAfar, hfar⟩ :=
    exists_nat_primitiveFarZeroKernelMass_le
  refine ⟨K, Camp, C, c, Ke, Afar, hK, hC, hc, hKe, hAfar, ?_⟩
  intro Q T x J hQ hT hx hTx
  dsimp only
  intro hlogAmp hamp hwidth hscale hcontract halpha
  let B : ℝ := (Q : ℝ) * ((T : ℝ) + 2)
  let eta : ℝ := lambda / Real.log B
  have hB : 0 < B := by dsimp [B]; positivity
  have hlogB : 0 < Real.log B := by
    apply Real.log_pos
    dsimp [B]
    have hQR : (3 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  have heta : 0 < eta := by dsimp [eta]; positivity
  have heta1 : eta < 1 := by
    have hlogBone : (1 : ℝ) ≤ Real.log B := by
      have hBlog8 : (8 : ℝ) ≤ B := by
        dsimp [B]
        have hQR : (3 : ℝ) ≤ Q := by exact_mod_cast hQ
        have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
        nlinarith
      have hlog8 : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num
      have hmono : Real.log 8 ≤ Real.log B :=
        Real.log_le_log (by norm_num) hBlog8
      nlinarith [Real.log_two_gt_d9]
    have hetaLeLambda : eta ≤ lambda := by
      dsimp [eta]
      rw [div_le_iff₀ hlogB]
      nlinarith
    exact hetaLeLambda.trans_lt (hlambdaLe.trans_lt
      (hlambda₀Small.trans_lt (by norm_num)))
  have hlower : lambda ≤ eta * Real.log B := by
    dsimp [eta]
    rw [div_mul_cancel₀ _ hlogB.ne']
  obtain ⟨m₀, hm₀Q, hpage, hwitness, hselection⟩ :=
    hPage lambda hlambda hlambdaLe Q T hQ hT
  refine ⟨m₀, hm₀Q, ?_, hwitness, hselection⟩
  have hzero := hkernel Q T (by omega) hT eta heta heta1 hlower
    hlogAmp hamp m₀ hpage x (by exact_mod_cast (show 1 ≤ x by omega))
    J hwidth hscale hcontract
  have hfarBound := hfar Q (by omega) (T : ℝ) (by exact_mod_cast hT)
    (x : ℝ) eta J (by exact_mod_cast hx) halpha
  have hendpointBound := hendpoint Q T x m₀ hT hx hTx
  calc
    (∑ q ∈ (Finset.Ioc 1 Q).filter (fun q ↦ q ≠ m₀),
        primitiveEndpointMass x q) ≤
        (Q : ℝ) ^ 2 *
            ((Ke : ℝ) * dirichletExplicitFormulaErrorScale x Q T) +
          nonexcludedPrimitiveZeroKernelMass Q m₀ x T := hendpointBound
    _ ≤ (Q : ℝ) ^ 2 *
            ((Ke : ℝ) * dirichletExplicitFormulaErrorScale x Q T) +
          (8 * C * Real.exp
              (c * eta * Real.log B - eta * Real.log x / 4) * x +
            primitiveFarZeroKernelMass Q x eta J T) := by
      gcongr
    _ ≤ (Q : ℝ) ^ 2 *
            ((Ke : ℝ) * dirichletExplicitFormulaErrorScale x Q T) +
          8 * C * Real.exp
              (c * eta * Real.log B - eta * Real.log x / 4) * x +
          (Q : ℝ) ^ 2 *
            (96 * (Afar : ℝ) *
              x ^ (1 - (((J + 1 : ℕ) : ℝ) * eta)) *
                Real.log B ^ 2) := by
      linarith
    _ = _ := by rfl

/-- Projection of the canonical Page-conductor selection which retains the
actual real-zero witness. -/
theorem exists_pageExcludedEndpointMass_explicit_bound_with_witness :
    ∃ cPage lambda₀ : ℝ,
      0 < cPage ∧ 0 < lambda₀ ∧ lambda₀ ≤ 1 / 16 ∧
      ∀ lambda : ℝ, 0 < lambda → lambda ≤ lambda₀ →
        ∃ K Camp C c : ℝ, ∃ Ke Afar : ℕ,
          0 < K ∧ 0 < C ∧ 0 < c ∧ 1 ≤ Ke ∧ 37 ≤ Afar ∧
          ∀ (Q T x J : ℕ), 3 ≤ Q → 2 ≤ T → 4 ≤ x → T ≤ x →
            let B := (Q : ℝ) * ((T : ℝ) + 2)
            let eta := lambda / Real.log B
            2 ≤ Real.log (((Q * (T + 2) : ℕ) : ℝ)) →
            20 * (K + (Real.log (Real.log (((Q * (T + 2) : ℕ) : ℝ))) + Camp + 2) +
                Real.log 2) ≤ Real.log (((Q * (T + 2) : ℕ) : ℝ)) →
            (∀ j ∈ Finset.range J,
              (((j + 2 : ℕ) : ℝ) * eta) ≤ 1 / 8) →
            c * Real.log B ≤ Real.log x / 4 →
            2 * Real.log 2 ≤ eta * Real.log x →
            1 / 2 ≤ 1 - (((J + 1 : ℕ) : ℝ) * eta) →
            ∃ m₀ : ℕ, m₀ ≤ Q ∧
              (∑ q ∈ (Finset.Ioc 1 Q).filter (fun q ↦ q ≠ m₀),
                  primitiveEndpointMass x q) ≤
                (Q : ℝ) ^ 2 *
                    ((Ke : ℝ) * dirichletExplicitFormulaErrorScale x Q T) +
                  8 * C * Real.exp
                    (c * eta * Real.log B - eta * Real.log x / 4) * x +
                  (Q : ℝ) ^ 2 *
                    (96 * (Afar : ℝ) *
                      x ^ (1 - (((J + 1 : ℕ) : ℝ) * eta)) *
                        Real.log B ^ 2) ∧
              (m₀ = 0 ∨ PageExceptionalWitness Q m₀ cPage) := by
  obtain ⟨cPage, lambda₀, hcPage, hlambda₀, hlambda₀Small,
      _hquadratic, hmain⟩ :=
    exists_pageExcludedEndpointMass_explicit_bound_with_selection
  refine ⟨cPage, lambda₀, hcPage, hlambda₀, hlambda₀Small, ?_⟩
  intro lambda hlambda hlambdaLe
  obtain ⟨K, Camp, C, c, Ke, Afar, hK, hC, hc, hKe, hAfar, hbound⟩ :=
    hmain lambda hlambda hlambdaLe
  refine ⟨K, Camp, C, c, Ke, Afar, hK, hC, hc, hKe, hAfar, ?_⟩
  intro Q T x J hQ hT hx hTx
  dsimp only
  intro hlogAmp hamp hwidth hscale hcontract halpha
  obtain ⟨m₀, hm₀, hmass, hwitness, _hselection⟩ :=
    hbound Q T x J hQ hT hx hTx hlogAmp hamp hwidth hscale hcontract halpha
  exact ⟨m₀, hm₀, hmass, hwitness⟩

/-- Backwards-compatible projection which forgets the Page-zero witness. -/
theorem exists_pageExcludedEndpointMass_explicit_bound :
    ∃ lambda₀ : ℝ, 0 < lambda₀ ∧ lambda₀ ≤ 1 / 16 ∧
      ∀ lambda : ℝ, 0 < lambda → lambda ≤ lambda₀ →
        ∃ K Camp C c : ℝ, ∃ Ke Afar : ℕ,
          0 < K ∧ 0 < C ∧ 0 < c ∧ 1 ≤ Ke ∧ 37 ≤ Afar ∧
          ∀ (Q T x J : ℕ), 3 ≤ Q → 2 ≤ T → 4 ≤ x → T ≤ x →
            let B := (Q : ℝ) * ((T : ℝ) + 2)
            let eta := lambda / Real.log B
            2 ≤ Real.log (((Q * (T + 2) : ℕ) : ℝ)) →
            20 * (K + (Real.log (Real.log (((Q * (T + 2) : ℕ) : ℝ))) + Camp + 2) +
                Real.log 2) ≤ Real.log (((Q * (T + 2) : ℕ) : ℝ)) →
            (∀ j ∈ Finset.range J,
              (((j + 2 : ℕ) : ℝ) * eta) ≤ 1 / 8) →
            c * Real.log B ≤ Real.log x / 4 →
            2 * Real.log 2 ≤ eta * Real.log x →
            1 / 2 ≤ 1 - (((J + 1 : ℕ) : ℝ) * eta) →
            ∃ m₀ : ℕ, m₀ ≤ Q ∧
              (∑ q ∈ (Finset.Ioc 1 Q).filter (fun q ↦ q ≠ m₀),
                  primitiveEndpointMass x q) ≤
                (Q : ℝ) ^ 2 *
                    ((Ke : ℝ) * dirichletExplicitFormulaErrorScale x Q T) +
                  8 * C * Real.exp
                    (c * eta * Real.log B - eta * Real.log x / 4) * x +
                  (Q : ℝ) ^ 2 *
                    (96 * (Afar : ℝ) *
                      x ^ (1 - (((J + 1 : ℕ) : ℝ) * eta)) *
                        Real.log B ^ 2) := by
  obtain ⟨_cPage, lambda₀, _hcPage, hlambda₀, hlambda₀Small, hmain⟩ :=
    exists_pageExcludedEndpointMass_explicit_bound_with_witness
  refine ⟨lambda₀, hlambda₀, hlambda₀Small, ?_⟩
  intro lambda hlambda hlambdaLe
  obtain ⟨K, Camp, C, c, Ke, Afar, hK, hC, hc, hKe, hAfar, hbound⟩ :=
    hmain lambda hlambda hlambdaLe
  refine ⟨K, Camp, C, c, Ke, Afar, hK, hC, hc, hKe, hAfar, ?_⟩
  intro Q T x J hQ hT hx hTx
  dsimp only
  intro hlogAmp hamp hwidth hscale hcontract halpha
  obtain ⟨m₀, hm₀, hmass, _hwitness⟩ :=
    hbound Q T x J hQ hT hx hTx hlogAmp hamp hwidth hscale hcontract halpha
  exact ⟨m₀, hm₀, hmass⟩

end

end Erdos48
