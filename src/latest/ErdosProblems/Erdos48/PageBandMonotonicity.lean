/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PageExcludedConductor

/-!
# Monotonicity of the Page zero band

Shrinking the real-width of a high-zero rectangle can only decrease its
analytic multiplicity.  Consequently the one conductor excluded by Page's
theorem at a fixed width also excludes every narrower positive width.  This
parameterized form is used to make the final endpoint error arbitrarily
small.
-/

namespace Erdos48

open Complex
open BoundedGaps.Maynard

noncomputable section

theorem highZeroRectangle_mono_width
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {etaSmall etaLarge T : ℝ} (heta : etaSmall ≤ etaLarge)
    (hetaLarge : etaLarge ≤ 1) (hT : 0 ≤ T) :
    highZeroRectangle hq chi hchi etaSmall T ⊆
      highZeroRectangle hq chi hchi etaLarge T := by
  intro rho hrho
  have hsmall :=
    (mem_highZeroRectangle_iff hq chi hchi (heta.trans hetaLarge) hT rho).mp hrho
  exact (mem_highZeroRectangle_iff hq chi hchi hetaLarge hT rho).mpr
    ⟨hsmall.1, by linarith [hsmall.2.1], hsmall.2.2⟩

theorem highZeroRectangleMass_mono_width
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {etaSmall etaLarge T : ℝ} (heta : etaSmall ≤ etaLarge)
    (hetaLarge : etaLarge ≤ 1) (hT : 0 ≤ T) :
    highZeroRectangleMass hq chi hchi etaSmall T ≤
      highZeroRectangleMass hq chi hchi etaLarge T := by
  unfold highZeroRectangleMass
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (highZeroRectangle_mono_width hq chi hchi heta hetaLarge hT)
    (fun _ _ _ ↦ Nat.zero_le _)

theorem primitiveHighZeroMassAt_mono_width
    {q : ℕ} (psi : primitiveCharacters q)
    {etaSmall etaLarge T : ℝ} (heta : etaSmall ≤ etaLarge)
    (hetaLarge : etaLarge ≤ 1) (hT : 0 ≤ T) :
    primitiveHighZeroMassAt q psi etaSmall T ≤
      primitiveHighZeroMassAt q psi etaLarge T := by
  by_cases hq : 1 < q
  · letI : NeZero q := ⟨by omega⟩
    rw [primitiveHighZeroMassAt_eq hq, primitiveHighZeroMassAt_eq hq]
    exact highZeroRectangleMass_mono_width hq psi.1 psi.2 heta hetaLarge hT
  · simp only [primitiveHighZeroMassAt, dif_neg hq]
    exact le_rfl

theorem exists_pageBand_excludedConductor_of_narrower_width_with_selection :
    ∃ cPage lambda₀ : ℝ,
      0 < cPage ∧ 0 < lambda₀ ∧ lambda₀ ≤ 1 / 16 ∧
      PageWindowIsQuadratic cPage ∧
      ∀ lambda : ℝ, 0 < lambda → lambda ≤ lambda₀ →
        ∀ (Q T : ℕ), 3 ≤ Q → 2 ≤ T →
          let B := (Q : ℝ) * ((T : ℝ) + 2)
          let eta := lambda / Real.log B
          ∃ m₀ : ℕ, m₀ ≤ Q ∧
            (∀ q ∈ Finset.Ioc 1 Q, q ≠ m₀ →
                ∀ psi : primitiveCharacters q,
                  primitiveHighZeroMassAt q psi eta T = 0) ∧
            (m₀ = 0 ∨ PageExceptionalWitness Q m₀ cPage) ∧
            PageConductorSelection Q m₀ cPage := by
  obtain ⟨cPage, lambda₀, hcPage, hlambda₀, hlambda₀Small,
      hquadratic, hPage⟩ :=
    exists_pageBand_excludedConductor_with_selection
  refine ⟨cPage, lambda₀, hcPage, hlambda₀, hlambda₀Small, hquadratic, ?_⟩
  intro lambda hlambda hlambdaLe Q T hQ hT
  dsimp only
  let B : ℝ := (Q : ℝ) * ((T : ℝ) + 2)
  have hB : (1 : ℝ) < B := by
    dsimp [B]
    have hQR : (3 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have hetaLe : lambda / Real.log B ≤ lambda₀ / Real.log B := by
    exact div_le_div_of_nonneg_right hlambdaLe hlogB.le
  have heta₀One : lambda₀ / Real.log B ≤ 1 := by
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
    rw [div_le_iff₀ hlogB]
    nlinarith
  obtain ⟨m₀, hm₀Q, hm₀, hwitness, hselection⟩ := hPage Q T hQ hT
  refine ⟨m₀, hm₀Q, ?_, hwitness, hselection⟩
  intro q hqMem hqNe psi
  have hzero : primitiveHighZeroMassAt q psi
      (lambda₀ / Real.log B) T = 0 := by
    simpa only [B] using hm₀ q hqMem hqNe psi
  have hmono := primitiveHighZeroMassAt_mono_width psi hetaLe heta₀One
    (by positivity : (0 : ℝ) ≤ T)
  have hsmall : primitiveHighZeroMassAt q psi
      (lambda / Real.log B) T = 0 := Nat.eq_zero_of_le_zero (hmono.trans_eq hzero)
  simpa only [B] using hsmall

/-- Projection of the canonical selection theorem which retains the actual
Page-window witness. -/
theorem exists_pageBand_excludedConductor_of_narrower_width_with_witness :
    ∃ cPage lambda₀ : ℝ,
      0 < cPage ∧ 0 < lambda₀ ∧ lambda₀ ≤ 1 / 16 ∧
      ∀ lambda : ℝ, 0 < lambda → lambda ≤ lambda₀ →
        ∀ (Q T : ℕ), 3 ≤ Q → 2 ≤ T →
          let B := (Q : ℝ) * ((T : ℝ) + 2)
          let eta := lambda / Real.log B
          ∃ m₀ : ℕ, m₀ ≤ Q ∧
            (∀ q ∈ Finset.Ioc 1 Q, q ≠ m₀ →
                ∀ psi : primitiveCharacters q,
                  primitiveHighZeroMassAt q psi eta T = 0) ∧
            (m₀ = 0 ∨ PageExceptionalWitness Q m₀ cPage) := by
  obtain ⟨cPage, lambda₀, hcPage, hlambda₀, hlambda₀Small,
      _hquadratic, hmain⟩ :=
    exists_pageBand_excludedConductor_of_narrower_width_with_selection
  refine ⟨cPage, lambda₀, hcPage, hlambda₀, hlambda₀Small, ?_⟩
  intro lambda hlambda hlambdaLe Q T hQ hT
  obtain ⟨m₀, hm₀, hzero, hwitness, _hselection⟩ :=
    hmain lambda hlambda hlambdaLe Q T hQ hT
  exact ⟨m₀, hm₀, hzero, hwitness⟩

/-- Backwards-compatible projection which forgets the Page-zero witness. -/
theorem exists_pageBand_excludedConductor_of_narrower_width :
    ∃ lambda₀ : ℝ, 0 < lambda₀ ∧ lambda₀ ≤ 1 / 16 ∧
      ∀ lambda : ℝ, 0 < lambda → lambda ≤ lambda₀ →
        ∀ (Q T : ℕ), 3 ≤ Q → 2 ≤ T →
          let B := (Q : ℝ) * ((T : ℝ) + 2)
          let eta := lambda / Real.log B
          ∃ m₀ : ℕ, m₀ ≤ Q ∧
            ∀ q ∈ Finset.Ioc 1 Q, q ≠ m₀ →
              ∀ psi : primitiveCharacters q,
                primitiveHighZeroMassAt q psi eta T = 0 := by
  obtain ⟨_cPage, lambda₀, _hcPage, hlambda₀, hlambda₀Small, hmain⟩ :=
    exists_pageBand_excludedConductor_of_narrower_width_with_witness
  refine ⟨lambda₀, hlambda₀, hlambda₀Small, ?_⟩
  intro lambda hlambda hlambdaLe Q T hQ hT
  obtain ⟨m₀, hm₀, hzero, _hwitness⟩ :=
    hmain lambda hlambda hlambdaLe Q T hQ hT
  exact ⟨m₀, hm₀, hzero⟩

end

end Erdos48
