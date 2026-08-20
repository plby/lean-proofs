/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.Page
import ErdosProblems.Erdos48.VariableLogFreeDensity
import BoundedGaps.BombieriVinogradov.Analytic.RawPrimitiveMaxima

/-!
# Removing the unique Page conductor

At the logarithmic width used by the variable-order density estimate, every
zero in the innermost rectangle is real.  Page uniqueness therefore places
all such zeros at a single conductor, which may simply be omitted in the
later averaging argument.
-/

namespace Erdos48

open Complex
open BoundedGaps.Maynard

noncomputable section

/-- An actual primitive real zero at conductor `m`, in the Page window of
width `c` at scale `Q`. -/
def PageExceptionalWitness (Q m : ℕ) (c : ℝ) : Prop :=
  ∃ z : PrimitiveRealZero, z.modulus = m ∧ InPageWindow Q c z

/-- The excluded conductor is selected canonically from the whole Page
window: every zero in that window has this conductor, and `0` is used
exactly when the window is empty. -/
def PageConductorSelection (Q m : ℕ) (c : ℝ) : Prop :=
  (∀ z : PrimitiveRealZero, InPageWindow Q c z → z.modulus = m) ∧
    (m = 0 ↔ ¬ ∃ z : PrimitiveRealZero, InPageWindow Q c z)

/-- Every real zero in a sufficiently narrow Page window belongs to a
quadratic character.  Keeping this fact with the chosen width lets later
arguments apply the effective quadratic real-zero gap to the retained
witness without making a second, unrelated choice of width. -/
def PageWindowIsQuadratic (c : ℝ) : Prop :=
  ∀ (Q : ℕ), 3 ≤ Q → ∀ z : PrimitiveRealZero,
    InPageWindow Q c z → z.character ^ 2 = 1

/-- There is a fixed Page-band width for which, at every conductor-height
box, all primitive zeros in the innermost rectangle have one common
conductor.  The returned value is `0` when the rectangle is empty; otherwise
the same conductor comes with the actual primitive real zero supplied by
the Page argument. -/
theorem exists_pageBand_excludedConductor_with_selection :
    ∃ cPage lambda : ℝ, 0 < cPage ∧ 0 < lambda ∧ lambda ≤ 1 / 16 ∧
      PageWindowIsQuadratic cPage ∧
      ∀ (Q T : ℕ), 3 ≤ Q → 2 ≤ T →
        let B := (Q : ℝ) * ((T : ℝ) + 2)
        let eta := lambda / Real.log B
        ∃ m₀ : ℕ, m₀ ≤ Q ∧
          (∀ q ∈ Finset.Ioc 1 Q, q ≠ m₀ →
              ∀ psi : primitiveCharacters q,
                primitiveHighZeroMassAt q psi eta T = 0) ∧
          (m₀ = 0 ∨ PageExceptionalWitness Q m₀ cPage) ∧
          PageConductorSelection Q m₀ cPage := by
  obtain ⟨cUnique, hcUnique, hPage⟩ :=
    exists_pageConstant_modulus_eq_and_beta_eq
  obtain ⟨M, hM, hshape⟩ :=
    exists_nat_nonprincipalNontrivialLFunctionZero_sq_eq_one_real_simple
  let cPage : ℝ := min cUnique (1 / (2 * (M : ℝ) ^ 2))
  let lambda : ℝ := min (1 / 16 : ℝ)
    (min (cPage / 2) (1 / (2 * (M : ℝ) ^ 2)))
  have hMreal : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hcPage : 0 < cPage := by
    dsimp [cPage]
    positivity
  have hcPageUnique : cPage ≤ cUnique := by
    exact min_le_left _ _
  have hcPageShape : cPage ≤ 1 / (2 * (M : ℝ) ^ 2) := by
    exact min_le_right _ _
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    positivity
  have hlambdaSmall : lambda ≤ 1 / 16 := by
    exact min_le_left _ _
  have hlambdaPage : lambda ≤ cPage / 2 :=
    (min_le_right (1 / 16 : ℝ) _).trans (min_le_left _ _)
  have hlambdaShape : lambda ≤ 1 / (2 * (M : ℝ) ^ 2) :=
    (min_le_right (1 / 16 : ℝ) _).trans (min_le_right _ _)
  have hPageMono (Q : ℕ) (hQ : 3 ≤ Q) (z : PrimitiveRealZero)
      (hz : InPageWindow Q cPage z) : InPageWindow Q cUnique z := by
    refine ⟨hz.1, ?_⟩
    have hlogQ : 0 < Real.log (Q : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
    have hdiv : cPage / Real.log (Q : ℝ) ≤
        cUnique / Real.log (Q : ℝ) :=
      div_le_div_of_nonneg_right hcPageUnique hlogQ.le
    linarith [hz.2]
  have hquadratic : PageWindowIsQuadratic cPage := by
    intro Q hQ z hz
    have hlogQ : 0 < Real.log (Q : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
    have htwoMle : 2 * z.modulus ≤ Q ^ 2 := by
      calc
        2 * z.modulus ≤ 2 * Q := Nat.mul_le_mul_left 2 hz.1
        _ ≤ Q * Q := Nat.mul_le_mul_right Q (by omega : 2 ≤ Q)
        _ = Q ^ 2 := by ring
    have hlogTwoM : 0 < Real.log ((z.modulus : ℝ) * 2) := by
      apply Real.log_pos
      have hzgt : (1 : ℝ) < z.modulus := by
        exact_mod_cast z.modulus_gt_one
      nlinarith
    have hlogCompare :
        Real.log ((z.modulus : ℝ) * 2) ≤
          2 * Real.log (Q : ℝ) := by
      calc
        Real.log ((z.modulus : ℝ) * 2) =
            Real.log ((2 * z.modulus : ℕ) : ℝ) := by
              norm_num [Nat.cast_mul, mul_comm]
        _ ≤ Real.log ((Q ^ 2 : ℕ) : ℝ) :=
          Real.log_le_log (by
            exact_mod_cast Nat.mul_pos (by norm_num : 0 < (2 : ℕ))
              (Nat.zero_lt_of_lt z.modulus_gt_one))
            (by exact_mod_cast htwoMle)
        _ = 2 * Real.log (Q : ℝ) := by
          rw [Nat.cast_pow, Real.log_pow]
          norm_num
    have hdenPos :
        0 < (M : ℝ) ^ 2 * Real.log ((z.modulus : ℝ) * 2) :=
      mul_pos (sq_pos_of_pos hMreal) hlogTwoM
    have hinv :
        1 / (2 * (M : ℝ) ^ 2 * Real.log (Q : ℝ)) ≤
          1 / ((M : ℝ) ^ 2 * Real.log ((z.modulus : ℝ) * 2)) := by
      apply one_div_le_one_div_of_le hdenPos
      nlinarith [sq_pos_of_pos hMreal, hlogQ]
    have hcRewrite :
        (1 / (2 * (M : ℝ) ^ 2)) / Real.log (Q : ℝ) =
          1 / (2 * (M : ℝ) ^ 2 * Real.log (Q : ℝ)) := by
      field_simp [hMreal.ne', hlogQ.ne']
    have hpageShape :
        1 - (1 / (2 * (M : ℝ) ^ 2)) / Real.log (Q : ℝ) < z.beta := by
      have hdiv : cPage / Real.log (Q : ℝ) ≤
          (1 / (2 * (M : ℝ) ^ 2)) / Real.log (Q : ℝ) :=
        div_le_div_of_nonneg_right hcPageShape hlogQ.le
      linarith [hz.2]
    have hnear :
        1 - 1 / ((M : ℝ) ^ 2 *
            Real.log ((z.modulus : ℝ) *
              (|(z.beta : ℂ).im| + 2))) ≤ z.beta := by
      rw [show |(z.beta : ℂ).im| + 2 = 2 by simp]
      rw [hcRewrite] at hpageShape
      linarith
    have hnontrivial :
        IsNonprincipalNontrivialLFunctionZero z.character (z.beta : ℂ) := by
      apply (isNonprincipalNontrivialLFunctionZero_iff _ _).2
      exact ⟨z.ne_one, z.isZero, by simpa using z.beta_pos,
        by simpa using z.beta_lt_one⟩
    exact (hshape z.modulus z.character (z.beta : ℂ)
      hnontrivial hnear).1
  refine ⟨cPage, lambda, hcPage, hlambda, hlambdaSmall, hquadratic, ?_⟩
  intro Q T hQ hT
  dsimp only
  let B : ℝ := (Q : ℝ) * ((T : ℝ) + 2)
  let eta : ℝ := lambda / Real.log B
  have hB : (8 : ℝ) ≤ B := by
    dsimp [B]
    have hQR : (3 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  have hlogB : 0 < Real.log B :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 8) hB)
  have heta : 0 < eta := by dsimp [eta]; positivity
  have heta1 : eta ≤ 1 := by
    have hlogBone : (1 : ℝ) ≤ Real.log B := by
      have hlog8 : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num
      have hmono : Real.log 8 ≤ Real.log B :=
        Real.log_le_log (by norm_num) hB
      nlinarith [Real.log_two_gt_d9]
    have : eta ≤ lambda := by
      dsimp [eta]
      rw [div_le_iff₀ hlogB]
      nlinarith
    linarith
  have hetaLtOne : eta < 1 := by
    have hlogBone : (1 : ℝ) ≤ Real.log B := by
      have hlog8 : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num
      have hmono : Real.log 8 ≤ Real.log B :=
        Real.log_le_log (by norm_num) hB
      nlinarith [Real.log_two_gt_d9]
    have hetaLeLambda : eta ≤ lambda := by
      dsimp [eta]
      rw [div_le_iff₀ hlogB]
      nlinarith
    exact hetaLeLambda.trans_lt (hlambdaSmall.trans_lt (by norm_num))
  have hpoint (q : ℕ) (hq : 1 < q) (hqQ : q ≤ Q)
      (psi : primitiveCharacters q) (rho : ℂ)
      (hrho : rho ∈ @highZeroRectangle q
        ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hq)⟩ hq
          psi.1 psi.2 eta T) :
      ∃ z : PrimitiveRealZero,
        z.modulus = q ∧ z.beta = rho.re ∧
          InPageWindow Q cPage z := by
    letI : NeZero q := ⟨by omega⟩
    have hrhoData :=
      (mem_highZeroRectangle_iff hq psi.1 psi.2 heta1
        (by positivity : (0 : ℝ) ≤ T) rho).mp hrho
    have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have himAbs : |rho.im| = rho.im := abs_of_nonneg hrhoData.2.2.2.1
    have hlocalPos : (0 : ℝ) < (q : ℝ) * (|rho.im| + 2) := by
      positivity
    have hlocalLe : (q : ℝ) * (|rho.im| + 2) ≤ B := by
      rw [himAbs]
      dsimp [B]
      have hqCast : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
      have himT : rho.im ≤ (T : ℝ) := hrhoData.2.2.2.2
      exact mul_le_mul hqCast (by linarith [hrhoData.2.2.2.1])
        (by linarith [hrhoData.2.2.2.1]) (by positivity)
    have hlogLocal : 0 < Real.log ((q : ℝ) * (|rho.im| + 2)) := by
      apply Real.log_pos
      have hqTwo : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
      nlinarith [abs_nonneg rho.im]
    have hlogLocalLe :
        Real.log ((q : ℝ) * (|rho.im| + 2)) ≤ Real.log B :=
      Real.log_le_log hlocalPos hlocalLe
    have hlambdaM : lambda ≤ 1 / ((M : ℝ) ^ 2) := by
      calc
        lambda ≤ 1 / (2 * (M : ℝ) ^ 2) := hlambdaShape
        _ ≤ 1 / ((M : ℝ) ^ 2) := by
          apply one_div_le_one_div_of_le (sq_pos_of_pos hMreal)
          nlinarith [sq_pos_of_pos hMreal]
    have hetaThreshold :
        eta ≤ 1 / ((M : ℝ) ^ 2 *
          Real.log ((q : ℝ) * (|rho.im| + 2))) := by
      dsimp [eta]
      rw [div_le_div_iff₀ hlogB
        (mul_pos (sq_pos_of_pos hMreal) hlogLocal)]
      calc
        lambda * ((M : ℝ) ^ 2 *
              Real.log ((q : ℝ) * (|rho.im| + 2))) ≤
            (1 / ((M : ℝ) ^ 2)) * ((M : ℝ) ^ 2 *
              Real.log ((q : ℝ) * (|rho.im| + 2))) := by
          gcongr
        _ = Real.log ((q : ℝ) * (|rho.im| + 2)) := by
          field_simp
        _ ≤ 1 * Real.log B := by simpa using hlogLocalLe
    have hnonprincipal : psi.1 ≠ 1 :=
      primitiveCharacter_ne_one_of_one_lt hq psi
    have hnontrivial :
        IsNonprincipalNontrivialLFunctionZero psi.1 rho :=
      (isNonprincipalNontrivialLFunctionZero_iff psi.1 rho).2
        ⟨hnonprincipal, hrhoData.1, by linarith [hrhoData.2.1],
          LFunction_zero_re_lt_one_of_isPrimitive hq psi.1 psi.2 hrhoData.1⟩
    have hnearShape :
        1 - 1 / ((M : ℝ) ^ 2 *
            Real.log ((q : ℝ) * (|rho.im| + 2))) ≤ rho.re := by
      linarith [hrhoData.2.1]
    have hrhoReal := (hshape q psi.1 rho hnontrivial hnearShape).2.1
    have hrhoEq : rho = (rho.re : ℂ) := by
      apply Complex.ext
      · simp only [ofReal_re]
      · simpa only [ofReal_im] using hrhoReal
    let z : PrimitiveRealZero :=
      { modulus := q
        modulus_gt_one := hq
        character := psi.1
        isPrimitive := psi.2
        ne_one := hnonprincipal
        beta := rho.re
        beta_pos := by linarith [hrhoData.2.1]
        beta_lt_one :=
          LFunction_zero_re_lt_one_of_isPrimitive hq psi.1 psi.2 hrhoData.1
        isZero := by
          change DirichletCharacter.LFunction psi.1 (rho.re : ℂ) = 0
          rw [← hrhoEq]
          exact hrhoData.1 }
    have hlogQ : 0 < Real.log (Q : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
    have hlogQLe : Real.log (Q : ℝ) ≤ Real.log B := by
      apply Real.log_le_log (by positivity)
      dsimp [B]
      have hT0R : (0 : ℝ) ≤ T := by positivity
      have hQR : (0 : ℝ) ≤ Q := by positivity
      nlinarith
    have hetaPage : eta < cPage / Real.log (Q : ℝ) := by
      have hhalf : lambda / Real.log B ≤
          (cPage / 2) / Real.log (Q : ℝ) := by
        rw [div_le_div_iff₀ hlogB hlogQ]
        calc
          lambda * Real.log (Q : ℝ) ≤
              (cPage / 2) * Real.log (Q : ℝ) := by
            gcongr
          _ ≤ (cPage / 2) * Real.log B := by
            gcongr
      dsimp [eta]
      exact hhalf.trans_lt (by
        rw [div_lt_div_iff₀ hlogQ hlogQ]
        nlinarith)
    refine ⟨z, rfl, rfl, hqQ, ?_⟩
    dsimp [z]
    linarith [hrhoData.2.1]
  by_cases hexists : ∃ z : PrimitiveRealZero, InPageWindow Q cPage z
  · obtain ⟨z₀, hz₀Page⟩ := hexists
    refine ⟨z₀.modulus, hz₀Page.1, ?_, Or.inr ⟨z₀, rfl, hz₀Page⟩, ?_⟩
    intro q hqMem hqNe psi
    have hq : 1 < q := (Finset.mem_Ioc.mp hqMem).1
    rw [primitiveHighZeroMassAt_eq hq]
    apply Finset.sum_eq_zero
    intro rho hrho
    obtain ⟨z, hzq, hzbeta, hzPage⟩ := hpoint q hq
      (Finset.mem_Ioc.mp hqMem).2 psi rho hrho
    have heq := hPage Q hQ z z₀ (hPageMono Q hQ z hzPage)
      (hPageMono Q hQ z₀ hz₀Page)
    have hqz₀ : q = z₀.modulus := hzq.symm.trans heq.1
    exact (hqNe hqz₀).elim
    refine ⟨?_, ?_⟩
    · intro z hz
      exact (hPage Q hQ z z₀ (hPageMono Q hQ z hz)
        (hPageMono Q hQ z₀ hz₀Page)).1
    · constructor
      · intro hzZero
        have : z₀.modulus = 0 := hzZero
        exact ((Nat.ne_of_gt (Nat.zero_lt_of_lt z₀.modulus_gt_one)) this).elim
      · intro hnone
        exact (hnone ⟨z₀, hz₀Page⟩).elim
  · refine ⟨0, by omega, ?_, Or.inl rfl, ?_⟩
    intro q hqMem hqNe psi
    have hq : 1 < q := (Finset.mem_Ioc.mp hqMem).1
    rw [primitiveHighZeroMassAt_eq hq]
    apply Finset.sum_eq_zero
    intro rho hrho
    obtain ⟨z, _hzq, _hzbeta, hzPage⟩ := hpoint q hq
      (Finset.mem_Ioc.mp hqMem).2 psi rho hrho
    exact (hexists ⟨z, hzPage⟩).elim
    refine ⟨?_, ?_⟩
    · intro z hz
      exact (hexists ⟨z, hz⟩).elim
    · constructor
      · intro _
        exact hexists
      · intro _
        rfl

/-- Projection of the canonical Page-conductor selection which retains only
the actual real-zero witness used by the endpoint argument. -/
theorem exists_pageBand_excludedConductor_with_witness :
    ∃ cPage lambda : ℝ, 0 < cPage ∧ 0 < lambda ∧ lambda ≤ 1 / 16 ∧
      ∀ (Q T : ℕ), 3 ≤ Q → 2 ≤ T →
        let B := (Q : ℝ) * ((T : ℝ) + 2)
        let eta := lambda / Real.log B
        ∃ m₀ : ℕ, m₀ ≤ Q ∧
          (∀ q ∈ Finset.Ioc 1 Q, q ≠ m₀ →
              ∀ psi : primitiveCharacters q,
                primitiveHighZeroMassAt q psi eta T = 0) ∧
          (m₀ = 0 ∨ PageExceptionalWitness Q m₀ cPage) := by
  obtain ⟨cPage, lambda, hcPage, hlambda, hlambdaSmall, _hquadratic, hmain⟩ :=
    exists_pageBand_excludedConductor_with_selection
  refine ⟨cPage, lambda, hcPage, hlambda, hlambdaSmall, ?_⟩
  intro Q T hQ hT
  obtain ⟨m₀, hm₀, hzero, hwitness, _hselection⟩ := hmain Q T hQ hT
  exact ⟨m₀, hm₀, hzero, hwitness⟩

/-- Backwards-compatible projection which forgets the real-zero witness. -/
theorem exists_pageBand_excludedConductor :
    ∃ lambda : ℝ, 0 < lambda ∧ lambda ≤ 1 / 16 ∧
      ∀ (Q T : ℕ), 3 ≤ Q → 2 ≤ T →
        let B := (Q : ℝ) * ((T : ℝ) + 2)
        let eta := lambda / Real.log B
        ∃ m₀ : ℕ, m₀ ≤ Q ∧
          ∀ q ∈ Finset.Ioc 1 Q, q ≠ m₀ →
            ∀ psi : primitiveCharacters q,
              primitiveHighZeroMassAt q psi eta T = 0 := by
  obtain ⟨_cPage, lambda, _hcPage, hlambda, hlambdaSmall, hmain⟩ :=
    exists_pageBand_excludedConductor_with_witness
  refine ⟨lambda, hlambda, hlambdaSmall, ?_⟩
  intro Q T hQ hT
  obtain ⟨m₀, hm₀, hzero, _hwitness⟩ := hmain Q T hQ hT
  exact ⟨m₀, hm₀, hzero⟩

end

end Erdos48
