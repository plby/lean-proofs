/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.SelectedZeroBandMass
import ErdosProblems.Erdos48.ZeroMultiplicityCover

/-!
# A raw log-free zero-density estimate

This module chooses the uniform band detectors simultaneously for every
primitive character, converts the selected ordinate count back to analytic
zero multiplicity, and applies the optimized hybrid large sieve.  The result
keeps harmless finite sums and constants explicit; later asymptotic layers
may weaken it to the customary `B ^ (C * eta)` form.
-/

namespace Erdos48

open Complex
open scoped BigOperators
open BoundedGaps.Maynard

noncomputable section

/-- Totalized multiplicity in one primitive high-zero rectangle. -/
noncomputable def primitiveHighZeroMassAt
    (q : ℕ) (psi : primitiveCharacters q) (eta T : ℝ) : ℕ :=
  if hq : 1 < q then
    @highZeroRectangleMass q ⟨by omega⟩ hq psi.1 psi.2 eta T
  else 0

/-- Aggregate primitive multiplicity for conductors `2 ≤ q ≤ Q`. -/
noncomputable def primitiveHighZeroMass
    (Q : ℕ) (eta T : ℝ) : ℕ :=
  ∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
    primitiveHighZeroMassAt q psi eta T

theorem primitiveHighZeroMassAt_eq
    {q : ℕ} (hq : 1 < q) (psi : primitiveCharacters q) (eta T : ℝ) :
    primitiveHighZeroMassAt q psi eta T =
      @highZeroRectangleMass q ⟨by omega⟩ hq psi.1 psi.2 eta T := by
  simp only [primitiveHighZeroMassAt, dif_pos hq]

/-- Fully assembled detector-density inequality.  The two lower-end
inequalities are isolated because they are elementary consequences of the
chosen power cutoff and are useful independently of the analytic argument. -/
theorem exists_raw_logFreeDensity_parameters :
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧
      ∃ lambda R delta eta₀ : ℝ,
        0 < lambda ∧ 0 < R ∧ 0 < delta ∧ delta ≤ 1 ∧
        0 < eta₀ ∧ eta₀ ≤ 1 / 8 ∧
        ∃ A : ℕ, 37 ≤ A ∧
        ∀ (Q T : ℕ), 2 ≤ Q →
          ∀ eta : ℝ, 0 < eta → eta ≤ eta₀ →
          eta * Real.log ((Q : ℝ) * ((T : ℝ) + 2)) ≤ lambda →
          let Y := zeroDetectorLowerCutoff
            ((Q : ℝ) * ((T : ℝ) + 2))
          let N := zeroDetectorCutoff R eta
          2 * ((T + 1) + 1) ≤ Y →
          2 * Q ^ 2 ≤ Y →
          (primitiveHighZeroMass Q eta T : ℝ) *
              (delta * eta) * (1 / 96 : ℝ) ^ 2 ≤
            (32 * (Real.log 4 + 4) +
                (256 * (A : ℝ) / 3) * lambda) *
              ∑ j ∈ Finset.Icc L J,
                (2 * Real.exp 2 * (1 + 8 * Real.pi)) *
                  (((T + 1) + 1 : ℕ) : ℝ) *
                  ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 *
                  ((((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) * Real.log 2) ^
                    (2 * ((j - 1) + 1))) *
                  (((Y : ℝ) / 2) ^ (-(2 * eta))) := by
  obtain ⟨L, J, hL2, hLJ, lambda, R, delta, eta₀,
      hlambda, hR, hdelta, hdelta1, heta₀, heta₀8, hselection⟩ :=
    exists_uniform_band_zero_detector
  obtain ⟨A, hA, hcoverBound⟩ :=
    exists_highZeroRectangleMass_cover_bound
  refine ⟨L, J, hL2, hLJ, lambda, R, delta, eta₀,
    hlambda, hR, hdelta, hdelta1, heta₀, heta₀8, A, hA, ?_⟩
  intro Q T hQ eta heta hetaSmall hglobal
  dsimp only
  intro hYheight hYconductor
  let Bglobal : ℝ := (Q : ℝ) * ((T : ℝ) + 2)
  let Y : ℕ := zeroDetectorLowerCutoff Bglobal
  let N : ℕ := zeroDetectorCutoff R eta
  let Klocal : ℝ := 32 * (Real.log 4 + 4) +
    (256 * (A : ℝ) / 3) * lambda
  have heta1 : eta ≤ 1 := by linarith
  have hT0 : (0 : ℝ) ≤ T := by positivity
  have hKlocal : 0 ≤ Klocal := by dsimp [Klocal]; positivity
  have hexists (q : ℕ) (psi : primitiveCharacters q) :
      ∃ S : Finset ℝ, ∃ order : ℝ → ℕ,
        q ∈ Finset.Ioc 1 Q →
          (∀ t ∈ S, 0 ≤ t ∧ t ≤ T) ∧
          (∀ x ∈ S, ∀ y ∈ S, x ≠ y →
            2 * delta * eta < dist x y) ∧
          (∀ t ∈ S, L ≤ order t ∧ order t ≤ J) ∧
          (∀ t ∈ S, ∀ u : ℝ, |u - t| ≤ delta * eta →
            (1 / 96 : ℝ) ≤
              ‖∑ n ∈ Finset.Ioc Y N,
                (weightedVonMangoldtMajorant eta (order t - 1) n : ℂ) *
                  psi.1 n *
                    Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖) ∧
          ((primitiveHighZeroMassAt q psi eta T : ℕ) : ℝ) ≤
            (S.card : ℝ) * Klocal := by
    by_cases hqMem : q ∈ Finset.Ioc 1 Q
    · have hqData := Finset.mem_Ioc.mp hqMem
      have hq1 : 1 < q := hqData.1
      have hqQ : q ≤ Q := hqData.2
      let : NeZero q := ⟨by omega⟩
      obtain ⟨S, order, hSsub, hsep, hcover, hYN, horder⟩ :=
        hselection Q hQ (T : ℝ) eta hT0 heta hetaSmall hglobal
          q hq1 hqQ psi.1 psi.2
      refine ⟨S, order, fun _ ↦ ⟨?_, hsep, ?_, ?_, ?_⟩⟩
      · intro t ht
        have htOrd := hSsub ht
        obtain ⟨rho, hzero, hrelo, hrehi, hrhoim, ht0, htT⟩ :=
          (mem_highZeroOrdinates_iff hq1 psi.1 psi.2 heta1 hT0 t).mp htOrd
        exact ⟨ht0, htT⟩
      · intro t ht
        exact ⟨(horder t ht).1, (horder t ht).2.1⟩
      · intro t ht u hu
        have hlarge := (horder t ht).2.2 u hu
        let j := order t
        have hjL : L ≤ j := by simpa only [j] using (horder t ht).1
        have hjPos : 1 ≤ j := by omega
        have hfac : (1 : ℝ) ≤ (j - 1).factorial := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
        have htwoetaPos : 0 < 2 * eta := by positivity
        have htwoetaOne : 2 * eta ≤ 1 := by linarith
        have hinv : (1 : ℝ) ≤ (2 * eta)⁻¹ :=
          (one_le_inv₀ htwoetaPos).2 htwoetaOne
        have hinvpow : (1 : ℝ) ≤ (2 * eta)⁻¹ ^ j := one_le_pow₀ hinv
        have hfactor : (1 / 96 : ℝ) ≤
            (j - 1).factorial * (1 / 96 : ℝ) * (2 * eta)⁻¹ ^ j := by
          nlinarith [show (0 : ℝ) ≤ 1 / 96 by norm_num]
        calc
          (1 / 96 : ℝ) ≤
              (j - 1).factorial * (1 / 96 : ℝ) * (2 * eta)⁻¹ ^ j := hfactor
          _ ≤ ‖bandZeroDetectorPolynomial psi.1 eta (j - 1) N Bglobal u‖ :=
            hlarge.le
          _ = ‖∑ n ∈ Finset.Ioc Y N,
                (weightedVonMangoldtMajorant eta (order t - 1) n : ℂ) *
                  psi.1 n *
                    Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ := by
            rfl
      · have hlogq : eta * Real.log ((q : ℝ) * ((T : ℝ) + 2)) ≤
            lambda := by
          have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
          have hinside : 0 < (q : ℝ) * ((T : ℝ) + 2) := by positivity
          have hlogle : Real.log ((q : ℝ) * ((T : ℝ) + 2)) ≤
              Real.log ((Q : ℝ) * ((T : ℝ) + 2)) := by
            apply Real.log_le_log hinside
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hqQ) (by positivity)
          exact (mul_le_mul_of_nonneg_left hlogle heta.le).trans hglobal
        have hmass := hcoverBound q hq1 psi.1 psi.2 eta (T : ℝ)
          lambda delta heta heta1 hT0 hdelta.le hdelta1 hlogq S hSsub hcover
        simpa only [primitiveHighZeroMassAt, dif_pos hq1, Klocal] using hmass
    · exact ⟨∅, fun _ ↦ L, fun h ↦ (hqMem h).elim⟩
  let S : ∀ q : ℕ, primitiveCharacters q → Finset ℝ :=
    fun q psi ↦ Classical.choose (hexists q psi)
  let order : ∀ q : ℕ, primitiveCharacters q → ℝ → ℕ :=
    fun q psi ↦ Classical.choose (Classical.choose_spec (hexists q psi))
  have hchosen (q : ℕ) (psi : primitiveCharacters q) :
      q ∈ Finset.Ioc 1 Q →
        (∀ t ∈ S q psi, 0 ≤ t ∧ t ≤ T) ∧
        (∀ x ∈ S q psi, ∀ y ∈ S q psi, x ≠ y →
          2 * delta * eta < dist x y) ∧
        (∀ t ∈ S q psi, L ≤ order q psi t ∧ order q psi t ≤ J) ∧
        (∀ t ∈ S q psi, ∀ u : ℝ, |u - t| ≤ delta * eta →
          (1 / 96 : ℝ) ≤
            ‖∑ n ∈ Finset.Ioc Y N,
              (weightedVonMangoldtMajorant eta (order q psi t - 1) n : ℂ) *
                psi.1 n *
                  Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖) ∧
        ((primitiveHighZeroMassAt q psi eta T : ℕ) : ℝ) ≤
          ((S q psi).card : ℝ) * Klocal := by
    exact Classical.choose_spec (Classical.choose_spec (hexists q psi))
  have hselected := sum_selectedOrdinates_card_mul_le_primitiveMass
    Q Y N T L J eta delta heta heta1 hdelta hdelta1 S order
      (fun q hq psi ↦ (hchosen q psi hq).1)
      (fun q hq psi ↦ (hchosen q psi hq).2.1)
      (fun q hq psi ↦ (hchosen q psi hq).2.2.1)
      (fun q hq psi ↦ (hchosen q psi hq).2.2.2.1)
  let totalCard : ℝ :=
    ∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
      ((S q psi).card : ℝ)
  have hmass : (primitiveHighZeroMass Q eta T : ℝ) ≤
      totalCard * Klocal := by
    unfold primitiveHighZeroMass
    push_cast
    calc
      (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
          (primitiveHighZeroMassAt q psi eta T : ℝ)) ≤
          ∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
            ((S q psi).card : ℝ) * Klocal := by
        apply Finset.sum_le_sum
        intro q hq
        apply Finset.sum_le_sum
        intro psi hpsi
        exact (hchosen q psi hq).2.2.2.2
      _ = totalCard * Klocal := by
        dsimp [totalCard]
        simp_rw [Finset.sum_mul]
  let c₀ : ℝ := (delta * eta) * (1 / 96 : ℝ) ^ 2
  have hc₀ : 0 ≤ c₀ := by dsimp [c₀]; positivity
  have hmassSelected :
      (primitiveHighZeroMass Q eta T : ℝ) * c₀ ≤
        Klocal *
          ∑ j ∈ Finset.Icc L J,
            ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
              primitiveNegativeDirichletMass Q (Finset.Ioc Y N)
                (fun n ↦
                  (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)) u := by
    calc
      (primitiveHighZeroMass Q eta T : ℝ) * c₀ ≤
          (totalCard * Klocal) * c₀ :=
        mul_le_mul_of_nonneg_right hmass hc₀
      _ = Klocal * (totalCard * c₀) := by ring
      _ ≤ Klocal *
          ∑ j ∈ Finset.Icc L J,
            ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
              primitiveNegativeDirichletMass Q (Finset.Ioc Y N)
                (fun n ↦
                  (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)) u := by
        apply mul_le_mul_of_nonneg_left _ hKlocal
        simpa only [totalCard, c₀, mul_assoc] using hselected
  have hintegrals :
      (∑ j ∈ Finset.Icc L J,
          ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            primitiveNegativeDirichletMass Q (Finset.Ioc Y N)
              (fun n ↦
                (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)) u) ≤
        ∑ j ∈ Finset.Icc L J,
          (2 * Real.exp 2 * (1 + 8 * Real.pi)) *
            (((T + 1) + 1 : ℕ) : ℝ) *
            ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 *
            ((((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) * Real.log 2) ^
              (2 * ((j - 1) + 1))) *
            (((Y : ℝ) / 2) ^ (-(2 * eta))) := by
    apply Finset.sum_le_sum
    intro j hj
    exact intervalIntegral_weightedDetectorBand_le
      Q Y N (T + 1) (j - 1) (by
        have : 2 * ((T + 1) + 1) ≤ Y := hYheight
        omega) hYheight hYconductor eta heta.le
  calc
    (primitiveHighZeroMass Q eta T : ℝ) *
        (delta * eta) * (1 / 96 : ℝ) ^ 2 =
      (primitiveHighZeroMass Q eta T : ℝ) * c₀ := by
        dsimp [c₀]
        ring
    _ ≤ Klocal *
        ∑ j ∈ Finset.Icc L J,
          ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            primitiveNegativeDirichletMass Q (Finset.Ioc Y N)
              (fun n ↦
                (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)) u :=
      hmassSelected
    _ ≤ Klocal *
        ∑ j ∈ Finset.Icc L J,
          (2 * Real.exp 2 * (1 + 8 * Real.pi)) *
            (((T + 1) + 1 : ℕ) : ℝ) *
            ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 *
            ((((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) * Real.log 2) ^
              (2 * ((j - 1) + 1))) *
            (((Y : ℝ) / 2) ^ (-(2 * eta))) :=
      mul_le_mul_of_nonneg_left hintegrals hKlocal
    _ = _ := by rfl

end

end Erdos48
