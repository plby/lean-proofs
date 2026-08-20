/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.DetectorShellAggregation
import ErdosProblems.Erdos48.SeparatedIntervalMass

/-!
# From separated detected zeros to detector mean square

This file is the counting half of the log-free density argument.  It is
stated for an arbitrary family of selected ordinates; the next layer obtains
that family from the uniform band detector.
-/

namespace Erdos48

open Complex
open scoped BigOperators
open BoundedGaps.Maynard

noncomputable section

private theorem continuous_negativeDetectorPolynomial_norm_sq
    {q : ℕ} (psi : primitiveCharacters q) (s : Finset ℕ)
    (c : ℕ → ℂ) :
    Continuous (fun t : ℝ ↦
      ‖∑ n ∈ s, c n * psi.1 n *
        Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) := by
  fun_prop

/-- Expanding the integral of the primitive mass into the finite conductor
and character sums. -/
theorem intervalIntegral_primitiveNegativeDirichletMass_eq
    (Q T : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass Q s c t) =
      ∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ psi : primitiveCharacters q,
            ∫ t in (0 : ℝ)..(T : ℝ),
              ‖∑ n ∈ s, c n * psi.1 n *
                Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
  classical
  unfold primitiveNegativeDirichletMass
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum]
    intro psi hpsi
    exact (continuous_negativeDetectorPolynomial_norm_sq psi s c).intervalIntegrable
      0 T
  · intro q hq
    apply Continuous.intervalIntegrable
    apply continuous_const.mul
    apply continuous_finsetSum Finset.univ
    intro psi hpsi
    exact continuous_negativeDetectorPolynomial_norm_sq psi s c

private theorem sum_orderFiber_card_eq
    (S : Finset ℝ) (order : ℝ → ℕ) {L J : ℕ}
    (horder : ∀ t ∈ S, L ≤ order t ∧ order t ≤ J) :
    ∑ j ∈ Finset.Icc L J, (S.filter fun t ↦ order t = j).card = S.card := by
  classical
  calc
    ∑ j ∈ Finset.Icc L J, (S.filter fun t ↦ order t = j).card =
        ∑ j ∈ Finset.Icc L J, ∑ t ∈ S, if order t = j then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp
    _ = ∑ t ∈ S, ∑ j ∈ Finset.Icc L J,
          if order t = j then 1 else 0 := by rw [Finset.sum_comm]
    _ = ∑ _t ∈ S, 1 := by
      apply Finset.sum_congr rfl
      intro t ht
      have htRange : order t ∈ Finset.Icc L J :=
        Finset.mem_Icc.mpr (horder t ht)
      simp [Finset.sum_ite_eq', htRange]
    _ = S.card := by simp

/-- A separated order-labelled family of ordinates is bounded by the sum of
the corresponding detector mean squares.  The right endpoint is enlarged
from `T + delta*eta` to the next integer height `T+1`. -/
theorem selectedOrdinates_card_mul_le_detector_integrals
    {q : ℕ} (psi : primitiveCharacters q)
    (Y N T L J : ℕ) (eta delta : ℝ)
    (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (S : Finset ℝ) (order : ℝ → ℕ)
    (hS : ∀ t ∈ S, 0 ≤ t ∧ t ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      2 * delta * eta < dist x y)
    (horder : ∀ t ∈ S, L ≤ order t ∧ order t ≤ J)
    (hlower : ∀ t ∈ S, ∀ u : ℝ, |u - t| ≤ delta * eta →
      (1 / 96 : ℝ) ≤
        ‖∑ n ∈ Finset.Ioc Y N,
          (weightedVonMangoldtMajorant eta (order t - 1) n : ℂ) * psi.1 n *
            Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖) :
    (S.card : ℝ) * (delta * eta) * (1 / 96 : ℝ) ^ 2 ≤
      ∑ j ∈ Finset.Icc L J,
        ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
          ‖∑ n ∈ Finset.Ioc Y N,
            (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * psi.1 n *
              Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
  classical
  let r : ℝ := delta * eta
  let B : ℝ := (1 / 96 : ℝ) ^ 2
  let F : ℕ → Finset ℝ := fun j ↦ S.filter fun t ↦ order t = j
  let f : ℕ → ℝ → ℝ := fun j u ↦
    ‖∑ n ∈ Finset.Ioc Y N,
      (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * psi.1 n *
        Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by dsimp [r]; nlinarith
  have hfiber (j : ℕ) (hj : j ∈ Finset.Icc L J) :
      ((F j).card : ℝ) * r * B ≤
        ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ), f j u := by
    have hshort := card_mul_interval_lower_le_integral
      (F j) hr (show (0 : ℝ) ≤ T by positivity)
      (fun t ht ↦ hS t (Finset.mem_filter.mp ht).1)
      (fun x hx y hy hxy ↦ by
        simpa only [r, mul_assoc] using
          hsep x (Finset.mem_filter.mp hx).1 y
            (Finset.mem_filter.mp hy).1 hxy)
      (f j)
      (by dsimp [f]; fun_prop)
      (fun u ↦ by dsimp [f]; positivity)
      (fun t ht u hu ↦ by
        have htS := (Finset.mem_filter.mp ht).1
        have htOrder := (Finset.mem_filter.mp ht).2
        have huAbs : |u - t| ≤ r := by
          rw [abs_of_nonneg (sub_nonneg.mpr hu.1.le)]
          linarith [hu.2]
        have hl := hlower t htS u (by simpa only [r] using huAbs)
        dsimp [f, B]
        rw [← htOrder]
        exact (sq_le_sq₀ (by norm_num)
          (norm_nonneg (∑ n ∈ Finset.Ioc Y N,
            (weightedVonMangoldtMajorant eta (order t - 1) n : ℂ) * psi.1 n *
              Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))))).2 hl
      )
    have hfi : IntervalIntegrable (f j) MeasureTheory.volume
        0 ((T + 1 : ℕ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        ((show Continuous (f j) by dsimp [f]; fun_prop).intervalIntegrable
          0 ((T : ℝ) + 1))
    exact hshort.trans (intervalIntegral.integral_mono_interval
      le_rfl (by positivity) (by
        dsimp [r]
        push_cast
        linarith) (Filter.Eventually.of_forall fun u ↦ by
          dsimp [f]
          positivity)
      hfi)
  have hsum := Finset.sum_le_sum fun j hj ↦ hfiber j hj
  have hcardEq := sum_orderFiber_card_eq S order horder
  calc
    (S.card : ℝ) * (delta * eta) * (1 / 96 : ℝ) ^ 2 =
        ∑ j ∈ Finset.Icc L J, ((F j).card : ℝ) * r * B := by
      rw [← hcardEq]
      push_cast
      simp_rw [Finset.sum_mul]
      dsimp [F, r, B]
    _ ≤ ∑ j ∈ Finset.Icc L J,
        ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ), f j u := hsum
    _ = _ := by rfl

/-- Summed version over all primitive characters of conductor in `(1,Q]`.
The primitive large-sieve mass also contains the harmless conductor-one
term, so its integral dominates the exact character sum used here. -/
theorem sum_selectedOrdinates_card_mul_le_primitiveMass
    (Q Y N T L J : ℕ) (eta delta : ℝ)
    (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (S : ∀ q : ℕ, primitiveCharacters q → Finset ℝ)
    (order : ∀ q : ℕ, primitiveCharacters q → ℝ → ℕ)
    (hS : ∀ q ∈ Finset.Ioc 1 Q, ∀ psi : primitiveCharacters q,
      ∀ t ∈ S q psi, 0 ≤ t ∧ t ≤ T)
    (hsep : ∀ q ∈ Finset.Ioc 1 Q, ∀ psi : primitiveCharacters q,
      ∀ x ∈ S q psi, ∀ y ∈ S q psi, x ≠ y →
        2 * delta * eta < dist x y)
    (horder : ∀ q ∈ Finset.Ioc 1 Q, ∀ psi : primitiveCharacters q,
      ∀ t ∈ S q psi, L ≤ order q psi t ∧ order q psi t ≤ J)
    (hlower : ∀ q ∈ Finset.Ioc 1 Q, ∀ psi : primitiveCharacters q,
      ∀ t ∈ S q psi, ∀ u : ℝ, |u - t| ≤ delta * eta →
        (1 / 96 : ℝ) ≤
          ‖∑ n ∈ Finset.Ioc Y N,
            (weightedVonMangoldtMajorant eta (order q psi t - 1) n : ℂ) *
              psi.1 n * Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖) :
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        ((S q psi).card : ℝ)) * (delta * eta) * (1 / 96 : ℝ) ^ 2 ≤
      ∑ j ∈ Finset.Icc L J,
        ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
          primitiveNegativeDirichletMass Q (Finset.Ioc Y N)
            (fun n ↦ (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)) u := by
  classical
  have hone (q : ℕ) (hq : q ∈ Finset.Ioc 1 Q)
      (psi : primitiveCharacters q) :
      ((S q psi).card : ℝ) * (delta * eta) * (1 / 96 : ℝ) ^ 2 ≤
        ∑ j ∈ Finset.Icc L J,
          ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            ‖∑ n ∈ Finset.Ioc Y N,
              (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * psi.1 n *
                Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2 :=
    selectedOrdinates_card_mul_le_detector_integrals psi Y N T L J eta delta
      heta heta1 hdelta hdelta1 (S q psi) (order q psi)
      (hS q hq psi) (hsep q hq psi) (horder q hq psi) (hlower q hq psi)
  have hweighted (q : ℕ) (hq : q ∈ Finset.Ioc 1 Q)
      (psi : primitiveCharacters q) :
      ((S q psi).card : ℝ) * (delta * eta) * (1 / 96 : ℝ) ^ 2 ≤
        (q : ℝ) / (q.totient : ℝ) *
          ∑ j ∈ Finset.Icc L J,
            ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
              ‖∑ n ∈ Finset.Ioc Y N,
                (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * psi.1 n *
                  Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
    refine (hone q hq psi).trans ?_
    have hqData := Finset.mem_Ioc.mp hq
    have hqpos : 0 < q := by omega
    have htotPos : (0 : ℝ) < q.totient := by
      exact_mod_cast (Nat.totient_pos.mpr hqpos)
    have hw : (1 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) :=
      (one_le_div htotPos).2 (by exact_mod_cast Nat.totient_le q)
    have hsum0 : 0 ≤ ∑ j ∈ Finset.Icc L J,
        ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
          ‖∑ n ∈ Finset.Ioc Y N,
            (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * psi.1 n *
              Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
      apply Finset.sum_nonneg
      intro j hj
      exact intervalIntegral.integral_nonneg (by positivity)
        (fun u hu ↦ by positivity)
    nlinarith
  have hsum :
      (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
          ((S q psi).card : ℝ) * (delta * eta) * (1 / 96 : ℝ) ^ 2) ≤
        ∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ j ∈ Finset.Icc L J,
              ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
                ‖∑ n ∈ Finset.Ioc Y N,
                  (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * psi.1 n *
                    Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro q hq
    apply Finset.sum_le_sum
    intro psi hpsi
    exact hweighted q hq psi
  calc
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        ((S q psi).card : ℝ)) * (delta * eta) * (1 / 96 : ℝ) ^ 2 =
        ∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
          ((S q psi).card : ℝ) * (delta * eta) * (1 / 96 : ℝ) ^ 2 := by
      simp_rw [Finset.sum_mul]
    _ ≤ ∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ j ∈ Finset.Icc L J,
            ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
              ‖∑ n ∈ Finset.Ioc Y N,
                (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * psi.1 n *
                  Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2 := hsum
    _ ≤ ∑ q ∈ Finset.Ioc 0 Q, ∑ psi : primitiveCharacters q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ j ∈ Finset.Icc L J,
            ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
              ‖∑ n ∈ Finset.Ioc Y N,
                (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * psi.1 n *
                  Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        have := Finset.mem_Ioc.mp hq
        exact Finset.mem_Ioc.mpr ⟨by omega, this.2⟩
      · intro q hqBig hqSmall
        have hqpos : 0 < q := (Finset.mem_Ioc.mp hqBig).1
        have htotPos : 0 < q.totient := Nat.totient_pos.mpr hqpos
        apply Finset.sum_nonneg
        intro psi hpsi
        apply mul_nonneg
        · exact div_nonneg (by positivity) (by exact_mod_cast htotPos.le)
        · apply Finset.sum_nonneg
          intro j hj
          exact intervalIntegral.integral_nonneg (by positivity)
            (fun u hu ↦ by positivity)
    _ = ∑ j ∈ Finset.Icc L J,
        ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
          primitiveNegativeDirichletMass Q (Finset.Ioc Y N)
            (fun n ↦ (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)) u := by
      simp_rw [Finset.mul_sum]
      have hswapChar :
          (∑ q ∈ Finset.Ioc 0 Q, ∑ psi : primitiveCharacters q,
              ∑ j ∈ Finset.Icc L J,
                (q : ℝ) / (q.totient : ℝ) *
                  ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
                    ‖∑ n ∈ Finset.Ioc Y N,
                      (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * psi.1 n *
                        Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2) =
            ∑ q ∈ Finset.Ioc 0 Q, ∑ j ∈ Finset.Icc L J,
              ∑ psi : primitiveCharacters q,
                (q : ℝ) / (q.totient : ℝ) *
                  ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
                    ‖∑ n ∈ Finset.Ioc Y N,
                      (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * psi.1 n *
                        Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
        exact Finset.sum_congr rfl fun q hq ↦ Finset.sum_comm
      rw [hswapChar, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral_primitiveNegativeDirichletMass_eq]
      apply Finset.sum_congr rfl
      intro q hq
      simp_rw [Finset.mul_sum]

end

end Erdos48
