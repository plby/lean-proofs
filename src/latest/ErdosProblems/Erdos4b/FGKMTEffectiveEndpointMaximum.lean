/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTEffectiveTwist
import BoundedGaps.BombieriVinogradov.Analytic.VaughanFiveTermEndpoint

/-!
# Effective primitive endpoint maxima with a common excluded prime

Small endpoints use the elementary Chebyshev bound. Larger endpoints use
the same conductor-scale exceptional prime, not a new prime for each endpoint.
The resulting centered maximum is the one in the conductor reduction.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter BoundedGaps.Maynard

theorem sqrt_le_expDecayEnvelope {x c : ℝ} (hx : 0 < x)
    (hlog : 4 ≤ Real.log x) (hc : c ≤ 1) :
    Real.sqrt x ≤ x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  let u : ℝ := Real.sqrt (Real.log x)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have husq : u ^ 2 = Real.log x := Real.sq_sqrt (by linarith)
  have hu2 : 2 ≤ u := by
    apply (sq_le_sq₀ (by norm_num) hu).mp
    nlinarith
  have hcu : c * u ≤ Real.log x / 2 := by
    have hcu' := mul_le_mul_of_nonneg_right hc hu
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hu2)]
  calc
    Real.sqrt x = Real.exp (Real.log x / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
      congr 1
      ring
    _ ≤ Real.exp (Real.log x - c * u) := Real.exp_monotone (by linarith)
    _ = _ := by
      rw [Real.exp_sub, Real.exp_log hx, div_eq_mul_inv, ← Real.exp_neg]
      simp only [neg_mul]
      rfl

theorem half_sqrt_log_le_of_sqrt_le {x y : ℝ}
    (hx : 0 < x) (hlog : 0 ≤ Real.log x) (hy : Real.sqrt x ≤ y) :
    Real.sqrt (Real.log x) / 2 ≤ Real.sqrt (Real.log y) := by
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hlogHalf : Real.log x / 2 ≤ Real.log y := by
    calc
      _ = Real.log (Real.sqrt x) := (Real.log_sqrt hx.le).symm
      _ ≤ _ := Real.log_le_log hsqrt hy
  have hylog : 0 ≤ Real.log y := by linarith
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [div_pow, Real.sq_sqrt hlog, Real.sq_sqrt hylog]
  nlinarith

theorem exists_exceptionalPrime_effective_endpointMaximum_bound :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ X0 : ℕ, 4 ≤ X0 ∧
      ∀ Q : ℕ, 2 ≤ Q → ∃ B : ℕ, 1 ≤ B ∧ B ≤ Q ∧ (B = 1 ∨ B.Prime) ∧
        ∀ x : ℕ, X0 ≤ x →
          (Q : ℝ) ^ 2 ≤ Real.exp (Real.sqrt (Real.log (x : ℝ)) / 2) →
          ∀ d : ℕ, 1 < d → d ≤ Q → d.Coprime B → ∀ psi : primitiveCharacters d,
            primitiveCenteredEndpointMaximum x d psi ≤
              C * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) := by
  obtain ⟨C0, c0, hC0, hc0, Xs, _hXs, hpoint⟩ :=
    exists_exceptionalPrime_effective_twistedSum_bound
  let Kpsi : ℝ := Real.log 4 + 4
  let C : ℝ := C0 + Kpsi
  let c : ℝ := min (c0 / 2) 1
  have hKpsi : 0 < Kpsi := by dsimp [Kpsi]; positivity
  have hC : 0 < C := add_pos hC0 hKpsi
  have hc : 0 < c := lt_min (by positivity) zero_lt_one
  have hcC0 : c ≤ c0 / 2 := min_le_left _ _
  have hcOne : c ≤ 1 := min_le_right _ _
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Xlog, hXlog⟩ := eventually_atTop.mp
    (hlogTop.eventually (eventually_ge_atTop (4 : ℝ)))
  let X0 : ℕ := max 4 (max Xlog (Xs ^ 2))
  refine ⟨C, c, hC, hc, X0, by simp [X0], ?_⟩
  intro Q hQ
  obtain ⟨B, hBpos, hBQ, hB, hpointB⟩ := hpoint Q hQ
  refine ⟨B, hBpos, hBQ, hB, ?_⟩
  intro x hxX0 hQheight d hd hdQ hcop psi
  have hxFour : 4 ≤ x := by dsimp [X0] at hxX0; omega
  have hXlogX : Xlog ≤ x := by dsimp [X0] at hxX0; omega
  have hXsSqX : Xs ^ 2 ≤ x := by dsimp [X0] at hxX0; omega
  have hxlog : 4 ≤ Real.log (x : ℝ) := hXlog x hXlogX
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hXsRoot : (Xs : ℝ) ≤ Real.sqrt (x : ℝ) := by
    have hsq : (Xs : ℝ) ^ 2 ≤ (x : ℝ) := by exact_mod_cast hXsSqX
    have hsqrt := Real.sqrt_le_sqrt hsq
    simpa only [Real.sqrt_sq (Nat.cast_nonneg Xs)] using hsqrt
  rw [primitiveCenteredEndpointMaximum_eq_raw x hd psi]
  unfold primitiveRawEndpointMaximum
  rw [dif_pos (by omega : 2 ≤ x)]
  apply Finset.sup'_le
  intro y hy
  obtain ⟨hyTwo, hyx⟩ := Finset.mem_Icc.mp hy
  have hyCast : (y : ℝ) ≤ x := by exact_mod_cast hyx
  by_cases hySmall : (y : ℝ) ≤ Real.sqrt (x : ℝ)
  · calc
      _ ≤ Chebyshev.psi (y : ℝ) := norm_twistedChebyshevSum_le_psi y d psi.1
      _ ≤ Kpsi * (y : ℝ) := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg y)
      _ ≤ Kpsi * Real.sqrt (x : ℝ) := mul_le_mul_of_nonneg_left hySmall hKpsi.le
      _ ≤ Kpsi * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) :=
        mul_le_mul_of_nonneg_left (sqrt_le_expDecayEnvelope hxpos hxlog hcOne) hKpsi.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)
  · have hyLarge := (lt_of_not_ge hySmall).le
    have hhalf := half_sqrt_log_le_of_sqrt_le hxpos (by linarith) hyLarge
    have hQheightY : (Q : ℝ) ^ 2 ≤ siegelWalfiszHeight y :=
      hQheight.trans (Real.exp_monotone hhalf)
    have hXsY : Xs ≤ y := by exact_mod_cast hXsRoot.trans hyLarge
    let : NeZero d := ⟨by omega⟩
    have hpointY := hpointB y hXsY hQheightY d hd hdQ psi.1 psi.2 hcop
    have hdecayScale : c * Real.sqrt (Real.log (x : ℝ)) ≤
        c0 * Real.sqrt (Real.log (y : ℝ)) := by
      calc
        _ ≤ (c0 / 2) * Real.sqrt (Real.log (x : ℝ)) :=
          mul_le_mul_of_nonneg_right hcC0 (Real.sqrt_nonneg _)
        _ = c0 * (Real.sqrt (Real.log (x : ℝ)) / 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hhalf hc0.le
    have hdecay : Real.exp (-c0 * Real.sqrt (Real.log (y : ℝ))) ≤
        Real.exp (-c * Real.sqrt (Real.log (x : ℝ))) :=
      Real.exp_monotone (by linarith)
    calc
      _ ≤ _ := hpointY
      _ ≤ C0 * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hyCast hdecay (by positivity)
          (Nat.cast_nonneg x)) hC0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sqrt_le_expDecayEnvelope
#print axioms Erdos4b.FGKMT.exists_exceptionalPrime_effective_endpointMaximum_bound
