import ErdosProblems.Erdos4.FGKMTUniformTwists
import BoundedGaps.BombieriVinogradov.Analytic.VaughanFiveTermEndpoint

/-!
# Uniform primitive endpoint maxima after prime excision

The same omitted prime works at every endpoint. Endpoints below the square
root use the elementary Chebyshev bound; larger endpoints use the uniform
pointwise character theorem.
-/

namespace Erdos4.FGKMT

open Filter BoundedGaps.Maynard

theorem exists_uniform_primitive_maximum :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ X₀ : ℕ, 4 ≤ X₀ ∧
      ∀ Q : ℕ, 2 ≤ Q → ∃ B : ℕ, B ≤ Q ∧ (B = 1 ∨ B.Prime) ∧
        ∀ x : ℕ, X₀ ≤ x →
          (Q : ℝ) ≤ Real.exp (Real.sqrt (Real.log (x : ℝ)) / 2) →
          ∀ d : ℕ, 1 < d → d ≤ Q → d.Coprime B → ∀ ψ : primitiveCharacters d,
            primitiveCenteredEndpointMaximum x d ψ ≤
              C * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) := by
  obtain ⟨C₀, c₀, hC₀, hc₀, Xs, hpoint⟩ := exists_uniform_twisted_sum
  let Kψ : ℝ := Real.log 4 + 4
  let C : ℝ := C₀ + Kψ
  let c : ℝ := min (c₀ / 2) 1
  have hKψ : 0 < Kψ := by unfold Kψ; positivity
  have hC : 0 < C := add_pos hC₀ hKψ
  have hc : 0 < c := lt_min (by positivity) zero_lt_one
  have hcc₀ : c ≤ c₀ / 2 := min_le_left _ _
  have hc1 : c ≤ 1 := min_le_right _ _
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Xlog, hXlog⟩ := Filter.eventually_atTop.mp
    (hlogTop.eventually (eventually_ge_atTop 4))
  let X₀ : ℕ := max 4 (max Xlog (Xs ^ 2))
  refine ⟨C, c, hC, hc, X₀, by simp [X₀], ?_⟩
  intro Q hQ
  obtain ⟨B, hBQ, hB, hpointB⟩ := hpoint Q hQ
  refine ⟨B, hBQ, hB, ?_⟩
  intro x hxX hQheight d hd hdQ hcop ψ
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hxX
  have hxlog : Xlog ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hxX)
  have hxsq : Xs ^ 2 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hxX)
  have hL4 : 4 ≤ Real.log (x : ℝ) := hXlog x hxlog
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hXsRoot : (Xs : ℝ) ≤ Real.sqrt (x : ℝ) := by
    have hsquares : (Xs : ℝ) ^ 2 ≤ (x : ℝ) := by exact_mod_cast hxsq
    have hh := Real.sqrt_le_sqrt hsquares
    simpa only [Real.sqrt_sq (Nat.cast_nonneg Xs)] using hh
  rw [primitiveCenteredEndpointMaximum_eq_raw x hd ψ]
  unfold primitiveRawEndpointMaximum
  rw [dif_pos (by omega : 2 ≤ x)]
  apply Finset.sup'_le
  intro y hy
  have hyb : 2 ≤ y ∧ y ≤ x := Finset.mem_Icc.mp hy
  have hypos : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  by_cases hys : (y : ℝ) ≤ Real.sqrt (x : ℝ)
  · have hlinear : ‖twistedChebyshevSum y d ψ.1‖ ≤ Kψ * Real.sqrt (x : ℝ) := by
      calc
        _ ≤ Chebyshev.psi (y : ℝ) := norm_twistedChebyshevSum_le_psi y d ψ.1
        _ ≤ Kψ * (y : ℝ) := Chebyshev.psi_le_const_mul_self hypos.le
        _ ≤ _ := mul_le_mul_of_nonneg_left hys hKψ.le
    let L := Real.log (x : ℝ)
    let u := Real.sqrt L
    have hL0 : 0 ≤ L := by dsimp [L]; linarith
    have hu0 : 0 ≤ u := Real.sqrt_nonneg L
    have husq : u ^ 2 = L := Real.sq_sqrt hL0
    have hu2 : 2 ≤ u := by
      apply (sq_le_sq₀ (by norm_num) hu0).mp
      dsimp [L] at husq
      nlinarith
    have hcu : c * u ≤ L / 2 := by
      have hh := mul_le_mul_of_nonneg_right hc1 hu0
      nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu2)]
    have hsqrt : Real.sqrt (x : ℝ) ≤
        (x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ))) := by
      calc
        _ = Real.exp (L / 2) := by
          rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hxpos]
          congr 1
          dsimp [L]
          ring
        _ ≤ Real.exp (L - c * u) := Real.exp_le_exp.mpr (by linarith)
        _ = _ := by
          rw [show L - c * u = L + (-c * u) by ring, Real.exp_add]
          dsimp [L, u]
          rw [Real.exp_log hxpos]
    calc
      _ ≤ Kψ * Real.sqrt (x : ℝ) := hlinear
      _ ≤ Kψ * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) :=
        mul_le_mul_of_nonneg_left hsqrt hKψ.le
      _ ≤ C * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) :=
        mul_le_mul_of_nonneg_right (by unfold C; linarith) (by positivity)
  · have hyLarge : Real.sqrt (x : ℝ) < (y : ℝ) := lt_of_not_ge hys
    let L := Real.log (x : ℝ)
    let l := Real.log (y : ℝ)
    have hL0 : 0 ≤ L := by dsimp [L]; linarith
    have hl0 : 0 ≤ l := Real.log_natCast_nonneg y
    have hhalf : L / 2 ≤ l := by
      calc
        _ = Real.log (Real.sqrt (x : ℝ)) := (Real.log_sqrt hxpos.le).symm
        _ ≤ _ := Real.log_le_log (Real.sqrt_pos.mpr hxpos) hyLarge.le
    have hsqrt : Real.sqrt L / 2 ≤ Real.sqrt l := by
      apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg l)).mp
      rw [div_pow, Real.sq_sqrt hL0, Real.sq_sqrt hl0]
      nlinarith
    have hQy : (Q : ℝ) ≤ siegelWalfiszHeight y := hQheight.trans (Real.exp_le_exp.mpr hsqrt)
    have hXsy : Xs ≤ y := by exact_mod_cast (hXsRoot.trans hyLarge.le)
    let χ : PrimitiveCharacter :=
      ⟨d, hd, ψ.1, ψ.2, primitiveCharacter_ne_one_of_one_lt hd ψ⟩
    have hpointY := hpointB y hXsy hQy χ hdQ hcop
    have hdecayScale : c * Real.sqrt L ≤ c₀ * Real.sqrt l := by
      calc
        _ ≤ (c₀ / 2) * Real.sqrt L := mul_le_mul_of_nonneg_right hcc₀ (Real.sqrt_nonneg L)
        _ = c₀ * (Real.sqrt L / 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt hc₀.le
    have hdecay : Real.exp (-c₀ * Real.sqrt l) ≤ Real.exp (-c * Real.sqrt L) :=
      Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ C₀ * ((y : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (y : ℝ)))) := hpointY
      _ ≤ C₀ * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (by exact_mod_cast hyb.2) hdecay (Real.exp_pos _).le (Nat.cast_nonneg x)) hC₀.le
      _ ≤ C * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) :=
        mul_le_mul_of_nonneg_right (by unfold C; linarith) (by positivity)

end Erdos4.FGKMT
