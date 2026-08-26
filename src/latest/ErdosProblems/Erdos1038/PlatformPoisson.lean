import ErdosProblems.Erdos1038.PlatformAngularMonotonicity

/-!
# Poisson coordinates for the constant-platform adjoint

Exterior points of `[a,2]` are parametrized by a number `ρ ∈ (0,1)`.
In angular coordinates the Cauchy factor `Kₓ / (d(θ)-x)` is exactly the
Poisson kernel.  This file records that identity and its endpoint
consequences for the adjoint density.
-/

open Set

namespace Erdos1038

noncomputable section

def platformRho (a x : ℝ) : ℝ :=
  platformRadius a /
    (platformCenter a - x + platformCrossingScale a x)

def platformPoissonKernel (rho θ : ℝ) : ℝ :=
  (1 - rho ^ 2) / (1 - 2 * rho * Real.cos θ + rho ^ 2)

lemma platformCenter_sub_x_sq_sub_radius_sq (a x : ℝ) :
    (platformCenter a - x) ^ 2 - platformRadius a ^ 2 =
      (a - x) * (2 - x) := by
  simp only [platformCenter, platformRadius]
  ring

lemma platformCrossingScale_sq {a x : ℝ} (hx : x < a) (ha2 : a < 2) :
    platformCrossingScale a x ^ 2 = (a - x) * (2 - x) := by
  unfold platformCrossingScale
  exact Real.sq_sqrt (mul_nonneg (sub_pos.mpr hx).le
    (sub_pos.mpr (hx.trans ha2)).le)

lemma platformRho_pos {a x : ℝ} (hx : x < a) (ha2 : a < 2) :
    0 < platformRho a x := by
  apply div_pos (platformRadius_pos ha2)
  have hK := platformCrossingScale_pos hx ha2
  have hz : 0 < platformCenter a - x := by
    have hc : a < platformCenter a := by
      simp [platformCenter]
      linarith
    linarith
  exact add_pos hz hK

lemma platformRho_lt_one {a x : ℝ} (hx : x < a) (ha2 : a < 2) :
    platformRho a x < 1 := by
  have hr := platformRadius_pos ha2
  have hK := platformCrossingScale_pos hx ha2
  have hden : 0 < platformCenter a - x + platformCrossingScale a x := by
    have hc : a < platformCenter a := by
      simp [platformCenter]
      linarith
    have hz : 0 < platformCenter a - x := by linarith
    exact add_pos hz hK
  rw [platformRho, div_lt_one hden]
  have hleft := platformCenter_sub_radius a
  linarith

lemma platformRho_mem_Ioo {a x : ℝ} (hx : x < a) (ha2 : a < 2) :
    platformRho a x ∈ Ioo (0 : ℝ) 1 :=
  ⟨platformRho_pos hx ha2, platformRho_lt_one hx ha2⟩

lemma platformPoissonKernel_den_pos {rho θ : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    0 < 1 - 2 * rho * Real.cos θ + rho ^ 2 := by
  have hcos : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hfirst : 0 < (1 - rho) ^ 2 := sq_pos_of_ne_zero (by linarith)
  have hsecond : 0 ≤ 2 * rho * (1 - Real.cos θ) :=
    mul_nonneg (mul_nonneg (by norm_num) hrho0) (sub_nonneg.mpr hcos)
  nlinarith

lemma platformRho_center_identity {a x : ℝ}
    (hx : x < a) (ha2 : a < 2) :
    2 * platformRho a x * (platformCenter a - x) =
      platformRadius a * (1 + platformRho a x ^ 2) := by
  let z := platformCenter a - x
  let r := platformRadius a
  let K := platformCrossingScale a x
  let rho := platformRho a x
  change 2 * rho * z = r * (1 + rho ^ 2)
  have hr : 0 < r := platformRadius_pos ha2
  have hK : 0 < K := platformCrossingScale_pos hx ha2
  have hz : 0 < z := by
    have hc : a < platformCenter a := by
      simp [platformCenter]
      linarith
    dsimp [z]
    linarith
  have hden : z + K ≠ 0 := (add_pos hz hK).ne'
  have hrho : rho * (z + K) = r := by
    change (r / (z + K)) * (z + K) = r
    exact div_mul_cancel₀ r hden
  have hKsq : K ^ 2 = z ^ 2 - r ^ 2 := by
    dsimp [K, z, r]
    rw [platformCrossingScale_sq hx ha2,
      platformCenter_sub_x_sq_sub_radius_sq]
  have hlinear : rho * K = r - rho * z := by
    nlinarith [hrho]
  have hsquare := congrArg (fun y : ℝ ↦ y ^ 2) hlinear
  change (rho * K) ^ 2 = (r - rho * z) ^ 2 at hsquare
  ring_nf at hsquare hKsq ⊢
  nlinarith

lemma platformRho_crossing_identity {a x : ℝ}
    (hx : x < a) (ha2 : a < 2) :
    2 * platformRho a x * platformCrossingScale a x =
      platformRadius a * (1 - platformRho a x ^ 2) := by
  let z := platformCenter a - x
  let r := platformRadius a
  let K := platformCrossingScale a x
  let rho := platformRho a x
  change 2 * rho * K = r * (1 - rho ^ 2)
  have hrho0 : 0 < rho := platformRho_pos hx ha2
  have hcenter := platformRho_center_identity hx ha2
  change 2 * rho * z = r * (1 + rho ^ 2) at hcenter
  have hden : z + K ≠ 0 := by
    have hz : 0 < z := by
      have hc : a < platformCenter a := by
        simp [platformCenter]
        linarith
      dsimp [z]
      linarith
    exact (add_pos hz (platformCrossingScale_pos hx ha2)).ne'
  have hrho : rho * (z + K) = r := by
    change (r / (z + K)) * (z + K) = r
    exact div_mul_cancel₀ r hden
  nlinarith

theorem platformCrossingScale_div_distance_eq_poisson
    {a x θ : ℝ} (hx : x < a) (ha2 : a < 2)
    (hθ : θ ∈ Icc 0 Real.pi) :
    platformCrossingScale a x / (platformAngularDistance a θ - x) =
      platformPoissonKernel (platformRho a x) θ := by
  have hrho := platformRho_mem_Ioo hx ha2
  have hdmem := platformAngularDistance_mem_Icc ha2.le hθ
  have hdistance : 0 < platformAngularDistance a θ - x := by
    linarith [hdmem.1]
  have hpden := platformPoissonKernel_den_pos (θ := θ) hrho.1.le hrho.2
  have hcenter := platformRho_center_identity hx ha2
  have hcrossing := platformRho_crossing_identity hx ha2
  have hradius : 0 < platformRadius a := platformRadius_pos ha2
  have hcoreMul :
      platformRadius a *
          (platformCrossingScale a x * (1 + platformRho a x ^ 2) -
            (platformCenter a - x) * (1 - platformRho a x ^ 2)) = 0 := by
    linear_combination
      -platformCrossingScale a x * hcenter +
        (platformCenter a - x) * hcrossing
  have hcore :
      platformCrossingScale a x * (1 + platformRho a x ^ 2) =
        (platformCenter a - x) * (1 - platformRho a x ^ 2) := by
    have hzero := (mul_eq_zero.mp hcoreMul).resolve_left hradius.ne'
    exact sub_eq_zero.mp hzero
  unfold platformPoissonKernel
  apply (div_eq_div_iff hdistance.ne' hpden.ne').2
  unfold platformAngularDistance
  linear_combination hcore - Real.cos θ * hcrossing

@[simp]
lemma platformPoissonKernel_zero {rho : ℝ} (hrho : rho ≠ 1) :
    platformPoissonKernel rho 0 = (1 + rho) / (1 - rho) := by
  unfold platformPoissonKernel
  simp only [Real.cos_zero]
  have hne : 1 - rho ≠ 0 := sub_ne_zero.mpr hrho.symm
  rw [show 1 - 2 * rho * 1 + rho ^ 2 = (1 - rho) ^ 2 by ring]
  field_simp [hne]
  ring

@[simp]
lemma platformPoissonKernel_pi {rho : ℝ} (hrho : rho ≠ -1) :
    platformPoissonKernel rho Real.pi = (1 - rho) / (1 + rho) := by
  unfold platformPoissonKernel
  rw [Real.cos_pi]
  have hne : 1 + rho ≠ 0 := by
    intro hzero
    apply hrho
    linarith
  rw [show 1 - 2 * rho * -1 + rho ^ 2 = (1 + rho) ^ 2 by ring]
  field_simp [hne]
  ring

lemma platformPoissonKernel_zero_sub_pi {rho : ℝ}
    (hrhoOne : rho ≠ 1) (hrhoNegOne : rho ≠ -1) :
    platformPoissonKernel rho 0 - platformPoissonKernel rho Real.pi =
      4 * rho / (1 - rho ^ 2) := by
  rw [platformPoissonKernel_zero hrhoOne,
    platformPoissonKernel_pi hrhoNegOne]
  have hone : 1 - rho ≠ 0 := sub_ne_zero.mpr hrhoOne.symm
  have hneg : 1 + rho ≠ 0 := by
    intro hzero
    apply hrhoNegOne
    linarith
  rw [show 1 - rho ^ 2 = (1 - rho) * (1 + rho) by ring]
  field_simp [hone, hneg]
  ring

lemma adjointNormalization_eq_poisson_zero
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2) :
    adjointNormalization a xMinus xPlus sigmaMinus sigmaPlus =
      sigmaMinus * platformPoissonKernel (platformRho a xMinus) 0 +
        sigmaPlus * platformPoissonKernel (platformRho a xPlus) 0 := by
  have hminus := platformCrossingScale_div_distance_eq_poisson
    hxMinus ha2 (show (0 : ℝ) ∈ Icc 0 Real.pi from
      ⟨le_rfl, Real.pi_pos.le⟩)
  have hplus := platformCrossingScale_div_distance_eq_poisson
    hxPlus ha2 (show (0 : ℝ) ∈ Icc 0 Real.pi from
      ⟨le_rfl, Real.pi_pos.le⟩)
  simp only [platformAngularDistance_zero] at hminus hplus
  unfold adjointNormalization
  rw [show sigmaMinus * platformCrossingScale a xMinus / (a - xMinus) =
      sigmaMinus * (platformCrossingScale a xMinus / (a - xMinus)) by ring,
    show sigmaPlus * platformCrossingScale a xPlus / (a - xPlus) =
      sigmaPlus * (platformCrossingScale a xPlus / (a - xPlus)) by ring]
  rw [hminus, hplus]

theorem platformAngularAdjointDensity_eq_poisson
    {a xMinus xPlus sigmaMinus sigmaPlus θ : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    (hθ : θ ∈ Icc 0 Real.pi) :
    platformAngularAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus θ =
      sigmaMinus *
          (platformPoissonKernel (platformRho a xMinus) 0 -
            platformPoissonKernel (platformRho a xMinus) θ) +
        sigmaPlus *
          (platformPoissonKernel (platformRho a xPlus) 0 -
            platformPoissonKernel (platformRho a xPlus) θ) := by
  have hminus := platformCrossingScale_div_distance_eq_poisson
    hxMinus ha2 hθ
  have hplus := platformCrossingScale_div_distance_eq_poisson
    hxPlus ha2 hθ
  unfold platformAngularAdjointDensity adjointNumerator
  rw [adjointNormalization_eq_poisson_zero hxMinus hxPlus ha2,
    show sigmaMinus * platformCrossingScale a xMinus /
        (platformAngularDistance a θ - xMinus) =
      sigmaMinus * (platformCrossingScale a xMinus /
        (platformAngularDistance a θ - xMinus)) by ring,
    show sigmaPlus * platformCrossingScale a xPlus /
        (platformAngularDistance a θ - xPlus) =
      sigmaPlus * (platformCrossingScale a xPlus /
        (platformAngularDistance a θ - xPlus)) by ring,
    hminus, hplus]
  ring

theorem platformBPi_eq_rho
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2) :
    platformBPi a xMinus xPlus sigmaMinus sigmaPlus =
      4 * sigmaMinus * platformRho a xMinus /
          (1 - platformRho a xMinus ^ 2) +
        4 * sigmaPlus * platformRho a xPlus /
          (1 - platformRho a xPlus ^ 2) := by
  have hrm := platformRho_mem_Ioo hxMinus ha2
  have hrp := platformRho_mem_Ioo hxPlus ha2
  rw [platformBPi, platformAngularAdjointDensity_eq_poisson
    hxMinus hxPlus ha2 ⟨Real.pi_pos.le, le_rfl⟩,
    platformPoissonKernel_zero_sub_pi (ne_of_lt hrm.2)
      (ne_of_gt ((show (-1 : ℝ) < 0 by norm_num).trans hrm.1)),
    platformPoissonKernel_zero_sub_pi (ne_of_lt hrp.2)
      (ne_of_gt ((show (-1 : ℝ) < 0 by norm_num).trans hrp.1))]
  ring

end

end Erdos1038
