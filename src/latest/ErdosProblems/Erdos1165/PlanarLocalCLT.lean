/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.OffDiagonal
import ErdosProblems.Erdos1165.BinomialGaussian

/-!
# Uniform planar local central-limit estimates

The diagonal coordinates `x.1 + x.2` and `x.1 - x.2` of planar simple random
walk are independent one-dimensional sign walks.  This file combines the
exact endpoint factorization from `OffDiagonal` with the explicit uniform
binomial estimates in `BinomialGaussian`.

At time `2n`, put

`d₊ = |x.1 + x.2| / 2`,  `d₋ = |x.1 - x.2| / 2`.

For an admissible endpoint and in the window `2 d₊, 2 d₋ ≤ n`, the endpoint
mass, multiplied by its Gaussian normalization, lies between `exp (-E)` and
`exp E`.  The error `E` is completely explicit and is
`O((d₊³+d₋³)/n² + (d₊²+d₋²)/n² + 1/n)`.  Thus it is uniform throughout every
window whose diagonal radius is `o(n^(2/3))`.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.PlanarLocalCLT

open BinomialGaussian

/-- Absolute value of the first diagonal coordinate. -/
def diagonalPlusAbs (x : Point) : ℕ := (x.1 + x.2).natAbs

/-- Absolute value of the second diagonal coordinate. -/
def diagonalMinusAbs (x : Point) : ℕ := (x.1 - x.2).natAbs

/-- Half of the absolute first diagonal coordinate.  At an even-time admissible
endpoint the division is exact. -/
def diagonalPlusHalf (x : Point) : ℕ := diagonalPlusAbs x / 2

/-- Half of the absolute second diagonal coordinate. -/
def diagonalMinusHalf (x : Point) : ℕ := diagonalMinusAbs x / 2

/-- The real-valued endpoint mass at the even time `2n`. -/
noncomputable def evenPlanarEndpointMass (n : ℕ) (x : Point) : ℝ :=
  (simpleRandomWalk {s | s (2 * n) = x}).toReal

/-- The one-coordinate error appearing in the explicit binomial local CLT. -/
noncomputable def coordinateGaussianError (n d : ℕ) : ℝ :=
  8 * n * |relativeDeviation n d| ^ 3 + relativeDeviation n d ^ 2 +
    (1 : ℝ) / (6 * (n - d))

/-- Sum of the two diagonal-coordinate errors. -/
noncomputable def planarGaussianError (n : ℕ) (x : Point) : ℝ :=
  coordinateGaussianError n (diagonalPlusHalf x) +
    coordinateGaussianError n (diagonalMinusHalf x)

/-- A common error bound for all endpoints whose two diagonal half-distances
are at most `D`. -/
noncomputable def uniformPlanarGaussianError (n D : ℕ) : ℝ :=
  16 * (D : ℝ) ^ 3 / (n : ℝ) ^ 2 + 2 * (D : ℝ) ^ 2 / (n : ℝ) ^ 2 +
    (1 : ℝ) / (3 * (n - D))

/-- The planar endpoint mass after multiplying by the lattice Gaussian
normalization in diagonal coordinates. -/
noncomputable def normalizedEvenPlanarEndpointMass (n : ℕ) (x : Point) : ℝ :=
  evenPlanarEndpointMass n x * (Real.pi * n) *
    Real.exp ((((diagonalPlusHalf x : ℕ) : ℝ) ^ 2 +
      ((diagonalMinusHalf x : ℕ) : ℝ) ^ 2) / n)

/-- The Cartesian Gaussian exponent `|x|²/(2n)` appropriate at time `2n`. -/
noncomputable def cartesianGaussianExponent (n : ℕ) (x : Point) : ℝ :=
  ((((x.1 : ℤ) : ℝ) ^ 2 + ((x.2 : ℤ) : ℝ) ^ 2) / (2 * (n : ℝ)))

lemma oneDimMinorityIndex_even (n : ℕ) (z : ℤ)
    (h : OneDimAdmissible (2 * n) z) :
    oneDimMinorityIndex (2 * n) z = n - z.natAbs / 2 := by
  unfold OneDimAdmissible at h
  unfold oneDimMinorityIndex
  obtain ⟨a, ha⟩ := Nat.even_iff.mpr h.2
  omega

lemma diagonalPlusAbs_even {n : ℕ} {x : Point}
    (h : PlanarAdmissible (2 * n) x) : diagonalPlusAbs x % 2 = 0 := by
  unfold PlanarAdmissible OneDimAdmissible at h
  unfold diagonalPlusAbs
  omega

lemma diagonalMinusAbs_even {n : ℕ} {x : Point}
    (h : PlanarAdmissible (2 * n) x) : diagonalMinusAbs x % 2 = 0 := by
  unfold PlanarAdmissible OneDimAdmissible at h
  unfold diagonalMinusAbs
  omega

lemma diagonalPlusAbs_eq_two_mul_half {n : ℕ} {x : Point}
    (h : PlanarAdmissible (2 * n) x) :
    diagonalPlusAbs x = 2 * diagonalPlusHalf x := by
  have heven := diagonalPlusAbs_even h
  unfold diagonalPlusHalf
  omega

lemma diagonalMinusAbs_eq_two_mul_half {n : ℕ} {x : Point}
    (h : PlanarAdmissible (2 * n) x) :
    diagonalMinusAbs x = 2 * diagonalMinusHalf x := by
  have heven := diagonalMinusAbs_even h
  unfold diagonalMinusHalf
  omega

lemma diagonalPlusHalf_le {n : ℕ} {x : Point}
    (h : PlanarAdmissible (2 * n) x) : diagonalPlusHalf x ≤ n := by
  have hrange := h.1.1
  change diagonalPlusAbs x ≤ 2 * n at hrange
  rw [diagonalPlusAbs_eq_two_mul_half h] at hrange
  omega

lemma diagonalMinusHalf_le {n : ℕ} {x : Point}
    (h : PlanarAdmissible (2 * n) x) : diagonalMinusHalf x ≤ n := by
  have hrange := h.2.1
  change diagonalMinusAbs x ≤ 2 * n at hrange
  rw [diagonalMinusAbs_eq_two_mul_half h] at hrange
  omega

/-- The diagonal quadratic form is the Cartesian quadratic form divided by
two.  The parity hypothesis is exactly what makes the half-diagonal
coordinates integral. -/
lemma diagonalHalf_sq_sum_eq_cartesian_half {n : ℕ} {x : Point}
    (h : PlanarAdmissible (2 * n) x) :
    ((diagonalPlusHalf x : ℕ) : ℝ) ^ 2 +
        ((diagonalMinusHalf x : ℕ) : ℝ) ^ 2 =
      ((((x.1 : ℤ) : ℝ) ^ 2 + ((x.2 : ℤ) : ℝ) ^ 2) / 2) := by
  have hpNat := diagonalPlusAbs_eq_two_mul_half h
  have hmNat := diagonalMinusAbs_eq_two_mul_half h
  have hpReal : |(((x.1 + x.2 : ℤ) : ℝ))| =
      2 * ((diagonalPlusHalf x : ℕ) : ℝ) := by
    have hpCast := congrArg (fun k : ℕ ↦ (k : ℝ)) hpNat
    simpa [diagonalPlusAbs] using hpCast
  have hmReal : |(((x.1 - x.2 : ℤ) : ℝ))| =
      2 * ((diagonalMinusHalf x : ℕ) : ℝ) := by
    have hmCast := congrArg (fun k : ℕ ↦ (k : ℝ)) hmNat
    simpa [diagonalMinusAbs] using hmCast
  have hpSq := congrArg (fun t : ℝ ↦ t ^ 2) hpReal
  have hmSq := congrArg (fun t : ℝ ↦ t ^ 2) hmReal
  simp only [sq_abs] at hpSq hmSq
  push_cast at hpSq hmSq
  nlinarith [hpSq, hmSq]

lemma diagonalGaussianExponent_eq_cartesian {n : ℕ} {x : Point}
    (hn : 0 < n) (h : PlanarAdmissible (2 * n) x) :
    ((((diagonalPlusHalf x : ℕ) : ℝ) ^ 2 +
        ((diagonalMinusHalf x : ℕ) : ℝ) ^ 2) / n) =
      cartesianGaussianExponent n x := by
  unfold cartesianGaussianExponent
  rw [diagonalHalf_sq_sum_eq_cartesian_half h]
  field_simp

/-- A one-dimensional admissible endpoint mass at even time, converted to
`ℝ`, is exactly the centered binomial mass. -/
lemma oneDimEndpointMass_toReal_even {n : ℕ} {z : ℤ}
    (h : OneDimAdmissible (2 * n) z) :
    (oneDimEndpointMass (2 * n) z).toReal =
      evenSymmetricMass n (z.natAbs / 2) := by
  have hd : z.natAbs / 2 ≤ n := by
    have hrange := h.1
    have heq : z.natAbs = 2 * (z.natAbs / 2) := by
      obtain ⟨a, ha⟩ := Nat.even_iff.mpr h.2
      omega
    rw [heq] at hrange
    omega
  rw [oneDimEndpointMass, oneDimEndpointCount_of_admissible h,
    oneDimMinorityIndex_even n z h]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat]
  exact evenSymmetricMass_sub_eq_add hd

/-- Exact real product formula for the planar endpoint mass at an admissible
even-time endpoint. -/
theorem evenPlanarEndpointMass_eq_product {n : ℕ} {x : Point}
    (h : PlanarAdmissible (2 * n) x) :
    evenPlanarEndpointMass n x =
      evenSymmetricMass n (diagonalPlusHalf x) *
        evenSymmetricMass n (diagonalMinusHalf x) := by
  rw [evenPlanarEndpointMass, simpleRandomWalk_endpoint_apply_product,
    ENNReal.toReal_mul]
  rw [oneDimEndpointMass_toReal_even h.1, oneDimEndpointMass_toReal_even h.2]
  rfl

private lemma normalizedEvenPlanarEndpointMass_eq_product {n : ℕ} {x : Point}
    (hn : 0 < n) (h : PlanarAdmissible (2 * n) x) :
    normalizedEvenPlanarEndpointMass n x =
      (evenSymmetricMass n (diagonalPlusHalf x) * Real.sqrt (Real.pi * n) *
        Real.exp (((diagonalPlusHalf x : ℕ) : ℝ) ^ 2 / n)) *
      (evenSymmetricMass n (diagonalMinusHalf x) * Real.sqrt (Real.pi * n) *
        Real.exp (((diagonalMinusHalf x : ℕ) : ℝ) ^ 2 / n)) := by
  rw [normalizedEvenPlanarEndpointMass, evenPlanarEndpointMass_eq_product h]
  have hsqrt : Real.sqrt (Real.pi * n) ^ 2 = Real.pi * n :=
    Real.sq_sqrt (by positivity)
  have hexp :
      Real.exp ((((diagonalPlusHalf x : ℕ) : ℝ) ^ 2 +
          ((diagonalMinusHalf x : ℕ) : ℝ) ^ 2) / n) =
        Real.exp (((diagonalPlusHalf x : ℕ) : ℝ) ^ 2 / n) *
          Real.exp (((diagonalMinusHalf x : ℕ) : ℝ) ^ 2 / n) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
  rw [hexp]
  calc
    evenSymmetricMass n (diagonalPlusHalf x) *
          evenSymmetricMass n (diagonalMinusHalf x) * (Real.pi * n) *
        (Real.exp (((diagonalPlusHalf x : ℕ) : ℝ) ^ 2 / n) *
          Real.exp (((diagonalMinusHalf x : ℕ) : ℝ) ^ 2 / n)) =
        evenSymmetricMass n (diagonalPlusHalf x) *
          evenSymmetricMass n (diagonalMinusHalf x) *
            (Real.sqrt (Real.pi * n) ^ 2) *
        (Real.exp (((diagonalPlusHalf x : ℕ) : ℝ) ^ 2 / n) *
          Real.exp (((diagonalMinusHalf x : ℕ) : ℝ) ^ 2 / n)) := by rw [hsqrt]
    _ = _ := by ring_nf

/-- **Uniform planar Gaussian local estimate.**  The statement is finite and
fully explicit.  The moderate window is imposed separately on the two
diagonal coordinates, exactly as required by the one-dimensional estimate. -/
theorem normalizedEvenPlanarEndpointMass_bounds {n : ℕ} {x : Point}
    (hn : 0 < n) (hadm : PlanarAdmissible (2 * n) x)
    (hplus : 2 * diagonalPlusHalf x ≤ n)
    (hminus : 2 * diagonalMinusHalf x ≤ n) :
    Real.exp (-planarGaussianError n x) ≤ normalizedEvenPlanarEndpointMass n x ∧
      normalizedEvenPlanarEndpointMass n x ≤ Real.exp (planarGaussianError n x) := by
  have hdplus : diagonalPlusHalf x < n := by omega
  have hdminus : diagonalMinusHalf x < n := by omega
  have hp := evenSymmetricMass_gaussian_bounds hn hdplus hplus
  have hm := evenSymmetricMass_gaussian_bounds hn hdminus hminus
  dsimp only at hp hm
  rw [normalizedEvenPlanarEndpointMass_eq_product hn hadm]
  unfold planarGaussianError
  constructor
  · rw [neg_add, Real.exp_add]
    change Real.exp (-(8 * n * |relativeDeviation n (diagonalPlusHalf x)| ^ 3 +
          relativeDeviation n (diagonalPlusHalf x) ^ 2 +
          1 / (6 * (n - diagonalPlusHalf x)))) *
        Real.exp (-(8 * n * |relativeDeviation n (diagonalMinusHalf x)| ^ 3 +
          relativeDeviation n (diagonalMinusHalf x) ^ 2 +
          1 / (6 * (n - diagonalMinusHalf x)))) ≤ _
    exact mul_le_mul hp.1 hm.1 (Real.exp_pos _).le
      (mul_nonneg
        (mul_nonneg (evenSymmetricMass_pos hdplus.le).le (Real.sqrt_nonneg _))
        (Real.exp_pos _).le)
  · rw [Real.exp_add]
    change _ ≤
      Real.exp (8 * n * |relativeDeviation n (diagonalPlusHalf x)| ^ 3 +
          relativeDeviation n (diagonalPlusHalf x) ^ 2 +
          1 / (6 * (n - diagonalPlusHalf x))) *
        Real.exp (8 * n * |relativeDeviation n (diagonalMinusHalf x)| ^ 3 +
          relativeDeviation n (diagonalMinusHalf x) ^ 2 +
          1 / (6 * (n - diagonalMinusHalf x)))
    exact mul_le_mul hp.2 hm.2
      (mul_nonneg
        (mul_nonneg (evenSymmetricMass_pos hdminus.le).le (Real.sqrt_nonneg _))
        (Real.exp_pos _).le)
      (Real.exp_pos _).le

lemma coordinateGaussianError_eq {n d : ℕ} (hn : 0 < n) :
    coordinateGaussianError n d =
      8 * (d : ℝ) ^ 3 / (n : ℝ) ^ 2 +
        (d : ℝ) ^ 2 / (n : ℝ) ^ 2 + (1 : ℝ) / (6 * (n - d)) := by
  unfold coordinateGaussianError relativeDeviation
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ) / n)]
  field_simp

lemma coordinateGaussianError_nonneg {n d : ℕ} (hd : d < n) :
    0 ≤ coordinateGaussianError n d := by
  rw [coordinateGaussianError_eq (Nat.zero_lt_of_lt hd)]
  have hsub : (0 : ℝ) < (n : ℝ) - d := sub_pos.mpr (by exact_mod_cast hd)
  positivity

lemma coordinateGaussianError_le_radius {n d D : ℕ}
    (hn : 0 < n) (hdD : d ≤ D) (hDn : D < n) :
    coordinateGaussianError n d ≤
      8 * (D : ℝ) ^ 3 / (n : ℝ) ^ 2 +
        (D : ℝ) ^ 2 / (n : ℝ) ^ 2 + (1 : ℝ) / (6 * (n - D)) := by
  have hdn : d < n := hdD.trans_lt hDn
  rw [coordinateGaussianError_eq hn]
  have hnR : (0 : ℝ) < n := by positivity
  have hpow2 : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
  have hdR : (0 : ℝ) ≤ d := by positivity
  have hDR : (d : ℝ) ≤ D := by exact_mod_cast hdD
  have hcubic : (d : ℝ) ^ 3 ≤ (D : ℝ) ^ 3 := by gcongr
  have hquad : (d : ℝ) ^ 2 ≤ (D : ℝ) ^ 2 := by gcongr
  have hsub : n - D ≤ n - d := Nat.sub_le_sub_left hdD n
  have hsubpos : (0 : ℝ) < n - D := by
    exact sub_pos.mpr (by exact_mod_cast hDn)
  have hinv : (1 : ℝ) / (6 * (n - d)) ≤ 1 / (6 * (n - D)) := by
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith
  gcongr

/-- The sum of the two coordinate errors is bounded uniformly by the advertised
`D³/n²` expression throughout a diagonal box of radius `D`. -/
theorem planarGaussianError_le_uniform {n D : ℕ} {x : Point}
    (hn : 0 < n) (hDn : D < n)
    (hp : diagonalPlusHalf x ≤ D) (hm : diagonalMinusHalf x ≤ D) :
    planarGaussianError n x ≤ uniformPlanarGaussianError n D := by
  have hp' := coordinateGaussianError_le_radius hn hp hDn
  have hm' := coordinateGaussianError_le_radius hn hm hDn
  unfold planarGaussianError uniformPlanarGaussianError
  calc
    coordinateGaussianError n (diagonalPlusHalf x) +
        coordinateGaussianError n (diagonalMinusHalf x) ≤
      (8 * (D : ℝ) ^ 3 / (n : ℝ) ^ 2 +
          (D : ℝ) ^ 2 / (n : ℝ) ^ 2 + (1 : ℝ) / (6 * (n - D))) +
        (8 * (D : ℝ) ^ 3 / (n : ℝ) ^ 2 +
          (D : ℝ) ^ 2 / (n : ℝ) ^ 2 + (1 : ℝ) / (6 * (n - D))) :=
      add_le_add hp' hm'
    _ = 16 * (D : ℝ) ^ 3 / (n : ℝ) ^ 2 +
        2 * (D : ℝ) ^ 2 / (n : ℝ) ^ 2 + (1 : ℝ) / (3 * (n - D)) := by
      have hsub : (0 : ℝ) < n - D := by
        exact sub_pos.mpr (by exact_mod_cast hDn)
      field_simp
      ring_nf

/-- The uniform error tends to zero whenever `n → ∞`, `D³/n² → 0`, and
eventually `2D ≤ n`.  This is the precise cubic formulation of the uniform
`D = o(n^(2/3))` regime, avoiding any rounding convention for `n^(2/3)`. -/
theorem tendsto_uniformPlanarGaussianError_zero_of_cubic
    {α : Type*} {l : Filter α} {n D : α → ℕ}
    (hn : Tendsto n l atTop)
    (hcubic : Tendsto (fun i ↦ (D i : ℝ) ^ 3 / (n i : ℝ) ^ 2) l (nhds 0))
    (hmoderate : ∀ᶠ i in l, 2 * D i ≤ n i) :
    Tendsto (fun i ↦ uniformPlanarGaussianError (n i) (D i)) l (nhds 0) := by
  have hquad : Tendsto (fun i ↦ (D i : ℝ) ^ 2 / (n i : ℝ) ^ 2) l (nhds 0) := by
    refine squeeze_zero (fun i ↦ by positivity) (fun i ↦ ?_) hcubic
    apply div_le_div_of_nonneg_right
    · by_cases hD : D i = 0
      · simp [hD]
      · have hDone : (1 : ℝ) ≤ D i := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hD)
        calc
          (D i : ℝ) ^ 2 ≤ (D i : ℝ) ^ 2 * D i :=
            le_mul_of_one_le_right (sq_nonneg _) hDone
          _ = (D i : ℝ) ^ 3 := by ring_nf
    · positivity
  have hsubNat : Tendsto (fun i ↦ n i - D i) l atTop := by
    rw [tendsto_atTop] at hn ⊢
    intro b
    filter_upwards [hn (2 * b), hmoderate] with i hni hmod
    omega
  have hsubReal : Tendsto (fun i ↦ ((n i - D i : ℕ) : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hsubNat
  have hrecipRaw : Tendsto
      (fun i ↦ (1 / 3 : ℝ) * (((n i - D i : ℕ) : ℝ))⁻¹) l (nhds 0) :=
    by simpa using hsubReal.inv_tendsto_atTop.const_mul (1 / 3 : ℝ)
  have hrecip : Tendsto
      (fun i ↦ (1 : ℝ) / (3 * (n i - D i))) l (nhds 0) := by
    refine hrecipRaw.congr' ?_
    filter_upwards [hmoderate] with i hi
    have hDi : D i ≤ n i := by omega
    rw [Nat.cast_sub hDi]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring_nf
  have hsum := ((hcubic.const_mul 16).add (hquad.const_mul 2)).add hrecip
  convert hsum using 1
  · funext i
    unfold uniformPlanarGaussianError
    ring_nf
  · ring_nf

/-- Radius-uniform version of the planar local CLT.  Its error tends to zero
whenever `D³/n² → 0` (equivalently, in the usual integral setting,
`D = o(n^(2/3))`) while `2D ≤ n`. -/
theorem normalizedEvenPlanarEndpointMass_uniform_bounds {n D : ℕ} {x : Point}
    (hn : 0 < n) (hadm : PlanarAdmissible (2 * n) x)
    (hDn : D < n) (hmoderate : 2 * D ≤ n)
    (hp : diagonalPlusHalf x ≤ D) (hm : diagonalMinusHalf x ≤ D) :
    Real.exp (-uniformPlanarGaussianError n D) ≤
        normalizedEvenPlanarEndpointMass n x ∧
      normalizedEvenPlanarEndpointMass n x ≤
        Real.exp (uniformPlanarGaussianError n D) := by
  have hplusModerate : 2 * diagonalPlusHalf x ≤ n :=
    (Nat.mul_le_mul_left 2 hp).trans hmoderate
  have hminusModerate : 2 * diagonalMinusHalf x ≤ n :=
    (Nat.mul_le_mul_left 2 hm).trans hmoderate
  have hlocal := normalizedEvenPlanarEndpointMass_bounds hn hadm
    hplusModerate hminusModerate
  have herr := planarGaussianError_le_uniform hn hDn hp hm
  constructor
  · exact (Real.exp_le_exp.mpr (neg_le_neg herr)).trans hlocal.1
  · exact hlocal.2.trans (Real.exp_le_exp.mpr herr)

/-- Cartesian-coordinate form of the radius-uniform local CLT.  The exponent
is `|x|²/(2n)`, as expected at time `2n`. -/
theorem evenPlanarEndpointMass_gaussian_uniform_bounds {n D : ℕ} {x : Point}
    (hn : 0 < n) (hadm : PlanarAdmissible (2 * n) x)
    (hDn : D < n) (hmoderate : 2 * D ≤ n)
    (hp : diagonalPlusHalf x ≤ D) (hm : diagonalMinusHalf x ≤ D) :
    Real.exp (-uniformPlanarGaussianError n D) ≤
        evenPlanarEndpointMass n x * (Real.pi * n) *
          Real.exp (cartesianGaussianExponent n x) ∧
      evenPlanarEndpointMass n x * (Real.pi * n) *
          Real.exp (cartesianGaussianExponent n x) ≤
        Real.exp (uniformPlanarGaussianError n D) := by
  have h := normalizedEvenPlanarEndpointMass_uniform_bounds hn hadm hDn hmoderate hp hm
  unfold normalizedEvenPlanarEndpointMass at h
  rw [diagonalGaussianExponent_eq_cartesian hn hadm] at h
  exact h

/-! ## A global Gaussian upper bound -/

/-- Exact adjacent-mass ratio for the centered symmetric binomial law. -/
lemma evenSymmetricMass_succ_eq {n d : ℕ} (hd : d < n) :
    evenSymmetricMass n (d + 1) = evenSymmetricMass n d *
      (((n - d : ℕ) : ℝ) / (n + d + 1)) := by
  have hchoose := Nat.choose_succ_right_eq (2 * n) (n + d)
  have hsub : 2 * n - (n + d) = n - d := by omega
  rw [hsub] at hchoose
  unfold evenSymmetricMass symBinomialMass
  rw [show n + (d + 1) = n + d + 1 by omega]
  have hcast := congrArg (fun k : ℕ ↦ (k : ℝ)) hchoose
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hcast
  have hden : (0 : ℝ) < n + d + 1 := by positivity
  field_simp
  nlinarith

private lemma adjacent_ratio_gaussian_le {n d : ℕ} (hn : 0 < n) (hd : d < n) :
    (((n - d : ℕ) : ℝ) / (n + d + 1)) ≤
      Real.exp (-((2 * d + 1 : ℕ) : ℝ) / (2 * n)) := by
  have hdn : d ≤ n := hd.le
  have hden : (0 : ℝ) < n + d + 1 := by positivity
  have htwoN : (0 : ℝ) < 2 * n := by positivity
  have hdenle : ((n + d + 1 : ℕ) : ℝ) ≤ 2 * n := by
    exact_mod_cast (by omega : n + d + 1 ≤ 2 * n)
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at hdenle
  have ht : ((2 * d + 1 : ℕ) : ℝ) / (2 * n) ≤
      ((2 * d + 1 : ℕ) : ℝ) / (n + d + 1) := by
    exact div_le_div_of_nonneg_left (by positivity) hden hdenle
  have hid : (((n - d : ℕ) : ℝ) / (n + d + 1)) =
      1 - ((2 * d + 1 : ℕ) : ℝ) / (n + d + 1) := by
    rw [Nat.cast_sub hdn]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    field_simp
    ring_nf
  rw [hid]
  exact (Real.one_sub_le_exp_neg _).trans
    (Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg ht))

/-- Global pointwise Gaussian decay away from the center.  Unlike the local
CLT bounds above, this estimate holds all the way to the edge of the support. -/
theorem evenSymmetricMass_global_gaussian_upper {n d : ℕ}
    (hn : 0 < n) (hd : d ≤ n) :
    evenSymmetricMass n d ≤ evenSymmetricMass n 0 *
      Real.exp (-((d : ℝ) ^ 2) / (2 * n)) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hdlt : d < n := by omega
      have hrec := evenSymmetricMass_succ_eq hdlt
      rw [hrec]
      have hratio := adjacent_ratio_gaussian_le hn hdlt
      have hratio_nonneg : (0 : ℝ) ≤ ((n - d : ℕ) : ℝ) / (n + d + 1) := by positivity
      calc
        evenSymmetricMass n d * (((n - d : ℕ) : ℝ) / (n + d + 1)) ≤
            (evenSymmetricMass n 0 * Real.exp (-((d : ℝ) ^ 2) / (2 * n))) *
              Real.exp (-((2 * d + 1 : ℕ) : ℝ) / (2 * n)) :=
          mul_le_mul (ih (by omega)) hratio hratio_nonneg
            (mul_nonneg (evenSymmetricMass_pos (by omega : 0 ≤ n)).le
              (Real.exp_pos _).le)
        _ = evenSymmetricMass n 0 *
            Real.exp (-(((d + 1 : ℕ) : ℝ) ^ 2) / (2 * n)) := by
          calc
            (evenSymmetricMass n 0 * Real.exp (-((d : ℝ) ^ 2) / (2 * n))) *
                Real.exp (-((2 * d + 1 : ℕ) : ℝ) / (2 * n)) =
              evenSymmetricMass n 0 *
                (Real.exp (-((d : ℝ) ^ 2) / (2 * n)) *
                  Real.exp (-((2 * d + 1 : ℕ) : ℝ) / (2 * n))) := by ring_nf
            _ = evenSymmetricMass n 0 *
                Real.exp (-(((d + 1 : ℕ) : ℝ) ^ 2) / (2 * n)) := by
              rw [← Real.exp_add]
              congr 2
              norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
              field_simp
              ring_nf

/-- Product global Gaussian upper bound for every admissible planar endpoint
at even time. -/
theorem evenPlanarEndpointMass_global_gaussian_upper {n : ℕ} {x : Point}
    (hn : 0 < n) (hadm : PlanarAdmissible (2 * n) x) :
    evenPlanarEndpointMass n x ≤
      evenSymmetricMass n 0 ^ 2 *
        Real.exp (-(cartesianGaussianExponent n x) / 2) := by
  rw [evenPlanarEndpointMass_eq_product hadm]
  have hp := evenSymmetricMass_global_gaussian_upper hn (diagonalPlusHalf_le hadm)
  have hm := evenSymmetricMass_global_gaussian_upper hn (diagonalMinusHalf_le hadm)
  have hnonneg : 0 ≤ evenSymmetricMass n (diagonalMinusHalf x) :=
    (evenSymmetricMass_pos (diagonalMinusHalf_le hadm)).le
  have hcenterMass : 0 < evenSymmetricMass n 0 :=
    evenSymmetricMass_pos (by omega)
  have hcenter : 0 ≤ evenSymmetricMass n 0 *
      Real.exp (-((diagonalPlusHalf x : ℕ) : ℝ) ^ 2 / (2 * n)) :=
    mul_nonneg hcenterMass.le (Real.exp_pos _).le
  calc
    evenSymmetricMass n (diagonalPlusHalf x) *
        evenSymmetricMass n (diagonalMinusHalf x) ≤
      (evenSymmetricMass n 0 *
          Real.exp (-((diagonalPlusHalf x : ℕ) : ℝ) ^ 2 / (2 * n))) *
        (evenSymmetricMass n 0 *
          Real.exp (-((diagonalMinusHalf x : ℕ) : ℝ) ^ 2 / (2 * n))) :=
      mul_le_mul hp hm hnonneg hcenter
    _ = evenSymmetricMass n 0 ^ 2 *
        Real.exp (-(cartesianGaussianExponent n x) / 2) := by
      calc
        (evenSymmetricMass n 0 *
              Real.exp (-((diagonalPlusHalf x : ℕ) : ℝ) ^ 2 / (2 * n))) *
            (evenSymmetricMass n 0 *
              Real.exp (-((diagonalMinusHalf x : ℕ) : ℝ) ^ 2 / (2 * n))) =
          evenSymmetricMass n 0 ^ 2 *
            (Real.exp (-((diagonalPlusHalf x : ℕ) : ℝ) ^ 2 / (2 * n)) *
              Real.exp (-((diagonalMinusHalf x : ℕ) : ℝ) ^ 2 / (2 * n))) := by ring_nf
        _ = evenSymmetricMass n 0 ^ 2 *
            Real.exp (-(cartesianGaussianExponent n x) / 2) := by
          rw [← Real.exp_add]
          congr 2
          have hdiag := diagonalGaussianExponent_eq_cartesian hn hadm
          field_simp at hdiag ⊢
          ring_nf at hdiag ⊢
          nlinarith

end Erdos1165.PlanarLocalCLT
