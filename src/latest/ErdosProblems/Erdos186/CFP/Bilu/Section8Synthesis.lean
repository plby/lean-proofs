/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.BadlyApproximable
import ErdosProblems.Erdos186.CFP.Bilu.DistortingMeasure
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# The measure synthesis in Bilu's Proposition 8.3

This file joins the two independent inputs used in Section 8 of Bilu's
proof.  Proposition 8.1 supplies a positive-measure set of distorting
points on the unit torus, while Lemma 6.8 chooses a badly approximable
system from any sequence of measurable sets whose volumes exceed its
explicit exceptional-set bound.

The bridge is the standard measurable fundamental domain `(0,1]^m` for
the unit torus.  It is important that the set passed to Lemma 6.8 lives in
the ambient real vector space, rather than in the quotient torus.
-/

namespace Erdos186.CFP.Bilu.Section8Synthesis

open scoped ENNReal
open MeasureTheory Set
open DistortingMeasure BadlyApproximable

/-- The half-open unit cube used as a measurable fundamental domain for
the unit torus. -/
def unitCubeIoc (m : ℕ) : Set (Fin m → ℝ) :=
  {x | ∀ i, x i ∈ Ioc 0 1}

/-- The coordinatewise quotient map from Euclidean space to the unit
torus. -/
def realToTorus {m : ℕ} (x : Fin m → ℝ) : Torus m :=
  fun i ↦ (x i : AddCircle (1 : ℝ))

/-- Real representatives in the fundamental cube of a measurable torus
set. -/
def cubeLift {m : ℕ} (S : Set (Torus m)) : Set (Fin m → ℝ) :=
  unitCubeIoc m ∩ realToTorus ⁻¹' S

theorem measurableSet_unitCubeIoc (m : ℕ) :
    MeasurableSet (unitCubeIoc m) := by
  exact MeasurableSet.univ_pi' fun _ ↦ measurableSet_Ioc

theorem measurable_realToTorus {m : ℕ} :
    Measurable (realToTorus : (Fin m → ℝ) → Torus m) := by
  exact measurable_pi_lambda _ fun i ↦
    AddCircle.measurable_mk'.comp (measurable_pi_apply i)

theorem measurableSet_cubeLift {m : ℕ} {S : Set (Torus m)}
    (hS : MeasurableSet S) : MeasurableSet (cubeLift S) := by
  exact (measurableSet_unitCubeIoc m).inter (hS.preimage measurable_realToTorus)

/-- Lebesgue volume in the fundamental cube is normalized Haar measure
on the unit torus. -/
theorem volume_cubeLift {m : ℕ} {S : Set (Torus m)}
    (hS : MeasurableSet S) :
    volume (cubeLift S) = torusMeasure m S := by
  have h := UnitAddTorus.lintegral_preimage
    (d := Fin m) (S.indicator fun _ ↦ (1 : ℝ≥0∞)) (fun _ ↦ 0)
  rw [lintegral_indicator hS, MeasureTheory.setLIntegral_one] at h
  change torusMeasure m S = _ at h
  simp only [zero_add] at h
  change torusMeasure m S =
    ∫⁻ (x : Fin m → ℝ) in unitCubeIoc m,
      S.indicator (fun _ ↦ (1 : ℝ≥0∞)) (realToTorus x) at h
  have hpre : MeasurableSet (realToTorus ⁻¹' S) :=
    hS.preimage measurable_realToTorus
  have hcube := measurableSet_unitCubeIoc m
  have hfun :
      (unitCubeIoc m).indicator
          (fun x ↦ S.indicator (fun _ ↦ (1 : ℝ≥0∞)) (realToTorus x)) =
        (cubeLift S).indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ unitCubeIoc m <;>
      by_cases hsx : realToTorus x ∈ S <;>
      simp [Set.indicator, hx, hsx, cubeLift]
  calc
    volume (cubeLift S) =
        ∫⁻ x, (cubeLift S).indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
      exact (lintegral_indicator_one (measurableSet_cubeLift hS)).symm
    _ = ∫⁻ x, (unitCubeIoc m).indicator
          (fun x ↦ S.indicator (fun _ ↦ (1 : ℝ≥0∞)) (realToTorus x)) x := by
      rw [hfun]
    _ = ∫⁻ (x : Fin m → ℝ) in unitCubeIoc m,
          S.indicator (fun _ ↦ (1 : ℝ≥0∞)) (realToTorus x) := by
      exact lintegral_indicator hcube _
    _ = torusMeasure m S := h.symm

/-- The real fundamental-domain representatives of Bilu's distorting
set. -/
def cubeDistortingSet {m : ℕ} (delta : ℝ)
    (K : Finset (Fin m → ℤ)) : Set (Fin m → ℝ) :=
  cubeLift (distortingSet delta K)

theorem measurableSet_cubeDistortingSet {m : ℕ} (delta : ℝ)
    (K : Finset (Fin m → ℤ)) : MeasurableSet (cubeDistortingSet delta K) := by
  exact measurableSet_cubeLift (measurableSet_distortingSet delta K)

theorem volume_cubeDistortingSet {m : ℕ} (delta : ℝ)
    (K : Finset (Fin m → ℤ)) :
    volume (cubeDistortingSet delta K) =
      torusMeasure m (distortingSet delta K) := by
  exact volume_cubeLift (measurableSet_distortingSet delta K)

/-- **Bilu, Propositions 8.2--8.3, measure synthesis.**

The explicit exceptional-set bound in Lemma 6.8 is compared with the
lower bound from Proposition 8.1.  The conclusion is an actual sequence
of real representatives which is simultaneously distorting at every
stage and badly approximable up to rank `r`.
-/
theorem exists_distorting_badlyApproximable {m r : ℕ}
    (K : Finset (Fin m → ℤ)) (B : Set (Fin m → ℝ))
    (sigma delta X C : ℝ)
    (hK : K.Nonempty) (hsigma : 0 < sigma)
    (hdeltapos : 0 < delta) (hdeltalt : delta < 1 / Real.sqrt sigma)
    (hsum : ((sumset K).card : ℝ) ≤ sigma * K.card)
    (hB : MeasurableSet B) (hX : 1 ≤ X) (hC : 0 < C)
    (hbudget :
      ENNReal.ofReal ((6 : ℝ) ^ m * 3 ^ r * X ^ (m + r) * C ^ m) * volume B <
        ENNReal.ofReal
          ((1 - delta * Real.sqrt sigma) / (sigma * K.card))) :
    ∃ a : ℕ → Fin m → ℝ,
      (∀ i < r, a i ∈ cubeDistortingSet delta K) ∧
        IsBadlyApproximableUpTo B X C r a := by
  have hreal := bilu_proposition_8_1 K sigma delta hK hsigma hdeltapos hdeltalt hsum
  have htorus_ne_top : torusMeasure m (distortingSet delta K) ≠ ∞ :=
    measure_ne_top _ _
  have hlower :
      ENNReal.ofReal ((1 - delta * Real.sqrt sigma) / (sigma * K.card)) ≤
        volume (cubeDistortingSet delta K) := by
    rw [volume_cubeDistortingSet]
    rw [← ENNReal.ofReal_toReal htorus_ne_top]
    exact ENNReal.ofReal_le_ofReal hreal
  apply lemma6_8 B X C (fun _ ↦ cubeDistortingSet delta K) hB hX hC
  · intro k hk
    exact measurableSet_cubeDistortingSet delta K
  · intro k hk
    exact hbudget.trans_le hlower

/-- Proposition 8.3 in the form in which the preceding polar-body
estimate is used: a real upper bound `P` for the polar volume, together
with the source's explicit numerical inequality, implies the hypotheses
of the measure synthesis theorem.  In particular, there is no remaining
measure-comparison hypothesis. -/
theorem exists_distorting_badlyApproximable_of_volume_le {m r : ℕ}
    (K : Finset (Fin m → ℤ)) (B : Set (Fin m → ℝ))
    (sigma delta X C P : ℝ)
    (hK : K.Nonempty) (hsigma : 0 < sigma)
    (hdeltapos : 0 < delta) (hdeltalt : delta < 1 / Real.sqrt sigma)
    (hsum : ((sumset K).card : ℝ) ≤ sigma * K.card)
    (hB : MeasurableSet B) (hX : 1 ≤ X) (hC : 0 < C)
    (hP : 0 ≤ P) (hvolume : volume B ≤ ENNReal.ofReal P)
    (hnumeric :
      ((6 : ℝ) ^ m * 3 ^ r * X ^ (m + r) * C ^ m) * P <
        (1 - delta * Real.sqrt sigma) / (sigma * K.card)) :
    ∃ a : ℕ → Fin m → ℝ,
      (∀ i < r, a i ∈ cubeDistortingSet delta K) ∧
        IsBadlyApproximableUpTo B X C r a := by
  apply exists_distorting_badlyApproximable K B sigma delta X C hK hsigma
    hdeltapos hdeltalt hsum hB hX hC
  calc
    ENNReal.ofReal ((6 : ℝ) ^ m * 3 ^ r * X ^ (m + r) * C ^ m) * volume B ≤
        ENNReal.ofReal ((6 : ℝ) ^ m * 3 ^ r * X ^ (m + r) * C ^ m) *
          ENNReal.ofReal P := by
      gcongr
    _ = ENNReal.ofReal
          (((6 : ℝ) ^ m * 3 ^ r * X ^ (m + r) * C ^ m) * P) := by
      exact (ENNReal.ofReal_mul (by positivity)).symm
    _ < ENNReal.ofReal
          ((1 - delta * Real.sqrt sigma) / (sigma * K.card)) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
        (mul_nonneg (by positivity) hP)).2 hnumeric

/-- The common exponent used in Bilu's specialization of Proposition
8.3. -/
noncomputable def proposition83Exponent (m r : ℕ) : ℝ :=
  1 / (2 * ((2 * m + r : ℕ) : ℝ))

/-- The explicit lower threshold on the expansion parameter which makes
the exceptional-volume estimate strict.  This is
`(2 · σ · 6^m · 3^r · 4^m)^2`, equivalently the constant obtained
by inserting (8.1) into Lemma 6.8. -/
noncomputable def proposition83Threshold (m r : ℕ) (sigma : ℝ) : ℝ :=
  (2 * sigma * (6 : ℝ) ^ m * 3 ^ r * 4 ^ m) ^ 2

/-- **Bilu, Proposition 8.3 (explicit specialization).**

Assume the polar body has the source's volume bound
`Vol(B⁺) ≤ 4^m / (ε |K|)`.  If `ε` is above the explicit
dimension/doubling threshold, then the choices

* `δ = 1 / (2√σ)`, and
* `X = C = ε ^ (1 / (2(2m+r)))`

produce a distorting, badly-approximable system.  The positivity
assumptions `1 ≤ σ` and `0 < 2m+r` are exactly the nondegenerate
parameter range in which this specialization is used.
-/
theorem bilu_proposition_8_3 {m r : ℕ}
    (K : Finset (Fin m → ℤ)) (B : Set (Fin m → ℝ))
    (sigma epsilon : ℝ)
    (hK : K.Nonempty) (hsigma : 1 ≤ sigma)
    (hdim : 0 < 2 * m + r)
    (hsum : ((sumset K).card : ℝ) ≤ sigma * K.card)
    (hB : MeasurableSet B)
    (hpolar :
      volume B ≤ ENNReal.ofReal ((4 : ℝ) ^ m / (epsilon * K.card)))
    (hepsilon : proposition83Threshold m r sigma < epsilon) :
    ∃ a : ℕ → Fin m → ℝ,
      (∀ i < r,
        a i ∈ cubeDistortingSet (1 / (2 * Real.sqrt sigma)) K) ∧
      IsBadlyApproximableUpTo B
        (epsilon ^ proposition83Exponent m r)
        (epsilon ^ proposition83Exponent m r) r a := by
  let q : ℝ := proposition83Exponent m r
  let T : ℝ := epsilon ^ q
  let delta : ℝ := 1 / (2 * Real.sqrt sigma)
  let P : ℝ := (4 : ℝ) ^ m / (epsilon * K.card)
  let A : ℝ := (6 : ℝ) ^ m * 3 ^ r * 4 ^ m
  have hsigma_pos : 0 < sigma := zero_lt_one.trans_le hsigma
  have hA_pos : 0 < A := by positivity
  have hthreshold_pos : 0 < proposition83Threshold m r sigma := by
    simp only [proposition83Threshold]
    positivity
  have hepsilon_pos : 0 < epsilon := hthreshold_pos.trans hepsilon
  have hepsilon_one : 1 ≤ epsilon := by
    have htwo_sigma_A : 2 ≤ 2 * sigma * A := by
      have hA_one : 1 ≤ A := by
        dsimp only [A]
        have h6 : (1 : ℝ) ≤ 6 ^ m := one_le_pow₀ (by norm_num)
        have h3 : (1 : ℝ) ≤ 3 ^ r := one_le_pow₀ (by norm_num)
        have h4 : (1 : ℝ) ≤ 4 ^ m := one_le_pow₀ (by norm_num)
        have h63 : (1 : ℝ) ≤ 6 ^ m * 3 ^ r := by
          nlinarith [mul_nonneg (sub_nonneg.mpr h6) (sub_nonneg.mpr h3)]
        nlinarith [mul_nonneg (sub_nonneg.mpr h63) (sub_nonneg.mpr h4)]
      nlinarith
    have hfour : 4 ≤ proposition83Threshold m r sigma := by
      simp only [proposition83Threshold]
      dsimp only [A] at htwo_sigma_A
      nlinarith
    linarith
  have hT_pos : 0 < T := Real.rpow_pos_of_pos hepsilon_pos q
  have hT_one : 1 ≤ T := by
    dsimp only [T, q, proposition83Exponent]
    apply Real.one_le_rpow hepsilon_one
    positivity
  have hsqrt_sigma_pos : 0 < Real.sqrt sigma := Real.sqrt_pos.2 hsigma_pos
  have hdelta_pos : 0 < delta := by
    dsimp only [delta]
    positivity
  have hdelta_lt : delta < 1 / Real.sqrt sigma := by
    dsimp only [delta]
    rw [div_lt_div_iff₀ (by positivity) hsqrt_sigma_pos]
    nlinarith
  have hcard_pos : (0 : ℝ) < K.card := by
    exact_mod_cast hK.card_pos
  have hP_nonneg : 0 ≤ P := by
    dsimp only [P]
    positivity
  have hNreal : (0 : ℝ) < ((2 * m + r : ℕ) : ℝ) := by
    exact_mod_cast hdim
  have hqN : q * ((2 * m + r : ℕ) : ℝ) = (1 : ℝ) / 2 := by
    dsimp only [q, proposition83Exponent]
    field_simp
  have hTpow : T ^ (2 * m + r) = Real.sqrt epsilon := by
    dsimp only [T]
    rw [← Real.rpow_mul_natCast hepsilon_pos.le, hqN, ← Real.sqrt_eq_rpow]
  have hpowers : T ^ (m + r) * T ^ m = Real.sqrt epsilon := by
    rw [← pow_add, show m + r + m = 2 * m + r by omega, hTpow]
  have hsqrt_epsilon_pos : 0 < Real.sqrt epsilon := Real.sqrt_pos.2 hepsilon_pos
  have hsqrt_epsilon_sq : (Real.sqrt epsilon) ^ 2 = epsilon := by
    exact Real.sq_sqrt hepsilon_pos.le
  have hlarge : 2 * sigma * A < Real.sqrt epsilon := by
    have hsq : (2 * sigma * A) ^ 2 < epsilon := by
      convert hepsilon using 1 <;>
        simp only [proposition83Threshold, A] <;> ring
    nlinarith
  have hsimple : A * Real.sqrt epsilon / epsilon < 1 / (2 * sigma) := by
    rw [div_lt_div_iff₀ hepsilon_pos (by positivity)]
    nlinarith
  have hnumeric :
      ((6 : ℝ) ^ m * 3 ^ r * T ^ (m + r) * T ^ m) * P <
        (1 - delta * Real.sqrt sigma) / (sigma * K.card) := by
    have hdivcard :
        (A * Real.sqrt epsilon / epsilon) / K.card <
          (1 / (2 * sigma)) / K.card :=
      div_lt_div_of_pos_right hsimple hcard_pos
    have hdelta_simp :
        (1 - delta * Real.sqrt sigma) / (sigma * K.card) =
          (1 / (2 * sigma)) / K.card := by
      dsimp only [delta]
      field_simp
      <;> ring
    rw [hdelta_simp]
    rw [show
      ((6 : ℝ) ^ m * 3 ^ r * T ^ (m + r) * T ^ m) * P =
        (A * (T ^ (m + r) * T ^ m) / epsilon) / K.card by
          dsimp only [P, A]
          ring]
    rw [hpowers]
    exact hdivcard
  have hresult := exists_distorting_badlyApproximable_of_volume_le
    K B sigma delta T T P hK hsigma_pos hdelta_pos hdelta_lt hsum hB
    hT_one hT_pos hP_nonneg (by simpa only [P] using hpolar) hnumeric
  simpa only [delta, T, q] using hresult

end Erdos186.CFP.Bilu.Section8Synthesis

#print axioms Erdos186.CFP.Bilu.Section8Synthesis.volume_cubeLift
#print axioms Erdos186.CFP.Bilu.Section8Synthesis.exists_distorting_badlyApproximable
#print axioms Erdos186.CFP.Bilu.Section8Synthesis.exists_distorting_badlyApproximable_of_volume_le
#print axioms Erdos186.CFP.Bilu.Section8Synthesis.bilu_proposition_8_3
