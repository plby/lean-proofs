import ErdosProblems.Erdos520.ExactEnergyMartingale
import ErdosProblems.Erdos520.LocalizedDoob

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos
namespace Problem520

/-!
# Small-energy estimates from the exact energy martingale

The Euler-product energy normalized by `primeEnergyNormalizer` is an exact
martingale.  This file samples that martingale along a monotone sequence of
prime cutoffs and records the localized maximal argument used by Caich.

The only non-elementary input left in the resulting estimate is displayed as
the fractional-moment inequality for the initial energy.
-/

/-! ## Sampling along a monotone cutoff schedule -/

/-- The prime-energy filtration sampled along a monotone cutoff schedule. -/
noncomputable def scheduledPrimeEnergyFiltration
    (y : ℕ → ℕ) (hy : Monotone y) :
    Filtration ℕ (inferInstance : MeasurableSpace Omega) where
  seq j := primeEnergyFiltration (y j)
  mono' _i _j hij := primeEnergyFiltration.mono (hy hij)
  le' j := primeEnergyFiltration.le (y j)

@[simp] theorem scheduledPrimeEnergyFiltration_apply
    (y : ℕ → ℕ) (hy : Monotone y) (j : ℕ) :
    scheduledPrimeEnergyFiltration y hy j = primeEnergyFiltration (y j) := rfl

/-- The exactly normalized energy sampled at the scheduled cutoff. -/
noncomputable def scheduledExactNormalizedEnergy
    (y : ℕ → ℕ) (j : ℕ) (omega : Omega) : ℝ :=
  exactNormalizedEnergy omega (y j)

theorem scheduledExactNormalizedEnergy_nonneg
    (y : ℕ → ℕ) (j : ℕ) (omega : Omega) :
    0 ≤ scheduledExactNormalizedEnergy y j omega :=
  exactNormalizedEnergy_nonneg omega (y j)

theorem stronglyAdapted_scheduledExactNormalizedEnergy
    (y : ℕ → ℕ) (hy : Monotone y) :
    StronglyAdapted (scheduledPrimeEnergyFiltration y hy)
      (scheduledExactNormalizedEnergy y) := by
  intro j
  exact stronglyMeasurable_exactNormalizedEnergy (y j)

/-- Sampling at arbitrary deterministic nondecreasing prime cutoffs preserves
the exact martingale property. -/
theorem martingale_scheduledExactNormalizedEnergy
    (y : ℕ → ℕ) (hy : Monotone y) :
    Martingale (scheduledExactNormalizedEnergy y)
      (scheduledPrimeEnergyFiltration y hy) μ := by
  refine ⟨stronglyAdapted_scheduledExactNormalizedEnergy y hy, ?_⟩
  intro i j hij
  exact condExp_exactNormalizedEnergy (hy hij)

/-! ## Fractional-moment Markov and localized Doob -/

section FractionalMoment

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {ν : Measure Ω}

/-- Markov's inequality written for a positive fractional power of a
nonnegative random variable. -/
theorem measureReal_gt_le_integral_rpow
    [IsFiniteMeasure ν] {W : Ω → ℝ} (hWnonneg : ∀ omega, 0 ≤ W omega)
    {q a L : ℝ} (hq : 0 < q) (ha : 0 < a)
    (hint : Integrable (fun omega => W omega ^ q) ν)
    (hmoment : (∫ omega, W omega ^ q ∂ν) ≤ L) :
    ν.real {omega | a < W omega} ≤ L / a ^ q := by
  let V : Ω → ℝ := fun omega => W omega ^ q
  have hVnonneg : 0 ≤ᵐ[ν] V :=
    ae_of_all ν fun omega => Real.rpow_nonneg (hWnonneg omega) q
  have hmarkov :=
    mul_meas_ge_le_integral_of_nonneg (μ := ν) hVnonneg hint (a ^ q)
  have hsubset : {omega | a < W omega} ⊆ {omega | a ^ q ≤ V omega} := by
    intro omega homega
    exact Real.rpow_le_rpow ha.le homega.le hq.le
  have hmul :
      a ^ q * ν.real {omega | a < W omega} ≤ L := by
    calc
      a ^ q * ν.real {omega | a < W omega} ≤
          a ^ q * ν.real {omega | a ^ q ≤ V omega} :=
        mul_le_mul_of_nonneg_left (measureReal_mono hsubset)
          (Real.rpow_nonneg ha.le q)
      _ ≤ ∫ omega, V omega ∂ν := hmarkov
      _ ≤ L := hmoment
  exact (le_div_iff₀ (Real.rpow_pos_of_pos ha q)).2 (by
    simpa [mul_comm] using! hmul)

/-- On a finite measure space, an integrable nonnegative random variable has
every positive fractional moment of order at most one. -/
theorem integrable_rpow_of_integrable_nonneg
    [IsFiniteMeasure ν] {W : Ω → ℝ} (hW : Integrable W ν)
    (hWnonneg : ∀ omega, 0 ≤ W omega) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Integrable (fun omega => W omega ^ q) ν := by
  have hnormone : Integrable (fun omega => ‖W omega‖ ^ (1 : ℝ)) ν := by
    simpa using! hW.norm
  have hnormq := integrable_norm_rpow_of_le hW.aestronglyMeasurable
    hq0 zero_le_one hq1 hnormone
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hWnonneg _)] using! hnormq

variable {𝒜 : Filtration ℕ m0} {X : ℕ → Ω → ℝ}

/-- The localized Doob split.  The maximal event is split according to
whether the initial energy is at most `a`; the complement is controlled by a
positive fractional moment. -/
theorem Martingale.measureReal_maximal_le_fractional_split
    [IsProbabilityMeasure ν]
    (hX : Martingale X 𝒜 ν) (hXnonneg : ∀ n omega, 0 ≤ X n omega)
    {q a u L : ℝ} (hq : 0 < q) (ha : 0 < a) (hu : 0 < u)
    (hpowInt : Integrable (fun omega => X 0 omega ^ q) ν)
    (hmoment : (∫ omega, X 0 omega ^ q ∂ν) ≤ L) (n : ℕ) :
    ν.real {omega | u ≤ finiteRunningMax X n omega} ≤
      a / u + L / a ^ q := by
  let A : Set Ω := {omega | X 0 omega ≤ a}
  let E : Set Ω := {omega | u ≤ finiteRunningMax X n omega}
  let B : Set Ω := {omega | a < X 0 omega}
  have hA : MeasurableSet[𝒜 0] A := by
    exact (hX.stronglyMeasurable 0).measurable measurableSet_Iic
  have hlocal : ν.real (A ∩ E) ≤ a / u := by
    exact Martingale.measureReal_initial_inter_maximal_le
      hX hXnonneg hA ha.le hu
      (fun omega homega => homega) n
  have htail : ν.real B ≤ L / a ^ q := by
    exact measureReal_gt_le_integral_rpow (hXnonneg 0) hq ha hpowInt hmoment
  have hsubset : E ⊆ (A ∩ E) ∪ B := by
    intro omega homega
    by_cases hle : X 0 omega ≤ a
    · exact Or.inl ⟨hle, homega⟩
    · exact Or.inr (lt_of_not_ge hle)
  calc
    ν.real E ≤ ν.real ((A ∩ E) ∪ B) := measureReal_mono hsubset
    _ ≤ ν.real (A ∩ E) + ν.real B := measureReal_union_le _ _
    _ ≤ a / u + L / a ^ q := add_le_add hlocal htail

end FractionalMoment

/-! ## The exact scheduled energy and Caich's exponents -/

/-- The localized maximal estimate for the scheduled exact energy at the
specific fractional exponent `2/3`.  The displayed moment hypothesis is the
sole deep input in this theorem. -/
theorem measureReal_scheduledExactNormalizedEnergy_max_le_twoThird
    (y : ℕ → ℕ) (hy : Monotone y) {a u L : ℝ}
    (ha : 0 < a) (hu : 0 < u)
    (hmoment :
      (∫ omega,
        scheduledExactNormalizedEnergy y 0 omega ^ ((2 : ℝ) / 3) ∂μ) ≤ L)
    (n : ℕ) :
    μ.real {omega |
        u ≤ finiteRunningMax (scheduledExactNormalizedEnergy y) n omega} ≤
      a / u + L / a ^ ((2 : ℝ) / 3) := by
  let X := scheduledExactNormalizedEnergy y
  let 𝒜 := scheduledPrimeEnergyFiltration y hy
  have hX : Martingale X 𝒜 μ :=
    martingale_scheduledExactNormalizedEnergy y hy
  have hXnonneg : ∀ j omega, 0 ≤ X j omega :=
    scheduledExactNormalizedEnergy_nonneg y
  have hpowInt : Integrable (fun omega => X 0 omega ^ ((2 : ℝ) / 3)) μ := by
    apply integrable_rpow_of_integrable_nonneg (hX.integrable 0) (hXnonneg 0)
    · norm_num
    · norm_num
  exact Martingale.measureReal_maximal_le_fractional_split
    hX hXnonneg (by norm_num) ha hu hpowInt hmoment n

/-- The initial-energy cutoff in Caich's localized Doob split. -/
noncomputable def caichInitialEnergyThreshold
    (ell K : ℕ) (T1 : ℝ) : ℝ :=
  T1 ^ ((1 : ℝ) / 4) / (ell : ℝ) ^ ((K : ℝ) / 2)

/-- The energy level whose crossing is ruled out by localized Doob. -/
noncomputable def caichMaximalEnergyThreshold
    (ell K : ℕ) (T1 : ℝ) : ℝ :=
  T1 ^ ((1 : ℝ) / 2) / (ell : ℝ) ^ ((K : ℝ) / 2)

/-- Harper's low fractional moment, in the exact scalar form needed here. -/
noncomputable def caichInitialEnergyMomentBudget
    (ell K : ℕ) (C : ℝ) : ℝ :=
  C / (ell : ℝ) ^ ((K : ℝ) / 3)

theorem caichInitialEnergyThreshold_pos
    {ell K : ℕ} {T1 : ℝ} (hell : 0 < ell) (hT1 : 0 < T1) :
    0 < caichInitialEnergyThreshold ell K T1 := by
  exact div_pos (Real.rpow_pos_of_pos hT1 _)
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hell) _)

theorem caichMaximalEnergyThreshold_pos
    {ell K : ℕ} {T1 : ℝ} (hell : 0 < ell) (hT1 : 0 < T1) :
    0 < caichMaximalEnergyThreshold ell K T1 := by
  exact div_pos (Real.rpow_pos_of_pos hT1 _)
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hell) _)

/-- The first scalar term in the localized split is exactly `T1⁻¹⁄⁴`. -/
theorem caich_initial_div_maximal
    {ell K : ℕ} {T1 : ℝ} (hell : 0 < ell) (hT1 : 0 < T1) :
    caichInitialEnergyThreshold ell K T1 /
        caichMaximalEnergyThreshold ell K T1 =
      T1 ^ (-(1 : ℝ) / 4) := by
  unfold caichInitialEnergyThreshold caichMaximalEnergyThreshold
  have hellR : 0 < (ell : ℝ) := Nat.cast_pos.mpr hell
  have hE : (ell : ℝ) ^ ((K : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos hellR _).ne'
  have hhalf : T1 ^ ((1 : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos hT1 _).ne'
  calc
    T1 ^ ((1 : ℝ) / 4) / (ell : ℝ) ^ ((K : ℝ) / 2) /
          (T1 ^ ((1 : ℝ) / 2) / (ell : ℝ) ^ ((K : ℝ) / 2)) =
        T1 ^ ((1 : ℝ) / 4) / T1 ^ ((1 : ℝ) / 2) := by
      field_simp
    _ = T1 ^ ((1 : ℝ) / 4 - (1 : ℝ) / 2) :=
      (Real.rpow_sub hT1 _ _).symm
    _ = T1 ^ (-(1 : ℝ) / 4) := by
      apply congrArg (fun z : ℝ => T1 ^ z)
      ring

/-- The fractional-moment term is exactly `C * T1⁻¹⁄⁶`; all
powers of `ell` cancel. -/
theorem caich_moment_div_initial_rpow
    {ell K : ℕ} {T1 C : ℝ} (hell : 0 < ell) (hT1 : 0 < T1) :
    caichInitialEnergyMomentBudget ell K C /
        caichInitialEnergyThreshold ell K T1 ^ ((2 : ℝ) / 3) =
      C * T1 ^ (-(1 : ℝ) / 6) := by
  have hellR : 0 < (ell : ℝ) := Nat.cast_pos.mpr hell
  have hdenpow :
      caichInitialEnergyThreshold ell K T1 ^ ((2 : ℝ) / 3) =
        T1 ^ ((1 : ℝ) / 6) /
          (ell : ℝ) ^ ((K : ℝ) / 3) := by
    unfold caichInitialEnergyThreshold
    rw [Real.div_rpow (Real.rpow_nonneg hT1.le _)
      (Real.rpow_nonneg hellR.le _)]
    rw [← Real.rpow_mul hT1.le, ← Real.rpow_mul hellR.le]
    apply congrArg₂ (fun x y : ℝ => x / y)
    · apply congrArg (fun z : ℝ => T1 ^ z)
      ring
    · apply congrArg (fun z : ℝ => (ell : ℝ) ^ z)
      ring
  unfold caichInitialEnergyMomentBudget
  rw [hdenpow]
  have hEllThird : (ell : ℝ) ^ ((K : ℝ) / 3) ≠ 0 :=
    (Real.rpow_pos_of_pos hellR _).ne'
  calc
    C / (ell : ℝ) ^ ((K : ℝ) / 3) /
          (T1 ^ ((1 : ℝ) / 6) / (ell : ℝ) ^ ((K : ℝ) / 3)) =
        C / T1 ^ ((1 : ℝ) / 6) := by
      field_simp
    _ = C * T1 ^ (-(1 : ℝ) / 6) := by
      rw [show (-(1 : ℝ) / 6) = -((1 : ℝ) / 6) by ring,
        Real.rpow_neg hT1.le]
      simp only [div_eq_mul_inv]

/-- Caich's small-energy maximal estimate with all elementary exponents
simplified.  The hypothesis is exactly the low `2/3` moment estimate at the
first cutoff; no small-energy event is postulated. -/
theorem measureReal_scheduledExactNormalizedEnergy_max_le_caich
    (y : ℕ → ℕ) (hy : Monotone y) (n ell K : ℕ) (T1 C : ℝ)
    (hell : 0 < ell) (hT1 : 0 < T1)
    (hmoment :
      (∫ omega,
        scheduledExactNormalizedEnergy y 0 omega ^ ((2 : ℝ) / 3) ∂μ) ≤
          caichInitialEnergyMomentBudget ell K C) :
    μ.real {omega |
        caichMaximalEnergyThreshold ell K T1 ≤
          finiteRunningMax (scheduledExactNormalizedEnergy y) n omega} ≤
      T1 ^ (-(1 : ℝ) / 4) + C * T1 ^ (-(1 : ℝ) / 6) := by
  have h := measureReal_scheduledExactNormalizedEnergy_max_le_twoThird
    y hy (a := caichInitialEnergyThreshold ell K T1)
    (u := caichMaximalEnergyThreshold ell K T1)
    (L := caichInitialEnergyMomentBudget ell K C)
    (caichInitialEnergyThreshold_pos (K := K) hell hT1)
    (caichMaximalEnergyThreshold_pos (K := K) hell hT1) hmoment n
  simpa only [caich_initial_div_maximal hell hT1,
    caich_moment_div_initial_rpow hell hT1] using! h

end Problem520
end Erdos
