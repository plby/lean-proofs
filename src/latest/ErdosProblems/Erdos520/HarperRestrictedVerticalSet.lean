import ErdosProblems.Erdos520.HarperRestrictedLocalFirstMoment
import ErdosProblems.Erdos520.HarperFixedFractionalMoment

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem520

/-!
# Restricted first moments on arbitrary finite vertical sets

The unit-interval change-of-measure lemma is enough for the outer shell
assembly.  Inside the central Rademacher shell, however, the correct proof
splits the vertical variable into dyadic bands.  This file records the same
Fubini/change-of-measure argument on an arbitrary measurable set of finite
Lebesgue measure, retaining its measure as the crucial geometric factor.
-/

/-- Normalized Euler-product mass on an arbitrary vertical set. -/
noncomputable def normalizedHarperEulerSetMass
    (y : Nat) (I : Set Real) (omega : Omega) : Real :=
  ∫ t in I, normalizedHarperEulerDensity y omega t

/-- The corresponding energy with the normalization used by the Parseval
assembly. -/
noncomputable def harperEulerSetEnergy
    (y : Nat) (I : Set Real) (omega : Omega) : Real :=
  (∫ t in I, harperEulerDensity y omega t) / Real.log (y : Real)

theorem harperEulerSetEnergy_eq_normalizer_mul_normalizedSetMass
    (y : Nat) (I : Set Real) (omega : Omega) :
    harperEulerSetEnergy y I omega =
      (primeEnergyNormalizer y / Real.log (y : Real)) *
        normalizedHarperEulerSetMass y I omega := by
  have hZ : primeEnergyNormalizer y ≠ 0 :=
    (primeEnergyNormalizer_pos y).ne'
  have hdensity :
      (fun t => harperEulerDensity y omega t) =
        fun t => primeEnergyNormalizer y *
          normalizedHarperEulerDensity y omega t := by
    funext t
    unfold normalizedHarperEulerDensity
    field_simp
  unfold harperEulerSetEnergy normalizedHarperEulerSetMass
  rw [hdensity, integral_const_mul]
  ring

theorem harperEulerSetEnergy_nonneg
    {y : Nat} (hy : 1 < y) {I : Set Real} (hI : MeasurableSet I)
    (omega : Omega) :
    0 ≤ harperEulerSetEnergy y I omega := by
  unfold harperEulerSetEnergy
  apply div_nonneg
  · exact setIntegral_nonneg hI fun t _ht =>
      harperEulerDensity_nonneg y omega t
  · exact (Real.log_pos (by exact_mod_cast hy)).le

theorem integrable_harperEulerDensity_prod_restrict
    (y : Nat) {I : Set Real} (hI : MeasurableSet I)
    (hIfinite : volume I ≠ ∞) :
    Integrable
      (fun w : Real × Omega => harperEulerDensity y w.2 w.1)
      ((volume.restrict I).prod μ) := by
  let : IsFiniteMeasure (volume.restrict I) :=
    isFiniteMeasure_restrict.2 hIfinite
  apply Integrable.of_bound
    (measurable_harperEulerDensity_joint y).aestronglyMeasurable
    (harperEulerDensityUniformBound y)
  exact ae_of_all _ fun w => by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (harperEulerDensity_nonneg y w.2 w.1)]
    exact harperEulerDensity_le_uniformBound y w.2 w.1

theorem integrable_harperEulerSetEnergy
    (y : Nat) {I : Set Real} (hI : MeasurableSet I)
    (hIfinite : volume I ≠ ∞) :
    Integrable (harperEulerSetEnergy y I) μ := by
  let nu : Measure Real := volume.restrict I
  let F : Real × Omega -> Real := fun w =>
    harperEulerDensity y w.2 w.1
  have hF : Integrable F (nu.prod μ) := by
    simpa only [nu, F] using!
      integrable_harperEulerDensity_prod_restrict y hI hIfinite
  have hinner : Integrable (fun omega => ∫ t, F (t, omega) ∂nu) μ :=
    hF.integral_prod_right
  simpa only [harperEulerSetEnergy, nu, F] using!
    hinner.div_const (Real.log (y : Real))

/-- Restricted change of measure on a finite-measure vertical set.  Unlike
the unit-interval form, the conclusion keeps `volume I`; this is what makes
the frequency-dependent Rademacher start shift summable over dyadic bands. -/
theorem integral_normalizedHarperEulerSetMass_restrict_le
    (y : Nat) {I : Set Real} (hI : MeasurableSet I)
    (hIfinite : volume I ≠ ∞)
    {G : Set Omega} (hG : MeasurableSet G)
    (A : Real -> Set (HarperPrimeCube y)) (H : Real)
    (hcontain : ∀ t ∈ I,
      G ⊆ harperPrimeRestriction y ⁻¹' A t)
    (hprob : ∀ t ∈ I,
      (harperTiltedCubeLaw y t).real (A t) ≤ H) :
    (∫ omega in G,
      normalizedHarperEulerSetMass y I omega ∂μ) ≤
      volume.real I * H := by
  let nu : Measure Real := volume.restrict I
  let F : Real × Omega -> Real := fun w =>
    normalizedHarperEulerDensity y w.2 w.1
  let S : Set (Real × Omega) := Set.univ ×ˢ G
  let FG : Real × Omega -> Real := S.indicator F
  have hF : Integrable F (nu.prod μ) := by
    have hEuler := integrable_harperEulerDensity_prod_restrict y hI hIfinite
    simpa only [F, nu, normalizedHarperEulerDensity] using!
      hEuler.div_const (primeEnergyNormalizer y)
  have hS : MeasurableSet S :=
    MeasurableSet.prod (MeasurableSet.univ :
      MeasurableSet (Set.univ : Set Real)) hG
  have hFG : Integrable FG (nu.prod μ) := hF.indicator hS
  have hleft :
      (∫ omega, ∫ t, FG (t, omega) ∂nu ∂μ) =
        ∫ omega in G,
          normalizedHarperEulerSetMass y I omega ∂μ := by
    rw [← integral_indicator hG]
    apply integral_congr_ae
    exact ae_of_all μ fun omega => by
      by_cases homega : omega ∈ G
      · simp [FG, S, F, homega, normalizedHarperEulerSetMass, nu]
      · simp [FG, S, F, homega, normalizedHarperEulerSetMass, nu]
  have hright (t : Real) :
      (∫ omega, FG (t, omega) ∂μ) =
        ∫ omega in G, normalizedHarperEulerDensity y omega t ∂μ := by
    rw [← integral_indicator hG]
    apply integral_congr_ae
    exact ae_of_all μ fun omega => by
      by_cases homega : omega ∈ G
      · simp [FG, S, F, Set.indicator_of_mem, homega]
      · simp [FG, S, F, Set.indicator_of_notMem, homega]
  have hswap :
      (∫ omega, ∫ t, FG (t, omega) ∂nu ∂μ) =
        ∫ t, ∫ omega, FG (t, omega) ∂μ ∂nu :=
    (integral_prod_symm FG hFG).symm.trans (integral_prod FG hFG)
  have hfubini :
      (∫ omega in G,
          normalizedHarperEulerSetMass y I omega ∂μ) =
        ∫ t, (∫ omega in G,
          normalizedHarperEulerDensity y omega t ∂μ) ∂nu := by
    calc
      (∫ omega in G,
          normalizedHarperEulerSetMass y I omega ∂μ) =
          ∫ omega, ∫ t, FG (t, omega) ∂nu ∂μ := hleft.symm
      _ = ∫ t, ∫ omega, FG (t, omega) ∂μ ∂nu := hswap
      _ = ∫ t, (∫ omega in G,
          normalizedHarperEulerDensity y omega t ∂μ) ∂nu := by
        apply integral_congr_ae
        exact ae_of_all nu hright
  have hinner (t : Real) (ht : t ∈ I) :
      (∫ omega in G, normalizedHarperEulerDensity y omega t ∂μ) ≤ H := by
    have hint : IntegrableOn
        (fun omega => normalizedHarperEulerDensity y omega t)
        (harperPrimeRestriction y ⁻¹' A t) μ :=
      (integrable_normalizedHarperEulerDensity y t).integrableOn
    have hnonneg : 0 ≤ᵐ[μ.restrict
        (harperPrimeRestriction y ⁻¹' A t)]
        fun omega => normalizedHarperEulerDensity y omega t :=
      Eventually.of_forall fun omega =>
        normalizedHarperEulerDensity_nonneg y omega t
    have hsubset : G ≤ᶠ[ae μ]
        (harperPrimeRestriction y ⁻¹' A t) :=
      Eventually.of_forall fun omega homega => hcontain t ht homega
    calc
      (∫ omega in G,
          normalizedHarperEulerDensity y omega t ∂μ) ≤
          ∫ omega in harperPrimeRestriction y ⁻¹' A t,
            normalizedHarperEulerDensity y omega t ∂μ :=
        setIntegral_mono_set hint hnonneg hsubset
      _ = (harperTiltedCubeLaw y t).real (A t) :=
        (harperTiltedCubeLaw_real_apply_eq_omega y t (A t)).symm
      _ ≤ H := hprob t ht
  have houterInt : Integrable
      (fun t => ∫ omega in G,
        normalizedHarperEulerDensity y omega t ∂μ) nu := by
    have heq :
        (fun t => ∫ omega, FG (t, omega) ∂μ) =
          fun t => ∫ omega in G,
            normalizedHarperEulerDensity y omega t ∂μ := by
      funext t
      exact hright t
    rw [← heq]
    exact hFG.integral_prod_left
  have hbound : ∀ᵐ t ∂nu,
      (∫ omega in G,
        normalizedHarperEulerDensity y omega t ∂μ) ≤ H :=
    (ae_restrict_mem hI).mono fun t ht => hinner t ht
  have hconst : Integrable (fun _t : Real => H) nu := by
    simpa only [nu] using!
      (integrableOn_const (μ := volume) (s := I) (C := H) hIfinite)
  rw [hfubini]
  calc
    (∫ t, (∫ omega in G,
        normalizedHarperEulerDensity y omega t ∂μ) ∂nu) ≤
        ∫ _t, H ∂nu :=
      integral_mono_ae houterInt hconst hbound
    _ = volume.real I * H := by
      rw [integral_const]
      simp only [nu, measureReal_restrict_apply MeasurableSet.univ,
        Set.univ_inter, smul_eq_mul]

/-- The arbitrary-set form for the actual Parseval-normalized energy. -/
theorem integral_harperEulerSetEnergy_restrict_le_explicitMertens
    {y : Nat} (hy : 2 ≤ y) {I : Set Real} (hI : MeasurableSet I)
    (hIfinite : volume I ≠ ∞)
    {G : Set Omega} (hG : MeasurableSet G)
    (A : Real -> Set (HarperPrimeCube y)) (H : Real) (hH : 0 ≤ H)
    (hcontain : ∀ t ∈ I,
      G ⊆ harperPrimeRestriction y ⁻¹' A t)
    (hprob : ∀ t ∈ I,
      (harperTiltedCubeLaw y t).real (A t) ≤ H) :
    (∫ omega in G, harperEulerSetEnergy y I omega ∂μ) ≤
      harperExplicitMertensConstant * (volume.real I * H) := by
  have hlog : 0 < Real.log (y : Real) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < y by omega)
  have hcoeffNonneg :
      0 ≤ primeEnergyNormalizer y / Real.log (y : Real) :=
    div_nonneg (primeEnergyNormalizer_pos y).le hlog.le
  have hcoeff : primeEnergyNormalizer y / Real.log (y : Real) ≤
      harperExplicitMertensConstant := by
    apply (div_le_iff₀ hlog).2
    simpa only [harperExplicitMertensConstant] using!
      primeEnergyNormalizer_le_mertensConstant_mul_log hy
  have hmass := integral_normalizedHarperEulerSetMass_restrict_le
    y hI hIfinite hG A H hcontain hprob
  have hvolNonneg : 0 ≤ volume.real I := measureReal_nonneg
  have henergy :
      (∫ omega in G, harperEulerSetEnergy y I omega ∂μ) =
        (primeEnergyNormalizer y / Real.log (y : Real)) *
          ∫ omega in G,
            normalizedHarperEulerSetMass y I omega ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all (μ.restrict G) fun omega =>
      harperEulerSetEnergy_eq_normalizer_mul_normalizedSetMass
        y I omega
  rw [henergy]
  calc
    (primeEnergyNormalizer y / Real.log (y : Real)) *
        (∫ omega in G,
          normalizedHarperEulerSetMass y I omega ∂μ) ≤
        (primeEnergyNormalizer y / Real.log (y : Real)) *
          (volume.real I * H) :=
      mul_le_mul_of_nonneg_left hmass hcoeffNonneg
    _ ≤ harperExplicitMertensConstant * (volume.real I * H) :=
      mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hvolNonneg hH)

/-- The full first moment on a finite vertical set is bounded by its length,
uniformly in the prime cutoff. -/
theorem integral_harperEulerSetEnergy_le_explicitMertens_mul_volume
    {y : Nat} (hy : 2 ≤ y) {I : Set Real} (hI : MeasurableSet I)
    (hIfinite : volume I ≠ ∞) :
    (∫ omega, harperEulerSetEnergy y I omega ∂μ) ≤
      harperExplicitMertensConstant * volume.real I := by
  have h := integral_harperEulerSetEnergy_restrict_le_explicitMertens
    hy hI hIfinite (G := Set.univ) MeasurableSet.univ
    (fun _t => Set.univ) 1 (by norm_num)
    (fun _t _ht _omega _homega => Set.mem_univ _)
    (fun t _ht =>
      (probReal_univ :
        (harperTiltedCubeLaw y t).real Set.univ = 1).le)
  simpa only [Measure.restrict_univ, mul_one] using! h

/-- Jensen on a short vertical set.  This is the complete treatment of the
very-small-frequency core in the Rademacher argument. -/
theorem integral_harperEulerSetEnergy_twoThird_le
    {y : Nat} (hy : 2 ≤ y) {I : Set Real} (hI : MeasurableSet I)
    (hIfinite : volume I ≠ ∞) :
    (∫ omega,
      harperEulerSetEnergy y I omega ^ harperTwoThird ∂μ) ≤
      (harperExplicitMertensConstant * volume.real I) ^
        harperTwoThird := by
  have hy1 : 1 < y := by omega
  have hZ := integrable_harperEulerSetEnergy y hI hIfinite
  have hnonneg : ∀ omega, 0 ≤ harperEulerSetEnergy y I omega :=
    harperEulerSetEnergy_nonneg hy1 hI
  have hJ := integral_rpow_twoThird_le_rpow_integral hZ hnonneg
  have hmean :=
    integral_harperEulerSetEnergy_le_explicitMertens_mul_volume
      hy hI hIfinite
  have hmean0 : 0 ≤ ∫ omega, harperEulerSetEnergy y I omega ∂μ :=
    integral_nonneg hnonneg
  exact hJ.trans (Real.rpow_le_rpow hmean0 hmean
    (by norm_num [harperTwoThird]))

end Problem520
end Erdos
