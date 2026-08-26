import ErdosProblems.Erdos520.HarperParsevalTail
import ErdosProblems.Erdos520.HarperTiltedOmega

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem520

/-!
# Restricted first moments of local Harper energy

The squared Euler product, divided by its exact finite-prime normalizer, is
the Radon--Nikodym density of Harper's tilted prime-cube law.  Integrating
this normalized density over a unit interval gives a local mass whose fair
expectation on any restricted event is controlled by the corresponding
tilted probabilities.
-/

/-- The normalized squared-Euler-product mass on one of the signed unit
intervals used by the Parseval assembly. -/
noncomputable def normalizedHarperEulerLocalMass
    (y : ℕ) (positive : Bool) (n : ℕ) (omega : Omega) : ℝ :=
  ∫ t in harperEulerUnitInterval positive n,
    normalizedHarperEulerDensity y omega t

/-- Exact conversion from normalized local mass to the repository's local
energy normalization. -/
theorem harperEulerLocalEnergy_eq_normalizer_mul_normalizedLocalMass
    (y : ℕ) (positive : Bool) (n : ℕ) (omega : Omega) :
    harperEulerLocalEnergy y positive n omega =
      (primeEnergyNormalizer y / Real.log (y : ℝ)) *
        normalizedHarperEulerLocalMass y positive n omega := by
  have hZ : primeEnergyNormalizer y ≠ 0 :=
    (primeEnergyNormalizer_pos y).ne'
  have hdensity :
      (fun t ↦ harperEulerDensity y omega t) =
        fun t ↦ primeEnergyNormalizer y *
          normalizedHarperEulerDensity y omega t := by
    funext t
    unfold normalizedHarperEulerDensity
    field_simp
  unfold harperEulerLocalEnergy normalizedHarperEulerLocalMass
  rw [hdensity, integral_const_mul]
  ring

theorem volume_real_harperEulerUnitInterval_eq_one
    (positive : Bool) (n : ℕ) :
    volume.real (harperEulerUnitInterval positive n) = 1 := by
  cases positive <;>
    simp [harperEulerUnitInterval, Measure.real,
      Real.volume_Ioc, Real.volume_Ico]

/-- Generic restricted change-of-measure/Fubini bound.  The family `A t`
may be arbitrary: the prime cube is finite, so every one of its subsets is
measurable. -/
theorem integral_normalizedHarperEulerLocalMass_restrict_le
    (y : ℕ) (positive : Bool) (n : ℕ)
    {G : Set Omega} (hG : MeasurableSet G)
    (A : ℝ → Set (HarperPrimeCube y)) (H : ℝ)
    (hcontain : ∀ t ∈ harperEulerUnitInterval positive n,
      G ⊆ harperPrimeRestriction y ⁻¹' A t)
    (hprob : ∀ t ∈ harperEulerUnitInterval positive n,
      (harperTiltedCubeLaw y t).real (A t) ≤ H) :
    (∫ omega in G,
      normalizedHarperEulerLocalMass y positive n omega ∂μ) ≤ H := by
  let I : Set ℝ := harperEulerUnitInterval positive n
  let ν : Measure ℝ := volume.restrict I
  let F : ℝ × Omega → ℝ := fun w ↦
    normalizedHarperEulerDensity y w.2 w.1
  let S : Set (ℝ × Omega) := Set.univ ×ˢ G
  let FG : ℝ × Omega → ℝ := S.indicator F
  have hF : Integrable F (ν.prod μ) := by
    have hEuler :=
      integrable_harperEulerDensity_prod_unitInterval y positive n
    simpa only [F, ν, normalizedHarperEulerDensity] using!
      hEuler.div_const (primeEnergyNormalizer y)
  have hS : MeasurableSet S :=
    MeasurableSet.prod (MeasurableSet.univ :
      MeasurableSet (Set.univ : Set ℝ)) hG
  have hFG : Integrable FG (ν.prod μ) := hF.indicator hS
  have hleft :
      (∫ omega, ∫ t, FG (t, omega) ∂ν ∂μ) =
        ∫ omega in G,
          normalizedHarperEulerLocalMass y positive n omega ∂μ := by
    rw [← integral_indicator hG]
    apply integral_congr_ae
    exact ae_of_all μ fun omega ↦ by
      by_cases homega : omega ∈ G
      · simp [FG, S, F, homega, normalizedHarperEulerLocalMass, ν, I]
      · simp [FG, S, F, homega, ν, I]
  have hright (t : ℝ) :
      (∫ omega, FG (t, omega) ∂μ) =
        ∫ omega in G, normalizedHarperEulerDensity y omega t ∂μ := by
    rw [← integral_indicator hG]
    apply integral_congr_ae
    exact ae_of_all μ fun omega ↦ by
      by_cases homega : omega ∈ G
      · simp [FG, S, F, Set.indicator_of_mem, homega]
      · simp [FG, S, F, Set.indicator_of_notMem, homega]
  have hswap :
      (∫ omega, ∫ t, FG (t, omega) ∂ν ∂μ) =
        ∫ t, ∫ omega, FG (t, omega) ∂μ ∂ν :=
    (integral_prod_symm FG hFG).symm.trans (integral_prod FG hFG)
  have hfubini :
      (∫ omega in G,
          normalizedHarperEulerLocalMass y positive n omega ∂μ) =
        ∫ t, (∫ omega in G,
          normalizedHarperEulerDensity y omega t ∂μ) ∂ν := by
    calc
      (∫ omega in G,
          normalizedHarperEulerLocalMass y positive n omega ∂μ) =
          ∫ omega, ∫ t, FG (t, omega) ∂ν ∂μ := hleft.symm
      _ = ∫ t, ∫ omega, FG (t, omega) ∂μ ∂ν := hswap
      _ = ∫ t, (∫ omega in G,
          normalizedHarperEulerDensity y omega t ∂μ) ∂ν := by
        apply integral_congr_ae
        exact ae_of_all ν hright
  have hinner (t : ℝ) (ht : t ∈ I) :
      (∫ omega in G, normalizedHarperEulerDensity y omega t ∂μ) ≤ H := by
    have hint : IntegrableOn
        (fun omega ↦ normalizedHarperEulerDensity y omega t)
        (harperPrimeRestriction y ⁻¹' A t) μ :=
      (integrable_normalizedHarperEulerDensity y t).integrableOn
    have hnonneg : 0 ≤ᵐ[μ.restrict
        (harperPrimeRestriction y ⁻¹' A t)]
        fun omega ↦ normalizedHarperEulerDensity y omega t :=
      Eventually.of_forall fun omega ↦
        normalizedHarperEulerDensity_nonneg y omega t
    have hsubset : G ≤ᶠ[ae μ]
        (harperPrimeRestriction y ⁻¹' A t) :=
      Eventually.of_forall fun omega homega ↦
        hcontain t (by simpa only [I] using! ht) homega
    calc
      (∫ omega in G,
          normalizedHarperEulerDensity y omega t ∂μ) ≤
          ∫ omega in harperPrimeRestriction y ⁻¹' A t,
            normalizedHarperEulerDensity y omega t ∂μ :=
        setIntegral_mono_set hint hnonneg hsubset
      _ = (harperTiltedCubeLaw y t).real (A t) :=
        (harperTiltedCubeLaw_real_apply_eq_omega y t (A t)).symm
      _ ≤ H := hprob t (by simpa only [I] using! ht)
  have houterInt : Integrable
      (fun t ↦ ∫ omega in G,
        normalizedHarperEulerDensity y omega t ∂μ) ν := by
    have heq :
        (fun t ↦ ∫ omega, FG (t, omega) ∂μ) =
          fun t ↦ ∫ omega in G,
            normalizedHarperEulerDensity y omega t ∂μ := by
      funext t
      exact hright t
    rw [← heq]
    exact hFG.integral_prod_left
  have hbound : ∀ᵐ t ∂ν,
      (∫ omega in G,
        normalizedHarperEulerDensity y omega t ∂μ) ≤ H := by
    exact (ae_restrict_mem (measurableSet_harperEulerUnitInterval positive n)).mono
      fun t ht ↦ hinner t (by simpa only [ν, I] using! ht)
  have hIfinite : volume I ≠ ∞ := by
    dsimp only [I]
    cases positive <;>
      simp [harperEulerUnitInterval, Real.volume_Ioc, Real.volume_Ico]
  have hconst : Integrable (fun _t : ℝ ↦ H) ν := by
    simpa only [ν] using!
      (integrableOn_const (μ := volume) (s := I) (C := H) hIfinite)
  rw [hfubini]
  calc
    (∫ t, (∫ omega in G,
        normalizedHarperEulerDensity y omega t ∂μ) ∂ν) ≤
        ∫ _t, H ∂ν :=
      integral_mono_ae houterInt hconst hbound
    _ = H := by
      rw [integral_const]
      have hν : ν.real Set.univ = 1 := by
        dsimp only [ν]
        rw [measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact volume_real_harperEulerUnitInterval_eq_one positive n
      rw [hν]
      simp

/-- Restricted first moment of the actual local energy, with the exact
elementary Mertens constant. -/
theorem integral_harperEulerLocalEnergy_restrict_le_explicitMertens
    {y : ℕ} (hy : 2 ≤ y) (positive : Bool) (n : ℕ)
    {G : Set Omega} (hG : MeasurableSet G)
    (A : ℝ → Set (HarperPrimeCube y)) (H : ℝ)
    (hcontain : ∀ t ∈ harperEulerUnitInterval positive n,
      G ⊆ harperPrimeRestriction y ⁻¹' A t)
    (hprob : ∀ t ∈ harperEulerUnitInterval positive n,
      (harperTiltedCubeLaw y t).real (A t) ≤ H) :
    (∫ omega in G, harperEulerLocalEnergy y positive n omega ∂μ) ≤
      harperExplicitMertensConstant * H := by
  have hlog : 0 < Real.log (y : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < y by omega)
  have hcoeffNonneg :
      0 ≤ primeEnergyNormalizer y / Real.log (y : ℝ) :=
    div_nonneg (primeEnergyNormalizer_pos y).le hlog.le
  have hcoeff : primeEnergyNormalizer y / Real.log (y : ℝ) ≤
      harperExplicitMertensConstant := by
    apply (div_le_iff₀ hlog).2
    simpa only [harperExplicitMertensConstant] using!
      primeEnergyNormalizer_le_mertensConstant_mul_log hy
  have hmass := integral_normalizedHarperEulerLocalMass_restrict_le
    y positive n hG A H hcontain hprob
  have hH : 0 ≤ H := by
    cases positive with
    | false =>
        have hp := hprob (-(n : ℝ)) (by
          simp [harperEulerUnitInterval])
        exact measureReal_nonneg.trans hp
    | true =>
        have hp := hprob (n : ℝ) (by
          simp [harperEulerUnitInterval])
        exact measureReal_nonneg.trans hp
  have henergy :
      (∫ omega in G, harperEulerLocalEnergy y positive n omega ∂μ) =
        (primeEnergyNormalizer y / Real.log (y : ℝ)) *
          ∫ omega in G,
            normalizedHarperEulerLocalMass y positive n omega ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all (μ.restrict G) fun omega ↦
      harperEulerLocalEnergy_eq_normalizer_mul_normalizedLocalMass
        y positive n omega
  rw [henergy]
  calc
    (primeEnergyNormalizer y / Real.log (y : ℝ)) *
        (∫ omega in G,
          normalizedHarperEulerLocalMass y positive n omega ∂μ) ≤
        (primeEnergyNormalizer y / Real.log (y : ℝ)) * H :=
      mul_le_mul_of_nonneg_left hmass hcoeffNonneg
    _ ≤ harperExplicitMertensConstant * H :=
      mul_le_mul_of_nonneg_right hcoeff hH

end Problem520
end Erdos
