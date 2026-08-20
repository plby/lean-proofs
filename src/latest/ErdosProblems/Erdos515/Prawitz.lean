import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Prawitz--Hardy estimates used in Erdős Problem 515

The Lewis--Rossi--Weitsman short-path argument uses three analytically distinct inputs about a
normalized univalent map of the disk:

* Prawitz's integral inequality, followed by the Koebe upper distortion estimate, gives a
  uniform `H^(1/4)` bound for `G z / z`;
* the Hardy--Littlewood radial maximal theorem turns that Hardy bound into a weak estimate;
* the logarithmic-derivative area estimate gives a second small exceptional set.

Mathlib currently has neither the univalent-function area theorem nor the Hardy--Littlewood
maximal theorem.  This file therefore gives fully proved interfaces for precisely these inputs and
formally proves every measure-theoretic and elementary inequality needed after them.  In
particular, `hardy_quarter_of_prawitz` combines a normalized Prawitz estimate with Koebe on small
radii, `weakRadialMax_of_hardyQuarter` is the explicit hypothesis-discharge point for the missing
Hardy--Littlewood theorem, and `exists_goodAngle` performs the final exceptional-set selection.
-/

open MeasureTheory Set

open scoped ENNReal Real

namespace Erdos515

namespace Prawitz

/-- The angular parameter interval used throughout the disk estimates. -/
def angularInterval : Set ℝ := Ioc 0 (2 * Real.pi)

/-- The point `r * exp(i θ)` in the unit disk. -/
noncomputable def circlePoint (r θ : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

/-- The radial quotient `|G(r exp(iθ))| / r`. -/
noncomputable def radialQuotient (G : ℂ → ℂ) (r θ : ℝ) : ℝ :=
  ‖G (circlePoint r θ)‖ / r

/-- The Hardy exponent used by Lewis--Rossi--Weitsman. -/
noncomputable def quarter : ℝ := (1 : ℝ) / 4

lemma quarter_pos : 0 < quarter := by
  norm_num [quarter]

lemma quarter_nonneg : 0 ≤ quarter := quarter_pos.le

/-- The beta-integral envelope obtained by substituting Koebe's estimate
`M∞(s,G) ≤ s / (1-s)^2` into Prawitz's inequality at exponent `1/4`. -/
noncomputable def koebeQuarterKernel (s : ℝ) : ℝ :=
  s ^ (-(3 : ℝ) / 4) * (1 - s) ^ (-(1 : ℝ) / 2)

lemma koebeQuarterKernel_nonneg {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    0 ≤ koebeQuarterKernel s := by
  exact mul_nonneg (Real.rpow_nonneg hs.1.le _) (Real.rpow_nonneg (sub_nonneg.2 hs.2) _)

/-- The elementary beta kernel arising from Prawitz and Koebe is integrable. -/
theorem integrableOn_koebeQuarterKernel :
    IntegrableOn koebeQuarterKernel (Ioc (0 : ℝ) 1) := by
  have hbeta : IntervalIntegrable
      (fun s : ℝ ↦
        (s : ℂ) ^ (((1 : ℝ) / 4 : ℂ) - 1) *
          (1 - (s : ℂ)) ^ (((1 : ℝ) / 2 : ℂ) - 1)) volume 0 1 := by
    exact Complex.betaIntegral_convergent (by norm_num) (by norm_num)
  have hnorm : IntegrableOn
      (fun s : ℝ ↦
        ‖(s : ℂ) ^ (((1 : ℝ) / 4 : ℂ) - 1) *
          (1 - (s : ℂ)) ^ (((1 : ℝ) / 2 : ℂ) - 1)‖) (Ioc (0 : ℝ) 1) :=
    hbeta.norm.1
  refine hnorm.congr_fun ?_ measurableSet_Ioc
  intro s hs
  change ‖(s : ℂ) ^ (((1 : ℝ) / 4 : ℂ) - 1) *
      (1 - (s : ℂ)) ^ (((1 : ℝ) / 2 : ℂ) - 1)‖ = koebeQuarterKernel s
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hs.1]
  have hone : 1 - (s : ℂ) = ((1 - s : ℝ) : ℂ) := by push_cast; ring
  rw [hone, Complex.norm_cpow_eq_rpow_re_of_nonneg (sub_nonneg.2 hs.2) (by norm_num)]
  norm_num [koebeQuarterKernel]

/-- The normalized form of the Prawitz estimate needed in the proof.

The factor `r^(-1/4)` converts Prawitz's estimate for `|G|^(1/4)` to the
corresponding estimate for `|G/r|^(1/4)`. -/
def PrawitzQuarterBound (G : ℂ → ℂ) : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 →
    (∫ θ in angularInterval, (radialQuotient G r θ) ^ quarter) ≤
      r ^ (-quarter) * (Real.pi / 2) *
        ∫ s in Ioc (0 : ℝ) r, koebeQuarterKernel s

/-- The radial form of Koebe's upper distortion estimate. -/
def KoebeUpperBound (G : ℂ → ℂ) : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 → ∀ θ : ℝ,
    radialQuotient G r θ ≤ (1 - r) ^ (-2 : ℝ)

/-- A uniform `H^(1/4)` bound for the analytic radial quotient. -/
def HardyQuarterBound (G : ℂ → ℂ) (C : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 →
    (∫ θ in angularInterval, (radialQuotient G r θ) ^ quarter) ≤ C

/-- An explicit constant for the Prawitz--Koebe reduction.  Its second term is the
Prawitz beta integral; its first term controls radii at most `1/2` directly by Koebe. -/
noncomputable def hardyQuarterConstant : ℝ :=
  max
    ((2 * Real.pi) * (((1 : ℝ) / 2) ^ (-2 : ℝ)) ^ quarter)
    ((((1 : ℝ) / 2) ^ (-quarter)) * (Real.pi / 2) *
      ∫ s in Ioc (0 : ℝ) 1, koebeQuarterKernel s)

/-- Prawitz plus Koebe gives the uniform `H^(1/4)` estimate used in the LRW proof.

The elementary beta-integrability fact is an explicit hypothesis so that this theorem is usable
independently of any particular library representation of improper beta integrals.  It is not an
analytic/univalent-function assumption: it concerns only the displayed real function
`s^(-3/4) * (1-s)^(-1/2)`. -/
theorem hardy_quarter_of_prawitz (G : ℂ → ℂ)
    (hPrawitz : PrawitzQuarterBound G) (hKoebe : KoebeUpperBound G) :
    HardyQuarterBound G hardyQuarterConstant := by
  have hKernel := integrableOn_koebeQuarterKernel
  intro r hr hr1
  by_cases hrhalf : r ≤ (1 : ℝ) / 2
  · have hpoint : ∀ θ ∈ angularInterval,
        (radialQuotient G r θ) ^ quarter ≤
          (((1 : ℝ) / 2) ^ (-2 : ℝ)) ^ quarter := by
      intro θ _
      have hq := hKoebe r hr hr1 θ
      have hbase : (1 - r) ^ (-2 : ℝ) ≤ ((1 : ℝ) / 2) ^ (-2 : ℝ) := by
        apply Real.rpow_le_rpow_of_nonpos
        · linarith
        · linarith
        · norm_num
      exact (Real.rpow_le_rpow (div_nonneg (norm_nonneg _) hr.le) hq quarter_nonneg).trans
        (Real.rpow_le_rpow (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 - r) _)
          hbase quarter_nonneg)
    have hsmall := setIntegral_mono_of_nonneg
      (fun θ _ ↦ Real.rpow_nonneg (div_nonneg (norm_nonneg _) hr.le) _)
      hpoint (integrableOn_const (μ := volume) (s := angularInterval) measure_Ioc_lt_top.ne)
    refine hsmall.trans ?_
    rw [setIntegral_const]
    simp only [angularInterval, Measure.real, Real.volume_Ioc, sub_zero]
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi)]
    simp only [smul_eq_mul]
    exact le_max_left _ _
  · have hrhalf' : (1 : ℝ) / 2 ≤ r := le_of_not_ge hrhalf
    have hsubset : Ioc (0 : ℝ) r ⊆ Ioc (0 : ℝ) 1 := Ioc_subset_Ioc_right hr1.le
    have hkernel_nonneg :
        0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] koebeQuarterKernel := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact koebeQuarterKernel_nonneg hs
    have hkernel_mono :
        (∫ s in Ioc (0 : ℝ) r, koebeQuarterKernel s) ≤
          ∫ s in Ioc (0 : ℝ) 1, koebeQuarterKernel s :=
      setIntegral_mono_set hKernel hkernel_nonneg hsubset.eventuallyLE
    have hrpow : r ^ (-quarter) ≤ ((1 : ℝ) / 2) ^ (-quarter) := by
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) hrhalf' (by simp [quarter_nonneg])
    have hkernel_r_nonneg :
        0 ≤ ∫ s in Ioc (0 : ℝ) r, koebeQuarterKernel s := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact koebeQuarterKernel_nonneg ⟨hs.1, hs.2.trans hr1.le⟩
    refine (hPrawitz r hr hr1).trans ?_
    calc
      r ^ (-quarter) * (Real.pi / 2) *
          (∫ s in Ioc (0 : ℝ) r, koebeQuarterKernel s) ≤
          ((1 : ℝ) / 2) ^ (-quarter) * (Real.pi / 2) *
            (∫ s in Ioc (0 : ℝ) r, koebeQuarterKernel s) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hrpow (by positivity)) hkernel_r_nonneg
      _ ≤ ((1 : ℝ) / 2) ^ (-quarter) * (Real.pi / 2) *
            (∫ s in Ioc (0 : ℝ) 1, koebeQuarterKernel s) := by
        exact mul_le_mul_of_nonneg_left hkernel_mono
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by positivity))
      _ ≤ hardyQuarterConstant := le_max_right _ _

/-- A weak `L^(1/4)` estimate for a radial maximal function `H`, at scale `a`.

This is deliberately a predicate: it lets the missing Hardy--Littlewood theorem be supplied as an
ordinary theorem hypothesis rather than as an unproved declaration. -/
def WeakRadialMaxBound (H : ℝ → ℝ) (a A : ℝ) : Prop :=
  ∀ K : ℝ, 0 < K →
    volume (angularInterval ∩ {θ | K * a < H θ}) ≤
      ENNReal.ofReal (A * K ^ (-quarter))

/-- Exact hypothesis-discharge interface for the Hardy--Littlewood radial maximal theorem. -/
theorem weakRadialMax_of_hardyQuarter {G : ℂ → ℂ} {H : ℝ → ℝ} {a A C : ℝ}
    (hHardy : HardyQuarterBound G C)
    (hHardyLittlewood : HardyQuarterBound G C → WeakRadialMaxBound H a A) :
    WeakRadialMaxBound H a A :=
  hHardyLittlewood hHardy

/-- Chebyshev's inequality in the precise set-integral form used for the radial
logarithmic-derivative mass. -/
theorem measure_superlevel_le_of_integral_le {J : ℝ → ℝ} {C T : ℝ}
    (hJ : IntegrableOn J angularInterval)
    (hJnonneg : ∀ θ ∈ angularInterval, 0 ≤ J θ)
    (hJC : (∫ θ in angularInterval, J θ) ≤ C) (hT : 0 < T) :
    (volume.restrict angularInterval) {θ | T ≤ J θ} ≤ ENNReal.ofReal (C / T) := by
  have hscaled : Integrable (fun θ ↦ J θ / T) (volume.restrict angularInterval) :=
    hJ.div_const T
  have hscaled_nonneg : 0 ≤ᵐ[volume.restrict angularInterval] (fun θ ↦ J θ / T) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    exact div_nonneg (hJnonneg θ hθ) hT.le
  refine (hscaled.measure_le_integral hscaled_nonneg (fun θ hθ ↦ ?_)).trans ?_
  · exact (le_div_iff₀ hT).2 (by simpa using hθ)
  · rw [integral_div]
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hJC hT.le)

/-- If the sum of the measures of two exceptional sets is smaller than the measure of the good
set, a point survives both deletions.  No measurability hypotheses are needed. -/
theorem exists_mem_not_mem_two_of_measure_gt_add {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {good bad₁ bad₂ : Set α}
    (hmeasure : μ bad₁ + μ bad₂ < μ good) :
    ∃ x, x ∈ good ∧ x ∉ bad₁ ∧ x ∉ bad₂ := by
  by_contra h
  push Not at h
  have hsubset : good ⊆ bad₁ ∪ bad₂ := by
    intro x hx
    by_cases hxbad : x ∈ bad₁
    · exact Or.inl hxbad
    · exact Or.inr (h x hx hxbad)
  have hle : μ good ≤ μ bad₁ + μ bad₂ :=
    (measure_mono hsubset).trans (measure_union_le bad₁ bad₂)
  exact (not_le_of_gt hmeasure) hle

/-- The final good-angle selection in the LRW short-path proof.

The Hall-good angles have measure at least `π`; the radial-maximal and log-derivative exceptional
sets each have measure less than `π/4`.  Therefore at least one angle has all three properties. -/
theorem exists_goodAngle {good bad₁ bad₂ : Set ℝ}
    (hgood : ENNReal.ofReal Real.pi ≤ volume good)
    (hbad₁ : volume bad₁ < ENNReal.ofReal (Real.pi / 4))
    (hbad₂ : volume bad₂ < ENNReal.ofReal (Real.pi / 4)) :
    ∃ θ, θ ∈ good ∧ θ ∉ bad₁ ∧ θ ∉ bad₂ := by
  apply exists_mem_not_mem_two_of_measure_gt_add volume
  have hsum :
      ENNReal.ofReal (Real.pi / 4) + ENNReal.ofReal (Real.pi / 4) =
        ENNReal.ofReal (Real.pi / 2) := by
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ Real.pi / 4)
      (by positivity : 0 ≤ Real.pi / 4)]
    congr 1
    ring
  have hhalf : ENNReal.ofReal (Real.pi / 2) < ENNReal.ofReal Real.pi := by
    rw [ENNReal.ofReal_lt_ofReal_iff Real.pi_pos]
    linarith [Real.pi_pos]
  exact (add_le_add hbad₁.le hbad₂.le).trans_lt
    (hsum ▸ hhalf.trans_le hgood)

end Prawitz

end Erdos515
