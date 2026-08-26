import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Probability.Martingale.OptionalStopping

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos
namespace Problem520

/-- The finite running maximum used in Mathlib's version of Doob's weak maximal inequality. -/
noncomputable def finiteRunningMax (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ f k ω

section WeakToStrong

variable {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω} {M : Ω → ℝ}

/-- The measure-theoretic core of the finite Doob `Lᵖ` inequality.

This turns a weak maximal estimate `t * μ {t ≤ M} ≤ ν {t ≤ M}` into the
pre-Hölder strong-moment estimate.  It is stated for arbitrary measures so that it can also
be reused after conditioning/fixing the old coordinates of a finite product space. -/
theorem weakMaximal_moment_mul_le (hM_nonneg : 0 ≤ M) (hM_meas : Measurable M)
    (hweak : ∀ t : ℝ≥0,
      (t : ℝ≥0∞) * μ {ω | (t : ℝ) ≤ M ω} ≤ ν {ω | (t : ℝ) ≤ M ω})
    {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (p - 1) * ∫⁻ ω, ENNReal.ofReal (M ω ^ p) ∂μ ≤
      ENNReal.ofReal p * ∫⁻ ω, ENNReal.ofReal (M ω ^ (p - 1)) ∂ν := by
  rw [lintegral_rpow_eq_lintegral_meas_le_mul μ
      (Eventually.of_forall hM_nonneg) hM_meas.aemeasurable (by linarith : 0 < p)]
  rw [lintegral_rpow_eq_lintegral_meas_le_mul ν
      (Eventually.of_forall hM_nonneg) hM_meas.aemeasurable (by linarith : 0 < p - 1)]
  calc
    _ = (ENNReal.ofReal (p - 1) * ENNReal.ofReal p) *
          ∫⁻ t in Ioi (0 : ℝ),
            μ {ω | t ≤ M ω} * ENNReal.ofReal (t ^ (p - 1)) := by ac_rfl
    _ ≤ (ENNReal.ofReal (p - 1) * ENNReal.ofReal p) *
          ∫⁻ t in Ioi (0 : ℝ),
            ν {ω | t ≤ M ω} * ENNReal.ofReal (t ^ (p - 2)) := by
      apply mul_le_mul_right
      refine setLIntegral_mono' measurableSet_Ioi fun t ht ↦ ?_
      have ht0 : 0 < t := ht
      have hw := hweak ⟨t, ht0.le⟩
      have hw' : ENNReal.ofReal t * μ {ω | t ≤ M ω} ≤ ν {ω | t ≤ M ω} := by
        rw [ENNReal.coe_nnreal_eq] at hw
        norm_cast at hw
      have hpow : ENNReal.ofReal (t ^ (p - 1)) =
          ENNReal.ofReal t * ENNReal.ofReal (t ^ (p - 2)) := by
        rw [← ENNReal.ofReal_mul ht0.le]
        congr 1
        calc
          t ^ (p - 1) = t ^ (1 + (p - 2)) := by congr 1; ring
          _ = t ^ (1 : ℝ) * t ^ (p - 2) := Real.rpow_add ht0 1 (p - 2)
          _ = t * t ^ (p - 2) := by rw [Real.rpow_one]
      rw [hpow, mul_left_comm]
      calc
        _ = (ENNReal.ofReal t * μ {ω | t ≤ M ω}) *
            ENNReal.ofReal (t ^ (p - 2)) := by ac_rfl
        _ ≤ _ := mul_le_mul_left hw' _
    _ = _ := by
      have hsub : p - 1 - 1 = p - 2 := by ring
      rw [hsub]
      ac_rfl

end WeakToStrong

section Doob

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒜 : Filtration ℕ m₀} {f : ℕ → Ω → ℝ}

/-- A finite running maximum is in `Lᵖ` when each of its finitely many entries is. -/
theorem memLp_finiteRunningMax {p : ℝ≥0∞} {n : ℕ}
    (hf : ∀ k ≤ n, MemLp (f k) p μ) : MemLp (finiteRunningMax f n) p μ := by
  unfold finiteRunningMax
  have hsup : MemLp ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one f) p μ :=
    Finset.sup'_induction (p := fun g : Ω → ℝ ↦ MemLp g p μ)
      Finset.nonempty_range_add_one f
      (fun _ ha _ hb ↦ ha.sup hb) fun k hk ↦ hf k (by simpa using! hk)
  refine hsup.ae_eq (Eventually.of_forall fun ω ↦ ?_)
  exact Finset.sup'_apply Finset.nonempty_range_add_one f ω

/-- Convexity of `x ↦ |x| ^ r`, packaged in the form needed by conditional Jensen. -/
private theorem convexOn_univ_abs_pow (r : ℕ) :
    ConvexOn ℝ univ (fun x : ℝ ↦ |x| ^ r) := by
  have habs : ConvexOn ℝ univ (fun x : ℝ ↦ |x|) := by
    simpa only [Real.norm_eq_abs] using! (convexOn_univ_norm :
      ConvexOn ℝ univ (fun x : ℝ ↦ ‖x‖))
  have himage : (fun x : ℝ ↦ |x|) '' univ = Ici 0 := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact abs_nonneg x
    · intro hy
      exact ⟨y, Set.mem_univ y, abs_of_nonneg hy⟩
  change ConvexOn ℝ univ ((fun y : ℝ ↦ y ^ r) ∘ fun x : ℝ ↦ |x|)
  apply ConvexOn.comp
  · rw [himage]
    exact convexOn_pow r
  · exact habs
  · rw [himage]
    exact pow_left_monotoneOn

/-- Convex powers of the absolute value of a real martingale form a submartingale.

The explicit integrability hypothesis is the only extra input needed by Mathlib's conditional
Jensen theorem.  It is automatic for the finite Walsh polynomials in the fresh-sign cube. -/
theorem Martingale.abs_pow_submartingale [SigmaFiniteFiltration μ 𝒜]
    (hX : Martingale f 𝒜 μ) (r : ℕ)
    (hint : ∀ k, Integrable (fun ω ↦ |f k ω| ^ r) μ) :
    Submartingale (fun k ω ↦ |f k ω| ^ r) 𝒜 μ := by
  let φ : ℝ → ℝ := fun x ↦ |x| ^ r
  have hφ_cvx : ConvexOn ℝ univ φ := convexOn_univ_abs_pow r
  have hφ_cont : LowerSemicontinuous φ := by
    exact (_root_.continuous_abs.pow r).lowerSemicontinuous
  refine ⟨?_, ?_, hint⟩
  · intro k
    simpa only [Real.norm_eq_abs, Pi.pow_apply] using! (hX.stronglyAdapted k).norm.pow r
  · intro i j hij
    have hJensen := hφ_cvx.map_condExp_le_univ (𝒜.le i) hφ_cont
      (hX.integrable j) (by simpa only [φ, Function.comp_apply] using! hint j)
    filter_upwards [hX.condExp_ae_eq hij, hJensen] with ω hcond hJ
    simpa only [φ, Function.comp_apply, hcond] using! hJ

/-- The pre-Hölder form of finite Doob `Lᵖ`, obtained from Mathlib's weak maximal
inequality and `weakMaximal_moment_mul_le`.

The right side is written using a density measure.  Expanding that density turns it into
`∫ f n * M^(p-1)`, the standard last step before Hölder's inequality. -/
theorem Submartingale.finiteRunningMax_moment_mul_le [IsFiniteMeasure μ]
    (hsub : Submartingale f 𝒜 μ) (hnonneg : 0 ≤ f) {p : ℝ} (hp : 1 < p) (n : ℕ) :
    ENNReal.ofReal (p - 1) *
        ∫⁻ ω, ENNReal.ofReal (finiteRunningMax f n ω ^ p) ∂μ ≤
      ENNReal.ofReal p *
        ∫⁻ ω, ENNReal.ofReal (finiteRunningMax f n ω ^ (p - 1))
          ∂μ.withDensity (fun ω ↦ ENNReal.ofReal (f n ω)) := by
  have hM_meas : Measurable (finiteRunningMax f n) := by
    exact Finset.measurable_range_sup'' fun k _ ↦
      (hsub.stronglyMeasurable k).measurable.le (𝒜.le k)
  have hM_nonneg : 0 ≤ finiteRunningMax f n := by
    intro ω
    exact (hnonneg 0 ω).trans (Finset.le_sup' (fun k ↦ f k ω) (by simp))
  refine weakMaximal_moment_mul_le hM_nonneg hM_meas ?_ hp
  intro t
  let s := {ω | (t : ℝ) ≤ finiteRunningMax f n ω}
  have hs : MeasurableSet s := measurableSet_le measurable_const hM_meas
  rw [withDensity_apply _ hs]
  rw [← ofReal_integral_eq_lintegral_ofReal (hsub.integrable n).integrableOn]
  · simpa only [finiteRunningMax] using! maximal_ineq hsub hnonneg n
  · exact ae_restrict_of_ae (Eventually.of_forall fun ω ↦ hnonneg n ω)

/-- `Submartingale.finiteRunningMax_moment_mul_le` with the density expanded as a product. -/
theorem Submartingale.finiteRunningMax_moment_mul_le' [IsFiniteMeasure μ]
    (hsub : Submartingale f 𝒜 μ) (hnonneg : 0 ≤ f) {p : ℝ} (hp : 1 < p) (n : ℕ) :
    ENNReal.ofReal (p - 1) *
        ∫⁻ ω, ENNReal.ofReal (finiteRunningMax f n ω ^ p) ∂μ ≤
      ENNReal.ofReal p * ∫⁻ ω,
        ENNReal.ofReal (f n ω) *
          ENNReal.ofReal (finiteRunningMax f n ω ^ (p - 1)) ∂μ := by
  have hfn_meas : Measurable (f n) :=
    (hsub.stronglyMeasurable n).measurable.le (𝒜.le n)
  have hM_meas : Measurable (finiteRunningMax f n) := by
    exact Finset.measurable_range_sup'' fun k _ ↦
      (hsub.stronglyMeasurable k).measurable.le (𝒜.le k)
  have hpow_meas : Measurable (fun ω ↦
      ENNReal.ofReal (finiteRunningMax f n ω ^ (p - 1))) := by
    apply Measurable.ennreal_ofReal
    exact (Real.continuous_rpow_const (by linarith : 0 ≤ p - 1)).measurable.comp hM_meas
  have h := Submartingale.finiteRunningMax_moment_mul_le hsub hnonneg hp n
  rw [lintegral_withDensity_eq_lintegral_mul μ hfn_meas.ennreal_ofReal hpow_meas] at h
  simpa only [Pi.mul_apply] using! h

/-- Finite Doob `L²` in the exact squared-moment form used by the thin-block argument.

The two `MemLp` assumptions merely supply finiteness for the last Cauchy--Schwarz step.  On the
finite fresh-sign cube relevant to Problem 520 they follow immediately from boundedness. -/
theorem Submartingale.integral_sq_finiteRunningMax_le [IsFiniteMeasure μ]
    (hsub : Submartingale f 𝒜 μ) (hnonneg : 0 ≤ f) (n : ℕ)
    (hM : MemLp (finiteRunningMax f n) 2 μ) (hfn : MemLp (f n) 2 μ) :
    ∫ ω, finiteRunningMax f n ω ^ 2 ∂μ ≤
      4 * ∫ ω, f n ω ^ 2 ∂μ := by
  have hM_nonneg : 0 ≤ finiteRunningMax f n := by
    intro ω
    exact (hnonneg 0 ω).trans (Finset.le_sup' (fun k ↦ f k ω) (by simp))
  have hM_sq_nonneg : 0 ≤ᵐ[μ] fun ω ↦ finiteRunningMax f n ω ^ 2 :=
    Eventually.of_forall fun _ ↦ sq_nonneg _
  have hfn_sq_nonneg : 0 ≤ᵐ[μ] fun ω ↦ f n ω ^ 2 :=
    Eventually.of_forall fun _ ↦ sq_nonneg _
  have hprod_nonneg : 0 ≤ᵐ[μ] fun ω ↦ f n ω * finiteRunningMax f n ω :=
    Eventually.of_forall fun ω ↦ mul_nonneg (hnonneg n ω) (hM_nonneg ω)
  have hprod_int : Integrable (fun ω ↦ f n ω * finiteRunningMax f n ω) μ := by
    simpa only [Pi.mul_apply] using! hfn.integrable_mul hM
  have hlin_prod :
      ∫⁻ ω, ENNReal.ofReal (f n ω) *
          ENNReal.ofReal (finiteRunningMax f n ω) ∂μ =
        ENNReal.ofReal (∫ ω, f n ω * finiteRunningMax f n ω ∂μ) := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (f n ω * finiteRunningMax f n ω) ∂μ := by
        refine lintegral_congr fun ω ↦ ?_
        exact (ENNReal.ofReal_mul (hnonneg n ω)).symm
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hprod_int hprod_nonneg).symm
  have hcore := Submartingale.finiteRunningMax_moment_mul_le'
    hsub hnonneg (p := (2 : ℝ)) (by norm_num) n
  norm_num [Real.rpow_two] at hcore
  rw [← ofReal_integral_eq_lintegral_ofReal hM.integrable_sq hM_sq_nonneg, hlin_prod] at hcore
  have hcore_real :
      ∫ ω, finiteRunningMax f n ω ^ 2 ∂μ ≤
        2 * ∫ ω, f n ω * finiteRunningMax f n ω ∂μ := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at hcore
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (by norm_num) (integral_nonneg_of_ae hprod_nonneg))).mp hcore
  have hholder :
      ∫ ω, f n ω * finiteRunningMax f n ω ∂μ ≤
        (∫ ω, f n ω ^ 2 ∂μ).sqrt *
          (∫ ω, finiteRunningMax f n ω ^ 2 ∂μ).sqrt := by
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using!
      (integral_mul_le_Lp_mul_Lq_of_nonneg (p := (2 : ℝ)) (q := (2 : ℝ)) (μ := μ)
      (Real.holderConjugate_iff.mpr (by norm_num))
      (Eventually.of_forall fun ω ↦ hnonneg n ω)
      (Eventually.of_forall hM_nonneg) (by simpa using! hfn) (by simpa using! hM))
  have hA_nonneg : 0 ≤ ∫ ω, finiteRunningMax f n ω ^ 2 ∂μ :=
    integral_nonneg_of_ae hM_sq_nonneg
  have hB_nonneg : 0 ≤ ∫ ω, f n ω ^ 2 ∂μ :=
    integral_nonneg_of_ae hfn_sq_nonneg
  nlinarith [sq_nonneg
    ((∫ ω, finiteRunningMax f n ω ^ 2 ∂μ).sqrt -
      2 * (∫ ω, f n ω ^ 2 ∂μ).sqrt),
    Real.sq_sqrt hA_nonneg, Real.sq_sqrt hB_nonneg,
    Real.sqrt_nonneg (∫ ω, finiteRunningMax f n ω ^ 2 ∂μ),
    Real.sqrt_nonneg (∫ ω, f n ω ^ 2 ∂μ)]

/-- Finite Doob `L²` with only the natural terminal `L²` hypothesis. -/
theorem Submartingale.integral_sq_finiteRunningMax_le_of_terminal [IsFiniteMeasure μ]
    (hsub : Submartingale f 𝒜 μ) (hnonneg : 0 ≤ f) (n : ℕ)
    (hfn : MemLp (f n) 2 μ) :
    ∫ ω, finiteRunningMax f n ω ^ 2 ∂μ ≤
      4 * ∫ ω, f n ω ^ 2 ∂μ := by
  apply Submartingale.integral_sq_finiteRunningMax_le hsub hnonneg n _ hfn
  apply memLp_finiteRunningMax
  intro k hk
  have hce : MemLp (μ[f n | 𝒜 k]) 2 μ := hfn.condExp (by norm_num)
  refine hce.mono' (hsub.integrable k).aestronglyMeasurable ?_
  filter_upwards [hsub.ae_le_condExp hk] with ω hle
  simpa only [Real.norm_of_nonneg (hnonneg k ω)] using! hle

/-- The finite even-moment Doob estimate needed in equation (17).

The left side is `(max_{k ≤ n} |X_k|^r)^2`, i.e. `max_{k ≤ n} |X_k|^(2r)`.
The only analytic side conditions are the integrability needed by conditional Jensen and the
terminal `2r`-moment. -/
theorem Martingale.integral_sq_finiteRunningMax_abs_pow_le
    [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝒜]
    (hX : Martingale f 𝒜 μ) (r n : ℕ)
    (hint : ∀ k, Integrable (fun ω ↦ |f k ω| ^ r) μ)
    (hterminal : MemLp (fun ω ↦ |f n ω| ^ r) 2 μ) :
    ∫ ω, finiteRunningMax (fun k ω ↦ |f k ω| ^ r) n ω ^ 2 ∂μ ≤
      4 * ∫ ω, |f n ω| ^ (2 * r) ∂μ := by
  have hY := Martingale.abs_pow_submartingale hX r hint
  have h := Submartingale.integral_sq_finiteRunningMax_le_of_terminal hY
    (fun _ _ ↦ pow_nonneg (abs_nonneg _) _) n hterminal
  simpa only [← pow_mul, Nat.mul_comm r 2] using! h

end Doob

end Problem520
end Erdos
