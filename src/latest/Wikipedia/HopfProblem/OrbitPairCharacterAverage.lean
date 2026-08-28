import Wikipedia.HopfProblem.SmoothCircleAverageBasic
import Wikipedia.HopfProblem.SmoothManifoldParameterIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Character-weighted circle averages

Weighting a period-one average by the inverse unit character produces
an equivariant complex-valued function. A function approximating that
character on one orbit has a nonzero weighted average there. These are
the analytic ingredients for constructing local sections of the actual
free circle quotient.
-/

noncomputable section

open Set MeasureTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.CharacterAverage

variable {M : Type*}

/-- The literal first-character projection, integrated over one period. -/
def average (act : ℝ → M → M) (χ : ℝ → ℂ) (g : M → ℂ) (x : M) : ℂ :=
  ∫ t in (0 : ℝ)..1, (χ t)⁻¹ * g (act t x)

theorem equivariant (act : ℝ → M → M) (χ : ℝ → ℂ)
    (hadd : ∀ t s x, act (t + s) x = act t (act s x))
    (hperiod : ∀ t x, act (t + 1) x = act t x)
    (hχadd : ∀ t s, χ (t + s) = χ t * χ s)
    (hχperiod : ∀ t, χ (t + 1) = χ t) (hχne : ∀ t, χ t ≠ 0)
    (g : M → ℂ) (s : ℝ) (x : M) :
    average act χ g (act s x) = χ s * average act χ g x := by
  let f : ℝ → ℂ := fun t => (χ t)⁻¹ * g (act t x)
  have hf : Function.Periodic f 1 := by
    intro t
    simp only [f, hχperiod, hperiod]
  have he : (fun t : ℝ => (χ t)⁻¹ * g (act t (act s x))) =
      (fun t => χ s * f (t + s)) := by
    funext t
    dsimp only [f]
    rw [hχadd, hadd]
    field_simp [hχne t, hχne s]
  change (∫ t in (0 : ℝ)..1, (χ t)⁻¹ * g (act t (act s x))) =
    χ s * ∫ t in (0 : ℝ)..1, f t
  rw [he, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_add_right f s, zero_add, add_comm (1 : ℝ) s]
  rw [hf.intervalIntegral_add_eq s 0, zero_add]

section Topology

variable [TopologicalSpace M]

theorem integrand_continuous (act : ℝ → M → M) (χ : ℝ → ℂ)
    (hact : Continuous (fun p : ℝ × M => act p.1 p.2))
    (hχ : Continuous χ) (hχne : ∀ t, χ t ≠ 0) {g : M → ℂ}
    (hg : Continuous g) (x : M) : Continuous (fun t => (χ t)⁻¹ * g (act t x)) :=
  (hχ.inv₀ hχne).mul (hg.comp (hact.comp (continuous_id.prodMk continuous_const)))

/-- Approximation of the unit character on one orbit controls its weighted average. -/
theorem dist_one_le_of_orbit_bound (act : ℝ → M → M) (χ : ℝ → ℂ)
    (hact : Continuous (fun p : ℝ × M => act p.1 p.2)) (hχ : Continuous χ)
    (hχunit : ∀ t, ‖χ t‖ = 1) {g : M → ℂ} (hg : Continuous g)
    (x : M) {ε : ℝ} (hbound : ∀ t ∈ Icc (0 : ℝ) 1, dist (g (act t x)) (χ t) ≤ ε) :
    dist (average act χ g x) 1 ≤ ε := by
  have hχne (t : ℝ) : χ t ≠ 0 := by
    intro h
    have hn := hχunit t
    rw [h, norm_zero] at hn
    norm_num at hn
  have hi : IntervalIntegrable (fun t => (χ t)⁻¹ * g (act t x)) volume 0 1 :=
    (integrand_continuous act χ hact hχ hχne hg x).intervalIntegrable 0 1
  have he : average act χ g x - 1 =
      ∫ t in (0 : ℝ)..1, (χ t)⁻¹ * g (act t x) - 1 := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [average, sub_zero, one_smul]
  rw [dist_eq_norm, he]
  have hb : ∀ t ∈ uIoc (0 : ℝ) 1, ‖(χ t)⁻¹ * g (act t x) - 1‖ ≤ ε := by
    intro t ht
    rw [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
    have he' : (χ t)⁻¹ * g (act t x) - 1 = (χ t)⁻¹ * (g (act t x) - χ t) := by
      rw [mul_sub, inv_mul_cancel₀ (hχne t)]
    rw [he', norm_mul, norm_inv, hχunit, inv_one, one_mul]
    simpa only [dist_eq_norm] using hbound t ⟨ht.1.le, ht.2⟩
  simpa only [sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const hb

theorem average_ne_zero_of_orbit_close (act : ℝ → M → M) (χ : ℝ → ℂ)
    (hact : Continuous (fun p : ℝ × M => act p.1 p.2)) (hχ : Continuous χ)
    (hχunit : ∀ t, ‖χ t‖ = 1) {g : M → ℂ} (hg : Continuous g) (x : M)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, dist (g (act t x)) (χ t) < (1 / 2 : ℝ)) :
    average act χ g x ≠ 0 := by
  have hd := dist_one_le_of_orbit_bound act χ hact hχ hχunit hg x
    (fun t ht => (hbound t ht).le)
  intro hz
  rw [hz] at hd
  norm_num at hd

end Topology

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem smooth (act : ℝ → M → M) (χ : ℝ → ℂ)
    (hact : ContMDiff ((𝓘(ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => act p.1 p.2))
    (hχ : ContDiff ℝ ∞ χ) (hχne : ∀ t, χ t ≠ 0) {g : M → ℂ}
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ g) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (average act χ g) := by
  have hswap : ContMDiff ((𝓘(ℝ, E)).prod 𝓘(ℝ))
      ((𝓘(ℝ)).prod 𝓘(ℝ, E)) ∞ (Prod.swap : M × ℝ → ℝ × M) :=
    contMDiff_snd.prodMk contMDiff_fst
  have hinv : ContDiff ℝ ∞ (fun t => (χ t)⁻¹) := hχ.inv hχne
  have hp : ContMDiff ((𝓘(ℝ, E)).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ × ℂ) ∞
      (fun p : M × ℝ => ((χ p.2)⁻¹, g (act p.2 p.1))) :=
    (hinv.contMDiff.comp contMDiff_snd).prodMk_space ((hg.comp hact).comp hswap)
  exact SmoothManifoldParameterIntegral.contMDiff_intervalIntegral
    (contDiff_mul.contMDiff.comp hp) 0 1

end Smooth

end Wikipedia.HopfProblem.OrbitPair.CharacterAverage
