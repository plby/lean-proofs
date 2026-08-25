import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.Linarith

/-!
# Compact moment convergence

The polynomial approximation step in the Laplace Tauberian argument: convergence
of all moments on a compact interval implies weak convergence of finite measures.
In particular no density theorem for the arithmetic sequence is assumed here.
-/

open MeasureTheory Filter Topology
open scoped unitInterval

namespace Bernays

private theorem continuous_integrable (μ : FiniteMeasure I) (g : C(I, ℝ)) :
    Integrable g (μ : Measure I) :=
  g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

theorem integral_continuousMap_sub_le (μ : FiniteMeasure I) (f g : C(I, ℝ)) :
    |(∫ x, f x ∂(μ : Measure I)) - ∫ x, g x ∂(μ : Measure I)| ≤
      ‖f - g‖ * (μ : Measure I).real Set.univ := by
  rw [← integral_sub (continuous_integrable μ f) (continuous_integrable μ g), ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le_const
    (Filter.Eventually.of_forall fun x => (f - g).norm_coe_le_norm x)

theorem polynomial_integral_tendsto_of_moments {ι : Type*} {l : Filter ι}
    {μ : ι → FiniteMeasure I} {ν : FiniteMeasure I}
    (h : ∀ k : ℕ, Tendsto (fun i => ∫ x : I, (x : ℝ) ^ k ∂(μ i : Measure I)) l
      (𝓝 (∫ x : I, (x : ℝ) ^ k ∂(ν : Measure I)))) (p : Polynomial ℝ) :
    Tendsto (fun i => ∫ x : I, p.eval (x : ℝ) ∂(μ i : Measure I)) l
      (𝓝 (∫ x : I, p.eval (x : ℝ) ∂(ν : Measure I))) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hadd (ρ : FiniteMeasure I) :
          (∫ x : I, (p + q).eval (x : ℝ) ∂(ρ : Measure I)) =
            (∫ x : I, p.eval (x : ℝ) ∂(ρ : Measure I)) +
            ∫ x : I, q.eval (x : ℝ) ∂(ρ : Measure I) := by
        simpa only [Polynomial.eval_add, Polynomial.toContinuousMapOn_apply,
          Polynomial.toContinuousMap_apply] using
          integral_add (continuous_integrable ρ (p.toContinuousMapOn I))
            (continuous_integrable ρ (q.toContinuousMapOn I))
      simpa only [hadd] using hp.add hq
  | monomial n a =>
      simp only [Polynomial.eval_monomial, integral_const_mul]
      exact (h n).const_mul a

theorem continuous_integral_tendsto_of_moments {ι : Type*} {l : Filter ι}
    {μ : ι → FiniteMeasure I} {ν : FiniteMeasure I}
    (h : ∀ k : ℕ, Tendsto (fun i => ∫ x : I, (x : ℝ) ^ k ∂(μ i : Measure I)) l
      (𝓝 (∫ x : I, (x : ℝ) ^ k ∂(ν : Measure I)))) (g : C(I, ℝ)) :
    Tendsto (fun i => ∫ x, g x ∂(μ i : Measure I)) l
      (𝓝 (∫ x, g x ∂(ν : Measure I))) := by
  have hmass := h 0
  simp only [pow_zero, integral_const, smul_eq_mul, mul_one] at hmass
  let M : ℝ := (ν : Measure I).real Set.univ + 1
  have hν : 0 ≤ (ν : Measure I).real Set.univ := measureReal_nonneg
  have hM : 0 < M := add_pos_of_nonneg_of_pos hν zero_lt_one
  have hmass_bound : ∀ᶠ i in l, (μ i : Measure I).real Set.univ < M :=
    hmass.eventually (gt_mem_nhds (lt_add_one _))
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε / (4 * (M + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : δ * (M + 1) = ε / 4 := by
    dsimp [δ]
    rw [div_mul_eq_div_div, div_mul_cancel₀ _ (by linarith : M + 1 ≠ 0)]
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap 0 1 g δ hδ
  let P : C(I, ℝ) := p.toContinuousMapOn I
  have hP : ‖P - g‖ < δ := hp
  have hpoly := polynomial_integral_tendsto_of_moments h p
  have hpoly_bound := (Metric.tendsto_nhds.mp hpoly) (ε / 2) (half_pos hε)
  filter_upwards [hmass_bound, hpoly_bound] with i hi hpi
  rw [Real.dist_eq] at hpi ⊢
  have hleft : |(∫ x, g x ∂(μ i : Measure I)) - ∫ x, P x ∂(μ i : Measure I)| ≤ δ * M := by
    refine (integral_continuousMap_sub_le (μ i) g P).trans ?_
    rw [norm_sub_rev]
    exact mul_le_mul hP.le hi.le measureReal_nonneg hδ.le
  have hright : |(∫ x, P x ∂(ν : Measure I)) - ∫ x, g x ∂(ν : Measure I)| ≤ δ * M := by
    refine (integral_continuousMap_sub_le ν P g).trans ?_
    exact mul_le_mul hP.le (le_add_of_nonneg_right zero_le_one) hν hδ.le
  have htri :
      |(∫ x, g x ∂(μ i : Measure I)) - ∫ x, g x ∂(ν : Measure I)| ≤
        |(∫ x, g x ∂(μ i : Measure I)) - ∫ x, P x ∂(μ i : Measure I)| +
        |(∫ x, P x ∂(μ i : Measure I)) - ∫ x, P x ∂(ν : Measure I)| +
        |(∫ x, P x ∂(ν : Measure I)) - ∫ x, g x ∂(ν : Measure I)| := by
    linarith [abs_sub_le (∫ x, g x ∂(μ i : Measure I))
      (∫ x, P x ∂(μ i : Measure I)) (∫ x, g x ∂(ν : Measure I)),
      abs_sub_le (∫ x, P x ∂(μ i : Measure I))
        (∫ x, P x ∂(ν : Measure I)) (∫ x, g x ∂(ν : Measure I))]
  change |(∫ x, P x ∂(μ i : Measure I)) - ∫ x, P x ∂(ν : Measure I)| < ε / 2 at hpi
  nlinarith

theorem finiteMeasure_tendsto_of_moments {ι : Type*} {l : Filter ι}
    {μ : ι → FiniteMeasure I} {ν : FiniteMeasure I}
    (h : ∀ k : ℕ, Tendsto (fun i => ∫ x : I, (x : ℝ) ^ k ∂(μ i : Measure I)) l
      (𝓝 (∫ x : I, (x : ℝ) ^ k ∂(ν : Measure I)))) :
    Tendsto μ l (𝓝 ν) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro g
  exact continuous_integral_tendsto_of_moments h ⟨g, g.continuous⟩

end Bernays
