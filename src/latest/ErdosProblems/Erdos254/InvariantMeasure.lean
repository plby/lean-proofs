/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.Basic

namespace Erdos254

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

/-- Probability measure on the first `N+1` points of an orbit. -/
noncomputable def orbitEmpirical (T : X → X) (x : X) (N : ℕ) : ProbabilityMeasure X :=
  ⟨((N + 1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range (N + 1), Measure.dirac (T^[k] x), by
    constructor
    simp only [Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply, Measure.dirac_apply_of_mem,
      mem_univ, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast Nat.succ_ne_zero N) (by simp)⟩

lemma integral_orbitEmpirical (T : X → X) (x : X) (N : ℕ) (g : C(X, ℝ)) :
    (∫ y, g y ∂(orbitEmpirical T x N : Measure X)) =
      birkhoffAverage ℝ T g (N + 1) x := by
  change (∫ y, g y ∂(((N + 1 : ℕ) : ℝ≥0∞)⁻¹ •
    ∑ k ∈ Finset.range (N + 1), Measure.dirac (T^[k] x))) = _
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, birkhoffAverage, birkhoffSum, ENNReal.toReal_add]
  · intro k _
    exact g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma integral_orbitEmpirical_comp (T : X → X) (hT : Continuous T) (x : X)
    (N : ℕ) (g : C(X, ℝ)) :
    (∫ y, g (T y) ∂(orbitEmpirical T x N : Measure X)) =
      birkhoffAverage ℝ T g (N + 1) (T x) := by
  change (∫ y, (g.comp ⟨T, hT⟩) y ∂(orbitEmpirical T x N : Measure X)) = _
  rw [integral_orbitEmpirical]
  simp only [birkhoffAverage, birkhoffSum, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [← Function.iterate_succ_apply' T k x, Function.iterate_succ_apply T k x]

/-- Krylov--Bogolyubov construction with an explicit lower bound on one
observable. Compactness is applied to empirical probability measures. -/
theorem exists_invariant_probability [HasOuterApproxClosed X]
    (T : X → X) (hT : Continuous T) (x : X) (f : C(X, ℝ)) (δ : ℝ)
    (hf : ∃ᶠ N : ℕ in atTop, δ ≤ birkhoffAverage ℝ T f (N + 1) x) :
    ∃ μ : ProbabilityMeasure X,
      MeasurePreserving T (μ : Measure X) μ ∧ δ ≤ ∫ y, f y ∂(μ : Measure X) := by
  let L : Filter ℕ := atTop ⊓ 𝓟 {N | δ ≤ birkhoffAverage ℝ T f (N + 1) x}
  have : L.NeBot := frequently_iff_neBot.mp hf
  let p := Ultrafilter.of L
  let q := p.map (orbitEmpirical T x)
  let μ : ProbabilityMeasure X := q.lim
  have hp : (p : Filter ℕ) ≤ atTop := (Ultrafilter.of_le L).trans inf_le_left
  have hlim : Tendsto (orbitEmpirical T x) (p : Filter ℕ) (𝓝 μ) := by
    change Filter.map (orbitEmpirical T x) (p : Filter ℕ) ≤ 𝓝 μ
    rw [← Ultrafilter.coe_map]
    exact q.le_nhds_lim
  have hi (g : C(X, ℝ)) : Tendsto
      (fun N ↦ ∫ y, g y ∂(orbitEmpirical T x N : Measure X)) (p : Filter ℕ)
      (𝓝 (∫ y, g y ∂(μ : Measure X))) :=
    ((ProbabilityMeasure.continuous_integral_continuousMap g).tendsto μ).comp hlim
  have hinv (g : C(X, ℝ)) : (∫ y, g (T y) ∂(μ : Measure X)) = ∫ y, g y ∂(μ : Measure X) := by
    have hbound : Bornology.IsBounded (Set.range g) := (isCompact_range g.continuous).isBounded
    have hsmall := (tendsto_birkhoffAverage_apply_sub_birkhoffAverage' ℝ hbound T x).comp
      (tendsto_add_atTop_nat 1)
    have hzero : Tendsto (fun N ↦
        (∫ y, g (T y) ∂(orbitEmpirical T x N : Measure X)) -
        ∫ y, g y ∂(orbitEmpirical T x N : Measure X)) (p : Filter ℕ) (𝓝 0) := by
      simpa only [integral_orbitEmpirical_comp T hT, integral_orbitEmpirical, Function.comp_def]
        using hsmall.mono_left hp
    have hdiff := (hi (g.comp ⟨T, hT⟩)).sub (hi g)
    exact sub_eq_zero.mp (tendsto_nhds_unique hdiff hzero)
  have hmap : Measure.map T (μ : Measure X) = (μ : Measure X) := by
    let ν : FiniteMeasure X := ⟨Measure.map T (μ : Measure X), inferInstance⟩
    have hEq : ν = μ.toFiniteMeasure := by
      apply FiniteMeasure.ext_of_forall_integral_eq
      intro g
      change (∫ y, g y ∂Measure.map T (μ : Measure X)) = ∫ y, g y ∂(μ : Measure X)
      rw [integral_map_of_stronglyMeasurable hT.measurable g.continuous.stronglyMeasurable]
      exact hinv g.toContinuousMap
    exact congrArg FiniteMeasure.toMeasure hEq
  refine ⟨μ, ⟨hT.measurable, hmap⟩, ge_of_tendsto (hi f) ?_⟩
  have hgood : ∀ᶠ N in (p : Filter ℕ), δ ≤ birkhoffAverage ℝ T f (N + 1) x :=
    (Ultrafilter.of_le L).trans inf_le_right (by simp)
  simpa only [integral_orbitEmpirical] using hgood

end Erdos254
