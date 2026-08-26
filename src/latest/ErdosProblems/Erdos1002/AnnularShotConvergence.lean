import ErdosProblems.Erdos1002.AnnularGridPartition
import ErdosProblems.Erdos1002.CountControlledApproximation
import ErdosProblems.Erdos1002.ConvergingTogether
import ErdosProblems.Erdos1002.FinitePartitionCountTightness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Convergence of the annular marked shot through explicit grids

This file closes the probability-theoretic mesh argument.  The grid at level
`m` is the explicit `(m+1)`-subdivision from `AnnularGridPartition`.  For each
fixed grid, mixed falling-factorial moments give the weighted independent
Poisson law.  Uniform tightness of the retained point count then turns the
deterministic kernel error into the nested two-parameter probability estimate
required by the converging-together theorem.

Thus neither the order of limits nor the dependence of the error on the
random number of points is left implicit.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos1002

noncomputable section

open MultivariateFactorialMomentMethod

local instance probabilityMeasureWeakTopologyASC :
    TopologicalSpace (ProbabilityMeasure ℝ) :=
  ProbabilityMeasure.instTopologicalSpace

/-- The mixed-factorial order selecting just one coordinate. -/
def singletonFactorialOrder {ι : Type*} [DecidableEq ι]
    (i : ι) : ι → ℕ :=
  fun j ↦ if j = i then 1 else 0

@[simp]
theorem mixedDescFactorial_singletonFactorialOrder
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (x : ι → ℕ) :
    mixedDescFactorial (singletonFactorialOrder i) x = x i := by
  classical
  unfold mixedDescFactorial singletonFactorialOrder
  rw [Fintype.prod_eq_single i]
  · simp
  · intro j hji
    simp [hji]

@[simp]
theorem prod_pow_singletonFactorialOrder
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (r : ι → NNReal) :
    (∏ j, (r j : ℝ) ^ (singletonFactorialOrder i j)) = (r i : ℝ) := by
  classical
  unfold singletonFactorialOrder
  rw [Fintype.prod_eq_single i]
  · simp
  · intro j hji
    simp [hji]

/-- The literal finite-cell approximation on the explicit level-`m` grid. -/
def annularGridShotApproximation
    (m N : ℕ) (ε A : ℝ) (α : ℝ) : ℝ :=
  finiteCellMarkedShotApproximation N N
    (annularGridCell ε A (m + 1))
    (fun i ↦ markedShotKernel (annularGridCenter ε A (m + 1) i)) α

theorem measurable_annularGridShotApproximation
    (m N : ℕ) (ε A : ℝ) :
    Measurable (annularGridShotApproximation m N ε A) := by
  unfold annularGridShotApproximation
  exact measurable_finiteCellMarkedShotApproximation N N
    (fun i ↦ measurableSet_annularGridCell ε A (m + 1) i) _

/-- Probability law of the explicit grid approximation. -/
def annularGridShotLaw
    (m N : ℕ) (ε A : ℝ) : ProbabilityMeasure ℝ :=
  uniform01.map
    (measurable_annularGridShotApproximation m N ε A).aemeasurable

/-- Probability law of the exact annular marked shot. -/
def annularMarkedShotLaw (N : ℕ) (ε A : ℝ) : ProbabilityMeasure ℝ :=
  uniform01.map (measurable_annularMarkedShotFunctional N ε A).aemeasurable

/-- The explicit grid law is exactly the finite-cell law used by the
count-vector moment method. -/
theorem annularGridShotLaw_eq_finiteCellMarkedShotLaw
    (m N : ℕ) (ε A : ℝ) :
    annularGridShotLaw m N ε A =
      finiteCellMarkedShotLaw N N
        (annularGridCell ε A (m + 1))
        (fun i ↦ measurableSet_annularGridCell ε A (m + 1) i)
        (fun i ↦ markedShotKernel (annularGridCenter ε A (m + 1) i)) := by
  rfl

/-- Fixed-grid convergence follows directly from convergence of every mixed
falling-factorial moment of the actual cell-count vector. -/
theorem tendsto_annularGridShotLaw_of_mixedFactorialMoments
    (m : ℕ) (Ns : ℕ → ℕ) (ε A : ℝ)
    (r : AnnularGridIndex (m + 1) → NNReal)
    (hFac : ∀ k : AnnularGridIndex (m + 1) → ℕ,
      Tendsto
        (fun n ↦ mixedFactorialMoment
          (markedResonanceCountVectorLaw (Ns n) (Ns n)
            (annularGridCell ε A (m + 1))
            (fun i ↦ measurableSet_annularGridCell ε A (m + 1) i)) k)
        atTop (𝓝 (∏ i, (r i : ℝ) ^ (k i)))) :
    Tendsto
      (fun n ↦ annularGridShotLaw m (Ns n) ε A)
      atTop
      (𝓝 (weightedIndependentPoissonLaw r
        (fun i ↦ markedShotKernel (annularGridCenter ε A (m + 1) i)))) := by
  simpa only [annularGridShotLaw_eq_finiteCellMarkedShotLaw] using!
    tendsto_finiteCellMarkedShotLaw_of_mixedFactorialMoments
      Ns Ns (annularGridCell ε A (m + 1))
      (fun i ↦ measurableSet_annularGridCell ε A (m + 1) i)
      r (fun i ↦ markedShotKernel (annularGridCenter ε A (m + 1) i)) hFac

/-- The order-one mixed factorial limit is literally the first moment of one
actual grid-cell count. -/
theorem tendsto_integral_annularGridCell_count_of_mixedFactorialMoments
    (m : ℕ) (Ns : ℕ → ℕ) (ε A : ℝ)
    (r : AnnularGridIndex (m + 1) → NNReal)
    (hFac : ∀ k : AnnularGridIndex (m + 1) → ℕ,
      Tendsto
        (fun n ↦ mixedFactorialMoment
          (markedResonanceCountVectorLaw (Ns n) (Ns n)
            (annularGridCell ε A (m + 1))
            (fun i ↦ measurableSet_annularGridCell ε A (m + 1) i)) k)
        atTop (𝓝 (∏ i, (r i : ℝ) ^ (k i))))
    (i : AnnularGridIndex (m + 1)) :
    Tendsto
      (fun n ↦ ∫ α,
        (markedResonanceCount (Ns n) (Ns n)
          (annularGridCell ε A (m + 1) i) α : ℝ)
          ∂uniform01Measure)
      atTop (𝓝 (r i : ℝ)) := by
  simpa only [mixedFactorialMoment_markedResonanceCountVectorLaw,
    mixedDescFactorial_singletonFactorialOrder,
    markedResonanceCountVector,
    prod_pow_singletonFactorialOrder] using!
      hFac (singletonFactorialOrder i)

/-- Tightness of the total annular point count is not an extra hypothesis:
it follows already from the order-one part of the mixed factorial limits on
the coarsest explicit grid. -/
theorem annularMarkedCount_tight_of_gridFactorialMoments
    (Ns : ℕ → ℕ) {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (r : AnnularGridIndex 1 → NNReal)
    (hFac : ∀ k : AnnularGridIndex 1 → ℕ,
      Tendsto
        (fun n ↦ mixedFactorialMoment
          (markedResonanceCountVectorLaw (Ns n) (Ns n)
            (annularGridCell ε A 1)
            (fun i ↦ measurableSet_annularGridCell ε A 1 i)) k)
        atTop (𝓝 (∏ i, (r i : ℝ) ^ (k i)))) :
    ∀ δ > 0, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      uniform01Measure.real
        {α | K < markedResonanceCount (Ns n) (Ns n)
          (compactAnnularMarkedRegion ε A) α} < δ := by
  apply markedResonanceCount_partition_tight
    Ns Ns (measurableSet_compactAnnularMarkedRegion ε A)
    (annularGridCell ε A 1)
    (fun i ↦ measurableSet_annularGridCell ε A 1 i)
    (annularGridCell_subset_compactAnnularMarkedRegion hεA (by norm_num))
    (fun z hz ↦ existsUnique_mem_annularGridCell hε hεA (by norm_num) hz)
    (fun i ↦ (r i : ℝ))
  · intro i
    positivity
  · intro i
    simpa using!
      tendsto_integral_annularGridCell_count_of_mixedFactorialMoments
        0 Ns ε A r hFac i

/-- At every prescribed one-point kernel tolerance, all sufficiently fine
explicit grids satisfy the deterministic error estimate simultaneously for
every sample size `N ≥ 2` and every sample point. -/
theorem eventually_annularGridShotApproximation_error_le_count
    {ε A η : ℝ} (hε : 0 < ε) (hεA : ε < A) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ N : ℕ, 2 ≤ N → ∀ α : ℝ,
      |annularMarkedShotFunctional N ε A α -
          annularGridShotApproximation m N ε A α| ≤
        η * (markedResonanceCount N N
          (compactAnnularMarkedRegion ε A) α : ℝ) := by
  obtain ⟨δ, hδ, hkernel⟩ :=
    exists_uniform_cell_radius_markedShotKernel hε hη
  have htime : ∀ᶠ m : ℕ in atTop,
      (1 : ℝ) / ((m + 1 : ℕ) : ℝ) < δ := by
    simpa only [Nat.cast_add, Nat.cast_one] using!
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const hδ
  have hsigned : ∀ᶠ m : ℕ in atTop,
      (A - ε) / ((m + 1 : ℕ) : ℝ) < δ := by
    have ht : Tendsto
        (fun m : ℕ ↦ (A - ε) / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using!
        (tendsto_const_div_atTop_nhds_zero_nat (A - ε)).comp
          (tendsto_add_atTop_nat 1)
    exact ht.eventually_lt_const hδ
  filter_upwards [htime, hsigned] with m htm hsm
  intro N hN α
  unfold annularGridShotApproximation
  apply abs_annularMarkedShotFunctional_sub_finiteCellApproximation_le_count
    hN hε.le (annularGridCell ε A (m + 1))
      (fun i ↦ markedShotKernel (annularGridCenter ε A (m + 1) i))
    (annularGridCell_subset_compactAnnularMarkedRegion hεA (by omega))
    (fun z hz ↦ existsUnique_mem_annularGridCell hε hεA (by omega) hz)
  intro i z hz
  exact (hkernel z
    (annularGridCell_subset_compactAnnularMarkedRegion hεA (by omega) i hz)
    (annularGridCenter ε A (m + 1) i)
    (annularGridCenter_mem_compactAnnularMarkedRegion hεA (by omega) i)
    (dist_annularGridCenter_lt hεA (by omega) htm hsm i hz)).le

/-- Uniform tightness of the actual retained point count converts the
preceding deterministic estimate into the exact nested probability bound
used by the converging-together theorem. -/
theorem twoParameter_close_annularGridShotApproximation
    (Ns : ℕ → ℕ) {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (hNs : ∀ᶠ n : ℕ in atTop, 2 ≤ Ns n)
    (hCountTight : ∀ δ > 0, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      uniform01Measure.real
        {α | K < markedResonanceCount (Ns n) (Ns n)
          (compactAnnularMarkedRegion ε A) α} < δ) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ m : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
        uniform01Measure.real
          {α | r ≤ ‖annularMarkedShotFunctional (Ns n) ε A α -
            annularGridShotApproximation m (Ns n) ε A α‖} < δ := by
  intro r hr δ hδ
  obtain ⟨K, hK⟩ := hCountTight δ hδ
  let η : ℝ := r / ((K : ℝ) + 1)
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hm := eventually_annularGridShotApproximation_error_le_count
    hε hεA hη
  filter_upwards [hm] with m hm
  filter_upwards [hNs, hK] with n hN hcount
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans_lt hcount
  intro α hbad
  by_contra hnotLarge
  have hCle : markedResonanceCount (Ns n) (Ns n)
      (compactAnnularMarkedRegion ε A) α ≤ K := Nat.le_of_not_gt hnotLarge
  have herr := hm (Ns n) hN α
  have hηnonneg : 0 ≤ η := hη.le
  have hηC :
      η * (markedResonanceCount (Ns n) (Ns n)
        (compactAnnularMarkedRegion ε A) α : ℝ) ≤ η * (K : ℝ) := by
    apply mul_le_mul_of_nonneg_left
    · exact_mod_cast hCle
    · exact hηnonneg
  have hηK : η * (K : ℝ) < r := by
    dsimp [η]
    have hden : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    calc
      r / ((K : ℝ) + 1) * (K : ℝ)
          < r / ((K : ℝ) + 1) * ((K : ℝ) + 1) := by
            apply mul_lt_mul_of_pos_left (by linarith) (div_pos hr hden)
      _ = r := by field_simp
  have herrlt :
      |annularMarkedShotFunctional (Ns n) ε A α -
          annularGridShotApproximation m (Ns n) ε A α| < r :=
    herr.trans_lt (hηC.trans_lt hηK)
  simp only [Real.norm_eq_abs] at hbad
  exact (not_lt_of_ge hbad) herrlt

/-- Fully assembled explicit-grid criterion.  The only remaining inputs are
the substantive arithmetic statements: mixed factorial limits for every
fixed grid, tightness of the retained count, and convergence of the resulting
finite independent-Poisson grid laws as the mesh vanishes. -/
theorem tendsto_annularMarkedShotLaw_of_gridFactorialMoments
    (Ns : ℕ → ℕ) {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (hNs : ∀ᶠ n : ℕ in atTop, 2 ≤ Ns n)
    (r : ∀ m : ℕ, AnnularGridIndex (m + 1) → NNReal)
    (hFac : ∀ m (k : AnnularGridIndex (m + 1) → ℕ),
      Tendsto
        (fun n ↦ mixedFactorialMoment
          (markedResonanceCountVectorLaw (Ns n) (Ns n)
            (annularGridCell ε A (m + 1))
            (fun i ↦ measurableSet_annularGridCell ε A (m + 1) i)) k)
        atTop (𝓝 (∏ i, (r m i : ℝ) ^ (k i))))
    (ν : ProbabilityMeasure ℝ)
    (hGridLimit : Tendsto
      (fun m ↦ weightedIndependentPoissonLaw (r m)
        (fun i ↦ markedShotKernel (annularGridCenter ε A (m + 1) i)))
      atTop (𝓝 ν)) :
    Tendsto (fun n ↦ annularMarkedShotLaw (Ns n) ε A)
      atTop (𝓝 ν) := by
  let XA : ℕ → ℕ → ℝ → ℝ :=
    fun m n ↦ annularGridShotApproximation m (Ns n) ε A
  let X : ℕ → ℝ → ℝ :=
    fun n ↦ annularMarkedShotFunctional (Ns n) ε A
  let νm : ℕ → ProbabilityMeasure ℝ := fun m ↦
    weightedIndependentPoissonLaw (r m)
      (fun i ↦ markedShotKernel (annularGridCenter ε A (m + 1) i))
  have hfixed : ∀ m,
      Tendsto
        (fun n ↦ (⟨uniform01Measure.map (XA m n),
          Measure.isProbabilityMeasure_map
            (measurable_annularGridShotApproximation
              m (Ns n) ε A).aemeasurable⟩ : ProbabilityMeasure ℝ))
        atTop
          (@nhds (ProbabilityMeasure ℝ)
            probabilityMeasureWeakTopologyASC (νm m)) := by
    intro m
    simpa only [XA, νm, annularGridShotLaw] using!
      tendsto_annularGridShotLaw_of_mixedFactorialMoments
        m Ns ε A (r m) (hFac m)
  have hCountTight : ∀ δ > 0, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      uniform01Measure.real
        {α | K < markedResonanceCount (Ns n) (Ns n)
          (compactAnnularMarkedRegion ε A) α} < δ := by
    apply annularMarkedCount_tight_of_gridFactorialMoments
      Ns hε hεA (r 0)
    simpa using! hFac 0
  have hclose : ∀ rr > 0, ∀ δ > 0,
      ∀ᶠ m : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
        uniform01Measure.real
          {α | rr ≤ ‖X n α - XA m n α‖} < δ := by
    simpa only [X, XA] using!
      twoParameter_close_annularGridShotApproximation
        Ns hε hεA hNs hCountTight
  have hmain := tendsto_map_of_convergingTogether
    (μ := uniform01Measure) X XA νm ν
    (fun n ↦ (measurable_annularMarkedShotFunctional (Ns n) ε A).aemeasurable)
    (fun m n ↦ (measurable_annularGridShotApproximation
      m (Ns n) ε A).aemeasurable)
    hfixed hGridLimit hclose
  simpa only [annularMarkedShotLaw, X] using! hmain

end

end Erdos1002
