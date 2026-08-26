import ErdosProblems.Erdos1002.AnnularCompoundPoisson
import ErdosProblems.Erdos1002.AnnularShotConvergence
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# From explicit annular grids to the continuum compound-Poisson law

This file identifies the formerly abstract mesh limit in
`AnnularShotConvergence`.  Each explicit cell is assigned its actual limiting
intensity, namely its mass under the product Lebesgue intensity divided by
`ζ(2) = π² / 6`.  The characteristic exponent of the resulting finite
independent-Poisson sum is a tagged integral over the grid.  Uniform
continuity of the marked-shot exponent on the compact annulus then proves
that these tagged integrals converge to the continuum exponent constructed
in `AnnularCompoundPoisson`.

The final theorem therefore consumes only mixed factorial-moment convergence
of the *actual* marked cell counts.  There is no separately assumed limiting
probability law and no separately assumed mesh-limit statement.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos1002

noncomputable section

/-! ## The genuine annular intensity and its grid cells -/

/-- Product Lebesgue measure in logarithmic time, signed resonance
coordinate, and torus mark.  It has total mass `2(A-ε)`; the factor
`1 / (π²/6)` is inserted only when defining Poisson rates. -/
def annularRawStateMeasure (ε A : ℝ) : Measure (ℝ × ℝ × ℝ) :=
  uniform01Measure.prod
    ((signedAnnulusFiniteMeasure ε A : Measure ℝ).prod uniform01Measure)

instance annularRawStateMeasure_isFinite (ε A : ℝ) :
    IsFiniteMeasure (annularRawStateMeasure ε A) := by
  unfold annularRawStateMeasure
  infer_instance

/-- The exponent integrand on the full three-coordinate marked state.  It is
independent of logarithmic time, exactly as in the manuscript. -/
def annularStateExponentIntegrand (t : ℝ) (z : ℝ × ℝ × ℝ) : ℂ :=
  signedAnnularExponentIntegrand t (z.2.1, z.2.2)

theorem measurable_annularStateExponentIntegrand (t : ℝ) :
    Measurable (annularStateExponentIntegrand t) := by
  exact (measurable_signedAnnularExponentIntegrand t).comp
    (measurable_fst.comp measurable_snd |>.prodMk
      (measurable_snd.comp measurable_snd))

theorem integrable_annularStateExponentIntegrand
    (ε A t : ℝ) :
    Integrable (annularStateExponentIntegrand t)
      (annularRawStateMeasure ε A) := by
  have hraw := integrable_signedAnnularExponentIntegrand_raw ε A t
  simpa only [annularRawStateMeasure, annularStateExponentIntegrand,
    Prod.snd] using! hraw.comp_snd uniform01Measure

/-- The full-state integral is exactly the two-coordinate raw integral used
in the definition of `signedAnnularPoissonExponent`. -/
theorem integral_annularStateExponentIntegrand
    (ε A t : ℝ) :
    (∫ z, annularStateExponentIntegrand t z
        ∂annularRawStateMeasure ε A) =
      ∫ xu, signedAnnularExponentIntegrand t xu
        ∂((signedAnnulusFiniteMeasure ε A : Measure ℝ).prod
          uniform01Measure) := by
  have hInt := integrable_annularStateExponentIntegrand ε A t
  rw [annularRawStateMeasure, integral_prod _ hInt]
  simp only [annularStateExponentIntegrand]
  rw [integral_const]
  simp

/-- Every point in the compact annulus lies in exactly one grid cell, hence
the finite union of all cells is the annulus itself. -/
theorem iUnion_annularGridCell_eq_compactAnnularMarkedRegion
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A) {n : ℕ} (hn : 0 < n) :
    (⋃ i : AnnularGridIndex n, annularGridCell ε A n i) =
      compactAnnularMarkedRegion ε A := by
  apply Set.Subset.antisymm
  · rw [iUnion_subset_iff]
    exact annularGridCell_subset_compactAnnularMarkedRegion hεA hn
  · intro z hz
    obtain ⟨i, hi, _hiUnique⟩ :=
      existsUnique_mem_annularGridCell hε hεA hn hz
    exact mem_iUnion.mpr ⟨i, hi⟩

/-- Distinct explicit cells are literally disjoint, not merely disjoint up
to null boundaries. -/
theorem pairwise_disjoint_annularGridCell
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A) {n : ℕ} (hn : 0 < n) :
    Pairwise (fun i j ↦
      Disjoint (annularGridCell ε A n i) (annularGridCell ε A n j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro z hzi hzj
  have hzK := annularGridCell_subset_compactAnnularMarkedRegion hεA hn i hzi
  obtain ⟨k, hk, hkUnique⟩ :=
    existsUnique_mem_annularGridCell hε hεA hn hzK
  have hi : i = k := hkUnique i hzi
  have hj : j = k := hkUnique j hzj
  exact hij (hi.trans hj.symm)

/-- The raw state measure is concentrated on the compact closed annulus.
This explicitly accounts for the open/closed endpoint convention: the raw
measure uses open intervals, all of which lie in the corresponding closed
grid region. -/
theorem ae_annularRawStateMeasure_mem_compactAnnularMarkedRegion
    (ε A : ℝ) :
    ∀ᵐ z ∂annularRawStateMeasure ε A,
      z ∈ compactAnnularMarkedRegion ε A := by
  rw [annularRawStateMeasure,
    Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_compactAnnularMarkedRegion ε A)]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hinner :
      ∀ᵐ xu ∂(signedAnnulusFiniteMeasure ε A : Measure ℝ).prod
          uniform01Measure,
        xu ∈ (Icc (-A) (-ε) ∪ Icc ε A) ×ˢ Icc (0 : ℝ) 1 := by
    rw [Measure.ae_prod_mem_iff_ae_ae_mem
      ((measurableSet_Icc.union measurableSet_Icc).prod measurableSet_Icc)]
    filter_upwards
      [ae_restrict_mem (measurableSet_signedAnnulusSet ε A)] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    refine ⟨?_, ⟨hu.1.le, hu.2.le⟩⟩
    rcases hx with hx | hx
    · exact Or.inl ⟨hx.1.le, hx.2.le⟩
    · exact Or.inr ⟨hx.1.le, hx.2.le⟩
  filter_upwards [hinner] with xu hxu
  exact ⟨⟨hs.1.le, hs.2.le⟩, hxu⟩

theorem restrict_compactAnnularMarkedRegion_annularRawStateMeasure
    (ε A : ℝ) :
    (annularRawStateMeasure ε A).restrict
        (compactAnnularMarkedRegion ε A) =
      annularRawStateMeasure ε A :=
  Measure.restrict_eq_self_of_ae_mem
    (ae_annularRawStateMeasure_mem_compactAnnularMarkedRegion ε A)

/-- Limiting Poisson rate of one actual explicit grid cell. -/
def annularGridCellPoissonRate
    (ε A : ℝ) (n : ℕ) (i : AnnularGridIndex n) : NNReal :=
  ⟨(annularRawStateMeasure ε A).real (annularGridCell ε A n i) /
      (Real.pi ^ 2 / 6), by positivity⟩

@[simp]
theorem coe_annularGridCellPoissonRate
    (ε A : ℝ) (n : ℕ) (i : AnnularGridIndex n) :
    (annularGridCellPoissonRate ε A n i : ℝ) =
      (annularRawStateMeasure ε A).real (annularGridCell ε A n i) /
        (Real.pi ^ 2 / 6) :=
  rfl

/-! ## Tagged characteristic exponents -/

theorem annularStateExponentIntegrand_eq_marked
    (t : ℝ) :
    annularStateExponentIntegrand t = fun z : ℝ × ℝ × ℝ ↦
      Complex.exp ((t : ℂ) * markedShotKernel z * Complex.I) - 1 := by
  funext z
  rfl

theorem continuousOn_annularStateExponentIntegrand
    {ε A : ℝ} (hε : 0 < ε) (t : ℝ) :
    ContinuousOn (annularStateExponentIntegrand t)
      (compactAnnularMarkedRegion ε A) := by
  rw [annularStateExponentIntegrand_eq_marked]
  intro z hz
  have hxann : z.2.1 ∈ Icc (-A) (-ε) ∪ Icc ε A := hz.2.1
  rw [mem_signedAnnulus_iff_abs hε.le] at hxann
  have hx0 : z.2.1 ≠ 0 := fun hx ↦ by
    simpa [hx] using! hε.trans_le hxann.1
  have hk : ContinuousAt markedShotKernel z :=
    continuousAt_markedShotKernel hx0
  have hkc : ContinuousAt (fun y ↦ (markedShotKernel y : ℂ)) z :=
    by
      simpa only [Function.comp_apply] using!
        Complex.continuous_ofReal.continuousAt.comp hk
  exact (((continuous_const.continuousAt.mul hkc).mul
    continuous_const.continuousAt).cexp.sub
      continuous_const.continuousAt).continuousWithinAt

theorem uniformContinuousOn_annularStateExponentIntegrand
    {ε A : ℝ} (hε : 0 < ε) (t : ℝ) :
    UniformContinuousOn (annularStateExponentIntegrand t)
      (compactAnnularMarkedRegion ε A) :=
  (isCompact_compactAnnularMarkedRegion ε A).uniformContinuousOn_of_continuous
    (continuousOn_annularStateExponentIntegrand hε t)

/-- The unscaled tagged exponent integral on the explicit level-`n` grid. -/
def annularGridTaggedExponent
    (ε A : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ∑ i : AnnularGridIndex n,
    (annularRawStateMeasure ε A).real (annularGridCell ε A n i) •
      annularStateExponentIntegrand t (annularGridCenter ε A n i)

theorem integral_annularStateExponentIntegrand_eq_sum_cells
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {n : ℕ} (hn : 0 < n) (t : ℝ) :
    (∫ z, annularStateExponentIntegrand t z
        ∂annularRawStateMeasure ε A) =
      ∑ i : AnnularGridIndex n,
        ∫ z in annularGridCell ε A n i,
          annularStateExponentIntegrand t z
            ∂annularRawStateMeasure ε A := by
  have hInt := integrable_annularStateExponentIntegrand ε A t
  calc
    (∫ z, annularStateExponentIntegrand t z
        ∂annularRawStateMeasure ε A) =
        ∫ z in compactAnnularMarkedRegion ε A,
          annularStateExponentIntegrand t z
            ∂annularRawStateMeasure ε A := by
      rw [restrict_compactAnnularMarkedRegion_annularRawStateMeasure ε A]
    _ = ∫ z in ⋃ i : AnnularGridIndex n, annularGridCell ε A n i,
          annularStateExponentIntegrand t z
            ∂annularRawStateMeasure ε A := by
      rw [iUnion_annularGridCell_eq_compactAnnularMarkedRegion hε hεA hn]
    _ = _ := integral_iUnion_fintype
      (fun i ↦ measurableSet_annularGridCell ε A n i)
      (pairwise_disjoint_annularGridCell hε hεA hn)
      (fun _i ↦ hInt.integrableOn)

theorem sum_measureReal_annularGridCell
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {n : ℕ} (hn : 0 < n) :
    (∑ i : AnnularGridIndex n,
      (annularRawStateMeasure ε A).real (annularGridCell ε A n i)) =
        (annularRawStateMeasure ε A).real
          (compactAnnularMarkedRegion ε A) := by
  have h := integral_iUnion_fintype
    (μ := annularRawStateMeasure ε A) (f := fun _ : ℝ × ℝ × ℝ ↦ (1 : ℝ))
    (fun i : AnnularGridIndex n ↦ measurableSet_annularGridCell ε A n i)
    (pairwise_disjoint_annularGridCell hε hεA hn)
    (fun _i ↦ integrableOn_const)
  rw [iUnion_annularGridCell_eq_compactAnnularMarkedRegion hε hεA hn] at h
  simpa only [setIntegral_const, smul_eq_mul, mul_one] using! h.symm

/-- Quantitative tagged-integral estimate.  Every cellwise oscillation at
most `η` gives total error at most `η` times the raw annular mass. -/
theorem norm_annularGridTaggedExponent_sub_integral_le
    {ε A η : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {n : ℕ} (hn : 0 < n) (t : ℝ)
    (hclose : ∀ (i : AnnularGridIndex n) z,
      z ∈ annularGridCell ε A n i →
        ‖annularStateExponentIntegrand t
            (annularGridCenter ε A n i) -
          annularStateExponentIntegrand t z‖ ≤ η) :
    ‖annularGridTaggedExponent ε A n t -
        ∫ z, annularStateExponentIntegrand t z
          ∂annularRawStateMeasure ε A‖ ≤
      η * (annularRawStateMeasure ε A).real
        (compactAnnularMarkedRegion ε A) := by
  classical
  rw [integral_annularStateExponentIntegrand_eq_sum_cells hε hεA hn]
  unfold annularGridTaggedExponent
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ i : AnnularGridIndex n,
        ((annularRawStateMeasure ε A).real (annularGridCell ε A n i) •
            annularStateExponentIntegrand t (annularGridCenter ε A n i) -
          ∫ z in annularGridCell ε A n i,
            annularStateExponentIntegrand t z
              ∂annularRawStateMeasure ε A)‖
        ≤ ∑ i : AnnularGridIndex n,
          ‖(annularRawStateMeasure ε A).real (annularGridCell ε A n i) •
              annularStateExponentIntegrand t (annularGridCenter ε A n i) -
            ∫ z in annularGridCell ε A n i,
              annularStateExponentIntegrand t z
                ∂annularRawStateMeasure ε A‖ := norm_sum_le _ _
    _ ≤ ∑ i : AnnularGridIndex n,
          η * (annularRawStateMeasure ε A).real
            (annularGridCell ε A n i) := by
      apply Finset.sum_le_sum
      intro i _hi
      have hcellInt : IntegrableOn (annularStateExponentIntegrand t)
          (annularGridCell ε A n i) (annularRawStateMeasure ε A) :=
        (integrable_annularStateExponentIntegrand ε A t).integrableOn
      have heq :
          (annularRawStateMeasure ε A).real (annularGridCell ε A n i) •
                annularStateExponentIntegrand t (annularGridCenter ε A n i) -
              ∫ z in annularGridCell ε A n i,
                annularStateExponentIntegrand t z
                  ∂annularRawStateMeasure ε A =
            ∫ z in annularGridCell ε A n i,
              (annularStateExponentIntegrand t
                  (annularGridCenter ε A n i) -
                annularStateExponentIntegrand t z)
                ∂annularRawStateMeasure ε A := by
        rw [integral_sub
          (μ := (annularRawStateMeasure ε A).restrict
            (annularGridCell ε A n i))
          (integrableOn_const
            (s := annularGridCell ε A n i)
            (μ := annularRawStateMeasure ε A)
            (C := annularStateExponentIntegrand t
              (annularGridCenter ε A n i)))
          hcellInt, setIntegral_const]
      rw [heq]
      exact norm_setIntegral_le_of_norm_le_const
        (measure_lt_top _ _) (hclose i)
    _ = η * (annularRawStateMeasure ε A).real
          (compactAnnularMarkedRegion ε A) := by
      rw [← Finset.mul_sum, sum_measureReal_annularGridCell hε hεA hn]

/-- As the explicit mesh tends to zero, the tagged exponent integral
converges to the genuine raw state integral. -/
theorem tendsto_annularGridTaggedExponent
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A) (t : ℝ) :
    Tendsto
      (fun m : ℕ ↦ annularGridTaggedExponent ε A (m + 1) t)
      atTop
      (𝓝 (∫ z, annularStateExponentIntegrand t z
        ∂annularRawStateMeasure ε A)) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  let M : ℝ := (annularRawStateMeasure ε A).real
    (compactAnnularMarkedRegion ε A)
  have hM : 0 ≤ M := measureReal_nonneg
  let q : ℝ := η / (M + 1)
  have hq : 0 < q := by
    dsimp [q]
    positivity
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (uniformContinuousOn_annularStateExponentIntegrand hε t) q hq
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
  apply eventually_atTop.1
  filter_upwards [htime, hsigned] with m htm hsm
  have herr := norm_annularGridTaggedExponent_sub_integral_le
    hε hεA (show 0 < m + 1 by omega) t (η := q) (by
      intro i z hz
      have hcenter := annularGridCenter_mem_compactAnnularMarkedRegion
        hεA (show 0 < m + 1 by omega) i
      have hzK := annularGridCell_subset_compactAnnularMarkedRegion
        hεA (show 0 < m + 1 by omega) i hz
      have hdist :
          dist (annularGridCenter ε A (m + 1) i) z < δ := by
        simpa only [dist_comm] using!
          dist_annularGridCenter_lt hεA (show 0 < m + 1 by omega)
            htm hsm i hz
      simpa only [dist_eq_norm] using! (hclose _ hcenter _ hzK hdist).le)
  have hqM : q * M < η := by
    calc
      q * M < q * (M + 1) := by
        exact mul_lt_mul_of_pos_left (by linarith) hq
      _ = η := by
        dsimp [q]
        field_simp
  rw [dist_eq_norm]
  exact herr.trans_lt (by simpa only [M] using! hqM)

/-- The characteristic exponent of the finite independent-Poisson grid
shot. -/
def annularGridIndependentPoissonExponent
    (ε A : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ∑ i : AnnularGridIndex n,
    (annularGridCellPoissonRate ε A n i : ℂ) *
      (Complex.exp
        (t * markedShotKernel (annularGridCenter ε A n i) * Complex.I) - 1)

theorem annularGridIndependentPoissonExponent_eq_tagged
    (ε A : ℝ) (n : ℕ) (t : ℝ) :
    annularGridIndependentPoissonExponent ε A n t =
      (1 / (Real.pi ^ 2 / 6) : ℝ) •
        annularGridTaggedExponent ε A n t := by
  classical
  unfold annularGridIndependentPoissonExponent annularGridTaggedExponent
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [smul_smul]
  simp only [annularStateExponentIntegrand_eq_marked,
    coe_annularGridCellPoissonRate, Complex.real_smul]
  push_cast
  ring

theorem signedAnnularPoissonExponent_eq_stateIntegral
    (ε A t : ℝ) :
    signedAnnularPoissonExponent ε A t =
      (1 / (Real.pi ^ 2 / 6) : ℝ) •
        (∫ z, annularStateExponentIntegrand t z
          ∂annularRawStateMeasure ε A) := by
  unfold signedAnnularPoissonExponent
  rw [integral_annularStateExponentIntegrand]

theorem tendsto_annularGridIndependentPoissonExponent
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A) (t : ℝ) :
    Tendsto
      (fun m : ℕ ↦
        annularGridIndependentPoissonExponent ε A (m + 1) t)
      atTop (𝓝 (signedAnnularPoissonExponent ε A t)) := by
  rw [signedAnnularPoissonExponent_eq_stateIntegral]
  have h := (tendsto_annularGridTaggedExponent hε hεA t).const_smul
    (1 / (Real.pi ^ 2 / 6) : ℝ)
  simpa only [annularGridIndependentPoissonExponent_eq_tagged] using! h

/-- The finite independent-Poisson grid laws converge to the explicitly
constructed continuum annular compound-Poisson law. -/
theorem tendsto_weightedIndependentPoissonLaw_annularGrid
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A) :
    Tendsto
      (fun m : ℕ ↦ weightedIndependentPoissonLaw
        (annularGridCellPoissonRate ε A (m + 1))
        (fun i ↦ markedShotKernel (annularGridCenter ε A (m + 1) i)))
      atTop (𝓝 (annularCompoundPoissonProbability ε A)) := by
  apply levy_continuity_real
  intro t
  rw [charFun_annularCompoundPoissonProbability hε.le hεA]
  have hExp : Tendsto
      (fun m : ℕ ↦ Complex.exp
        (annularGridIndependentPoissonExponent ε A (m + 1) t))
      atTop
      (𝓝 (Complex.exp (signedAnnularPoissonExponent ε A t))) :=
    Complex.continuous_exp.continuousAt.tendsto.comp
      (tendsto_annularGridIndependentPoissonExponent hε hεA t)
  apply hExp.congr'
  filter_upwards with m
  rw [charFun_weightedIndependentPoissonLaw]
  congr 1

/-! ## Direct mixed-factorial criterion -/

/-- The raw limiting intensity is absolutely continuous with respect to
three-dimensional Lebesgue measure. -/
theorem annularRawStateMeasure_absolutelyContinuous_volume
    (ε A : ℝ) :
    annularRawStateMeasure ε A ≪ volume := by
  unfold annularRawStateMeasure uniform01Measure
  rw [signedAnnulusFiniteMeasure_toMeasure]
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
  exact Measure.restrict_le_self.absolutelyContinuous.prod
    (Measure.restrict_le_self.absolutelyContinuous.prod
      Measure.restrict_le_self.absolutelyContinuous)

/-- Consequently every actual half-open grid cell is a continuity set for
the genuine limiting intensity.  In particular all endpoint and terminal
singleton conventions have zero limiting mass. -/
theorem annularRawStateMeasure_frontier_annularGridCell_eq_zero
    {ε A : ℝ} (hεA : ε < A) {n : ℕ} (hn : 0 < n)
    (i : AnnularGridIndex n) :
    annularRawStateMeasure ε A
      (frontier (annularGridCell ε A n i)) = 0 :=
  measure_frontier_annularGridCell_eq_zero_of_absolutelyContinuous
    hεA hn i (annularRawStateMeasure ε A)
      (annularRawStateMeasure_absolutelyContinuous_volume ε A)

/-- Fully explicit fixed-annulus Poisson convergence criterion.  The sole
substantive input is convergence of every joint falling-factorial moment of
the actual marked counts in every fixed explicit grid cell. -/
theorem tendsto_annularMarkedShotLaw_compoundPoisson_of_gridFactorialMoments
    (Ns : ℕ → ℕ) {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (hNs : ∀ᶠ n : ℕ in atTop, 2 ≤ Ns n)
    (hFac : ∀ m (k : AnnularGridIndex (m + 1) → ℕ),
      Tendsto
        (fun n ↦ MultivariateFactorialMomentMethod.mixedFactorialMoment
          (markedResonanceCountVectorLaw (Ns n) (Ns n)
            (annularGridCell ε A (m + 1))
            (fun i ↦ measurableSet_annularGridCell ε A (m + 1) i)) k)
        atTop
        (𝓝 (∏ i,
          (annularGridCellPoissonRate ε A (m + 1) i : ℝ) ^ (k i)))) :
    Tendsto
      (fun n ↦ annularMarkedShotLaw (Ns n) ε A)
      atTop (𝓝 (annularCompoundPoissonProbability ε A)) := by
  exact tendsto_annularMarkedShotLaw_of_gridFactorialMoments
    Ns hε hεA hNs
    (fun m ↦ annularGridCellPoissonRate ε A (m + 1))
    hFac (annularCompoundPoissonProbability ε A)
    (tendsto_weightedIndependentPoissonLaw_annularGrid hε hεA)

end

end Erdos1002
