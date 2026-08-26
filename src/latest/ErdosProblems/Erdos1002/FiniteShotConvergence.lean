import ErdosProblems.Erdos1002.CountVectorMapping
import ErdosProblems.Erdos1002.SmallCoordinateTruncation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite-cell approximations to the marked shot functional

This file isolates the deterministic and continuous-mapping part of the
finite-shot limit.  On a compact annulus the marked shot kernel is uniformly
continuous.  A finite measurable partition may therefore be replaced by its
cell representatives, with a pointwise error bounded by the mesh error times
the number of retained marked points.  The resulting random variable is
literally the weighted count-vector functional whose weak limit was proved in
`CountVectorMapping`.

No point-process convention is hidden here: every identity is an identity of
finite sums over denominators.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

open MultivariateFactorialMomentMethod

local instance finiteShotConvergencePropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! ## The compact annular state space -/

/-- The compact state-space region used for a fixed annular cutoff.  The
torus coordinate is represented by `[0,1]`; using the closed interval is
harmless because actual representatives lie in `[0,1)`. -/
def compactAnnularMarkedRegion (ε A : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Icc (0 : ℝ) 1 ×ˢ
    ((Icc (-A) (-ε) ∪ Icc ε A) ×ˢ Icc (0 : ℝ) 1)

theorem isCompact_compactAnnularMarkedRegion (ε A : ℝ) :
    IsCompact (compactAnnularMarkedRegion ε A) := by
  exact isCompact_Icc.prod
    ((isCompact_Icc.union isCompact_Icc).prod isCompact_Icc)

theorem measurableSet_compactAnnularMarkedRegion (ε A : ℝ) :
    MeasurableSet (compactAnnularMarkedRegion ε A) :=
  (isCompact_compactAnnularMarkedRegion ε A).isClosed.measurableSet

/-- Membership in the two signed `x`-intervals is exactly the absolute-value
annulus, provided the inner radius is nonnegative. -/
theorem mem_signedAnnulus_iff_abs
    {ε A x : ℝ} (hε : 0 ≤ ε) :
    x ∈ Icc (-A) (-ε) ∪ Icc ε A ↔ ε ≤ |x| ∧ |x| ≤ A := by
  by_cases hx : x < 0
  · rw [abs_of_neg hx]
    constructor
    · rintro (hleft | hright)
      · exact ⟨by linarith [hleft.2], by linarith [hleft.1]⟩
      · linarith [hright.1]
    · rintro ⟨hlow, hupp⟩
      left
      exact ⟨by linarith, by linarith⟩
  · have hx0 : 0 ≤ x := le_of_not_gt hx
    rw [abs_of_nonneg hx0]
    constructor
    · rintro (hleft | hright)
      · have hxle : x ≤ 0 := le_trans hleft.2 (neg_nonpos.mpr hε)
        have hxzero : x = 0 := le_antisymm hxle hx0
        subst x
        exact ⟨by linarith [hleft.2], by linarith [hleft.1]⟩
      · exact hright
    · intro h
      exact Or.inr h

/-- A retained denominator has logarithmic time in `[0,1]`. -/
theorem resonanceTimeCoordinate_mem_Icc
    {N p : ℕ} (hN : 2 ≤ N) (hp : p ∈ Finset.Icc 1 N) :
    resonanceTimeCoordinate N p ∈ Icc (0 : ℝ) 1 := by
  have hp' : 1 ≤ p ∧ p ≤ N := Finset.mem_Icc.mp hp
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp'.1
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le zero_lt_one hp1
  have hpN : (p : ℝ) ≤ (N : ℝ) := by exact_mod_cast hp'.2
  have hlogp0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  have hlogpN : Real.log (p : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hp0 hpN
  constructor
  · exact div_nonneg hlogp0 hlogN.le
  · exact (div_le_one hlogN).2 hlogpN

/-- For `p ≤ N`, the absolute-value cutoff in the annular shot functional
is exactly membership of the marked point in the compact annular region. -/
theorem markedResonancePoint_mem_compactAnnularMarkedRegion_iff
    {N p : ℕ} (hN : 2 ≤ N) (hp : p ∈ Finset.Icc 1 N)
    {ε A : ℝ} (hε : 0 ≤ ε) (α : ℝ) :
    markedResonancePoint N p α ∈ compactAnnularMarkedRegion ε A ↔
      ε ≤ |scaledResonanceCoordinate N p α| ∧
        |scaledResonanceCoordinate N p α| ≤ A := by
  rw [compactAnnularMarkedRegion, mem_prod, mem_prod]
  simp only [markedResonancePoint]
  refine and_iff_right (resonanceTimeCoordinate_mem_Icc hN hp) |>.trans ?_
  rw [mem_signedAnnulus_iff_abs hε]
  exact and_iff_left
    ⟨(resonanceTorusCoordinate_mem_Ico N p α).1,
      (resonanceTorusCoordinate_mem_Ico N p α).2.le⟩

/-- On a compact annulus with positive inner radius the marked shot kernel is
uniformly continuous.  This is the precise Heine--Cantor input used by finite
cell approximations. -/
theorem uniformContinuousOn_markedShotKernel_compactAnnular
    {ε A : ℝ} (hε : 0 < ε) :
    UniformContinuousOn markedShotKernel (compactAnnularMarkedRegion ε A) := by
  apply (isCompact_compactAnnularMarkedRegion ε A).uniformContinuousOn_of_continuous
  intro z hz
  apply (continuousAt_markedShotKernel ?_).continuousWithinAt
  have hxann : z.2.1 ∈ Icc (-A) (-ε) ∪ Icc ε A := hz.2.1
  rw [mem_signedAnnulus_iff_abs hε.le] at hxann
  exact fun hx0 ↦ by simpa [hx0] using! hε.trans_le hxann.1

/-- Metric epsilon-delta form of uniform continuity on the compact annulus. -/
theorem exists_uniform_cell_radius_markedShotKernel
    {ε A η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, ∀ z ∈ compactAnnularMarkedRegion ε A,
      ∀ z' ∈ compactAnnularMarkedRegion ε A,
        dist z z' < δ →
          |markedShotKernel z - markedShotKernel z'| < η := by
  exact Metric.uniformContinuousOn_iff.mp
    (uniformContinuousOn_markedShotKernel_compactAnnular hε) η hη

/-! ## Exact finite sums and finite-cell approximations -/

/-- The literal marked-kernel sum over a measurable region. -/
def markedKernelSum (N P : ℕ) (K : Set (ℝ × ℝ × ℝ)) (α : ℝ) : ℝ :=
  ∑ p ∈ Finset.Icc 1 P,
    if IsPrimitiveResonance p α ∧ markedResonancePoint N p α ∈ K then
      markedShotKernel (markedResonancePoint N p α)
    else 0

theorem measurable_markedKernelSum (N P : ℕ)
    {K : Set (ℝ × ℝ × ℝ)} (hK : MeasurableSet K) :
    Measurable (markedKernelSum N P K) := by
  classical
  unfold markedKernelSum
  apply Finset.measurable_fun_sum
  intro p _hp
  apply Measurable.ite
  · exact (measurableSet_isPrimitiveResonance p).inter
      (hK.preimage (measurable_markedResonancePoint N p))
  · exact measurable_markedShotKernel.comp (measurable_markedResonancePoint N p)
  · exact measurable_const

/-- The annular shot is exactly the marked-kernel sum over the compact
annular state space. -/
theorem annularMarkedShotFunctional_eq_markedKernelSum
    {N : ℕ} (hN : 2 ≤ N) {ε A : ℝ} (hε : 0 ≤ ε) (α : ℝ) :
    annularMarkedShotFunctional N ε A α =
      markedKernelSum N N (compactAnnularMarkedRegion ε A) α := by
  classical
  unfold annularMarkedShotFunctional markedKernelSum
  apply Finset.sum_congr rfl
  intro p hp
  rw [markedResonancePoint_mem_compactAnnularMarkedRegion_iff hN hp hε α]
  split_ifs <;> rfl

variable {ι : Type*} [Fintype ι]

/-- A finite-cell approximation written denominator first.  This ordering is
convenient for pointwise estimates; the next theorem identifies it with the
weighted marked-count functional. -/
def finiteCellMarkedShotApproximation
    (N P : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (w : ι → ℝ) (α : ℝ) : ℝ :=
  ∑ p ∈ Finset.Icc 1 P,
    if IsPrimitiveResonance p α then
      ∑ i, if markedResonancePoint N p α ∈ B i then w i else 0
    else 0

theorem finiteCellMarkedShotApproximation_eq_weightedCountSum
    (N P : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (w : ι → ℝ) (α : ℝ) :
    finiteCellMarkedShotApproximation N P B w α =
      weightedCountSum w (markedResonanceCountVector N P B α) := by
  classical
  unfold finiteCellMarkedShotApproximation weightedCountSum
    markedResonanceCountVector markedResonanceCount
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hprim : IsPrimitiveResonance p α
  · simp [hprim]
  · simp [hprim]

theorem measurable_finiteCellMarkedShotApproximation
    (N P : ℕ) {B : ι → Set (ℝ × ℝ × ℝ)}
    (hB : ∀ i, MeasurableSet (B i)) (w : ι → ℝ) :
    Measurable (finiteCellMarkedShotApproximation N P B w) := by
  have hfun : finiteCellMarkedShotApproximation N P B w =
      weightedCountSum w ∘ markedResonanceCountVector N P B := by
    funext α
    exact finiteCellMarkedShotApproximation_eq_weightedCountSum N P B w α
  rw [hfun]
  exact (continuous_weightedCountSum w).measurable.comp
    (measurable_markedResonanceCountVector N P hB)

/-- If the cells form a genuine finite partition of `K` and the kernel varies
by at most `η` on each cell, then the exact finite marked sum differs from its
cell approximation by at most `η` times the number of retained points. -/
theorem abs_markedKernelSum_sub_finiteCellApproximation_le_count
    (N P : ℕ) (K : Set (ℝ × ℝ × ℝ))
    (B : ι → Set (ℝ × ℝ × ℝ)) (w : ι → ℝ)
    {η : ℝ}
    (hsub : ∀ i, B i ⊆ K)
    (hpart : ∀ z ∈ K, ∃! i, z ∈ B i)
    (happrox : ∀ i z, z ∈ B i →
      |markedShotKernel z - w i| ≤ η)
    (α : ℝ) :
    |markedKernelSum N P K α -
        finiteCellMarkedShotApproximation N P B w α| ≤
      η * (markedResonanceCount N P K α : ℝ) := by
  classical
  unfold markedKernelSum finiteCellMarkedShotApproximation
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ p ∈ Finset.Icc 1 P,
        ((if IsPrimitiveResonance p α ∧ markedResonancePoint N p α ∈ K then
            markedShotKernel (markedResonancePoint N p α) else 0) -
          if IsPrimitiveResonance p α then
            ∑ i, if markedResonancePoint N p α ∈ B i then w i else 0
          else 0)|
        ≤ ∑ p ∈ Finset.Icc 1 P,
            |((if IsPrimitiveResonance p α ∧ markedResonancePoint N p α ∈ K then
                markedShotKernel (markedResonancePoint N p α) else 0) -
              if IsPrimitiveResonance p α then
                ∑ i, if markedResonancePoint N p α ∈ B i then w i else 0
              else 0)| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Finset.Icc 1 P,
          if IsPrimitiveResonance p α ∧ markedResonancePoint N p α ∈ K
          then η else 0 := by
      apply Finset.sum_le_sum
      intro p _hp
      let z := markedResonancePoint N p α
      by_cases hprim : IsPrimitiveResonance p α
      · by_cases hzK : z ∈ K
        · obtain ⟨i, hiB, hiUnique⟩ := hpart z hzK
          have hsum : (∑ j, if z ∈ B j then w j else 0) = w i := by
            rw [Fintype.sum_eq_single i]
            · simp [hiB]
            · intro j hji
              rw [if_neg]
              intro hjB
              exact hji (hiUnique j hjB)
          simp only [hprim, hzK, and_self, if_true, z]
          rw [hsum]
          exact happrox i z hiB
        · have hnone : ∀ i, z ∉ B i := by
            intro i hiB
            exact hzK (hsub i hiB)
          simp [hprim, hzK, hnone, z]
      · simp [hprim]
    _ = η * (markedResonanceCount N P K α : ℝ) := by
      unfold markedResonanceCount
      simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases h : IsPrimitiveResonance p α ∧ markedResonancePoint N p α ∈ K
      · simp [h]
      · simp [h]

/-- The preceding estimate specialized to the manuscript's annular shot. -/
theorem abs_annularMarkedShotFunctional_sub_finiteCellApproximation_le_count
    {N : ℕ} (hN : 2 ≤ N) {ε A η : ℝ} (hε : 0 ≤ ε)
    (B : ι → Set (ℝ × ℝ × ℝ)) (w : ι → ℝ)
    (hsub : ∀ i, B i ⊆ compactAnnularMarkedRegion ε A)
    (hpart : ∀ z ∈ compactAnnularMarkedRegion ε A, ∃! i, z ∈ B i)
    (happrox : ∀ i z, z ∈ B i →
      |markedShotKernel z - w i| ≤ η)
    (α : ℝ) :
    |annularMarkedShotFunctional N ε A α -
        finiteCellMarkedShotApproximation N N B w α| ≤
      η * (markedResonanceCount N N
        (compactAnnularMarkedRegion ε A) α : ℝ) := by
  rw [annularMarkedShotFunctional_eq_markedKernelSum hN hε α]
  exact abs_markedKernelSum_sub_finiteCellApproximation_le_count
    N N (compactAnnularMarkedRegion ε A) B w hsub hpart happrox α

/-- A fully quantified finite-mesh approximation statement.  For every
target one-point error there is a single mesh radius which works for every
finite measurable or nonmeasurable partition, every choice of cell centers,
every sample point, and every retained denominator simultaneously. -/
theorem exists_cell_radius_abs_annularShot_sub_approximation_le_count
    {N : ℕ} (hN : 2 ≤ N) {ε A η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0,
      ∀ (B : ι → Set (ℝ × ℝ × ℝ))
        (c : ι → ℝ × ℝ × ℝ),
        (∀ i, B i ⊆ compactAnnularMarkedRegion ε A) →
        (∀ z ∈ compactAnnularMarkedRegion ε A, ∃! i, z ∈ B i) →
        (∀ i, c i ∈ compactAnnularMarkedRegion ε A) →
        (∀ i z, z ∈ B i → dist z (c i) < δ) →
        ∀ α,
          |annularMarkedShotFunctional N ε A α -
              finiteCellMarkedShotApproximation N N B
                (fun i ↦ markedShotKernel (c i)) α| ≤
            η * (markedResonanceCount N N
              (compactAnnularMarkedRegion ε A) α : ℝ) := by
  obtain ⟨δ, hδ, hkernel⟩ :=
    exists_uniform_cell_radius_markedShotKernel hε hη
  refine ⟨δ, hδ, ?_⟩
  intro B c hsub hpart hcenters hmesh α
  apply abs_annularMarkedShotFunctional_sub_finiteCellApproximation_le_count
    hN hε.le B (fun i ↦ markedShotKernel (c i)) hsub hpart
  intro i z hz
  exact (hkernel z (hsub i hz) (c i) (hcenters i) (hmesh i z hz)).le

/-! ## Law and weak-convergence bridge -/

/-- Probability law of the literal denominator-first finite-cell shot. -/
def finiteCellMarkedShotLaw
    (N P : ℕ) (B : ι → Set (ℝ × ℝ × ℝ))
    (hB : ∀ i, MeasurableSet (B i)) (w : ι → ℝ) :
    ProbabilityMeasure ℝ :=
  uniform01.map
    (measurable_finiteCellMarkedShotApproximation N P hB w).aemeasurable

/-- The law of the denominator-first cell approximation is exactly the
weighted count-vector law. -/
theorem finiteCellMarkedShotLaw_eq_weightedMarkedCountLaw
    (N P : ℕ) (B : ι → Set (ℝ × ℝ × ℝ))
    (hB : ∀ i, MeasurableSet (B i)) (w : ι → ℝ) :
    finiteCellMarkedShotLaw N P B hB w =
      weightedMarkedCountLaw N P B hB w := by
  unfold finiteCellMarkedShotLaw
  unfold weightedMarkedCountLaw
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (finiteCellMarkedShotApproximation N P B w)
      (uniform01 : Measure ℝ) =
    Measure.map (weightedCountSum w)
      (Measure.map (markedResonanceCountVector N P B) (uniform01 : Measure ℝ))
  rw [AEMeasurable.map_map_of_aemeasurable
    (continuous_weightedCountSum w).measurable.aemeasurable
    (measurable_markedResonanceCountVector N P hB).aemeasurable]
  congr 1
  funext α
  exact finiteCellMarkedShotApproximation_eq_weightedCountSum N P B w α

/-- Mixed factorial convergence of the cell-count vector gives weak
convergence of the literal denominator-first finite-cell shot.  This is the
continuous-mapping step needed after choosing a finite annular partition. -/
theorem tendsto_finiteCellMarkedShotLaw_of_mixedFactorialMoments
    (Ns Ps : ℕ → ℕ) (B : ι → Set (ℝ × ℝ × ℝ))
    (hB : ∀ i, MeasurableSet (B i)) (r : ι → NNReal)
    (w : ι → ℝ)
    (hFac : ∀ k : ι → ℕ,
      Tendsto
        (fun n ↦ mixedFactorialMoment
          (markedResonanceCountVectorLaw (Ns n) (Ps n) B hB) k)
        atTop (nhds (∏ i, (r i : ℝ) ^ (k i)))) :
    Tendsto
      (fun n ↦ finiteCellMarkedShotLaw (Ns n) (Ps n) B hB w)
      atTop (nhds (weightedIndependentPoissonLaw r w)) :=
  (tendsto_weightedMarkedCountLaw_of_mixedFactorialMoments
    Ns Ps B hB r w hFac).congr'
      (Filter.Eventually.of_forall fun n ↦
        finiteCellMarkedShotLaw_eq_weightedMarkedCountLaw
          (Ns n) (Ps n) B hB w |>.symm)

end

end Erdos1002
