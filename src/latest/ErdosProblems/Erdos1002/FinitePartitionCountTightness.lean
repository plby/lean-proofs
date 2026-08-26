import ErdosProblems.Erdos1002.FiniteShotConvergence
import ErdosProblems.Erdos1002.MarkedCountTightness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Point-count tightness from a finite marked partition

For a genuine finite partition, the number of points in the union is
exactly the sum of the cell counts, with multiplicities handled explicitly.
Consequently convergence of the finitely many cell first moments gives
tightness of the total count required by the finite-mesh shot argument.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance finitePartitionCountTightnessPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

variable {ι : Type*} [Fintype ι]

/-- Counts are exactly additive over a finite genuine partition. -/
theorem sum_markedResonanceCount_partition
    (N P : ℕ) (K : Set (ℝ × ℝ × ℝ))
    (B : ι → Set (ℝ × ℝ × ℝ))
    (hsub : ∀ i, B i ⊆ K)
    (hpart : ∀ z ∈ K, ∃! i, z ∈ B i)
    (α : ℝ) :
    (∑ i, markedResonanceCount N P (B i) α) =
      markedResonanceCount N P K α := by
  classical
  unfold markedResonanceCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _hp
  let z := markedResonancePoint N p α
  by_cases hprim : IsPrimitiveResonance p α
  · by_cases hzK : z ∈ K
    · obtain ⟨i, hiB, hiUnique⟩ := hpart z hzK
      have hsingle :
          (∑ j : ι, if IsPrimitiveResonance p α ∧ z ∈ B j then 1 else 0) = 1 := by
        rw [Fintype.sum_eq_single i]
        · simp [hprim, hiB]
        · intro j hji
          rw [if_neg]
          intro hj
          exact hji (hiUnique j hj.2)
      simpa [z, hprim, hzK] using! hsingle
    · have hnone : ∀ i, z ∉ B i := by
        intro i hi
        exact hzK (hsub i hi)
      simp [z, hprim, hzK, hnone]
  · simp [hprim]

/-- The integral of the total count is the finite sum of the cell-count
integrals. -/
theorem integral_markedResonanceCount_partition
    (N P : ℕ) {K : Set (ℝ × ℝ × ℝ)}
    (B : ι → Set (ℝ × ℝ × ℝ))
    (hB : ∀ i, MeasurableSet (B i))
    (hsub : ∀ i, B i ⊆ K)
    (hpart : ∀ z ∈ K, ∃! i, z ∈ B i) :
    (∫ α, (markedResonanceCount N P K α : ℝ) ∂uniform01Measure) =
      ∑ i, ∫ α,
        (markedResonanceCount N P (B i) α : ℝ) ∂uniform01Measure := by
  have hfun : (fun α ↦ (markedResonanceCount N P K α : ℝ)) =
      fun α ↦ ∑ i, (markedResonanceCount N P (B i) α : ℝ) := by
    funext α
    exact_mod_cast (sum_markedResonanceCount_partition
      N P K B hsub hpart α).symm
  rw [hfun, MeasureTheory.integral_finset_sum]
  intro i _hi
  exact integrable_markedResonanceCount_cast N P (hB i)

/-- Cellwise first-moment convergence implies convergence of the total
partition count's first moment. -/
theorem tendsto_integral_markedResonanceCount_partition
    (Ns Ps : ℕ → ℕ) {K : Set (ℝ × ℝ × ℝ)}
    (B : ι → Set (ℝ × ℝ × ℝ))
    (hB : ∀ i, MeasurableSet (B i))
    (hsub : ∀ i, B i ⊆ K)
    (hpart : ∀ z ∈ K, ∃! i, z ∈ B i)
    (r : ι → ℝ)
    (hcell : ∀ i, Tendsto
      (fun n ↦ ∫ α,
        (markedResonanceCount (Ns n) (Ps n) (B i) α : ℝ)
          ∂uniform01Measure)
      atTop (nhds (r i))) :
    Tendsto
      (fun n ↦ ∫ α,
        (markedResonanceCount (Ns n) (Ps n) K α : ℝ)
          ∂uniform01Measure)
      atTop (nhds (∑ i, r i)) := by
  have hsum := tendsto_finset_sum Finset.univ (fun i _hi ↦ hcell i)
  apply hsum.congr'
  exact Eventually.of_forall fun n ↦ by
    change (∑ i, ∫ α,
      (markedResonanceCount (Ns n) (Ps n) (B i) α : ℝ)
        ∂uniform01Measure) =
      ∫ α, (markedResonanceCount (Ns n) (Ps n) K α : ℝ)
        ∂uniform01Measure
    exact (integral_markedResonanceCount_partition
      (Ns n) (Ps n) B hB hsub hpart).symm

/-- Hence the total count of a finite marked partition is tight. -/
theorem markedResonanceCount_partition_tight
    (Ns Ps : ℕ → ℕ) {K : Set (ℝ × ℝ × ℝ)} (hK : MeasurableSet K)
    (B : ι → Set (ℝ × ℝ × ℝ))
    (hB : ∀ i, MeasurableSet (B i))
    (hsub : ∀ i, B i ⊆ K)
    (hpart : ∀ z ∈ K, ∃! i, z ∈ B i)
    (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hcell : ∀ i, Tendsto
      (fun n ↦ ∫ α,
        (markedResonanceCount (Ns n) (Ps n) (B i) α : ℝ)
          ∂uniform01Measure)
      atTop (nhds (r i))) :
    ∀ δ > 0, ∃ C : ℕ, ∀ᶠ n : ℕ in atTop,
      uniform01Measure.real
        {α | C < markedResonanceCount (Ns n) (Ps n) K α} < δ := by
  apply markedResonanceCount_tight_of_tendsto_firstMoment
    Ns Ps hK (∑ i, r i)
  · exact Finset.sum_nonneg fun i _hi ↦ hr i
  · exact tendsto_integral_markedResonanceCount_partition
      Ns Ps B hB hsub hpart r hcell

end

end Erdos1002
