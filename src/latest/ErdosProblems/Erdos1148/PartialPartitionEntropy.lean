import ErdosProblems.Erdos1148.FinitePartitionEntropy

/-! # Entropy of a subfamily is bounded by entropy of the whole family -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory

theorem finitePartitionEntropy_subtype_le {X ι : Type*} [MeasurableSpace X]
    [Fintype ι] (μ : Measure X) [IsProbabilityMeasure μ] (s : ι → Set X)
    (p : ι → Prop) [DecidablePred p] :
    finitePartitionEntropy μ (fun i : Subtype p => s i.val) ≤ finitePartitionEntropy μ s := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype p (fun i => Real.negMulLog (μ.real (s i)))
  have hnonneg : 0 ≤ ∑ i : {i // ¬p i}, Real.negMulLog (μ.real (s i.val)) :=
    Finset.sum_nonneg (fun _ _ => Real.negMulLog_nonneg measureReal_nonneg measureReal_le_one)
  change (∑ i : Subtype p, Real.negMulLog (μ.real (s i.val))) ≤
    ∑ i, Real.negMulLog (μ.real (s i))
  linarith

end Erdos1148.DukeArithmetic
