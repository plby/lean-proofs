import ErdosProblems.Erdos1148.PartitionEntropyCollision
import ErdosProblems.Erdos1148.FiniteEntropyBounds

/-! # Join subadditivity and invariance of entropy for finite measurable partitions -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Function

lemma sum_measureReal_inter_partition {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) [IsFiniteMeasure μ] (s : ι → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hdisj : Pairwise (Disjoint on s))
    (hcover : (⋃ i, s i) = Set.univ) {E : Set X} (hE : MeasurableSet E) :
    (∑ i, μ.real (E ∩ s i)) = μ.real E := by
  have hd : Pairwise (Disjoint on fun i => E ∩ s i) :=
    fun i j hij => (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right
  rw [← measureReal_iUnion_fintype hd (fun i => hE.inter (hs i)),
    ← Set.inter_iUnion, hcover, Set.inter_univ]

theorem finitePartitionEntropy_join_le {X ι κ : Type*} [MeasurableSpace X]
    [Fintype ι] [Fintype κ] (μ : Measure X) [IsProbabilityMeasure μ]
    (s : ι → Set X) (t : κ → Set X) (hs : ∀ i, MeasurableSet (s i))
    (ht : ∀ j, MeasurableSet (t j)) (hsdisj : Pairwise (Disjoint on s))
    (htdisj : Pairwise (Disjoint on t)) (hscover : (⋃ i, s i) = Set.univ)
    (htcover : (⋃ j, t j) = Set.univ) :
    finitePartitionEntropy μ (fun x : ι × κ => s x.1 ∩ t x.2) ≤
      finitePartitionEntropy μ s + finitePartitionEntropy μ t := by
  have hrow (i : ι) : (∑ j, μ.real (s i ∩ t j)) = μ.real (s i) :=
    sum_measureReal_inter_partition μ t ht htdisj htcover (hs i)
  have hcol (j : κ) : (∑ i, μ.real (s i ∩ t j)) = μ.real (t j) := by
    simpa only [Set.inter_comm] using
      sum_measureReal_inter_partition μ s hs hsdisj hscover (ht j)
  have hsum : (∑ x : ι × κ, μ.real (s x.1 ∩ t x.2)) = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [hrow]
    rw [← measureReal_iUnion_fintype hsdisj hs, hscover]
    simp
  have h := finiteEntropy_joint_le_add_marginals (fun x : ι × κ => μ.real (s x.1 ∩ t x.2))
    (fun _ => measureReal_nonneg) hsum
  simpa only [finitePartitionEntropy, hrow, hcol] using h

theorem finitePartitionEntropy_preimage_of_invariant {X ι : Type*} [MeasurableSpace X]
    [Fintype ι] (μ : Measure X) (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    {f : X → X} (hf : Measurable f) (hinv : Measure.map f μ = μ) :
    finitePartitionEntropy μ (fun i => f ⁻¹' s i) = finitePartitionEntropy μ s := by
  have heq (i : ι) : μ.real (f ⁻¹' s i) = μ.real (s i) := by
    unfold Measure.real
    rw [← Measure.map_apply hf (hs i), hinv]
  simp only [finitePartitionEntropy, heq]

end Erdos1148.DukeArithmetic
