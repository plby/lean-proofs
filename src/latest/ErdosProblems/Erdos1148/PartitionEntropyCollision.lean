import ErdosProblems.Erdos1148.FiniteEntropyCollision
import ErdosProblems.Erdos1148.PartialEntropyCollision
import ErdosProblems.Erdos1148.FiniteCoverPairMass

/-! # Pair-mass estimates give entropy bounds for finite measurable partitions -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Function

noncomputable def finitePartitionEntropy {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (s : ι → Set X) : ℝ :=
  finiteEntropy (fun i => μ.real (s i))

theorem neg_mass_log_pair_bound_div_mass_le_partitionEntropy {X ι : Type*}
    [MeasurableSpace X] [Fintype ι] (μ : Measure X) [IsFiniteMeasure μ] (s : ι → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hdisj : Pairwise (Disjoint on s))
    {m : ℝ} (hm : 0 < m) (hsum : ∑ i, μ.real (s i) = m) {R : Set (X × X)}
    (hpair : ∀ i, s i ×ˢ s i ⊆ R) {B : ℝ} (hB : (μ.prod μ).real R ≤ B) :
    -m * Real.log (B / m) ≤ finitePartitionEntropy μ s := by
  have hpos := finite_collision_pos_of_sum_pos (by rwa [hsum] : 0 < ∑ i, μ.real (s i))
  have hcol := (sum_sq_measureReal_le_pair_mass μ s hs hdisj hpair).trans hB
  have hlog := Real.log_le_log (div_pos hpos hm) (div_le_div_of_nonneg_right hcol hm.le)
  exact (mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr hm.le)).trans
    (neg_mul_log_collision_div_mass_le_finiteEntropy (fun i => measureReal_nonneg) hm hsum)

theorem neg_log_pair_bound_le_partitionEntropy {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) [IsProbabilityMeasure μ] (s : ι → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hdisj : Pairwise (Disjoint on s))
    (hcover : (⋃ i, s i) = Set.univ) {R : Set (X × X)}
    (hpair : ∀ i, s i ×ˢ s i ⊆ R) {B : ℝ} (hB : (μ.prod μ).real R ≤ B) :
    -Real.log B ≤ finitePartitionEntropy μ s := by
  have hsum : ∑ i, μ.real (s i) = 1 := by
    rw [← measureReal_iUnion_fintype hdisj hs, hcover]
    simp
  have hcol := sum_sq_measureReal_le_pair_mass μ s hs hdisj hpair
  exact (neg_le_neg (Real.log_le_log (finite_collision_pos hsum) (hcol.trans hB))).trans
    (neg_log_collision_le_finiteEntropy (fun i => measureReal_nonneg) hsum)

end Erdos1148.DukeArithmetic
