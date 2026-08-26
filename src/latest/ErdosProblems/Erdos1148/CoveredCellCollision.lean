import ErdosProblems.Erdos1148.PartitionEntropyCollision

/-! # Collision and entropy bounds for disjoint cells with bounded local covers -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Function

theorem sum_sq_mass_le_cover_bound_mul_pair_mass {X ι : Type*} [MeasurableSpace X]
    [Fintype ι] (μ : Measure X) [IsFiniteMeasure μ] (s : ι → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hdisj : Pairwise (Disjoint on s))
    {R : Set (X × X)} (hR : MeasurableSet R) {C : ℝ} (hC : 0 ≤ C)
    (hcover : ∀ i, ∃ (N : ℕ) (B : Fin N → Set X), (N : ℝ) ≤ C ∧
      (∀ j, MeasurableSet (B j)) ∧ s i ⊆ ⋃ j, B j ∧ ∀ j, B j ×ˢ B j ⊆ R) :
    (∑ i, μ.real (s i) ^ 2) ≤ C * (μ.prod μ).real R := by
  have hcell (i : ι) : μ.real (s i) ^ 2 ≤ C * (μ.prod μ).real ((s i ×ˢ s i) ∩ R) := by
    obtain ⟨N, B, hN, hB, hcov, hpair⟩ := hcover i
    have hcov' : s i ⊆ ⋃ j, B j ∩ s i := by
      intro x hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov hx)
      exact Set.mem_iUnion.mpr ⟨j, hj, hx⟩
    have hpair' (j : Fin N) : (B j ∩ s i) ×ˢ (B j ∩ s i) ⊆ (s i ×ˢ s i) ∩ R := by
      rintro ⟨x, y⟩ ⟨⟨hxB, hxs⟩, ⟨hyB, hys⟩⟩
      exact ⟨⟨hxs, hys⟩, hpair j ⟨hxB, hyB⟩⟩
    exact (finite_cover_mass_sq_le_pair_mass μ (fun j => B j ∩ s i)
      (fun j => (hB j).inter (hs i)) hcov' hpair').trans
      (mul_le_mul_of_nonneg_right hN measureReal_nonneg)
  have hpairdisj : Pairwise (Disjoint on fun i => (s i ×ˢ s i) ∩ R) := by
    intro i j hij
    have hd : Disjoint (s i) (s j) := hdisj hij
    have hp : Disjoint (s i ×ˢ s i) (s j ×ˢ s j) := by
      apply Set.disjoint_left.mpr
      rintro ⟨x, y⟩ hx hy
      exact Set.disjoint_left.mp hd hx.1 hy.1
    exact hp.mono Set.inter_subset_left Set.inter_subset_left
  have hsum : (∑ i, (μ.prod μ).real ((s i ×ˢ s i) ∩ R)) ≤ (μ.prod μ).real R := by
    rw [← measureReal_iUnion_fintype hpairdisj (fun i => ((hs i).prod (hs i)).inter hR)]
    exact measureReal_mono (Set.iUnion_subset (fun _ => Set.inter_subset_right))
  calc
    _ ≤ ∑ i, C * (μ.prod μ).real ((s i ×ˢ s i) ∩ R) := Finset.sum_le_sum (fun i _ => hcell i)
    _ = C * ∑ i, (μ.prod μ).real ((s i ×ˢ s i) ∩ R) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hC

theorem covered_cells_entropy_lower_bound {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) [IsFiniteMeasure μ] (s : ι → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hdisj : Pairwise (Disjoint on s))
    {R : Set (X × X)} (hR : MeasurableSet R) {C B m : ℝ} (hC : 0 ≤ C)
    (hcover : ∀ i, ∃ (N : ℕ) (D : Fin N → Set X), (N : ℝ) ≤ C ∧
      (∀ j, MeasurableSet (D j)) ∧ s i ⊆ ⋃ j, D j ∧ ∀ j, D j ×ˢ D j ⊆ R)
    (hpair : (μ.prod μ).real R ≤ B) (hm : 0 < m) (hsum : (∑ i, μ.real (s i)) = m) :
    -m * Real.log ((C * B) / m) ≤ finitePartitionEntropy μ s := by
  have hpos := finite_collision_pos_of_sum_pos (by rwa [hsum] : 0 < ∑ i, μ.real (s i))
  have hcol := (sum_sq_mass_le_cover_bound_mul_pair_mass μ s hs hdisj hR hC hcover).trans
    (mul_le_mul_of_nonneg_left hpair hC)
  have hlog := Real.log_le_log (div_pos hpos hm) (div_le_div_of_nonneg_right hcol hm.le)
  exact (mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr hm.le)).trans
    (neg_mul_log_collision_div_mass_le_finiteEntropy (fun i => measureReal_nonneg) hm hsum)

end Erdos1148.DukeArithmetic
