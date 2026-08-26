import ErdosProblems.Erdos633b.BoundaryCover
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real

/-! Length additivity for an actual finite segment partition, derived from
one-dimensional Lebesgue measure and the affine line-map distance formula. -/

open MeasureTheory
open scoped ENNReal

namespace Erdos633b

theorem real_segment_partition_length_on {ι : Type*} [Fintype ι]
    (c d : ℝ) (hcd : c ≤ d) (a b : ι → ℝ) (hab : ∀ i, a i ≠ b i)
    (hc : (⋃ i, segment ℝ (a i) (b i)) = Set.Icc c d)
    (hd : Pairwise fun i j => Disjoint (openSegment ℝ (a i) (b i))
      (openSegment ℝ (a j) (b j))) :
    ∑ i, |a i - b i| = d - c := by
  have hae (i : ι) : segment ℝ (a i) (b i) =ᵐ[volume]
      openSegment ℝ (a i) (b i) := by
    rw [segment_eq_uIcc, ← Set.Icc_min_max, openSegment_eq_Ioo' (hab i)]
    exact Ioo_ae_eq_Icc.symm
  have hm (i : ι) : MeasurableSet (openSegment ℝ (a i) (b i)) := by
    rw [openSegment_eq_Ioo' (hab i)]
    exact measurableSet_Ioo
  have hf (i : ι) : volume (openSegment ℝ (a i) (b i)) ≠ ∞ := by
    rw [openSegment_eq_Ioo' (hab i), Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hl (i : ι) : volume.real (openSegment ℝ (a i) (b i)) = |a i - b i| := by
    rw [← measureReal_congr (hae i), segment_eq_uIcc, Real.volume_real_interval]
    exact abs_sub_comm _ _
  have hu := measureReal_congr (Filter.EventuallyEq.countable_iUnion hae)
  rw [hc, Real.volume_real_Icc_of_le hcd] at hu
  rw [measureReal_iUnion_fintype hd hm hf] at hu
  simpa only [hl] using hu.symm

theorem real_segment_partition_length {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (hab : ∀ i, a i ≠ b i)
    (hc : (⋃ i, segment ℝ (a i) (b i)) = Set.Icc (0 : ℝ) 1)
    (hd : Pairwise fun i j => Disjoint (openSegment ℝ (a i) (b i))
      (openSegment ℝ (a j) (b j))) :
    ∑ i, |a i - b i| = 1 := by
  simpa only [sub_zero] using real_segment_partition_length_on 0 1 (by norm_num) a b hab hc hd

theorem segment_partition_coordinates {ι : Type*}
    (P Q : Plane) (hPQ : P ≠ Q) (A B : ι → Plane) (hAB : ∀ i, A i ≠ B i)
    (hc : (⋃ i, segment ℝ (A i) (B i)) = segment ℝ P Q)
    (hd : Pairwise fun i j => Disjoint (openSegment ℝ (A i) (B i))
      (openSegment ℝ (A j) (B j))) :
    ∃ a b : ι → ℝ,
      (∀ i, AffineMap.lineMap P Q (a i) = A i) ∧
      (∀ i, AffineMap.lineMap P Q (b i) = B i) ∧ (∀ i, a i ≠ b i) ∧
      (⋃ i, segment ℝ (a i) (b i)) = Set.Icc (0 : ℝ) 1 ∧
      Pairwise (fun i j => Disjoint (openSegment ℝ (a i) (b i))
        (openSegment ℝ (a j) (b j))) := by
  have hsub (i : ι) : segment ℝ (A i) (B i) ⊆ segment ℝ P Q := by
    rw [← hc]
    exact Set.subset_iUnion (fun j : ι => segment ℝ (A j) (B j)) i
  let L : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap P Q
  have hL : Function.Injective L := AffineMap.lineMap_injective ℝ hPQ
  have hA (i : ι) : ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ L t = A i := by
    have h := hsub i (left_mem_segment ℝ (A i) (B i))
    rw [segment_eq_image_lineMap] at h
    exact h
  have hB (i : ι) : ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ L t = B i := by
    have h := hsub i (right_mem_segment ℝ (A i) (B i))
    rw [segment_eq_image_lineMap] at h
    exact h
  choose a ha hAa using hA
  choose b hb hBb using hB
  have hab (i : ι) : a i ≠ b i := by
    intro hi
    exact hAB i (hAa i ▸ hBb i ▸ congrArg L hi)
  have himage (i : ι) : L '' segment ℝ (a i) (b i) = segment ℝ (A i) (B i) := by
    rw [image_segment, hAa, hBb]
  have hopen (i : ι) : L '' openSegment ℝ (a i) (b i) = openSegment ℝ (A i) (B i) := by
    rw [image_openSegment, hAa, hBb]
  have hcover : (⋃ i, segment ℝ (a i) (b i)) = Set.Icc (0 : ℝ) 1 := by
    apply hL.image_injective
    rw [Set.image_iUnion, show L '' Set.Icc (0 : ℝ) 1 = segment ℝ P Q from
      (segment_eq_image_lineMap ℝ P Q).symm]
    simpa only [himage] using hc
  have hdisj : Pairwise fun i j => Disjoint (openSegment ℝ (a i) (b i))
      (openSegment ℝ (a j) (b j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro t hti htj
    have hi : L t ∈ openSegment ℝ (A i) (B i) := hopen i ▸ ⟨t, hti, rfl⟩
    have hj : L t ∈ openSegment ℝ (A j) (B j) := hopen j ▸ ⟨t, htj, rfl⟩
    exact Set.disjoint_left.mp (hd hij) hi hj
  exact ⟨a, b, hAa, hBb, hab, hcover, hdisj⟩

theorem segment_partition_length {ι : Type*} [Fintype ι]
    (P Q : Plane) (hPQ : P ≠ Q) (A B : ι → Plane) (hAB : ∀ i, A i ≠ B i)
    (hc : (⋃ i, segment ℝ (A i) (B i)) = segment ℝ P Q)
    (hd : Pairwise fun i j => Disjoint (openSegment ℝ (A i) (B i))
      (openSegment ℝ (A j) (B j))) :
    dist P Q = ∑ i, dist (A i) (B i) := by
  obtain ⟨a, b, hAa, hBb, hab, hcover, hdisj⟩ :=
    segment_partition_coordinates P Q hPQ A B hAB hc hd
  have hsum := real_segment_partition_length a b hab hcover hdisj
  have hdist (i : ι) : dist (A i) (B i) = |a i - b i| * dist P Q := by
    rw [← hAa i, ← hBb i]
    exact (dist_lineMap_lineMap P Q (a i) (b i)).trans (by rw [Real.dist_eq])
  simp_rw [hdist]
  rw [← Finset.sum_mul, hsum, one_mul]

end Erdos633b
