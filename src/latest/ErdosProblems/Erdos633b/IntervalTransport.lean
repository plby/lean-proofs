import ErdosProblems.Erdos633b.SegmentLength
import Mathlib.Topology.Order.IntermediateValue

/-! Transporting a finite interval partition through a continuous strictly
increasing function, with exact total variation from its endpoints. -/

namespace Erdos633b

theorem monotone_image_segment (f : ℝ → ℝ) (hf : Continuous f)
    (hm : StrictMonoOn f (Set.Icc 0 1)) {a b : ℝ}
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) :
    f '' segment ℝ a b = segment ℝ (f a) (f b) := by
  have hs : segment ℝ a b ⊆ Set.Icc (0 : ℝ) 1 :=
    (convex_Icc (0 : ℝ) 1).segment_subset ha hb
  rw [segment_eq_uIcc] at hs
  rw [segment_eq_uIcc, segment_eq_uIcc]
  exact hf.continuousOn.image_uIcc_of_monotoneOn (hm.monotoneOn.mono hs)

theorem monotone_image_openSegment (f : ℝ → ℝ) (hf : Continuous f)
    (hm : StrictMonoOn f (Set.Icc 0 1)) {a b : ℝ}
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (hab : a ≠ b) :
    f '' openSegment ℝ a b = openSegment ℝ (f a) (f b) := by
  rcases lt_or_gt_of_ne hab with h | h
  · rw [openSegment_eq_Ioo h, openSegment_eq_Ioo (hm ha hb h)]
    exact hf.continuousOn.image_Ioo_of_strictMonoOn h.le
      (hm.mono (Set.Icc_subset_Icc ha.1 hb.2))
  · rw [openSegment_symm ℝ a b, openSegment_symm ℝ (f a) (f b),
      openSegment_eq_Ioo h, openSegment_eq_Ioo (hm hb ha h)]
    exact hf.continuousOn.image_Ioo_of_strictMonoOn h.le
      (hm.mono (Set.Icc_subset_Icc hb.1 ha.2))

theorem interval_partition_monotone_sum {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (ha : ∀ i, a i ∈ Set.Icc 0 1) (hb : ∀ i, b i ∈ Set.Icc 0 1)
    (hab : ∀ i, a i ≠ b i) (hc : (⋃ i, segment ℝ (a i) (b i)) = Set.Icc 0 1)
    (hd : Pairwise fun i j => Disjoint (openSegment ℝ (a i) (b i))
      (openSegment ℝ (a j) (b j))) (f : ℝ → ℝ) (hf : Continuous f)
    (hm : StrictMonoOn f (Set.Icc 0 1)) :
    ∑ i, |f (a i) - f (b i)| = f 1 - f 0 := by
  have himage (i : ι) := monotone_image_segment f hf hm (ha i) (hb i)
  have hopen (i : ι) := monotone_image_openSegment f hf hm (ha i) (hb i) (hab i)
  have hcover : (⋃ i, segment ℝ (f (a i)) (f (b i))) = Set.Icc (f 0) (f 1) := by
    calc
      _ = f '' (⋃ i, segment ℝ (a i) (b i)) := by
        rw [Set.image_iUnion]
        simp only [himage]
      _ = f '' Set.Icc 0 1 := by rw [hc]
      _ = Set.Icc (f 0) (f 1) :=
        hf.continuousOn.image_Icc_of_monotoneOn (by norm_num) hm.monotoneOn
  have hsub (i : ι) : openSegment ℝ (a i) (b i) ⊆ Set.Icc 0 1 :=
    (openSegment_subset_segment ℝ _ _).trans ((convex_Icc (0 : ℝ) 1).segment_subset (ha i) (hb i))
  have hdisj : Pairwise fun i j => Disjoint (openSegment ℝ (f (a i)) (f (b i)))
      (openSegment ℝ (f (a j)) (f (b j))) := by
    intro i j hij
    rw [← hopen i, ← hopen j]
    apply Set.disjoint_left.mpr
    rintro y ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
    have hvu : v = u := hm.injOn (hsub j hv) (hsub i hu) he
    subst v
    exact Set.disjoint_left.mp (hd hij) hu hv
  have hne (i : ι) : f (a i) ≠ f (b i) := fun h => hab i (hm.injOn (ha i) (hb i) h)
  exact real_segment_partition_length_on (f 0) (f 1)
    (hm.monotoneOn (by norm_num) (by norm_num) (by norm_num)) _ _ hne hcover hdisj

end Erdos633b
