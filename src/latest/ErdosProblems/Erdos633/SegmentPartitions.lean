import ErdosProblems.Erdos633.BoundaryIntervals
import ErdosProblems.Erdos633.BoundarySideCounts
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Finite segment partitions and marked endpoints

This transports the interval obstruction to planar segments. Coverage may
initially omit a finite exceptional set, and pairwise intersections need only
be finite. These are exactly the geometric boundary facts proved for tilings.
-/

namespace Erdos633

theorem closed_cover_Icc_of_finite_exception {S F : Set ℝ}
    (hS : IsClosed S) (hF : F.Finite)
    (hcover : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ∉ F → x ∈ S) :
    Set.Icc (0 : ℝ) 1 ⊆ S := by
  have hd : Dense Fᶜ := by
    simpa only [Set.sdiff_eq, Set.univ_inter] using dense_univ.sdiff_finite hF
  have hs : Set.Ioo (0 : ℝ) 1 ∩ Fᶜ ⊆ S := by
    rintro x ⟨hx, hf⟩
    exact hcover x ⟨hx.1.le, hx.2.le⟩ hf
  have hi : Set.Ioo (0 : ℝ) 1 ⊆ S :=
    (hd.open_subset_closure_inter isOpen_Ioo).trans (closure_minimal hs hS)
  have hc := closure_minimal hi hS
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hc
  exact hc

theorem no_injective_segment_endpoint_marks {ι : Type*} [Finite ι]
    (A B : ℂ) (hAB : A ≠ B) (u v g : ι → ℂ)
    (hne : ∀ i, u i ≠ v i)
    (hsub : ∀ i, segment ℝ (u i) (v i) ⊆ segment ℝ A B)
    (F : Set ℂ) (hF : F.Finite)
    (hcover : ∀ z ∈ segment ℝ A B, z ∉ F → ∃ i, z ∈ segment ℝ (u i) (v i))
    (hinter : Pairwise fun i j =>
      (segment ℝ (u i) (v i) ∩ segment ℝ (u j) (v j)).Finite)
    (hmark : ∀ i, g i = u i ∨ g i = v i)
    (hends : ∀ i, g i ≠ A ∧ g i ≠ B)
    (hinj : Function.Injective g) : False := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let f : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap A B
  have hf : Function.Injective f := AffineMap.lineMap_injective ℝ hAB
  have hu (i : ι) : ∃ t ∈ Set.Icc (0 : ℝ) 1, f t = u i := by
    have h := hsub i (left_mem_segment ℝ (u i) (v i))
    rw [segment_eq_image_lineMap] at h
    exact h
  have hv (i : ι) : ∃ t ∈ Set.Icc (0 : ℝ) 1, f t = v i := by
    have h := hsub i (right_mem_segment ℝ (u i) (v i))
    rw [segment_eq_image_lineMap] at h
    exact h
  choose p hp hpu using hu
  choose q hq hqv using hv
  let l (i : ι) := min (p i) (q i)
  let r (i : ι) := max (p i) (q i)
  let m (i : ι) := if g i = u i then p i else q i
  have hpq (i : ι) : p i ≠ q i := fun h => hne i (by rw [← hpu i, ← hqv i, h])
  have hlr (i : ι) : l i < r i := min_lt_max.mpr (hpq i)
  have hbound (i : ι) : 0 ≤ l i ∧ r i ≤ 1 :=
    ⟨le_min (hp i).1 (hq i).1, max_le (hp i).2 (hq i).2⟩
  have himage (i : ι) : f '' Set.Icc (l i) (r i) = segment ℝ (u i) (v i) := by
    rw [← segment_eq_Icc' (p i) (q i), image_segment, hpu i, hqv i]
  have hmem (i : ι) (t : ℝ) :
      t ∈ Set.Icc (l i) (r i) ↔ f t ∈ segment ℝ (u i) (v i) := by
    rw [← himage i, hf.mem_set_image]
  have hFc : (f ⁻¹' F).Finite := hF.preimage hf.injOn
  have hcov : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ i, t ∈ Set.Icc (l i) (r i) := by
    have hclosed : IsClosed (⋃ i, Set.Icc (l i) (r i)) :=
      isClosed_iUnion_of_finite (fun _ => isClosed_Icc)
    have hc : Set.Icc (0 : ℝ) 1 ⊆ ⋃ i, Set.Icc (l i) (r i) := by
      apply closed_cover_Icc_of_finite_exception hclosed hFc
      intro t ht htF
      obtain ⟨i, hi⟩ := hcover (f t) (lineMap_mem_segment ℝ A B ht) htF
      exact Set.mem_iUnion.mpr ⟨i, (hmem i t).mpr hi⟩
    intro t ht
    exact Set.mem_iUnion.mp (hc ht)
  have hdisj : Pairwise fun i j =>
      Disjoint (Set.Ioo (l i) (r i)) (Set.Ioo (l j) (r j)) := by
    intro i j hij
    apply Set.Ioo_disjoint_Ioo.mpr
    by_contra h
    have hlt : max (l i) (l j) < min (r i) (r j) := lt_of_not_ge h
    have hfin := (hinter hij).preimage hf.injOn
    have hs : Set.Ioo (max (l i) (l j)) (min (r i) (r j)) ⊆
        f ⁻¹' (segment ℝ (u i) (v i) ∩ segment ℝ (u j) (v j)) := by
      intro t ht
      exact ⟨(hmem i t).mp ⟨(le_max_left _ _).trans ht.1.le,
        ht.2.le.trans (min_le_left _ _)⟩,
        (hmem j t).mp ⟨(le_max_right _ _).trans ht.1.le,
        ht.2.le.trans (min_le_right _ _)⟩⟩
    exact Set.Ioo_infinite hlt (hfin.subset hs)
  have hmimage (i : ι) : f (m i) = g i := by
    dsimp [m]
    split_ifs with h
    · exact (hpu i).trans h.symm
    · exact (hqv i).trans ((hmark i).resolve_left h).symm
  have hmpq (i : ι) : m i = p i ∨ m i = q i := by
    dsimp [m]
    split_ifs <;> simp
  have hm (i : ι) : m i = l i ∨ m i = r i := by
    rcases le_total (p i) (q i) with h | h
    · simpa only [l, r, min_eq_left h, max_eq_right h] using hmpq i
    · simpa only [l, r, min_eq_right h, max_eq_left h, or_comm] using hmpq i
  have hmint (i : ι) : m i ∈ Set.Ioo (0 : ℝ) 1 := by
    have hmi : m i ∈ Set.Icc (0 : ℝ) 1 := by
      rcases hmpq i with h | h
      · exact h.symm ▸ hp i
      · exact h.symm ▸ hq i
    have h0 : m i ≠ 0 := by
      intro h
      exact (hends i).1 (by rw [← hmimage i, h]; exact AffineMap.lineMap_apply_zero A B)
    have h1 : m i ≠ 1 := by
      intro h
      exact (hends i).2 (by rw [← hmimage i, h]; exact AffineMap.lineMap_apply_one A B)
    exact ⟨lt_of_le_of_ne hmi.1 h0.symm, lt_of_le_of_ne hmi.2 h1⟩
  have hminj : Function.Injective m := by
    intro i j hij
    apply hinj
    rw [← hmimage i, ← hmimage j, hij]
  exact no_injective_interior_endpoint_marks l r m hlr hbound hcov hdisj hm hmint hminj

end Erdos633
