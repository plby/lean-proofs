import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-! Successor intervals and endpoint collisions in an actual finite partition
of a closed real interval. No ordering of the given index type is assumed. -/

namespace Erdos633b.IntervalPartition

theorem bounds {ι : Type*} (a b : ι → ℝ) (hab : ∀ i, a i < b i)
    (hc : (⋃ i, Set.Icc (a i) (b i)) = Set.Icc 0 1) (i : ι) :
    0 ≤ a i ∧ b i ≤ 1 := by
  have ha : a i ∈ Set.Icc (0 : ℝ) 1 := by
    rw [← hc]
    exact Set.mem_iUnion.mpr ⟨i, le_rfl, (hab i).le⟩
  have hb : b i ∈ Set.Icc (0 : ℝ) 1 := by
    rw [← hc]
    exact Set.mem_iUnion.mpr ⟨i, (hab i).le, le_rfl⟩
  exact ⟨ha.1, hb.2⟩

theorem left_ge_of_right_endpoint_lt {ι : Type*} (a b : ι → ℝ)
    (hab : ∀ i, a i < b i)
    (hd : Pairwise fun i j => Disjoint (Set.Ioo (a i) (b i)) (Set.Ioo (a j) (b j)))
    (i j : ι) {z : ℝ} (hiz : b i < z) (hzj : z ∈ Set.Icc (a j) (b j)) :
    b i ≤ a j := by
  by_contra hn
  have haj : a j < b i := lt_of_not_ge hn
  have hmax : max (a i) (a j) < b i := max_lt (hab i) haj
  obtain ⟨u, hu1, hu2⟩ := exists_between hmax
  have hij : i ≠ j := by
    intro h
    subst j
    exact (not_lt_of_ge hzj.2) hiz
  apply Set.disjoint_left.mp (hd hij)
  · exact ⟨(le_max_left _ _).trans_lt hu1, hu2⟩
  · exact ⟨(le_max_right _ _).trans_lt hu1, hu2.trans (hiz.trans_le hzj.2)⟩

theorem exists_successor {ι : Type*} [Finite ι] (a b : ι → ℝ)
    (hab : ∀ i, a i < b i)
    (hc : (⋃ i, Set.Icc (a i) (b i)) = Set.Icc 0 1)
    (hd : Pairwise fun i j => Disjoint (Set.Ioo (a i) (b i)) (Set.Ioo (a j) (b j)))
    (i : ι) (hi : b i < 1) : ∃ j, a j = b i := by
  let J := {j : ι // b i ≤ a j}
  let U : Set ℝ := ⋃ j : J, Set.Icc (a j.val) (b j.val)
  have hU : IsClosed U := isClosed_iUnion_of_finite (fun _ => isClosed_Icc)
  have hsub : Set.Ioo (b i) 1 ⊆ U := by
    intro z hz
    have hz0 : z ∈ Set.Icc (0 : ℝ) 1 := by
      have hi0 := (bounds a b hab hc i).1
      exact ⟨hi0.trans ((hab i).le.trans hz.1.le), hz.2.le⟩
    rw [← hc, Set.mem_iUnion] at hz0
    obtain ⟨j, hj⟩ := hz0
    exact Set.mem_iUnion.mpr ⟨⟨j, left_ge_of_right_endpoint_lt a b hab hd i j hz.1 hj⟩, hj⟩
  have hcl := closure_minimal hsub hU
  rw [closure_Ioo hi.ne] at hcl
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcl ⟨le_rfl, hi.le⟩)
  exact ⟨j.val, le_antisymm hj.1 j.property⟩

theorem endpoint_collision {ι : Type*} [Finite ι] (a b selected : ι → ℝ)
    (hab : ∀ i, a i < b i)
    (hc : (⋃ i, Set.Icc (a i) (b i)) = Set.Icc 0 1)
    (hd : Pairwise fun i j => Disjoint (Set.Ioo (a i) (b i)) (Set.Ioo (a j) (b j)))
    (he : ∀ i, selected i = a i ∨ selected i = b i)
    (h0 : ∀ i, selected i ≠ 0) (h1 : ∀ i, selected i ≠ 1) :
    ∃ i j, i ≠ j ∧ selected i = selected j := by
  classical
  let _ := Fintype.ofFinite ι
  have hzero : (0 : ℝ) ∈ ⋃ i, Set.Icc (a i) (b i) := by rw [hc]; exact ⟨le_rfl, zero_le_one⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hzero
  have hak : a k = 0 := le_antisymm hk.1 (bounds a b hab hc k).1
  have hsk : selected k = b k := (he k).resolve_left (by intro h; exact h0 k (h.trans hak))
  let R : Finset ι := Finset.univ.filter (fun i => selected i = b i)
  have hR : R.Nonempty := ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hsk⟩⟩
  obtain ⟨i, hiR, hmax⟩ := Finset.exists_max_image R b hR
  have hsi : selected i = b i := (Finset.mem_filter.mp hiR).2
  have hi1 : b i < 1 := lt_of_le_of_ne (bounds a b hab hc i).2
    (by intro h; exact h1 i (hsi.trans h))
  obtain ⟨j, hj⟩ := exists_successor a b hab hc hd i hi1
  have hbj : b i < b j := hj ▸ hab j
  have hsj : selected j = a j := (he j).resolve_right (by
    intro h
    have hm := hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
    exact (not_le_of_gt hbj) hm)
  have hij : i ≠ j := by intro h; subst j; exact (hab i).ne hj
  exact ⟨i, j, hij, hsi.trans (hj.symm.trans hsj.symm)⟩

end Erdos633b.IntervalPartition
