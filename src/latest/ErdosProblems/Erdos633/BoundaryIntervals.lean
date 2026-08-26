import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# A finite marked-interval obstruction

A partition of a closed interval into nondegenerate intervals cannot mark
one endpoint of each piece injectively while avoiding both outer endpoints.
The proof follows the right-pointing intervals and uses finite extrema.
-/

namespace Erdos633

theorem interval_partition_right_neighbor {ι : Type*} [Finite ι]
    (l r : ι → ℝ) (hpos : ∀ i, l i < r i)
    (hbound : ∀ i, 0 ≤ l i ∧ r i ≤ 1)
    (hcover : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ i, x ∈ Set.Icc (l i) (r i))
    (hdisj : Pairwise fun i j => Disjoint (Set.Ioo (l i) (r i)) (Set.Ioo (l j) (r j)))
    (i : ι) (hi : r i < 1) :
    ∃ j, l j = r i ∧ r i < r j := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let s := Finset.univ.filter fun j => r i < r j
  have hs : s.Nonempty := by
    obtain ⟨j, hj⟩ := hcover 1 (by simp)
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, by linarith [hj.2]⟩⟩
  obtain ⟨j, hj, hmin⟩ := s.exists_min_image l hs
  have hrij : r i < r j := (Finset.mem_filter.mp hj).2
  have hlj : l j ≤ r i := by
    by_contra h
    have hlt : r i < l j := lt_of_not_ge h
    let x := (r i + l j) / 2
    have hri0 : 0 ≤ r i := le_trans (hbound i).1 (hpos i).le
    have hlj1 : l j ≤ 1 := le_trans (hpos j).le (hbound j).2
    have hx : x ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp [x]
      constructor <;> linarith
    obtain ⟨k, hk⟩ := hcover x hx
    have hks : k ∈ s := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ k, ?_⟩
      dsimp [x] at hk
      linarith [hk.2]
    have hm := hmin k hks
    dsimp [x] at hk
    linarith [hk.1]
  have hij : i ≠ j := by
    intro h
    subst j
    exact (lt_irrefl _ hrij)
  have hd := Set.Ioo_disjoint_Ioo.mp (hdisj hij)
  rw [min_eq_left hrij.le, le_max_iff] at hd
  exact ⟨j, le_antisymm hlj (hd.resolve_left (not_le_of_gt (hpos i))), hrij⟩

theorem no_injective_interior_endpoint_marks {ι : Type*} [Finite ι]
    (l r g : ι → ℝ) (hpos : ∀ i, l i < r i)
    (hbound : ∀ i, 0 ≤ l i ∧ r i ≤ 1)
    (hcover : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ i, x ∈ Set.Icc (l i) (r i))
    (hdisj : Pairwise fun i j => Disjoint (Set.Ioo (l i) (r i)) (Set.Ioo (l j) (r j)))
    (hmark : ∀ i, g i = l i ∨ g i = r i)
    (hinterior : ∀ i, g i ∈ Set.Ioo (0 : ℝ) 1)
    (hinj : Function.Injective g) : False := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let s := Finset.univ.filter fun i => g i = r i
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hcover 0 (by simp)
    have hl : l i = 0 := le_antisymm hi.1 (hbound i).1
    have hm : g i = r i := (hmark i).resolve_left (by
      intro h
      have hp := (hinterior i).1
      rw [h, hl] at hp
      exact lt_irrefl _ hp)
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hm⟩⟩
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image g hs
  have hgi : g i = r i := (Finset.mem_filter.mp hi).2
  have hri : r i < 1 := hgi ▸ (hinterior i).2
  obtain ⟨j, hlj, hrij⟩ := interval_partition_right_neighbor l r hpos hbound hcover hdisj i hri
  have hij : i ≠ j := by
    intro h
    subst j
    exact lt_irrefl _ hrij
  have hgj : g j = r j := (hmark j).resolve_left (by
    intro h
    have heq : g i = g j := by rw [hgi, h, hlj]
    exact hij (hinj heq))
  have hm := hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hgj⟩)
  rw [hgi, hgj] at hm
  exact (not_le_of_gt hrij) hm

end Erdos633
