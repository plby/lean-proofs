import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Three intervals covering an interval

Three nondegenerate closed subintervals of `[0,L]` that cover `[0,L]` and have
pairwise disjoint open interiors are consecutive after ordering their left
endpoints.  If their lengths agree, their endpoints are the thirds of `[0,L]`.
No adjacency or ordering assumption is needed in the public partition results.
-/

open Set

namespace Puzzling139335.N6.TripleSectors.Angles.Partition

private theorem right_le_left_of_disjoint {a b c d : ℝ}
    (hac : a ≤ c) (hcd : c < d) (h : Disjoint (Ioo a b) (Ioo c d)) : b ≤ c := by
  have hmin := Ioo_disjoint_Ioo.mp h
  rw [max_eq_right hac, min_le_iff] at hmin
  exact hmin.resolve_right (not_le_of_gt hcd)

/-- In increasing left-endpoint order, coverage and disjoint interiors force
the first and last endpoints and the two adjacencies. -/
theorem endpoints_of_sorted_cover {a b : Fin 3 → ℝ} {L : ℝ} (hL : 0 < L)
    (hbounds : ∀ i, 0 ≤ a i ∧ a i < b i ∧ b i ≤ L)
    (hdisjoint : Pairwise fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))
    (hcover : ∀ x ∈ Icc 0 L, ∃ i, x ∈ Icc (a i) (b i))
    (hmono : Monotone a) :
    a 0 = 0 ∧ b 0 = a 1 ∧ b 1 = a 2 ∧ b 2 = L := by
  have h01 : a 0 ≤ a 1 := hmono (by decide)
  have h12 : a 1 ≤ a 2 := hmono (by decide)
  have hgap01 : b 0 ≤ a 1 :=
    right_le_left_of_disjoint h01 (hbounds 1).2.1 (hdisjoint (by decide))
  have hgap12 : b 1 ≤ a 2 :=
    right_le_left_of_disjoint h12 (hbounds 2).2.1 (hdisjoint (by decide))
  have hfirst : a 0 = 0 := by
    obtain ⟨i, hi⟩ := hcover 0 ⟨le_rfl, hL.le⟩
    have h0i : a 0 ≤ a i := hmono (Fin.zero_le i)
    exact le_antisymm (h0i.trans hi.1) (hbounds 0).1
  have hlast : b 2 = L := by
    obtain ⟨i, hi⟩ := hcover L ⟨hL.le, le_rfl⟩
    have hi2 : b i ≤ b 2 := by
      fin_cases i
      · exact hgap01.trans ((hbounds 1).2.1.le.trans
          (hgap12.trans (hbounds 2).2.1.le))
      · exact hgap12.trans (hbounds 2).2.1.le
      · exact le_rfl
    exact le_antisymm (hbounds 2).2.2 (hi.2.trans hi2)
  have hadj01 : b 0 = a 1 := by
    apply le_antisymm hgap01
    by_contra hnot
    have hgap : b 0 < a 1 := lt_of_not_ge hnot
    have hx : (b 0 + a 1) / 2 ∈ Icc 0 L := by
      constructor
      · linarith [(hbounds 0).1, (hbounds 0).2.1]
      · linarith [(hbounds 1).2.1, (hbounds 1).2.2]
    obtain ⟨i, hi⟩ := hcover ((b 0 + a 1) / 2) hx
    fin_cases i
    · change a 0 ≤ (b 0 + a 1) / 2 ∧ (b 0 + a 1) / 2 ≤ b 0 at hi
      linarith [hi.2]
    · change a 1 ≤ (b 0 + a 1) / 2 ∧ (b 0 + a 1) / 2 ≤ b 1 at hi
      linarith [hi.1]
    · change a 2 ≤ (b 0 + a 1) / 2 ∧ (b 0 + a 1) / 2 ≤ b 2 at hi
      linarith [hi.1]
  have hadj12 : b 1 = a 2 := by
    apply le_antisymm hgap12
    by_contra hnot
    have hgap : b 1 < a 2 := lt_of_not_ge hnot
    have hx : (b 1 + a 2) / 2 ∈ Icc 0 L := by
      constructor
      · linarith [(hbounds 1).1, (hbounds 1).2.1]
      · linarith [(hbounds 2).2.1, (hbounds 2).2.2]
    obtain ⟨i, hi⟩ := hcover ((b 1 + a 2) / 2) hx
    fin_cases i
    · change a 0 ≤ (b 1 + a 2) / 2 ∧ (b 1 + a 2) / 2 ≤ b 0 at hi
      linarith [hi.2, (hbounds 1).2.1]
    · change a 1 ≤ (b 1 + a 2) / 2 ∧ (b 1 + a 2) / 2 ≤ b 1 at hi
      linarith [hi.2]
    · change a 2 ≤ (b 1 + a 2) / 2 ∧ (b 1 + a 2) / 2 ≤ b 2 at hi
      linarith [hi.1]
  exact ⟨hfirst, hadj01, hadj12, hlast⟩

/-- Sorting any three intervals gives their actual consecutive order; the
adjacency conclusion is derived from coverage, rather than assumed. -/
theorem exists_consecutive_permutation {a b : Fin 3 → ℝ} {L : ℝ} (hL : 0 < L)
    (hbounds : ∀ i, 0 ≤ a i ∧ a i < b i ∧ b i ≤ L)
    (hdisjoint : Pairwise fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))
    (hcover : ∀ x ∈ Icc 0 L, ∃ i, x ∈ Icc (a i) (b i)) :
    ∃ σ : Equiv.Perm (Fin 3),
      a (σ 0) = 0 ∧ b (σ 0) = a (σ 1) ∧
        b (σ 1) = a (σ 2) ∧ b (σ 2) = L := by
  classical
  let σ := Tuple.sort a
  refine ⟨σ, endpoints_of_sorted_cover (a := a ∘ σ) (b := b ∘ σ) hL
    (fun i => hbounds (σ i)) ?_ ?_ (Tuple.monotone_sort a)⟩
  · intro i j hij
    exact hdisjoint (σ.injective.ne hij)
  · intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    refine ⟨σ.symm i, ?_⟩
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi

/-- Three equal-length intervals with disjoint open interiors covering
`[0,L]` are exactly its three thirds, up to permutation. -/
theorem exists_thirds_permutation {a b : Fin 3 → ℝ} {L : ℝ} (hL : 0 < L)
    (hbounds : ∀ i, 0 ≤ a i ∧ a i < b i ∧ b i ≤ L)
    (hdisjoint : Pairwise fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))
    (hcover : ∀ x ∈ Icc 0 L, ∃ i, x ∈ Icc (a i) (b i))
    (hequal : ∀ i j, b i - a i = b j - a j) :
    ∃ σ : Equiv.Perm (Fin 3),
      a (σ 0) = 0 ∧ b (σ 0) = L / 3 ∧
      a (σ 1) = L / 3 ∧ b (σ 1) = 2 * L / 3 ∧
      a (σ 2) = 2 * L / 3 ∧ b (σ 2) = L := by
  obtain ⟨σ, hfirst, hadj01, hadj12, hlast⟩ :=
    exists_consecutive_permutation hL hbounds hdisjoint hcover
  have hwidth01 := hequal (σ 0) (σ 1)
  have hwidth12 := hequal (σ 1) (σ 2)
  refine ⟨σ, hfirst, ?_, ?_, ?_, ?_, hlast⟩ <;> linarith

/-- Every one of the three congruent angular intervals has width `L/3`. -/
theorem width_eq_third {a b : Fin 3 → ℝ} {L : ℝ} (hL : 0 < L)
    (hbounds : ∀ i, 0 ≤ a i ∧ a i < b i ∧ b i ≤ L)
    (hdisjoint : Pairwise fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))
    (hcover : ∀ x ∈ Icc 0 L, ∃ i, x ∈ Icc (a i) (b i))
    (hequal : ∀ i j, b i - a i = b j - a j) (i : Fin 3) :
    b i - a i = L / 3 := by
  obtain ⟨σ, hfirst, hthird, _⟩ :=
    exists_thirds_permutation hL hbounds hdisjoint hcover hequal
  calc
    b i - a i = b (σ 0) - a (σ 0) := hequal i (σ 0)
    _ = L / 3 := by rw [hfirst, hthird, sub_zero]

end Puzzling139335.N6.TripleSectors.Angles.Partition
