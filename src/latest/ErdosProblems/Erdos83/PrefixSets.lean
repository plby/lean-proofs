import Mathlib

/-!
# Prefix and tail sets for Erdős Problem 83

This file packages the elementary finite-set combinatorics used by the
specialized Ahlswede--Khachatrian defect argument.  The first `ell` points of
`Fin N` form `«prefix» N ell`; the remaining points form `tailAfter N ell`.
-/

namespace Erdos83

open Finset

/-- The first `ell` elements of `Fin N`.  When `ell ≤ N`, this has exactly
`ell` elements. -/
def «prefix» (N ell : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun x ↦ x.val < ell

/-- The elements of `Fin N` at or after position `ell`. -/
def tailAfter (N ell : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun x ↦ ell ≤ x.val

@[simp] theorem mem_prefix {N ell : ℕ} {x : Fin N} :
    x ∈ «prefix» N ell ↔ x.val < ell := by
  simp [«prefix»]

@[simp] theorem mem_tailAfter {N ell : ℕ} {x : Fin N} :
    x ∈ tailAfter N ell ↔ ell ≤ x.val := by
  simp [tailAfter]

theorem prefix_subset_univ (N ell : ℕ) :
    «prefix» N ell ⊆ (Finset.univ : Finset (Fin N)) := by
  simp

theorem tailAfter_subset_univ (N ell : ℕ) :
    tailAfter N ell ⊆ (Finset.univ : Finset (Fin N)) := by
  simp

/-- The «prefix» has its expected cardinality whenever its endpoint is in the
ambient range. -/
theorem card_prefix {N ell : ℕ} (h : ell ≤ N) :
    («prefix» N ell).card = ell := by
  let hlt : ∀ m ∈ Finset.range ell, m < N := by
    intro m hm
    exact (Finset.mem_range.mp hm).trans_le h
  have hp : «prefix» N ell = (Finset.range ell).attachFin hlt := by
    ext x
    simp only [mem_prefix, Finset.mem_attachFin, Finset.mem_range]
  rw [hp, Finset.card_attachFin, Finset.card_range]

/-- Alias with the definition-first naming order. -/
theorem prefix_card {N ell : ℕ} (h : ell ≤ N) :
    («prefix» N ell).card = ell :=
  card_prefix h

theorem tailAfter_eq_univ_sdiff (N ell : ℕ) :
    tailAfter N ell = (Finset.univ : Finset (Fin N)) \ «prefix» N ell := by
  ext x
  simp only [mem_tailAfter, Finset.mem_sdiff, Finset.mem_univ, true_and, mem_prefix]
  omega

/-- The tail has the complementary cardinality. -/
theorem card_tailAfter {N ell : ℕ} (h : ell ≤ N) :
    (tailAfter N ell).card = N - ell := by
  rw [tailAfter_eq_univ_sdiff]
  simpa [card_prefix h] using
    (Finset.card_sdiff_of_subset (prefix_subset_univ N ell))

/-- Alias with the definition-first naming order. -/
theorem tailAfter_card {N ell : ℕ} (h : ell ≤ N) :
    (tailAfter N ell).card = N - ell :=
  card_tailAfter h

theorem disjoint_prefix_tailAfter (N ell : ℕ) :
    Disjoint («prefix» N ell) (tailAfter N ell) := by
  rw [tailAfter_eq_univ_sdiff]
  exact Finset.disjoint_sdiff

theorem prefix_disjoint_tailAfter (N ell : ℕ) :
    Disjoint («prefix» N ell) (tailAfter N ell) :=
  disjoint_prefix_tailAfter N ell

@[simp] theorem prefix_inter_tailAfter (N ell : ℕ) :
    «prefix» N ell ∩ tailAfter N ell = ∅ := by
  exact Finset.disjoint_iff_inter_eq_empty.mp (disjoint_prefix_tailAfter N ell)

@[simp] theorem tailAfter_inter_prefix (N ell : ℕ) :
    tailAfter N ell ∩ «prefix» N ell = ∅ := by
  rw [Finset.inter_comm, prefix_inter_tailAfter]

theorem prefix_union_tailAfter (N ell : ℕ) :
    «prefix» N ell ∪ tailAfter N ell = (Finset.univ : Finset (Fin N)) := by
  ext x
  simp only [Finset.mem_union, mem_prefix, mem_tailAfter, Finset.mem_univ,
    iff_true]
  omega

theorem tailAfter_union_prefix (N ell : ℕ) :
    tailAfter N ell ∪ «prefix» N ell = (Finset.univ : Finset (Fin N)) := by
  rw [Finset.union_comm, prefix_union_tailAfter]

/-- Every finite set is reconstructed from its «prefix» and tail pieces. -/
theorem inter_prefix_union_inter_tailAfter {N ell : ℕ}
    (S : Finset (Fin N)) :
    (S ∩ «prefix» N ell) ∪ (S ∩ tailAfter N ell) = S := by
  ext x
  by_cases hx : x.val < ell
  · simp [hx]
  · have hxe : ell ≤ x.val := Nat.le_of_not_gt hx
    simp [hx, hxe]

/-- The two pieces in the preceding decomposition are disjoint. -/
theorem disjoint_inter_prefix_inter_tailAfter {N ell : ℕ}
    (S : Finset (Fin N)) :
    Disjoint (S ∩ «prefix» N ell) (S ∩ tailAfter N ell) := by
  exact (disjoint_prefix_tailAfter N ell).mono Finset.inter_subset_right
    Finset.inter_subset_right

/-- Cardinality splits as the sum of the «prefix» and tail cardinalities. -/
theorem card_inter_prefix_add_card_inter_tailAfter {N ell : ℕ}
    (S : Finset (Fin N)) :
    (S ∩ «prefix» N ell).card + (S ∩ tailAfter N ell).card = S.card := by
  rw [← Finset.card_union_of_disjoint
    (disjoint_inter_prefix_inter_tailAfter S),
    inter_prefix_union_inter_tailAfter]

/-- Unioning a «prefix» part and a tail part and then restricting to the «prefix»
recovers the «prefix» part. -/
theorem union_inter_prefix {N ell : ℕ} {A B : Finset (Fin N)}
    (hA : A ⊆ «prefix» N ell) (hB : B ⊆ tailAfter N ell) :
    (A ∪ B) ∩ «prefix» N ell = A := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxAB, hxp⟩
    rcases Finset.mem_union.mp hxAB with hxA | hxB
    · exact hxA
    · have hxt := hB hxB
      exact ((Finset.disjoint_left.mp (disjoint_prefix_tailAfter N ell)) hxp hxt).elim
  · intro hxA
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hxA, hA hxA⟩

/-- The tail analogue of `union_inter_prefix`. -/
theorem union_inter_tailAfter {N ell : ℕ} {A B : Finset (Fin N)}
    (hA : A ⊆ «prefix» N ell) (hB : B ⊆ tailAfter N ell) :
    (A ∪ B) ∩ tailAfter N ell = B := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxAB, hxt⟩
    rcases Finset.mem_union.mp hxAB with hxA | hxB
    · have hxp := hA hxA
      exact ((Finset.disjoint_left.mp (disjoint_prefix_tailAfter N ell)) hxp hxt).elim
    · exact hxB
  · intro hxB
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hxB, hB hxB⟩

/-- Inclusion--exclusion gives the universal lower bound on the intersection
of two subsets of an `ell`-point «prefix». -/
theorem prefix_inter_card_lower_bound {N ell a b : ℕ}
    {A B : Finset (Fin N)} (hN : ell ≤ N)
    (hA : A ⊆ «prefix» N ell) (hB : B ⊆ «prefix» N ell)
    (hAcard : A.card = a) (hBcard : B.card = b) :
    a + b - ell ≤ (A ∩ B).card := by
  have hUnion : A ∪ B ⊆ «prefix» N ell := Finset.union_subset hA hB
  have hUnionCard : (A ∪ B).card ≤ ell := by
    simpa [card_prefix hN] using Finset.card_le_card hUnion
  have hIE := Finset.card_union_add_card_inter A B
  omega

/-- Given a `b`-subset of an `ell`-point «prefix», any feasible `a` admits a
«prefix» subset meeting it in at most one point.

The proof first uses points outside `B`.  If there are not quite enough,
the numerical hypothesis says that exactly one point of `B` is needed. -/
theorem exists_prefix_subset_card_inter_le_one {N ell a b : ℕ}
    (hN : ell ≤ N) (B : Finset (Fin N))
    (hB : B ⊆ «prefix» N ell) (hBcard : B.card = b)
    (ha : a ≤ ell) (hab : a + b ≤ ell + 1) :
    ∃ A : Finset (Fin N),
      A ⊆ «prefix» N ell ∧ A.card = a ∧ (A ∩ B).card ≤ 1 := by
  have hb : b ≤ ell := by
    have := Finset.card_le_card hB
    simpa [hBcard, card_prefix hN] using this
  let C := «prefix» N ell \ B
  have hCcard : C.card = ell - b := by
    dsimp [C]
    simpa [hBcard, card_prefix hN] using Finset.card_sdiff_of_subset hB
  by_cases hac : a ≤ ell - b
  · have hacard : a ≤ C.card := by simpa [hCcard] using hac
    obtain ⟨A, hAC, hAcard⟩ := Finset.exists_subset_card_eq hacard
    refine ⟨A, hAC.trans Finset.sdiff_subset, hAcard, ?_⟩
    have hdisj : Disjoint A B := by
      refine Finset.disjoint_left.mpr ?_
      intro x hxA hxB'
      exact (Finset.mem_sdiff.mp (hAC hxA)).2 hxB'
    rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj]
    simp
  · have haeq : a = ell - b + 1 := by omega
    have hbpos : 0 < B.card := by
      rw [hBcard]
      omega
    obtain ⟨x, hxB⟩ := Finset.card_pos.mp hbpos
    let A := C ∪ {x}
    have hxPrefix : x ∈ «prefix» N ell := hB hxB
    have hxC : x ∉ C := by
      simp [C, hxB]
    have hdisj : Disjoint C ({x} : Finset (Fin N)) := by
      exact Finset.disjoint_singleton_right.mpr hxC
    have hAcard : A.card = a := by
      simp only [A, Finset.card_union_of_disjoint hdisj, hCcard,
        Finset.card_singleton]
      omega
    have hAinter : A ∩ B = {x} := by
      ext y
      simp [A, C, hxB]
    refine ⟨A, ?_, hAcard, ?_⟩
    · exact Finset.union_subset Finset.sdiff_subset
        (Finset.singleton_subset_iff.mpr hxPrefix)
    · rw [hAinter]
      simp

end Erdos83
