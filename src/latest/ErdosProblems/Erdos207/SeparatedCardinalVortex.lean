/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialVortexTypicality

/-!
# Explicit vortices separated from an absorber

Positive vortex levels consist of the flexible root set together with a
prefix of vertices lying in neither the absorber graph support nor the
absorber bank support.  Thus all positive levels satisfy
`AbsorberSeparatedLevel`, while their free cardinalities are controlled by
an arbitrary antitone schedule.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Every absorber edge is covered by some bank triple (apply the absorption
property to the empty root leave), so its endpoints belong to the bank
support. -/
lemma graphSupportFinset_subset_verticesOn_of_absorptionBank
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    (hA : HasHighGirthAbsorptionBank q H X B) :
    graphSupportFinset H ⊆ verticesOn B := by
  have hsupport : GraphSupportedOn (⊥ : SimpleGraph V) (X : Set V) := by
    intro u v huv
    exact huv.elim
  have hdiv : TriangleDivisible (⊥ : SimpleGraph V) :=
    emptyGraph_triangleDivisible
  obtain ⟨C, hCB, hC⟩ := hA.2 (⊥ : SimpleGraph V) hsupport hdiv
  intro x hx
  obtain ⟨y, hxy⟩ := mem_graphSupportFinset_iff.mp hx
  have hxySup : (H ⊔ (⊥ : SimpleGraph V)).Adj x y := by
    simpa using hxy
  obtain ⟨T, hTC, hxT, _hyT⟩ := (hC.1.2 x y hxySup).exists
  exact mem_biUnion.mpr ⟨T, hCB hTC, hxT⟩

/-- Ambient vertices which are neither roots nor part of either absorber
support. -/
def absorberFreeVertices {n : ℕ} (H : SimpleGraph (Fin n))
    (X : Finset (Fin n)) (B : TripleSystemOn (Fin n)) : Finset (Fin n) :=
  univ \ (X ∪ (graphSupportFinset H ∪ verticesOn B))

/-- The first `r` absorber-free vertices in the canonical order on `Fin n`.
-/
def absorberFreePrefix {n : ℕ} (H : SimpleGraph (Fin n))
    (X : Finset (Fin n)) (B : TripleSystemOn (Fin n)) (r : ℕ) :
    Finset (Fin n) :=
  (((absorberFreeVertices H X B).sort (· ≤ ·)).take r).toFinset

lemma absorberFreePrefix_subset {n r : ℕ} (H : SimpleGraph (Fin n))
    (X : Finset (Fin n)) (B : TripleSystemOn (Fin n)) :
    absorberFreePrefix H X B r ⊆ absorberFreeVertices H X B := by
  intro x hx
  rw [absorberFreePrefix, List.mem_toFinset] at hx
  simpa using List.mem_of_mem_take hx

lemma absorberFreePrefix_mono {n r s : ℕ} (H : SimpleGraph (Fin n))
    (X : Finset (Fin n)) (B : TripleSystemOn (Fin n)) (hrs : r ≤ s) :
    absorberFreePrefix H X B r ⊆ absorberFreePrefix H X B s := by
  intro x hx
  rw [absorberFreePrefix, List.mem_toFinset] at hx ⊢
  exact List.take_subset_take_left
    ((absorberFreeVertices H X B).sort (· ≤ ·)) hrs hx

lemma card_absorberFreePrefix {n r : ℕ} (H : SimpleGraph (Fin n))
    (X : Finset (Fin n)) (B : TripleSystemOn (Fin n)) :
    (absorberFreePrefix H X B r).card =
      min r (absorberFreeVertices H X B).card := by
  have hnodup : ((absorberFreeVertices H X B).sort (· ≤ ·)).Nodup :=
    Finset.sort_nodup _ _
  rw [absorberFreePrefix,
    List.toFinset_card_of_nodup (List.Pairwise.take hnodup),
    List.length_take, Finset.length_sort]

lemma freeSize_le_card_absorberFreeVertices
    {n q C r : ℕ} {H : SimpleGraph (Fin n)} {X : Finset (Fin n)}
    {B : TripleSystemOn (Fin n)}
    (hA : HasHighGirthAbsorptionBank q H X B)
    (hX : X.card ≤ C) (hB : (verticesOn B).card ≤ C)
    (hfit : r + 2 * C ≤ n) :
    r ≤ (absorberFreeVertices H X B).card := by
  have hHsub := graphSupportFinset_subset_verticesOn_of_absorptionBank hA
  have hunion :
      (X ∪ (graphSupportFinset H ∪ verticesOn B)).card ≤ 2 * C := by
    rw [union_eq_right.mpr hHsub]
    calc
      (X ∪ verticesOn B).card ≤ X.card + (verticesOn B).card :=
        card_union_le _ _
      _ ≤ 2 * C := by omega
  have hcard : (absorberFreeVertices H X B).card =
      n - (X ∪ (graphSupportFinset H ∪ verticesOn B)).card := by
    rw [absorberFreeVertices, card_sdiff_of_subset (subset_univ _),
      card_univ, Fintype.card_fin]
  rw [hcard]
  omega

lemma disjoint_absorberFreePrefix_root {n r : ℕ}
    (H : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (B : TripleSystemOn (Fin n)) :
    Disjoint X (absorberFreePrefix H X B r) := by
  rw [Finset.disjoint_left]
  intro x hxX hxFree
  have hx := absorberFreePrefix_subset (r := r) H X B hxFree
  exact (mem_sdiff.mp hx).2 (mem_union_left _ hxX)

/-- The vortex with ambient level zero and absorber-separated positive
levels having the scheduled numbers of free vertices. -/
def separatedCardinalVortex {n ell : ℕ}
    (H : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (B : TripleSystemOn (Fin n))
    (freeSize : Fin (ell + 1) → ℕ) (hanti : Antitone freeSize) :
    Vortex (Fin n) ell where
  U i := if i = 0 then univ else X ∪ absorberFreePrefix H X B (freeSize i)
  root := by simp
  antitone := by
    intro i j hij
    by_cases hi : i = 0
    · subst i
      simp
    have hj : j ≠ 0 := by
      intro hj
      subst j
      apply hi
      exact Fin.le_antisymm hij (Fin.zero_le i)
    simp only [hi, hj, ↓reduceIte]
    exact union_subset_union_right
      (absorberFreePrefix_mono H X B (hanti hij))

@[simp]
lemma separatedCardinalVortex_U_zero {n ell : ℕ}
    (H : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (B : TripleSystemOn (Fin n))
    (freeSize : Fin (ell + 1) → ℕ) (hanti : Antitone freeSize) :
    (separatedCardinalVortex H X B freeSize hanti).U 0 = univ := by
  simp [separatedCardinalVortex]

lemma separatedCardinalVortex_U_of_ne_zero {n ell : ℕ}
    (H : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (B : TripleSystemOn (Fin n))
    (freeSize : Fin (ell + 1) → ℕ) (hanti : Antitone freeSize)
    {i : Fin (ell + 1)} (hi : i ≠ 0) :
    (separatedCardinalVortex H X B freeSize hanti).U i =
      X ∪ absorberFreePrefix H X B (freeSize i) := by
  simp [separatedCardinalVortex, hi]

lemma separatedCardinalVortex_separated {n ell : ℕ}
    (H : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (B : TripleSystemOn (Fin n))
    (freeSize : Fin (ell + 1) → ℕ) (hanti : Antitone freeSize)
    {i : Fin (ell + 1)} (hi : i ≠ 0) :
    AbsorberSeparatedLevel H X B
      ((separatedCardinalVortex H X B freeSize hanti).U i) := by
  rw [separatedCardinalVortex_U_of_ne_zero H X B freeSize hanti hi]
  constructor
  · exact subset_union_left
  · intro x hxU hxX
    have hxPrefix : x ∈ absorberFreePrefix H X B (freeSize i) :=
      (mem_union.mp hxU).resolve_left hxX
    have hxFree := absorberFreePrefix_subset (r := freeSize i) H X B hxPrefix
    have hxNot := (mem_sdiff.mp hxFree).2
    constructor
    · intro hxH
      exact hxNot (mem_union_right X (mem_union_left _ hxH))
    · intro hxB
      exact hxNot (mem_union_right X (mem_union_right _ hxB))

lemma card_separatedCardinalVortex_of_capacity {n ell : ℕ}
    (H : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (B : TripleSystemOn (Fin n))
    (freeSize : Fin (ell + 1) → ℕ) (hanti : Antitone freeSize)
    {i : Fin (ell + 1)} (hi : i ≠ 0)
    (hcap : freeSize i ≤ (absorberFreeVertices H X B).card) :
    ((separatedCardinalVortex H X B freeSize hanti).U i).card =
      X.card + freeSize i := by
  rw [separatedCardinalVortex_U_of_ne_zero H X B freeSize hanti hi,
    card_union_of_disjoint
      (disjoint_absorberFreePrefix_root (r := freeSize i) H X B),
    card_absorberFreePrefix, min_eq_left hcap]

lemma separatedCardinalVortex_U_last {n ell : ℕ} (hell : 0 < ell)
    (H : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (B : TripleSystemOn (Fin n))
    (freeSize : Fin (ell + 1) → ℕ) (hanti : Antitone freeSize)
    (hlast : freeSize (Fin.last ell) = 0) :
    (separatedCardinalVortex H X B freeSize hanti).U (Fin.last ell) = X := by
  have hlast0 : (Fin.last ell : Fin (ell + 1)) ≠ 0 := by
    intro heq
    have hval := congrArg Fin.val heq
    simp only [Fin.val_last, Fin.val_zero] at hval
    omega
  rw [separatedCardinalVortex_U_of_ne_zero H X B freeSize hanti hlast0,
    hlast, absorberFreePrefix]
  simp

lemma separatedCardinalVortex_nonempty {n ell : ℕ}
    (H : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (B : TripleSystemOn (Fin n))
    (freeSize : Fin (ell + 1) → ℕ) (hanti : Antitone freeSize)
    (hX : X.Nonempty) :
    ∀ i, ((separatedCardinalVortex H X B freeSize hanti).U i).Nonempty := by
  intro i
  by_cases hi : i = 0
  · subst i
    obtain ⟨x, hx⟩ := hX
    exact ⟨x, mem_univ x⟩
  · rw [separatedCardinalVortex_U_of_ne_zero H X B freeSize hanti hi]
    exact hX.mono subset_union_left

end

end Erdos207
