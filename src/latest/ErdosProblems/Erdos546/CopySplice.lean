/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos546.Basic

/-!
# Erdős Problem 546: deletion and copy splicing

This file contains the two elementary pieces of finite-graph bookkeeping used
to pass from a bounded-degree induced subgraph back to the original graph.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos546

open Finset
open SimpleGraph

/-! ## Splicing copies across a monochromatic pair -/

/-- If the exceptional vertices of `G` inject into the clique side `X` of a
monochromatic pair, while the graph induced by the remaining vertices has a
copy in `Y`, then the whole graph has a copy in the ambient graph.  Containment
is ordinary (not induced), so extra edges inside `X`, across `X,Y`, or in `Y`
are harmless. -/
theorem isContained_of_monoPair_of_induce_isContained
    {v N : ℕ} {G : SimpleGraph (Fin v)} {H : SimpleGraph (Fin N)}
    {A : Finset (Fin v)} {X Y : Finset (Fin N)}
    (hXY : MonoPair H X Y)
    (fA : (↑A : Set (Fin v)) ↪ (↑X : Set (Fin N)))
    (hrest : G.induce (↑A : Set (Fin v))ᶜ ⊑ H.induce (↑Y : Set (Fin N))) :
    G ⊑ H := by
  classical
  rcases hrest with ⟨fY⟩
  let f : Fin v → Fin N := fun a ↦
    if ha : a ∈ A then (fA ⟨a, ha⟩ : Fin N)
    else (fY ⟨a, by simpa using ha⟩ : Fin N)
  have hfA (a : Fin v) (ha : a ∈ A) : f a = fA ⟨a, ha⟩ := by
    simp [f, ha]
  have hfY (a : Fin v) (ha : a ∉ A) : f a = fY ⟨a, by simpa using ha⟩ := by
    simp [f, ha]
  have hf_injective : Function.Injective f := by
    intro a b hab
    by_cases ha : a ∈ A
    · by_cases hb : b ∈ A
      · rw [hfA a ha, hfA b hb] at hab
        exact congrArg Subtype.val (fA.injective (Subtype.ext hab))
      · rw [hfA a ha, hfY b hb] at hab
        have hfa : (fA ⟨a, ha⟩ : Fin N) ∈ X := (fA ⟨a, ha⟩).property
        have hfb : (fY ⟨b, by simpa using hb⟩ : Fin N) ∈ Y :=
          (fY ⟨b, by simpa using hb⟩).property
        exact False.elim (Finset.disjoint_left.mp hXY.1 hfa (hab ▸ hfb))
    · by_cases hb : b ∈ A
      · rw [hfY a ha, hfA b hb] at hab
        have hfa : (fY ⟨a, by simpa using ha⟩ : Fin N) ∈ Y :=
          (fY ⟨a, by simpa using ha⟩).property
        have hfb : (fA ⟨b, hb⟩ : Fin N) ∈ X := (fA ⟨b, hb⟩).property
        exact False.elim (Finset.disjoint_left.mp hXY.1 hfb (hab ▸ hfa))
      · rw [hfY a ha, hfY b hb] at hab
        exact congrArg Subtype.val (fY.injective (Subtype.ext hab))
  refine ⟨⟨⟨f, ?_⟩, hf_injective⟩⟩
  intro a b hab
  by_cases ha : a ∈ A
  · by_cases hb : b ∈ A
    · rw [hfA a ha, hfA b hb]
      apply hXY.2.1 (fA ⟨a, ha⟩).property (fA ⟨b, hb⟩).property
      intro heq
      exact hab.ne (congrArg Subtype.val (fA.injective (Subtype.ext heq)))
    · rw [hfA a ha, hfY b hb]
      exact hXY.2.2 _ (fA ⟨a, ha⟩).property _
        (fY ⟨b, by simpa using hb⟩).property
  · by_cases hb : b ∈ A
    · rw [hfY a ha, hfA b hb]
      exact (hXY.2.2 _ (fA ⟨b, hb⟩).property _
        (fY ⟨a, by simpa using ha⟩).property).symm
    · rw [hfY a ha, hfY b hb]
      exact fY.toHom.map_rel' hab

/-- Cardinality-based form of
`isContained_of_monoPair_of_induce_isContained`, convenient when a preceding
argument only supplies a lower bound on the size of the clique side. -/
theorem isContained_of_monoPair_of_card_le_of_induce_isContained
    {v N : ℕ} {G : SimpleGraph (Fin v)} {H : SimpleGraph (Fin N)}
    {A : Finset (Fin v)} {X Y : Finset (Fin N)}
    (hXY : MonoPair H X Y)
    (hAX : A.card ≤ X.card)
    (hrest : G.induce (↑A : Set (Fin v))ᶜ ⊑ H.induce (↑Y : Set (Fin N))) :
    G ⊑ H := by
  have hcard : Fintype.card (↑A : Set (Fin v)) ≤
      Fintype.card (↑X : Set (Fin N)) := by
    simpa using hAX
  exact isContained_of_monoPair_of_induce_isContained hXY
    (Function.Embedding.nonempty_of_card_le hcard).some hrest

/-! ## High-degree deletion -/

/-- Restricting a finite graph to a set cannot increase the degree of a
remaining vertex. -/
theorem degree_induce_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Set V) [DecidablePred (· ∈ S)] (x : S) :
    (G.induce S).degree x ≤ G.degree x := by
  classical
  change #((G.induce S).neighborFinset x) ≤ #(G.neighborFinset x)
  calc
    #((G.induce S).neighborFinset x) =
        #(((G.induce S).neighborFinset x).map (.subtype (· ∈ S))) :=
      (card_map _).symm
    _ = #(G.neighborFinset x ∩ S.toFinset) := by
      rw [G.map_neighborFinset_induce x]
    _ ≤ #(G.neighborFinset x) := Finset.card_le_card inter_subset_left

/-- Delete every vertex of degree greater than `D`.  If the degree-sum bound
places fewer than `k+1` such vertices in the graph, at most `k` vertices are
deleted, and the remaining induced graph has maximum degree at most `D`.

The numerical hypothesis is the denominator-free threshold estimate
`2m < (D+1)(k+1)`, where `m` is the number of edges. -/
theorem exists_deleted_card_le_and_maxDegree_induce_le
    {v D k m : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (hm : G.edgeFinset.card = m)
    (hthreshold : 2 * m < (D + 1) * (k + 1)) :
    ∃ A : Finset (Fin v), A.card ≤ k ∧
      (G.induce (↑A : Set (Fin v))ᶜ).maxDegree ≤ D := by
  classical
  let A : Finset (Fin v) := Finset.univ.filter fun x ↦ D < G.degree x
  refine ⟨A, ?_, ?_⟩
  · have hlow : (D + 1) * A.card ≤ ∑ x ∈ A, G.degree x := by
      simpa [Nat.mul_comm] using
        (Finset.card_nsmul_le_sum A (fun x ↦ G.degree x) (D + 1) fun x hx ↦ by
          have hx' : D < G.degree x := by simpa [A] using hx
          omega)
    have hsum : ∑ x ∈ A, G.degree x ≤ 2 * m := by
      calc
        ∑ x ∈ A, G.degree x ≤ ∑ x : Fin v, G.degree x :=
          Finset.sum_le_sum_of_subset (by simp [A])
        _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
        _ = 2 * m := by rw [hm]
    have : (D + 1) * A.card < (D + 1) * (k + 1) :=
      lt_of_le_of_lt (hlow.trans hsum) hthreshold
    exact Nat.le_of_lt_succ (lt_of_mul_lt_mul_left' this)
  · apply (G.induce (↑A : Set (Fin v))ᶜ).maxDegree_le_of_forall_degree_le
    intro x
    refine (degree_induce_le G _ x).trans ?_
    have hx : x.1 ∉ A := x.2
    have hx' : ¬ D < G.degree x := by simpa [A] using hx
    omega

end Erdos546
