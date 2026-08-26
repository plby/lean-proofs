import ErdosProblems.Erdos19.DummyAvailability
import ErdosProblems.Erdos19.DummyInsertion

/-!
# Deterministic dummy assignment from a finite request list

A request `(e, i)` adds one fresh vertex from pool `i` to edge `e`. Rank and
pool-load budgets include all remaining requests, making the greedy induction
exact. The resulting codegree bound is constant when the pool slack is a
fixed positive fraction of the maximum degree.
-/

namespace Erdos19

open Finset Erdos76 Erdos76.FiniteHypergraph

theorem exists_augmentation_by_requests {V E I : Type*}
    [DecidableEq V] [Fintype E] [DecidableEq E] [DecidableEq I]
    (R D L : ℕ) (hD : 0 < D) (hL : 0 < L)
    (P : I → Finset V) (hdisjoint : Pairwise fun i j ↦ Disjoint (P i) (P j))
    (M : I → ℕ)
    (hroom : ∀ i, M i / D + R + R * (R * D / L) < (P i).card)
    (requests : List (E × I)) :
    ∀ H : FiniteHypergraph V E,
      (∀ i, P i ⊆ H.vertexSet) →
      (∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) →
      (∀ x ∈ H.vertexSet, ∀ y ∈ H.vertexSet, x ≠ y → H.edgePairDegree x y ≤ L) →
      (∀ e, (H.support e).card + (requests.map Prod.fst).count e ≤ R) →
      (∀ i, (∑ d ∈ P i, H.edgeDegree d) + (requests.map Prod.snd).count i ≤ M i) →
      ∃ K : FiniteHypergraph V E,
        K.vertexSet = H.vertexSet ∧ (∀ e, H.support e ⊆ K.support e) ∧
        K.IsBounded R ∧ (∀ v ∈ K.vertexSet, K.edgeDegree v ≤ D) ∧
        (∀ x ∈ K.vertexSet, ∀ y ∈ K.vertexSet, x ≠ y → K.edgePairDegree x y ≤ L) ∧
        ∀ e i, (K.support e ∩ P i).card =
          (H.support e ∩ P i).card + requests.count (e, i) := by
  classical
  induction requests with
  | nil =>
    intro H _ hdeg hpair hrank _
    refine ⟨H, rfl, fun _ ↦ Subset.rfl, ?_, hdeg, hpair, ?_⟩
    · intro e
      simpa using hrank e
    · intro e i
      simp
  | cons request rest ih =>
    intro H hpool hdeg hpair hrank hload
    rcases request with ⟨e, i⟩
    have hbound : H.IsBounded R := fun f ↦ (Nat.le_add_right _ _).trans (hrank f)
    have hScard : (H.support e).card ≤ R := hbound e
    have hlocalroom : M i / D + (H.support e).card +
        (H.support e).card * (R * D / L) < (P i).card := by
      have hmul := Nat.mul_le_mul_right (R * D / L) hScard
      exact (Nat.add_le_add (Nat.add_le_add_left hScard _) hmul).trans_lt (hroom i)
    have hcurrentload : (∑ d ∈ P i, H.edgeDegree d) ≤ M i :=
      (Nat.le_add_right _ _).trans (hload i)
    obtain ⟨d, hdP, hfresh, hddeg, hdslack⟩ :=
      exists_dummy_with_degree_and_pairDegree_slack H R D L (M i) hbound hD hL
        (H.support e) (P i) (fun x hx ↦ hdeg x (H.support_subset_vertexSet e hx))
        hcurrentload hlocalroom
    have hd : d ∈ H.vertexSet := hpool i hdP
    let H' := insertToEdge H e d hd
    obtain ⟨hdeg', hpair'⟩ :=
      insertToEdge_preserves_degree_and_pairDegree H e d hd hfresh D L hdeg hddeg hpair hdslack
    have hpoolmem : ∀ j, d ∈ P j ↔ j = i := by
      intro j
      constructor
      · intro hdj
        by_contra hji
        exact (Finset.disjoint_left.mp (hdisjoint hji) hdj) hdP
      · rintro rfl
        exact hdP
    have hrank' : ∀ f, (H'.support f).card + (rest.map Prod.fst).count f ≤ R := by
      intro f
      rw [insertToEdge_support_card H e f d hd hfresh]
      have h := hrank f
      by_cases hfe : f = e
      · subst f
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simpa [List.count_cons, hfe, Ne.symm hfe] using h
    have hload' : ∀ j, (∑ x ∈ P j, H'.edgeDegree x) +
        (rest.map Prod.snd).count j ≤ M j := by
      intro j
      rw [insertToEdge_pool_load H e d hd hfresh]
      have h := hload j
      by_cases hji : j = i
      · subst j
        simpa [hdP, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · have hdnot : d ∉ P j := fun hmem ↦ hji ((hpoolmem j).mp hmem)
        simpa [List.count_cons, hdnot, hji, Ne.symm hji] using h
    obtain ⟨K, hKvertices, hKsupport, hKrank, hKdeg, hKpair, hKcount⟩ :=
      ih H' hpool hdeg' hpair' hrank' hload'
    refine ⟨K, hKvertices, ?_, hKrank, hKdeg, hKpair, ?_⟩
    · intro f
      exact (support_subset_insertToEdge H e f d hd).trans (hKsupport f)
    · intro f j
      rw [hKcount f j, insertToEdge_support_inter_card H e f d hd hfresh]
      by_cases hfe : f = e
      · subst f
        by_cases hji : j = i
        · subst j
          simp [hdP, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        · have hdnot : d ∉ P j := fun hmem ↦ hji ((hpoolmem j).mp hmem)
          simp [List.count_cons, hdnot, hji, Ne.symm hji]
      · simp [List.count_cons, hfe, Ne.symm hfe]

#print axioms exists_augmentation_by_requests

end Erdos19
