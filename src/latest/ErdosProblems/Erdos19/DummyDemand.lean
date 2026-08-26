import ErdosProblems.Erdos19.DummyAssignment
import Mathlib.Data.Finsupp.Multiset

/-! # Dummy assignment for a matrix of incidence demands -/

namespace Erdos19

open Finset Erdos76 Erdos76.FiniteHypergraph

theorem count_map_fst_eq_sum_count {E I : Type*} [DecidableEq E] [Fintype I]
    [DecidableEq I] (requests : List (E × I)) (e : E) :
    (requests.map Prod.fst).count e = ∑ i : I, requests.count (e, i) := by
  induction requests with
  | nil => simp
  | cons p rest ih =>
    rcases p with ⟨f, j⟩
    by_cases hfe : f = e
    · subst f
      simp [List.count_cons, ih, sum_add_distrib]
    · simp [List.count_cons, ih, hfe, sum_add_distrib]

theorem count_map_snd_eq_sum_count {E I : Type*} [Fintype E] [DecidableEq E]
    [DecidableEq I] (requests : List (E × I)) (i : I) :
    (requests.map Prod.snd).count i = ∑ e : E, requests.count (e, i) := by
  induction requests with
  | nil => simp
  | cons p rest ih =>
    rcases p with ⟨f, j⟩
    by_cases hji : j = i
    · subst j
      simp [List.count_cons, ih, sum_add_distrib]
    · simp [List.count_cons, ih, hji, sum_add_distrib]

theorem exists_requests_of_demands {E I : Type*} [Fintype E] [DecidableEq E]
    [Fintype I] [DecidableEq I] (a : E → I → ℕ) :
    ∃ requests : List (E × I),
      (∀ e i, requests.count (e, i) = a e i) ∧
      (∀ e, (requests.map Prod.fst).count e = ∑ i : I, a e i) ∧
      (∀ i, (requests.map Prod.snd).count i = ∑ e : E, a e i) := by
  classical
  let weights : (E × I) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun p ↦ a p.1 p.2)
  let requests := weights.toMultiset.toList
  have hcount : ∀ e i, requests.count (e, i) = a e i := by
    intro e i
    calc
      requests.count (e, i) = (requests : Multiset (E × I)).count (e, i) := by
        simp only [Multiset.count, Multiset.coe_countP, List.count]
        apply List.countP_congr
        intro p _
        simp only [beq_iff_eq, decide_eq_true_eq]
        exact eq_comm
      _ = weights.toMultiset.count (e, i) := by rw [Multiset.coe_toList]
      _ = a e i := by rw [Finsupp.count_toMultiset]; rfl
  refine ⟨requests, hcount, ?_, ?_⟩
  · intro e
    rw [count_map_fst_eq_sum_count]
    exact sum_congr rfl fun i _ ↦ hcount e i
  · intro i
    rw [count_map_snd_eq_sum_count]
    exact sum_congr rfl fun e _ ↦ hcount e i

/-- Simultaneously meet every prescribed edge-pool incidence demand, without
random choices. The exact budgets are expressed entirely as finite sums. -/
theorem exists_augmentation_of_demands {V E I : Type*}
    [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (H : FiniteHypergraph V E) (R D L : ℕ) (hD : 0 < D) (hL : 0 < L)
    (P : I → Finset V) (hdisjoint : Pairwise fun i j ↦ Disjoint (P i) (P j))
    (hpool : ∀ i, P i ⊆ H.vertexSet) (M : I → ℕ) (a : E → I → ℕ)
    (hroom : ∀ i, M i / D + R + R * (R * D / L) < (P i).card)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hpair : ∀ x ∈ H.vertexSet, ∀ y ∈ H.vertexSet, x ≠ y → H.edgePairDegree x y ≤ L)
    (hrank : ∀ e, (H.support e).card + ∑ i : I, a e i ≤ R)
    (hload : ∀ i, (∑ d ∈ P i, H.edgeDegree d) + ∑ e : E, a e i ≤ M i) :
    ∃ K : FiniteHypergraph V E,
      K.vertexSet = H.vertexSet ∧ (∀ e, H.support e ⊆ K.support e) ∧
      K.IsBounded R ∧ (∀ v ∈ K.vertexSet, K.edgeDegree v ≤ D) ∧
      (∀ x ∈ K.vertexSet, ∀ y ∈ K.vertexSet, x ≠ y → K.edgePairDegree x y ≤ L) ∧
      ∀ e i, (K.support e ∩ P i).card = (H.support e ∩ P i).card + a e i := by
  obtain ⟨requests, hcount, hfst, hsnd⟩ := exists_requests_of_demands a
  obtain ⟨K, hKvertices, hKsupport, hKrank, hKdeg, hKpair, hKcount⟩ :=
    exists_augmentation_by_requests R D L hD hL P hdisjoint M hroom requests H hpool hdeg hpair
      (by simpa only [hfst] using hrank) (by simpa only [hsnd] using hload)
  refine ⟨K, hKvertices, hKsupport, hKrank, hKdeg, hKpair, ?_⟩
  intro e i
  simpa only [hcount] using hKcount e i

#print axioms exists_augmentation_of_demands

end Erdos19
