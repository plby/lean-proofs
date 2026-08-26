import ErdosProblems.Erdos547.VertexPairing
import Mathlib.Combinatorics.Hall.Finite

/-!
# Hall's condition from weighted pairs of parents
-/

namespace Erdos547

open Finset SimpleGraph

open scoped Classical in
theorem weighted_hall_of_pairing {U V : Type*} [Fintype U]
    (P : SimpleGraph U) (w : U → ℕ) (L b : ℕ) (candidates : U → Finset V)
    (htotal : (∑ u, w u) ≤ L)
    (hweight : ∀ J : Finset U, (∀ u ∈ J, ∀ v ∈ J, ¬ P.Adj u v) →
      2 * (∑ u ∈ J, w u) ≤ L + b)
    (hsingle : ∀ u, L + b ≤ 2 * (candidates u).card)
    (hpair : ∀ u v, P.Adj u v → L ≤ (candidates u ∪ candidates v).card) :
    ∀ J : Finset U, (∑ u ∈ J, w u) ≤ (J.biUnion candidates).card := by
  classical
  intro J
  by_cases hp : ∃ u ∈ J, ∃ v ∈ J, P.Adj u v
  · obtain ⟨u, hu, v, hv, huv⟩ := hp
    have hsum : (∑ x ∈ J, w x) ≤ L :=
      (Finset.sum_le_sum_of_subset (Finset.subset_univ J)).trans htotal
    have hsub : candidates u ∪ candidates v ⊆ J.biUnion candidates := by
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact Finset.mem_biUnion.mpr ⟨u, hu, hz⟩
      · exact Finset.mem_biUnion.mpr ⟨v, hv, hz⟩
    exact hsum.trans ((hpair u v huv).trans (Finset.card_le_card hsub))
  · have hind : ∀ u ∈ J, ∀ v ∈ J, ¬ P.Adj u v :=
      fun u hu v hv huv ↦ hp ⟨u, hu, v, hv, huv⟩
    by_cases hJ : J.Nonempty
    · obtain ⟨u, hu⟩ := hJ
      have hweightJ := hweight J hind
      have hcap := hsingle u
      have hsum : (∑ x ∈ J, w x) ≤ (candidates u).card := by omega
      apply hsum.trans
      apply Finset.card_le_card
      intro z hz
      exact Finset.mem_biUnion.mpr ⟨u, hu, hz⟩
    · simp [Finset.not_nonempty_iff_eq_empty.mp hJ]

/-- The full multiplicity of leaves at a parent. -/
noncomputable def parentWeight {L U : Type*} [Fintype L] (parent : L → U) (u : U) : ℕ := by
  classical
  exact ((Finset.univ : Finset L).filter fun x ↦ parent x = u).card

theorem sum_parentWeight {L U : Type*} [Fintype L] [Fintype U] (parent : L → U) :
    (∑ u, parentWeight parent u) = Fintype.card L := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := parent)
    (s := (Finset.univ : Finset L)) (t := (Finset.univ : Finset U))
    (fun _ _ ↦ Finset.mem_univ _)
  simpa only [Finset.card_univ, parentWeight] using h.symm

open scoped Classical in
/-- Weighted Hall on parents implies the ordinary Hall condition on leaves,
with every repeated parent counted at its full multiplicity. -/
theorem leaf_hall_of_parent_capacity {L U V : Type*} [Fintype L]
    (parent : L → U) (candidates : U → Finset V)
    (hweighted : ∀ J : Finset U, (∑ u ∈ J, parentWeight parent u) ≤ (J.biUnion candidates).card) :
    ∀ X : Finset L, X.card ≤ (X.biUnion fun x ↦ candidates (parent x)).card := by
  classical
  intro X
  let J := X.image parent
  have hcount : X.card ≤ ∑ u ∈ J, parentWeight parent u := by
    rw [Finset.card_eq_sum_card_image parent X]
    apply Finset.sum_le_sum
    intro u _
    exact Finset.card_le_card (Finset.filter_subset_filter (fun x ↦ parent x = u)
      (Finset.subset_univ X))
  have h := hcount.trans (hweighted J)
  have hbi : J.biUnion candidates = X.biUnion (fun x ↦ candidates (parent x)) := by
    ext v
    simp only [J, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨u, ⟨x, hx, rfl⟩, hv⟩
      exact ⟨x, hx, hv⟩
    · rintro ⟨x, hx, hv⟩
      exact ⟨parent x, ⟨x, hx, rfl⟩, hv⟩
  rwa [hbi] at h

open scoped Classical in
theorem exists_leaf_assignment_of_pairing {L U V : Type*} [Fintype L] [Finite U]
    (parent : L → U) (P : SimpleGraph U) (b : ℕ) (candidates : U → Finset V)
    (hweight : ∀ J : Finset U, (∀ u ∈ J, ∀ v ∈ J, ¬ P.Adj u v) →
      2 * (∑ u ∈ J, parentWeight parent u) ≤ Fintype.card L + b)
    (hsingle : ∀ u, Fintype.card L + b ≤ 2 * (candidates u).card)
    (hpair : ∀ u v, P.Adj u v → Fintype.card L ≤ (candidates u ∪ candidates v).card) :
    ∃ f : L → V, Function.Injective f ∧ ∀ x, f x ∈ candidates (parent x) := by
  classical
  let := Fintype.ofFinite U
  have hweighted := weighted_hall_of_pairing P (parentWeight parent) (Fintype.card L) b
    candidates (sum_parentWeight parent).le hweight hsingle hpair
  exact (Finset.all_card_le_biUnion_card_iff_existsInjective'
    (fun x ↦ candidates (parent x))).mp (leaf_hall_of_parent_capacity parent candidates hweighted)

end Erdos547

#print axioms Erdos547.exists_leaf_assignment_of_pairing
