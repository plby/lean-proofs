import ErdosProblems.Erdos1010.CutBipartite
import ErdosProblems.Erdos1010.SparseCharge

/-! # Counting triangles across a cut -/

open Finset

namespace Erdos1010

variable {V : Type*} [Fintype V] [DecidableEq V]

def crossTriangleIncidences (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Finset (Σ _p : Finset V, V) :=
  (internalPairs G S).sigma fun p ↦ Sᶜ.filter (fun v ↦ ∀ w ∈ p, G.Adj w v)

def twoSideTriangles (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun p ↦ (p ∩ S).card = 2

lemma cross_incidence_properties (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    {i : Σ _p : Finset V, V} (hi : i ∈ crossTriangleIncidences G S) :
    G.IsNClique 3 (insert i.2 i.1) ∧ (insert i.2 i.1) ∩ S = i.1 ∧ i.2 ∉ S := by
  obtain ⟨hp, hv⟩ := mem_sigma.mp hi
  obtain ⟨hpG, hpS⟩ := mem_filter.mp hp
  obtain ⟨hvS, hvadj⟩ := mem_filter.mp hv
  have hvnot : i.2 ∉ S := mem_compl.mp hvS
  refine ⟨(G.mem_cliqueFinset_iff.mp hpG).insert (fun w hw ↦ (hvadj w hw).symm), ?_, hvnot⟩
  ext v
  simp only [mem_inter, mem_insert]
  constructor
  · rintro ⟨h | h, hv⟩
    · exact (hvnot (h ▸ hv)).elim
    · exact h
  · intro hv
    exact ⟨Or.inr hv, hpS hv⟩

lemma cross_incidence_support_injective (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Set.InjOn (fun i : Σ _p : Finset V, V ↦ insert i.2 i.1) (crossTriangleIncidences G S) := by
  intro i hi j hj heq
  change insert i.2 i.1 = insert j.2 j.1 at heq
  have hpi := cross_incidence_properties G S hi
  have hpj := cross_incidence_properties G S hj
  have hp : i.1 = j.1 := by rw [← hpi.2.1, ← hpj.2.1, heq]
  have hv : i.2 = j.2 := by
    have hmem : i.2 ∈ insert j.2 j.1 := by rw [← heq]; simp
    rcases mem_insert.mp hmem with hv | hv
    · exact hv
    · have hjS : j.1 ⊆ S := (mem_filter.mp (mem_sigma.mp hj).1).2
      exact (hpi.2.2 (hjS hv)).elim
  cases i
  cases j
  dsimp at hp hv
  subst_vars
  rfl

lemma card_cross_incidence_le (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (crossTriangleIncidences G S).card ≤ (twoSideTriangles G S).card := by
  calc
    _ = ((crossTriangleIncidences G S).image (fun i ↦ insert i.2 i.1)).card :=
      (card_image_of_injOn (cross_incidence_support_injective G S)).symm
    _ ≤ _ := by
      apply card_le_card
      intro p hp
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
      have h := cross_incidence_properties G S hi
      apply mem_filter.mpr
      refine ⟨G.mem_cliqueFinset_iff.mpr h.1, ?_⟩
      rw [h.2.1]
      exact (G.mem_cliqueFinset_iff.mp (mem_filter.mp (mem_sigma.mp hi).1).1).card_eq

lemma card_cross_incidences_add_le_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    (crossTriangleIncidences G S).card + (crossTriangleIncidences G Sᶜ).card ≤ (G.cliqueFinset 3).card := by
  have hdis : Disjoint (twoSideTriangles G S) (twoSideTriangles G Sᶜ) := by
    apply disjoint_left.mpr
    intro p hp hq
    obtain ⟨hpG, hpS⟩ := mem_filter.mp hp
    have hpSc := (mem_filter.mp hq).2
    have hc := (G.mem_cliqueFinset_iff.mp hpG).card_eq
    have hsum := pair_inter_compl_card p S
    omega
  have hsub : twoSideTriangles G S ∪ twoSideTriangles G Sᶜ ⊆ G.cliqueFinset 3 :=
    union_subset (filter_subset _ _) (filter_subset _ _)
  have hcard := card_le_card hsub
  rw [card_union_of_disjoint hdis] at hcard
  have hS := card_cross_incidence_le G S
  have hSc := card_cross_incidence_le G Sᶜ
  omega

lemma pair_common_neighbor_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (T p : Finset V) (hp : p.card = 2) :
    T.card ≤ (T.filter fun v ↦ ∀ w ∈ p, G.Adj w v).card + ∑ w ∈ p, missingDegree G T w := by
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hp
  let C := T.filter fun v ↦ G.Adj a v ∧ G.Adj b v
  let X := T.filter fun v ↦ ¬G.Adj a v
  let Y := T.filter fun v ↦ ¬G.Adj b v
  have hsub : T ⊆ C ∪ X ∪ Y := by
    intro v hv
    by_cases ha : G.Adj a v
    · by_cases hb : G.Adj b v
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hv, ha, hb⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨hv, hb⟩)
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hv, ha⟩))
  have hc := card_le_card hsub
  have hu := card_union_le (C ∪ X) Y
  have hu' := card_union_le C X
  have hbound : T.card ≤ C.card + X.card + Y.card := by omega
  simpa [C, X, Y, missingDegree, sum_pair hab, add_assoc] using hbound

lemma cross_incidence_lower_bound (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (Sᶜ.card : ℤ) * (internalPairs G S).card ≤ (crossTriangleIncidences G S).card +
      pairCharge (internalPairs G S) (fun v ↦ (missingDegree G Sᶜ v : ℤ)) := by
  have hpoint : ∀ p ∈ internalPairs G S, (Sᶜ.card : ℤ) ≤
      ((Sᶜ.filter fun v ↦ ∀ w ∈ p, G.Adj w v).card : ℤ) + ∑ w ∈ p, (missingDegree G Sᶜ w : ℤ) := by
    intro p hp
    exact_mod_cast pair_common_neighbor_bound G Sᶜ p (G.mem_cliqueFinset_iff.mp (mem_filter.mp hp).1).card_eq
  have hsum := sum_le_sum hpoint
  have hi : ((crossTriangleIncidences G S).card : ℤ) =
      ∑ p ∈ internalPairs G S, ((Sᶜ.filter fun v ↦ ∀ w ∈ p, G.Adj w v).card : ℤ) := by
    unfold crossTriangleIncidences
    rw [card_sigma, Nat.cast_sum]
  rw [sum_add_distrib, ← hi] at hsum
  simpa [sum_const, pairCharge, mul_comm] using hsum

lemma cross_triangle_lower_bound (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (Sᶜ.card : ℤ) * (internalPairs G S).card + (S.card : ℤ) * (internalPairs G Sᶜ).card ≤
      (G.cliqueFinset 3).card + pairCharge (internalPairs G S) (fun v ↦ (missingDegree G Sᶜ v : ℤ)) +
      pairCharge (internalPairs G Sᶜ) (fun v ↦ (missingDegree G S v : ℤ)) := by
  have hS := cross_incidence_lower_bound G S
  have hSc := cross_incidence_lower_bound G Sᶜ
  rw [compl_compl] at hSc
  have hi : ((crossTriangleIncidences G S).card : ℤ) + (crossTriangleIncidences G Sᶜ).card ≤
      (G.cliqueFinset 3).card := by exact_mod_cast card_cross_incidences_add_le_triangles G S
  linarith

lemma cutCharge_missingCross (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    cutCharge (G.induce (S : Set V)) (G.induce ((Sᶜ : Finset V) : Set V)) (missingCross G S) =
      pairCharge (internalPairs G S) (fun v ↦ (missingDegree G Sᶜ v : ℤ)) +
      pairCharge (internalPairs G Sᶜ) (fun v ↦ (missingDegree G S v : ℤ)) := by
  rw [pairCharge_internalPairs, pairCharge_internalPairs]
  unfold cutCharge
  simp only [leftDegree_missingCross, rightDegree_missingCross]

lemma cross_triangle_lower_bound_induced (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (Sᶜ.card : ℤ) * (G.induce (S : Set V)).edgeFinset.card +
      (S.card : ℤ) * (G.induce ((Sᶜ : Finset V) : Set V)).edgeFinset.card ≤
      (G.cliqueFinset 3).card + cutCharge (G.induce (S : Set V))
        (G.induce ((Sᶜ : Finset V) : Set V)) (missingCross G S) := by
  rw [cutCharge_missingCross]
  have h := cross_triangle_lower_bound G S
  rw [card_internalPairs, card_internalPairs] at h
  linarith

end Erdos1010
