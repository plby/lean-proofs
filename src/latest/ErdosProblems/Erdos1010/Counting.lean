import Mathlib

/-!
Elementary incidence-counting helpers reused from `ErdosProblems.Erdos905`.
They are kept independent of that module's book theorem and its resource options.
-/

open SimpleGraph

namespace Erdos1010.Counting

variable {V : Type*} [Fintype V]

noncomputable def triangleDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) : ℕ :=
  Sym2.lift
    ⟨fun u v => Fintype.card (G.commonNeighbors u v),
     fun u v => by simp [G.commonNeighbors_symm]⟩ e

/-- Evaluates `triangleDegree` at a concrete pair. -/
theorem triangleDegree_mk
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    triangleDegree G s(u, v) =
      Fintype.card (G.commonNeighbors u v) := by
  simp [triangleDegree, Sym2.lift_mk]
lemma degree_add_degree_le_card_add_commonNeighbors
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    G.degree u + G.degree v ≤
      Fintype.card V + Fintype.card (G.commonNeighbors u v) := by
  classical
  calc
    G.degree u + G.degree v
        = (G.neighborFinset u ∪ G.neighborFinset v).card +
            (G.neighborFinset u ∩ G.neighborFinset v).card := by
          change (G.neighborFinset u).card + (G.neighborFinset v).card =
            (G.neighborFinset u ∪ G.neighborFinset v).card +
              (G.neighborFinset u ∩ G.neighborFinset v).card
          exact (Finset.card_union_add_card_inter
            (G.neighborFinset u) (G.neighborFinset v)).symm
    _ ≤ Fintype.card V + (G.neighborFinset u ∩ G.neighborFinset v).card := by
          exact Nat.add_le_add_right (Finset.card_le_univ _) _
    _ = Fintype.card V + Fintype.card (G.commonNeighbors u v) := by
          congr 1
          exact (Fintype.card_of_finset'
            (G.neighborFinset u ∩ G.neighborFinset v)
            (fun x ↦ by
              simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
                SimpleGraph.commonNeighbors, Set.mem_inter_iff,
                SimpleGraph.mem_neighborSet])).symm
lemma sum_triangleDegree_eq_three_mul_cliqueFinset [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ e ∈ G.edgeFinset, triangleDegree G e = 3 * (G.cliqueFinset 3).card := by
  -- Count incidences `(edge of a triangle)` in two ways:
  -- once by summing the number of common neighbors of each edge,
  -- and once by observing that every triangle contributes exactly three edges.
  unfold triangleDegree
  simp +decide [SimpleGraph.cliqueFinset]
  convert Finset.sum_congr rfl fun e he => ?_
  rotate_left
  · use fun e =>
      ∑ T ∈ Finset.filter (fun T => G.IsNClique 3 T) Finset.univ,
        if e ∈ Finset.image (fun p : V × V => s(p.1, p.2)) (Finset.offDiag T) then 1 else 0
  · rcases e with ⟨u, v⟩
    simp +decide [SimpleGraph.commonNeighbors]
    refine Finset.card_bij (fun w _hw => {u, v, (w : V)}) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      have ha' : a ∈ G.neighborSet u ∩ G.neighborSet v :=
        (Finset.mem_filter.mp ha).2
      have hua : G.Adj u a :=
        (SimpleGraph.mem_neighborSet G u a).mp ha'.1
      have hva : G.Adj v a :=
        (SimpleGraph.mem_neighborSet G v a).mp ha'.2
      have huv : G.Adj u v := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      have huv_ne : u ≠ v := G.ne_of_adj huv
      have hua_ne : u ≠ a := G.ne_of_adj hua
      have hva_ne : v ≠ a := G.ne_of_adj hva
      have hnc : G.IsNClique 3 {u, v, a} := by
        refine ⟨?_, Finset.card_eq_three.mpr ⟨u, v, a, huv_ne, hua_ne, hva_ne, rfl⟩⟩
        rw [SimpleGraph.isClique_iff]
        intro x hx y hy hxy
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx hy
        rcases hx with (rfl | rfl | rfl) <;> rcases hy with (rfl | rfl | rfl)
        · exact (hxy rfl).elim
        · exact huv
        · exact hua
        · simpa only [SimpleGraph.adj_comm] using huv
        · exact (hxy rfl).elim
        · exact hva
        · simpa only [SimpleGraph.adj_comm] using hua
        · simpa only [SimpleGraph.adj_comm] using hva
        · exact (hxy rfl).elim
      refine ⟨hnc, u, v, ?_, Or.inl ⟨rfl, rfl⟩⟩
      exact ⟨by simp, by simp, huv_ne⟩
    · intro a₁ ha₁ a₂ ha₂ h
      have ha₁' : a₁ ∈ G.neighborSet u ∩ G.neighborSet v :=
        (Finset.mem_filter.mp ha₁).2
      have hua₁ : G.Adj u a₁ :=
        (SimpleGraph.mem_neighborSet G u a₁).mp ha₁'.1
      have hva₁ : G.Adj v a₁ :=
        (SimpleGraph.mem_neighborSet G v a₁).mp ha₁'.2
      have hmem : a₁ ∈ ({u, v, a₂} : Finset V) := by
        rw [← h]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hmem | hmem | hmem
      · exact (G.ne_of_adj hua₁ hmem.symm).elim
      · exact (G.ne_of_adj hva₁ hmem.symm).elim
      · exact hmem
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rcases hb with ⟨hb, p, q, ⟨hp, hq, hpq⟩, hpq_uv⟩
      obtain ⟨hu, hv, huv⟩ : u ∈ b ∧ v ∈ b ∧ u ≠ v := by
        rcases hpq_uv with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨hp, hq, hpq⟩
        · exact ⟨hq, hp, Ne.symm hpq⟩
      have hv_erase : v ∈ b.erase u := Finset.mem_erase.mpr ⟨huv.symm, hv⟩
      have hcard_rem : ((b.erase u).erase v).card = 1 := by
        rw [Finset.card_erase_of_mem hv_erase, Finset.card_erase_of_mem hu, hb.card_eq]
      have hrem_nonempty : ((b.erase u).erase v).Nonempty :=
        Finset.card_pos.mp (by rw [hcard_rem]; decide)
      obtain ⟨a, ha_rem⟩ := hrem_nonempty
      have ha_v : a ≠ v := (Finset.mem_erase.mp ha_rem).1
      have ha_erase_u : a ∈ b.erase u := (Finset.mem_erase.mp ha_rem).2
      have ha_u : a ≠ u := (Finset.mem_erase.mp ha_erase_u).1
      have ha : a ∈ b := (Finset.mem_erase.mp ha_erase_u).2
      have hua : G.Adj u a := hb.isClique hu ha ha_u.symm
      have hva : G.Adj v a := hb.isClique hv ha ha_v.symm
      have ha_domain :
          a ∈ Finset.filter (Membership.mem (G.neighborSet u ∩ G.neighborSet v))
            Finset.univ := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ a,
          Set.mem_inter ((SimpleGraph.mem_neighborSet G u a).mpr hua)
            ((SimpleGraph.mem_neighborSet G v a).mpr hva)⟩
      have hcard_triple : ({u, v, a} : Finset V).card = 3 :=
        Finset.card_eq_three.mpr ⟨u, v, a, huv, ha_u.symm, ha_v.symm, rfl⟩
      have hsubset : ({u, v, a} : Finset V) ⊆ b := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hu
        · exact hv
        · exact ha
      refine ⟨a, ha_domain, Finset.eq_of_subset_of_card_le hsubset ?_⟩
      rw [hb.card_eq, hcard_triple]
  · rw [Finset.sum_comm, Finset.sum_congr rfl]
    all_goals try rw [Finset.sum_const, smul_eq_mul, mul_comm]
    simp +decide [SimpleGraph.isNClique_iff]
    intro x hx hx'
    rw [Finset.card_eq_three] at hx'
    obtain ⟨a, b, c, hab, hbc, hac⟩ := hx'
    simp_all +decide [SimpleGraph.isClique_iff]
    rw [Finset.card_eq_three]
    use s(a, b), s(a, c), s(b, c)
    simp +decide [*, Finset.ext_iff]
    intro e
    constructor <;> intro he <;> rcases e with ⟨u, v⟩ <;> simp_all +decide
    · grind
    · rcases he with
      ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        simp_all +decide [SimpleGraph.adj_comm]
      exacts [⟨u, v, by aesop⟩, ⟨u, v, by aesop⟩, ⟨u, v, by aesop⟩,
        ⟨u, v, by aesop⟩, ⟨u, v, by aesop⟩, ⟨u, v, by aesop⟩]
lemma commonNeighbors_card_eq_triangleDegree_edge
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) :
    (Finset.filter (fun y => y ∈ G.commonNeighbors e.out.1 e.out.2)
      (Finset.univ : Finset V)).card = triangleDegree G e := by
  classical
  convert triangleDegree_mk G (Quot.out e).1 (Quot.out e).2 using 1
  · convert rfl
    convert triangleDegree_mk G (Quot.out e).1 (Quot.out e).2 using 1
    rw [Fintype.card_of_subtype]
    aesop
  · exact congr_arg _ (by exact Eq.symm (Quot.out_eq e))
lemma edge_endpoint_degree_sum_eq_indicator_sum
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq V] :
    ∑ e ∈ G.edgeFinset, (G.degree e.out.1 + G.degree e.out.2) =
      ∑ v : V, ∑ e ∈ G.edgeFinset, (if v ∈ e then G.degree v else 0) := by
  classical
  rw [Finset.sum_comm, Finset.sum_congr rfl]
  intro e he
  have h_edge_repr : e = s(e.out.1, e.out.2) := by
    exact Eq.symm (Quot.out_eq e)
  rw [h_edge_repr, Finset.sum_ite]
  rw [Finset.sum_eq_add (Quot.out e |>.1) (Quot.out e |>.2)] <;> simp +decide
  · rw [← h_edge_repr]
  · intro h
    rw [h_edge_repr] at he
    simp +decide [h] at he

lemma edge_endpoint_degree_sum_eq_neighbor_sum
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ e ∈ G.edgeFinset, (G.degree e.out.1 + G.degree e.out.2) =
      ∑ v : V, ∑ _ ∈ G.neighborFinset v, G.degree v := by
  classical
  rw [edge_endpoint_degree_sum_eq_indicator_sum]
  refine Finset.sum_congr rfl ?_
  intro v hv
  calc
    (∑ e ∈ G.edgeFinset, if v ∈ e then G.degree v else 0)
        = ∑ e ∈ G.edgeFinset.filter (fun e => v ∈ e), G.degree v := by
            rw [Finset.sum_filter]
    _ = ∑ e ∈ G.incidenceFinset v, G.degree v := by
          rw [SimpleGraph.incidenceFinset_eq_filter]
    _ = G.degree v * G.degree v := by
          rw [Finset.sum_const_nat (m := G.degree v) (f := fun _ => G.degree v)]
          · rw [SimpleGraph.card_incidenceFinset_eq_degree, mul_comm]
          · intro x hx
            rfl
    _ = ∑ u ∈ G.neighborFinset v, G.degree v := by
          rw [Finset.sum_const_nat (m := G.degree v) (f := fun _ => G.degree v)]
          · rw [SimpleGraph.degree, mul_comm]
          · intro x hx
            rfl

lemma edge_endpoint_degree_sum_eq_sum_sq
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ e ∈ G.edgeFinset, (G.degree e.out.1 + G.degree e.out.2) =
      ∑ v : V, G.degree v ^ 2 := by
  classical
  simp +decide [edge_endpoint_degree_sum_eq_neighbor_sum, pow_two]

end Erdos1010.Counting
