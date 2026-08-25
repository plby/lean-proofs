import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma SimpleGraphComponentEdgeSumBound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (hcomp : ∀ c : G.ConnectedComponent,
      (G.induce c.supp).edgeFinset.card ≤ 3 * Fintype.card c.supp) :
    G.edgeFinset.card ≤ 3 * Fintype.card V := by
  classical
  let edgeComp : Sym2 V → G.ConnectedComponent := fun e =>
    G.connectedComponentMk e.out.1
  have edge_mem_comp :
      ∀ e : G.edgeFinset, e.1 ∈ (edgeComp e.1).supp.toFinset.sym2 := by
    intro e
    rw [Finset.mem_sym2_iff]
    intro v hv
    have hout : e.1 = s(e.1.out.1, e.1.out.2) := by
      rw [Sym2.mk, e.1.out_eq]
    have hadj : G.Adj e.1.out.1 e.1.out.2 := by
      have he_mem : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
        rw [← hout]
        exact SimpleGraph.mem_edgeFinset.mp e.2
      exact (SimpleGraph.mem_edgeSet (G := G)).mp he_mem
    have hv_cases : v = e.1.out.1 ∨ v = e.1.out.2 := by
      rw [hout] at hv
      simpa using hv
    rcases hv_cases with rfl | rfl
    · exact Set.mem_toFinset.mpr (show e.1.out.1 ∈ (edgeComp e.1).supp from rfl)
    · exact Set.mem_toFinset.mpr
        (((edgeComp e.1).mem_supp_congr_adj hadj).mp
          (show e.1.out.1 ∈ (edgeComp e.1).supp from rfl))
  have edge_card_fiber :
      G.edgeFinset.card =
        ∑ c : G.ConnectedComponent,
          (G.edgeFinset.filter (fun e => edgeComp e = c)).card := by
    simpa [edgeComp] using
      (Finset.card_eq_sum_card_fiberwise (f := edgeComp) (s := G.edgeFinset)
        (t := (Finset.univ : Finset G.ConnectedComponent))
        (by intro e he; exact Finset.mem_univ (edgeComp e)))
  have fiber_subset :
      ∀ c : G.ConnectedComponent,
        (G.edgeFinset.filter (fun e => edgeComp e = c)).card ≤
          (G.edgeFinset ∩ c.supp.toFinset.sym2).card := by
    intro c
    apply Finset.card_le_card
    intro e he
    rw [Finset.mem_filter] at he
    rw [Finset.mem_inter]
    exact ⟨he.1, by simpa [he.2] using edge_mem_comp ⟨e, he.1⟩⟩
  have inter_card_eq :
      ∀ c : G.ConnectedComponent,
        (G.edgeFinset ∩ c.supp.toFinset.sym2).card =
          (G.induce c.supp).edgeFinset.card := by
    intro c
    have hmap :
        (G.induce c.supp).edgeFinset.map (Function.Embedding.subtype (· ∈ c.supp)).sym2Map
          = G.edgeFinset ∩ c.supp.toFinset.sym2 := by
      aesop (add simp [Finset.ext_iff, Sym2.exists, Sym2.forall, SimpleGraph.adj_comm])
    have hcard := congrArg Finset.card hmap
    simpa using hcard.symm
  calc
    G.edgeFinset.card
        = ∑ c : G.ConnectedComponent,
            (G.edgeFinset.filter (fun e => edgeComp e = c)).card := edge_card_fiber
    _ ≤ ∑ c : G.ConnectedComponent, (G.edgeFinset ∩ c.supp.toFinset.sym2).card := by
      exact Finset.sum_le_sum (fun c _ => fiber_subset c)
    _ = ∑ c : G.ConnectedComponent, (G.induce c.supp).edgeFinset.card := by
      simp [inter_card_eq]
    _ ≤ ∑ c : G.ConnectedComponent, 3 * Fintype.card c.supp := by
      exact Finset.sum_le_sum (fun c _ => hcomp c)
    _ = 3 * Fintype.card V := by
      have hvertex :
          (Finset.univ : Finset V) =
            (Finset.univ : Finset G.ConnectedComponent).biUnion
              (fun c => c.supp.toFinset) := by
        ext v
        simp
      have hpair :
          Set.PairwiseDisjoint (↑(Finset.univ : Finset G.ConnectedComponent))
            (fun c : G.ConnectedComponent => c.supp.toFinset) := by
        intro c _ d _ hcd
        exact Set.disjoint_toFinset.mpr
          (SimpleGraph.pairwise_disjoint_supp_connectedComponent G hcd)
      have hcard :
          Fintype.card V =
            ∑ c : G.ConnectedComponent, Fintype.card c.supp := by
        calc
          Fintype.card V = (Finset.univ : Finset V).card := by simp
          _ = ((Finset.univ : Finset G.ConnectedComponent).biUnion
                (fun c => c.supp.toFinset)).card := by rw [hvertex]
          _ = ∑ c : G.ConnectedComponent, (c.supp.toFinset).card := by
            rw [Finset.card_biUnion hpair]
          _ = ∑ c : G.ConnectedComponent, Fintype.card c.supp := by simp
      rw [hcard, Finset.mul_sum]
