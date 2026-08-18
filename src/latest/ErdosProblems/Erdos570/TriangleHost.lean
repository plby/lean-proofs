/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.EmbeddingNeighborhood
import ErdosProblems.Erdos570.CycleCode
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Triangle-free host and independent-set degree bounds

This file collects the elementary graph facts used by both branches of the
Goddard--Kleitman induction.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

theorem cliqueFree_three_of_cycleCode_not_isContained
    {V : Type*} (C : SimpleGraph V)
    (hno : ¬ (cycleCode 3).graph ⊑ C) : C.CliqueFree 3 := by
  by_contra hfree
  have htop : (⊤ : SimpleGraph (Fin 3)) ⊑ C :=
    (SimpleGraph.not_cliqueFree_iff_top_isContained 3).mp hfree
  apply hno
  simpa [cycleCode, SimpleGraph.cycleGraph_three_eq_top] using htop

/-- Every red neighbourhood is a blue clique, and hence has size at most
the maximum blue clique. -/
theorem degree_le_compl_cliqueNum_of_cliqueFree_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (hfree : C.CliqueFree 3) (v : V) :
    C.degree v ≤ Cᶜ.cliqueNum := by
  have hind := C.isIndepSet_neighborSet_of_triangleFree hfree v
  have hclique : Cᶜ.IsClique (C.neighborFinset v : Set V) := by
    rw [SimpleGraph.isClique_compl]
    simpa using hind
  exact hclique.card_le_cliqueNum

/-- An arbitrary graph whose order fits in a clique is contained in the
ambient graph. -/
theorem isContained_of_isClique_card_le
    {W V : Type*} [Fintype W] [Fintype V] [DecidableEq V]
    (H : SimpleGraph W) (B : SimpleGraph V) (T : Finset V)
    (hT : B.IsClique (T : Set V))
    (hcard : Fintype.card W ≤ T.card) : H ⊑ B := by
  let f : W ↪ T := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_coe] using hcard))
  let hom : H →g B :=
    { toFun := fun w ↦ (f w).1
      map_rel' := by
        intro x y hxy
        apply hT (f x).2 (f y).2
        intro heq
        exact hxy.ne (f.injective (Subtype.ext heq)) }
  exact ⟨hom.toCopy (fun _ _ h ↦ f.injective (Subtype.ext h))⟩

/-- The one-vertex deletion obstruction, with the host degree replaced by
the maximum size of a blue clique. -/
theorem deletion_obstruction_le_compl_cliqueNum
    {H : GraphCode} {N : ℕ} (C : SimpleGraph (Fin N))
    [DecidableRel C.Adj] (v : Fin H.vertexCount)
    [DecidableRel H.graph.Adj] (hdeg : 0 < H.graph.degree v)
    (hroom : H.vertexCount - 1 ≤ N)
    (hRamsey : RamseyAt (cycleCode 3) (supportCode (deleteVertexCode H v)) N)
    (hnoF : ¬ (cycleCode 3).graph ⊑ C) (hnoH : ¬ H.graph ⊑ Cᶜ) :
    N - (H.vertexCount - 1) ≤
      H.graph.degree v * Cᶜ.cliqueNum := by
  obtain ⟨u, hu⟩ := exists_large_degree_of_ramseyAt_supported_delete
    C v hdeg hroom hRamsey hnoF hnoH
  have hfree := cliqueFree_three_of_cycleCode_not_isContained C hnoF
  exact hu.trans (Nat.mul_le_mul_left _
    (degree_le_compl_cliqueNum_of_cliqueFree_three C hfree u))

/-- An independent set meets every edge at most once, so the sum of the
degrees of its vertices is at most the total number of edges. -/
theorem sum_degrees_independent_le_card_edges
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (S : Finset W) (hS : G.IsIndepSet (S : Set W)) :
    ∑ x ∈ S, G.degree x ≤ G.edgeFinset.card := by
  let D := Σ x : S, ↑(G.neighborFinset x.1)
  let toEdge : D → G.edgeFinset := fun z ↦
    ⟨s(z.1.1, z.2.1), by
      rw [G.mem_edgeFinset]
      exact (G.mem_neighborFinset z.1.1 z.2.1).mp z.2.2⟩
  have htoEdge : Function.Injective toEdge := by
    rintro ⟨x, z⟩ ⟨x', z'⟩ heq
    have hsym : s(x.1, z.1) = s(x'.1, z'.1) :=
      congrArg Subtype.val heq
    rw [Sym2.eq_iff] at hsym
    rcases hsym with hsame | hswap
    · cases Subtype.ext hsame.1
      cases Subtype.ext hsame.2
      rfl
    · exfalso
      have hadj : G.Adj x.1 x'.1 := by
        have hxz := (G.mem_neighborFinset x.1 z.1).mp z.2
        simpa [hswap.2] using hxz
      exact hS x.2 x'.2 hadj.ne hadj
  have hcard := Fintype.card_le_of_injective toEdge htoEdge
  have hdomain : Fintype.card D = ∑ x ∈ S, G.degree x := by
    simp only [D, Fintype.card_sigma]
    rw [Finset.univ_eq_attach S]
    simpa only [Fintype.card_coe,
      SimpleGraph.card_neighborFinset_eq_degree] using
      Finset.sum_attach S (fun x ↦ G.degree x)
  rw [hdomain] at hcard
  simpa only [Fintype.card_coe] using hcard

/-- Trim every blue cross-neighbourhood of a maximum blue clique to the
same size `|Y|-|T|`.  Triangle-freeness bounds the omitted red neighbours
by `|T|`. -/
theorem exists_uniform_blue_cross_family
    {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (hfree : C.CliqueFree 3) (T Y : Finset V)
    (hTY : Disjoint T Y) (hTcard : T.card = Cᶜ.cliqueNum) :
    ∃ N : T → Finset Y, ∀ x : T,
      (N x).card = Y.card - T.card ∧
        ∀ y ∈ N x, Cᶜ.Adj x.1 y.1 := by
  classical
  let raw : T → Finset Y := fun x ↦
    Finset.univ.filter fun y : Y ↦ Cᶜ.Adj x.1 y.1
  have hraw (x : T) : Y.card - T.card ≤ (raw x).card := by
    let red : Finset Y :=
      Finset.univ.filter fun y : Y ↦ C.Adj x.1 y.1
    let intoNeighbor : red ↪ C.neighborFinset x.1 :=
      { toFun := fun y ↦ ⟨y.1.1, by
          rw [C.mem_neighborFinset]
          exact (Finset.mem_filter.mp y.2).2⟩
        inj' := by
          intro a b hab
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun z : C.neighborFinset x.1 ↦ z.1) hab }
    have hredDegree : red.card ≤ C.degree x.1 := by
      have hc := Fintype.card_le_of_injective intoNeighbor intoNeighbor.injective
      simpa only [Fintype.card_coe,
        SimpleGraph.card_neighborFinset_eq_degree] using hc
    have hredT : red.card ≤ T.card := by
      rw [hTcard]
      exact hredDegree.trans
        (degree_le_compl_cliqueNum_of_cliqueFree_three C hfree x.1)
    have hpred (y : Y) : Cᶜ.Adj x.1 y.1 ↔ ¬ C.Adj x.1 y.1 := by
      have hne : x.1 ≠ y.1 := by
        intro heq
        exact Finset.disjoint_left.mp hTY x.2 (heq ▸ y.2)
      rw [SimpleGraph.compl_adj]
      simp [hne]
    have hpart : red.card + (raw x).card = Y.card := by
      have hfilter := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset Y))
        (p := fun y : Y ↦ C.Adj x.1 y.1)
      have hrawEq : raw x = Finset.univ.filter
          (fun y : Y ↦ ¬ C.Adj x.1 y.1) := by
        ext y
        simp only [raw, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hpred y
      rw [hrawEq]
      simpa only [red, Finset.card_univ, Fintype.card_coe] using hfilter
    omega
  choose N hNsub hNcard using fun x : T ↦
    Finset.exists_subset_card_eq (hraw x)
  refine ⟨N, fun x ↦ ⟨hNcard x, ?_⟩⟩
  intro y hy
  have := hNsub x hy
  exact (Finset.mem_filter.mp this).2

end Erdos570
