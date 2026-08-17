import ErdosProblems.Erdos182.Codegree
import ErdosProblems.Erdos182.PRSEntry
import ErdosProblems.Erdos182.PRSFactor

namespace Erdos182

open Finset

namespace BipartiteGraph

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Containing a regular bipartite subgraph is monotone under addition of edges. -/
theorem ContainsRegularBipartiteSubgraph.mono {R S : BipartiteGraph A B} {k : ℕ}
    (hR : R.ContainsRegularBipartiteSubgraph k) (hRS : R ≤ S) :
    S.ContainsRegularBipartiteSubgraph k := by
  obtain ⟨A₁, B₁, H, hHR, hsupp, hA₁, hB₁, hleft, hright⟩ := hR
  exact ⟨A₁, B₁, H, hHR.trans hRS, hsupp, hA₁, hB₁, hleft, hright⟩

/-- A copy of a graph in an ambient graph carries every regular subgraph to
the ambient graph. -/
theorem containsRegularSubgraph_of_copy {X Y : Type*} [Fintype X] [Fintype Y]
    {P : SimpleGraph X} {G : SimpleGraph Y} {k : ℕ}
    (f : SimpleGraph.Copy P G) (hP : ContainsRegularSubgraph P k) :
    ContainsRegularSubgraph G k := by
  classical
  obtain ⟨J, hJne, hJreg⟩ := hP
  let L : G.Subgraph := J.map f.toHom
  let e : J.coe ≃g L.coe := f.isoSubgraphMap J
  refine ⟨L, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hJne
    exact ⟨f v, by
      change f v ∈ f '' J.verts
      exact ⟨v, hv, rfl⟩⟩
  · intro v
    have hv : v.1 ∈ f '' J.verts := by
      exact v.2
    obtain ⟨x, hx, hxv⟩ := hv
    let xJ : J.verts := ⟨x, hx⟩
    have hev : e xJ = v := by
      apply Subtype.ext
      exact hxv
    rw [← hev]
    rw [← Set.ncard_congr' (e.mapNeighborSet xJ)]
    exact hJreg xJ

/-- A spanning-coefficient graph regular on its nonisolated support is a
regular subgraph in the support-sensitive sense used by the problem. -/
theorem containsRegularSubgraph_of_regular_support_mono
    {X : Type*} [Fintype X] {G P : SimpleGraph X} {k : ℕ}
    (hPG : P ≤ G) (hPne : P.support.Nonempty)
    (hPreg : ∀ v ∈ P.support, (P.neighborSet v).ncard = k) :
    ContainsRegularSubgraph G k := by
  let H : G.Subgraph :=
    { verts := P.support
      Adj := P.Adj
      adj_sub := fun {_ _} h ↦ hPG h
      edge_vert := fun {_ _} h ↦ h.mem_support_left
      symm := P.symm }
  have hHne : H.verts.Nonempty := by simpa [H] using hPne
  refine ⟨H, hHne, ?_⟩
  intro v
  have hcard : (H.coe.neighborSet v).ncard =
      (P.neighborSet (v : X)).ncard := by
    refine Set.ncard_congr (s := H.coe.neighborSet v)
      (t := P.neighborSet (v : X)) (fun w _ ↦ (w : X)) ?_ ?_ ?_
    · intro w hw
      change P.Adj (v : X) (w : X) at hw ⊢
      exact hw
    · intro w z _ _ hwz
      exact Subtype.ext hwz
    · intro w hw
      let z : H.verts := ⟨w, by simpa [H] using hw.mem_support_right⟩
      refine ⟨z, ?_, rfl⟩
      change P.Adj (v : X) (z : X)
      exact hw
  exact hcard.trans (hPreg v (by simpa [H] using v.property))

/-- Failure of bipartite `K_{k,k}`-freeness explicitly supplies a complete
`k` by `k` subgraph, hence a regular bipartite subgraph. -/
theorem containsRegularBipartiteSubgraph_of_not_isBipartiteKFree
    (R : BipartiteGraph A B) [DecidableRel R.Adj] {k : ℕ}
    (hk : 0 < k)
    (hfree : ¬ IsBipartiteKFree R.Adj k) :
    R.ContainsRegularBipartiteSubgraph k := by
  classical
  simp only [IsBipartiteKFree, not_forall, not_lt] at hfree
  obtain ⟨S, hS⟩ := hfree
  obtain ⟨hScard, hcommon⟩ := hS
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := commonRight R.Adj S) hcommon
  let H : BipartiteGraph A B := ⟨fun a b ↦ a ∈ S ∧ b ∈ T⟩
  have hHR : H ≤ R := by
    intro a b hab
    have hbcommon : b ∈ commonRight R.Adj S := hTsub hab.2
    have hb : ∀ a ∈ S, R.Adj a b := by
      simpa [commonRight] using hbcommon
    exact hb a hab.1
  have hsupp : H.SupportedOn S T := by
    intro a b hab
    exact hab
  refine ⟨S, T, H, hHR, hsupp, ?_, ?_, ?_, ?_⟩
  · exact Finset.card_pos.mp (by omega)
  · exact Finset.card_pos.mp (by omega)
  · intro a ha
    simp [H, leftDegree, rightNeighbors, hTcard, ha]
  · intro b hb
    simp [H, rightDegree, leftNeighbors, hScard, hb]

/-- For a two-sorted subgraph lying between disjoint parts of an ambient
simple graph, either it is `K_{k,k}`-free or the ambient graph already has a
nonempty `k`-regular subgraph. -/
theorem isBipartiteKFree_or_containsRegularSubgraph
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {A B : Finset V} (hAB : Disjoint (A : Set V) (B : Set V))
    (R : BipartiteGraph A B) [DecidableRel R.Adj]
    (hRG : R ≤ PRSEntry.fromSimpleGraph G A B) (k : ℕ) (hk : 0 < k) :
    IsBipartiteKFree R.Adj k ∨ ContainsRegularSubgraph G k := by
  by_cases hfree : IsBipartiteKFree R.Adj k
  · exact Or.inl hfree
  · exact Or.inr <|
      containsRegularSubgraph_of_containsRegularBipartiteSubgraph hAB hRG
        (containsRegularBipartiteSubgraph_of_not_isBipartiteKFree R hk hfree)

end BipartiteGraph

end Erdos182
