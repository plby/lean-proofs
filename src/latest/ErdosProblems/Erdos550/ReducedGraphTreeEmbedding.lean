import Mathlib
import ErdosProblems.Erdos550.RegularClusterEmbedding
import ErdosProblems.Erdos550.RegularPairTree
import ErdosProblems.Erdos550.RegularPairTools

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# From a load-balanced tree→reduced-graph homomorphism to a tree embedding

This file supplies the two interface ingredients of the tree "Key Lemma" that sit
between the abstract multi-cluster embedding engine
`Erdos550.regularClusters_forest_embedding` and the regularity partition:

* **(a) The homomorphism interface.**  `Erdos550.tree_embeds_in_reducedGraph`
  turns the engine's *rooted-forest* hypotheses into a clean *tree*-level
  statement: given pairwise-disjoint clusters `C : ι → Finset V`, a reduced graph
  `R` all of whose edges are `ε`-uniform density-`≥d` pairs, and a graph
  homomorphism `col : α → ι` from the tree `T` into `R` (adjacent tree vertices go
  to `R`-adjacent clusters) together with a bound `BB` on the number of distinct
  clusters among the neighbours of any single tree vertex and the per-cluster
  capacity condition `load(i) + BB·ε·|C i| < (d−ε)·|C i|`, the tree `T` embeds into
  `G`.  This is exactly "a load-balanced tree→reduced-graph homomorphism
  satisfying the capacity condition embeds the tree".

* **(b) The high-degree / concentration handling.**  The per-vertex slack in the
  capacity condition is `BB·ε·|C i|`, where `BB` bounds the number of *distinct
  child-clusters* of a tree vertex.  A single high-degree vertex could have many
  children; if those children were spread over many clusters, `BB` — and hence the
  slack — would blow up.  `Erdos550.exists_sibling_concentrated_hom` shows the
  children can always be *concentrated*: for any `R`-edge `(i₀,i₁)` there is a
  homomorphism `col : α → ι` into that edge (a depth-parity 2-colouring) for which
  **every** vertex sends *all* of its neighbours into a single cluster, so the
  distinct-child-cluster count is `≤ 1` regardless of degrees
  (`sibling_concentrated_distinct_le`).  Thus high-degree vertices contribute no
  extra slack — `BB = 1` — which is the special handling those vertices require.

Both results reduce to the engine and to
`Erdos550.IsTree.exists_rooted_structure`.
-/

open SimpleGraph Finset

namespace Erdos550

/-
**Rooting of a finite tree, exposing parent links as edges.**

A refinement of `Erdos550.IsTree.exists_rooted_structure` whose output records
that each `parent` link is an actual edge of `T` (needed to transport a graph
homomorphism `T → R` to the parent-link homomorphism required by
`Erdos550.regularClusters_forest_embedding`).
-/
lemma IsTree.exists_rooted_edge_structure {α : Type*} [Fintype α] [DecidableEq α]
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) :
    ∃ (parent : α → Option α) (rank : α → ℕ),
      (∀ a b, parent a = some b → rank b < rank a) ∧
      (∀ a b, parent a = some b → T.Adj a b) ∧
      (∀ a b, T.Adj a b → (parent a = some b ∨ parent b = some a)) := by
  obtain ⟨r, hr⟩ : ∃ r : α, True := by
    cases isEmpty_or_nonempty α <;> simp_all +decide;
    exact hT.1.nonempty.elim ( fun x => ‹IsEmpty α›.elim x );
  obtain ⟨par, hpar⟩ : ∃ par : α → α, (∀ a : α, a ≠ r → T.Adj a (par a) ∧ T.dist (par a) r < T.dist a r) ∧ (∀ a : α, a ≠ r → ∀ b : α, T.Adj a b → T.dist b r < T.dist a r → b = par a) := by
    choose! par hpar using fun a ha => tree_closer_neighbor_exists_unique T hT r a ha;
    exact ⟨ par, fun a ha => hpar a ha |>.1, fun a ha b hb hb' => hpar a ha |>.2 b ⟨ hb, hb' ⟩ ⟩;
  refine' ⟨ fun a => if a = r then none else some ( par a ), fun a => T.dist a r, _, _, _ ⟩ <;> simp_all +decide;
  intro a b hab;
  by_cases ha : a = r <;> by_cases hb : b = r <;> simp_all +decide;
  · grind +suggestions;
  · grind +suggestions;
  · by_cases h : T.dist a r < T.dist b r;
    · exact Or.inr ( hpar.2 b hb a hab.symm h ▸ rfl );
    · grind +suggestions

/-
**(a) Load-balanced tree→reduced-graph homomorphism ⟹ tree embedding.**

Let `C : ι → Finset V` be pairwise-disjoint nonempty clusters and `R` a graph on
`ι` all of whose edges `(i,j)` are `ε`-uniform pairs `(C i, C j)` of density `≥ d`.
Let `T` be a finite tree and `col : α → ι` a graph homomorphism `T → R` (adjacent
tree vertices map to `R`-adjacent clusters).  Let `BB` bound, for every vertex,
the number of distinct clusters among its neighbours, and suppose each cluster's
load `#{a : col a = i}` plus the slack `BB·ε·|C i|` is `< (d−ε)·|C i|`.  Then
`T ⊑ G`.
-/
theorem tree_embeds_in_reducedGraph
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε d : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hd1 : d ≤ 1)
    {ι : Type*} [DecidableEq ι] (C : ι → Finset V) (R : SimpleGraph ι)
    (hne : ∀ i, (C i).Nonempty)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (huni : ∀ i j, R.Adj i j → G.IsUniform ε (C i) (C j))
    (hdens : ∀ i j, R.Adj i j → d ≤ (G.edgeDensity (C i) (C j) : ℝ))
    {α : Type*} [Fintype α] [DecidableEq α] (T : SimpleGraph α) [DecidableRel T.Adj]
    (hT : T.IsTree)
    (col : α → ι)
    (hcol : ∀ a b, T.Adj a b → R.Adj (col a) (col b))
    (BB : ℕ)
    (hB : ∀ a, ((univ.filter (fun x => T.Adj a x)).image col).card ≤ BB)
    (hcap : ∀ i, ((univ.filter (fun a => col a = i)).card : ℝ)
              + (BB : ℝ) * (ε * ((C i).card : ℝ)) < (d - ε) * ((C i).card : ℝ)) :
    T ⊑ G := by
  by_contra h_contra;
  have := @Erdos550.regularClusters_forest_embedding;
  obtain ⟨parent, rank, hrank, hpar_edge, hedge⟩ := IsTree.exists_rooted_edge_structure T hT;
  obtain ⟨ f, hf_inj, hf_side, hf_adj ⟩ := this G hε0 hε1 hd1 C R hne hdisj huni hdens parent rank hrank col ( fun a b hab => hcol a b ( hpar_edge a b hab ) ) BB ( fun a => by
    refine' le_trans ( Finset.card_le_card _ ) ( hB a );
    simp +decide [ Finset.subset_iff ];
    exact fun b hb => ⟨ b, by simpa [ hb ] using! hpar_edge b a hb |> SimpleGraph.Adj.symm, rfl ⟩ ) hcap;
  refine' h_contra ⟨ ⟨ f, _ ⟩, hf_inj ⟩;
  intro a b hab; specialize hedge a b hab; cases' hedge with h h <;> [ exact hf_adj a b h; exact SimpleGraph.Adj.symm ( hf_adj b a h ) ] ;

/-
**(b) Sibling-concentration bound.**

If a colouring `col` sends, for every vertex `a`, all `T`-neighbours of `a` into a
single cluster (`hconc`), then the number of distinct clusters among the
neighbours of any vertex is `≤ 1`.  Consequently `BB = 1` suffices in
`tree_embeds_in_reducedGraph`, regardless of how high the degree of `a` is.
-/
lemma sibling_concentrated_distinct_le {α : Type*} [Fintype α] [DecidableEq α]
    (T : SimpleGraph α) [DecidableRel T.Adj] {ι : Type*} [DecidableEq ι] (col : α → ι)
    (hconc : ∀ a x y, T.Adj a x → T.Adj a y → col x = col y) :
    ∀ a, ((univ.filter (fun x => T.Adj a x)).image col).card ≤ 1 := by
  intro a;
  exact Finset.card_le_one.mpr fun x hx y hy => by obtain ⟨ u, hu, rfl ⟩ := Finset.mem_image.mp hx; obtain ⟨ v, hv, rfl ⟩ := Finset.mem_image.mp hy; aesop;

/-
**(b) Existence of a sibling-concentrated homomorphism into a single edge.**

For any edge `(i₀, i₁)` of the reduced graph `R`, a finite tree `T` admits a graph
homomorphism `col : α → ι` into that edge (a depth-parity 2-colouring: `col` takes
only the two values `i₀, i₁`, adjacent vertices get different ones), and this `col`
is *sibling-concentrated*: all neighbours of any vertex share a single cluster.
This is the concentration used for high-degree tree vertices, guaranteeing the
per-vertex slack `BB·ε·|C i|` stays small (`BB = 1`).
-/
lemma exists_sibling_concentrated_hom {α : Type*} [Fintype α] [DecidableEq α]
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    {ι : Type*} [DecidableEq ι] (R : SimpleGraph ι) {i₀ i₁ : ι} (hR : R.Adj i₀ i₁) :
    ∃ col : α → ι,
      (∀ a, col a = i₀ ∨ col a = i₁) ∧
      (∀ a b, T.Adj a b → R.Adj (col a) (col b)) ∧
      (∀ a x y, T.Adj a x → T.Adj a y → col x = col y) := by
  have h_colorable : Nonempty (T.Coloring (Fin 2)) := by
    exact ⟨ by exact ( Erdos550.IsTree.colorable_two T hT ).some ⟩;
  obtain ⟨ c ⟩ := h_colorable; use fun a => if c a = 0 then i₀ else i₁; simp +decide [  ] ;
  refine' ⟨ _, _, _ ⟩;
  · grind;
  · intro a b hab; have := c.valid hab; split_ifs <;> simp_all +decide ;
    · exact hR.symm;
    · grind;
  · intro a x y hx hy; have := c.valid hx; have := c.valid hy; simp_all +decide [  ] ;
    grind +splitImp

end Erdos550
