import Mathlib
import ErdosProblems.Erdos550.ComplementRegularity
import ErdosProblems.Erdos550.Stability

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The `α(Q) < ηℓ` step: no large sparse-regular family of clusters

In the direct off-Turán embedding one shows that
the blue reduced graph `Q` has small independence number: `α(Q) < ηℓ`.  The
argument is: a large independent set `I` of clusters contains (by Turán, since few
pairs are irregular) a set of `q+1` clusters that are pairwise `ε`-regular; being
independent in `Q`, each such pair has **blue** density `< d`, hence **red**
density `> 1 − d`, so a red copy of the `(q+1)`-colourable graph `F` appears,
contradicting `F`-freeness of the red graph.

This file supplies that step as two reusable lemmas:

* `exists_reg_clique` — the Turán extraction: if the "regular-pairs" graph `Rg`
  induced on a cluster set `I` has more than `turanEdges q |I|` edges, then `I`
  contains `q+1` clusters pairwise `Rg`-adjacent.
* `no_large_sparse_regular_family` — combining `exists_reg_clique` with the
  red-graph embedding `exists_red_multipartite_of_sparse`: for an `F`-free red
  host there is no cluster family `I` that is simultaneously large (enough
  regular pairs), pairwise disjoint, of large clusters, pairwise `ε₀`-regular and
  pairwise **blue**-sparse (density `< d`).
-/

open SimpleGraph Finset

namespace Erdos550

/-
**Turán extraction of a regular clique.**  If the regular-pairs graph `Rg`,
induced on the cluster set `I`, has strictly more than `turanEdges q |I|` edges,
then `I` contains a `(q+1)`-element subset that is pairwise `Rg`-adjacent.
-/
lemma exists_reg_clique {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Rg : SimpleGraph ι) [DecidableRel Rg.Adj] (I : Finset ι) (q : ℕ)
    (h : (turanEdges q I.card : ℕ) < (Rg.induce (↑I : Set ι)).edgeFinset.card) :
    ∃ s : Finset ι, s ⊆ I ∧ s.card = q + 1 ∧
      (∀ a ∈ s, ∀ b ∈ s, a ≠ b → Rg.Adj a b) := by
  -- By contradiction, assume that $Rg$ is $(q+1)$-clique-free.
  by_contra h_contra
  have h_clique_free : (induce (↑I) Rg).CliqueFree (q + 1) := by
    intro s hs; contrapose! h_contra; use Finset.image Subtype.val s; simp_all +decide only [SetLike.coe_sort_coe, mem_image, Subtype.exists, exists_and_right, exists_eq_right,
    ne_eq, forall_exists_index] ;
    exact ⟨ Finset.image_subset_iff.mpr fun x hx => x.2, by rw [ Finset.card_image_of_injective _ Subtype.coe_injective, hs.2 ], fun a ha ha' b hb hb' hab => by simpa [ hab ] using! hs.1 ha' hb' <| by aesop ⟩;
  contrapose! h;
  convert! SimpleGraph.CliqueFree.card_edgeFinset_le h_clique_free using 1;
  convert! SimpleGraph.card_edgeFinset_turanGraph using 1;
  simp +decide [ Fintype.card_subtype ]

/-
**No large sparse-regular family (`α(Q) < ηℓ`).**  For a `(q+1)`-colourable
graph `F` on `W` and slack `0 < d < 1`, there are `ε₀ > 0` and `m₀` such that if
the red graph `Gᶜ` is `F`-free, then there is **no** cluster family `C` indexed by
a set `I` of clusters with: more than `turanEdges q |I|` pairwise-regular pairs
(`Rg` induced on `I`), each cluster of size `≥ m₀`, pairwise disjoint on `I`,
`Rg`-pairs `ε₀`-uniform, and every `Rg`-pair within `I` of **blue** density `< d`.
-/
lemma no_large_sparse_regular_family {W : Type} [Fintype W] (F : SimpleGraph W)
    (q : ℕ) (hcol : F.Colorable (q + 1)) (d : ℝ) (hd1 : d < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ m₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], ¬ (F ⊑ Gᶜ) →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (C : ι → Finset V)
        (Rg : SimpleGraph ι) [DecidableRel Rg.Adj] (I : Finset ι),
        (turanEdges q I.card : ℕ) < (Rg.induce (↑I : Set ι)).edgeFinset.card →
        (∀ i ∈ I, m₀ ≤ (C i).card) →
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (C i) (C j)) →
        (∀ i j, Rg.Adj i j → G.IsUniform ε₀ (C i) (C j)) →
        (∀ i ∈ I, ∀ j ∈ I, Rg.Adj i j → (G.edgeDensity (C i) (C j) : ℝ) < d) →
        False := by
  obtain ⟨ ε₀, hε₀, m₀, h ⟩ := Erdos550.exists_red_multipartite_of_sparse F q hcol ( 1 - d ) ( by linarith );
  refine' ⟨ ε₀, hε₀, m₀, _ ⟩;
  intro V _ _ G _ hG ι _ _ C Rg _ I hI hC hdisj hreg hsparse
  obtain ⟨s, hs⟩ := Erdos550.exists_reg_clique Rg I q hI
  obtain ⟨P, hP⟩ : ∃ P : Fin (q + 1) → ι, (∀ i, P i ∈ s) ∧ (∀ i j, i ≠ j → P i ≠ P j) ∧ (∀ i j, i ≠ j → Rg.Adj (P i) (P j)) := by
    obtain ⟨e, he⟩ : ∃ e : Fin (q + 1) ≃ s, True := by
      exact ⟨ Fintype.equivOfCardEq ( by simp +decide [ hs.2.1 ] ), trivial ⟩;
    exact ⟨ fun i => e i |>.1, fun i => e i |>.2, fun i j hij => fun h => hij <| e.injective <| Subtype.ext h, fun i j hij => hs.2.2 _ ( e i |>.2 ) _ ( e j |>.2 ) <| fun h => hij <| e.injective <| Subtype.ext h ⟩;
  exact hG <| h G ( fun i => C ( P i ) ) ( fun i => hC _ <| hs.1 <| hP.1 i ) ( fun i j hij => hdisj _ ( hs.1 <| hP.1 i ) _ ( hs.1 <| hP.1 j ) <| hP.2.1 i j hij ) ( fun i j hij => hreg _ _ <| hP.2.2 i j hij ) ( fun i j hij => by linarith [ hsparse _ ( hs.1 <| hP.1 i ) _ ( hs.1 <| hP.1 j ) <| hP.2.2 i j hij ] )

/-
**Turán threshold from few irregular pairs.**  If the induced regular-pairs
graph on `𝒜` has at most `B` non-edges (irregular pairs) and
`turanEdges q |𝒜| + B < C(|𝒜|,2)`, then it has more than `turanEdges q |𝒜|`
edges — the hypothesis consumed by `exists_reg_clique` /
`exists_dense_regular_pair_in_family`.
-/
lemma turan_lt_induce_of_few_irregular {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Rg : SimpleGraph ι) [DecidableRel Rg.Adj] (𝒜 : Finset ι) (q B : ℕ)
    (hbad : ((Rg.induce (↑𝒜 : Set ι))ᶜ).edgeFinset.card ≤ B)
    (hthr : turanEdges q 𝒜.card + B < (𝒜.card).choose 2) :
    turanEdges q 𝒜.card < (Rg.induce (↑𝒜 : Set ι)).edgeFinset.card := by
  classical
  contrapose! hthr; have := Fintype.card_coe 𝒜; simp_all +decide [ Nat.choose_two_right ] ;
  have h_edge_count : ((induce (↑𝒜) Rg).edgeFinset.card + (induce (↑𝒜) Rg)ᶜ.edgeFinset.card) = (Nat.choose (Finset.card 𝒜) 2) := by
    rw [ ← Finset.card_union_of_disjoint ];
    · have h_card_edges : (induce (𝒜 : Set ι) Rg).edgeFinset ∪ (induce (𝒜 : Set ι) Rg)ᶜ.edgeFinset = (⊤ : SimpleGraph {x // x ∈ 𝒜}).edgeFinset := by
        ext ⟨x, y⟩; simp only [SetLike.coe_sort_coe, mem_union, mem_edgeFinset, mem_edgeSet, comap_adj, compl_adj, ne_eq,
    edgeFinset_top, Set.toFinset_compl, mem_compl, Set.mem_toFinset, Sym2.mem_diagSet, Sym2.mk_isDiag_iff];
        by_cases h : x = y <;> simp +decide [ h ];
        exact em _;
      rw [ h_card_edges, SimpleGraph.card_edgeFinset_top_eq_card_choose_two ];
      rw [ Fintype.card_coe ];
    · simp +decide only [SetLike.coe_sort_coe, disjoint_edgeFinset];
      rintro ⟨ ⟨ u, hu ⟩, ⟨ v, hv ⟩ ⟩ ; simp +decide [ SimpleGraph.compl_adj ] ; aesop;
  cases k : Finset.card 𝒜 <;> simp_all +decide [ Nat.choose_two_right ] ; omega

/-- **Heavy set spans a dense regular pair.**  For an `F`-free red host, if a
cluster family `𝒜` is large (more than `turanEdges q |𝒜|` regular pairs `Rg`
inside it), of large clusters, pairwise disjoint and pairwise-`Rg`-`ε₀`-uniform,
then `𝒜` contains a pair that is both `Rg`-regular and of **blue** density `≥ d`
— i.e. an edge of the reduced graph `Q`.  (This is the `|𝒜| > α(Q)` ⇒ `Q[𝒜]`
has an edge step, in a self-contained form.) -/
lemma exists_dense_regular_pair_in_family {W : Type} [Fintype W] (F : SimpleGraph W)
    (q : ℕ) (hcol : F.Colorable (q + 1)) (d : ℝ) (hd1 : d < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ m₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], ¬ (F ⊑ Gᶜ) →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (C : ι → Finset V)
        (Rg : SimpleGraph ι) [DecidableRel Rg.Adj] (𝒜 : Finset ι),
        (turanEdges q 𝒜.card : ℕ) < (Rg.induce (↑𝒜 : Set ι)).edgeFinset.card →
        (∀ i ∈ 𝒜, m₀ ≤ (C i).card) →
        (∀ i ∈ 𝒜, ∀ j ∈ 𝒜, i ≠ j → Disjoint (C i) (C j)) →
        (∀ i j, Rg.Adj i j → G.IsUniform ε₀ (C i) (C j)) →
        ∃ i ∈ 𝒜, ∃ j ∈ 𝒜, Rg.Adj i j ∧ (d : ℝ) ≤ (G.edgeDensity (C i) (C j) : ℝ) := by
  obtain ⟨ε₀, hε₀, m₀, hmain⟩ := no_large_sparse_regular_family F q hcol d hd1
  refine ⟨ε₀, hε₀, m₀, ?_⟩
  intro V _ _ G _ hFfree ι _ _ C Rg _ 𝒜 hbig hC hdisj hreg
  by_contra hcon
  push_neg at hcon
  exact hmain G hFfree C Rg 𝒜 hbig hC hdisj hreg hcon

end Erdos550
