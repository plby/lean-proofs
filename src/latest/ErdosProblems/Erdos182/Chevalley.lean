import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.FieldTheory.ChevalleyWarning

/-!
# A Chevalley--Warning lemma for divisible-degree subgraphs

For a prime `p`, put one variable on every edge of a finite simple graph and, for every
vertex, impose the polynomial equation

`sum_{e incident to v} X_e^(p - 1) = 0`.

If there are more than `(p - 1) * |V|` edges, Chevalley--Warning says that the number of
common zeroes is divisible by `p`.  Besides the all-zero solution there is consequently a
nonzero solution.  The support of such a solution is a nonempty edge set whose degree at
every vertex is divisible by `p`.
-/

namespace Erdos182

open Finset MvPolynomial

section

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable local instance finiteEdgeSet {W : Type*} [Finite W] (A : SimpleGraph W) :
    Fintype A.edgeSet :=
  Fintype.ofFinite A.edgeSet

noncomputable local instance finiteNeighborSet {W : Type*} [Finite W]
    (A : SimpleGraph W) (v : W) :
    Fintype (A.neighborSet v) :=
  Fintype.ofFinite (A.neighborSet v)

private def edgeEmbedding (G : SimpleGraph V) : G.edgeFinset ↪ Sym2 V :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- The number of edges in `F` incident with `v`.  The edge type is a subtype of the
edge finset, so membership in `F` already certifies that every edge belongs to `G`. -/
noncomputable def edgeSubsetDegree (G : SimpleGraph V) (F : Finset G.edgeFinset) (v : V) : ℕ :=
  (F.filter fun e : G.edgeFinset ↦ v ∈ edgeEmbedding G e).card

/-- The spanning simple graph containing exactly the edges in `F`. -/
noncomputable def edgeSubsetGraph (G : SimpleGraph V) (F : Finset G.edgeFinset) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (((F.map (edgeEmbedding G) : Finset (Sym2 V)) : Set (Sym2 V)))

@[simp]
theorem edgeFinset_edgeSubsetGraph (G : SimpleGraph V) (F : Finset G.edgeFinset) :
    (edgeSubsetGraph G F).edgeFinset =
      F.map (edgeEmbedding G) := by
  classical
  ext e
  rw [SimpleGraph.mem_edgeFinset]
  change e ∈ (SimpleGraph.fromEdgeSet
    (((F.map (edgeEmbedding G) : Finset (Sym2 V)) : Set (Sym2 V)))).edgeSet ↔ _
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  simp only [Set.mem_diff, Finset.mem_coe]
  constructor
  · exact And.left
  · intro he
    refine ⟨he, ?_⟩
    rw [Finset.mem_map] at he
    obtain ⟨e', _, rfl⟩ := he
    exact G.not_isDiag_of_mem_edgeFinset e'.property

theorem edgeSubsetGraph_le (G : SimpleGraph V) (F : Finset G.edgeFinset) :
    edgeSubsetGraph G F ≤ G := by
  classical
  rw [← SimpleGraph.edgeFinset_subset_edgeFinset,
    edgeFinset_edgeSubsetGraph]
  intro e he
  rw [Finset.mem_map] at he
  obtain ⟨e', _, rfl⟩ := he
  exact e'.property

@[simp]
theorem edgeSubsetGraph_eq_bot_iff (G : SimpleGraph V) (F : Finset G.edgeFinset) :
    edgeSubsetGraph G F = ⊥ ↔ F = ∅ := by
  classical
  rw [← SimpleGraph.edgeFinset_eq_empty, edgeFinset_edgeSubsetGraph,
    Finset.map_eq_empty]

@[simp]
theorem degree_edgeSubsetGraph (G : SimpleGraph V) (F : Finset G.edgeFinset) (v : V) :
    (edgeSubsetGraph G F).degree v = edgeSubsetDegree G F v := by
  classical
  rw [← SimpleGraph.card_incidenceFinset_eq_degree,
    SimpleGraph.incidenceFinset_eq_filter, edgeFinset_edgeSubsetGraph,
    Finset.filter_map, Finset.card_map]
  simp only [edgeSubsetDegree, Function.comp_apply]

@[simp]
theorem edgeSubsetDegree_empty (G : SimpleGraph V) (v : V) :
    edgeSubsetDegree G ∅ v = 0 := by
  simp [edgeSubsetDegree]

/-- Selecting edges cannot increase a vertex degree. -/
theorem edgeSubsetDegree_le_degree (G : SimpleGraph V)
    (F : Finset G.edgeFinset) (v : V) :
    edgeSubsetDegree G F v ≤ G.degree v := by
  rw [← degree_edgeSubsetGraph]
  exact SimpleGraph.degree_le_of_le (G := edgeSubsetGraph G F) (H := G)
    (v := v) (edgeSubsetGraph_le G F)

variable (G : SimpleGraph V) (p : ℕ)

/-- The incidence polynomial at `v`, with one variable for every edge of `G`. -/
private noncomputable def incidencePolynomial (v : V) :
    MvPolynomial G.edgeFinset (ZMod p) :=
  ∑ e : G.edgeFinset, if v ∈ edgeEmbedding G e then X e ^ (p - 1) else 0

private theorem totalDegree_incidencePolynomial_le (hp : p.Prime) (v : V) :
    (incidencePolynomial (G := G) p v).totalDegree ≤ p - 1 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  apply totalDegree_finsetSum_le
  intro e _
  split_ifs
  · exact (totalDegree_X_pow e (p - 1)).le
  · simp

/-- **Prime divisible-degree edge-set lemma.**  If a finite simple graph has more than
`(p - 1) |V|` edges, for prime `p`, it has a nonempty set of edges whose degree at every
vertex is divisible by `p`.

The returned finset is a finset of the subtype `G.edgeFinset`; in particular all its
members are edges of `G` without a separate subset side condition. -/
theorem exists_nonempty_edgeSubset_degree_dvd_prime
    {p : ℕ} (hp : p.Prime)
    (hE : (p - 1) * Fintype.card V < G.edgeFinset.card) :
    ∃ F : Finset G.edgeFinset,
      F.Nonempty ∧ ∀ v : V, p ∣ edgeSubsetDegree G F v := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let f : V → MvPolynomial G.edgeFinset (ZMod p) := incidencePolynomial (G := G) p
  have hdegree : (∑ v : V, (f v).totalDegree) < Fintype.card G.edgeFinset := by
    calc
      (∑ v : V, (f v).totalDegree) ≤ ∑ _v : V, (p - 1) :=
        Finset.sum_le_sum fun v _ ↦ totalDegree_incidencePolynomial_le (G := G) p hp v
      _ = (p - 1) * Fintype.card V := by simp [mul_comm]
      _ < G.edgeFinset.card := hE
      _ = Fintype.card G.edgeFinset := (Fintype.card_coe G.edgeFinset).symm
  let S := {x : G.edgeFinset → ZMod p // ∀ v : V, eval x (f v) = 0}
  let zeroSolution : S := ⟨0, by
    intro v
    have hp1 : p - 1 ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hp.one_lt)
    simp only [f, incidencePolynomial, eval_sum]
    apply Finset.sum_eq_zero
    intro e _
    split_ifs
    · simp [hp1]
    · simp⟩
  have hcard_pos : 0 < Fintype.card S :=
    @Fintype.card_pos S _ ⟨zeroSolution⟩
  have hp_card : p ∣ Fintype.card S := by
    simpa [S] using
      (char_dvd_card_solutions_of_fintype_sum_lt p (K := ZMod p) (f := f) hdegree)
  have hp_le_card : p ≤ Fintype.card S := Nat.le_of_dvd hcard_pos hp_card
  obtain ⟨x, hx⟩ :=
    Fintype.exists_ne_of_one_lt_card (hp.one_lt.trans_le hp_le_card) zeroSolution
  let F : Finset G.edgeFinset := Finset.univ.filter fun e ↦ x.1 e ≠ 0
  have hF_nonempty : F.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hF
    apply hx
    apply Subtype.ext
    funext e
    have he : x.1 e = 0 := by
      by_contra hne
      have : e ∈ F := by simp [F, hne]
      simpa [hF] using this
    simp [zeroSolution, he]
  refine ⟨F, hF_nonempty, fun v ↦ ?_⟩
  rw [← CharP.cast_eq_zero_iff (ZMod p)]
  change (((F.filter fun e : G.edgeFinset ↦ v ∈ edgeEmbedding G e).card : ℕ) : ZMod p) = 0
  rw [← Finset.sum_boole]
  have hv := x.2 v
  have hp1 : p - 1 ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hp.one_lt)
  have hv' :
      (∑ e : G.edgeFinset,
        if v ∈ edgeEmbedding G e then
          (if x.1 e ≠ 0 then (1 : ZMod p) else 0) else 0) = 0 := by
    simp only [f, incidencePolynomial, eval_sum] at hv
    have heval (e : G.edgeFinset) :
        eval x.1 (if v ∈ edgeEmbedding G e then X e ^ (p - 1) else 0) =
          if v ∈ edgeEmbedding G e then (if x.1 e ≠ 0 then 1 else 0) else 0 := by
      by_cases hi : v ∈ edgeEmbedding G e
      · by_cases he : x.1 e = 0
        · simp [hi, he, hp1]
        · simp [hi, he, ZMod.pow_card_sub_one]
      · simp [hi]
    simpa only [heval] using hv
  change (∑ e ∈ (Finset.univ.filter fun e : G.edgeFinset ↦ x.1 e ≠ 0),
    if v ∈ edgeEmbedding G e then (1 : ZMod p) else 0) = 0
  rw [Finset.sum_filter]
  exact (Finset.sum_congr rfl fun e _ ↦ by split_ifs <;> rfl).trans hv'

/-- A divisible positive integer strictly below `2p` is equal to `p`. -/
theorem eq_prime_of_pos_of_dvd_of_lt_two_mul {p d : ℕ}
    (hd : 0 < d) (hpd : p ∣ d) (hlt : d < 2 * p) : d = p := by
  exact Nat.eq_of_dvd_of_lt_two_mul hd.ne' hpd hlt

/-- Degree-window corollary of `exists_nonempty_edgeSubset_degree_dvd_prime`.

If every degree in the Chevalley--Warning edge set is below `2p`, then each non-isolated
vertex has degree exactly `p`.  Thus the selected edges, after discarding isolated vertices,
form a `p`-regular subgraph. -/
theorem exists_nonempty_edgeSubset_degree_zero_or_prime
    {p : ℕ} (hp : p.Prime)
    (hE : (p - 1) * Fintype.card V < G.edgeFinset.card)
    (hwindow : ∀ v : V, G.degree v < 2 * p) :
    ∃ F : Finset G.edgeFinset,
      F.Nonempty ∧ ∀ v : V,
        edgeSubsetDegree G F v = 0 ∨ edgeSubsetDegree G F v = p := by
  obtain ⟨F, hF, hdiv⟩ := exists_nonempty_edgeSubset_degree_dvd_prime G hp hE
  refine ⟨F, hF, fun v ↦ ?_⟩
  by_cases hz : edgeSubsetDegree G F v = 0
  · exact Or.inl hz
  · exact Or.inr <| eq_prime_of_pos_of_dvd_of_lt_two_mul
      (Nat.pos_of_ne_zero hz) (hdiv v) ((edgeSubsetDegree_le_degree G F v).trans_lt (hwindow v))

/-- Graph-level degree-window form of the Chevalley--Warning lemma.

The graph `H` is a nonempty spanning subgraph of `G`.  Its only possible degrees are `0`
and `p`, and its support is nonempty. -/
theorem exists_nonempty_subgraph_degree_zero_or_prime
    {p : ℕ} (hp : p.Prime)
    (hE : (p - 1) * Fintype.card V < G.edgeFinset.card)
    (hwindow : ∀ v : V, G.degree v < 2 * p) :
    ∃ H : SimpleGraph V,
      H ≤ G ∧ H ≠ ⊥ ∧
      (∀ v : V, H.degree v = 0 ∨ H.degree v = p) ∧
      H.support.Nonempty := by
  classical
  obtain ⟨F, hF, hdegrees⟩ :=
    exists_nonempty_edgeSubset_degree_zero_or_prime G hp hE hwindow
  let H := edgeSubsetGraph G F
  have hH_ne : H ≠ ⊥ := by
    change edgeSubsetGraph G F ≠ ⊥
    intro hbot
    exact Finset.nonempty_iff_ne_empty.mp hF <|
      (edgeSubsetGraph_eq_bot_iff G F).mp hbot
  have hHdegrees : ∀ v : V, H.degree v = 0 ∨ H.degree v = p := by
    intro v
    change (edgeSubsetGraph G F).degree v = 0 ∨
      (edgeSubsetGraph G F).degree v = p
    simpa only [degree_edgeSubsetGraph] using hdegrees v
  have hsupport : H.support.Nonempty := by
    obtain ⟨v, w, hvw⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hH_ne
    exact ⟨v, w, hvw⟩
  exact ⟨H, edgeSubsetGraph_le G F, hH_ne, hHdegrees, hsupport⟩

/-- Exact regular-subgraph packaging of the degree-window lemma.  The vertex set of the
returned subgraph is the support of the spanning zero-or-`p` graph, so it has no isolated
vertices and is `p`-regular. -/
theorem exists_regular_subgraph_prime_of_degree_window
    {p : ℕ} (hp : p.Prime)
    (hE : (p - 1) * Fintype.card V < G.edgeFinset.card)
    (hwindow : ∀ v : V, G.degree v < 2 * p) :
    ∃ K : G.Subgraph, K.verts.Nonempty ∧
      ∀ v : K.verts, (K.coe.neighborSet v).ncard = p := by
  classical
  obtain ⟨H, hHG, _hH_ne, hdegrees, hsupport⟩ :=
    exists_nonempty_subgraph_degree_zero_or_prime G hp hE hwindow
  let K : G.Subgraph :=
    { verts := H.support
      Adj := H.Adj
      adj_sub := fun h ↦ hHG h
      edge_vert := fun h ↦ ⟨_, h⟩
      symm := H.symm }
  refine ⟨K, hsupport, fun v ↦ ?_⟩
  have hpos : 0 < H.degree (v : V) :=
    (H.degree_pos_iff_exists_adj (v : V)).mpr v.property
  have hpdeg : H.degree (v : V) = p :=
    (hdegrees v).resolve_left (Nat.ne_of_gt hpos)
  calc
    (K.coe.neighborSet v).ncard = (K.neighborSet (v : V)).ncard :=
      Set.ncard_congr' (K.coeNeighborSetEquiv v)
    _ = (H.neighborSet (v : V)).ncard := by rfl
    _ = Fintype.card (H.neighborSet (v : V)) :=
      (Set.fintypeCard_eq_ncard (H.neighborSet (v : V))).symm
    _ = H.degree (v : V) := H.card_neighborSet_eq_degree (v : V)
    _ = p := hpdeg

end

end Erdos182
