import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Existence of a large matching in the reduced graph

This file supplies the **existence of a large matching** used in the
stateful matching embedding: in a
bounded-degree graph, in exactly the packaged form
(`cL cR : κ → ι`, `Sum.elim cL cR` injective, `R.Adj (cL k) (cR k)`) consumed by
the off--Turán matching pipeline.

The mathematical content is the standard *maximal-matching lower bound*: a graph
`H` with maximum degree `≤ Δ` and `e` edges has a matching with `≥ e / (2·Δ)`
edges.  Indeed a maximum-cardinality matching `M` is maximal, so every edge of
`H` is incident to the support of `M` (a set of `2·|M|` vertices), and each such
vertex meets at most `Δ` edges, giving `e ≤ 2·Δ·|M|`.

Applied to the reduced graph restricted to the common neighbourhood of a dense
head pair `X–Y`, this locates the regular matching `M` whose existence the routing
core of the stateful matching pipeline assumes.

The principal definitions and results are:

* `Erdos550.IsMatchingFamily` — a matching packaged as a `Finset (ι × ι)` of
  pairwise vertex-disjoint edges.
* `Erdos550.exists_maximum_matchingFamily` — existence of a maximum-cardinality
  matching family.
* `Erdos550.maximal_matchingFamily_covers` — maximality: every edge of `H`
  touches the support of a maximum matching.
* `Erdos550.matchingFamily_card_lower_bound` — the counting bound
  `e(H) ≤ 2·Δ·|M|`.
* `Erdos550.exists_matching_family` — the packaged `cL/cR` form.
-/

open Finset SimpleGraph

namespace Erdos550

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A matching packaged as a finite set of ordered pairs (directed edges) of `H`
that are pairwise vertex-disjoint: any two pairs sharing an endpoint are equal. -/
def IsMatchingFamily (H : SimpleGraph ι) [DecidableRel H.Adj]
    (P : Finset (ι × ι)) : Prop :=
  (∀ p ∈ P, H.Adj p.1 p.2) ∧
  (∀ p ∈ P, ∀ q ∈ P,
    (p.1 = q.1 ∨ p.1 = q.2 ∨ p.2 = q.1 ∨ p.2 = q.2) → p = q)

/-- The support (set of all endpoints) of a matching family. -/
def support (P : Finset (ι × ι)) : Finset ι :=
  P.image Prod.fst ∪ P.image Prod.snd

/-
The support of a matching family has exactly `2 · |P|` vertices.
-/
omit [Fintype ι] in
lemma support_card {H : SimpleGraph ι} [DecidableRel H.Adj]
    {P : Finset (ι × ι)} (hP : IsMatchingFamily H P) :
    (support P).card = 2 * P.card := by
  rw [ two_mul, support, Finset.card_union_of_disjoint ];
  · rw [ Finset.card_image_of_injOn, Finset.card_image_of_injOn ];
    · intro p hp q hq; have := hP.2 p hp q hq; aesop;
    · intro p hp q hq h; have := hP.2 p hp q hq; aesop;
  · simp_all +decide [ Finset.disjoint_left ];
    intro a x hx y hy; have := hP.2 ( a, x ) hx ( y, a ) hy; simp_all +decide ;
    simpa using! hP.1 _ hy

/-
Every maximum-cardinality matching family is *maximal*: every edge of `H`
has at least one endpoint in the support of `M`.
-/
omit [Fintype ι] in
lemma maximal_matchingFamily_covers {H : SimpleGraph ι} [DecidableRel H.Adj]
    {M : Finset (ι × ι)} (hM : IsMatchingFamily H M)
    (hmax : ∀ P, IsMatchingFamily H P → P.card ≤ M.card)
    {a b : ι} (hab : H.Adj a b) :
    a ∈ support M ∨ b ∈ support M := by
  contrapose! hmax;
  refine' ⟨ Insert.insert ( a, b ) M, _, _ ⟩;
  · refine' ⟨ _, _ ⟩;
    · simp_all +decide [ IsMatchingFamily ];
    · simp_all +decide [ IsMatchingFamily, support ];
      grind;
  · rw [ Finset.card_insert_of_notMem ] <;> simp_all +decide [ support ]

/-
Existence of a maximum-cardinality matching family.
-/
omit [DecidableEq ι] in
lemma exists_maximum_matchingFamily (H : SimpleGraph ι) [DecidableRel H.Adj] :
    ∃ M : Finset (ι × ι), IsMatchingFamily H M ∧
      ∀ P, IsMatchingFamily H P → P.card ≤ M.card := by
  have h_finite : Set.Finite {P : Finset (ι × ι) | IsMatchingFamily H P} := by
    exact Set.toFinite _;
  apply_rules [ Set.exists_max_image ];
  exact ⟨ ∅, by exact ⟨ by simp +decide, by simp +decide ⟩ ⟩

/-
**Maximal-matching lower bound.**  A graph `H` with maximum degree `≤ Δ`
has a matching family `M` with `e(H) ≤ 2 · Δ · |M|`.
-/
lemma matchingFamily_card_lower_bound (H : SimpleGraph ι) [DecidableRel H.Adj]
    (Δ : ℕ) (hΔ : ∀ i, H.degree i ≤ Δ) :
    ∃ M : Finset (ι × ι), IsMatchingFamily H M ∧
      H.edgeFinset.card ≤ 2 * Δ * M.card := by
  -- Use `exists_maximum_matchingFamily H` to obtain a maximum matching `M`.
  obtain ⟨M, hM⟩ := exists_maximum_matchingFamily H;
  refine' ⟨ M, hM.1, _ ⟩;
  -- Every edge of `H` is incident to the support of `M`.
  have h_incident : H.edgeFinset ⊆ Finset.biUnion (support M) (fun v => H.incidenceFinset v) := by
    intro e he;
    obtain ⟨a, b, hab⟩ : ∃ a b, e = s(a, b) ∧ H.Adj a b := by
      rcases e with ⟨ a, b ⟩ ; aesop;
    have := maximal_matchingFamily_covers hM.1 hM.2 hab.2; simp_all +decide only [mem_biUnion, mem_incidenceFinset] ;
    exact this.elim
      (fun h => ⟨a, h, H.mk'_mem_incidenceSet_left_iff.mpr hab.2⟩)
      (fun h => ⟨b, h, H.mk'_mem_incidenceSet_right_iff.mpr hab.2⟩);
  refine' le_trans ( Finset.card_le_card h_incident ) _;
  refine' le_trans ( Finset.card_biUnion_le ) _;
  refine' le_trans ( Finset.sum_le_sum fun v hv => show # ( H.incidenceFinset v ) ≤ Δ from _ ) _;
  · simpa only [SimpleGraph.card_incidenceFinset_eq_degree] using hΔ v;
  · simp +decide [ mul_comm, mul_left_comm, support_card hM.1 ]

/-
**Packaged matching family for the tree-embedding engine.**  If `H` has
maximum degree `≤ Δ` and more than `2 · Δ · t` edges, then `H` has a matching of
more than `t` edges, presented as `cL cR : κ → ι` with `Sum.elim cL cR` injective
and each `(cL k, cR k)` an edge of `H`.  This is exactly the regular-matching
data consumed by the stateful matching embedding.
-/
theorem exists_matching_family (H : SimpleGraph ι) [DecidableRel H.Adj]
    (Δ t : ℕ) (hΔ : ∀ i, H.degree i ≤ Δ)
    (he : 2 * Δ * t < H.edgeFinset.card) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (cL cR : κ → ι),
      t < Fintype.card κ ∧
      (∀ k, H.Adj (cL k) (cR k)) ∧
      Function.Injective (Sum.elim cL cR) := by
  rcases M : matchingFamily_card_lower_bound H Δ hΔ with ⟨ M, hM₁, hM₂ ⟩;
  obtain ⟨κ, hκ⟩ : ∃ κ : Type, ∃ (inst : Fintype κ) (inst_1 : DecidableEq κ), Fintype.card κ = Finset.card ‹Finset (ι × ι)› ∧ t < Fintype.card κ := by
    refine' ⟨ Fin ( Finset.card ‹Finset ( ι × ι ) › ), inferInstance, inferInstance, _, _ ⟩ <;> simp +decide;
    nlinarith;
  obtain ⟨inst, inst_1, hκ₁, hκ₂⟩ := hκ
  use κ, inst, inst_1;
  obtain ⟨cL, cR, hc⟩ : ∃ cL cR : κ → ι, (∀ k, H.Adj (cL k) (cR k)) ∧ (∀ k₁ k₂, cL k₁ = cL k₂ ∨ cL k₁ = cR k₂ ∨ cR k₁ = cL k₂ ∨ cR k₁ = cR k₂ → k₁ = k₂) := by
    obtain ⟨f, hf⟩ : ∃ f : κ → ι × ι, Function.Injective f ∧ ∀ k, f k ∈ ‹Finset (ι × ι)› := by
      have h_equiv : Nonempty (κ ≃ {x : ι × ι // x ∈ ‹Finset (ι × ι)›}) := by
        exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ hκ₁ ] ⟩;
      exact ⟨ _, Subtype.val_injective.comp h_equiv.some.injective, fun k => h_equiv.some k |>.2 ⟩;
    exact ⟨ fun k => ( f k ).1, fun k => ( f k ).2, fun k => hM₁.1 _ ( hf.2 k ), fun k₁ k₂ h => hf.1 <| by have := hM₁.2 _ ( hf.2 k₁ ) _ ( hf.2 k₂ ) h; aesop ⟩;
  refine' ⟨ cL, cR, hκ₂, hc.1, _ ⟩;
  intro x y; cases x <;> cases y <;> simp +decide only [Sum.elim_inl, Sum.elim_inr, reduceCtorEq, imp_false, Sum.inl.injEq,
    Sum.inr.injEq] ;
  · exact fun h => hc.2 _ _ ( Or.inl h );
  · intro h; have := hc.1 ‹_›; have := hc.1 ‹_›; simp_all +decide ;
    have := hc.2 _ _ ( Or.inr <| Or.inl h ) ; simp_all +decide ;
    exact absurd h ( by have := hc.1 ‹_›; exact this.ne );
  · intro h; have := hc.1 ‹_›; have := hc.1 ‹_›; simp_all +decide ;
    have := hc.2 _ _ ( Or.inr <| Or.inr <| Or.inl h ) ; simp_all +decide ;
    exact absurd ( hc.1 ‹_› ) ( by simp +decide [ h ] );
  · exact fun h => hc.2 _ _ ( Or.inr <| Or.inr <| Or.inr h )

/-- The subgraph of the reduced graph `R` keeping only edges `a–b` for which both
`a` and `b` are common neighbours of the head pair `X, Y`.  A matching in this
subgraph is exactly a regular matching *attached to both heads*, as required by
the stateful matching embedding's head-adjacency hypothesis. -/
def headCommonSubgraph (R : SimpleGraph ι) [DecidableRel R.Adj] (X Y : ι) :
    SimpleGraph ι where
  Adj a b := R.Adj a b ∧ (R.Adj a X ∧ R.Adj a Y) ∧ (R.Adj b X ∧ R.Adj b Y)
  symm := ⟨fun _a _b h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _a h => h.1.ne rfl⟩

instance (R : SimpleGraph ι) [DecidableRel R.Adj] (X Y : ι) :
    DecidableRel (headCommonSubgraph R X Y).Adj :=
  fun a b => by unfold headCommonSubgraph; exact inferInstance

/-
**Regular matching at a dense head pair.**  In the reduced graph `R`, given a
head pair `X, Y` and a maximum-degree bound `Δ`, if the head-common subgraph has
more than `2·Δ·t` edges, then there is a matching of more than `t` edges, all of
whose clusters are common neighbours of both heads, packaged as the data
`cL cR : κ → ι` with the full disjointness `Sum.elim cL (Sum.elim cR …)`
injective — exactly the regular-matching hypotheses `hbinadj`, `hmatchhead`,
indexing condition consumed by the stateful matching embedding.
-/
theorem exists_regular_matching_at_head (R : SimpleGraph ι) [DecidableRel R.Adj]
    (X Y : ι) (hXY : R.Adj X Y) (Δ t : ℕ) (hΔ : ∀ i, R.degree i ≤ Δ)
    (he : 2 * Δ * t < (headCommonSubgraph R X Y).edgeFinset.card) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (cL cR : κ → ι),
      t < Fintype.card κ ∧
      (∀ k, R.Adj (cL k) (cR k)) ∧
      (∀ k, R.Adj (cL k) X ∧ R.Adj (cL k) Y ∧ R.Adj (cR k) X ∧ R.Adj (cR k) Y) ∧
      Function.Injective
        (Sum.elim cL (Sum.elim cR (fun b => bif b then Y else X)) :
          κ ⊕ κ ⊕ Bool → ι) := by
  have := @Erdos550.exists_matching_family;
  specialize this (headCommonSubgraph R X Y) Δ t (fun i => by
    exact le_trans ( SimpleGraph.degree_le_of_le ( show headCommonSubgraph R X Y ≤ R from fun a b hab => hab.1 ) ) ( hΔ i )) he
  generalize_proofs at *;
  obtain ⟨κ, x, x_1, cL, cR, ht, hadj, hinj⟩ := this
  use κ, x, x_1, cL, cR
  simp_all +decide only [Sum.elim_injective, Bool.injective_iff, cond_false, cond_true, ne_eq, Bool.forall_bool,
    Sum.forall, Sum.elim_inl, Sum.elim_inr];
  constructor
  · trivial
  constructor
  · intro k
    exact (hadj k).1
  constructor
  · intro k
    exact ⟨(hadj k).2.1.1, (hadj k).2.1.2, (hadj k).2.2.1, (hadj k).2.2.2⟩
  constructor
  · trivial
  constructor
  · constructor
    · trivial
    constructor
    · exact hXY.ne
    · intro k
      exact ⟨(hadj k).2.2.1.ne, (hadj k).2.2.2.ne⟩
  · intro k
    exact ⟨fun _ => trivial, (hadj k).2.1.1.ne, (hadj k).2.1.2.ne⟩

end Erdos550
