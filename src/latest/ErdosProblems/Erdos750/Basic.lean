/-
Adapted from Shashi456/erdos-formalizations, Erdos/P750/Proof.lean:
https://github.com/Shashi456/erdos-formalizations/blob/main/Erdos/P750/Proof.lean
Original formalization posted by paws on 4 May 2026:
https://www.erdosproblems.com/forum/thread/750#post-6255
-/
import Mathlib

namespace Erdos750

open SimpleGraph Filter
open scoped NNReal

universe u v

/-! ## §2. Generalized Mycielski operation -/

/-- The vertex type of `genMyc s G`: `Fin s` levels of `V`, plus one apex vertex. -/
abbrev MycVerts (s : ℕ) (V : Type u) : Type u := (Fin s × V) ⊕ Unit

/-- The apex vertex of `genMyc s G`. -/
@[reducible] def apex (s : ℕ) (V : Type u) : MycVerts s V := Sum.inr ()

/-- The "level i" vertex `(i, v)` in `genMyc s G`. -/
@[reducible] def lvl (s : ℕ) {V : Type u} (i : Fin s) (v : V) : MycVerts s V :=
  Sum.inl (i, v)

/-- Raw adjacency relation of `genMyc s G`, before symmetry/irreflexivity packaging. -/
def MycAdj (s : ℕ) {V : Type u} (G : SimpleGraph V) :
    MycVerts s V → MycVerts s V → Prop
  | Sum.inl (i, u), Sum.inl (j, v) =>
      (i.val = 0 ∧ j.val = 0 ∧ G.Adj u v)
      ∨ (j.val = i.val + 1 ∧ G.Adj u v)
      ∨ (i.val = j.val + 1 ∧ G.Adj u v)
  | Sum.inl (i, _), Sum.inr () => i.val + 1 = s
  | Sum.inr (), Sum.inl (i, _) => i.val + 1 = s
  | Sum.inr (), Sum.inr () => False

lemma MycAdj_symm (s : ℕ) {V : Type u} (G : SimpleGraph V) :
    Std.Symm (MycAdj s G) := by
  constructor
  intro a b h
  match a, b, h with
  | Sum.inl (i, u), Sum.inl (j, v), h =>
      simp only [MycAdj] at h ⊢
      rcases h with ⟨hi, hj, h⟩ | ⟨hji, h⟩ | ⟨hij, h⟩
      · exact Or.inl ⟨hj, hi, h.symm⟩
      · exact Or.inr (Or.inr ⟨hji, h.symm⟩)
      · exact Or.inr (Or.inl ⟨hij, h.symm⟩)
  | Sum.inl (i, _), Sum.inr (), h =>
      simp only [MycAdj] at h ⊢; exact h
  | Sum.inr (), Sum.inl (i, _), h =>
      simp only [MycAdj] at h ⊢; exact h
  | Sum.inr (), Sum.inr (), h =>
      simp only [MycAdj] at h

lemma MycAdj_irrefl (s : ℕ) {V : Type u} (G : SimpleGraph V) :
    Std.Irrefl (MycAdj s G) := by
  constructor
  intro a h
  match a, h with
  | Sum.inl (i, v), h =>
      simp only [MycAdj] at h
      rcases h with ⟨_, _, h⟩ | ⟨hii, _⟩ | ⟨hii, _⟩
      · exact G.irrefl ‹_›
      · omega
      · omega
  | Sum.inr (), h =>
      simp only [MycAdj] at h

/--
The **generalized Mycielski graph** `Mₛ(G)` of a graph `G` (PDF Definition 2.1):
* level-0 internal edges `(0,u)-(0,v)` for each edge `uv ∈ E(G)`;
* cross-level edges `(i,u)-(i+1,v)` for each edge `uv` and `0 ≤ i < s-1`;
* the apex `z` is adjacent to every top-level vertex `(s-1,v)`.

`M₂(G)` is the classical Mycielskian; `M₁(G)` adds a universal vertex.
-/
def genMyc (s : ℕ) {V : Type u} (G : SimpleGraph V) : SimpleGraph (MycVerts s V) where
  Adj := MycAdj s G
  symm := MycAdj_symm s G
  loopless := MycAdj_irrefl s G

/-- Projection of a vertex set in `Mₛ(G)` back to `V(G)`. The apex is ignored. -/
def proj {s : ℕ} {V : Type u} (X : Set (MycVerts s V)) : Set V :=
  { v | ∃ i : Fin s, lvl s i v ∈ X }

/-! ## §3. Odd-cycle transversal number `oct` -/

/--
The **odd-cycle transversal number** of an induced subgraph `G[X]`: the minimum size
of `T ⊆ X` such that `G` restricted to `X \ T` is bipartite.

Defined for any `G : SimpleGraph V` (possibly infinite) and any `X : Finset V`.
Since `T = X` always works (the empty graph is bipartite), the set of valid `t` is
nonempty and `sInf` returns a natural number.
-/
noncomputable def oct {V : Type u} [DecidableEq V] (G : SimpleGraph V) (X : Finset V) : ℕ :=
  sInf { t : ℕ | ∃ T : Finset V, T ⊆ X ∧ T.card = t ∧
    (G.induce ((↑X : Set V) \ (↑T : Set V))).IsBipartite }

/-! ### OCT API — extraction / introduction lemmas -/

/-- Empty induced subgraph is bipartite (works on any vertex type). -/
private lemma induce_empty_isBipartite {V : Type u} (G : SimpleGraph V) :
    (G.induce (∅ : Set V)).IsBipartite := by
  refine ⟨Coloring.mk (fun _ => 0) ?_⟩
  rintro ⟨_, hv⟩ _ _; exact absurd hv (Set.notMem_empty _)

/-- The witness set defining `oct G X` is nonempty (`T = X` always works). -/
private lemma oct_nonempty_witness {V : Type u}
    (G : SimpleGraph V) (X : Finset V) :
    ({ t : ℕ | ∃ T : Finset V, T ⊆ X ∧ T.card = t ∧
        (G.induce ((↑X : Set V) \ (↑T : Set V))).IsBipartite }).Nonempty := by
  refine ⟨X.card, X, subset_refl _, rfl, ?_⟩
  rw [show ((↑X : Set V) \ (↑X : Set V)) = (∅ : Set V) from Set.sdiff_self]
  exact induce_empty_isBipartite G

/-- **Introduction.** If a `T ⊆ X` of size `≤ k` makes `G[X \ T]` bipartite, then
`oct G X ≤ k`. -/
lemma oct_le_of_delete {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {X T : Finset V} (hT : T ⊆ X) {k : ℕ} (hcard : T.card ≤ k)
    (hbip : (G.induce ((↑X : Set V) \ (↑T : Set V))).IsBipartite) :
    oct G X ≤ k :=
  le_trans (Nat.sInf_le ⟨T, hT, rfl, hbip⟩) hcard

/-- **Extraction.** `oct G X` is realised by some witness `T ⊆ X`. -/
lemma oct_witness {V : Type u} [DecidableEq V] (G : SimpleGraph V) (X : Finset V) :
    ∃ T : Finset V, T ⊆ X ∧ T.card = oct G X ∧
      (G.induce ((↑X : Set V) \ (↑T : Set V))).IsBipartite := by
  have hmem := Nat.sInf_mem (oct_nonempty_witness G X)
  exact hmem

/-- `oct G X = 0` iff `G[X]` is already bipartite. -/
lemma oct_eq_zero_iff {V : Type u} [DecidableEq V] (G : SimpleGraph V) (X : Finset V) :
    oct G X = 0 ↔ (G.induce ((↑X : Set V))).IsBipartite := by
  refine ⟨fun h => ?_, fun hbip => ?_⟩
  · obtain ⟨T, hT, hcard, hbip⟩ := oct_witness G X
    rw [h, Finset.card_eq_zero] at hcard
    subst hcard
    rw [Finset.coe_empty, Set.sdiff_empty] at hbip
    exact hbip
  · refine le_antisymm ?_ (Nat.zero_le _)
    refine oct_le_of_delete (Finset.empty_subset X) (by simp) ?_
    rw [Finset.coe_empty, Set.sdiff_empty]
    exact hbip

/-- `oct G ∅ = 0` (empty graph is bipartite). -/
@[simp] lemma oct_empty {V : Type u} [DecidableEq V] (G : SimpleGraph V) :
    oct G ∅ = 0 := by
  rw [oct_eq_zero_iff]
  rw [Finset.coe_empty]
  exact induce_empty_isBipartite G

/-- Trivial bound: `oct G X ≤ |X|` (delete everything). -/
lemma oct_le_card {V : Type u} [DecidableEq V] (G : SimpleGraph V) (X : Finset V) :
    oct G X ≤ X.card := by
  refine oct_le_of_delete (subset_refl _) (le_refl _) ?_
  rw [show ((↑X : Set V) \ (↑X : Set V)) = (∅ : Set V) from Set.sdiff_self]
  exact induce_empty_isBipartite G

/-- **Edge-monotonicity.** Adding edges to a graph only increases its OCT. Equivalently,
removing edges (passing to a sub-graph on the same vertex set) only decreases OCT.

This bridges the gap between the PDF's "every finite subgraph `F ⊆ G[X]`" formulation
and our induced-subgraph form: any `H ≤ G` (i.e., `H.Adj ⊆ G.Adj`) satisfies
`oct H X ≤ oct G X`, so an OCT bound on the induced graph yields one on every subgraph. -/
lemma oct_mono_edges {V : Type u} [DecidableEq V] {H G : SimpleGraph V}
    (hsub : H ≤ G) (X : Finset V) :
    oct H X ≤ oct G X := by
  obtain ⟨T, hT, hTcard, hbipG⟩ := oct_witness G X
  -- The same deletion `T` works for `H`: `H.induce S` is a subgraph of `G.induce S`,
  -- and `Colorable 2` is monotone in the subgraph relation.
  refine oct_le_of_delete hT hTcard.le ?_
  -- `(H.induce ((↑X) \ (↑T))).IsBipartite`
  have hsubInd : (H.induce ((↑X : Set V) \ (↑T : Set V))) ≤
      (G.induce ((↑X : Set V) \ (↑T : Set V))) := by
    intro a b hab
    exact hsub hab
  exact hbipG.mono_left hsubInd

/-! ## Recursive generalized Mycielski graphs -/

/--
Predicate that a graph `G` was assembled from `K₂` by iterated `Mₛ`-cones.
Stiebitz's theorem applies *only* to graphs in this recursively built class; it is
**not** true that `χ(Mₛ(H)) = χ(H) + 1` for every graph `H` and every `s ≥ 3`.

`IsRecursivelyBuiltMr r G` says: `G ≃g K₂` if `r = 2`, otherwise there exists some
graph `H` in `Mᵣ₋₁` and some `s ≥ 1` such that `G ≃g genMyc s H`.
-/
def IsRecursivelyBuiltMr : ∀ (_r : ℕ) {_V : Type u} (_G : SimpleGraph _V), Prop
  | 0, _, _ => False
  | 1, _, _ => False
  | 2, _, G => Nonempty (G ≃g (completeGraph (Fin 2)))
  | r + 3, _, G => ∃ (W : Type u) (H : SimpleGraph W) (s : ℕ),
      1 ≤ s ∧ IsRecursivelyBuiltMr (r + 2) H ∧ Nonempty (G ≃g genMyc s H)

end Erdos750
