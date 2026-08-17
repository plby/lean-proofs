/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Util.Ramsey

/-!
# Erdős Problem 546: basic finite-graph infrastructure

This file packages the diagonal two-colour Ramsey number of an arbitrary finite
simple graph and the elementary finite counting notions used in the proof of
Sudakov's bound.  Graph containment is ordinary (not necessarily induced)
containment, represented by `SimpleGraph.IsContained` (`⊑`).
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos546

open Finset
open SimpleGraph

/-! ## Diagonal graph Ramsey numbers -/

/-- Every red/blue colouring of the complete graph on `N` vertices contains a
monochromatic, not necessarily induced, copy of `G`.  The red graph is `R` and
the blue graph is its complement. -/
def GraphRamseyProperty {v : ℕ} (G : SimpleGraph (Fin v)) (N : ℕ) : Prop :=
  ∀ R : SimpleGraph (Fin N), G ⊑ R ∨ G ⊑ Rᶜ

/-- Every fixed finite graph has a diagonal two-colour Ramsey bound. -/
theorem graphRamseyProperty_exists {v : ℕ} (G : SimpleGraph (Fin v)) :
    ∃ N, GraphRamseyProperty G N := by
  refine ⟨Ramsey.ramseyNumber v v, ?_⟩
  intro R
  have hRamsey := Ramsey.ramseyNumber_spec v v R
  have hGtop : G ⊑ completeGraph (Fin v) := IsContained.of_le le_top
  by_cases hR : R.CliqueFree v
  · right
    have hRc : ¬ Rᶜ.CliqueFree v := by
      intro h
      exact hRamsey ⟨hR, by simpa [cliqueFree_compl] using h⟩
    exact hGtop.trans ((Rᶜ.not_cliqueFree_iff_top_isContained v).mp hRc)
  · left
    exact hGtop.trans ((R.not_cliqueFree_iff_top_isContained v).mp hR)

/-- The least order of a complete graph which arrows `G` in two colours. -/
noncomputable def graphRamseyNumber {v : ℕ} (G : SimpleGraph (Fin v)) : ℕ :=
  sInf {N : ℕ | GraphRamseyProperty G N}

/-- The graph Ramsey number has its defining Ramsey property. -/
theorem graphRamseyNumber_spec {v : ℕ} (G : SimpleGraph (Fin v)) :
    GraphRamseyProperty G (graphRamseyNumber G) := by
  change sInf {N : ℕ | GraphRamseyProperty G N} ∈
    {N : ℕ | GraphRamseyProperty G N}
  exact csInf_mem (graphRamseyProperty_exists G)

/-- Any explicit host order with the Ramsey property bounds the least one. -/
theorem graphRamseyNumber_le_of_property {v N : ℕ} {G : SimpleGraph (Fin v)}
    (h : GraphRamseyProperty G N) :
    graphRamseyNumber G ≤ N :=
  csInf_le' h

/-- The fixed-target graph Ramsey property is monotone in the host order. -/
theorem graphRamseyProperty_mono {v N M : ℕ} {G : SimpleGraph (Fin v)}
    (hNM : N ≤ M) (h : GraphRamseyProperty G N) :
    GraphRamseyProperty G M := by
  intro R
  let e : Fin N ↪ Fin M := Fin.castLEEmb hNM
  rcases h (R.comap e) with hred | hblue
  · exact Or.inl <| hred.trans (SimpleGraph.Embedding.comap e R).isContained
  · exact Or.inr <| hblue.trans
      ⟨((SimpleGraph.Embedding.complEquiv (G := R.comap e) (H := R)).toFun
          (SimpleGraph.Embedding.comap e R)).toCopy⟩

/-! ## Monochromatic pairs -/

/-- `X,Y` form a monochromatic pair in `H` if they are disjoint, `X` is a
clique, and every edge from `X` to `Y` belongs to `H`.  There is deliberately no
condition on edges internal to `Y`. -/
def MonoPair {V : Type*} (H : SimpleGraph V)
    (X Y : Finset V) : Prop :=
  Disjoint X Y ∧ H.IsClique (↑X : Set V) ∧
    ∀ x ∈ X, ∀ y ∈ Y, H.Adj x y

/-- `X,Y` form a monochromatic pair in one of the two colours of `R`. -/
def HasMonoPair {V : Type*} (R : SimpleGraph V)
    (X Y : Finset V) : Prop :=
  MonoPair R X Y ∨ MonoPair Rᶜ X Y

theorem MonoPair.mono {V : Type*} {H : SimpleGraph V}
    {X Y X' Y' : Finset V} (h : MonoPair H X Y)
    (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    MonoPair H X' Y' := by
  refine ⟨h.1.mono hX hY, h.2.1.subset ?_, ?_⟩
  · exact_mod_cast hX
  · intro x hx y hy
    exact h.2.2 x (hX hx) y (hY hy)

theorem HasMonoPair.mono {V : Type*} {R : SimpleGraph V}
    {X Y X' Y' : Finset V} (h : HasMonoPair R X Y)
    (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    HasMonoPair R X' Y' := by
  rcases h with h | h
  · exact Or.inl (h.mono hX hY)
  · exact Or.inr (h.mono hX hY)

@[simp] theorem hasMonoPair_compl_iff {V : Type*} (R : SimpleGraph V)
    (X Y : Finset V) :
    HasMonoPair Rᶜ X Y ↔ HasMonoPair R X Y := by
  simp only [HasMonoPair, compl_compl]
  exact or_comm

/-! ## Denominator-free dyadic sparsity -/

/-- The number of ordered `H`-edges from `X` to `Y`. -/
noncomputable def crossEdgeCount {N : ℕ} (H : SimpleGraph (Fin N))
    (X Y : Finset (Fin N)) : ℕ := by
  classical
  exact (H.interedges X Y).card

/-- The number of ordered internal `H`-edges in `S`.  Thus every undirected
internal edge is counted in both orientations. -/
noncomputable def squareEdgeCount {N : ℕ} (H : SimpleGraph (Fin N))
    (S : Finset (Fin N)) : ℕ := by
  classical
  exact (H.interedges S S).card

/-- The density of `H` from `X` to `Y` is at most `2⁻ˣ`, written without
division so that empty sets cause no exceptional case. -/
def PairSparse {N : ℕ} (q : ℕ) (H : SimpleGraph (Fin N))
    (X Y : Finset (Fin N)) : Prop :=
  2 ^ q * crossEdgeCount H X Y ≤ X.card * Y.card

/-- The ordered internal density of `H` on `S` is at most `2⁻ˣ`. -/
def SquareSparse {N : ℕ} (q : ℕ) (H : SimpleGraph (Fin N))
    (S : Finset (Fin N)) : Prop :=
  2 ^ q * squareEdgeCount H S ≤ S.card * S.card

theorem crossEdgeCount_comm {N : ℕ} (H : SimpleGraph (Fin N))
    (X Y : Finset (Fin N)) :
    crossEdgeCount H X Y = crossEdgeCount H Y X := by
  classical
  have := H.symm
  exact Rel.card_interedges_comm (r := H.Adj) X Y

theorem pairSparse_comm {N q : ℕ} {H : SimpleGraph (Fin N)}
    {X Y : Finset (Fin N)} :
    PairSparse q H X Y ↔ PairSparse q H Y X := by
  simp only [PairSparse, crossEdgeCount_comm, Nat.mul_comm]

/-! ## The no-isolated-vertices edge bound -/

/-- A finite graph with no isolated vertices has at most twice as many vertices
as edges. -/
theorem noIsolated_card_le_twice_edges {v : ℕ} (G : SimpleGraph (Fin v))
    [DecidableRel G.Adj]
    (hG : ∀ x, ¬ G.IsIsolated x) :
    v ≤ 2 * G.edgeFinset.card := by
  classical
  calc
    v = ∑ _x : Fin v, 1 := by simp
    _ ≤ ∑ x : Fin v, G.degree x := by
      exact Finset.sum_le_sum fun x _ ↦ (G.degree_pos x).mpr (hG x)
    _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges

/-- If a finite graph without isolated vertices has no edges, its vertex type is
empty. -/
theorem card_eq_zero_of_noIsolated_of_edgeFinset_card_eq_zero {v : ℕ}
    (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (hG : ∀ x, ¬ G.IsIsolated x)
    (hm : G.edgeFinset.card = 0) :
    v = 0 := by
  have h := noIsolated_card_le_twice_edges G hG
  omega

/-- The zero-edge case of the Ramsey bound: once isolated vertices are
excluded, the target is the empty graph and its Ramsey number is zero. -/
theorem graphRamseyNumber_eq_zero_of_noIsolated_of_edgeFinset_card_eq_zero
    {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (hG : ∀ x, ¬ G.IsIsolated x)
    (hm : G.edgeFinset.card = 0) :
    graphRamseyNumber G = 0 := by
  have hv : v = 0 := card_eq_zero_of_noIsolated_of_edgeFinset_card_eq_zero G hG hm
  subst v
  apply Nat.eq_zero_of_le_zero
  apply graphRamseyNumber_le_of_property
  intro R
  left
  have hGbot : G = (⊥ : SimpleGraph (Fin 0)) := Subsingleton.elim _ _
  rw [hGbot, bot_isContained_iff_card_le]

end Erdos546
