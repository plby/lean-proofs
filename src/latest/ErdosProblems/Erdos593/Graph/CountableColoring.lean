import ErdosProblems.Erdos593.Graph.FiniteOutdegreeColoring
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Nat.Pairing

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Countable graph colouring interfaces

This file turns the set-family compactness result in
`FiniteOutdegreeColoring` into graph colourings and packages the layer-product
argument used in manuscript Lemma 2.1. The genuinely infinitary construction
of a small closed layer decomposition is deliberately kept separate.
-/

namespace Erdos593

universe u v

namespace SimpleGraph

variable {V : Type u}

/-- A graph is countably colourable when it has a proper colouring by natural
numbers. -/
def CountablyColorable (G : _root_.SimpleGraph V) : Prop :=
  Nonempty (G.Coloring ℕ)

theorem CountablyColorable.comap {W : Type v} {G : _root_.SimpleGraph V}
    {H : _root_.SimpleGraph W} (hH : CountablyColorable H) (f : G →g H) :
    CountablyColorable G := by
  rcases hH with ⟨C⟩
  exact ⟨C.comap f⟩

theorem CountablyColorable.induce (G : _root_.SimpleGraph V)
    (hG : CountablyColorable G) (s : Set V) :
    CountablyColorable (G.induce s) :=
  hG.comap (_root_.SimpleGraph.Embedding.induce s).toHom

/-- A graph whose edges are covered by uniformly finite directed target sets
has the finite `2*d+1` colouring supplied by de Bruijn--Erdős/Rado
compactness. -/
theorem coloring_of_finite_targets (G : _root_.SimpleGraph V)
    (targets : V → Finset V) (d : ℕ)
    (hcard : ∀ x, (targets x).card ≤ d)
    (hcover : ∀ {x y : V}, G.Adj x y →
      y ∈ targets x ∨ x ∈ targets y) :
    Nonempty (G.Coloring (Fin (2 * d + 1))) := by
  classical
  obtain ⟨color, hcolor⟩ :=
    FiniteOutdegreeColoring.exists_coloring targets d hcard
  refine ⟨_root_.SimpleGraph.Coloring.mk color ?_⟩
  intro x y hxy
  exact hcolor (G.ne_of_adj hxy) (hcover hxy)

/-- The graph-facing bounded-outdegree orientation lemma. `targets x` is the
set of heads of arrows with tail `x`; every undirected edge must be assigned in
at least one direction. -/
theorem countablyColorable_of_finite_targets (G : _root_.SimpleGraph V)
    (targets : V → Finset V) (d : ℕ)
    (hcard : ∀ x, (targets x).card ≤ d)
    (hcover : ∀ {x y : V}, G.Adj x y →
      y ∈ targets x ∨ x ∈ targets y) :
    CountablyColorable G := by
  rcases coloring_of_finite_targets G targets d hcard hcover with ⟨C⟩
  refine ⟨_root_.SimpleGraph.Coloring.mk (fun x ↦ (C x).val) ?_⟩
  intro x y hxy hEq
  exact C.valid hxy (Fin.ext hEq)

/-- Combine a countable colouring of each rank fibre with a finite colouring
of all cross-rank edges. -/
theorem countablyColorable_of_within_and_cross
    (G : _root_.SimpleGraph V) {I : Type v} (rank : V → I)
    (within : V → ℕ) {k : ℕ} (cross : V → Fin k)
    (hwithin : ∀ {x y : V}, G.Adj x y → rank x = rank y →
      within x ≠ within y)
    (hcross : ∀ {x y : V}, G.Adj x y → rank x ≠ rank y →
      cross x ≠ cross y) :
    CountablyColorable G := by
  refine ⟨_root_.SimpleGraph.Coloring.mk
    (fun x ↦ Nat.pair (within x) (cross x).val) ?_⟩
  intro x y hxy hEq
  have hp := Nat.pair_eq_pair.mp hEq
  by_cases hrank : rank x = rank y
  · exact hwithin hxy hrank hp.1
  · exact hcross hxy hrank (Fin.ext hp.2)

/-- The exact reusable layer lemma behind the graph argument. If every rank
fibre is countably colourable and every vertex has at most `d` neighbours of
smaller rank, then the whole graph is countably colourable.

No well-foundedness or cardinal assumption on the rank type is needed here;
those belong only to the construction of the ranks. -/
theorem countablyColorable_of_finite_back_neighbors
    (G : _root_.SimpleGraph V) {I : Type v} [LinearOrder I]
    (rank : V → I) (d : ℕ)
    (hfinite : ∀ x : V,
      Set.Finite {y : V | G.Adj x y ∧ rank y < rank x})
    (hcard : ∀ x : V,
      (hfinite x).toFinset.card ≤ d)
    (hfiber : ∀ i : I,
      CountablyColorable (G.induce {x : V | rank x = i})) :
    CountablyColorable G := by
  classical
  let targets : V → Finset V := fun x ↦ (hfinite x).toFinset
  have htargets_card : ∀ x, (targets x).card ≤ d := by
    intro x
    exact hcard x
  have htargets_cover : ∀ {x y : V}, G.Adj x y → rank x ≠ rank y →
      y ∈ targets x ∨ x ∈ targets y := by
    intro x y hxy hne
    rcases lt_or_gt_of_ne hne with hxyRank | hyxRank
    · right
      simp only [targets, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact ⟨hxy.symm, hxyRank⟩
    · left
      simp only [targets, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact ⟨hxy, hyxRank⟩
  let crossGraph : _root_.SimpleGraph V :=
    _root_.SimpleGraph.fromRel fun x y ↦ G.Adj x y ∧ rank x ≠ rank y
  have hcross_cover : ∀ {x y : V}, crossGraph.Adj x y →
      y ∈ targets x ∨ x ∈ targets y := by
    intro x y hxy
    rcases hxy.2 with h | h
    · exact htargets_cover h.1 h.2
    · exact htargets_cover h.1.symm h.2.symm
  obtain ⟨cross⟩ :=
    coloring_of_finite_targets crossGraph targets d htargets_card hcross_cover
  let layerColor : ∀ i : I,
      (G.induce {x : V | rank x = i}).Coloring ℕ := fun i ↦
    Classical.choice (hfiber i)
  let fiberColor : I → V → ℕ := fun i x ↦
    if hx : rank x = i then layerColor i ⟨x, hx⟩ else 0
  have hfiberColor (i : I) {x y : V} (hxy : G.Adj x y)
      (hx : rank x = i) (hy : rank y = i) :
      fiberColor i x ≠ fiberColor i y := by
    simp only [fiberColor, dif_pos hx, dif_pos hy]
    exact (layerColor i).valid hxy
  let within : V → ℕ := fun x ↦ fiberColor (rank x) x
  have hwithin : ∀ {x y : V}, G.Adj x y → rank x = rank y →
      within x ≠ within y := by
    intro x y hxy hrank
    change fiberColor (rank x) x ≠ fiberColor (rank y) y
    rw [hrank]
    exact hfiberColor (rank y) hxy hrank rfl
  apply countablyColorable_of_within_and_cross G rank within cross hwithin
  intro x y hxy hne
  exact cross.valid ⟨G.ne_of_adj hxy, Or.inl ⟨hxy, hne⟩⟩

end SimpleGraph

end Erdos593
