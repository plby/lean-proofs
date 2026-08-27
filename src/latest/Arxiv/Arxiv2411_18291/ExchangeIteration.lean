import Arxiv.Arxiv2411_18291.PrepareEdge
import Mathlib.Tactic.Ring

/-! # Iterating the two-attachment construction over a finite edge set -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem exists_prepared_subfamily_with_vertex_bound
    (E : ExchangeSeed V q r) (hr : 0 < r) (hqr : r < q)
    (s : Finset (Block V r)) : s ⊆ cliqueEdges r E.positiveClique →
    ∃ T : FiniteExchangeSystem q r, ∃ f : V ↪ T.Vertex,
      T.system.base = mapBlock f E.positiveClique ∧
      (∃ P : PreparedFamily T.system.graph T.system.negative T.system.base s
        (fun i => mapBlock f i), P.Protects T.system.positive) ∧
      T.system.graph.card ≤ (2 * s.card + 1) * E.graph.card ∧
      (IsCrossSimple r E.positive E.negative →
        IsCrossSimple r T.system.positive T.system.negative) ∧
      Fintype.card T.Vertex ≤ (2 * s.card + 1) * Fintype.card V := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨E.toSystem.toFinite, Function.Embedding.refl V, ?_, ?_, ?_, ?_, ?_⟩
    · simp [ExchangeSeed.toSystem, ExchangeSystem.toFinite]
    · exact ⟨PreparedFamily.empty _ _ _ _, PreparedFamily.empty_protects _ _ _ _ _⟩
    · simp [ExchangeSeed.toSystem, ExchangeSystem.toFinite]
    · exact fun h => h
    · simp only [ExchangeSystem.toFinite, card_empty, mul_zero, zero_add, one_mul]
      exact le_rfl
  | @insert j s hj ih =>
    intro hs
    obtain ⟨T, f, hB, ⟨P, hP⟩, hcard, hcross, hvertices⟩ :=
      ih (fun i hi => hs (mem_insert_of_mem hi))
    have hjB : (mapBlock f j).val ⊆ T.system.base.val := by
      rw [hB, mapBlock_subset_mapBlock]
      exact (mem_cliqueEdges j E.positiveClique).mp (hs (mem_insert_self j s))
    obtain ⟨T', g, hB', ⟨P', hP'⟩, hcard', hcross', hvertices'⟩ :=
      exists_prepare_edge_with_vertex_bound T.system E hr hqr P (mapBlock_injective f) j hj hjB
    refine ⟨T', f.trans g, ?_, ?_, ?_, ?_, ?_⟩
    · exact hB'.trans ((congrArg (mapBlock g) hB).trans (mapBlock_map f g E.positiveClique))
    · have hw : ∃ P'' : PreparedFamily T'.system.graph T'.system.negative T'.system.base
          (insert j s) (fun i => mapBlock g (mapBlock f i)),
          P''.Protects T'.system.positive := ⟨P', hP' hP⟩
      have heq : (fun i : Block V r => mapBlock g (mapBlock f i)) =
          (fun i => mapBlock (f.trans g) i) := funext fun i => mapBlock_map f g i
      exact (congrArg (fun edge' => ∃ P'' : PreparedFamily T'.system.graph T'.system.negative
        T'.system.base (insert j s) edge', P''.Protects T'.system.positive) heq).mp hw
    · rw [card_insert_of_notMem hj]
      calc
        T'.system.graph.card ≤ T.system.graph.card + 2 * E.graph.card := hcard'
        _ ≤ (2 * s.card + 1) * E.graph.card + 2 * E.graph.card := Nat.add_le_add_right hcard _
        _ = _ := by ring
    · exact fun hE => hcross' (hcross hE) hE
    · rw [card_insert_of_notMem hj]
      calc
        _ ≤ Fintype.card T.Vertex + 2 * Fintype.card V := hvertices'
        _ ≤ (2 * s.card + 1) * Fintype.card V + 2 * Fintype.card V :=
          Nat.add_le_add_right hvertices _
        _ = _ := by ring

/-- The original interface, retaining the stronger construction internally. -/
theorem exists_prepared_subfamily (E : ExchangeSeed V q r) (hr : 0 < r) (hqr : r < q)
    (s : Finset (Block V r)) (hs : s ⊆ cliqueEdges r E.positiveClique) :
    ∃ T : FiniteExchangeSystem q r, ∃ f : V ↪ T.Vertex,
      T.system.base = mapBlock f E.positiveClique ∧
      (∃ P : PreparedFamily T.system.graph T.system.negative T.system.base s
        (fun i => mapBlock f i), P.Protects T.system.positive) ∧
      T.system.graph.card ≤ (2 * s.card + 1) * E.graph.card ∧
      (IsCrossSimple r E.positive E.negative →
        IsCrossSimple r T.system.positive T.system.negative) := by
  obtain ⟨T, f, hb, hp, hc, hs', _⟩ :=
    exists_prepared_subfamily_with_vertex_bound E hr hqr s hs
  exact ⟨T, f, hb, hp, hc, hs'⟩

end Arxiv2411_18291
