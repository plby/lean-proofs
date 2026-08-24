/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset
open scoped SimpleGraph

namespace Erdos1019

def problemThreshold (n : ℕ) : ℕ := n * n / 4 + (n + 1) / 2

def bipyramidGraph (l : ℕ) : SimpleGraph (Fin l ⊕ Bool) where
  Adj u v := match u, v with
    | Sum.inl i, Sum.inl j => (SimpleGraph.cycleGraph l).Adj i j
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    intro u v h
    rcases u with i | p <;> rcases v with j | q
    · exact ((SimpleGraph.cycleGraph l).adj_comm i j).mp h
    · exact h
    · exact h
    · exact h⟩
  loopless := ⟨by
    intro u
    cases u <;> simp⟩

def CanonicalPlanarTriangulationModel {W : Type*} (H : SimpleGraph W) : Prop :=
  Nonempty (H ≃g (⊤ : SimpleGraph (Fin 4))) ∨
    ∃ l : ℕ, 3 ≤ l ∧ Nonempty (H ≃g bipyramidGraph l)

def IsCertifiedSaturatedPlanar {W : Type*} [Fintype W]
    (H : SimpleGraph W) : Prop :=
  CanonicalPlanarTriangulationModel H ∧
    3 < Fintype.card W ∧
    H.edgeSet.ncard = 3 * Fintype.card W - 6

structure SaturatedPlanarSubgraph (V : Type*) (G : SimpleGraph V) where
  W : Type
  fintypeW : Fintype W
  H : SimpleGraph W
  certified : @IsCertifiedSaturatedPlanar W fintypeW H
  copy : H ⊑ G

def ContainsSaturatedPlanarBeyondTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (SaturatedPlanarSubgraph V G)

theorem erdos_1019 {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hE : #G.edgeFinset = problemThreshold (Fintype.card V)) :
    ContainsSaturatedPlanarBeyondTriangle G := by
  sorry

end Erdos1019
