/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Formalization Project
-/

import ErdosProblems.Erdos565.Events
import ErdosProblems.Erdos565.ExtensionAux
import Mathlib.Tactic

/-!
# Deleted-target supersaturation

This file implements the deterministic Section 6 step which applies the strong-induction event
after deleting one vertex from one target.  The target tuple and its order vector are constructed
explicitly.  If the induction event were won by an unchanged color, restriction and radius
monotonicity would contradict the localized bad event; hence the deleted color wins.
-/

open scoped BigOperators SimpleGraph

namespace Erdos565
namespace DeletedTarget

open Events

/-- Decrease coordinate `i` by one. -/
def decreaseAt {r : ℕ} (order : Fin r → ℕ) (i : Fin r) : Fin r → ℕ :=
  Function.update order i (order i - 1)

@[simp] theorem decreaseAt_self {r : ℕ} (order : Fin r → ℕ) (i : Fin r) :
    decreaseAt order i i = order i - 1 := by
  simp [decreaseAt]

@[simp] theorem decreaseAt_of_ne {r : ℕ} (order : Fin r → ℕ) {i j : Fin r}
    (hji : j ≠ i) : decreaseAt order i j = order j := by
  simp [decreaseAt, hji]

theorem decreaseAt_le {r : ℕ} (order : Fin r → ℕ) (i j : Fin r) :
    decreaseAt order i j ≤ order j := by
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

/-- Decreasing a positive coordinate lowers the total order by exactly one. -/
theorem totalOrder_decreaseAt {r : ℕ} (order : Fin r → ℕ) (i : Fin r)
    (hi : 0 < order i) :
    totalOrder (decreaseAt order i) + 1 = totalOrder order := by
  classical
  rw [totalOrder, totalOrder, decreaseAt,
    Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  omega

theorem totalOrder_decreaseAt_lt {r : ℕ} (order : Fin r → ℕ) (i : Fin r)
    (hi : 0 < order i) :
    totalOrder (decreaseAt order i) < totalOrder order := by
  have h := totalOrder_decreaseAt order i hi
  omega

theorem totalOrder_sub_decreaseAt {r : ℕ} (order : Fin r → ℕ) (i : Fin r)
    (hi : 0 < order i) :
    totalOrder order - totalOrder (decreaseAt order i) = 1 := by
  have h := totalOrder_decreaseAt order i hi
  omega

/-- The deleted vertex type has the expected cardinality. -/
theorem card_deletedVertices {n : ℕ} (root : Fin n) :
    Fintype.card (DeletedVertices root) = n - 1 := by
  simp [DeletedVertices]

/-- A canonical labelling of the vertices remaining after deleting `root`. -/
noncomputable def deletedVerticesEquivFin {n : ℕ} (root : Fin n) :
    DeletedVertices root ≃ Fin (n - 1) :=
  Fintype.equivFinOfCardEq (card_deletedVertices root)

/-- Delete `root` and relabel the remaining target by `Fin (n-1)`. -/
noncomputable def deleteVertexFin {n : ℕ} (F : SimpleGraph (Fin n)) (root : Fin n) :
    SimpleGraph (Fin (n - 1)) :=
  (deleteVertex F root).map (deletedVerticesEquivFin root).toEmbedding

/-- The canonical deletion is isomorphic to the literal induced deletion. -/
theorem deleteVertex_iso_deleteVertexFin {n : ℕ} (F : SimpleGraph (Fin n)) (root : Fin n) :
    Nonempty (deleteVertex F root ≃g deleteVertexFin F root) := by
  exact ⟨SimpleGraph.Iso.map (deletedVerticesEquivFin root) (deleteVertex F root)⟩

/-- Replace target `i` by its chosen one-vertex deletion. -/
noncomputable def targetsWithDeletion {r : ℕ} {order : Fin r → ℕ}
    (targets : TargetVector r order) (i : Fin r) (root : Fin (order i)) :
    TargetVector r (decreaseAt order i) := fun j ↦ by
  classical
  by_cases hji : j = i
  · subst j
    simpa [decreaseAt] using deleteVertexFin (targets i) root
  · simpa [decreaseAt, hji] using targets j

theorem targetsWithDeletion_self_heq {r : ℕ} {order : Fin r → ℕ}
    (targets : TargetVector r order) (i : Fin r) (root : Fin (order i)) :
    HEq (targetsWithDeletion targets i root i) (deleteVertexFin (targets i) root) := by
  simp [targetsWithDeletion]

theorem targetsWithDeletion_of_ne_heq {r : ℕ} {order : Fin r → ℕ}
    (targets : TargetVector r order) (i : Fin r) (root : Fin (order i))
    (j : Fin r) (hji : j ≠ i) :
    HEq (targetsWithDeletion targets i root j) (targets j) := by
  simp [targetsWithDeletion, hji]

universe u v

/-- A heterogeneous identification of target graphs induces equality of their copy
hypergraphs, once the target vertex types have been identified. -/
theorem copyHypergraph_eq_of_target_heq
    {U U' : Type u} {V : Type v} [Fintype V] [DecidableEq V]
    {F : SimpleGraph U} {F' : SimpleGraph U'}
    (hU : U = U') (hF : HEq F F') (G' G : SimpleGraph V) :
    copyHypergraph F G' G = copyHypergraph F' G' G := by
  cases hU
  rw [eq_of_heq hF]

/-- Deleted-target supersaturation in the global coordinates used by localization.

The size hypothesis is written with exponent one because the constructed target tuple loses
exactly one vertex.  The conclusion is the actual copy hypergraph of the chosen deletion; no
abstract supersaturation predicate is assumed. -/
theorem deletedTarget_isJanson
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {order : Fin r → ℕ}
    {pNum pDen deltaNum deltaDen shrinkDen : ℕ}
    {localRadius : ℝ}
    {targets : TargetVector r order} {G : SimpleGraph V}
    {S W : Finset V} (i : Fin r) (root : Fin (order i))
    (hi : 2 ≤ order i)
    (hstrong : StrongInductionEventGlobalOn pNum pDen deltaNum deltaDen
      shrinkDen order G)
    (coloring : G.EdgeLabeling (Fin r))
    (hWS : W ⊆ S)
    (hsize : MeetsDescendedSize deltaNum deltaDen shrinkDen 1
      (Fintype.card V) W.card)
    (hlocal : ∀ j,
      ¬ (((copyHypergraph (targets j) (colorClassGraph coloring j) G).restrict S).IsJanson
        (rationalParameter pNum pDen)
        localRadius))
    (hp : 0 < rationalParameter pNum pDen)
    (hlocalRadius : 0 ≤ localRadius)
    (hradius : localRadius ≤ jansonRadius pNum pDen W.card) :
    ((copyHypergraph (deleteVertexFin (targets i) root)
      (colorClassGraph coloring i) G).restrict W).IsJanson
        (rationalParameter pNum pDen) (jansonRadius pNum pDen W.card) := by
  classical
  let smaller := decreaseAt order i
  let smallerTargets := targetsWithDeletion targets i root
  have hiPos : 0 < order i := by omega
  have hcoord : ∀ j, smaller j ≤ order j := by
    intro j
    exact decreaseAt_le order i j
  have htotal : totalOrder smaller < totalOrder order := by
    exact totalOrder_decreaseAt_lt order i hiPos
  have hgap : totalOrder order - totalOrder smaller = 1 := by
    exact totalOrder_sub_decreaseAt order i hiPos
  have hsize' : MeetsDescendedSize deltaNum deltaDen shrinkDen
      (totalOrder order - totalOrder smaller) (Fintype.card V) W.card := by
    simpa [hgap] using hsize
  obtain ⟨j, hj⟩ :=
    hstrong smaller hcoord htotal smallerTargets W hsize' coloring
  by_cases hji : j = i
  · subst j
    have htarget : HEq (smallerTargets i) (deleteVertexFin (targets i) root) := by
      simpa [smallerTargets] using targetsWithDeletion_self_heq targets i root
    have hvertex : Fin (smaller i) = Fin (order i - 1) := by
      exact congrArg Fin (by simp [smaller])
    have hcopy := copyHypergraph_eq_of_target_heq hvertex htarget
      (colorClassGraph coloring i) G
    rw [hcopy] at hj
    exact hj
  · have htarget : HEq (smallerTargets j) (targets j) := by
      simpa [smallerTargets] using targetsWithDeletion_of_ne_heq targets i root j hji
    have hvertex : Fin (smaller j) = Fin (order j) := by
      exact congrArg Fin (by simp [smaller, hji])
    have hcopy := copyHypergraph_eq_of_target_heq hvertex htarget
      (colorClassGraph coloring j) G
    rw [hcopy] at hj
    have hj' :
        ((copyHypergraph (targets j) (colorClassGraph coloring j) G).restrict W).IsJanson
          (rationalParameter pNum pDen) (jansonRadius pNum pDen W.card) := by
      exact hj
    have hjS :
        ((copyHypergraph (targets j) (colorClassGraph coloring j) G).restrict S).IsJanson
          (rationalParameter pNum pDen) (jansonRadius pNum pDen W.card) :=
      Hypergraph.IsJanson.mono_edges
        (Hypergraph.restrict_mono_right _ hWS) hj'
    exact False.elim <| hlocal j <|
      Hypergraph.IsJanson.mono_params hjS hp (le_refl _)
        hlocalRadius hradius

end DeletedTarget
end Erdos565
