/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeAugmentedFullAccounting
import ErdosProblems.Erdos599.ColouredSafeAugmentedPredecessorRefinement
import ErdosProblems.Erdos599.ColouredSafeSourceRefinedLimit

/-!
# Accounted histories in an explicit augmented graph

The original and augmented webs are separate parameters. Only actual warp
incidence, monotone observables, target accounting and predecessor refinement
are required. In particular no identification of two imaginary graphs occurs.
-/

namespace Erdos599

open Set DirectedPath Alternating ColouredSafeLocalTransactionRealLedger
open ColouredSafeAugmentedRealReach

universe u v

structure AugmentedAccountedChain {V : Type u} (Gamma D : DWeb V) (I : Type v)
    [LinearOrder I] where
  stage : I → Set D.DPath
  warp : ∀ i, D.IsWarp (stage i)
  vertices_mono : Monotone (fun i ↦ D.vertexSet (stage i))
  edges_mono : Monotone (fun i ↦ RealEdges (Gamma := D) Gamma.graph.Adj (stage i))
  initials_mono : Monotone (fun i ↦ D.initialSet (stage i))
  source_no_incoming : ∀ i a, a ∈ Gamma.source → ¬HasIncoming (familyEdges (stage i)) a
  account : ∀ {i j}, i ≤ j → FullAccount Gamma D (stage i) (stage j) Gamma.target
  predecessor : ∀ {i j}, i ≤ j → SourcePredecessorRefines Gamma D (stage i) (stage j)

namespace AugmentedAccountedChain

variable {V : Type u} {Gamma D : DWeb V} {I : Type v} [LinearOrder I]

def vertexUnion (C : AugmentedAccountedChain Gamma D I) : Set V := ⋃ i, D.vertexSet (C.stage i)

def eventualEdges (C : AugmentedAccountedChain Gamma D I) : Set (V × V) :=
  {e | ∃ i, ∀ j, i ≤ j → e ∈ familyEdges (C.stage j)}

theorem stage_vertices_subset (C : AugmentedAccountedChain Gamma D I) (i : I) :
    D.vertexSet (C.stage i) ⊆ C.vertexUnion :=
  Set.subset_iUnion (fun j ↦ D.vertexSet (C.stage j)) i

theorem stage_realEdges_subset (C : AugmentedAccountedChain Gamma D I) (i : I) :
    RealEdges (Gamma := D) Gamma.graph.Adj (C.stage i) ⊆ C.eventualEdges := by
  intro e he
  exact ⟨i, fun j hij ↦ (C.edges_mono hij he).1⟩

theorem realReach_eventual (C : AugmentedAccountedChain Gamma D I)
    {i : I} {a b : V} (h : RealReach Gamma D (C.stage i) a b) :
    Relation.ReflTransGen (fun x y ↦ (x, y) ∈ C.eventualEdges) a b :=
  Relation.ReflTransGen.mono (fun _ _ he ↦ C.stage_realEdges_subset i he) _ _ h.2

theorem eventualEdges_biUnique (C : AugmentedAccountedChain Gamma D I) :
    Relator.BiUnique fun x y ↦ (x, y) ∈ C.eventualEdges := by
  constructor
  · rintro x y z ⟨i, hi⟩ ⟨j, hj⟩
    exact (IsWarp.familyEdges_biUnique (C.warp (max i j))).1
      (hi _ (le_max_left _ _)) (hj _ (le_max_right _ _))
  · rintro x y z ⟨i, hi⟩ ⟨j, hj⟩
    exact (IsWarp.familyEdges_biUnique (C.warp (max i j))).2
      (hi _ (le_max_left _ _)) (hj _ (le_max_right _ _))

theorem eventualEdges_adj (C : AugmentedAccountedChain Gamma D I) :
    C.eventualEdges ⊆ {e | D.graph.Adj e.1 e.2} := by
  rintro e ⟨i, hi⟩
  exact familyEdges_subset_adj (C.stage i) (hi i le_rfl)

theorem eventualEdges_endpoints (C : AugmentedAccountedChain Gamma D I) :
    ∀ e ∈ C.eventualEdges, e.1 ∈ C.vertexUnion ∧ e.2 ∈ C.vertexUnion := by
  rintro e ⟨i, hi⟩
  have hends := familyEdges_subset_vertexSet_prod (C.stage i) (hi i le_rfl)
  exact ⟨C.stage_vertices_subset i hends.1, C.stage_vertices_subset i hends.2⟩

theorem eventualEdges_source_no_incoming (C : AugmentedAccountedChain Gamma D I)
    {a : V} (ha : a ∈ Gamma.source) : ¬HasIncoming C.eventualEdges a := by
  rintro ⟨x, i, hi⟩
  exact C.source_no_incoming i a ha ⟨x, hi i le_rfl⟩

theorem eventualEdges_not_containsDirectedCycle (C : AugmentedAccountedChain Gamma D I) :
    ¬ContainsDirectedCycle C.eventualEdges := by
  classical
  rintro ⟨Q, hQ⟩
  let stageOf : Fin Q.length → I := fun n ↦ Classical.choose (hQ ⟨n, rfl⟩)
  have hstageOf (n : Fin Q.length) : ∀ j, stageOf n ≤ j →
      (Q.vertex n, Q.vertex (Q.next n)) ∈ familyEdges (C.stage j) :=
    Classical.choose_spec (hQ ⟨n, rfl⟩)
  let first : Fin Q.length := ⟨0, Q.positive⟩
  let : Nonempty I := ⟨stageOf first⟩
  obtain ⟨j, hj⟩ := Finite.exists_le stageOf
  apply PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsDirectedCycle (C.warp j)
  exact ⟨Q, fun _ ⟨n, he⟩ ↦ he ▸ hstageOf n j (hj n)⟩

/-- The three-way source-anchored predecessor certificate rules out reverse
rays by induction on one old finite initial prefix. -/
theorem eventualEdges_not_containsReverseDirectedRay
    (C : AugmentedAccountedChain Gamma D I) : ¬ContainsReverseDirectedRay C.eventualEdges := by
  rintro ⟨R, hR⟩
  obtain ⟨i, hi⟩ := hR 0
  have hheadV := (familyEdges_subset_vertexSet_prod (C.stage i) (hi i le_rfl)).2
  obtain ⟨p, hp, hR0p⟩ := hheadV
  have hprefix := RootReachableRelation.path_initial_reaches_of_mem_support
    (familyEdges (C.stage i)) p
    (fun _ he ↦ Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, he⟩⟩) hR0p
  have hrootV : p.initial ∈ D.vertexSet (C.stage i) := ⟨p, hp, p.initial_mem_support⟩
  have hrootNo : ¬HasIncoming (familyEdges (C.stage i)) p.initial := by
    have hrootI : p.initial ∈ D.initialSet (C.stage i) := ⟨p, hp, rfl⟩
    rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp
      (C.warp i)] at hrootI
    exact hrootI.2
  have noSource (a : V) (ha : a ∈ Gamma.source) {x : V}
      (hax : Relation.ReflTransGen (fun u v ↦ (u, v) ∈ C.eventualEdges) a x)
      (n : Nat) (hxn : x = R.vertex n) : False := by
    obtain ⟨m, ham⟩ :=
      Blueprint.ColouredSafeShortcutGraph.RealStageChain.exists_reverse_index_of_reaches
        C.eventualEdges_biUnique.1 R.vertex hR hax n hxn
    exact C.eventualEdges_source_no_incoming ha ⟨R.vertex (m + 1), ham ▸ hR m⟩
  have impossible : ∀ {x : V},
      Relation.ReflTransGen (fun u v ↦ (u, v) ∈ familyEdges (C.stage i)) p.initial x →
      ∀ n, x = R.vertex n → False := by
    intro x hpx
    induction hpx with
    | refl =>
        intro n hpn
        obtain ⟨j0, hj0⟩ := hR n
        let j := max i j0
        have hrj : (R.vertex (n + 1), p.initial) ∈ familyEdges (C.stage j) :=
          hpn ▸ hj0 j (le_max_right _ _)
        rcases C.predecessor (le_max_left i j0) hrootV hrj with
          hold | ⟨z, hz, _⟩ | ⟨a, ha, hax⟩
        · exact hrootNo ⟨_, hold⟩
        · exact hrootNo ⟨z, hz⟩
        · exact noSource a ha (C.realReach_eventual hax) n hpn
    | @tail u x hpu hux ih =>
        intro n hxn
        obtain ⟨j0, hj0⟩ := hR n
        let j := max i j0
        have hrj : (R.vertex (n + 1), x) ∈ familyEdges (C.stage j) :=
          hxn ▸ hj0 j (le_max_right _ _)
        have hxV := (familyEdges_subset_vertexSet_prod (C.stage i) hux).2
        rcases C.predecessor (le_max_left i j0) hxV hrj with
          hold | ⟨z, hz, hzx⟩ | ⟨a, ha, hax⟩
        · have hyu := (IsWarp.familyEdges_biUnique (C.warp i)).1 hold hux
          exact ih (n + 1) hyu.symm
        · have hzu := (IsWarp.familyEdges_biUnique (C.warp i)).1 hz hux
          obtain ⟨m, hzm⟩ :=
            Blueprint.ColouredSafeShortcutGraph.RealStageChain.exists_reverse_index_of_reaches
              C.eventualEdges_biUnique.1 R.vertex hR (C.realReach_eventual hzx) n hxn
          exact ih m (hzu.symm.trans hzm)
        · exact noSource a ha (C.realReach_eventual hax) n hxn
  exact impossible hprefix 0 rfl

#print axioms eventualEdges_not_containsDirectedCycle
#print axioms eventualEdges_not_containsReverseDirectedRay

end AugmentedAccountedChain
end Erdos599
