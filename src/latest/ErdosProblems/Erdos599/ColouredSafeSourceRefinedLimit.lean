/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeFairSourceSelection
import ErdosProblems.Erdos599.ColouredSafeSourcePredecessorRefinement
import ErdosProblems.Erdos599.RootReachablePathRetention
import Mathlib.Data.Fintype.Order

/-!
# No reverse rays under native source-anchored predecessor refinement

The eventual full relation contains every stage real edge. Its incoming
edges at original sources are excluded by the actual source-cover clauses.
The finite old prefix to a hypothetical reverse-ray vertex, together with
the three-way predecessor refinement, gives a finite induction contradiction.
No fair enumeration or final target completion is used in this argument.
-/

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph.RealStageChain

open Set Cardinal DirectedPath Alternating ColouredSafeLocalTransactionRealLedger

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}} {I : Type v} [LinearOrder I] {frontier : I → Set V}

def eventualEdges (C : RealStageChain Gamma Y kappa I frontier) : Set (V × V) :=
  {e | ∃ i, ∀ j, i ≤ j → e ∈ familyEdges (C.stage j)}

theorem edgeUnion_subset_eventualEdges (C : RealStageChain Gamma Y kappa I frontier) :
    C.edgeUnion ⊆ C.eventualEdges := by
  intro e he
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
  exact ⟨i, fun j hij ↦ (C.edges_mono hij hi).1⟩

theorem eventualEdges_biUnique (C : RealStageChain Gamma Y kappa I frontier) :
    Relator.BiUnique fun x y ↦ (x, y) ∈ C.eventualEdges := by
  constructor
  · rintro x y z ⟨i, hi⟩ ⟨j, hj⟩
    exact (IsWarp.familyEdges_biUnique (C.warp (max i j))).1
      (hi _ (le_max_left _ _)) (hj _ (le_max_right _ _))
  · rintro x y z ⟨i, hi⟩ ⟨j, hj⟩
    exact (IsWarp.familyEdges_biUnique (C.warp (max i j))).2
      (hi _ (le_max_left _ _)) (hj _ (le_max_right _ _))

theorem eventualEdges_source_no_incoming (C : RealStageChain Gamma Y kappa I frontier)
    {a : V} (ha : a ∈ Gamma.source) : ¬HasIncoming C.eventualEdges a := by
  rintro ⟨x, i, hi⟩
  have he := hi i le_rfl
  have haV := (familyEdges_subset_vertexSet_prod (C.stage i) he).2
  rcases C.covers_source i ha with haInitial | haReference
  · rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp
      (C.warp i)] at haInitial
    exact haInitial.2 ⟨x, he⟩
  · obtain ⟨p, hp, hpa⟩ := haReference
    exact hp.2 ⟨hp.1.1, a, hpa ▸ p.initial_mem_support, haV⟩

/-- Trace a finite relation path backwards along a reverse ray using only
uniqueness of incoming edges. No simplicity assumption is needed here. -/
theorem exists_reverse_index_of_reaches
    {E : Set (V × V)} (hleft : Relator.LeftUnique fun x y ↦ (x, y) ∈ E)
    (r : ℕ → V) (hr : ∀ n, (r (n + 1), r n) ∈ E)
    {a b : V} (hab : Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b) :
    ∀ n, b = r n → ∃ m, a = r m := by
  induction hab with
  | refl => exact fun n h ↦ ⟨n, h⟩
  | @tail c d hac hcd ih =>
      intro n hdn
      have hcr : c = r (n + 1) := hleft (hdn ▸ hcd) (hr n)
      exact ih (n + 1) hcr

theorem eventualEdges_not_containsDirectedCycle
    (C : RealStageChain Gamma Y kappa I frontier) :
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

/-- The source alternative in predecessor refinement is sufficient to
rule out reverse rays; all old roots need not be original sources. -/
theorem eventualEdges_not_containsReverseDirectedRay
    (C : RealStageChain Gamma Y kappa I frontier)
    (hrefine : ∀ {i j}, i ≤ j → SourcePredecessorRefines (C.stage i) (C.stage j)) :
    ¬ContainsReverseDirectedRay C.eventualEdges := by
  rintro ⟨R, hR⟩
  obtain ⟨i, hi⟩ := hR 0
  have hheadV := (familyEdges_subset_vertexSet_prod (C.stage i) (hi i le_rfl)).2
  obtain ⟨p, hp, hR0p⟩ := hheadV
  have hprefix := RootReachableRelation.path_initial_reaches_of_mem_support
    (familyEdges (C.stage i)) p
    (fun _ he ↦ Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, he⟩⟩) hR0p
  have hrootV : p.initial ∈ (imaginaryWeb Y kappa).vertexSet (C.stage i) :=
    ⟨p, hp, p.initial_mem_support⟩
  have hrootNo : ¬HasIncoming (familyEdges (C.stage i)) p.initial := by
    have hrootI : p.initial ∈ (imaginaryWeb Y kappa).initialSet (C.stage i) :=
      ⟨p, hp, rfl⟩
    rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp
      (C.warp i)] at hrootI
    exact hrootI.2
  have noSource (a : V) (ha : a ∈ Gamma.source) {x : V}
      (hax : Relation.ReflTransGen (fun u v ↦ (u, v) ∈ C.eventualEdges) a x)
      (n : ℕ) (hxn : x = R.vertex n) : False := by
    obtain ⟨m, ham⟩ := exists_reverse_index_of_reaches
      C.eventualEdges_biUnique.1 R.vertex hR hax n hxn
    exact C.eventualEdges_source_no_incoming ha ⟨R.vertex (m + 1), ham ▸ hR m⟩
  have realToEventual {j : I} {a x : V} (hax : RealReach (C.stage j) a x) :
      Relation.ReflTransGen (fun u v ↦ (u, v) ∈ C.eventualEdges) a x :=
    Relation.ReflTransGen.mono
      (fun _ _ he ↦ C.edgeUnion_subset_eventualEdges (C.stage_edges_subset j he)) _ _ hax.2
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
        rcases hrefine (le_max_left i j0) hrootV hrj with hold | ⟨z, hz, _⟩ | ⟨a, ha, hax⟩
        · exact hrootNo ⟨_, hold⟩
        · exact hrootNo ⟨z, hz⟩
        · exact noSource a ha (realToEventual hax) n hpn
    | @tail u x hpu hux ih =>
        intro n hxn
        obtain ⟨j0, hj0⟩ := hR n
        let j := max i j0
        have hrj : (R.vertex (n + 1), x) ∈ familyEdges (C.stage j) :=
          hxn ▸ hj0 j (le_max_right _ _)
        have hxV := (familyEdges_subset_vertexSet_prod (C.stage i) hux).2
        rcases hrefine (le_max_left i j0) hxV hrj with hold | ⟨z, hz, hzx⟩ | ⟨a, ha, hax⟩
        · have hyu := (IsWarp.familyEdges_biUnique (C.warp i)).1 hold hux
          exact ih (n + 1) hyu.symm
        · have hzu := (IsWarp.familyEdges_biUnique (C.warp i)).1 hz hux
          obtain ⟨m, hzm⟩ := exists_reverse_index_of_reaches
            C.eventualEdges_biUnique.1 R.vertex hR (realToEventual hzx) n hxn
          exact ih m (hzu.symm.trans hzm)
        · exact noSource a ha (realToEventual hax) n hxn
  exact impossible hprefix 0 rfl

theorem edgeUnion_not_containsReverseDirectedRay
    (C : RealStageChain Gamma Y kappa I frontier)
    (hrefine : ∀ {i j}, i ≤ j → SourcePredecessorRefines (C.stage i) (C.stage j)) :
    ¬ContainsReverseDirectedRay C.edgeUnion := by
  rintro ⟨R, hR⟩
  exact C.eventualEdges_not_containsReverseDirectedRay hrefine
    ⟨R, fun n ↦ C.edgeUnion_subset_eventualEdges (hR n)⟩

#print axioms eventualEdges_not_containsDirectedCycle
#print axioms eventualEdges_not_containsReverseDirectedRay
#print axioms edgeUnion_not_containsReverseDirectedRay

end Erdos599.Blueprint.ColouredSafeShortcutGraph.RealStageChain
