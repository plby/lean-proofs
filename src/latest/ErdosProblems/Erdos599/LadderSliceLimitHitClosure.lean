/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderSliceGeometry
import ErdosProblems.Erdos599.LadderLimitHitClosure

/-!
# Limit-hit closure from marker-independent slice geometry

The existing persistence proof uses only successor inessential persistence,
threadwise limits and strict-roof monotonicity. This interface makes those
dependencies explicit and applies to the actual unroofed ladder. It never
manufactures the historical split-legality or marker-exhaustion predicates.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder

open Set Cardinal Order Ladder

universe u

variable {V : Type u} {G : DWeb V} {κ : Cardinal.{u}} {L : G.KappaLadder κ}

theorem SliceGeometry.strictRoof_frontier_mono (hL : L.SliceGeometry)
    {a b : Stage κ} (hab : a ≤ b) :
    G.strictRoof (L.frontier a) ⊆ G.strictRoof (L.frontier b) := by
  rcases hab.lt_or_eq with hab | rfl
  · intro x hx
    constructor
    · exact G.roof_cut (hL.frontierChronology hab) hx.1
    · intro hxEssential
      have hxFrontier : x ∈ L.frontier b := by
        rw [← hL.frontiersEssential b]
        exact hxEssential
      exact Set.disjoint_left.1 (hL.strictFrontierChronology hab) hx hxFrontier
  · exact fun _ hx ↦ hx

/-- Inessential components persist between ordinary stages of every legal
ladder.  Successors use the explicit legality clause; limits use the genuine
threadwise limit and strict-frontier chronology. -/
theorem SliceGeometry.inessentialPaths_mono_stage (hL : L.SliceGeometry)
    {a b : Stage κ} (hab : a ≤ b) :
    G.inessentialPaths (L.warpAt a) ⊆
      G.inessentialPaths (L.warpAt b) := by
  let accumulatedAt (o : Ordinal.{u}) (ho : o < κ.ord) :=
    L.accumulated (⟨o, ho.le⟩ : ExtendedStage κ)
  have hmain : ∀ o : Ordinal.{u}, ∀ ho : o < κ.ord,
      ∀ c : Ordinal.{u}, c ≤ o → ∀ hc : c < κ.ord,
        G.inessentialPaths (accumulatedAt c hc) ⊆
          G.inessentialPaths (accumulatedAt o ho) := by
    intro o
    induction o using Ordinal.limitRecOn with
    | zero =>
        intro ho c hc hcκ
        have hc0 : c = 0 := le_antisymm hc bot_le
        subst c
        exact Set.Subset.rfl
    | add_one o ih =>
        intro ho c hc hcκ p hp
        rcases hc.lt_or_eq with hc | rfl
        · have hco : c ≤ o := (Order.lt_add_one_iff).1 hc
          have hoκ : o < κ.ord :=
            (show o < o + 1 by
              rw [← Order.succ_eq_add_one]
              exact Order.lt_succ o).trans ho
          have hpO := ih hoκ c hco hcκ hp
          let os : Stage κ := ⟨o, hoκ⟩
          have hpNext := hL.currentInessentialPersists os hpO
          exact hpNext
        · exact hp
    | limit o hoLimit ih =>
        intro hoκ c hc hcκ p hp
        rcases hc.lt_or_eq with hc | rfl
        · let oe : ExtendedStage κ := ⟨o, hoκ.le⟩
          obtain ⟨C, hstage, hlimit⟩ := hL.limitStages oe hoLimit
          let : Nonempty (Set.Iio o) := hoLimit.nonempty_Iio.to_subtype
          let ci : Set.Iio o := ⟨c, hc⟩
          have hpCi : p ∈ G.inessentialPaths (C.stage ci) := by
            rw [hstage ci]
            exact hp
          have hpTail : ∀ d, ci ≤ d →
              p ∈ G.inessentialPaths (C.stage d) := by
            intro d hcd
            rw [hstage d]
            apply ih d.1 d.2 (d.2.trans hoκ) c hcd hcκ
            exact hp
          have hstrict :
              G.strictRoof (G.terminalFrontier (C.stage ci)) ⊆
                G.strictRoof (G.terminalFrontier (C.limitPaths G)) := by
            rw [hstage ci, ← hlimit]
            let cs : Stage κ := ⟨c, hcκ⟩
            let os : Stage κ := ⟨o, hoκ⟩
            change
              G.strictRoof (G.terminalFrontier (L.warpAt cs)) ⊆
                G.strictRoof (G.terminalFrontier (L.warpAt os))
            have hfront := hL.strictRoof_frontier_mono
              (show cs ≤ os from hc.le)
            simpa only [
              L.frontier_eq_essential_terminalFrontier
                hL.roofsSourceAtStages,
              G.strictRoof_essential] using hfront
          change p ∈ G.inessentialPaths (L.accumulated oe)
          rw [hlimit]
          exact C.mem_inessentialPaths_limitPaths_of_tail
            ci hpCi hpTail hstrict
        · exact hp
  exact hmain b.1 b.2 a.1 hab a.2

/-- An inessential ordinary-stage component occurs literally in the final
ladder warp.  At the final direct limit its thread is eventually constant. -/
theorem SliceGeometry.mem_limitWarp_of_mem_inessential (hL : L.SliceGeometry)
    {a : Stage κ} {p : G.DPath}
    (hp : p ∈ G.inessentialPaths (L.warpAt a)) :
    p ∈ L.limitWarp := by
  have hκLimit : Order.IsSuccLimit κ.ord :=
    Cardinal.isSuccLimit_ord hL.regular.aleph0_le
  obtain ⟨C, hstage, hlimit⟩ :=
    hL.limitStages (Ladder.finalStage κ) hκLimit
  let : Nonempty (Set.Iio κ.ord) := hκLimit.nonempty_Iio.to_subtype
  let ai : Set.Iio κ.ord := ⟨a.1, a.2⟩
  have hpAi : p ∈ C.stage ai := by
    rw [hstage ai]
    exact hp.1
  have hpTail : ∀ b, ai ≤ b → p ∈ C.stage b := by
    intro b hab
    rw [hstage b]
    let bs : Stage κ := ⟨b.1, b.2⟩
    exact (hL.inessentialPaths_mono_stage
      (a := a) (b := bs) hab hp).1
  change p ∈ L.accumulated (Ladder.finalStage κ)
  rw [hlimit]
  exact C.mem_limitPaths_of_tail ai hpAi hpTail

/-- A component of an ordinary stage which meets a component of the final
warp extends to that very final component.  Both extensions belong to the
final warp, where path disjointness makes the continuation unique. -/
theorem SliceGeometry.extends_limitWarp_of_stage_intersects (hL : L.SliceGeometry)
    {a : Stage κ} {q p : G.DPath}
    (hq : q ∈ L.warpAt a) (hp : p ∈ L.limitWarp)
    (hqp : (q.support ∩ p.support).Nonempty) :
    G.Extends q p := by
  have hκLimit : Order.IsSuccLimit κ.ord :=
    Cardinal.isSuccLimit_ord hL.regular.aleph0_le
  obtain ⟨r, hr, hqr⟩ := hL.limitStages.grows_to_limit
    (Ladder.finalStage κ) hκLimit ⟨a.1, a.2⟩ q hq
  have hrpMeet : (r.support ∩ p.support).Nonempty := by
    obtain ⟨x, hxq, hxp⟩ := hqp
    exact ⟨x, G.support_mono_of_extends hqr hxq, hxp⟩
  have hrp : r = p := by
    by_contra hne
    obtain ⟨x, hxr, hxp⟩ := hrpMeet
    exact Set.disjoint_left.1
      (hL.warpStages (Ladder.finalStage κ) hr hp hne) hxr hxp
  rwa [hrp] at hqr

/-- Every hit of a limiting ladder path is witnessed by an essential
component of the corresponding accumulated warp. -/
theorem SliceGeometry.limitWarp_hitStages_essential_prefix (hL : L.SliceGeometry)
    {p : G.DPath} (_hp : p ∈ L.limitWarp)
    (Sigma : Set (Stage κ)) :
    ∀ a ∈ L.hitStages Sigma p,
      ∃ q ∈ G.essentialWarpPart (L.warpAt a),
        (p.support ∩ q.support).Nonempty := by
  intro a ha
  obtain ⟨x, hxFrontier, hxp⟩ := ha.2
  have hxEssential :
      x ∈ G.essential (G.terminalFrontier (L.warpAt a)) := by
    rwa [← L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages a]
  have hxTerminal :
      x ∈ G.terminalFrontier (G.essentialWarpPart (L.warpAt a)) := by
    rwa [G.terminalFrontier_essentialWarpPart]
  obtain ⟨q, hq, hqx⟩ := hxTerminal
  exact ⟨q, hq, x, hxp, G.terminal_mem_support hqx⟩

/-- Closed frontier-hit stages use the actual limit-miss certificate, not
an assumption that arbitrary limits remain essential. -/
theorem SliceGeometry.hitStages_isClosed (hL : L.SliceGeometry)
    (Sigma : Set (Stage κ)) (p : G.DPath)
    (hSigma : Stationary.IsClubBelow κ Sigma)
    (hprefix : ∀ a ∈ L.hitStages Sigma p,
      ∃ q ∈ G.essentialWarpPart (L.warpAt a), (p.support ∩ q.support).Nonempty)
    (hmiss : L.LimitMissIsInessential Sigma p) (havoid : Disjoint Sigma L.phi) :
    DirSupClosed (L.hitStages Sigma p) :=
  L.hitStages_isClosed Sigma p hSigma hL.warpStages hL.recordedPathsPersist hprefix hmiss
    (fun a hp ↦ hL.currentInessentialPersists a hp) havoid

#print axioms SliceGeometry.strictRoof_frontier_mono
#print axioms SliceGeometry.inessentialPaths_mono_stage
#print axioms SliceGeometry.mem_limitWarp_of_mem_inessential
#print axioms SliceGeometry.extends_limitWarp_of_stage_intersects
#print axioms SliceGeometry.limitWarp_hitStages_essential_prefix
#print axioms SliceGeometry.hitStages_isClosed

end Erdos599.DWeb.KappaLadder
