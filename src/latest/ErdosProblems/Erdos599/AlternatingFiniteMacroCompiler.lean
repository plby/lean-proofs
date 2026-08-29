/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingMacroAssembly
import ErdosProblems.Erdos599.AlternatingMacroProvenance
import ErdosProblems.Erdos599.FiniteChronologicalErasure
import ErdosProblems.Erdos599.FiniteMacroRouteProvenance

/-!
# The finite endpoint-pure macro compiler

This file isolates the finite analogue of the tagged provenance interface
used by the infinite macro compiler.  It also supplies the complete generic
compiler: bounded chronological erasure followed by maximal-run compression
preserves literal labels and unique backward owners.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u v

variable {V : Type u} {Γ : DWeb V}

/-- Tagged, orientation-aware provenance for a positive finite raw walk. -/
structure FiniteEdgeProvenance {N : ℕ} (f : Fin (N + 1) → V)
    (Z Y : Set Γ.DPath) (M : Type v) where
  member : Fin N → M
  colour : M → Direction
  carrier : M → Γ.DPath
  carrier_injective_on_colour : ∀ {a b : M},
    colour a = colour b → carrier a = carrier b → a = b
  carrier_mem_forward : ∀ a, colour a = .forward → carrier a ∈ Z
  carrier_mem_backward : ∀ a, colour a = .backward → carrier a ∈ Y
  edge_mem_forward : ∀ i, colour (member i) = .forward →
    (f ⟨i.1, by omega⟩, f ⟨i.1 + 1, by omega⟩) ∈ (carrier (member i)).edgeSet
  edge_mem_backward : ∀ i, colour (member i) = .backward →
    (f ⟨i.1 + 1, by omega⟩, f ⟨i.1, by omega⟩) ∈ (carrier (member i)).edgeSet
  member_convex : ∀ {i j k : Fin N}, i ≤ j → j ≤ k →
    member i = member k → member j = member i

namespace FiniteEdgeProvenance

variable {Z Y : Set Γ.DPath} {M : Type v} {N : ℕ}
variable {f : Fin (N + 1) → V}

/-- Same-colour raw edges which join through a vertex have the same tagged
owner. -/
theorem member_eq_of_colour_eq_of_join
    (P : FiniteEdgeProvenance f Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    {i j : Fin N}
    (hcolour : P.colour (P.member i) = P.colour (P.member j))
    (hjoin : f ⟨i.1 + 1, by omega⟩ = f ⟨j.1, by omega⟩) :
    P.member i = P.member j := by
  cases hi : P.colour (P.member i) with
  | forward =>
      have hj : P.colour (P.member j) = .forward := hcolour.symm.trans hi
      have hei := P.edge_mem_forward i hi
      have hej := P.edge_mem_forward j hj
      have hxi : f ⟨i.1 + 1, by omega⟩ ∈ (P.carrier (P.member i)).support :=
        ((P.carrier (P.member i)).edgeSet_subset_support_prod hei).2
      have hxj : f ⟨i.1 + 1, by omega⟩ ∈ (P.carrier (P.member j)).support := by
        rw [hjoin]
        exact ((P.carrier (P.member j)).edgeSet_subset_support_prod hej).1
      have hc : P.carrier (P.member i) = P.carrier (P.member j) :=
        DWeb.IsWarp.eq_of_mem_support hZ
          (P.carrier_mem_forward _ hi) (P.carrier_mem_forward _ hj) hxi hxj
      exact P.carrier_injective_on_colour hcolour hc
  | backward =>
      have hj : P.colour (P.member j) = .backward := hcolour.symm.trans hi
      have hei := P.edge_mem_backward i hi
      have hej := P.edge_mem_backward j hj
      have hxi : f ⟨i.1 + 1, by omega⟩ ∈ (P.carrier (P.member i)).support :=
        ((P.carrier (P.member i)).edgeSet_subset_support_prod hei).1
      have hxj : f ⟨i.1 + 1, by omega⟩ ∈ (P.carrier (P.member j)).support := by
        rw [hjoin]
        exact ((P.carrier (P.member j)).edgeSet_subset_support_prod hej).2
      have hc : P.carrier (P.member i) = P.carrier (P.member j) :=
        DWeb.IsWarp.eq_of_mem_support hY
          (P.carrier_mem_backward _ hi) (P.carrier_mem_backward _ hj) hxi hxj
      exact P.carrier_injective_on_colour hcolour hc

/-- Feed a finite tagged raw walk to chronological erasure. -/
noncomputable def finiteInput
    (P : FiniteEdgeProvenance f Z Y M) (hN : 0 < N)
    (hroot : ∀ i, f i = f ⟨0, Nat.zero_lt_succ _⟩ → i.1 = 0) :
    RunCompressor.FiniteInput Γ.graph :=
  RunCompressor.FiniteInput.ofLoopErasure hN f hroot
    (fun i ↦ P.colour (P.member i))
    (fun i hi ↦
      (P.carrier (P.member i)).edgeSet_subset_adj (P.edge_mem_forward i hi))
    (fun i hi ↦
      (P.carrier (P.member i)).edgeSet_subset_adj (P.edge_mem_backward i hi))

@[simp] theorem finiteInput_colour
    (P : FiniteEdgeProvenance f Z Y M) (hN : 0 < N) (hroot)
    (i : Fin (finiteLoopLength f)) :
    (P.finiteInput hN hroot).colour i =
      P.colour (P.member ⟨(finiteLoopIndex f i.1).1,
        finiteLoopIndex_lt_top_of_lt_length f i.2⟩) :=
  rfl

/-- The tagged owner of a retained edge position. -/
noncomputable def retainedMember
    (P : FiniteEdgeProvenance f Z Y M) (k : Fin (finiteLoopLength f)) : M :=
  P.member ⟨(finiteLoopIndex f k.1).1,
    finiteLoopIndex_lt_top_of_lt_length f k.2⟩

theorem retainedMember_eq_of_colour_eq
    (P : FiniteEdgeProvenance f Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    {i : ℕ} (hi : i + 1 < finiteLoopLength f)
    (hcolour : P.colour (P.retainedMember ⟨i, by omega⟩) =
      P.colour (P.retainedMember ⟨i + 1, hi⟩)) :
    P.retainedMember ⟨i, by omega⟩ = P.retainedMember ⟨i + 1, hi⟩ := by
  apply P.member_eq_of_colour_eq_of_join hZ hY hcolour
  exact finiteLoopIndex_join_of_lt f
    (finiteLoopIndex_lt_top_of_lt_length f (by omega))

/-- Constancy of colour on a retained interval implies constancy of its
tagged owner. -/
theorem retainedMember_eq_of_colour_constant
    (P : FiniteEdgeProvenance f Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    {a k : ℕ} (hak : a ≤ k) (hk : k < finiteLoopLength f)
    (hcolour : ∀ j (haj : a ≤ j) (hjk : j ≤ k),
      P.colour (P.retainedMember ⟨j, hjk.trans_lt hk⟩) =
        P.colour (P.retainedMember ⟨a, hak.trans_lt hk⟩)) :
    P.retainedMember ⟨k, hk⟩ = P.retainedMember ⟨a, by omega⟩ := by
  induction k, hak using Nat.le_induction with
  | base => rfl
  | succ k hak ih =>
      have hk' : k + 1 < finiteLoopLength f := by omega
      have hadj := P.retainedMember_eq_of_colour_eq hZ hY hk'
        ((hcolour k (by omega) (by omega)).trans
          (hcolour (k + 1) (by omega) le_rfl).symm)
      exact hadj.symm.trans (ih (by omega) (fun j haj hjk ↦
        hcolour j haj (LE.le.trans hjk (Nat.le_succ k))))

variable (hN : 0 < N)
variable (hroot : ∀ i, f i = f ⟨0, Nat.zero_lt_succ _⟩ → i.1 = 0)

private theorem runLower_lt_lastEdge
    (P : FiniteEdgeProvenance f Z Y M)
    (i : Fin (P.finiteInput hN hroot).runs.length) :
    RunCompressor.runLower (P.finiteInput hN hroot).runs i.1 <
      (P.finiteInput hN hroot).lastEdge := by
  let S := P.finiteInput hN hroot
  have hpos : 0 < (S.runs.get i).length :=
    List.length_pos_iff_ne_nil.mpr (S.run_ne_nil (List.get_mem _ i))
  have hu := S.runUpper_le_lastEdge i
  change RunCompressor.runLower S.runs i.1 < S.lastEdge
  omega

/-- Tagged owner of a finite maximal run. -/
noncomputable def finiteRunOwner
    (P : FiniteEdgeProvenance f Z Y M)
    (i : Fin (P.finiteInput hN hroot).runs.length) : M :=
  P.retainedMember ⟨RunCompressor.runLower (P.finiteInput hN hroot).runs i.1,
    P.runLower_lt_lastEdge hN hroot i⟩

@[simp] theorem finiteRunWalk_run_direction
    (P : FiniteEdgeProvenance f Z Y M)
    (i : Fin (P.finiteInput hN hroot).runs.length) :
    ((P.finiteInput hN hroot).projectedRun i).link.direction =
      P.colour (P.finiteRunOwner hN hroot i) := by
  rw [(P.finiteInput hN hroot).projectedRun_direction]
  unfold RunCompressor.FiniteInput.runDirection finiteRunOwner
  apply Eq.symm
  apply (P.finiteInput hN hroot).colour_run_offset i (k := 0)
  exact List.length_pos_iff_ne_nil.mpr
    ((P.finiteInput hN hroot).run_ne_nil (List.get_mem _ i))

/-- Every retained position in a finite maximal run has its run owner. -/
theorem retainedMember_eq_finiteRunOwner
    (P : FiniteEdgeProvenance f Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (i : Fin (P.finiteInput hN hroot).runs.length) {k : ℕ}
    (hlo : RunCompressor.runLower (P.finiteInput hN hroot).runs i.1 ≤ k)
    (hhi : k < RunCompressor.runLower (P.finiteInput hN hroot).runs (i.1 + 1)) :
    P.retainedMember ⟨k, by
      have hb : RunCompressor.runLower (P.finiteInput hN hroot).runs
          (i.1 + 1) ≤ (P.finiteInput hN hroot).lastEdge := by
        rw [RunCompressor.runLower_succ _ i.2]
        exact (P.finiteInput hN hroot).runUpper_le_lastEdge i
      exact hhi.trans_le hb⟩ =
      P.finiteRunOwner hN hroot i := by
  apply P.retainedMember_eq_of_colour_constant hZ hY hlo
  intro j hjlo hjhi
  have hb : RunCompressor.runLower (P.finiteInput hN hroot).runs
      (i.1 + 1) ≤ (P.finiteInput hN hroot).lastEdge := by
    rw [RunCompressor.runLower_succ _ i.2]
    exact (P.finiteInput hN hroot).runUpper_le_lastEdge i
  change (P.finiteInput hN hroot).colour ⟨j, by
      exact (hjhi.trans_lt hhi).trans_le hb⟩ =
    (P.finiteInput hN hroot).colour
      ⟨RunCompressor.runLower (P.finiteInput hN hroot).runs i.1,
        P.runLower_lt_lastEdge hN hroot i⟩
  have hrun := ((P.finiteInput hN hroot).colour_run_offset i
    (k := j - RunCompressor.runLower (P.finiteInput hN hroot).runs i.1)
    (by
      have hjlt : j < RunCompressor.runLower
          (P.finiteInput hN hroot).runs i.1 +
          ((P.finiteInput hN hroot).runs.get i).length := by
        simpa only [RunCompressor.runLower_succ _ i.2] using
          hjhi.trans_lt hhi
      omega)).trans
    ((P.finiteInput hN hroot).colour_run_offset i (k := 0)
      (List.length_pos_iff_ne_nil.mpr
        ((P.finiteInput hN hroot).run_ne_nil (List.get_mem _ i)))).symm
  have hindex :
      (⟨RunCompressor.runLower (P.finiteInput hN hroot).runs i.1 +
          (j - RunCompressor.runLower (P.finiteInput hN hroot).runs i.1), by
        omega⟩ : Fin (P.finiteInput hN hroot).lastEdge) =
        ⟨j, by omega⟩ := by
    apply Fin.ext
    exact Nat.add_sub_of_le hjlo
  rwa [hindex] at hrun

/-- The directed edge set of a compressed finite run is contained in the
edge set of its unique tagged raw owner. -/
theorem finiteRunWalk_run_edgeSet_subset_owner
    (P : FiniteEdgeProvenance f Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (i : Fin (P.finiteInput hN hroot).runs.length) :
    ((P.finiteInput hN hroot).projectedRun i).link.path.edgeSet ⊆
      (P.carrier (P.finiteRunOwner hN hroot i)).edgeSet := by
  intro e he
  let S := P.finiteInput hN hroot
  have hupper (i : Fin S.runs.length) :
      RunCompressor.runLower S.runs (i.1 + 1) ≤ S.lastEdge := by
    rw [RunCompressor.runLower_succ _ i.2]
    exact S.runUpper_le_lastEdge i
  rcases S.projectedRun_edge_provenance i he with
      ⟨hdir, k, hk, rfl⟩ | ⟨hdir, k, hk, rfl⟩
  · let r := RunCompressor.runLower S.runs i.1 + k
    have hrlo : RunCompressor.runLower S.runs i.1 ≤ r := by
      simp [r]
    have hrhi : r < RunCompressor.runLower S.runs (i.1 + 1) := by
      rw [RunCompressor.runLower_succ S.runs i.2]
      simpa [r, Nat.add_assoc] using Nat.add_lt_add_left hk
        (RunCompressor.runLower S.runs i.1)
    have hmember := P.retainedMember_eq_finiteRunOwner hN hroot hZ hY i
      hrlo hrhi
    have hcolour :
        P.colour (P.retainedMember ⟨r, by
          exact hrhi.trans_le (hupper i)⟩) = .forward := by
      change S.colour ⟨r, _⟩ = .forward
      have hrundir : (S.projectedRun i).link.direction = .forward := hdir
      rw [S.projectedRun_direction] at hrundir
      exact (S.colour_run_offset i hk).trans hrundir
    have hq : (finiteLoopIndex f r).1 < N :=
      finiteLoopIndex_lt_top_of_lt_length f
        (hrhi.trans_le (hupper i))
    have hedge := P.edge_mem_forward ⟨(finiteLoopIndex f r).1, hq⟩ hcolour
    change (f ⟨(finiteLoopIndex f r).1, by omega⟩,
        f ⟨(finiteLoopIndex f r).1 + 1, by omega⟩) ∈
      (P.carrier (P.retainedMember ⟨r, by
        exact hrhi.trans_le (hupper i)⟩)).edgeSet at hedge
    rw [hmember] at hedge
    change (finiteLoopVertex f r, finiteLoopVertex f (r + 1)) ∈ _
    rcases finiteLoopVertex_succ f
      (show r < finiteLoopLength f by
        exact hrhi.trans_le (hupper i)) with ⟨hcur, hnext⟩
    simpa [hcur, hnext] using hedge
  · let r := RunCompressor.runLower S.runs i.1 + k
    have hrlo : RunCompressor.runLower S.runs i.1 ≤ r := by
      simp [r]
    have hrhi : r < RunCompressor.runLower S.runs (i.1 + 1) := by
      rw [RunCompressor.runLower_succ S.runs i.2]
      simpa [r, Nat.add_assoc] using Nat.add_lt_add_left hk
        (RunCompressor.runLower S.runs i.1)
    have hmember := P.retainedMember_eq_finiteRunOwner hN hroot hZ hY i
      hrlo hrhi
    have hcolour :
        P.colour (P.retainedMember ⟨r, by
          exact hrhi.trans_le (hupper i)⟩) = .backward := by
      change S.colour ⟨r, _⟩ = .backward
      have hrundir : (S.projectedRun i).link.direction = .backward := hdir
      rw [S.projectedRun_direction] at hrundir
      exact (S.colour_run_offset i hk).trans hrundir
    have hq : (finiteLoopIndex f r).1 < N :=
      finiteLoopIndex_lt_top_of_lt_length f
        (hrhi.trans_le (hupper i))
    have hedge := P.edge_mem_backward ⟨(finiteLoopIndex f r).1, hq⟩ hcolour
    change (f ⟨(finiteLoopIndex f r).1 + 1, by omega⟩,
        f ⟨(finiteLoopIndex f r).1, by omega⟩) ∈
      (P.carrier (P.retainedMember ⟨r, by
        exact hrhi.trans_le (hupper i)⟩)).edgeSet at hedge
    rw [hmember] at hedge
    change (finiteLoopVertex f (r + 1), finiteLoopVertex f r) ∈ _
    rcases finiteLoopVertex_succ f
      (show r < finiteLoopLength f by
        exact hrhi.trans_le (hupper i)) with ⟨hcur, hnext⟩
    simpa [hcur, hnext] using hedge

/-- Complete literal labels for the finite compressed stream.  The endpoint
purity assumptions are unconditional, hence also discharge the conditional
endpoint fields of `LiteralBracketLabels`. -/
theorem finiteRunWalk_literalBracketLabels
    (P : FiniteEdgeProvenance f Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hinitial : f ⟨0, Nat.zero_lt_succ _⟩ ∉ Γ.vertexSet Y)
    (hterminal : f ⟨N, Nat.lt_succ_self _⟩ ∉ Γ.vertexSet Y) :
    (P.finiteInput hN hroot).toFiniteRunWalk.LiteralBracketLabels Z Y := by
  let S := P.finiteInput hN hroot
  let W := S.toFiniteRunWalk
  refine {
    reference_isWarp := hY
    backward_on := ?_
    forward_on := ?_
    initial_outside := ?_
    terminal_outside := ?_
  }
  · intro i hi
    let j := S.runIndex i
    let a := P.finiteRunOwner hN hroot j
    refine ⟨P.carrier a, ?_, ?_⟩
    · apply P.carrier_mem_backward
      change (S.projectedRun j).link.direction = .backward at hi
      exact (P.finiteRunWalk_run_direction hN hroot j).symm.trans hi
    · apply finitePath_isSubpathOf_of_edgeSet_subset _ _
        (W.run i).link.nontrivial
      change (S.projectedRun j).link.path.edgeSet ⊆ _
      exact P.finiteRunWalk_run_edgeSet_subset_owner hN hroot hZ hY j
  · intro i hi
    let j := S.runIndex i
    let a := P.finiteRunOwner hN hroot j
    refine ⟨P.carrier a, ?_, ?_⟩
    · apply P.carrier_mem_forward
      change (S.projectedRun j).link.direction = .forward at hi
      exact (P.finiteRunWalk_run_direction hN hroot j).symm.trans hi
    · apply finitePath_isSubpathOf_of_edgeSet_subset _ _
        (W.run i).link.nontrivial
      change (S.projectedRun j).link.path.edgeSet ⊆ _
      exact P.finiteRunWalk_run_edgeSet_subset_owner hN hroot hZ hY j
  · intro _hi
    rw [show W.vertex 0 = f ⟨0, Nat.zero_lt_succ _⟩ by
      exact RunCompressor.FiniteInput.ofLoopErasure_runWalk_initial
        hN f hroot _ _ _]
    exact hinitial
  · intro _hi
    rw [show W.vertex (W.run W.lastRunIndex).last =
        f ⟨N, Nat.lt_succ_self _⟩ by
      exact RunCompressor.FiniteInput.ofLoopErasure_runWalk_terminal
        hN f hroot _ _ _]
    exact hterminal

/-- Distinct maximal finite runs have distinct tagged owners. -/
theorem finiteRunOwner_ne_of_lt
    (P : FiniteEdgeProvenance f Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    {i j : Fin (P.finiteInput hN hroot).runs.length} (hij : i < j) :
    P.finiteRunOwner hN hroot i ≠ P.finiteRunOwner hN hroot j := by
  let S := P.finiteInput hN hroot
  let k : Fin (P.finiteInput hN hroot).runs.length := ⟨i.1 + 1, by omega⟩
  have hab : RunCompressor.runLower S.runs i.1 ≤
      RunCompressor.runLower S.runs k.1 :=
    RunCompressor.runLower_mono S.runs (by
      change i.1 ≤ i.1 + 1
      omega)
  have hbc : RunCompressor.runLower S.runs k.1 ≤
      RunCompressor.runLower S.runs j.1 :=
    RunCompressor.runLower_mono S.runs (by
      change i.1 + 1 ≤ j.1
      omega)
  have hmono : Monotone (finiteLoopIndex f) :=
    monotone_nat_of_le_succ (finiteLoopIndex_le_succ f)
  have hrawab : finiteLoopIndex f (RunCompressor.runLower S.runs i.1) ≤
      finiteLoopIndex f (RunCompressor.runLower S.runs k.1) := hmono hab
  have hrawbc : finiteLoopIndex f (RunCompressor.runLower S.runs k.1) ≤
      finiteLoopIndex f (RunCompressor.runLower S.runs j.1) := hmono hbc
  intro howners
  have hmid : P.finiteRunOwner hN hroot k =
      P.finiteRunOwner hN hroot i := by
    unfold finiteRunOwner retainedMember at howners ⊢
    exact P.member_convex hrawab hrawbc howners
  have hiS : i.1 < S.runs.length := by
    change i.1 < (P.finiteInput hN hroot).runs.length
    exact i.2
  have hikS : i.1 + 1 < S.runs.length := by
    change i.1 + 1 < (P.finiteInput hN hroot).runs.length
    omega
  have hdirne : S.runDirection i ≠ S.runDirection k := by
    have hne := RunCompressor.finiteColourRuns_head_ne_head S.colours
      ⟨i.1, by
        apply Nat.lt_sub_of_add_lt
        exact hikS⟩
    intro heq
    apply hne
    change S.runDirection ⟨i.1, hiS⟩ =
      S.runDirection ⟨i.1 + 1, hikS⟩
    have hiFin : (⟨i.1, hiS⟩ : Fin S.runs.length) = i := Fin.ext rfl
    have hkFin : (⟨i.1 + 1, hikS⟩ : Fin S.runs.length) = k :=
      Fin.ext rfl
    rw [hiFin, hkFin]
    exact heq
  have hci : P.colour (P.finiteRunOwner hN hroot i) =
      S.runDirection i :=
    (P.finiteRunWalk_run_direction hN hroot i).symm.trans
      (S.projectedRun_direction i)
  have hck : P.colour (P.finiteRunOwner hN hroot k) =
      S.runDirection k :=
    (P.finiteRunWalk_run_direction hN hroot k).symm.trans
      (S.projectedRun_direction k)
  apply hdirne
  rw [← hci, ← hck, hmid]

/-- Indexed backward-owner provenance for the finite compressed stream. -/
noncomputable def finiteIndexedBackwardProvenance
    (P : FiniteEdgeProvenance f Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y) :
    (AltPath.finite
      (P.finiteInput hN hroot).toFiniteRunWalk.toFiniteTrace).IndexedBackwardProvenance
        Y (Fin ((P.finiteInput hN hroot).toFiniteRunWalk.lastIndex + 1)) := by
  let S := P.finiteInput hN hroot
  let W := S.toFiniteRunWalk
  refine {
    link := fun i ↦ (W.run i).link
    links_eq_range := W.toFiniteTrace_links
    owner := fun i _ ↦ P.carrier (P.finiteRunOwner hN hroot (S.runIndex i))
    owner_mem := ?_
    isSubpath := ?_
    owner_unique := ?_
  }
  · intro i hi
    apply P.carrier_mem_backward
    change (S.projectedRun (S.runIndex i)).link.direction = .backward at hi
    exact (P.finiteRunWalk_run_direction hN hroot (S.runIndex i)).symm.trans hi
  · intro i _hi
    apply finitePath_isSubpathOf_of_edgeSet_subset _ _
      (W.run i).link.nontrivial
    change (S.projectedRun (S.runIndex i)).link.path.edgeSet ⊆ _
    exact P.finiteRunWalk_run_edgeSet_subset_owner hN hroot hZ hY
      (S.runIndex i)
  · intro i j hi hj howner
    have hci : P.colour (P.finiteRunOwner hN hroot (S.runIndex i)) =
        .backward :=
      (P.finiteRunWalk_run_direction hN hroot (S.runIndex i)).symm.trans (by
        change (S.projectedRun (S.runIndex i)).link.direction = .backward at hi
        exact hi)
    have hcj : P.colour (P.finiteRunOwner hN hroot (S.runIndex j)) =
        .backward :=
      (P.finiteRunWalk_run_direction hN hroot (S.runIndex j)).symm.trans (by
        change (S.projectedRun (S.runIndex j)).link.direction = .backward at hj
        exact hj)
    have htag : P.finiteRunOwner hN hroot (S.runIndex i) =
        P.finiteRunOwner hN hroot (S.runIndex j) :=
      P.carrier_injective_on_colour (hci.trans hcj.symm) howner
    have hij' : S.runIndex i = S.runIndex j := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hij | hji
      · exact (P.finiteRunOwner_ne_of_lt hN hroot hZ hY hij) htag
      · exact (P.finiteRunOwner_ne_of_lt hN hroot hZ hY hji) htag.symm
    have hij : i = j := by
      apply Fin.ext
      have hval : (S.runIndex i).1 = (S.runIndex j).1 :=
        congrArg (fun x : Fin S.runs.length ↦ x.1) hij'
      exact hval
    subst j
    rfl

/-- Endpoint purity forces the first compressed run to point forward. -/
theorem finiteRunWalk_first_forward
    (P : FiniteEdgeProvenance f Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hinitial : f ⟨0, Nat.zero_lt_succ _⟩ ∉ Γ.vertexSet Y) :
    ((P.finiteInput hN hroot).toFiniteRunWalk.run
      ⟨0, Nat.zero_lt_succ _⟩).link.direction = .forward := by
  let S := P.finiteInput hN hroot
  let W := S.toFiniteRunWalk
  cases hd : (W.run ⟨0, Nat.zero_lt_succ _⟩).link.direction with
  | forward => rfl
  | backward =>
      exfalso
      let i := S.runIndex (⟨0, Nat.zero_lt_succ _⟩ :
        Fin (W.lastIndex + 1))
      have hc : P.colour (P.finiteRunOwner hN hroot i) = .backward := by
        apply (P.finiteRunWalk_run_direction hN hroot i).symm.trans
        change (S.projectedRun i).link.direction = .backward
        exact hd
      have hpY := P.carrier_mem_backward _ hc
      apply hinitial
      rw [DWeb.mem_vertexSet]
      refine ⟨P.carrier (P.finiteRunOwner hN hroot i), hpY, ?_⟩
      have hentry := (W.run ⟨0, Nat.zero_lt_succ _⟩).link.entry_mem_support
      have hsub := finitePath_isSubpathOf_of_edgeSet_subset
        (W.run ⟨0, Nat.zero_lt_succ _⟩).link.path
        (P.carrier (P.finiteRunOwner hN hroot i))
        (W.run ⟨0, Nat.zero_lt_succ _⟩).link.nontrivial
        (by
          change (S.projectedRun i).link.path.edgeSet ⊆ _
          exact P.finiteRunWalk_run_edgeSet_subset_owner
            hN hroot hZ hY i)
      have hmem := hsub.1 hentry
      rw [(W.run ⟨0, Nat.zero_lt_succ _⟩).entry_eq, W.starts_zero] at hmem
      have hwzero : W.vertex 0 = f ⟨0, Nat.zero_lt_succ _⟩ :=
        RunCompressor.FiniteInput.ofLoopErasure_runWalk_initial
          hN f hroot _ _ _
      rwa [hwzero] at hmem

/-- Endpoint purity forces the last compressed run to point forward. -/
theorem finiteRunWalk_last_forward
    (P : FiniteEdgeProvenance f Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hterminal : f ⟨N, Nat.lt_succ_self _⟩ ∉ Γ.vertexSet Y) :
    ((P.finiteInput hN hroot).toFiniteRunWalk.run
      (P.finiteInput hN hroot).toFiniteRunWalk.lastRunIndex).link.direction =
        .forward := by
  let S := P.finiteInput hN hroot
  let W := S.toFiniteRunWalk
  cases hd : (W.run W.lastRunIndex).link.direction with
  | forward => rfl
  | backward =>
      exfalso
      let i := S.runIndex W.lastRunIndex
      have hc : P.colour (P.finiteRunOwner hN hroot i) = .backward := by
        apply (P.finiteRunWalk_run_direction hN hroot i).symm.trans
        change (S.projectedRun i).link.direction = .backward
        exact hd
      have hpY := P.carrier_mem_backward _ hc
      apply hterminal
      rw [DWeb.mem_vertexSet]
      refine ⟨P.carrier (P.finiteRunOwner hN hroot i), hpY, ?_⟩
      have hexit := (W.run W.lastRunIndex).link.exit_mem_support
      have hsub := finitePath_isSubpathOf_of_edgeSet_subset
        (W.run W.lastRunIndex).link.path
        (P.carrier (P.finiteRunOwner hN hroot i))
        (W.run W.lastRunIndex).link.nontrivial
        (by
          change (S.projectedRun i).link.path.edgeSet ⊆ _
          exact P.finiteRunWalk_run_edgeSet_subset_owner
            hN hroot hZ hY i)
      have hmem := hsub.1 hexit
      rw [(W.run W.lastRunIndex).exit_eq] at hmem
      have hwlast : W.vertex (W.run W.lastRunIndex).last =
          f ⟨N, Nat.lt_succ_self _⟩ :=
        RunCompressor.FiniteInput.ofLoopErasure_runWalk_terminal
          hN f hroot _ _ _
      rwa [hwlast] at hmem


end FiniteEdgeProvenance

namespace FiniteMacroRoute

variable {Z Y : Set Γ.DPath} (C : FiniteMacroRoute Γ Z Y)

/-- The tagged construction history of the concrete finite route, packaged
in the generic finite chronological-erasure interface. -/
noncomputable def edgeProvenance
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial ∉ Γ.vertexSet Y) :
    FiniteEdgeProvenance (C.routeRawVertex hZfin hYfin) Z Y C.EdgeTag where
  member := C.routeEdgeTag hZfin hYfin
  colour := C.edgeTagColour
  carrier := C.edgeTagCarrier
  carrier_injective_on_colour := by
    intro a b hc hp
    exact C.edgeTagCarrier_injective_on_colour hZ hY hroot hc hp
  carrier_mem_forward := C.edgeTagCarrier_mem_forward
  carrier_mem_backward := C.edgeTagCarrier_mem_backward
  edge_mem_forward := by
    intro i hi
    exact C.routeEdge_mem_forward hZfin hYfin i hi
  edge_mem_backward := by
    intro i hi
    exact C.routeEdge_mem_backward hZfin hYfin i hi
  member_convex := by
    intro i j k hij hjk hik
    exact C.routeEdgeTag_convex hZfin hYfin hij hjk hik

/-- The unconditional finite edge-level compiler for a path-level finite
macro route. -/
noncomputable def compilation
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    {u : V} (hp₀ : (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial = u)
    (huT : u ∉ Γ.terminalFrontier Z)
    (hroot : (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial ∉ Γ.vertexSet Y) :
    C.Compilation := by
  let f := C.routeRawVertex hZfin hYfin
  have hN : 0 < (C.routeWalk hZfin hYfin).length :=
    C.routeWalk_length_pos hZfin hYfin hp₀ huT
  have hrootUnique : ∀ i, f i = f ⟨0, Nat.zero_lt_succ _⟩ → i.1 = 0 := by
    intro i hi
    exact C.routeRawVertex_root_unique hZ hY hZfin hYfin hroot i hi
  let P := C.edgeProvenance hZ hY hZfin hYfin hroot
  let W := (P.finiteInput hN hrootUnique).toFiniteRunWalk
  apply Compilation.ofRunWalk C hZ hY hZfin W
  · apply P.finiteRunWalk_literalBracketLabels hN hrootUnique hZ hY
    · change f ⟨0, Nat.zero_lt_succ _⟩ ∉ Γ.vertexSet Y
      have hfzero : f ⟨0, Nat.zero_lt_succ _⟩ =
          (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial :=
        C.routeRawVertex_zero hZfin hYfin
      rw [hfzero]
      exact hroot
    · change f ⟨(C.routeWalk hZfin hYfin).length,
          Nat.lt_succ_self _⟩ ∉ Γ.vertexSet Y
      have hflast : f ⟨(C.routeWalk hZfin hYfin).length,
          Nat.lt_succ_self _⟩ = C.finalTerminal :=
        C.routeRawVertex_last hZfin hYfin
      rw [hflast]
      exact C.final_uncovered
  · exact P.finiteIndexedBackwardProvenance hN hrootUnique hZ hY
  · change W.vertex 0 = _
    calc
      W.vertex 0 = f ⟨0, Nat.zero_lt_succ _⟩ :=
        RunCompressor.FiniteInput.ofLoopErasure_runWalk_initial
          hN f hrootUnique _ _ _
      _ = _ := C.routeRawVertex_zero hZfin hYfin
  · change W.vertex (W.run W.lastRunIndex).last = _
    calc
      W.vertex (W.run W.lastRunIndex).last =
          f ⟨(C.routeWalk hZfin hYfin).length, Nat.lt_succ_self _⟩ :=
        RunCompressor.FiniteInput.ofLoopErasure_runWalk_terminal
          hN f hrootUnique _ _ _
      _ = _ := C.routeRawVertex_last hZfin hYfin
  · exact P.finiteRunWalk_first_forward hN hrootUnique hZ hY (by
      change f ⟨0, Nat.zero_lt_succ _⟩ ∉ Γ.vertexSet Y
      have hfzero : f ⟨0, Nat.zero_lt_succ _⟩ =
          (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial :=
        C.routeRawVertex_zero hZfin hYfin
      rw [hfzero]
      exact hroot)
  · exact P.finiteRunWalk_last_forward hN hrootUnique hZ hY (by
      change f ⟨(C.routeWalk hZfin hYfin).length,
        Nat.lt_succ_self _⟩ ∉ Γ.vertexSet Y
      have hflast : f ⟨(C.routeWalk hZfin hYfin).length,
          Nat.lt_succ_self _⟩ = C.finalTerminal :=
        C.routeRawVertex_last hZfin hYfin
      rw [hflast]
      exact C.final_uncovered)

end FiniteMacroRoute

variable {V : Type u} {Γ : DWeb V}

/-- The finite compiler in exactly the globally quantified form consumed by
`safeAlternatingDichotomyStatement_of_macro_compilers`. -/
noncomputable def finiteMacroCompiler
    (Z Y : Set Γ.DPath)
    (_hZA : Γ.initialSet Z ⊆ Γ.source)
    (_hZB : Γ.terminalFrontier Z ⊆ Γ.target)
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (_hinit : Γ.initialSet Y ⊆ Γ.initialSet Z)
    (u : V) (hu : u ∈ Γ.initialSet Z \ Γ.vertexSet Y)
    (p₀ : Z) (hp₀ : p₀.1.initial = u)
    (huT : u ∉ Γ.terminalFrontier Z)
    (C : FiniteMacroRoute Γ Z Y)
    (hC₀ : C.z ⟨0, Nat.zero_lt_succ _⟩ = p₀) : C.Compilation := by
  apply C.compilation hZ hY hZfin hYfin
  · rw [hC₀, hp₀]
  · exact huT
  · rw [hC₀, hp₀]
    exact hu.2

end Alternating
end Erdos599
