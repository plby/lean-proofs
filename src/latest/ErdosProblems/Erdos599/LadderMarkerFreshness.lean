/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderConstantLimit
import ErdosProblems.Erdos599.LadderExhaustionLoose
import ErdosProblems.Erdos599.LadderRoofRecursion
import ErdosProblems.Erdos599.LadderSchedule

/-!
# Marker freshness and exhaustion in the canonical ladder

This file isolates the marker bookkeeping which is independent of the
frontier and stationary-set arguments.  The two roofing invariants turn
geometric eligibility into genuine freshness, while global pathwise growth
prevents a marker inserted at one successor from ever being selected again.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- An inactive recursive state cannot itself choose a marker. -/
theorem ladderMarkerOfState_eq_none_of_inactive
    (preferred : Option V) (s : G.LadderAccumulationState)
    (hinactive : s.2 ≠ true) :
    G.ladderMarkerOfState preferred s = none := by
  have hfalse : s.2 = false := by
    cases h : s.2 <;> simp_all
  simp [ladderMarkerOfState, hfalse]

/-- The state at the successor of a canonical stage is exactly the
unrestricted successor operation applied at that stage. -/
theorem canonicalLadderState_succ
    (kappa : Cardinal.{u})
    (preferred : Ladder.Stage kappa → Option V)
    (a : Ladder.Stage kappa) :
    G.canonicalLadderState kappa preferred (Ladder.Stage.succExtended a) =
      G.ladderSuccessorState
        (extendLadderPreference kappa preferred) a.1
        (G.canonicalLadderState kappa preferred
          (Ladder.Stage.toExtended a)) := by
  simp only [canonicalLadderState, ladderAccumulatedState_succ]

/-- Once the unrestricted canonical recursion has become inactive, its
activity flag stays inactive at every later ordinal, including genuine
limits.  This is a purely Boolean fact about the recursion; it does not use
any graph-theoretic invariant. -/
theorem ladderAccumulatedStateAux_inactive_mono
    (preferred : Ordinal.{u} → Option V) :
    ∀ b a, a ≤ b →
      (G.ladderAccumulatedStateAux
        (G.ladderSuccessorState preferred) a).2 ≠ true →
      (G.ladderAccumulatedStateAux
        (G.ladderSuccessorState preferred) b).2 ≠ true := by
  intro b
  induction b using Ordinal.limitRecOn with
  | zero =>
      intro a hab ha
      have ha0 : a = 0 := bot_unique hab
      subst a
      exact ha
  | add_one o ih =>
      intro a hab ha
      by_cases hao : a = o + 1
      · subst a
        exact ha
      · have hao' : a ≤ o :=
          (Order.lt_add_one_iff).1 (lt_of_le_of_ne hab hao)
        have hprior := ih a hao' ha
        have hstep :
            G.ladderAccumulatedStateAux
                (G.ladderSuccessorState preferred) (o + 1) =
              G.ladderSuccessorState preferred o
                (G.ladderAccumulatedStateAux
                  (G.ladderSuccessorState preferred) o) := by
          simp [ladderAccumulatedStateAux]
        rw [hstep, ladderSuccessorState, dif_neg hprior]
        simp
  | limit o ho ih =>
      intro a hab ha
      by_cases hao : a = o
      · subst a
        exact ha
      · have hao' : a < o := lt_of_le_of_ne hab hao
        have haPrior := ih a hao' a le_rfl ha
        rw [ladderAccumulatedStateAux,
          Ordinal.limitRecOn_limit _ _ _ _ ho]
        simp only [ladderLimitState]
        split
        · rename_i hchain
          split
          · rename_i hall
            exact (haPrior (hall a hao')).elim
          · simp
        · simp

/-- Restricted canonical-stage form of activity monotonicity. -/
theorem canonicalLadderState_inactive_mono
    (kappa : Cardinal.{u})
    (preferred : Ladder.Stage kappa → Option V)
    {a b : Ladder.Stage kappa} (hab : a ≤ b)
    (ha : ¬ DWeb.KappaLadder.CanonicalStageActive
      (G := G) preferred a) :
    ¬ DWeb.KappaLadder.CanonicalStageActive
      (G := G) preferred b := by
  intro hb
  exact G.ladderAccumulatedStateAux_inactive_mono
    (extendLadderPreference kappa preferred) b.1 a.1 hab ha hb

namespace KappaLadder

variable {G : DWeb V} {kappa : Cardinal.{u}}

/-- The geometric hypotheses needed for marker freshness.  They are exactly
the three outputs of the canonical transfinite recursion used here: source
roofing, self-roofing, and one-sided growth. -/
structure CanonicalMarkerGeometry
    (L : G.KappaLadder kappa) : Prop where
  sourceRoof : L.RoofsSourceAtStages
  selfRoof : ∀ a : Ladder.ExtendedStage kappa,
    G.vertexSet (L.accumulated a) ⊆
      G.roof (G.terminalFrontier (L.accumulated a))
  grows : ∀ {a b : Ladder.ExtendedStage kappa}, a ≤ b →
    G.LadderGrows (L.accumulated a) (L.accumulated b)

/-- Canonical markers are pairwise distinct.  An earlier marker singleton
grows into every later accumulated family.  At the later stage the two roof
invariants identify every surviving, target-reachable old vertex with the
stage source, whereas marker candidates explicitly avoid that source. -/
theorem canonicalLadderCore_markersInjective_of_geometry
    (preferred : Ladder.Stage kappa → Option V)
    (hgeom : CanonicalMarkerGeometry
      (G.canonicalLadderCore kappa preferred)) :
    (G.canonicalLadderCore kappa preferred).MarkersInjective := by
  let L := G.canonicalLadderCore kappa preferred
  intro a b y ha hb
  rcases lt_trichotomy a b with hab | hab | hba
  · have hsab : Ladder.Stage.succExtended a ≤
        Ladder.Stage.toExtended b := by
      change a.1 + 1 ≤ b.1
      exact (Order.add_one_le_iff).2 hab
    obtain ⟨q, hq, hpq⟩ := hgeom.grows hsab
      (G.trivialPath y)
      (canonicalLadderCore_trivialPath_mem_successorWarp preferred a ha)
    let sb := G.canonicalLadderState kappa preferred
      (Ladder.Stage.toExtended b)
    have hbState : G.ladderMarkerOfState (preferred b) sb = some y := hb
    have hcontact : G.LadderStateContactsStageSource sb :=
      G.ladderStateContactsStageSource_of_roofs sb
        (hgeom.sourceRoof (Ladder.Stage.toExtended b))
        (hgeom.selfRoof (Ladder.Stage.toExtended b))
    have hnot := G.ladderMarkerOfState_not_mem_old_vertexSet
      hcontact hbState
    exfalso
    apply hnot
    refine ⟨q, hq, G.support_mono_of_extends hpq ?_⟩
    rw [G.support_trivialPath]
    exact Set.mem_singleton y
  · exact hab
  · have hsba : Ladder.Stage.succExtended b ≤
        Ladder.Stage.toExtended a := by
      change b.1 + 1 ≤ a.1
      exact (Order.add_one_le_iff).2 hba
    obtain ⟨q, hq, hpq⟩ := hgeom.grows hsba
      (G.trivialPath y)
      (canonicalLadderCore_trivialPath_mem_successorWarp preferred b hb)
    let sa := G.canonicalLadderState kappa preferred
      (Ladder.Stage.toExtended a)
    have haState : G.ladderMarkerOfState (preferred a) sa = some y := ha
    have hcontact : G.LadderStateContactsStageSource sa :=
      G.ladderStateContactsStageSource_of_roofs sa
        (hgeom.sourceRoof (Ladder.Stage.toExtended a))
        (hgeom.selfRoof (Ladder.Stage.toExtended a))
    have hnot := G.ladderMarkerOfState_not_mem_old_vertexSet
      hcontact haState
    exfalso
    apply hnot
    refine ⟨q, hq, G.support_mono_of_extends hpq ?_⟩
    rw [G.support_trivialPath]
    exact Set.mem_singleton y

/-- Marker exhaustion at an active stage is definitionally exact.  This
version is named in the freshness module for downstream assembly. -/
theorem canonicalLadderCore_active_marker_none_iff_candidates_empty
    (preferred : Ladder.Stage kappa → Option V)
    (a : Ladder.Stage kappa)
    (hactive : CanonicalStageActive (G := G) preferred a) :
    (G.canonicalLadderCore kappa preferred).marker a = none ↔
      (G.canonicalLadderCore kappa preferred).markerCandidates a = ∅ :=
  canonicalLadderCore_marker_eq_none_iff preferred a hactive

/-- The exact state property needed after the activity flag becomes false.
It separates the graph-theoretic maximal-wave quotient calculation from the
pure ordinal/marker bookkeeping below. -/
def CanonicalInactiveStagesFrozen
    (preferred : Ladder.Stage kappa → Option V) : Prop :=
  ∀ a : Ladder.Stage kappa,
    ¬ CanonicalStageActive (G := G) preferred a →
      (G.canonicalLadderCore kappa preferred).markerCandidates a = ∅ ∧
      ((G.canonicalLadderCore kappa preferred).stageWeb a).IsLoose

/-- An empty candidate set makes the immediately following recursive state
inactive. -/
theorem canonicalLadderState_succ_inactive_of_candidates_empty
    (preferred : Ladder.Stage kappa → Option V)
    (a : Ladder.Stage kappa)
    (hempty :
      (G.canonicalLadderCore kappa preferred).markerCandidates a = ∅) :
    (G.canonicalLadderState kappa preferred
      (Ladder.Stage.succExtended a)).2 ≠ true := by
  rw [G.canonicalLadderState_succ kappa preferred a]
  let s := G.canonicalLadderState kappa preferred
    (Ladder.Stage.toExtended a)
  change (G.ladderSuccessorState
    (extendLadderPreference kappa preferred) a.1 s).2 ≠ true
  by_cases hs : s.2 = true
  · rw [ladderSuccessorState, dif_pos hs]
    have hempty' : G.ladderMarkerCandidatesOfState s = ∅ := hempty
    simp [hempty']
  · rw [ladderSuccessorState, dif_neg hs]
    simp

/-- Once inactive stages are known to be exhausted, marker absence is
equivalent to geometric exhaustion at every canonical stage, active or not. -/
theorem canonicalLadderCore_marker_none_iff_candidates_empty_of_frozen
    (preferred : Ladder.Stage kappa → Option V)
    (hfrozen : CanonicalInactiveStagesFrozen (G := G) preferred)
    (a : Ladder.Stage kappa) :
    (G.canonicalLadderCore kappa preferred).marker a = none ↔
      (G.canonicalLadderCore kappa preferred).markerCandidates a = ∅ := by
  by_cases hactive : CanonicalStageActive (G := G) preferred a
  · exact canonicalLadderCore_marker_eq_none_iff preferred a hactive
  · have hnone :
        (G.canonicalLadderCore kappa preferred).marker a = none := by
      change G.ladderMarkerOfState (preferred a)
        (G.canonicalLadderState kappa preferred
          (Ladder.Stage.toExtended a)) = none
      exact G.ladderMarkerOfState_eq_none_of_inactive _ _ hactive
    simp only [hnone, hfrozen a hactive |>.1]

/-- Pure recursion bookkeeping for marking time: after the first absent
marker, every later stage is inactive; the frozen-state theorem then makes
its marker absent and its canonical maximal rung trivial. -/
theorem canonicalLadderCore_marksTimeAfterExhaustion_of_frozen
    (preferred : Ladder.Stage kappa → Option V)
    (hfrozen : CanonicalInactiveStagesFrozen (G := G) preferred) :
    (G.canonicalLadderCore kappa preferred).MarksTimeAfterExhaustion := by
  intro a b hnone hab
  have hbInactive :
      ¬ CanonicalStageActive (G := G) preferred b := by
    by_cases haActive : CanonicalStageActive (G := G) preferred a
    · have haEmpty :
          (G.canonicalLadderCore kappa preferred).markerCandidates a = ∅ :=
        (canonicalLadderCore_marker_eq_none_iff preferred a haActive).1 hnone
      have habv : a.1 < b.1 := hab
      have hasBound : a.1 + 1 < kappa.ord :=
        ((Order.add_one_le_iff).2 habv).trans_lt b.2
      let a' : Ladder.Stage kappa := ⟨a.1 + 1, hasBound⟩
      have ha'Inactive :
          ¬ CanonicalStageActive (G := G) preferred a' := by
        change (G.canonicalLadderState kappa preferred
          (Ladder.Stage.succExtended a)).2 ≠ true
        exact canonicalLadderState_succ_inactive_of_candidates_empty
          preferred a haEmpty
      apply G.canonicalLadderState_inactive_mono kappa preferred
        (a := a') (b := b)
      · change a.1 + 1 ≤ b.1
        exact (Order.add_one_le_iff).2 hab
      · exact ha'Inactive
    · exact G.canonicalLadderState_inactive_mono kappa preferred
        hab.le haActive
  constructor
  · change G.ladderMarkerOfState (preferred b)
      (G.canonicalLadderState kappa preferred
        (Ladder.Stage.toExtended b)) = none
    exact G.ladderMarkerOfState_eq_none_of_inactive _ _ hbInactive
  · exact (G.canonicalLadderCore kappa preferred).stageWeb b
      |>.chosenMaximalWave_eq_trivialWave (hfrozen b hbInactive).2

end KappaLadder

/-- Candidate formation only depends on the path-family component of an
accumulation state, not on its Boolean activity flag. -/
theorem ladderMarkerCandidatesOfState_eq_of_fst_eq
    {s t : G.LadderAccumulationState} (hst : s.1 = t.1) :
    G.ladderMarkerCandidatesOfState s =
      G.ladderMarkerCandidatesOfState t := by
  rcases s with ⟨W, active⟩
  rcases t with ⟨Z, active'⟩
  simp only at hst
  subst Z
  rfl

/-- After the unrestricted canonical recursion becomes inactive, its path
family is literally constant at every later ordinal.  At genuine limits
this uses that the threadwise direct limit of an eventually constant growing
warp chain is the stabilized family. -/
theorem ladderAccumulatedStateAux_fst_eq_of_inactive
    (hNoEnter : G.NoEdgeEnters G.source)
    (preferred : Ordinal.{u} → Option V) :
    ∀ b a, a ≤ b →
      (G.ladderAccumulatedStateAux
        (G.ladderSuccessorState preferred) a).2 ≠ true →
      (G.ladderAccumulatedStateAux
        (G.ladderSuccessorState preferred) b).1 =
      (G.ladderAccumulatedStateAux
        (G.ladderSuccessorState preferred) a).1 := by
  intro b
  induction b using Ordinal.limitRecOn with
  | zero =>
      intro a hab _ha
      have ha0 : a = 0 := bot_unique hab
      subst a
      rfl
  | add_one o ih =>
      intro a hab ha
      by_cases hao : a = o + 1
      · subst a
        rfl
      · have hao' : a ≤ o :=
          (Order.lt_add_one_iff).1 (lt_of_le_of_ne hab hao)
        have hoInactive := G.ladderAccumulatedStateAux_inactive_mono
          preferred o a hao' ha
        have hstep :
            G.ladderAccumulatedStateAux
                (G.ladderSuccessorState preferred) (o + 1) =
              G.ladderSuccessorState preferred o
                (G.ladderAccumulatedStateAux
                  (G.ladderSuccessorState preferred) o) := by
          simp [ladderAccumulatedStateAux]
        rw [hstep, ladderSuccessorState, dif_neg hoInactive]
        exact ih a hao' ha
  | limit o ho ih =>
      intro a hab ha
      by_cases hao : a = o
      · subst a
        rfl
      · have hao' : a < o := lt_of_le_of_ne hab hao
        have hinv (z : Ordinal.{u}) :
            KappaLadder.CanonicalRecursionInvariant (G := G)
              (G.ladderSuccessorState preferred) z :=
          KappaLadder.canonicalRecursionInvariant_all hNoEnter preferred z
        have hmatching : G.HasMatchingLadderChain o
            (fun z _hz ↦ G.ladderAccumulatedStateAux
              (G.ladderSuccessorState preferred) z) :=
          G.hasMatchingLadderChain_of_invariants
            (G.ladderSuccessorState preferred) o
            (fun z hz ↦ ⟨(hinv z).warp, (hinv z).grows⟩)
        let C : G.GrowingWarpChain (Set.Iio o) :=
          Classical.choose hmatching
        have hstage (z : Set.Iio o) :
            C.stage z =
              (G.ladderAccumulatedStateAux
                (G.ladderSuccessorState preferred) z.1).1 :=
          Classical.choose_spec hmatching z
        have hstate :
            (G.ladderAccumulatedStateAux
              (G.ladderSuccessorState preferred) o).1 =
              C.limitPaths G := by
          rw [ladderAccumulatedStateAux,
            Ordinal.limitRecOn_limit _ _ _ _ ho]
          simp only [ladderLimitState]
          split
          · rfl
          · rename_i h
            exact (h hmatching).elim
        let : Nonempty (Set.Iio o) := ho.nonempty_Iio.to_subtype
        let ai : Set.Iio o := ⟨a, hao'⟩
        have hconstant : ∀ z, ai ≤ z → C.stage z = C.stage ai := by
          intro z haz
          rw [hstage z, hstage ai]
          exact ih z.1 z.2 a haz ha
        rw [hstate, C.limitPaths_eq_stage_of_eventually_constant G ai
          hconstant, hstage ai]

/-- In the unrestricted recursion, every inactive state is already an
exhausted and loose frozen stage.  The successor case is the quotient
calculation in `LadderExhaustionLoose`; the limit case reduces to an earlier
inactive state by literal stabilization. -/
theorem ladderAccumulatedStateAux_inactive_frozen
    (hNoEnter : G.NoEdgeEnters G.source)
    (preferred : Ordinal.{u} → Option V) :
    ∀ o,
      (G.ladderAccumulatedStateAux
        (G.ladderSuccessorState preferred) o).2 ≠ true →
      G.ladderMarkerCandidatesOfState
          (G.ladderAccumulatedStateAux
            (G.ladderSuccessorState preferred) o) = ∅ ∧
        (G.stageWebOf
          (G.ladderAccumulatedStateAux
            (G.ladderSuccessorState preferred) o).1).IsLoose := by
  intro o
  induction o using Ordinal.limitRecOn with
  | zero =>
      intro h
      exact (h (by simp [ladderAccumulatedStateAux])).elim
  | add_one o ih =>
      intro hnextInactive
      let s := G.ladderAccumulatedStateAux
        (G.ladderSuccessorState preferred) o
      have hnext :
          G.ladderAccumulatedStateAux
              (G.ladderSuccessorState preferred) (o + 1) =
            G.ladderSuccessorState preferred o s := by
        simp [s, ladderAccumulatedStateAux]
      by_cases hs : s.2 = true
      · have hnotNonempty :
            ¬ (G.ladderMarkerCandidatesOfState s).Nonempty := by
          intro hne
          apply hnextInactive
          rw [hnext, ladderSuccessorState, dif_pos hs, if_pos hne]
        have hempty : G.ladderMarkerCandidatesOfState s = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp hnotNonempty
        have hinv := KappaLadder.canonicalRecursionInvariant_all
          hNoEnter preferred o
        have hnextExact :
            G.ladderAccumulatedStateAux
                (G.ladderSuccessorState preferred) (o + 1) =
              (G.activeLadderSuccessor (preferred o) s, false) := by
          rw [hnext, ladderSuccessorState, dif_pos hs, if_neg hnotNonempty]
        rw [hnextExact]
        constructor
        · exact G.ladderMarkerCandidatesOfState_activeLadderSuccessor_eq_empty
            hNoEnter (preferred o) s false hs hinv.warp hinv.selfRoof
              hinv.sourceRoof hempty
        · exact G.stageWebOf_activeLadderSuccessor_isLoose_of_candidates_empty
            hNoEnter (preferred o) s hs hinv.warp hinv.selfRoof
              hinv.sourceRoof hempty
      · have hprior := ih hs
        have hfamily :
            (G.ladderAccumulatedStateAux
              (G.ladderSuccessorState preferred) (o + 1)).1 = s.1 := by
          rw [hnext, ladderSuccessorState, dif_neg hs]
        have hcandidates := G.ladderMarkerCandidatesOfState_eq_of_fst_eq
          (s := G.ladderAccumulatedStateAux
            (G.ladderSuccessorState preferred) (o + 1))
          (t := s) hfamily
        constructor
        · rw [hcandidates]
          exact hprior.1
        · rw [hfamily]
          exact hprior.2
  | limit o ho ih =>
      intro hoInactive
      have hinv (z : Ordinal.{u}) :
          KappaLadder.CanonicalRecursionInvariant (G := G)
            (G.ladderSuccessorState preferred) z :=
        KappaLadder.canonicalRecursionInvariant_all hNoEnter preferred z
      have hmatching : G.HasMatchingLadderChain o
          (fun z _hz ↦ G.ladderAccumulatedStateAux
            (G.ladderSuccessorState preferred) z) :=
        G.hasMatchingLadderChain_of_invariants
          (G.ladderSuccessorState preferred) o
          (fun z hz ↦ ⟨(hinv z).warp, (hinv z).grows⟩)
      have hnotAll : ¬ G.AllPriorLadderStagesActive o
          (fun z hz ↦ G.ladderAccumulatedStateAux
            (G.ladderSuccessorState preferred) z) := by
        intro hall
        apply hoInactive
        rw [ladderAccumulatedStateAux,
          Ordinal.limitRecOn_limit _ _ _ _ ho]
        simp only [ladderLimitState]
        have hmatching' : G.HasMatchingLadderChain o
            (fun z _hz ↦ Ordinal.limitRecOn z (G.trivialWave, true)
              (G.ladderSuccessorState preferred) G.ladderLimitState) := by
          simpa only [ladderAccumulatedStateAux] using hmatching
        have hall' : G.AllPriorLadderStagesActive o
            (fun z _hz ↦ Ordinal.limitRecOn z (G.trivialWave, true)
              (G.ladderSuccessorState preferred) G.ladderLimitState) := by
          simpa only [ladderAccumulatedStateAux] using hall
        rw [dif_pos hmatching', if_pos hall']
      rw [AllPriorLadderStagesActive] at hnotAll
      push_neg at hnotAll
      obtain ⟨b, hb, hbInactive⟩ := hnotAll
      have hprior := ih b hb hbInactive
      have hfamily := G.ladderAccumulatedStateAux_fst_eq_of_inactive
        hNoEnter preferred o b hb.le hbInactive
      have hcandidates := G.ladderMarkerCandidatesOfState_eq_of_fst_eq
        (s := G.ladderAccumulatedStateAux
          (G.ladderSuccessorState preferred) o)
        (t := G.ladderAccumulatedStateAux
          (G.ladderSuccessorState preferred) b) hfamily
      constructor
      · rw [hcandidates]
        exact hprior.1
      · rw [hfamily]
        exact hprior.2

namespace KappaLadder

variable {G : DWeb V} {kappa : Cardinal.{u}}

/-- Every inactive ordinary stage of the canonical ladder is exhausted and
loose.  This is the restricted-stage form of the unrestricted transfinite
freezing theorem. -/
theorem canonicalLadderCore_inactiveStagesFrozen
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    CanonicalInactiveStagesFrozen (G := G) preferred := by
  intro a ha
  change G.ladderMarkerCandidatesOfState
        (G.ladderAccumulatedStateAux
          (G.ladderSuccessorState
            (extendLadderPreference kappa preferred)) a.1) = ∅ ∧
      (G.stageWebOf
        (G.ladderAccumulatedStateAux
          (G.ladderSuccessorState
            (extendLadderPreference kappa preferred)) a.1).1).IsLoose
  exact G.ladderAccumulatedStateAux_inactive_frozen hNoEnter
    (extendLadderPreference kappa preferred) a.1 ha

/-- Marker absence is exactly exhaustion of the canonical candidate set at
every stage, including all stages after the recursion freezes. -/
theorem canonicalLadderCore_marker_none_iff_candidates_empty
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source)
    (a : Ladder.Stage kappa) :
    (G.canonicalLadderCore kappa preferred).marker a = none ↔
      (G.canonicalLadderCore kappa preferred).markerCandidates a = ∅ :=
  canonicalLadderCore_marker_none_iff_candidates_empty_of_frozen
    preferred (canonicalLadderCore_inactiveStagesFrozen preferred hNoEnter) a

/-- The canonical core satisfies the complete fresh-marker law. -/
theorem canonicalLadderCore_hasFreshMarkers
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (G.canonicalLadderCore kappa preferred).HasFreshMarkers := by
  refine ⟨canonicalLadderCore_marker_none_iff_candidates_empty
      preferred hNoEnter, ?_⟩
  intro a y hy
  exact ⟨G.ladderMarkerOfState_mem_candidates hy,
    canonicalLadderCore_trivialPath_mem_successorWarp preferred a hy⟩

/-- The canonical core marks time after the first exhausted stage. -/
theorem canonicalLadderCore_marksTimeAfterExhaustion
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (G.canonicalLadderCore kappa preferred).MarksTimeAfterExhaustion :=
  canonicalLadderCore_marksTimeAfterExhaustion_of_frozen preferred
    (canonicalLadderCore_inactiveStagesFrozen preferred hNoEnter)

/-- The strengthened canonical roof recursion supplies all geometry needed
to make the core marker map injective. -/
theorem canonicalLadderCore_markersInjective
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (G.canonicalLadderCore kappa preferred).MarkersInjective := by
  have hgeometry := canonicalLadder_geometry (G := G) preferred hNoEnter
  apply canonicalLadderCore_markersInjective_of_geometry preferred
  exact
    { sourceRoof := hgeometry.roofsSourceAtStages
      selfRoof := hgeometry.selfRoofing
      grows := hgeometry.grows }

/-- Exact marker exhaustion for the bookkeeping-installed canonical ladder. -/
theorem canonicalLadderWithBookkeeping_marker_none_iff_candidates_empty
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source)
    (a : Ladder.Stage kappa) :
    (canonicalLadder G kappa preferred).marker a = none ↔
      (canonicalLadder G kappa preferred).markerCandidates a = ∅ :=
  canonicalLadderCore_marker_none_iff_candidates_empty
    preferred hNoEnter a

/-- Fresh markers for the bookkeeping-installed canonical ladder. -/
theorem canonicalLadderWithBookkeeping_hasFreshMarkers
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (canonicalLadder G kappa preferred).HasFreshMarkers :=
  canonicalLadderCore_hasFreshMarkers preferred hNoEnter

/-- Pairwise distinct markers for the bookkeeping-installed canonical
ladder. -/
theorem canonicalLadderWithBookkeeping_markersInjective
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (canonicalLadder G kappa preferred).MarkersInjective :=
  canonicalLadderCore_markersInjective preferred hNoEnter

/-- Marking-time persistence for the bookkeeping-installed canonical
ladder. -/
theorem canonicalLadderWithBookkeeping_marksTimeAfterExhaustion
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (canonicalLadder G kappa preferred).MarksTimeAfterExhaustion :=
  canonicalLadderCore_marksTimeAfterExhaustion preferred hNoEnter

/-- The full positive and negative marker clauses for the canonical core,
once the graph-theoretic frozen-stage property has been established. -/
theorem canonicalLadderCore_hasFreshMarkers_of_frozen
    (preferred : Ladder.Stage kappa → Option V)
    (hfrozen : CanonicalInactiveStagesFrozen (G := G) preferred) :
    (G.canonicalLadderCore kappa preferred).HasFreshMarkers := by
  refine ⟨canonicalLadderCore_marker_none_iff_candidates_empty_of_frozen
      preferred hfrozen, ?_⟩
  intro a y hy
  constructor
  · exact G.ladderMarkerOfState_mem_candidates hy
  · exact canonicalLadderCore_trivialPath_mem_successorWarp
      preferred a hy

/-- Installing the independent bookkeeping choice preserves marker
injectivity. -/
theorem withValidBookkeeping_markersInjective
    (L : G.KappaLadder kappa) (hL : L.MarkersInjective) :
    L.withValidBookkeeping.MarkersInjective := by
  intro a b y ha hb
  exact hL ha hb

/-- Installing the independent bookkeeping choice preserves the exact
marker-exhaustion and insertion clauses. -/
theorem withValidBookkeeping_hasFreshMarkers
    (L : G.KappaLadder kappa) (hL : L.HasFreshMarkers) :
    L.withValidBookkeeping.HasFreshMarkers := by
  exact hL

/-- Installing the independent bookkeeping choice preserves marking time. -/
theorem withValidBookkeeping_marksTimeAfterExhaustion
    (L : G.KappaLadder kappa) (hL : L.MarksTimeAfterExhaustion) :
    L.withValidBookkeeping.MarksTimeAfterExhaustion := by
  exact hL

end KappaLadder
end DWeb
end Erdos599
