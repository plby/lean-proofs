/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Ladder

/-!
# Structural induction for the canonical ladder recursion

This file discharges the genuinely transfinite part of the ladder
construction.  It is deliberately stated first for an arbitrary successor
operation: once a successor sends warps to warps and extends every old
component, the fallback branch in `ladderLimitState` is never reached.
Consequently every limit is the genuine threadwise direct limit of all
earlier stages.

The local graph-theoretic successor obligations for the canonical rung and
marker are kept separate.  This separation makes explicit that no property
of a limit is being assumed in order to define that limit.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- One-sided pathwise growth, permitting fresh components in the later
family. -/
def LadderGrows (U W : Set G.DPath) : Prop :=
  ∀ p ∈ U, ∃ q ∈ W, G.Extends p q

theorem ladderGrows_refl (U : Set G.DPath) : G.LadderGrows U U := by
  intro p hp
  exact ⟨p, hp, G.extends_refl p⟩

theorem LadderGrows.trans {U W Z : Set G.DPath}
    (hUW : G.LadderGrows U W) (hWZ : G.LadderGrows W Z) :
    G.LadderGrows U Z := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := hUW p hp
  obtain ⟨r, hr, hqr⟩ := hWZ q hq
  exact ⟨r, hr, G.extends_trans hpq hqr⟩

/-- The induction invariant for the unrestricted ordinal recursion: the
current family is a warp and every earlier family grows into it. -/
def LadderRecursionInvariant
    (step : Ordinal.{u} → G.LadderAccumulationState →
      G.LadderAccumulationState)
    (o : Ordinal.{u}) : Prop :=
  G.IsWarp (G.ladderAccumulatedStateAux step o).1 ∧
    ∀ b, b < o →
      G.LadderGrows (G.ladderAccumulatedStateAux step b).1
        (G.ladderAccumulatedStateAux step o).1

/-- Earlier invariant stages form the exact growing chain required by the
limit constructor. -/
noncomputable def ladderChainOfInvariants
    (step : Ordinal.{u} → G.LadderAccumulationState →
      G.LadderAccumulationState)
    (o : Ordinal.{u})
    (ih : ∀ b, b < o → G.LadderRecursionInvariant step b) :
    G.GrowingWarpChain (Set.Iio o) where
  stage b := (G.ladderAccumulatedStateAux step b.1).1
  isWarp b := (ih b.1 b.2).1
  grows := by
    intro i j hij p hp
    rcases hij.lt_or_eq with hij | rfl
    · exact (ih j.1 j.2).2 i.1 hij p hp
    · exact ⟨p, hp, G.extends_refl p⟩

@[simp]
theorem ladderChainOfInvariants_stage
    (step : Ordinal.{u} → G.LadderAccumulationState →
      G.LadderAccumulationState)
    (o : Ordinal.{u})
    (ih : ∀ b, b < o → G.LadderRecursionInvariant step b)
    (b : Set.Iio o) :
    (G.ladderChainOfInvariants step o ih).stage b =
      (G.ladderAccumulatedStateAux step b.1).1 :=
  rfl

theorem hasMatchingLadderChain_of_invariants
    (step : Ordinal.{u} → G.LadderAccumulationState →
      G.LadderAccumulationState)
    (o : Ordinal.{u})
    (ih : ∀ b, b < o → G.LadderRecursionInvariant step b) :
    G.HasMatchingLadderChain o
      (fun b _hb ↦ G.ladderAccumulatedStateAux step b) := by
  exact ⟨G.ladderChainOfInvariants step o ih, fun _ ↦ rfl⟩

/-- Transfinite closure theorem for the ladder accumulator.  The two
hypotheses are precisely the local successor obligations; all warp and
direct-limit facts at arbitrary ordinals are derived here. -/
theorem ladderRecursionInvariant_all
    (step : Ordinal.{u} → G.LadderAccumulationState →
      G.LadderAccumulationState)
    (stepWarp : ∀ o s, G.IsWarp s.1 → G.IsWarp (step o s).1)
    (stepGrows : ∀ o s, G.IsWarp s.1 →
      G.LadderGrows s.1 (step o s).1) :
    ∀ o, G.LadderRecursionInvariant step o := by
  intro o
  induction o using Ordinal.limitRecOn with
  | zero =>
      constructor
      · simpa [ladderAccumulatedStateAux] using G.isWarp_trivialWave
      · intro b hb
        exact (not_lt_of_ge (bot_le : (0 : Ordinal.{u}) ≤ b) hb).elim
  | add_one o ih =>
      have hstate :
          G.ladderAccumulatedStateAux step (o + 1) =
            step o (G.ladderAccumulatedStateAux step o) := by
        simp [ladderAccumulatedStateAux]
      constructor
      · rw [hstate]
        exact stepWarp o _ ih.1
      · intro b hb
        have hbo : b ≤ o := (Order.lt_add_one_iff).1 hb
        rw [hstate]
        rcases hbo.lt_or_eq with hbo | heq
        · exact LadderGrows.trans (G := G) (ih.2 b hbo)
            (stepGrows o _ ih.1)
        · subst b
          exact stepGrows o _ ih.1
  | limit o ho ih =>
      let hchain : G.HasMatchingLadderChain o
          (fun b _hb ↦ G.ladderAccumulatedStateAux step b) :=
        G.hasMatchingLadderChain_of_invariants step o ih
      let C : G.GrowingWarpChain (Set.Iio o) := Classical.choose hchain
      have hstate :
          (G.ladderAccumulatedStateAux step o).1 = C.limitPaths G := by
        rw [ladderAccumulatedStateAux, Ordinal.limitRecOn_limit _ _ _ _ ho]
        simp only [ladderLimitState]
        split
        · rfl
        · rename_i h
          exact (h hchain).elim
      constructor
      · rw [hstate]
        exact C.isWarp_limitPaths G
      · intro b hb
        let bi : Set.Iio o := ⟨b, hb⟩
        have hstage : C.stage bi =
            (G.ladderAccumulatedStateAux step b).1 :=
          Classical.choose_spec hchain bi
        rw [hstate]
        intro p hp
        have hpC : p ∈ C.stage bi := hstage.symm ▸ hp
        exact C.grows_limitPaths G bi p hpC

/-- Under the local successor obligations, the unrestricted recursion has
a matching growing chain at every genuine limit. -/
theorem hasMatchingLadderChain_all
    (step : Ordinal.{u} → G.LadderAccumulationState →
      G.LadderAccumulationState)
    (stepWarp : ∀ o s, G.IsWarp s.1 → G.IsWarp (step o s).1)
    (stepGrows : ∀ o s, G.IsWarp s.1 →
      G.LadderGrows s.1 (step o s).1)
    (o : Ordinal.{u}) :
    G.HasMatchingLadderChain o
      (fun b _hb ↦ G.ladderAccumulatedStateAux step b) :=
  G.hasMatchingLadderChain_of_invariants step o
    (fun b _hb ↦ G.ladderRecursionInvariant_all step stepWarp stepGrows b)

/-- Restricting the structural recursion theorem to stages through `κ`
gives warp-valued accumulated stages. -/
theorem ladderAccumulated_hasWarpStages
    (kappa : Cardinal.{u})
    (step : Ordinal.{u} → G.LadderAccumulationState →
      G.LadderAccumulationState)
    (stepWarp : ∀ o s, G.IsWarp s.1 → G.IsWarp (step o s).1)
    (stepGrows : ∀ o s, G.IsWarp s.1 →
      G.LadderGrows s.1 (step o s).1) :
    ∀ a : Ladder.ExtendedStage kappa,
      G.IsWarp (G.ladderAccumulated kappa step a) := by
  intro a
  exact (G.ladderRecursionInvariant_all step stepWarp stepGrows a.1).1

/-- Every earlier restricted stage grows into every later restricted stage.
This is the global chronology exported by the transfinite induction. -/
theorem ladderAccumulated_grows
    (kappa : Cardinal.{u})
    (step : Ordinal.{u} → G.LadderAccumulationState →
      G.LadderAccumulationState)
    (stepWarp : ∀ o s, G.IsWarp s.1 → G.IsWarp (step o s).1)
    (stepGrows : ∀ o s, G.IsWarp s.1 →
      G.LadderGrows s.1 (step o s).1)
    {a b : Ladder.ExtendedStage kappa} (hab : a ≤ b) :
    G.LadderGrows (G.ladderAccumulated kappa step a)
      (G.ladderAccumulated kappa step b) := by
  rcases hab.lt_or_eq with hab | rfl
  · exact (G.ladderRecursionInvariant_all step stepWarp stepGrows b.1).2
      a.1 hab
  · exact G.ladderGrows_refl _

/-- Restricting the structural recursion theorem to stages through `κ`
also gives the exact direct-limit clause used by `KappaLadder.IsLegal`. -/
theorem ladderAccumulated_hasLimitStages
    (kappa : Cardinal.{u})
    (step : Ordinal.{u} → G.LadderAccumulationState →
      G.LadderAccumulationState)
    (stepWarp : ∀ o s, G.IsWarp s.1 → G.IsWarp (step o s).1)
    (stepGrows : ∀ o s, G.IsWarp s.1 →
      G.LadderGrows s.1 (step o s).1) :
    ∀ (a : Ladder.ExtendedStage kappa), Order.IsSuccLimit a.1 →
      ∃ C : G.GrowingWarpChain (Set.Iio a.1),
        (∀ b : Set.Iio a.1,
          C.stage b = G.ladderAccumulated kappa step
            ⟨b.1, b.2.le.trans a.2⟩) ∧
        G.ladderAccumulated kappa step a = C.limitPaths G := by
  intro a ha
  exact G.exists_ladderLimitChain kappa step a ha
    (G.hasMatchingLadderChain_all step stepWarp stepGrows a.1)

/-! ## Local facts for the canonical successor -/

/-- The two consecutive lifts used by a canonical rung preserve the warp
property. -/
theorem isWarp_liftedLadderRungOfState
    (s : G.LadderAccumulationState) :
    G.IsWarp (G.liftedLadderRungOfState s) := by
  let Q := G.quotient (G.terminalFrontier s.1)
  have hR : Q.essentialPart.IsWarp (G.ladderRungOfState s) :=
    (G.stageWebOf s.1).chosenMaximalWave.property.1
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hpq
  let p' : Q.essentialPart.DPath := p
  let q' : Q.essentialPart.DPath := q
  have hp' : p' ∈ G.ladderRungOfState s := hp
  have hq' : q' ∈ G.ladderRungOfState s := hq
  have hpq' : p' ≠ q' := by
    intro h
    apply hpq
    change G.liftLadderStagePathOf s.1
        (show (G.stageWebOf s.1).DPath from p') =
      G.liftLadderStagePathOf s.1
        (show (G.stageWebOf s.1).DPath from q')
    rw [h]
  have hdisj : Disjoint p'.support q'.support := hR hp' hq' hpq'
  change Disjoint
    (G.liftQuotientPath (G.terminalFrontier s.1)
      (Q.liftEssentialPartPath p')).support
    (G.liftQuotientPath (G.terminalFrontier s.1)
      (Q.liftEssentialPartPath q')).support
  simpa only [G.support_liftQuotientPath,
    Q.support_liftEssentialPartPath] using hdisj

/-- Every old component grows into the canonical successor.  This holds
both while the recursion is active (by the concrete arrow) and after it
has frozen. -/
theorem ladderSuccessorState_grows
    (preferred : Ordinal.{u} → Option V) (o : Ordinal.{u})
    (s : G.LadderAccumulationState) :
    G.LadderGrows s.1 (G.ladderSuccessorState preferred o s).1 := by
  classical
  by_cases hs : s.2 = true
  · rw [ladderSuccessorState, dif_pos hs]
    intro p hp
    obtain ⟨q, hq, hpq⟩ :=
      (G.forwardExtension_arrow s.1 (G.liftedLadderRungOfState s)).1 p hp
    exact ⟨q, Or.inl hq, hpq⟩
  · rw [ladderSuccessorState, dif_neg hs]
    exact G.ladderGrows_refl s.1

/-- A useful exact reduction of the remaining successor-warp obligation:
only disjointness of the optional marker from the concrete arrow is
needed. -/
theorem isWarp_ladderSuccessorState_of_marker_disjoint
    (preferred : Ordinal.{u} → Option V) (o : Ordinal.{u})
    (s : G.LadderAccumulationState) (hwarp : G.IsWarp s.1)
    (hmarker : ∀ {p : G.DPath},
      p ∈ G.arrow s.1 (G.liftedLadderRungOfState s) →
      ∀ {q : G.DPath}, q ∈ G.ladderMarkerPathSetOfState (preferred o) s →
      p ≠ q → Disjoint p.support q.support) :
    G.IsWarp (G.ladderSuccessorState preferred o s).1 := by
  classical
  by_cases hs : s.2 = true
  · rw [ladderSuccessorState, dif_pos hs]
    have harrow :
        G.IsWarp (G.arrow s.1 (G.liftedLadderRungOfState s)) :=
      G.isWarp_arrow hwarp (G.isWarp_liftedLadderRungOfState s)
    change G.IsWarp
      (G.arrow s.1 (G.liftedLadderRungOfState s) ∪
        G.ladderMarkerPathSetOfState (preferred o) s)
    unfold IsWarp
    rw [Set.pairwiseDisjoint_union]
    refine ⟨harrow, ?_, ?_⟩
    · cases hm : G.ladderMarkerOfState (preferred o) s with
      | none => simp [ladderMarkerPathSetOfState, hm]
      | some y =>
          intro p hp q hq hpq
          simp only [ladderMarkerPathSetOfState, hm,
            Set.mem_singleton_iff] at hp hq hpq
          exact (hpq (hp.trans hq.symm)).elim
    · intro p hp q hq hpq
      exact hmarker hp hq hpq
  · rw [ladderSuccessorState, dif_neg hs]
    exact hwarp

/-- Thus the complete warp/direct-limit part of the canonical construction
follows from marker/arrow disjointness at active stages. -/
theorem canonicalLadderCore_structural_of_marker_disjoint
    (kappa : Cardinal.{u})
    (preferred : Ladder.Stage kappa → Option V)
    (hmarker : ∀ o s, G.IsWarp s.1 →
      ∀ {p : G.DPath},
        p ∈ G.arrow s.1 (G.liftedLadderRungOfState s) →
        ∀ {q : G.DPath},
          q ∈ G.ladderMarkerPathSetOfState
            (extendLadderPreference kappa preferred o) s →
          p ≠ q → Disjoint p.support q.support) :
    (G.canonicalLadderCore kappa preferred).HasWarpStages ∧
      (G.canonicalLadderCore kappa preferred).HasLimitStages := by
  let step := G.ladderSuccessorState
    (extendLadderPreference kappa preferred)
  have stepWarp : ∀ o s, G.IsWarp s.1 → G.IsWarp (step o s).1 := by
    intro o s hs
    exact G.isWarp_ladderSuccessorState_of_marker_disjoint _ o s hs
      (hmarker o s hs)
  have stepGrows : ∀ o s, G.IsWarp s.1 →
      G.LadderGrows s.1 (step o s).1 := by
    intro o s _hs
    exact G.ladderSuccessorState_grows _ o s
  constructor
  · intro a
    change G.IsWarp (G.ladderAccumulated kappa step a)
    exact G.ladderAccumulated_hasWarpStages kappa step stepWarp stepGrows a
  · intro a ha
    change ∃ C : G.GrowingWarpChain (Set.Iio a.1),
      (∀ b : Set.Iio a.1,
        C.stage b = G.ladderAccumulated kappa step
          ⟨b.1, b.2.le.trans a.2⟩) ∧
      G.ladderAccumulated kappa step a = C.limitPaths G
    exact G.ladderAccumulated_hasLimitStages kappa step stepWarp stepGrows a ha

/-- Global one-sided growth for the canonical core under the same exact
marker-disjointness obligation. -/
theorem canonicalLadderCore_grows_of_marker_disjoint
    (kappa : Cardinal.{u})
    (preferred : Ladder.Stage kappa → Option V)
    (hmarker : ∀ o s, G.IsWarp s.1 →
      ∀ {p : G.DPath},
        p ∈ G.arrow s.1 (G.liftedLadderRungOfState s) →
        ∀ {q : G.DPath},
          q ∈ G.ladderMarkerPathSetOfState
            (extendLadderPreference kappa preferred o) s →
          p ≠ q → Disjoint p.support q.support)
    {a b : Ladder.ExtendedStage kappa} (hab : a ≤ b) :
    G.LadderGrows
      ((G.canonicalLadderCore kappa preferred).accumulated a)
      ((G.canonicalLadderCore kappa preferred).accumulated b) := by
  let step := G.ladderSuccessorState
    (extendLadderPreference kappa preferred)
  have stepWarp : ∀ o s, G.IsWarp s.1 → G.IsWarp (step o s).1 := by
    intro o s hs
    exact G.isWarp_ladderSuccessorState_of_marker_disjoint _ o s hs
      (hmarker o s hs)
  have stepGrows : ∀ o s, G.IsWarp s.1 →
      G.LadderGrows s.1 (step o s).1 := by
    intro o s _hs
    exact G.ladderSuccessorState_grows _ o s
  change G.LadderGrows (G.ladderAccumulated kappa step a)
    (G.ladderAccumulated kappa step b)
  exact G.ladderAccumulated_grows kappa step stepWarp stepGrows hab

namespace KappaLadder

variable {G : DWeb V}

/-- The canonical core starts with the original trivial wave, independently
of every successor choice. -/
theorem canonicalLadderCore_hasInitialStage
    (kappa : Cardinal.{u})
    (preferred : Ladder.Stage kappa → Option V) :
    (G.canonicalLadderCore kappa preferred).HasInitialStage := by
  exact G.ladderAccumulated_zero kappa _

/-- Every canonical rung is a genuine wave in its essential quotient
stage. -/
theorem canonicalLadderCore_hasWaveRungs
    (kappa : Cardinal.{u})
    (preferred : Ladder.Stage kappa → Option V) :
    (G.canonicalLadderCore kappa preferred).HasWaveRungs := by
  intro a
  exact ((G.canonicalLadderCore kappa preferred).stageWeb a)
    |>.chosenMaximalWave.property

/-- Canonical-core warp stages, reduced to the exact two local successor
facts.  No hypothesis concerning limit stages remains. -/
theorem canonicalLadderCore_hasWarpStages_of_successor
    (kappa : Cardinal.{u})
    (preferred : Ladder.Stage kappa → Option V)
    (stepWarp : ∀ o s, G.IsWarp s.1 →
      G.IsWarp
        (G.ladderSuccessorState
          (extendLadderPreference kappa preferred) o s).1)
    (stepGrows : ∀ o s, G.IsWarp s.1 →
      G.LadderGrows s.1
        (G.ladderSuccessorState
          (extendLadderPreference kappa preferred) o s).1) :
    (G.canonicalLadderCore kappa preferred).HasWarpStages := by
  exact G.ladderAccumulated_hasWarpStages kappa _ stepWarp stepGrows

/-- Canonical-core limit stages, reduced to the exact two local successor
facts. -/
theorem canonicalLadderCore_hasLimitStages_of_successor
    (kappa : Cardinal.{u})
    (preferred : Ladder.Stage kappa → Option V)
    (stepWarp : ∀ o s, G.IsWarp s.1 →
      G.IsWarp
        (G.ladderSuccessorState
          (extendLadderPreference kappa preferred) o s).1)
    (stepGrows : ∀ o s, G.IsWarp s.1 →
      G.LadderGrows s.1
        (G.ladderSuccessorState
          (extendLadderPreference kappa preferred) o s).1) :
    (G.canonicalLadderCore kappa preferred).HasLimitStages := by
  exact G.ladderAccumulated_hasLimitStages kappa _ stepWarp stepGrows

end KappaLadder
end DWeb
end Erdos599
