/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureShortcutDegeneracy

/-!
# Contained avoiding witnesses for actual nondegenerate shortcut intervals

The smaller closure supplies a filtered large family, and the actual causal
large diagnostic replaces it inside the original global carrier. Cardinal
avoidance then selects a path missing any prescribed small forbidden set in
its interior. The starting hypothesis concerns the actual interval's
nondegeneracy, not a bare strong-edge proposition.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}
variable {A : PostClosureCompressorAssignment T} {e : V × V}

theorem ShortcutIntervalWitness.exists_contained_avoiding_path_of_filtered_large
    (W : ShortcutIntervalWitness A e)
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {causalSeed : Set V} (hseed : #causalSeed ≤ succ kappa)
    (hC : C.ladder = CausalSection9Rows.finalLadder
      Gamma kappa hkappa hGamma causalSeed hseed)
    (hZ : globalZ = CausalSection9Rows.globalCarrier
      Gamma kappa hkappa hGamma causalSeed hseed)
    (hlarge : HasFilteredNondegenerateHammockCard Gamma C.ladder.limitWarp
      e.1 (.vertex e.2)
      (CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder)
      (succ kappa))
    {F : Set V} (hF : #F ≤ kappa) :
    ∃ Q : AltPath Gamma.graph,
      Q.vertexSet ⊆ globalZ ∧ IsSafe C.ladder.limitWarp Q ∧
      Q.initial = e.1 ∧ HasEnd Q (.vertex e.2) ∧
      ¬IsDegenerate C.ladder.limitWarp Q (.vertex e.2) ∧
      CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder Q ∧
      Disjoint (hammockInterior e.1 (.vertex e.2) Q) F := by
  have hglobal : Rlimit.closedSet ⊆
      CausalSection9Rows.globalCarrier Gamma kappa hkappa hGamma causalSeed hseed := by
    simpa only [hZ] using Rlimit.subset_global
  have helig : HammockEligible
      (CausalSection9Rows.globalCarrier Gamma kappa hkappa hGamma causalSeed hseed)
      C.ladder.limitStrictRoof C.ladder.limitRoof e.1 (.vertex e.2) :=
    ⟨⟨hglobal W.eligible.1.1, W.eligible.1.2⟩,
      ⟨hglobal W.eligible.2.1, W.eligible.2.2⟩⟩
  rw [hC] at helig hlarge
  have hresult := CausalSection9Rows.exists_nondegenerate_path_in_globalCarrier_disjoint
    hkappa hGamma hseed W.distinct helig hlarge hF
  simpa only [hC, hZ] using hresult

theorem ShortcutIntervalWitness.exists_contained_avoiding_path_of_nondegenerate
    (W : ShortcutIntervalWitness A e)
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {causalSeed : Set V} (hseed : #causalSeed ≤ succ kappa)
    (hC : C.ladder = CausalSection9Rows.finalLadder
      Gamma kappa hkappa hGamma causalSeed hseed)
    (hZ : globalZ = CausalSection9Rows.globalCarrier
      Gamma kappa hkappa hGamma causalSeed hseed)
    (hfiltered : FiniteFilteredHammockClosedUpTo Gamma C.ladder.limitWarp
      Rlimit.closedSet Rlimit.closedSet C.ladder.limitStrictRoof C.ladder.limitRoof
        (CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder) kappa)
    (hnondeg : ¬IsDegenerate C.ladder.limitWarp W.path (.vertex e.2))
    {F : Set V} (hF : #F ≤ kappa) :
    ∃ Q : AltPath Gamma.graph,
      Q.vertexSet ⊆ globalZ ∧ IsSafe C.ladder.limitWarp Q ∧
      Q.initial = e.1 ∧ HasEnd Q (.vertex e.2) ∧
      ¬IsDegenerate C.ladder.limitWarp Q (.vertex e.2) ∧
      CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder Q ∧
      Disjoint (hammockInterior e.1 (.vertex e.2) Q) F :=
  W.exists_contained_avoiding_path_of_filtered_large hkappa hGamma hseed hC hZ
    (W.filtered_large_of_not_isDegenerate hfiltered hnondeg) hF

#print axioms ShortcutIntervalWitness.exists_contained_avoiding_path_of_filtered_large
#print axioms ShortcutIntervalWitness.exists_contained_avoiding_path_of_nondegenerate

end Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment
