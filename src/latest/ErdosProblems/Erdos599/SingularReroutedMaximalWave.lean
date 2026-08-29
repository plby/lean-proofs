/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularSafeDesignatedLimit

/-!
# Rerouted resurrection of maximal residual waves

Lifting a maximal wave from `G.delete X` and adding trivial paths at the
deleted sources is in general too weak, even when the deletion is
unhindered: a surviving source may have a path to a target in `X`.  The
correct limit witness is allowed to reroute the deleted-source components
depending on the maximal residual wave.

This file records the exact consumer of that witness.  For every maximal
wave `M` in the final residual, it is enough to find an ambient family `R`
whose initial set consists precisely of the sources removed by `X` and such
that `R` together with the lift of `M` is an ambient wave.  Ambient
unhinderedness then forces `M` to start at every surviving source.  Notice
that neither the paths nor the carrier of `R` are required to agree with the
family whose carrier was deleted; this is the M-dependent exchange allowed
at the limit.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularReroutedMaximalWave

open SingularSafeDesignatedLimit

universe u

variable {V : Type u}

/-- An M-dependent ambient resurrection of one residual wave.  The rerouted
family starts at exactly the ambient sources removed by `X`. -/
structure ReroutedWaveWitness (G : DWeb V) (X : Set V)
    (M : (G.delete X).Wave) where
  paths : Set G.DPath
  initialSet_eq : G.initialSet paths = G.source ∩ X
  wave : G.IsWave (paths ∪ G.liftDeleteFamily X M.1)

/-- Every maximal wave of the final residual admits an M-dependent ambient
resurrection. -/
def MaximalWavesRerouteAcrossDelete (G : DWeb V) (X : Set V) : Prop :=
  ∀ M : (G.delete X).Wave, IsMax M →
    Nonempty (ReroutedWaveWitness G X M)

namespace ReroutedWaveWitness

variable {G : DWeb V} {X : Set V} {M : (G.delete X).Wave}

/-- The initial set of the resurrected union is the deleted ambient sources
together with the initial set of the residual wave. -/
theorem initialSet_union (R : ReroutedWaveWitness G X M) :
    G.initialSet (R.paths ∪ G.liftDeleteFamily X M.1) =
      (G.source ∩ X) ∪ (G.delete X).initialSet M.1 := by
  rw [G.initialSet_union, R.initialSet_eq,
    G.initialSet_liftDeleteFamily]

end ReroutedWaveWitness

/-- M-dependent rerouted resurrection transports ambient unhinderedness to
the final deleted web. -/
theorem maximalWaveComplete_delete_of_rerouted
    {G : DWeb V} {X : Set V}
    (hG : G.IsUnhindered)
    (hreroute : MaximalWavesRerouteAcrossDelete G X) :
    MaximalWaveComplete (G.delete X) := by
  intro M hMmax
  obtain ⟨R⟩ := hreroute M hMmax
  have hfull :
      G.initialSet (R.paths ∪ G.liftDeleteFamily X M.1) = G.source :=
    G.isUnhindered_iff.mp hG _ R.wave
  rw [R.initialSet_union] at hfull
  apply Set.Subset.antisymm M.2.2.1
  intro a ha
  have haSource : a ∈ G.source := ha.1
  have haUnion :
      a ∈ (G.source ∩ X) ∪ (G.delete X).initialSet M.1 :=
    hfull.symm ▸ haSource
  rcases haUnion with haDeleted | haM
  · exact (ha.2 haDeleted.2).elim
  · exact haM

/-- The machine-facing form: rerouted resurrection proves that the final
residual is unhindered. -/
theorem isUnhindered_delete_of_rerouted
    {G : DWeb V} {X : Set V}
    (hG : G.IsUnhindered)
    (hreroute : MaximalWavesRerouteAcrossDelete G X) :
    (G.delete X).IsUnhindered :=
  isUnhindered_of_maximalWaveComplete
    (maximalWaveComplete_delete_of_rerouted hG hreroute)

/-! ## Adapters for construction-facing linkage witnesses -/

/-- A target linkage on the deleted sources supplies the exact initial-set
field required by a rerouted witness.  The linkage itself may depend on
`M`; only the ambient-wave union is used by the limit argument. -/
def witnessOfLinkage
    {G : DWeb V} {X : Set V} {M : (G.delete X).Wave}
    {P : Set G.DPath}
    (hP : IsLinkageBetween G (G.source ∩ X) G.target P)
    (hWave : G.IsWave (P ∪ G.liftDeleteFamily X M.1)) :
    ReroutedWaveWitness G X M where
  paths := P
  initialSet_eq := hP.initialSet_eq
  wave := hWave

/-- Pointwise construction of M-dependent target linkages is sufficient for
the complete rerouted-resurrection predicate. -/
theorem maximalWavesRerouteAcrossDelete_of_linkages
    {G : DWeb V} {X : Set V}
    (hlink : ∀ M : (G.delete X).Wave, IsMax M →
      ∃ P : Set G.DPath,
        IsLinkageBetween G (G.source ∩ X) G.target P ∧
          G.IsWave (P ∪ G.liftDeleteFamily X M.1)) :
    MaximalWavesRerouteAcrossDelete G X := by
  intro M hMmax
  obtain ⟨P, hP, hWave⟩ := hlink M hMmax
  exact ⟨witnessOfLinkage hP hWave⟩

/-- Direct deletion theorem in the exact form produced by an M-dependent
lower-cardinal exchange. -/
theorem isUnhindered_delete_of_rerouted_linkages
    {G : DWeb V} {X : Set V}
    (hG : G.IsUnhindered)
    (hlink : ∀ M : (G.delete X).Wave, IsMax M →
      ∃ P : Set G.DPath,
        IsLinkageBetween G (G.source ∩ X) G.target P ∧
          G.IsWave (P ∪ G.liftDeleteFamily X M.1)) :
    (G.delete X).IsUnhindered := by
  apply isUnhindered_delete_of_rerouted hG
  exact maximalWavesRerouteAcrossDelete_of_linkages hlink

#print axioms maximalWaveComplete_delete_of_rerouted
#print axioms isUnhindered_delete_of_rerouted
#print axioms isUnhindered_delete_of_rerouted_linkages

end SingularReroutedMaximalWave
end CardinalInduction
end Erdos599

