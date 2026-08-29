/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularReroutedMaximalWave

/-!
# Initial-profile restoration of maximal residual waves

To prove that `G.delete X` is unhindered, an ambient comparison wave does
not have to contain the lifted residual wave literally.  The only datum used
by the maximal-wave argument is its set of initial vertices.  Consequently
all paths may be rerouted: for every maximal residual wave `M`, it is enough
to construct an ambient wave whose initial set is the union of the deleted
ambient sources and the initial set of `M`.

This is strictly weaker than `MaximalWavesRerouteAcrossDelete`.  It is the
source-faithful interface naturally produced by an arrow or alternating
exchange, both of which may replace residual components while preserving
their initial coordinates.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMaximalWaveInitialProfile

open SingularSafeDesignatedLimit SingularReroutedMaximalWave

universe u

variable {V : Type u}

/-- An ambient wave with exactly the initial profile needed to test whether
the residual wave `M` is full.  No path of `M` has to occur literally in
`paths`. -/
structure InitialProfileWaveWitness (G : DWeb V) (X : Set V)
    (M : (G.delete X).Wave) where
  paths : Set G.DPath
  wave : G.IsWave paths
  initialSet_eq :
    G.initialSet paths =
      (G.source ∩ X) ∪ (G.delete X).initialSet M.1

/-- Every maximal residual wave has an ambient wave with the same surviving
initial coordinates, together with all source coordinates removed by the
deletion. -/
def MaximalWaveInitialProfilesLiftAcrossDelete
    (G : DWeb V) (X : Set V) : Prop :=
  ∀ M : (G.delete X).Wave, IsMax M →
    Nonempty (InitialProfileWaveWitness G X M)

/-- Initial-profile restoration is sufficient to make every maximal wave in
the deleted web full. -/
theorem maximalWaveComplete_delete_of_initialProfiles
    {G : DWeb V} {X : Set V}
    (hG : G.IsUnhindered)
    (hprofiles : MaximalWaveInitialProfilesLiftAcrossDelete G X) :
    MaximalWaveComplete (G.delete X) := by
  intro M hMmax
  obtain ⟨R⟩ := hprofiles M hMmax
  have hfull : G.initialSet R.paths = G.source :=
    G.isUnhindered_iff.mp hG R.paths R.wave
  have hprofile :
      (G.source ∩ X) ∪ (G.delete X).initialSet M.1 = G.source :=
    R.initialSet_eq.symm.trans hfull
  apply Set.Subset.antisymm M.2.2.1
  intro a ha
  have haUnion :
      a ∈ (G.source ∩ X) ∪ (G.delete X).initialSet M.1 :=
    hprofile.symm ▸ ha.1
  rcases haUnion with haDeleted | haM
  · exact (ha.2 haDeleted.2).elim
  · exact haM

/-- Machine-facing deletion theorem using only maximal-wave initial
profiles. -/
theorem isUnhindered_delete_of_initialProfiles
    {G : DWeb V} {X : Set V}
    (hG : G.IsUnhindered)
    (hprofiles : MaximalWaveInitialProfilesLiftAcrossDelete G X) :
    (G.delete X).IsUnhindered :=
  isUnhindered_of_maximalWaveComplete
    (maximalWaveComplete_delete_of_initialProfiles hG hprofiles)

/-- A literal rerouted witness is, in particular, an initial-profile
witness.  This adapter retains compatibility with the stronger earlier
interface while allowing new constructions to target the weaker one. -/
def initialProfileWitnessOfRerouted
    {G : DWeb V} {X : Set V} {M : (G.delete X).Wave}
    (R : ReroutedWaveWitness G X M) :
    InitialProfileWaveWitness G X M where
  paths := R.paths ∪ G.liftDeleteFamily X M.1
  wave := R.wave
  initialSet_eq := R.initialSet_union

/-- The earlier literal-residual rerouting predicate implies the exact
initial-profile predicate. -/
theorem maximalWaveInitialProfiles_of_rerouted
    {G : DWeb V} {X : Set V}
    (hreroute : MaximalWavesRerouteAcrossDelete G X) :
    MaximalWaveInitialProfilesLiftAcrossDelete G X := by
  intro M hMmax
  obtain ⟨R⟩ := hreroute M hMmax
  exact ⟨initialProfileWitnessOfRerouted R⟩

#print axioms maximalWaveComplete_delete_of_initialProfiles
#print axioms isUnhindered_delete_of_initialProfiles
#print axioms maximalWaveInitialProfiles_of_rerouted

end SingularMaximalWaveInitialProfile
end CardinalInduction
end Erdos599
