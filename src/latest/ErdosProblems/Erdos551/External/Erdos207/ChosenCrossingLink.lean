/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.CrossingLinkGraph

/-!
# Crossing covers with chosen balanced link bisections

The robust matching estimate is not valid for an arbitrary half of a link
vertex set.  KSSS first chooses a random balanced bisection preserving link
degrees and codegrees.  This file corrects the structural crossing-cover
interface so it accepts that chosen bisection while retaining the exact
residual-neighbor coverage proof.
-/

namespace Erdos207

open Finset

noncomputable section

/-- A bipartite link is a balanced partition of the exact residual neighbor
set at `v`. -/
def IsResidualBipartition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : TripleSystemOn V) (v : V) (K : BipartiteLink V) : Prop :=
  K.center = v ∧
  K.left ∪ K.right = residualNeighbors G R v ∧
  K.left.card = K.right.card

/-- Covering any chosen residual bipartition covers every residual spoke at
its center. -/
theorem CoversBipartiteLink.covers_residualNeighbors_of_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R M : TripleSystemOn V} {v : V} {K : BipartiteLink V}
    (hK : IsResidualBipartition G R v K)
    (hcover : CoversBipartiteLink K M) :
    ∀ w ∈ residualNeighbors G R v, (coveredGraph M).Adj v w := by
  intro w hw
  have hwUnion : w ∈ K.left ∪ K.right := by
    rw [hK.2.1]
    exact hw
  rcases mem_union.mp hwUnion with hwL | hwR
  · simpa only [hK.1] using hcover.1 w hwL
  · simpa only [hK.1] using hcover.2 w hwR

/-- Chosen residual link covers imply coverage of every graph edge with an
endpoint outside `U`. -/
theorem covers_outside_of_chosen_residualLink_covers
    {O V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {R M : TripleSystemOn V}
    (center : O → V) (hout : ∀ o, center o ∉ U)
    (hcomplete : ∀ v, v ∉ U → ∃ o, center o = v)
    (K : O → BipartiteLink V)
    (hK : ∀ o, IsResidualBipartition G R (center o) (K o))
    (hlinks : ∀ o, CoversBipartiteLink (K o) M) :
    ∀ u v : V, G.Adj u v → (u ∉ U ∨ v ∉ U) →
      (coveredGraph (R ∪ M)).Adj u v := by
  intro u v huv houtside
  by_cases hR : (coveredGraph R).Adj u v
  · obtain ⟨T, hTR, huT, hvT, huvT⟩ := coveredGraph_adj.mp hR
    exact coveredGraph_adj.mpr
      ⟨T, mem_union_left M hTR, huT, hvT, huvT⟩
  · have liftM : ∀ {x y}, (coveredGraph M).Adj x y →
        (coveredGraph (R ∪ M)).Adj x y := by
      intro x y hxy
      obtain ⟨T, hTM, hxT, hyT, hxyT⟩ := coveredGraph_adj.mp hxy
      exact coveredGraph_adj.mpr
        ⟨T, mem_union_right R hTM, hxT, hyT, hxyT⟩
    rcases houtside with hu | hv
    · obtain ⟨o, ho⟩ := hcomplete u hu
      have hvRes : v ∈ residualNeighbors G R u :=
        mem_residualNeighbors_iff.mpr ⟨huv, hR⟩
      subst u
      exact liftM ((hlinks o).covers_residualNeighbors_of_partition
        (hK o) v hvRes)
    · obtain ⟨o, ho⟩ := hcomplete v hv
      have huRes : u ∈ residualNeighbors G R v :=
        mem_residualNeighbors_iff.mpr ⟨huv.symm, fun h ↦ hR h.symm⟩
      subst v
      exact liftM (((hlinks o).covers_residualNeighbors_of_partition
        (hK o) u huRes).symm)

/-- Structural endpoint of the crossing-link phase with externally chosen
balanced residual bisections. -/
theorem exists_crossingLinkCover_of_chosen_partitions
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {F : ForbiddenFamilyOn V}
    {available P0 R0 : TripleSystemOn V}
    (K : {x : V // x ∉ U} → BipartiteLink V)
    (hK : ∀ o, IsResidualBipartition G R0 o.1 (K o))
    (hP0packing : IsPackingOn P0) (hP0avoid : AvoidsForbidden P0 F)
    (hstep : ∀ (P : TripleSystemOn V),
      P0 ⊆ P → P ⊆ P0 ∪ available →
      IsPackingOn P → AvoidsForbidden P F →
      ∀ o : {x : V // x ∉ U},
        HasLinkCoverExtension F available P (K o)) :
    ∃ M : TripleSystemOn V,
      M ⊆ available ∧ Disjoint P0 M ∧
      IsPackingOn (P0 ∪ M) ∧ AvoidsForbidden (P0 ∪ M) F ∧
      ∀ u v : V, G.Adj u v → (u ∉ U ∨ v ∉ U) →
        (coveredGraph (R0 ∪ M)).Adj u v := by
  obtain ⟨M, hMavailable, hP0Mdisjoint, hP0Mpacking, hP0Mavoid,
      hlinks⟩ :=
    exists_simultaneous_bipartiteLink_cover F available P0 K
      hP0packing hP0avoid hstep
  refine ⟨M, hMavailable, hP0Mdisjoint, hP0Mpacking, hP0Mavoid, ?_⟩
  exact covers_outside_of_chosen_residualLink_covers
    (fun o : {x : V // x ∉ U} ↦ o.1) (fun o ↦ o.2)
    (fun v hv ↦ ⟨⟨v, hv⟩, rfl⟩) K hK hlinks

end

end Erdos207
