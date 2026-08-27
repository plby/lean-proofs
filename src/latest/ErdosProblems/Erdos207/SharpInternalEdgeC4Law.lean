/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpInhomogeneousJointInclusion
import ErdosProblems.Erdos207.InternalEdgeRandomGreedy

/-!
# Sharp C4 for the scheduled internal-edge process

The scheduled process has cumulative point hazard at most `D⁻¹` for every
triangle.  The sharp inhomogeneous joint-inclusion lemma therefore gives a
pure `D⁻|Q|` bound, with neither a schedule-length nor a factorial factor.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Sharp B4 for prescribed triangles disjoint from the initial family. -/
theorem internalEdgeGreedyProcess_probability_subset_chosen_le_sharp
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (hnodup : edges.Nodup)
    (hu : ∀ e, e ∈ edges -> e.out.1 ∉ U)
    (hv : ∀ e, e ∈ edges -> e.out.2 ∉ U)
    (hSU : ∀ e, e ∈ edges -> S e ⊆ U)
    (D : Nat) (hD : 0 < D) (P0 Q : TripleSystemOn V)
    (hdisjoint : Disjoint Q P0) :
    (internalEdgeGreedyProcessLaw F G U omega S edges hne D P0).probability
        (fun z => Q ⊆ z.chosen) <=
      (D : NNReal)⁻¹ ^ Q.card := by
  let z0 : InternalEdgeGreedyStateOn V :=
    { chosen := P0, failed := false }
  have hjoint := evolveKernels_probability_subset_le_pointWeights_sharp
    (internalEdgeGreedyKernel F G U omega S edges hne D)
    (fun z : InternalEdgeGreedyStateOn V => z.chosen)
    (internalEdgePointHazard U edges hne D)
    (internalEdgeGreedyKernel_monotone_singleInsertion
      F G U omega S edges hne D)
    (internalEdgeGreedyKernel_probability_new_triangle_le
      F G U omega S edges hne hSU D hD)
    z0 Q hdisjoint edges.length
  have hweight :
      setWeight
          (cumulativePointHazard
            (internalEdgePointHazard U edges hne D) edges.length) Q <=
        setWeight (fun _ : TripleOn V => (D : NNReal)⁻¹) Q := by
    unfold setWeight
    apply prod_le_prod
    · intro T hTQ
      exact bot_le
    · intro T hTQ
      exact cumulative_internalEdgePointHazard_le hnodup hu hv D T
  calc
    (internalEdgeGreedyProcessLaw F G U omega S edges hne D P0).probability
        (fun z => Q ⊆ z.chosen) <=
      setWeight
        (cumulativePointHazard
          (internalEdgePointHazard U edges hne D) edges.length) Q := by
        simpa only [internalEdgeGreedyProcessLaw, z0] using hjoint
    _ <= setWeight (fun _ : TripleOn V => (D : NNReal)⁻¹) Q := hweight
    _ = (D : NNReal)⁻¹ ^ Q.card := by simp [setWeight]

/-- Sharp C4 for the genuinely new triangles; no disjointness premise is
needed because the event is impossible when `Q` meets `P0`. -/
theorem internalEdgeGreedyProcess_probability_subset_newChosen_le_sharp
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (hnodup : edges.Nodup)
    (hu : ∀ e, e ∈ edges -> e.out.1 ∉ U)
    (hv : ∀ e, e ∈ edges -> e.out.2 ∉ U)
    (hSU : ∀ e, e ∈ edges -> S e ⊆ U)
    (D : Nat) (hD : 0 < D) (P0 Q : TripleSystemOn V) :
    (internalEdgeGreedyProcessLaw F G U omega S edges hne D P0).probability
        (fun z => Q ⊆ z.chosen \ P0) <=
      (D : NNReal)⁻¹ ^ Q.card := by
  let L := internalEdgeGreedyProcessLaw F G U omega S edges hne D P0
  by_cases hdisjoint : Disjoint Q P0
  · calc
      L.probability (fun z => Q ⊆ z.chosen \ P0) <=
          L.probability (fun z => Q ⊆ z.chosen) := by
        apply L.probability_mono
        intro z hz T hT
        exact (mem_sdiff.mp (hz hT)).1
      _ <= (D : NNReal)⁻¹ ^ Q.card :=
        internalEdgeGreedyProcess_probability_subset_chosen_le_sharp
          F G U omega S edges hne hnodup hu hv hSU D hD P0 Q hdisjoint
  · have himpossible : ∀ z : InternalEdgeGreedyStateOn V,
        ¬ Q ⊆ z.chosen \ P0 := by
      intro z hsub
      apply hdisjoint
      rw [disjoint_left]
      intro T hTQ hTP0
      exact (mem_sdiff.mp (hsub hTQ)).2 hTP0
    calc
      L.probability (fun z => Q ⊆ z.chosen \ P0) <=
          L.probability (fun _ => False) := by
        apply L.probability_mono
        intro z hz
        exact himpossible z hz
      _ = 0 := L.probability_false
      _ <= (D : NNReal)⁻¹ ^ Q.card := zero_le

end

end Erdos207
