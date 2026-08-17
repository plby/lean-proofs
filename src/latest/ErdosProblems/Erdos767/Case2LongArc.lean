import ErdosProblems.Erdos767.Case2Assembly
import ErdosProblems.Erdos58.CycleArcs

open Finset
open scoped SimpleGraph

namespace E767DiracBuild

open SimpleGraph
open Erdos767Scratch

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The longer complementary arc of the rooted longest cycle, oriented from
the second aligned ear to the first.  Its length is at least half the old
cycle length and all its vertices lie in the non-repeated cycle carrier. -/
theorem Case2FanData.exists_longArc
    {B : BestLollipop G} {j₁ : ℕ}
    (D : Case2FanData B j₁) (hpos : 0 < B.tail.length) :
    ∃ Q : G.Walk D.E₂.a D.E₁.a,
      Q.IsPath ∧
      B.cycle.length ≤ 2 * Q.length ∧
      (∀ v, v ∈ Q.support →
        v ∈ B.rotatedCycle.support.dropLast.toFinset) := by
  have ha₂ : D.E₂.a ∈ B.rotatedCycle.support :=
    List.mem_of_mem_dropLast (List.mem_toFinset.mp D.E₂.a_mem)
  have ha₁ : D.E₁.a ∈ B.rotatedCycle.support :=
    List.mem_of_mem_dropLast (List.mem_toFinset.mp D.E₁.a_mem)
  have hne : D.E₂.a ≠ D.E₁.a := (D.a_ne hpos).symm
  obtain ⟨P, Q, hP, hQ, hPpos, hQpos, hlen, hmeet, hcover,
      hPedge, hQedge⟩ :=
    Erdos58.exists_path_arcs_of_cycle B.rotatedCycle_isCycle
      ha₂ ha₁ hne
  have hcarrierP : ∀ v, v ∈ P.support →
      v ∈ B.rotatedCycle.support.dropLast.toFinset := by
    intro v hv
    have hvC : v ∈ B.rotatedCycle.support := (hcover v).mpr (Or.inl hv)
    have hvF : v ∈ B.rotatedCycle.support.toFinset :=
      List.mem_toFinset.mpr hvC
    rw [E767WalkIndex.cycle_support_toFinset_eq_cycleVertexFinset
      B.rotatedCycle_isCycle] at hvF
    exact hvF
  have hcarrierQ : ∀ v, v ∈ Q.support →
      v ∈ B.rotatedCycle.support.dropLast.toFinset := by
    intro v hv
    have hvC : v ∈ B.rotatedCycle.support := (hcover v).mpr (Or.inr hv)
    have hvF : v ∈ B.rotatedCycle.support.toFinset :=
      List.mem_toFinset.mpr hvC
    rw [E767WalkIndex.cycle_support_toFinset_eq_cycleVertexFinset
      B.rotatedCycle_isCycle] at hvF
    exact hvF
  have hlen' : P.length + Q.length = B.cycle.length := by
    simpa using hlen
  rcases le_total P.length Q.length with hPQ | hQP
  · refine ⟨Q, hQ, ?_, hcarrierQ⟩
    omega
  · refine ⟨P, hP, ?_, hcarrierP⟩
    omega

end

end E767DiracBuild

