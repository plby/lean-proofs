import ErdosProblems.Erdos767.Case1
import ErdosProblems.Erdos767.Case2Body
import ErdosProblems.Erdos767.Case2LongArc
import ErdosProblems.Erdos767.Case2Splice

open Finset Set
open scoped SimpleGraph

namespace Erdos767Scratch

open SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Case 2 of the relative degree theorem: if every terminal neighbor lies
on the lollipop tail, the aligned-fan splice contradicts a cycle shorter
than twice the terminal degree. -/
theorem BestLollipop.relative_low_degree_case2
    (hTwo : Erdos58.TwoConnected G) (B : BestLollipop G)
    (hpos : 0 < B.tail.length)
    (hN : G.neighborFinset B.terminal ⊆ B.tail.support.toFinset) :
    2 * G.degree B.terminal ≤ B.cycle.length := by
  by_contra hbound
  have hshort : B.cycle.length < 2 * G.degree B.terminal := by omega
  obtain ⟨j₁, hj₁J, hD⟩ :=
    E767DiracBuild.BestLollipop.exists_case2FanData hTwo B hpos
  obtain ⟨D⟩ := hD
  obtain ⟨S⟩ :=
    E767DiracBuild.Case2FanData.exists_tailData D hj₁J hN
  obtain ⟨Q, hQ, hQlong, hQcycle⟩ :=
    E767DiracBuild.Case2FanData.exists_longArc D hpos
  have hbody := E767DiracBuild.Case2FanData.spliceBody_isPath D hpos S
  have hdisj := E767DiracBuild.Case2FanData.longArc_disjoint_spliceBody
    D hpos S Q hQ hQcycle
  have hmiddle : G.degree B.terminal ≤
      S.A.length + 1 + S.returnPath.length := by
    simpa [E767DiracBuild.Case2TailData.returnPath, Walk.length_copy]
      using S.degree_le
  obtain ⟨C, hC, _hsize, hlong⟩ :=
    Erdos767DiracCase2.exists_longer_cycle_of_aligned_splice
      B.cycle Q D.E₁.path S.A S.chord S.returnPath D.E₂.path
      (G.degree B.terminal) B.cycle_isCycle hQ hbody hdisj
      hmiddle hQlong hshort
  exact (Nat.not_lt_of_ge (B.cycle_maximal C hC)) hlong

/-- Relative Dirac bound at the terminal of a positive best lollipop.  This
is the strengthened form used both for circumference and for exterior-edge
peeling arguments. -/
theorem BestLollipop.relative_low_degree
    (hTwo : Erdos58.TwoConnected G) (B : BestLollipop G)
    (hpos : 0 < B.tail.length) :
    2 * G.degree B.terminal ≤ B.cycle.length := by
  rcases B.degree_bound_or_all_neighbors_tail hpos with hcase₁ | hcase₂
  · exact hcase₁
  · exact B.relative_low_degree_case2 hTwo hpos hcase₂

/-- Dirac's circumference theorem in minimum-degree lower-bound form. -/
theorem exists_cycle_length_ge_min_card_two_mul
    (hTwo : Erdos58.TwoConnected G) (k : ℕ)
    (hdegree : ∀ v : V, k ≤ G.degree v) :
    ∃ (z : V) (C : G.Walk z z), C.IsCycle ∧
      min (Fintype.card V) (2 * k) ≤ C.length := by
  obtain ⟨B⟩ := BestLollipop.exists_bestLollipop hTwo
  by_cases hspan : B.cycle.support.toFinset = (Finset.univ : Finset V)
  · refine ⟨B.cycleBase, B.cycle, B.cycle_isCycle, ?_⟩
    have hcard := Erdos767LongestCycle.cycleCarrier_card B.cycle_isCycle
    rw [hspan, Finset.card_univ] at hcard
    rw [← hcard]
    exact min_le_left _ _
  · have hpos := B.tail_length_pos_of_cycle_not_spanning hTwo hspan
    have hrel := B.relative_low_degree hTwo hpos
    have hk : 2 * k ≤ B.cycle.length :=
      (Nat.mul_le_mul_left 2 (hdegree B.terminal)).trans hrel
    exact ⟨B.cycleBase, B.cycle, B.cycle_isCycle,
      (min_le_right _ _).trans hk⟩

end

end Erdos767Scratch
