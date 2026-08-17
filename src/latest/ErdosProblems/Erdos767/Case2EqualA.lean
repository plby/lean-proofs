import ErdosProblems.Erdos767.Build
import ErdosProblems.Erdos767.Case1Geometry
import ErdosProblems.Erdos767.WalkIndex

open Finset
open scoped SimpleGraph

namespace E767Case2EqualA

open SimpleGraph
open Erdos767Scratch

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- One rooted ear which avoids the lollipop attachment replaces the deleted
root edge of the cycle by at least two edges and hence lengthens the cycle. -/
private theorem exists_longer_cycle_of_rooted_ear_avoiding_attachment
    (B : BestLollipop G) (hpos : 0 < B.tail.length)
    {b : V} (R : G.Walk B.rotatedCycle.snd b) (hR : R.IsPath)
    (hb : b ∈ B.tail.support)
    (hcycle : ∀ w, w ∈ R.support →
      w ∈ B.rotatedCycle.support.dropLast.toFinset →
      w = B.rotatedCycle.snd)
    (havoid : B.start ∉ R.support) :
    ∃ D : G.Walk B.rotatedCycle.snd B.rotatedCycle.snd,
      D.IsCycle ∧ B.cycle.length < D.length := by
  let C := B.rotatedCycle
  let A : Finset V := C.support.dropLast.toFinset
  let T : Finset V := B.tail.support.toFinset
  have hxA : C.snd ∈ A := by
    have hxC : C.snd ∈ C.support := List.tail_subset C.support
      (C.snd_mem_tail_support B.rotatedCycle_isCycle.not_nil)
    have hxF : C.snd ∈ C.support.toFinset := List.mem_toFinset.mpr hxC
    rw [E767WalkIndex.cycle_support_toFinset_eq_cycleVertexFinset
      B.rotatedCycle_isCycle] at hxF
    exact hxF
  have hbT : b ∈ T := List.mem_toFinset.mpr hb
  obtain ⟨K⟩ := E767DiracBuild.exists_blockEar hR A T hxA hbT
  have hKa : K.a = C.snd := by
    apply hcycle K.a
    · exact K.support_subset K.a K.path.start_mem_support
    · exact K.a_mem
  let E : G.Walk C.snd K.b := K.path.copy hKa rfl
  have hE : E.IsPath := by
    simpa [E, Walk.support_copy] using K.isPath
  have hEb : K.b ∈ B.tail.support := List.mem_toFinset.mp K.b_mem
  have hKb_ne_start : K.b ≠ B.start := by
    intro heq
    apply havoid
    have : K.b ∈ R.support :=
      K.support_subset K.b K.path.end_mem_support
    simpa [heq] using this
  have hx_ne_start : C.snd ≠ B.start := by
    have hadj : G.Adj B.start C.snd := C.adj_snd B.rotatedCycle_isCycle.not_nil
    exact hadj.ne.symm
  have hKb_ne_x : K.b ≠ C.snd := by
    intro heq
    have hKbC : K.b ∈ B.cycle.support := by
      apply B.mem_cycle_of_mem_rotatedCycle
      rw [heq]
      exact List.tail_subset C.support
        (C.snd_mem_tail_support B.rotatedCycle_isCycle.not_nil)
    have : K.b = B.start := B.cycle_tail_inter hKbC hEb
    exact hx_ne_start (heq.symm.trans this)
  let P : G.Walk B.start K.b := B.tail.takeUntil K.b hEb
  have hP : P.IsPath := B.tail_isPath.takeUntil hEb
  have hmeetCP : ∀ w : V, w ∈ C.tail.support →
      w ∈ P.support → w = B.start := by
    intro w hwC hwP
    apply B.cycle_tail_inter
    · apply B.mem_cycle_of_mem_rotatedCycle
      have hwC' : w ∈ C.support.tail := by
        rw [← C.support_tail_of_not_nil B.rotatedCycle_isCycle.not_nil]
        exact hwC
      exact List.tail_subset C.support hwC'
    · exact B.tail.support_takeUntil_subset_support hEb hwP
  let Q : G.Walk C.snd K.b := C.tail.append P
  have hQ : Q.IsPath :=
    E767AlignedAlt.isPath_append_of_meet_eq_end
      B.rotatedCycle_isCycle.isPath_tail hP hmeetCP
  have hdisj : Q.support.tail.Disjoint E.reverse.support.tail := by
    rw [List.disjoint_left]
    intro w hwQ hwE
    have hwQ' : w ∈ Q.support := List.mem_of_mem_tail hwQ
    have hwE' : w ∈ E.reverse.support := List.mem_of_mem_tail hwE
    have hwK : w ∈ K.path.support := by
      simpa [E, Walk.support_reverse, Walk.support_copy] using hwE'
    simp only [Q, Walk.mem_support_append_iff] at hwQ'
    rcases hwQ' with hwC | hwP
    · have hwCF : w ∈ A := by
        have hwC' : w ∈ C.support.tail := by
          rw [← C.support_tail_of_not_nil B.rotatedCycle_isCycle.not_nil]
          exact hwC
        have hwCs : w ∈ C.support := List.tail_subset C.support hwC'
        have hwCf : w ∈ C.support.toFinset := List.mem_toFinset.mpr hwCs
        rw [E767WalkIndex.cycle_support_toFinset_eq_cycleVertexFinset
          B.rotatedCycle_isCycle] at hwCf
        exact hwCf
      have hwx : w = C.snd := (K.meet_A w hwK hwCF).trans hKa
      have hxnot : C.snd ∉ Q.support.tail := by
        have hn := hQ.support_nodup
        rw [← Q.cons_tail_support, List.nodup_cons] at hn
        exact hn.1
      exact hxnot (hwx ▸ hwQ)
    · have hwTail : w ∈ T := by
        apply List.mem_toFinset.mpr
        exact B.tail.support_takeUntil_subset_support hEb hwP
      have hwb : w = K.b := K.meet_B w hwK hwTail
      have hbnot : K.b ∉ E.reverse.support.tail := by
        have hn := hE.reverse.support_nodup
        rw [← E.reverse.cons_tail_support, List.nodup_cons] at hn
        exact hn.1
      exact hbnot (hwb ▸ hwE)
  let D : G.Walk C.snd C.snd := Q.append E.reverse
  have hQtwo : 1 < Q.length := by
    have htail : C.tail.length = C.length - 1 := C.length_tail
    have hthree : 3 ≤ C.length := by
      simpa [C] using B.rotatedCycle_isCycle.three_le_length
    have hle : C.tail.length ≤ Q.length := by simp [Q]
    omega
  have hD : D.IsCycle :=
    hQ.isCycle_append hE.reverse hdisj (Or.inl hQtwo)
  have hPpos : 0 < P.length := by
    rw [← Walk.not_nil_iff_lt_length]
    exact Walk.not_nil_of_ne hKb_ne_start.symm
  have hEpos : 0 < E.length := by
    rw [← Walk.not_nil_iff_lt_length]
    exact Walk.not_nil_of_ne hKb_ne_x.symm
  have hDlen : D.length = C.tail.length + P.length + E.length := by
    simp [D, Q, Walk.length_append]
  have hCtail : C.tail.length = C.length - 1 := C.length_tail
  have hlong : C.length < D.length := by
    rw [hDlen, hCtail]
    omega
  refine ⟨D, hD, ?_⟩
  simpa [C] using hlong

/-- Exceptional equal-last-cycle-endpoint branch of the aligned-fan proof.

After the two extracted ears have been rewritten to start at the common
cycle root, internal disjointness makes at least one ear avoid the deleted
cycle-edge endpoint.  Re-extracting its first hit on the whole lollipop tail
then gives the strictly longer replacement cycle. -/
theorem exists_longer_cycle_of_two_rooted_ears
    (B : BestLollipop G) (hpos : 0 < B.tail.length)
    {b₁ b₂ : V}
    (R₁ : G.Walk B.rotatedCycle.snd b₁)
    (R₂ : G.Walk B.rotatedCycle.snd b₂)
    (hR₁ : R₁.IsPath) (hR₂ : R₂.IsPath)
    (hb₁ : b₁ ∈ B.tail.support) (hb₂ : b₂ ∈ B.tail.support)
    (hcycle₁ : ∀ w, w ∈ R₁.support →
      w ∈ B.rotatedCycle.support.dropLast.toFinset →
      w = B.rotatedCycle.snd)
    (hcycle₂ : ∀ w, w ∈ R₂.support →
      w ∈ B.rotatedCycle.support.dropLast.toFinset →
      w = B.rotatedCycle.snd)
    (hmeet : ∀ w, w ∈ R₁.support → w ∈ R₂.support →
      w = B.rotatedCycle.snd) :
    ∃ D : G.Walk B.rotatedCycle.snd B.rotatedCycle.snd,
      D.IsCycle ∧ B.cycle.length < D.length := by
  by_cases hs₁ : B.start ∈ R₁.support
  · have hs₂ : B.start ∉ R₂.support := by
      intro hs₂
      have heq := hmeet B.start hs₁ hs₂
      have hadj : G.Adj B.start B.rotatedCycle.snd :=
        B.rotatedCycle.adj_snd B.rotatedCycle_isCycle.not_nil
      exact hadj.ne heq
    exact exists_longer_cycle_of_rooted_ear_avoiding_attachment
      B hpos R₂ hR₂ hb₂ hcycle₂ hs₂
  · exact exists_longer_cycle_of_rooted_ear_avoiding_attachment
      B hpos R₁ hR₁ hb₁ hcycle₁ hs₁

/-- Direct wrapper for the exceptional branch as it arises from the two
`BlockEar`s extracted from an aligned fan.  Equality of their last cycle
vertices and branch disjointness force that common vertex to be the fan
root, after which `exists_longer_cycle_of_two_rooted_ears` applies. -/
theorem exists_longer_cycle_of_equal_blockEars
    (B : BestLollipop G) (hpos : 0 < B.tail.length)
    {z₁ z₂ : V}
    (R₁ : G.Walk B.rotatedCycle.snd z₁)
    (R₂ : G.Walk B.rotatedCycle.snd z₂)
    (hR₁ : R₁.IsPath) (hR₂ : R₂.IsPath)
    (hmeet : ∀ w, w ∈ R₁.support → w ∈ R₂.support →
      w = B.rotatedCycle.snd)
    (Y : Finset V) (hYtail : Y ⊆ B.tail.support.toFinset)
    (E₁ : E767DiracBuild.BlockEar R₁
      B.rotatedCycle.support.dropLast.toFinset Y)
    (E₂ : E767DiracBuild.BlockEar R₂
      B.rotatedCycle.support.dropLast.toFinset Y)
    (haeq : E₁.a = E₂.a) :
    ∃ D : G.Walk B.rotatedCycle.snd B.rotatedCycle.snd,
      D.IsCycle ∧ B.cycle.length < D.length := by
  have ha₁root : E₁.a = B.rotatedCycle.snd := by
    apply hmeet E₁.a
    · exact E₁.support_subset E₁.a E₁.path.start_mem_support
    · rw [haeq]
      exact E₂.support_subset E₂.a E₂.path.start_mem_support
  have ha₂root : E₂.a = B.rotatedCycle.snd := haeq.symm.trans ha₁root
  let S₁ : G.Walk B.rotatedCycle.snd E₁.b := E₁.path.copy ha₁root rfl
  let S₂ : G.Walk B.rotatedCycle.snd E₂.b := E₂.path.copy ha₂root rfl
  have hS₁ : S₁.IsPath := by
    simpa [S₁, Walk.support_copy] using E₁.isPath
  have hS₂ : S₂.IsPath := by
    simpa [S₂, Walk.support_copy] using E₂.isPath
  have hb₁ : E₁.b ∈ B.tail.support :=
    List.mem_toFinset.mp (hYtail E₁.b_mem)
  have hb₂ : E₂.b ∈ B.tail.support :=
    List.mem_toFinset.mp (hYtail E₂.b_mem)
  have hcycle₁ : ∀ w, w ∈ S₁.support →
      w ∈ B.rotatedCycle.support.dropLast.toFinset →
      w = B.rotatedCycle.snd := by
    intro w hwS hwC
    have hwE : w ∈ E₁.path.support := by simpa [S₁] using hwS
    exact (E₁.meet_A w hwE hwC).trans ha₁root
  have hcycle₂ : ∀ w, w ∈ S₂.support →
      w ∈ B.rotatedCycle.support.dropLast.toFinset →
      w = B.rotatedCycle.snd := by
    intro w hwS hwC
    have hwE : w ∈ E₂.path.support := by simpa [S₂] using hwS
    exact (E₂.meet_A w hwE hwC).trans ha₂root
  have hmeetS : ∀ w, w ∈ S₁.support → w ∈ S₂.support →
      w = B.rotatedCycle.snd := by
    intro w hw₁ hw₂
    have hwE₁ : w ∈ E₁.path.support := by simpa [S₁] using hw₁
    have hwE₂ : w ∈ E₂.path.support := by simpa [S₂] using hw₂
    exact hmeet w
      (E₁.support_subset w hwE₁) (E₂.support_subset w hwE₂)
  exact exists_longer_cycle_of_two_rooted_ears B hpos
    S₁ S₂ hS₁ hS₂ hb₁ hb₂ hcycle₁ hcycle₂ hmeetS

end

end E767Case2EqualA

