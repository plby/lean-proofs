import ErdosProblems.Erdos215.GlobalOneCross

/-!
# Concrete global assembly for Erdős Problem 215

This module connects the terminal candidate construction and one-cross
theorem to the generic well-founded outer recursion.  The only remaining
component parameter is the rich selector theorem.
-/

namespace Erdos215

open Set

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Global
namespace CodedDavies

variable (D : DaviesDecomposition Code.skolem)

local instance : IsWellOrder D.Index D.lt := D.isWellOrder

/-- A fixed residue requirement used only to seed the Cantor schedule once
an active frame has been exhibited. -/
def defaultRequirement {A : TerminalLayer} (n : ℕ) (hn : n ∈ A.active) :
    ScheduledRequirement A where
  index := n
  active := hn
  residue := {
    d := 1
    hd := by norm_num
    i := 0
    j := 0
    a := 0
    b := 0 }

/-- The exact concrete stage extension consumed by the well-founded outer
recursion. -/
theorem stageExtension (selector : RichSelectorTheorem) :
    OuterRecursion.StageExtension D.lt (terminalLayer D)
      (fun i x ↦ Code.point x ∈ D.layer i) := by
  intro i prev hprefix
  let A := terminalLayer D i
  let old := stageOld D prev
  by_cases hactive : A.active.Nonempty
  · obtain ⟨n, hn⟩ := hactive
    let default : ScheduledRequirement A := defaultRequirement n hn
    let hOld : IsPartialSteinhaus old := stageOld_partial D hprefix
    let hbefore : ∀ x ∈ old, Code.point x ∈ D.before i :=
      stageOld_before D hprefix
    let hclass : ∀ m ∈ A.active,
        Code.latticeClass (OrientedFrame.classOf (A.frame m)) ∈ D.layer i :=
      fun m hm ↦ active_frame_class_mem_layer D hm
    let hclassInj : Set.InjOn
        (fun m ↦ OrientedFrame.classOf (A.frame m)) A.active :=
      terminalLayer_class_injOn D i
    have hone : A.OneCross old
        (candidateSource D default
          (outerForbiddenLines D threeCircleFiniteness hOld hbefore hclass)
          hclass hclassInj) := by
      simpa only [A, old, stageSource] using
        stageOneCross D threeCircleFiniteness hprefix default
    let cert := terminalStage D selector threeCircleFiniteness hOld hbefore
      hclass hclassInj default hone
    let block : Set Point := cert.selected \ old
    refine ⟨block, ?_⟩
    refine {
      block_partial := ?_
      earlier_separated := ?_
      hits_up_to := ?_
      first_added_located := ?_
      old_new_explained := ?_ }
    · intro x hx y hy hxy z
      exact cert.isPartial hx.1 hy.1 hxy z
    · intro j hji x hx y hy hxy z hdist
      exact cert.isPartial (cert.old_subset ⟨j, hji, hx⟩) hy.1 hxy z hdist
    · intro m hm K hK
      obtain ⟨p, hp, hpK⟩ := cert.hits m hm K hK
      refine ⟨p, ?_, hpK⟩
      by_cases hpold : p ∈ old
      · exact Or.inl hpold
      · exact Or.inr ⟨hp, hpold⟩
    · intro x hx
      exact cert.located_new x hx.1 hx.2
    · intro j hji x hx y hy hdist
      exact cert.explains_old_new x ⟨j, hji, hx⟩ y hy.1 hy.2 hdist
  · refine ⟨∅, ?_⟩
    refine {
      block_partial := by simp [IsPartialSteinhaus]
      earlier_separated := by simp
      hits_up_to := ?_
      first_added_located := by simp
      old_new_explained := by simp }
    intro n hn
    exact (hactive ⟨n, hn⟩).elim

/-- The concrete outer recursion produces a verified global family of birth
blocks. -/
theorem exists_globalBlockFamily (selector : RichSelectorTheorem) :
    Nonempty (BlockFamily D.Index D.lt (terminalLayer D)) :=
  OuterRecursion.exists_blockFamily D.lt (terminalLayer D)
    (fun i x ↦ Code.point x ∈ D.layer i)
    (stageExtension D selector)

/-- Global partial-Steinhaus set meeting every rational-equivalence class of
oriented integer lattices. -/
theorem global_rational_classes (selector : RichSelectorTheorem) :
    ∃ S : Set Point, IsPartialSteinhaus S ∧
      ∀ L : OrientedFrame, HitsRationalClass S L := by
  let D := decomposition
  obtain ⟨B⟩ := exists_globalBlockFamily D selector
  let : IsWellOrder D.Index D.lt := D.isWellOrder
  refine ⟨B.result, ?_, ?_⟩
  · apply B.result_partial
    intro i j
    rcases trichotomous_of D.lt i j with hij | hij | hij
    · exact Or.inr (Or.inl hij)
    · exact Or.inl hij
    · exact Or.inr (Or.inr hij)
  · intro L K hKL
    exact blockFamily_hitsAllFrames D B K

end CodedDavies
end Global

end

end Erdos215
