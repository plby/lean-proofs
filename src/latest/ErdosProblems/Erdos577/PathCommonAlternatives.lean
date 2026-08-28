import ErdosProblems.Erdos577.PathClassification

/-! The two common-neighbor alternatives used after exposing the path in patterns (18) and (20). -/

namespace Erdos577.PathBlock

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Classified.common_alternatives (p : FourPath G) (q : Quadrilateral G)
    (h : Classified p q) :
    CommonReplacement G (p.vertices 2) (p.vertices 3) (p.vertices 1) q.support ∨
      CommonReplacement G (p.vertices 1) (p.vertices 0) (p.vertices 2) q.support := by
  obtain ⟨_, reverse, q', hq', hcase⟩ := h
  rcases hcase with ⟨_, ha⟩ | ⟨_, hb⟩
  · have hr := ha 2 1 0 (by decide) (by decide) (by decide)
    rw [hq'] at hr
    cases reverse
    · exact Or.inr hr
    · exact Or.inl hr
  · obtain ⟨i, hi, _, hc⟩ := hb
    rcases hi with rfl | rfl
    · have hr := hc 2 3 (by decide) (by decide) (by decide)
      rw [hq'] at hr
      cases reverse
      · exact Or.inl hr
      · exact Or.inr hr
    · have hr := hc 1 0 (by decide) (by decide) (by decide)
      rw [hq'] at hr
      cases reverse
      · exact Or.inr hr
      · exact Or.inl hr

end Erdos577.PathBlock
