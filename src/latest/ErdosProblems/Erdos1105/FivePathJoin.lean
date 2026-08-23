import ErdosProblems.Erdos1105.PathSegments
import ErdosProblems.Erdos1105.PathCycleSplice

namespace Erdos1105

open SimpleGraph

/-- Concatenate five disjoint paths with four connecting edges. -/
theorem path_of_five_disjoint_paths {V : Type*} {G : SimpleGraph V}
    {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ : V}
    (p₁ : G.Walk a₁ b₁) (p₂ : G.Walk a₂ b₂) (p₃ : G.Walk a₃ b₃)
    (p₄ : G.Walk a₄ b₄) (p₅ : G.Walk a₅ b₅)
    (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath) (hp₃ : p₃.IsPath)
    (hp₄ : p₄.IsPath) (hp₅ : p₅.IsPath)
    (h₁₂ : p₁.support.Disjoint p₂.support) (h₁₃ : p₁.support.Disjoint p₃.support)
    (h₁₄ : p₁.support.Disjoint p₄.support) (h₁₅ : p₁.support.Disjoint p₅.support)
    (h₂₃ : p₂.support.Disjoint p₃.support) (h₂₄ : p₂.support.Disjoint p₄.support)
    (h₂₅ : p₂.support.Disjoint p₅.support) (h₃₄ : p₃.support.Disjoint p₄.support)
    (h₃₅ : p₃.support.Disjoint p₅.support) (h₄₅ : p₄.support.Disjoint p₅.support)
    (he₁ : G.Adj b₁ a₂) (he₂ : G.Adj b₂ a₃) (he₃ : G.Adj b₃ a₄) (he₄ : G.Adj b₄ a₅) :
    ∃ q : G.Walk a₁ b₅, q.IsPath ∧
      q.length = p₁.length + p₂.length + p₃.length + p₄.length + p₅.length + 4 ∧
      ∀ z, z ∈ q.support ↔ z ∈ p₁.support ∨ z ∈ p₂.support ∨ z ∈ p₃.support ∨
        z ∈ p₄.support ∨ z ∈ p₅.support := by
  let q := p₁.append (Walk.cons he₁ (p₂.append (Walk.cons he₂
    (p₃.append (Walk.cons he₃ (p₄.append (Walk.cons he₄ p₅)))))))
  have hsupp : q.support = p₁.support ++ p₂.support ++ p₃.support ++ p₄.support ++ p₅.support := by
    simp only [q, Walk.support_append, Walk.support_cons, List.tail_cons, List.append_assoc]
  refine ⟨q, Walk.IsPath.mk' ?_, ?_, ?_⟩
  · rw [hsupp]
    simp only [List.nodup_append', List.disjoint_append_left, hp₁.support_nodup,
      hp₂.support_nodup, hp₃.support_nodup, hp₄.support_nodup, hp₅.support_nodup,
      h₁₂, h₁₃, h₁₄, h₁₅, h₂₃, h₂₄, h₂₅, h₃₄, h₃₅, h₄₅, and_self]
  · simp only [q, Walk.length_append, Walk.length_cons]
    omega
  · intro z
    rw [hsupp]
    simp only [List.mem_append, or_assoc]

theorem disjoint_pathSegments_of_separated {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) (a b c d : ℕ)
    (hab : a ≤ b) (hcd : c ≤ d) (hb : b ≤ p.length) (hd : d ≤ p.length)
    (hsep : b < c ∨ d < a) :
    (pathSegment p a b hab).support.Disjoint (pathSegment p c d hcd).support := by
  rcases hsep with h | h
  · exact disjoint_pathSegments p hp a b c d hab h hcd hd
  · exact (disjoint_pathSegments p hp c d a b hcd h hab hb).symm

end Erdos1105

#print axioms Erdos1105.path_of_five_disjoint_paths
