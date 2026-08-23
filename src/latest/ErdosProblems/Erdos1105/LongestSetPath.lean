import ErdosProblems.Erdos1105.Basic

namespace Erdos1105

open SimpleGraph Finset

theorem exists_longest_path_between_sets {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A B : Set V)
    (hex : ∃ x ∈ A, ∃ y ∈ B, ∃ p : G.Walk x y, p.IsPath) :
    ∃ x ∈ A, ∃ y ∈ B, ∃ p : G.Walk x y, p.IsPath ∧
      ∀ a ∈ A, ∀ b ∈ B, ∀ q : G.Walk a b, q.IsPath → q.length ≤ p.length := by
  classical
  let P := (range (Fintype.card V)).filter fun n ↦
    ∃ x ∈ A, ∃ y ∈ B, ∃ p : G.Walk x y, p.IsPath ∧ p.length = n
  have hP : P.Nonempty := by
    obtain ⟨x, hx, y, hy, p, hp⟩ := hex
    exact ⟨p.length, mem_filter.mpr ⟨mem_range.mpr hp.length_lt, x, hx, y, hy, p, hp, rfl⟩⟩
  obtain ⟨m, hm, hmax⟩ := P.exists_max_image id hP
  obtain ⟨x, hx, y, hy, p, hp, hpm⟩ := (mem_filter.mp hm).2
  refine ⟨x, hx, y, hy, p, hp, ?_⟩
  intro a ha b hb q hq
  rw [hpm]
  exact hmax q.length (mem_filter.mpr ⟨mem_range.mpr hq.length_lt, a, ha, b, hb, q, hq, rfl⟩)

end Erdos1105
