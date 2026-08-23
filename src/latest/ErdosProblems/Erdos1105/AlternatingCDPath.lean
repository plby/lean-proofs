import ErdosProblems.Erdos1105.AlternatingPathJoin

namespace Erdos1105

open SimpleGraph

theorem AlternatingEnds.middle_segment_support {V : Type*} {G : SimpleGraph V} {x y : V}
    {p : G.Walk x y} {d a : ℕ} (hp : AlternatingEnds p d a)
    {i j : ℕ} (hij : i ≤ j) (hj : j < d + 2 - a) :
    ∀ z ∈ (pathSegment p (a + 2 * i) (a + 2 * j) (by omega)).support,
      ∃ s, a ≤ s ∧ s ≤ p.length - a ∧ p.getVert s = z := by
  have hlen := hp.length_eq
  have ha := hp.pos
  have had := hp.le_core
  intro z hz
  obtain ⟨s, hslo, hshi, hs⟩ := (mem_pathSegment_support p (a + 2 * i) (a + 2 * j)
    (by omega) (by omega)).mp hz
  exact ⟨s, by omega, by omega, hs⟩

theorem AlternatingEnds.middle_segment_avoid {V : Type*} {G : SimpleGraph V} {x y : V}
    {p : G.Walk x y} {d a : ℕ} (hp : AlternatingEnds p d a)
    {i j t : ℕ} (hij : i ≤ j) (hj : j < d + 2 - a) (ht : t ≤ p.length)
    (hsep : t < a + 2 * i ∨ a + 2 * j < t) :
    p.getVert t ∉ (pathSegment p (a + 2 * i) (a + 2 * j) (by omega)).support := by
  have hlen := hp.length_eq
  have ha := hp.pos
  have had := hp.le_core
  rw [getVert_mem_pathSegment p hp.isPath _ _ _ (by omega) t ht]
  omega

theorem AlternatingEnds.append_middle_vertex {V : Type*} {G : SimpleGraph V} {x y c : V}
    {p : G.Walk x y} {d a t : ℕ} (hp : AlternatingEnds p d a) (ht : t < d + 1 - a)
    (q : G.Walk c (p.getVert (a + 2 * (t + 1)))) (hq : q.IsPath)
    (hqlen : q.length = 2 * d) (hqsub : q.support ⊆ p.support)
    (hnot : p.getVert (a + 2 * t + 1) ∉ q.support) :
    ∃ r : G.Walk c (p.getVert (a + 2 * t + 1)),
      r.IsPath ∧ r.length = 2 * d + 1 ∧ r.support ⊆ p.support := by
  have hlen := hp.length_eq
  have ha := hp.pos
  have had := hp.le_core
  have he : G.Adj (p.getVert (a + 2 * (t + 1))) (p.getVert (a + 2 * t + 1)) := by
    have h := (p.adj_getVert_succ (i := a + 2 * t + 1) (by omega)).symm
    convert h using 1 <;> congr 1 <;> omega
  refine ⟨q.concat he, hq.concat hnot he, by rw [Walk.length_concat, hqlen], ?_⟩
  intro z hz
  simp only [Walk.support_concat, List.mem_append, List.mem_singleton] at hz
  rcases hz with hz | rfl
  · exact hqsub hz
  · exact p.getVert_mem_support _

/-- A near-spanning path from a noninitial attachment to a middle
vertex on its right. -/
theorem AlternatingEnds.path_C_D_internal {V : Type*} {G : SimpleGraph V} {x y : V}
    {p : G.Walk x y} {d a : ℕ} (hp : AlternatingEnds p d a)
    {i t : ℕ} (hi : 1 ≤ i) (hit : i ≤ t) (ht : t < d + 1 - a) :
    ∃ q : G.Walk (p.getVert (a + 2 * i)) (p.getVert (a + 2 * t + 1)),
      q.IsPath ∧ q.length = 2 * d + 1 ∧ q.support ⊆ p.support := by
  have hlen := hp.length_eq
  have ha := hp.pos
  have had := hp.le_core
  let q₁ := pathSegment p (a + 2 * i) (a + 2 * t) (by omega)
  let q₂ := pathSegment p (a + 2 * 0) (a + 2 * (i - 1)) (by omega)
  let q₃ := (pathSegment p (a + 2 * (t + 1)) (a + 2 * (d + 1 - a)) (by omega)).reverse
  have hsub₁ := hp.middle_segment_support hit (show t < d + 2 - a by omega)
  have hsub₂ := hp.middle_segment_support (show 0 ≤ i - 1 by omega) (show i - 1 < d + 2 - a by omega)
  have hsub₃ : ∀ z ∈ q₃.support, ∃ s, a ≤ s ∧ s ≤ p.length - a ∧ p.getVert s = z := by
    simpa only [q₃, Walk.support_reverse, List.mem_reverse] using
      hp.middle_segment_support (show t + 1 ≤ d + 1 - a by omega) (show d + 1 - a < d + 2 - a by omega)
  have h₁₂ : q₁.support.Disjoint q₂.support :=
    disjoint_pathSegments_of_separated p hp.isPath _ _ _ _ (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have h₁₃ : q₁.support.Disjoint q₃.support := by
    simpa only [q₁, q₃, Walk.support_reverse, List.disjoint_reverse_right] using
      disjoint_pathSegments_of_separated p hp.isPath (a + 2 * i) (a + 2 * t)
        (a + 2 * (t + 1)) (a + 2 * (d + 1 - a)) (by omega) (by omega)
        (by omega) (by omega) (by omega)
  have h₂₃ : q₂.support.Disjoint q₃.support := by
    simpa only [q₂, q₃, Walk.support_reverse, List.disjoint_reverse_right] using
      disjoint_pathSegments_of_separated p hp.isPath (a + 2 * 0) (a + 2 * (i - 1))
        (a + 2 * (t + 1)) (a + 2 * (d + 1 - a)) (by omega) (by omega)
        (by omega) (by omega) (by omega)
  obtain ⟨q, hq, hqlen, hqsub, hqmiddle⟩ := hp.join_three_middle q₁ q₂ q₃
    (by omega) (by omega) (by omega) (by omega)
    (pathSegment_isPath p hp.isPath _ _ _) (pathSegment_isPath p hp.isPath _ _ _)
    (pathSegment_isPath p hp.isPath _ _ _).reverse hsub₁ hsub₂ hsub₃ h₁₂ h₁₃ h₂₃
  have hlen₁ : q₁.length = (a + 2 * t) - (a + 2 * i) := pathSegment_length p _ _ _ (by omega)
  have hlen₂ : q₂.length = (a + 2 * (i - 1)) - (a + 2 * 0) := pathSegment_length p _ _ _ (by omega)
  have hlen₃ : q₃.length = (a + 2 * (d + 1 - a)) - (a + 2 * (t + 1)) := by
    rw [Walk.length_reverse, pathSegment_length p _ _ _ (by omega)]
  have hqlen' : q.length = 2 * d := by omega
  have hnot₁ : p.getVert (a + 2 * t + 1) ∉ q₁.support :=
    hp.middle_segment_avoid hit (by omega) (by omega) (by omega)
  have hnot₂ : p.getVert (a + 2 * t + 1) ∉ q₂.support :=
    hp.middle_segment_avoid (by omega) (by omega) (by omega) (by omega)
  have hnot₃ : p.getVert (a + 2 * t + 1) ∉ q₃.support := by
    simpa only [q₃, Walk.support_reverse, List.mem_reverse] using
      hp.middle_segment_avoid (show t + 1 ≤ d + 1 - a by omega) (by omega)
        (show a + 2 * t + 1 ≤ p.length by omega) (by omega)
  have hnot : p.getVert (a + 2 * t + 1) ∉ q.support := by
    rw [hqmiddle _ ⟨a + 2 * t + 1, by omega, by omega, rfl⟩]
    tauto
  have he : G.Adj (p.getVert (a + 2 * (t + 1))) (p.getVert (a + 2 * t + 1)) := by
    have h := (p.adj_getVert_succ (i := a + 2 * t + 1) (by omega)).symm
    convert h using 1 <;> congr 1 <;> omega
  refine ⟨q.concat he, hq.concat hnot he, by rw [Walk.length_concat, hqlen'], ?_⟩
  intro z hz
  simp only [Walk.support_concat, List.mem_append, List.mem_singleton] at hz
  rcases hz with hz | rfl
  · exact hqsub hz
  · exact p.getVert_mem_support _

end Erdos1105

#print axioms Erdos1105.AlternatingEnds.path_C_D_internal
