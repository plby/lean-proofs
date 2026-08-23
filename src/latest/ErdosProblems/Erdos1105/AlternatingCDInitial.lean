import ErdosProblems.Erdos1105.AlternatingCDPath

namespace Erdos1105

open SimpleGraph

set_option maxHeartbeats 800000 in
-- The interval cases and their disjointness arithmetic share a large elaboration context.
theorem AlternatingEnds.path_C_C_via_intervals {V : Type*} {G : SimpleGraph V} {x y : V}
    {p : G.Walk x y} {d a t : ℕ} (hp : AlternatingEnds p d a)
    (ht : t < d + 1 - a) (l₁ r₁ l₂ r₂ r₃ : ℕ)
    (h₁ : l₁ ≤ r₁) (h₂ : l₂ ≤ r₂) (h₃ : t + 1 ≤ r₃)
    (hr₁ : r₁ < d + 2 - a) (hr₂ : r₂ < d + 2 - a) (hr₃ : r₃ < d + 2 - a)
    (hs₁₂ : r₁ < l₂ ∨ r₂ < l₁) (hs₁₃ : r₁ < t + 1 ∨ r₃ < l₁)
    (hs₂₃ : r₂ < t + 1 ∨ r₃ < l₂)
    (hav₁ : r₁ ≤ t ∨ t < l₁) (hav₂ : r₂ ≤ t ∨ t < l₂)
    (hsum : (r₁ - l₁) + (r₂ - l₂) + (r₃ - (t + 1)) + a + 1 = d) :
    ∃ q : G.Walk (p.getVert (a + 2 * l₁)) (p.getVert (a + 2 * (t + 1))),
      q.IsPath ∧ q.length = 2 * d ∧ q.support ⊆ p.support ∧
        p.getVert (a + 2 * t + 1) ∉ q.support := by
  have hlen := hp.length_eq
  have ha := hp.pos
  have had := hp.le_core
  let q₁ := pathSegment p (a + 2 * l₁) (a + 2 * r₁) (by omega)
  let q₂ := pathSegment p (a + 2 * l₂) (a + 2 * r₂) (by omega)
  let q₃ := (pathSegment p (a + 2 * (t + 1)) (a + 2 * r₃) (by omega)).reverse
  have hsub₁ := hp.middle_segment_support h₁ hr₁
  have hsub₂ := hp.middle_segment_support h₂ hr₂
  have hsub₃ : ∀ z ∈ q₃.support, ∃ s, a ≤ s ∧ s ≤ p.length - a ∧ p.getVert s = z := by
    simpa only [q₃, Walk.support_reverse, List.mem_reverse] using hp.middle_segment_support h₃ hr₃
  have hd₁₂ : q₁.support.Disjoint q₂.support :=
    disjoint_pathSegments_of_separated p hp.isPath _ _ _ _ (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have hd₁₃ : q₁.support.Disjoint q₃.support := by
    simpa only [q₁, q₃, Walk.support_reverse, List.disjoint_reverse_right] using
      disjoint_pathSegments_of_separated p hp.isPath (a + 2 * l₁) (a + 2 * r₁)
        (a + 2 * (t + 1)) (a + 2 * r₃) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hd₂₃ : q₂.support.Disjoint q₃.support := by
    simpa only [q₂, q₃, Walk.support_reverse, List.disjoint_reverse_right] using
      disjoint_pathSegments_of_separated p hp.isPath (a + 2 * l₂) (a + 2 * r₂)
        (a + 2 * (t + 1)) (a + 2 * r₃) (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨q, hq, hqlen, hqsub, hqmiddle⟩ := hp.join_three_middle q₁ q₂ q₃
    hr₁ (by omega) hr₂ hr₃
    (pathSegment_isPath p hp.isPath _ _ _) (pathSegment_isPath p hp.isPath _ _ _)
    (pathSegment_isPath p hp.isPath _ _ _).reverse hsub₁ hsub₂ hsub₃ hd₁₂ hd₁₃ hd₂₃
  have hlen₁ : q₁.length = (a + 2 * r₁) - (a + 2 * l₁) := pathSegment_length p _ _ _ (by omega)
  have hlen₂ : q₂.length = (a + 2 * r₂) - (a + 2 * l₂) := pathSegment_length p _ _ _ (by omega)
  have hlen₃ : q₃.length = (a + 2 * r₃) - (a + 2 * (t + 1)) := by
    rw [Walk.length_reverse, pathSegment_length p _ _ _ (by omega)]
  have hqlen' : q.length = 2 * d := by omega
  have hnot₁ : p.getVert (a + 2 * t + 1) ∉ q₁.support :=
    hp.middle_segment_avoid h₁ hr₁ (by omega) (by omega)
  have hnot₂ : p.getVert (a + 2 * t + 1) ∉ q₂.support :=
    hp.middle_segment_avoid h₂ hr₂ (by omega) (by omega)
  have hnot₃ : p.getVert (a + 2 * t + 1) ∉ q₃.support := by
    simpa only [q₃, Walk.support_reverse, List.mem_reverse] using
      hp.middle_segment_avoid h₃ hr₃ (show a + 2 * t + 1 ≤ p.length by omega) (by omega)
  have hnot : p.getVert (a + 2 * t + 1) ∉ q.support := by
    rw [hqmiddle _ ⟨a + 2 * t + 1, by omega, by omega, rfl⟩]
    tauto
  exact ⟨q, hq, hqlen', hqsub, hnot⟩

theorem AlternatingEnds.path_C_D_via_intervals {V : Type*} {G : SimpleGraph V} {x y : V}
    {p : G.Walk x y} {d a t : ℕ} (hp : AlternatingEnds p d a)
    (ht : t < d + 1 - a) (l₁ r₁ l₂ r₂ r₃ : ℕ)
    (h₁ : l₁ ≤ r₁) (h₂ : l₂ ≤ r₂) (h₃ : t + 1 ≤ r₃)
    (hr₁ : r₁ < d + 2 - a) (hr₂ : r₂ < d + 2 - a) (hr₃ : r₃ < d + 2 - a)
    (hs₁₂ : r₁ < l₂ ∨ r₂ < l₁) (hs₁₃ : r₁ < t + 1 ∨ r₃ < l₁)
    (hs₂₃ : r₂ < t + 1 ∨ r₃ < l₂)
    (hav₁ : r₁ ≤ t ∨ t < l₁) (hav₂ : r₂ ≤ t ∨ t < l₂)
    (hsum : (r₁ - l₁) + (r₂ - l₂) + (r₃ - (t + 1)) + a + 1 = d) :
    ∃ q : G.Walk (p.getVert (a + 2 * l₁)) (p.getVert (a + 2 * t + 1)),
      q.IsPath ∧ q.length = 2 * d + 1 ∧ q.support ⊆ p.support := by
  obtain ⟨q, hq, hqlen, hsub, hnot⟩ := hp.path_C_C_via_intervals ht l₁ r₁ l₂ r₂ r₃
    h₁ h₂ h₃ hr₁ hr₂ hr₃ hs₁₂ hs₁₃ hs₂₃ hav₁ hav₂ hsum
  exact hp.append_middle_vertex ht q hq hqlen hsub hnot

theorem AlternatingEnds.path_C_D_initial {V : Type*} {G : SimpleGraph V} {x y : V}
    {p : G.Walk x y} {d a t : ℕ} (hp : AlternatingEnds p d a)
    (had : a < d) (ht : t < d + 1 - a) :
    ∃ q : G.Walk (p.getVert a) (p.getVert (a + 2 * t + 1)),
      q.IsPath ∧ q.length = 2 * d + 1 ∧ q.support ⊆ p.support := by
  have ha := hp.pos
  by_cases ht0 : t = 0
  · subst t
    exact hp.path_C_D_via_intervals ht 0 0 2 (d + 1 - a) 1
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · exact hp.path_C_D_via_intervals ht 0 0 1 t (d + 1 - a)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem AlternatingEnds.path_C_D {V : Type*} {G : SimpleGraph V} {x y : V}
    {p : G.Walk x y} {d a i t : ℕ} (hp : AlternatingEnds p d a)
    (had : a < d) (hi : i < d + 2 - a) (ht : t < d + 1 - a) :
    ∃ q : G.Walk (p.getVert (a + 2 * i)) (p.getVert (a + 2 * t + 1)),
      q.IsPath ∧ q.length = 2 * d + 1 ∧ q.support ⊆ p.support := by
  have hlen := hp.length_eq
  have ha := hp.pos
  have hone {v w : V} {r : G.Walk v w} (hr : AlternatingEnds r d a)
      {j s : ℕ} (hjs : j ≤ s) (hs : s < d + 1 - a) :
      ∃ q : G.Walk (r.getVert (a + 2 * j)) (r.getVert (a + 2 * s + 1)),
        q.IsPath ∧ q.length = 2 * d + 1 ∧ q.support ⊆ r.support := by
    by_cases hj0 : j = 0
    · subst j
      simpa only [Nat.mul_zero, Nat.add_zero] using hr.path_C_D_initial had hs
    · exact hr.path_C_D_internal (by omega) hjs hs
  by_cases hit : i ≤ t
  · exact hone hp hit ht
  · obtain ⟨q, hq, hqlen, hqsub⟩ := hone hp.reverse
      (show d + 1 - a - i ≤ d - a - t by omega) (show d - a - t < d + 1 - a by omega)
    have he₁ : p.reverse.getVert (a + 2 * (d + 1 - a - i)) = p.getVert (a + 2 * i) := by
      rw [Walk.getVert_reverse]
      congr 1
      omega
    have he₂ : p.reverse.getVert (a + 2 * (d - a - t) + 1) = p.getVert (a + 2 * t + 1) := by
      rw [Walk.getVert_reverse]
      congr 1
      omega
    refine ⟨q.copy he₁ he₂, by simpa only [Walk.isPath_copy] using hq,
      by simpa only [Walk.length_copy] using hqlen, ?_⟩
    simpa only [Walk.support_copy, Walk.support_reverse, List.subset_reverse] using hqsub

end Erdos1105

#print axioms Erdos1105.AlternatingEnds.path_C_D
