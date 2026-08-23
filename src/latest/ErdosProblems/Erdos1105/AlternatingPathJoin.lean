import ErdosProblems.Erdos1105.AlternatingEnds

namespace Erdos1105

open SimpleGraph

/-- Join three disjoint pieces of the alternating middle, using the two
end blocks as connectors. The support remains inside the original path. -/
theorem AlternatingEnds.join_three_middle {V : Type*} {G : SimpleGraph V} {x y : V}
    {p : G.Walk x y} {d a : ℕ} (hp : AlternatingEnds p d a)
    {c e : V} {j₁ j₂ j₃ j₄ : ℕ}
    (q₁ : G.Walk c (p.getVert (a + 2 * j₁)))
    (q₂ : G.Walk (p.getVert (a + 2 * j₂)) (p.getVert (a + 2 * j₃)))
    (q₃ : G.Walk (p.getVert (a + 2 * j₄)) e)
    (hj₁ : j₁ < d + 2 - a) (hj₂ : j₂ < d + 2 - a)
    (hj₃ : j₃ < d + 2 - a) (hj₄ : j₄ < d + 2 - a)
    (hq₁ : q₁.IsPath) (hq₂ : q₂.IsPath) (hq₃ : q₃.IsPath)
    (hsub₁ : ∀ z ∈ q₁.support, ∃ i, a ≤ i ∧ i ≤ p.length - a ∧ p.getVert i = z)
    (hsub₂ : ∀ z ∈ q₂.support, ∃ i, a ≤ i ∧ i ≤ p.length - a ∧ p.getVert i = z)
    (hsub₃ : ∀ z ∈ q₃.support, ∃ i, a ≤ i ∧ i ≤ p.length - a ∧ p.getVert i = z)
    (h₁₂ : q₁.support.Disjoint q₂.support) (h₁₃ : q₁.support.Disjoint q₃.support)
    (h₂₃ : q₂.support.Disjoint q₃.support) :
    ∃ q : G.Walk c e, q.IsPath ∧ q.length = q₁.length + q₂.length + q₃.length + 2 * a + 2 ∧
      q.support ⊆ p.support ∧
      ∀ z, (∃ i, a ≤ i ∧ i ≤ p.length - a ∧ p.getVert i = z) →
        (z ∈ q.support ↔ z ∈ q₁.support ∨ z ∈ q₂.support ∨ z ∈ q₃.support) := by
  have hlen := hp.length_eq
  have ha := hp.pos
  have had := hp.le_core
  let A := pathSegment p 0 (a - 1) (by omega)
  let B := pathSegment p (p.length - (a - 1)) p.length (by omega)
  have hdisjA {v w : V} (r : G.Walk v w)
      (hsub : ∀ z ∈ r.support, ∃ i, a ≤ i ∧ i ≤ p.length - a ∧ p.getVert i = z) :
      A.support.Disjoint r.support := by
    intro z hzA hzr
    obtain ⟨i, hi0, hia, hi⟩ := (mem_pathSegment_support p 0 (a - 1) (by omega) (by omega)).mp hzA
    obtain ⟨j, haj, hjL, hj⟩ := hsub z hzr
    have := hp.isPath.getVert_injOn (show i ≤ p.length by omega) (show j ≤ p.length by omega)
      (hi.trans hj.symm)
    omega
  have hdisjB {v w : V} (r : G.Walk v w)
      (hsub : ∀ z ∈ r.support, ∃ i, a ≤ i ∧ i ≤ p.length - a ∧ p.getVert i = z) :
      B.support.Disjoint r.support := by
    intro z hzB hzr
    obtain ⟨i, hi0, hiL, hi⟩ := (mem_pathSegment_support p (p.length - (a - 1)) p.length
      (by omega) le_rfl).mp hzB
    obtain ⟨j, haj, hjL, hj⟩ := hsub z hzr
    have := hp.isPath.getVert_injOn hiL (show j ≤ p.length by omega) (hi.trans hj.symm)
    omega
  have hAB : A.support.Disjoint B.support :=
    disjoint_pathSegments p hp.isPath _ _ _ _ (by omega) (by omega) (by omega) le_rfl
  have he₁ : G.Adj (p.getVert (a + 2 * j₁)) (p.getVert 0) :=
    (hp.left_join 0 (by omega) j₁ hj₁).symm
  have he₂ : G.Adj (p.getVert (a - 1)) (p.getVert (a + 2 * j₂)) :=
    hp.left_join _ (by omega) j₂ hj₂
  have he₃ : G.Adj (p.getVert (a + 2 * j₃)) (p.getVert (p.length - (a - 1))) :=
    (hp.right_join _ (by omega) j₃ hj₃).symm
  have he₄ : G.Adj (p.getVert p.length) (p.getVert (a + 2 * j₄)) := by
    simpa only [Nat.sub_zero] using hp.right_join 0 (by omega) j₄ hj₄
  obtain ⟨q, hq, hqlen, hsupp⟩ := path_of_five_disjoint_paths q₁ A q₂ B q₃
    hq₁ (pathSegment_isPath p hp.isPath _ _ _) hq₂ (pathSegment_isPath p hp.isPath _ _ _) hq₃
    (hdisjA q₁ hsub₁).symm h₁₂ (hdisjB q₁ hsub₁).symm h₁₃
    (hdisjA q₂ hsub₂) hAB (hdisjA q₃ hsub₃) (hdisjB q₂ hsub₂).symm h₂₃
    (hdisjB q₃ hsub₃) he₁ he₂ he₃ he₄
  have hAlen : A.length = a - 1 := by
    simpa only [Nat.sub_zero] using pathSegment_length p 0 (a - 1) (by omega) (by omega)
  have hBlen : B.length = a - 1 := by
    rw [pathSegment_length p _ _ _ le_rfl]
    omega
  refine ⟨q, hq, by omega, ?_, ?_⟩
  · intro z hz
    rcases (hsupp z).mp hz with h | h | h | h | h
    · obtain ⟨i, _, _, hi⟩ := hsub₁ z h
      exact hi ▸ p.getVert_mem_support i
    · exact pathSegment_support_subset p _ _ _ (by omega) h
    · obtain ⟨i, _, _, hi⟩ := hsub₂ z h
      exact hi ▸ p.getVert_mem_support i
    · exact pathSegment_support_subset p _ _ _ le_rfl h
    · obtain ⟨i, _, _, hi⟩ := hsub₃ z h
      exact hi ▸ p.getVert_mem_support i
  · intro z hz
    have hzA : z ∉ A.support := by
      intro hzA
      exact hdisjA (Walk.nil : G.Walk z z) (by simpa using hz) hzA (by simp)
    have hzB : z ∉ B.support := by
      intro hzB
      exact hdisjB (Walk.nil : G.Walk z z) (by simpa using hz) hzB (by simp)
    simpa only [hzA, hzB, false_or] using hsupp z

end Erdos1105

#print axioms Erdos1105.AlternatingEnds.join_three_middle
