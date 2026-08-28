import Wikipedia.SmoothSixDPoincare.CornerStripData

/-!
# Boundary-arc injectivity and endpoint-only coincidences from the actual strips

These facts are recovered from the constructed strip maps. No additional
boundary-embedding or endpoint-coincidence assumption is needed downstream.
-/

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem CleanStripPatch.center_injOn {S T : Set M} {a : ℝ → M} {k₀ k₁ : (ℝ × ℝ) → M}
    (k : CleanStripPatch (E := E) S T a k₀ k₁) : InjOn a (Icc (0 : ℝ) 1) := by
  intro t ht s hs heq
  have h0 : (0 : ℝ) ∈ Icc (-k.width) k.width :=
    ⟨neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
  have htK : (t, 0) ∈ k.domain := k.contains_strip ⟨ht, h0⟩
  have hsK : (s, 0) ∈ k.domain := k.contains_strip ⟨hs, h0⟩
  have hmaps : k.map (t, 0) = k.map (s, 0) := by
    rw [k.center t ht, k.center s hs]
    exact heq
  exact congrArg Prod.fst (k.injective htK hsK hmaps)

theorem strip_center_coincidences_of_corner_overlap
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M}
    (k : CleanStripPatch (E := E) S T a k₀ k₁)
    (l : CleanStripPatch (E := E) T S b l₀ l₁)
    (hover : ∀ p ∈ k.domain, ∀ q ∈ l.domain, k.map p = l.map q →
      p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, a t = b s →
      (t = 0 ∧ s = 0) ∨ (t = 1 ∧ s = 1) := by
  intro t ht s hs heq
  have hk0 : (0 : ℝ) ∈ Icc (-k.width) k.width :=
    ⟨neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
  have hl0 : (0 : ℝ) ∈ Icc (-l.width) l.width :=
    ⟨neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩
  have hmaps : k.map (t, 0) = l.map (s, 0) := by rw [k.center t ht, l.center s hs]; exact heq
  rcases hover (t, 0) (k.contains_strip ⟨ht, hk0⟩) (s, 0)
      (l.contains_strip ⟨hs, hl0⟩) hmaps with hleft | hright
  · exact Or.inl ⟨congrArg Prod.fst hleft, (congrArg Prod.snd hleft).symm⟩
  · right
    have ht' : 1 - t = 0 := congrArg Prod.fst hright
    have hs' : 0 = 1 - s := congrArg Prod.snd hright
    constructor <;> linarith

end Wikipedia.SmoothSixDPoincare
