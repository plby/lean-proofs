import StackExchange.Puzzling139335.N4HalfLeg.Defs

/-!
# Two intervals covering the middle of a square side

If two closed intervals cover another interval, their total length is at
least the covered length.  The proof uses only endpoint membership and
the impossibility of an uncovered midpoint between disjoint intervals.

For actual right-side contacts, this bounds the total source support-face
length using the contact extrema supplied by `RightSpan`.
-/

open Set

namespace Puzzling139335.N4HalfLeg

/-- A cover by two nonempty closed intervals bounds the covered length
by the sum of their lengths.  The covered interval may be empty. -/
theorem length_le_add_lengths_of_Icc_subset_union {a b l₁ r₁ l₂ r₂ : ℝ}
    (h₁ : l₁ ≤ r₁) (h₂ : l₂ ≤ r₂)
    (hcover : Icc a b ⊆ Icc l₁ r₁ ∪ Icc l₂ r₂) :
    b - a ≤ (r₁ - l₁) + (r₂ - l₂) := by
  by_cases hab : a ≤ b
  · have ha := hcover (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
    have hb := hcover (show b ∈ Icc a b from ⟨hab, le_rfl⟩)
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · linarith [ha.1, hb.2]
    · have hoverlap : l₂ ≤ r₁ := by
        by_contra hnot
        have hgap : r₁ < l₂ := lt_of_not_ge hnot
        have hmid : (r₁ + l₂) / 2 ∈ Icc a b :=
          ⟨by linarith [ha.2], by linarith [hb.1]⟩
        rcases hcover hmid with hleft | hright
        · linarith [hleft.2]
        · linarith [hright.1]
      linarith [ha.1, hb.2]
    · have hoverlap : l₁ ≤ r₂ := by
        by_contra hnot
        have hgap : r₂ < l₁ := lt_of_not_ge hnot
        have hmid : (r₂ + l₁) / 2 ∈ Icc a b :=
          ⟨by linarith [ha.2], by linarith [hb.1]⟩
        rcases hcover hmid with hleft | hright
        · linarith [hleft.1]
        · linarith [hright.2]
      linarith [ha.1, hb.2]
    · linarith [ha.1, hb.2]
  · have hba : b < a := lt_of_not_ge hab
    linarith

/-- Two actual right-side contact spans covering the middle side segment
have source support-face lengths totaling at least that segment's length. -/
theorem RightSpan.middle_length_le_add_lengths {P Q R : Set Plane}
    {e f : Plane ≃ᵃⁱ[ℝ] Plane} (rQ : RightSpan P Q e) (rR : RightSpan P R f)
    {b : ℝ}
    (hcover : ∀ y ∈ Icc b (1 - b),
      Schoenflies.Plane.mk 1 y ∈ Q ∨ Schoenflies.Plane.mk 1 y ∈ R) :
    1 - 2 * b ≤ rQ.face.length + rR.face.length := by
  have hinterval : Icc b (1 - b) ⊆
      Icc rQ.bottom rQ.top ∪ Icc rR.bottom rR.top := by
    intro y hy
    rcases hcover y hy with hQ | hR
    · exact Or.inl (rQ.bounds y hQ)
    · exact Or.inr (rR.bounds y hR)
  have hlength := length_le_add_lengths_of_Icc_subset_union
    rQ.bottom_lt_top.le rR.bottom_lt_top.le hinterval
  rw [rQ.length_eq, rR.length_eq]
  linarith

end Puzzling139335.N4HalfLeg
