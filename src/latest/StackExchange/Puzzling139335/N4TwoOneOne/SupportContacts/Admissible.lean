import StackExchange.Puzzling139335.N4TwoOneOne.SupportContacts.Core
import StackExchange.Puzzling139335.N4TwoOneOne.SupportContacts.NormalPairs

/-!
# The actual source has only the permitted nontrivial support directions
-/

open Set

namespace Puzzling139335.N4TwoOneOne.SupportContacts

noncomputable section

/-- Two distinct actual support points exclude the interiors of all three
source-corner normal cones. The conclusion is an explicit coefficient test. -/
theorem hasTwoSupportPoints_allowed {P : Set Plane} {θ u v a b : ℝ}
    (h : SourceSupport P θ u v) (hc : 0 < Real.cos θ) (hs : 0 < Real.sin θ)
    (hne : a ≠ 0 ∨ b ≠ 0) (hface : HasTwoSupportPoints P a b) :
    AllowedNormal (Real.cos θ) (Real.sin θ) a b := by
  rcases lt_trichotomy b 0 with hb | rfl | hb
  · left
    refine ⟨?_, hb⟩
    by_contra ha
    exact not_hasTwoSupportPoints_downward h ha hb hface
  · right; left
    exact ⟨rfl, hne.resolve_right (by simp)⟩
  · rcases lt_trichotomy a 0 with ha | rfl | ha
    · right; right; right
      refine ⟨ha, hb, ?_⟩
      by_contra hbound
      have hα : 0 < a * Real.cos θ + b * Real.sin θ := by
        linarith only [lt_of_not_ge hbound]
      have hβ : 0 < -a * Real.sin θ + b * Real.cos θ :=
        add_pos (mul_pos (neg_pos.mpr ha) hs) (mul_pos hb hc)
      exact not_hasTwoSupportPoints_strict_upper h hα hβ hface
    · have hα : 0 < (0 : ℝ) * Real.cos θ + b * Real.sin θ := by
        simpa only [zero_mul, zero_add] using mul_pos hb hs
      have hβ : 0 < -(0 : ℝ) * Real.sin θ + b * Real.cos θ := by
        simpa only [neg_zero, zero_mul, zero_add] using mul_pos hb hc
      exact (not_hasTwoSupportPoints_strict_upper h hα hβ hface).elim
    · right; right; left
      refine ⟨ha, hb, ?_⟩
      by_contra hbound
      have hα : 0 < a * Real.cos θ + b * Real.sin θ :=
        add_pos (mul_pos ha hc) (mul_pos hb hs)
      have hβ : 0 < -a * Real.sin θ + b * Real.cos θ := by
        linarith only [lt_of_not_ge hbound]
      exact not_hasTwoSupportPoints_strict_upper h hα hβ hface

/-- Opposite nontrivial support directions of the source must be horizontal. -/
theorem opposite_hasTwoSupportPoints_y_eq_zero {P : Set Plane} {θ u v a b : ℝ}
    (h : SourceSupport P θ u v) (hc : 0 < Real.cos θ) (hs : 0 < Real.sin θ)
    (hne : a ≠ 0 ∨ b ≠ 0) (hface : HasTwoSupportPoints P a b)
    (hopp : HasTwoSupportPoints P (-a) (-b)) : b = 0 := by
  apply opposite_allowed_y_eq_zero
    (hasTwoSupportPoints_allowed h hc hs hne hface)
  apply hasTwoSupportPoints_allowed h hc hs _ hopp
  simpa only [neg_ne_zero] using hne

theorem supportsAt_left_at_base_left {P : Set Plane} {θ u v : ℝ}
    (h : SourceSupport P θ u v) : SupportsAt P (-1) 0 (corner 0) := by
  refine ⟨h.base_left, ?_⟩
  intro p hp
  have hpx := (h.subset_square hp).1.1
  simpa [corner] using neg_nonpos.mpr hpx

theorem supportsAt_right_at_base_right {P : Set Plane} {θ u v : ℝ}
    (h : SourceSupport P θ u v) : SupportsAt P 1 0 (corner 1) := by
  refine ⟨h.base_right, ?_⟩
  intro p hp
  simpa [corner] using (h.subset_square hp).1.2

theorem supportsAt_bottom_at_base_left {P : Set Plane} {θ u v : ℝ}
    (h : SourceSupport P θ u v) : SupportsAt P 0 (-1) (corner 0) := by
  refine ⟨h.base_left, ?_⟩
  intro p hp
  simpa [corner] using neg_nonpos.mpr (h.subset_square hp).2.1

theorem supportsAt_bottom_at_base_right {P : Set Plane} {θ u v : ℝ}
    (h : SourceSupport P θ u v) : SupportsAt P 0 (-1) (corner 1) := by
  refine ⟨h.base_right, ?_⟩
  intro p hp
  simpa [corner] using neg_nonpos.mpr (h.subset_square hp).2.1

theorem supportsAt_e_at_upper_corner {P : Set Plane} {θ u v : ℝ}
    (h : SourceSupport P θ u v) :
    SupportsAt P (Real.cos θ) (Real.sin θ) (sourceCorner θ u v) := by
  refine ⟨h.upper_corner, ?_⟩
  intro p hp
  change eCoord θ p ≤ eCoord θ (sourceCorner θ u v)
  rw [eCoord_sourceCorner]
  exact h.e_le p hp

theorem supportsAt_f_at_upper_corner {P : Set Plane} {θ u v : ℝ}
    (h : SourceSupport P θ u v) :
    SupportsAt P (-Real.sin θ) (Real.cos θ) (sourceCorner θ u v) := by
  refine ⟨h.upper_corner, ?_⟩
  intro p hp
  change fCoord θ p ≤ fCoord θ (sourceCorner θ u v)
  rw [fCoord_sourceCorner]
  exact h.f_le p hp

/-- The source corner common to a perpendicular pair is one of the three
named actual corners. -/
theorem common_support_of_bottom_horizontal {P : Set Plane} {θ u v a b d e : ℝ}
    (h : SourceSupport P θ u v) (hp : BottomHorizontalPair a b d e) :
    ∃ p : Plane, (p = corner 0 ∨ p = corner 1 ∨ p = sourceCorner θ u v) ∧
      SupportsAt P a b p ∧ SupportsAt P d e p := by
  rcases hp with ⟨rfl, rfl, rfl, hd⟩ | ⟨rfl, rfl, rfl, ha⟩
  · rcases hd with rfl | rfl
    · exact ⟨corner 1, Or.inr (Or.inl rfl),
        supportsAt_bottom_at_base_right h, supportsAt_right_at_base_right h⟩
    · exact ⟨corner 0, Or.inl rfl,
        supportsAt_bottom_at_base_left h, supportsAt_left_at_base_left h⟩
  · rcases ha with rfl | rfl
    · exact ⟨corner 1, Or.inr (Or.inl rfl),
        supportsAt_right_at_base_right h, supportsAt_bottom_at_base_right h⟩
    · exact ⟨corner 0, Or.inl rfl,
        supportsAt_left_at_base_left h, supportsAt_bottom_at_base_left h⟩

/-- Perpendicular nontrivial supporting lines have one of the three actual
source corners as a common support point. -/
theorem common_support_of_perpendicular_faces {P : Set Plane} {θ u v a b d e : ℝ}
    (h : SourceSupport P θ u v) (hc : 0 < Real.cos θ) (hs : 0 < Real.sin θ)
    (hunit₁ : a ^ 2 + b ^ 2 = 1) (hunit₂ : d ^ 2 + e ^ 2 = 1)
    (horth : a * d + b * e = 0)
    (hfirst : HasTwoSupportPoints P a b) (hsecond : HasTwoSupportPoints P d e) :
    ∃ p : Plane, (p = corner 0 ∨ p = corner 1 ∨ p = sourceCorner θ u v) ∧
      SupportsAt P a b p ∧ SupportsAt P d e p := by
  have hne₁ : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hn
    push Not at hn
    rw [hn.1, hn.2] at hunit₁
    norm_num at hunit₁
  have hne₂ : d ≠ 0 ∨ e ≠ 0 := by
    by_contra hn
    push Not at hn
    rw [hn.1, hn.2] at hunit₂
    norm_num at hunit₂
  have hf := hasTwoSupportPoints_allowed h hc hs hne₁ hfirst
  have hg := hasTwoSupportPoints_allowed h hc hs hne₂ hsecond
  rcases orthogonal_allowed_classification hc hs (cos_sq_add_sin_sq θ)
      hf hg hunit₁ hunit₂ horth with haxis | hupper | hupper
  · exact common_support_of_bottom_horizontal h haxis
  · rcases hupper with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨sourceCorner θ u v, Or.inr (Or.inr rfl),
      supportsAt_e_at_upper_corner h, supportsAt_f_at_upper_corner h⟩
  · rcases hupper with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨sourceCorner θ u v, Or.inr (Or.inr rfl),
      supportsAt_f_at_upper_corner h, supportsAt_e_at_upper_corner h⟩

end

end Puzzling139335.N4TwoOneOne.SupportContacts
