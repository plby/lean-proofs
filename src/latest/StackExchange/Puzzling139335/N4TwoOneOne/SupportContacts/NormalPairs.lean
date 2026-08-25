import StackExchange.Puzzling139335.N4TwoOneOne.Defs
import StackExchange.Puzzling139335.N4TwoOneOne.SupportContacts.NormalPairs.UpperPair
import Mathlib.Tactic

/-!
# Pairs of admissible normals in the degree-(2,1,1,0) case

The predicate below records coordinate signs and the two closed angular
inequalities directly.  In particular it does not assume the desired
classification of orthogonal pairs.
-/

namespace Puzzling139335.N4TwoOneOne.SupportContacts

/-- Nonzero directions that can support two distinct source points. -/
def AllowedNormal (c s a b : ℝ) : Prop :=
  (a = 0 ∧ b < 0) ∨
  (b = 0 ∧ a ≠ 0) ∨
  (0 < a ∧ 0 < b ∧ b * c ≤ a * s) ∨
  (a < 0 ∧ 0 < b ∧ b * s ≤ (-a) * c)

theorem AllowedNormal.nonzero {c s a b : ℝ}
    (h : AllowedNormal c s a b) : a ≠ 0 ∨ b ≠ 0 := by
  rcases h with ⟨ha, hb⟩ | ⟨hb, ha⟩ | ⟨ha, hb, hcs⟩ | ⟨ha, hb, hcs⟩
  · exact Or.inr (ne_of_lt hb)
  · exact Or.inl ha
  · exact Or.inl (ne_of_gt ha)
  · exact Or.inl (ne_of_lt ha)

theorem AllowedNormal.y_neg_of_x_eq_zero {c s a b : ℝ}
    (h : AllowedNormal c s a b) (ha : a = 0) : b < 0 := by
  rcases h with ⟨_, hb⟩ | ⟨_, ha'⟩ | ⟨ha', _, _⟩ | ⟨ha', _, _⟩
  · exact hb
  · exact (ha' ha).elim
  · linarith
  · linarith

theorem AllowedNormal.upper_of_nonzero_coords {c s a b : ℝ}
    (h : AllowedNormal c s a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    (0 < a ∧ 0 < b ∧ b * c ≤ a * s) ∨
      (a < 0 ∧ 0 < b ∧ b * s ≤ (-a) * c) := by
  rcases h with ⟨ha', _⟩ | ⟨hb', _⟩ | h | h
  · exact (ha ha').elim
  · exact (hb hb').elim
  · exact Or.inl h
  · exact Or.inr h

/-- A direction and its opposite can both be admissible only horizontally.
No unit-length or trigonometric assumptions are needed for this fact. -/
theorem opposite_allowed_y_eq_zero {c s a b : ℝ}
    (h : AllowedNormal c s a b) (hneg : AllowedNormal c s (-a) (-b)) : b = 0 := by
  rcases h with ⟨ha, hb⟩ | ⟨hb, ha⟩ | ⟨ha, hb, hcs⟩ | ⟨ha, hb, hcs⟩
  · rcases hneg with ⟨ha', hb'⟩ | ⟨hb', ha'⟩ |
      ⟨ha', hb', hcs'⟩ | ⟨ha', hb', hcs'⟩ <;> linarith
  · exact hb
  · rcases hneg with ⟨ha', hb'⟩ | ⟨hb', ha'⟩ |
      ⟨ha', hb', hcs'⟩ | ⟨ha', hb', hcs'⟩ <;> linarith
  · rcases hneg with ⟨ha', hb'⟩ | ⟨hb', ha'⟩ |
      ⟨ha', hb', hcs'⟩ | ⟨ha', hb', hcs'⟩ <;> linarith

/-- Opposite admissible unit normals are precisely the two horizontal
unit directions, in either order. -/
theorem opposite_allowed_classification {c s a b : ℝ}
    (h : AllowedNormal c s a b) (hneg : AllowedNormal c s (-a) (-b))
    (hunit : a ^ 2 + b ^ 2 = 1) : b = 0 ∧ (a = 1 ∨ a = -1) := by
  have hb := opposite_allowed_y_eq_zero h hneg
  refine ⟨hb, sq_eq_one_iff.mp ?_⟩
  simpa [hb] using hunit

/-- The two possible orders of a bottom/horizontal pair of unit normals. -/
def BottomHorizontalPair (a b d e : ℝ) : Prop :=
  (a = 0 ∧ b = -1 ∧ e = 0 ∧ (d = 1 ∨ d = -1)) ∨
  (d = 0 ∧ e = -1 ∧ b = 0 ∧ (a = 1 ∨ a = -1))

/-- At the sign level an admissible orthogonal pair is either an axis
pair, or an upper-right/upper-left pair in one of its two orders. -/
theorem orthogonal_allowed_sign_classification {c s a b d e : ℝ}
    (ha : AllowedNormal c s a b) (hd : AllowedNormal c s d e)
    (hunit₁ : a ^ 2 + b ^ 2 = 1) (hunit₂ : d ^ 2 + e ^ 2 = 1)
    (horth : a * d + b * e = 0) :
    BottomHorizontalPair a b d e ∨
    (0 < a ∧ 0 < b ∧ b * c ≤ a * s ∧
      d < 0 ∧ 0 < e ∧ e * s ≤ (-d) * c) ∨
    (0 < d ∧ 0 < e ∧ e * c ≤ d * s ∧
      a < 0 ∧ 0 < b ∧ b * s ≤ (-a) * c) := by
  by_cases hb : b = 0
  · have ha0 : a ≠ 0 := by
      intro ha0
      simp [ha0, hb] at hunit₁
    have hd0 : d = 0 := by
      have hmul : a * d = 0 := by simpa [hb] using horth
      exact (mul_eq_zero.mp hmul).resolve_left ha0
    have he : e < 0 := hd.y_neg_of_x_eq_zero hd0
    have heunit : e ^ 2 = 1 := by simpa [hd0] using hunit₂
    have heone : e = -1 := (sq_eq_one_iff.mp heunit).resolve_left (by linarith)
    have haunit : a ^ 2 = 1 := by simpa [hb] using hunit₁
    exact Or.inl (Or.inr ⟨hd0, heone, hb, sq_eq_one_iff.mp haunit⟩)
  by_cases he : e = 0
  · have hd0 : d ≠ 0 := by
      intro hd0
      simp [hd0, he] at hunit₂
    have ha0 : a = 0 := by
      have hmul : a * d = 0 := by simpa [he] using horth
      exact (mul_eq_zero.mp hmul).resolve_right hd0
    have hbneg : b < 0 := ha.y_neg_of_x_eq_zero ha0
    have hbunit : b ^ 2 = 1 := by simpa [ha0] using hunit₁
    have hbone : b = -1 := (sq_eq_one_iff.mp hbunit).resolve_left (by linarith)
    have hdunit : d ^ 2 = 1 := by simpa [he] using hunit₂
    exact Or.inl (Or.inl ⟨ha0, hbone, he, sq_eq_one_iff.mp hdunit⟩)
  have ha0 : a ≠ 0 := by
    intro ha0
    have hmul : b * e = 0 := by simpa [ha0] using horth
    exact mul_ne_zero hb he hmul
  have hd0 : d ≠ 0 := by
    intro hd0
    have hmul : b * e = 0 := by simpa [hd0] using horth
    exact mul_ne_zero hb he hmul
  rcases ha.upper_of_nonzero_coords ha0 hb with ⟨ha, hb, hcs⟩ | ⟨ha, hb, hcs⟩
  · rcases hd.upper_of_nonzero_coords hd0 he with ⟨hd, he, hds⟩ | ⟨hd, he, hds⟩
    · have had : 0 < a * d := mul_pos ha hd
      have hbe : 0 < b * e := mul_pos hb he
      linarith
    · exact Or.inr (Or.inl ⟨ha, hb, hcs, hd, he, hds⟩)
  · rcases hd.upper_of_nonzero_coords hd0 he with ⟨hd, he, hds⟩ | ⟨hd, he, hds⟩
    · exact Or.inr (Or.inr ⟨hd, he, hds, ha, hb, hcs⟩)
    · have had : 0 < a * d := mul_pos_of_neg_of_neg ha hd
      have hbe : 0 < b * e := mul_pos hb he
      linarith

/-- Admissible orthogonal unit normals are either a bottom/horizontal
pair, or the two original upper supporting normals, in either order. -/
theorem orthogonal_allowed_classification {c s a b d e : ℝ}
    (hc : 0 < c) (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1)
    (ha : AllowedNormal c s a b) (hd : AllowedNormal c s d e)
    (hunit₁ : a ^ 2 + b ^ 2 = 1) (hunit₂ : d ^ 2 + e ^ 2 = 1)
    (horth : a * d + b * e = 0) :
    BottomHorizontalPair a b d e ∨
      (a = c ∧ b = s ∧ d = -s ∧ e = c) ∨
      (d = c ∧ e = s ∧ a = -s ∧ b = c) := by
  rcases orthogonal_allowed_sign_classification ha hd hunit₁ hunit₂ horth with
    haxis | ⟨ha, hb, hfirst, hd, he, hsecond⟩ | ⟨hd, he, hfirst, ha, hb, hsecond⟩
  · exact Or.inl haxis
  · exact Or.inr (Or.inl
      (upper_pair_eq hc hs hcs ha hb hd he hunit₁ hunit₂ horth hfirst hsecond))
  · have horth' : d * a + e * b = 0 := by nlinarith only [horth]
    exact Or.inr (Or.inr
      (upper_pair_eq hc hs hcs hd he ha hb hunit₂ hunit₁ horth' hfirst hsecond))

end Puzzling139335.N4TwoOneOne.SupportContacts
