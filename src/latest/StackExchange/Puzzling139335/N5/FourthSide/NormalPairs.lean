import StackExchange.Puzzling139335.N5.FaceNormals.Defs
import StackExchange.Puzzling139335.N4TwoOneOne.SupportContacts.NormalPairs

/-!
# Orthogonal pairs of allowed N5 face normals

The N5 normal families are contained in the previously classified N4 families. Their
extra sign restriction excludes the negative horizontal unit normal, so the only axis
pair is right/down. The upper pair is unchanged.
-/

namespace Puzzling139335.N5.FourthSide

/-- The N5 sign and support inequalities imply the broader N4 admissibility conditions. -/
theorem allowed_to_n4 {c s a b : ℝ} (h : AllowedNormal c s a b) :
    N4TwoOneOne.SupportContacts.AllowedNormal c s a b := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb, hbound⟩ | ⟨ha, hb, hbound, _hsum⟩
  · exact Or.inl ⟨ha, by linarith only [hb]⟩
  · by_cases hb0 : b = 0
    · exact Or.inr (Or.inl ⟨hb0, ne_of_gt ha⟩)
    · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      exact Or.inr (Or.inr (Or.inl ⟨ha, hbpos, by nlinarith only [hbound]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ha, hb, by nlinarith only [hbound]⟩))

/-- Every horizontal N5 allowed normal points to the right. -/
theorem allowed_x_pos_of_y_zero {c s a b : ℝ}
    (h : AllowedNormal c s a b) (hb0 : b = 0) : 0 < a := by
  rcases h with ⟨_ha, hb⟩ | ⟨ha, _hb, _hbound⟩ | ⟨_ha, hb, _hbound, _hsum⟩
  · linarith only [hb, hb0]
  · exact ha
  · linarith only [hb, hb0]

/-- Two orthogonal allowed unit normals form the right/down pair or the two original
upper supporting normals, with either ordering. Only positivity of `c,s` is needed. -/
theorem orthogonal_allowed_classification {c s a b d e : ℝ}
    (hc : 0 < c) (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1)
    (ha : AllowedNormal c s a b) (hd : AllowedNormal c s d e)
    (hunit₁ : a ^ 2 + b ^ 2 = 1) (hunit₂ : d ^ 2 + e ^ 2 = 1)
    (horth : a * d + b * e = 0) :
    (a = 1 ∧ b = 0 ∧ d = 0 ∧ e = -1) ∨
    (a = 0 ∧ b = -1 ∧ d = 1 ∧ e = 0) ∨
    (a = c ∧ b = s ∧ d = -s ∧ e = c) ∨
    (a = -s ∧ b = c ∧ d = c ∧ e = s) := by
  rcases N4TwoOneOne.SupportContacts.orthogonal_allowed_classification hc hs hcs
      (allowed_to_n4 ha) (allowed_to_n4 hd) hunit₁ hunit₂ horth with
    haxis | hupper | hreverse
  · rcases haxis with ⟨ha0, hbneg, he0, hdunit⟩ | ⟨hd0, heneg, hb0, haunit⟩
    · have hdpos := allowed_x_pos_of_y_zero hd he0
      have hdone : d = 1 := by
        rcases hdunit with hdone | hdneg
        · exact hdone
        · linarith only [hdpos, hdneg]
      exact Or.inr (Or.inl ⟨ha0, hbneg, hdone, he0⟩)
    · have hapos := allowed_x_pos_of_y_zero ha hb0
      have haone : a = 1 := by
        rcases haunit with haone | haneg
        · exact haone
        · linarith only [hapos, haneg]
      exact Or.inl ⟨haone, hb0, hd0, heneg⟩
  · exact Or.inr (Or.inr (Or.inl hupper))
  · rcases hreverse with ⟨hdc, hes, hanegs, hbc⟩
    exact Or.inr (Or.inr (Or.inr ⟨hanegs, hbc, hdc, hes⟩))

end Puzzling139335.N5.FourthSide
