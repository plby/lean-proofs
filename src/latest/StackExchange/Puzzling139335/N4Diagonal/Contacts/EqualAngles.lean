import StackExchange.Puzzling139335.N4Diagonal.Contacts.Frames
import StackExchange.Puzzling139335.N4Diagonal.Placements

/-!
# Equal-angle facing contacts

When the two supporting angles agree, their vertices are separated only
in the common perpendicular direction. A full unit separation would place
the second vertex at another square corner of the actual first piece,
contradicting its unique square corner.
-/

open Set

namespace Puzzling139335.N4Diagonal.Model

open ThreeCorners

/-- Equal-angle vertices have strictly less than unit separation in their
common facing direction, because the actual first placement has one corner. -/
theorem equal_angle_separation_lt_one (m : Model) (heq : m.β = m.θ) :
    inner ℝ (perpRay m.θ) (m.q - m.p) < 1 := by
  have hRay : inner ℝ (ray m.θ) (m.q - m.p) = 0 := by
    have hfirst := (m.first_support m.q m.q_mem).2
    have hlast := (m.last_support m.p m.p_mem).1
    rw [heq] at hlast
    simp only [inner_sub_right] at hfirst hlast ⊢
    linarith
  have hbound := (m.first_inward_bounds m.q_mem).1.2
  apply lt_of_le_of_ne hbound
  intro hunit
  have hcorner : ∃ j : Fin 4, m.e m.q = corner j := by
    rcases m.first_form with hform | hform
    · rcases m.firstCorner_one_or_three with hj | hj
      · refine ⟨2, ?_⟩
        rw [hform]
        ext i
        fin_cases i <;> norm_num [firstPlus, SquareSymmetry.cornerFlipPoint,
          corner, Fin.ext_iff, hj, hRay, hunit]
      · refine ⟨0, ?_⟩
        rw [hform]
        ext i
        fin_cases i <;> norm_num [firstPlus, SquareSymmetry.cornerFlipPoint,
          corner, Fin.ext_iff, hj, hRay, hunit]
    · rcases m.firstCorner_one_or_three with hj | hj
      · refine ⟨0, ?_⟩
        rw [hform]
        ext i
        fin_cases i <;> norm_num [firstMinus, firstPlus,
          SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff, hj, hRay, hunit]
      · refine ⟨2, ?_⟩
        rw [hform]
        ext i
        fin_cases i <;> norm_num [firstMinus, firstPlus,
          SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff, hj, hRay, hunit]
  obtain ⟨j, hj⟩ := hcorner
  have howner := m.first_only_corner j ⟨m.q, m.q_mem, hj⟩
  have hequal : m.e m.q = m.e m.p := by
    rw [hj, howner, m.first_corner]
  exact m.p_ne_q (m.e.injective hequal).symm

theorem equal_angles_first_contact_eq_empty (m : Model) (heq : m.β = m.θ) :
    N4Midline.levelOneContact m.P m.p (perpRay m.θ) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, hlevel⟩
  have hsep := m.equal_angle_separation_lt_one heq
  have hlast := (m.last_support x hx).2
  rw [heq] at hlast
  simp only [inner_sub_right] at hsep hlast hlevel
  linarith

theorem equal_angles_last_contact_eq_empty (m : Model) (heq : m.β = m.θ) :
    N4Midline.levelOneContact m.P m.q (-perpRay m.β) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, hlevel⟩
  have hsep := m.equal_angle_separation_lt_one heq
  have hfirst := (m.first_support x hx).1
  rw [heq, inner_neg_left] at hlevel
  simp only [inner_sub_right] at hsep hfirst hlevel
  linarith

end Puzzling139335.N4Diagonal.Model
