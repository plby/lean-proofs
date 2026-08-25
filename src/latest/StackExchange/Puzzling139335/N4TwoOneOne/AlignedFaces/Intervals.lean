import StackExchange.Puzzling139335.N4TwoOneOne.AlignedOutgoing.Rectangles

/-!
# Translating an outer top interval onto the middle interval

The left endpoints and right endpoints of the actual translated intervals
force the two inequalities `3 * T ≤ 1` and `1 ≤ 3 * T`.
-/

open Set

namespace Puzzling139335.N4TwoOneOne

private theorem top_mem_horizontalShift_image_iff (P : Set Plane) (a x : ℝ) :
    (!₂[x, 1] : Plane) ∈ AlignedOutgoing.horizontalShift a '' P ↔
      (!₂[x - a, 1] : Plane) ∈ P := by
  constructor
  · rintro ⟨p, hp, hpx⟩
    have hx : p 0 = x - a := by
      have hx' := congrArg (fun q : Plane => q 0) hpx
      change p 0 + a = x at hx'
      linarith only [hx']
    have hy : p 1 = 1 := congrArg (fun q : Plane => q 1) hpx
    have hpEq : p = !₂[x - a, 1] := by
      ext i
      fin_cases i
      · exact hx
      · exact hy
    exact hpEq ▸ hp
  · intro hp
    refine ⟨!₂[x - a, 1], hp, ?_⟩
    ext i
    fin_cases i
    · change x - a + a = x
      ring
    · rfl

theorem right_shift_interval_third {P Q : Set Plane} {T : ℝ}
    (hT : T ∈ Ioo (0 : ℝ) (1 / 2))
    (hP : ∀ x ∈ Icc (0 : ℝ) 1, (!₂[x, 1] : Plane) ∈ P ↔ 1 - T ≤ x)
    (hQ : ∀ x ∈ Icc (0 : ℝ) 1,
      (!₂[x, 1] : Plane) ∈ Q ↔ T ≤ x ∧ x ≤ 1 - T)
    (hshift : AlignedOutgoing.horizontalShift (-T) '' P = Q) : T = 1 / 3 := by
  have hPleft : (!₂[1 - T, 1] : Plane) ∈ P :=
    (hP (1 - T) ⟨by linarith [hT.2], by linarith [hT.1]⟩).mpr le_rfl
  have hQleftImage : (!₂[(1 - T) + -T, 1] : Plane) ∈ Q := by
    rw [← hshift]
    exact mem_image_of_mem (AlignedOutgoing.horizontalShift (-T)) hPleft
  have hUpper : T ≤ (1 - T) + -T :=
    ((hQ ((1 - T) + -T)
      ⟨by linarith [hT.2], by linarith [hT.1]⟩).mp hQleftImage).1
  have hQleft : (!₂[T, 1] : Plane) ∈ Q :=
    (hQ T ⟨hT.1.le, by linarith [hT.2]⟩).mpr
      ⟨le_rfl, by linarith [hT.2]⟩
  have hPback : (!₂[T - -T, 1] : Plane) ∈ P :=
    (top_mem_horizontalShift_image_iff P (-T) T).mp (hshift.symm ▸ hQleft)
  have hLower : 1 - T ≤ T - -T :=
    (hP (T - -T) ⟨by linarith [hT.1], by linarith [hT.2]⟩).mp hPback
  linarith only [hUpper, hLower]

theorem left_shift_interval_third {P Q : Set Plane} {T : ℝ}
    (hT : T ∈ Ioo (0 : ℝ) (1 / 2))
    (hP : ∀ x ∈ Icc (0 : ℝ) 1, (!₂[x, 1] : Plane) ∈ P ↔ x ≤ T)
    (hQ : ∀ x ∈ Icc (0 : ℝ) 1,
      (!₂[x, 1] : Plane) ∈ Q ↔ T ≤ x ∧ x ≤ 1 - T)
    (hshift : AlignedOutgoing.horizontalShift T '' P = Q) : T = 1 / 3 := by
  have hPright : (!₂[T, 1] : Plane) ∈ P :=
    (hP T ⟨hT.1.le, by linarith [hT.2]⟩).mpr le_rfl
  have hQrightImage : (!₂[T + T, 1] : Plane) ∈ Q := by
    rw [← hshift]
    exact mem_image_of_mem (AlignedOutgoing.horizontalShift T) hPright
  have hUpper : T + T ≤ 1 - T :=
    ((hQ (T + T) ⟨by linarith [hT.1], by linarith [hT.2]⟩).mp hQrightImage).2
  have hQright : (!₂[1 - T, 1] : Plane) ∈ Q :=
    (hQ (1 - T) ⟨by linarith [hT.2], by linarith [hT.1]⟩).mpr
      ⟨by linarith [hT.2], le_rfl⟩
  have hPback : (!₂[(1 - T) - T, 1] : Plane) ∈ P :=
    (top_mem_horizontalShift_image_iff P T (1 - T)).mp (hshift.symm ▸ hQright)
  have hLower : (1 - T) - T ≤ T :=
    (hP ((1 - T) - T)
      ⟨by linarith [hT.2], by linarith [hT.1]⟩).mp hPback
  linarith only [hUpper, hLower]

end Puzzling139335.N4TwoOneOne
