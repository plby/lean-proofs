import StackExchange.Puzzling139335.DoubleCorner.RotationTriod
import StackExchange.Puzzling139335.DoubleCorner.Reflection
import StackExchange.Puzzling139335.DoubleCorner.HalfGerm

/-!
# The repeated-point double-corner theorem at the origin

The assumptions are a genuine congruence fixing the common corner, square
containment, disjoint interiors, and actual local coverage.  Exhaustive
plane-isometry classification supplies the rotation or reflection case.
-/

open Set Metric

namespace Puzzling139335.DoubleCorner

open PlaneIsometries AcuteCorner

private theorem reversing_involutive {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : ∀ p, e p = reversingCoordinates c s 0 p) : Function.Involutive e := by
  intro p
  rw [he (e p), he p]
  apply plane_ext
  · simp only [reversingCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
      PiLp.zero_apply, add_zero]
    linear_combination p 0 * hcs
  · simp only [reversingCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
      PiLp.zero_apply, add_zero]
    linear_combination p 1 * hcs

/-- Two congruent Jordan pieces covering a square-corner neighborhood,
with that corner fixed by their congruence, occupy opposite diagonal cones. -/
theorem diagonal_cones_of_local_congruence
    {P Q : Set Plane} (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPsub : P ⊆ unitSquare) (hQsub : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hzeroP : (0 : Plane) ∈ P) (hzeroQ : (0 : Plane) ∈ Q)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hePQ : e '' P = Q) (he0 : e 0 = 0)
    {ε : ℝ} (hε : 0 < ε) (hcover : ball 0 ε ∩ unitSquare ⊆ P ∪ Q) :
    (P ⊆ cone45 ∧ Q ⊆ upperCone45) ∨
      (P ⊆ upperCone45 ∧ Q ⊆ cone45) := by
  obtain ⟨c, s, hcs, hform | hform⟩ := affine_coordinate_classification e
  · have he : ∀ p, e p = directCoordinates c s 0 p := by
      intro p
      simpa only [he0] using hform p
    have hePsub : e '' P ⊆ unitSquare := by simpa only [hePQ] using hQsub
    have hdis' : Disjoint (interior P) (interior (e '' P)) := by
      simpa only [hePQ] using hdis
    have hc := normalized_rotation_cos_pos e he hPsub hePsub hP.interior_nonempty
    have hsne := normalized_rotation_sin_ne_zero e hcs he hPsub hePsub
      hP.interior_nonempty hdis'
    rcases lt_or_gt_of_ne hsne with hs | hs
    · have heinv : e.symm '' Q = P := by
        rw [← hePQ, image_image]
        simp
      have he' := normalized_rotation_symm_coordinates e hcs he
      have hcover' : ball 0 ε ∩ unitSquare ⊆ Q ∪ P := by
        simpa only [union_comm] using hcover
      have hle : c ≤ -s := positive_rotation_double_corner_cos_le_sin hQ hP
        hQsub hPsub hdis.symm hzeroQ e.symm heinv hc (neg_pos.mpr hs)
        he' hε hcover'
      obtain ⟨hupper, hlower⟩ := negative_rotation_square_cones e hc hle he hPsub hePsub
      exact Or.inr ⟨hupper, by simpa only [hePQ] using hlower⟩
    · have hle := positive_rotation_double_corner_cos_le_sin hP hQ hPsub hQsub
        hdis hzeroP e hePQ hc hs he hε hcover
      obtain ⟨hlower, hupper⟩ := positive_rotation_square_cones e hc hle he hPsub hePsub
      have hupper' : e '' P ⊆ upperCone45 := fun q hq => hupper q hq
      exact Or.inl ⟨hlower, by simpa only [hePQ] using hupper'⟩
  · have he : ∀ p, e p = reversingCoordinates c s 0 p := by
      intro p
      simpa only [he0] using hform p
    have heq := Reflection.eq_diagonal_of_involutive_local_cover hP hPsub hQsub
      hdis e he0 (reversing_involutive hcs e he) hePQ hε hcover
    have hdiag : ReflectionSeparation.diagonal '' P = Q := by
      simpa only [heq] using hePQ
    rcases ReflectionSeparation.diagonal_side hP hdiag hdis with habove | hbelow
    · apply Or.inr
      refine ⟨fun p hp => ⟨(hPsub hp).1.1, habove hp⟩, ?_⟩
      rintro q hq
      obtain ⟨p, hp, rfl⟩ := (Set.ext_iff.mp hdiag q).mpr hq
      change 0 ≤ p 0 ∧ p 0 ≤ p 1
      exact ⟨(hPsub hp).1.1, habove hp⟩
    · apply Or.inl
      refine ⟨fun p hp => ⟨(hPsub hp).2.1, hbelow hp⟩, ?_⟩
      rintro q hq
      obtain ⟨p, hp, rfl⟩ := (Set.ext_iff.mp hdiag q).mpr hq
      change 0 ≤ p 1 ∧ p 1 ≤ p 0
      exact ⟨(hPsub hp).2.1, hbelow hp⟩

/-- The supports from a repeated double corner are genuine local
half-quadrants of the pieces, with either choice of which copy is lower. -/
theorem halfCone_germs_of_local_congruence
    {P Q : Set Plane} (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPsub : P ⊆ unitSquare) (hQsub : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hzeroP : (0 : Plane) ∈ P) (hzeroQ : (0 : Plane) ∈ Q)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hePQ : e '' P = Q) (he0 : e 0 = 0)
    {ε : ℝ} (hε : 0 < ε) (hcover : ball 0 ε ∩ unitSquare ⊆ P ∪ Q) :
    (P ⊆ cone45 ∧ Q ⊆ upperCone45 ∧
      SameBoundaryGerm P cone45 0 ∧ SameBoundaryGerm Q upperCone45 0) ∨
    (P ⊆ upperCone45 ∧ Q ⊆ cone45 ∧
      SameBoundaryGerm P upperCone45 0 ∧ SameBoundaryGerm Q cone45 0) := by
  rcases diagonal_cones_of_local_congruence hP hQ hPsub hQsub hdis hzeroP hzeroQ
    e hePQ he0 hε hcover with ⟨hPlower, hQupper⟩ | ⟨hPupper, hQlower⟩
  · obtain ⟨hPgerm, hQgerm⟩ := halfCone_germs_of_local_cover hε hP.isClosed hQ.isClosed
      hPlower hQupper hcover
    exact Or.inl ⟨hPlower, hQupper, hPgerm, hQgerm⟩
  · have hcover' : ball 0 ε ∩ unitSquare ⊆ Q ∪ P := by
      simpa only [union_comm] using hcover
    obtain ⟨hQgerm, hPgerm⟩ := halfCone_germs_of_local_cover hε hQ.isClosed hP.isClosed
      hQlower hPupper hcover'
    exact Or.inr ⟨hPupper, hQlower, hPgerm, hQgerm⟩

/-- Global 45-degree supports exclude the square center from both
interiors. The conclusion is about the actual congruent pieces. -/
theorem support_and_center_exclusion_of_local_congruence
    {P Q : Set Plane} (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPsub : P ⊆ unitSquare) (hQsub : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hzeroP : (0 : Plane) ∈ P) (hzeroQ : (0 : Plane) ∈ Q)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hePQ : e '' P = Q) (he0 : e 0 = 0)
    {ε : ℝ} (hε : 0 < ε) (hcover : ball 0 ε ∩ unitSquare ⊆ P ∪ Q) :
    Supports45 P 0 ∧ Supports45 Q 0 ∧
      squareCenter ∉ interior P ∧ squareCenter ∉ interior Q := by
  have hcones := diagonal_cones_of_local_congruence hP hQ hPsub hQsub hdis hzeroP hzeroQ
    e hePQ he0 hε hcover
  have hPside : (∀ p ∈ P, p 0 ≤ p 1) ∨ (∀ p ∈ P, p 1 ≤ p 0) := by
    rcases hcones with h | h
    · exact Or.inr (fun p hp => (h.1 hp).2)
    · exact Or.inl (fun p hp => (h.1 hp).2)
  have hQside : (∀ p ∈ Q, p 0 ≤ p 1) ∨ (∀ p ∈ Q, p 1 ≤ p 0) := by
    rcases hcones with h | h
    · exact Or.inl (fun p hp => (h.2 hp).2)
    · exact Or.inr (fun p hp => (h.2 hp).2)
  have hcorner : corner 0 = (0 : Plane) := by
    ext i
    fin_cases i <;> norm_num [corner, Fin.ext_iff]
  refine ⟨?_, ?_, squareCenter_not_mem_interior_of_diagonal_support hPside,
    squareCenter_not_mem_interior_of_diagonal_support hQside⟩
  · simpa only [hcorner] using Reflection.supports45_of_diagonal_side hPsub hPside
  · simpa only [hcorner] using Reflection.supports45_of_diagonal_side hQsub hQside

end Puzzling139335.DoubleCorner
