import Wikipedia.SmoothSixDPoincare.ComplementCoefficientDeterminant
import Wikipedia.SmoothSixDPoincare.PlanarFrameCoordinates

/-!
# Factor the actual two-sheet tangent sum into disk and normal determinant blocks

Use one explicit, fixed coordinate rearrangement for both corners: the two
arc parameters first, followed by the two transverse sheet models. If the
arc columns lie in the disk plane, the resulting actual tangent-sum operator
has zero lower-left block. Its determinant is the disk-tangent determinant
times the determinant of the two normal-image frames.
-/

noncomputable section

open Function

namespace Wikipedia.SmoothSixDPoincare.IntersectionCoordinates

open PlaneImmersion (Plane linearMap)

variable {A B F : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Fixed rearrangement of the actual two-sheet tangent sum into disk-then-normal coordinates. -/
def jointBlock (j : (A × B) ≃L[ℝ] F)
    (P : (ℝ × A) →L[ℝ] (Plane × F)) (Q : (ℝ × B) →L[ℝ] (Plane × F)) :
    (Plane × (A × B)) →L[ℝ] (Plane × (A × B)) :=
  (ContinuousLinearEquiv.prodCongr
    (ContinuousLinearEquiv.refl ℝ Plane) j.symm).toContinuousLinearMap.comp
      ((P.coprod Q).comp
        (ContinuousLinearEquiv.prodProdProdComm ℝ ℝ A ℝ B).symm.toContinuousLinearMap)

theorem jointBlock_apply (j : (A × B) ≃L[ℝ] F)
    (P : (ℝ × A) →L[ℝ] (Plane × F)) (Q : (ℝ × B) →L[ℝ] (Plane × F))
    (p : Plane × (A × B)) :
    jointBlock j P Q p =
      ((P (p.1.1, p.2.1) + Q (p.1.2, p.2.2)).1,
        j.symm ((P (p.1.1, p.2.1) + Q (p.1.2, p.2.2)).2)) := rfl

theorem map_first_axis (P : (ℝ × A) →L[ℝ] (Plane × F)) (s : ℝ) :
    P (s, 0) = s • P (1, 0) := by
  have hs : (s, (0 : A)) = s • ((1 : ℝ), 0) := by ext <;> simp
  rw [hs, map_smul]

variable [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]

/-- The full determinant separates into the actual arc columns and normal-frame blocks. -/
theorem det_jointBlock (j : (A × B) ≃L[ℝ] F)
    (P : (ℝ × A) →L[ℝ] (Plane × F)) (Q : (ℝ × B) →L[ℝ] (Plane × F))
    {u v : Plane} (hP : P (1, 0) = (u, 0)) (hQ : Q (1, 0) = (v, 0)) :
    (jointBlock j P Q).toLinearMap.det = (linearMap (u, v)).toLinearMap.det *
      (j.symm.toContinuousLinearMap.comp
        (((ContinuousLinearMap.snd ℝ Plane F).comp (P.comp (ContinuousLinearMap.inr ℝ ℝ A))).coprod
          ((ContinuousLinearMap.snd ℝ Plane F).comp
            (Q.comp (ContinuousLinearMap.inr ℝ ℝ B))))).toLinearMap.det := by
  have hzero : ∀ w : Plane, (jointBlock j P Q (w, 0)).2 = 0 := by
    intro w
    rw [jointBlock_apply]
    change j.symm ((P (w.1, 0) + Q (w.2, 0)).2) = 0
    rw [map_first_axis P w.1, map_first_axis Q w.2, hP, hQ]
    simp
  have hfirst : (ContinuousLinearMap.fst ℝ Plane (A × B)).comp
      ((jointBlock j P Q).comp (ContinuousLinearMap.inl ℝ Plane (A × B))) = linearMap (u, v) := by
    apply ContinuousLinearMap.ext
    intro w
    change (jointBlock j P Q (w, 0)).1 = w.1 • u + w.2 • v
    rw [jointBlock_apply]
    change (P (w.1, 0) + Q (w.2, 0)).1 = w.1 • u + w.2 • v
    rw [map_first_axis P w.1, map_first_axis Q w.2, hP, hQ]
    rfl
  have hsecond : (ContinuousLinearMap.snd ℝ Plane (A × B)).comp
      ((jointBlock j P Q).comp (ContinuousLinearMap.inr ℝ Plane (A × B))) =
      j.symm.toContinuousLinearMap.comp
        (((ContinuousLinearMap.snd ℝ Plane F).comp (P.comp (ContinuousLinearMap.inr ℝ ℝ A))).coprod
          ((ContinuousLinearMap.snd ℝ Plane F).comp
            (Q.comp (ContinuousLinearMap.inr ℝ ℝ B)))) := by
    apply ContinuousLinearMap.ext
    intro w
    rfl
  rw [FrameField.det_of_zero_lower_left _ hzero, hfirst, hsecond]

end Wikipedia.SmoothSixDPoincare.IntersectionCoordinates
