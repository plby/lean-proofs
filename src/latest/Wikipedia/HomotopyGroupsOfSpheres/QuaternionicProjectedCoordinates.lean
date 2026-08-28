import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicProjectedSmoothness
import Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates

/-!
# Source coordinates and the injective projected differential

The source chart uses the two Bott angles and stereographic coordinates on
the five-sphere. The actual first-column map is smooth in these coordinates,
and its real Frechet derivative is injective at every selected-target input.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix

local notation "ℍ" => Quaternion ℝ

abbrev ParameterSpace (z : UnitSphere) := ℝ × ℝ × SphereCenteredCoordinates.Tangent z

def localSphere (z : UnitSphere) (p : ParameterSpace z) : UnitSphere :=
  SphereCenteredCoordinates.inverse z p.2.2

def localProjection (z : UnitSphere) (p : ParameterSpace z) : Fin 2 → ℍ :=
  firstColumnFormula (Real.pi / 2 + p.1) (Real.pi / 2 + p.2.1)
    (symmetricMap (localSphere z p))

@[simp] theorem localSphere_zero (z : UnitSphere) : localSphere z 0 = z :=
  SphereCenteredCoordinates.inverse_zero z

@[simp] theorem localProjection_zero (z : UnitSphere) :
    localProjection z 0 = firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) := by
  simp [localProjection]

theorem contDiff_localSphere_entry (z : UnitSphere) {n : ℕ∞ω} (r : Fin 3) :
    ContDiff ℝ n (fun p : ParameterSpace z ↦ (localSphere z p).val r) :=
  (PiLp.proj 2 (fun _ : Fin 3 ↦ ℂ) r : EuclideanSpace ℂ (Fin 3) →L[ℝ] ℂ).contDiff.comp
    ((SphereCenteredCoordinates.contDiff_inverse_val z).comp contDiff_snd.snd)

theorem contDiff_localProjection (z : UnitSphere) {n : ℕ∞ω} :
    ContDiff ℝ n (localProjection z) := by
  apply contDiff_pi.mpr
  intro r
  exact contDiff_firstColumnFormula_entry _ _ _
    (contDiff_const.add contDiff_fst) (contDiff_const.add contDiff_snd.fst)
    (contDiff_symmetricMap_entry (localSphere z) (contDiff_localSphere_entry z)) r

theorem hasDerivAt_localSphere_line_entry (z : UnitSphere) (v : ParameterSpace z) (r : Fin 3) :
    HasDerivAt (fun t : ℝ ↦ (localSphere z (t • v)).val r) (v.2.2.val r) 0 := by
  have h := (PiLp.proj 2 (fun _ : Fin 3 ↦ ℂ) r :
    EuclideanSpace ℂ (Fin 3) →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt 0
      (SphereCenteredCoordinates.hasDerivAt_inverse_line z v.2.2)
  convert h using 1 <;> try rfl

theorem localProjection_fderiv_kernel (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (v : ParameterSpace z) (hv : fderiv ℝ (localProjection z) 0 v = 0) : v = 0 := by
  have hf := (contDiff_localProjection z (n := 1)).differentiable (by decide)
  have hfd : HasFDerivAt (localProjection z) (fderiv ℝ (localProjection z) 0)
      ((0 : ℝ) • v) := by
    simpa only [zero_smul] using (hf 0).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ ↦ localProjection z (t • v)) (0 : Fin 2 → ℍ) 0 := by
    have he := hfd.comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).smul_const v)
    convert he using 1 <;> try rfl
    simpa only [one_smul] using hv.symm
  have hs : HasDerivAt (fun t : ℝ ↦ Real.pi / 2 + (t • v).1) v.1 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const v.1).const_add (Real.pi / 2) using 1 <;>
      try rfl
    simp
  have ht : HasDerivAt (fun t : ℝ ↦ Real.pi / 2 + (t • v).2.1) v.2.1 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const v.2.1).const_add (Real.pi / 2) using 1 <;>
      try rfl
    simp
  obtain ⟨ha, hb, hc⟩ := firstColumn_curve_kernel_midpoint
    (fun t : ℝ ↦ Real.pi / 2 + (t • v).1)
    (fun t : ℝ ↦ Real.pi / 2 + (t • v).2.1)
    (fun t : ℝ ↦ localSphere z (t • v)) v.1 v.2.1 0 v.2.2.val hs ht
    (hasDerivAt_localSphere_line_entry z v) (by simp) (by simp)
    (by simpa using hz) (hasDerivAt_pi.mp hline)
  apply Prod.ext ha
  apply Prod.ext hb
  apply Subtype.ext
  exact congrArg (WithLp.toLp 2) hc

theorem localProjection_fderiv_injective (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn) :
    Function.Injective (fderiv ℝ (localProjection z) 0) := by
  intro v w h
  have he : fderiv ℝ (localProjection z) 0 (v - w) = 0 := by
    rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (localProjection_fderiv_kernel z hz (v - w) he)

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
