import StackExchange.Puzzling139335.PlaneIsometries
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Angular directions in the punctured plane

The angular coordinate is obtained by normalizing a nonzero complex vector,
then using the standard homeomorphism from `AddCircle 1` to the unit circle.
It is jointly continuous in the two distinct points.  An affine direct
isometry adds a constant to this angular coordinate; this is the concrete
input for winding-number invariance, without any assumption on the curves.
-/

open Set

namespace Puzzling139335.CentralRotation.BoundaryOrientation

noncomputable section

private def nonzeroDirection (z : ({0}ᶜ : Set ℂ)) : Circle :=
  ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr (by
      simpa only [mem_compl_iff, mem_singleton_iff] using z.property))⟩

private theorem continuous_nonzeroDirection : Continuous nonzeroDirection := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.div
    (Complex.continuous_ofReal.comp continuous_subtype_val.norm)
    (fun z => Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (by
        simpa only [mem_compl_iff, mem_singleton_iff] using z.property)))

/-- The standard angular coordinate, with one full turn equal to one. -/
def circleAngle (u : Circle) : AddCircle (1 : ℝ) :=
  (AddCircle.homeomorphCircle one_ne_zero).symm u

theorem continuous_circleAngle : Continuous circleAngle :=
  (AddCircle.homeomorphCircle one_ne_zero).symm.continuous

theorem circleAngle_mul (u v : Circle) :
    circleAngle (u * v) = circleAngle u + circleAngle v := by
  apply (AddCircle.homeomorphCircle one_ne_zero).injective
  simp only [circleAngle, Homeomorph.apply_symm_apply,
    AddCircle.homeomorphCircle_apply, AddCircle.toCircle_add]
  rw [← AddCircle.homeomorphCircle_apply one_ne_zero,
    ← AddCircle.homeomorphCircle_apply one_ne_zero]
  simp

private theorem nonzeroDirection_mul (a : Circle) (z : ({0}ᶜ : Set ℂ)) :
    nonzeroDirection ⟨(a : ℂ) * z, by
      simp only [mem_compl_iff, mem_singleton_iff]
      exact mul_ne_zero (Circle.coe_ne_zero a) (by
        simpa only [mem_compl_iff, mem_singleton_iff] using z.property)⟩ =
      a * nonzeroDirection z := by
  apply Subtype.ext
  change (a : ℂ) * (z : ℂ) / (‖(a : ℂ) * (z : ℂ)‖ : ℂ) =
    (a : ℂ) * ((z : ℂ) / (‖(z : ℂ)‖ : ℂ))
  rw [norm_mul, Circle.norm_coe, one_mul, mul_div_assoc]

/-- The angular direction from the second point to the first point. -/
def directionDifference : C(({p : Plane × Plane | p.1 ≠ p.2}), AddCircle (1 : ℝ)) where
  toFun p := circleAngle (nonzeroDirection
    ⟨PlaneIsometries.complexEquiv (p.val.1 - p.val.2), by
      simp only [mem_compl_iff, mem_singleton_iff]
      exact (map_ne_zero_iff PlaneIsometries.complexEquiv
        PlaneIsometries.complexEquiv.injective).mpr (sub_ne_zero.mpr p.property)⟩)
  continuous_toFun := by
    apply continuous_circleAngle.comp
    apply continuous_nonzeroDirection.comp
    apply Continuous.subtype_mk
    exact PlaneIsometries.complexEquiv.continuous.comp
      ((continuous_fst.comp continuous_subtype_val).sub
        (continuous_snd.comp continuous_subtype_val))

/-- Angular direction from a fixed point, defined on its complement. -/
def directionFrom (x : Plane) : C(({x}ᶜ : Set Plane), AddCircle (1 : ℝ)) where
  toFun p := directionDifference ⟨((p : Plane), x), by
    change (p : Plane) ≠ x
    simpa only [mem_compl_iff, mem_singleton_iff] using p.property⟩
  continuous_toFun := directionDifference.continuous.comp
    ((continuous_subtype_val.prodMk continuous_const).subtype_mk _)

/-- Angular direction along a path avoiding the specified point. -/
def directionPath (f : C(unitInterval, Plane)) (x : Plane)
    (hx : ∀ t, f t ≠ x) : C(unitInterval, AddCircle (1 : ℝ)) where
  toFun t := directionFrom x ⟨f t, by
    simpa only [mem_compl_iff, mem_singleton_iff] using hx t⟩
  continuous_toFun := (directionFrom x).continuous.comp
    (f.continuous.subtype_mk _)

/-- A total angular function, with an irrelevant value at its excluded point.
Its only continuity assertion is on the punctured plane. -/
def directionAt (x p : Plane) : AddCircle (1 : ℝ) := by
  classical
  exact if hp : p = x then 0 else directionFrom x ⟨p, hp⟩

theorem directionAt_of_ne {x p : Plane} (hp : p ≠ x) :
    directionAt x p = directionFrom x ⟨p, hp⟩ := dif_neg hp

theorem continuousOn_directionAt (x : Plane) :
    ContinuousOn (directionAt x) ({x}ᶜ : Set Plane) := by
  rw [continuousOn_iff_continuous_restrict]
  have hrestrict : ({x}ᶜ : Set Plane).domRestrict (directionAt x) = directionFrom x := by
    funext p
    exact directionAt_of_ne p.property
  rw [hrestrict]
  exact (directionFrom x).continuous

theorem directionPath_apply (f : C(unitInterval, Plane)) (x : Plane)
    (hx : ∀ t, f t ≠ x) (t : unitInterval) :
    directionPath f x hx t = directionAt x (f t) :=
  (directionAt_of_ne (hx t)).symm

/-- The direct affine formula is all that is needed for angular transport. -/
theorem directionDifference_direct {g : Plane → Plane} {a : Circle} {b : ℂ}
    (hg : ∀ p, PlaneIsometries.complexEquiv (g p) =
      (a : ℂ) * PlaneIsometries.complexEquiv p + b)
    {p q : Plane} (hpq : p ≠ q) (hgpq : g p ≠ g q) :
    directionDifference ⟨(g p, g q), hgpq⟩ =
      circleAngle a + directionDifference ⟨(p, q), hpq⟩ := by
  have hdiff : PlaneIsometries.complexEquiv (g p - g q) =
      (a : ℂ) * PlaneIsometries.complexEquiv (p - q) := by
    simp only [map_sub, hg]
    ring
  change circleAngle (nonzeroDirection _) =
    circleAngle a + circleAngle (nonzeroDirection _)
  rw [← circleAngle_mul]
  apply congrArg circleAngle
  rw [← nonzeroDirection_mul]
  apply congrArg nonzeroDirection
  exact Subtype.ext hdiff

/-- Direct isometries rotate every angular path by the same constant. -/
theorem directionFrom_direct (g : Plane ≃ᵃⁱ[ℝ] Plane) {a : Circle} {b : ℂ}
    (hg : ∀ p, PlaneIsometries.complexEquiv (g p) =
      (a : ℂ) * PlaneIsometries.complexEquiv p + b)
    (x : Plane) (p : ({x}ᶜ : Set Plane)) :
    directionFrom (g x) ⟨g p, by
      simp only [mem_compl_iff, mem_singleton_iff]
      exact g.injective.ne (by
        simpa only [mem_compl_iff, mem_singleton_iff] using p.property)⟩ =
      circleAngle a + directionFrom x p :=
  directionDifference_direct hg
    (by simpa only [mem_compl_iff, mem_singleton_iff] using p.property)
    (g.injective.ne (by simpa only [mem_compl_iff, mem_singleton_iff] using p.property))

theorem directionAt_direct (g : Plane ≃ᵃⁱ[ℝ] Plane) {a : Circle} {b : ℂ}
    (hg : ∀ p, PlaneIsometries.complexEquiv (g p) =
      (a : ℂ) * PlaneIsometries.complexEquiv p + b)
    {x p : Plane} (hp : p ≠ x) :
    directionAt (g x) (g p) = circleAngle a + directionAt x p := by
  rw [directionAt_of_ne (g.injective.ne hp), directionAt_of_ne hp]
  exact directionFrom_direct g hg x ⟨p, hp⟩

end

end Puzzling139335.CentralRotation.BoundaryOrientation
