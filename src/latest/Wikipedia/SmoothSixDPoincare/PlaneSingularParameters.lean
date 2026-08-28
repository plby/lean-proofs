import Wikipedia.SmoothSixDPoincare.PlaneAffinePerturbation

/-!
# Parametrizing all singular differentials of plane perturbations

A nonzero kernel vector has a nonzero first or second coordinate. Dividing
by that coordinate expresses one parameter column in terms of the other.
Thus every singular parameter lies in one of two explicitly smooth images.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.PlaneImmersion

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Parameters singular on a direction with first coordinate one. -/
def badFirst (f : Plane → F) (q : Plane × (ℝ × F)) : F × F :=
  (-fderiv ℝ f q.1 (1, q.2.1) - q.2.1 • q.2.2, q.2.2)

/-- Parameters singular on a direction with second coordinate one. -/
def badSecond (f : Plane → F) (q : Plane × (ℝ × F)) : F × F :=
  (q.2.2, -fderiv ℝ f q.1 (q.2.1, 1) - q.2.1 • q.2.2)

theorem contDiff_badFirst {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (badFirst f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have he : ContDiff ℝ ∞ (fun q : Plane × (ℝ × F) => fderiv ℝ f q.1 (1, q.2.1)) :=
    (hd.comp contDiff_fst).clm_apply (contDiff_const.prodMk (contDiff_fst.comp contDiff_snd))
  exact (he.neg.sub ((contDiff_fst.comp contDiff_snd).smul
    (contDiff_snd.comp contDiff_snd))).prodMk (contDiff_snd.comp contDiff_snd)

theorem contDiff_badSecond {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (badSecond f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have he : ContDiff ℝ ∞ (fun q : Plane × (ℝ × F) => fderiv ℝ f q.1 (q.2.1, 1)) :=
    (hd.comp contDiff_fst).clm_apply ((contDiff_fst.comp contDiff_snd).prodMk contDiff_const)
  exact (contDiff_snd.comp contDiff_snd).prodMk
    (he.neg.sub ((contDiff_fst.comp contDiff_snd).smul (contDiff_snd.comp contDiff_snd)))

/-- Every actual nonzero kernel vector puts the parameter in one of the two bad images. -/
theorem mem_bad_of_nonzero_kernel (f : Plane → F) (A : F × F) (x v : Plane)
    (hv : v ≠ 0) (hker : (fderiv ℝ f x + linearMap A) v = 0) :
    A ∈ range (badFirst f) ∪ range (badSecond f) := by
  by_cases hfirst : v.1 = 0
  · have hsecond : v.2 ≠ 0 := by
      intro h
      exact hv (Prod.ext hfirst h)
    let r := v.1 / v.2
    have hvec : (r, (1 : ℝ)) = v.2⁻¹ • v := by
      apply Prod.ext
      · change v.1 / v.2 = v.2⁻¹ * v.1
        rw [div_eq_mul_inv, mul_comm]
      · change (1 : ℝ) = v.2⁻¹ * v.2
        rw [inv_mul_cancel₀ hsecond]
    have hz : (fderiv ℝ f x + linearMap A) (r, 1) = 0 := by
      rw [hvec, map_smul, hker, smul_zero]
    change fderiv ℝ f x (r, 1) + (r • A.1 + (1 : ℝ) • A.2) = 0 at hz
    rw [one_smul, ← add_assoc] at hz
    have hsolve : A.2 = -(fderiv ℝ f x (r, 1) + r • A.1) := eq_neg_of_add_eq_zero_right hz
    apply Or.inr
    refine ⟨(x, (r, A.1)), Prod.ext rfl ?_⟩
    change -fderiv ℝ f x (r, 1) - r • A.1 = A.2
    simpa only [neg_add, sub_eq_add_neg] using hsolve.symm
  · let r := v.2 / v.1
    have hvec : ((1 : ℝ), r) = v.1⁻¹ • v := by
      apply Prod.ext
      · change (1 : ℝ) = v.1⁻¹ * v.1
        rw [inv_mul_cancel₀ hfirst]
      · change v.2 / v.1 = v.1⁻¹ * v.2
        rw [div_eq_mul_inv, mul_comm]
    have hz : (fderiv ℝ f x + linearMap A) (1, r) = 0 := by
      rw [hvec, map_smul, hker, smul_zero]
    change fderiv ℝ f x (1, r) + ((1 : ℝ) • A.1 + r • A.2) = 0 at hz
    rw [one_smul, ← add_assoc] at hz
    have hsolve : fderiv ℝ f x (1, r) + A.1 = -(r • A.2) := eq_neg_of_add_eq_zero_left hz
    apply Or.inl
    refine ⟨(x, (r, A.2)), Prod.ext ?_ rfl⟩
    change -fderiv ℝ f x (1, r) - r • A.2 = A.1
    rw [sub_eq_add_neg, ← hsolve, neg_add_cancel_left]

/-- Avoiding the two explicit images makes every perturbed differential injective. -/
theorem injective_add_linearMap_of_not_bad (f : Plane → F) {A : F × F}
    (hA : A ∉ range (badFirst f) ∪ range (badSecond f)) (x : Plane) :
    Function.Injective (fderiv ℝ f x + linearMap A) := by
  intro v w hvw
  have hz : (fderiv ℝ f x + linearMap A) (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have heq : v - w = 0 := by
    by_contra hne
    exact hA (mem_bad_of_nonzero_kernel f A x (v - w) hne hz)
  exact sub_eq_zero.mp heq

end Wikipedia.SmoothSixDPoincare.PlaneImmersion
