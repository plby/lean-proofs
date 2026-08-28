import Wikipedia.NoExoticSixSphere.JamesSphereEquatorCoordinates

/-!
# Matching the actual James punctures with antipodal sphere poles

Doubling finite stereographic coordinates preserves the middle equator
and fixes infinity. It sends the actual quarter-time punctures to the
two antipodal orthogonal poles, with no change to the original spaces.
-/

noncomputable section

open scoped unitInterval OnePoint

namespace NoExoticSixSphere.JamesSphere

def dilation (n : ℕ) : Sphere (n + 1) ≃ₜ Sphere (n + 1) :=
  (euclideanOnePointSphere (n + 1)).symm.trans
    ((Homeomorph.smulOfNeZero (2 : ℝ) (by norm_num) : V (n + 1) ≃ₜ V (n + 1)).onePointCongr.trans
      (euclideanOnePointSphere (n + 1)))

theorem dilation_finite (n : ℕ) (x : V (n + 1)) :
    dilation n (euclideanOnePointSphere (n + 1) (x : OnePoint _)) =
      euclideanOnePointSphere (n + 1) (((2 : ℝ) • x) : OnePoint _) := by
  change euclideanOnePointSphere (n + 1)
    ((Homeomorph.smulOfNeZero (2 : ℝ) (by norm_num) : V (n + 1) ≃ₜ V (n + 1)).onePointCongr
      ((euclideanOnePointSphere (n + 1)).symm
        (euclideanOnePointSphere (n + 1) (x : OnePoint _)))) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

theorem dilation_pole (n : ℕ) : dilation n (spherePole (n + 1)) = spherePole (n + 1) := by
  rw [← euclideanOnePointSphere_infty (n + 1)]
  change euclideanOnePointSphere (n + 1)
    ((Homeomorph.smulOfNeZero (2 : ℝ) (by norm_num) : V (n + 1) ≃ₜ V (n + 1)).onePointCongr
      ((euclideanOnePointSphere (n + 1)).symm
        (euclideanOnePointSphere (n + 1) OnePoint.infty))) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

theorem dilation_mem_equator_iff (n : ℕ) (x : Sphere (n + 1)) :
    dilation n x ∈ equator (equatorPole n) ↔ x ∈ equator (equatorPole n) := by
  obtain ⟨z, rfl⟩ := (euclideanOnePointSphere (n + 1)).surjective x
  induction z using OnePoint.rec with
  | infty => rw [euclideanOnePointSphere_infty, dilation_pole]
  | coe z =>
    rw [dilation_finite]
    simp only [equatorPole, StereographicEquator.finite_mem_equator_iff,
      StereographicEquator.finite_mem_equator_iff, real_inner_smul_right]
    exact mul_eq_zero.trans (or_iff_right (by norm_num : (2 : ℝ) ≠ 0))

theorem dilation_lowerPuncture (n : ℕ) :
    dilation n (lowerPuncture n) = antipode (equatorPole n) := by
  rw [lowerPuncture_finite, dilation_finite, product_linePoint, smul_smul]
  have he : (2 : ℝ) * (-1) = -2 := by norm_num
  rw [he]
  exact StereographicEquator.compactification_neg_double_axis (n + 1) (coordinateAxis n)

theorem dilation_upperPuncture (n : ℕ) : dilation n (upperPuncture n) = equatorPole n := by
  rw [upperPuncture_finite, dilation_finite, product_linePoint, one_smul]
  exact StereographicEquator.compactification_double_axis (n + 1) (coordinateAxis n)

def overlap (n : ℕ) : Set (Sphere (n + 1)) := {lowerPuncture n}ᶜ ∩ {upperPuncture n}ᶜ

theorem dilation_mem_punctured_iff (n : ℕ) (x : Sphere (n + 1)) :
    dilation n x ∈ SphereEquatorRetraction.punctured (equatorPole n) ↔ x ∈ overlap n := by
  rw [SphereEquatorRetraction.punctured_eq]
  change (dilation n x ≠ equatorPole n ∧ dilation n x ≠ antipode (equatorPole n)) ↔
    x ≠ lowerPuncture n ∧ x ≠ upperPuncture n
  rw [← dilation_lowerPuncture, ← dilation_upperPuncture]
  simp only [(dilation n).injective.ne_iff, and_comm]

def overlapHomeomorph (n : ℕ) : overlap n ≃ₜ SphereEquatorRetraction.punctured (equatorPole n) :=
  (dilation n).subtype (fun x ↦ (dilation_mem_punctured_iff n x).symm)

def equatorDilation (n : ℕ) : Equator (equatorPole n) ≃ₜ Equator (equatorPole n) :=
  (dilation n).subtype (fun x ↦ (dilation_mem_equator_iff n x).symm)

end NoExoticSixSphere.JamesSphere
