import ErdosProblems.Erdos1148.PairEmbeddings

/-!
# Explicit orthogonal frames for the discriminant form

For the particular split ternary form needed here, a nondegenerate pair has
an explicit orthogonal complement. This gives a direct replacement for the
Witt-extension step in Appendix A of arXiv:1109.0413.
-/

namespace Erdos1148.DukeArithmetic

def pairNormal {R : Type*} [CommRing R] (t u : R × R × R) : R × R × R :=
  (t.1 * u.2.1 - t.2.1 * u.1,
    2 * (t.1 * u.2.2 - t.2.2 * u.1), t.2.1 * u.2.2 - t.2.2 * u.2.1)

lemma pairing_normal_left {R : Type*} [CommRing R] (t u : R × R × R) :
    pairing t (pairNormal t u) = 0 := by
  dsimp [pairing, pairNormal]
  ring

lemma pairing_normal_right {R : Type*} [CommRing R] (t u : R × R × R) :
    pairing u (pairNormal t u) = 0 := by
  dsimp [pairing, pairNormal]
  ring

lemma four_discr_pairNormal {R : Type*} [CommRing R] (t u : R × R × R) :
    4 * discr (pairNormal t u) = pairing t u ^ 2 - 4 * discr t * discr u := by
  dsimp [pairing, pairNormal, discr]
  ring

def pairFrame {R : Type*} [CommRing R] (t u : R × R × R) :
    Matrix (Fin 3) (Fin 3) R :=
  !![t.1, u.1, (pairNormal t u).1;
     t.2.1, u.2.1, (pairNormal t u).2.1;
     t.2.2, u.2.2, (pairNormal t u).2.2]

lemma eight_det_pairFrame {R : Type*} [CommRing R] (t u : R × R × R) :
    8 * (pairFrame t u).det = 4 * discr t * discr u - pairing t u ^ 2 := by
  simp [pairFrame, Matrix.det_fin_three, pairNormal, discr, pairing]
  ring

lemma det_pairFrame_ne_zero {R : Type*} [CommRing R] {d ℓ : R}
    (p : FormPair R d ℓ) (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) :
    (pairFrame p.1.1 p.1.2).det ≠ 0 := by
  intro hz
  have h := eight_det_pairFrame p.1.1 p.1.2
  rw [hz, mul_zero, p.2.1, p.2.2.1, p.2.2.2] at h
  apply hnd
  linear_combination h

lemma discr_pairNormal_eq {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    {d ℓ : R} (p q : FormPair R d ℓ) :
    discr (pairNormal p.1.1 p.1.2) = discr (pairNormal q.1.1 q.1.2) := by
  apply mul_left_cancel₀ (show (4 : R) ≠ 0 by norm_num)
  rw [four_discr_pairNormal, four_discr_pairNormal,
    p.2.1, p.2.2.1, p.2.2.2, q.2.1, q.2.2.1, q.2.2.2]

lemma det_pairFrame_eq {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    {d ℓ : R} (p q : FormPair R d ℓ) :
    (pairFrame p.1.1 p.1.2).det = (pairFrame q.1.1 q.1.2).det := by
  apply mul_left_cancel₀ (show (8 : R) ≠ 0 by norm_num)
  rw [eight_det_pairFrame, eight_det_pairFrame,
    p.2.1, p.2.2.1, p.2.2.2, q.2.1, q.2.2.1, q.2.2.2]

def coeffVecEquiv (R : Type*) [CommRing R] : (R × R × R) ≃ₗ[R] (Fin 3 → R) where
  toFun t := ![t.1, t.2.1, t.2.2]
  invFun v := (v 0, v 1, v 2)
  left_inv _ := rfl
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' t u := by ext i; fin_cases i <;> rfl
  map_smul' a t := by ext i; fin_cases i <;> rfl

lemma coeffVecEquiv_apply {R : Type*} [CommRing R] (t : R × R × R) :
    coeffVecEquiv R t = ![t.1, t.2.1, t.2.2] := rfl

lemma coeffVecEquiv_symm_apply {R : Type*} [CommRing R] (v : Fin 3 → R) :
    (coeffVecEquiv R).symm v = (v 0, v 1, v 2) := rfl

noncomputable def pairFrameEquivOfUnit {R : Type*} [CommRing R] {d ℓ : R}
    (p : FormPair R d ℓ) (hdet : IsUnit (pairFrame p.1.1 p.1.2).det) :
    (R × R × R) ≃ₗ[R] (R × R × R) :=
  (coeffVecEquiv R).trans
    ((Matrix.toLinearEquiv (Pi.basisFun R (Fin 3)) (pairFrame p.1.1 p.1.2) hdet).trans
      (coeffVecEquiv R).symm)

lemma pairFrameEquivOfUnit_apply {R : Type*} [CommRing R] {d ℓ : R}
    (p : FormPair R d ℓ) (hdet : IsUnit (pairFrame p.1.1 p.1.2).det) (v : R × R × R) :
    pairFrameEquivOfUnit p hdet v =
      v.1 • p.1.1 + v.2.1 • p.1.2 + v.2.2 • pairNormal p.1.1 p.1.2 := by
  ext <;> simp [pairFrameEquivOfUnit, coeffVecEquiv_apply, coeffVecEquiv_symm_apply,
    Matrix.toLinearEquiv_apply,
    Matrix.toLin_eq_toLin', Matrix.toLin'_apply, pairFrame] <;> ring

lemma discr_three_combination {R : Type*} [CommRing R] (t u w : R × R × R) (x y z : R) :
    discr (x • t + y • u + z • w) =
      x ^ 2 * discr t + y ^ 2 * discr u + z ^ 2 * discr w +
        x * y * pairing t u + x * z * pairing t w + y * z * pairing u w := by
  dsimp [discr, pairing]
  ring

lemma discr_pairFrameEquivOfUnit {R : Type*} [CommRing R] {d ℓ : R}
    (p : FormPair R d ℓ) (hdet : IsUnit (pairFrame p.1.1 p.1.2).det) (v : R × R × R) :
    discr (pairFrameEquivOfUnit p hdet v) =
      v.1 ^ 2 * d + v.2.1 ^ 2 * d +
        v.2.2 ^ 2 * discr (pairNormal p.1.1 p.1.2) + v.1 * v.2.1 * ℓ := by
  rw [pairFrameEquivOfUnit_apply, discr_three_combination,
    pairing_normal_left, pairing_normal_right, p.2.1, p.2.2.1, p.2.2.2]
  ring

lemma det_pairFrameEquivOfUnit {R : Type*} [CommRing R] {d ℓ : R}
    (p : FormPair R d ℓ) (hdet : IsUnit (pairFrame p.1.1 p.1.2).det) :
    LinearMap.det (pairFrameEquivOfUnit p hdet).toLinearMap = (pairFrame p.1.1 p.1.2).det := by
  let f := Matrix.toLinearEquiv (Pi.basisFun R (Fin 3)) (pairFrame p.1.1 p.1.2) hdet
  calc
    _ = LinearMap.det f.toLinearMap := by
      let e := (coeffVecEquiv R).symm
      have heq : (pairFrameEquivOfUnit p hdet).toLinearMap =
          ((e.symm.trans f).trans e).toLinearMap := by
        apply LinearMap.ext
        intro v
        rfl
      have h : LinearMap.det ((e.symm.trans f).trans e).toLinearMap =
          LinearMap.det f.toLinearMap := by
        simpa only [LinearEquiv.coe_det] using
          congrArg (fun x : Rˣ => (x : R)) (LinearEquiv.det_conj f e)
      exact (congrArg (fun F : (R × R × R) →ₗ[R] (R × R × R) => LinearMap.det F) heq).trans h
    _ = (pairFrame p.1.1 p.1.2).det := LinearMap.det_toLin _ _

lemma pairFrameEquivOfUnit_first {R : Type*} [CommRing R] {d ℓ : R}
    (p : FormPair R d ℓ) (hdet : IsUnit (pairFrame p.1.1 p.1.2).det) :
    pairFrameEquivOfUnit p hdet (1, 0, 0) = p.1.1 := by
  simp only [pairFrameEquivOfUnit_apply, one_smul, zero_smul, add_zero]

lemma pairFrameEquivOfUnit_second {R : Type*} [CommRing R] {d ℓ : R}
    (p : FormPair R d ℓ) (hdet : IsUnit (pairFrame p.1.1 p.1.2).det) :
    pairFrameEquivOfUnit p hdet (0, 1, 0) = p.1.2 := by
  simp only [pairFrameEquivOfUnit_apply, one_smul, zero_smul, zero_add, add_zero]

/-- An explicit extension of the isometry between the two binary subspaces. -/
noncomputable def frameIsometryOfUnit {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    {d ℓ : R} (p q : FormPair R d ℓ)
    (hp : IsUnit (pairFrame p.1.1 p.1.2).det) (hq : IsUnit (pairFrame q.1.1 q.1.2).det) :
    QuadraticMap.IsometryEquiv (discrQuadraticForm R) (discrQuadraticForm R) :=
  { (pairFrameEquivOfUnit p hp).symm.trans (pairFrameEquivOfUnit q hq) with
    map_app' := by
      intro v
      change discr (pairFrameEquivOfUnit q hq ((pairFrameEquivOfUnit p hp).symm v)) = discr v
      calc
        _ = discr (pairFrameEquivOfUnit p hp ((pairFrameEquivOfUnit p hp).symm v)) := by
          rw [discr_pairFrameEquivOfUnit, discr_pairFrameEquivOfUnit, discr_pairNormal_eq p q]
        _ = discr v := congrArg discr ((pairFrameEquivOfUnit p hp).apply_symm_apply v) }

lemma frameIsometryOfUnit_first {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    {d ℓ : R} (p q : FormPair R d ℓ)
    (hp : IsUnit (pairFrame p.1.1 p.1.2).det) (hq : IsUnit (pairFrame q.1.1 q.1.2).det) :
    frameIsometryOfUnit p q hp hq p.1.1 = q.1.1 := by
  change pairFrameEquivOfUnit q hq ((pairFrameEquivOfUnit p hp).symm p.1.1) = q.1.1
  rw [← pairFrameEquivOfUnit_first p hp, LinearEquiv.symm_apply_apply,
    pairFrameEquivOfUnit_first]

lemma frameIsometryOfUnit_second {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    {d ℓ : R} (p q : FormPair R d ℓ)
    (hp : IsUnit (pairFrame p.1.1 p.1.2).det) (hq : IsUnit (pairFrame q.1.1 q.1.2).det) :
    frameIsometryOfUnit p q hp hq p.1.2 = q.1.2 := by
  change pairFrameEquivOfUnit q hq ((pairFrameEquivOfUnit p hp).symm p.1.2) = q.1.2
  rw [← pairFrameEquivOfUnit_second p hp, LinearEquiv.symm_apply_apply,
    pairFrameEquivOfUnit_second]

lemma frameIsometryOfUnit_det {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    {d ℓ : R} (p q : FormPair R d ℓ)
    (hp : IsUnit (pairFrame p.1.1 p.1.2).det) (hq : IsUnit (pairFrame q.1.1 q.1.2).det) :
    LinearMap.det (frameIsometryOfUnit p q hp hq).toLinearEquiv.toLinearMap = 1 := by
  change LinearMap.det ((pairFrameEquivOfUnit q hq).toLinearMap.comp
    (pairFrameEquivOfUnit p hp).symm.toLinearMap) = 1
  rw [LinearMap.det_comp]
  have hdet : LinearMap.det (pairFrameEquivOfUnit q hq).toLinearMap =
      LinearMap.det (pairFrameEquivOfUnit p hp).toLinearMap := by
    rw [det_pairFrameEquivOfUnit, det_pairFrameEquivOfUnit, det_pairFrame_eq q p]
  rw [hdet]
  exact LinearEquiv.det_mul_det_symm _

lemma isUnit_det_pairFrame {R : Type*} [CommRing R] {d ℓ : R}
    (p : FormPair R d ℓ) (hunit : IsUnit (ℓ ^ 2 - 4 * d ^ 2)) :
    IsUnit (pairFrame p.1.1 p.1.2).det := by
  have hprod : IsUnit ((8 : R) * (pairFrame p.1.1 p.1.2).det) := by
    rw [eight_det_pairFrame, p.2.1, p.2.2.1, p.2.2.2]
    convert hunit.neg using 1
    ring
  exact isUnit_of_mul_isUnit_right hprod

/-- The unramified, unit-discriminant case needs no lattice enumeration. -/
theorem exists_isometry_of_unit_pair_discriminant {R : Type*} [CommRing R]
    [NoZeroDivisors R] [CharZero R] {d ℓ : R} (p q : FormPair R d ℓ)
    (hunit : IsUnit (ℓ ^ 2 - 4 * d ^ 2)) :
    ∃ g : QuadraticMap.IsometryEquiv (discrQuadraticForm R) (discrQuadraticForm R),
      g p.1.1 = q.1.1 ∧ g p.1.2 = q.1.2 := by
  let hp := isUnit_det_pairFrame p hunit
  let hq := isUnit_det_pairFrame q hunit
  exact ⟨frameIsometryOfUnit p q hp hq,
    frameIsometryOfUnit_first p q hp hq, frameIsometryOfUnit_second p q hp hq⟩

/-- The rational extension step, specialized to the discriminant ternary form. -/
theorem exists_isometry_of_nondegenerate_pair {K : Type*} [Field K] [CharZero K]
    {d ℓ : K} (p q : FormPair K d ℓ) (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) :
    ∃ g : QuadraticMap.IsometryEquiv (discrQuadraticForm K) (discrQuadraticForm K),
      g p.1.1 = q.1.1 ∧ g p.1.2 = q.1.2 :=
  exists_isometry_of_unit_pair_discriminant p q (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hnd))

/-- The explicit extension also has determinant one, as required for special-orthogonal orbits. -/
theorem exists_specialIsometry_of_unit_pair_discriminant {R : Type*} [CommRing R]
    [NoZeroDivisors R] [CharZero R] {d ℓ : R} (p q : FormPair R d ℓ)
    (hunit : IsUnit (ℓ ^ 2 - 4 * d ^ 2)) :
    ∃ g : QuadraticMap.IsometryEquiv (discrQuadraticForm R) (discrQuadraticForm R),
      LinearMap.det g.toLinearEquiv.toLinearMap = 1 ∧ g p.1.1 = q.1.1 ∧ g p.1.2 = q.1.2 := by
  let hp := isUnit_det_pairFrame p hunit
  let hq := isUnit_det_pairFrame q hunit
  exact ⟨frameIsometryOfUnit p q hp hq, frameIsometryOfUnit_det p q hp hq,
    frameIsometryOfUnit_first p q hp hq, frameIsometryOfUnit_second p q hp hq⟩

theorem exists_specialIsometry_of_nondegenerate_pair {K : Type*} [Field K] [CharZero K]
    {d ℓ : K} (p q : FormPair K d ℓ) (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) :
    ∃ g : QuadraticMap.IsometryEquiv (discrQuadraticForm K) (discrQuadraticForm K),
      LinearMap.det g.toLinearEquiv.toLinearMap = 1 ∧ g p.1.1 = q.1.1 ∧ g p.1.2 = q.1.2 :=
  exists_specialIsometry_of_unit_pair_discriminant p q
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hnd))

end Erdos1148.DukeArithmetic
