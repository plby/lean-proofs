/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Primitive integral representatives of rational projective points

This file supplies the elementary normalization layer used in the proof of
Erdős Problem 407.  A nonzero vector over `ℚ` is cleared of denominators and
then divided by the gcd of its integral coordinates.  We characterize
primitivity by a Bézout identity; this makes uniqueness up to sign especially
convenient to use.
-/

namespace Erdos407.Primitive

open scoped BigOperators LinearAlgebra.Projectivization

variable {ι : Type*} [Fintype ι]

/-- Coordinatewise coercion of an integral vector to a rational vector. -/
def intCastVec (z : ι → ℤ) : ι → ℚ := fun i => z i

@[simp] theorem intCastVec_apply (z : ι → ℤ) (i : ι) :
    intCastVec z i = (z i : ℚ) := rfl

theorem intCastVec_injective : Function.Injective (intCastVec : (ι → ℤ) → ι → ℚ) := by
  intro x y h
  funext i
  have hi : (x i : ℚ) = (y i : ℚ) := by
    simpa [intCastVec] using congrFun h i
  exact_mod_cast hi

/-- A finite integral vector is primitive when its coordinates have a
Bézout combination equal to one. -/
def IsPrimitive (z : ι → ℤ) : Prop :=
  ∃ u : ι → ℤ, ∑ i, u i * z i = 1

theorem IsPrimitive.ne_zero {z : ι → ℤ} (hz : IsPrimitive z) : z ≠ 0 := by
  rintro rfl
  simpa [IsPrimitive] using hz

private def rowMatrix (x : ι → ℚ) : Matrix Unit ι ℚ := fun _ i => x i

/-- A common positive denominator for all coordinates. -/
def commonDen (x : ι → ℚ) : ℕ := (rowMatrix x).den

/-- The integral vector obtained by clearing all denominators. -/
def clearDen (x : ι → ℚ) : ι → ℤ := fun i => (rowMatrix x).num () i

theorem commonDen_ne_zero (x : ι → ℚ) : commonDen x ≠ 0 :=
  Matrix.den_ne_zero (rowMatrix x)

theorem clearDen_div_commonDen (x : ι → ℚ) (i : ι) :
    (clearDen x i : ℚ) / commonDen x = x i := by
  exact Matrix.num_div_den (rowMatrix x) () i

theorem clearDen_ne_zero {x : ι → ℚ} (hx : x ≠ 0) : clearDen x ≠ 0 := by
  intro h
  apply hx
  funext i
  have hi := clearDen_div_commonDen x i
  rw [congrFun h i] at hi
  simpa using hi.symm

/-- The (nonnegative) gcd of the coordinates of an integral vector. -/
def content (z : ι → ℤ) : ℤ := Finset.univ.gcd z

theorem content_dvd (z : ι → ℤ) (i : ι) : content z ∣ z i := by
  exact Finset.gcd_dvd (Finset.mem_univ i)

theorem content_ne_zero {z : ι → ℤ} (hz : z ≠ 0) : content z ≠ 0 := by
  rw [content, Finset.gcd_ne_zero_iff]
  simpa [funext_iff] using hz

/-- Divide an integral vector by the gcd of all its coordinates. -/
def divideContent (z : ι → ℤ) : ι → ℤ := fun i => z i / content z

theorem content_mul_divideContent (z : ι → ℤ) (i : ι) :
    content z * divideContent z i = z i := by
  rw [mul_comm]
  exact Int.ediv_mul_cancel (content_dvd z i)

private theorem exists_bezout_finset (s : Finset ι) (z : ι → ℤ) :
    ∃ u : ι → ℤ, ∑ i ∈ s, u i * z i = s.gcd z := by
  classical
  induction s using Finset.induction with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨u, hu⟩ := ih
      let A : ℤ := Int.gcdA (z a) (s.gcd z)
      let B : ℤ := Int.gcdB (z a) (s.gcd z)
      refine ⟨fun i => if i = a then A else B * u i, ?_⟩
      rw [Finset.sum_insert ha, Finset.gcd_insert]
      simp only [if_pos, mul_assoc]
      have hsum :
          (∑ i ∈ s, (if i = a then A else B * u i) * z i) =
            B * s.gcd z := by
        calc
          (∑ i ∈ s, (if i = a then A else B * u i) * z i) =
              ∑ i ∈ s, B * (u i * z i) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [if_neg (by intro hia; subst i; exact ha hi)]
                ring
          _ = B * ∑ i ∈ s, u i * z i := by
                rw [Finset.mul_sum]
          _ = B * s.gcd z := by rw [hu]
      rw [hsum]
      dsimp [A, B]
      rw [mul_comm B, mul_comm (Int.gcdA (z a) (s.gcd z))]
      exact (Int.gcd_eq_gcd_ab (z a) (s.gcd z)).symm

theorem isPrimitive_of_content_eq_one {z : ι → ℤ} (hz : content z = 1) :
    IsPrimitive z := by
  obtain ⟨u, hu⟩ := exists_bezout_finset Finset.univ z
  have hu' : ∑ i, u i * z i = content z := by
    simpa [content] using hu
  exact ⟨u, hu'.trans hz⟩

theorem divideContent_primitive {z : ι → ℤ} (hz : z ≠ 0) :
    IsPrimitive (divideContent z) := by
  apply isPrimitive_of_content_eq_one
  rw [content]
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hz (funext h)
  exact Finset.gcd_div_eq_one (Finset.mem_univ i) hi

theorem divideContent_ne_zero {z : ι → ℤ} (hz : z ≠ 0) :
    divideContent z ≠ 0 := (divideContent_primitive hz).ne_zero

/-- The primitive integral normalization of a rational vector.  Its useful
properties require that the input vector be nonzero. -/
def normalize (x : ι → ℚ) : ι → ℤ := divideContent (clearDen x)

/-- The rational scalar relating a vector to its primitive normalization. -/
def normalizationScale (x : ι → ℚ) : ℚ :=
  (content (clearDen x) : ℚ) / commonDen x

theorem normalize_primitive {x : ι → ℚ} (hx : x ≠ 0) :
    IsPrimitive (normalize x) :=
  divideContent_primitive (clearDen_ne_zero hx)

theorem normalize_ne_zero {x : ι → ℚ} (hx : x ≠ 0) : normalize x ≠ 0 :=
  (normalize_primitive hx).ne_zero

theorem normalizationScale_ne_zero {x : ι → ℚ} (hx : x ≠ 0) :
    normalizationScale x ≠ 0 := by
  apply div_ne_zero
  · exact_mod_cast content_ne_zero (clearDen_ne_zero hx)
  · exact_mod_cast commonDen_ne_zero x

/-- Clearing denominators and dividing by the content changes a nonzero
vector only by a nonzero rational scalar. -/
theorem eq_normalizationScale_smul (x : ι → ℚ) :
    x = normalizationScale x • intCastVec (normalize x) := by
  funext i
  change x i = normalizationScale x * (normalize x i : ℚ)
  rw [← clearDen_div_commonDen x i]
  rw [← content_mul_divideContent (clearDen x) i]
  simp only [normalizationScale, normalize, intCastVec_apply, Int.cast_mul]
  ring

/-- Two nonzero rational vectors are projectively equivalent when one is a
nonzero scalar multiple of the other. -/
def ProjectivelyEquivalent (x y : ι → ℚ) : Prop :=
  ∃ q : ℚ, q ≠ 0 ∧ x = q • y

theorem projectivelyEquivalent_normalize {x : ι → ℚ} (hx : x ≠ 0) :
    ProjectivelyEquivalent x (intCastVec (normalize x)) :=
  ⟨normalizationScale x, normalizationScale_ne_zero hx,
    eq_normalizationScale_smul x⟩

theorem ProjectivelyEquivalent.refl {x : ι → ℚ} (hx : x ≠ 0) :
    ProjectivelyEquivalent x x := ⟨1, one_ne_zero, by simp⟩

theorem ProjectivelyEquivalent.symm {x y : ι → ℚ}
    (h : ProjectivelyEquivalent x y) : ProjectivelyEquivalent y x := by
  obtain ⟨q, hq, rfl⟩ := h
  refine ⟨q⁻¹, inv_ne_zero hq, ?_⟩
  ext i
  simp [hq]

theorem ProjectivelyEquivalent.trans {x y z : ι → ℚ}
    (hxy : ProjectivelyEquivalent x y) (hyz : ProjectivelyEquivalent y z) :
    ProjectivelyEquivalent x z := by
  obtain ⟨q, hq, rfl⟩ := hxy
  obtain ⟨r, hr, rfl⟩ := hyz
  refine ⟨q * r, mul_ne_zero hq hr, ?_⟩
  simp [smul_smul]

/-! ## Preservation of equations and nondegenerate subsums -/

/-- No nonempty coefficient-weighted subsum vanishes. -/
def IsNondegenerateFor (coeff x : ι → ℚ) : Prop :=
  ∀ I : Finset ι, I.Nonempty → (∑ i ∈ I, coeff i * x i) ≠ 0

theorem weightedSubsum_eq_zero_iff_of_eq_smul
    (coeff : ι → ℚ) (I : Finset ι) {x y : ι → ℚ} {q : ℚ}
    (hq : q ≠ 0) (hxy : x = q • y) :
    (∑ i ∈ I, coeff i * x i) = 0 ↔
      (∑ i ∈ I, coeff i * y i) = 0 := by
  have hsum :
      (∑ i ∈ I, coeff i * x i) = q * ∑ i ∈ I, coeff i * y i := by
    rw [hxy]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum, mul_eq_zero]
  simp [hq]

theorem weightedEquation_preserved_of_eq_smul
    (coeff : ι → ℚ) {x y : ι → ℚ} {q : ℚ}
    (hq : q ≠ 0) (hxy : x = q • y) :
    (∑ i, coeff i * x i) = 0 ↔ (∑ i, coeff i * y i) = 0 := by
  simpa using weightedSubsum_eq_zero_iff_of_eq_smul coeff Finset.univ hq hxy

theorem weightedSubsum_normalize_iff (coeff : ι → ℚ) (I : Finset ι)
    {x : ι → ℚ} (hx : x ≠ 0) :
    (∑ i ∈ I, coeff i * x i) = 0 ↔
      (∑ i ∈ I, coeff i * (normalize x i : ℚ)) = 0 := by
  exact weightedSubsum_eq_zero_iff_of_eq_smul coeff I
    (normalizationScale_ne_zero hx) (eq_normalizationScale_smul x)

theorem weightedEquation_normalize_iff (coeff : ι → ℚ)
    {x : ι → ℚ} (hx : x ≠ 0) :
    (∑ i, coeff i * x i) = 0 ↔
      (∑ i, coeff i * (normalize x i : ℚ)) = 0 := by
  simpa using weightedSubsum_normalize_iff coeff Finset.univ hx

theorem nondegenerateFor_preserved_of_eq_smul
    (coeff : ι → ℚ) {x y : ι → ℚ} {q : ℚ}
    (hq : q ≠ 0) (hxy : x = q • y) :
    IsNondegenerateFor coeff x ↔ IsNondegenerateFor coeff y := by
  constructor <;> intro h I hI hzero
  · exact h I hI ((weightedSubsum_eq_zero_iff_of_eq_smul coeff I hq hxy).2 hzero)
  · exact h I hI ((weightedSubsum_eq_zero_iff_of_eq_smul coeff I hq hxy).1 hzero)

theorem nondegenerateFor_normalize_iff (coeff : ι → ℚ)
    {x : ι → ℚ} (hx : x ≠ 0) :
    IsNondegenerateFor coeff x ↔
      IsNondegenerateFor coeff (intCastVec (normalize x)) :=
  nondegenerateFor_preserved_of_eq_smul coeff
    (normalizationScale_ne_zero hx) (eq_normalizationScale_smul x)

/-! ## Uniqueness of primitive representatives -/

private theorem scalar_is_integer_of_primitive
    {x y : ι → ℤ} (hy : IsPrimitive y) {q : ℚ}
    (hxy : intCastVec x = q • intCastVec y) :
    ∃ k : ℤ, q = k ∧ ∀ i, x i = k * y i := by
  obtain ⟨v, hv⟩ := hy
  let k : ℤ := ∑ i, v i * x i
  have hcoord (i : ι) : (x i : ℚ) = q * (y i : ℚ) := by
    simpa [intCastVec] using congrFun hxy i
  have hvQ : ∑ i, (v i : ℚ) * (y i : ℚ) = 1 := by
    exact_mod_cast hv
  have hqk : q = (k : ℚ) := by
    calc
      q = q * ∑ i, (v i : ℚ) * (y i : ℚ) := by rw [hvQ, mul_one]
      _ = ∑ i, (v i : ℚ) * (q * (y i : ℚ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ i, (v i : ℚ) * (x i : ℚ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hcoord]
      _ = (k : ℚ) := by
        simp only [k, Int.cast_sum, Int.cast_mul]
  refine ⟨k, hqk, fun i => ?_⟩
  have hi := hcoord i
  rw [hqk] at hi
  exact_mod_cast hi

/-- Primitive integral representatives of the same rational projective point
are equal up to the only integral units, `1` and `-1`. -/
theorem primitive_eq_or_eq_neg {x y : ι → ℤ}
    (hx : IsPrimitive x) (hy : IsPrimitive y)
    (hproj : ProjectivelyEquivalent (intCastVec x) (intCastVec y)) :
    x = y ∨ x = -y := by
  obtain ⟨q, hq, hxy⟩ := hproj
  obtain ⟨k, hqk, hk⟩ := scalar_is_integer_of_primitive hy hxy
  obtain ⟨u, hu⟩ := hx
  let t : ℤ := ∑ i, u i * y i
  have hkt : k * t = 1 := by
    calc
      k * t = ∑ i, u i * (k * y i) := by
        simp only [t]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ i, u i * x i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hk]
      _ = 1 := hu
  have hkunit : IsUnit k := isUnit_iff_dvd_one.mpr ⟨t, hkt.symm⟩
  rcases Int.isUnit_eq_one_or hkunit with hkone | hkneg
  · left
    funext i
    rw [hk i, hkone, one_mul]
  · right
    funext i
    rw [hk i, hkneg]
    simp

/-- Normalizing projectively equivalent rational vectors gives the same
primitive vector up to sign. -/
theorem normalize_eq_or_eq_neg_of_projectivelyEquivalent
    {x y : ι → ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : ProjectivelyEquivalent x y) :
    normalize x = normalize y ∨ normalize x = -normalize y := by
  apply primitive_eq_or_eq_neg (normalize_primitive hx) (normalize_primitive hy)
  exact ((projectivelyEquivalent_normalize hx).symm.trans hxy).trans
    (projectivelyEquivalent_normalize hy)

/-! ## A primitive representative chosen for each projective point -/

theorem intCastVec_ne_zero {z : ι → ℤ} (hz : z ≠ 0) : intCastVec z ≠ 0 := by
  intro h
  apply hz
  apply intCastVec_injective
  have hzero : intCastVec (0 : ι → ℤ) = 0 := by
    funext i
    rfl
  exact h.trans hzero.symm

/-- A primitive integral representative of a rational projective point. -/
noncomputable def projectiveNormalize
    (p : Projectivization ℚ (ι → ℚ)) : ι → ℤ :=
  normalize p.rep

theorem projectiveNormalize_primitive (p : Projectivization ℚ (ι → ℚ)) :
    IsPrimitive (projectiveNormalize p) :=
  normalize_primitive p.rep_nonzero

theorem projectiveNormalize_ne_zero (p : Projectivization ℚ (ι → ℚ)) :
    projectiveNormalize p ≠ 0 :=
  (projectiveNormalize_primitive p).ne_zero

theorem intCast_projectiveNormalize_ne_zero
    (p : Projectivization ℚ (ι → ℚ)) :
    intCastVec (projectiveNormalize p) ≠ 0 :=
  intCastVec_ne_zero (projectiveNormalize_ne_zero p)

/-- The chosen integral vector represents the projective point from which it
was constructed. -/
theorem mk_projectiveNormalize (p : Projectivization ℚ (ι → ℚ)) :
    Projectivization.mk ℚ (intCastVec (projectiveNormalize p))
      (intCast_projectiveNormalize_ne_zero p) = p := by
  have hmk :
      Projectivization.mk ℚ p.rep p.rep_nonzero =
        Projectivization.mk ℚ (intCastVec (projectiveNormalize p))
          (intCast_projectiveNormalize_ne_zero p) := by
    apply (Projectivization.mk_eq_mk_iff' ℚ p.rep
      (intCastVec (projectiveNormalize p)) p.rep_nonzero
      (intCast_projectiveNormalize_ne_zero p)).2
    exact ⟨normalizationScale p.rep, (eq_normalizationScale_smul p.rep).symm⟩
  exact hmk.symm.trans p.mk_rep

/-- Distinct rational projective points have distinct chosen primitive
integral representatives. -/
theorem projectiveNormalize_injective :
    Function.Injective
      (projectiveNormalize : Projectivization ℚ (ι → ℚ) → ι → ℤ) := by
  intro p q hpq
  rw [← mk_projectiveNormalize p, ← mk_projectiveNormalize q]
  congr

/-- Every fibre of the primitive-representative map contains at most one
projective point. -/
theorem projectiveNormalize_fiber_subsingleton (z : ι → ℤ) :
    ({p : Projectivization ℚ (ι → ℚ) | projectiveNormalize p = z} : Set _).Subsingleton := by
  intro p hp q hq
  exact projectiveNormalize_injective (hp.trans hq.symm)

/-- Pulling back a finite collection of primitive vectors gives a finite
collection of projective points. -/
theorem finite_preimage_projectiveNormalize {S : Set (ι → ℤ)} (hS : S.Finite) :
    {p : Projectivization ℚ (ι → ℚ) | projectiveNormalize p ∈ S}.Finite := by
  exact hS.preimage projectiveNormalize_injective.injOn

end Erdos407.Primitive
