import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticProduct
import Mathlib.Topology.Covering.AddCircle

/-!
# The actual finite circle quotient in the Seifert solid torus

The cyclic generator is translation by `ell/m`.  For the two primitive
twists `ell = ±1`, its actual orbit quotient is the original additive circle,
and the quotient coordinate is exactly multiplication by `m`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticModel

open SpecialPeriods ThreefoldOverlapMappingTorus
open Wikipedia.HopfProblem.Elliptic

/-- The native circle translation, with its signed integral twist. -/
def circleShift (m : ℕ) (ell : ℤ) : Circle ≃ₜ Circle :=
  Homeomorph.addRight (((ell : ℝ) / m : ℝ) : Circle)

@[simp] theorem circleShift_apply (m : ℕ) (ell : ℤ) (c : Circle) :
    circleShift m ell c = c + (((ell : ℝ) / m : ℝ) : Circle) := rfl

theorem circleShift_iterate (m : ℕ) (ell : ℤ) (r : ℕ) (c : Circle) :
    (circleShift m ell : Circle → Circle)^[r] c =
      c + r • (((ell : ℝ) / m : ℝ) : Circle) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, circleShift_apply, succ_nsmul, add_assoc]

theorem circleShift_perm_pow_apply (m : ℕ) (ell : ℤ) (r : ℕ) (c : Circle) :
    ((circleShift m ell).toEquiv ^ r) c =
      c + r • (((ell : ℝ) / m : ℝ) : Circle) := by
  rw [Equiv.Perm.coe_pow]
  exact circleShift_iterate m ell r c

private theorem homeomorphPerm_pow_apply (B : Circle ≃ₜ Circle) (n : ℕ) (c : Circle) :
    (B.toEquiv ^ n) c = (B ^ n) c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', Equiv.Perm.mul_apply, Homeomorph.mul_apply]
    exact congrArg B ih

theorem order_smul_shift (m : ℕ) [NeZero m] (ell : ℤ) :
    m • (((ell : ℝ) / m : ℝ) : Circle) = 0 := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have he : (m : ℝ) * ((ell : ℝ) / m) = ell := by field_simp
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul, he]
  exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨ell, by simp⟩

theorem circleShift_pow_order (m : ℕ) [NeZero m] (ell : ℤ) :
    circleShift m ell ^ m = 1 := by
  apply Homeomorph.ext
  intro c
  rw [← homeomorphPerm_pow_apply, circleShift_perm_pow_apply, order_smul_shift, add_zero]
  rfl

/-- The original degree-`m` circle covering. -/
def circleMultiple (m : ℕ) : C(Circle, Circle) := ⟨fun c => m • c, by fun_prop⟩

theorem circleMultiple_isOpenQuotientMap (m : ℕ) [NeZero m] :
    IsOpenQuotientMap (circleMultiple m) := by
  have h := AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero (1 : ℝ) m
  exact ⟨h.surjective, h.continuous, h.isCoveringMap.isOpenMap⟩

variable (m : ℕ) [NeZero m] (ell : ℤ)

abbrev CircleQuotient := FibreQuotient m (circleShift m ell) (circleShift_pow_order m ell)

def circleProject : Circle → CircleQuotient m ell :=
  fibreProject m (circleShift m ell) (circleShift_pow_order m ell)

theorem circleProject_isOpenQuotientMap : IsOpenQuotientMap (circleProject m ell) :=
  fibreProject_isOpenQuotientMap m (circleShift m ell) (circleShift_pow_order m ell)

omit [NeZero m] in
private theorem nsmul_sector_coe (r : ℕ) :
    r • sector m = (((r : ℝ) / m : ℝ) : Circle) := by
  change r • (((1 : ℝ) / m : ℝ) : Circle) = _
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  congr 1
  ring

/-- Actual orbit equality is exactly equality under the degree-`m` covering. -/
theorem circleProject_eq_iff (hell : ell = 1 ∨ ell = -1) (c d : Circle) :
    circleProject m ell c = circleProject m ell d ↔
      circleMultiple m c = circleMultiple m d := by
  let := fibreAction m (circleShift m ell) (circleShift_pow_order m ell)
  change FiniteQuotient.project (Multiplicative (ZMod m)) Circle c =
    FiniteQuotient.project (Multiplicative (ZMod m)) Circle d ↔ m • c = m • d
  rw [FiniteQuotient.project_eq_iff_mem_orbit]
  constructor
  · rintro ⟨g, hg⟩
    have hp : d + g.toAdd.val • (((ell : ℝ) / m : ℝ) : Circle) = c :=
      (circleShift_perm_pow_apply m ell g.toAdd.val d).symm.trans hg
    rw [← hp, smul_add, smul_comm m g.toAdd.val, order_smul_shift, smul_zero, add_zero]
  · intro h
    have hz : m • (c - d) = 0 := by rw [smul_sub, h, sub_self]
    obtain ⟨r, hr, hc⟩ := (AddCircle.nsmul_eq_zero_iff (p := (1 : ℝ))
      (Nat.pos_of_ne_zero (NeZero.ne m))).mp hz
    have hsector : r • sector m = c - d := by
      rw [nsmul_sector_coe]
      simpa only [mul_one] using hc
    rcases hell with rfl | rfl
    · refine ⟨CyclicAction.generator m ^ r, ?_⟩
      have hs := CyclicAction.generator_pow_smul (circleShift m 1).toEquiv
        (fibrePermutation_pow_order m (circleShift m 1) (circleShift_pow_order m 1)) r d
      change (CyclicAction.generator m ^ r) • d = c
      rw [hs]
      change (circleShift m 1 : Circle → Circle)^[r] d = c
      rw [circleShift_iterate]
      rw [Int.cast_one]
      change d + r • sector m = c
      rw [hsector]
      abel
    · refine ⟨(CyclicAction.generator m ^ r)⁻¹, ?_⟩
      apply (inv_smul_eq_iff).mpr
      have hs := CyclicAction.generator_pow_smul (circleShift m (-1)).toEquiv
        (fibrePermutation_pow_order m (circleShift m (-1)) (circleShift_pow_order m (-1))) r c
      rw [hs]
      symm
      change (circleShift m (-1) : Circle → Circle)^[r] c = d
      rw [circleShift_iterate]
      rw [Int.cast_neg, Int.cast_one]
      change c + r • ((((-1 : ℝ) / m : ℝ)) : Circle) = d
      rw [neg_div, AddCircle.coe_neg, smul_neg]
      change c + -(r • sector m) = d
      rw [hsector]
      abel

/-- Homeomorphism of the genuine circle orbit quotient, with its quotient topology. -/
def circleQuotientHomeomorph (hell : ell = 1 ∨ ell = -1) : CircleQuotient m ell ≃ₜ Circle :=
  quotientHomeomorph (circleProject m ell) (circleMultiple m)
    (circleProject_isOpenQuotientMap m ell).isQuotientMap
    (circleMultiple_isOpenQuotientMap m).isQuotientMap
    (circleProject_eq_iff m ell hell)

@[simp] theorem circleQuotientHomeomorph_project (hell : ell = 1 ∨ ell = -1) (c : Circle) :
    circleQuotientHomeomorph m ell hell (circleProject m ell c) = m • c :=
  quotientHomeomorph_apply _ _ _ _ _ c

theorem circleQuotientHomeomorph_symm_multiple (hell : ell = 1 ∨ ell = -1) (c : Circle) :
    (circleQuotientHomeomorph m ell hell).symm (m • c) = circleProject m ell c :=
  quotientHomeomorph_symm_apply _ _ _ _ _ c

/-- The signed first-circle coordinate used to remove the disc rotation. -/
def signedCoordinate (ell : ℤ) : C(Circle, Circle) := ⟨fun c => ell • c, by fun_prop⟩

@[simp] theorem signedCoordinate_apply (ell : ℤ) (c : Circle) :
    signedCoordinate ell c = ell • c := rfl

omit [NeZero m] in
theorem signedCoordinate_circleShift (hell : ell = 1 ∨ ell = -1) (c : Circle) :
    signedCoordinate ell (circleShift m ell c) = signedCoordinate ell c + sector m := by
  rw [signedCoordinate_apply, signedCoordinate_apply, circleShift_apply]
  rcases hell with rfl | rfl
  · simp only [one_zsmul, Int.cast_one]
    rfl
  · simp only [neg_one_zsmul, Int.cast_neg, Int.cast_one, neg_div, AddCircle.coe_neg]
    change -(c + -sector m) = -c + sector m
    abel

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticModel
