import Wikipedia.HopfProblem.UnitQuaternionSphere
import Mathlib.Topology.Homotopy.Basic

/-!
# Complex coordinate powers on the punctured quaternion space

The two complex coordinates are the usual expression `q = z + w j`.
Every quaternion power has imaginary part a real scalar times the original
imaginary part. The scalar is a polynomial, defined recursively here.
-/

noncomputable section

open scoped Topology Quaternion unitInterval

namespace Wikipedia.HopfProblem.QuaternionCoordinatePowers

abbrev Punctured := {q : ℍ // q ≠ 0}

def first (q : ℍ) : ℂ := ⟨q.re, q.imI⟩

def second (q : ℍ) : ℂ := ⟨q.imJ, q.imK⟩

def pair (z w : ℂ) : ℍ := ⟨z.re, z.im, w.re, w.im⟩

@[simp] theorem first_pair (z w : ℂ) : first (pair z w) = z := rfl

@[simp] theorem second_pair (z w : ℂ) : second (pair z w) = w := rfl

@[simp] theorem pair_coordinates (q : ℍ) : pair (first q) (second q) = q := rfl

@[simp] theorem first_zero : first 0 = 0 := rfl

@[simp] theorem second_zero : second 0 = 0 := rfl

@[simp] theorem pair_zero : pair 0 0 = 0 := rfl

theorem pair_eq_zero_iff (z w : ℂ) : pair z w = 0 ↔ z = 0 ∧ w = 0 := by
  constructor
  · intro h
    exact ⟨congrArg first h, congrArg second h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem coordinates_ne_zero (q : Punctured) : first q.val ≠ 0 ∨ second q.val ≠ 0 := by
  by_cases h : first q.val = 0
  · right
    intro hs
    exact q.property (by rw [← pair_coordinates q.val, h, hs, pair_zero])
  · exact Or.inl h

theorem first_continuous : Continuous first := by
  have h := Complex.continuous_ofReal.comp Quaternion.continuous_re |>.add
    ((Complex.continuous_ofReal.comp Quaternion.continuous_imI).mul_const Complex.I)
  apply h.congr
  intro q
  apply Complex.ext <;> simp [first]

theorem second_continuous : Continuous second := by
  have h := Complex.continuous_ofReal.comp Quaternion.continuous_imJ |>.add
    ((Complex.continuous_ofReal.comp Quaternion.continuous_imK).mul_const Complex.I)
  apply h.congr
  intro q
  apply Complex.ext <;> simp [second]

theorem pair_continuous : Continuous (fun p : ℂ × ℂ => pair p.1 p.2) := by
  have hc : Continuous Quaternion.ofComplex :=
    Quaternion.ofComplex.toLinearMap.continuous_of_finiteDimensional
  have h := (hc.comp continuous_fst).add
    ((hc.comp continuous_snd).mul_const (pair 0 1))
  apply h.congr
  intro p
  change Quaternion.ofComplex p.1 + Quaternion.ofComplex p.2 * pair 0 1 = pair p.1 p.2
  change (p.1 : ℍ) + (p.2 : ℍ) * pair 0 1 = pair p.1 p.2
  apply QuaternionAlgebra.ext
  · change (↑p.1 + ↑p.2 * pair 0 1 : ℍ).re = p.1.re
    rw [Quaternion.re_add, Quaternion.re_mul]
    simp [pair]
  · change (↑p.1 + ↑p.2 * pair 0 1 : ℍ).imI = p.1.im
    rw [Quaternion.imI_add, Quaternion.imI_mul]
    simp [pair]
  · change (↑p.1 + ↑p.2 * pair 0 1 : ℍ).imJ = p.2.re
    rw [Quaternion.imJ_add, Quaternion.imJ_mul]
    simp [pair]
  · change (↑p.1 + ↑p.2 * pair 0 1 : ℍ).imK = p.2.im
    rw [Quaternion.imK_add, Quaternion.imK_mul]
    simp [pair]

def powerCoefficient : ℕ → ℍ → ℝ
  | 0, _ => 0
  | n + 1, q => (q ^ n).re + powerCoefficient n q * q.re

theorem powerCoefficient_continuous (n : ℕ) : Continuous (powerCoefficient n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact (Quaternion.continuous_re.comp (continuous_id.pow n)).add
      (ih.mul Quaternion.continuous_re)

theorem power_imaginary (n : ℕ) (q : ℍ) :
    (q ^ n).imI = powerCoefficient n q * q.imI ∧
    (q ^ n).imJ = powerCoefficient n q * q.imJ ∧
    (q ^ n).imK = powerCoefficient n q * q.imK := by
  induction n with
  | zero => simp [powerCoefficient]
  | succ n ih =>
    rw [pow_succ]
    simp only [Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      ih.1, ih.2.1, ih.2.2, powerCoefficient]
    constructor
    · ring
    constructor <;> ring

theorem second_pow (n : ℕ) (q : ℍ) :
    second (q ^ n) = (powerCoefficient n q : ℂ) * second q := by
  apply Complex.ext
  · simpa only [second, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using (power_imaginary n q).2.1
  · simpa only [second, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using (power_imaginary n q).2.2

theorem pair_zero_second (z : ℂ) : pair z 0 = Quaternion.ofComplex z := rfl

theorem first_pow_of_second_zero (n : ℕ) (q : ℍ) (h : second q = 0) :
    first (q ^ n) = first q ^ n := by
  have hq : q = Quaternion.ofComplex (first q) := by
    rw [← pair_zero_second, ← h, pair_coordinates]
  calc
    first (q ^ n) = first (Quaternion.ofComplex (first q) ^ n) := congrArg (fun a => first (a ^ n)) hq
    _ = first (Quaternion.ofComplex (first q ^ n)) := congrArg first (map_pow Quaternion.ofComplex _ _).symm
    _ = first q ^ n := rfl

def firstPower (n : ℕ) : C(Punctured, Punctured) where
  toFun q := ⟨pair (first q.val ^ n) (second q.val), by
    intro h
    obtain ⟨h₁, h₂⟩ := (pair_eq_zero_iff _ _).mp h
    rcases coordinates_ne_zero q with hn | hn
    · exact (pow_ne_zero n hn) h₁
    · exact hn h₂⟩
  continuous_toFun :=
    (pair_continuous.comp (((first_continuous.comp continuous_subtype_val).pow n).prodMk
      (second_continuous.comp continuous_subtype_val))).subtype_mk _

def quaternionPower (n : ℕ) : C(Punctured, Punctured) where
  toFun q := ⟨q.val ^ n, pow_ne_zero n q.property⟩
  continuous_toFun := (continuous_subtype_val.pow n).subtype_mk _

end Wikipedia.HopfProblem.QuaternionCoordinatePowers
