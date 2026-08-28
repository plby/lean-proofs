import Wikipedia.NoExoticSixSphere.QuaternionicHopfPolynomial

/-!
# Quaternionic projection identities for the actual Hopf map

The matrix with rows `(1+t,z)` and `(conjugate(z),1-t)` is twice
the rank-one projection associated with a unit point `(t,z)` of `S⁴`.
Its image satisfies two linear equations. On unit quaternion pairs,
these equations recover the literal Hopf polynomial, not just its fiber type.
-/

noncomputable section

open scoped Quaternion

namespace NoExoticSixSphere.QuaternionicHopf

def projectedFirst (t : ℝ) (z a b : ℍ) : ℍ := (1 + t) • a + z * b

def projectedSecond (t : ℝ) (z a b : ℍ) : ℍ := star z * a + (1 - t) • b

theorem projectedFirst_relation (t : ℝ) (z a b : ℍ)
    (h : t ^ 2 + Quaternion.normSq z = 1) :
    (1 - t) • projectedFirst t z a b = z * projectedSecond t z a b := by
  have hc : (1 - t) * (1 + t) = Quaternion.normSq z := by nlinarith
  simp only [projectedFirst, projectedSecond, smul_add, smul_smul, mul_add,
    ← mul_assoc, Quaternion.self_mul_star, Quaternion.coe_mul_eq_smul,
    mul_smul_comm, hc]

theorem projectedSecond_relation (t : ℝ) (z a b : ℍ)
    (h : t ^ 2 + Quaternion.normSq z = 1) :
    (1 + t) • projectedSecond t z a b = star z * projectedFirst t z a b := by
  have hc : (1 + t) * (1 - t) = Quaternion.normSq z := by nlinarith
  simp only [projectedFirst, projectedSecond, smul_add, smul_smul, mul_add,
    ← mul_assoc, Quaternion.star_mul_self, Quaternion.coe_mul_eq_smul,
    mul_smul_comm, hc]

theorem re_mul_swap (a b : ℍ) : (a * b).re = (b * a).re := by
  simp only [Quaternion.re_mul]
  ring

theorem eigen_head (t : ℝ) (z a b : ℍ)
    (ha : (1 - t) • a = z * b) (hb : (1 + t) • b = star z * a)
    (hn : Quaternion.normSq a + Quaternion.normSq b = 1) :
    Quaternion.normSq a - Quaternion.normSq b = t := by
  have h₁ := congrArg (fun q : ℍ ↦ (q * star a).re) ha
  have h₂ := congrArg (fun q : ℍ ↦ (b * star q).re) hb
  have he : (z * b * star a).re = (b * (star a * z)).re := by
    rw [mul_assoc, re_mul_swap, mul_assoc]
  simp only [smul_mul_assoc, Quaternion.self_mul_star, Quaternion.re_smul,
    Quaternion.re_coe, smul_eq_mul] at h₁
  simp only [Quaternion.star_smul, mul_smul_comm, Quaternion.self_mul_star,
    Quaternion.re_smul, Quaternion.re_coe, smul_eq_mul, star_mul, star_star] at h₂
  rw [he] at h₁
  have htn := congrArg (fun r : ℝ ↦ t * r) hn
  nlinarith only [h₁, h₂, htn]

theorem eigen_tail (t : ℝ) (z a b : ℍ)
    (ha : (1 - t) • a = z * b) (hb : (1 + t) • b = star z * a)
    (hn : Quaternion.normSq a + Quaternion.normSq b = 1) :
    (2 : ℝ) • (a * star b) = z := by
  have h₁ : (1 - t) • (a * star b) = Quaternion.normSq b • z := by
    have hh := congrArg (fun q : ℍ ↦ q * star b) ha
    simpa only [smul_mul_assoc, mul_assoc, Quaternion.self_mul_star,
      Quaternion.mul_coe_eq_smul] using hh
  have h₂ : (1 + t) • (a * star b) = Quaternion.normSq a • z := by
    have hh := congrArg (fun q : ℍ ↦ a * star q) hb
    simpa only [Quaternion.star_smul, mul_smul_comm, star_mul, star_star,
      ← mul_assoc, Quaternion.self_mul_star, Quaternion.coe_mul_eq_smul] using hh
  calc
    (2 : ℝ) • (a * star b) = ((1 - t) + (1 + t)) • (a * star b) := by
      congr 1
      ring
    _ = (Quaternion.normSq b + Quaternion.normSq a) • z := by
      rw [add_smul, h₁, h₂, ← add_smul]
    _ = z := by rw [add_comm, hn, one_smul]

theorem projectedFirst_self (a b : ℍ)
    (hn : Quaternion.normSq a + Quaternion.normSq b = 1) :
    projectedFirst (Quaternion.normSq a - Quaternion.normSq b)
      ((2 : ℝ) • (a * star b)) a b = (2 : ℝ) • a := by
  have hc : 1 + (Quaternion.normSq a - Quaternion.normSq b) +
      2 * Quaternion.normSq b = 2 := by linarith
  simp only [projectedFirst, smul_mul_assoc, mul_assoc, Quaternion.star_mul_self,
    Quaternion.mul_coe_eq_smul, smul_smul, ← add_smul, hc]

theorem projectedSecond_self (a b : ℍ)
    (hn : Quaternion.normSq a + Quaternion.normSq b = 1) :
    projectedSecond (Quaternion.normSq a - Quaternion.normSq b)
      ((2 : ℝ) • (a * star b)) a b = (2 : ℝ) • b := by
  have hc : 2 * Quaternion.normSq a +
      (1 - (Quaternion.normSq a - Quaternion.normSq b)) = 2 := by linarith
  simp only [projectedSecond, Quaternion.star_smul, star_mul, star_star,
    smul_mul_assoc, mul_assoc, Quaternion.star_mul_self,
    Quaternion.mul_coe_eq_smul, smul_smul, ← add_smul, hc]

end NoExoticSixSphere.QuaternionicHopf
