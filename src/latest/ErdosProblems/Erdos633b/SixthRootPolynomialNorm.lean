import ErdosProblems.Erdos633b.CosinePolynomialLifts

/-! A positive rational polynomial norm for coefficients in the sixth
root of unity, with exact degree and primitive-root consequences. -/

namespace Erdos633b
open Polynomial

noncomputable def sixthRootPolynomialNorm (p q : ℚ[X]) : ℚ[X] := p ^ 2 + p * q + q ^ 2

theorem sixthRootPolynomialNorm_zero_iff (p q : ℚ[X]) :
    sixthRootPolynomialNorm p q = 0 ↔ p = 0 ∧ q = 0 := by
  constructor
  · intro h
    have he (t : ℚ) : p.eval t = 0 ∧ q.eval t = 0 := by
      have hh := congrArg (fun f : ℚ[X] => f.eval t) h
      simp only [sixthRootPolynomialNorm, eval_add, eval_mul, eval_pow, eval_zero] at hh
      have hq : q.eval t = 0 := by
        nlinarith [sq_nonneg (2 * p.eval t + q.eval t), sq_nonneg (q.eval t)]
      exact ⟨by nlinarith [sq_nonneg (p.eval t)], hq⟩
    constructor
    · apply Polynomial.funext
      intro t
      simpa only [eval_zero] using (he t).1
    · apply Polynomial.funext
      intro t
      simpa only [eval_zero] using (he t).2
  · rintro ⟨rfl, rfl⟩
    simp [sixthRootPolynomialNorm]

theorem sixthRootPolynomialNorm_degree (p q : ℚ[X]) (L : ℕ)
    (hp : p.natDegree ≤ L) (hq : q.natDegree ≤ L) :
    (sixthRootPolynomialNorm p q).natDegree ≤ 2 * L := by
  have hp2 : (p ^ 2).natDegree ≤ 2 * L := by
    have hh : (p ^ 2).natDegree ≤ 2 * p.natDegree := natDegree_pow_le
    omega
  have hq2 : (q ^ 2).natDegree ≤ 2 * L := by
    have hh : (q ^ 2).natDegree ≤ 2 * q.natDegree := natDegree_pow_le
    omega
  have hpq : (p * q).natDegree ≤ 2 * L := by
    have hh : (p * q).natDegree ≤ p.natDegree + q.natDegree := natDegree_mul_le
    omega
  unfold sixthRootPolynomialNorm
  exact (natDegree_add_le _ _).trans (max_le
    ((natDegree_add_le _ _).trans (max_le hp2 hpq)) hq2)

theorem sixthRootPolynomialNorm_aeval_zero (ω z : ℂ) (hω : ω ^ 2 - ω + 1 = 0)
    (p q : ℚ[X]) (hg : aeval z p + ω * aeval z q = 0) :
    aeval z (sixthRootPolynomialNorm p q) = 0 := by
  simp only [sixthRootPolynomialNorm, map_add, map_mul, map_pow]
  linear_combination (aeval z p + (1 - ω) * aeval z q) * hg + (aeval z q) ^ 2 * hω

theorem sixth_root_polynomials_zero_of_degree (D : ℕ) (hD : 0 < D)
    (z : ℂ) (hz : IsPrimitiveRoot z D) (ω : ℂ) (hω : ω ^ 2 - ω + 1 = 0)
    (p q : ℚ[X]) (L : ℕ) (hp : p.natDegree ≤ L) (hq : q.natDegree ≤ L)
    (hdeg : 2 * L < D.totient) (he : aeval z p + ω * aeval z q = 0) : p = 0 ∧ q = 0 := by
  apply (sixthRootPolynomialNorm_zero_iff p q).mp
  exact zero_of_primitive_root_and_small_degree D hD z hz _
    (sixthRootPolynomialNorm_aeval_zero ω z hω p q he)
    ((sixthRootPolynomialNorm_degree p q L hp hq).trans_lt hdeg)

end Erdos633b
