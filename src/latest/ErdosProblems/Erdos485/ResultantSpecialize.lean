import ErdosProblems.Erdos485.Bivariate
import ErdosProblems.Erdos485.ResultantDegree
import ErdosProblems.Erdos485.ResultantGap

/-!
# Specializing the resultant identity

This file packages the exact elimination argument used in the positive outer-degree branch of
Schinzel's squarefree-gap lemma.  Coprimality is required only after passing from `K[z]` to its
fraction field; the Sylvester-adjugate identity is then specialized at `y = x^n`.
-/

namespace Erdos485

open Polynomial

noncomputable section

@[simp] theorem specialize_eq_eval {K : Type*} [CommSemiring K]
    (n : ℕ) (H : BiPolynomial K) :
    specialize n H = H.eval (X ^ n) := by
  rfl

/-- The resultant-specialization degree squeeze.  This is the direct interface needed after
the weighted Euler construction: `D` has no larger bidegree than `H`, the two polynomials are
coprime over `K(z)`, and `H(x^n,x)` divides `D(x^n,x)^2`. -/
theorem resultant_specialize_le_four_mul
    {K : Type*} [Field K]
    (H D : BiPolynomial K) (n dZ : ℕ)
    (hH : H ≠ 0)
    (hHy : 0 < H.natDegree)
    (hDy : D.natDegree ≤ H.natDegree)
    (hHz : maxCoeffDegree H ≤ dZ)
    (hDz : maxCoeffDegree D ≤ dZ)
    (hcop : IsCoprime
      (H.map (algebraMap (Polynomial K) (FractionRing (Polynomial K))))
      (D.map (algebraMap (Polynomial K) (FractionRing (Polynomial K)))))
    (hdiv : specialize n H ∣ (specialize n D) ^ 2)
    (hdeg : ZDegreeLT n H) :
    n ≤ 4 * dZ := by
  let dY := H.natDegree
  let R : Polynomial K := H.resultant D
  have hR0 : R ≠ 0 := by
    exact resultant_ne_zero_of_isCoprime_fractionRing H D hcop
  have hn : 0 < n := by
    exact Nat.zero_lt_of_lt
      (hdeg H.natDegree (Polynomial.natDegree_mem_support_of_nonzero hH))
  have hcoeff : ∀ i, (H.coeff i).natDegree < n := by
    intro i
    by_cases hi : i ∈ H.support
    · exact hdeg i hi
    · rw [not_ne_iff.mp (mt Polynomial.mem_support_iff.mpr hi)]
      exact hn
  have hlower : n * dY ≤ (specialize n H).natDegree := by
    rw [specialize_eq_eval]
    exact mul_natDegree_le_natDegree_eval_X_pow H n hH hcoeff
  have hRdeg : R.natDegree ≤ 2 * dY * dZ := by
    calc
      R.natDegree ≤
          H.natDegree * maxCoeffDegree D + D.natDegree * maxCoeffDegree H :=
        natDegree_resultant_le_maxCoeffDegree H D
      _ ≤ dY * dZ + dY * dZ := by
        exact Nat.add_le_add (Nat.mul_le_mul le_rfl hDz) (Nat.mul_le_mul hDy hHz)
      _ = 2 * dY * dZ := by ring
  obtain ⟨A, B, _hAdeg, _hBdeg, hbez⟩ :=
    exists_bivariate_bezout_resultant H D H.natDegree D.natDegree le_rfl le_rfl
      (Or.inl hHy.ne')
  have hbezSpec := congrArg (specialize n) hbez
  simp only [map_add, map_mul] at hbezSpec
  have hbezSpec' :
      specialize n H * specialize n A + specialize n D * specialize n B = R := by
    simpa [R] using hbezSpec
  have hdivR : specialize n H ∣ R ^ 2 := by
    obtain ⟨Q, hQ⟩ := hdiv
    refine ⟨specialize n H * (specialize n A) ^ 2 +
        2 * specialize n A * specialize n D * specialize n B +
        Q * (specialize n B) ^ 2, ?_⟩
    calc
      R ^ 2 =
          (specialize n H * specialize n A +
            specialize n D * specialize n B) ^ 2 := by rw [hbezSpec']
      _ = (specialize n H * specialize n A) ^ 2 +
          2 * (specialize n H * specialize n A) *
            (specialize n D * specialize n B) +
          (specialize n D) ^ 2 * (specialize n B) ^ 2 := by ring
      _ = _ := by rw [hQ]; ring
  have hR20 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR0
  have hmid : (specialize n H).natDegree ≤ (R ^ 2).natDegree :=
    Polynomial.natDegree_le_of_dvd hdivR hR20
  have hupper : (R ^ 2).natDegree ≤ 4 * dY * dZ := by
    calc
      (R ^ 2).natDegree ≤ 2 * R.natDegree := Polynomial.natDegree_pow_le
      _ ≤ 2 * (2 * dY * dZ) := Nat.mul_le_mul_left 2 hRdeg
      _ = 4 * dY * dZ := by ring
  have hmul : n * dY ≤ (4 * dZ) * dY := by
    calc
      n * dY ≤ (specialize n H).natDegree := hlower
      _ ≤ (R ^ 2).natDegree := hmid
      _ ≤ 4 * dY * dZ := hupper
      _ = (4 * dZ) * dY := by ring
  exact Nat.le_of_mul_le_mul_right hmul hHy

/-! ## Removing a unit squarefree cofactor -/

/-- If a bivariate polynomial is associated to a square times a unit, then it is literally a
nonzero scalar times a square.  Both polynomial layers have to be removed: units of `K[z][y]`
are constant in `y`, and units of `K[z]` are nonzero constants in `z`. -/
theorem eq_scalar_mul_sq_of_associated_sq_mul_isUnit
    {K : Type*} [Field K]
    (F A H : BiPolynomial K)
    (hassoc : Associated F (A ^ 2 * H))
    (hH : IsUnit H) :
    ∃ c : K, c ≠ 0 ∧ F = C (C c) * A ^ 2 := by
  have hFA : Associated F (A ^ 2) :=
    hassoc.trans (associated_mul_unit_left (A ^ 2) H hH)
  obtain ⟨u, hu⟩ := hFA.symm
  obtain ⟨p, hp, hpu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  obtain ⟨c, hc, hcp⟩ := Polynomial.isUnit_iff.mp hp
  refine ⟨c, hc.ne_zero, ?_⟩
  rw [← hu, ← hpu, ← hcp]
  ring

end

end Erdos485
