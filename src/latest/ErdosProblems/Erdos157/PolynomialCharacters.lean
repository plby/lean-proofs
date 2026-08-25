import ErdosProblems.Erdos157.PolynomialDivision
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Complex.Basic

/-!
# Polynomial character coefficients

Long division makes every residue class occur equally often among monic
polynomials of any degree at least the modulus degree. Hence a nonprincipal
character's generating series has only finitely many nonzero coefficients.
-/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

/-- A character of a finite unit group has values in the closed unit disk. -/
theorem character_norm_le_one {R : Type*} [CommMonoid R] [Finite Rˣ]
    (χ : MulChar R ℂ) (a : R) : ‖χ a‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    have hp : χ (u : R) ^ Nat.card Rˣ = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one]
    exact (Complex.norm_eq_one_of_pow_eq_one hp Nat.card_pos.ne').le
  · rw [χ.map_nonunit ha, norm_zero]
    exact zero_le_one

/-- Odd-order unit groups have no nonprincipal quadratic character. -/
theorem character_sq_ne_one {R : Type*} [CommMonoid R] [Fintype Rˣ]
    (hodd : Odd (Fintype.card Rˣ)) (χ : MulChar R ℂ) (hχ : χ ≠ 1) : χ ^ 2 ≠ 1 := by
  intro hsq
  obtain ⟨k, hk⟩ := hodd
  have hp := χ.pow_card_eq_one
  have hk' : Fintype.card Rˣ = 2 * k + 1 := by omega
  rw [hk', pow_succ, pow_mul, hsq, one_pow, one_mul] at hp
  exact hχ hp

theorem monic_coefficients_injective (d : ℕ) :
    Function.Injective (fun f : MonicDegreeEq K d => fun i : Fin d => f.1.coeff i) := by
  intro f g h
  apply Subtype.ext
  ext i
  by_cases hi : i < d
  · exact congrFun h ⟨i, hi⟩
  · rw [f.coeff_of_ge i (by omega), g.coeff_of_ge i (by omega)]

instance monicFinite [Finite K] (d : ℕ) : Finite (MonicDegreeEq K d) :=
  Finite.of_injective _ (monic_coefficients_injective d)

noncomputable instance monicFintype [Finite K] (d : ℕ) : Fintype (MonicDegreeEq K d) :=
  Fintype.ofFinite _

/-- Unique bounded-degree representatives for the quotient by a monic polynomial. -/
noncomputable def residueEquiv (g : K[X]) (hg : g.Monic) :
    AdjoinRoot g ≃ {r : K[X] // r.degree < (g.natDegree : WithBot ℕ)} where
  toFun a := ⟨AdjoinRoot.modByMonicHom hg a, by
    induction a using AdjoinRoot.induction_on
    rw [AdjoinRoot.modByMonicHom_mk, ← Polynomial.degree_eq_natDegree hg.ne_zero]
    exact Polynomial.degree_modByMonic_lt _ hg⟩
  invFun r := AdjoinRoot.mk g r.1
  left_inv := AdjoinRoot.mk_leftInverse hg
  right_inv r := by
    apply Subtype.ext
    change r.1 %ₘ g = r.1
    apply (Polynomial.modByMonic_eq_self_iff hg).mpr
    simpa only [Polynomial.degree_eq_natDegree hg.ne_zero] using r.2

/-- A monic polynomial is its residue and a free monic quotient. -/
noncomputable def monicResidueEquiv (g : K[X]) (hg : g.Monic) (d : ℕ)
    (hd : g.natDegree ≤ d) :
    MonicDegreeEq K d ≃ AdjoinRoot g × MonicDegreeEq K (d - g.natDegree) :=
  (PolynomialDivision.monicRemainderQuotientEquiv K g hg rfl hd).trans
    (Equiv.prodCongr (residueEquiv g hg).symm (Equiv.refl _))

theorem monicResidueEquiv_fst (g : K[X]) (hg : g.Monic) (d : ℕ)
    (hd : g.natDegree ≤ d) (f : MonicDegreeEq K d) :
    (monicResidueEquiv g hg d hd f).1 = AdjoinRoot.mk g f.1 := by
  change AdjoinRoot.mk g (f.1 %ₘ g) = AdjoinRoot.mk g f.1
  apply AdjoinRoot.mk_eq_mk.mpr
  exact Polynomial.dvd_modByMonic_sub f.1 g

/-- The degree coefficient of the character's monic-polynomial generating series. -/
noncomputable def coefficient [Finite K] (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ)
    (d : ℕ) : ℂ := ∑ f : MonicDegreeEq K d, χ (AdjoinRoot.mk g f.1)

/-- Monic polynomials have exactly one free coefficient at every lower degree. -/
noncomputable def monicCoefficientsEquiv (d : ℕ) :
    MonicDegreeEq K d ≃ (Fin d → K) :=
  ({ toFun := fun f => ⟨f.1, f.monic, f.natDegree⟩
     invFun := fun f => MonicDegreeEq.mk f.1 f.2.1 f.2.2
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl } :
    MonicDegreeEq K d ≃ {f : K[X] // f.Monic ∧ f.natDegree = d}).trans
      ((Polynomial.monicEquivDegreeLT d).trans (Polynomial.degreeLTEquiv K d).toEquiv)

theorem card_monic [Fintype K] (d : ℕ) :
    Fintype.card (MonicDegreeEq K d) = Fintype.card K ^ d := by
  simpa using Fintype.card_congr (monicCoefficientsEquiv (K := K) d)

theorem coefficient_zero [Finite K] (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ) :
    coefficient g χ 0 = 1 := by
  have hpoly : ∀ f : MonicDegreeEq K 0, f.1 = 1 :=
    fun f => eq_one_of_monic_natDegree_zero f.monic f.natDegree
  have hcard : Fintype.card (MonicDegreeEq K 0) = 1 := by
    let : Fintype K := Fintype.ofFinite _
    rw [card_monic, pow_zero]
  simp only [coefficient, hpoly, map_one, Finset.sum_const,
    Finset.card_univ, hcard, one_smul]

/-- Nonprincipal character coefficients vanish beyond the modulus degree. -/
theorem coefficient_eq_zero [Finite K] (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) (d : ℕ) (hd : g.natDegree ≤ d) :
    coefficient g χ d = 0 := by
  classical
  let : Finite (AdjoinRoot g) :=
    Finite.of_injective (AdjoinRoot.powerBasisAux' hg).equivFun
      (AdjoinRoot.powerBasisAux' hg).equivFun.injective
  let : Fintype (AdjoinRoot g) := Fintype.ofFinite _
  let e := monicResidueEquiv g hg d hd
  have he : coefficient g χ d =
      ∑ p : AdjoinRoot g × MonicDegreeEq K (d - g.natDegree), χ p.1 := by
    have hs := Equiv.sum_comp e (fun p => χ p.1)
    simpa only [e, monicResidueEquiv_fst, coefficient] using hs
  rw [he, Fintype.sum_prod_type]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero]

/-- The finite polynomial equal to the complete monic character series. -/
noncomputable def lPolynomial [Finite K] (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ) : ℂ[X] :=
  ∑ d ∈ Finset.range g.natDegree, Polynomial.monomial d (coefficient g χ d)

theorem lPolynomial_coeff [Finite K] (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ)
    (d : ℕ) :
    (lPolynomial g χ).coeff d = if d < g.natDegree then coefficient g χ d else 0 := by
  simp [lPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]

theorem lPolynomial_coeff_eq [Finite K] (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) (d : ℕ) :
    (lPolynomial g χ).coeff d = coefficient g χ d := by
  rw [lPolynomial_coeff]
  split_ifs with hd
  · rfl
  · exact (coefficient_eq_zero g hg χ hχ d (by omega)).symm

theorem lPolynomial_constantCoeff [Finite K] (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) :
    (lPolynomial g χ).coeff 0 = 1 := by
  rw [lPolynomial_coeff_eq g hg χ hχ, coefficient_zero]

theorem lPolynomial_degree_lt [Finite K] (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ) :
    (lPolynomial g χ).degree < (g.natDegree : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro d hd
  rw [lPolynomial_coeff, if_neg (by omega)]

/-- The elementary absolute bound on every degree coefficient. -/
theorem norm_coefficient_le [Fintype K] (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (d : ℕ) :
    ‖coefficient g χ d‖ ≤ (Fintype.card K : ℝ) ^ d := by
  let : Finite (AdjoinRoot g) :=
    Finite.of_injective (AdjoinRoot.powerBasisAux' hg).equivFun
      (AdjoinRoot.powerBasisAux' hg).equivFun.injective
  calc
    _ ≤ ∑ f : MonicDegreeEq K d, ‖χ (AdjoinRoot.mk g f.1)‖ := norm_sum_le _ _
    _ ≤ ∑ _f : MonicDegreeEq K d, (1 : ℝ) :=
      Finset.sum_le_sum (fun f _ => character_norm_le_one χ _)
    _ = _ := by simp [card_monic]

end Erdos157.Elementary.PolynomialCharacters
