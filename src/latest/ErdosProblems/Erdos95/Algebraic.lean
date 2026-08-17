/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Algebraic lemmas for Erdős Problem 95

This file contains the elementary algebraic input to the polynomial-partitioning
argument: a polynomial restricted to an affine line has degree at most the
total degree of the original polynomial, and therefore a line not contained in
the zero set has at most that many intersections with it.
-/

open scoped BigOperators

namespace Erdos95.Algebraic

/-- Restriction of a multivariate polynomial to the affine line `x + t • v`. -/
noncomputable def lineRestriction {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) (x v : ι → ℝ) : Polynomial ℝ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)) p

theorem eval_lineRestriction {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) (x v : ι → ℝ) (t : ℝ) :
    (lineRestriction p x v).eval t =
      MvPolynomial.eval (fun i => x i + t * v i) p := by
  change Polynomial.evalRingHom t
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)) p) = _
  rw [MvPolynomial.map_eval₂Hom]
  apply MvPolynomial.eval₂Hom_congr
  · ext r
    change Polynomial.eval t (Polynomial.C r) = r
    exact Polynomial.eval_C
  · funext i
    change Polynomial.eval t
      (Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)) = _
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_C]
  · rfl

private theorem natDegree_linear {ι : Type*} (x v : ι → ℝ) (i : ι) :
    (Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)).natDegree ≤ 1 := by
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simp only [Polynomial.natDegree_C]
    omega
  · exact Polynomial.natDegree_mul_le.trans (by simp)

/-- Substitution of affine-linear polynomials does not increase total degree. -/
theorem natDegree_lineRestriction {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) (x v : ι → ℝ) :
    (lineRestriction p x v).natDegree ≤ p.totalDegree := by
  rw [lineRestriction]
  conv_lhs => rw [p.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  rw [MvPolynomial.eval₂Hom_monomial]
  have hprod :
      (d.prod fun i k =>
        (Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)) ^ k).natDegree ≤
        d.sum fun _ k => k := by
    rw [Finsupp.prod, Finsupp.sum]
    exact (Polynomial.natDegree_prod_le d.support _).trans <| by
      apply Finset.sum_le_sum
      intro i hi
      exact Polynomial.natDegree_pow_le.trans <| by
        simpa using Nat.mul_le_mul_left (d i) (natDegree_linear x v i)
  calc
    _ ≤ (Polynomial.C (MvPolynomial.coeff d p)).natDegree +
        (d.prod fun i k =>
          (Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)) ^ k).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + d.sum fun _ k => k := add_le_add (by simp) hprod
    _ = d.sum fun _ k => k := Nat.zero_add _
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd

/-- A finite collection of distinct parameters at which a nonzero line
restriction vanishes has cardinality at most the total degree. -/
theorem card_line_zeros_le_totalDegree {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) (x v : ι → ℝ) (S : Finset ℝ)
    (hp : lineRestriction p x v ≠ 0)
    (hS : ∀ t ∈ S, MvPolynomial.eval (fun i => x i + t * v i) p = 0) :
    S.card ≤ p.totalDegree := by
  have hsub : S ⊆ (lineRestriction p x v).roots.toFinset := by
    intro t ht
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot,
      eval_lineRestriction]
    exact hS t ht
  calc
    S.card ≤ (lineRestriction p x v).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ (lineRestriction p x v).roots.card := Multiset.toFinset_card_le _
    _ ≤ (lineRestriction p x v).natDegree := Polynomial.card_roots' _
    _ ≤ p.totalDegree := natDegree_lineRestriction p x v

/-- An affine line is contained in a polynomial zero set exactly when the
univariate restriction of the polynomial to that line is zero. -/
def LineContained {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) (x v : ι → ℝ) : Prop :=
  lineRestriction p x v = 0

theorem lineContained_iff {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) (x v : ι → ℝ) :
    LineContained p x v ↔
      ∀ t : ℝ, MvPolynomial.eval (fun i ↦ x i + t * v i) p = 0 := by
  constructor
  · intro h t
    unfold LineContained at h
    have ht := congrArg (fun q : Polynomial ℝ ↦ q.eval t) h
    simpa only [eval_lineRestriction, Polynomial.eval_zero] using ht
  · intro h
    unfold LineContained
    apply Polynomial.funext
    intro t
    simpa only [eval_lineRestriction, Polynomial.eval_zero] using h t

/-- Line Bézout in dichotomy form: a line is contained in the surface, or
any prescribed finite collection of intersections has size at most the total
degree. -/
theorem lineContained_or_card_zeros_le_totalDegree {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) (x v : ι → ℝ) (S : Finset ℝ)
    (hS : ∀ t ∈ S, MvPolynomial.eval (fun i ↦ x i + t * v i) p = 0) :
    LineContained p x v ∨ S.card ≤ p.totalDegree := by
  by_cases hp : lineRestriction p x v = 0
  · exact Or.inl hp
  · exact Or.inr (card_line_zeros_le_totalDegree p x v S hp hS)

theorem lineRestriction_mul {ι : Type*} [Fintype ι]
    (p q : MvPolynomial ι ℝ) (x v : ι → ℝ) :
    lineRestriction (p * q) x v = lineRestriction p x v * lineRestriction q x v := by
  exact map_mul _ p q

/-- A line lies in the zero set of a product precisely when it lies in the
zero set of at least one factor.  This is the factor-by-factor reduction used
for ruled and unruled components. -/
theorem lineContained_mul_iff {ι : Type*} [Fintype ι]
    (p q : MvPolynomial ι ℝ) (x v : ι → ℝ) :
    LineContained (p * q) x v ↔ LineContained p x v ∨ LineContained q x v := by
  change lineRestriction (p * q) x v = 0 ↔
    lineRestriction p x v = 0 ∨ lineRestriction q x v = 0
  rw [lineRestriction_mul, mul_eq_zero]

/-! ## Low-degree interpolation in three variables -/

/-- Coefficient indices for the box of monomials whose three individual
degrees are at most `k`. -/
abbrev CoeffIndex (k : ℕ) := Fin 3 → Fin (k + 1)

noncomputable def exponent {k : ℕ} (e : CoeffIndex k) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (e i : ℕ))

theorem exponent_injective {k : ℕ} : Function.Injective (@exponent k) := by
  intro e f h
  funext i
  apply Fin.ext
  have hi := congrArg (fun d : Fin 3 →₀ ℕ => d i) h
  simpa [exponent] using hi

noncomputable def boxMonomial {k : ℕ} (e : CoeffIndex k) :
    MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.monomial (exponent e) 1

theorem boxMonomial_linearIndependent (k : ℕ) :
    LinearIndependent ℝ (@boxMonomial k) := by
  change LinearIndependent ℝ
    (fun e : CoeffIndex k => MvPolynomial.monomial (exponent e) 1)
  exact (MvPolynomial.basisMonomials (Fin 3) ℝ).linearIndependent.comp
    (@exponent k) exponent_injective

noncomputable def polynomialOfCoefficients (k : ℕ) :
    (CoeffIndex k → ℝ) →ₗ[ℝ] MvPolynomial (Fin 3) ℝ :=
  Fintype.linearCombination ℝ (@boxMonomial k)

theorem polynomialOfCoefficients_injective (k : ℕ) :
    Function.Injective (polynomialOfCoefficients k) :=
  (boxMonomial_linearIndependent k).fintypeLinearCombination_injective

private noncomputable def evalLinear (z : Fin 3 → ℝ) :
    MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ :=
  (MvPolynomial.aeval z).toLinearMap

private noncomputable def evalOn (S : Finset (Fin 3 → ℝ)) :
    MvPolynomial (Fin 3) ℝ →ₗ[ℝ] (S → ℝ) :=
  LinearMap.pi (fun z : S => evalLinear z.1)

private theorem evalOn_apply (S : Finset (Fin 3 → ℝ))
    (p : MvPolynomial (Fin 3) ℝ) (z : S) :
    evalOn S p z = MvPolynomial.eval z.1 p := by
  simp [evalOn, evalLinear, MvPolynomial.aeval_def]

private noncomputable def coefficientEvaluation
    (S : Finset (Fin 3 → ℝ)) (k : ℕ) :
    (CoeffIndex k → ℝ) →ₗ[ℝ] (S → ℝ) :=
  (evalOn S).comp (polynomialOfCoefficients k)

private theorem exists_interpolating_coefficients
    (S : Finset (Fin 3 → ℝ)) (k : ℕ)
    (hcard : S.card < (k + 1) ^ 3) :
    ∃ c : CoeffIndex k → ℝ, c ≠ 0 ∧ coefficientEvaluation S k c = 0 := by
  have hfin_dom : Module.finrank ℝ (CoeffIndex k → ℝ) = (k + 1) ^ 3 := by
    rw [Module.finrank_pi]
    simp [CoeffIndex]
  have hfin_cod : Module.finrank ℝ (S → ℝ) = S.card := by
    rw [Module.finrank_pi]
    simp
  have hnotinj : ¬ Function.Injective (coefficientEvaluation S k) := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [hfin_dom, hfin_cod] at hle
    omega
  have hex : ∃ a b,
      coefficientEvaluation S k a = coefficientEvaluation S k b ∧ a ≠ b := by
    by_contra h
    apply hnotinj
    intro a b hab
    by_contra hne
    exact h ⟨a, b, hab, hne⟩
  obtain ⟨a, b, hab, hne⟩ := hex
  refine ⟨a - b, sub_ne_zero.mpr hne, ?_⟩
  rw [map_sub, hab, sub_self]

theorem totalDegree_boxMonomial_le (k : ℕ) (e : CoeffIndex k) :
    (boxMonomial e).totalDegree ≤ 3 * k := by
  rw [boxMonomial, MvPolynomial.totalDegree_monomial _ one_ne_zero]
  rw [Finsupp.sum_fintype (exponent e) (fun _ n => n) (fun _ => rfl)]
  calc
    ∑ i, exponent e i ≤ ∑ _i : Fin 3, k := by
      apply Finset.sum_le_sum
      intro i hi
      change (e i).val ≤ k
      omega
    _ = 3 * k := by simp

theorem totalDegree_polynomialOfCoefficients_le
    (k : ℕ) (c : CoeffIndex k → ℝ) :
    (polynomialOfCoefficients k c).totalDegree ≤ 3 * k := by
  rw [polynomialOfCoefficients, Fintype.linearCombination_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e he
  exact (MvPolynomial.totalDegree_smul_le _ _).trans
    (totalDegree_boxMonomial_le k e)

/-- Interpolation in a monomial box: fewer than `(k+1)^3` prescribed
points in three-space lie on a nonzero polynomial surface of total degree at
most `3k`.  The nonzero conclusion is proved from linear independence of
the monomials, rather than merely from a nonzero coefficient vector. -/
theorem exists_interpolating_polynomial
    (S : Finset (Fin 3 → ℝ)) (k : ℕ)
    (hcard : S.card < (k + 1) ^ 3) :
    ∃ p : MvPolynomial (Fin 3) ℝ,
      p ≠ 0 ∧ p.totalDegree ≤ 3 * k ∧
        ∀ z ∈ S, MvPolynomial.eval z p = 0 := by
  obtain ⟨c, hc, hce⟩ := exists_interpolating_coefficients S k hcard
  refine ⟨polynomialOfCoefficients k c,
    fun hp => hc (polynomialOfCoefficients_injective k
      (hp.trans (map_zero _).symm)),
    totalDegree_polynomialOfCoefficients_le k c, ?_⟩
  intro z hz
  let zsub : S := ⟨z, hz⟩
  have hpoint := congrFun hce zsub
  change evalOn S (polynomialOfCoefficients k c) zsub = 0 at hpoint
  simpa only [evalOn_apply] using hpoint

end Erdos95.Algebraic
