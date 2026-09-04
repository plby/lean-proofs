/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.Algebraic
import ErdosProblems.Erdos95.Geometry
import ErdosProblems.Erdos95.Hilbert
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Low-degree non-clustering for Elekes--Sharir lines

This file develops the polynomial ruling vector field used in Guth's
low-degree proof.  Its first key consequence is completely algebraic: if a
surface contains a line in the ruling with fixed first endpoint, then the
directional derivative of its defining polynomial along the ruling field
contains that line as well.
-/

open scoped BigOperators

namespace Erdos95.NonClustering

open Erdos95.Algebraic
open Erdos95.ES
open Erdos95.Hilbert

abbrev Poly3 := MvPolynomial (Fin 3) ℝ

/-- Polynomial coordinates of `ES.rulingVectorField`. -/
noncomputable def rulingPolynomial (p : PlanePoint) : Fin 3 → Poly3
  | 0 => MvPolynomial.X 2 * MvPolynomial.X 0 + MvPolynomial.X 1 -
      MvPolynomial.X 2 * MvPolynomial.C (p 0) - MvPolynomial.C (p 1)
  | 1 => MvPolynomial.C (p 0) - MvPolynomial.X 0 -
      MvPolynomial.X 2 * MvPolynomial.C (p 1) +
        MvPolynomial.X 2 * MvPolynomial.X 1
  | 2 => 1 + MvPolynomial.X 2 ^ 2

theorem eval_rulingPolynomial (p : PlanePoint) (x : Space3) (i : Fin 3) :
    MvPolynomial.eval x (rulingPolynomial p i) = rulingVectorField p x i := by
  fin_cases i <;> simp [rulingPolynomial, rulingVectorField] <;> ring

/-- The derivation of a polynomial along the ruling vector field. -/
noncomputable def rulingDerivative (p : PlanePoint) : Poly3 → Poly3 :=
  MvPolynomial.mkDerivation ℝ (rulingPolynomial p)

theorem rulingDerivative_add (p : PlanePoint) (Q R : Poly3) :
    rulingDerivative p (Q + R) = rulingDerivative p Q + rulingDerivative p R := by
  exact map_add _ _ _

theorem rulingDerivative_mul (p : PlanePoint) (Q R : Poly3) :
    rulingDerivative p (Q * R) =
      Q * rulingDerivative p R + R * rulingDerivative p Q := by
  exact (MvPolynomial.mkDerivation ℝ (rulingPolynomial p)).leibniz Q R

/-- Partial differentiation cannot increase total degree. -/
theorem totalDegree_pderiv_le {ι : Type*} [Fintype ι]
    (Q : MvPolynomial ι ℝ) (i : ι) :
    (MvPolynomial.pderiv i Q).totalDegree ≤ Q.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro m hm
  have hc : MvPolynomial.coeff m (MvPolynomial.pderiv i Q) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hc
  have hcQ : MvPolynomial.coeff (m + Finsupp.single i 1) Q ≠ 0 := by
    intro hz
    simp [hz] at hc
  have hmem : m + Finsupp.single i 1 ∈ Q.support :=
    MvPolynomial.mem_support_iff.mpr hcQ
  calc
    m.sum (fun _ e => e) ≤
        (m + Finsupp.single i 1).sum (fun _ e => e) := by
      rw [Finsupp.sum_add_index'] <;> simp
    _ ≤ Q.totalDegree := MvPolynomial.le_totalDegree hmem

theorem irreducible_totalDegree_pos {Q : Poly3} (hQirr : Irreducible Q) :
    0 < Q.totalDegree := by
  by_contra h
  have hdeg : Q.totalDegree = 0 := by omega
  have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
  have hc : MvPolynomial.coeff 0 Q ≠ 0 := by
    intro hc0
    apply hQirr.ne_zero
    rw [hC, hc0, map_zero]
  have hunit : IsUnit (MvPolynomial.coeff 0 Q) := isUnit_iff_ne_zero.mpr hc
  exact hQirr.not_isUnit (hC ▸ hunit.map (MvPolynomial.C : ℝ →+* Poly3))

/-- An irreducible nonconstant polynomial in characteristic zero has a
nonzero partial derivative. -/
theorem exists_pderiv_ne_zero {Q : Poly3} (hQirr : Irreducible Q) :
    ∃ i : Fin 3, MvPolynomial.pderiv i Q ≠ 0 := by
  have hQ0 := hQirr.ne_zero
  have hsupp : Q.support.Nonempty := by
    simpa [MvPolynomial.support_nonempty] using hQ0
  obtain ⟨m, hm, heq⟩ := Q.support.exists_mem_eq_sup hsupp
    (fun m : Fin 3 →₀ ℕ => m.sum fun _ e => e)
  have hsum : 0 < m.sum (fun _ e => e) := by
    rw [← heq]
    exact irreducible_totalDegree_pos hQirr
  have hm0 : m ≠ 0 := by
    intro hzero
    subst m
    simp at hsum
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hm0
  refine ⟨i, ?_⟩
  intro hderiv
  let d := m - Finsupp.single i 1
  have hmi : m i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hadd : d + Finsupp.single i 1 = m :=
    Finsupp.sub_add_single_one_cancel hmi
  have hcoeffQ : MvPolynomial.coeff m Q ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  have hcoeff := MvPolynomial.coeff_pderiv (i := i) Q d
  rw [hderiv, MvPolynomial.coeff_zero, hadd] at hcoeff
  have hnat : (d i : ℝ) + 1 ≠ 0 := by positivity
  exact (mul_ne_zero hcoeffQ hnat) hcoeff.symm

/-- Every nonzero partial derivative has strictly smaller total degree than
a nonconstant polynomial. -/
theorem totalDegree_pderiv_lt {Q : Poly3} {i : Fin 3}
    (hQdeg : 0 < Q.totalDegree) :
    (MvPolynomial.pderiv i Q).totalDegree < Q.totalDegree := by
  rw [MvPolynomial.totalDegree, Finset.sup_lt_iff hQdeg]
  intro d hd
  have hc : MvPolynomial.coeff d (MvPolynomial.pderiv i Q) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  rw [MvPolynomial.coeff_pderiv] at hc
  have hcQ : MvPolynomial.coeff (d + Finsupp.single i 1) Q ≠ 0 := by
    intro hz
    simp [hz] at hc
  have hmem : d + Finsupp.single i 1 ∈ Q.support :=
    MvPolynomial.mem_support_iff.mpr hcQ
  have hsum : (d + Finsupp.single i 1).sum (fun _ e => e) =
      d.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index'] <;> simp
  rw [← Nat.add_one_le_iff, ← hsum]
  exact MvPolynomial.le_totalDegree hmem

/-- The Hilbert line-counting bound is monotone when the second degree is
bounded by the first. -/
theorem lineSurfaceBound_mono {a b : ℕ} (hb : b ≤ a) :
    a * b * (2 * (a * b) + a + b + 2) ≤
      a * a * (2 * (a * a) + a + a + 2) := by
  gcongr

/-- A point of a hypersurface is singular when all its first partial
derivatives vanish there. -/
def SingularAt (Q : Poly3) (x : Space3) : Prop :=
  ∀ i : Fin 3, MvPolynomial.eval x (MvPolynomial.pderiv i Q) = 0

/-- If every point of every indexed line on an irreducible surface is
singular, the Hilbert bound applied to a nonzero partial derivative bounds
the number of lines. -/
theorem card_le_of_all_lines_singular
    {I : Type*} [Fintype I] [DecidableEq I]
    (idx : I → PlanePoint × PlanePoint) (hinj : Function.Injective idx)
    {Q : Poly3} (hQirr : Irreducible Q)
    (hQlines : ∀ i, LineContained Q
      (linePoint (idx i).1 (idx i).2 0) (lineDirection (idx i).1 (idx i).2))
    (hsing : ∀ i t, SingularAt Q (linePoint (idx i).1 (idx i).2 t)) :
    Fintype.card I ≤ Q.totalDegree * Q.totalDegree *
      (2 * (Q.totalDegree * Q.totalDegree) + Q.totalDegree + Q.totalDegree + 2) := by
  obtain ⟨j, hj⟩ := exists_pderiv_ne_zero hQirr
  have hdeg := totalDegree_pderiv_lt (i := j) (irreducible_totalDegree_pos hQirr)
  have hnotdiv : ¬ Q ∣ MvPolynomial.pderiv j Q := by
    intro hdiv
    have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hj
    omega
  have hDlines : ∀ i, LineContained (MvPolynomial.pderiv j Q)
      (linePoint (idx i).1 (idx i).2 0) (lineDirection (idx i).1 (idx i).2) := by
    intro i
    rw [lineContained_iff]
    intro t
    have hpoint : (fun k => linePoint (idx i).1 (idx i).2 0 k +
        t * lineDirection (idx i).1 (idx i).2 k) =
        linePoint (idx i).1 (idx i).2 t := by
      funext k
      fin_cases k <;> simp [linePoint, lineDirection] <;> ring
    rw [hpoint]
    exact hsing i t j
  have hbound := card_le_of_lines_in_two_surfaces idx hinj
    hQirr.ne_zero hj hQirr hnotdiv rfl rfl hQlines hDlines
  exact hbound.trans (lineSurfaceBound_mono hdeg.le)

/-- More lines than the singular-line bound force a nonsingular point on
one of them. -/
theorem exists_nonsingular_point_of_bound_lt_card
    {I : Type*} [Fintype I] [DecidableEq I]
    (idx : I → PlanePoint × PlanePoint) (hinj : Function.Injective idx)
    {Q : Poly3} (hQirr : Irreducible Q)
    (hQlines : ∀ i, LineContained Q
      (linePoint (idx i).1 (idx i).2 0) (lineDirection (idx i).1 (idx i).2))
    (hlarge : Q.totalDegree * Q.totalDegree *
      (2 * (Q.totalDegree * Q.totalDegree) + Q.totalDegree + Q.totalDegree + 2) <
        Fintype.card I) :
    ∃ i t, ¬ SingularAt Q (linePoint (idx i).1 (idx i).2 t) := by
  by_contra h
  push Not at h
  exact (Nat.not_le_of_lt hlarge)
    (card_le_of_all_lines_singular idx hinj hQirr hQlines h)

theorem rulingDerivative_eq_pderiv (p : PlanePoint) (Q : Poly3) :
    rulingDerivative p Q =
      rulingPolynomial p 0 * MvPolynomial.pderiv 0 Q +
        rulingPolynomial p 1 * MvPolynomial.pderiv 1 Q +
          rulingPolynomial p 2 * MvPolynomial.pderiv 2 Q := by
  let D : Derivation ℝ Poly3 Poly3 :=
    (rulingPolynomial p 0) • (MvPolynomial.pderiv 0) +
      (rulingPolynomial p 1) • (MvPolynomial.pderiv 1) +
        (rulingPolynomial p 2) • (MvPolynomial.pderiv 2)
  have hD : MvPolynomial.mkDerivation ℝ (rulingPolynomial p) = D := by
    apply MvPolynomial.derivation_ext
    intro j
    fin_cases j <;>
      simp [D, MvPolynomial.pderiv_X, Pi.single_apply]
  have h := DFunLike.congr_fun hD Q
  simpa [rulingDerivative, D, smul_eq_mul] using h

private theorem totalDegree_rulingPolynomial_le (p : PlanePoint) (i : Fin 3) :
    (rulingPolynomial p i).totalDegree ≤ 2 := by
  fin_cases i
  · dsimp only [rulingPolynomial]
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
      · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
        · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
        · simp
      · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
    · simp
  · dsimp only [rulingPolynomial]
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
      · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
        · simp
        · simp
      · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  · dsimp only [rulingPolynomial]
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · simp
    · exact (MvPolynomial.totalDegree_pow _ _).trans (by simp)

/-- The ruling derivative has degree at most two more than the original
polynomial.  The sharper `d+1` estimate is unnecessary for the incidence
argument; this cancellation-free form is stable under all degenerate cases. -/
theorem totalDegree_rulingDerivative_le (p : PlanePoint) (Q : Poly3) :
    (rulingDerivative p Q).totalDegree ≤ Q.totalDegree + 2 := by
  have hterm (i : Fin 3) :
      (rulingPolynomial p i * MvPolynomial.pderiv i Q).totalDegree ≤
        Q.totalDegree + 2 :=
    (MvPolynomial.totalDegree_mul _ _).trans <| by
      have hfield := totalDegree_rulingPolynomial_le p i
      have hderiv := totalDegree_pderiv_le Q i
      omega
  rw [rulingDerivative_eq_pderiv]
  exact (MvPolynomial.totalDegree_add _ _).trans <| max_le
    ((MvPolynomial.totalDegree_add _ _).trans <| max_le (hterm 0) (hterm 1))
    (hterm 2)

/-- Polynomial uniqueness for the first-order ODE used below.  If a
polynomial solution of `a f' = f g` vanishes at a point where `a` does not,
then it vanishes identically. -/
private theorem polynomial_eq_zero_of_mul_derivative_eq_mul
    (a f g : Polynomial ℝ) (t : ℝ)
    (ha : a.eval t ≠ 0) (hfroot : f.eval t = 0)
    (hode : a * f.derivative = f * g) :
    f = 0 := by
  by_contra hf
  have hfroot' : f.IsRoot t := hfroot
  have hdegree : f.natDegree ≠ 0 := by
    intro hzero
    rw [Polynomial.eq_C_of_natDegree_eq_zero hzero, Polynomial.eval_C] at hfroot
    apply hf
    rw [Polynomial.eq_C_of_natDegree_eq_zero hzero, hfroot, map_zero]
  have hfderiv : f.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr hdegree
  have haleft : a * f.derivative ≠ 0 := by
    apply mul_ne_zero
    · intro hazero
      exact ha (hazero ▸ Polynomial.eval_zero)
    · exact hfderiv
  have hgright : f * g ≠ 0 := hode ▸ haleft
  have ha_notroot : ¬a.IsRoot t := ha
  have hmult_a : a.rootMultiplicity t = 0 :=
    Polynomial.rootMultiplicity_eq_zero ha_notroot
  have hmult_deriv : f.derivative.rootMultiplicity t =
      f.rootMultiplicity t - 1 :=
    Polynomial.derivative_rootMultiplicity_of_root hfroot'
  have hmult := congrArg (Polynomial.rootMultiplicity t) hode
  rw [Polynomial.rootMultiplicity_mul haleft,
    Polynomial.rootMultiplicity_mul hgright, hmult_a, zero_add,
    hmult_deriv] at hmult
  have hmpos : 0 < f.rootMultiplicity t :=
    (Polynomial.rootMultiplicity_pos hf).mpr hfroot'
  omega

private noncomputable def lineSubstitution {ι : Type*} [Fintype ι]
    (x v : ι → ℝ) : MvPolynomial ι ℝ →ₐ[ℝ] Polynomial ℝ :=
  MvPolynomial.aeval
    (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i))

private theorem lineSubstitution_apply {ι : Type*} [Fintype ι]
    (x v : ι → ℝ) (Q : MvPolynomial ι ℝ) :
    lineSubstitution x v Q = lineRestriction Q x v :=
  by simp [lineSubstitution, lineRestriction, MvPolynomial.aeval_def]

/-- Constant-coefficient directional derivative in an arbitrary finite
number of variables. -/
private noncomputable def constantDirectionalDerivative
    {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    MvPolynomial ι ℝ → MvPolynomial ι ℝ :=
  MvPolynomial.mkDerivation ℝ (fun i => MvPolynomial.C (v i))

/-- Formal chain rule for restriction to an affine line, packaged using the
universal derivation of a multivariate polynomial ring. -/
theorem derivative_lineRestriction {ι : Type*} [Fintype ι]
    (Q : MvPolynomial ι ℝ) (x v : ι → ℝ) :
    (lineRestriction Q x v).derivative =
      lineRestriction (constantDirectionalDerivative v Q) x v := by
  let φ : MvPolynomial ι ℝ →ₐ[ℝ] Polynomial ℝ := lineSubstitution x v
  let : Algebra (MvPolynomial ι ℝ) (Polynomial ℝ) := φ.toRingHom.toAlgebra
  let : IsScalarTower ℝ (MvPolynomial ι ℝ) (Polynomial ℝ) :=
    IsScalarTower.of_algHom φ
  let D₁ : Derivation ℝ (MvPolynomial ι ℝ) (Polynomial ℝ) :=
    { toFun := fun F => (φ F).derivative
      map_add' := fun F G => by simp
      map_smul' := fun r F => by
        change (φ (r • F)).derivative = r • (φ F).derivative
        simp
      map_one_eq_zero' := by simp
      leibniz' := fun F G => by
        change (φ (F * G)).derivative =
          F • (φ G).derivative + G • (φ F).derivative
        simp [Polynomial.derivative_mul, mul_comm, Algebra.smul_def,
          RingHom.algebraMap_toAlgebra]
        ring }
  let D₂ : Derivation ℝ (MvPolynomial ι ℝ) (Polynomial ℝ) :=
    { toFun := fun F => φ (constantDirectionalDerivative v F)
      map_add' := fun F G => by simp [constantDirectionalDerivative]
      map_smul' := fun r F => by simp [constantDirectionalDerivative]
      map_one_eq_zero' := by simp [constantDirectionalDerivative]
      leibniz' := fun F G => by
        change φ (constantDirectionalDerivative v (F * G)) =
          F • φ (constantDirectionalDerivative v G) +
            G • φ (constantDirectionalDerivative v F)
        simp [constantDirectionalDerivative, Algebra.smul_def, mul_comm,
          RingHom.algebraMap_toAlgebra] }
  have hD : D₁ = D₂ := by
    apply MvPolynomial.derivation_ext
    intro i
    dsimp [D₁, D₂]
    change (φ (MvPolynomial.X i)).derivative =
      φ (constantDirectionalDerivative v (MvPolynomial.X i))
    simp [constantDirectionalDerivative, φ, lineSubstitution,
      Polynomial.derivative_mul]
  have h := DFunLike.congr_fun hD Q
  simpa [D₁, D₂, φ, lineSubstitution_apply] using h

private theorem lineRestriction_rulingPolynomial (p q : PlanePoint)
    (i : Fin 3) :
    lineRestriction (rulingPolynomial p i) (linePoint p q 0)
        (lineDirection p q) =
      (1 + Polynomial.X ^ 2) * Polynomial.C (lineDirection p q i) := by
  apply Polynomial.funext
  intro t
  rw [eval_lineRestriction]
  have hpoint : (fun j => linePoint p q 0 j + t * lineDirection p q j) =
      linePoint p q t := by
    funext j
    fin_cases j <;> simp [linePoint, lineDirection] <;> ring
  rw [hpoint, eval_rulingPolynomial, rulingVectorField_linePoint]
  fin_cases i <;> simp [lineDirection] <;> ring

/-- Restriction of the ruling derivative to a ruling line is `(1+X²)`
times the derivative of the original line restriction. -/
theorem lineRestriction_rulingDerivative (p q : PlanePoint) (Q : Poly3) :
    lineRestriction (rulingDerivative p Q) (linePoint p q 0)
        (lineDirection p q) =
      (1 + Polynomial.X ^ 2) *
        (lineRestriction Q (linePoint p q 0) (lineDirection p q)).derivative := by
  let φ : Poly3 →ₐ[ℝ] Polynomial ℝ :=
    lineSubstitution (linePoint p q 0) (lineDirection p q)
  let : Algebra Poly3 (Polynomial ℝ) := φ.toRingHom.toAlgebra
  let : IsScalarTower ℝ Poly3 (Polynomial ℝ) := IsScalarTower.of_algHom φ
  let D₁ : Derivation ℝ Poly3 (Polynomial ℝ) :=
    { toFun := fun F => φ (rulingDerivative p F)
      map_add' := fun F G => by simp [rulingDerivative_add]
      map_smul' := fun r F => by
        change φ (rulingDerivative p (r • F)) = r • φ (rulingDerivative p F)
        simp [rulingDerivative]
      map_one_eq_zero' := by simp [rulingDerivative]
      leibniz' := fun F G => by
        change φ (rulingDerivative p (F * G)) =
          F • φ (rulingDerivative p G) + G • φ (rulingDerivative p F)
        simp [rulingDerivative_mul, Algebra.smul_def, mul_comm,
          RingHom.algebraMap_toAlgebra] }
  let Ddir : Derivation ℝ Poly3 (Polynomial ℝ) :=
    { toFun := fun F => φ (constantDirectionalDerivative (lineDirection p q) F)
      map_add' := fun F G => by simp [constantDirectionalDerivative]
      map_smul' := fun r F => by simp [constantDirectionalDerivative]
      map_one_eq_zero' := by simp [constantDirectionalDerivative]
      leibniz' := fun F G => by
        change φ (constantDirectionalDerivative (lineDirection p q) (F * G)) =
          F • φ (constantDirectionalDerivative (lineDirection p q) G) +
            G • φ (constantDirectionalDerivative (lineDirection p q) F)
        simp [constantDirectionalDerivative, Algebra.smul_def, mul_comm,
          RingHom.algebraMap_toAlgebra] }
  let D₂ : Derivation ℝ Poly3 (Polynomial ℝ) :=
    (1 + Polynomial.X ^ 2 : Polynomial ℝ) • Ddir
  have hD : D₁ = D₂ := by
    apply MvPolynomial.derivation_ext
    intro i
    dsimp [D₁, D₂, Ddir]
    change φ (rulingDerivative p (MvPolynomial.X i)) =
      (1 + Polynomial.X ^ 2) *
        φ (constantDirectionalDerivative (lineDirection p q) (MvPolynomial.X i))
    simp only [rulingDerivative, constantDirectionalDerivative,
      MvPolynomial.mkDerivation_X]
    change φ (rulingPolynomial p i) =
      (1 + Polynomial.X ^ 2) * φ (MvPolynomial.C (lineDirection p q i))
    simpa [φ, lineSubstitution_apply] using lineRestriction_rulingPolynomial p q i
  have h := DFunLike.congr_fun hD Q
  rw [derivative_lineRestriction]
  simpa [D₁, D₂, Ddir, φ, lineSubstitution_apply, rulingDerivative] using h

/-- A ruling line contained in `Z(Q)` is also contained in the zero set of
the ruling derivative. -/
theorem lineContained_rulingDerivative {p q : PlanePoint} {Q : Poly3}
    (hQ : LineContained Q (linePoint p q 0) (lineDirection p q)) :
    LineContained (rulingDerivative p Q)
      (linePoint p q 0) (lineDirection p q) := by
  unfold LineContained at hQ ⊢
  rw [lineRestriction_rulingDerivative, hQ, Polynomial.derivative_zero, mul_zero]

/-- If an irreducible surface factor divides its ruling derivative, the
unique ruling line through any zero of the factor is contained in the
surface.  This is the algebraic uniqueness-of-integral-curves step in
Guth's non-clustering lemma. -/
theorem lineContained_secondIndexThrough_of_dvd_rulingDerivative
    {p : PlanePoint} {Q : Poly3} {x : Space3}
    (hdiv : Q ∣ rulingDerivative p Q)
    (hx : MvPolynomial.eval x Q = 0) :
    LineContained Q
      (linePoint p (secondIndexThrough p x) 0)
      (lineDirection p (secondIndexThrough p x)) := by
  obtain ⟨R, hR⟩ := hdiv
  let q := secondIndexThrough p x
  let f := lineRestriction Q (linePoint p q 0) (lineDirection p q)
  let g := lineRestriction R (linePoint p q 0) (lineDirection p q)
  have hode : (1 + Polynomial.X ^ 2) * f.derivative = f * g := by
    dsimp only [f, g]
    rw [← lineRestriction_rulingDerivative, hR,
      lineRestriction_mul]
  have hroot : f.eval (x 2) = 0 := by
    dsimp only [f]
    rw [eval_lineRestriction]
    have hparam :
        (fun i => linePoint p q 0 i + x 2 * lineDirection p q i) =
          linePoint p q (x 2) := by
      funext i
      fin_cases i <;> simp [linePoint, lineDirection] <;> ring
    rw [hparam]
    change MvPolynomial.eval
      (linePoint p (secondIndexThrough p x) (x 2)) Q = 0
    rw [linePoint_secondIndexThrough]
    exact hx
  have hlead : (1 + Polynomial.X ^ 2 : Polynomial ℝ).eval (x 2) ≠ 0 := by
    simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_pow,
      Polynomial.eval_X]
    nlinarith [sq_nonneg (x 2)]
  exact polynomial_eq_zero_of_mul_derivative_eq_mul
    (1 + Polynomial.X ^ 2) f g (x 2) hlead hroot hode

/-! ## A Hilbert-function line bound -/

/-- Second endpoints whose fixed-first-endpoint ruling lines lie on `Q`. -/
noncomputable def secondIndicesOnSurface (P : Finset PlanePoint)
    (p : PlanePoint) (Q : Poly3) : Finset PlanePoint := by
  classical
  exact P.filter fun q =>
    LineContained Q (linePoint p q 0) (lineDirection p q)

/-- Unless `Q` divides its ruling derivative, only boundedly many members of
one fixed ruling can lie on the irreducible surface `Q`. -/
theorem dvd_rulingDerivative_or_card_secondIndicesOnSurface_le
    (P : Finset PlanePoint) (p : PlanePoint) (Q : Poly3)
    (hQirr : Irreducible Q) :
    Q ∣ rulingDerivative p Q ∨
      (secondIndicesOnSurface P p Q).card ≤
        Q.totalDegree * (rulingDerivative p Q).totalDegree *
          (2 * (Q.totalDegree * (rulingDerivative p Q).totalDegree) +
            Q.totalDegree + (rulingDerivative p Q).totalDegree + 2) := by
  classical
  by_cases hdiv : Q ∣ rulingDerivative p Q
  · exact Or.inl hdiv
  · right
    let S := secondIndicesOnSurface P p Q
    let idx : S → PlanePoint × PlanePoint := fun q => (p, q.1)
    have hinj : Function.Injective idx := by
      intro q r hqr
      apply Subtype.ext
      exact congrArg Prod.snd hqr
    have hR0 : rulingDerivative p Q ≠ 0 := by
      intro hzero
      exact hdiv (hzero ▸ dvd_zero Q)
    have hQlines : ∀ q : S, LineContained Q
        (linePoint (idx q).1 (idx q).2 0)
        (lineDirection (idx q).1 (idx q).2) := by
      intro q
      exact (Finset.mem_filter.mp q.2).2
    have hRlines : ∀ q : S, LineContained (rulingDerivative p Q)
        (linePoint (idx q).1 (idx q).2 0)
        (lineDirection (idx q).1 (idx q).2) := by
      intro q
      exact lineContained_rulingDerivative (hQlines q)
    have hbound := card_le_of_lines_in_two_surfaces idx hinj
      hQirr.ne_zero hR0 hQirr hdiv rfl rfl hQlines hRlines
    simpa [S] using hbound

noncomputable def affineFirst (p r : PlanePoint) (s : ℝ) : PlanePoint :=
  (1 - s) • p + s • r

lemma rulingDerivative_affineFirst (p r : PlanePoint) (s : ℝ) (Q : Poly3) :
    rulingDerivative (affineFirst p r s) Q =
      (1 - s) • rulingDerivative p Q + s • rulingDerivative r Q := by
  have hfield (i : Fin 3) :
      rulingPolynomial (affineFirst p r s) i =
        (1 - s) • rulingPolynomial p i + s • rulingPolynomial r i := by
    fin_cases i <;>
      simp [affineFirst, rulingPolynomial, MvPolynomial.smul_eq_C_mul] <;> ring
  rw [rulingDerivative_eq_pderiv, rulingDerivative_eq_pderiv,
    rulingDerivative_eq_pderiv, hfield 0, hfield 1, hfield 2]
  simp only [add_mul, MvPolynomial.smul_eq_C_mul]
  ring

lemma dvd_rulingDerivative_affineFirst {p r : PlanePoint} {Q : Poly3}
    (hp : Q ∣ rulingDerivative p Q) (hr : Q ∣ rulingDerivative r Q) (s : ℝ) :
    Q ∣ rulingDerivative (affineFirst p r s) Q := by
  rw [rulingDerivative_affineFirst]
  exact dvd_add (dvd_smul_of_dvd (1 - s) hp) (dvd_smul_of_dvd s hr)

noncomputable def tangentPolynomial (Q : Poly3) (x : Space3) : Poly3 :=
  ∑ i : Fin 3, MvPolynomial.C (MvPolynomial.eval x (MvPolynomial.pderiv i Q)) *
    (MvPolynomial.X i - MvPolynomial.C (x i))

lemma eval_tangentPolynomial (Q : Poly3) (x y : Space3) :
    MvPolynomial.eval y (tangentPolynomial Q x) =
      ∑ i : Fin 3, MvPolynomial.eval x (MvPolynomial.pderiv i Q) * (y i - x i) := by
  simp [tangentPolynomial]

lemma totalDegree_tangentPolynomial_le (Q : Poly3) (x : Space3) :
    (tangentPolynomial Q x).totalDegree ≤ 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  calc
    _ ≤ (MvPolynomial.C (MvPolynomial.eval x (MvPolynomial.pderiv i Q))).totalDegree +
        (MvPolynomial.X i - MvPolynomial.C (x i)).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + 1 := Nat.add_le_add (by simp)
      ((MvPolynomial.totalDegree_sub _ _).trans (by simp))
    _ = 1 := by omega

lemma tangentPolynomial_ne_zero {Q : Poly3} {x : Space3}
    (hx : ¬ SingularAt Q x) : tangentPolynomial Q x ≠ 0 := by
  simp only [SingularAt, not_forall] at hx
  obtain ⟨j, hj⟩ := hx
  intro hzero
  let y : Space3 := fun k => x k + if k = j then 1 else 0
  have heval := congrArg (MvPolynomial.eval y) hzero
  rw [eval_tangentPolynomial] at heval
  simp only [map_zero] at heval
  dsimp [y] at heval
  fin_cases j <;> simp at heval <;> exact hj heval

lemma dotGradient_lineDirection_eq_zero {p q : PlanePoint} {Q : Poly3}
    (hQ : LineContained Q (linePoint p q 0) (lineDirection p q)) (t : ℝ) :
    ∑ i : Fin 3, MvPolynomial.eval (linePoint p q t) (MvPolynomial.pderiv i Q) *
      lineDirection p q i = 0 := by
  have hDline := lineContained_rulingDerivative hQ
  rw [lineContained_iff] at hDline
  have hD := hDline t
  have hpoint : (fun i => linePoint p q 0 i + t * lineDirection p q i) =
      linePoint p q t := by
    funext i
    fin_cases i <;> simp [linePoint, lineDirection] <;> ring
  rw [hpoint, rulingDerivative_eq_pderiv] at hD
  simp only [map_add, map_mul, eval_rulingPolynomial] at hD
  rw [rulingVectorField_linePoint] at hD
  simp only [Pi.smul_apply, smul_eq_mul] at hD
  have hfactor :
      (1 + t ^ 2) *
        (∑ i : Fin 3, MvPolynomial.eval (linePoint p q t)
          (MvPolynomial.pderiv i Q) * lineDirection p q i) = 0 := by
    rw [Fin.sum_univ_three]
    linear_combination hD
  exact (mul_eq_zero.mp hfactor).resolve_left <| by
    nlinarith [sq_nonneg t]

lemma lineContained_tangentPolynomial_of_rulingLine
    {p q : PlanePoint} {Q : Poly3}
    (hQ : LineContained Q (linePoint p q 0) (lineDirection p q)) (t : ℝ) :
    LineContained (tangentPolynomial Q (linePoint p q t))
      (linePoint p q 0) (lineDirection p q) := by
  rw [lineContained_iff]
  intro u
  rw [eval_tangentPolynomial]
  have hdot := dotGradient_lineDirection_eq_zero hQ t
  rw [Fin.sum_univ_three] at hdot ⊢
  simp [linePoint, lineDirection] at hdot ⊢
  linear_combination (u - t) * hdot

lemma not_dvd_tangentPolynomial {Q : Poly3} {x : Space3}
    (hdeg : 1 < Q.totalDegree) (hnz : tangentPolynomial Q x ≠ 0) :
    ¬ Q ∣ tangentPolynomial Q x := by
  intro hdiv
  have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hnz
  have htan := totalDegree_tangentPolynomial_le Q x
  omega

lemma affineFirst_injective {p r : PlanePoint} (hpr : p ≠ r) :
    Function.Injective (affineFirst p r) := by
  have hcoord : ∃ j : Fin 2, p j ≠ r j := by
    by_contra h
    push Not at h
    apply hpr
    apply PiLp.ext
    exact h
  obtain ⟨j, hj⟩ := hcoord
  intro s t hst
  have hc := congrArg (fun z : PlanePoint => z j) hst
  simp [affineFirst] at hc
  have hprod : (s - t) * (r j - p j) = 0 := by
    linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hj.symm))

lemma eval_linePoint_eq_zero_of_lineContained {p q : PlanePoint} {Q : Poly3}
    (hQ : LineContained Q (linePoint p q 0) (lineDirection p q)) (t : ℝ) :
    MvPolynomial.eval (linePoint p q t) Q = 0 := by
  rw [lineContained_iff] at hQ
  have h := hQ t
  have hpoint : (fun i => linePoint p q 0 i + t * lineDirection p q i) =
      linePoint p q t := by
    funext i
    fin_cases i <;> simp [linePoint, lineDirection] <;> ring
  rwa [hpoint] at h

lemma eq_of_two_exceptional_of_many_lines
    {I : Type*} [Fintype I] [DecidableEq I]
    (idx₀ : I → PlanePoint × PlanePoint) (hinj₀ : Function.Injective idx₀)
    {Q : Poly3} (hQirr : Irreducible Q) (hdeg : 1 < Q.totalDegree)
    (hQlines : ∀ i, LineContained Q
      (linePoint (idx₀ i).1 (idx₀ i).2 0)
      (lineDirection (idx₀ i).1 (idx₀ i).2))
    (hlarge : Q.totalDegree * Q.totalDegree *
      (2 * (Q.totalDegree * Q.totalDegree) + Q.totalDegree + Q.totalDegree + 2) <
        Fintype.card I)
    {p r : PlanePoint}
    (hp : Q ∣ rulingDerivative p Q) (hr : Q ∣ rulingDerivative r Q) :
    p = r := by
  by_contra hpr
  obtain ⟨i₀, t₀, hxnsing⟩ :=
    exists_nonsingular_point_of_bound_lt_card idx₀ hinj₀ hQirr hQlines hlarge
  let x : Space3 := linePoint (idx₀ i₀).1 (idx₀ i₀).2 t₀
  have hxQ : MvPolynomial.eval x Q = 0 := by
    exact eval_linePoint_eq_zero_of_lineContained (hQlines i₀) t₀
  have hT0 : tangentPolynomial Q x ≠ 0 := tangentPolynomial_ne_zero hxnsing
  let B := Q.totalDegree * Q.totalDegree *
    (2 * (Q.totalDegree * Q.totalDegree) + Q.totalDegree + Q.totalDegree + 2)
  let N := B + 1
  let first : Fin N → PlanePoint := fun j => affineFirst p r (j : ℝ)
  let idx : Fin N → PlanePoint × PlanePoint := fun j =>
    (first j, secondIndexThrough (first j) x)
  have hinj : Function.Injective idx := by
    intro j k hjk
    have hfirst : first j = first k := congrArg Prod.fst hjk
    have hcast : (j : ℝ) = (k : ℝ) := by
      exact affineFirst_injective hpr hfirst
    exact Fin.ext (by exact_mod_cast hcast)
  have hdiv (j : Fin N) : Q ∣ rulingDerivative (first j) Q := by
    exact dvd_rulingDerivative_affineFirst hp hr (j : ℝ)
  have hlinesQ : ∀ j, LineContained Q
      (linePoint (idx j).1 (idx j).2 0)
      (lineDirection (idx j).1 (idx j).2) := by
    intro j
    exact lineContained_secondIndexThrough_of_dvd_rulingDerivative (hdiv j) hxQ
  have hlinesT : ∀ j, LineContained (tangentPolynomial Q x)
      (linePoint (idx j).1 (idx j).2 0)
      (lineDirection (idx j).1 (idx j).2) := by
    intro j
    have h := lineContained_tangentPolynomial_of_rulingLine (hlinesQ j) (x 2)
    have hxline : linePoint (idx j).1 (idx j).2 (x 2) = x := by
      exact linePoint_secondIndexThrough (first j) x
    rwa [hxline] at h
  have hnotdiv : ¬ Q ∣ tangentPolynomial Q x :=
    not_dvd_tangentPolynomial hdeg hT0
  have hbound := card_le_of_lines_in_two_surfaces idx hinj
    hQirr.ne_zero hT0 hQirr hnotdiv rfl rfl hlinesQ hlinesT
  have hTdeg : (tangentPolynomial Q x).totalDegree ≤ Q.totalDegree :=
    (totalDegree_tangentPolynomial_le Q x).trans hdeg.le
  have hmono := lineSurfaceBound_mono hTdeg
  have hcontr : Fintype.card (Fin N) ≤ B := hbound.trans hmono
  simpa [N, B] using hcontr


noncomputable def lineIndicesOnSurface (P : Finset PlanePoint) (Q : Poly3) :
    Finset (PlanePoint × PlanePoint) := by
  classical
  exact (P.product P).filter fun pq =>
    LineContained Q (linePoint pq.1 pq.2 0) (lineDirection pq.1 pq.2)

noncomputable def fiberPairs (P : Finset PlanePoint) (p : PlanePoint) (Q : Poly3) :
    Finset (PlanePoint × PlanePoint) := by
  classical
  exact (secondIndicesOnSurface P p Q).image fun q => (p, q)

lemma lineIndicesOnSurface_eq_biUnion (P : Finset PlanePoint) (Q : Poly3) :
    lineIndicesOnSurface P Q = P.biUnion fun p => fiberPairs P p Q := by
  classical
  ext pq
  simp [lineIndicesOnSurface, fiberPairs, secondIndicesOnSurface]
  aesop

lemma card_fiberPairs (P : Finset PlanePoint) (p : PlanePoint) (Q : Poly3) :
    (fiberPairs P p Q).card = (secondIndicesOnSurface P p Q).card := by
  classical
  apply Finset.card_image_of_injective
  intro q r hqr
  exact congrArg Prod.snd hqr

lemma card_lineIndicesOnSurface_le_sum_fibers (P : Finset PlanePoint) (Q : Poly3) :
    (lineIndicesOnSurface P Q).card ≤
      ∑ p ∈ P, (secondIndicesOnSurface P p Q).card := by
  rw [lineIndicesOnSurface_eq_biUnion]
  exact Finset.card_biUnion_le.trans <| by
    apply Finset.sum_le_sum
    intro p hp
    rw [card_fiberPairs]

lemma lineSurfaceBound_mono_right {a b c : ℕ} (hbc : b ≤ c) :
    a * b * (2 * (a * b) + a + b + 2) ≤
      a * c * (2 * (a * c) + a + c + 2) := by
  gcongr

noncomputable def rulingFiberBound (Q : Poly3) : ℕ :=
  Q.totalDegree * (Q.totalDegree + 2) *
    (2 * (Q.totalDegree * (Q.totalDegree + 2)) +
      Q.totalDegree + (Q.totalDegree + 2) + 2)

lemma card_secondIndicesOnSurface_le_rulingFiberBound
    (P : Finset PlanePoint) (p : PlanePoint) {Q : Poly3}
    (hQirr : Irreducible Q) (hnot : ¬ Q ∣ rulingDerivative p Q) :
    (secondIndicesOnSurface P p Q).card ≤ rulingFiberBound Q := by
  rcases dvd_rulingDerivative_or_card_secondIndicesOnSurface_le P p Q hQirr with
    hdiv | hcard
  · exact (hnot hdiv).elim
  · exact hcard.trans (lineSurfaceBound_mono_right
      (totalDegree_rulingDerivative_le p Q))

noncomputable def exceptionalFirstIndices (P : Finset PlanePoint) (Q : Poly3) :
    Finset PlanePoint := by
  classical
  exact P.filter fun p => Q ∣ rulingDerivative p Q

lemma card_exceptionalFirstIndices_le_one_of_many_lines
    (P : Finset PlanePoint) {Q : Poly3}
    (hQirr : Irreducible Q) (hdeg : 1 < Q.totalDegree)
    (hlarge : Q.totalDegree * Q.totalDegree *
      (2 * (Q.totalDegree * Q.totalDegree) + Q.totalDegree + Q.totalDegree + 2) <
        (lineIndicesOnSurface P Q).card) :
    (exceptionalFirstIndices P Q).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro p r hp hr
  have hp' := (Finset.mem_filter.mp hp).2
  have hr' := (Finset.mem_filter.mp hr).2
  let S := lineIndicesOnSurface P Q
  let idx : S → PlanePoint × PlanePoint := fun z => z.1
  have hinj : Function.Injective idx := fun a b h => Subtype.ext h
  have hlines : ∀ z : S, LineContained Q
      (linePoint (idx z).1 (idx z).2 0)
      (lineDirection (idx z).1 (idx z).2) := by
    intro z
    exact (Finset.mem_filter.mp z.2).2
  exact eq_of_two_exceptional_of_many_lines idx hinj hQirr hdeg hlines
    (by simpa [S] using hlarge) hp' hr'

lemma card_secondIndicesOnSurface_le_card (P : Finset PlanePoint)
    (p : PlanePoint) (Q : Poly3) :
    (secondIndicesOnSurface P p Q).card ≤ P.card := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

lemma sum_secondIndicesOnSurface_le_of_many_lines
    (P : Finset PlanePoint) {Q : Poly3}
    (hQirr : Irreducible Q) (hdeg : 1 < Q.totalDegree)
    (hlarge : Q.totalDegree * Q.totalDegree *
      (2 * (Q.totalDegree * Q.totalDegree) + Q.totalDegree + Q.totalDegree + 2) <
        (lineIndicesOnSurface P Q).card) :
    (∑ p ∈ P, (secondIndicesOnSurface P p Q).card) ≤
      P.card + P.card * rulingFiberBound Q := by
  classical
  let E := exceptionalFirstIndices P Q
  have hE : E.card ≤ 1 :=
    card_exceptionalFirstIndices_le_one_of_many_lines P hQirr hdeg hlarge
  have hexc : (∑ p ∈ E, (secondIndicesOnSurface P p Q).card) ≤ P.card := by
    calc
      _ ≤ E.card • P.card := Finset.sum_le_card_nsmul E _ P.card fun p hp =>
        card_secondIndicesOnSurface_le_card P p Q
      _ ≤ 1 • P.card := by gcongr
      _ = P.card := by simp
  have hnon : (∑ p ∈ P.filter fun p => ¬ Q ∣ rulingDerivative p Q,
      (secondIndicesOnSurface P p Q).card) ≤ P.card * rulingFiberBound Q := by
    calc
      _ ≤ (P.filter fun p => ¬ Q ∣ rulingDerivative p Q).card • rulingFiberBound Q :=
        Finset.sum_le_card_nsmul _ _ _ fun p hp =>
          card_secondIndicesOnSurface_le_rulingFiberBound P p hQirr
            (Finset.mem_filter.mp hp).2
      _ ≤ P.card * rulingFiberBound Q := by
        simpa [nsmul_eq_mul] using Nat.mul_le_mul_right (rulingFiberBound Q)
          (Finset.card_le_card (Finset.filter_subset _ _))
  rw [← Finset.sum_filter_add_sum_filter_not P
    (fun p => Q ∣ rulingDerivative p Q)]
  change (∑ p ∈ E, (secondIndicesOnSurface P p Q).card) +
    (∑ p ∈ P.filter fun p => ¬ Q ∣ rulingDerivative p Q,
      (secondIndicesOnSurface P p Q).card) ≤ _
  omega

lemma card_lineIndicesOnSurface_le_nonLinearIrreducible
    (P : Finset PlanePoint) {Q : Poly3}
    (hQirr : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    (lineIndicesOnSurface P Q).card ≤
      Q.totalDegree * Q.totalDegree *
        (2 * (Q.totalDegree * Q.totalDegree) + Q.totalDegree + Q.totalDegree + 2) +
      P.card + P.card * rulingFiberBound Q := by
  by_cases hlarge : Q.totalDegree * Q.totalDegree *
      (2 * (Q.totalDegree * Q.totalDegree) + Q.totalDegree + Q.totalDegree + 2) <
        (lineIndicesOnSurface P Q).card
  · exact (card_lineIndicesOnSurface_le_sum_fibers P Q).trans <|
      (sum_secondIndicesOnSurface_le_of_many_lines P hQirr hdeg hlarge).trans
        (by omega)
  · omega

noncomputable def affineNormal (Q : Poly3) : Space3 :=
  fun i => MvPolynomial.coeff (Finsupp.single i 1) Q

noncomputable def affinePolynomial (Q : Poly3) : Poly3 :=
  MvPolynomial.C (MvPolynomial.coeff 0 Q) +
    ∑ i : Fin 3, MvPolynomial.C (affineNormal Q i) * MvPolynomial.X i

lemma eq_affinePolynomial_of_totalDegree_le_one {Q : Poly3}
    (hdeg : Q.totalDegree ≤ 1) : Q = affinePolynomial Q := by
  ext d
  unfold affinePolynomial
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C,
    MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
  by_cases hd0 : d = 0
  · subst d
    simp
  by_cases hsum : d.sum (fun _ e => e) = 1
  · obtain ⟨i, rfl⟩ := (Finsupp.sum_eq_one_iff d).mp hsum
    have hzero : (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single i 1 := Ne.symm hd0
    have hsingleiff (j : Fin 3) :
        Finsupp.single j 1 = Finsupp.single i 1 ↔ j = i :=
      (Finsupp.single_left_injective one_ne_zero).eq_iff
    simp [affineNormal, hsingleiff, hzero]
  · have hcoeff : MvPolynomial.coeff d Q = 0 := by
      by_contra hc
      have hdmem : d ∈ Q.support := MvPolynomial.mem_support_iff.mpr hc
      have hle := (MvPolynomial.le_totalDegree hdmem).trans hdeg
      have hpos : 0 < d.sum (fun _ e => e) := by
        obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd0
        rw [Finsupp.sum]
        exact lt_of_lt_of_le (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi)
      omega
    have hsingle : ∀ i : Fin 3, d ≠ Finsupp.single i 1 := by
      intro i hi
      apply hsum
      rw [hi]
      simp
    have hsingle' : ∀ i : Fin 3, Finsupp.single i 1 ≠ d :=
      fun i hi => hsingle i hi.symm
    have hzero : (0 : Fin 3 →₀ ℕ) ≠ d := Ne.symm hd0
    simp [affineNormal, hcoeff, hzero, hsingle']

lemma affineNormal_ne_zero_of_totalDegree_eq_one {Q : Poly3}
    (hdeg : Q.totalDegree = 1) : affineNormal Q ≠ 0 := by
  intro hzero
  have hQ := eq_affinePolynomial_of_totalDegree_le_one hdeg.le
  have hz (i : Fin 3) : affineNormal Q i = 0 := congrFun hzero i
  have hQC : Q = MvPolynomial.C (MvPolynomial.coeff 0 Q) := by
    rw [hQ]
    simp [affinePolynomial, hz]
  rw [hQC, MvPolynomial.totalDegree_C] at hdeg
  omega

lemma eval_affinePolynomial (Q : Poly3) (x : Space3) :
    MvPolynomial.eval x (affinePolynomial Q) =
      MvPolynomial.coeff 0 Q + planeValue (affineNormal Q) x := by
  simp [affinePolynomial, affineNormal, planeValue, Fin.sum_univ_three]

lemma lineInAffinePlane_of_lineContained_of_totalDegree_eq_one
    {p q : PlanePoint} {Q : Poly3} (hdeg : Q.totalDegree = 1)
    (hline : LineContained Q (linePoint p q 0) (lineDirection p q)) :
    LineInAffinePlane (affineNormal Q) (-MvPolynomial.coeff 0 Q) p q := by
  intro t
  have hzero := eval_linePoint_eq_zero_of_lineContained hline t
  rw [eq_affinePolynomial_of_totalDegree_le_one hdeg.le,
    eval_affinePolynomial] at hzero
  linarith

lemma card_lineIndicesOnSurface_le_of_totalDegree_eq_one
    (P : Finset PlanePoint) {Q : Poly3} (hdeg : Q.totalDegree = 1) :
    (lineIndicesOnSurface P Q).card ≤ P.card := by
  classical
  have hnormal : affineNormal Q ≠ 0 :=
    affineNormal_ne_zero_of_totalDegree_eq_one hdeg
  have hsub : lineIndicesOnSurface P Q ⊆
      lineIndicesInAffinePlane P (affineNormal Q) (-MvPolynomial.coeff 0 Q) := by
    intro pq hpq
    have hpq' := Finset.mem_filter.mp hpq
    apply Finset.mem_filter.mpr
    refine ⟨hpq'.1, ?_⟩
    exact lineInAffinePlane_of_lineContained_of_totalDegree_eq_one hdeg hpq'.2
  exact (Finset.card_le_card hsub).trans
    (card_lineIndicesInAffinePlane_le P hnormal)

noncomputable def irreducibleSurfaceLineConstant (Q : Poly3) : ℕ :=
  Q.totalDegree * Q.totalDegree *
      (2 * (Q.totalDegree * Q.totalDegree) + Q.totalDegree + Q.totalDegree + 2) +
    1 + rulingFiberBound Q

lemma card_lineIndicesOnSurface_le_irreducible
    (P : Finset PlanePoint) {Q : Poly3} (hQirr : Irreducible Q) :
    (lineIndicesOnSurface P Q).card ≤
      irreducibleSurfaceLineConstant Q * (P.card + 1) := by
  have hpos := irreducible_totalDegree_pos hQirr
  by_cases hdeg : Q.totalDegree = 1
  · have hline := card_lineIndicesOnSurface_le_of_totalDegree_eq_one P hdeg
    have hconst : 1 ≤ irreducibleSurfaceLineConstant Q := by
      simp [irreducibleSurfaceLineConstant, hdeg, rulingFiberBound]
    exact hline.trans <| calc
      P.card ≤ 1 * (P.card + 1) := by omega
      _ ≤ irreducibleSurfaceLineConstant Q * (P.card + 1) := by gcongr
  · have hdeg' : 1 < Q.totalDegree := by omega
    have hline := card_lineIndicesOnSurface_le_nonLinearIrreducible P hQirr hdeg'
    exact hline.trans <| by
      dsimp [irreducibleSurfaceLineConstant]
      nlinarith [Nat.zero_le (P.card *
        (Q.totalDegree * Q.totalDegree *
          (2 * (Q.totalDegree * Q.totalDegree) + Q.totalDegree + Q.totalDegree + 2))),
        Nat.zero_le (P.card * rulingFiberBound Q)]

end Erdos95.NonClustering
