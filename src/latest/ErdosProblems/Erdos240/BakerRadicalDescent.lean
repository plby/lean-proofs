/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.RadicalBasisCore
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Radical coefficient descent in van der Poorten--Loxton Lemma 6

This file proves the algebraic coefficient-extraction step on pp. 50--52 of
van der Poorten--Loxton.  An exponent vector is divided coordinatewise by the
auxiliary prime: its residues index the radical monomials, while its quotients
give the exponents in the next auxiliary function.  Regrouping a finite sum by
those residues and applying linear independence of the radical monomials shows
that every residue-class subsum vanishes.

The last theorem also performs the choice made in the paper.  From a nonzero
integer coefficient family it selects a residue class whose restriction is
still nonzero.  Restriction changes a coefficient only to zero, so the common
coefficient-height bound is preserved exactly.

The main extraction theorem is generic over a proved `LinearIndependent`
family.  `radicalDescent_thirteenthRoots_of_finrank` instantiates that family
with the checked thirteenth-root monomials from `RadicalBasisCore`; the exact
prime-radical wrapper can provide its finrank premise using `Kummer.lean`.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerRadicalDescent

open Finset

section ExponentDivision

variable {κ K : Type*} [Fintype κ]

/-- Coordinatewise residue of a natural exponent vector modulo `q`. -/
def exponentResidue (q : ℕ) [NeZero q] (e : κ → ℕ) : κ → Fin q :=
  fun i ↦ ⟨e i % q, Nat.mod_lt _ (NeZero.pos q)⟩

/-- Coordinatewise quotient of a natural exponent vector by `q`. -/
def exponentQuotient (q : ℕ) (e : κ → ℕ) : κ → ℕ :=
  fun i ↦ e i / q

@[simp]
theorem exponentResidue_val (q : ℕ) [NeZero q] (e : κ → ℕ) (i : κ) :
    ((exponentResidue q e i : Fin q) : ℕ) = e i % q :=
  rfl

@[simp]
theorem exponentQuotient_apply (q : ℕ) (e : κ → ℕ) (i : κ) :
    exponentQuotient q e i = e i / q :=
  rfl

/-- Coordinatewise Euclidean division, in the orientation used to split a
radical monomial into a bounded residue monomial and a rational factor. -/
theorem exponent_eq_residue_add_mul_quotient (q : ℕ) [NeZero q]
    (e : κ → ℕ) (i : κ) :
    e i = (exponentResidue q e i : ℕ) + q * exponentQuotient q e i := by
  simpa [exponentResidue, exponentQuotient] using (Nat.mod_add_div (e i) q).symm

/-- Multiplication of a bounded residue by an integer, reduced modulo `q`. -/
def residueMul (q l : ℕ) [NeZero q] (r : Fin q) : Fin q :=
  ⟨((r : ℕ) * l) % q, Nat.mod_lt _ (NeZero.pos q)⟩

/-- If `l` is coprime to `q`, multiplication by `l` permutes the residue
classes modulo `q`. -/
theorem residueMul_injective (q l : ℕ) [NeZero q] (h : l.Coprime q) :
    Function.Injective (residueMul q l) := by
  intro r s hrs
  apply Fin.ext
  have hv := congrArg Fin.val hrs
  change ((r.val * l) % q) = ((s.val * l) % q) at hv
  have hz : (r.val : ZMod q) * (l : ZMod q) =
      (s.val : ZMod q) * (l : ZMod q) := by
    have hz' := congrArg (fun t : ℕ ↦ (t : ZMod q)) hv
    simpa [Nat.cast_mul] using hz'
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime l h
  have hzu : (r.val : ZMod q) * (u : ZMod q) =
      (s.val : ZMod q) * (u : ZMod q) := by
    simpa [u, ZMod.unitOfCoprime] using hz
  have hcancel := congrArg
    (fun z : ZMod q ↦ z * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) hzu
  have hcast : (r.val : ZMod q) = (s.val : ZMod q) := by
    simpa [mul_assoc] using hcancel
  have hval := congrArg ZMod.val hcast
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt r.isLt,
    Nat.mod_eq_of_lt s.isLt] using hval

/-- Coordinatewise multiplication of a residue vector by `l`. -/
def residueVectorMul (q l : ℕ) [NeZero q] (r : κ → Fin q) : κ → Fin q :=
  fun i ↦ residueMul q l (r i)

theorem residueVectorMul_injective (q l : ℕ) [NeZero q]
    (h : l.Coprime q) :
    Function.Injective (residueVectorMul (κ := κ) q l) := by
  intro r s hrs
  funext i
  exact residueMul_injective q l h (congrFun hrs i)

/-- Taking residues after multiplying all exponents by `l` agrees with
coordinatewise multiplication of their original residues. -/
theorem exponentResidue_mul (q l : ℕ) [NeZero q] (e : κ → ℕ) :
    exponentResidue q (fun i ↦ e i * l) =
      residueVectorMul q l (exponentResidue q e) := by
  funext i
  apply Fin.ext
  simp [exponentResidue, residueVectorMul, residueMul, Nat.mul_mod]

/-- The monomial whose exponents are the coordinatewise residues modulo `q`. -/
def radicalResidueMonomial [CommMonoid K] (q : ℕ) (beta : κ → K)
    (r : κ → Fin q) : K :=
  ∏ i, beta i ^ (r i : ℕ)

/-- The rational factor contributed by the coordinatewise quotients. -/
def rationalQuotientFactor (q : ℕ) (a : κ → ℚ) (e : κ → ℕ) : ℚ :=
  ∏ i, a i ^ exponentQuotient q e i

/-- Exact division-with-remainder identity for a product of radicals. -/
theorem radicalMonomial_eq_map_quotient_mul_residue
    [Field K] [Algebra ℚ K]
    (q : ℕ) [NeZero q] (a : κ → ℚ) (beta : κ → K)
    (hbeta : ∀ i, beta i ^ q = algebraMap ℚ K (a i)) (e : κ → ℕ) :
    (∏ i, beta i ^ e i) =
      algebraMap ℚ K (rationalQuotientFactor q a e) *
        radicalResidueMonomial q beta (exponentResidue q e) := by
  rw [rationalQuotientFactor, radicalResidueMonomial, map_prod,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [exponent_eq_residue_add_mul_quotient q e i, pow_add, pow_mul, hbeta,
    map_pow, mul_comm]

/-- Source form of the split at the grid integer `l`: the fixed residue of
the coefficient index is multiplied by `l` modulo `q`, and all carries are
absorbed into a rational quotient factor. -/
theorem radicalMonomial_mul_eq_map_quotient_mul_residueMul
    [Field K] [Algebra ℚ K]
    (q l : ℕ) [NeZero q] (a : κ → ℚ) (beta : κ → K)
    (hbeta : ∀ i, beta i ^ q = algebraMap ℚ K (a i)) (e : κ → ℕ) :
    (∏ i, beta i ^ (e i * l)) =
      algebraMap ℚ K
          (rationalQuotientFactor q a (fun i ↦ e i * l)) *
        radicalResidueMonomial q beta
          (residueVectorMul q l (exponentResidue q e)) := by
  rw [← exponentResidue_mul q l e]
  exact radicalMonomial_eq_map_quotient_mul_residue q a beta hbeta
    (fun i ↦ e i * l)

/-- Reindexing any independent radical family by multiplication with a unit
modulo `q` preserves linear independence. -/
theorem linearIndependent_residueVectorMul
    [Field K] [Algebra ℚ K]
    (q l : ℕ) [NeZero q] (base : (κ → Fin q) → K)
    (hbase : LinearIndependent ℚ base) (hcop : l.Coprime q) :
    LinearIndependent ℚ
      (fun r ↦ base (residueVectorMul q l r)) := by
  change LinearIndependent ℚ
    (base ∘ residueVectorMul (κ := κ) q l)
  exact hbase.comp (residueVectorMul (κ := κ) q l)
    (residueVectorMul_injective q l hcop)

end ExponentDivision

section CoefficientExtraction

variable {I ρ K X : Type*}
  [Fintype ρ] [DecidableEq ρ]
  [Field K] [Algebra ℚ K]

/-- Restrict an integer coefficient family to one residue fibre. -/
def restrictCoefficients (residue : I → ρ) (r : ρ) (c : I → ℤ) : I → ℤ :=
  fun i ↦ if residue i = r then c i else 0

@[simp]
theorem restrictCoefficients_apply_of_eq
    (residue : I → ρ) (r : ρ) (c : I → ℤ) (i : I)
    (hi : residue i = r) :
    restrictCoefficients residue r c i = c i := by
  simp [restrictCoefficients, hi]

@[simp]
theorem restrictCoefficients_apply_of_ne
    (residue : I → ρ) (r : ρ) (c : I → ℤ) (i : I)
    (hi : residue i ≠ r) :
    restrictCoefficients residue r c i = 0 := by
  simp [restrictCoefficients, hi]

/-- A nonzero family has a nonzero restriction to at least one residue
fibre.  This is the residue class selected at the end of each source level. -/
theorem exists_restrictCoefficients_ne_zero
    (residue : I → ρ) (c : I → ℤ) (hc : c ≠ 0) :
    ∃ r, restrictCoefficients residue r c ≠ 0 := by
  have hex : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    apply hc
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  refine ⟨residue i, ?_⟩
  intro hzero
  have := congrFun hzero i
  simp [restrictCoefficients, hi] at this

/-- Restriction to a residue fibre preserves a `natAbs` height bound. -/
theorem restrictCoefficients_natAbs_le
    (residue : I → ρ) (r : ρ) (c : I → ℤ) (H : ℕ)
    (hc : ∀ i, (c i).natAbs ≤ H) :
    ∀ i, (restrictCoefficients residue r c i).natAbs ≤ H := by
  intro i
  by_cases hi : residue i = r
  · simpa [restrictCoefficients, hi] using hc i
  · simp [restrictCoefficients, hi]

/-- Restriction to a residue fibre preserves the real absolute-value height
bound used in the source parameter package. -/
theorem restrictCoefficients_abs_le
    (residue : I → ρ) (r : ρ) (c : I → ℤ) (H : ℝ)
    (hc : ∀ i, |(c i : ℝ)| ≤ H) :
    ∀ i, |(restrictCoefficients residue r c i : ℝ)| ≤ H := by
  intro i
  by_cases hi : residue i = r
  · simpa [restrictCoefficients, hi] using hc i
  · have hH : 0 ≤ H := (abs_nonneg (c i : ℝ)).trans (hc i)
    simpa [restrictCoefficients, hi] using hH

/-- The canonical index type for the selected residue class.  This is the
source's new `mu`-box before replacing its coordinate bounds by the explicit
floors. -/
abbrev ResidueFiber (residue : I → ρ) (r : ρ) :=
  {i : I // residue i = r}

/-- The next-level integer coefficient family, now genuinely reindexed on
the selected fibre rather than zero-padded on the old box. -/
def fiberCoefficients (residue : I → ρ) (r : ρ) (c : I → ℤ) :
    ResidueFiber residue r → ℤ :=
  fun i ↦ c i.1

/-- A nonzero old coefficient family has a residue fibre whose reindexed
next-level coefficient family is nonzero. -/
theorem exists_fiberCoefficients_ne_zero
    (residue : I → ρ) (c : I → ℤ) (hc : c ≠ 0) :
    ∃ r, fiberCoefficients residue r c ≠ 0 := by
  have hex : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    apply hc
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  refine ⟨residue i, ?_⟩
  intro hzero
  have := congrFun hzero (⟨i, rfl⟩ : ResidueFiber residue (residue i))
  exact hi this

/-- Reindexing on a residue fibre preserves the height verbatim. -/
theorem fiberCoefficients_abs_le
    (residue : I → ρ) (r : ρ) (c : I → ℤ) (H : ℝ)
    (hc : ∀ i, |(c i : ℝ)| ≤ H) :
    ∀ i, |(fiberCoefficients residue r c i : ℝ)| ≤ H := by
  intro i
  exact hc i.1

/-- On the selected fibre, every old exponent is its fixed residue plus `q`
times the next-level quotient exponent. -/
theorem exponent_eq_selectedResidue_add_mul_quotient
    {κ : Type*} [Fintype κ] (q : ℕ) [NeZero q]
    (exponent : I → κ → ℕ) (r : κ → Fin q)
    (i : ResidueFiber (fun j ↦ exponentResidue q (exponent j)) r)
    (k : κ) :
    exponent i.1 k = (r k : ℕ) + q * exponentQuotient q (exponent i.1) k := by
  have hir : (exponentResidue q (exponent i.1) k : ℕ) = (r k : ℕ) :=
    congrArg Fin.val (congrFun i.2 k)
  calc
    exponent i.1 k = (exponentResidue q (exponent i.1) k : ℕ) +
        q * exponentQuotient q (exponent i.1) k :=
      exponent_eq_residue_add_mul_quotient q (exponent i.1) k
    _ = (r k : ℕ) + q * exponentQuotient q (exponent i.1) k := by rw [hir]

/-- The rational coefficient of the radical monomial indexed by `r`, after
regrouping a finite source sum by residue classes. -/
def fiberEvaluation (support : Finset I) (residue : I → ρ)
    (c : I → ℤ) (factor : I → X → ℚ) (r : ρ) (x : X) : ℚ :=
  ∑ i ∈ support, (restrictCoefficients residue r c i : ℚ) * factor i x

/-- The original algebraic value before coefficient extraction. -/
def radicalEvaluation (support : Finset I) (residue : I → ρ)
    (base : ρ → K) (c : I → ℤ) (factor : I → X → ℚ) (x : X) : K :=
  ∑ i ∈ support,
    algebraMap ℚ K ((c i : ℚ) * factor i x) * base (residue i)

/-- The same radical expansion when the independent radical family varies
with the grid point.  In Lemma 6 the family at the integer `l` is obtained by
multiplying all residue exponents by `l` modulo `q`. -/
def varyingRadicalEvaluation (support : Finset I) (residue : I → ρ)
    (base : X → ρ → K) (c : I → ℤ) (factor : I → X → ℚ) (x : X) : K :=
  ∑ i ∈ support,
    algebraMap ℚ K ((c i : ℚ) * factor i x) * base x (residue i)

theorem varyingRadicalEvaluation_eq_radicalEvaluation
    (support : Finset I) (residue : I → ρ) (base : X → ρ → K)
    (c : I → ℤ) (factor : I → X → ℚ) (x : X) :
    varyingRadicalEvaluation support residue base c factor x =
      radicalEvaluation support residue (base x) c factor x :=
  rfl

/-- Writing a residue restriction with an `if` is exactly the corresponding
filtered subsum. -/
theorem fiberEvaluation_eq_sum_filter
    (support : Finset I) (residue : I → ρ)
    (c : I → ℤ) (factor : I → X → ℚ) (r : ρ) (x : X) :
    fiberEvaluation support residue c factor r x =
      ∑ i ∈ support with residue i = r, (c i : ℚ) * factor i x := by
  classical
  simp only [fiberEvaluation, restrictCoefficients]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hir : residue i = r <;> simp [hir]

/-- Regroup the full algebraic sum by its radical residue monomial. -/
theorem radicalEvaluation_eq_sum_fiberEvaluation
    (support : Finset I) (residue : I → ρ) (base : ρ → K)
    (c : I → ℤ) (factor : I → X → ℚ) (x : X) :
    radicalEvaluation support residue base c factor x =
      ∑ r, algebraMap ℚ K (fiberEvaluation support residue c factor r x) *
        base r := by
  classical
  rw [radicalEvaluation]
  calc
    (∑ i ∈ support,
        algebraMap ℚ K ((c i : ℚ) * factor i x) * base (residue i)) =
        ∑ r, ∑ i ∈ support with residue i = r,
          algebraMap ℚ K ((c i : ℚ) * factor i x) * base (residue i) := by
      exact (Finset.sum_fiberwise support residue
        (fun i ↦ algebraMap ℚ K ((c i : ℚ) * factor i x) *
          base (residue i))).symm
    _ =
        ∑ r, ∑ i ∈ support with residue i = r,
          algebraMap ℚ K ((c i : ℚ) * factor i x) * base r := by
      apply Finset.sum_congr rfl
      intro r _hr
      apply Finset.sum_congr rfl
      intro i hi
      have hir : residue i = r := (Finset.mem_filter.mp hi).2
      rw [hir]
    _ = ∑ r, algebraMap ℚ K
          (∑ i ∈ support with residue i = r, (c i : ℚ) * factor i x) *
            base r := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [map_sum, Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [fiberEvaluation_eq_sum_filter]

theorem varyingRadicalEvaluation_eq_sum_fiberEvaluation
    (support : Finset I) (residue : I → ρ) (base : X → ρ → K)
    (c : I → ℤ) (factor : I → X → ℚ) (x : X) :
    varyingRadicalEvaluation support residue base c factor x =
      ∑ r, algebraMap ℚ K (fiberEvaluation support residue c factor r x) *
        base x r := by
  rw [varyingRadicalEvaluation_eq_radicalEvaluation,
    radicalEvaluation_eq_sum_fiberEvaluation]

/-- Linear independence of the radical monomials extracts every rational
residue-class coefficient from a vanishing algebraic sum. -/
theorem fiberEvaluation_eq_zero_of_linearIndependent
    (support : Finset I) (residue : I → ρ) (base : ρ → K)
    (hbase : LinearIndependent ℚ base)
    (c : I → ℤ) (factor : I → X → ℚ) (x : X)
    (hzero : radicalEvaluation support residue base c factor x = 0) :
    ∀ r, fiberEvaluation support residue c factor r x = 0 := by
  have hsum :
      ∑ r, fiberEvaluation support residue c factor r x • base r = 0 := by
    simpa only [Algebra.smul_def, radicalEvaluation_eq_sum_fiberEvaluation]
      using hzero
  exact (Fintype.linearIndependent_iff.mp hbase
    (fun r ↦ fiberEvaluation support residue c factor r x) hsum)

/-- Pointwise coefficient extraction for a radical basis which varies with
the grid point. -/
theorem fiberEvaluation_eq_zero_of_varyingLinearIndependent
    (support : Finset I) (residue : I → ρ) (base : X → ρ → K)
    (hbase : ∀ x, LinearIndependent ℚ (base x))
    (c : I → ℤ) (factor : I → X → ℚ) (x : X)
    (hzero : varyingRadicalEvaluation support residue base c factor x = 0) :
    ∀ r, fiberEvaluation support residue c factor r x = 0 := by
  rw [varyingRadicalEvaluation_eq_radicalEvaluation] at hzero
  exact fiberEvaluation_eq_zero_of_linearIndependent support residue (base x)
    (hbase x) c factor x hzero

/-- Concrete radical descent.

If the old algebraic evaluation vanishes on a set of grid indices, then a
nonzero residue restriction of its integer coefficients gives a next-level
rational evaluation which vanishes on the same indices.  The coefficient
height is unchanged. -/
theorem exists_nonzero_restriction_and_fiber_vanishing
    (support : Finset I) (residue : I → ρ) (base : ρ → K)
    (hbase : LinearIndependent ℚ base)
    (c : I → ℤ) (hc : c ≠ 0) (factor : I → X → ℚ)
    (grid : Set X) (H : ℝ) (hheight : ∀ i, |(c i : ℝ)| ≤ H)
    (hvanish : ∀ x ∈ grid,
      radicalEvaluation support residue base c factor x = 0) :
    ∃ r,
      restrictCoefficients residue r c ≠ 0 ∧
      (∀ i, |(restrictCoefficients residue r c i : ℝ)| ≤ H) ∧
      ∀ x ∈ grid, fiberEvaluation support residue c factor r x = 0 := by
  obtain ⟨r, hr⟩ := exists_restrictCoefficients_ne_zero residue c hc
  refine ⟨r, hr, restrictCoefficients_abs_le residue r c H hheight, ?_⟩
  intro x hx
  exact fiberEvaluation_eq_zero_of_linearIndependent support residue base hbase
    c factor x (hvanish x hx) r

/-- The preceding descent with a point-dependent independent radical family.
This is the exact form used at the coprime grid points in source Lemma 6. -/
theorem exists_nonzero_restriction_and_varying_fiber_vanishing
    (support : Finset I) (residue : I → ρ) (base : X → ρ → K)
    (c : I → ℤ) (hc : c ≠ 0) (factor : I → X → ℚ)
    (grid : Set X) (hbase : ∀ x ∈ grid, LinearIndependent ℚ (base x))
    (H : ℝ) (hheight : ∀ i, |(c i : ℝ)| ≤ H)
    (hvanish : ∀ x ∈ grid,
      varyingRadicalEvaluation support residue base c factor x = 0) :
    ∃ r,
      restrictCoefficients residue r c ≠ 0 ∧
      (∀ i, |(restrictCoefficients residue r c i : ℝ)| ≤ H) ∧
      ∀ x ∈ grid, fiberEvaluation support residue c factor r x = 0 := by
  obtain ⟨r, hr⟩ := exists_restrictCoefficients_ne_zero residue c hc
  refine ⟨r, hr, restrictCoefficients_abs_le residue r c H hheight, ?_⟩
  intro x hx
  have hz := hvanish x hx
  rw [varyingRadicalEvaluation_eq_radicalEvaluation] at hz
  exact fiberEvaluation_eq_zero_of_linearIndependent support residue (base x)
    (hbase x hx) c factor x hz r

end CoefficientExtraction

section RationalToIntegralGrid

variable {I ρ M : Type*} [Fintype ρ] [DecidableEq ρ]

/-- Source-facing form of the coefficient descent.

The premise is the old auxiliary function after evaluating it on the
rational grid and rewriting it as a radical expansion.  The conclusion is
the integral-grid vanishing of the next auxiliary function obtained by
retaining one residue fibre.  In the concrete source construction the
displayed radical expansion is proved using
`radicalMonomial_eq_map_quotient_mul_residue`. -/
theorem exists_radicalDescent_of_rationalGrid_vanishing
    {K : Type*} [Field K] [Algebra ℚ K]
    (support : Finset I) (residue : I → ρ) (base : ρ → K)
    (hbase : LinearIndependent ℚ base)
    (c : I → ℤ) (hc : c ≠ 0)
    (factor : I → ℕ → M → ℚ) (weight : M → ℕ) (R S : ℕ)
    (H : ℝ) (hheight : ∀ i, |(c i : ℝ)| ≤ H)
    (hvanish : ∀ l, 1 ≤ l → l ≤ R →
      ∀ m, weight m ≤ S →
        radicalEvaluation support residue base c
          (fun i x ↦ factor i x.1 x.2) (l, m) = 0) :
    ∃ r,
      restrictCoefficients residue r c ≠ 0 ∧
      (∀ i, |(restrictCoefficients residue r c i : ℝ)| ≤ H) ∧
      ∀ l, 1 ≤ l → l ≤ R → ∀ m, weight m ≤ S →
        fiberEvaluation support residue c
          (fun i x ↦ factor i x.1 x.2) r (l, m) = 0 := by
  let grid : Set (ℕ × M) :=
    {x | 1 ≤ x.1 ∧ x.1 ≤ R ∧ weight x.2 ≤ S}
  obtain ⟨r, hr, hheight', hzero⟩ :=
    exists_nonzero_restriction_and_fiber_vanishing support residue base hbase
      c hc (fun i x ↦ factor i x.1 x.2) grid H hheight
        (by
          rintro ⟨l, m⟩ ⟨hl, hlR, hm⟩
          exact hvanish l hl hlR m hm)
  refine ⟨r, hr, hheight', ?_⟩
  intro l hl hlR m hm
  exact hzero (l, m) ⟨hl, hlR, hm⟩

/-- Exact coprime part of the source transition on pp. 50--51.

At the integer `l`, the radical basis may be reindexed by multiplication by
`l` modulo `q`; hence its independence is required only when `l` is coprime
to `q`.  This is precisely the range in which the source first constructs
the next coefficient family.  Its subsequent interpolation argument treats
the complementary integers divisible by `q`. -/
theorem exists_radicalDescent_of_coprime_rationalGrid_vanishing
    {K : Type*} [Field K] [Algebra ℚ K]
    {q : ℕ} [NeZero q]
    (support : Finset I) (residue : I → ρ)
    (base : ℕ → M → ρ → K)
    (hbase : ∀ l, l.Coprime q → ∀ m,
      LinearIndependent ℚ (base l m))
    (c : I → ℤ) (hc : c ≠ 0)
    (factor : I → ℕ → M → ℚ) (weight : M → ℕ) (R S : ℕ)
    (H : ℝ) (hheight : ∀ i, |(c i : ℝ)| ≤ H)
    (hvanish : ∀ l, 1 ≤ l → l ≤ R → l.Coprime q →
      ∀ m, weight m ≤ S →
        varyingRadicalEvaluation support residue
          (fun x ↦ base x.1 x.2) c
          (fun i x ↦ factor i x.1 x.2) (l, m) = 0) :
    ∃ r,
      restrictCoefficients residue r c ≠ 0 ∧
      (∀ i, |(restrictCoefficients residue r c i : ℝ)| ≤ H) ∧
      ∀ l, 1 ≤ l → l ≤ R → l.Coprime q →
        ∀ m, weight m ≤ S →
          fiberEvaluation support residue c
            (fun i x ↦ factor i x.1 x.2) r (l, m) = 0 := by
  let grid : Set (ℕ × M) :=
    {x | 1 ≤ x.1 ∧ x.1 ≤ R ∧ x.1.Coprime q ∧ weight x.2 ≤ S}
  obtain ⟨r, hr, hheight', hzero⟩ :=
    exists_nonzero_restriction_and_varying_fiber_vanishing support residue
      (fun x ↦ base x.1 x.2) c hc (fun i x ↦ factor i x.1 x.2) grid
      (by
        rintro ⟨l, m⟩ ⟨_hl, _hlR, hcop, _hm⟩
        exact hbase l hcop m)
      H hheight
      (by
        rintro ⟨l, m⟩ ⟨hl, hlR, hcop, hm⟩
        exact hvanish l hl hlR hcop m hm)
  refine ⟨r, hr, hheight', ?_⟩
  intro l hl hlR hcop m hm
  exact hzero (l, m) ⟨hl, hlR, hcop, hm⟩

end RationalToIntegralGrid

section ThirteenthRoots

open Erdos240.Kummer

variable {I ι Ω X : Type*}
  [Fintype I] [Fintype ι] [DecidableEq ι]
  [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω]

/-- The source descent specialized to thirteenth-root monomials.  The exact
finrank premise is discharged by the prime-radical degree theorem in
`Kummer.lean`; keeping it explicit here makes this module depend only on the
checked algebraic core. -/
theorem radicalDescent_thirteenthRoots_of_finrank
    (p : ι → ℕ) (beta : ι → Ω)
    (hbeta : ∀ i, beta i ^ 13 = algebraMap ℚ Ω (p i : ℚ))
    (hfinrank : Module.finrank ℚ
        (IntermediateField.adjoin ℚ (Set.range beta)) =
      13 ^ Fintype.card ι)
    (support : Finset I) (exponent : I → ι → ℕ)
    (c : I → ℤ) (hc : c ≠ 0) (factor : I → X → ℚ)
    (grid : Set X) (H : ℝ) (hheight : ∀ i, |(c i : ℝ)| ≤ H)
    (hvanish : ∀ x ∈ grid,
      radicalEvaluation support (fun i ↦ exponentResidue 13 (exponent i))
        (thirteenthRootMonomial beta) c factor x = 0) :
    ∃ r : ι → Fin 13,
      restrictCoefficients (fun i ↦ exponentResidue 13 (exponent i)) r c ≠ 0 ∧
      (∀ i,
        |(restrictCoefficients (fun i ↦ exponentResidue 13 (exponent i)) r c i : ℝ)| ≤ H) ∧
      ∀ x ∈ grid,
        fiberEvaluation support (fun i ↦ exponentResidue 13 (exponent i))
          c factor r x = 0 := by
  exact exists_nonzero_restriction_and_fiber_vanishing support
    (fun i ↦ exponentResidue 13 (exponent i))
    (thirteenthRootMonomial beta)
    (linearIndependent_thirteenthRootMonomials_of_finrank p beta hbeta hfinrank)
    c hc factor grid H hheight hvanish

/-- Multiplying every residue exponent by an integer coprime to `13`
permutes the checked thirteenth-root monomial basis. -/
theorem linearIndependent_thirteenthRootMonomials_residueMul_of_finrank
    (p : ι → ℕ) (beta : ι → Ω)
    (hbeta : ∀ i, beta i ^ 13 = algebraMap ℚ Ω (p i : ℚ))
    (hfinrank : Module.finrank ℚ
        (IntermediateField.adjoin ℚ (Set.range beta)) =
      13 ^ Fintype.card ι)
    (l : ℕ) (hcop : l.Coprime 13) :
    LinearIndependent ℚ
      (fun r : ι → Fin 13 ↦
        radicalResidueMonomial 13 beta (residueVectorMul 13 l r)) := by
  have hstandard : LinearIndependent ℚ
      (radicalResidueMonomial 13 beta) := by
    change LinearIndependent ℚ (thirteenthRootMonomial beta)
    exact linearIndependent_thirteenthRootMonomials_of_finrank
      p beta hbeta hfinrank
  exact linearIndependent_residueVectorMul 13 l
    (radicalResidueMonomial 13 beta) hstandard hcop

/-- Concrete coprime-grid coefficient descent for the thirteenth-root
extension used in Erdős 240.

The old exponents are split modulo `13`.  At a coprime grid point `l`, the
radical monomial belonging to a residue vector `r` has exponents `l*r`
modulo `13`; the preceding theorem supplies its linear independence.  The
conclusion selects one nonzero residue fibre, preserves the coefficient
height, and proves all of its next-level integral-grid equations. -/
theorem radicalDescent_thirteenthRoots_coprime_of_finrank
    {M : Type*}
    (p : ι → ℕ) (beta : ι → Ω)
    (hbeta : ∀ i, beta i ^ 13 = algebraMap ℚ Ω (p i : ℚ))
    (hfinrank : Module.finrank ℚ
        (IntermediateField.adjoin ℚ (Set.range beta)) =
      13 ^ Fintype.card ι)
    (support : Finset I) (exponent : I → ι → ℕ)
    (c : I → ℤ) (hc : c ≠ 0)
    (factor : I → ℕ → M → ℚ) (weight : M → ℕ) (R S : ℕ)
    (H : ℝ) (hheight : ∀ i, |(c i : ℝ)| ≤ H)
    (hvanish : ∀ l, 1 ≤ l → l ≤ R → l.Coprime 13 →
      ∀ m, weight m ≤ S →
        varyingRadicalEvaluation support
          (fun i ↦ exponentResidue 13 (exponent i))
          (fun x r ↦ radicalResidueMonomial 13 beta
            (residueVectorMul 13 x.1 r)) c
          (fun i x ↦ factor i x.1 x.2) (l, m) = 0) :
    ∃ r : ι → Fin 13,
      restrictCoefficients
          (fun i ↦ exponentResidue 13 (exponent i)) r c ≠ 0 ∧
      (∀ i, |(restrictCoefficients
          (fun i ↦ exponentResidue 13 (exponent i)) r c i : ℝ)| ≤ H) ∧
      ∀ l, 1 ≤ l → l ≤ R → l.Coprime 13 →
        ∀ m, weight m ≤ S →
          fiberEvaluation support
            (fun i ↦ exponentResidue 13 (exponent i)) c
            (fun i x ↦ factor i x.1 x.2) r (l, m) = 0 := by
  exact exists_radicalDescent_of_coprime_rationalGrid_vanishing
    support (fun i ↦ exponentResidue 13 (exponent i))
    (fun l _m r ↦ radicalResidueMonomial 13 beta
      (residueVectorMul 13 l r))
    (fun l hcop _m ↦
      linearIndependent_thirteenthRootMonomials_residueMul_of_finrank
        p beta hbeta hfinrank l hcop)
    c hc factor weight R S H hheight hvanish

end ThirteenthRoots

end Erdos240.BakerRadicalDescent

#print axioms Erdos240.BakerRadicalDescent.radicalMonomial_eq_map_quotient_mul_residue
#print axioms Erdos240.BakerRadicalDescent.fiberEvaluation_eq_zero_of_linearIndependent
#print axioms Erdos240.BakerRadicalDescent.exists_nonzero_restriction_and_fiber_vanishing
#print axioms Erdos240.BakerRadicalDescent.exists_radicalDescent_of_rationalGrid_vanishing
#print axioms Erdos240.BakerRadicalDescent.exists_radicalDescent_of_coprime_rationalGrid_vanishing
#print axioms Erdos240.BakerRadicalDescent.radicalDescent_thirteenthRoots_of_finrank
#print axioms Erdos240.BakerRadicalDescent.radicalDescent_thirteenthRoots_coprime_of_finrank
