/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.Algebraic
import ErdosProblems.Erdos95.External.Tucker

/-!
# Finite polynomial partitioning for Erdős Problem 95

This file develops the finite Stone--Tukey input and the sign-cell
bookkeeping used by the low-degree incidence induction.  A strict sign cell
is indexed by a Boolean sign pattern; points on one of the polynomial walls
belong to no strict cell.
-/

open scoped BigOperators

namespace Erdos95.Partitioning

open Erdos95.Algebraic

/-- A real-valued function bisects a finite set when neither strict sign side
contains more than half of its points.  Points on the zero set are allowed on
the cutting wall. -/
def Bisects {X : Type*} (f : X → ℝ) (S : Finset X) : Prop :=
  2 * (S.filter fun x ↦ 0 < f x).card ≤ S.card ∧
    2 * (S.filter fun x ↦ f x < 0).card ≤ S.card

theorem bisects_neg {X : Type*} [DecidableEq X]
    (f : X → ℝ) (S : Finset X) :
    Bisects (-f) S ↔ Bisects f S := by
  classical
  simp only [Bisects, Pi.neg_apply, neg_pos, neg_lt_zero]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₂, h₁⟩

/-- Evaluation of a box-coefficient polynomial is the corresponding finite
linear combination of the box monomials. -/
theorem eval_polynomialOfCoefficients (k : ℕ)
    (c : CoeffIndex k → ℝ) (z : Fin 3 → ℝ) :
    MvPolynomial.eval z (polynomialOfCoefficients k c) =
      ∑ e : CoeffIndex k, c e * MvPolynomial.eval z (boxMonomial e) := by
  rw [polynomialOfCoefficients, Fintype.linearCombination_apply]
  simp only [map_sum, MvPolynomial.smul_eval]

/-- The strict sign cell cut out inside `S` by a finite list of
polynomials.  `true` denotes the positive side and `false` the negative
side. -/
noncomputable def signCell (S : Finset (Fin 3 → ℝ)) {j : ℕ}
    (p : Fin j → MvPolynomial (Fin 3) ℝ) (sign : Fin j → Bool) :
    Finset (Fin 3 → ℝ) :=
  S.filter fun x ↦ ∀ i, if sign i then 0 < MvPolynomial.eval x (p i)
    else MvPolynomial.eval x (p i) < 0

theorem mem_signCell_iff {S : Finset (Fin 3 → ℝ)} {j : ℕ}
    {p : Fin j → MvPolynomial (Fin 3) ℝ} {sign : Fin j → Bool}
    {x : Fin 3 → ℝ} :
    x ∈ signCell S p sign ↔
      x ∈ S ∧ ∀ i, if sign i then 0 < MvPolynomial.eval x (p i)
        else MvPolynomial.eval x (p i) < 0 := by
  classical
  simp [signCell]

theorem signCell_snoc (S : Finset (Fin 3 → ℝ)) {j : ℕ}
    (p : Fin j → MvPolynomial (Fin 3) ℝ) (q : MvPolynomial (Fin 3) ℝ)
    (sign : Fin j → Bool) (b : Bool) :
    signCell S (Fin.snoc p q) (Fin.snoc sign b) =
      (signCell S p sign).filter fun x ↦
        if b then 0 < MvPolynomial.eval x q
        else MvPolynomial.eval x q < 0 := by
  classical
  ext x
  simp only [mem_signCell_iff, Finset.mem_filter]
  rw [Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  tauto

theorem card_signCell_snoc_le_of_bisects
    (S : Finset (Fin 3 → ℝ)) {j : ℕ}
    (p : Fin j → MvPolynomial (Fin 3) ℝ) (q : MvPolynomial (Fin 3) ℝ)
    (sign : Fin j → Bool)
    (hbisect : Bisects (fun x ↦ MvPolynomial.eval x q) (signCell S p sign))
    (b : Bool) :
    2 * (signCell S (Fin.snoc p q) (Fin.snoc sign b)).card ≤
      (signCell S p sign).card := by
  rw [signCell_snoc]
  cases b with
  | false => simpa [Bisects] using hbisect.2
  | true => simpa [Bisects] using hbisect.1

/-- The coefficient vector evaluates at a point by taking its dot product
with the vector of box-monomial values. -/
noncomputable def coefficientValue (k : ℕ) (c : CoeffIndex k → ℝ)
    (z : Fin 3 → ℝ) : ℝ :=
  ∑ e : CoeffIndex k, c e * MvPolynomial.eval z (boxMonomial e)

theorem coefficientValue_eq_eval (k : ℕ) (c : CoeffIndex k → ℝ)
    (z : Fin 3 → ℝ) :
    coefficientValue k c z =
      MvPolynomial.eval z (polynomialOfCoefficients k c) := by
  rw [eval_polynomialOfCoefficients]
  rfl

/-! ## The finite Stone--Tukey interface -/

/-- The universal finite central-hyperplane bisection statement.  The strict
dimension inequality leaves at least one coefficient direction after the
simultaneous bisection constraints.  This is the finite form of the
Stone--Tukey theorem to be proved from Tucker's lemma below. -/
def FiniteLinearBisection : Prop :=
  ∀ (I B X : Type) [Fintype I] [Fintype B],
    Fintype.card I < Fintype.card B →
      ∀ (S : I → Finset X) (a : X → B → ℝ),
        ∃ c : B → ℝ, c ≠ 0 ∧
          ∀ i, Bisects (fun x ↦ ∑ b, c b * a x b) (S i)

/-- A proof of finite linear bisection supplies a nonzero low-degree
polynomial simultaneously bisecting any family whose cardinality fits in the
box coefficient space. -/
theorem exists_bisecting_polynomial_of_finiteLinearBisection
    (hStoneTukey : FiniteLinearBisection)
    (k : ℕ) (I : Type) [Fintype I]
    (S : I → Finset (Fin 3 → ℝ))
    (hcard : Fintype.card I < (k + 1) ^ 3) :
    ∃ p : MvPolynomial (Fin 3) ℝ,
      p ≠ 0 ∧ p.totalDegree ≤ 3 * k ∧
        ∀ i, Bisects (fun x ↦ MvPolynomial.eval x p) (S i) := by
  classical
  have hdim : Fintype.card I < Fintype.card (CoeffIndex k) := by
    simpa [CoeffIndex] using hcard
  obtain ⟨c, hc, hbisect⟩ :=
    hStoneTukey I (CoeffIndex k) (Fin 3 → ℝ) hdim S
      (fun x e ↦ MvPolynomial.eval x (boxMonomial e))
  refine ⟨polynomialOfCoefficients k c, ?_,
    totalDegree_polynomialOfCoefficients_le k c, ?_⟩
  · intro hp
    apply hc
    apply polynomialOfCoefficients_injective k
    simpa using hp
  · intro i
    simpa only [eval_polynomialOfCoefficients] using hbisect i

/-- All current sign cells can be bisected at once whenever their number
fits into the selected coefficient box. -/
theorem exists_next_partition_cut
    (hStoneTukey : FiniteLinearBisection)
    (S : Finset (Fin 3 → ℝ)) {j k : ℕ}
    (p : Fin j → MvPolynomial (Fin 3) ℝ)
    (hcard : 2 ^ j < (k + 1) ^ 3) :
    ∃ q : MvPolynomial (Fin 3) ℝ,
      q ≠ 0 ∧ q.totalDegree ≤ 3 * k ∧
        ∀ sign : Fin j → Bool,
          Bisects (fun x ↦ MvPolynomial.eval x q) (signCell S p sign) := by
  classical
  apply exists_bisecting_polynomial_of_finiteLinearBisection hStoneTukey k
    (Fin j → Bool) (fun sign ↦ signCell S p sign)
  simpa using hcard

/-- Iterating simultaneous bisection produces `2^J` strict sign cells, each
containing at most a `2^{-J}` fraction of the original finite set.  The
inequality is kept in denominator-free natural-number form. -/
theorem exists_partition_cuts_of_finiteLinearBisection
    (hStoneTukey : FiniteLinearBisection)
    (S : Finset (Fin 3 → ℝ)) (J : ℕ) (k : Fin J → ℕ)
    (hfit : ∀ j : Fin J, 2 ^ (j : ℕ) < (k j + 1) ^ 3) :
    ∃ p : Fin J → MvPolynomial (Fin 3) ℝ,
      (∀ j, p j ≠ 0 ∧ (p j).totalDegree ≤ 3 * k j) ∧
        ∀ sign : Fin J → Bool,
          2 ^ J * (signCell S p sign).card ≤ S.card := by
  classical
  induction J with
  | zero =>
      let p : Fin 0 → MvPolynomial (Fin 3) ℝ := fun i ↦ Fin.elim0 i
      refine ⟨p, ?_, ?_⟩
      · intro j
        exact Fin.elim0 j
      · intro sign
        simp [signCell]
  | succ J ih =>
      have hfitInit : ∀ j : Fin J,
          2 ^ (j : ℕ) < (Fin.init k j + 1) ^ 3 := by
        intro j
        change 2 ^ (j : ℕ) < (k j.castSucc + 1) ^ 3
        exact hfit j.castSucc
      obtain ⟨p, hp, hcells⟩ := ih (Fin.init k) hfitInit
      have hfitLast : 2 ^ J < (k (Fin.last J) + 1) ^ 3 := by
        simpa using hfit (Fin.last J)
      obtain ⟨q, hq, hqdeg, hqbisect⟩ :=
        exists_next_partition_cut hStoneTukey S p hfitLast
      refine ⟨Fin.snoc p q, ?_, ?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun i ↦ ?_) j
        · simpa using And.intro hq hqdeg
        · rw [Fin.snoc_castSucc]
          have hi := hp i
          change p i ≠ 0 ∧ (p i).totalDegree ≤ 3 * k i.castSucc at hi
          exact hi
      · intro sign'
        rw [← Fin.snoc_init_self sign']
        calc
          2 ^ (J + 1) *
                (signCell S (Fin.snoc p q)
                  (Fin.snoc (Fin.init sign') (sign' (Fin.last J)))).card =
              2 ^ J *
                (2 * (signCell S (Fin.snoc p q)
                  (Fin.snoc (Fin.init sign') (sign' (Fin.last J)))).card) := by
                rw [pow_succ]
                ring
          _ ≤ 2 ^ J * (signCell S p (Fin.init sign')).card :=
            Nat.mul_le_mul_left _
              (card_signCell_snoc_le_of_bisects S p q (Fin.init sign')
                (hqbisect (Fin.init sign')) (sign' (Fin.last J)))
          _ ≤ S.card := hcells (Fin.init sign')

/-! ## The product wall -/

/-- The single polynomial whose zero set is the union of all successive
partitioning walls. -/
noncomputable def partitionPolynomial {J : ℕ}
    (p : Fin J → MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  ∏ j, p j

theorem partitionPolynomial_ne_zero {J : ℕ}
    (p : Fin J → MvPolynomial (Fin 3) ℝ) (hp : ∀ j, p j ≠ 0) :
    partitionPolynomial p ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ hp j

theorem totalDegree_partitionPolynomial_le {J : ℕ}
    (p : Fin J → MvPolynomial (Fin 3) ℝ) :
    (partitionPolynomial p).totalDegree ≤ ∑ j, (p j).totalDegree := by
  classical
  simpa [partitionPolynomial] using
    MvPolynomial.totalDegree_finsetProd (Finset.univ : Finset (Fin J)) p

theorem totalDegree_partitionPolynomial_le_sum_three_mul {J : ℕ}
    (p : Fin J → MvPolynomial (Fin 3) ℝ) (k : Fin J → ℕ)
    (hdeg : ∀ j, (p j).totalDegree ≤ 3 * k j) :
    (partitionPolynomial p).totalDegree ≤ ∑ j, 3 * k j := by
  exact (totalDegree_partitionPolynomial_le p).trans <|
    Finset.sum_le_sum fun j _ ↦ hdeg j

theorem eval_partitionPolynomial {J : ℕ}
    (p : Fin J → MvPolynomial (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    MvPolynomial.eval x (partitionPolynomial p) =
      ∏ j, MvPolynomial.eval x (p j) := by
  classical
  simp [partitionPolynomial, map_prod]

theorem eval_ne_zero_of_mem_signCell
    {S : Finset (Fin 3 → ℝ)} {J : ℕ}
    {p : Fin J → MvPolynomial (Fin 3) ℝ} {sign : Fin J → Bool}
    {x : Fin 3 → ℝ} (hx : x ∈ signCell S p sign) (j : Fin J) :
    MvPolynomial.eval x (p j) ≠ 0 := by
  have hj := (mem_signCell_iff.mp hx).2 j
  split at hj <;> linarith

theorem eval_partitionPolynomial_ne_zero_of_mem_signCell
    {S : Finset (Fin 3 → ℝ)} {J : ℕ}
    {p : Fin J → MvPolynomial (Fin 3) ℝ} {sign : Fin J → Bool}
    {x : Fin 3 → ℝ} (hx : x ∈ signCell S p sign) :
    MvPolynomial.eval x (partitionPolynomial p) ≠ 0 := by
  rw [eval_partitionPolynomial]
  exact Finset.prod_ne_zero_iff.mpr fun j _ ↦
    eval_ne_zero_of_mem_signCell hx j

end Erdos95.Partitioning
