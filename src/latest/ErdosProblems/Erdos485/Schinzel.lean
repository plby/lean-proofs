import ErdosProblems.Erdos485.Arithmetic
import ErdosProblems.Erdos485.Basic
import ErdosProblems.Erdos485.Hajos
import ErdosProblems.Erdos485.Normalization
import ErdosProblems.Erdos485.Trinomial
import ErdosProblems.Erdos485.Deformation
import ErdosProblems.Erdos485.SquarefreeGap
import ErdosProblems.Erdos485.RecursiveSpecialization

/-!
# Schinzel's support bound: induction wrapper

This file contains the natural-number induction which turns Schinzel's
algebraic reduction into the explicit support estimate used for Erdős
Problem 485.  Keeping this part separate is useful: all analytic and
polynomial-algebra input is concentrated in `SchinzelReduction`, while the
argument below only uses the two numerical estimates from `Arithmetic`.
-/

namespace Erdos485

open Polynomial

noncomputable section

/-- A polynomial with at least two terms has a square with at least three
terms.  This is the form of Hajós' lemma used to split the induction into its
trinomial base case and the range `t ≥ 4`. -/
theorem three_le_square_termCount (P : ℚ[X]) (hP : 2 ≤ termCount P) :
    3 ≤ termCount (P ^ 2) := by
  exact three_le_sq_support_card hP

/-- The normalized-trinomial base case required by the induction. -/
def TrinomialSquareProperty : Prop :=
  ∀ P : ℚ[X], 2 ≤ termCount P → termCount (P ^ 2) = 3 → termCount P = 2

/-- Normalized form of the trinomial-square base case. -/
def PrimitiveTrinomialProperty : Prop :=
  ∀ {P : ℚ[X]} (N : PrimitiveNormalization P),
    2 ≤ N.poly.support.card →
    (N.poly ^ 2).support.card = 3 →
    N.poly.support.card = 2

/-- Schinzel's normalized trinomial base case. -/
theorem primitiveTrinomialProperty : PrimitiveTrinomialProperty := by
  intro P N hN hthree
  exact primitive_trinomial_support_card_eq_two N hN hthree

/-- The output of the deformation and generic-specialization argument in the
non-base range. -/
def SchinzelInductionStep : Prop :=
  ∀ P : ℚ[X], 2 ≤ termCount P → 4 ≤ termCount (P ^ 2) →
    termCount P ≤ 1 + 8 ^ (termCount (P ^ 2) - 2) / 2 ∨
      ∃ G : ℚ[X],
        2 ≤ termCount G ∧
        termCount (G ^ 2) < termCount (P ^ 2) ∧
        termCount P ≤ termCount G ^ 2

/-- Normalized form of the non-base algebraic step. -/
def PrimitiveSchinzelInductionStep : Prop :=
  ∀ {P : ℚ[X]} (N : PrimitiveNormalization P),
    2 ≤ N.poly.support.card →
    4 ≤ (N.poly ^ 2).support.card →
    N.poly.support.card ≤ 1 + 8 ^ ((N.poly ^ 2).support.card - 2) / 2 ∨
      ∃ G : ℚ[X],
        2 ≤ termCount G ∧
        termCount (G ^ 2) < (N.poly ^ 2).support.card ∧
        N.poly.support.card ≤ termCount G ^ 2

/-- The single remaining output expected from the squarefree-gap and generic
specialization part of the proof. -/
def DeformationRecursiveProperty : Prop :=
  ∀ {P : ℚ[X]} {N : PrimitiveNormalization P},
    Deformation N →
      ∃ G : ℚ[X],
        2 ≤ G.support.card ∧
        (G ^ 2).support.card < (N.poly ^ 2).support.card ∧
        N.poly.support.card ≤ G.support.card ^ 2

/-- Unconditional recursive output of Schinzel's deformation and generic
specialization. -/
theorem deformationRecursiveProperty : DeformationRecursiveProperty := by
  intro P N D
  obtain ⟨F₀, c, hc, hsquare⟩ := Deformation.exists_eq_scalar_mul_sq N D
  exact deformation_recursive_step_of_scalar_square D c hc F₀ hsquare

/-- The complete Dirichlet alternative turns a recursive-specialization
theorem into the normalized induction step. -/
theorem primitiveSchinzelInductionStep_of_deformation
    (hrecursive : DeformationRecursiveProperty) :
    PrimitiveSchinzelInductionStep := by
  intro P N _hN ht
  rcases primitiveNormalization_deformation N ht with hsmall | hD
  · exact Or.inl hsmall
  · obtain ⟨D⟩ := hD
    rcases hrecursive D with ⟨G, hG, hG2, hNG⟩
    exact Or.inr ⟨G, hG, hG2, hNG⟩

/-- Primitive normalization transports the normalized trinomial result back
to the original polynomial. -/
theorem trinomialSquareProperty_of_primitive
    (hbase : PrimitiveTrinomialProperty) : TrinomialSquareProperty := by
  intro P hP hP2
  obtain ⟨N⟩ := exists_primitiveNormalization P hP
  have hN : 2 ≤ N.poly.support.card := by
    rw [N.card_support_eq]
    exact hP
  have hN2 : (N.poly ^ 2).support.card = 3 := by
    rw [N.card_sq_support_eq]
    exact hP2
  rw [termCount, ← N.card_support_eq]
  exact hbase N hN hN2

/-- Primitive normalization transports the normalized non-base step back to
the original polynomial. -/
theorem schinzelInductionStep_of_primitive
    (hstep : PrimitiveSchinzelInductionStep) : SchinzelInductionStep := by
  intro P hP hP2
  obtain ⟨N⟩ := exists_primitiveNormalization P hP
  have hN : 2 ≤ N.poly.support.card := by
    rw [N.card_support_eq]
    exact hP
  have hN2 : 4 ≤ (N.poly ^ 2).support.card := by
    rw [N.card_sq_support_eq]
    exact hP2
  rcases hstep N hN hN2 with hsmall | ⟨G, hG, hG2, hNG⟩
  · left
    simpa only [termCount, N.card_support_eq, N.card_sq_support_eq] using hsmall
  · right
    refine ⟨G, hG, ?_, ?_⟩
    · simpa only [termCount, N.card_sq_support_eq] using hG2
    · simpa only [termCount, N.card_support_eq] using hNG

/-- The exact output needed from Schinzel's algebraic reduction.

For a polynomial `P` with at least two terms, put `t = terms(P²)`.  Either
`t = 3` and `P` is a binomial, or `t ≥ 4` and one of the following holds:

* the elementary all-zero estimate already bounds `terms(P)`; or
* a new polynomial `G` has at least two terms, its square has strictly fewer
  than `t` terms, and `terms(P) ≤ terms(G)²`.

The latter alternative is precisely the result of the generic Laurent
specialization in Schinzel's proof. -/
def SchinzelReduction : Prop :=
  ∀ P : ℚ[X], 2 ≤ termCount P →
    let t := termCount (P ^ 2)
    (t = 3 ∧ termCount P = 2) ∨
      (4 ≤ t ∧
        (termCount P ≤ 1 + 8 ^ (t - 2) / 2 ∨
          ∃ G : ℚ[X],
            2 ≤ termCount G ∧
            termCount (G ^ 2) < t ∧
            termCount P ≤ termCount G ^ 2))

/-- Assemble the exact reduction property from the trinomial base case and
the non-base algebraic step. -/
theorem schinzelReduction_of_base_step
    (hbase : TrinomialSquareProperty) (hstep : SchinzelInductionStep) :
    SchinzelReduction := by
  intro P hP
  let t := termCount (P ^ 2)
  have ht3 : 3 ≤ t := three_le_square_termCount P hP
  by_cases ht : t = 3
  · exact Or.inl ⟨ht, hbase P hP ht⟩
  · have ht4 : 4 ≤ t := by omega
    exact Or.inr ⟨ht4, hstep P hP ht4⟩

/-- The entire induction step, conditional only on the algebraic reduction.

This theorem is intentionally independent of the implementation details of
the normalization, resultant, and specialization arguments. -/
theorem schinzel_support_bound_of_reduction
    (hred : SchinzelReduction) (P : ℚ[X]) (hP : 2 ≤ termCount P) :
    termCount P ≤ B (termCount (P ^ 2)) := by
  generalize ht : termCount (P ^ 2) = t
  induction t using Nat.strong_induction_on generalizing P with
  | h t ih =>
      have hreduce := hred P hP
      simp only [ht] at hreduce
      rcases hreduce with hbase | ⟨ht4, hsmall | hrecursive⟩
      · rcases hbase with ⟨rfl, hterms⟩
        simpa [hterms]
      · exact hsmall.trans (all_zero_estimate ht4)
      · obtain ⟨G, hG, hGt, hPG⟩ := hrecursive
        have hGB : termCount G ≤ B (termCount (G ^ 2)) :=
          ih (termCount (G ^ 2)) hGt G hG rfl
        have hGt_pred : termCount (G ^ 2) ≤ t - 1 := by omega
        have hGBpred : termCount G ≤ B (t - 1) :=
          hGB.trans (B_mono hGt_pred)
        have hsq : termCount G ^ 2 ≤ B (t - 1) ^ 2 :=
          Nat.pow_le_pow_left hGBpred 2
        exact (hPG.trans hsq).trans (Nat.le_of_lt (B_pred_sq_lt ht4))

/-- Direct normalized-input version of the exact support theorem. -/
theorem schinzel_support_bound_of_primitive
    (hbase : PrimitiveTrinomialProperty)
    (hstep : PrimitiveSchinzelInductionStep)
    (P : ℚ[X]) (hP : 2 ≤ termCount P) :
    termCount P ≤ B (termCount (P ^ 2)) :=
  schinzel_support_bound_of_reduction
    (schinzelReduction_of_base_step
      (trinomialSquareProperty_of_primitive hbase)
      (schinzelInductionStep_of_primitive hstep)) P hP

/-- With the trinomial base case discharged, the exact estimate depends only
on the normalized non-base reduction. -/
theorem schinzel_support_bound_of_primitive_step
    (hstep : PrimitiveSchinzelInductionStep)
    (P : ℚ[X]) (hP : 2 ≤ termCount P) :
    termCount P ≤ B (termCount (P ^ 2)) :=
  schinzel_support_bound_of_primitive primitiveTrinomialProperty hstep P hP

/-- Exact estimate conditional only on the recursive output of generic
specialization. -/
theorem schinzel_support_bound_of_deformation_recursive
    (hrecursive : DeformationRecursiveProperty)
    (P : ℚ[X]) (hP : 2 ≤ termCount P) :
    termCount P ≤ B (termCount (P ^ 2)) :=
  schinzel_support_bound_of_primitive_step
    (primitiveSchinzelInductionStep_of_deformation hrecursive) P hP

/-- Coarse subtraction-free form of Schinzel's estimate. -/
theorem schinzel_coarse_bound_of_reduction
    (hred : SchinzelReduction) (P : ℚ[X]) (hP : 2 ≤ termCount P) :
    termCount P ≤ 1 + 32 ^ (2 ^ termCount (P ^ 2)) :=
  (schinzel_support_bound_of_reduction hred P hP).trans
    (B_le_coarse (termCount (P ^ 2)))

/-- Direct normalized-input version of the coarse subtraction-free bound. -/
theorem schinzel_coarse_bound_of_primitive
    (hbase : PrimitiveTrinomialProperty)
    (hstep : PrimitiveSchinzelInductionStep)
    (P : ℚ[X]) (hP : 2 ≤ termCount P) :
    termCount P ≤ 1 + 32 ^ (2 ^ termCount (P ^ 2)) :=
  (schinzel_support_bound_of_primitive hbase hstep P hP).trans
    (B_le_coarse (termCount (P ^ 2)))

/-- Coarse estimate depending only on the normalized non-base reduction. -/
theorem schinzel_coarse_bound_of_primitive_step
    (hstep : PrimitiveSchinzelInductionStep)
    (P : ℚ[X]) (hP : 2 ≤ termCount P) :
    termCount P ≤ 1 + 32 ^ (2 ^ termCount (P ^ 2)) :=
  schinzel_coarse_bound_of_primitive primitiveTrinomialProperty hstep P hP

/-- Coarse estimate conditional only on recursive specialization. -/
theorem schinzel_coarse_bound_of_deformation_recursive
    (hrecursive : DeformationRecursiveProperty)
    (P : ℚ[X]) (hP : 2 ≤ termCount P) :
    termCount P ≤ 1 + 32 ^ (2 ^ termCount (P ^ 2)) :=
  (schinzel_support_bound_of_deformation_recursive hrecursive P hP).trans
    (B_le_coarse (termCount (P ^ 2)))

/-- Conditional end-to-end resolution, useful as the final integration
check for the algebraic reduction. -/
theorem erdos_485_of_reduction (hred : SchinzelReduction) :
    Filter.Tendsto f Filter.atTop Filter.atTop :=
  tendsto_f_atTop_of_uniform_bound (schinzel_coarse_bound_of_reduction hred)

/-- Normalized-input version of the conditional end-to-end resolution. -/
theorem erdos_485_of_primitive
    (hbase : PrimitiveTrinomialProperty)
    (hstep : PrimitiveSchinzelInductionStep) :
    Filter.Tendsto f Filter.atTop Filter.atTop :=
  tendsto_f_atTop_of_uniform_bound
    (schinzel_coarse_bound_of_primitive hbase hstep)

/-- End-to-end resolution depending only on the normalized non-base
reduction. -/
theorem erdos_485_of_primitive_step (hstep : PrimitiveSchinzelInductionStep) :
    Filter.Tendsto f Filter.atTop Filter.atTop :=
  erdos_485_of_primitive primitiveTrinomialProperty hstep

/-- End-to-end resolution conditional only on recursive specialization. -/
theorem erdos_485_of_deformation_recursive
    (hrecursive : DeformationRecursiveProperty) :
    Filter.Tendsto f Filter.atTop Filter.atTop :=
  tendsto_f_atTop_of_uniform_bound
    (schinzel_coarse_bound_of_deformation_recursive hrecursive)

/-! ## Unconditional Schinzel bound and resolution of Problem 485 -/

/-- The normalized non-base induction step, with all deformation,
squarefree-gap, and specialization inputs discharged. -/
theorem primitiveSchinzelInductionStep : PrimitiveSchinzelInductionStep :=
  primitiveSchinzelInductionStep_of_deformation deformationRecursiveProperty

/-- Schinzel's complete algebraic reduction for rational polynomials. -/
theorem schinzel_reduction : SchinzelReduction :=
  schinzelReduction_of_base_step
    (trinomialSquareProperty_of_primitive primitiveTrinomialProperty)
    (schinzelInductionStep_of_primitive primitiveSchinzelInductionStep)

/-- Schinzel's explicit support bound for squares of rational polynomials. -/
theorem schinzel_support_bound (P : ℚ[X]) (hP : 2 ≤ termCount P) :
    termCount P ≤ B (termCount (P ^ 2)) :=
  schinzel_support_bound_of_reduction schinzel_reduction P hP

/-- A subtraction-free coarse form of Schinzel's bound. -/
theorem schinzel_term_bound (P : ℚ[X]) (hP : 2 ≤ termCount P) :
    termCount P ≤ 1 + 32 ^ (2 ^ termCount (P ^ 2)) :=
  schinzel_coarse_bound_of_reduction schinzel_reduction P hP

/-- The final limit theorem, packaged for the top-level Problem 485 file. -/
theorem erdos_485_from_schinzel : Filter.Tendsto f Filter.atTop Filter.atTop :=
  erdos_485_of_reduction schinzel_reduction

end

end Erdos485
