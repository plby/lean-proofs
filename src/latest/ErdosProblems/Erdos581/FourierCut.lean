import ErdosProblems.Erdos581.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Data.Complex.BigOperators

/-!
# Erdős 581: a finite Fourier cut bound

The lemma in this file is an elementary Rayleigh-quotient argument, proved
directly from the orthogonal character basis of a finite abelian group.
-/

open Finset Set Function RCLike
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace

namespace Erdos581

noncomputable section

private lemma wInner_sum_left {ι κ : Type*} [Fintype ι]
    (s : Finset κ) (F : κ → ι → ℂ) (g : ι → ℂ) :
    ⟪∑ k ∈ s, F k, g⟫ₙ_[ℂ] = ∑ k ∈ s, ⟪F k, g⟫ₙ_[ℂ] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, ih, RCLike.wInner_add_left]

private lemma wInner_sum_right {ι κ : Type*} [Fintype ι]
    (s : Finset κ) (F : κ → ι → ℂ) (g : ι → ℂ) :
    ⟪g, ∑ k ∈ s, F k⟫ₙ_[ℂ] = ∑ k ∈ s, ⟪g, F k⟫ₙ_[ℂ] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, ih, RCLike.wInner_add_right]

/-- If a complex linear operator is diagonal with nonnegative real entries
in the finite character basis, then its quadratic form is nonnegative. -/
theorem characterEigenbasis_quadratic_nonneg
    {G : Type*} [AddCommGroup G] [Fintype G]
    (A : (G → ℂ) →ₗ[ℂ] (G → ℂ)) (μ : AddChar G ℂ → ℝ)
    (heig : ∀ ψ : AddChar G ℂ, A ψ = (μ ψ : ℂ) • (ψ : G → ℂ))
    (hμ : ∀ ψ, 0 ≤ μ ψ) (f : G → ℂ) :
    0 ≤ (⟪f, A f⟫ₙ_[ℂ]).re := by
  classical
  let B := AddChar.complexBasis G
  let c : AddChar G ℂ → ℂ := fun ψ ↦ B.repr f ψ
  have hf : (∑ ψ, c ψ • (ψ : G → ℂ)) = f := by
    simpa [B, c, AddChar.complexBasis_apply] using B.sum_repr f
  have hAf : A f = ∑ ψ, (c ψ * (μ ψ : ℂ)) • (ψ : G → ℂ) := by
    rw [← hf, map_sum]
    refine Finset.sum_congr rfl ?_
    intro ψ _
    rw [LinearMap.map_smul, heig]
    ext x
    simp [Pi.smul_apply, mul_assoc]
  have hquad : ⟪f, A f⟫ₙ_[ℂ] =
      ∑ ψ, (starRingEnd ℂ) (c ψ) * c ψ * (μ ψ : ℂ) := by
    rw [hAf, ← hf]
    rw [show ⟪∑ ψ, c ψ • (ψ : G → ℂ),
        ∑ φ, (c φ * (μ φ : ℂ)) • (φ : G → ℂ)⟫ₙ_[ℂ] =
        ∑ ψ, ⟪c ψ • (ψ : G → ℂ),
          ∑ φ, (c φ * (μ φ : ℂ)) • (φ : G → ℂ)⟫ₙ_[ℂ] by
      simpa using wInner_sum_left Finset.univ
        (fun ψ ↦ c ψ • (ψ : G → ℂ))
        (∑ φ, (c φ * (μ φ : ℂ)) • (φ : G → ℂ))]
    simp_rw [show ∀ ψ : AddChar G ℂ,
        ⟪c ψ • (ψ : G → ℂ),
          ∑ φ, (c φ * (μ φ : ℂ)) • (φ : G → ℂ)⟫ₙ_[ℂ] =
        ∑ φ, ⟪c ψ • (ψ : G → ℂ),
          (c φ * (μ φ : ℂ)) • (φ : G → ℂ)⟫ₙ_[ℂ] by
      intro ψ
      simpa using wInner_sum_right Finset.univ
        (fun φ ↦ (c φ * (μ φ : ℂ)) • (φ : G → ℂ))
        (c ψ • (ψ : G → ℂ))]
    simp_rw [RCLike.wInner_smul_left, RCLike.wInner_smul_right,
      AddChar.wInner_cWeight_eq_boole]
    simp [mul_assoc]
  rw [hquad, Complex.re_sum]
  refine Finset.sum_nonneg fun ψ _ ↦ ?_
  rw [← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact mul_nonneg (Complex.normSq_nonneg _) (hμ ψ)

/-- The adjacency-sum operator of a finite simple graph. -/
def adjacencyOperator {G : Type*} [Fintype G] [DecidableEq G]
    (X : SimpleGraph G) [DecidableRel X.Adj] :
    (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f x := ∑ y ∈ X.neighborFinset x, f y
  map_add' f g := by
    ext x
    simp [Finset.sum_add_distrib]
  map_smul' c f := by
    ext x
    simp [Finset.mul_sum]

@[simp] lemma adjacencyOperator_apply {G : Type*} [Fintype G]
    [DecidableEq G] (X : SimpleGraph G) [DecidableRel X.Adj]
    (f : G → ℂ) (x : G) :
    adjacencyOperator X f x = ∑ y ∈ X.neighborFinset x, f y := rfl

private noncomputable def signFunction {G : Type*} (s : Set G) : G → ℂ := by
  classical
  exact fun x ↦ if x ∈ s then 1 else -1

private lemma signFunction_mul {G : Type*} (s : Set G) (x y : G) :
    signFunction s x * signFunction s y =
      if (x ∈ s) ≠ (y ∈ s) then -1 else 1 := by
  by_cases hx : x ∈ s <;> by_cases hy : y ∈ s <;> simp [signFunction, hx, hy]

private lemma adjacency_quadratic_eq
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : SimpleGraph G) [DecidableRel X.Adj] (s : Set G) :
    (∑ x, signFunction s x * adjacencyOperator X (signFunction s) x) =
      (((2 * X.edgeFinset.card : ℤ) -
        4 * (cutGraph X s).edgeSet.ncard : ℤ) : ℂ) := by
  classical
  let P : Finset (G × G) := Finset.univ.filter fun p ↦ X.Adj p.1 p.2
  let C : Finset (G × G) := P.filter fun p ↦ (p.1 ∈ s) ≠ (p.2 ∈ s)
  have hdouble :
      (∑ x, signFunction s x * adjacencyOperator X (signFunction s) x) =
        ∑ p ∈ P, signFunction s p.1 * signFunction s p.2 := by
    simp only [adjacencyOperator_apply, Finset.mul_sum]
    calc
      (∑ x, ∑ i ∈ X.neighborFinset x, signFunction s x * signFunction s i) =
          ∑ x, ∑ i, if X.Adj x i then
            signFunction s x * signFunction s i else 0 := by
              refine Finset.sum_congr rfl ?_
              intro x _
              rw [← Finset.sum_filter]
              congr 1
              ext i
              simp
      _ = ∑ p : G × G, if X.Adj p.1 p.2 then
            signFunction s p.1 * signFunction s p.2 else 0 := by
              rw [Fintype.sum_prod_type]
      _ = ∑ p ∈ P, signFunction s p.1 * signFunction s p.2 := by
              rw [Finset.sum_filter]
  have hPcard : P.card = 2 * X.edgeFinset.card := by
    simpa [P] using X.two_mul_card_edgeFinset.symm
  have hCcard : C.card = 2 * (cutGraph X s).edgeFinset.card := by
    have h := (cutGraph X s).two_mul_card_edgeFinset.symm
    simpa [C, P, Finset.filter_filter, cutGraph_adj, and_assoc, and_left_comm,
      and_comm] using h
  have hedgecard : (cutGraph X s).edgeFinset.card =
      (cutGraph X s).edgeSet.ncard := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [hdouble]
  calc
    (∑ p ∈ P, signFunction s p.1 * signFunction s p.2) =
        ∑ p ∈ P, ((1 : ℂ) - 2 * if (p.1 ∈ s) ≠ (p.2 ∈ s) then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [signFunction_mul]
          by_cases hcross : (p.1 ∈ s) ≠ (p.2 ∈ s) <;>
            simp [hcross] <;> norm_num
    _ = (P.card : ℂ) - 2 * (C.card : ℂ) := by
          rw [Finset.sum_sub_distrib]
          have hone : (∑ _p ∈ P, (1 : ℂ)) = P.card := by simp
          have hind :
              (∑ p ∈ P, (if (p.1 ∈ s) ≠ (p.2 ∈ s) then (1 : ℂ) else 0)) =
                C.card := by
                  rw [← Finset.sum_filter]
                  simp [C]
          rw [hone, ← Finset.mul_sum, hind]
    _ = (((2 * X.edgeFinset.card : ℤ) -
        4 * (cutGraph X s).edgeSet.ncard : ℤ) : ℂ) := by
          rw [hPcard, hCcard, hedgecard]
          push_cast
          ring

/-- Spectral Max-Cut inequality, in the character-diagonal form needed for
the characteristic-two Cayley blocks. -/
theorem cut_le_of_character_eigenvalues
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (X : SimpleGraph G) [DecidableRel X.Adj]
    (eigval : AddChar G ℂ → ℝ) (L : ℝ)
    (heig : ∀ ψ : AddChar G ℂ,
      adjacencyOperator X ψ = (eigval ψ : ℂ) • (ψ : G → ℂ))
    (hlower : ∀ ψ, -L ≤ eigval ψ) (s : Set G) :
    ((cutGraph X s).edgeSet.ncard : ℝ) ≤
      (X.edgeFinset.card : ℝ) / 2 + L * Fintype.card G / 4 := by
  classical
  let A : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
    adjacencyOperator X + (L : ℂ) • LinearMap.id
  let μ : AddChar G ℂ → ℝ := fun ψ ↦ eigval ψ + L
  have heigA : ∀ ψ : AddChar G ℂ,
      A ψ = (μ ψ : ℂ) • (ψ : G → ℂ) := by
    intro ψ
    ext x
    simp only [A, μ, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply, Pi.add_apply, Pi.smul_apply]
    rw [congr_fun (heig ψ) x]
    simp only [Pi.smul_apply]
    push_cast
    ring
  have hμ : ∀ ψ, 0 ≤ μ ψ := by
    intro ψ
    dsimp [μ]
    linarith [hlower ψ]
  let z : G → ℂ := signFunction s
  have hpos : 0 ≤ (⟪z, A z⟫ₙ_[ℂ]).re :=
    characterEigenbasis_quadratic_nonneg A μ heigA hμ z
  have hsum :
      (∑ x, A z x * (starRingEnd ℂ) (z x)) =
        (((2 * X.edgeFinset.card : ℤ) -
          4 * (cutGraph X s).edgeSet.ncard : ℤ) : ℂ) +
            (L : ℂ) * Fintype.card G := by
    have hadj := adjacency_quadratic_eq X s
    change (∑ x, A z x * (starRingEnd ℂ) (z x)) = _
    calc
      (∑ x, A z x * (starRingEnd ℂ) (z x)) =
          (∑ x, signFunction s x *
            adjacencyOperator X (signFunction s) x) +
              ∑ _x : G, (L : ℂ) := by
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl ?_
                intro x _
                by_cases hx : x ∈ s <;>
                  simp [A, z, signFunction, hx, mul_add, mul_comm, mul_left_comm,
                    mul_assoc]
      _ = (((2 * X.edgeFinset.card : ℤ) -
          4 * (cutGraph X s).edgeSet.ncard : ℤ) : ℂ) +
            (L : ℂ) * Fintype.card G := by
              rw [hadj]
              simp
              ring
  have hinner : (⟪z, A z⟫ₙ_[ℂ]).re =
      (Fintype.card G : ℝ)⁻¹ *
        ((2 * X.edgeFinset.card : ℝ) -
          4 * (cutGraph X s).edgeSet.ncard + L * Fintype.card G) := by
    rw [RCLike.wInner_cWeight_eq_expect, Fintype.expect_eq_sum_div_card]
    simp only [RCLike.inner_apply]
    rw [hsum]
    simp only [div_eq_inv_mul, Complex.mul_re, Complex.inv_re,
      Complex.natCast_re, Complex.natCast_im, Complex.add_re, Complex.intCast_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
      Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Nat.cast_ofNat]
    norm_num
  rw [hinner] at hpos
  have hn : 0 < (Fintype.card G : ℝ) := by positivity
  have hmain : 0 ≤ (2 * X.edgeFinset.card : ℝ) -
      4 * (cutGraph X s).edgeSet.ncard + L * Fintype.card G := by
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hpos) (inv_pos.mpr hn)
  nlinarith

end

end Erdos581
