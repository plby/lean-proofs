/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 88: the structured quadratic calculation

This file formalizes the deterministic algebra in Section 12 of
Kwan--Sah--Sauermann--Sawhney.  The equal buckets are represented by a
product type `K × J`: `K` is the bucket index and `J` is the position in a
bucket.  `bucketProjection` is the matrix `Q` which replaces every
coordinate by the average in its bucket.

The deep probabilistic inputs of the paper (robust rank, the invariance
principle, and the two averaging claims) are deliberately not asserted here.
Instead, the assembly lemmas below accept their estimates as hypotheses and
prove the exact algebraic and numerical deductions made from them.
-/

open scoped BigOperators Matrix

namespace Erdos88
namespace Structured

universe u v w

section BucketProjection

variable (K : Type u) (J : Type v) [Fintype K] [Fintype J]
  [DecidableEq K] [DecidableEq J] [Nonempty J]

/-- The matrix which averages coordinates inside each equal bucket. -/
noncomputable def bucketProjection : Matrix (K × J) (K × J) ℝ :=
  fun i j ↦ if i.1 = j.1 then (Fintype.card J : ℝ)⁻¹ else 0

/-- Applying `Q` really is averaging over the second coordinate. -/
lemma bucketProjection_mulVec (x : K × J → ℝ) :
    bucketProjection K J *ᵥ x =
      fun i ↦ (∑ j : J, x (i.1, j)) / Fintype.card J := by
  funext i
  classical
  simp only [bucketProjection, Matrix.mulVec, dotProduct, div_eq_mul_inv,
    ← Finset.univ_product_univ, Finset.sum_product, Prod.fst, ite_mul, zero_mul]
  calc
    (∑ k : K, ∑ j : J,
        if i.1 = k then (Fintype.card J : ℝ)⁻¹ * x (k, j) else 0) =
        ∑ k : K, if i.1 = k then
          ∑ j : J, (Fintype.card J : ℝ)⁻¹ * x (k, j) else 0 := by
            apply Finset.sum_congr rfl
            intro k _
            by_cases h : i.1 = k <;> simp [h]
    _ = ∑ j : J, (Fintype.card J : ℝ)⁻¹ * x (i.1, j) := by simp
    _ = (∑ j : J, x (i.1, j)) * (Fintype.card J : ℝ)⁻¹ := by
      rw [← Finset.mul_sum]
      ring

/-- The bucket-averaging matrix is symmetric. -/
lemma bucketProjection_transpose :
    (bucketProjection K J)ᵀ = bucketProjection K J := by
  ext i j
  simp only [Matrix.transpose_apply, bucketProjection]
  by_cases h : i.1 = j.1
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- The bucket-averaging matrix is a projection. -/
lemma bucketProjection_mul_self :
    bucketProjection K J * bucketProjection K J = bucketProjection K J := by
  classical
  ext i j
  simp only [Matrix.mul_apply, bucketProjection]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  by_cases h : i.1 = j.1
  · rw [if_pos h]
    have hc : (Fintype.card J : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero (α := J)
    apply mul_right_cancel₀ hc
    rw [inv_mul_cancel₀ hc]
    rw [Finset.sum_mul]
    simp_rw [Finset.sum_mul]
    calc
      (∑ x : K, ∑ y : J,
          ((if i.1 = x then (Fintype.card J : ℝ)⁻¹ else 0) *
            if x = j.1 then (Fintype.card J : ℝ)⁻¹ else 0) *
            Fintype.card J) =
          ∑ x : K, ∑ y : J, if i.1 = x then
            (Fintype.card J : ℝ)⁻¹ else 0 := by
              apply Finset.sum_congr rfl
              intro x _
              apply Finset.sum_congr rfl
              intro y _
              by_cases hx : i.1 = x
              · have hxj : x = j.1 := hx.symm.trans h
                rw [if_pos hx, if_pos hxj]
                field_simp
              · rw [if_neg hx]
                simp
      _ = 1 := by
        simp [Fintype.card_ne_zero]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro l _
    by_cases hik : i.1 = k
    · have hkj : k ≠ j.1 := by
        intro h'
        exact h (hik.trans h')
      rw [if_pos hik, if_neg hkj, mul_zero]
    · rw [if_neg hik, zero_mul]

/-- Bucket averaging is idempotent, in operator form. -/
lemma bucketProjection_idempotent (x : K × J → ℝ) :
    bucketProjection K J *ᵥ (bucketProjection K J *ᵥ x) =
      bucketProjection K J *ᵥ x := by
  rw [Matrix.mulVec_mulVec, bucketProjection_mul_self]

/-- The sum of the centered coordinates in every bucket is zero. -/
lemma sum_sub_bucketProjection (x : K × J → ℝ) (k : K) :
    ∑ j : J, (x - bucketProjection K J *ᵥ x) (k, j) = 0 := by
  have hQ : ∀ j : J, (bucketProjection K J *ᵥ x) (k, j) =
      (∑ j : J, x (k, j)) / Fintype.card J := by
    intro j
    exact congr_fun (bucketProjection_mulVec K J x) (k, j)
  simp_rw [Pi.sub_apply, hQ]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card J : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

end BucketProjection

section ProjectionAlgebra

variable {I : Type w} [Fintype I] [DecidableEq I]

/-- A symmetric idempotent matrix, the algebraic interface used for `Q`. -/
structure IsOrthogonalProjection (Q : Matrix I I ℝ) : Prop where
  transpose_eq : Qᵀ = Q
  mul_self : Q * Q = Q

/-- The concrete equal-bucket averaging matrix satisfies the abstract
projection interface. -/
lemma bucketProjection_isOrthogonalProjection
    (K : Type u) (J : Type v) [Fintype K] [Fintype J]
    [DecidableEq K] [DecidableEq J] [Nonempty J] :
    IsOrthogonalProjection (bucketProjection K J) :=
  ⟨bucketProjection_transpose K J, bucketProjection_mul_self K J⟩

/-- `I-Q`, the projection onto the bucket-centered coordinates. -/
def centeredProjection (Q : Matrix I I ℝ) : Matrix I I ℝ := 1 - Q

/-- The bucket-average component `Delta = Qx`. -/
def delta (Q : Matrix I I ℝ) (x : I → ℝ) : I → ℝ := Q *ᵥ x

/-- The centered component `(I-Q)x`. -/
def residual (Q : Matrix I I ℝ) (x : I → ℝ) : I → ℝ :=
  centeredProjection Q *ᵥ x

lemma residual_eq_sub (Q : Matrix I I ℝ) (x : I → ℝ) :
    residual Q x = x - delta Q x := by
  simp [residual, centeredProjection, delta, Matrix.sub_mulVec]

lemma delta_add_residual (Q : Matrix I I ℝ) (x : I → ℝ) :
    delta Q x + residual Q x = x := by
  rw [residual_eq_sub]
  exact add_sub_cancel _ _

lemma centeredProjection_transpose {Q : Matrix I I ℝ}
    (hQ : IsOrthogonalProjection Q) :
    (centeredProjection Q)ᵀ = centeredProjection Q := by
  simp [centeredProjection, hQ.transpose_eq]

lemma centeredProjection_mul_self {Q : Matrix I I ℝ}
    (hQ : IsOrthogonalProjection Q) :
    centeredProjection Q * centeredProjection Q = centeredProjection Q := by
  simp only [centeredProjection]
  calc
    (1 - Q) * (1 - Q) = 1 - Q - Q + Q * Q := by noncomm_ring
    _ = 1 - Q := by rw [hQ.mul_self]; abel

lemma centeredProjection_delta_eq_zero {Q : Matrix I I ℝ}
    (hQ : IsOrthogonalProjection Q) (x : I → ℝ) :
    centeredProjection Q *ᵥ delta Q x = 0 := by
  rw [delta, Matrix.mulVec_mulVec]
  have h : centeredProjection Q * Q = 0 := by
    simp only [centeredProjection]
    calc
      (1 - Q) * Q = Q - Q * Q := by noncomm_ring
      _ = 0 := by rw [hQ.mul_self]; exact sub_self Q
  rw [h]
  exact Matrix.zero_mulVec x

lemma delta_residual_eq_zero {Q : Matrix I I ℝ}
    (hQ : IsOrthogonalProjection Q) (x : I → ℝ) :
    Q *ᵥ residual Q x = 0 := by
  rw [residual, Matrix.mulVec_mulVec]
  have h : Q * centeredProjection Q = 0 := by
    simp only [centeredProjection]
    calc
      Q * (1 - Q) = Q - Q * Q := by noncomm_ring
      _ = 0 := by rw [hQ.mul_self]; exact sub_self Q
  rw [h]
  exact Matrix.zero_mulVec x

/-- Self-adjointness of the centered projection, expressed as a dot-product
identity. -/
lemma dot_centeredProjection (Q : Matrix I I ℝ)
    (hQ : IsOrthogonalProjection Q) (u v : I → ℝ) :
    (centeredProjection Q *ᵥ u) ⬝ᵥ v =
      u ⬝ᵥ (centeredProjection Q *ᵥ v) := by
  calc
    (centeredProjection Q *ᵥ u) ⬝ᵥ v =
        v ⬝ᵥ (centeredProjection Q *ᵥ u) := dotProduct_comm _ _
    _ = v ⬝ᵥ ((centeredProjection Q)ᵀ *ᵥ u) := by
      rw [centeredProjection_transpose hQ]
    _ = u ⬝ᵥ (centeredProjection Q *ᵥ v) :=
      Matrix.dotProduct_transpose_mulVec _ _ _

/-- The centered matrix
`M* = (1/8) (I-Q) M (I-Q)` from KSSS Section 12. -/
noncomputable def mStar (Q M : Matrix I I ℝ) : Matrix I I ℝ :=
  (1 / 8 : ℝ) • (centeredProjection Q * M * centeredProjection Q)

/-- The centered linear coefficient
`w*_Delta = (1/2)(I-Q)(y + (1/2) M Delta)`. -/
noncomputable def wStar (Q M : Matrix I I ℝ) (y d : I → ℝ) : I → ℝ :=
  (1 / 2 : ℝ) •
    (centeredProjection Q *ᵥ (y + (1 / 2 : ℝ) • (M *ᵥ d)))

/-- The constant part after conditioning on `Delta`. -/
noncomputable def conditionalShift (E : ℝ) (M : Matrix I I ℝ) (y d : I → ℝ) : ℝ :=
  E + (1 / 2 : ℝ) * (y ⬝ᵥ d) + (1 / 8 : ℝ) * (d ⬝ᵥ (M *ᵥ d))

/-- The original quadratic random variable in the structured branch. -/
noncomputable def structuredQuadratic (E : ℝ) (M : Matrix I I ℝ)
    (y x : I → ℝ) : ℝ :=
  E + (1 / 2 : ℝ) * (y ⬝ᵥ x) + (1 / 8 : ℝ) * (x ⬝ᵥ (M *ᵥ x))

lemma wStar_dot (Q M : Matrix I I ℝ) (hQ : IsOrthogonalProjection Q)
    (y d x : I → ℝ) :
    wStar Q M y d ⬝ᵥ x =
      (1 / 2 : ℝ) * (y ⬝ᵥ residual Q x) +
        (1 / 4 : ℝ) * ((M *ᵥ d) ⬝ᵥ residual Q x) := by
  rw [wStar, smul_dotProduct, dot_centeredProjection Q hQ]
  rw [add_dotProduct, smul_dotProduct]
  norm_num
  rw [residual]
  ring

lemma dot_mStar (Q M : Matrix I I ℝ) (hQ : IsOrthogonalProjection Q)
    (x : I → ℝ) :
    x ⬝ᵥ (mStar Q M *ᵥ x) =
      (1 / 8 : ℝ) * (residual Q x ⬝ᵥ (M *ᵥ residual Q x)) := by
  rw [mStar, Matrix.smul_mulVec, dotProduct_smul]
  have hmul : (centeredProjection Q * M * centeredProjection Q) *ᵥ x =
      centeredProjection Q *ᵥ (M *ᵥ residual Q x) := by
    rw [residual, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [hmul]
  calc
    (1 / 8 : ℝ) *
        (x ⬝ᵥ centeredProjection Q *ᵥ (M *ᵥ residual Q x)) =
        (1 / 8 : ℝ) *
          ((centeredProjection Q *ᵥ (M *ᵥ residual Q x)) ⬝ᵥ x) := by
            rw [dotProduct_comm]
    _ = (1 / 8 : ℝ) *
          ((M *ᵥ residual Q x) ⬝ᵥ centeredProjection Q *ᵥ x) := by
            rw [dot_centeredProjection Q hQ]
    _ = (1 / 8 : ℝ) *
          (residual Q x ⬝ᵥ (M *ᵥ residual Q x)) := by
            rw [residual, dotProduct_comm]

lemma quadratic_add_of_symmetric (M : Matrix I I ℝ) (hM : Mᵀ = M)
    (d r : I → ℝ) :
    (d + r) ⬝ᵥ (M *ᵥ (d + r)) =
      d ⬝ᵥ (M *ᵥ d) + 2 * (r ⬝ᵥ (M *ᵥ d)) +
        r ⬝ᵥ (M *ᵥ r) := by
  have hcross : d ⬝ᵥ (M *ᵥ r) = r ⬝ᵥ (M *ᵥ d) := by
    calc
      d ⬝ᵥ (M *ᵥ r) = d ⬝ᵥ (Mᵀ *ᵥ r) := by rw [hM]
      _ = r ⬝ᵥ (M *ᵥ d) := Matrix.dotProduct_transpose_mulVec _ _ _
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
    hcross]
  ring

/-- Equation (12.3): after conditioning on `Delta = Qx`, the original
quadratic form is a constant shift plus a centered linear form and a
centered quadratic form. -/
theorem structured_decomposition (Q M : Matrix I I ℝ)
    (hQ : IsOrthogonalProjection Q) (hM : Mᵀ = M)
    (E : ℝ) (y x : I → ℝ) :
    structuredQuadratic E M y x =
      conditionalShift E M y (delta Q x) +
        wStar Q M y (delta Q x) ⬝ᵥ x +
          x ⬝ᵥ (mStar Q M *ᵥ x) := by
  let d := delta Q x
  let r := residual Q x
  have hx : x = d + r := by
    exact (delta_add_residual Q x).symm
  have hquad := quadratic_add_of_symmetric M hM d r
  have hw := wStar_dot Q M hQ y d x
  have hm := dot_mStar Q M hQ x
  have hy : y ⬝ᵥ x = y ⬝ᵥ d + y ⬝ᵥ r := by
    rw [hx, dotProduct_add]
  have hquadX : x ⬝ᵥ (M *ᵥ x) =
      d ⬝ᵥ (M *ᵥ d) + 2 * (r ⬝ᵥ (M *ᵥ d)) +
        r ⬝ᵥ (M *ᵥ r) := by
    rw [hx]
    exact hquad
  have hr : residual Q x = r := rfl
  rw [structuredQuadratic, conditionalShift, hw, hm]
  rw [hy, hquadX, hr]
  rw [dotProduct_comm (M *ᵥ d) r]
  ring

/-- The centered coefficient is orthogonal to the bucket-constant space. -/
lemma delta_wStar_eq_zero (Q M : Matrix I I ℝ)
    (hQ : IsOrthogonalProjection Q) (y d : I → ℝ) :
    Q *ᵥ wStar Q M y d = 0 := by
  rw [wStar, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  have h : Q * centeredProjection Q = 0 := by
    simp only [centeredProjection]
    calc
      Q * (1 - Q) = Q - Q * Q := by noncomm_ring
      _ = 0 := by rw [hQ.mul_self]; exact sub_self Q
  rw [h, Matrix.zero_mulVec]
  exact smul_zero _

/-- `M*` kills every bucket-constant vector. -/
lemma mStar_delta_eq_zero (Q M : Matrix I I ℝ)
    (hQ : IsOrthogonalProjection Q) (x : I → ℝ) :
    mStar Q M *ᵥ delta Q x = 0 := by
  rw [mStar]
  rw [Matrix.smul_mulVec]
  have hz := centeredProjection_delta_eq_zero hQ x
  rw [show centeredProjection Q * M * centeredProjection Q =
      centeredProjection Q * (M * centeredProjection Q) by rw [Matrix.mul_assoc]]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz,
    Matrix.mulVec_zero, Matrix.mulVec_zero]
  exact smul_zero _

end ProjectionAlgebra

section ConditionalMoments

universe z

variable {Ω : Type z} [Fintype Ω] [Nonempty Ω]

/-- Uniform expectation on a nonempty finite space. -/
noncomputable def finiteMean (X : Ω → ℝ) : ℝ :=
  (∑ ω, X ω) / Fintype.card Ω

/-- Uniform variance on a nonempty finite space. -/
noncomputable def finiteVariance (X : Ω → ℝ) : ℝ :=
  finiteMean (fun ω ↦ (X ω - finiteMean X) ^ 2)

lemma finiteMean_const (c : ℝ) : finiteMean (fun _ : Ω ↦ c) = c := by
  simp only [finiteMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

lemma finiteMean_add (X Y : Ω → ℝ) :
    finiteMean (fun ω ↦ X ω + Y ω) = finiteMean X + finiteMean Y := by
  simp only [finiteMean, Finset.sum_add_distrib]
  ring

lemma finiteMean_add_const (X : Ω → ℝ) (c : ℝ) :
    finiteMean (fun ω ↦ c + X ω) = c + finiteMean X := by
  rw [finiteMean_add, finiteMean_const]

lemma finiteVariance_add_const (X : Ω → ℝ) (c : ℝ) :
    finiteVariance (fun ω ↦ c + X ω) = finiteVariance X := by
  rw [finiteVariance, finiteMean_add_const]
  congr 1
  funext ω
  ring

/-- Conditional-mean formula obtained from (12.3), on any explicitly
supplied finite fibre of outcomes with fixed `Delta`. -/
lemma conditional_mean_formula {I : Type w} [Fintype I] [DecidableEq I]
    (Q M : Matrix I I ℝ) (hQ : IsOrthogonalProjection Q) (hM : Mᵀ = M)
    (E : ℝ) (y d : I → ℝ) (x : Ω → I → ℝ)
    (hdelta : ∀ ω, delta Q (x ω) = d) :
    finiteMean (fun ω ↦ structuredQuadratic E M y (x ω)) =
      conditionalShift E M y d +
        finiteMean (fun ω ↦
          wStar Q M y d ⬝ᵥ x ω + x ω ⬝ᵥ (mStar Q M *ᵥ x ω)) := by
  have hfun : (fun ω ↦ structuredQuadratic E M y (x ω)) =
      fun ω ↦ conditionalShift E M y d +
        (wStar Q M y d ⬝ᵥ x ω + x ω ⬝ᵥ (mStar Q M *ᵥ x ω)) := by
    funext ω
    rw [structured_decomposition Q M hQ hM, hdelta ω]
    ring
  rw [hfun, finiteMean_add_const]

/-- Conditional variance is unaffected by the deterministic conditional
shift in (12.3). -/
lemma conditional_variance_formula {I : Type w} [Fintype I] [DecidableEq I]
    (Q M : Matrix I I ℝ) (hQ : IsOrthogonalProjection Q) (hM : Mᵀ = M)
    (E : ℝ) (y d : I → ℝ) (x : Ω → I → ℝ)
    (hdelta : ∀ ω, delta Q (x ω) = d) :
    finiteVariance (fun ω ↦ structuredQuadratic E M y (x ω)) =
      finiteVariance (fun ω ↦
        wStar Q M y d ⬝ᵥ x ω + x ω ⬝ᵥ (mStar Q M *ᵥ x ω)) := by
  have hfun : (fun ω ↦ structuredQuadratic E M y (x ω)) =
      fun ω ↦ conditionalShift E M y d +
        (wStar Q M y d ⬝ᵥ x ω + x ω ⬝ᵥ (mStar Q M *ᵥ x ω)) := by
    funext ω
    rw [structured_decomposition Q M hQ hM, hdelta ω]
    ring
  rw [hfun, finiteVariance_add_const]

end ConditionalMoments

section NumericalAssembly

universe t

/-- Squared Frobenius norm, written as the finite sum used in (12.4)--(12.5). -/
noncomputable def matrixSqNorm {I : Type t} [Fintype I]
    (M : Matrix I I ℝ) : ℝ :=
  ∑ i, ∑ j, (M i j) ^ 2

/-- Squared Euclidean norm of a coefficient vector. -/
noncomputable def vectorSqNorm {I : Type t} [Fintype I]
    (w : I → ℝ) : ℝ :=
  ∑ i, (w i) ^ 2

lemma matrixSqNorm_nonneg {I : Type t} [Fintype I]
    (M : Matrix I I ℝ) : 0 ≤ matrixSqNorm M := by
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma vectorSqNorm_nonneg {I : Type t} [Fintype I]
    (w : I → ℝ) : 0 ≤ vectorSqNorm w := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- Turns the `O(error)` statement in the conditional variance formula
into the two inequalities actually used later.  The analytic estimate is
an explicit hypothesis. -/
lemma conditional_variance_interval {sigmaSq frobSq weightSq error : ℝ}
    (hmoment : |sigmaSq - (2 * frobSq + weightSq)| ≤ error) :
    2 * frobSq + weightSq - error ≤ sigmaSq ∧
      sigmaSq ≤ 2 * frobSq + weightSq + error := by
  rcases abs_le.mp hmoment with ⟨hlower, hupper⟩
  constructor <;> linarith

/-- The deterministic deduction from the conditional variance estimate
(12.5) and robust rank: a nonnegative standard deviation whose square has
the required lower bound is itself linear in `n`. -/
lemma sigma_lower_bound {sigma c n : ℝ} (hsigma : 0 ≤ sigma)
    (hc : 0 ≤ c) (hn : 0 ≤ n) (hvar : (c * n) ^ 2 ≤ sigma ^ 2) :
    c * n ≤ sigma := by
  nlinarith

/-- Upper counterpart used in the near-balanced range. -/
lemma sigma_upper_bound {sigma U : ℝ} (hsigma : 0 ≤ sigma)
    (hU : 0 ≤ U) (hvar : sigma ^ 2 ≤ U ^ 2) : sigma ≤ U := by
  nlinarith

/-- Robust rank plus the conditional moment estimate gives the linear
lower bound on the conditional standard deviation in (12.5). -/
lemma sigma_lower_from_robust_rank
    {sigma frobSq weightSq error c n : ℝ}
    (hsigma : 0 ≤ sigma) (hc : 0 ≤ c) (hn : 0 ≤ n)
    (hfrob : (c * n) ^ 2 ≤ frobSq) (hweight : 0 ≤ weightSq)
    (herror : error ≤ (c * n) ^ 2)
    (hmoment : |sigma ^ 2 - (2 * frobSq + weightSq)| ≤ error) :
    c * n ≤ sigma := by
  have hlower := (conditional_variance_interval hmoment).1
  apply sigma_lower_bound hsigma hc hn
  nlinarith

/-- The lower-bound multiplication in the structured averaging argument.
The hypotheses are precisely the probability of the good shift event and
the conditional point probability supplied by Claim 12.1. -/
lemma structured_lower_assembly
    {eventProb conditionalProb a b K sigma scale : ℝ}
    (hK : 0 < K) (hsigma : 0 < sigma) (hscale : 0 < scale)
    (hevent : a * sigma / scale ≤ eventProb)
    (hconditional : b / (K ^ 2 * sigma) ≤ conditionalProb)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hevent_nonneg : 0 ≤ eventProb) (_hcond_nonneg : 0 ≤ conditionalProb) :
    a * b / K ^ 2 / scale ≤ eventProb * conditionalProb := by
  have hprod := mul_le_mul hevent hconditional
    (by positivity : 0 ≤ b / (K ^ 2 * sigma)) hevent_nonneg
  calc
    a * b / K ^ 2 / scale =
        (a * sigma / scale) * (b / (K ^ 2 * sigma)) := by
          field_simp
    _ ≤ eventProb * conditionalProb := hprod

/-- Weighted law-of-total-probability upper assembly.  `cond d` is the
conditional window probability at a fixed bucket-count vector, and the
last hypothesis is the quantitative output of the dyadic Claim 12.2
summation. -/
lemma structured_upper_assembly {D : Type u} [Fintype D]
    (weight cond majorant : D → ℝ) (target : ℝ)
    (hweight : ∀ d, 0 ≤ weight d)
    (hcond : ∀ d, cond d ≤ majorant d)
    (haverage : (∑ d, weight d * majorant d) ≤ target) :
    (∑ d, weight d * cond d) ≤ target := by
  apply le_trans (Finset.sum_le_sum fun d _ ↦
    mul_le_mul_of_nonneg_left (hcond d) (hweight d)) haverage

/-- Exact finite law of total probability when the outer weights sum to
one.  This is the algebraic averaging identity used after conditioning on
the bucket-count vector `Delta`. -/
lemma weighted_total_probability {D : Type u} [Fintype D]
    (weight cond : D → ℝ) (hsum : ∑ d, weight d = 1) (c : ℝ)
    (hcond : ∀ d, cond d = c) :
    (∑ d, weight d * cond d) = c := by
  simp_rw [hcond]
  rw [← Finset.sum_mul, hsum, one_mul]

end NumericalAssembly

end Structured
end Erdos88
