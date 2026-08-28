import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrixAlgebra
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

/-! # Complex unitary matrices as the centralizer of the scalar quaternion i -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres

namespace QuaternionicComplexPlane

local notation "ℍ" => Quaternion ℝ

def complexPart (q : ℍ) : ℂ := ⟨q.re, q.imI⟩

theorem coe_complexPart {q : ℍ} (hq : QuaternionicScalars.i * q = q * QuaternionicScalars.i) :
    (complexPart q : ℍ) = q := by
  rcases q with ⟨a, b, c, d⟩
  have hq' : (QuaternionAlgebra.mk 0 1 0 0 : QuaternionAlgebra ℝ (-1) 0 (-1)) *
      QuaternionAlgebra.mk a b c d =
        QuaternionAlgebra.mk a b c d * QuaternionAlgebra.mk 0 1 0 0 := hq
  have hc := congrArg QuaternionAlgebra.imK hq'
  have hd := congrArg QuaternionAlgebra.imJ hq'
  norm_num at hc hd
  have hc0 : c = 0 := by linarith
  have hd0 : d = 0 := by linarith
  subst c d
  rfl

theorem coeComplex_star (z : ℂ) : ((star z : ℂ) : ℍ) = star (z : ℍ) := by
  ext <;> simp

theorem embed_mul_coeComplex_star (z w : ℂ) :
    embed z * ((star w : ℂ) : ℍ) = embed (z * w) := by
  rw [embed, mul_assoc, j_mul_coeComplex, star_star, ← mul_assoc,
    ← Quaternion.coeComplex_mul]
  rfl

end QuaternionicComplexPlane

namespace QuaternionicSymmetricMatrices

open QuaternionicComplexPlane QuaternionicColumns

local notation "ℍ" => Quaternion ℝ

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem complexInclusion_star (B : Matrix N N ℂ) :
    complexInclusion (star B) = star (complexInclusion B) := by
  apply Matrix.ext
  intro r s
  exact coeComplex_star (B s r)

theorem exists_complex_unitary_of_commute (U : SpGroup N)
    (hU : Matrix.diagonal (fun _ : N ↦ QuaternionicScalars.i) * U.val =
      U.val * Matrix.diagonal (fun _ : N ↦ QuaternionicScalars.i)) :
    ∃ V : unitary (Matrix N N ℂ), complexInclusion V.val = U.val := by
  let V : Matrix N N ℂ := U.val.map complexPart
  have hV : complexInclusion V = U.val := by
    apply Matrix.ext
    intro r s
    apply coe_complexPart
    have h := congrArg (fun A : Matrix N N ℍ ↦ A r s) hU
    simpa only [Matrix.diagonal_mul, Matrix.mul_diagonal] using h
  have hunit : V ∈ unitary (Matrix N N ℂ) := by
    constructor
    · apply complexInclusion_injective
      rw [map_mul, complexInclusion_star, hV, map_one]
      exact Unitary.star_mul_self_of_mem U.property
    · apply complexInclusion_injective
      rw [map_mul, complexInclusion_star, hV, map_one]
      exact Unitary.mul_star_self_of_mem U.property
  exact ⟨⟨V, hunit⟩, hV⟩

theorem quaternionMatrix_mul_left (B C : Matrix N N ℂ) :
    quaternionMatrix (B * C) = complexInclusion B * quaternionMatrix C := by
  apply Matrix.ext
  intro r s
  change ((∑ k, B r k * C k s : ℂ) : ℍ) * QuaternionicScalars.j =
    ∑ k, (B r k : ℍ) * embed (C k s)
  have hsum : ((∑ k, B r k * C k s : ℂ) : ℍ) = ∑ k, ((B r k * C k s : ℂ) : ℍ) :=
    map_sum Quaternion.ofComplex _ _
  rw [hsum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [Quaternion.coeComplex_mul, mul_assoc]
  rfl

theorem quaternionMatrix_mul_transpose (B U : Matrix N N ℂ) :
    quaternionMatrix (B * U.transpose) = quaternionMatrix B * star (complexInclusion U) := by
  apply Matrix.ext
  intro r s
  change ((∑ k, B r k * U s k : ℂ) : ℍ) * QuaternionicScalars.j =
    ∑ k, embed (B r k) * star (U s k : ℍ)
  have hsum : ((∑ k, B r k * U s k : ℂ) : ℍ) = ∑ k, ((B r k * U s k : ℂ) : ℍ) :=
    map_sum Quaternion.ofComplex _ _
  rw [hsum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [← coeComplex_star, embed_mul_coeComplex_star]
  rfl

theorem quaternionMatrix_mul_self_transpose (U : Matrix N N ℂ) :
    quaternionMatrix (U * U.transpose) = complexInclusion U *
      Matrix.diagonal (fun _ : N ↦ QuaternionicScalars.j) * star (complexInclusion U) := by
  rw [quaternionMatrix_mul_transpose]
  have h : quaternionMatrix U = complexInclusion U *
      Matrix.diagonal (fun _ : N ↦ QuaternionicScalars.j) := by
    simpa only [mul_one, quaternionMatrix_identity] using quaternionMatrix_mul_left U 1
  rw [h]

end QuaternionicSymmetricMatrices

end Wikipedia.HomotopyGroupsOfSpheres
