import ErdosProblems.Erdos941.QuaternionCentralizer
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-! # The imaginary quadratic field attached to an integral sphere -/

namespace Erdos941

open scoped Quaternion

abbrev SphereQuadraticField (n : ℕ) := QuadraticAlgebra ℚ (-(n : ℚ)) 0

instance sphereQuadraticField_noRoot (n : ℕ) [hn : Fact (0 < n)] :
    Fact (∀ r : ℚ, r ^ 2 ≠ -(n : ℚ) + 0 * r) := by
  refine ⟨fun r hr => ?_⟩
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn.out
  nlinarith [sq_nonneg r]

instance sphereQuadraticField_numberField (n : ℕ) [Fact (0 < n)] :
    NumberField (SphereQuadraticField n) where

theorem sphereQuadraticField_finrank (n : ℕ) :
    Module.finrank ℚ (SphereQuadraticField n) = 2 :=
  QuadraticAlgebra.finrank_eq_two _ _

theorem pureQuaternion_mul_self (v : Triple) :
    pureQuaternion v * pureQuaternion v = -(tripleNorm v : ℚ) • (1 : ℍ[ℚ]) := by
  apply Quaternion.ext
  · rw [Quaternion.re_mul, Quaternion.re_smul]
    dsimp [pureQuaternion, tripleNorm, norm3]
    push_cast
    ring
  · rw [Quaternion.imI_mul, Quaternion.imI_smul]
    simp [pureQuaternion, mul_comm]
  · rw [Quaternion.imJ_mul, Quaternion.imJ_smul]
    simp [pureQuaternion, mul_comm]
  · rw [Quaternion.imK_mul, Quaternion.imK_smul]
    simp [pureQuaternion, mul_comm]

def sphereFieldEmbedding {v : Triple} {n : ℕ} (hv : tripleNorm v = n) :
    SphereQuadraticField n →ₐ[ℚ] ℍ[ℚ] :=
  QuadraticAlgebra.lift ⟨pureQuaternion v, by
    rw [pureQuaternion_mul_self, hv]
    simp⟩

theorem sphereFieldEmbedding_apply {v : Triple} {n : ℕ} (hv : tripleNorm v = n)
    (z : SphereQuadraticField n) :
    sphereFieldEmbedding hv z = z.re • (1 : ℍ[ℚ]) + z.im • pureQuaternion v := rfl

@[simp] theorem sphereFieldEmbedding_re {v : Triple} {n : ℕ} (hv : tripleNorm v = n)
    (z : SphereQuadraticField n) : (sphereFieldEmbedding hv z).re = z.re := by
  rw [sphereFieldEmbedding_apply, Quaternion.re_add, Quaternion.re_smul, Quaternion.re_smul]
  simp [pureQuaternion]

@[simp] theorem sphereFieldEmbedding_imI {v : Triple} {n : ℕ} (hv : tripleNorm v = n)
    (z : SphereQuadraticField n) : (sphereFieldEmbedding hv z).imI = z.im * (v.1 : ℚ) := by
  rw [sphereFieldEmbedding_apply, Quaternion.imI_add, Quaternion.imI_smul, Quaternion.imI_smul]
  simp [pureQuaternion]

@[simp] theorem sphereFieldEmbedding_imJ {v : Triple} {n : ℕ} (hv : tripleNorm v = n)
    (z : SphereQuadraticField n) : (sphereFieldEmbedding hv z).imJ = z.im * (v.2.1 : ℚ) := by
  rw [sphereFieldEmbedding_apply, Quaternion.imJ_add, Quaternion.imJ_smul, Quaternion.imJ_smul]
  simp [pureQuaternion]

@[simp] theorem sphereFieldEmbedding_imK {v : Triple} {n : ℕ} (hv : tripleNorm v = n)
    (z : SphereQuadraticField n) : (sphereFieldEmbedding hv z).imK = z.im * (v.2.2 : ℚ) := by
  rw [sphereFieldEmbedding_apply, Quaternion.imK_add, Quaternion.imK_smul, Quaternion.imK_smul]
  simp [pureQuaternion]

theorem sphereFieldEmbedding_omega {v : Triple} {n : ℕ} (hv : tripleNorm v = n) :
    sphereFieldEmbedding hv QuadraticAlgebra.omega = pureQuaternion v := by
  rw [sphereFieldEmbedding_apply]
  simp

theorem sphereFieldEmbedding_range {v : Triple} {n : ℕ} (hv : tripleNorm v = n)
    (hv0 : v ≠ 0) (q : ℍ[ℚ]) :
    q ∈ (sphereFieldEmbedding hv).range ↔ q * pureQuaternion v = pureQuaternion v * q := by
  rw [pureQuaternion_commutes_iff hv0 q]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.re, z.im, sphereFieldEmbedding_apply hv z⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨⟨a, b⟩, rfl⟩

theorem sphereFieldEmbedding_injective {v : Triple} {n : ℕ} [Fact (0 < n)]
    (hv : tripleNorm v = n) : Function.Injective (sphereFieldEmbedding hv) :=
  (sphereFieldEmbedding hv).injective

/-- The order cut out by the Hurwitz lattice in the quadratic subfield. -/
def sphereQuadraticOrder {v : Triple} {n : ℕ} (hv : tripleNorm v = n) :
    Subring (SphereQuadraticField n) :=
  hurwitzOrder.comap (sphereFieldEmbedding hv).toRingHom

theorem sphereQuadraticOrder_omega_mem {v : Triple} {n : ℕ} (hv : tripleNorm v = n) :
    QuadraticAlgebra.omega ∈ sphereQuadraticOrder hv := by
  change sphereFieldEmbedding hv QuadraticAlgebra.omega ∈ hurwitzOrder
  rw [sphereFieldEmbedding_omega]
  exact pureQuaternion_mem v

end Erdos941
