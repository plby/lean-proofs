import ErdosProblems.Erdos1148.QuadraticFormEmbedding
import ErdosProblems.Erdos1148.SharedPrimitivePeriod

/-! # Integral matrices in the rational embedding of an integral form -/

namespace Erdos1148.DukeArithmetic

def integralRationalMatrices : Subring (Matrix (Fin 2) (Fin 2) ℚ) :=
  (Int.castRingHom ℚ).mapMatrix.range

lemma mem_integralRationalMatrices_iff (M : Matrix (Fin 2) (Fin 2) ℚ) :
    M ∈ integralRationalMatrices ↔
      ∃ N : Matrix (Fin 2) (Fin 2) ℤ, N.map (Int.castRingHom ℚ) = M := by
  rfl

lemma discr_rat_mapCoeffs {d : ℤ} {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    discr (mapCoeffs (Int.castRingHom ℚ) t) = (d : ℚ) := by
  rw [discr_mapCoeffs, ht]
  rfl

noncomputable def integralFormFieldEmbedding {d : ℤ} {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    QuadraticDiscrAlgebra d →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ :=
  quadraticFormEmbedding (discr_rat_mapCoeffs ht)

lemma integralFormFieldEmbedding_apply {d : ℤ} {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    (w : QuadraticDiscrAlgebra d) :
    integralFormFieldEmbedding ht w = pellFormMatrix (mapCoeffs (Int.castRingHom ℚ) t) w.re w.im :=
  quadraticFormEmbedding_apply (discr_rat_mapCoeffs ht) w

lemma orderGenerator_image_integral {d : ℤ} {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    integralFormFieldEmbedding ht (quadraticOrderGenerator d) ∈ integralRationalMatrices := by
  obtain ⟨k, hk⟩ := ht ▸ even_middle_sub_discr t
  have hkQ : (t.2.1 : ℚ) - d = (k : ℚ) + k := by exact_mod_cast hk
  rw [mem_integralRationalMatrices_iff]
  refine ⟨!![-k, -t.2.2; t.1, d + k], ?_⟩
  rw [integralFormFieldEmbedding_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    dsimp [Matrix.map, pellFormMatrix, mapCoeffs, quadraticOrderGenerator] <;> push_cast
  · linarith
  · ring
  · ring
  · linarith

lemma quadraticOrder_le_integral_preimage {d : ℤ} {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    quadraticOrder d ≤
      integralRationalMatrices.comap (integralFormFieldEmbedding ht).toRingHom := by
  apply Subring.closure_le.mpr
  intro w hw
  obtain rfl := Set.mem_singleton_iff.mp hw
  exact orderGenerator_image_integral ht

end Erdos1148.DukeArithmetic
