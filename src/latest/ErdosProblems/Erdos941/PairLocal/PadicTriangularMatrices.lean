/- Adapted from the checked repository proof in Erdos1148/PadicTriangularMatrices.lean. -/
import ErdosProblems.Erdos941.PairLocal.TriangularMatrices
import ErdosProblems.Erdos941.PairLocal.ResidueFibers

/-!
# Finite residue parameters for triangular p-adic matrices

The diagonal parameter is reduced to a power of `p`, and the off-diagonal
parameter to its residue modulo that power. Thus each depth has finitely
many matrix representatives.
-/

namespace Erdos941.PairLocal

lemma reduce_padic_triangular_matrix (p : ℕ) [Fact p.Prime]
    (δ z : PadicInt p) (hδ : δ ≠ 0) :
    ∃ (V : Matrix (Fin 2) (Fin 2) (PadicInt p)) (n : ℕ) (w : ZMod (p ^ n)),
      IsUnit V.det ∧ V * neighborMatrix δ z =
        neighborMatrix ((p : PadicInt p) ^ n) (w.val : PadicInt p) := by
  let n := δ.valuation
  let u := PadicInt.unitCoeff hδ
  let w := PadicInt.toZModPow n z
  have hz : (p : PadicInt p) ^ n ∣ z - (w.val : PadicInt p) := by
    apply (padic_pow_dvd_sub_iff_reduction_eq p n _ _).mpr
    simp [w]
  obtain ⟨q, hq⟩ := hz
  have huδ : (↑u⁻¹ : PadicInt p) * δ = (p : PadicInt p) ^ n := by
    rw [PadicInt.unitCoeff_spec hδ]
    change (↑u⁻¹ : PadicInt p) * ((u : PadicInt p) * (p : PadicInt p) ^ n) = _
    rw [← mul_assoc, Units.inv_mul, one_mul]
  let V : Matrix (Fin 2) (Fin 2) (PadicInt p) := !![1, -q * (↑u⁻¹ : PadicInt p); 0, ↑u⁻¹]
  refine ⟨V, n, w, ?_, ?_⟩
  · have hdet : V.det = (↑u⁻¹ : PadicInt p) := by simp [V, Matrix.det_fin_two]
    rw [hdet]
    exact Units.isUnit _
  · ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j
    · change 1 * 1 + (-q * (↑u⁻¹ : PadicInt p)) * 0 = 1
      ring
    · change 1 * z + (-q * (↑u⁻¹ : PadicInt p)) * δ = (w.val : PadicInt p)
      linear_combination hq - q * huδ
    · change 0 * 1 + (↑u⁻¹ : PadicInt p) * 0 = 0
      ring
    · change 0 * z + (↑u⁻¹ : PadicInt p) * δ = (p : PadicInt p) ^ n
      simpa only [zero_mul, zero_add] using huδ

theorem padic_triangular_representatives (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 2) (Fin 2) (PadicInt p)) (hA : A.det ≠ 0)
    (ha : ∃ i j, IsUnit (A i j)) :
    ∃ (U : Matrix (Fin 2) (Fin 2) (PadicInt p)) (n : ℕ) (z : ZMod (p ^ n)),
      IsUnit U.det ∧
      (U * A = neighborMatrix ((p : PadicInt p) ^ n) (z.val : PadicInt p) ∨
        U * A * swapMatrix = neighborMatrix ((p : PadicInt p) ^ n) (z.val : PadicInt p)) := by
  obtain ⟨U, δ, z, hU, hδ, heq⟩ := triangularize_unit_entry A hA ha
  obtain ⟨V, n, w, hV, hVeq⟩ := reduce_padic_triangular_matrix p δ z hδ
  refine ⟨V * U, n, w, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact hV.mul hU
  · rcases heq with heq | heq
    · left
      rw [Matrix.mul_assoc, heq, hVeq]
    · right
      rw [Matrix.mul_assoc V U A, Matrix.mul_assoc V (U * A) swapMatrix, heq, hVeq]

end Erdos941.PairLocal
