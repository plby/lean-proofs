import ErdosProblems.Erdos538.LinearLayerUnion
import ErdosProblems.Erdos538.Truncation

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538

/-- Finite truncation engine with the new linear-in-`K` layer retention. -/
theorem exists_admissible_linear_baseline_inequality (N K : ℕ) :
    ∃ A : Finset ℕ,
      Admissible 2 N A ∧
      (K + 1) • reciprocalMassNN (positiveSquarefree N) ≤
        (K + 1) • (1 + (128 * K) • reciprocalMassNN A) +
          primeHarmonicNN N * harmonicMassNN N := by
  obtain ⟨A, hAdm, -, hlow⟩ :=
    exists_admissible_lowSquarefreeLayers_linear N K
  have hlow' : reciprocalMassNN (lowSquarefreeLayers N K) ≤
      (128 * K) • reciprocalMassNN A := by
    rw [reciprocalMassNN_lowSquarefreeLayers]
    exact hlow
  refine ⟨A, hAdm, ?_⟩
  have hmono := add_le_add_right
    (nsmul_le_nsmul_right (add_le_add_left hlow' 1) (K + 1))
    (primeHarmonicNN N * harmonicMassNN N)
  apply (squarefree_truncation_inequality N K).trans
  simpa only [add_comm] using hmono

/-- If `K+1` dominates four times the prime reciprocal sum, the linear layer
construction gives harmonic mass over `K`, rather than over `K²`. -/
theorem exists_admissible_linear_of_primeHarmonic_le
    (N K : ℕ) (hprime : 4 * primeHarmonicNN N ≤ K + 1) :
    ∃ A : Finset ℕ,
      Admissible 2 N A ∧
      harmonicMassNN N ≤ 4 + (512 * K) • reciprocalMassNN A := by
  obtain ⟨A, hAdm, hbase⟩ :=
    exists_admissible_linear_baseline_inequality N K
  refine ⟨A, hAdm, ?_⟩
  let S := reciprocalMassNN (positiveSquarefree N)
  let H := harmonicMassNN N
  let P := primeHarmonicNN N
  let M := reciprocalMassNN A
  let q : ℚ≥0 := K + 1
  let C : ℚ≥0 := 128 * K
  have hHS : H ≤ 2 * S := by
    simpa [H, S] using harmonicMassNN_le_two_mul_squarefree N
  have htail : 2 * (P * H) ≤ q * S := by
    have h1 : 2 * (P * H) ≤ 4 * P * S := by
      calc
        2 * (P * H) = (2 * P) * H := by ring
        _ ≤ (2 * P) * (2 * S) := mul_le_mul_right hHS (2 * P)
        _ = 4 * P * S := by ring
    have h2 : 4 * P * S ≤ q * S := by
      apply mul_le_mul_left
      simpa [P, q] using hprime
    exact h1.trans h2
  have hbase' : q * S ≤ q * (1 + C * M) + P * H := by
    simp only [nsmul_eq_mul] at hbase
    dsimp [q, S, C, M, P, H]
    push_cast at hbase ⊢
    convert hbase using 1 <;> ring
  have hq : (0 : ℚ≥0) < q := by simp [q]
  have hSM : S ≤ 2 * (1 + C * M) := by
    have hmul : q * S ≤ q * (2 * (1 + C * M)) := by
      qify at hbase' htail ⊢
      nlinarith
    exact (mul_le_mul_iff_of_pos_left hq).mp (by
      convert hmul using 1 <;> ring)
  calc
    harmonicMassNN N = H := rfl
    _ ≤ 2 * S := hHS
    _ ≤ 2 * (2 * (1 + C * M)) := mul_le_mul_right hSM 2
    _ = 4 + (512 * K) • reciprocalMassNN A := by
      simp [C, M, nsmul_eq_mul]
      ring

end Erdos538
