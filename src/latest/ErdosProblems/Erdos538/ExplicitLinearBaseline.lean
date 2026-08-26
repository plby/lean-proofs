import ErdosProblems.Erdos538.LinearTruncation
import ErdosProblems.Erdos538.ExplicitBaseline

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538

/-- Fully explicit finite matching-order lower construction for cap two. -/
theorem exists_admissible_explicit_linear_baseline (N : ℕ) :
    ∃ A : Finset ℕ,
      Admissible 2 N A ∧
      harmonicMassNN N ≤
        4 + (8192 * (Nat.log 2 (Nat.log 2 N) + 1)) •
          reciprocalMassNN A := by
  obtain ⟨A, hAdm, hmass⟩ := exists_admissible_linear_of_primeHarmonic_le
    N (baselineK N) (four_primeHarmonicNN_le_baselineK_add_one N)
  refine ⟨A, hAdm, ?_⟩
  have hcoeff : 512 * baselineK N =
      8192 * (Nat.log 2 (Nat.log 2 N) + 1) := by
    simp [baselineK]
    ring
  rw [hcoeff] at hmass
  exact hmass

/-- Real-logarithmic form: an admissible family has reciprocal mass at least
`(log(N+1)-4)/(8192(1+log₂ log₂ N))`. -/
theorem exists_admissible_explicit_linear_log_baseline (N : ℕ) :
    ∃ A : Finset ℕ,
      Admissible 2 N A ∧
      Real.log (N + 1) ≤
        4 + (8192 * (Nat.log 2 (Nat.log 2 N) + 1) : ℕ) *
          (reciprocalMassNN A : ℝ) := by
  obtain ⟨A, hAdm, hmass⟩ := exists_admissible_explicit_linear_baseline N
  refine ⟨A, hAdm, ?_⟩
  have hmassR := (NNRat.cast_le (K := ℝ)).mpr hmass
  calc
    Real.log (N + 1) ≤ (harmonic N : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic N
    _ = (harmonicMassNN N : ℝ) := (coe_harmonicMassNN N).symm
    _ ≤ 4 + (8192 * (Nat.log 2 (Nat.log 2 N) + 1) : ℕ) *
        (reciprocalMassNN A : ℝ) := by
      simpa [nsmul_eq_mul] using hmassR

end Erdos538
