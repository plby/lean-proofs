import ErdosProblems.Erdos67.StationaryRationalAtoms
import ErdosProblems.Erdos67.StationaryIrrationalAtoms

/-!
# The correlation spectrum has no atoms

This combines zero-frequency exclusion, infinite-order exclusion, and rational
mass propagation with the finite energy bound. All three cases are explicit.
-/

open MeasureTheory

namespace Erdos67.StationaryModel

theorem correlation_spectrum_noAtoms (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (B : ℝ) (hB : ∀ N, (∫ ω, blockSum N ω ^ 2 ∂(Q : Measure Configuration)) ≤ B) :
    NullSingletonClass (σ : Measure FrequencyCircle) := by
  constructor
  intro θ
  by_cases hzero : θ = 0
  · subst θ
    exact correlation_spectrum_zero_atom Q hQ σ hσ B hB
  by_cases hord : addOrderOf θ = 0
  · apply spectral_atom_zero_of_infinite_order Q hQ hCD σ hσ θ
    intro n hn he
    have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr he
    rw [hord, zero_dvd_iff] at hd
    exact hn.ne' hd
  · let q : ℕ+ := ⟨addOrderOf θ, Nat.pos_of_ne_zero hord⟩
    have hq : 1 < q.val := by
      have hne : addOrderOf θ ≠ 1 := by
        intro he
        apply hzero
        have hh : 1 • θ = 0 := he ▸ addOrderOf_nsmul_eq_zero θ
        simpa using hh
      change 1 < addOrderOf θ
      omega
    apply (measureReal_eq_zero_iff (μ := (σ : Measure FrequencyCircle)) (s := {θ})).mp
    calc
      (σ : Measure FrequencyCircle).real {θ} = rationalAtomMass σ q :=
        atom_mass_eq_of_order Q hQ hCD σ hσ q θ rfl
      _ = 0 := rational_atom_mass_zero Q hQ hCD σ hσ
        (integrable_spectralEnergy Q hQ σ hσ B hB) q hq

end Erdos67.StationaryModel
