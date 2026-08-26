import ErdosProblems.Erdos67.StationaryAtomTransport

/-!
# Exclusion of atoms at points of infinite additive order

The dilation fibers of an infinite-order point are pairwise disjoint. Atom
transport would assign them a divergent harmonic total mass.
-/

open scoped BigOperators Topology
open Finset Filter MeasureTheory

namespace Erdos67.StationaryModel

theorem dilation_fibers_disjoint {η : FrequencyCircle}
    (hη : ∀ n : ℕ, 0 < n → n • η ≠ 0) {a b : ℕ} (hab : a ≠ b) :
    Disjoint {θ : FrequencyCircle | a • θ = η} {θ : FrequencyCircle | b • θ = η} := by
  apply Set.disjoint_left.mpr
  intro θ ha hb
  have he : a • η = b • η := by
    calc
      a • η = a • (b • θ) := by rw [hb]
      _ = b • (a • θ) := smul_comm a b θ
      _ = b • η := by rw [ha]
  rcases lt_or_gt_of_ne hab with hab | hba
  · apply hη (b - a) (Nat.sub_pos_of_lt hab)
    rw [sub_nsmul _ hab.le, he, add_neg_cancel]
  · apply hη (a - b) (Nat.sub_pos_of_lt hba)
    rw [sub_nsmul _ hba.le, he, add_neg_cancel]

theorem spectral_infinite_order_harmonic_bound (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (η : FrequencyCircle) (hη : ∀ n : ℕ, 0 < n → n • η ≠ 0) (N : ℕ) :
    (σ : Measure FrequencyCircle).real {η} * StationaryHarmonicAverage.mass N ≤ 1 := by
  have hs : (∑ n ∈ range N, (σ : Measure FrequencyCircle).real {θ | (n + 1) • θ = η}) ≤ 1 := by
    have he := sum_measureReal_le_measureReal_univ
      (μ := (σ : Measure FrequencyCircle)) (s := range N)
      (t := fun n ↦ {θ : FrequencyCircle | (n + 1) • θ = η})
      (fun n _ ↦ (isClosed_eq (continuous_id.nsmul (n + 1)) continuous_const).measurableSet)
      (fun a _ b _ hab ↦ dilation_fibers_disjoint hη (by omega : a + 1 ≠ b + 1))
    simpa using he
  calc
    _ = ∑ n ∈ range N, (σ : Measure FrequencyCircle).real {η} / (n + 1 : ℕ) := by
      simp only [StationaryHarmonicAverage.mass, mul_sum, div_eq_mul_inv]
    _ ≤ ∑ n ∈ range N, (σ : Measure FrequencyCircle).real {θ | (n + 1) • θ = η} := by
      apply sum_le_sum
      intro n _
      apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos n))).2
      have ht := spectral_atom_transport Q hQ hCD σ hσ η ⟨n + 1, Nat.succ_pos n⟩
      simpa only [PNat.mk_coe, mul_comm] using ht
    _ ≤ 1 := hs

theorem spectral_atom_zero_of_infinite_order (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (η : FrequencyCircle) (hη : ∀ n : ℕ, 0 < n → n • η ≠ 0) :
    (σ : Measure FrequencyCircle) {η} = 0 := by
  have hz : (σ : Measure FrequencyCircle).real {η} = 0 := by
    by_contra hne
    have ha : 0 < (σ : Measure FrequencyCircle).real {η} :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne)
    obtain ⟨N, hN⟩ := (StationaryHarmonicAverage.tendsto_mass_atTop.eventually
      (eventually_gt_atTop (1 / (σ : Measure FrequencyCircle).real {η}))).exists
    have hb := spectral_infinite_order_harmonic_bound Q hQ hCD σ hσ η hη N
    have hp := (div_lt_iff₀ ha).mp hN
    nlinarith
  exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top _ _)

end Erdos67.StationaryModel
