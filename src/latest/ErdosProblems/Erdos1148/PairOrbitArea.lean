import ErdosProblems.Erdos1148.PairRealFrames
import ErdosProblems.Erdos1148.BasicLemmaOrbitCount

/-!
# Summed parameter area over integral pair orbits

This combines the arithmetic orbit count with the real flow-area estimate.
The sum is over chosen representatives of actual integral pair orbits.
It is not yet identified with a measure on the modular quotient.
-/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups ENNReal

lemma finite_integralPairOrbits_of_nondegenerate {d ℓ : ℤ}
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) : Finite (IntegralPairOrbits d ℓ) := by
  classical
  by_cases h : Nonempty (IntegralPairOrbits d ℓ)
  · exact finite_integralPairOrbits h.some.out hnd
  · let : IsEmpty (IntegralPairOrbits d ℓ) := not_nonempty_iff.mp h
    infer_instance

noncomputable def pairOrbitParameterArea {d : ℤ} (hd : 0 < d) (ℓ : ℤ) (η : ℝ) : ℝ≥0∞ :=
  ∑' q : IntegralPairOrbits d ℓ,
    let f := chooseIntegralPairFrame hd q.out
    volume (signedCloseDiagonalFlowTimes (f.first⁻¹ * f.second) η)

lemma pairOrbitParameterArea_le {d ℓ : ℤ} (hd : 0 < d) (hℓ : ℓ ≠ 2 * d)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2) :
    pairOrbitParameterArea hd ℓ η ≤
      (Nat.card (IntegralPairOrbits d ℓ) : ℝ≥0∞) *
        ENNReal.ofReal (16 * η * Real.log (4 * (d : ℝ))) := by
  classical
  let := finite_integralPairOrbits_of_nondegenerate hnd
  let := Fintype.ofFinite (IntegralPairOrbits d ℓ)
  calc
    pairOrbitParameterArea hd ℓ η ≤
        ∑' _ : IntegralPairOrbits d ℓ, ENNReal.ofReal (16 * η * Real.log (4 * (d : ℝ))) :=
      ENNReal.tsum_le_tsum (fun q => (chooseIntegralPairFrame hd q.out).volume_close_times_le
        hd hℓ hη0 hη)
    _ = _ := by simp [tsum_fintype, Nat.card_eq_fintype_card]

theorem exists_sum_pairOrbitParameterArea_le {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ) (L : ℤ) (hd : 0 < (d : ℤ)) (η : ℝ),
      0 ≤ L → L ≤ d → 0 < η → η ≤ 1 / 2 →
      (∑ ℓ ∈ noncentralMultiples (2 * d) L 1, pairOrbitParameterArea hd ℓ η) ≤
        ENNReal.ofReal (K * L * η * (d : ℝ) ^ ε * Real.log (4 * (d : ℝ))) := by
  classical
  obtain ⟨C, hC, hcount⟩ := exists_sum_integral_pair_orbits_le hε
  refine ⟨16 * C, by positivity, ?_⟩
  intro d L hd η hL hLd hη0 hη
  have hdN : 0 < d := by exact_mod_cast hd
  let S := noncentralMultiples (2 * d) L 1
  have hsum := hcount d L hdN hL hLd
  have hterm (ℓ : ℤ) (hℓ : ℓ ∈ S) :
      pairOrbitParameterArea hd ℓ η ≤
        (Nat.card (IntegralPairOrbits d ℓ) : ℝ≥0∞) *
          ENNReal.ofReal (16 * η * Real.log (4 * (d : ℝ))) := by
    have hne : ℓ ≠ 2 * (d : ℤ) := (Finset.mem_filter.mp hℓ).2.2
    exact pairOrbitParameterArea_le hd hne (noncentral_pair_nondegenerate hdN hLd hℓ) hη0 hη
  have hcast : (∑ ℓ ∈ S, (Nat.card (IntegralPairOrbits d ℓ) : ℝ≥0∞)) =
      ENNReal.ofReal (∑ ℓ ∈ S, (Nat.card (IntegralPairOrbits d ℓ) : ℝ)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    simp
  calc
    (∑ ℓ ∈ S, pairOrbitParameterArea hd ℓ η) ≤
        ∑ ℓ ∈ S, (Nat.card (IntegralPairOrbits d ℓ) : ℝ≥0∞) *
          ENNReal.ofReal (16 * η * Real.log (4 * (d : ℝ))) := Finset.sum_le_sum hterm
    _ = (∑ ℓ ∈ S, (Nat.card (IntegralPairOrbits d ℓ) : ℝ≥0∞)) *
        ENNReal.ofReal (16 * η * Real.log (4 * (d : ℝ))) := (Finset.sum_mul _ _ _).symm
    _ = ENNReal.ofReal (∑ ℓ ∈ S, (Nat.card (IntegralPairOrbits d ℓ) : ℝ)) *
        ENNReal.ofReal (16 * η * Real.log (4 * (d : ℝ))) := by rw [hcast]
    _ ≤ ENNReal.ofReal (C * L * (d : ℝ) ^ ε) *
        ENNReal.ofReal (16 * η * Real.log (4 * (d : ℝ))) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hsum) le_rfl
    _ = ENNReal.ofReal ((16 * C) * L * η * (d : ℝ) ^ ε * Real.log (4 * (d : ℝ))) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ C * L * (d : ℝ) ^ ε)]
      congr 1
      ring

end Erdos1148.DukeArithmetic
