import ErdosProblems.Erdos1148.OrbitCoverEntropyEstimate
import ErdosProblems.Erdos1148.PositiveMassAvoidanceRate
import ErdosProblems.Erdos1148.PartitionStableCores
import ErdosProblems.Erdos1148.CompactOrdinaryOrbitCover

/-! # Strict entropy bounds for every finite continuity partition -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure
open scoped MatrixGroups ENNReal

theorem orbitEntropy_linear_gap_of_avoidance_rate
    (μ : Measure ModularOrbitSpace) [IsProbabilityMeasure μ]
    (hf : MeasurePreserving modularTimeOne μ μ) {n : ℕ} (hn : 0 < n)
    {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hcover : ∀ δ : ℝ, 0 < δ → ∃ M : ℝ, 1 ≤ M ∧
      ∀ k : ℕ, 0 < k → ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
        (N : ℝ) ≤ M * Real.exp ((1 - d) * ((k : ℝ) * n)) ∧
        (3 / 4 : ℝ) ≤ μ.real (⋃ i, modularMk '' B i) ∧
        (∀ i, IsCompact (B i)) ∧ ∀ i, LiftForwardClose δ ((k : ℝ) * n) (B i))
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : FiniteMeasurablePartition ModularOrbitSpace ι)
    (hboundary : ∀ i, μ (frontier (P.atom i)) = 0) :
    ∃ D : ℝ, ∀ k : ℕ, 0 < k → P.orbitEntropy μ modularTimeOne (k * n) ≤
      D + (1 - 3 * d / 8) * ((k : ℝ) * n) := by
  classical
  let q := Real.log (Fintype.card ι)
  have hq : 0 ≤ q := Real.log_nonneg (by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
  let β := d / (32 * (q + 1))
  have hβ : 0 < β := by dsimp only [β]; positivity
  have hβeq : β * (32 * (q + 1)) = d := by
    dsimp only [β]
    field_simp
  have hβq : 2 * β * q ≤ d / 16 := by
    nlinarith only [hβeq, hβ]
  have hβsmall : β ≤ 1 / 4 := by
    have hprod := mul_nonneg hβ.le hq
    nlinarith only [hβeq, hd1, hprod]
  obtain ⟨τ, hτ, hwords⟩ := exists_small_mismatch_family_bound ι
    (show 0 < d / 16 by positivity)
  obtain ⟨C, η, hC, hCsub, hCmass, hη, hηsmall, hstable⟩ :=
    exists_partition_stable_cores P μ hboundary (mul_pos hτ hβ)
  have hQ : MeasurableSet (⋃ i, C i)ᶜ :=
    (MeasurableSet.iUnion fun i => (hC i).measurableSet).compl
  have hQmass : μ.real (⋃ i, C i)ᶜ / τ ≤ β :=
    (div_le_iff₀ hτ).mpr (by linarith only [hCmass])
  obtain ⟨K, _, hK, hKmass⟩ := MeasurableSet.univ.exists_isCompact_sdiff_lt
    (μ := μ) (measure_ne_top μ Set.univ) (ENNReal.ofReal_ne_zero_iff.mpr hβ)
  rw [Set.sdiff_eq, Set.univ_inter] at hKmass
  have hKR : μ.real Kᶜ < β := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hKmass
    simpa only [Measure.real, ENNReal.toReal_ofReal hβ.le] using h
  have hKlower : 1 - β ≤ μ.real K := by
    have hsplit := measureReal_add_measureReal_compl (μ := μ) hK.measurableSet
    rw [probReal_univ] at hsplit
    linarith only [hKR, hsplit]
  obtain ⟨Mg, hMg, hgood⟩ := hcover η hη
  obtain ⟨Ma, hMa, hordinary⟩ := exists_compact_ordinary_orbit_cover hK hη
    (hηsmall.trans (by norm_num))
  refine ⟨Real.log 3 + Real.log Mg + Real.log (Mg + Ma), ?_⟩
  intro k hk
  obtain ⟨Ng, Bg, hNg, hgmass, _, hBg⟩ := hgood k hk
  obtain ⟨Na, Ba, hNa, hcov, _, hBa⟩ := hordinary ((k : ℝ) * n) (by positivity)
  have hamass : 1 - β ≤ μ.real (⋃ i, modularMk '' Ba i) :=
    hKlower.trans (measureReal_mono hcov)
  have hBg' : ∀ i, LiftForwardClose η (k * n : ℕ) (Bg i) := by
    simpa only [Nat.cast_mul] using hBg
  have hBa' : ∀ i, LiftForwardClose η (k * n : ℕ) (Ba i) := by
    simpa only [Nat.cast_mul] using hBa
  have hNg' : (Ng : ℝ) ≤ Mg * Real.exp ((1 - d) * (k * n : ℕ)) := by
    simpa only [Nat.cast_mul] using hNg
  have hNa' : (Na : ℝ) ≤ Ma * Real.exp (k * n : ℕ) := by
    simpa only [Nat.cast_mul] using hNa
  have hent := orbitEntropy_le_of_two_covers P μ hf C hCsub (Nat.mul_pos hk hn) hτ
    hd.le hMg hMa.le hβsmall hβq hQ hQmass hstable (hwords (k * n))
    Bg Ba hBg' hBa' hNg' hNa' hgmass hamass
  simpa only [Nat.cast_mul] using hent

end Erdos1148.DukeArithmetic
