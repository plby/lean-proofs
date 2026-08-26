import ErdosProblems.Erdos67b.Section4FinalSelection
import ErdosProblems.Erdos67b.Section4FinalContradiction
import ErdosProblems.Erdos67b.Section4FinalScales

/-! # The unconditional stochastic discrepancy theorem

One finite conductor maximum and one final dyadic scale make the Euler,
phase-removal, and BCC certificates hold for the sample selected afterward.
-/

open scoped BigOperators Topology
open Filter Finset

namespace Erdos67b

open EulerResidue

noncomputable section

theorem exists_section4UniformEulerThreshold (A k H : ℕ) (hH : 0 < H) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ q : ℕ, 0 < q → q ≤ A →
      ∀ u : ℕ →*₀ ℂ, HasUnitNorm u →
        (∀ p : ℕ, p.Prime → p ∣ q → u p = 1) →
        EulerResidue.pretentiousMass u X ≤ 2 * A →
          Nonempty (EulerResidueBounds.TaoTransferReady u q k X (2 * A) (1 / (2 * H))) := by
  have hq : ∀ q ∈ Icc 1 A,
      ∀ᶠ X : ℕ in atTop, ∀ u : ℕ →*₀ ℂ, HasUnitNorm u →
        (∀ p : ℕ, p.Prime → p ∣ q → u p = 1) →
        EulerResidue.pretentiousMass u X ≤ 2 * A →
          Nonempty (EulerResidueBounds.TaoTransferReady u q k X (2 * A) (1 / (2 * H))) := by
    intro q hq
    have hq0 : q ≠ 0 := by have := (mem_Icc.1 hq).1; omega
    exact EulerResidueBounds.eventually_taoTransferReady hq0 (2 * A) (1 / (2 * H))
      (by positivity) (by positivity)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 ((Finset.eventually_all (Icc 1 A)).2 hq)
  exact ⟨X₀, fun X hX q hqlo hqhi ↦ hX₀ X hX q (mem_Icc.2 ⟨hqlo, hqhi⟩)⟩

theorem section4LargeScale_ge_index (K : ℕ) {D : ℕ} (hD : 0 < D) :
    K ≤ (4 ^ K) ^ D := by
  have hKY : K ≤ 4 ^ K := K.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by norm_num) K)
  have hYY : 4 ^ K ≤ (4 ^ K) ^ D := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (Nat.one_le_pow K 4 (by norm_num)) hD
  exact hKY.trans hYY

theorem section4_twice_modulus_le_square {K r : ℕ} (hK : 2 ≤ K) (hr : r ≤ K) :
    2 * r ≤ (4 ^ K) ^ 2 := by
  have hKY := section4LargeScale_ge_index K (by norm_num : 0 < 1)
  simp only [pow_one] at hKY
  have hY2 : 2 ≤ 4 ^ K := hK.trans hKY
  nlinarith

theorem stochasticDiscrepancyStatement : StochasticDiscrepancyStatement := by
  by_contra hnot
  obtain ⟨μ, C, hbound⟩ := not_stochasticDiscrepancy_iff_exists_uniform_square_bound.1 hnot
  obtain ⟨A, hA, hselect⟩ := exists_final_weightedSection4Selection μ C hbound
  obtain ⟨c, hc, hlower⟩ :=
    EulerLower.exists_pos_eventually_mul_log_le_norm_singularSeries (2 * A)
  let Bcc : ℝ := 2 * (16 * section4B C / c ^ 2 + 4) + 2
  have hBcc : 0 ≤ Bcc := by
    have hB := section4B_pos C
    dsimp [Bcc]
    positivity
  obtain ⟨P, hPc⟩ := exists_section4BCCParameters_with_large_separation A Bcc hA hBcc hc
  obtain ⟨Ksel, hKsel⟩ := hselect Bcc P
  obtain ⟨Kscale, hKscaleA, hKscale2, hKscale⟩ :=
    exists_section4FinalScaleThreshold A P.H P.k P.D P.D_pos hc hPc
  obtain ⟨Xeuler, hXeuler⟩ := exists_section4UniformEulerThreshold A P.k P.H P.H_pos
  obtain ⟨Xlower, hXlower⟩ := eventually_atTop.1 hlower
  let K := max Ksel (max Kscale (max Xeuler Xlower))
  have hKKsel : Ksel ≤ K := le_max_left _ _
  have hKKscale : Kscale ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKXeuler : Xeuler ≤ K :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hKXlower : Xlower ≤ K :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hK2 : 2 ≤ K := hKscale2.trans hKKscale
  have hAK : A ≤ K := ((le_max_left _ _).trans hKscaleA).trans hKKscale
  have hrK : A ^ P.k ≤ K := ((le_max_right _ _).trans hKscaleA).trans hKKscale
  let Y := 4 ^ K
  let X := Y ^ P.D
  have hKX : K ≤ X := section4LargeScale_ge_index K P.D_pos
  have hX : 1 < X := by omega
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hlog : 2 ≤ Real.log (X : ℝ) :=
    (Nat.cast_le.2 hK2).trans (section4Log_largeScale_ge P.D_pos K)
  obtain ⟨N, hN, htail⟩ := exists_taoHighTailMass_le (X := X) (A := Y ^ 2) hX
    (by norm_num : (0 : ℝ) < 1)
  let V := concreteSection4WeightWindow P.H X Y N hY hN
  obtain ⟨S, hSA, hSK, hSB, hSP, hselected⟩ := hKsel K hKKsel V
  obtain ⟨hSH, hSk, hSD⟩ := Section4Selection.fields_eq_of_params_heq hSA hSB hSP
  obtain ⟨W⟩ := S.exists_characterData
  have hqA : W.primitiveQ ≤ A := by simpa only [hSA] using W.primitiveQ_le_A
  have hmass : EulerResidue.pretentiousMass W.primitiveCorrectionHom X ≤ 2 * A := by
    simpa only [hSK, hSD, hSA] using
      W.primitiveCorrection_pretentiousMass_at_largeScale_lt_two_mul_A.le
  obtain ⟨E⟩ := hXeuler X (hKXeuler.trans hKX) W.primitiveQ W.primitiveQ_pos hqA
    W.primitiveCorrectionHom W.primitiveCorrectionHom_hasUnitNorm
    W.primitiveCorrectionHom_prime_dvd hmass
  have hsingular := hXlower X (hKXlower.trans hKX) W.primitiveCorrectionHom
    W.primitiveCorrectionHom_hasUnitNorm hmass
  obtain ⟨_hApow, hphase, hquad, hlinear, htailScale⟩ := hKscale K hKKscale
  have hqk : W.primitiveQ ^ S.k ≤ A ^ P.k := by
    rw [hSk]
    exact Nat.pow_le_pow_left hqA _
  have hqkr : ((W.primitiveQ ^ S.k : ℕ) : ℝ) ≤ ((A ^ P.k : ℕ) : ℝ) := Nat.cast_le.2 hqk
  apply W.primitive_contradiction_of_finalWindow (X := X) (N := N) hc
    (by simpa only [hSk, hSH, hSA] using E) hlog
  · simpa only [hSK] using hN
  · simpa only [hSK] using section4_twice_modulus_le_square hK2 (hqk.trans hrK)
  · exact htail
  · simpa only [V, concreteSection4WeightWindow, hSK, taoWindowMass] using hselected.le
  · exact hsingular
  · simpa only [hSH, hSK] using hphase
  · simpa only [hSH, hSK] using hquad
  · rw [hSH]
    exact (by gcongr : 8 * ((W.primitiveQ ^ S.k : ℕ) : ℝ) * P.H ≤
      8 * ((A ^ P.k : ℕ) : ℝ) * P.H).trans hlinear
  · rw [hSH]
    exact (by gcongr : 4 * ((W.primitiveQ ^ S.k : ℕ) : ℝ) * P.H * (1 + 4 * P.H) ≤
      4 * ((A ^ P.k : ℕ) : ℝ) * P.H * (1 + 4 * P.H)).trans htailScale
  · rw [hSB]

end

end Erdos67b
