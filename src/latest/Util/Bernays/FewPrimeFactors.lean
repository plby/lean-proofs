import Util.Bernays.LocalPrimePackets

/-!
# Integers with few prime divisors from a divergent allowed family

The estimate is relative to the exact `x / sqrt(log x)` local count, rather
than merely an `o(x)` density estimate.
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

noncomputable def fewPrimeFactorValues (S E : ℕ → Prop) (k N : ℕ) : Finset ℕ :=
  (localValues S N).filter fun n => (n.primeFactors.filter E).card ≤ k

theorem packetCount_dvd_le_primeFactors (P : Finset ℕ) (E : ℕ → Prop)
    (hP : ∀ p ∈ P, p.Prime ∧ E p) {n : ℕ} (hn : 0 < n) :
    packetCount P (fun p n => p ∣ n) n ≤ (n.primeFactors.filter E).card := by
  rw [packetCount_eq_eventCount]
  unfold eventCount
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro p hp
  have h : p ∈ P ∧ p ∣ n := by simpa only [Finset.mem_filter] using hp
  exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨(hP p h.1).1, h.2, hn.ne'⟩, (hP p h.1).2⟩

theorem fewPrimeFactorValues_card_le_packet (S E : ℕ → Prop) (k N : ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ E p) :
    (fewPrimeFactorValues S E k N).card ≤
      eventCount (localValues S N) (fun n => packetCount P (fun p n => p ∣ n) n ≤ k) := by
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnA, hnk⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨hnA, ?_⟩
  have hnpos : 0 < n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hnA).1).1
  exact (packetCount_dvd_le_primeFactors P E hP hnpos).trans (by exact_mod_cast hnk)

theorem eventually_fewPrimeFactorValues_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1)
    (E : ℕ → Prop)
    (hE : ∀ R : ℝ, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ χ p ≠ -1 ∧ E p) ∧ R < ∑ p ∈ P, (p : ℝ)⁻¹)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ((fewPrimeFactorValues (fun p : ℕ => χ p = -1) E k N).card : ℝ) ≤ ε * scale N := by
  let C := characterLocalConstant χ / sqrt π
  have hC : 0 < C := div_pos (characterLocalConstant_pos χ hχ) (sqrt_pos.mpr pi_pos)
  obtain ⟨P, hP, hmass⟩ := hE (max (2 * (k : ℝ)) (8 * C / ε))
  have hM : 0 < ∑ p ∈ P, (p : ℝ)⁻¹ :=
    (by positivity : (0 : ℝ) ≤ 2 * k).trans_lt ((le_max_left _ _).trans_lt hmass)
  have hk : 2 * (k : ℝ) ≤ ∑ p ∈ P, (p : ℝ)⁻¹ := (le_max_left _ _).trans hmass.le
  have hratio : 8 * C / (∑ p ∈ P, (p : ℝ)⁻¹) ≤ ε := by
    apply (div_le_iff₀ hM).mpr
    have h := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hmass)
    nlinarith
  have hbound := eventually_local_fewPacketCount_le χ hχ₂ hχ P
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1⟩) (Nat.cast_nonneg k) hM hk
  filter_upwards [hbound, eventually_ge_atTop (2 : ℕ)] with N hN hN₂
  have hs : 0 < scale (N : ℝ) := scale_pos (by exact_mod_cast (show 1 < N by omega))
  have hle : ((fewPrimeFactorValues (fun p : ℕ => χ p = -1) E k N).card : ℝ) ≤
      (eventCount (localValues (fun p : ℕ => χ p = -1) N)
        (fun n => packetCount P (fun p n => p ∣ n) n ≤ k) : ℝ) := by
    exact_mod_cast fewPrimeFactorValues_card_le_packet (fun p : ℕ => χ p = -1) E k N P
      (fun p hp => ⟨(hP p hp).1, (hP p hp).2.2⟩)
  exact (hle.trans hN).trans (mul_le_mul_of_nonneg_right hratio hs.le)

theorem fewPrimeFactorValues_div_scale_tendsto_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1)
    (E : ℕ → Prop)
    (hE : ∀ R : ℝ, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ χ p ≠ -1 ∧ E p) ∧ R < ∑ p ∈ P, (p : ℝ)⁻¹)
    (k : ℕ) :
    Tendsto (fun N : ℕ => ((fewPrimeFactorValues (fun p : ℕ => χ p = -1) E k N).card : ℝ) /
      scale N) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hbound := eventually_fewPrimeFactorValues_le χ hχ₂ hχ E hE k (half_pos hε)
  filter_upwards [hbound, eventually_ge_atTop (2 : ℕ)] with N hN hN₂
  have hs : 0 < scale (N : ℝ) := scale_pos (by exact_mod_cast (show 1 < N by omega))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hs.le)]
  exact ((div_le_iff₀ hs).mpr hN).trans_lt (half_lt_self hε)

end Bernays
