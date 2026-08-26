import ErdosProblems.Erdos421.FiniteBuchstabPrimeSaving
import ErdosProblems.Erdos421.SievePrimeEndpoint
import ErdosProblems.Erdos421.BuchstabScaleParameters

/-! # The full prime sum in the rough-number induction -/

namespace Erdos421

theorem buchstab_open_prime_main_saving (n : ℕ) {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ B > 1, ∀ b : ℝ, B ≤ b → ∀ z : ℕ, 2 ≤ z → (z : ℝ) ≤ Real.sqrt b →
      b ≤ (z : ℝ) ^ (n + 3) →
      |1 / Real.log b + (∑ p ∈ primesInRealInterval z (Real.sqrt b),
        finiteBuchstab n (logarithmicBuchstabArgument b p) / ((p : ℝ) * Real.log p)) -
        finiteBuchstab (n + 1) (Real.log b / Real.log z) / Real.log z| ≤
          ε / (Real.log b) ^ A := by
  let K : ℝ := (n : ℝ) + 3
  have hK : 0 < K := by dsimp only [K]; positivity
  let η : ℝ := ε / K ^ A
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨Z₀, hZ₀, hprime⟩ := finiteBuchstab_prime_log_saving hA hη hK.le
  obtain ⟨B, hB, hcut⟩ := power_cutoff_large (n + 3) (by omega) Z₀
  refine ⟨B, hB, ?_⟩
  intro b hb z hz hzs hbz
  obtain ⟨hZz, hlz⟩ := hcut b hb z hbz
  have hb1 := hB.trans_le hb
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hscale : Real.log b ≤ K * Real.log z := by
    have h := log_le_nat_power_scale (by linarith : 0 < b) hbz
    simpa only [Nat.cast_add, Nat.cast_ofNat, K] using h
  have harg : ∀ t ∈ Set.Icc (z : ℝ) (Real.sqrt b),
      1 ≤ logarithmicBuchstabArgument b t := by
    intro t ht
    have h := logarithmicBuchstabArgument_antitone hb1 (hz1.trans_le ht.1)
      (hz1.trans_le hzs) ht.2
    rwa [logarithmicBuchstabArgument_sqrt hb1] at h
  have hD := hprime b z (Real.sqrt b) hb1 hZz hzs hlz hscale n harg
  have hm := buchstabPrimeWeight_main_term n hb1 hz1 hzs
  have heq : 1 / Real.log b + (∑ p ∈ primesInRealInterval z (Real.sqrt b),
      finiteBuchstab n (logarithmicBuchstabArgument b p) / ((p : ℝ) * Real.log p)) -
      finiteBuchstab (n + 1) (Real.log b / Real.log z) / Real.log z =
      buchstabPrimeDiscrepancy b (finiteBuchstab n) z (Real.sqrt b) := by
    unfold buchstabPrimeDiscrepancy
    linarith only [hm]
  rw [heq]
  exact hD.trans (scaled_log_saving_le hb1 hz1 hK hA hε.le hscale)

theorem buchstab_inclusive_prime_main_saving (n : ℕ) {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ B > 1, ∀ b : ℝ, B ≤ b → ∀ z : ℕ, 2 ≤ z → (z : ℝ) ≤ Real.sqrt b →
      b ≤ (z : ℝ) ^ (n + 3) →
      |1 / Real.log b + (∑ p ∈ sievePrimes z (roughSquareCutoff b),
        finiteBuchstab n (logarithmicBuchstabArgument b p) / ((p : ℝ) * Real.log p)) -
        finiteBuchstab (n + 1) (Real.log b / Real.log z) / Real.log z| ≤
          ε / (Real.log b) ^ A := by
  have hε₂ : 0 < ε / 2 := by positivity
  obtain ⟨B₁, hB₁, hopen⟩ := buchstab_open_prime_main_saving n hA hε₂
  obtain ⟨B₂, hB₂, hend⟩ := buchstab_endpoint_log_saving n hA hε₂
  refine ⟨max B₁ B₂, hB₁.trans_le (le_max_left _ _), ?_⟩
  intro b hb z hz hzs hbz
  have hb₁ : B₁ ≤ b := (le_max_left _ _).trans hb
  have hb₂ : B₂ ≤ b := (le_max_right _ _).trans hb
  have ho := hopen b hb₁ z hz hzs hbz
  have he := (sieve_square_buchstab_endpoint_error n (hB₁.trans_le hb₁) hz hzs).trans
    (hend b hb₂ z hz hbz)
  let S : ℝ := ∑ p ∈ sievePrimes z (roughSquareCutoff b),
    finiteBuchstab n (logarithmicBuchstabArgument b p) / ((p : ℝ) * Real.log p)
  let T : ℝ := ∑ p ∈ primesInRealInterval z (Real.sqrt b),
    finiteBuchstab n (logarithmicBuchstabArgument b p) / ((p : ℝ) * Real.log p)
  let M : ℝ := finiteBuchstab (n + 1) (Real.log b / Real.log z) / Real.log z
  change |1 / Real.log b + S - M| ≤ _
  calc
    _ = |(1 / Real.log b + T - M) + (S - T)| := by congr 1; ring
    _ ≤ |1 / Real.log b + T - M| + |S - T| := abs_add_le _ _
    _ ≤ ε / 2 / (Real.log b) ^ A + ε / 2 / (Real.log b) ^ A := add_le_add ho he
    _ = _ := by ring

end Erdos421
