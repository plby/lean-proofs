import ErdosProblems.Erdos587.HighBlocks
import ErdosProblems.Erdos587.FresnelTails

/-!
# Partition of the nearby rational frequencies

Low frequencies, bounded dual widths, and gcd/dyadic blocks cover every
frequency. The finite covering argument keeps the normalized main term intact.
-/

open scoped BigOperators SchwartzMap

namespace Erdos587

noncomputable def nearbySmallFrequencies (u v M M₀ : ℕ) (L : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 M).filter fun m => M₀ < m ∧ ((m / m.gcd u : ℕ) : ℝ) * L / v ≤ 4

noncomputable def nearbyLargeFrequencies (u v M M₀ : ℕ) (L : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 M).filter fun m => M₀ < m ∧ 4 < ((m / m.gcd u : ℕ) : ℝ) * L / v

lemma nearby_frequency_cover (u v M M₀ : ℕ) (L : ℝ) (w : ℕ → ℝ) (hw : ∀ m, 0 ≤ w m) :
    (∑ m ∈ Finset.Icc 1 M, w m) ≤
      (∑ m ∈ Finset.Icc 1 M₀, w m) +
        (∑ m ∈ nearbySmallFrequencies u v M M₀ L, w m) +
        (∑ m ∈ nearbyLargeFrequencies u v M M₀ L, w m) := by
  classical
  let F : Fin 3 → Finset ℕ := fun i => if i = 0 then Finset.Icc 1 M₀
    else if i = 1 then nearbySmallFrequencies u v M M₀ L
    else nearbyLargeFrequencies u v M M₀ L
  have hcover : ∀ m ∈ Finset.Icc 1 M, ∃ i ∈ (Finset.univ : Finset (Fin 3)), m ∈ F i := by
    intro m hm
    by_cases hlo : m ≤ M₀
    · refine ⟨0, Finset.mem_univ _, ?_⟩
      simpa only [F, if_pos rfl] using Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1, hlo⟩
    · have hhigh : M₀ < m := by omega
      by_cases hwide : ((m / m.gcd u : ℕ) : ℝ) * L / v ≤ 4
      · refine ⟨1, Finset.mem_univ _, ?_⟩
        have hsmall : m ∈ nearbySmallFrequencies u v M M₀ L :=
          Finset.mem_filter.mpr ⟨hm, hhigh, hwide⟩
        simpa [F] using hsmall
      · refine ⟨2, Finset.mem_univ _, ?_⟩
        have hlarge : m ∈ nearbyLargeFrequencies u v M M₀ L :=
          Finset.mem_filter.mpr ⟨hm, hhigh, lt_of_not_ge hwide⟩
        simpa [F] using hlarge
  have h := sum_le_sum_family_of_cover (Finset.Icc 1 M) Finset.univ F w hw hcover
  simpa [Fin.sum_univ_three, F, add_assoc] using h

theorem exists_nearby_small_frequency_sum_bound (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a u v M M₀ : ℕ), 0 < u → 0 < v → a.Coprime u →
      ∀ L : ℝ, 0 < L → (u : ℝ) * v / L ^ 2 < M₀ + 1 →
        (∑ m ∈ nearbySmallFrequencies u v M M₀ L,
          ‖nearbyQuadraticRemainder f u m v (a : ℤ) L‖) ≤ C * M * Real.sqrt L := by
  obtain ⟨C, hC, hsmall⟩ := exists_nearby_small_dual_width_bound f
  refine ⟨C, hC, ?_⟩
  intro a u v M M₀ hu hv ha L hL hcutoff
  classical
  let S := nearbySmallFrequencies u v M M₀ L
  have hpoint (m : ℕ) (hm : m ∈ S) :
      ‖nearbyQuadraticRemainder f u m v (a : ℤ) L‖ ≤ C * Real.sqrt L := by
    have hm' : m ∈ Finset.Icc 1 M ∧ M₀ < m ∧ ((m / m.gcd u : ℕ) : ℝ) * L / v ≤ 4 :=
      Finset.mem_filter.mp hm
    have hmpos : 0 < m := (Finset.mem_Icc.mp hm'.1).1
    let d := m.gcd u
    let q := u / d
    let r := m / d
    have hd : 0 < d := Nat.gcd_pos_of_pos_right m hu
    have hq : 0 < q := Nat.div_pos (Nat.gcd_le_right m hu) hd
    have hr : 0 < r := Nat.div_pos (Nat.gcd_le_left u hmpos) hd
    have hdq : d * q = u := Nat.mul_div_cancel' (Nat.gcd_dvd_right m u)
    have hdr : d * r = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m u)
    have hqdiv : q ∣ u := ⟨d, by simpa only [mul_comm] using hdq.symm⟩
    have hrq : r.Coprime q := Nat.coprime_div_gcd_div_gcd hd
    have haq : a.Coprime q := Nat.Coprime.of_dvd_right hqdiv ha
    have hunit : IsUnit (((r : ℤ) * (a : ℤ) : ℤ) : ZMod q) := by
      have h := (ZMod.isUnit_iff_coprime (r * a) q).mpr (hrq.mul_left haq)
      simpa only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast] using h
    have hA : 1 ≤ ((r : ℝ) / (q * v)) * L ^ 2 :=
      high_profile_parameter_ge_one hd hq hv hL hdq hcutoff (by simpa only [hdr] using hm'.2.1)
    have heq : nearbyQuadraticRemainder f u m v (a : ℤ) L =
        nearbyQuadraticRemainder f q r v (a : ℤ) L := by
      rw [← hdr, ← hdq]
      exact nearbyQuadraticRemainder_mul f hd hq r v (a : ℤ) L
    rw [heq]
    exact hsmall q r v hq hr hv (a : ℤ) L hL hunit hA hm'.2.2
  have hcard : S.card ≤ M := by
    have hs : S ⊆ Finset.Icc 1 M := Finset.filter_subset _ _
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hs
  apply (Finset.sum_le_sum hpoint).trans
  simp only [Finset.sum_const, nsmul_eq_mul]
  calc
    (S.card : ℝ) * (C * Real.sqrt L) ≤ (M : ℝ) * (C * Real.sqrt L) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by ring

def nearbyBlockIndexSet (u M : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  u.divisors.sigma fun d => dyadicBlockIndices (M / d)

noncomputable def nearbyHighBlockImage (u v M M₀ : ℕ) (L : ℝ) (i : Σ _ : ℕ, ℕ) : Finset ℕ :=
  (nearbyHighBlock (u / i.1) v M M₀ i.1 (2 ^ i.2) L).image (fun r => i.1 * r)

lemma nearby_large_frequency_covered {u : ℕ} (hu : 0 < u) (v M M₀ : ℕ) (L : ℝ)
    (m : ℕ) (hm : m ∈ nearbyLargeFrequencies u v M M₀ L) :
    ∃ i ∈ nearbyBlockIndexSet u M, m ∈ nearbyHighBlockImage u v M M₀ L i := by
  classical
  have hm' : m ∈ Finset.Icc 1 M ∧ M₀ < m ∧ 4 < ((m / m.gcd u : ℕ) : ℝ) * L / v :=
    Finset.mem_filter.mp hm
  have hmpos : 0 < m := (Finset.mem_Icc.mp hm'.1).1
  let d := m.gcd u
  let r := m / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_right m hu
  have hr : 0 < r := Nat.div_pos (Nat.gcd_le_left u hmpos) hd
  have hdr : d * r = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m u)
  have hdiv : r ≤ M / d := Nat.div_le_div_right (Finset.mem_Icc.mp hm'.1).2
  obtain ⟨k, hk, hlow, hhigh, hpow⟩ := exists_dyadic_block hr hdiv
  have hdmem : d ∈ u.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right m u, hu.ne'⟩
  refine ⟨⟨d, k⟩, Finset.mem_sigma.mpr ⟨hdmem, hk⟩, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨r, ?_, hdr⟩
  apply (mem_nearbyHighBlock (u / d) v M M₀ d (2 ^ k) r L).mpr
  exact ⟨⟨hlow, hhigh.le⟩, Nat.coprime_div_gcd_div_gcd hd,
    by simpa only [hdr] using hm'.2.1,
    by simpa only [hdr] using (Finset.mem_Icc.mp hm'.1).2, hm'.2.2⟩

lemma sum_nearby_large_le_blocks (f : 𝓢(ℝ, ℂ)) (a u v M M₀ : ℕ) (hu : 0 < u) (L : ℝ) :
    (∑ m ∈ nearbyLargeFrequencies u v M M₀ L,
      ‖nearbyQuadraticRemainder f u m v (a : ℤ) L‖) ≤
      ∑ d ∈ u.divisors, ∑ k ∈ dyadicBlockIndices (M / d),
        ∑ r ∈ nearbyHighBlock (u / d) v M M₀ d (2 ^ k) L,
          ‖nearbyQuadraticRemainder f u (d * r) v (a : ℤ) L‖ := by
  classical
  apply (sum_le_sum_family_of_cover (nearbyLargeFrequencies u v M M₀ L)
    (nearbyBlockIndexSet u M) (nearbyHighBlockImage u v M M₀ L)
    (fun m => ‖nearbyQuadraticRemainder f u m v (a : ℤ) L‖) (fun _ => norm_nonneg _)
    (nearby_large_frequency_covered hu v M M₀ L)).trans_eq
  rw [nearbyBlockIndexSet, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_image
  intro r hr r' hr' heq
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_mem_divisors hd) heq

/-- Summing all large-dual-width frequencies costs only a harmonic factor
from the gcd classes. The dyadic block lengths form a geometric sum. -/
theorem exists_nearby_large_frequency_sum_bound (j : ℕ) (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧ ∀ (a u v M M₀ Y : ℕ),
      0 < u → 0 < v → 0 < M → 1 ≤ Y → a.Coprime u → u.Coprime v → u ∣ a * v + 1 →
      ∀ L : ℝ, 0 < L → (u : ℝ) * v / L ^ 2 < M₀ + 1 →
        4 * (Y : ℝ) * L ≤ v → 64 * (M : ℝ) * L ≤ u * v →
        64 * ((u + v) * M + 1) ≤ Y ^ (4 ^ j) →
        (∑ m ∈ nearbyLargeFrequencies u v M M₀ L,
          ‖nearbyQuadraticRemainder f u m v (a : ℤ) L‖) ≤
            C * M * Real.sqrt L * (1 + Real.log u) * Real.log (35 * (M : ℝ)) ^ O := by
  obtain ⟨C, hC, O, hO, hblock⟩ := exists_nearby_high_block_global_bound j f
  refine ⟨2 * C, by positivity, O, hO, ?_⟩
  intro a u v M M₀ Y hu hv hM hY ha huv hav L hL hcutoff hYv hglobal hsize
  have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlogM : 0 ≤ Real.log (35 * (M : ℝ)) := Real.log_nonneg (by linarith)
  let F := Real.log (35 * (M : ℝ)) ^ O
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hpoint (d : ℕ) (hd : d ∈ u.divisors) (k : ℕ) (hk : k ∈ dyadicBlockIndices (M / d)) :
      (∑ r ∈ nearbyHighBlock (u / d) v M M₀ d (2 ^ k) L,
        ‖nearbyQuadraticRemainder f u (d * r) v (a : ℤ) L‖) ≤
          C * (2 : ℝ) ^ k * Real.sqrt L * F := by
    have hR : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) k
    have hRM : (2 : ℕ) ^ k ≤ M := (pow_le_of_mem_dyadicBlockIndices hk).trans (Nat.div_le_self M d)
    have hRMreal : (2 : ℝ) ^ k ≤ M := by exact_mod_cast hRM
    have hRreal : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    have hlogR : 0 ≤ Real.log (35 * (2 : ℝ) ^ k) := Real.log_nonneg (by nlinarith)
    have hlog : Real.log (35 * (2 : ℝ) ^ k) ≤ Real.log (35 * (M : ℝ)) :=
      Real.log_le_log (by positivity) (by linarith)
    have hh := hblock a u v M M₀ Y hu hv hY ha huv hav L hL hcutoff hYv hglobal hsize d hd (2 ^ k) hR
    have hh' : (∑ r ∈ nearbyHighBlock (u / d) v M M₀ d (2 ^ k) L,
        ‖nearbyQuadraticRemainder f u (d * r) v (a : ℤ) L‖) ≤
          C * (2 : ℝ) ^ k * Real.sqrt L * Real.log (35 * (2 : ℝ) ^ k) ^ O := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hh
    apply hh'.trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogR hlog O) (by positivity)
  apply (sum_nearby_large_le_blocks f a u v M M₀ hu L).trans
  calc
    _ ≤ ∑ d ∈ u.divisors, ∑ k ∈ dyadicBlockIndices (M / d),
        C * (2 : ℝ) ^ k * Real.sqrt L * F := by
      apply Finset.sum_le_sum
      intro d hd
      exact Finset.sum_le_sum (fun k hk => hpoint d hd k hk)
    _ = (C * Real.sqrt L * F) *
        (∑ d ∈ u.divisors, ∑ k ∈ dyadicBlockIndices (M / d), (2 : ℝ) ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (C * Real.sqrt L * F) * (2 * M * (1 + Real.log u)) :=
      mul_le_mul_of_nonneg_left (sum_gcd_dyadic_block_mass_le hu M) (by positivity)
    _ = _ := by dsimp [F]; ring

end Erdos587
