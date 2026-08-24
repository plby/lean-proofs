import ErdosProblems.Erdos587.ArithmeticBlocks
import ErdosProblems.Erdos587.BlockParameters

/-!
# Uniform high-frequency gcd blocks

The inverse congruences are supplied by Bezout coefficients. The global size
conditions imply every hypothesis of the high-frequency block mean.
-/

open scoped BigOperators SchwartzMap

namespace Erdos587

noncomputable def nearbyHighBlock (q v M M₀ d R : ℕ) (L : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc R (2 * R)).filter fun r =>
    r.Coprime q ∧ M₀ < d * r ∧ d * r ≤ M ∧ 4 < (r : ℝ) * L / v

lemma mem_nearbyHighBlock (q v M M₀ d R r : ℕ) (L : ℝ) :
    r ∈ nearbyHighBlock q v M M₀ d R L ↔
      (R ≤ r ∧ r ≤ 2 * R) ∧ r.Coprime q ∧ M₀ < d * r ∧ d * r ≤ M ∧
        4 < (r : ℝ) * L / v := by
  classical
  simp only [nearbyHighBlock, Finset.mem_filter, Finset.mem_Icc]

lemma large_dual_width_implies_block_width {r R v : ℕ} {L : ℝ}
    (hv : 0 < v) (hL : 0 < L) (hrR : r ≤ 2 * R) (hwide : 4 < (r : ℝ) * L / v) :
    2 ≤ (R : ℝ) * L / v := by
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hrR' : (r : ℝ) ≤ 2 * R := by exact_mod_cast hrR
  have hmul := mul_le_mul_of_nonneg_right hrR' hL.le
  have hwide' := (lt_div_iff₀ hvR).mp hwide
  apply (le_div_iff₀ hvR).mpr
  nlinarith

lemma high_profile_parameter_ge_one {u v M₀ d q r : ℕ} {L : ℝ}
    (hd : 0 < d) (hq : 0 < q) (hv : 0 < v) (hL : 0 < L) (hdq : d * q = u)
    (hcutoff : (u : ℝ) * v / L ^ 2 < M₀ + 1) (hm : M₀ < d * r) :
    1 ≤ ((r : ℝ) / (q * v)) * L ^ 2 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hnext : (M₀ : ℝ) + 1 ≤ (d : ℝ) * r := by exact_mod_cast (show M₀ + 1 ≤ d * r by omega)
  have hlt := hcutoff.trans_le hnext
  have hmul := (div_lt_iff₀ (pow_pos hL 2)).mp hlt
  have hdqR : (d : ℝ) * q = u := by exact_mod_cast hdq
  have hprod : (d : ℝ) * ((q : ℝ) * v) < (d : ℝ) * ((r : ℝ) * L ^ 2) := by
    rw [show (d : ℝ) * ((q : ℝ) * v) = ((d : ℝ) * q) * v by ring, hdqR]
    nlinarith only [hmul]
  have hqv := (mul_lt_mul_iff_right₀ hdR).mp hprod
  rw [show ((r : ℝ) / (q * v)) * L ^ 2 = ((r : ℝ) * L ^ 2) / (q * v) by ring]
  exact (le_div_iff₀ (mul_pos hqR hvR)).mpr (by simpa only [one_mul] using hqv.le)

/-- A common set of global assumptions supplies the size conditions for
every nonempty high-frequency block in every gcd class. -/
theorem exists_nearby_high_block_global_bound (j : ℕ) (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧ ∀ (a u v M M₀ Y : ℕ),
      0 < u → 0 < v → 1 ≤ Y → a.Coprime u → u.Coprime v → u ∣ a * v + 1 →
      ∀ L : ℝ, 0 < L → (u : ℝ) * v / L ^ 2 < M₀ + 1 →
        4 * (Y : ℝ) * L ≤ v → 64 * (M : ℝ) * L ≤ u * v →
        64 * ((u + v) * M + 1) ≤ Y ^ (4 ^ j) →
        ∀ d ∈ u.divisors, ∀ R : ℕ, 0 < R →
          (∑ r ∈ nearbyHighBlock (u / d) v M M₀ d R L,
            ‖nearbyQuadraticRemainder f u (d * r) v (a : ℤ) L‖) ≤
              C * R * Real.sqrt L * Real.log (35 * (R : ℝ)) ^ O := by
  obtain ⟨C, hC, O, hO, hblock⟩ := exists_nearby_high_frequency_block_bound j f
  refine ⟨C, hC, O, hO, ?_⟩
  intro a u v M M₀ Y hu hv hY ha huv hav L hL hcutoff hYv hglobal hsize d hd R hR
  classical
  let q := u / d
  let D := nearbyHighBlock q v M M₀ d R L
  change (∑ r ∈ D, ‖nearbyQuadraticRemainder f u (d * r) v (a : ℤ) L‖) ≤ _
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdvd : d ∣ u := (Nat.mem_divisors.mp hd).1
  have hq : 0 < q := Nat.div_pos (Nat.le_of_dvd hu hdvd) hdpos
  have hdq : d * q = u := Nat.mul_div_cancel' hdvd
  have hqdiv : q ∣ u := ⟨d, by simpa only [mul_comm] using hdq.symm⟩
  by_cases hD : D.Nonempty
  · obtain ⟨r₀, hr₀⟩ := hD
    obtain ⟨⟨hRr₀, hr₀R⟩, hcop₀, hlow₀, hupper₀, hwide₀⟩ :=
      (mem_nearbyHighBlock q v M M₀ d R r₀ L).mp hr₀
    have hwidth := large_dual_width_implies_block_width hv hL hr₀R hwide₀
    have hdR : d * R ≤ M := (Nat.mul_le_mul_left d hRr₀).trans hupper₀
    obtain ⟨hK, hKR, h16, hroot, hKL⟩ := nearbyBlockWidth_global_conditions j u v M Y d q R
      hdpos hq hv hY hL hdq hdR hwidth hYv hglobal hsize
    have hDv (r : ℕ) (hr : r ∈ D) := (mem_nearbyHighBlock q v M M₀ d R r L).mp hr
    have hDr : ∀ r ∈ D, R ≤ r ∧ r ≤ 2 * R := fun r hr => (hDv r hr).1
    have hqv : q.Coprime v := Nat.Coprime.of_dvd_left hqdiv huv
    have haq : a.Coprime q := Nat.Coprime.of_dvd_right hqdiv ha
    have hinv : ∀ r ∈ D, (r : ℤ) ∣ (q : ℤ) * Nat.gcdA q r - 1 := by
      intro r hr
      exact gcdA_inverse_congruence (hDv r hr).2.1.symm
    have hB : ∀ r ∈ D, (q : ℤ) ∣ (r : ℤ) * a * Nat.gcdA (r * a) q - 1 := by
      intro r hr
      have hh := gcdA_inverse_congruence ((hDv r hr).2.1.mul_left haq)
      simpa only [Nat.cast_mul] using hh
    have hbv : (q : ℤ) ∣ (a : ℤ) * v + 1 := by exact_mod_cast hqdiv.trans hav
    have hA : ∀ r ∈ D, 1 ≤ ((r : ℝ) / (q * v)) * L ^ 2 := by
      intro r hr
      exact high_profile_parameter_ge_one hdpos hq hv hL hdq hcutoff (hDv r hr).2.2.1
    have hscale : ∀ r ∈ D,
        1 / 2 ≤ ((v : ℝ) / (r * L)) * nearbyBlockWidth R v L ∧
          ((v : ℝ) / (r * L)) * nearbyBlockWidth R v L ≤ 2 := by
      intro r hr
      exact nearbyBlockWidth_profile_scale hR hv hL hwidth (hDr r hr).1 (hDr r hr).2
    have hh := hblock v q R (nearbyBlockWidth R v L) hv hK hKR h16 hqv hroot
      D (fun r => Nat.gcdA q r) hDr hinv L hL hA hscale hKL (a : ℤ)
      (fun r => Nat.gcdA (r * a) q) hbv hB
    have heq (r : ℕ) : nearbyQuadraticRemainder f u (d * r) v (a : ℤ) L =
        nearbyQuadraticRemainder f q r v (a : ℤ) L := by
      rw [← hdq]
      exact nearbyQuadraticRemainder_mul f hdpos hq r v (a : ℤ) L
    simp_rw [heq]
    exact hh
  · have hempty : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    rw [hempty, Finset.sum_empty]
    have hlog : 0 ≤ Real.log (35 * (R : ℝ)) := by
      apply Real.log_nonneg
      have hRR : (1 : ℝ) ≤ R := by exact_mod_cast hR
      linarith
    positivity

end Erdos587
