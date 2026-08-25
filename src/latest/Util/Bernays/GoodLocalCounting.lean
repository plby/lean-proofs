import Util.Bernays.LocalAvoidance
import Util.Bernays.GenusNorms

/-!
# Exact counting of local norms coprime to the discriminant
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

theorem coprime_iff_primeFactors_avoid {M : ℕ} (hM : M ≠ 0) (n : ℕ) :
    n.Coprime M ↔ ∀ p ∈ M.primeFactors, ¬p ∣ n := by
  constructor
  · intro hc p hp hpn
    have hdata := Nat.mem_primeFactors.mp hp
    exact hdata.1.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd hpn hdata.2.1)
  · intro h
    by_contra hc
    obtain ⟨p, hp, hpn, hpM⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    exact h p (Nat.mem_primeFactors.mpr ⟨hp, hpM, hM⟩) hpn

noncomputable def goodLocalValues (d b : ℤ) (hD : b ^ 2 + 4 * d ≠ 0) (N : ℕ) : Finset ℕ :=
  (localValues (fun p : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD p = -1) N).filter
    fun n => n.Coprime (discriminantLevel (b ^ 2 + 4 * d))

noncomputable def goodLocalConstant (d b : ℤ) (hD : b ^ 2 + 4 * d ≠ 0) : ℝ := by
  letI : NeZero (discriminantLevel (b ^ 2 + 4 * d)) := ⟨(discriminantLevel_pos hD).ne'⟩
  exact (characterLocalConstant (discriminantCharacter (b ^ 2 + 4 * d) hD) / sqrt π) *
    avoidFactor (discriminantLevel (b ^ 2 + 4 * d)).primeFactors

theorem goodLocalConstant_pos {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) : 0 < goodLocalConstant d b hD.ne := by
  letI : NeZero (discriminantLevel (b ^ 2 + 4 * d)) := ⟨(discriminantLevel_pos hD.ne).ne'⟩
  exact mul_pos
    (div_pos (characterLocalConstant_pos _ (discriminantCharacter_ne_one hD)) (sqrt_pos.mpr pi_pos))
    (avoidFactor_pos _ (fun _ hp => (Nat.mem_primeFactors.mp hp).1))

theorem goodLocalValues_eq_avoid {d b : ℤ} (hD : b ^ 2 + 4 * d ≠ 0) (N : ℕ) :
    goodLocalValues d b hD N =
      localAvoidValues (fun p : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD p = -1)
        (discriminantLevel (b ^ 2 + 4 * d)).primeFactors N := by
  ext n
  simp only [goodLocalValues, localAvoidValues, Finset.mem_filter,
    coprime_iff_primeFactors_avoid (discriminantLevel_pos hD).ne']

theorem goodLocalValues_card_limit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    Tendsto (fun N : ℕ => ((goodLocalValues d b hD.ne N).card : ℝ) / scale N)
      atTop (𝓝 (goodLocalConstant d b hD.ne)) := by
  letI : NeZero (discriminantLevel (b ^ 2 + 4 * d)) := ⟨(discriminantLevel_pos hD.ne).ne'⟩
  simp_rw [goodLocalValues_eq_avoid]
  unfold goodLocalConstant
  apply localAvoidValues_card_limit _ (discriminantCharacter_sq _ hD.ne)
    (discriminantCharacter_ne_one hD)
  intro p hp
  have hdata := Nat.mem_primeFactors.mp hp
  refine ⟨hdata.1, ?_⟩
  have hz : discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = 0 :=
    (char_prime_eq_zero_iff _ ⟨p, hdata.1⟩).mpr hdata.2.1
  rw [hz]
  norm_num

end Bernays
