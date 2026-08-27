/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UncoveredNeighborEnvelope
import ErdosProblems.Erdos207.KSSSErrorEnvelopeUpper

/-! # A relative extension envelope with a vanishing terminal error -/

namespace Erdos207

noncomputable section

def relativePatternEnvelope (E t : ℝ) (s B : ℕ) (time : ℝ) : ℝ :=
  ksssErrorEnvelope E (16 * t ^ 2 / t ^ s) (B + 2) time

theorem relativePatternEnvelope_pair_error
    (E N t time x : ℝ) (s B : ℕ) (hN : 0 < N) (ht : 0 < t)
    (hp : 0 < ksssEdgeDensity E time)
    (hx : N / (2 * t) * ksssEdgeDensity E time ^ 2 ≤ x) :
    8 * t * ksssErrorEnvelope E (N / t ^ s) B time / x ≤
      relativePatternEnvelope E t s B time := by
  have h := pair_error_le_neighbor_envelope N t t (ksssEdgeDensity E time) x s B
    hN ht.le ht hp hx
  simpa only [relativePatternEnvelope, ksssErrorEnvelope, pow_two, mul_assoc] using h

theorem relativePatternEnvelope_growth
    (E t time : ℝ) (s B : ℕ) (hE : 0 < E) (ht : 0 < t)
    (hclock : 3 * (time + 1) < E) :
    6 * relativePatternEnvelope E t s B time / (E * ksssEdgeDensity E time) ≤
      relativePatternEnvelope E t s B (time + 1) - relativePatternEnvelope E t s B time := by
  have hg := ksssErrorEnvelope_unitStep_growth E (16 * t ^ 2 / t ^ s) time (B + 2)
    hE (by positivity) hclock
  have hp := ksssEdgeDensity_pos hE (show 3 * time < E by linarith)
  have hz : 0 ≤ relativePatternEnvelope E t s B time := by
    unfold relativePatternEnvelope ksssErrorEnvelope
    positivity
  have hcoef : (6 : ℝ) ≤ 3 * ((B + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 6 ≤ 3 * (B + 2) by omega)
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hz)
    (mul_pos hE hp).le).trans hg

theorem relativePatternEnvelope_terminal_bound
    (E t time : ℝ) (b B : ℕ) (ht : 0 < t)
    (hfloor : 1 / t ^ b ≤ ksssEdgeDensity E time) :
    relativePatternEnvelope E t (ksssPowerErrorExponent b B) B time ≤ 16 / t ^ b := by
  let p := ksssEdgeDensity E time
  let s := ksssPowerErrorExponent b B
  have hp : 0 < p := (by positivity : 0 < 1 / t ^ b).trans_le hfloor
  have hinverse := inverse_density_power_le t p b (B + 2) ht hp hfloor
  calc
    _ = (16 * t ^ 2 / t ^ s) * (1 / p ^ (B + 2)) := by
      unfold relativePatternEnvelope ksssErrorEnvelope
      ring
    _ ≤ (16 * t ^ 2 / t ^ s) * t ^ (b * (B + 2)) :=
      mul_le_mul_of_nonneg_left hinverse (by positivity)
    _ = _ := by
      have hexp : s = b * (B + 2) + b + 2 := by dsimp only [s, ksssPowerErrorExponent]; ring
      rw [hexp, pow_add, pow_add]
      field_simp

theorem relativePatternEnvelope_unitStep_abs_le_clock
    (E t time : ℝ) (b B : ℕ) (hE : 0 < E) (ht : 1 ≤ t) (hb : 1 ≤ b)
    (hclock : 3 * time + 6 ≤ E) (hfloor : 1 / t ^ b ≤ ksssEdgeDensity E time)
    (hcoefficient : 6 * ((B + 2 : ℕ) : ℝ) * 2 ^ (B + 2) ≤ t) :
    |relativePatternEnvelope E t (ksssPowerErrorExponent b B) B (time + 1) -
      relativePatternEnvelope E t (ksssPowerErrorExponent b B) B time| ≤
        16 / (E * ksssEdgeDensity E time) := by
  have htpos : 0 < t := by linarith
  have hp := ksssEdgeDensity_pos hE (show 3 * time < E by linarith)
  have hz0 : 0 ≤ relativePatternEnvelope E t (ksssPowerErrorExponent b B) B time := by
    unfold relativePatternEnvelope ksssErrorEnvelope
    positivity
  have hpower : t ≤ t ^ b := by simpa only [pow_one] using pow_le_pow_right₀ ht hb
  have hz : relativePatternEnvelope E t (ksssPowerErrorExponent b B) B time ≤ 16 / t :=
    (relativePatternEnvelope_terminal_bound E t time b B htpos hfloor).trans
      (div_le_div_of_nonneg_left (by norm_num) htpos hpower)
  have he := ksssErrorEnvelope_unitStep_abs_upper E
    (16 * t ^ 2 / t ^ ksssPowerErrorExponent b B) time (B + 2) hE (by positivity) hclock
  calc
    _ ≤ (6 * ((B + 2 : ℕ) : ℝ) * 2 ^ (B + 2)) *
        relativePatternEnvelope E t (ksssPowerErrorExponent b B) B time /
          (E * ksssEdgeDensity E time) := he
    _ ≤ t * (16 / t) / (E * ksssEdgeDensity E time) := by gcongr
    _ = _ := by field_simp

theorem relativePatternEnvelope_taylor_cover
    (E t time : ℝ) (s B : ℕ) (hE : 0 < E) (ht : 1 ≤ t)
    (htime : 0 ≤ time) (hclock : 3 * time < E) :
    4 / t ^ s ≤ 3 * relativePatternEnvelope E t s B time := by
  have htpos : 0 < t := by linarith
  have hscale := ksssErrorEnvelope_ge_scale E (16 * t ^ 2 / t ^ s) time (B + 2)
    hE (by positivity) htime hclock
  have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht
  calc
    _ ≤ (48 * t ^ 2) / t ^ s := div_le_div_of_nonneg_right (by linarith only [ht2]) (by positivity)
    _ = 3 * (16 * t ^ 2 / t ^ s) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by norm_num)

end

end Erdos207
