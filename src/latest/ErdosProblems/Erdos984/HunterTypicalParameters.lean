/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterTypical

/-!
# Explicit parameters for typical rotations

This file specializes the abstract character-minor union bound to the
integer-power scale used by the finite Hunter construction.
-/

namespace Erdos984

noncomputable section

/-- Coordinate bound for every Fourier frequency used later. -/
def hunterFrequencyBound (D : ℕ) : ℕ := D ^ 300

/-- One more than the allowed rational rank of the resonant frequencies. -/
def hunterRankWitness (D : ℕ) : ℕ := D / 100 + 1

/-- A finite alphabet encoding every integer in the symmetric frequency
box `[-hunterFrequencyBound D, hunterFrequencyBound D]`. -/
abbrev HunterFrequencyAlphabet (D : ℕ) :=
  Fin (2 * hunterFrequencyBound D + 1)

/-- Interpret a frequency digit as a signed integer. -/
def decodeHunterFrequency (D : ℕ) (q : HunterFrequencyAlphabet D) : ℤ :=
  (q.val : ℤ) - hunterFrequencyBound D

/-- Radius of the simultaneous small-phase event. -/
def hunterPhaseTolerance (D : ℕ) : ℝ :=
  (D : ℝ) ^ (1000 * D) / hunterX D

/-- Exact cardinality of the index type in the typical-rotation union
bound. -/
lemma card_hunterTypicalIndex (D : ℕ) :
    Fintype.card
        (Fin (hunterN D) ×
          (Fin (hunterRankWitness D) → Fin D → HunterFrequencyAlphabet D) ×
          (Fin (hunterRankWitness D) → Fin D)) =
      hunterN D *
        (2 * hunterFrequencyBound D + 1) ^
          (D * hunterRankWitness D) *
        D ^ hunterRankWitness D := by
  simp [HunterFrequencyAlphabet, pow_mul]
  ring

lemma hunterFrequencyAlphabet_card_le (D : ℕ) (hD : 2 ≤ D) :
    2 * hunterFrequencyBound D + 1 ≤ D ^ 302 := by
  have hpos : 0 < D ^ 300 := pow_pos (by omega) _
  calc
    2 * hunterFrequencyBound D + 1 ≤ 3 * D ^ 300 := by
      simp only [hunterFrequencyBound]
      omega
    _ ≤ D ^ 2 * D ^ 300 := by
      gcongr
      nlinarith
    _ = D ^ 302 := by rw [← pow_add]

lemma hunter_D_le_rank_mul (D : ℕ) :
    D ≤ 100 * hunterRankWitness D := by
  unfold hunterRankWitness
  omega

lemma card_hunterTypicalIndex_le_pow (D : ℕ) (hD : 2 ≤ D) :
    Fintype.card
        (Fin (hunterN D) ×
          (Fin (hunterRankWitness D) → Fin D → HunterFrequencyAlphabet D) ×
          (Fin (hunterRankWitness D) → Fin D)) ≤
      D ^ (1000 * D * hunterRankWitness D) := by
  let r := hunterRankWitness D
  have hrpos : 0 < r := by simp [r, hunterRankWitness]
  have hDpos : 0 < D := by omega
  have hDsq : D ^ 2 ≤ 100 * (D * r) := by
    rw [pow_two, show 100 * (D * r) = D * (100 * r) by ring]
    exact Nat.mul_le_mul_left D (by simpa [r] using hunter_D_le_rank_mul D)
  have hr : r ≤ D * r := by
    simpa only [one_mul] using Nat.mul_le_mul_right r (by omega : 1 ≤ D)
  rw [card_hunterTypicalIndex]
  calc
    hunterN D * (2 * hunterFrequencyBound D + 1) ^ (D * r) * D ^ r =
        D ^ (D ^ 2) * (2 * hunterFrequencyBound D + 1) ^ (D * r) * D ^ r := by
      rw [hunterN]
    _ ≤
        D ^ (D ^ 2) * (D ^ 302) ^ (D * r) * D ^ r := by
      gcongr
      exact hunterFrequencyAlphabet_card_le D hD
    _ = D ^ (D ^ 2 + 302 * (D * r) + r) := by
      simp only [← pow_mul, ← pow_add]
    _ ≤ D ^ (1000 * D * r) := by
      apply Nat.pow_le_pow_right hDpos
      calc
        D ^ 2 + 302 * (D * r) + r ≤
            100 * (D * r) + 302 * (D * r) + D * r := by omega
        _ ≤ 1000 * (D * r) := by omega
        _ = 1000 * D * r := by ring

lemma two_mul_hunterPhaseTolerance_le (D : ℕ) (hD : 2 ≤ D) :
    2 * hunterPhaseTolerance D ≤
      ((D : ℝ) ^ (90000 * D))⁻¹ := by
  have hDreal : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (D : ℝ) ≠ 0 := by positivity
  have hphase : hunterPhaseTolerance D =
      ((D : ℝ) ^ (99000 * D))⁻¹ := by
    rw [hunterPhaseTolerance, hunterX, Nat.cast_pow]
    rw [show 100000 * D = 1000 * D + 99000 * D by omega, pow_add]
    field_simp
  rw [hphase]
  rw [show 99000 * D = 90000 * D + 9000 * D by omega, pow_add]
  rw [mul_inv]
  calc
    2 * (((D : ℝ) ^ (90000 * D))⁻¹ *
        ((D : ℝ) ^ (9000 * D))⁻¹) =
        ((D : ℝ) ^ (90000 * D))⁻¹ *
          (2 * ((D : ℝ) ^ (9000 * D))⁻¹) := by ring
    _ ≤ ((D : ℝ) ^ (90000 * D))⁻¹ * 1 := by
      gcongr
      rw [← div_eq_mul_inv, div_le_one (by positivity)]
      exact hDreal.trans (by
        rw [show 9000 * D = (9000 * D - 1) + 1 by omega, pow_succ]
        exact le_mul_of_one_le_left (by positivity)
          (one_le_pow₀ (by linarith : (1 : ℝ) ≤ D)))
    _ = ((D : ℝ) ^ (90000 * D))⁻¹ := by ring

lemma hunterPhaseTolerance_nonneg (D : ℕ) :
    0 ≤ hunterPhaseTolerance D := by
  unfold hunterPhaseTolerance
  positivity

lemma hunterPhaseTolerance_le_half (D : ℕ) (hD : 2 ≤ D) :
    hunterPhaseTolerance D ≤ (1 : ℝ) / 2 := by
  have htwo := two_mul_hunterPhaseTolerance_le D hD
  have hinv : ((D : ℝ) ^ (90000 * D))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ D by omega))
  linarith

lemma hunter_typical_real_cost_lt_one (D : ℕ) (hD : 2 ≤ D) :
    (Fintype.card
        (Fin (hunterN D) ×
          (Fin (hunterRankWitness D) → Fin D → HunterFrequencyAlphabet D) ×
          (Fin (hunterRankWitness D) → Fin D)) : ℝ) *
      (2 * hunterPhaseTolerance D) ^ hunterRankWitness D < 1 := by
  let r := hunterRankWitness D
  have hDreal : (1 : ℝ) < D := by exact_mod_cast hD
  have hrpos : 0 < r := by simp [r, hunterRankWitness]
  have hcardNat := card_hunterTypicalIndex_le_pow D hD
  have hcard :
      (Fintype.card
        (Fin (hunterN D) ×
          (Fin r → Fin D → HunterFrequencyAlphabet D) ×
          (Fin r → Fin D)) : ℝ) ≤
        (D : ℝ) ^ (1000 * D * r) := by
    exact_mod_cast hcardNat
  calc
    (Fintype.card
        (Fin (hunterN D) ×
          (Fin r → Fin D → HunterFrequencyAlphabet D) ×
          (Fin r → Fin D)) : ℝ) *
        (2 * hunterPhaseTolerance D) ^ r ≤
      (D : ℝ) ^ (1000 * D * r) *
        (((D : ℝ) ^ (90000 * D))⁻¹) ^ r := by
      gcongr
      · exact pow_nonneg
          (mul_nonneg zero_le_two (hunterPhaseTolerance_nonneg D)) r
      · exact mul_nonneg zero_le_two (hunterPhaseTolerance_nonneg D)
      · exact two_mul_hunterPhaseTolerance_le D hD
    _ = (D : ℝ) ^ (1000 * D * r) /
        (D : ℝ) ^ (90000 * D * r) := by
      rw [inv_pow, ← pow_mul]
      rfl
    _ < 1 := by
      rw [div_lt_one (by positivity)]
      apply pow_lt_pow_right₀ hDreal
      exact Nat.mul_lt_mul_of_pos_right
        (Nat.mul_lt_mul_of_pos_right (by omega) (by omega : 0 < D)) hrpos

lemma hunter_typical_real_cost_lt_half (D : ℕ) (hD : 2 ≤ D) :
    (Fintype.card
        (Fin (hunterN D) ×
          (Fin (hunterRankWitness D) → Fin D → HunterFrequencyAlphabet D) ×
          (Fin (hunterRankWitness D) → Fin D)) : ℝ) *
      (2 * hunterPhaseTolerance D) ^ hunterRankWitness D < (1 : ℝ) / 2 := by
  let r := hunterRankWitness D
  have hDreal : (1 : ℝ) < D := by exact_mod_cast hD
  have hrpos : 0 < r := by simp [r, hunterRankWitness]
  have hcardNat := card_hunterTypicalIndex_le_pow D hD
  have hcard :
      (Fintype.card
        (Fin (hunterN D) ×
          (Fin r → Fin D → HunterFrequencyAlphabet D) ×
          (Fin r → Fin D)) : ℝ) ≤
        (D : ℝ) ^ (1000 * D * r) := by
    exact_mod_cast hcardNat
  calc
    (Fintype.card
        (Fin (hunterN D) ×
          (Fin r → Fin D → HunterFrequencyAlphabet D) ×
          (Fin r → Fin D)) : ℝ) *
        (2 * hunterPhaseTolerance D) ^ r ≤
      (D : ℝ) ^ (1000 * D * r) *
        (((D : ℝ) ^ (90000 * D))⁻¹) ^ r := by
      gcongr
      · exact pow_nonneg
          (mul_nonneg zero_le_two (hunterPhaseTolerance_nonneg D)) r
      · exact mul_nonneg zero_le_two (hunterPhaseTolerance_nonneg D)
      · exact two_mul_hunterPhaseTolerance_le D hD
    _ = (D : ℝ) ^ (1000 * D * r) /
        (D : ℝ) ^ (90000 * D * r) := by
      rw [inv_pow, ← pow_mul]
      rfl
    _ < (1 : ℝ) / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      have hexp : 1000 * D * r + 1 < 90000 * D * r := by
        have hone : 1 ≤ D * r := Nat.one_le_iff_ne_zero.2 (mul_ne_zero
          (by omega) hrpos.ne')
        have hgap : 1000 * D * r + 1 ≤ 1001 * D * r := by
          rw [show 1001 * D * r = 1000 * D * r + D * r by ring]
          exact Nat.add_le_add_left hone _
        exact hgap.trans_lt (Nat.mul_lt_mul_of_pos_right
          (Nat.mul_lt_mul_of_pos_right (by omega) (by omega : 0 < D)) hrpos)
      have hpow :
          (D : ℝ) ^ (1000 * D * r + 1) <
            (D : ℝ) ^ (90000 * D * r) :=
        pow_lt_pow_right₀ hDreal hexp
      rw [pow_succ] at hpow
      have htwo :
          2 * (D : ℝ) ^ (1000 * D * r) ≤
            (D : ℝ) ^ (1000 * D * r) * D := by
        have hDtwo : (2 : ℝ) ≤ D := by exact_mod_cast hD
        simpa only [mul_comm] using
          (mul_le_mul_of_nonneg_right hDtwo
            (pow_nonneg (by positivity : (0 : ℝ) ≤ D) (1000 * D * r)))
      nlinarith

lemma hunter_typical_cost_lt_one (D : ℕ) (hD : 2 ≤ D) :
    (Fintype.card
        (Fin (hunterN D) ×
          (Fin (hunterRankWitness D) → Fin D → HunterFrequencyAlphabet D) ×
          (Fin (hunterRankWitness D) → Fin D)) : ENNReal) *
      (ENNReal.ofReal (2 * hunterPhaseTolerance D)) ^ hunterRankWitness D < 1 := by
  apply ennreal_nat_mul_ofReal_pow_lt_one
  · exact mul_nonneg zero_le_two (hunterPhaseTolerance_nonneg D)
  · exact hunter_typical_real_cost_lt_one D hD

lemma hunter_typical_cost_lt_half (D : ℕ) (hD : 2 ≤ D) :
    (Fintype.card
        (Fin (hunterN D) ×
          (Fin (hunterRankWitness D) → Fin D → HunterFrequencyAlphabet D) ×
          (Fin (hunterRankWitness D) → Fin D)) : ENNReal) *
      (ENNReal.ofReal (2 * hunterPhaseTolerance D)) ^ hunterRankWitness D <
        ENNReal.ofReal ((1 : ℝ) / 2) := by
  rw [← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_pow
      (mul_nonneg zero_le_two (hunterPhaseTolerance_nonneg D)),
    ← ENNReal.ofReal_mul (by positivity)]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2
    (hunter_typical_real_cost_lt_half D hD)

/-- An explicit typical rotation at the Hunter parameter scale. -/
lemma exists_hunter_typical_rotation (D : ℕ) (hD : 2 ≤ D) :
    ∃ θ : UnitAddTorus (Fin D),
      ∀ (n : Fin (hunterN D))
        (q : Fin (hunterRankWitness D) → Fin D → HunterFrequencyAlphabet D)
        (σ : Fin (hunterRankWitness D) → Fin D),
        (integerCharacterMinorRealMatrix
          (decodedFrequency (decodeHunterFrequency D) q) σ).det ≠ 0 →
        nsmulIntegerCharacterTuple (n + 1)
          (decodedFrequency (decodeHunterFrequency D) q) θ ∉
          Metric.closedBall
            (0 : UnitAddTorus (Fin (hunterRankWitness D)))
            (hunterPhaseTolerance D) := by
  apply exists_avoiding_character_minors
  · exact hunterPhaseTolerance_nonneg D
  · exact hunterPhaseTolerance_le_half D hD
  · simpa using hunter_typical_cost_lt_one D hD

end

end Erdos984
