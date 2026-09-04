import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Quantitative residue-class averages

All errors are uniform in the modulus and the residue. No limiting
equidistribution statement is substituted for the finite estimate.
-/

namespace Erdos69.Elementary

def residueCount (T d v : ℕ) : ℕ := T.count (fun k ↦ k ≡ v [MOD d])

noncomputable def residueFrequency (T d v : ℕ) : ℝ := (residueCount T d v : ℝ) / T

theorem residueCount_eq (T d v : ℕ) (hd : 0 < d) :
    residueCount T d v = T / d + if v % d < T % d then 1 else 0 :=
  Nat.count_modEq_card T hd v

theorem residueCount_error (T d v : ℕ) (hd : 0 < d) :
    |(residueCount T d v : ℝ) - (T : ℝ) / d| ≤ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hrem : ((T % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt T hd
  have hrem0 : (0 : ℝ) ≤ ((T % d : ℕ) : ℝ) := by positivity
  have hdecomp : (T : ℝ) = (d : ℝ) * ((T / d : ℕ) : ℝ) + ((T % d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod T d).symm
  have hquot : (T : ℝ) / d = ((T / d : ℕ) : ℝ) + ((T % d : ℕ) : ℝ) / d := by
    rw [div_eq_iff hdR.ne']
    field_simp
    nlinarith [hdecomp]
  have hfrac0 : (0 : ℝ) ≤ ((T % d : ℕ) : ℝ) / d := div_nonneg hrem0 hdR.le
  have hfrac1 : ((T % d : ℕ) : ℝ) / d < 1 := (div_lt_one hdR).mpr hrem
  rw [residueCount_eq T d v hd, hquot]
  split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

/-- The finite average differs from `1/d` by at most `1/T`. -/
theorem residueFrequency_error (T d v : ℕ) (hT : 0 < T) (hd : 0 < d) :
    |residueFrequency T d v - (1 : ℝ) / d| ≤ (1 : ℝ) / T := by
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hid : residueFrequency T d v - (1 : ℝ) / d =
      ((residueCount T d v : ℝ) - (T : ℝ) / d) / T := by
    unfold residueFrequency
    field_simp
  rw [hid, abs_div, abs_of_pos hTR]
  exact div_le_div_of_nonneg_right (residueCount_error T d v hd) hTR.le

/-- A coprime affine congruence is exactly one residue class, even when
the modulus is composite. -/
theorem exists_affine_residue (d Q b : ℕ) (hd : 0 < d) (hQ : Q.Coprime d) :
    ∃ v : ℕ, ∀ t : ℕ, d ∣ b + Q * t ↔ t ≡ v [MOD d] := by
  let : NeZero d := ⟨hd.ne'⟩
  let z : ZMod d := -((Q : ZMod d)⁻¹ * (b : ZMod d))
  refine ⟨z.val, fun t ↦ ?_⟩
  have hinv : (Q : ZMod d)⁻¹ * (Q : ZMod d) = 1 := by
    rw [mul_comm]
    exact ZMod.coe_mul_inv_eq_one Q hQ
  have hinv' : (Q : ZMod d) * (Q : ZMod d)⁻¹ = 1 := by
    rw [mul_comm]
    exact hinv
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_natCast_iff,
    Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  change (b : ZMod d) + (Q : ZMod d) * (t : ZMod d) = 0 ↔ (t : ZMod d) = z
  constructor
  · intro ht
    have h := congrArg (fun w : ZMod d ↦ (Q : ZMod d)⁻¹ * w) ht
    rw [mul_add, ← mul_assoc, hinv, one_mul, mul_zero] at h
    dsimp [z]
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using h)
  · intro ht
    rw [ht]
    dsimp [z]
    rw [mul_neg, ← mul_assoc, hinv', one_mul, add_neg_cancel]

def affineResidueCount (T d Q b : ℕ) : ℕ := T.count (fun t ↦ d ∣ b + Q * t)

theorem affineResidueCount_error (T d Q b : ℕ) (hd : 0 < d) (hQ : Q.Coprime d) :
    |(affineResidueCount T d Q b : ℝ) - (T : ℝ) / d| ≤ 1 := by
  obtain ⟨v, hv⟩ := exists_affine_residue d Q b hd hQ
  have heq : affineResidueCount T d Q b = residueCount T d v := by
    unfold affineResidueCount residueCount
    congr 1
    funext t
    exact propext (hv t)
  rw [heq]
  exact residueCount_error T d v hd

theorem affineResidueFrequency_error (T d Q b : ℕ) (hT : 0 < T)
    (hd : 0 < d) (hQ : Q.Coprime d) :
    |(affineResidueCount T d Q b : ℝ) / T - (1 : ℝ) / d| ≤ (1 : ℝ) / T := by
  obtain ⟨v, hv⟩ := exists_affine_residue d Q b hd hQ
  have heq : affineResidueCount T d Q b = residueCount T d v := by
    unfold affineResidueCount residueCount
    congr 1
    funext t
    exact propext (hv t)
  rw [heq]
  exact residueFrequency_error T d v hT hd

end Erdos69.Elementary
