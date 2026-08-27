/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic

/-! # Nonzero distinct roots of the literal one-family pinned forms -/

namespace Erdos4b.FGKMT

noncomputable section

def commonPinnedSlope {m : ℕ} (h : Fin (m + 1) → ℕ) (j : Fin (m + 1))
    (p : ℕ) (i : Fin m) : ZMod p :=
  (h (j.succAbove i) : ZMod p) - h j

def commonPinnedRoot {m : ℕ} (h : Fin (m + 1) → ℕ) (j : Fin (m + 1))
    (Q p : ℕ) (i : Fin m) : ZMod p :=
  -(Q : ZMod p) * (commonPinnedSlope h j p i)⁻¹

theorem commonPinnedSlope_ne_zero {m p : ℕ} (h : Fin (m + 1) → ℕ)
    (hinj : Function.Injective h) (hsmall : ∀ i, h i < p)
    (j : Fin (m + 1)) (i : Fin m) : commonPinnedSlope h j p i ≠ 0 := by
  intro hz
  have he : (h (j.succAbove i) : ZMod p) = h j := sub_eq_zero.mp hz
  have hm := (ZMod.natCast_eq_natCast_iff _ _ p).mp he
  have hij := hinj (hm.eq_of_lt_of_lt (hsmall _) (hsmall _))
  exact Fin.succAbove_ne j i hij

theorem commonPinnedSlope_injective {m p : ℕ} (h : Fin (m + 1) → ℕ)
    (hinj : Function.Injective h) (hsmall : ∀ i, h i < p)
    (j : Fin (m + 1)) : Function.Injective (commonPinnedSlope h j p) := by
  intro i l he
  have hcast : (h (j.succAbove i) : ZMod p) = h (j.succAbove l) := sub_left_inj.mp he
  have hm := (ZMod.natCast_eq_natCast_iff _ _ p).mp hcast
  exact j.succAboveEmb.injective (hinj (hm.eq_of_lt_of_lt (hsmall _) (hsmall _)))

theorem commonPinnedRoot_iff_affine_zero {m Q p : ℕ} (hp : p.Prime)
    (h : Fin (m + 1) → ℕ) (hinj : Function.Injective h) (hsmall : ∀ i, h i < p)
    (j : Fin (m + 1)) (i : Fin m) (z : ZMod p) :
    z = commonPinnedRoot h j Q p i ↔ (Q : ZMod p) + commonPinnedSlope h j p i * z = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  rw [commonPinnedRoot, ← div_eq_mul_inv,
    eq_div_iff (commonPinnedSlope_ne_zero h hinj hsmall j i)]
  constructor <;> intro he <;> linear_combination he

theorem commonPinnedRoot_ne_zero {m Q p : ℕ} (hp : p.Prime) (hQ : ¬p ∣ Q)
    (h : Fin (m + 1) → ℕ) (hinj : Function.Injective h) (hsmall : ∀ i, h i < p)
    (j : Fin (m + 1)) (i : Fin m) : commonPinnedRoot h j Q p i ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  exact mul_ne_zero
    (neg_ne_zero.mpr (fun hz => hQ ((ZMod.natCast_eq_zero_iff Q p).mp hz)))
    (inv_ne_zero (commonPinnedSlope_ne_zero h hinj hsmall j i))

theorem commonPinnedRoot_injective {m Q p : ℕ} (hp : p.Prime) (hQ : ¬p ∣ Q)
    (h : Fin (m + 1) → ℕ) (hinj : Function.Injective h) (hsmall : ∀ i, h i < p)
    (j : Fin (m + 1)) : Function.Injective (commonPinnedRoot h j Q p) := by
  let : Fact p.Prime := ⟨hp⟩
  have hQ0 : -(Q : ZMod p) ≠ 0 :=
    neg_ne_zero.mpr (fun hz => hQ ((ZMod.natCast_eq_zero_iff Q p).mp hz))
  intro i l he
  exact commonPinnedSlope_injective h hinj hsmall j
    (inv_injective (mul_left_cancel₀ hQ0 he))

theorem commonPinnedRoot_iff_int_dvd {m Q p : ℕ} (hp : p.Prime)
    (h : Fin (m + 1) → ℕ) (hinj : Function.Injective h) (hsmall : ∀ i, h i < p)
    (j : Fin (m + 1)) (i : Fin m) (P : ℤ) :
    (P : ZMod p) = commonPinnedRoot h j Q p i ↔
      (p : ℤ) ∣ (Q : ℤ) - (h j : ℤ) * P + (h (j.succAbove i) : ℤ) * P := by
  rw [commonPinnedRoot_iff_affine_zero hp h hinj hsmall j i,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast, commonPinnedSlope]
  ring_nf

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonPinnedRoot_iff_int_dvd
#print axioms Erdos4b.FGKMT.commonPinnedRoot_injective
#print axioms Erdos4b.FGKMT.commonPinnedRoot_ne_zero
