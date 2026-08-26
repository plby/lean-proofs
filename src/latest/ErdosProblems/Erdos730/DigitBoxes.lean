/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.HigherPowerCount
import ErdosProblems.Erdos730.KummerTransition
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Erdős 730: finite lower-half digit boxes

This file supplies the concrete finite set used by the p-adic block counts.
For an odd prime `p`, `halfDigitCount p = (p+1)/2`; the permitted digits are
exactly `0, ..., halfDigitCount p - 1`.  Encoding `r` such digits in base `p`
gives a subset of `ZMod (p^r)` of cardinality `halfDigitCount p ^ r`.

The final membership theorem is the bridge needed by every event count:
`LowerHalfDigits p n` forces the residue of `n` modulo `p^r` to lie in this
finite box.  Leading zeroes are inserted explicitly, so the statement also
covers `n = 0` and `r = 0`.
-/

namespace Erdos730
namespace DigitBoxes

open KummerTransition

/-- Number of permitted base-`p` digits for an odd prime. -/
def halfDigitCount (p : ℕ) : ℕ := (p + 1) / 2

theorem halfDigitCount_eq_succ_half {p : ℕ} (hpodd : p % 2 = 1) :
    halfDigitCount p = (p - 1) / 2 + 1 := by
  unfold halfDigitCount
  omega

theorem halfDigitCount_pos {p : ℕ} (hp : 1 ≤ p) :
    0 < halfDigitCount p := by
  unfold halfDigitCount
  omega

theorem one_lt_halfDigitCount {p : ℕ} (hp : 3 ≤ p) :
    1 < halfDigitCount p := by
  unfold halfDigitCount
  omega

theorem halfDigitCount_le {p : ℕ} (hp : 1 ≤ p) :
    halfDigitCount p ≤ p := by
  unfold halfDigitCount
  omega

/-- Natural encodings of all length-`r` strings of permitted digits. -/
noncomputable def lowerHalfResiduesNat (p r : ℕ) : Finset ℕ := by
  classical
  by_cases hH : 1 < halfDigitCount p
  · exact (List.fixedLengthDigits hH r).image (Nat.ofDigits p)
  · exact ∅

private theorem ofDigits_injective_on_lowerHalf
    {p r : ℕ} (hp : 1 < p) (hH : 1 < halfDigitCount p)
    (hHp : halfDigitCount p ≤ p) :
    Set.InjOn (Nat.ofDigits p) (List.fixedLengthDigits hH r) := by
  intro L hL K hK hEq
  have hLm := (List.mem_fixedLengthDigits_iff hH).mp hL
  have hKm := (List.mem_fixedLengthDigits_iff hH).mp hK
  exact Nat.ofDigits_inj_of_len_eq hp (hLm.1.trans hKm.1.symm)
    (fun d hd ↦ (hLm.2 d hd).trans_le hHp)
    (fun d hd ↦ (hKm.2 d hd).trans_le hHp) hEq

theorem lowerHalfResiduesNat_card
    {p r : ℕ} (hp : 3 ≤ p) :
    (lowerHalfResiduesNat p r).card = halfDigitCount p ^ r := by
  classical
  have hp1 : 1 < p := by omega
  have hH : 1 < halfDigitCount p := one_lt_halfDigitCount hp
  have hHp : halfDigitCount p ≤ p := halfDigitCount_le (by omega)
  rw [lowerHalfResiduesNat, dif_pos hH,
    Finset.card_image_iff.mpr (ofDigits_injective_on_lowerHalf hp1 hH hHp),
    List.card_fixedLengthDigits]

theorem mem_lowerHalfResiduesNat_lt_pow
    {p r n : ℕ} (hp : 3 ≤ p)
    (hn : n ∈ lowerHalfResiduesNat p r) : n < p ^ r := by
  classical
  have hH : 1 < halfDigitCount p := one_lt_halfDigitCount hp
  rw [lowerHalfResiduesNat, dif_pos hH, Finset.mem_image] at hn
  obtain ⟨L, hL, rfl⟩ := hn
  have hLm := (List.mem_fixedLengthDigits_iff hH).mp hL
  rw [← hLm.1]
  exact Nat.ofDigits_lt_base_pow_length (by omega)
    (fun d hd ↦ (hLm.2 d hd).trans_le (halfDigitCount_le (by omega)))

/-- The permitted digit box as residues modulo `p^r`. -/
noncomputable def lowerHalfResidues (p r : ℕ) : Finset (ZMod (p ^ r)) :=
  Finset.image (fun n : ℕ ↦ (n : ZMod (p ^ r)))
    (lowerHalfResiduesNat p r)

private theorem natCast_injective_on_lowerHalf
    {p r : ℕ} (hp : 3 ≤ p) :
    Set.InjOn (fun n : ℕ ↦ (n : ZMod (p ^ r)))
      (lowerHalfResiduesNat p r) := by
  intro m hm n hn hcast
  have hmLt := mem_lowerHalfResiduesNat_lt_pow hp hm
  have hnLt := mem_lowerHalfResiduesNat_lt_pow hp hn
  have hval := congrArg ZMod.val hcast
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hmLt,
    Nat.mod_eq_of_lt hnLt] using hval

theorem lowerHalfResidues_card {p r : ℕ} (hp : 3 ≤ p) :
    (lowerHalfResidues p r).card = halfDigitCount p ^ r := by
  classical
  rw [lowerHalfResidues,
    Finset.card_image_iff.mpr (natCast_injective_on_lowerHalf hp),
    lowerHalfResiduesNat_card hp]

private def paddedLowDigits (p r n : ℕ) : List ℕ :=
  let low := (Nat.digits p n).take r
  low ++ List.replicate (r - low.length) 0

private theorem paddedLowDigits_length (p r n : ℕ) :
    (paddedLowDigits p r n).length = r := by
  simp only [paddedLowDigits, List.length_append, List.length_replicate,
    List.length_take]
  omega

private theorem paddedLowDigits_digits_lt_half
    {p r n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : LowerHalfDigits p n) :
    ∀ d ∈ paddedLowDigits p r n, d < halfDigitCount p := by
  intro d hd
  rw [paddedLowDigits, List.mem_append, List.mem_replicate] at hd
  rcases hd with hd | ⟨_hrep, rfl⟩
  · have hdDigits : d ∈ Nat.digits p n :=
      List.mem_of_mem_take hd
    have hdHalf := hn d hdDigits
    rw [halfDigitCount_eq_succ_half
      ((hp.mod_two_eq_one_iff_ne_two).2 hp2)]
    omega
  · exact halfDigitCount_pos hp.one_le

private theorem ofDigits_paddedLowDigits
    {p r n : ℕ} (hp : p.Prime) :
    Nat.ofDigits p (paddedLowDigits p r n) = n % p ^ r := by
  unfold paddedLowDigits
  rw [Nat.ofDigits_append_replicate_zero]
  exact (Nat.self_mod_pow_eq_ofDigits_take r n hp.two_le).symm

/-- Every lower-half integer lands in the finite lower-half residue box at
every depth. -/
theorem natCast_mem_lowerHalfResidues
    {p r n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : LowerHalfDigits p n) :
    (n : ZMod (p ^ r)) ∈ lowerHalfResidues p r := by
  classical
  have hp3 : 3 ≤ p := by
    have hp2le := hp.two_le
    omega
  have hH : 1 < halfDigitCount p := one_lt_halfDigitCount hp3
  let L := paddedLowDigits p r n
  have hLmem : L ∈ List.fixedLengthDigits hH r := by
    rw [List.mem_fixedLengthDigits_iff hH]
    exact ⟨paddedLowDigits_length p r n,
      paddedLowDigits_digits_lt_half hp hp2 hn⟩
  have hNat : Nat.ofDigits p L ∈ lowerHalfResiduesNat p r := by
    rw [lowerHalfResiduesNat, dif_pos hH]
    exact Finset.mem_image.mpr ⟨L, hLmem, rfl⟩
  rw [lowerHalfResidues, Finset.mem_image]
  refine ⟨Nat.ofDigits p L, hNat, ?_⟩
  have hDigits : Nat.ofDigits p L = n % p ^ r := by
    simpa [L] using ofDigits_paddedLowDigits (p := p) (r := r) (n := n) hp
  calc
    ((Nat.ofDigits p L : ℕ) : ZMod (p ^ r)) =
        ((n % p ^ r : ℕ) : ZMod (p ^ r)) := congrArg (fun m : ℕ ↦
          (m : ZMod (p ^ r))) hDigits
    _ = (n : ZMod (p ^ r)) := ZMod.natCast_mod n (p ^ r)

#print axioms lowerHalfResiduesNat_card
#print axioms lowerHalfResidues_card
#print axioms natCast_mem_lowerHalfResidues

end DigitBoxes
end Erdos730
