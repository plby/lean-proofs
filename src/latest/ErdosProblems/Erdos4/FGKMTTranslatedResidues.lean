import ErdosProblems.Erdos4.FGKMTTranslatedWeights
import ErdosProblems.Erdos4.LabelResidueClass

/-! Each translated divisor label is exactly one residue class. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical DivisorCoefficients DivisibilityExpansion ProductCharacterEncoding

theorem modEq_add_offset_iff (n a Y T d : ℕ) (hTY : T + Y ≡ 0 [MOD d]) :
    n + T ≡ a [MOD d] ↔ n ≡ a + Y [MOD d] := by
  constructor
  · intro hn
    have hc : n + T + Y ≡ n [MOD d] := by
      simpa only [Nat.add_assoc, Nat.add_zero] using (Nat.ModEq.refl n).add hTY
    exact hc.symm.trans (hn.add (Nat.ModEq.refl Y))
  · intro hn
    have hYT : Y + T ≡ 0 [MOD d] := by simpa only [Nat.add_comm] using hTY
    have hc : a + Y + T ≡ a [MOD d] := by
      simpa only [Nat.add_assoc, Nat.add_zero] using (Nat.ModEq.refl a).add hYT
    exact (hn.add (Nat.ModEq.refl T)).trans hc

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

def translatedNaturalOffset (Y : ℕ) : ℕ := modulus ell * (Y + 1) - Y

theorem translatedNaturalOffset_add (Y : ℕ) :
    translatedNaturalOffset ell Y + Y = modulus ell * (Y + 1) := by
  have hM : 1 ≤ modulus ell := Finset.prod_pos
    (fun l _ => (Fact.out : (ell l).Prime).pos)
  have hY : Y ≤ modulus ell * (Y + 1) :=
    (Nat.le_succ Y).trans (by simpa only [one_mul] using Nat.mul_le_mul_right (Y + 1) hM)
  exact Nat.sub_add_cancel hY

theorem totalDivisor_dvd_modulus (a : P → Option (Fin k)) : totalDivisor ell a ∣ modulus ell := by
  apply Finset.prod_dvd_prod_of_dvd
  intro l _
  split_ifs
  · exact one_dvd _
  · exact dvd_rfl

theorem translatedNaturalOffset_modEq (Y d : ℕ) (hd : d ∣ modulus ell) :
    translatedNaturalOffset ell Y + Y ≡ 0 [MOD d] := by
  rw [translatedNaturalOffset_add]
  exact Nat.modEq_zero_iff_dvd.mpr (hd.trans (dvd_mul_right _ _))

theorem translatedResidueState_eq_shifted (h : Fin k → ℕ) (Y n p : ℕ) (l : P) :
    translatedResidueState ell h Y n p l =
      AffineWeights.residueState ell h (n + translatedNaturalOffset ell Y) p l := by
  have hz : (translatedNaturalOffset ell Y : ZMod (ell l)) + Y = 0 := by
    rw [← Nat.cast_add, translatedNaturalOffset_add]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr
      ((local_dvd_modulus ell l).trans (dvd_mul_right _ _))
  have heq : ((n + translatedNaturalOffset ell Y : ℕ) : ZMod (ell l)) =
      (n : ZMod (ell l)) - Y := by
    rw [Nat.cast_add]
    linear_combination hz
  unfold translatedResidueState AffineWeights.residueState
  rw [heq]

theorem translated_evaluation_is_residue
    (hcop : Pairwise (fun l r => (ell l).Coprime (ell r)))
    (h : Fin k → ℕ) (hinj : ∀ l, Function.Injective (fun i => (h i : ZMod (ell l))))
    (Y p : ℕ) (hp : p.Coprime (modulus ell)) (a : P → Option (Fin k)) :
    ∃ r : ℕ, ∀ n : ℕ, evaluation (translatedResidueState ell h Y n p) a =
      if n ≡ r [MOD totalDivisor ell a] then 1 else 0 := by
  obtain ⟨r, hr⟩ := LabelResidueClass.evaluation_is_residue ell hcop h hinj p hp a
  refine ⟨r + Y, ?_⟩
  intro n
  have hs : translatedResidueState ell h Y n p =
      AffineWeights.residueState ell h (n + translatedNaturalOffset ell Y) p :=
    funext (translatedResidueState_eq_shifted ell h Y n p)
  rw [hs, hr]
  simp only [modEq_add_offset_iff n r Y (translatedNaturalOffset ell Y) (totalDivisor ell a)
    (translatedNaturalOffset_modEq ell Y _ (totalDivisor_dvd_modulus ell a))]

end Erdos4.FGKMT
