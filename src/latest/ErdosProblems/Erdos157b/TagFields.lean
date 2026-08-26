import ErdosProblems.Erdos157b.Parameters
import ErdosProblems.Erdos157b.TagSupports
import ErdosProblems.Erdos157.TagFields

/-! Polynomial-sized characteristic-seven tags for the binary coefficient field. -/

namespace Erdos157.Binary

open Elementary

abbrev CoefficientField := ZMod 2

theorem card_coefficientField : Fintype.card CoefficientField = 2 := by simp [CoefficientField]

abbrev TagField (i : ℕ) := GaloisField 7 (tagDimension i)

noncomputable instance tagFieldFintype (i : ℕ) : Fintype (TagField i) := Fintype.ofFinite _

noncomputable instance tagFieldDecidableEq (i : ℕ) : DecidableEq (TagField i) := Classical.decEq _

theorem card_tagField (i : ℕ) : Fintype.card (TagField i) = 7 ^ tagDimension i := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 7 (tagDimension i) (Nat.ne_of_gt (tagDimension_pos i))

noncomputable def tagCoordinates (i : ℕ) :
    TagField i ≃ₗ[ZMod 7] (Fin (tagDimension i) → ZMod 7) :=
  (Module.finBasisOfFinrankEq (ZMod 7) (TagField i)
    (GaloisField.finrank 7 (Nat.ne_of_gt (tagDimension_pos i)))).equivFun

theorem tag_pair_decoding (i : ℕ) (a b c d : TagField i)
    (hsum : ∀ j, tagCoordinates i a j + tagCoordinates i b j =
      tagCoordinates i c j + tagCoordinates i d j)
    (hsq : ∀ j, tagCoordinates i (a ^ 2) j + tagCoordinates i (b ^ 2) j =
      tagCoordinates i (c ^ 2) j + tagCoordinates i (d ^ 2) j) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have h2 : (2 : TagField i) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff (TagField i) 7 2).mp h
    norm_num at this
  apply Parabola.pair_eq_of_sum_and_sq_sum h2
  · apply (tagCoordinates i).injective
    ext j
    simpa using hsum j
  · apply (tagCoordinates i).injective
    ext j
    simpa using hsq j

theorem tagField_disjoint_trials (i n : ℕ) (hn : 1 ≤ n)
    (hsize : 7 * n ≤ 7 ^ tagDimension i) (u v : TagField i) :
    ∃ T : Fin n → TagField i × TagField i × TagField i,
      (∀ j, Parabola.IsTriple u v (T j)) ∧
      (∀ j, 2 ≤ (Parabola.support (T j)).card) ∧
      Pairwise (fun j k => Disjoint (Parabola.support (T j)) (Parabola.support (T k))) := by
  exact Binary.exists_disjoint_triples u v n hn (by simpa only [card_tagField] using hsize)

end Erdos157.Binary
