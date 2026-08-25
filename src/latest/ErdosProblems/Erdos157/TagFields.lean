import ErdosProblems.Erdos157.Parabola
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The characteristic-seven tag fields

Block indices are zero-based: block `i` uses the field with `7^(i+2)`
elements, recorded in `i+2` base-seven coordinates.
-/

namespace Erdos157.Elementary

instance seven_isPrime : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The tag field for block `i`. -/
abbrev TagField (i : ℕ) := GaloisField 7 (i + 2)

noncomputable instance tagFieldFintype (i : ℕ) : Fintype (TagField i) :=
  Fintype.ofFinite _

noncomputable instance tagFieldDecidableEq (i : ℕ) : DecidableEq (TagField i) :=
  Classical.decEq _

theorem card_tagField (i : ℕ) : Fintype.card (TagField i) = 7 ^ (i + 2) := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 7 (i + 2) (by omega)

/-- The base-seven vector representation used by the integer encoding. -/
noncomputable def tagCoordinates (i : ℕ) :
    TagField i ≃ₗ[ZMod 7] (Fin (i + 2) → ZMod 7) :=
  (Module.finBasisOfFinrankEq (ZMod 7) (TagField i)
    (GaloisField.finrank 7 (by omega))).equivFun

/-- Equality of the encoded first and second moments recovers the tag pair. -/
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

/-- Each sufficiently high tag field supplies the required number of trials. -/
theorem tagField_disjoint_trials (i n : ℕ) (hn : 1 ≤ n) (hsize : n ≤ 7 ^ i)
    (u v : TagField i) :
    ∃ T : Fin n → TagField i × TagField i × TagField i,
      (∀ j, Parabola.IsTriple u v (T j)) ∧
      (∀ j, 2 ≤ (Parabola.support (T j)).card) ∧
      Pairwise (fun j k => Disjoint (Parabola.support (T j)) (Parabola.support (T k))) := by
  apply Parabola.exists_disjoint_triples u v n hn
  rw [card_tagField, pow_add]
  norm_num
  nlinarith

end Erdos157.Elementary
