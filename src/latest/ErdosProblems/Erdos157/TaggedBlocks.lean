import ErdosProblems.Erdos157.ResidueLogs
import ErdosProblems.Erdos157.PairDigits

/-! Packed blocks for the tagged integer encoding. -/

namespace Erdos157.Elementary

namespace PackedDigits

/-- Every digit is strictly below half its radix. Thus two strings add without carries. -/
def HalfValid : List (ℕ × ℕ) → Prop
  | [] => True
  | (b, d) :: xs => 2 ≤ b ∧ 2 * d < b ∧ HalfValid xs

theorem halfValid_append (xs ys : List (ℕ × ℕ)) :
    HalfValid (xs ++ ys) ↔ HalfValid xs ∧ HalfValid ys := by
  induction xs with
  | nil => simp [HalfValid]
  | cons p xs ih => rcases p with ⟨b, d⟩; simp [HalfValid, ih, and_assoc]

theorem halfValid_iff_forall (xs : List (ℕ × ℕ)) :
    HalfValid xs ↔ ∀ p ∈ xs, 2 ≤ p.1 ∧ 2 * p.2 < p.1 := by
  induction xs with
  | nil => simp [HalfValid]
  | cons p xs ih => rcases p with ⟨b, d⟩; simp [HalfValid, ih, and_assoc]

theorem halfValid_ofFn {n : ℕ} (f : Fin n → ℕ × ℕ)
    (hf : ∀ i, 2 ≤ (f i).1 ∧ 2 * (f i).2 < (f i).1) : HalfValid (List.ofFn f) := by
  rw [halfValid_iff_forall]
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact hf i

theorem HalfValid.valid {xs : List (ℕ × ℕ)} (h : HalfValid xs) : MixedRadix.Valid xs := by
  induction xs with
  | nil => trivial
  | cons p xs ih =>
    rcases p with ⟨b, d⟩
    exact ⟨h.1, by have := h.2.1; omega, ih h.2.2⟩

theorem HalfValid.two_encode_lt_place {xs : List (ℕ × ℕ)} (h : HalfValid xs) :
    2 * MixedRadix.encode xs < MixedRadix.place xs := by
  induction xs with
  | nil => simp
  | cons p xs ih =>
    rcases p with ⟨b, d⟩
    have ht := ih h.2.2
    have hb := h.1
    have hd := h.2.1
    have hm := Nat.mul_le_mul_left b (show 2 * MixedRadix.encode xs + 1 ≤ MixedRadix.place xs by omega)
    rw [MixedRadix.encode_cons, MixedRadix.place_cons]
    nlinarith

theorem pair_encode_lt_place {xs ys : List (ℕ × ℕ)} (hx : HalfValid xs) (hy : HalfValid ys)
    (hp : MixedRadix.place xs = MixedRadix.place ys) :
    MixedRadix.encode xs + MixedRadix.encode ys < MixedRadix.place xs := by
  have h1 := hx.two_encode_lt_place
  have h2 := hy.two_encode_lt_place
  omega

theorem halfValid_pack (b x : ℕ) (a : AuxiliaryDigit) (hx : x < b) :
    2 ≤ 103 * b ∧ 2 * PairDigits.pack b x a < 103 * b := by
  have h := PairDigits.pack_lt b x a hx
  omega

end PackedDigits

abbrev BlockAuxIndex (i : ℕ) := Unit ⊕ (Fin (i + 2) ⊕ Fin (i + 2))

structure BlockChoice (i : ℕ) where
  tag : TagField i
  auxiliary : BlockAuxIndex i → AuxiliaryDigit

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

open AuxiliaryModuli PackedDigits

noncomputable def blockDigits (i : ℕ) (τ : TagField i → LogDigit K i)
    (u : (ResidueField K i)ˣ) (c : BlockChoice i) : List (ℕ × ℕ) :=
  (103 * Nat.card (ResidueField K i)ˣ,
    PairDigits.pack (Nat.card (ResidueField K i)ˣ) (maskedLog K i τ c.tag u).val
      (c.auxiliary (.inl ()))) ::
    (List.ofFn (fun j : Fin (i + 2) =>
      (103 * 7, PairDigits.pack 7 (tagCoordinates i c.tag j).val (c.auxiliary (.inr (.inl j))))) ++
    List.ofFn (fun j : Fin (i + 2) =>
      (103 * 7, PairDigits.pack 7 (tagCoordinates i (c.tag ^ 2) j).val (c.auxiliary (.inr (.inr j))))))

theorem blockDigits_halfValid (i : ℕ) (τ : TagField i → LogDigit K i)
    (u : (ResidueField K i)ˣ) (c : BlockChoice i) : HalfValid (blockDigits K i τ u c) := by
  unfold blockDigits
  have hp := halfValid_pack _ _ (c.auxiliary (.inl ())) (ZMod.val_lt (maskedLog K i τ c.tag u))
  refine ⟨hp.1, hp.2, ?_⟩
  rw [halfValid_append]
  constructor <;> apply halfValid_ofFn <;> intro j <;>
    exact halfValid_pack _ _ _ (ZMod.val_lt _)

theorem blockDigits_length (i : ℕ) (τ : TagField i → LogDigit K i)
    (u : (ResidueField K i)ˣ) (c : BlockChoice i) : (blockDigits K i τ u c).length = 2 * i + 5 := by
  simp only [blockDigits, List.length_cons, List.length_append, List.length_ofFn]
  omega

theorem blockDigits_radices_eq (i : ℕ) (τ σ : TagField i → LogDigit K i)
    (u v : (ResidueField K i)ˣ) (c d : BlockChoice i) :
    (blockDigits K i τ u c).map Prod.fst = (blockDigits K i σ v d).map Prod.fst := by
  simp only [blockDigits, List.map_cons, List.map_append, List.map_ofFn, Function.comp_def]

theorem blockDigits_get_log (i : ℕ) (τ : TagField i → LogDigit K i)
    (u : (ResidueField K i)ˣ) (c : BlockChoice i) :
    (blockDigits K i τ u c)[0]? = some (103 * Nat.card (ResidueField K i)ˣ,
      PairDigits.pack (Nat.card (ResidueField K i)ˣ) (maskedLog K i τ c.tag u).val
        (c.auxiliary (.inl ()))) := rfl

theorem blockDigits_get_tag (i : ℕ) (τ : TagField i → LogDigit K i)
    (u : (ResidueField K i)ˣ) (c : BlockChoice i) (j : Fin (i + 2)) :
    (blockDigits K i τ u c)[j.1 + 1]? = some (721,
      PairDigits.pack 7 (tagCoordinates i c.tag j).val (c.auxiliary (.inr (.inl j)))) := by
  unfold blockDigits
  rw [List.getElem?_cons_succ, List.getElem?_append_left (by simpa only [List.length_ofFn] using j.2),
    List.getElem?_ofFn, dif_pos j.2]

theorem blockDigits_get_square (i : ℕ) (τ : TagField i → LogDigit K i)
    (u : (ResidueField K i)ˣ) (c : BlockChoice i) (j : Fin (i + 2)) :
    (blockDigits K i τ u c)[i + 2 + j.1 + 1]? = some (721,
      PairDigits.pack 7 (tagCoordinates i (c.tag ^ 2) j).val (c.auxiliary (.inr (.inr j)))) := by
  unfold blockDigits
  rw [List.getElem?_cons_succ, List.getElem?_append_right (by simp only [List.length_ofFn]; omega),
    List.length_ofFn, Nat.add_sub_cancel_left, List.getElem?_ofFn, dif_pos j.2]

noncomputable def blockRadix (i : ℕ) : ℕ :=
  (103 * Nat.card (ResidueField K i)ˣ) * 721 ^ (2 * i + 4)

theorem blockDigits_place (i : ℕ) (τ : TagField i → LogDigit K i)
    (u : (ResidueField K i)ˣ) (c : BlockChoice i) :
    MixedRadix.place (blockDigits K i τ u c) = blockRadix K i := by
  simp only [MixedRadix.place, blockDigits, List.map_cons, List.map_append, List.map_ofFn,
    Function.comp_def, List.prod_cons, List.prod_append, List.ofFn_const, List.prod_replicate]
  change (103 * Nat.card (ResidueField K i)ˣ) * (721 ^ (i + 2) * 721 ^ (i + 2)) = _
  rw [← pow_add]
  congr 2
  omega

end Erdos157.Elementary
