import ErdosProblems.Erdos157.TaggedBlocks
import ErdosProblems.Erdos157b.ResidueLogs

namespace Erdos157.Binary

open Erdos157.Elementary

abbrev BlockAuxIndex (i : ℕ) := Unit ⊕ (Fin (tagDimension i) ⊕ Fin (tagDimension i))

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
    (List.ofFn (fun j : Fin (tagDimension i) =>
      (103 * 7, PairDigits.pack 7 (tagCoordinates i c.tag j).val (c.auxiliary (.inr (.inl j))))) ++
    List.ofFn (fun j : Fin (tagDimension i) =>
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
    (u : (ResidueField K i)ˣ) (c : BlockChoice i) : (blockDigits K i τ u c).length = 1 + 2 * tagDimension i := by
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
    (u : (ResidueField K i)ˣ) (c : BlockChoice i) (j : Fin (tagDimension i)) :
    (blockDigits K i τ u c)[j.1 + 1]? = some (721,
      PairDigits.pack 7 (tagCoordinates i c.tag j).val (c.auxiliary (.inr (.inl j)))) := by
  unfold blockDigits
  rw [List.getElem?_cons_succ, List.getElem?_append_left (by simpa only [List.length_ofFn] using j.2),
    List.getElem?_ofFn, dif_pos j.2]

theorem blockDigits_get_square (i : ℕ) (τ : TagField i → LogDigit K i)
    (u : (ResidueField K i)ˣ) (c : BlockChoice i) (j : Fin (tagDimension i)) :
    (blockDigits K i τ u c)[tagDimension i + j.1 + 1]? = some (721,
      PairDigits.pack 7 (tagCoordinates i (c.tag ^ 2) j).val (c.auxiliary (.inr (.inr j)))) := by
  unfold blockDigits
  rw [List.getElem?_cons_succ, List.getElem?_append_right (by simp only [List.length_ofFn]; omega),
    List.length_ofFn, Nat.add_sub_cancel_left, List.getElem?_ofFn, dif_pos j.2]

noncomputable def blockRadix (i : ℕ) : ℕ :=
  (103 * Nat.card (ResidueField K i)ˣ) * 721 ^ (2 * tagDimension i)

theorem blockDigits_place (i : ℕ) (τ : TagField i → LogDigit K i)
    (u : (ResidueField K i)ˣ) (c : BlockChoice i) :
    MixedRadix.place (blockDigits K i τ u c) = blockRadix K i := by
  simp only [MixedRadix.place, blockDigits, List.map_cons, List.map_append, List.map_ofFn,
    Function.comp_def, List.prod_cons, List.prod_append, List.ofFn_const, List.prod_replicate]
  change (103 * Nat.card (ResidueField K i)ˣ) * (721 ^ (tagDimension i) * 721 ^ (tagDimension i)) = _
  rw [← pow_add]
  congr 2
  omega

end Erdos157.Binary
