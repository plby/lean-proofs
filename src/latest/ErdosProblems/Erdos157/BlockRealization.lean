import ErdosProblems.Erdos157.TargetBlocks
import ErdosProblems.Erdos157.TripleDigits

/-! Exact realization of a tagged target block by a compatible residue triple. -/

namespace Erdos157.Elementary

open AuxiliaryModuli

theorem encode_packed_block {n : ℕ} (b x : ℕ) (y z : Fin n → ℕ) :
    MixedRadix.encode ((103 * b, x) ::
      (List.ofFn (fun j => (721, y j)) ++ List.ofFn (fun j => (721, z j)))) =
      x + 103 * b * (MixedRadix.encode (List.ofFn (fun j => (721, y j))) +
        721 ^ n * MixedRadix.encode (List.ofFn (fun j => (721, z j)))) := by
  rw [MixedRadix.encode_cons, MixedRadix.encode_append]
  have hp : MixedRadix.place (List.ofFn (fun j => (721, y j))) = 721 ^ n := by
    simp only [MixedRadix.place, List.map_ofFn, Function.comp_def, List.ofFn_const, List.prod_replicate]
  rw [hp]

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

theorem realize_blockTarget (i : ℕ) (τ : TagField i → LogDigit K i)
    (d : BlockTarget K i) (u₁ u₂ u₃ : (ResidueField K i)ˣ)
    (t₁ t₂ t₃ : TagField i)
    (hlog : maskedLog K i τ t₁ u₁ + maskedLog K i τ t₂ u₂ + maskedLog K i τ t₃ u₃ = d.1.data.val)
    (hfirst : ∀ j, tagCoordinates i t₁ j + tagCoordinates i t₂ j + tagCoordinates i t₃ j =
      ((d.2.1 j).data.val : ZMod 7))
    (hsecond : ∀ j, tagCoordinates i (t₁ ^ 2) j + tagCoordinates i (t₂ ^ 2) j +
      tagCoordinates i (t₃ ^ 2) j = ((d.2.2 j).data.val : ZMod 7)) :
    ∃ a₁ a₂ a₃ : BlockAuxIndex i → AuxiliaryDigit,
      MixedRadix.encode (blockDigits K i τ u₁ ⟨t₁, a₁⟩) +
        MixedRadix.encode (blockDigits K i τ u₂ ⟨t₂, a₂⟩) +
        MixedRadix.encode (blockDigits K i τ u₃ ⟨t₃, a₃⟩) =
        MixedRadix.encode (blockTargetDigits K i d) := by
  classical
  obtain ⟨l₁, l₂, l₃, hl⟩ := d.1.realize (maskedLog K i τ t₁ u₁)
    (maskedLog K i τ t₂ u₂) (maskedLog K i τ t₃ u₃) hlog
  choose f₁ f₂ f₃ hf using (fun j => (d.2.1 j).realize
    (tagCoordinates i t₁ j) (tagCoordinates i t₂ j) (tagCoordinates i t₃ j) (hfirst j))
  choose s₁ s₂ s₃ hs using (fun j => (d.2.2 j).realize
    (tagCoordinates i (t₁ ^ 2) j) (tagCoordinates i (t₂ ^ 2) j)
      (tagCoordinates i (t₃ ^ 2) j) (hsecond j))
  let a₁ : BlockAuxIndex i → AuxiliaryDigit := Sum.elim (fun _ => l₁) (Sum.elim f₁ s₁)
  let a₂ : BlockAuxIndex i → AuxiliaryDigit := Sum.elim (fun _ => l₂) (Sum.elim f₂ s₂)
  let a₃ : BlockAuxIndex i → AuxiliaryDigit := Sum.elim (fun _ => l₃) (Sum.elim f₃ s₃)
  refine ⟨a₁, a₂, a₃, ?_⟩
  let x₁ := PairDigits.pack (Nat.card (ResidueField K i)ˣ) (maskedLog K i τ t₁ u₁).val l₁
  let x₂ := PairDigits.pack (Nat.card (ResidueField K i)ˣ) (maskedLog K i τ t₂ u₂).val l₂
  let x₃ := PairDigits.pack (Nat.card (ResidueField K i)ˣ) (maskedLog K i τ t₃ u₃).val l₃
  let y₁ := fun j => PairDigits.pack 7 (tagCoordinates i t₁ j).val (f₁ j)
  let y₂ := fun j => PairDigits.pack 7 (tagCoordinates i t₂ j).val (f₂ j)
  let y₃ := fun j => PairDigits.pack 7 (tagCoordinates i t₃ j).val (f₃ j)
  let z₁ := fun j => PairDigits.pack 7 (tagCoordinates i (t₁ ^ 2) j).val (s₁ j)
  let z₂ := fun j => PairDigits.pack 7 (tagCoordinates i (t₂ ^ 2) j).val (s₂ j)
  let z₃ := fun j => PairDigits.pack 7 (tagCoordinates i (t₃ ^ 2) j).val (s₃ j)
  let E (v : Fin (i + 2) → ℕ) := MixedRadix.encode (List.ofFn (fun j => (721, v j)))
  have hfy : E y₁ + E y₂ + E y₃ = E (fun j => (d.2.1 j).value) :=
    encode_ofFn_triple_eq (fun _ => 721) y₁ y₂ y₃ _ hf
  have hsz : E z₁ + E z₂ + E z₃ = E (fun j => (d.2.2 j).value) :=
    encode_ofFn_triple_eq (fun _ => 721) z₁ z₂ z₃ _ hs
  change MixedRadix.encode ((103 * Nat.card (ResidueField K i)ˣ, x₁) ::
      (List.ofFn (fun j => (721, y₁ j)) ++ List.ofFn (fun j => (721, z₁ j)))) +
    MixedRadix.encode ((103 * Nat.card (ResidueField K i)ˣ, x₂) ::
      (List.ofFn (fun j => (721, y₂ j)) ++ List.ofFn (fun j => (721, z₂ j)))) +
    MixedRadix.encode ((103 * Nat.card (ResidueField K i)ˣ, x₃) ::
      (List.ofFn (fun j => (721, y₃ j)) ++ List.ofFn (fun j => (721, z₃ j)))) = _
  rw [encode_packed_block, encode_packed_block, encode_packed_block]
  change (x₁ + 103 * Nat.card (ResidueField K i)ˣ * (E y₁ + 721 ^ (i + 2) * E z₁)) +
    (x₂ + 103 * Nat.card (ResidueField K i)ˣ * (E y₂ + 721 ^ (i + 2) * E z₂)) +
    (x₃ + 103 * Nat.card (ResidueField K i)ˣ * (E y₃ + 721 ^ (i + 2) * E z₃)) = _
  calc
    _ = (x₁ + x₂ + x₃) + 103 * Nat.card (ResidueField K i)ˣ *
        ((E y₁ + E y₂ + E y₃) + 721 ^ (i + 2) * (E z₁ + E z₂ + E z₃)) := by ring
    _ = d.1.value + 103 * Nat.card (ResidueField K i)ˣ *
        (E (fun j => (d.2.1 j).value) + 721 ^ (i + 2) * E (fun j => (d.2.2 j).value)) := by
      rw [hl, hfy, hsz]
    _ = _ := (encode_packed_block _ _ _ _).symm

end Erdos157.Elementary
