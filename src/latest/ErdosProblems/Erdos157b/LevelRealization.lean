import ErdosProblems.Erdos157b.LocalEncoding
import ErdosProblems.Erdos157b.BlockRealization
import ErdosProblems.Erdos157b.TripleBlockLists

/-! Exact three-summand representations from compatible logarithms and tags. -/

namespace Erdos157.Binary

open Erdos157.Elementary

open AuxiliaryModuli

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

theorem realize_levelTarget (τ : MaskChoice K) (k : ℕ) (f₁ f₂ f₃ : LevelLabel K k)
    (d : ∀ i : Fin k, BlockTarget K i) (t : ∀ i : Fin k, TagField i × TagField i × TagField i)
    (hmom : ∀ i, Parabola.IsTriple ((targetMoments K d).firstMoment i)
      ((targetMoments K d).secondMoment i) (t i))
    (hlog : ∀ i : Fin k, maskedLog K i (τ i) (t i).1 (primeAtLevelResidue K k f₁ i) +
      maskedLog K i (τ i) (t i).2.1 (primeAtLevelResidue K k f₂ i) +
      maskedLog K i (τ i) (t i).2.2 (primeAtLevelResidue K k f₃ i) = (d i).1.data.val)
    (z : ℕ) (hzlo : 3 ≤ z) (hzhi : z ≤ 3 * Fintype.card K ^ (3 * k)) :
    ∃ c₁ c₂ c₃ : LocalChoice K k,
      localValue K τ k f₁ c₁ + localValue K τ k f₂ c₂ + localValue K τ k f₃ c₃ =
        levelTargetValue K d + blockPlace K 0 k * z := by
  classical
  have hfirst (i : Fin k) (j : Fin (tagDimension i)) :
      tagCoordinates i (t i).1 j + tagCoordinates i (t i).2.1 j + tagCoordinates i (t i).2.2 j =
        (((d i).2.1 j).data.val : ZMod 7) := by
    have hs := congrArg (fun a => tagCoordinates i a j) (hmom i).1
    simpa only [map_add, Pi.add_apply, targetMoments, LinearEquiv.apply_symm_apply] using hs
  have hsecond (i : Fin k) (j : Fin (tagDimension i)) :
      tagCoordinates i ((t i).1 ^ 2) j + tagCoordinates i ((t i).2.1 ^ 2) j +
        tagCoordinates i ((t i).2.2 ^ 2) j = (((d i).2.2 j).data.val : ZMod 7) := by
    have hs := congrArg (fun a => tagCoordinates i a j) (hmom i).2
    simpa only [map_add, Pi.add_apply, targetMoments, LinearEquiv.apply_symm_apply] using hs
  choose a₁ a₂ a₃ ha using (fun i : Fin k => realize_blockTarget K i (τ i) (d i)
    (primeAtLevelResidue K k f₁ i) (primeAtLevelResidue K k f₂ i) (primeAtLevelResidue K k f₃ i)
    (t i).1 (t i).2.1 (t i).2.2 (hlog i) (hfirst i) (hsecond i))
  obtain ⟨r₁, r₂, r₃, hr⟩ := three_top_digits (by positivity : 0 < Fintype.card K ^ (3 * k)) hzlo hzhi
  let c₁ : LocalChoice K k := (fun i => ⟨(t i).1, a₁ i⟩, r₁)
  let c₂ : LocalChoice K k := (fun i => ⟨(t i).2.1, a₂ i⟩, r₂)
  let c₃ : LocalChoice K k := (fun i => ⟨(t i).2.2, a₃ i⟩, r₃)
  let x₁ := fun i : Fin k => blockDigits K i (τ i) (primeAtLevelResidue K k f₁ i) (c₁.1 i)
  let x₂ := fun i : Fin k => blockDigits K i (τ i) (primeAtLevelResidue K k f₂ i) (c₂.1 i)
  let x₃ := fun i : Fin k => blockDigits K i (τ i) (primeAtLevelResidue K k f₃ i) (c₃.1 i)
  let w := fun i : Fin k => blockTargetDigits K i (d i)
  have hplace₁ (i : Fin k) : MixedRadix.place (x₁ i) = blockRadix K i := blockDigits_place K _ _ _ _
  have hplace₂ (i : Fin k) : MixedRadix.place (x₂ i) = blockRadix K i := blockDigits_place K _ _ _ _
  have hplace₃ (i : Fin k) : MixedRadix.place (x₃ i) = blockRadix K i := blockDigits_place K _ _ _ _
  have hplacew (i : Fin k) : MixedRadix.place (w i) = blockRadix K i := blockTargetDigits_place K _ _
  have hsum := encode_flatten_triple_eq x₁ x₂ x₃ w
    (fun i => (hplace₁ i).trans (hplace₂ i).symm)
    (fun i => (hplace₁ i).trans (hplace₃ i).symm)
    (fun i => (hplace₁ i).trans (hplacew i).symm) ha
  refine ⟨c₁, c₂, c₃, ?_⟩
  rw [levelTargetValue_eq_encode]
  change (MixedRadix.encode (List.ofFn x₁).flatten + blockPlace K 0 k * (1 + r₁.val)) +
    (MixedRadix.encode (List.ofFn x₂).flatten + blockPlace K 0 k * (1 + r₂.val)) +
    (MixedRadix.encode (List.ofFn x₃).flatten + blockPlace K 0 k * (1 + r₃.val)) =
    MixedRadix.encode (List.ofFn w).flatten + blockPlace K 0 k * z
  nlinarith

end Erdos157.Binary
