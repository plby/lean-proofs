import Arxiv.Arxiv2411_18291.SparseRainbowGeneration

/-! # Repeated colour labels do not enlarge the generator union -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {I J T V : Type*} [Fintype I] [Fintype J] [Fintype T] [DecidableEq V] {q : ℕ}

theorem permutedUnion_comp_surjective (σ : I → Equiv.Perm V) (f : J → I)
    (hf : Function.Surjective f) (D : Finset (Block V q)) :
    permutedUnion (fun j => σ (f j)) D = permutedUnion σ D := by
  ext Q
  rw [mem_permutedUnion, mem_permutedUnion]
  constructor
  · rintro ⟨j, P, hP, heq⟩
    exact ⟨f j, P, hP, heq⟩
  · rintro ⟨i, P, hP, heq⟩
    obtain ⟨j, rfl⟩ := hf i
    exact ⟨j, P, hP, heq⟩

theorem permutedUnion_augmented_repeated [Nonempty T]
    (σ : J → Equiv.Perm V) (τ : I → Equiv.Perm V) (D : Finset (Block V q)) :
    permutedUnion (augmentedPermutation (fun p : T × J => σ p.2) τ) D =
      permutedUnion (augmentedPermutation σ τ) D := by
  let f : Option ((T × J) ⊕ I) → Option (J ⊕ I) :=
    Option.map (Sum.map Prod.snd id)
  have hf : Function.Surjective f := by
    intro o
    cases o with
    | none => exact ⟨none, rfl⟩
    | some o =>
      cases o with
      | inl j => exact ⟨some (Sum.inl (Classical.choice inferInstance, j)), rfl⟩
      | inr i => exact ⟨some (Sum.inr i), rfl⟩
  have heq : augmentedPermutation (fun p : T × J => σ p.2) τ =
      fun o => augmentedPermutation σ τ (f o) := by
    funext o
    cases o with
    | none => rfl
    | some o => cases o <;> rfl
  rw [heq]
  exact permutedUnion_comp_surjective (augmentedPermutation σ τ) f hf D

end Arxiv2411_18291
