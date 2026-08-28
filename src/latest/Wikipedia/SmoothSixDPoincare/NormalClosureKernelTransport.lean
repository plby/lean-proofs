import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Transport of exact normal-closure kernels along a surjective homomorphism -/

open Set Function

namespace Wikipedia.SmoothSixDPoincare.NormalClosureKernel

variable {A B C D R : Type*} [Group A] [Group B] [Group C] [Group D] [Group R]

theorem kernel_map (f : A →* B) (g : C →* D) (ρ : A →* C) (hρ : Surjective ρ)
    (hnull : ∀ a, f a = 1 ↔ g (ρ a) = 1) : g.ker = f.ker.map ρ := by
  ext γ
  constructor
  · intro hγ
    obtain ⟨δ, rfl⟩ := hρ γ
    exact ⟨δ, (hnull δ).mpr hγ, rfl⟩
  · rintro ⟨δ, hδ, rfl⟩
    exact (hnull δ).mp hδ

theorem kernel_normalClosure (f : A →* B) (g : C →* D) (ρ : A →* C)
    (s : R →* A) (hρ : Surjective ρ) (hnull : ∀ a, f a = 1 ↔ g (ρ a) = 1)
    (hker : f.ker = Subgroup.normalClosure (range s)) :
    g.ker = Subgroup.normalClosure (range (ρ.comp s)) := by
  calc
    g.ker = f.ker.map ρ := kernel_map f g ρ hρ hnull
    _ = (Subgroup.normalClosure (range s)).map ρ := congrArg (Subgroup.map ρ) hker
    _ = Subgroup.normalClosure (ρ '' range s) := Subgroup.map_normalClosure (range s) ρ hρ
    _ = Subgroup.normalClosure (range (ρ.comp s)) :=
      congrArg Subgroup.normalClosure (Set.range_comp ρ s).symm

end Wikipedia.SmoothSixDPoincare.NormalClosureKernel
