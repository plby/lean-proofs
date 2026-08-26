import ErdosProblems.Erdos73.QuadrangularFaceSwitch
import Mathlib.Logic.Equiv.Set

/-! Constructing the vertex rotation by matching two oriented-edge enumerations. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Equiv

theorem exists_perm_matching_range {D X : Type*} [Finite D] (A B : D → X)
    (hA : Function.Injective A) (hrange : Set.range A = Set.range B) :
    ∃ σ : Perm D, ∀ d, A (σ d) = B d := by
  let e := Equiv.ofInjective A hA
  let f : D → D := fun d => e.symm ⟨B d, hrange ▸ Set.mem_range_self d⟩
  have hf : ∀ d, A (f d) = B d := by
    intro d
    exact congrArg Subtype.val (e.apply_symm_apply ⟨B d, hrange ▸ Set.mem_range_self d⟩)
  have hsurj : Function.Surjective f := by
    intro d
    obtain ⟨x, hx⟩ := hrange ▸ Set.mem_range_self d
    refine ⟨x, hA ?_⟩
    exact (hf x).trans hx
  exact ⟨Equiv.ofBijective f ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩, hf⟩

def orientedPortPair {D U : Type*} (label : D → U) (α : Perm D) (d : D) : U × U :=
  (label d, label (α d))

theorem rotation_label_of_pair_eq {D U : Type*} (label : D → U) (α β σ : Perm D)
    (hpair : ∀ d, orientedPortPair label α (σ d) = orientedPortPair label β d) (d : D) :
    label (σ d) = label d := congrArg Prod.fst (hpair d)

theorem rotation_intertwines_of_pair_eq {D U : Type*} (label : D → U) (α β σ : Perm D)
    (hα : Function.Involutive α) (hβ : Function.Involutive β)
    (hA : Function.Injective (orientedPortPair label α))
    (hpair : ∀ d, orientedPortPair label α (σ d) = orientedPortPair label β d) :
    α * σ = σ * β := by
  ext d
  apply hA
  change orientedPortPair label α (α (σ d)) = orientedPortPair label α (σ (β d))
  rw [hpair (β d)]
  apply Prod.ext
  · exact congrArg Prod.snd (hpair d)
  · change label (α (α (σ d))) = label (β (β d))
    rw [hα (σ d), hβ d]
    exact rotation_label_of_pair_eq label α β σ hpair d

theorem exists_quadrangular_rotation {D U : Type*} [Finite D]
    (label : D → U) (α τ : Perm D) (hα : Function.Involutive α)
    (hτ : Function.Involutive τ) (hcomm : Function.Commute α τ)
    (hA : Function.Injective (orientedPortPair label α))
    (hrange : Set.range (orientedPortPair label α) =
      Set.range (orientedPortPair label (τ * α))) :
    ∃ σ : Perm D, (∀ d, orientedPortPair label α (σ d) = orientedPortPair label (τ * α) d) ∧
      (∀ d, label (σ d) = label d) ∧ σ⁻¹ * α * σ * α = τ := by
  obtain ⟨σ, hσ⟩ := exists_perm_matching_range (orientedPortPair label α)
    (orientedPortPair label (τ * α)) hA hrange
  have hβ : Function.Involutive (τ * α) := by
    intro d
    change τ (α (τ (α d))) = d
    rw [hcomm, hα d, hτ d]
  have hh := rotation_intertwines_of_pair_eq label α (τ * α) σ hα hβ hA hσ
  refine ⟨σ, hσ, rotation_label_of_pair_eq label α (τ * α) σ hσ, ?_⟩
  have hαα : α * α = 1 := by ext d; exact hα d
  calc
    σ⁻¹ * α * σ * α = σ⁻¹ * (α * σ) * α := by group
    _ = σ⁻¹ * (σ * (τ * α)) * α := by rw [hh]
    _ = τ * (α * α) := by group
    _ = τ := by rw [hαα, mul_one]

end
end Erdos73
