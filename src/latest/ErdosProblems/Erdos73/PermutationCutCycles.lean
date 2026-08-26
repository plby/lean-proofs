import Mathlib.GroupTheory.Perm.Cycle.Basic

/-! A cycle leaving a finite cut must return; application to involutive switches. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Equiv

variable {D : Type*} [Finite D]

theorem sameCycle_of_unique_return (ρ : Perm D) (P : D → Prop) (a b : D)
    (ha : P a) (hout : ¬P (ρ a))
    (hreturn : ∀ x, ¬P x → P (ρ x) → x = b) : ρ.SameCycle a b := by
  by_contra hn
  let s : Set D := {x | ρ.SameCycle a x ∧ ¬P x}
  have hmap : Set.MapsTo ρ s s := by
    intro x hx
    refine ⟨hx.1.apply_right, ?_⟩
    intro hpx
    have he := hreturn x hx.2 hpx
    exact hn (he ▸ hx.1)
  have hbij := (s.toFinite.injOn_iff_bijOn_of_mapsTo hmap).mp ρ.injective.injOn
  have hmem : ρ a ∈ s := ⟨(Perm.SameCycle.refl ρ a).apply_right, hout⟩
  obtain ⟨x, hx, he⟩ := hbij.surjOn hmem
  exact hx.2 (ρ.injective he ▸ ha)

theorem sameCycle_switch_of_cut (σ S : Perm D)
    (a : D) (P : D → Prop) (hσ : ∀ x, P (σ x) ↔ P x)
    (ha : P a) (hSa : ¬P (S a))
    (hreturn : ∀ x, ¬P x → P (S x) → x = S a) :
    (σ * S).SameCycle a (S a) := by
  apply sameCycle_of_unique_return (σ * S) P a (S a) ha
  · simpa only [Perm.mul_apply, hσ] using hSa
  · intro x hx hsx
    exact hreturn x hx ((hσ (S x)).mp hsx)

theorem sameCycle_of_steps {ρ σ : Perm D}
    (hstep : ∀ x, ρ.SameCycle x (σ x)) {a b : D} (hab : σ.SameCycle a b) :
    ρ.SameCycle a b := by
  obtain ⟨n, rfl⟩ := hab.exists_nat_pow_eq
  clear hab
  induction n with
  | zero => simpa only [pow_zero, Perm.one_apply] using Perm.SameCycle.refl ρ a
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact ih.trans (hstep _)

theorem sameCycle_rotation_of_switch {σ S : Perm D} (hS : Function.Involutive S)
    (hswitch : ∀ a, (σ * S).SameCycle a (S a)) {a b : D} (hab : σ.SameCycle a b) :
    (σ * S).SameCycle a b := by
  apply sameCycle_of_steps (σ := σ) (fun x => ?_) hab
  have hh := (hswitch x).apply_right
  simpa only [Perm.mul_apply, hS x] using hh

theorem label_eq_of_sameCycle {U : Type*} (σ : Perm D) (label : D → U)
    (hlabel : ∀ d, label (σ d) = label d) {a b : D} (hab : σ.SameCycle a b) : label a = label b := by
  obtain ⟨n, rfl⟩ := hab.exists_nat_pow_eq
  clear hab
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, hlabel]
    exact ih

end
end Erdos73
