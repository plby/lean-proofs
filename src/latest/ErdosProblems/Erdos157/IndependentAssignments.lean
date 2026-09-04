import ErdosProblems.Erdos157.FiniteDensity
import Mathlib.Data.ZMod.Basic

/-! Disjoint prescribed assignments are independent under finite uniform choices. -/

namespace Erdos157.Elementary

namespace UniformTrials

theorem finiteDensity_missed_points_le_exp {A G : Type*} [AddCommGroup A] [AddCommGroup G]
    [Fintype A] [Fintype G] {n : ℕ} (f : A →+ (Fin n → G))
    (hf : Function.Surjective f) (w : Fin n → G) :
    finiteDensity (fun a => ∀ j, f a j ≠ w j) ≤ Real.exp (-(n : ℝ) / Fintype.card G) := by
  classical
  obtain ⟨a₀, ha₀⟩ := hf w
  let e : A ≃ A :=
    { toFun := fun a => a + a₀
      invFun := fun a => a - a₀
      left_inv := fun _ => add_sub_cancel_right _ _
      right_inv := fun _ => sub_add_cancel _ _ }
  have hshift : finiteDensity (fun a => ∀ j, f a j ≠ w j) =
      finiteDensity (fun a => ∀ j, f a j ≠ 0) := by
    rw [← finiteDensity_equiv e]
    apply finiteDensity_congr
    intro a
    change (∀ j, f (a + a₀) j ≠ w j) ↔ _
    simp only [map_add, Pi.add_apply, ha₀]
    apply forall_congr'
    intro j
    apply not_congr
    constructor
    · intro h
      exact add_right_cancel (h.trans (zero_add (w j)).symm)
    · intro h
      rw [h, zero_add]
  have hz : finiteDensity (fun g : G => g = 0) = 1 / Fintype.card G := by
    have h := finiteDensity_finset ({0} : Finset G)
    simpa only [Finset.mem_singleton, Finset.card_singleton, Nat.cast_one] using h
  rw [hshift]
  have hb := finiteDensity_missed_le_exp f hf (fun g => g = 0)
  rw [hz] at hb
  convert hb using 1 <;> ring_nf

def assignmentTrials {I J G : Type*} [AddCommGroup G] {n : ℕ}
    (f : Fin n → J → I) : (I → G) →+ (Fin n → J → G) where
  toFun a j s := a (f j s)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem assignmentTrials_surjective {I J G : Type*} [AddCommGroup G] {n : ℕ}
    (f : Fin n → J → I) (hf : Function.Injective (Function.uncurry f)) :
    Function.Surjective (assignmentTrials (G := G) f) := by
  classical
  intro w
  refine ⟨Function.extend (Function.uncurry f) (Function.uncurry w) (fun _ => 0), ?_⟩
  funext j s
  exact hf.extend_apply (Function.uncurry w) (fun _ => 0) (j, s)

end UniformTrials

theorem finiteDensity_disjoint_assignments {I J X : Type*}
    [Fintype I] [Fintype J] [Fintype X] [Nonempty X] {n : ℕ}
    (f : Fin n → J → I) (hf : Function.Injective (Function.uncurry f)) (v : Fin n → J → X) :
    finiteDensity (fun a : I → X => ∀ j, ¬ ∀ s, a (f j s) = v j s) ≤
      Real.exp (-(n : ℝ) / (Fintype.card X : ℝ) ^ Fintype.card J) := by
  classical
  let D := Fintype.card X
  let : NeZero D := ⟨(Fintype.card_pos (α := X)).ne'⟩
  let e : X ≃ ZMod D := (Fintype.equivFin X).trans (ZMod.finEquiv D).toEquiv
  let E : (I → ZMod D) ≃ (I → X) := Equiv.piCongrRight (fun _ => e.symm)
  rw [← finiteDensity_equiv E]
  have heq : finiteDensity (fun a : I → ZMod D => ∀ j, ¬ ∀ s, E a (f j s) = v j s) =
      finiteDensity (fun a : I → ZMod D => ∀ j,
        UniformTrials.assignmentTrials f a j ≠ (fun s => e (v j s))) := by
    apply finiteDensity_congr
    intro a
    apply forall_congr'
    intro j
    apply not_congr
    rw [funext_iff]
    apply forall_congr'
    intro s
    change e.symm (a (f j s)) = v j s ↔ a (f j s) = e (v j s)
    exact e.symm_apply_eq
  rw [heq]
  have hb := UniformTrials.finiteDensity_missed_points_le_exp
    (UniformTrials.assignmentTrials (G := ZMod D) f)
    (UniformTrials.assignmentTrials_surjective f hf) (fun j s => e (v j s))
  simpa only [Fintype.card_fun, ZMod.card, Nat.cast_pow] using hb

end Erdos157.Elementary
