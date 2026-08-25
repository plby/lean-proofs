import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting a finite family modulo associates
-/

namespace Bernays

theorem natCard_associate_fiber_le {R X Y : Type*} [CommMonoid R] [Finite Rˣ]
    (z : X → R) (hz : Function.Injective z) (f : X → Y)
    (hassoc : ∀ x y, f x = f y → Associated (z x) (z y)) (y : Y) :
    Nat.card {x : X // f x = y} ≤ Nat.card Rˣ := by
  classical
  by_cases hne : Nonempty {x : X // f x = y}
  · obtain ⟨x₀⟩ := hne
    have hex (x : {x : X // f x = y}) : ∃ u : Rˣ, z x.1 * u = z x₀.1 :=
      hassoc x.1 x₀.1 (x.2.trans x₀.2.symm)
    let u : {x : X // f x = y} → Rˣ := fun x => (hex x).choose
    have hu (x : {x : X // f x = y}) : z x.1 * u x = z x₀.1 := (hex x).choose_spec
    apply Nat.card_le_card_of_injective u
    intro x w h
    apply Subtype.ext
    apply hz
    apply (u x).isUnit.mul_right_cancel
    rw [hu x, h, hu w]
  · haveI : IsEmpty {x : X // f x = y} := not_nonempty_iff.mp hne
    simp

theorem natCard_le_units_mul_of_associate_fibers {R X Y : Type*}
    [CommMonoid R] [Finite Rˣ] [Finite X] [Finite Y]
    (z : X → R) (hz : Function.Injective z) (f : X → Y)
    (hassoc : ∀ x y, f x = f y → Associated (z x) (z y)) :
    Nat.card X ≤ Nat.card Rˣ * Nat.card Y := by
  classical
  letI := Fintype.ofFinite Y
  calc
    Nat.card X = ∑ y : Y, Nat.card {x : X // f x = y} := by
      rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
    _ ≤ ∑ _y : Y, Nat.card Rˣ := Finset.sum_le_sum fun y _ => natCard_associate_fiber_le z hz f hassoc y
    _ = Nat.card Rˣ * Nat.card Y := by simp [Nat.card_eq_fintype_card, Nat.mul_comm]

theorem natCard_associate_fiber_eq {R X Y : Type*} [CommMonoidWithZero R]
    [IsCancelMulZero R] [Finite Rˣ] [Finite X]
    (z : X → R) (hz : Function.Injective z) (hz₀ : ∀ x, z x ≠ 0)
    (f : X → Y) (hassoc : ∀ x y, f x = f y → Associated (z x) (z y))
    (hstable : ∀ x : X, ∀ u : Rˣ, ∃ w : X, z w = z x * u ∧ f w = f x)
    (y : Y) (hy : ∃ x, f x = y) : Nat.card {x : X // f x = y} = Nat.card Rˣ := by
  classical
  apply Nat.le_antisymm (natCard_associate_fiber_le z hz f hassoc y)
  obtain ⟨x₀, hx₀⟩ := hy
  let w : Rˣ → X := fun u => (hstable x₀ u).choose
  have hw (u : Rˣ) : z (w u) = z x₀ * u ∧ f (w u) = f x₀ := (hstable x₀ u).choose_spec
  let e : Rˣ → {x : X // f x = y} := fun u => ⟨w u, (hw u).2.trans hx₀⟩
  apply Nat.card_le_card_of_injective e
  intro u v huv
  apply Units.ext
  have heq : z (w u) = z (w v) := congrArg (fun t : {x : X // f x = y} => z t.1) huv
  rw [(hw u).1, (hw v).1] at heq
  exact mul_left_cancel₀ (hz₀ x₀) heq

theorem natCard_eq_units_mul_of_associate_fibers {R X Y : Type*}
    [CommMonoidWithZero R] [IsCancelMulZero R] [Finite Rˣ] [Finite X] [Finite Y]
    (z : X → R) (hz : Function.Injective z) (hz₀ : ∀ x, z x ≠ 0)
    (f : X → Y) (hf : Function.Surjective f)
    (hassoc : ∀ x y, f x = f y → Associated (z x) (z y))
    (hstable : ∀ x : X, ∀ u : Rˣ, ∃ w : X, z w = z x * u ∧ f w = f x) :
    Nat.card X = Nat.card Rˣ * Nat.card Y := by
  classical
  letI := Fintype.ofFinite Y
  calc
    Nat.card X = ∑ y : Y, Nat.card {x : X // f x = y} := by
      rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
    _ = ∑ _y : Y, Nat.card Rˣ := Finset.sum_congr rfl fun y _ =>
      natCard_associate_fiber_eq z hz hz₀ f hassoc hstable y (hf y)
    _ = Nat.card Rˣ * Nat.card Y := by simp [Nat.card_eq_fintype_card, Nat.mul_comm]

end Bernays
