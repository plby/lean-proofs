import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Finite fiber counts and the elementary many-large-fibers inequality. -/

namespace Erdos157.Elementary.FiniteFiberCounts

variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable def fiberCard (f : A → B) (b : B) : ℕ := Nat.card {a // f a = b}

theorem sum_fiberCard (f : A → B) : ∑ b, fiberCard f b = Fintype.card A := by
  classical
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  simpa only [Fintype.card_sigma, fiberCard, Nat.card_eq_fintype_card] using h

theorem sum_fiberCard_real (f : A → B) : ∑ b, (fiberCard f b : ℝ) = Fintype.card A := by
  exact_mod_cast sum_fiberCard f

theorem card_le_of_fiber_lower (f : A → B) (L : ℝ)
    (hlower : ∀ b, L ≤ fiberCard f b) : (Fintype.card B : ℝ) * L ≤ Fintype.card A := by
  calc
    _ = ∑ _b : B, L := by simp
    _ ≤ ∑ b, (fiberCard f b : ℝ) := Finset.sum_le_sum (fun b _ => hlower b)
    _ = _ := sum_fiberCard_real f

theorem sum_le_threshold_add_cap (w : B → ℝ) (T U : ℝ) (hT : 0 ≤ T)
    (hcap : ∀ b, w b ≤ U) :
    ∑ b, w b ≤ (Fintype.card B : ℝ) * T + (Nat.card {b // T ≤ w b} : ℝ) * U := by
  classical
  let : Fintype {b // T ≤ w b} := Fintype.ofFinite _
  have hterm (b : B) : w b ≤ T + if T ≤ w b then U else 0 := by
    split_ifs with hb
    · linarith [hcap b]
    · have hlt := lt_of_not_ge hb
      linarith
  have hsum : (∑ b : B, if T ≤ w b then U else 0) = (Nat.card {b // T ≤ w b} : ℝ) * U := by
    rw [← Finset.sum_filter, Finset.sum_subtype (p := fun b => T ≤ w b) _ (by simp)]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
    infer_instance
  calc
    _ ≤ ∑ b, (T + if T ≤ w b then U else 0) := Finset.sum_le_sum (fun b _ => hterm b)
    _ = _ := by rw [Finset.sum_add_distrib, hsum]; simp

/-- If the small fibers account for at most half the mass, the remaining
mass forces many fibers above the threshold. -/
theorem many_large_fibers (f : A → B) (M T U : ℝ) (hT : 0 ≤ T) (hU : 0 < U)
    (hmass : M ≤ Fintype.card A) (hsmall : (Fintype.card B : ℝ) * T ≤ M / 2)
    (hcap : ∀ b, (fiberCard f b : ℝ) ≤ U) :
    M / (2 * U) ≤ Nat.card {b // T ≤ (fiberCard f b : ℝ)} := by
  have h := sum_le_threshold_add_cap (fun b => (fiberCard f b : ℝ)) T U hT hcap
  rw [sum_fiberCard_real] at h
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

theorem many_large_fibers_fraction (f : A → B) (ε U : ℝ) (hε : 0 ≤ ε) (hU : 0 < U)
    (hmass : 2 * (Fintype.card B : ℝ) * ε * U ≤ Fintype.card A)
    (hcap : ∀ b, (fiberCard f b : ℝ) ≤ U) :
    ε * (Fintype.card B : ℝ) ≤ Nat.card {b // ε * U ≤ (fiberCard f b : ℝ)} := by
  have h := many_large_fibers f (2 * (Fintype.card B : ℝ) * ε * U) (ε * U) U
    (by positivity) hU hmass (by nlinarith) hcap
  have heq : 2 * (Fintype.card B : ℝ) * ε * U / (2 * U) = ε * Fintype.card B := by
    field_simp
  rwa [heq] at h

def fiberRestriction {C : Type*} (f : A → B) (p : B → C) (u : C) :
    {a // p (f a) = u} → {b // p b = u} := fun a => ⟨f a.1, a.2⟩

def fiberRestrictionEquiv {C : Type*} (f : A → B) (p : B → C) (u : C)
    (b : {b // p b = u}) :
    {a : {a // p (f a) = u} // fiberRestriction f p u a = b} ≃ {a // f a = b.1} where
  toFun a := ⟨a.1.1, congrArg Subtype.val a.2⟩
  invFun a := ⟨⟨a.1, by rw [a.2]; exact b.2⟩, Subtype.ext a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fiberCard_restriction {C : Type*} (f : A → B) (p : B → C) (u : C)
    (b : {b // p b = u}) :
    fiberCard (fiberRestriction f p u) b = fiberCard f b.1 :=
  Nat.card_congr (fiberRestrictionEquiv f p u b)

end Erdos157.Elementary.FiniteFiberCounts
