import ErdosProblems.Erdos547.StructuralAssembly
import ErdosProblems.Erdos547.BlowupAllocation

/-!
# Rational scaling of the integer-budget structure theorem

The blow-up makes every budget integral. Averaging the allocations back down
preserves the skews and all the anchored-pair inequalities.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem exists_anchored_totals_scaled_nat (w : EdgeWeights G) (c : V)
    (a₁ a₂ b₁ b₂ p q : ℕ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hp : 0 < p) (hq : 0 < q)
    (hlarge : (p : ℝ) / q * ((a₁ : ℝ) + a₂ + b₁ + b₂) ≤ w.degree c)
    (hdeg : ∀ v, (p : ℝ) / q * ((a₁ : ℝ) + a₂ + b₁ + b₂) / 2 ≤ w.degree v) :
    HasAnchoredTotals w ((a₂ : ℝ) / a₁) ((b₂ : ℝ) / b₁)
      ((p : ℝ) / q * ((a₁ : ℝ) + a₂)) ((p : ℝ) / q * ((b₁ : ℝ) + b₂)) := by
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  let c' : V × Fin q := (c, ⟨0, hq⟩)
  have hlarge' : ((p * a₁ : ℕ) : ℝ) + (p * a₂ : ℕ) + (p * b₁ : ℕ) + (p * b₂ : ℕ) ≤
      (Blowup.weights (I := Fin q) w).degree c' := by
    rw [Blowup.degree_weights, Fintype.card_fin]
    calc
      _ = (q : ℝ) * ((p : ℝ) / q * ((a₁ : ℝ) + a₂ + b₁ + b₂)) := by
        push_cast
        field_simp [hq'.ne']
      _ ≤ (q : ℝ) * w.degree c := mul_le_mul_of_nonneg_left hlarge hq'.le
  have hdeg' (v : V × Fin q) :
      (((p * a₁ : ℕ) : ℝ) + (p * a₂ : ℕ) + (p * b₁ : ℕ) + (p * b₂ : ℕ)) / 2 ≤
        (Blowup.weights (I := Fin q) w).degree v := by
    rw [Blowup.degree_weights, Fintype.card_fin]
    calc
      _ = (q : ℝ) * ((p : ℝ) / q * ((a₁ : ℝ) + a₂ + b₁ + b₂) / 2) := by
        push_cast
        field_simp [hq'.ne']
      _ ≤ (q : ℝ) * w.degree v.1 := mul_le_mul_of_nonneg_left (hdeg v.1) hq'.le
  have h := exists_anchored_totals_of_degree (Blowup.weights (I := Fin q) w) c'
    (p * a₁) (p * a₂) (p * b₁) (p * b₂)
    (Nat.mul_pos hp ha₁) (Nat.mul_pos hp ha₂) (Nat.mul_pos hp hb₁) (Nat.mul_pos hp hb₂)
    hlarge' hdeg'
  have hrat (x y : ℕ) : ((p * x : ℕ) : ℝ) / (p * y : ℕ) = (x : ℝ) / y := by
    rw [Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ hp'.ne']
  rw [hrat a₂ a₁, hrat b₂ b₁] at h
  have hc := Blowup.collapse_anchoredTotals h (by simpa only [Fintype.card_fin] using hq)
  simp only [Fintype.card_fin, Nat.cast_mul] at hc
  convert hc using 1 <;> ring

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_anchored_totals_scaled_nat
