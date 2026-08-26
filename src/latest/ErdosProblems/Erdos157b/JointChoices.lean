import ErdosProblems.Erdos157b.ConditionalDensity
import ErdosProblems.Erdos157.UniformProducts
import Mathlib.Data.Fin.Tuple.Basic

/-! The finite marginal needed for choosing all masks and all labels in one product space. -/

namespace Erdos157.Binary

open Elementary

theorem finiteDensity_prod_fst {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (p : A → Prop) : finiteDensity (fun x : A × B => p x.1) = finiteDensity p := by
  let e : {x : A × B // p x.1} ≃ {a : A // p a} × B :=
    { toFun := fun x => (⟨x.1.1, x.2⟩, x.1.2)
      invFun := fun x => ⟨(x.1.1, x.2), x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hb : (Nat.card B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.card_pos (α := B)))
  unfold finiteDensity
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_right _ _ hb

def pairedPrefixEquiv (A B : ℕ → Type*) (k : ℕ) :
    (∀ i : Fin (k + 1), A i × B i) ≃
      (((∀ i : Fin k, A i) × B k) × (A k × (∀ i : Fin k, B i))) where
  toFun x := ((fun i => (x i.castSucc).1, (x (Fin.last k)).2),
    ((x (Fin.last k)).1, fun i => (x i.castSucc).2))
  invFun x := Fin.snoc (fun i => (x.1.1 i, x.2.2 i)) (x.2.1, x.1.2)
  left_inv x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv x := by
    rcases x with ⟨⟨a, b⟩, c, d⟩
    simp

theorem pairedPrefix_density (A B : ℕ → Type*)
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Nonempty (A i)] [∀ i, Nonempty (B i)]
    (k : ℕ) (p : ((∀ i : Fin k, A i) × B k) → Prop) :
    finiteDensity (fun x : ∀ i : Fin (k + 1), A i × B i =>
      p (fun i => (x i.castSucc).1, (x (Fin.last k)).2)) = finiteDensity p := by
  have h := finiteDensity_equiv (pairedPrefixEquiv A B k) (fun x => p x.1)
  exact h.trans (finiteDensity_prod_fst p)

theorem joint_cylinder_density (A B : ℕ → Type*)
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Nonempty (A i)] [∀ i, Nonempty (B i)]
    [∀ i, MeasurableSpace (A i × B i)] [∀ i, MeasurableSingletonClass (A i × B i)]
    (k : ℕ) (p : ((∀ i : Fin k, A i) × B k) → Prop) :
    (UniformProducts.productMeasure (fun i => A i × B i)).real
      {x | p (fun i : Fin k => (x i).1, (x k).2)} = finiteDensity p := by
  have h := UniformProducts.prefix_density (fun i => A i × B i) (k + 1)
    (fun x => p (fun i : Fin k => (x i.castSucc).1, (x (Fin.last k)).2))
  exact h.trans (pairedPrefix_density A B k p)

end Erdos157.Binary
