import ErdosProblems.Erdos591.ArchitectBudget

/-!
# Sparse input sequences with finite label reserves

Any natural-valued bound can prescribe the number of unused pool members
between consecutive chosen inputs. The same gap puts the next input
above that bound. The construction uses increasing enumeration and does
not require a density hypothesis or a bound on the prescribed function.
-/

namespace Erdos591.Positive.Game

theorem exists_sparse_reserves {H : Set ℕ} (hH : H.Infinite) (B : ℕ → ℕ) (K : ℕ) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ (∀ n, f n ∈ H) ∧ (∀ n, K < f n) ∧
      (∀ n, B (f n) < f (n + 1)) ∧
      ∀ n, ∃ R : Finset ℕ, R.card = B (f n) ∧
        ∀ x ∈ R, x ∈ H ∧ f n < x ∧ x < f (n + 1) := by
  classical
  let e := Erdos590.Larson.enumOf H
  have he : StrictMono e := Erdos590.Larson.enumOf_strictMono hH
  have heSelf (n : ℕ) : n ≤ e n := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (he (Nat.lt_succ_self n)))
  let k : ℕ → ℕ := Nat.rec (K + 1) (fun _ r => r + B (e r) + 1)
  let f : ℕ → ℕ := fun n => e (k n)
  have hk (n : ℕ) : k (n + 1) = k n + B (f n) + 1 := rfl
  have hkmono : StrictMono k := strictMono_nat_of_lt_succ (fun n => by rw [hk]; omega)
  have hfmono : StrictMono f := he.comp hkmono
  refine ⟨f, hfmono, fun n => Erdos590.Larson.enumOf_mem hH (k n), ?_, ?_, ?_⟩
  · intro n
    have hkn := hkmono.monotone (Nat.zero_le n)
    have hkzero : k 0 = K + 1 := rfl
    have hself := heSelf (k n)
    change K < e (k n)
    omega
  · intro n
    have hgt : B (f n) < k (n + 1) := by rw [hk]; omega
    exact hgt.trans_le (heSelf _)
  · intro n
    let R := (Finset.range (B (f n))).image (fun j => e (k n + 1 + j))
    have hinj : Function.Injective (fun j => e (k n + 1 + j)) := by
      intro i j hij
      exact Nat.add_left_cancel (he.injective hij)
    refine ⟨R, by simp [R, Finset.card_image_of_injective _ hinj], ?_⟩
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hj' := Finset.mem_range.mp hj
    refine ⟨Erdos590.Larson.enumOf_mem hH _, he (by omega), ?_⟩
    apply he
    rw [hk]
    omega

#print axioms exists_sparse_reserves

end Erdos591.Positive.Game
