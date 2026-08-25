import ErdosProblems.Erdos1141.BurgessCompositeCorrelation
import ErdosProblems.Erdos1141.BurgessTupleBound
import ErdosProblems.Erdos1141.BurgessAmplifier

/-!
# The complete Burgess moment for squarefree quadratic characters

This bound is valid at every moment order. Its only arithmetic loss beyond
the prime-field square-root estimate is a fixed power of the divisor count.
-/

namespace Pollack17.Burgess

open scoped BigOperators

theorem productChar_prod (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {ι : Type*} [Fintype ι] (f : ι → ZMod (primeModulus s)) :
    productChar s hs (∏ i, f i) = ∏ i, productChar s hs (f i) := by
  classical
  simp only [productChar, localChar, qchar, map_prod, Finset.prod_apply, Int.cast_prod]
  rw [Finset.prod_comm]

theorem productChar_moment_expansion (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] (V n : ℕ) :
    (∑ x : ZMod (primeModulus s), naturalShiftSum (productChar s hs) V x ^ n) =
      ∑ v : Fin n → (Finset.Icc 1 V), ∑ x : ZMod (primeModulus s),
        productChar s hs (∏ i : Fin n, (x + (v i : ℕ))) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [naturalShiftSum, ← Finset.sum_attach, Finset.attach_eq_univ, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro v _
  exact (productChar_prod s hs (fun i : Fin n => x + (v i : ℕ))).symm

noncomputable def gcdKernel (q a b : ℕ) : ℝ :=
  if b ≠ a then (q.gcd (Nat.dist a b) : ℝ) else 0

theorem gcdKernel_nonneg (q a b : ℕ) : 0 ≤ gcdKernel q a b := by
  unfold gcdKernel
  split_ifs <;> positivity

theorem sum_gcdKernel_le {q : ℕ} (hq : q ≠ 0) (V : ℕ) (a : Finset.Icc 1 V) :
    (∑ b : Finset.Icc 1 V, gcdKernel q a b) ≤ 2 * V * q.divisors.card := by
  rw [Finset.sum_coe_sort (Finset.Icc 1 V) (fun b : ℕ => gcdKernel q a b)]
  simp only [gcdKernel, ← Finset.sum_filter, Finset.filter_ne']
  exact_mod_cast sum_gcd_dist_erase_le hq (Finset.mem_Icc.mp a.property).2

theorem productChar_even_moment_le (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] (V r : ℕ) :
    (∑ x : ZMod (primeModulus s), naturalShiftSum (productChar s hs) V x ^ (2 * r)) ≤
      (V : ℝ) ^ r * (r : ℝ) ^ (2 * r) * primeModulus s +
        ((Stepanov.simpleRootConstant (2 * r) : ℝ) ^ s.card * Real.sqrt (primeModulus s)) *
          (2 * r : ℕ) * V * (2 * V * ((primeModulus s).divisors.card : ℝ)) ^ (2 * r - 1) := by
  classical
  let α := Finset.Icc 1 V
  let q := primeModulus s
  let corr : (Fin (2 * r) → α) → ℝ := fun v =>
    ∑ x : ZMod q, productChar s hs (∏ i : Fin (2 * r), (x + (v i : ℕ)))
  let w : α → α → ℝ := fun a b => gcdKernel q a b
  let C : ℝ := (Stepanov.simpleRootConstant (2 * r) : ℝ) ^ s.card * Real.sqrt q
  have hw : ∀ a b : α, 0 ≤ w a b := fun a b => gcdKernel_nonneg q a b
  have hrow : ∀ a : α, (∑ b : α, w a b) ≤ 2 * V * (q.divisors.card : ℝ) :=
    fun a => sum_gcdKernel_le (NeZero.ne q) V a
  have htrivial (v : Fin (2 * r) → α) : corr v ≤ q := by
    calc
      _ ≤ ∑ _x : ZMod q, (1 : ℝ) := Finset.sum_le_sum fun x _ =>
        (le_abs_self _).trans (abs_productChar_le_one s hs _)
      _ = _ := by simp
  have hsingle (v : Fin (2 * r) → α) (i : Fin (2 * r))
      (hi : ∀ j, j ≠ i → v j ≠ v i) : corr v ≤ C * starWeight w v i := by
    have hbound := product_correlation_le_gcd s hs (fun j => (v j : ℕ)) i
    have hwprod : starWeight w v i =
        ∏ j ∈ Finset.univ.erase i, (q.gcd (Nat.dist (v i) (v j)) : ℝ) := by
      rw [starWeight_eq_prod_erase]
      apply Finset.prod_congr rfl
      intro j hj
      have hne : (v j : ℕ) ≠ v i := fun h => hi j (Finset.mem_erase.mp hj).1 (Subtype.ext h)
      exact if_pos hne
    rw [hwprod]
    exact (le_abs_self (corr v)).trans hbound
  rw [productChar_moment_expansion]
  have h := sum_tuple_correlations_le r corr w hw (Nat.cast_nonneg q)
    (by dsimp [C]; positivity) hrow htrivial hsingle
  simpa only [α, corr, C, q, Fintype.card_coe, Nat.card_Icc, Nat.add_sub_cancel] using h

end Pollack17.Burgess
