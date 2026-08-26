/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedSourcePrimeCount

/-!
# Product support of the reduced source coefficient and its actual modulus

Extending by one at the pin preserves the divisor products. The source
simplex support therefore bounds the actual flat lcm independently of
the coordinate cutoff.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem prod_extendPinnedDivisorTuple {K : ℕ} (h : Fin K) (d : PinnedShiftIndex h → ℕ) :
    (∏ i : Fin K, extendPinnedDivisorTuple h d i) = ∏ i, d i := by
  have hp : (∏ i : Fin K, extendPinnedDivisorTuple h d i) =
      ∏ i : PinnedShiftIndex h, extendPinnedDivisorTuple h d i.val := by
    simpa only [extendPinnedDivisorTuple_at_pin, one_mul] using!
      Fintype.prod_eq_mul_prod_subtype_ne (extendPinnedDivisorTuple h d) h
  rw [hp]
  apply Finset.prod_congr rfl
  intro i hi
  exact extendPinnedDivisorTuple_at_other h d i

theorem pinnedSourceSelbergCoefficient_nonzero_squarefree
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (LD LE : ℝ) (d e : PinnedShiftIndex h → ℕ)
    (hne : pinnedSourceSelbergCoefficient S F G h LD LE d e ≠ 0) :
    ∀ i, Squarefree (d i) ∧ Squarefree (e i) := by
  have hfull := sourceAnalyticSelbergCoefficient_extend_ne_zero S F G h LD LE d e hne
  have hsq := sourceAnalyticSelbergCoefficient_nonzero_squarefree S F G LD LE _ _ hfull
  intro i
  simpa only [extendPinnedDivisorTuple_at_other] using hsq i.val

theorem pinnedSourceSelbergCoefficient_nonzero_product_bounds
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) {LD LE A : ℝ} (hLD : 0 < LD) (hLE : 0 < LE)
    (hFsupport : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ A)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (d e : PinnedShiftIndex h → ℕ)
    (hne : pinnedSourceSelbergCoefficient S F G h LD LE d e ≠ 0) :
    (∏ i, d i) ≤ ⌈Real.exp (A * LD)⌉₊ ∧
      (∏ i, e i) ≤ ⌈Real.exp ((K : ℝ) * LE)⌉₊ := by
  have hfull := sourceAnalyticSelbergCoefficient_extend_ne_zero S F G h LD LE d e hne
  have hsq := sourceAnalyticSelbergCoefficient_nonzero_squarefree S F G LD LE _ _ hfull
  have hbounds := sourceAnalyticSelbergCoefficient_nonzero_product_bounds S F G hLD hLE
    hFsupport hGsupport (extendPinnedDivisorTuple h d) (extendPinnedDivisorTuple h e)
    (fun i ↦ (hsq i).1.ne_zero.bot_lt) (fun i ↦ (hsq i).2.ne_zero.bot_lt) hfull
  simpa only [prod_extendPinnedDivisorTuple, Fintype.card_fin] using hbounds

theorem pinnedFlatDivisorModulus_le_four_products
    {K : ℕ} (h : Fin K)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)
    (hpos : ∀ i b, 0 < d i b) :
    pinnedFlatDivisorModulus h d ≤
      ((∏ i, d (.inl i) false) * (∏ i, d (.inr i) false)) *
        ((∏ i, d (.inl i) true) * (∏ i, d (.inr i) true)) := by
  have hle : pinnedFlatDivisorModulus h d ≤
      ∏ ib : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) × Bool, d ib.1 ib.2 :=
    Nat.le_of_dvd (Finset.prod_pos fun ib hib ↦ hpos ib.1 ib.2)
      (Finset.lcm_dvd_prod Finset.univ
        (fun ib : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) × Bool ↦ d ib.1 ib.2))
  apply hle.trans_eq
  simp only [Fintype.prod_prod_type, Fintype.prod_bool, Fintype.prod_sum_type,
    Finset.prod_mul_distrib]
  ring

theorem pinnedFlatDivisorModulus_le_source_product_radii
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) {LD LE A : ℝ} (hLD : 0 < LD) (hLE : 0 < LE)
    (hFsupport : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ A)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)
    (hne : pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i false) *
      pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i true) ≠ 0) :
    pinnedFlatDivisorModulus h d ≤
      (⌈Real.exp (A * LD)⌉₊ * ⌈Real.exp ((K : ℝ) * LE)⌉₊) ^ 2 := by
  have hn (c : Bool) :
      pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i c) ≠ 0 := by
    cases c
    · exact (mul_ne_zero_iff.mp hne).1
    · exact (mul_ne_zero_iff.mp hne).2
  have hsq (c : Bool) := pinnedSourceSelbergCoefficient_nonzero_squarefree S F G h LD LE
    (fun i ↦ d (.inl i) c) (fun i ↦ d (.inr i) c) (hn c)
  have hpos (i : PinnedShiftIndex h ⊕ PinnedShiftIndex h) (c : Bool) : 0 < d i c := by
    cases i with
    | inl i => exact (hsq c i).1.ne_zero.bot_lt
    | inr i => exact (hsq c i).2.ne_zero.bot_lt
  have hbounds (c : Bool) := pinnedSourceSelbergCoefficient_nonzero_product_bounds S F G h
    hLD hLE hFsupport hGsupport (fun i ↦ d (.inl i) c) (fun i ↦ d (.inr i) c) (hn c)
  apply (pinnedFlatDivisorModulus_le_four_products h d hpos).trans
  rw [pow_two]
  exact Nat.mul_le_mul
    (Nat.mul_le_mul (hbounds false).1 (hbounds false).2)
    (Nat.mul_le_mul (hbounds true).1 (hbounds true).2)

theorem exists_uniform_pinnedSourceFlatCoefficient_bound
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFcont : ∀ j i, Continuous (F j i))
    (hGcompact : HasCompactSupport G) (hGcont : Continuous G) :
    ∃ C ≥ 0, ∀ (h : Fin K) LD LE (v : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → ℕ),
      ‖pinnedSourceFlatCoefficient S F G h LD LE v‖ ≤ C := by
  obtain ⟨C, hC, hc⟩ := exists_uniform_sourceAnalyticSelbergCoefficient_bound S F G
    hFcompact hFcont hGcompact hGcont
  refine ⟨C, hC, ?_⟩
  intro h LD LE v
  rw [pinnedSourceFlatCoefficient, ← sourceAnalyticSelbergCoefficient_extend_eq_pinned,
    Complex.norm_real, Real.norm_eq_abs]
  exact hc LD LE _ _

end

end Erdos4b
