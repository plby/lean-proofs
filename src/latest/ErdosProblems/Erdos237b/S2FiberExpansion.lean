import ErdosProblems.Erdos237b.S2SquareComparison

/-!
# Positive finite expansion of the S2 fiber diagonal

Expanding the square makes two inner coordinates explicit. This permits
lower bounds from any injectively indexed collection of compatible triples.
-/

namespace Erdos237b

open Finset BoundedGaps.Maynard
open scoped BigOperators

noncomputable def s2FiberTripleSupport (H : Finset ℕ) (R W : ℕ) (m : H) :
    Finset ((H → ℕ) × (H → ℕ) × (H → ℕ)) := by
  classical
  let S := maynardDivisorTupleSupport H R W
  exact ((S.filter (fun r => r m = 1)) ×ˢ (S ×ˢ S)).filter
    (fun t => IsMaynardS2MainFace m t.1 t.2.1 ∧ IsMaynardS2MainFace m t.1 t.2.2)

noncomputable def s2FiberTripleTerm (H : Finset ℕ) (y : (H → ℕ) → ℝ) (m : H)
    (t : (H → ℕ) × (H → ℕ) × (H → ℕ)) : ℝ :=
  (y t.2.1 / Nat.totient (t.2.1 m)) * (y t.2.2 / Nat.totient (t.2.2 m)) /
    ∏ h : H, (maynardS2G (t.1 h) : ℝ)

theorem s2FiberTripleTerm_nonneg {H : Finset ℕ} {y : (H → ℕ) → ℝ}
    (hy : ∀ r, 0 ≤ y r) (m : H) (t : (H → ℕ) × (H → ℕ) × (H → ℕ)) :
    0 ≤ s2FiberTripleTerm H y m t := by
  unfold s2FiberTripleTerm
  exact div_nonneg (mul_nonneg (div_nonneg (hy _) (by positivity))
    (div_nonneg (hy _) (by positivity))) (by positivity)

theorem s2FiberSquareDiagonal_eq_tripleSum (H : Finset ℕ) (R W : ℕ)
    (y : (H → ℕ) → ℝ) (m : H) :
    s2FiberSquareDiagonal H R W y m =
      ∑ t ∈ s2FiberTripleSupport H R W m, s2FiberTripleTerm H y m t := by
  classical
  unfold s2FiberTripleSupport
  dsimp only
  rw [sum_filter, sum_product]
  unfold s2FiberSquareDiagonal
  apply sum_congr rfl
  intro r _
  rw [sum_product]
  unfold maynardS2CoordinateFiberSum s2FiberTripleTerm
  simp only [pow_two, sum_mul, mul_sum, sum_div]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  split_ifs <;> simp_all
  ring

theorem sum_le_s2FiberSquareDiagonal {α : Type*} {H : Finset ℕ} {R W : ℕ}
    {y : (H → ℕ) → ℝ} (hy : ∀ r, 0 ≤ y r) (m : H)
    (T : Finset α) (f : α → ℝ)
    (i : α → (H → ℕ) × (H → ℕ) × (H → ℕ))
    (hmem : ∀ z ∈ T, i z ∈ s2FiberTripleSupport H R W m)
    (hinj : Set.InjOn i T) (hterm : ∀ z ∈ T, f z ≤ s2FiberTripleTerm H y m (i z)) :
    (∑ z ∈ T, f z) ≤ s2FiberSquareDiagonal H R W y m := by
  classical
  rw [s2FiberSquareDiagonal_eq_tripleSum]
  calc
    _ ≤ ∑ z ∈ T, s2FiberTripleTerm H y m (i z) := sum_le_sum hterm
    _ = ∑ t ∈ T.image i, s2FiberTripleTerm H y m t := (sum_image hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
      (fun t ht => by obtain ⟨z, hz, rfl⟩ := mem_image.mp ht; exact hmem z hz)
      (fun t _ _ => s2FiberTripleTerm_nonneg hy m t)

theorem maynardS2G_le_totient {n : ℕ} (hn : Squarefree n) :
    maynardS2G n ≤ Nat.totient n := by
  rw [← sum_maynardS2G_divisors_eq_totient hn]
  exact single_le_sum (fun _ _ => Nat.zero_le _) (Nat.mem_divisors.mpr ⟨dvd_rfl, hn.ne_zero⟩)

end Erdos237b
