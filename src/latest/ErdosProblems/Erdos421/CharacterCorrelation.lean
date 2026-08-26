import ErdosProblems.Erdos421.CharacterScaling

/-! # Finite Fourier correlations between different tuple spaces -/

namespace Erdos421

open scoped ComplexConjugate

variable {q k : ℕ} [NeZero q]

theorem vectorCharacterSum_correlation {X Y : Type*} (S : Finset X) (T : Finset Y)
    (f : X → Fin k → ZMod q) (g : Y → Fin k → ZMod q) :
    (∑ a : Fin k → ZMod q, vectorCharacterSum S f a * conj (vectorCharacterSum T g a)) =
      (q : ℂ) ^ k * (((S ×ˢ T).filter (fun p ↦ f p.1 = g p.2)).card : ℂ) := by
  classical
  have hexpand (a : Fin k → ZMod q) :
      vectorCharacterSum S f a * conj (vectorCharacterSum T g a) =
        ∑ x ∈ S, ∑ y ∈ T, vectorCharacter a (f x - g y) := by
    simp only [vectorCharacterSum, map_sum, Finset.sum_mul, Finset.mul_sum,
      vectorCharacter_mul_conj]
    exact Finset.sum_comm
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  have hswap (x : X) : (∑ a : Fin k → ZMod q, ∑ y ∈ T, vectorCharacter a (f x - g y)) =
      ∑ y ∈ T, ∑ a : Fin k → ZMod q, vectorCharacter a (f x - g y) := Finset.sum_comm
  simp_rw [hswap, sum_vectorCharacter, sub_eq_zero]
  rw [← Finset.sum_product (f := fun p : X × Y ↦ if f p.1 = g p.2 then (q : ℂ) ^ k else 0),
    ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem vectorCharacterSum_correlation_bound {X Y : Type*} (S : Finset X) (T : Finset Y)
    (f : X → Fin k → ZMod q) (g : Y → Fin k → ZMod q) :
    (q : ℝ) ^ k * (((S ×ˢ T).filter (fun p ↦ f p.1 = g p.2)).card : ℝ) ≤
      ∑ a : Fin k → ZMod q, ‖vectorCharacterSum S f a‖ * ‖vectorCharacterSum T g a‖ := by
  have hn := norm_sum_le (Finset.univ : Finset (Fin k → ZMod q))
    (fun a ↦ vectorCharacterSum S f a * conj (vectorCharacterSum T g a))
  rw [vectorCharacterSum_correlation] at hn
  simpa only [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_conj] using hn

theorem vectorCharacterSum_repeated_factor {X : Type*} [Fintype X]
    (f : X → Fin k → ZMod q) (n : ℕ) (a : Fin k → ZMod q) :
    vectorCharacterSum Finset.univ
        (fun x : (Fin n → X) × X ↦ (∑ i : Fin n, f (x.1 i)) + f x.2 + f x.2) a =
      vectorCharacterSum Finset.univ f a ^ n *
        vectorCharacterSum Finset.univ (fun x j ↦ (2 : ZMod q) * f x j) a := by
  classical
  rw [vectorCharacterSum_power]
  simp only [vectorCharacterSum, Fintype.sum_prod_type, vectorCharacter_add]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have he : (fun j ↦ (2 : ZMod q) * f y j) = f y + f y := by
    funext j
    exact two_mul _
  rw [he, vectorCharacter_add]
  ring

end Erdos421
