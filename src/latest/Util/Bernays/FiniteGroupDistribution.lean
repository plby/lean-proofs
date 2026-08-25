import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Util.Bernays.FiniteVariance

/-!
# Finite-group distribution from character cancellation
-/

open Filter Topology
open scoped Classical

namespace Bernays

theorem character_fiber_indicator {G : Type*} [CommGroup G] [Fintype G] (g h : G) :
    (if g = h then (1 : ℂ) else 0) =
      (∑ ψ : AddChar (Additive G) ℂ, ψ (Additive.ofMul g) / ψ (Additive.ofMul h)) /
        (Fintype.card G : ℂ) := by
  have hsum := AddChar.sum_apply_eq_ite (Additive.ofMul (g / h))
  simp only [ofMul_div, AddChar.map_sub_eq_div, sub_eq_zero, Additive.ofMul.injective.eq_iff] at hsum
  rw [Fintype.card_congr (Additive.ofMul : G ≃ Additive G).symm] at hsum
  rw [hsum]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  by_cases hgh : g = h
  · simp only [if_pos hgh]
    exact (div_self hcard).symm
  · simp only [if_neg hgh, zero_div]

theorem fiber_card_eq_character_sum {α G : Type*} [CommGroup G] [Fintype G]
    (A : Finset α) (f : α → G) (g : G) :
    (eventCount A (fun x => f x = g) : ℂ) =
      (∑ ψ : AddChar (Additive G) ℂ,
        (∑ x ∈ A, ψ (Additive.ofMul (f x))) / ψ (Additive.ofMul g)) / (Fintype.card G : ℂ) := by
  have hcard : (eventCount A (fun x => f x = g) : ℂ) =
      ∑ x ∈ A, if f x = g then (1 : ℂ) else 0 := by
    unfold eventCount
    convert (Finset.sum_boole (R := ℂ) (fun x => f x = g) A).symm using 1 <;> congr
  rw [hcard]
  simp_rw [character_fiber_indicator]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl (fun _ _ => (Finset.sum_div _ _ _).symm)

theorem fiber_card_limit_of_character_cancellation {α G : Type*} [CommGroup G] [Fintype G]
    (A : ℕ → Finset α) (f : α → G) (s : ℕ → ℝ) {C : ℝ}
    (hA : Tendsto (fun N => ((A N).card : ℝ) / s N) atTop (𝓝 C))
    (hχ : ∀ ψ : AddChar (Additive G) ℂ, ψ ≠ 0 →
      Tendsto (fun N => (∑ x ∈ A N, ψ (Additive.ofMul (f x))) / (s N : ℂ)) atTop (𝓝 0))
    (g : G) :
    Tendsto (fun N => (eventCount (A N) (fun x => f x = g) : ℝ) / s N)
      atTop (𝓝 (C / Fintype.card G)) := by
  have htotal : Tendsto (fun N => ((A N).card : ℂ) / (s N : ℂ)) atTop (𝓝 (C : ℂ)) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using hA.ofReal
  have hterm (ψ : AddChar (Additive G) ℂ) :
      Tendsto (fun N => ((∑ x ∈ A N, ψ (Additive.ofMul (f x))) / ψ (Additive.ofMul g)) / (s N : ℂ))
        atTop (𝓝 (if ψ = 0 then (C : ℂ) else 0)) := by
    by_cases hψ : ψ = 0
    · subst ψ
      simpa only [AddChar.zero_apply, Finset.sum_const, nsmul_eq_mul, mul_one, div_one, if_true] using htotal
    · have h := (hχ ψ hψ).div_const (ψ (Additive.ofMul g))
      simp only [zero_div] at h
      rw [if_neg hψ]
      convert h using 1
      ext N
      ring
  have h := (tendsto_finsetSum Finset.univ (fun ψ _ => hterm ψ)).div_const (Fintype.card G : ℂ)
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  have hfiber : Tendsto (fun N => (eventCount (A N) (fun x => f x = g) : ℂ) / (s N : ℂ))
      atTop (𝓝 ((C : ℂ) / (Fintype.card G : ℂ))) := by
    convert h using 1
    ext N
    rw [fiber_card_eq_character_sum, ← Finset.sum_div]
    ring
  have hre := (Complex.continuous_re.tendsto _).comp hfiber
  simpa only [Function.comp_def, ← Complex.ofReal_natCast, Complex.div_ofReal_re,
    Complex.ofReal_re] using hre

end Bernays
