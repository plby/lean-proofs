import Util.Bernays.GoodIdealNormFibers
import Util.Bernays.InertPrimePowerIdeals

/-!
# Support and unit coefficient of the good ideal norm count
-/

namespace Bernays

theorem goodMaximal_norm_coprime {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ P : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      (P : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal →
      IsCoprime (P : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot.Coprime (discriminantLevel (b ^ 2 + 4 * d)) := by
  let := quadraticOrderIsDomain hD
  intro P hP hPF
  obtain ⟨q, _, hc, h | ⟨s, hs, ε, rfl⟩⟩ := goodMaximal_prime_description hD P hP hPF
  · rw [h.2.1]
    exact hc.pow_left 2
  · rw [s.ideal_cardQuot hD ε, hs]
    exact hc

theorem goodIdeal_norm_coprime {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot.Coprime (discriminantLevel (b ^ 2 + 4 * d)) := by
  let := quadraticOrderIsDomain hD
  intro I hIF
  obtain ⟨l, hl, hP⟩ := goodQuadraticIdeal_factorization hD I hIF
  rw [← hl]
  clear hl I hIF
  induction l with
  | nil => simp [Submodule.cardQuot_top]
  | cons P l ih =>
    rw [List.prod_cons, InvertibleIdeal.cardQuot_mul]
    exact (goodMaximal_norm_coprime hD P (hP P List.mem_cons_self).1 (hP P List.mem_cons_self).2).mul_left
      (ih (fun Q hQ => hP Q (List.mem_cons_of_mem P hQ)))

theorem goodIdealNormFiber_card_zero {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) :
    letI := quadraticOrderIsDomain hD
    Nat.card (GoodIdealNormFiber F 0) = 0 := by
  let := quadraticOrderIsDomain hD
  let : IsEmpty (GoodIdealNormFiber F 0) := ⟨fun I => I.1.cardQuot_pos.ne' I.2.1⟩
  simp

theorem goodIdealNormFiber_card_one {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) :
    letI := quadraticOrderIsDomain hD
    Nat.card (GoodIdealNormFiber F 1) = 1 := by
  let := quadraticOrderIsDomain hD
  let O := QuadraticAlgebra ℤ d b
  let x : GoodIdealNormFiber F 1 := ⟨(1 : InvertibleIdeal O), by
    change (⊤ : Ideal O).cardQuot = 1
    exact Submodule.cardQuot_top O O, by
    rw [InvertibleIdeal.coe_one]
    exact Ideal.isCoprime_iff_sup_eq.mpr (top_sup_eq _)⟩
  let : Unique (GoodIdealNormFiber F 1) :=
    { default := x
      uniq := by
        intro I
        apply Subtype.ext
        apply InvertibleIdeal.ext
        change (I.1 : Ideal O) = ⊤
        exact Submodule.cardQuot_eq_one_iff.mp I.2.1 }
  exact Nat.card_unique

theorem goodIdealNormFiber_card_eq_zero_of_not_coprime {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (n : ℕ) (hn : ¬ n.Coprime (discriminantLevel (b ^ 2 + 4 * d))) :
    letI := quadraticOrderIsDomain hD
    Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) n) = 0 := by
  let := quadraticOrderIsDomain hD
  let : IsEmpty (GoodIdealNormFiber (quadraticBadIdeal d b) n) := ⟨fun I => by
    have h := goodIdeal_norm_coprime hD I.1 I.2.2
    rw [I.2.1] at h
    exact hn h⟩
  simp

end Bernays
