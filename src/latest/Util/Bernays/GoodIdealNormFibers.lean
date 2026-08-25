import Util.Bernays.CoprimeIdealDecomposition
import Util.Bernays.NormFiberCounts

/-!
# Multiplicativity of counts of coprime quadratic ideals of prescribed norm
-/

namespace Bernays

abbrev GoodIdealNormFiber {R : Type*} [CommRing R] [IsDomain R]
    (F : Ideal R) (n : ℕ) :=
  {I : InvertibleIdeal R // (I : Ideal R).cardQuot = n ∧ IsCoprime (I : Ideal R) F}

theorem finite_goodIdealNormFiber {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (F : Ideal (QuadraticAlgebra ℤ d b)) (n : ℕ), Finite (GoodIdealNormFiber F n) := by
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  intro F n
  let O := QuadraticAlgebra ℤ d b
  letI (C : ClassGroup O) := finite_idealClassBall hD C n
  let e : GoodIdealNormFiber F n → Σ C : ClassGroup O, IdealClassBall O C n :=
    fun I => ⟨I.1.idealClass, ⟨I.1, rfl, I.2.1.le⟩⟩
  apply Finite.of_injective e
  intro I J hIJ
  exact Subtype.ext (congrArg (fun t : Σ C : ClassGroup O, IdealClassBall O C n => t.2.1) hIJ)

noncomputable def goodIdealNormFiberMulEquiv {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) (m n : ℕ) (hmn : m.Coprime n) :
    letI := quadraticOrderIsDomain hD
    GoodIdealNormFiber F m × GoodIdealNormFiber F n ≃ GoodIdealNormFiber F (m * n) := by
  letI := quadraticOrderIsDomain hD
  let O := QuadraticAlgebra ℤ d b
  let f : GoodIdealNormFiber F m × GoodIdealNormFiber F n → GoodIdealNormFiber F (m * n) :=
    fun x => ⟨x.1.1 * x.2.1, by rw [InvertibleIdeal.cardQuot_mul, x.1.2.1, x.2.2.1],
      x.1.2.2.mul_left x.2.2.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    have hprod : x.1.1 * x.2.1 = y.1.1 * y.2.1 := congrArg Subtype.val hxy
    have hc : (x.1.1 : Ideal O).cardQuot.Coprime (x.2.1 : Ideal O).cardQuot := by
      rwa [x.1.2.1, x.2.2.1]
    obtain ⟨h₁, h₂⟩ := InvertibleIdeal.coprime_norm_factors_unique hprod hc
      (x.1.2.1.trans y.1.2.1.symm) (x.2.2.1.trans y.2.2.1.symm)
    exact Prod.ext (Subtype.ext h₁) (Subtype.ext h₂)
  · intro I
    obtain ⟨J, K, hJK, hJ, hK⟩ := exists_coprime_norm_factors hD I.1 m n hmn I.2.1
    have hcop : IsCoprime ((J : Ideal O) * (K : Ideal O)) F := by
      change IsCoprime ((J * K : InvertibleIdeal O) : Ideal O) F
      rw [hJK]
      exact I.2.2
    exact ⟨(⟨J, hJ, hcop.of_mul_left_left⟩, ⟨K, hK, hcop.of_mul_left_right⟩), Subtype.ext hJK⟩

theorem goodIdealNormFiber_card_mul {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) (m n : ℕ) (hmn : m.Coprime n) :
    letI := quadraticOrderIsDomain hD
    Nat.card (GoodIdealNormFiber F (m * n)) =
      Nat.card (GoodIdealNormFiber F m) * Nat.card (GoodIdealNormFiber F n) := by
  letI := quadraticOrderIsDomain hD
  rw [← Nat.card_congr (goodIdealNormFiberMulEquiv hD F m n hmn), Nat.card_prod]

end Bernays
