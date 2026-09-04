import Util.Bernays.GenusTwistedArithmetic

/-!
# The convolution square of a genus-twisted norm indicator

The square correction is supported exactly on squares of inert-prime products.
-/

open scoped Classical

namespace Bernays

theorem squareSupportAF_primePower_of_not {S : ℕ → Prop} {p : ℕ} (hp : p.Prime)
    (hS : ¬ S p) (e : ℕ) :
    squareSupportAF S (p ^ e) = if e = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [pow_zero, (squareSupportAF_isMultiplicative S).1, if_pos rfl]
  · rw [squareSupportAF_primePower S hp he, if_neg (not_and.mpr (fun h => False.elim (hS h))),
      if_neg he.ne']

theorem squareSupportAF_primePower_of_mem {S : ℕ → Prop} {p : ℕ} (hp : p.Prime)
    (hS : S p) (e : ℕ) :
    squareSupportAF S (p ^ e) = if Even e then 1 else 0 := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [pow_zero, (squareSupportAF_isMultiplicative S).1, if_pos Even.zero]
  · rw [squareSupportAF_primePower S hp he]
    simp only [hS, true_and]

theorem arithmetic_mul_primePower_congr (f g u v : ArithmeticFunction ℂ) {p : ℕ}
    (hp : p.Prime) (hfu : ∀ e : ℕ, f (p ^ e) = u (p ^ e))
    (hgv : ∀ e : ℕ, g (p ^ e) = v (p ^ e)) (e : ℕ) :
    (f * g) (p ^ e) = (u * v) (p ^ e) := by
  rw [arithmetic_mul_primePower f g hp, arithmetic_mul_primePower u v hp]
  exact Finset.sum_congr rfl (fun k _ => by rw [hfu, hgv])

theorem genusLocalAF_square {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
      genusLocalAF hD ψ * genusLocalAF hD ψ =
        genusIdealAF hD ψ * squareSupportAF (fun p => discriminantCharacter _ hD.ne p = -1) := by
  let := quadraticOrderIsDomain hD
  intro ψ
  let f := genusLocalAF hD ψ
  let a := genusIdealAF hD ψ
  let H := squareSupportAF (fun p => discriminantCharacter _ hD.ne p = -1)
  have hf : f.IsMultiplicative := genusLocalAF_isMultiplicative hD ψ
  have ha : a.IsMultiplicative := genusIdealAF_isMultiplicative hD ψ
  have hH : H.IsMultiplicative := squareSupportAF_isMultiplicative _
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers (f * f) (hf.mul hf)
    (a * H) (ha.mul hH)).mpr
  intro p e hp
  by_cases hc : p.Coprime (discriminantLevel (b ^ 2 + 4 * d))
  · by_cases hχ : discriminantCharacter _ hD.ne p = -1
    · apply arithmetic_mul_primePower_congr f f a H hp
      · intro k
        exact (genusLocalAF_inert_primePower hD ψ p hp hc hχ k).trans
          (genusIdealAF_inert_primePower hD ψ p hp hc hχ k).symm
      · intro k
        exact (genusLocalAF_inert_primePower hD ψ p hp hc hχ k).trans
          (squareSupportAF_primePower_of_mem hp hχ k).symm
    · rw [arithmetic_mul_primePower_geometric f hp _
        (genusLocalAF_split_primePower hD ψ p hp hc hχ),
        arithmetic_mul_primePower_delta a H hp (squareSupportAF_primePower_of_not hp hχ)]
      exact (genusIdealAF_split_primePower hD ψ p hp hc hχ e).symm
  · have hχ : discriminantCharacter _ hD.ne p ≠ -1 := by
      rw [discriminantCharacter_eq_zero_of_not_coprime hD.ne hc]
      norm_num
    apply arithmetic_mul_primePower_congr f f a H hp
    · intro k
      exact (genusLocalAF_bad_primePower hD ψ p hp hc k).trans
        (genusIdealAF_bad_primePower hD ψ p hc k).symm
    · intro k
      exact (genusLocalAF_bad_primePower hD ψ p hp hc k).trans
        (squareSupportAF_primePower_of_not hp hχ k).symm

end Bernays
