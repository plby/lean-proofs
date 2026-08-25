import ErdosProblems.Erdos1141.QuadraticDecomposition
import ErdosProblems.Erdos1141.QuadraticCRT

/-!
# Real-valued quadratic characters and the product-character interface
-/

namespace Pollack17

open scoped BigOperators

theorem quadratic_apply_im_zero {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) (x : R) : (χ x).im = 0 := by
  rcases hχ x with h | h | h <;> simp [h]

noncomputable def quadraticRealChar {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) : MulChar R ℝ where
  toFun x := (χ x).re
  map_one' := by rw [map_one, Complex.one_re]
  map_mul' x y := by
    rw [map_mul, Complex.mul_re, quadratic_apply_im_zero χ hχ, zero_mul, sub_zero]
  map_nonunit' x hx := by rw [χ.map_nonunit hx, Complex.zero_re]

theorem quadraticRealChar_apply {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) (x : R) :
    quadraticRealChar χ hχ x = (χ x).re := rfl

theorem quadraticRealChar_isQuadratic {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) : (quadraticRealChar χ hχ).IsQuadratic := by
  intro x
  rcases hχ x with h | h | h
  · exact Or.inl (by simp [quadraticRealChar_apply, h])
  · exact Or.inr (Or.inl (by simp [quadraticRealChar_apply, h]))
  · exact Or.inr (Or.inr (by simp [quadraticRealChar_apply, h]))

theorem ofReal_quadraticRealChar {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) (x : R) :
    (quadraticRealChar χ hχ x : ℂ) = χ x := by
  apply Complex.ext
  · rfl
  · exact (quadratic_apply_im_zero χ hχ x).symm

theorem abs_quadraticRealChar_le_one {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) (x : R) : |quadraticRealChar χ hχ x| ≤ 1 := by
  rcases quadraticRealChar_isQuadratic χ hχ x with h | h | h <;> norm_num [h]

theorem product_quadraticPrimeValue_eq (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (a : ℕ) :
    (∏ p ∈ s, quadraticPrimeValue p a) =
      (Burgess.productChar s hs (a : ZMod (Burgess.primeModulus s)) : ℂ) := by
  classical
  rw [Burgess.productChar, Complex.ofReal_prod]
  rw [← Finset.prod_coe_sort s (fun p => quadraticPrimeValue p a)]
  apply Finset.prod_congr rfl
  intro p _
  rw [Burgess.primeCRT_natCast]
  simp only [quadraticPrimeValue, dif_pos (hs p p.property), Burgess.localChar, Burgess.qchar,
    Complex.ofReal_intCast]

theorem quadratic_character_real_decomposition {m : ℕ} (hm : m ≠ 0)
    (χ : DirichletCharacter ℂ m) (hχ : χ.IsQuadratic) :
    ∃ s : Finset ℕ, s ⊆ m.primeFactors.erase 2 ∧
      ∃ hs : ∀ p ∈ s, p.Prime, ∃ e : ℕ, e ≤ 3 ∧ e ≤ m.factorization 2 ∧
        ∃ θ : DirichletCharacter ℝ (2 ^ e), θ.IsQuadratic ∧
          ∀ a : ℕ, a.Coprime m → quadraticRealChar χ hχ (a : ZMod m) =
            θ (a : ZMod (2 ^ e)) * Burgess.productChar s hs
              (a : ZMod (Burgess.primeModulus s)) := by
  obtain ⟨s, hsm, e, he3, hem, θ, hθ, heval⟩ := quadratic_character_decomposition hm χ hχ
  have hs : ∀ p ∈ s, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp (hsm hp)).2
  refine ⟨s, hsm, hs, e, he3, hem, quadraticRealChar θ hθ,
    quadraticRealChar_isQuadratic θ hθ, fun a ha => ?_⟩
  have h := congrArg Complex.re (heval a ha)
  rw [product_quadraticPrimeValue_eq s hs a] at h
  simpa only [quadraticRealChar_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] using h

end Pollack17
