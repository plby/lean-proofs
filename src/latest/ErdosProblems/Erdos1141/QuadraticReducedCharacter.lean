import ErdosProblems.Erdos1141.QuadraticProductCharacters

/-!
# A reduced conductor dividing the original modulus
-/

namespace Pollack17

open scoped BigOperators

theorem pow_two_coprime_primeModulus {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (hodd : 2 ∉ s) (e : ℕ) : (2 ^ e).Coprime (Burgess.primeModulus s) := by
  apply Nat.Coprime.pow_left
  apply Nat.Coprime.prod_right
  intro p hp
  exact (Nat.coprime_primes Nat.prime_two (hs p hp)).mpr (by
    intro h
    exact hodd (h ▸ hp))

theorem primeModulus_dvd_of_subset {m : ℕ} {s : Finset ℕ} (hs : s ⊆ m.primeFactors) :
    Burgess.primeModulus s ∣ m :=
  (Finset.prod_dvd_prod_of_subset s m.primeFactors id hs).trans (Nat.prod_primeFactors_dvd m)

theorem exists_quadratic_reduced_character {m : ℕ} (hm : m ≠ 0)
    (χ : DirichletCharacter ℂ m) (hχ : χ.IsQuadratic) :
    ∃ (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime), s ⊆ m.primeFactors.erase 2 ∧
      ∃ e : ℕ, e ≤ 3 ∧ e ≤ m.factorization 2 ∧
        ∃ θ : DirichletCharacter ℝ (2 ^ e), θ.IsQuadratic ∧
          ∃ hcop : (2 ^ e).Coprime (Burgess.primeModulus s),
            ∃ hd : 2 ^ e * Burgess.primeModulus s ∣ m,
              quadraticRealChar χ hχ = DirichletCharacter.changeLevel hd
                (tensorDirichletChar hcop θ (Burgess.productDirichletChar s hs)) := by
  have : NeZero m := ⟨hm⟩
  obtain ⟨s, hsm, hs, e, he3, hem, θ, hθ, heval⟩ :=
    quadratic_character_real_decomposition hm χ hχ
  have hodd : 2 ∉ s := fun h => (Finset.mem_erase.mp (hsm h)).1 rfl
  have hcop := pow_two_coprime_primeModulus hs hodd e
  have hq : Burgess.primeModulus s ∣ m := primeModulus_dvd_of_subset
    (fun p hp => (Finset.mem_erase.mp (hsm hp)).2)
  have h2 : 2 ^ e ∣ m := Nat.prime_two.pow_dvd_iff_le_factorization hm |>.mpr hem
  have hd := hcop.mul_dvd_of_dvd_of_dvd h2 hq
  refine ⟨s, hs, hsm, e, he3, hem, θ, hθ, hcop, hd, ?_⟩
  apply MulChar.ext
  intro x
  have ha := ZMod.val_coe_unit_coprime x
  have h := changeLevel_natCast hd
    (tensorDirichletChar hcop θ (Burgess.productDirichletChar s hs)) (x : ZMod m).val ha
  rw [tensorDirichletChar_natCast, Burgess.productDirichletChar_apply,
    ← heval _ ha] at h
  simpa only [ZMod.natCast_zmod_val] using h.symm

theorem quadraticRealChar_eq_one_iff {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) : quadraticRealChar χ hχ = 1 ↔ χ = 1 := by
  constructor
  · intro h
    apply MulChar.ext
    intro x
    have hx := ofReal_quadraticRealChar χ hχ (x : R)
    rw [h, MulChar.one_apply_coe, Complex.ofReal_one] at hx
    simpa only [MulChar.one_apply_coe] using hx.symm
  · intro h
    apply MulChar.ext
    intro x
    simp only [quadraticRealChar_apply, h, MulChar.one_apply_coe, Complex.one_re]

end Pollack17
