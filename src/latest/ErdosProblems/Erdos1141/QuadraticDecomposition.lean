import ErdosProblems.Erdos1141.QuadraticPrimePowerComponents
import ErdosProblems.Erdos1141.QuadraticPrimePowerReduction

/-!
# Decomposing every quadratic Dirichlet character on the units

The only two-adic factor has modulus at most eight. The odd factors are
selected Legendre characters; omitted prime factors contribute the principal
character. Values away from the units will be handled by inclusion-exclusion.
-/

namespace Pollack17

open scoped BigOperators

noncomputable def quadraticPrimeValue (p a : ℕ) : ℂ := by
  classical
  exact if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    (quadraticChar (ZMod p) (a : ZMod p) : ℂ)
  else 0

theorem exists_subset_product_choices (s : Finset ℕ) (f g : ℕ → ℕ → ℂ) (P : ℕ → Prop)
    (h : ∀ p ∈ s, ∃ b : Bool, ∀ a, P a → f p a = if b then g p a else 1) :
    ∃ t ⊆ s, ∀ a, P a → (∏ p ∈ s, f p a) = ∏ p ∈ t, g p a := by
  classical
  choose b hb using h
  let B : ℕ → Bool := fun p => if hp : p ∈ s then b p hp else false
  refine ⟨s.filter (fun p => B p), Finset.filter_subset _ _, fun a ha => ?_⟩
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  simpa only [B, dif_pos hp] using hb p hp a ha

theorem quadratic_character_decomposition {m : ℕ} (hm : m ≠ 0)
    (χ : DirichletCharacter ℂ m) (hχ : χ.IsQuadratic) :
    ∃ s : Finset ℕ, s ⊆ m.primeFactors.erase 2 ∧
      ∃ e : ℕ, e ≤ 3 ∧ e ≤ m.factorization 2 ∧
        ∃ θ : DirichletCharacter ℂ (2 ^ e), θ.IsQuadratic ∧
          ∀ a : ℕ, a.Coprime m → χ (a : ZMod m) =
            θ (a : ZMod (2 ^ e)) * ∏ p ∈ s, quadraticPrimeValue p a := by
  classical
  obtain ⟨ψ, hψ, hprod⟩ := exists_quadratic_primePower_components hm χ hχ
  let f : ℕ → ℕ → ℂ := fun p a =>
    if hp : p ∈ m.primeFactors then ψ ⟨p, hp⟩ (a : ZMod (p ^ m.factorization p)) else 1
  have hlocal : ∀ p ∈ m.primeFactors.erase 2, ∃ b : Bool,
      ∀ a : ℕ, a.Coprime m → f p a = if b then quadraticPrimeValue p a else 1 := by
    intro p hp
    have hpne : p ≠ 2 := (Finset.mem_erase.mp hp).1
    have hpm : p ∈ m.primeFactors := (Finset.mem_erase.mp hp).2
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpm
    have : Fact p.Prime := ⟨hpp⟩
    have he : 0 < m.factorization p :=
      hpp.factorization_pos_of_dvd hm (Nat.dvd_of_mem_primeFactors hpm)
    obtain ⟨b, hb⟩ := quadratic_odd_prime_power_values hpp hpne he (ψ ⟨p, hpm⟩) (hψ ⟨p, hpm⟩)
    refine ⟨b, fun a ha => ?_⟩
    have hap : a.Coprime p := ha.of_dvd_right (Nat.dvd_of_mem_primeFactors hpm)
    simpa only [f, dif_pos hpm, quadraticPrimeValue, dif_pos hpp] using hb a hap
  obtain ⟨s, hs, hodd⟩ := exists_subset_product_choices (m.primeFactors.erase 2) f
    quadraticPrimeValue (fun a => a.Coprime m) hlocal
  have htwo : ∃ e : ℕ, e ≤ 3 ∧ e ≤ m.factorization 2 ∧
      ∃ θ : DirichletCharacter ℂ (2 ^ e), θ.IsQuadratic ∧
        ∀ a : ℕ, a.Coprime m → f 2 a = θ (a : ZMod (2 ^ e)) := by
    by_cases h2 : 2 ∈ m.primeFactors
    · obtain ⟨e, he3, hem, θ, hθ, heval⟩ :=
        quadratic_two_power_small_level (m.factorization 2) (ψ ⟨2, h2⟩) (hψ ⟨2, h2⟩)
      refine ⟨e, he3, hem, θ, hθ, fun a ha => ?_⟩
      have hd : 2 ^ m.factorization 2 ∣ m :=
        Nat.prime_two.pow_dvd_iff_le_factorization hm |>.mpr le_rfl
      simpa only [f, dif_pos h2] using heval a (ha.of_dvd_right hd)
    · refine ⟨0, by omega, Nat.zero_le _, 1, ?_, fun a ha => ?_⟩
      · exact MulChar.isQuadratic_iff_sq_eq_one.mpr (one_pow 2)
      · have hunit : IsUnit (a : ZMod (2 ^ 0)) :=
          (ZMod.isUnit_iff_coprime a _).mpr (by simp)
        simp only [f, dif_neg h2, MulChar.one_apply hunit]
  obtain ⟨e, he3, hem, θ, hθ, heval⟩ := htwo
  refine ⟨s, hs, e, he3, hem, θ, hθ, fun a ha => ?_⟩
  have hprod' : χ (a : ZMod m) = ∏ p ∈ m.primeFactors, f p a := by
    rw [hprod a ha]
    rw [← Finset.prod_coe_sort m.primeFactors (fun p => f p a)]
    apply Finset.prod_congr rfl
    intro p _
    simp only [f, dif_pos p.property]
  rw [hprod']
  have hsplit : (∏ p ∈ m.primeFactors, f p a) =
      f 2 a * ∏ p ∈ m.primeFactors.erase 2, f p a := by
    by_cases h2 : 2 ∈ m.primeFactors
    · exact (Finset.mul_prod_erase _ _ h2).symm
    · simp only [Finset.erase_eq_of_notMem h2, f, dif_neg h2, one_mul]
  rw [hsplit, heval a ha, hodd a ha]

end Pollack17
