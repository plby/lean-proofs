import ErdosProblems.Erdos1148.FiniteRingUnitDensity
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Data.Nat.PrimeFin

/-! # Bounding maximal ideals of a finite quotient by residue characteristic -/

namespace Erdos1148.DukeArithmetic

open NumberField

theorem maximalSpectrum_characteristic_card_le_degree
    (K : Type*) [Field K] [NumberField K] {R : Type*} [CommRing R] [Finite R]
    (g : 𝓞 K →+* R) (hg : Function.Surjective g) (p : ℕ) (hp : p.Prime) :
    Nat.card {m : MaximalSpectrum R // ringChar (R ⧸ m.asIdeal) = p} ≤ Module.finrank ℚ K := by
  classical
  let M := {m : MaximalSpectrum R // ringChar (R ⧸ m.asIdeal) = p}
  let := Fintype.ofFinite M
  let := Fintype.ofFinite R
  let := (⟨hp⟩ : Fact p.Prime)
  have hcop : Pairwise (fun m n : M => IsCoprime m.1.asIdeal n.1.asIdeal) := by
    intro m n hmn
    exact Ideal.isCoprime_of_isMaximal (fun h => hmn (Subtype.ext (MaximalSpectrum.ext h)))
  let F : 𝓞 K →+* (∀ m : M, R ⧸ m.1.asIdeal) :=
    RingHom.pi (fun m => (Ideal.Quotient.mk m.1.asIdeal).comp g)
  have hF : Function.Surjective F := by
    intro x
    obtain ⟨r, hr⟩ := Ideal.pi_quotient_surjective hcop x
    obtain ⟨b, rfl⟩ := hg r
    exact ⟨b, funext hr⟩
  let P : Ideal (𝓞 K) := Ideal.span {(p : 𝓞 K)}
  have hP : P ≤ RingHom.ker F := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change F (p : 𝓞 K) = 0
    funext m
    change Ideal.Quotient.mk m.1.asIdeal (g (p : 𝓞 K)) = 0
    rw [map_natCast, map_natCast]
    calc
      (p : R ⧸ m.1.asIdeal) = (ringChar (R ⧸ m.1.asIdeal) : R ⧸ m.1.asIdeal) :=
        congrArg Nat.cast m.2.symm
      _ = 0 := CharP.cast_eq_zero _ _
  let Fq : (𝓞 K ⧸ P) →+* (∀ m : M, R ⧸ m.1.asIdeal) := Ideal.Quotient.lift P F hP
  have hFq : Function.Surjective Fq := by
    intro x
    obtain ⟨b, rfl⟩ := hF x
    exact ⟨Ideal.Quotient.mk P b, rfl⟩
  have hP₀ : P ≠ ⊥ := by
    intro h
    apply hp.ne_zero
    exact Nat.cast_eq_zero.mp (Ideal.span_singleton_eq_bot.mp h)
  let := P.finiteQuotientOfFreeOfNeBot hP₀
  have hcard := Nat.card_le_card_of_surjective Fq hFq
  have hPcard : Nat.card (𝓞 K ⧸ P) = p ^ Module.finrank ℚ K := by
    change P.absNorm = _
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  rw [hPcard, Nat.card_pi] at hcard
  have hfield : ∀ m : M, p ≤ Nat.card (R ⧸ m.1.asIdeal) := by
    intro m
    let := Fintype.ofFinite (R ⧸ m.1.asIdeal)
    have hpchar : p ∣ ringChar (R ⧸ m.1.asIdeal) := by rw [m.2]
    have hdiv := (prime_dvd_char_iff_dvd_card p).mp hpchar
    exact Nat.le_of_dvd Nat.card_pos (by simpa only [Nat.card_eq_fintype_card] using hdiv)
  have hpow : p ^ Nat.card M ≤ p ^ Module.finrank ℚ K := by
    calc
      _ = ∏ _m : M, p := by simp [Nat.card_eq_fintype_card]
      _ ≤ ∏ m : M, Nat.card (R ⧸ m.1.asIdeal) := Finset.prod_le_prod' (fun m _ => hfield m)
      _ ≤ _ := hcard
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hpow

theorem maximalSpectrum_card_le_degree_mul_primeFactors
    (K : Type*) [Field K] [NumberField K] {R : Type*} [CommRing R] [Finite R]
    (g : 𝓞 K →+* R) (hg : Function.Surjective g) (n : ℕ) (hn : n ≠ 0) (hnR : (n : R) = 0) :
    Nat.card (MaximalSpectrum R) ≤ Module.finrank ℚ K * n.primeFactors.card := by
  classical
  let := Fintype.ofFinite R
  let c : MaximalSpectrum R → ℕ := fun m => ringChar (R ⧸ m.asIdeal)
  have hmem : ∀ m, c m ∈ n.primeFactors := by
    intro m
    apply Nat.mem_primeFactors.mpr
    refine ⟨CharP.prime_ringChar (R ⧸ m.asIdeal), ?_, hn⟩
    apply (CharP.cast_eq_zero_iff (R ⧸ m.asIdeal) (c m) n).mp
    have h := congrArg (Ideal.Quotient.mk m.asIdeal) hnR
    simpa only [map_natCast, map_zero] using h
  let E := Equiv.sigmaSubtypeFiberEquiv c (fun p => p ∈ n.primeFactors) hmem
  calc
    Nat.card (MaximalSpectrum R) =
        Nat.card (Σ p : {p // p ∈ n.primeFactors}, {m // c m = p.1}) :=
      (Nat.card_congr E).symm
    _ = ∑ p : {p // p ∈ n.primeFactors}, Nat.card {m // c m = p.1} := Nat.card_sigma
    _ ≤ ∑ _p : {p // p ∈ n.primeFactors}, Module.finrank ℚ K := by
      apply Finset.sum_le_sum
      intro p _
      exact maximalSpectrum_characteristic_card_le_degree K g hg p.1
        (Nat.prime_of_mem_primeFactors p.2)
    _ = Module.finrank ℚ K * n.primeFactors.card := by simp [mul_comm]

end Erdos1148.DukeArithmetic
