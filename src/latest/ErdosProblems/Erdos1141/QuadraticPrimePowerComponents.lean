import ErdosProblems.Erdos1141.QuadraticCharacterProducts
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Group.Units.Equiv

/-!
# Prime-power components of an arbitrary quadratic Dirichlet character
-/

namespace Pollack17

open scoped BigOperators

noncomputable def primePowerCRT (m : ℕ) (hm : m ≠ 0) :
    ZMod m ≃+* (∀ p : m.primeFactors, ZMod ((p : ℕ) ^ m.factorization p)) := by
  have hprod := Nat.prod_primeFactors_coe_pow_factorization hm
  refine (ZMod.ringEquivCongr hprod).trans (ZMod.prodEquivPi _ ?_)
  intro p r hpr
  have hp := Nat.prime_of_mem_primeFactors p.property
  have hr := Nat.prime_of_mem_primeFactors r.property
  have hcop : (p : ℕ).Coprime (r : ℕ) := (Nat.coprime_primes hp hr).mpr (by
    intro h
    exact hpr (Subtype.ext h))
  exact hcop.pow _ _

theorem primePowerCRT_natCast (m : ℕ) (hm : m ≠ 0) (a : ℕ) (p : m.primeFactors) :
    primePowerCRT m hm (a : ZMod m) p = (a : ZMod ((p : ℕ) ^ m.factorization p)) := by
  simp [primePowerCRT]

theorem exists_quadratic_primePower_components {m : ℕ} (hm : m ≠ 0)
    (χ : DirichletCharacter ℂ m) (hχ : χ.IsQuadratic) :
    ∃ ψ : ∀ p : m.primeFactors, DirichletCharacter ℂ ((p : ℕ) ^ m.factorization p),
      (∀ p, (ψ p).IsQuadratic) ∧
        ∀ a : ℕ, a.Coprime m → χ (a : ZMod m) =
          ∏ p : m.primeFactors, ψ p (a : ZMod ((p : ℕ) ^ m.factorization p)) := by
  classical
  let R : m.primeFactors → Type := fun p => ZMod ((p : ℕ) ^ m.factorization p)
  let e := primePowerCRT m hm
  let eU := Units.mapEquiv e.toMulEquiv
  let χ' := pullbackUnitChar χ eU.symm.toMonoidHom
  have hχ' : χ'.IsQuadratic := pullbackUnitChar_isQuadratic χ hχ _
  refine ⟨productComponentChar R χ', productComponentChar_isQuadratic R χ' hχ', ?_⟩
  intro a ha
  let x := ZMod.unitOfCoprime a ha
  have hχx : χ (a : ZMod m) = χ' (eU x : ∀ p, R p) := by
    have h := pullbackUnitChar_apply_unit χ eU.symm.toMonoidHom (eU x)
    simpa only [x, χ', MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, ZMod.coe_unitOfCoprime]
      using h.symm
  rw [hχx, character_eq_prod_components R χ' (eU x)]
  apply Finset.prod_congr rfl
  intro p _
  congr 1
  change e (a : ZMod m) p = (a : R p)
  exact primePowerCRT_natCast m hm a p

end Pollack17
