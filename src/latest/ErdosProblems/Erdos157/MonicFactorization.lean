import ErdosProblems.Erdos157.CharacterSeries
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Prime factor coordinates on monic polynomials

Unique factorization gives an exact equivalence with finite multisets of
monic irreducibles. This is the indexing change for the Euler product.
-/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial UniqueFactorizationMonoid

variable {K : Type*} [Field K] [DecidableEq K]

abbrev MonicPolynomial (K : Type*) [Field K] := {f : K[X] // f.Monic}
abbrev PrimePolynomial (K : Type*) [Field K] := {f : K[X] // f.Monic ∧ Irreducible f}

/-- Forget the recorded degree; it can be recovered from the polynomial. -/
noncomputable def allMonicEquiv : AllMonic K ≃ MonicPolynomial K where
  toFun f := ⟨f.2.1, f.2.monic⟩
  invFun f := ⟨f.1.natDegree, MonicDegreeEq.mk f.1 f.2 rfl⟩
  left_inv f := by
    rcases f with ⟨d, f⟩
    rcases f with ⟨p, hp⟩
    have hd : p.natDegree = d := MonicDegreeEq.natDegree ⟨p, hp⟩
    subst d
    rfl
  right_inv _ := rfl

/-- The normalized prime factors, with their monicity and irreducibility retained. -/
noncomputable def primeFactors (f : MonicPolynomial K) : Multiset (PrimePolynomial K) := by
  classical
  exact (normalizedFactors f.1).attach.map fun p =>
    ⟨p.1, ((Polynomial.mem_normalizedFactors_iff f.2.ne_zero).mp p.2).2.1,
      ((Polynomial.mem_normalizedFactors_iff f.2.ne_zero).mp p.2).1⟩

theorem primeFactors_map_val (f : MonicPolynomial K) :
    (primeFactors f).map Subtype.val = normalizedFactors f.1 := by
  classical
  simp only [primeFactors, Multiset.map_map, Function.comp_def, Multiset.attach_map_val]

/-- Multiply a finite multiset of prime polynomials. -/
noncomputable def primeProduct (s : Multiset (PrimePolynomial K)) : MonicPolynomial K :=
  ⟨(s.map Subtype.val).prod, Polynomial.monic_multiset_prod_of_monic s Subtype.val
    (fun p _ => p.2.1)⟩

theorem primeProduct_primeFactors (f : MonicPolynomial K) :
    primeProduct (primeFactors f) = f := by
  classical
  apply Subtype.ext
  change ((primeFactors f).map Subtype.val).prod = f.1
  rw [primeFactors_map_val, prod_normalizedFactors_eq f.2.ne_zero, f.2.normalize_eq_self]

theorem primeFactors_primeProduct (s : Multiset (PrimePolynomial K)) :
    primeFactors (primeProduct s) = s := by
  classical
  apply Multiset.map_injective (f := Subtype.val) Subtype.val_injective
  rw [primeFactors_map_val]
  change normalizedFactors (s.map Subtype.val).prod = s.map Subtype.val
  rw [normalizedFactors_prod_eq _ (by
    intro p hp
    obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hp
    exact p.2.2)]
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro p _
  exact p.2.1.normalize_eq_self

/-- Exact prime factorization, including the empty multiset representing one. -/
noncomputable def primeFactorizationEquiv : MonicPolynomial K ≃ Multiset (PrimePolynomial K) where
  toFun := primeFactors
  invFun := primeProduct
  left_inv := primeProduct_primeFactors
  right_inv := primeFactors_primeProduct

omit [DecidableEq K] in
theorem primeProduct_natDegree (s : Multiset (PrimePolynomial K)) :
    (primeProduct s).1.natDegree = (s.map fun p => p.1.natDegree).sum := by
  change (s.map Subtype.val).prod.natDegree = _
  rw [Polynomial.natDegree_multiset_prod_of_monic _ (by
    intro p hp
    obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hp
    exact p.2.1), Multiset.map_map]
  rfl

omit [DecidableEq K] in
/-- Every prime polynomial has positive degree. -/
theorem primePolynomial_degree_pos (p : PrimePolynomial K) : 0 < p.1.natDegree := by
  by_contra h
  have hz : p.1.natDegree = 0 := by omega
  exact p.2.2.not_isUnit (by rw [Polynomial.eq_one_of_monic_natDegree_zero p.2.1 hz]; exact isUnit_one)

end Erdos157.Elementary.PolynomialCharacters
