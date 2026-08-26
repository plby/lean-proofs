import ErdosProblems.Erdos538.Structural

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538

/-- Two genuinely distinct prime representations with squarefree quotients force
the common product to be squarefree. -/
theorem squarefree_of_two_representations {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (ha : Squarefree a) (hb : Squarefree b)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hpq : p ≠ q) (heq : p * a = q * b) :
    Squarefree (p * a) := by
  apply Nat.squarefree_of_factorization_le_one (Nat.mul_ne_zero hp.ne_zero ha0)
  intro x
  by_cases hxp : x = p
  · rw [heq, Nat.factorization_mul hq.ne_zero hb0, hq.factorization]
    simp [hxp, hpq]
    exact Squarefree.natFactorization_le_one p hb
  · rw [Nat.factorization_mul hp.ne_zero ha0, hp.factorization]
    simp [hxp]
    exact Squarefree.natFactorization_le_one x ha

/-- On a squarefree candidate family, a nonsquarefree target has at most one
prime-times-member representation. -/
theorem nonsquarefree_representations_card_le_one {A : Finset ℕ} {m : ℕ}
    (hpos : ∀ a ∈ A, 1 ≤ a)
    (hsq : ∀ a ∈ A, Squarefree a)
    (hm : ¬ Squarefree m) :
    (representations A m).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro pa qa hpa hqa
  rcases Finset.mem_filter.mp hpa with ⟨hpaProd, hp, hmpa⟩
  rcases Finset.mem_filter.mp hqa with ⟨hqaProd, hq, hmqa⟩
  have hpaA : pa.2 ∈ A := (Finset.mem_product.mp hpaProd).2
  have hqaA : qa.2 ∈ A := (Finset.mem_product.mp hqaProd).2
  by_cases hpq : pa.1 = qa.1
  · apply Prod.ext hpq
    exact representation_prime_injective hpa hqa hpq
  · exfalso
    apply hm
    rw [hmpa]
    apply squarefree_of_two_representations hp hq (hsq pa.2 hpaA) (hsq qa.2 hqaA)
    · have := hpos pa.2 hpaA
      omega
    · have := hpos qa.2 hqaA
      omega
    · exact hpq
    · exact hmpa.symm.trans hmqa

/-- The daisy cap on squarefree targets, expressed arithmetically through prime
quotients. -/
def SquarefreeDaisyCap (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ m : ℕ, Squarefree m → (quotientPrimes A m).card ≤ r

/-- For a squarefree candidate family and a positive cap, full admissibility is
exactly the daisy condition on squarefree targets. -/
theorem squarefree_admissible_iff {A : Finset ℕ} {r N : ℕ}
    (hr : 1 ≤ r)
    (hpos : ∀ a ∈ A, 1 ≤ a)
    (hsq : ∀ a ∈ A, Squarefree a) :
    Admissible r N A ↔
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧ SquarefreeDaisyCap r A := by
  constructor
  · intro hA
    refine ⟨hA.1, ?_⟩
    intro m _
    rw [← representations_card_eq_quotientPrimes]
    exact hA.2 m
  · rintro ⟨hrange, hcap⟩
    refine ⟨hrange, ?_⟩
    intro m
    by_cases hm : Squarefree m
    · rw [representations_card_eq_quotientPrimes]
      exact hcap m hm
    · exact (nonsquarefree_representations_card_le_one hpos hsq hm).trans hr

end Erdos538
