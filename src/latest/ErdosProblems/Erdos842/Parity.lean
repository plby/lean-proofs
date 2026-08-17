import Mathlib

/-!
# The indexed-arc coefficient identity used in Erdős Problem 842

This file isolates the algebraic part of the Fleischner--Stiebitz/Petrov
argument.  Parallel arcs are deliberately represented by an arbitrary finite
index type `A`: this is the interface needed when a Hamiltonian-cycle arc and
a triangle arc happen to have the same endpoints.
-/

open scoped BigOperators

namespace Erdos842.Parity

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

/-- The six-term cancellation for a cyclically oriented triangle.  This is the
denominator-free form of equation (5.1) in the mathematical writeup. -/
theorem directedTriangle_expansion (a b c : V) :
    (MvPolynomial.X a - MvPolynomial.X b) *
        (MvPolynomial.X b - MvPolynomial.X c) *
          (MvPolynomial.X c - MvPolynomial.X a : MvPolynomial V ℤ) =
      MvPolynomial.X b * MvPolynomial.X c ^ 2 +
        MvPolynomial.X a ^ 2 * MvPolynomial.X c +
        MvPolynomial.X a * MvPolynomial.X b ^ 2 -
        MvPolynomial.X b ^ 2 * MvPolynomial.X c -
        MvPolynomial.X a * MvPolynomial.X c ^ 2 -
        MvPolynomial.X a ^ 2 * MvPolynomial.X b := by
  ring

/-- An odd number of fibres, each contributing either `2` or `-2`, contributes
`2` modulo `4`.  This packages the last sign-forgetting step of Petrov's
constant-term argument. -/
theorem signed_two_sum_modEq_two {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ x ∈ s, f x = 2 ∨ f x = -2) (hs : Odd s.card) :
    (∑ x ∈ s, f x) ≡ 2 [ZMOD 4] := by
  have hterm : ∀ x ∈ s, f x ≡ (2 : ℤ) [ZMOD 4] := by
    intro x hx
    rcases hf x hx with h | h <;> rw [h] <;> norm_num
  have hsum := Int.ModEq.sum hterm
  calc
    (∑ x ∈ s, f x) ≡ ∑ _x ∈ s, (2 : ℤ) [ZMOD 4] := hsum
    _ = (s.card : ℤ) * 2 := by simp
    _ ≡ 2 [ZMOD 4] := by
      rcases hs with ⟨k, hk⟩
      rw [hk]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      rw [Int.modEq_iff_dvd]
      refine ⟨-(k : ℤ), ?_⟩
      ring

/-- A finite directed multigraph whose arcs have explicit indices. -/
structure IndexedArcs (V A : Type*) where
  tail : A → V
  head : A → V

namespace IndexedArcs

variable (D : IndexedArcs V A)

/-- The graph polynomial, retaining parallel indexed arcs as separate factors. -/
noncomputable def polynomial : MvPolynomial V ℤ :=
  ∏ a : A, (MvPolynomial.X (D.tail a) - MvPolynomial.X (D.head a))

/-- The exponent of the term which chooses the head of precisely the arcs in `S`. -/
noncomputable def choiceExponent (S : Finset A) : V →₀ ℕ :=
  (∑ a ∈ (Finset.univ : Finset A) \ S, Finsupp.single (D.tail a) 1) +
    ∑ a ∈ S, Finsupp.single (D.head a) 1

/-- The exponent assigning `2` to every vertex. -/
noncomputable def centralExponent (D : IndexedArcs V A) : V →₀ ℕ :=
  ∑ v : V, Finsupp.single v 2

/-- Number of selected arcs entering a vertex. -/
def selectedIn (S : Finset A) (v : V) : ℕ :=
  (S.filter fun a ↦ D.head a = v).card

/-- Number of selected arcs leaving a vertex. -/
def selectedOut (S : Finset A) (v : V) : ℕ :=
  (S.filter fun a ↦ D.tail a = v).card

/-- A selected indexed-arc set is Eulerian when indegree equals outdegree at every vertex. -/
def Balanced (S : Finset A) : Prop :=
  ∀ v, D.selectedIn S v = D.selectedOut S v

noncomputable instance balancedDecidable : DecidablePred D.Balanced :=
  Classical.decPred _

private lemma prod_X_eq_monomial_sum_single (s : Finset A) (f : A → V) :
    (∏ a ∈ s, MvPolynomial.X (f a) : MvPolynomial V ℤ) =
      MvPolynomial.monomial (∑ a ∈ s, Finsupp.single (f a) 1) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha, Finset.sum_insert ha, ih]
      simp [MvPolynomial.X, MvPolynomial.monomial_mul]

/-- Full subset expansion of the indexed graph polynomial. -/
theorem polynomial_eq_sum_monomial :
    D.polynomial =
      ∑ S ∈ (Finset.univ : Finset A).powerset,
        MvPolynomial.monomial (D.choiceExponent S) ((-1 : ℤ) ^ S.card) := by
  classical
  rw [polynomial, Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro S hS
  rw [prod_X_eq_monomial_sum_single, prod_X_eq_monomial_sum_single]
  simp only [choiceExponent]
  rw [mul_assoc, MvPolynomial.monomial_mul]
  have hcoeff : ((-1 : MvPolynomial V ℤ) ^ S.card) =
      MvPolynomial.C ((-1 : ℤ) ^ S.card) := by
    rw [map_pow]
    simp
  rw [hcoeff]
  rw [MvPolynomial.C_mul_monomial]
  simp

/-- Coefficient form of `polynomial_eq_sum_monomial`, before imposing regularity. -/
theorem coeff_polynomial (m : V →₀ ℕ) :
    MvPolynomial.coeff m D.polynomial =
      ∑ S ∈ (Finset.univ : Finset A).powerset,
        if D.choiceExponent S = m then ((-1 : ℤ) ^ S.card) else 0 := by
  classical
  rw [D.polynomial_eq_sum_monomial, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro S hS
  simp [MvPolynomial.coeff_monomial, eq_comm]

@[simp] theorem centralExponent_apply (v : V) : D.centralExponent v = 2 := by
  classical
  simp [centralExponent]

theorem choiceExponent_apply (S : Finset A) (v : V) :
    D.choiceExponent S v =
      (((Finset.univ : Finset A) \ S).filter fun a ↦ D.tail a = v).card +
        D.selectedIn S v := by
  classical
  have count_single (s : Finset A) (f : A → V) :
      (∑ a ∈ s, Finsupp.single (f a) 1) v = (s.filter fun a ↦ f a = v).card := by
    rw [Finset.card_eq_sum_ones]
    simp [Finsupp.single_apply]
  change
    (∑ a ∈ (Finset.univ : Finset A) \ S, Finsupp.single (D.tail a) 1) v +
        (∑ a ∈ S, Finsupp.single (D.head a) 1) v = _
  rw [count_single, count_single]
  rfl

/-- The elementary count splitting all outgoing arcs into selected and unselected ones. -/
theorem unselectedOut_add_selectedOut (S : Finset A) (v : V) :
    (((Finset.univ : Finset A) \ S).filter fun a ↦ D.tail a = v).card +
        D.selectedOut S v =
      ((Finset.univ : Finset A).filter fun a ↦ D.tail a = v).card := by
  classical
  rw [selectedOut]
  have hd : Disjoint
      (((Finset.univ : Finset A) \ S).filter fun a ↦ D.tail a = v)
      (S.filter fun a ↦ D.tail a = v) := by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
      true_and]
    aesop
  rw [← Finset.card_union_of_disjoint hd]
  congr 1
  ext a
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  tauto

/-- With exactly two outgoing arcs at every vertex, a term has central exponent exactly when
its chosen arc set is Eulerian. -/
theorem choiceExponent_eq_central_iff
    (hout : ∀ v, ((Finset.univ : Finset A).filter fun a ↦ D.tail a = v).card = 2)
    (S : Finset A) :
    D.choiceExponent S = D.centralExponent ↔ D.Balanced S := by
  classical
  constructor
  · intro h v
    have hv := DFunLike.congr_fun h v
    rw [D.choiceExponent_apply, D.centralExponent_apply] at hv
    have hsplit := D.unselectedOut_add_selectedOut S v
    rw [hout v] at hsplit
    omega
  · intro h
    ext v
    rw [D.choiceExponent_apply, D.centralExponent_apply, h v]
    exact D.unselectedOut_add_selectedOut S v |>.trans (hout v)

/-- Eulerian-subgraph interpretation of the central coefficient for a two-out-regular indexed
digraph.  This is equation (4.2) in the mathematical writeup. -/
theorem coeff_central_eq_signed_balanced
    (hout : ∀ v, ((Finset.univ : Finset A).filter fun a ↦ D.tail a = v).card = 2) :
    MvPolynomial.coeff D.centralExponent D.polynomial =
      ∑ S : Finset A, if D.Balanced S then ((-1 : ℤ) ^ S.card) else 0 := by
  classical
  rw [D.coeff_polynomial]
  simp only [Finset.powerset_univ, Finset.sum_const_zero, Finset.sum_ite_irrel]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [D.choiceExponent_eq_central_iff hout S]

/-- A modulo-four value of `2` immediately makes the central coefficient nonzero. -/
theorem coeff_central_ne_zero_of_modEq_two
    (h : MvPolynomial.coeff D.centralExponent D.polynomial ≡ 2 [ZMOD 4]) :
    MvPolynomial.coeff D.centralExponent D.polynomial ≠ 0 := by
  intro hz
  rw [hz] at h
  norm_num at h

end IndexedArcs

end Erdos842.Parity
