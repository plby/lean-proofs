import ErdosProblems.Erdos796.CollisionCleaning
import Mathlib.Tactic

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Cross-compatibility of large-prime cofactor fibres

For an admissible set `A`, attach to a large prime `q` the cofactors `u ≤ R`
for which `q*u ∈ A`.  Distinct large primes give rectangular product
convolution at most two: every ordered cofactor representation injects into a
strict factor representation in `A`.
-/

namespace Erdos796

namespace SmoothFiberCross

/-- Cofactors supported on `[1,R]` whose `q`-multiple belongs to `A`. -/
def cofactorFiber (A : Finset ℕ) (R q : ℕ) : Finset ℕ :=
  (positiveIcc R).filter fun u => q * u ∈ A

@[simp]
theorem mem_cofactorFiber {A : Finset ℕ} {R q u : ℕ} :
    u ∈ cofactorFiber A R q ↔ u ∈ positiveIcc R ∧ q * u ∈ A := by
  simp [cofactorFiber]

theorem cofactorFiber_subset (A : Finset ℕ) (R q : ℕ) :
    cofactorFiber A R q ⊆ positiveIcc R :=
  Finset.filter_subset _ _

/-- Two distinct primes larger than all positive cofactors cannot exchange
their cofactor multiples. -/
theorem prime_mul_cofactor_ne
    {R q Q u v : ℕ} (hq : q.Prime) (hQ : Q.Prime) (hneq : q ≠ Q)
    (hqR : R < q) (_hu : u ∈ positiveIcc R) (hv : v ∈ positiveIcc R) :
    q * u ≠ Q * v := by
  intro heq
  have hqdvd : q ∣ Q * v := by
    rw [← heq]
    exact dvd_mul_right q u
  rcases hq.dvd_or_dvd hqdvd with hqQ | hqv
  · exact hneq ((Nat.prime_dvd_prime_iff_eq hq hQ).mp hqQ)
  · have hvPos : 0 < v := (mem_positiveIcc.mp hv).1
    have hqvle : q ≤ v := Nat.le_of_dvd hvPos hqv
    have hvR : v ≤ R := (mem_positiveIcc.mp hv).2
    omega

/-- Put an unequal pair into the strict order used by
`strictProductRepCount`. -/
def strictOrder (a b : ℕ) : ℕ × ℕ :=
  if a < b then (a, b) else (b, a)

theorem strictOrder_mem_strict_product
    {A : Finset ℕ} {a b M : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (hne : a ≠ b) (hprod : a * b = M) :
    strictOrder a b ∈
      (A ×ˢ A).filter (fun xy => xy.1 < xy.2 ∧ xy.1 * xy.2 = M) := by
  by_cases hab : a < b
  · simp [strictOrder, hab, ha, hb, hprod]
  · have hba : b < a := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hab) hne.symm
    simp [strictOrder, hab, ha, hb, hba, Nat.mul_comm, hprod]

/-- Equality of strictly ordered versions gives equality of the underlying
unordered pairs. -/
theorem strictOrder_eq_imp {a b c d : ℕ}
    (h : strictOrder a b = strictOrder c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  by_cases hablt : a < b <;> by_cases hcdlt : c < d
  · have h' : a = c ∧ b = d := by
      simpa [strictOrder, hablt, hcdlt, Prod.ext_iff] using h
    exact Or.inl h'
  · have h' : a = d ∧ b = c := by
      simpa [strictOrder, hablt, hcdlt, Prod.ext_iff] using h
    exact Or.inr h'
  · have h' : b = c ∧ a = d := by
      simpa [strictOrder, hablt, hcdlt, Prod.ext_iff] using h
    exact Or.inr ⟨h'.2, h'.1⟩
  · have h' : b = d ∧ a = c := by
      simpa [strictOrder, hablt, hcdlt, Prod.ext_iff] using h
    exact Or.inl ⟨h'.2, h'.1⟩

/-- The map from an ordered cofactor pair to its corresponding strict pair of
members of `A`. -/
def representationMap (q Q : ℕ) (uv : ℕ × ℕ) : ℕ × ℕ :=
  strictOrder (q * uv.1) (Q * uv.2)

/-- Every ordered cofactor solution produces a strict representation of the
same enlarged product. -/
theorem representationMap_mem
    {A : Finset ℕ} {R q Q m : ℕ}
    (hq : q.Prime) (hQ : Q.Prime) (hneq : q ≠ Q)
    (hqR : R < q) {uv : ℕ × ℕ}
    (huv : uv ∈
      ((cofactorFiber A R q ×ˢ cofactorFiber A R Q).filter
        fun uv => uv.1 * uv.2 = m)) :
    representationMap q Q uv ∈
      ((A ×ˢ A).filter fun xy =>
        xy.1 < xy.2 ∧ xy.1 * xy.2 = q * Q * m) := by
  have huv' := Finset.mem_filter.mp huv
  have hmem := Finset.mem_product.mp huv'.1
  have hu := mem_cofactorFiber.mp hmem.1
  have hv := mem_cofactorFiber.mp hmem.2
  apply strictOrder_mem_strict_product hu.2 hv.2
  · exact prime_mul_cofactor_ne hq hQ hneq hqR hu.1 hv.1
  · calc
      (q * uv.1) * (Q * uv.2) = q * Q * (uv.1 * uv.2) := by ring
      _ = q * Q * m := by rw [huv'.2]

/-- Distinct ordered cofactor solutions remain distinct after strict
orientation. -/
theorem representationMap_injective_on
    {A : Finset ℕ} {R q Q m : ℕ}
    (hq : q.Prime) (hQ : Q.Prime) (hneq : q ≠ Q)
    (hqR : R < q) :
    Set.InjOn (representationMap q Q)
      (((cofactorFiber A R q ×ˢ cofactorFiber A R Q).filter
        fun uv => uv.1 * uv.2 = m) : Set (ℕ × ℕ)) := by
  intro uv huv xy hxy heq
  have huv' := Finset.mem_filter.mp huv
  have hxy' := Finset.mem_filter.mp hxy
  have huvMem := Finset.mem_product.mp huv'.1
  have hxyMem := Finset.mem_product.mp hxy'.1
  have hu := (mem_cofactorFiber.mp huvMem.1).1
  have hv := (mem_cofactorFiber.mp huvMem.2).1
  have hx := (mem_cofactorFiber.mp hxyMem.1).1
  have hy := (mem_cofactorFiber.mp hxyMem.2).1
  have hquv : q * uv.1 ≠ Q * uv.2 :=
    prime_mul_cofactor_ne hq hQ hneq hqR hu hv
  have hqxy : q * xy.1 ≠ Q * xy.2 :=
    prime_mul_cofactor_ne hq hQ hneq hqR hx hy
  have hunordered := strictOrder_eq_imp heq
  rcases hunordered with hsame | hswap
  · apply Prod.ext
    · exact Nat.eq_of_mul_eq_mul_left hq.pos hsame.1
    · exact Nat.eq_of_mul_eq_mul_left hQ.pos hsame.2
  · exfalso
    exact prime_mul_cofactor_ne hq hQ hneq hqR hu hy hswap.1

/-- Rectangular cofactor convolution injects into strict representations in
`A`. -/
theorem productRepCount_cofactorFiber_le_strict
    {A : Finset ℕ} {R q Q m : ℕ}
    (hq : q.Prime) (hQ : Q.Prime) (hneq : q ≠ Q)
    (hqR : R < q) :
    productRepCount (cofactorFiber A R q) (cofactorFiber A R Q) m ≤
      strictProductRepCount A (q * Q * m) := by
  let S := ((cofactorFiber A R q ×ˢ cofactorFiber A R Q).filter
    fun uv => uv.1 * uv.2 = m)
  let P := ((A ×ˢ A).filter fun xy =>
    xy.1 < xy.2 ∧ xy.1 * xy.2 = q * Q * m)
  have hmap : S.image (representationMap q Q) ⊆ P := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨uv, huv, rfl⟩
    exact representationMap_mem hq hQ hneq hqR huv
  calc
    productRepCount (cofactorFiber A R q) (cofactorFiber A R Q) m = S.card := rfl
    _ = (S.image (representationMap q Q)).card := by
      symm
      apply Finset.card_image_of_injOn
      exact representationMap_injective_on hq hQ hneq hqR
    _ ≤ P.card := Finset.card_le_card hmap
    _ = strictProductRepCount A (q * Q * m) := rfl

/-- Distinct large-prime fibres of an admissible set are cross-compatible. -/
theorem cofactorFibers_crossCompatibleOn
    {n R : ℕ} {A Qs : Finset ℕ}
    (hA : Admissible n A)
    (hprime : ∀ q ∈ Qs, q.Prime)
    (hlarge : ∀ q ∈ Qs, R < q) :
    CollisionCleaning.CrossCompatibleOn Qs (cofactorFiber A R) := by
  intro q hq Q hQ hneq m
  exact (productRepCount_cofactorFiber_le_strict
    (hprime q hq) (hprime Q hQ) hneq (hlarge q hq)).trans
      (hA.2 (q * Q * m))

/-- Applying finite collision cleaning to the cofactor fibres gives a family
which is compatible also on each individual fibre, at total cost at most
`R⁴`. -/
theorem exists_cleaned_cofactorFibers
    {n R : ℕ} {A Qs : Finset ℕ}
    (hA : Admissible n A)
    (hprime : ∀ q ∈ Qs, q.Prime)
    (hlarge : ∀ q ∈ Qs, R < q) :
    ∃ S : ℕ → Finset ℕ,
      (∀ q ∈ Qs, S q ⊆ cofactorFiber A R q) ∧
      (∀ i ∈ Qs, ∀ j ∈ Qs, ∀ m : ℕ,
        productRepCount (S i) (S j) m ≤ 2) ∧
      (∑ q ∈ Qs,
        ((cofactorFiber A R q).card - (S q).card) ≤ R ^ 4) := by
  apply CollisionCleaning.exists_compatible_cleaning
  · intro q _
    exact cofactorFiber_subset A R q
  · exact cofactorFibers_crossCompatibleOn hA hprime hlarge

end SmoothFiberCross

end Erdos796
