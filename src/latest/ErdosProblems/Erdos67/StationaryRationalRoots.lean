import ErdosProblems.Erdos67.StationaryRootMassComparison

/-!
# Rational frequencies and their prime dilation roots

Primitive residues modulo `q` index exactly frequencies of order `q`.
For a prime coprime to `q`, all roots other than the unique order-`q` root
have order `pq`, making the extra fibers disjoint across distinct primes.
-/

open MeasureTheory

namespace Erdos67.StationaryModel

noncomputable def primitiveFrequency (q : ℕ+) (a : (ZMod q.val)ˣ) : FrequencyCircle :=
  ZMod.toAddCircle (a : ZMod q.val)

theorem primitiveFrequency_injective (q : ℕ+) : Function.Injective (primitiveFrequency q) := by
  intro a b hab
  apply Units.ext
  exact ZMod.toAddCircle_injective q.val hab

theorem primitiveFrequency_order (q : ℕ+) (a : (ZMod q.val)ˣ) :
    addOrderOf (primitiveFrequency q a) = q.val := by
  have ha := ZMod.val_coe_unit_coprime a
  have he := AddCircle.addOrderOf_div_of_gcd_eq_one (p := (1 : ℝ)) q.pos ha.gcd_eq_one
  simpa only [primitiveFrequency, ZMod.toAddCircle_apply, mul_one] using he

theorem coprime_nsmul_injective_on_torsion {G : Type*} [AddCommGroup G]
    (p q : ℕ) (hpq : Nat.Coprime p q) (x y : G)
    (hx : q • x = 0) (hy : q • y = 0) (hxy : p • x = p • y) : x = y := by
  have hp : p • (x - y) = 0 := by rw [nsmul_sub, hxy, sub_self]
  have hq : q • (x - y) = 0 := by rw [nsmul_sub, hx, hy, sub_self]
  have hd : addOrderOf (x - y) ∣ 1 := by
    rw [← hpq.gcd_eq_one]
    exact Nat.dvd_gcd (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hp)
      (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hq)
  have he := addOrderOf_dvd_iff_nsmul_eq_zero.mp hd
  simpa only [one_nsmul, sub_eq_zero] using he

theorem prime_root_order_cases {η θ : FrequencyCircle} {q p : ℕ}
    (hq : 0 < q) (hp : p.Prime) (hη : addOrderOf η = q) (hθ : p • θ = η) :
    addOrderOf θ = q ∨ addOrderOf θ = p * q := by
  have ht : IsOfFinAddOrder θ := by
    apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    refine ⟨p * q, Nat.mul_pos hp.pos hq, ?_⟩
    rw [mul_nsmul, hθ, ← hη, addOrderOf_nsmul_eq_zero]
  have ho := IsOfFinAddOrder.addOrderOf_nsmul θ p ht
  rw [hθ, hη] at ho
  rcases (Nat.dvd_prime hp).mp (Nat.gcd_dvd_right (addOrderOf θ) p) with hg | hg
  · rw [hg, Nat.div_one] at ho
    exact Or.inl ho.symm
  · rw [hg] at ho
    have hd : p ∣ addOrderOf θ := by
      rw [← hg]
      exact Nat.gcd_dvd_left _ _
    exact Or.inr ((Nat.eq_mul_of_div_eq_left hd ho.symm).trans (Nat.mul_comm q p))

theorem other_prime_root_order {η ξ θ : FrequencyCircle} {q p : ℕ}
    (hq : 0 < q) (hp : p.Prime) (hpq : Nat.Coprime p q)
    (hη : addOrderOf η = q) (hξ : addOrderOf ξ = q)
    (hroot : p • ξ = η) (hθ : p • θ = η) (hne : θ ≠ ξ) : addOrderOf θ = p * q := by
  rcases prime_root_order_cases hq hp hη hθ with he | he
  · apply False.elim
    apply hne
    apply coprime_nsmul_injective_on_torsion p q hpq θ ξ
    · rw [← he, addOrderOf_nsmul_eq_zero]
    · rw [← hξ, addOrderOf_nsmul_eq_zero]
    · exact hθ.trans hroot.symm
  · exact he

theorem prime_primitive_root (q : ℕ+) (p : ℕ) (hpq : Nat.Coprime p q.val)
    (a : (ZMod q.val)ˣ) :
    p • primitiveFrequency q ((ZMod.unitOfCoprime p hpq)⁻¹ * a) = primitiveFrequency q a := by
  unfold primitiveFrequency
  rw [← map_nsmul, nsmul_eq_mul, ← ZMod.coe_unitOfCoprime p hpq,
    ← Units.val_mul, mul_inv_cancel_left]

theorem other_primitive_prime_roots_order (q : ℕ+) (p : ℕ) (hp : p.Prime)
    (hpq : Nat.Coprime p q.val) (a : (ZMod q.val)ˣ) (θ : FrequencyCircle)
    (hθ : p • θ = primitiveFrequency q a)
    (hne : θ ≠ primitiveFrequency q ((ZMod.unitOfCoprime p hpq)⁻¹ * a)) :
    addOrderOf θ = p * q.val :=
  other_prime_root_order q.pos hp hpq (primitiveFrequency_order q a)
    (primitiveFrequency_order q _) (prime_primitive_root q p hpq a) hθ hne

end Erdos67.StationaryModel
