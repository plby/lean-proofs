/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.StructuredCount

/-!
# Erdős 360: a large common scale divides the target

An element of `primeStructuredTestSet n y U` has the form `u * q`, where
`u ∣ n`, `u ≤ U`, and `q` is prime.  If a positive integer `k` divides more
than `U` distinct elements of this set, then `k ∣ n`.

Indeed, if `k ∤ n`, prime factorization supplies a prime whose exponent in
`k` is larger than its exponent in `n`.  Since `u ∣ n`, divisibility of
`u * q` by `k` forces this prime to be `q`.  Thus all the prime quotients are
the same, and the elements are parametrized injectively by the at most `U`
possible positive values of `u`, a contradiction.
-/

namespace Erdos360

attribute [local instance] Classical.propDecidable

private theorem commonScale_dvd_target_of_large_factorized_set
    {n U k : ℕ} {X : Finset ℕ}
    (hsource : ∀ x ∈ X, ∃ u q : ℕ,
      u ∣ n ∧ n ≠ 0 ∧ u ≤ U ∧ q.Prime ∧ x = u * q)
    (hk : 0 < k) (hkX : ∀ x ∈ X, k ∣ x)
    (hcard : U < X.card) :
    k ∣ n := by
  have hXne : X.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hXe
    subst X
    simp at hcard
  obtain ⟨x0, hx0⟩ := hXne
  obtain ⟨_u0, _q0, _hu0n, hn, _hu0U, _hq0prime, _hx0⟩ :=
    hsource x0 hx0
  by_contra hkn
  have hnotFac :
      ¬ ∀ p : ℕ, p.Prime →
        k.factorization p ≤ n.factorization p := by
    intro hfac
    exact hkn ((Nat.factorization_prime_le_iff_dvd hk.ne' hn).mp hfac)
  push Not at hnotFac
  obtain ⟨p, hp, hpFac⟩ := hnotFac
  have hXimage :
      X ⊆ (Finset.Icc 1 U).image (fun u : ℕ ↦ u * p) := by
    intro x hx
    obtain ⟨u, q, hun, _hn, huU, hq, hxu⟩ := hsource x hx
    have hu : 0 < u :=
      Nat.pos_of_dvd_of_pos hun (Nat.pos_of_ne_zero hn)
    have hkuq : k ∣ u * q := by
      simpa [hxu] using hkX x hx
    have hkFac : k.factorization p ≤ (u * q).factorization p :=
      ((Nat.factorization_le_iff_dvd hk.ne'
        (Nat.mul_ne_zero hu.ne' hq.ne_zero)).mpr hkuq) p
    have huFac : u.factorization p ≤ n.factorization p :=
      ((Nat.factorization_le_iff_dvd hu.ne' hn).mpr hun) p
    rw [Nat.factorization_mul hu.ne' hq.ne_zero,
      Finsupp.add_apply] at hkFac
    have hqFac : q.factorization p ≠ 0 := by omega
    have hqp : q = p := hq.eq_of_factorization_pos hqFac
    apply Finset.mem_image.mpr
    refine ⟨u, Finset.mem_Icc.mpr ⟨hu, huU⟩, ?_⟩
    simpa [hqp] using hxu.symm
  have hcardUpper : X.card ≤ U := by
    calc
      X.card ≤ ((Finset.Icc 1 U).image (fun u : ℕ ↦ u * p)).card :=
        Finset.card_le_card hXimage
      _ ≤ (Finset.Icc 1 U).card := Finset.card_image_le
      _ = U := by simp
  omega

/-- If a positive common divisor divides more than `U` elements of the
prime-structured source, then it divides the target. -/
theorem commonScale_dvd_target_of_large_subset_primeStructuredTestSet
    {n y U k : ℕ} {X : Finset ℕ}
    (hX : X ⊆ primeStructuredTestSet n y U)
    (hk : 0 < k) (hkX : ∀ x ∈ X, k ∣ x)
    (hcard : U < X.card) :
    k ∣ n := by
  apply commonScale_dvd_target_of_large_factorized_set ?_ hk hkX hcard
  intro x hx
  obtain ⟨u, hun, hn, huU, q, _hyq, _hq2, hq, _hqn, hxu⟩ :=
    mem_primeStructuredTestSet.mp (hX hx)
  exact ⟨u, q, hun, hn, huU, hq, hxu⟩

#print axioms Erdos360.commonScale_dvd_target_of_large_subset_primeStructuredTestSet

end Erdos360
