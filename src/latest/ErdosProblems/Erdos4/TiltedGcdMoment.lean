import ErdosProblems.Erdos4.TiltedDivisorTail

/-! The averaged gcd tilt is bounded using only finite divisor probabilities. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

theorem squarefree_divisor_bound {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (G : Ω → ℕ) (S : Finset ℕ) (hG : ∀ o, Squarefree (G o))
    (hprime : ∀ p ∈ S, p.Prime) {X : ℕ} {D a : ℝ}
    (hcount : ∀ d, Squarefree d → 1 < d → d ≤ X → d.primeFactors ⊆ S →
      μ.prob (fun o => d ∣ G o) ≤ D * a ^ d.primeFactors.card / (d : ℝ) ^ 2) :
    DivisorBound μ S (fun o => (G o).primeFactors) X D a := by
  classical
  intro T hTS hTne hTX
  have hprimes : ∀ p ∈ T, p.Prime := fun p hp => hprime p ((Finset.mem_powerset.mp hTS) hp)
  let d := ∏ p ∈ T, p
  have hd : Squarefree d := prime_product_squarefree T hprimes
  have hd1 : 1 < d := by
    obtain ⟨p, hp⟩ := hTne
    have hpd : p ∣ d := Finset.dvd_prod_of_mem (fun p : ℕ => p) hp
    exact (hprimes p hp).one_lt.trans_le (Nat.le_of_dvd hd.ne_zero.bot_lt hpd)
  have heq : (fun o => T ⊆ (G o).primeFactors) = (fun o => d ∣ G o) := by
    funext o
    exact propext (prime_product_dvd_iff hprimes (hG o).ne_zero).symm
  rw [heq]
  have hfactor : d.primeFactors = T := Nat.primeFactors_prod hprimes
  have hc := hcount d hd hd1 hTX (by rw [hfactor]; exact Finset.mem_powerset.mp hTS)
  rw [hfactor] at hc
  have hw : (∏ p ∈ T, (a / (p : ℝ) ^ 2)) = a ^ T.card / (d : ℝ) ^ 2 := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.prod_pow, ← Nat.cast_prod]
  rw [hw]
  simpa only [mul_div_assoc] using hc

theorem squarefree_tilt_moment {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (G : Ω → ℕ) (S : Finset ℕ) {W R X N : ℕ}
    (hW : 0 < W) (hR : 1 ≤ R) (hRX : R * R ≤ X)
    (hS : ∀ p ∈ S, p.Prime ∧ W < p ∧ p ≤ X)
    (hG : ∀ o, Squarefree (G o)) (hfactors : ∀ o, (G o).primeFactors ⊆ S)
    (hsize : ∀ o, G o ≤ N) {τ D a : ℝ}
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) (hD : 0 ≤ D) (ha : 0 ≤ a)
    (hcount : ∀ d, Squarefree d → 1 < d → d ≤ X → d.primeFactors ⊆ S →
      μ.prob (fun o => d ∣ G o) ≤ D * a ^ d.primeFactors.card / (d : ℝ) ^ 2) :
    μ.mean (fun o => (G o : ℝ) ^ τ) ≤
      1 + D * (Real.exp (2 * a * (W : ℝ) ^ (-(1 / 2 : ℝ))) - 1) +
        (N : ℝ) ^ τ * (D * (a / R + (R : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.exp (2 * a * (W : ℝ) ^ (-(1 / 2 : ℝ))))) := by
  have hbound := squarefree_divisor_bound μ G S hG (fun p hp => (hS p hp).1) hcount
  have hX : 1 ≤ X := by nlinarith
  have hm := product_moment_with_tail μ S (fun o => (G o).primeFactors) hW hX
    (fun p hp => (hS p hp).2.1) hfactors
    (fun o => by simpa only [Nat.prod_primeFactors_of_squarefree (hG o)] using hsize o)
    hτ0 hτ hD ha hbound
  have ht := divisor_product_tail μ S (fun o => (G o).primeFactors) hW hR hRX
    (fun p hp => (hS p hp).2) hfactors hD ha hbound
  simp only [Nat.prod_primeFactors_of_squarefree (hG _)] at hm ht
  exact hm.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ht
    (Real.rpow_nonneg (Nat.cast_nonneg N) τ)))

end Erdos4.Tilted
