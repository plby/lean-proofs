import ErdosProblems.Erdos768.Defs
import ErdosProblems.Erdos768.SubsetProduct
import ErdosProblems.Erdos768.LargeSieveMult
import ErdosProblems.Erdos768.PNT

/- Ported to Lean/Mathlib 4.33.0; imports and proof elaboration adapted. -/
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Erdős Problem 768 — analytic inputs (Sections 2–3 of the paper)

These are the standard analytic-number-theory inputs used in the constructive
lower bound: the Bombieri–Davenport multiplicative large sieve, a
prime-number-theorem estimate for primes in short logarithmic intervals, and the
Fourier / subset-product second-moment lemma.

They are stated faithfully here.  The large sieve and the prime number theorem
with classical error term are deep external results (not currently available in
Mathlib in this quantitative form); they are recorded as the analytic hypotheses
of the paper.
-/

open scoped Classical BigOperators
open Finset Filter

namespace Erdos768

/-- **Theorem 2.6 (multiplicative large sieve, Bombieri–Davenport form).**
For complex numbers `a_n` and `N, Q ≥ 1`,
`∑_{q ≤ Q} (q/φ(q)) ∑*_{χ mod q} |∑_{n ≤ N} a_n χ(n)|² ≪ (N + Q²) ∑_{n ≤ N} |a_n|²`,
where the star restricts to primitive Dirichlet characters. -/
theorem multiplicative_large_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ (N Q : ℕ) (a : ℕ → ℂ),
      ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) / (Nat.totient q) *
          ∑ χ : DirichletCharacter ℂ q,
            (if DirichletCharacter.IsPrimitive χ then
              ‖∑ n ∈ Finset.Icc 1 N, a n * χ n‖ ^ 2 else 0)
        ≤ C * ((N : ℝ) + Q ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
  Erdos768LS.mult_large_sieve_final

/-- **Lemma 2.8 (primes in logarithmic intervals).**  If `u_n → ∞` and
`u_n^{-2} ≤ δ_n ≤ 1` (eventually), then, uniformly in this range,
`#{ p prime : e^{u-δ} < p ≤ e^u } = (1+o(1)) (1 - e^{-δ}) e^u / u`. -/
theorem primes_in_log_interval
    (u δ : ℕ → ℝ) (hu : Tendsto u atTop atTop)
    (hδ : ∀ᶠ n in atTop, (u n)⁻¹ ^ 2 ≤ δ n ∧ δ n ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        (((Finset.Icc 1 ⌊Real.exp (u n)⌋₊).filter
            (fun p => Nat.Prime p ∧ Real.exp (u n - δ n) < (p : ℝ))).card : ℝ)
          / ((1 - Real.exp (-(δ n))) * Real.exp (u n) / (u n)))
      atTop (nhds 1) :=
  primes_in_log_interval_proof u δ hu hδ

/-- **Lemma 3.1 (subset products hit the identity).**  Let `G` be a finite
abelian group and `X_1,…,X_m` independent `G`-valued random variables (with laws
`μ_j`).  If every nonprincipal Fourier coefficient is at most `ρ` and `mρ ≤ 1`,
then, writing `Λ = 2^m / |G|`, whenever `Λ ≥ Λ₀` the probability that no nonempty
subset product equals the identity is `≤ C₁/Λ`. -/
theorem subset_product_hits_identity :
    ∃ (Λ₀ C₁ : ℝ), 0 < Λ₀ ∧ 0 < C₁ ∧
      ∀ (G : Type) [AddCommGroup G] [Fintype G] (m : ℕ)
        (μ : Fin m → PMF G) (ρ : ℝ),
        (∀ j : Fin m, ∀ χ : AddChar G ℂ, χ ≠ 1 →
            ‖∑ g : G, (μ j g).toReal * χ g‖ ≤ ρ) →
        (m : ℝ) * ρ ≤ 1 →
        Λ₀ ≤ (2 : ℝ) ^ m / (Fintype.card G : ℝ) →
        (∑ ω : (Fin m → G),
            (∏ j, (μ j (ω j)).toReal) *
              (if ∀ J : Finset (Fin m), J.Nonempty → ∑ j ∈ J, ω j ≠ 0 then (1 : ℝ)
               else 0))
          ≤ C₁ * (Fintype.card G : ℝ) / (2 : ℝ) ^ m :=
  subset_product_core

end Erdos768
