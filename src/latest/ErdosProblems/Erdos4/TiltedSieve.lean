import ErdosProblems.Erdos4.TiltedLaw
import ErdosProblems.Erdos4.RandomResidueSieve
import Mathlib.Data.Nat.Squarefree

/-!
# Exact tilted sieve probabilities

The preliminary choices are independent at the coordinate primes, but
survival of different integers is not assumed independent. In particular,
the squarefree one-point law is proved from the actual product measure.
-/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT RandomResidueSieve

variable {P : Type*} [Fintype P] [DecidableEq P]
  (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

noncomputable def sieveLaw (τ : ℝ) (hτ : 0 ≤ τ) :
    FiniteLaw (∀ l, ZMod (ell l)) where
  weight a := ∏ l, (residueLaw (ell l) (Fact.out : (ell l).Prime).two_le τ hτ).weight (a l)
  nonneg a := Finset.prod_nonneg (fun l _ =>
    (residueLaw (ell l) (Fact.out : (ell l).Prime).two_le τ hτ).nonneg (a l))
  total := Erdos4.assignmentWeight_sum _ (fun l =>
    (residueLaw (ell l) (Fact.out : (ell l).Prime).two_le τ hτ).total)

noncomputable def primeSurvival (τ : ℝ) : ℝ :=
  ∏ l, baseline (ell l) ((ell l : ℝ) ^ (-τ))

omit [DecidableEq P] in
theorem primeSurvival_pos (τ : ℝ) : 0 < primeSurvival ell τ := by
  apply Finset.prod_pos
  intro l _
  exact baseline_pos (Fact.out : (ell l).Prime).two_le
    (rpow_tilt_pos (Fact.out : (ell l).Prime).two_le τ).le

/-- Independent coordinates factor for arbitrary coordinate events. -/
theorem sieveLaw_prob_all (τ : ℝ) (hτ : 0 ≤ τ)
    (E : ∀ l, ZMod (ell l) → Prop) :
    (sieveLaw ell τ hτ).prob (fun a => ∀ l, E l (a l)) =
      ∏ l, (residueLaw (ell l) (Fact.out : (ell l).Prime).two_le τ hτ).prob
        (E l) := by
  classical
  simp only [FiniteLaw.prob, sieveLaw]
  convert Erdos4.independent_assignment_miss_mass
    (fun l => (residueLaw (ell l) (Fact.out : (ell l).Prime).two_le τ hτ).weight)
    E using 1
  · apply Finset.sum_congr rfl
    intro a _
    by_cases h : ∀ l, E l (a l) <;> simp [h]

/-- The exact independent-coordinate factorization for an arbitrary target set. -/
theorem sieveLaw_survival_product (τ : ℝ) (hτ : 0 ≤ τ) (T : Finset ℕ) :
    (sieveLaw ell τ hτ).prob (fun a => Survives ell a T) =
      ∏ l, (residueLaw (ell l) (Fact.out : (ell l).Prime).two_le τ hτ).prob
        (fun a => a ∉ residues ell T l) :=
  sieveLaw_prob_all ell τ hτ (fun l a => a ∉ residues ell T l)

theorem sieveLaw_singleton_pos (τ : ℝ) (hτ : 0 ≤ τ) (n : ℕ) :
    0 < (sieveLaw ell τ hτ).prob (fun a => Survives ell a {n}) := by
  rw [sieveLaw_survival_product]
  simp only [residues, Finset.image_singleton, Finset.mem_singleton]
  exact Finset.prod_pos (fun l _ =>
    residueLaw_survival_pos (ell l) (Fact.out : (ell l).Prime).two_le τ hτ n)

/-- Before squarefreeness is imposed, the tilt acts on distinct prime divisors. -/
theorem sieveLaw_singleton (τ : ℝ) (hτ : 0 ≤ τ) (n : ℕ) :
    (sieveLaw ell τ hτ).prob (fun a => Survives ell a {n}) =
      primeSurvival ell τ * ∏ l, if ell l ∣ n then (ell l : ℝ) ^ (-τ) else 1 := by
  rw [sieveLaw_survival_product]
  simp only [residues, Finset.image_singleton, Finset.mem_singleton]
  simp_rw [residueLaw_survival]
  rw [Finset.prod_mul_distrib]
  rfl

theorem sieveLaw_singleton_prime (τ : ℝ) (hτ : 0 ≤ τ) {q : ℕ}
    (hq : q.Prime) (hgreater : ∀ l, ell l < q) :
    (sieveLaw ell τ hτ).prob (fun a => Survives ell a {q}) = primeSurvival ell τ := by
  rw [sieveLaw_singleton]
  have hnot (l : P) : ¬ell l ∣ q := by
    intro hd
    have heq := (Nat.prime_dvd_prime_iff_eq (Fact.out : (ell l).Prime) hq).mp hd
    exact (ne_of_lt (hgreater l)) heq
  simp only [hnot, if_false, Finset.prod_const_one, mul_one]

omit [DecidableEq P] in
theorem divisor_tilt_product (hinj : Function.Injective ell) (τ : ℝ) {n : ℕ}
    (hn : n ≠ 0) (hcomplete : ∀ p ∈ n.primeFactors, ∃ l, ell l = p) :
    (∏ l, if ell l ∣ n then (ell l : ℝ) ^ (-τ) else 1) =
      ∏ p ∈ n.primeFactors, (p : ℝ) ^ (-τ) := by
  classical
  rw [← Finset.prod_filter]
  apply Finset.prod_bij (fun l _ => ell l)
  · intro l hl
    exact (Fact.out : (ell l).Prime).mem_primeFactors (Finset.mem_filter.mp hl).2 hn
  · intro l _ l' _ hll
    exact hinj hll
  · intro p hp
    obtain ⟨l, hl⟩ := hcomplete p hp
    refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, ?_⟩, hl⟩
    rw [hl]
    exact Nat.dvd_of_mem_primeFactors hp
  · intro l _
    rfl

theorem nat_prod_rpow (S : Finset ℕ) (τ : ℝ) :
    (∏ p ∈ S, (p : ℝ) ^ τ) = ((∏ p ∈ S, p : ℕ) : ℝ) ^ τ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    rw [Finset.prod_insert hp, Finset.prod_insert hp, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), ih]

/-- The exact squarefree survival law (3.7), with every prime factor represented. -/
theorem sieveLaw_squarefree (hinj : Function.Injective ell) (τ : ℝ) (hτ : 0 ≤ τ)
    {n : ℕ} (hn : Squarefree n)
    (hcomplete : ∀ p ∈ n.primeFactors, ∃ l, ell l = p) :
    (sieveLaw ell τ hτ).prob (fun a => Survives ell a {n}) =
      primeSurvival ell τ * (n : ℝ) ^ (-τ) := by
  rw [sieveLaw_singleton, divisor_tilt_product ell hinj τ hn.ne_zero hcomplete,
    nat_prod_rpow, Nat.prod_primeFactors_of_squarefree hn]

end Erdos4.Tilted
