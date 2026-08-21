import ErdosProblems.Erdos239.External.Erdos67.CharacterTransport
import ErdosProblems.Erdos239.External.Erdos67.EulerResidue

/-!
# Patching the bad prime coordinates of a Dirichlet character

A Dirichlet character vanishes at the primes dividing its level, whereas
the Euler-product form of Halász's argument is most convenient for a
completely multiplicative coefficient of norm one at every positive
integer.  This file contains the dependency-light prime-coordinate patch
used by both Section 4 and the Halász argument.

The patch changes a character only at the finitely many primes dividing its
level, where its value is replaced by `1`.  The resulting prime assignment
therefore still takes values in the circle and has a canonical
zero-preserving completely multiplicative extension to all naturals.
-/

namespace Erdos67

noncomputable section

/-- Extend circle-valued prime coordinates to a zero-preserving completely
multiplicative complex function. -/
def zeroPreservingPrimeExtension (z : PrimeAssignment) : ℕ →*₀ ℂ :=
  primeAssignmentMonoidWithZeroHom z

@[simp] theorem zeroPreservingPrimeExtension_apply_of_ne_zero
    (z : PrimeAssignment) {n : ℕ} (hn : n ≠ 0) :
    zeroPreservingPrimeExtension z n = (primeExtension z n : ℂ) := by
  exact primeAssignmentMonoidWithZeroHom_apply_of_ne_zero z hn

@[simp] theorem zeroPreservingPrimeExtension_apply_prime
    (z : PrimeAssignment) (p : PrimeNat) :
    zeroPreservingPrimeExtension z p = (z p : ℂ) := by
  exact primeAssignmentMonoidWithZeroHom_apply_prime z p

theorem zeroPreservingPrimeExtension_hasUnitNorm (z : PrimeAssignment) :
    EulerResidue.HasUnitNorm (zeroPreservingPrimeExtension z) := by
  intro n hn
  exact norm_primeAssignmentMonoidWithZeroHom_apply_of_ne_zero z hn

/-- Embed the prime factors of a level into the type of natural primes. -/
def primeFactorEmbedding (q : ℕ) : ↑q.primeFactors ↪ PrimeNat where
  toFun p := ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩
  inj' := by
    intro p r h
    apply Subtype.ext
    exact congrArg (fun x : PrimeNat ↦ (x : ℕ)) h

/-- The finite set of prime divisors of the supplied Dirichlet-character
level. -/
def levelPrimeFinset (q : ℕ) : Finset PrimeNat :=
  q.primeFactors.attach.map (primeFactorEmbedding q)

@[simp] theorem mem_levelPrimeFinset_iff
    {q : ℕ} (hq : q ≠ 0) (p : PrimeNat) :
    p ∈ levelPrimeFinset q ↔ (p : ℕ) ∣ q := by
  rw [levelPrimeFinset, Finset.mem_map]
  constructor
  · rintro ⟨r, _hr, hrp⟩
    have hrval : (r : ℕ) = (p : ℕ) :=
      congrArg (fun x : PrimeNat ↦ (x : ℕ)) hrp
    rw [← hrval]
    exact Nat.dvd_of_mem_primeFactors r.2
  · intro hpq
    have hpMem : (p : ℕ) ∈ q.primeFactors :=
      p.2.mem_primeFactors hpq hq
    refine ⟨⟨p, hpMem⟩, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    rfl

/-- Patch a Dirichlet character to the circle at primes dividing its level.
Away from those primes this is literally the original character. -/
def patchedDirichletPrimeAssignment {q : ℕ}
    (chi : DirichletCharacter ℂ q) : PrimeAssignment :=
  fun p ↦ if hpq : (p : ℕ) ∣ q then 1 else
    ⟨chi (p : ℕ), by
      change chi (p : ℕ) ∈ Metric.sphere 0 1
      apply mem_sphere_zero_iff_norm.2
      have hcop : Nat.Coprime (p : ℕ) q :=
        p.2.coprime_iff_not_dvd.mpr hpq
      have hu : IsUnit ((p : ℕ) : ZMod q) :=
        (ZMod.isUnit_iff_coprime (p : ℕ) q).2 hcop
      simpa only [hu.unit_spec] using chi.unit_norm_eq_one hu.unit⟩

@[simp] theorem patchedDirichletPrimeAssignment_of_dvd
    {q : ℕ} (chi : DirichletCharacter ℂ q) (p : PrimeNat)
    (hpq : (p : ℕ) ∣ q) :
    patchedDirichletPrimeAssignment chi p = 1 := by
  simp [patchedDirichletPrimeAssignment, hpq]

@[simp] theorem patchedDirichletPrimeAssignment_coe_of_dvd
    {q : ℕ} (chi : DirichletCharacter ℂ q) (p : PrimeNat)
    (hpq : (p : ℕ) ∣ q) :
    (patchedDirichletPrimeAssignment chi p : ℂ) = 1 := by
  simp [patchedDirichletPrimeAssignment, hpq]

@[simp] theorem patchedDirichletPrimeAssignment_coe_of_not_dvd
    {q : ℕ} (chi : DirichletCharacter ℂ q) (p : PrimeNat)
    (hpq : ¬ (p : ℕ) ∣ q) :
    (patchedDirichletPrimeAssignment chi p : ℂ) = chi (p : ℕ) := by
  simp [patchedDirichletPrimeAssignment, hpq]

end

end Erdos67
