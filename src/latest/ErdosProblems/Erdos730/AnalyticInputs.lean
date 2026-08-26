/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Erdős 730: exact analytic dependency surface

The fixed-depth proof uses two standard analytic-number-theory inputs which
are not both theorems in the pinned Mathlib release: Mertens' reciprocal-prime
asymptotic and the prime number theorem in each fixed arithmetic progression.
This file defines their exact qualitative surfaces and declares no axiom.

The ordinary qualitative PNT in AP is enough for the divisor-switching step:
the modulus is fixed, so convergence is uniform over its finitely many reduced
residue classes, and the weighted main terms have total order `Z`.
-/

open Filter Finset
open scoped Topology

namespace Erdos730.FullDensity

/-- Sum of reciprocal primes at most `N`. -/
noncomputable def reciprocalPrimeSum (N : ℕ) : ℝ :=
  ∑ p ∈ (range (N + 1)).filter Nat.Prime, (p : ℝ)⁻¹

/-- The integer specialization of a reciprocal-prime Mertens bound.  The
coefficient is fixed and positive; its numerical value is immaterial to the
uniform depth-tail argument. -/
def MertensReciprocalPrimeInput : Prop :=
  ∃ M C : ℝ, 0 < C ∧
    ∀ N : ℕ, 3 ≤ N →
      |reciprocalPrimeSum N - Real.log (Real.log N) - M| ≤
        C / Real.log N

/-- Number of primes at most `N` in the residue class `a mod A`. -/
def primeAPCount (A a N : ℕ) : ℕ :=
  ((range (N + 1)).filter fun p => p.Prime ∧ p % A = a % A).card

/-- Qualitative prime number theorem in the reduced residue classes of one
specified fixed modulus.  No zero-free-region error term is required by the
cleaned proof. -/
def PNTAPInputAtModulus (A : ℕ) : Prop :=
  0 < A ∧ ∀ a : ℕ, a < A → a.Coprime A →
    Tendsto
      (fun N : ℕ =>
        (primeAPCount A a N : ℝ) /
          ((N : ℝ) / Real.log N))
      atTop (𝓝 ((Nat.totient A : ℝ)⁻¹))

/-- Exactly the three fixed moduli occurring in the proof: ordinary prime
counting and the two divisor-switching moduli.  This deliberately does not
assume PNT-AP uniformly over arbitrary moduli. -/
def RequiredFixedModulusPNTAPInput : Prop :=
  PNTAPInputAtModulus 1 ∧
    PNTAPInputAtModulus 222138 ∧
      PNTAPInputAtModulus 148092

/-- The single explicit external analytic closure required by the candidate
proof.  This is a conjunction of two independently classical theorems, not an
assumption of strength equivalent to Erdős #730. -/
def RequiredAnalyticInputs : Prop :=
  MertensReciprocalPrimeInput ∧ RequiredFixedModulusPNTAPInput

theorem requiredAnalyticInputs_iff :
    RequiredAnalyticInputs ↔
      MertensReciprocalPrimeInput ∧
        PNTAPInputAtModulus 1 ∧
          PNTAPInputAtModulus 222138 ∧
            PNTAPInputAtModulus 148092 := by
  rfl

#print axioms requiredAnalyticInputs_iff

end Erdos730.FullDensity
