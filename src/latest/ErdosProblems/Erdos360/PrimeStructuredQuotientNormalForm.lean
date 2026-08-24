/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.StructuredCount

/-!
# Normal form after extracting a divisor from the prime-structured source

An element of `primeStructuredTestSet n y U` has the form `u * q`, where
`u ∣ n` and `q` is a prime which does not divide `n`.  If a divisor `d ∣ n`
has been extracted from such elements, cancellation takes place entirely in
the target-divisor coordinate: `u = d * u'`, while the prime coordinate is
unchanged.  Thus every extracted quotient has the form `u' * q`.

This file records that invariant without imposing any cardinality or
diversity hypotheses on the extracted set.  The final two lemmas also retain
the small-prime coprimality needed by the modular stage.
-/

namespace Erdos360

attribute [local instance] Classical.propDecidable

/-- Exact factorization data inherited by one quotient of a
prime-structured source element after division by `d`. -/
structure PrimeStructuredQuotientNormalForm
    (n y U d z : ℕ) where
  /-- The target divisor before extraction. -/
  u : ℕ
  /-- The target-divisor coordinate after extraction. -/
  u' : ℕ
  /-- The prime coordinate, unchanged by extraction. -/
  q : ℕ
  u_dvd_target : u ∣ n
  target_ne_zero : n ≠ 0
  u_le_cutoff : u ≤ U
  quotient_lower : y / u < q
  quotient_upper : q ≤ 2 * (y / u)
  quotient_prime : q.Prime
  quotient_not_target_factor : q ∉ n.primeFactors
  u_eq_scale_mul : u = d * u'
  z_eq : z = u' * q

namespace PrimeStructuredQuotientNormalForm

variable {n y U d z : ℕ}

lemma u_pos (h : PrimeStructuredQuotientNormalForm n y U d z) :
    0 < h.u :=
  Nat.pos_of_dvd_of_pos h.u_dvd_target (Nat.pos_of_ne_zero h.target_ne_zero)

lemma reduced_dvd_target (h : PrimeStructuredQuotientNormalForm n y U d z) :
    h.u' ∣ n := by
  apply dvd_trans (show h.u' ∣ h.u from ?_) h.u_dvd_target
  exact ⟨d, by simpa [Nat.mul_comm] using h.u_eq_scale_mul⟩

lemma reduced_le_cutoff (h : PrimeStructuredQuotientNormalForm n y U d z) :
    h.u' ≤ U := by
  have hdiv : h.u' ∣ h.u :=
    ⟨d, by simpa [Nat.mul_comm] using h.u_eq_scale_mul⟩
  exact (Nat.le_of_dvd h.u_pos hdiv).trans h.u_le_cutoff

end PrimeStructuredQuotientNormalForm

/-- Dividing a prime-structured source element by an extracted scale which
divides the target leaves the prime coordinate untouched. -/
lemma primeStructured_quotient_normalForm
    {n y U d z : ℕ}
    (hdn : d ∣ n)
    (hz : d * z ∈ primeStructuredTestSet n y U) :
    Nonempty (PrimeStructuredQuotientNormalForm n y U d z) := by
  obtain ⟨u, hun, hn, huU, q, hyq, hq2, hqprime, hqnot, heq⟩ :=
    mem_primeStructuredTestSet.mp hz
  have hqndvd : ¬q ∣ n := by
    intro hqn
    exact hqnot (Nat.mem_primeFactors.mpr ⟨hqprime, hqn, hn⟩)
  have hqddvd : ¬q ∣ d := fun hqd ↦ hqndvd (hqd.trans hdn)
  have hqdz : q ∣ d * z := by
    rw [heq]
    exact dvd_mul_left q u
  have hqz : q ∣ z := (hqprime.dvd_mul.mp hqdz).resolve_left hqddvd
  obtain ⟨u', hu'⟩ := hqz
  have hdu : u = d * u' := by
    apply Nat.eq_of_mul_eq_mul_right hqprime.pos
    calc
      u * q = d * z := heq.symm
      _ = d * (q * u') := by rw [hu']
      _ = (d * u') * q := by ring
  refine ⟨
    { u := u
      u' := u'
      q := q
      u_dvd_target := hun
      target_ne_zero := hn
      u_le_cutoff := huU
      quotient_lower := hyq
      quotient_upper := hq2
      quotient_prime := hqprime
      quotient_not_target_factor := hqnot
      u_eq_scale_mul := hdu
      z_eq := ?_ }⟩
  simpa [Nat.mul_comm] using hu'

/-- Setwise version of `primeStructured_quotient_normalForm`, matching the
output interface of common-divisor extraction. -/
lemma primeStructured_extracted_set_normalForm
    {n y U d : ℕ} {W Z : Finset ℕ}
    (hdn : d ∣ n)
    (hW : W ⊆ primeStructuredTestSet n y U)
    (hscale : ∀ z ∈ Z, d * z ∈ W) :
    ∀ z ∈ Z, Nonempty (PrimeStructuredQuotientNormalForm n y U d z) := by
  intro z hz
  exact primeStructured_quotient_normalForm hdn (hW (hscale z hz))

/-- Under a uniform lower cutoff on the dyadic fibres, the retained prime
coordinate is larger than the last selected prime. -/
lemma PrimeStructuredQuotientNormalForm.primeAt_lt_quotient
    {n y U d z r : ℕ}
    (hU : 0 < U)
    (hcut : primeAt (r - 1) ≤ y / U)
    (h : PrimeStructuredQuotientNormalForm n y U d z) :
    primeAt (r - 1) < h.q := by
  have hu : 0 < h.u := h.u_pos
  have hscale : y / U ≤ y / h.u :=
    Nat.div_le_div_left h.u_le_cutoff hu
  exact (hcut.trans hscale).trans_lt h.quotient_lower

/-- A divisor below a cutoff smaller than the retained prime coordinate can
only divide the reduced target-divisor coordinate.  This is the dynamic
`e ≤ B`, `e ∣ z` invariant used by the adaptive modular argument. -/
lemma PrimeStructuredQuotientNormalForm.small_dvd_reduced
    {n y U d z B e : ℕ}
    (h : PrimeStructuredQuotientNormalForm n y U d z)
    (hBq : B < h.q) (heB : e ≤ B) (hez : e ∣ z) :
    e ∣ h.u' := by
  have hqne : ¬h.q ∣ e := by
    intro hqe
    have hu' : 0 < h.u' := by
      have hu := h.u_pos
      rw [h.u_eq_scale_mul] at hu
      exact Nat.pos_of_mul_pos_left hu
    have hzpos : 0 < z := by
      rw [h.z_eq]
      exact Nat.mul_pos hu' h.quotient_prime.pos
    have hepos : 0 < e := Nat.pos_of_dvd_of_pos hez hzpos
    have hqle : h.q ≤ e := Nat.le_of_dvd hepos hqe
    omega
  have heq : Nat.Coprime e h.q :=
    (h.quotient_prime.coprime_iff_not_dvd.mpr hqne).symm
  apply heq.dvd_of_dvd_mul_right
  simpa only [h.z_eq] using hez

/-- Prime-cutoff specialization of `small_dvd_reduced`. -/
lemma PrimeStructuredQuotientNormalForm.small_dvd_reduced_of_primeAt
    {n y U d z r e : ℕ}
    (hU : 0 < U)
    (hcut : primeAt (r - 1) ≤ y / U)
    (h : PrimeStructuredQuotientNormalForm n y U d z)
    (he : e ≤ primeAt (r - 1)) (hez : e ∣ z) :
    e ∣ h.u' :=
  h.small_dvd_reduced (h.primeAt_lt_quotient hU hcut) he hez

/-- The unchanged prime coordinate is coprime to the product of all missing
primes up to the selected cutoff. -/
lemma PrimeStructuredQuotientNormalForm.quotient_coprime_missingPrimeProduct
    {n y U d z r : ℕ}
    (hU : 0 < U)
    (hcut : primeAt (r - 1) ≤ y / U)
    (h : PrimeStructuredQuotientNormalForm n y U d z) :
    Nat.Coprime h.q (missingPrimeProduct n (primeAt (r - 1))) := by
  apply Nat.Coprime.of_dvd_right
      (missingPrimeProduct_dvd_primorial n (primeAt (r - 1)))
  rw [h.quotient_prime.coprime_iff_not_dvd]
  intro hqdvd
  have hqle : h.q ≤ primeAt (r - 1) :=
    h.quotient_prime.dvd_primorial_iff.mp hqdvd
  exact (Nat.not_lt_of_ge hqle) (h.primeAt_lt_quotient hU hcut)

/-- Every extracted quotient is a unit modulo the complete missing-prime
product below the cutoff: its reduced target-divisor coordinate divides
`n`, and its prime coordinate lies strictly above the cutoff. -/
lemma PrimeStructuredQuotientNormalForm.coprime_missingPrimeProduct
    {n y U d z r : ℕ}
    (hU : 0 < U)
    (hcut : primeAt (r - 1) ≤ y / U)
    (h : PrimeStructuredQuotientNormalForm n y U d z) :
    Nat.Coprime (missingPrimeProduct n (primeAt (r - 1))) z := by
  have hred : Nat.Coprime
      (missingPrimeProduct n (primeAt (r - 1))) h.u' :=
    Nat.Coprime.of_dvd_right h.reduced_dvd_target
      (missingPrimeProduct_coprime_target n (primeAt (r - 1)))
  have hprime : Nat.Coprime
      (missingPrimeProduct n (primeAt (r - 1))) h.q :=
    (h.quotient_coprime_missingPrimeProduct hU hcut).symm
  rw [h.z_eq]
  exact hred.mul_right hprime

/-- Extraction-facing setwise coprimality statement. -/
lemma primeStructured_extracted_set_coprime_missingPrimeProduct
    {n y U d r : ℕ} {W Z : Finset ℕ}
    (hU : 0 < U)
    (hcut : primeAt (r - 1) ≤ y / U)
    (hdn : d ∣ n)
    (hW : W ⊆ primeStructuredTestSet n y U)
    (hscale : ∀ z ∈ Z, d * z ∈ W) :
    ∀ z ∈ Z,
      Nat.Coprime (missingPrimeProduct n (primeAt (r - 1))) z := by
  intro z hz
  let h := Classical.choice
    (primeStructured_extracted_set_normalForm hdn hW hscale z hz)
  exact h.coprime_missingPrimeProduct hU hcut

/-- Cutoff-value form of the preceding coprimality theorem.  It avoids
rounding a numerical cutoff to a prime index: every retained prime
coordinate is strictly larger than any `B ≤ y/U`. -/
lemma primeStructured_extracted_set_coprime_missingPrimeProduct_le_cutoff
    {n y U d B : ℕ} {W Z : Finset ℕ}
    (hU : 0 < U) (hB : B ≤ y / U)
    (hdn : d ∣ n)
    (hW : W ⊆ primeStructuredTestSet n y U)
    (hscale : ∀ z ∈ Z, d * z ∈ W) :
    ∀ z ∈ Z, Nat.Coprime (missingPrimeProduct n B) z := by
  intro z hz
  let h := Classical.choice
    (primeStructured_extracted_set_normalForm hdn hW hscale z hz)
  have hUpos : 0 < h.u := h.u_pos
  have hBU : B ≤ y / h.u :=
    hB.trans (Nat.div_le_div_left h.u_le_cutoff hUpos)
  have hBq : B < h.q := hBU.trans_lt h.quotient_lower
  have hred : Nat.Coprime (missingPrimeProduct n B) h.u' :=
    Nat.Coprime.of_dvd_right h.reduced_dvd_target
      (missingPrimeProduct_coprime_target n B)
  have hprime : Nat.Coprime (missingPrimeProduct n B) h.q := by
    apply Nat.Coprime.of_dvd_left
      (missingPrimeProduct_dvd_primorial n B)
    rw [Nat.coprime_comm, h.quotient_prime.coprime_iff_not_dvd]
    intro hqprimorial
    have hqle : h.q ≤ B :=
      h.quotient_prime.dvd_primorial_iff.mp hqprimorial
    omega
  rw [h.z_eq]
  exact hred.mul_right hprime

end Erdos360

#print axioms Erdos360.primeStructured_quotient_normalForm
#print axioms Erdos360.primeStructured_extracted_set_coprime_missingPrimeProduct
