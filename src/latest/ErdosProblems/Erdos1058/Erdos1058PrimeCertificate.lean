import Mathlib.NumberTheory.LucasPrimality

namespace Erdos1058

namespace PrimeGap210Certificate

/-- Binary modular exponentiation.  Unlike the ordinary monoid power, this
recurses on the binary digits of the exponent, so concrete certificate checks
remain within Lean's default recursion depth. -/
def binaryPowMod (a m n : ℕ) : ℕ :=
  Nat.binaryRec' (1 % m)
    (fun b _ _ r => if b then (r * r % m) * a % m else r * r % m) n

theorem binaryPowMod_eq_pow_mod (a m n : ℕ) :
    binaryPowMod a m n = a ^ n % m := by
  induction n using Nat.binaryRec' with
  | zero => simp [binaryPowMod]
  | bit b n h ih =>
      rw [binaryPowMod, Nat.binaryRec'_eq b n h]
      change (if b then (binaryPowMod a m n * binaryPowMod a m n % m) * a % m
        else binaryPowMod a m n * binaryPowMod a m n % m) = a ^ Nat.bit b n % m
      rw [ih]
      cases b <;>
        simp [Nat.bit_false, Nat.bit_true, ← Nat.mul_mod, pow_mul, pow_add, pow_two,
          mul_comm, mul_left_comm, mul_assoc]

/- A recursive Lucas--Pratt certificate and its list of prime factors. -/
mutual
  inductive PrimeCertificate where
    | two
    | lucas (p a : ℕ) (factors : PrimeFactorCertificates)

  inductive PrimeFactorCertificates where
    | nil
    | cons (head : PrimeCertificate) (tail : PrimeFactorCertificates)
end

open PrimeCertificate PrimeFactorCertificates

def PrimeCertificate.value : PrimeCertificate → ℕ
  | .two => 2
  | .lucas p _ _ => p

def PrimeFactorCertificates.product : PrimeFactorCertificates → ℕ
  | .nil => 1
  | .cons c cs => c.value * cs.product

def PrimeFactorCertificates.nontrivial (p a : ℕ) : PrimeFactorCertificates → Bool
  | .nil => true
  | .cons c cs =>
      decide (binaryPowMod a p ((p - 1) / c.value) ≠ 1) && cs.nontrivial p a

mutual
  def PrimeCertificate.check : PrimeCertificate → Bool
    | .two => true
    | .lucas p a fs =>
        decide (2 ≤ p) && decide (fs.product = p - 1) &&
          decide (binaryPowMod a p (p - 1) = 1) && fs.check && fs.nontrivial p a

  def PrimeFactorCertificates.check : PrimeFactorCertificates → Bool
    | .nil => true
    | .cons c cs => c.check && cs.check
end

lemma zmod_pow_eq_one_of_binaryPowMod_eq_one {p a e : ℕ}
    (h : binaryPowMod a p e = 1) : (a : ZMod p) ^ e = 1 := by
  have hmod : a ^ e % p = 1 := by
    rw [← binaryPowMod_eq_pow_mod]
    exact h
  have hcast := congrArg (fun x : ℕ => (x : ZMod p)) hmod
  simpa only [ZMod.natCast_mod, Nat.cast_pow, Nat.cast_one] using hcast

lemma zmod_pow_ne_one_of_binaryPowMod_ne_one {p a e : ℕ} (hp2 : 2 ≤ p)
    (h : binaryPowMod a p e ≠ 1) : (a : ZMod p) ^ e ≠ 1 := by
  have hmod : a ^ e % p ≠ 1 := by
    rw [← binaryPowMod_eq_pow_mod]
    exact h
  intro hz
  have hcasts : (((a ^ e : ℕ) : ZMod p)) = (((1 : ℕ) : ZMod p)) := by
    simpa only [Nat.cast_pow, Nat.cast_one] using hz
  have hmods : a ^ e % p = 1 % p :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcasts
  apply hmod
  simpa [Nat.mod_eq_of_lt (by omega : 1 < p)] using hmods

/- Soundness of the recursive Lucas--Pratt certificate checker. -/
mutual
  theorem PrimeCertificate.sound (c : PrimeCertificate) (hcheck : c.check = true) :
      c.value.Prime := by
    cases c with
    | two => exact Nat.prime_two
    | lucas p a fs =>
        simp only [PrimeCertificate.check, Bool.and_eq_true] at hcheck
        rcases hcheck with ⟨⟨⟨⟨hp2, hprod⟩, ha⟩, hfs⟩, hnon⟩
        have hp2' : 2 ≤ p := of_decide_eq_true hp2
        apply lucas_primality p (a : ZMod p)
        · exact zmod_pow_eq_one_of_binaryPowMod_eq_one (of_decide_eq_true ha)
        · intro q hq hqdiv
          have hqprod : q ∣ fs.product := by
            rw [of_decide_eq_true hprod]
            exact hqdiv
          exact fs.excludes p a hp2' hfs hnon q hq hqprod

  theorem PrimeFactorCertificates.excludes (fs : PrimeFactorCertificates)
      (p a : ℕ) (hp2 : 2 ≤ p)
      (hcheck : fs.check = true) (hnon : fs.nontrivial p a = true)
      (q : ℕ) (hq : q.Prime) (hqdiv : q ∣ fs.product) :
      ((a : ZMod p) ^ ((p - 1) / q)) ≠ 1 := by
    revert hcheck hnon q
    cases fs with
    | nil =>
        intro hcheck hnon q hq hqdiv
        simp only [PrimeFactorCertificates.product] at hqdiv
        exact (hq.not_dvd_one hqdiv).elim
    | cons c cs =>
        intro hcheck hnon q hq hqdiv
        simp only [PrimeFactorCertificates.check, Bool.and_eq_true] at hcheck
        simp only [PrimeFactorCertificates.nontrivial, Bool.and_eq_true] at hnon
        rw [PrimeFactorCertificates.product] at hqdiv
        rcases hq.dvd_mul.mp hqdiv with hqc | hqcs
        · have hcprime : c.value.Prime := c.sound hcheck.1
          have hqcEq : q = c.value :=
            (Nat.prime_dvd_prime_iff_eq hq hcprime).mp hqc
          subst q
          exact zmod_pow_ne_one_of_binaryPowMod_ne_one hp2
            (of_decide_eq_true hnon.1)
        · exact cs.excludes p a hp2 hcheck.2 hnon.2 q hq hqcs
end

lemma PrimeCertificate.forall_prime_of_all_check {cs : List PrimeCertificate}
    (hcheck : cs.all PrimeCertificate.check = true) :
    (cs.map PrimeCertificate.value).Forall Nat.Prime := by
  rw [List.forall_iff_forall_mem]
  intro p hp
  rw [List.mem_map] at hp
  obtain ⟨c, hc, rfl⟩ := hp
  exact c.sound ((List.all_eq_true.mp hcheck) c hc)

end PrimeGap210Certificate

end Erdos1058
