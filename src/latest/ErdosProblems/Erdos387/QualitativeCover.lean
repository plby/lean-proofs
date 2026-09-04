/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.CoverAlgebra
import ErdosProblems.Erdos387.CoverBPZPrelude

/-!
# The unconditional fixed-parameter cover

The quantitative BNPZ theorem needs a cover whose weight grows with `k` and
whose constants are uniform in `k`.  Erdős Problem 387 itself only needs a
counterexample for each *fixed* endpoint.  The axiom-free covering lemma in
`CoverLemma.lean` is therefore already strong enough: after fixing the weight
`m`, it supplies arbitrarily large `k` and an exact absorber factorization on
an infinite arithmetic progression.

This file records that qualitative interface separately from the stronger
uniform cover in `CoverBPZConditional.lean`.
-/

namespace Erdos387.CoverBPZ

/-- For every fixed weight `m ≥ 3` and every lower bound on `k`, the
unconditional covering lemma supplies a valid absorber cover.  In particular,
the covering factors are all at least `m`, multiply to `k!`, and the residual
linear factors are pairwise coprime throughout the resulting progression. -/
theorem exists_absorberCoverValid_above (m K : ℕ) (hm : 3 ≤ m) :
    ∃ k : ℕ, K ≤ k ∧ 3 ≤ k ∧ Nonempty (AbsorberCoverValid m k) := by
  obtain ⟨k, hkK, hk3, ⟨cert⟩⟩ :=
    exists_residue_certificate_above m K hm
  exact ⟨k, hkK, hk3,
    absorber_cover_from_cert m k (le_trans (by norm_num) hk3) cert⟩

namespace AbsorberCoverValid

/-- Restrict an absorber progression to parameters divisible by a positive
integer `Q`.  If `Q` has no prime factor above `k`, all validity properties
are preserved. -/
noncomputable def rescale {m k : ℕ} (C : AbsorberCoverValid m k)
    (Q : ℕ) (hQpos : 0 < Q)
    (hQsmooth : ∀ p : ℕ, p.Prime → p ∣ Q → p ≤ k) :
    AbsorberCoverValid m k := by
  let C' : AbsorberCover m k :=
    { N₀ := C.toAbsorberCover.N₀
      Mk := C.toAbsorberCover.Mk * Q
      Mk_pos := Nat.mul_pos C.toAbsorberCover.Mk_pos hQpos
      B := C.toAbsorberCover.B
      B_ge_m := C.toAbsorberCover.B_ge_m
      prod_B_eq_factorial := C.toAbsorberCover.prod_B_eq_factorial }
  refine
    { toAbsorberCover := C'
      L_div := ?_
      N_pos := ?_
      binom_eq := ?_
      pairwise_coprime := ?_
      k_lt_N_toNat := ?_
      Mk_smooth := ?_
      B_dvd_Mk := ?_ }
  · intro n j
    simpa [C', AbsorberCover.N, mul_assoc] using C.L_div (Q * n) j
  · intro n
    simpa [C', AbsorberCover.N, mul_assoc] using C.N_pos (Q * n)
  · intro n
    simpa [C', AbsorberCover.N, AbsorberCover.L, mul_assoc] using
      C.binom_eq (Q * n)
  · intro n i j hij
    simpa [C', AbsorberCover.N, AbsorberCover.L, mul_assoc] using
      C.pairwise_coprime (Q * n) i j hij
  · intro n
    simpa [C', AbsorberCover.N, mul_assoc] using C.k_lt_N_toNat (Q * n)
  · intro p hp hpd
    rcases hp.dvd_mul.mp hpd with hpM | hpQ
    · exact C.Mk_smooth p hp hpM
    · exact hQsmooth p hp hpQ
  · intro j
    exact (C.B_dvd_Mk j).trans (Nat.dvd_mul_right _ Q)

/-- Restrict to the affine subprogression `t = t₀ + Q u`.  This is the form
needed to freeze the finitely many small-prime valuations of all residual
linear factors. -/
noncomputable def affineRescale {m k : ℕ} (C : AbsorberCoverValid m k)
    (t₀ Q : ℕ) (hQpos : 0 < Q)
    (hQsmooth : ∀ p : ℕ, p.Prime → p ∣ Q → p ≤ k) :
    AbsorberCoverValid m k := by
  let C' : AbsorberCover m k :=
    { N₀ := C.toAbsorberCover.N t₀
      Mk := C.toAbsorberCover.Mk * Q
      Mk_pos := Nat.mul_pos C.toAbsorberCover.Mk_pos hQpos
      B := C.toAbsorberCover.B
      B_ge_m := C.toAbsorberCover.B_ge_m
      prod_B_eq_factorial := C.toAbsorberCover.prod_B_eq_factorial }
  have hN (u : ℕ) :
      C'.N u = C.toAbsorberCover.N (t₀ + Q * u) := by
    simp [C', AbsorberCover.N]
    ring
  refine
    { toAbsorberCover := C'
      L_div := ?_
      N_pos := ?_
      binom_eq := ?_
      pairwise_coprime := ?_
      k_lt_N_toNat := ?_
      Mk_smooth := ?_
      B_dvd_Mk := ?_ }
  · intro u j
    rw [hN]
    exact C.L_div (t₀ + Q * u) j
  · intro u
    rw [hN]
    exact C.N_pos (t₀ + Q * u)
  · intro u
    simpa [AbsorberCover.L, hN] using C.binom_eq (t₀ + Q * u)
  · intro u i j hij
    simpa [AbsorberCover.L, hN] using
      C.pairwise_coprime (t₀ + Q * u) i j hij
  · intro u
    rw [hN]
    exact C.k_lt_N_toNat (t₀ + Q * u)
  · intro p hp hpd
    rcases hp.dvd_mul.mp hpd with hpM | hpQ
    · exact C.Mk_smooth p hp hpM
    · exact hQsmooth p hp hpQ
  · intro j
    exact (C.B_dvd_Mk j).trans (Nat.dvd_mul_right _ Q)

/-- Natural value of the arithmetic progression supplied by an absorber
cover. -/
def nNat {m k : ℕ} (C : AbsorberCoverValid m k) (t : ℕ) : ℕ :=
  (C.toAbsorberCover.N t).toNat

/-- The positive natural residual factor indexed by `j`. -/
def residual {m k : ℕ} (C : AbsorberCoverValid m k)
    (t : ℕ) (j : Fin k) : ℕ :=
  (C.toAbsorberCover.L t j).toNat

@[simp] theorem rescale_nNat {m k : ℕ} (C : AbsorberCoverValid m k)
    (Q : ℕ) (hQpos : 0 < Q)
    (hQsmooth : ∀ p : ℕ, p.Prime → p ∣ Q → p ≤ k) (t : ℕ) :
    (C.rescale Q hQpos hQsmooth).nNat t = C.nNat (Q * t) := by
  simp [nNat, rescale, AbsorberCover.N, mul_assoc]

@[simp] theorem affineRescale_nNat {m k : ℕ} (C : AbsorberCoverValid m k)
    (t₀ Q : ℕ) (hQpos : 0 < Q)
    (hQsmooth : ∀ p : ℕ, p.Prime → p ∣ Q → p ≤ k) (u : ℕ) :
    (C.affineRescale t₀ Q hQpos hQsmooth).nNat u =
      C.nNat (t₀ + Q * u) := by
  simp [nNat, affineRescale, AbsorberCover.N]
  ring_nf

@[simp] theorem rescale_residual {m k : ℕ} (C : AbsorberCoverValid m k)
    (Q : ℕ) (hQpos : 0 < Q)
    (hQsmooth : ∀ p : ℕ, p.Prime → p ∣ Q → p ≤ k)
    (t : ℕ) (j : Fin k) :
    (C.rescale Q hQpos hQsmooth).residual t j =
      C.residual (Q * t) j := by
  simp [residual, rescale, AbsorberCover.L, AbsorberCover.N, mul_assoc]

@[simp] theorem affineRescale_residual {m k : ℕ}
    (C : AbsorberCoverValid m k) (t₀ Q : ℕ) (hQpos : 0 < Q)
    (hQsmooth : ∀ p : ℕ, p.Prime → p ∣ Q → p ≤ k)
    (u : ℕ) (j : Fin k) :
    (C.affineRescale t₀ Q hQpos hQsmooth).residual u j =
      C.residual (t₀ + Q * u) j := by
  simp [residual, affineRescale, AbsorberCover.L, AbsorberCover.N]
  ring_nf

theorem nNat_cast {m k : ℕ} (C : AbsorberCoverValid m k) (t : ℕ) :
    (C.nNat t : ℤ) = C.toAbsorberCover.N t := by
  unfold nNat
  exact Int.toNat_of_nonneg (C.N_pos t).le

theorem k_lt_nNat {m k : ℕ} (C : AbsorberCoverValid m k) (t : ℕ) :
    k < C.nNat t := C.k_lt_N_toNat t

theorem residual_int_pos {m k : ℕ} (C : AbsorberCoverValid m k)
    (t : ℕ) (j : Fin k) :
    0 < C.toAbsorberCover.L t j := by
  have hBnat : 0 < C.toAbsorberCover.B j :=
    Erdos387.CoverBPZ.B_pos C.toAbsorberCover j
  have hB : (0 : ℤ) < C.toAbsorberCover.B j := by
    exact_mod_cast hBnat
  have hNcast := C.nNat_cast t
  have hkn := C.k_lt_nNat t
  have hnum : (0 : ℤ) <
      C.toAbsorberCover.N t - (k : ℤ) + (j.val + 1 : ℤ) := by
    rw [← hNcast]
    have hknz : (k : ℤ) < (C.nNat t : ℤ) := by exact_mod_cast hkn
    have hjz : (0 : ℤ) < (j.val + 1 : ℕ) := by exact_mod_cast Nat.succ_pos j.val
    omega
  have hmul := Int.ediv_mul_cancel (C.L_div t j)
  change C.toAbsorberCover.L t j *
      (C.toAbsorberCover.B j : ℤ) =
        C.toAbsorberCover.N t - (k : ℤ) + (j.val + 1 : ℤ) at hmul
  nlinarith

theorem residual_cast {m k : ℕ} (C : AbsorberCoverValid m k)
    (t : ℕ) (j : Fin k) :
    (C.residual t j : ℤ) = C.toAbsorberCover.L t j := by
  unfold residual
  exact Int.toNat_of_nonneg (C.residual_int_pos t j).le

/-- Exact natural affine formula for each residual factor. -/
theorem residual_add_mul {m k : ℕ} (C : AbsorberCoverValid m k)
    (t₀ Q u : ℕ) (j : Fin k) :
    C.residual (t₀ + Q * u) j = C.residual t₀ j +
      (C.toAbsorberCover.Mk / C.toAbsorberCover.B j) * Q * u := by
  let M := C.toAbsorberCover.Mk
  let B := C.toAbsorberCover.B j
  have hBpos : 0 < B := Erdos387.CoverBPZ.B_pos C.toAbsorberCover j
  have hBne : (B : ℤ) ≠ 0 := by exact_mod_cast hBpos.ne'
  have hBM : B ∣ M := C.B_dvd_Mk j
  have hsecondNat :
      (M * (Q * u)) / B = (M / B) * Q * u := by
    calc
      (M * (Q * u)) / B = ((Q * u) * M) / B := by rw [mul_comm]
      _ = (Q * u) * (M / B) := Nat.mul_div_assoc _ hBM
      _ = (M / B) * Q * u := by ring
  have hsecondInt :
      ((M : ℤ) * ((Q : ℤ) * u)) / B =
        (((M / B) * Q * u : ℕ) : ℤ) := by
    have hcast : (((M * (Q * u)) / B : ℕ) : ℤ) =
        (((M / B) * Q * u : ℕ) : ℤ) := by exact_mod_cast hsecondNat
    rw [← hcast]
    push_cast
    exact (Int.natCast_div (M * (Q * u)) B).symm
  have hdiv : (B : ℤ) ∣ (M : ℤ) * ((Q : ℤ) * u) := by
    exact (by exact_mod_cast hBM : (B : ℤ) ∣ (M : ℤ)).mul_right _
  have hL :
      C.toAbsorberCover.L (t₀ + Q * u) j =
        C.toAbsorberCover.L t₀ j + (((M / B) * Q * u : ℕ) : ℤ) := by
    unfold AbsorberCover.L AbsorberCover.N
    change
      (C.toAbsorberCover.N₀ + (M : ℤ) * (t₀ + Q * u) - k + (j.val + 1)) /
          B =
        (C.toAbsorberCover.N₀ + (M : ℤ) * t₀ - k + (j.val + 1)) / B + _
    rw [show C.toAbsorberCover.N₀ + (M : ℤ) * (t₀ + Q * u) - k +
          (j.val + 1) =
        (C.toAbsorberCover.N₀ + (M : ℤ) * t₀ - k + (j.val + 1)) +
          (M : ℤ) * ((Q : ℤ) * u) by push_cast; ring]
    rw [Int.add_ediv_of_dvd_right hdiv, hsecondInt]
  apply Int.ofNat_inj.mp
  push_cast
  rw [C.residual_cast, C.residual_cast, hL]
  push_cast
  rfl

/-- Adding a multiple of one power beyond the exact `p`-adic valuation does
not change that valuation. -/
theorem factorization_add_eq_of_pow_succ_dvd
    {p r delta : ℕ} (hp : p.Prime) (hr : 0 < r)
    (hdelta : p ^ (r.factorization p + 1) ∣ delta) :
    (r + delta).factorization p = r.factorization p := by
  let v := r.factorization p
  have hvDvdR : p ^ v ∣ r := Nat.ordProj_dvd r p
  have hvDvdSucc : p ^ v ∣ p ^ (v + 1) := pow_dvd_pow p (by omega)
  have hvDvdDelta : p ^ v ∣ delta := hvDvdSucc.trans hdelta
  have hvDvdSum : p ^ v ∣ r + delta := dvd_add hvDvdR hvDvdDelta
  have hsumPos : 0 < r + delta := by omega
  have hlo : v ≤ (r + delta).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hsumPos.ne').mp hvDvdSum
  have hnotR : ¬p ^ (v + 1) ∣ r := by
    intro h
    have := (Nat.Prime.pow_dvd_iff_le_factorization hp hr.ne').mp h
    simp [v] at this
  have hnotSum : ¬p ^ (v + 1) ∣ r + delta := by
    intro hsum
    exact hnotR ((Nat.dvd_add_iff_right hdelta).mpr
      (by simpa [add_comm] using hsum))
  have hhi : (r + delta).factorization p < v + 1 := by
    by_contra h
    exact hnotSum ((Nat.Prime.pow_dvd_iff_le_factorization hp hsumPos.ne').mpr
      (Nat.le_of_not_gt h))
  omega

/-- A deliberately oversized exponent dominating the valuations of every
residual at the base point. -/
def freezeExponent {m k : ℕ} (C : AbsorberCoverValid m k) (t₀ : ℕ) : ℕ :=
  ∏ j : Fin k, C.residual t₀ j

/-- Smooth modulus used to freeze all primes at most `k`. -/
def freezeModulus {m k : ℕ} (C : AbsorberCoverValid m k) (t₀ : ℕ) : ℕ :=
  k.factorial ^ C.freezeExponent t₀

theorem freezeExponent_pos {m k : ℕ} (C : AbsorberCoverValid m k)
    (t₀ : ℕ) : 0 < C.freezeExponent t₀ := by
  unfold freezeExponent
  apply Finset.prod_pos
  intro j _
  have h := C.residual_int_pos t₀ j
  unfold residual
  omega

theorem freezeModulus_pos {m k : ℕ} (C : AbsorberCoverValid m k)
    (t₀ : ℕ) : 0 < C.freezeModulus t₀ := by
  unfold freezeModulus
  positivity

theorem freezeModulus_smooth {m k : ℕ} (C : AbsorberCoverValid m k)
    (t₀ : ℕ) (p : ℕ) (hp : p.Prime) (hpd : p ∣ C.freezeModulus t₀) :
    p ≤ k := by
  apply hp.dvd_factorial.mp
  exact hp.dvd_of_dvd_pow (by simpa [freezeModulus] using hpd)

theorem pow_factorization_succ_dvd_freezeModulus
    {m k : ℕ} (C : AbsorberCoverValid m k) (t₀ : ℕ)
    (j : Fin k) {p : ℕ} (hp : p.Prime) (hpk : p ≤ k) :
    p ^ ((C.residual t₀ j).factorization p + 1) ∣ C.freezeModulus t₀ := by
  let r := C.residual t₀ j
  let R := C.freezeExponent t₀
  have hr : 0 < r := by
    have h := C.residual_int_pos t₀ j
    unfold r residual
    omega
  have hR : 0 < R := C.freezeExponent_pos t₀
  have hrDvdR : r ∣ R := by
    unfold R freezeExponent
    exact Finset.dvd_prod_of_mem (fun i => C.residual t₀ i) (Finset.mem_univ j)
  have hvr : r.factorization p + 1 ≤ r := by
    have := Nat.factorization_lt p hr.ne'
    omega
  have hrR : r ≤ R := Nat.le_of_dvd hR hrDvdR
  have hvR : r.factorization p + 1 ≤ R := hvr.trans hrR
  have hpFact : p ∣ k.factorial := hp.dvd_factorial.mpr hpk
  unfold freezeModulus
  exact pow_dvd_pow_of_dvd_of_le hpFact hvR

/-- On the affine subprogression with the freeze modulus, every valuation at
a prime `p ≤ k` is exactly its base-point valuation. -/
theorem factorization_residual_affine_frozen
    {m k : ℕ} (C : AbsorberCoverValid m k) (t₀ u : ℕ)
    (j : Fin k) {p : ℕ} (hp : p.Prime) (hpk : p ≤ k) :
    (C.residual (t₀ + C.freezeModulus t₀ * u) j).factorization p =
      (C.residual t₀ j).factorization p := by
  let delta :=
    (C.toAbsorberCover.Mk / C.toAbsorberCover.B j) *
      C.freezeModulus t₀ * u
  have hdelta : p ^ ((C.residual t₀ j).factorization p + 1) ∣ delta := by
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right
        (C.pow_factorization_succ_dvd_freezeModulus t₀ j hp hpk) _ ) _
  rw [C.residual_add_mul t₀ (C.freezeModulus t₀) u j]
  apply factorization_add_eq_of_pow_succ_dvd hp
  · have h := C.residual_int_pos t₀ j
    unfold residual
    omega
  · exact hdelta

/-- The canonical affine subcover on which every small-prime valuation is
frozen. -/
noncomputable def frozen {m k : ℕ} (C : AbsorberCoverValid m k)
    (t₀ : ℕ) : AbsorberCoverValid m k :=
  C.affineRescale t₀ (C.freezeModulus t₀) (C.freezeModulus_pos t₀)
    (C.freezeModulus_smooth t₀)

@[simp] theorem frozen_nNat {m k : ℕ} (C : AbsorberCoverValid m k)
    (t₀ u : ℕ) :
    (C.frozen t₀).nNat u = C.nNat (t₀ + C.freezeModulus t₀ * u) := by
  simp [frozen]

@[simp] theorem frozen_residual {m k : ℕ} (C : AbsorberCoverValid m k)
    (t₀ u : ℕ) (j : Fin k) :
    (C.frozen t₀).residual u j =
      C.residual (t₀ + C.freezeModulus t₀ * u) j := by
  simp [frozen]

theorem frozen_residual_factorization_smallPrime
    {m k : ℕ} (C : AbsorberCoverValid m k) (t₀ u : ℕ)
    (j : Fin k) {p : ℕ} (hp : p.Prime) (hpk : p ≤ k) :
    ((C.frozen t₀).residual u j).factorization p =
      (C.residual t₀ j).factorization p := by
  rw [C.frozen_residual]
  exact C.factorization_residual_affine_frozen t₀ u j hp hpk

theorem residual_pos {m k : ℕ} (C : AbsorberCoverValid m k)
    (t : ℕ) (j : Fin k) : 0 < C.residual t j := by
  have h := C.residual_int_pos t j
  unfold residual
  omega

/-- Product of the prime-power factors of `n` supported on primes at most
`k`. -/
noncomputable def smallPrimePart (k n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p ≤ k), p ^ n.factorization p

/-- Complementary product supported on primes greater than `k`. -/
noncomputable def largePrimePart (k n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => ¬p ≤ k), p ^ n.factorization p

theorem smallPrimePart_mul_largePrimePart {k n : ℕ} (hn : n ≠ 0) :
    smallPrimePart k n * largePrimePart k n = n := by
  unfold smallPrimePart largePrimePart
  rw [Finset.prod_filter_mul_prod_filter_not]
  exact (Nat.prod_primeFactors_pow_factorization hn).symm

theorem smallPrimePart_dvd {k n : ℕ} (hn : n ≠ 0) :
    smallPrimePart k n ∣ n := by
  exact ⟨largePrimePart k n, (smallPrimePart_mul_largePrimePart hn).symm⟩

theorem largePrimePart_dvd {k n : ℕ} (hn : n ≠ 0) :
    largePrimePart k n ∣ n := by
  refine ⟨smallPrimePart k n, ?_⟩
  simpa [mul_comm] using (smallPrimePart_mul_largePrimePart hn).symm

theorem smallPrimePart_pos {k n : ℕ} (hn : 0 < n) :
    0 < smallPrimePart k n := by
  have hprod := smallPrimePart_mul_largePrimePart (k := k) hn.ne'
  by_contra hzero
  have : smallPrimePart k n = 0 := Nat.eq_zero_of_not_pos hzero
  rw [this, zero_mul] at hprod
  omega

theorem largePrimePart_pos {k n : ℕ} (hn : 0 < n) :
    0 < largePrimePart k n := by
  have hprod := smallPrimePart_mul_largePrimePart (k := k) hn.ne'
  by_contra hzero
  have : largePrimePart k n = 0 := Nat.eq_zero_of_not_pos hzero
  rw [this, mul_zero] at hprod
  omega

/-- Every prime divisor of the large-prime part is strictly larger than the
cutoff used to define that part. -/
theorem lt_of_prime_dvd_largePrimePart {k n p : ℕ} (hp : p.Prime)
    (hpd : p ∣ largePrimePart k n) : k < p := by
  unfold largePrimePart at hpd
  obtain ⟨q, hq, hpqpow⟩ :=
    (hp.prime.dvd_finsetProd_iff
      (fun q => q ^ n.factorization q)).mp hpd
  obtain ⟨hqFactor, hqLarge⟩ := Finset.mem_filter.mp hq
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hqFactor
  have hpq : p ∣ q := hp.dvd_of_dvd_pow hpqpow
  have hpEq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqPrime).mp hpq
  subst q
  exact Nat.lt_of_not_ge hqLarge

/-- The small-prime part of every frozen residual is literally constant. -/
theorem smallPrimePart_frozen_residual
    {m k : ℕ} (C : AbsorberCoverValid m k) (t₀ u : ℕ) (j : Fin k) :
    smallPrimePart k ((C.frozen t₀).residual u j) =
      smallPrimePart k (C.residual t₀ j) := by
  let n₁ := (C.frozen t₀).residual u j
  let n₀ := C.residual t₀ j
  have hn₁ : 0 < n₁ := (C.frozen t₀).residual_pos u j
  have hn₀ : 0 < n₀ := C.residual_pos t₀ j
  have hfac (p : ℕ) (hp : p.Prime) (hpk : p ≤ k) :
      n₁.factorization p = n₀.factorization p := by
    exact C.frozen_residual_factorization_smallPrime t₀ u j hp hpk
  have hsets :
      n₁.primeFactors.filter (fun p => p ≤ k) =
        n₀.primeFactors.filter (fun p => p ≤ k) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp₁, hpk⟩
      have hpPrime := Nat.prime_of_mem_primeFactors hp₁
      have hpDvd := Nat.dvd_of_mem_primeFactors hp₁
      have hpos := hpPrime.factorization_pos_of_dvd hn₁.ne' hpDvd
      rw [hfac p hpPrime hpk] at hpos
      have hpDvd₀ : p ∣ n₀ := by
        by_contra hnot
        rw [Nat.factorization_eq_zero_of_not_dvd hnot] at hpos
        omega
      exact ⟨hpPrime.mem_primeFactors hpDvd₀ hn₀.ne', hpk⟩
    · rintro ⟨hp₀, hpk⟩
      have hpPrime := Nat.prime_of_mem_primeFactors hp₀
      have hpDvd := Nat.dvd_of_mem_primeFactors hp₀
      have hpos := hpPrime.factorization_pos_of_dvd hn₀.ne' hpDvd
      rw [← hfac p hpPrime hpk] at hpos
      have hpDvd₁ : p ∣ n₁ := by
        by_contra hnot
        rw [Nat.factorization_eq_zero_of_not_dvd hnot] at hpos
        omega
      exact ⟨hpPrime.mem_primeFactors hpDvd₁ hn₁.ne', hpk⟩
  unfold smallPrimePart
  rw [show ((C.frozen t₀).residual u j) = n₁ by rfl,
    show C.residual t₀ j = n₀ by rfl, hsets]
  apply Finset.prod_congr rfl
  intro p hp
  exact congrArg (fun e => p ^ e)
    (hfac p (Nat.prime_of_mem_primeFactors
      ((Finset.mem_filter.mp hp).1)) (Finset.mem_filter.mp hp).2)

/-- Canonical factorization of a frozen residual into its fixed small-prime
part and its varying complementary part. -/
theorem frozen_residual_eq_smallPrimePart_mul_largePrimePart
    {m k : ℕ} (C : AbsorberCoverValid m k) (t₀ u : ℕ) (j : Fin k) :
    (C.frozen t₀).residual u j =
      smallPrimePart k (C.residual t₀ j) *
        largePrimePart k ((C.frozen t₀).residual u j) := by
  rw [← C.smallPrimePart_frozen_residual t₀ u j]
  exact (smallPrimePart_mul_largePrimePart
    ((C.frozen t₀).residual_pos u j).ne').symm

/-- Multiplying a natural residual by its covering factor recovers the
corresponding falling-factorial term. -/
theorem residual_mul_B {m k : ℕ} (C : AbsorberCoverValid m k)
    (t : ℕ) (j : Fin k) :
    C.residual t j * C.toAbsorberCover.B j =
      C.nNat t - k + (j.val + 1) := by
  have hkn : k ≤ C.nNat t := (C.k_lt_nNat t).le
  have hmulInt := Int.ediv_mul_cancel (C.L_div t j)
  change C.toAbsorberCover.L t j *
      (C.toAbsorberCover.B j : ℤ) =
        C.toAbsorberCover.N t - (k : ℤ) + (j.val + 1 : ℤ) at hmulInt
  have hmulCast :
      ((C.residual t j * C.toAbsorberCover.B j : ℕ) : ℤ) =
        ((C.nNat t - k + (j.val + 1) : ℕ) : ℤ) := by
    rw [Nat.cast_mul, C.residual_cast, Nat.cast_add,
      Nat.cast_sub hkn, C.nNat_cast]
    push_cast
    exact hmulInt
  exact Int.ofNat_inj.mp hmulCast

/-- The natural binomial coefficient is exactly the product of the positive
residual factors. -/
theorem choose_eq_prod_residual {m k : ℕ}
    (C : AbsorberCoverValid m k) (t : ℕ) :
    (C.nNat t).choose k = ∏ j : Fin k, C.residual t j := by
  have hbin := C.binom_eq t
  have hprod :
      (((∏ j : Fin k, C.residual t j : ℕ) : ℕ) : ℤ) =
        ∏ j : Fin k, C.toAbsorberCover.L t j := by
    push_cast
    apply Finset.prod_congr rfl
    intro j hj
    exact C.residual_cast t j
  have hcast : (((C.nNat t).choose k : ℕ) : ℤ) =
      ((∏ j : Fin k, C.residual t j : ℕ) : ℤ) := by
    exact hbin.trans hprod.symm
  exact_mod_cast hcast

theorem residual_dvd_choose {m k : ℕ}
    (C : AbsorberCoverValid m k) (t : ℕ) (j : Fin k) :
    C.residual t j ∣ (C.nNat t).choose k := by
  rw [C.choose_eq_prod_residual]
  exact Finset.dvd_prod_of_mem
    (fun i : Fin k => C.residual t i) (Finset.mem_univ j)

/-- Residual factors at different shifts are pairwise coprime. -/
theorem residual_coprime {m k : ℕ} (C : AbsorberCoverValid m k)
    (t : ℕ) (i j : Fin k) (hij : i ≠ j) :
    Nat.Coprime (C.residual t i) (C.residual t j) := by
  have h := C.pairwise_coprime t i j hij
  rw [Int.gcd_def, ← C.residual_cast t i, ← C.residual_cast t j,
    Int.natAbs_natCast, Int.natAbs_natCast] at h
  exact h

/-- Every residual factor is at most the progression value divided by the
fixed cover weight. -/
theorem residual_le_div {m k : ℕ} (C : AbsorberCoverValid m k)
    (hm : 0 < m) (t : ℕ) (j : Fin k) :
    C.residual t j ≤ C.nNat t / m := by
  have hBnat : 0 < C.toAbsorberCover.B j :=
    Erdos387.CoverBPZ.B_pos C.toAbsorberCover j
  have hkn : k ≤ C.nNat t := (C.k_lt_nNat t).le
  apply (Nat.le_div_iff_mul_le hm).2
  calc
    C.residual t j * m ≤
        C.residual t j * C.toAbsorberCover.B j := by
      gcongr
      exact C.toAbsorberCover.B_ge_m j
    _ = C.nNat t - k + (j.val + 1) := C.residual_mul_B t j
    _ ≤ C.nNat t := by omega

/-- Reindexing the absorber factors in descending-factorial order produces
the repository's generic `CoverFactorization` interface. -/
noncomputable def toCoverFactorization {m k : ℕ}
    (C : AbsorberCoverValid m k) (t : ℕ) :
    Erdos387.CoverFactorization (C.nNat t) k := by
  let g : ℕ → ℕ := fun i =>
    if hi : i < k then C.toAbsorberCover.B (Fin.rev ⟨i, hi⟩) else 1
  refine
    { g := g
      divides_term := ?_
      product_eq_factorial := ?_ }
  · intro i hi
    have hmul := C.residual_mul_B t (Fin.rev ⟨i, hi⟩)
    have hterm :
        C.nNat t - k + ((Fin.rev ⟨i, hi⟩).val + 1) =
          C.nNat t - i := by
      have hkn := C.k_lt_nNat t
      simp only [Fin.val_rev]
      omega
    rw [hterm] at hmul
    refine ⟨C.residual t (Fin.rev ⟨i, hi⟩), ?_⟩
    simpa [g, hi, mul_comm] using hmul.symm
  · calc
      ∏ i ∈ Finset.range k, g i = ∏ i : Fin k, g i := by
        exact (Fin.prod_univ_eq_prod_range g k).symm
      _ = ∏ i : Fin k, C.toAbsorberCover.B (Fin.rev i) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [g]
      _ = ∏ i : Fin k, C.toAbsorberCover.B i := by
        exact Fintype.prod_equiv (Fin.revPerm : Equiv.Perm (Fin k))
          (fun i : Fin k => C.toAbsorberCover.B (Fin.rev i))
          C.toAbsorberCover.B (fun _ => rfl)
      _ = k.factorial := C.toAbsorberCover.prod_B_eq_factorial

/-- The generic cover quotient is exactly the correspondingly reversed
absorber residual. -/
theorem coverQuotient_eq_residual {m k : ℕ}
    (C : AbsorberCoverValid m k) (t : ℕ) (i : Fin k) :
    (C.nNat t - (i : ℕ)) / (C.toCoverFactorization t).g i =
      C.residual t (Fin.rev i) := by
  have hBpos : 0 < C.toAbsorberCover.B (Fin.rev i) :=
    Erdos387.CoverBPZ.B_pos C.toAbsorberCover (Fin.rev i)
  have hmul := C.residual_mul_B t (Fin.rev i)
  have hterm :
      C.nNat t - k + ((Fin.rev i).val + 1) =
        C.nNat t - (i : ℕ) := by
    have hkn := C.k_lt_nNat t
    simp only [Fin.val_rev]
    omega
  rw [hterm] at hmul
  have hg : (C.toCoverFactorization t).g i =
      C.toAbsorberCover.B (Fin.rev i) := by
    simp [toCoverFactorization]
  rw [hg]
  exact Nat.div_eq_of_eq_mul_left hBpos (by simpa [mul_comm] using hmul.symm)

/-- The generic cover quotients inherited from an absorber remain pairwise
coprime. -/
theorem coverQuotients_pairwise_coprime {m k : ℕ}
    (C : AbsorberCoverValid m k) (t : ℕ) :
    ∀ i < k, ∀ j < k, i ≠ j →
      Nat.Coprime
        ((C.nNat t - i) / (C.toCoverFactorization t).g i)
        ((C.nNat t - j) / (C.toCoverFactorization t).g j) := by
  intro i hi j hj hij
  let i' : Fin k := ⟨i, hi⟩
  let j' : Fin k := ⟨j, hj⟩
  rw [show (C.nNat t - i) / (C.toCoverFactorization t).g i =
      C.residual t (Fin.rev i') by
        simpa [i'] using C.coverQuotient_eq_residual t i',
    show (C.nNat t - j) / (C.toCoverFactorization t).g j =
      C.residual t (Fin.rev j') by
        simpa [j'] using C.coverQuotient_eq_residual t j']
  apply C.residual_coprime t
  intro hrev
  have : i' = j' := Fin.rev_injective hrev
  exact hij (congrArg Fin.val this)

end AbsorberCoverValid

end Erdos387.CoverBPZ
