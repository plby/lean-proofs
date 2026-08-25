import Util.TaoTeravainen.ModulusLift

/-!
# Tao--Teräväinen: prime-power residue transforms

The existing Erdős 248 development adjoins one prime divisibility condition
to a Maynard weight. Here the same CRT residue is formed with a prime power.
The transformed Y-variable still depends only on the underlying prime; the
higher exponent is carried entirely by the lifted outer modulus.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace TaoTeravainen

local instance primePowerTransformDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The simultaneous CRT residue extending a residue modulo W by the
condition p^a ∣ n + k. -/
def extendPrimePowerEventResidue {W p : ℕ} (hcop : Nat.Coprime W p)
    (a v k : ℕ) : ℕ :=
  Nat.chineseRemainder (hcop.pow_right a) v
    (negativeShiftResidue (p ^ a) k)

/-- Characterization of the prime-power CRT residue. -/
theorem modEq_extendPrimePowerEventResidue_iff
    {W p a v k n : ℕ} (hp : 0 < p) (ha : 0 < a)
    (hcop : Nat.Coprime W p) :
    n ≡ extendPrimePowerEventResidue hcop a v k [MOD W * p ^ a] ↔
      n ≡ v [MOD W] ∧ p ^ a ∣ n + k := by
  have hpa : 0 < p ^ a := pow_pos hp _
  constructor
  · intro hn
    have hnW := hn.of_dvd (dvd_mul_right W (p ^ a))
    have hnp := hn.of_dvd (dvd_mul_left (p ^ a) W)
    have hresW : extendPrimePowerEventResidue hcop a v k ≡ v [MOD W] :=
      (Nat.chineseRemainder (hcop.pow_right a) v
        (negativeShiftResidue (p ^ a) k)).property.1
    have hresp : extendPrimePowerEventResidue hcop a v k ≡
        negativeShiftResidue (p ^ a) k [MOD p ^ a] :=
      (Nat.chineseRemainder (hcop.pow_right a) v
        (negativeShiftResidue (p ^ a) k)).property.2
    exact ⟨hnW.trans hresW,
      (modEq_negativeShiftResidue_iff_dvd_add
        (p ^ a) k n hpa).mp (hnp.trans hresp)⟩
  · rintro ⟨hnW, hpk⟩
    have hnp : n ≡ negativeShiftResidue (p ^ a) k [MOD p ^ a] :=
      (modEq_negativeShiftResidue_iff_dvd_add
        (p ^ a) k n hpa).mpr hpk
    exact Nat.chineseRemainder_modEq_unique (hcop.pow_right a) hnW hnp

/-- A prime-power residue refines the corresponding one-prime residue. -/
theorem modEq_primePower_iff_primeResidue_and_dvd
    {W p a v k n : ℕ} (hp : 0 < p) (ha : 0 < a)
    (hcop : Nat.Coprime W p) :
    n ≡ extendPrimePowerEventResidue hcop a v k [MOD W * p ^ a] ↔
      n ≡ Erdos248.extendPrimeEventResidue hcop v k [MOD W * p] ∧
        p ^ a ∣ n + k := by
  rw [modEq_extendPrimePowerEventResidue_iff hp ha hcop,
    Erdos248.modEq_extendPrimeEventResidue_iff hp hcop]
  constructor
  · rintro ⟨hnW, hpow⟩
    exact ⟨⟨hnW, (dvd_pow_self p (by omega)).trans hpow⟩, hpow⟩
  · rintro ⟨⟨hnW, _hpdiv⟩, hpow⟩
    exact ⟨hnW, hpow⟩

/-- Cancellation of a common positive factor from both values and the
modulus in a natural congruence. -/
theorem modEq_mul_left_iff {p M x y : ℕ} (hp : 0 < p) :
    p * x ≡ p * y [MOD p * M] ↔ x ≡ y [MOD M] := by
  change p * x % (p * M) = p * y % (p * M) ↔ x % M = y % M
  rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
  constructor
  · exact Nat.eq_of_mul_eq_mul_left hp
  · intro h
    rw [h]

/-- When p is already in the base modulus p*W₀ and k=p*s, the compatible
residue for p^a ∣ n+k is obtained by solving the quotient congruence and
multiplying the result by p. -/
def smallPrimePowerEventResidue {W₀ p : ℕ} (hcop : Nat.Coprime W₀ p)
    (a s : ℕ) : ℕ :=
  p * extendPrimePowerEventResidue hcop (a - 1) 0 s

/-- Exact CRT characterization for a prime power whose underlying prime is
already present once in the pre-sieve modulus. -/
theorem modEq_smallPrimePowerEventResidue_iff
    {W₀ p a s n : ℕ} (hp : 0 < p) (ha : 2 ≤ a)
    (hcop : Nat.Coprime W₀ p) :
    n ≡ smallPrimePowerEventResidue hcop a s
          [MOD (p * W₀) * p ^ (a - 1)] ↔
      n ≡ 0 [MOD p * W₀] ∧ p ^ a ∣ n + p * s := by
  let t := extendPrimePowerEventResidue hcop (a - 1) 0 s
  let M := W₀ * p ^ (a - 1)
  have ha' : 0 < a - 1 := by omega
  have hpow : p ^ a = p * p ^ (a - 1) := by
    calc
      p ^ a = p ^ ((a - 1) + 1) := by congr 1 <;> omega
      _ = p ^ (a - 1) * p := by rw [pow_succ]
      _ = p * p ^ (a - 1) := by ring
  have hmod : (p * W₀) * p ^ (a - 1) = p * M := by
    dsimp [M]
    ring
  have ht :
      ∀ u : ℕ, u ≡ t [MOD M] ↔
        u ≡ 0 [MOD W₀] ∧ p ^ (a - 1) ∣ u + s := by
    intro u
    simpa [t, M] using
      (modEq_extendPrimePowerEventResidue_iff
        (W := W₀) (p := p) (a := a - 1) (v := 0) (k := s) (n := u)
        hp ha' hcop)
  constructor
  · intro hn
    have hnp : p ∣ n := by
      have hnmod : n ≡ smallPrimePowerEventResidue hcop a s [MOD p] :=
        hn.of_dvd (by
          rw [hmod]
          exact dvd_mul_right p M)
      have hres : smallPrimePowerEventResidue hcop a s ≡ 0 [MOD p] := by
        simp [smallPrimePowerEventResidue, Nat.ModEq]
      have : n ≡ 0 [MOD p] := hnmod.trans hres
      exact Nat.dvd_iff_mod_eq_zero.mpr this
    obtain ⟨u, rfl⟩ := hnp
    have hu : u ≡ t [MOD M] := by
      apply (modEq_mul_left_iff hp).mp
      rw [← hmod]
      simpa [smallPrimePowerEventResidue, t] using hn
    have huData := (ht u).mp hu
    refine ⟨?_, ?_⟩
    · exact Nat.ModEq.mul_left' p huData.1
    · rw [hpow, ← mul_add]
      exact Nat.mul_dvd_mul_left p huData.2
  · rintro ⟨hnW, hpowdvd⟩
    have hnp : p ∣ n := by
      exact Nat.dvd_iff_mod_eq_zero.mpr
        (hnW.of_dvd (dvd_mul_right p W₀))
    obtain ⟨u, rfl⟩ := hnp
    have huW : u ≡ 0 [MOD W₀] := by
      apply (modEq_mul_left_iff hp).mp
      simpa using hnW
    have hudvd : p ^ (a - 1) ∣ u + s := by
      apply Nat.dvd_of_mul_dvd_mul_left hp
      rw [← hpow]
      simpa [Nat.mul_add] using hpowdvd
    have hu : u ≡ t [MOD M] := (ht u).mpr ⟨huW, hudvd⟩
    rw [hmod]
    apply (modEq_mul_left_iff hp).mpr
    simpa [smallPrimePowerEventResidue, t] using hu

/-- If the base modulus is p*W₀, a compatible small-prime-power event only
lifts the outer residue modulus; the Y-variable is unchanged. -/
theorem indicator_smallPrimePower_fromYWeight
    {H : Finset ℕ} {R W₀ p a s n : ℕ}
    {y : (H → ℕ) → ℝ}
    (hp : 0 < p) (ha : 2 ≤ a) (hcop : Nat.Coprime W₀ p) :
    (if p ^ a ∣ n + p * s then
        Erdos248.fromYWeight R (p * W₀) 0 y n else 0) =
      Erdos248.fromYWeight R ((p * W₀) * p ^ (a - 1))
        (smallPrimePowerEventResidue hcop a s) y n := by
  let vpow := smallPrimePowerEventResidue hcop a s
  have hres : ∀ m : ℕ,
      m ≡ vpow [MOD (p * W₀) * p ^ (a - 1)] ↔
        m ≡ 0 [MOD p * W₀] ∧ p ^ a ∣ m + p * s := by
    intro m
    simpa [vpow] using
      (modEq_smallPrimePowerEventResidue_iff
        (W₀ := W₀) (p := p) (a := a) (s := s) (n := m) hp ha hcop)
  have hrestrict :
      (if p ^ a ∣ n + p * s then
          Erdos248.fromYWeight R (p * W₀) 0 y n else 0) =
        preSievedSquareDivisorWeight H
          (maynardDivisorTupleSupport H R (p * W₀))
          (maynardCoefficientFromY H R (p * W₀) y)
          vpow ((p * W₀) * p ^ (a - 1)) n := by
    have hraw := indicator_fromYWeight_eq_preSieved_of_modEq_iff
      (H := H) (R := R) (W := p * W₀)
      (W' := (p * W₀) * p ^ (a - 1))
      (v := 0) (v' := vpow) (n := n) (y := y)
      (P := fun m => p ^ a ∣ m + p * s) hres
    by_cases hpow : p ^ a ∣ n + p * s <;>
      simp [hpow] at hraw ⊢ <;> exact hraw
  have hlift :
      Erdos248.fromYWeight R ((p * W₀) * p ^ (a - 1)) vpow y n =
        preSievedSquareDivisorWeight H
          (maynardDivisorTupleSupport H R (p * W₀))
          (maynardCoefficientFromY H R (p * W₀) y)
          vpow ((p * W₀) * p ^ (a - 1)) n := by
    exact congrFun (fromYWeight_mul_pow_eq_preSieved_of_dvd
      (H := H) R (p * W₀) p (a - 1) vpow
      (dvd_mul_right p W₀) y) n
  exact hrestrict.trans hlift.symm

/-- Residue obtained by simultaneously lifting two distinct primes already
present once in a squarefree base modulus. -/
def twoSmallPrimePowerEventResidue {W₀ p q : ℕ}
    (hpW : Nat.Coprime W₀ p) (hqW : Nat.Coprime W₀ q)
    (hpq : Nat.Coprime p q) (a b s : ℕ) : ℕ :=
  let u₁ := extendPrimePowerEventResidue hpW (a - 1) 0 s
  let hq : Nat.Coprime (W₀ * p ^ (a - 1)) q :=
    (Nat.coprime_mul_iff_left.mpr
      ⟨hqW, hpq.pow_left (a - 1)⟩)
  p * q * extendPrimePowerEventResidue hq (b - 1) u₁ s

/-- Exact CRT characterization for two distinct prime powers whose base
primes are already present once in the outer modulus. -/
theorem modEq_twoSmallPrimePowerEventResidue_iff
    {W₀ p q a b s n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hpW : Nat.Coprime W₀ p) (hqW : Nat.Coprime W₀ q) :
    n ≡ twoSmallPrimePowerEventResidue hpW hqW
          ((Nat.coprime_primes hp hq).mpr hpq) a b s
          [MOD ((p * q) * W₀) * p ^ (a - 1) * q ^ (b - 1)] ↔
      n ≡ 0 [MOD (p * q) * W₀] ∧
        p ^ a ∣ n + (p * q) * s ∧ q ^ b ∣ n + (p * q) * s := by
  let hpqCop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  let u₁ := extendPrimePowerEventResidue hpW (a - 1) 0 s
  let hq' : Nat.Coprime (W₀ * p ^ (a - 1)) q :=
    Nat.coprime_mul_iff_left.mpr ⟨hqW, hpqCop.pow_left (a - 1)⟩
  let u₂ := extendPrimePowerEventResidue hq' (b - 1) u₁ s
  have ha' : 0 < a - 1 := by omega
  have hb' : 0 < b - 1 := by omega
  have hpu : ∀ u : ℕ,
      u ≡ u₁ [MOD W₀ * p ^ (a - 1)] ↔
        u ≡ 0 [MOD W₀] ∧ p ^ (a - 1) ∣ u + s := by
    intro u
    simpa [u₁] using
      (modEq_extendPrimePowerEventResidue_iff
        (W := W₀) (p := p) (a := a - 1) (v := 0) (k := s) (n := u)
        hp.pos ha' hpW)
  have hqu : ∀ u : ℕ,
      u ≡ u₂ [MOD (W₀ * p ^ (a - 1)) * q ^ (b - 1)] ↔
        u ≡ u₁ [MOD W₀ * p ^ (a - 1)] ∧
          q ^ (b - 1) ∣ u + s := by
    intro u
    simpa [u₂] using
      (modEq_extendPrimePowerEventResidue_iff
        (W := W₀ * p ^ (a - 1)) (p := q) (a := b - 1)
        (v := u₁) (k := s) (n := u) hq.pos hb' hq')
  have hmod :
      ((p * q) * W₀) * p ^ (a - 1) * q ^ (b - 1) =
        (p * q) * ((W₀ * p ^ (a - 1)) * q ^ (b - 1)) := by ring
  have hpowp : p ^ a = p * p ^ (a - 1) := by
    calc
      p ^ a = p ^ ((a - 1) + 1) := by congr 1 <;> omega
      _ = p ^ (a - 1) * p := by rw [pow_succ]
      _ = p * p ^ (a - 1) := by ring
  have hpowq : q ^ b = q * q ^ (b - 1) := by
    calc
      q ^ b = q ^ ((b - 1) + 1) := by congr 1 <;> omega
      _ = q ^ (b - 1) * q := by rw [pow_succ]
      _ = q * q ^ (b - 1) := by ring
  have hpcond : ∀ u : ℕ,
      p ^ a ∣ (p * q) * u + (p * q) * s ↔
        p ^ (a - 1) ∣ u + s := by
    intro u
    rw [← mul_add, hpowp]
    constructor
    · intro h
      have h' : p ^ (a - 1) ∣ q * (u + s) := by
        apply Nat.dvd_of_mul_dvd_mul_left hp.pos
        simpa [mul_assoc] using h
      exact (hpqCop.pow_left (a - 1)).dvd_mul_left.mp h'
    · rintro ⟨c, hc⟩
      refine ⟨q * c, ?_⟩
      rw [hc]
      ring
  have hqcond : ∀ u : ℕ,
      q ^ b ∣ (p * q) * u + (p * q) * s ↔
        q ^ (b - 1) ∣ u + s := by
    intro u
    rw [← mul_add, hpowq]
    constructor
    · intro h
      have h' : q ^ (b - 1) ∣ p * (u + s) := by
        apply Nat.dvd_of_mul_dvd_mul_left hq.pos
        simpa [mul_assoc, mul_left_comm, mul_comm] using h
      exact (hpqCop.symm.pow_left (b - 1)).dvd_mul_left.mp h'
    · rintro ⟨c, hc⟩
      refine ⟨p * c, ?_⟩
      rw [hc]
      ring
  rw [hmod]
  constructor
  · intro hn
    have hdiv : p * q ∣ n := by
      have hn0 : n ≡ 0 [MOD p * q] :=
        (hn.of_dvd (dvd_mul_right (p * q)
          ((W₀ * p ^ (a - 1)) * q ^ (b - 1)))).trans (by
            simp [twoSmallPrimePowerEventResidue, Nat.ModEq])
      exact Nat.dvd_iff_mod_eq_zero.mpr hn0
    obtain ⟨u, rfl⟩ := hdiv
    have hu : u ≡ u₂ [MOD (W₀ * p ^ (a - 1)) * q ^ (b - 1)] := by
      apply (modEq_mul_left_iff (mul_pos hp.pos hq.pos)).mp
      simpa [twoSmallPrimePowerEventResidue, hpqCop, u₂] using hn
    have hdata := (hqu u).mp hu
    have hpdata := (hpu u).mp hdata.1
    refine ⟨?_, ?_, ?_⟩
    · exact Nat.ModEq.mul_left' (p * q) hpdata.1
    · exact (hpcond u).mpr hpdata.2
    · exact (hqcond u).mpr hdata.2
  · rintro ⟨hnW, hpn, hqn⟩
    have hdiv : p * q ∣ n := by
      exact Nat.dvd_iff_mod_eq_zero.mpr
        (hnW.of_dvd (dvd_mul_right (p * q) W₀))
    obtain ⟨u, rfl⟩ := hdiv
    have huW : u ≡ 0 [MOD W₀] := by
      apply (modEq_mul_left_iff (mul_pos hp.pos hq.pos)).mp
      simpa using hnW
    have hpu' : p ^ (a - 1) ∣ u + s := (hpcond u).mp hpn
    have hqu' : q ^ (b - 1) ∣ u + s := (hqcond u).mp hqn
    have hu₁ : u ≡ u₁ [MOD W₀ * p ^ (a - 1)] :=
      (hpu u).mpr ⟨huW, hpu'⟩
    have hu₂ : u ≡ u₂ [MOD (W₀ * p ^ (a - 1)) * q ^ (b - 1)] :=
      (hqu u).mpr ⟨hu₁, hqu'⟩
    apply (modEq_mul_left_iff (mul_pos hp.pos hq.pos)).mpr
    simpa [twoSmallPrimePowerEventResidue, hpqCop, u₂] using hu₂

/-- Restricting the base pre-sieved weight by two compatible small
prime-power events only lifts the outer residue; the Y-variable is unchanged. -/
theorem indicator_twoSmallPrimePower_fromYWeight
    {H : Finset ℕ} {R W₀ p q a b s n : ℕ}
    {y : (H → ℕ) → ℝ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hpW : Nat.Coprime W₀ p) (hqW : Nat.Coprime W₀ q) :
    (if p ^ a ∣ n + (p * q) * s ∧ q ^ b ∣ n + (p * q) * s then
        Erdos248.fromYWeight R ((p * q) * W₀) 0 y n else 0) =
      Erdos248.fromYWeight R
        (((p * q) * W₀) * p ^ (a - 1) * q ^ (b - 1))
        (twoSmallPrimePowerEventResidue hpW hqW
          ((Nat.coprime_primes hp hq).mpr hpq) a b s) y n := by
  let vpow := twoSmallPrimePowerEventResidue hpW hqW
    ((Nat.coprime_primes hp hq).mpr hpq) a b s
  let W := (p * q) * W₀
  let W' := W * p ^ (a - 1) * q ^ (b - 1)
  have hres : ∀ m : ℕ,
      m ≡ vpow [MOD W'] ↔
        m ≡ 0 [MOD W] ∧
          (p ^ a ∣ m + (p * q) * s ∧ q ^ b ∣ m + (p * q) * s) := by
    intro m
    simpa [vpow, W, W'] using
      (modEq_twoSmallPrimePowerEventResidue_iff
        (W₀ := W₀) (p := p) (q := q) (a := a) (b := b)
        (s := s) (n := m) hp hq hpq ha hb hpW hqW)
  have hrestrict := indicator_fromYWeight_eq_preSieved_of_modEq_iff
    (H := H) (R := R) (W := W) (W' := W')
    (v := 0) (v' := vpow) (n := n) (y := y)
    (P := fun m => p ^ a ∣ m + (p * q) * s ∧
      q ^ b ∣ m + (p * q) * s) hres
  have hpWbase : p ∣ W := by
    dsimp [W]
    exact dvd_mul_of_dvd_left (dvd_mul_right p q) W₀
  have hqWbase : q ∣ W := by
    dsimp [W]
    exact dvd_mul_of_dvd_left (dvd_mul_left q p) W₀
  have hqWlift : q ∣ W * p ^ (a - 1) :=
    dvd_mul_of_dvd_left hqWbase _
  have hsupp :
      maynardDivisorTupleSupport H R W' =
        maynardDivisorTupleSupport H R W := by
    dsimp [W']
    calc
      maynardDivisorTupleSupport H R
          ((W * p ^ (a - 1)) * q ^ (b - 1)) =
          maynardDivisorTupleSupport H R (W * p ^ (a - 1)) :=
        maynardDivisorTupleSupport_mul_pow_eq_of_dvd
          H R (W * p ^ (a - 1)) q (b - 1) hqWlift
      _ = maynardDivisorTupleSupport H R W :=
        maynardDivisorTupleSupport_mul_pow_eq_of_dvd
          H R W p (a - 1) hpWbase
  have hcoeff :
      maynardCoefficientFromY H R W' y =
        maynardCoefficientFromY H R W y := by
    funext d
    dsimp [W']
    calc
      maynardCoefficientFromY H R
          ((W * p ^ (a - 1)) * q ^ (b - 1)) y d =
          maynardCoefficientFromY H R (W * p ^ (a - 1)) y d :=
        maynardCoefficientFromY_mul_pow_eq_of_dvd
          R (W * p ^ (a - 1)) q (b - 1) hqWlift y d
      _ = maynardCoefficientFromY H R W y d :=
        maynardCoefficientFromY_mul_pow_eq_of_dvd
          R W p (a - 1) hpWbase y d
  have hlift :
      Erdos248.fromYWeight R W' vpow y n =
        preSievedSquareDivisorWeight H
          (maynardDivisorTupleSupport H R W)
          (maynardCoefficientFromY H R W y)
          vpow W' n := by
    unfold Erdos248.fromYWeight
    rw [hsupp, hcoeff]
  simpa [W, W', vpow] using hrestrict.trans hlift.symm

/-- The separated-prime divisor-removal argument only needs that the event
prime divide none of the exact shift distances; the usual strict-distance
hypothesis is merely a convenient sufficient condition. -/
theorem not_prime_dvd_tupleProduct_of_event_of_not_dvd_dist
    {H : Finset ℕ} {R W p n k : ℕ} {d : H → ℕ}
    (hp : p.Prime) (hd : IsMaynardDivisorTuple H R W d)
    (hdn : divisorTupleCondition H n d) (hpn : p ∣ n + k)
    (hnodiv : ∀ h : H, ¬ p ∣ Nat.dist k h.1) :
    ¬p ∣ divisorTupleProduct H d := by
  intro hpProd
  obtain ⟨h, _hh, hph⟩ :=
    Prime.exists_mem_finset_dvd (Nat.prime_iff.mp hp) hpProd
  have hpnh : p ∣ n + h.1 := hph.trans (hdn h)
  exact hnodiv h (Erdos248.prime_dvd_shift_distance hpn hpnh)

/-- Exact divisor-sum identity under the sharp noncollision condition. -/
theorem divisorSum_eq_erasePrimeDivisorSum_of_not_dvd_dist
    {H : Finset ℕ} {R W p n k : ℕ} {y : (H → ℕ) → ℝ}
    (hp : p.Prime) (hy : IsSupportedMaynardY H R W y)
    (hpn : p ∣ n + k)
    (hnodiv : ∀ h : H, ¬ p ∣ Nat.dist k h.1) :
    (∑ d ∈ (maynardDivisorTupleSupport H R W).filter
        (divisorTupleCondition H n),
        maynardCoefficientFromY H R W y d) =
      ∑ d ∈ (maynardDivisorTupleSupport H R (W * p)).filter
        (divisorTupleCondition H n),
        maynardCoefficientFromY H R (W * p)
          (Erdos248.erasePrimeY R W p y) d := by
  classical
  let D := maynardDivisorTupleSupport H R W
  let Dp := maynardDivisorTupleSupport H R (W * p)
  let P : (H → ℕ) → Prop := fun d => p ∣ divisorTupleProduct H d
  let C : (H → ℕ) → Prop := divisorTupleCondition H n
  have hDp : Dp = D.filter (fun d => ¬P d) := by
    ext d
    simp only [Dp, D, P, Finset.mem_filter]
    exact Erdos248.mem_support_mul_prime_iff hp d
  have hremove :
      (∑ d ∈ D.filter C, maynardCoefficientFromY H R W y d) =
        ∑ d ∈ (D.filter (fun d => ¬P d)).filter C,
          maynardCoefficientFromY H R W y d := by
    symm
    apply Finset.sum_subset
    · intro d hd
      have hdData := Finset.mem_filter.mp hd
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hdData.1).1, hdData.2⟩
    · intro d hdOld hdNot
      have hdData := Finset.mem_filter.mp hdOld
      have hpProd : P d := by
        by_contra hpNot
        exact hdNot (Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨hdData.1, hpNot⟩, hdData.2⟩)
      have hnot := not_prime_dvd_tupleProduct_of_event_of_not_dvd_dist hp
        (isMaynardDivisorTuple_of_mem_support hdData.1)
        hdData.2 hpn hnodiv
      exact False.elim (hnot hpProd)
  rw [hremove, ← hDp]
  apply Finset.sum_congr rfl
  intro d hd
  have hdSupport := (Finset.mem_filter.mp hd).1
  have hpNot : ¬p ∣ divisorTupleProduct H d :=
    (Erdos248.mem_support_mul_prime_iff hp d).mp hdSupport |>.2
  have hpCop : Nat.Coprime p (divisorTupleProduct H d) :=
    hp.coprime_iff_not_dvd.mpr hpNot
  rw [Erdos248.maynardCoefficientFromY_erasePrimeY hp hy d, if_pos hpCop]

/-- Pointwise prime-event transform under exact noncollision of the event
shift with every sieve coordinate. -/
theorem indicator_separatedPrime_fromYWeight_of_not_dvd_dist
    {H : Finset ℕ} {R W v p k n : ℕ} {y : (H → ℕ) → ℝ}
    (hp : p.Prime) (hpW : Nat.Coprime p W)
    (hy : IsSupportedMaynardY H R W y)
    (hnodiv : ∀ h : H, ¬ p ∣ Nat.dist k h.1) :
    (if p ∣ n + k then Erdos248.fromYWeight R W v y n else 0) =
      Erdos248.fromYWeight R (W * p)
        (Erdos248.extendPrimeEventResidue hpW.symm v k)
        (Erdos248.erasePrimeY R W p y) n := by
  by_cases hnW : n ≡ v [MOD W]
  · by_cases hpn : p ∣ n + k
    · rw [if_pos hpn]
      have hcrt : n ≡ Erdos248.extendPrimeEventResidue hpW.symm v k
          [MOD W * p] :=
        (Erdos248.modEq_extendPrimeEventResidue_iff hp.pos hpW.symm).mpr
          ⟨hnW, hpn⟩
      unfold Erdos248.fromYWeight preSievedSquareDivisorWeight
      rw [if_pos hnW, if_pos hcrt]
      unfold squareDivisorWeight
      rw [divisorSum_eq_erasePrimeDivisorSum_of_not_dvd_dist hp hy hpn hnodiv]
    · rw [if_neg hpn]
      have hnew : ¬n ≡ Erdos248.extendPrimeEventResidue hpW.symm v k
          [MOD W * p] := by
        intro hnew
        exact hpn ((Erdos248.modEq_extendPrimeEventResidue_iff
          hp.pos hpW.symm).mp hnew).2
      simp [Erdos248.fromYWeight, preSievedSquareDivisorWeight, hnew]
  · have hnew : ¬n ≡ Erdos248.extendPrimeEventResidue hpW.symm v k
        [MOD W * p] := by
      intro hnew
      exact hnW ((Erdos248.modEq_extendPrimeEventResidue_iff
        hp.pos hpW.symm).mp hnew).1
    simp [Erdos248.fromYWeight, preSievedSquareDivisorWeight, hnW, hnew]

/-- Prime-power version of the exact noncollision transform. -/
theorem indicator_separatedPrimePower_fromYWeight_of_not_dvd_dist
    {H : Finset ℕ} {R W v p a k n : ℕ}
    {y : (H → ℕ) → ℝ}
    (hp : p.Prime) (ha : 0 < a) (hpW : Nat.Coprime p W)
    (hy : IsSupportedMaynardY H R W y)
    (hnodiv : ∀ h : H, ¬ p ∣ Nat.dist k h.1) :
    (if p ^ a ∣ n + k then Erdos248.fromYWeight R W v y n else 0) =
      Erdos248.fromYWeight R (W * p ^ a)
        (extendPrimePowerEventResidue hpW.symm a v k)
        (Erdos248.erasePrimeY R W p y) n := by
  let v₁ := Erdos248.extendPrimeEventResidue hpW.symm v k
  let vpow := extendPrimePowerEventResidue hpW.symm a v k
  let z := Erdos248.erasePrimeY R W p y
  have hone :
      (if p ∣ n + k then Erdos248.fromYWeight R W v y n else 0) =
        Erdos248.fromYWeight R (W * p) v₁ z n := by
    simpa [v₁, z] using
      (indicator_separatedPrime_fromYWeight_of_not_dvd_dist
        (R := R) (W := W) (v := v) (p := p) (k := k) (n := n)
        (y := y) hp hpW hy hnodiv)
  have hres : ∀ m : ℕ,
      m ≡ vpow [MOD W * p ^ a] ↔
        m ≡ v₁ [MOD W * p] ∧ p ^ a ∣ m + k := by
    intro m
    simpa [v₁, vpow] using
      (modEq_primePower_iff_primeResidue_and_dvd
        (W := W) (p := p) (a := a) (v := v) (k := k) (n := m)
        hp.pos ha hpW.symm)
  have hrestrict :
      (if p ^ a ∣ n + k then
          Erdos248.fromYWeight R (W * p) v₁ z n else 0) =
        preSievedSquareDivisorWeight H
          (maynardDivisorTupleSupport H R (W * p))
          (maynardCoefficientFromY H R (W * p) z)
          vpow (W * p ^ a) n := by
    have hraw := indicator_fromYWeight_eq_preSieved_of_modEq_iff
      (H := H) (R := R) (W := W * p) (W' := W * p ^ a)
      (v := v₁) (v' := vpow) (n := n) (y := z)
      (P := fun m => p ^ a ∣ m + k) hres
    by_cases hpow : p ^ a ∣ n + k <;>
      simp [hpow] at hraw ⊢ <;> exact hraw
  have hmod : (W * p) * p ^ (a - 1) = W * p ^ a := by
    have hpow : p * p ^ (a - 1) = p ^ a := by
      conv_rhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
      ring
    calc
      (W * p) * p ^ (a - 1) = W * (p * p ^ (a - 1)) := by ring
      _ = W * p ^ a := by rw [hpow]
  have hlift :
      Erdos248.fromYWeight R (W * p ^ a) vpow z n =
        preSievedSquareDivisorWeight H
          (maynardDivisorTupleSupport H R (W * p))
          (maynardCoefficientFromY H R (W * p) z)
          vpow (W * p ^ a) n := by
    have hraw := fromYWeight_mul_pow_eq_preSieved_of_dvd
      (H := H) R (W * p) p (a - 1) vpow (dvd_mul_left p W) z
    simpa [hmod] using congrFun hraw n
  calc
    (if p ^ a ∣ n + k then Erdos248.fromYWeight R W v y n else 0) =
        if p ^ a ∣ n + k then
          (if p ∣ n + k then Erdos248.fromYWeight R W v y n else 0)
        else 0 := by
          by_cases hpow : p ^ a ∣ n + k
          · have hpdiv : p ∣ n + k :=
              (dvd_pow_self p (by omega)).trans hpow
            simp [hpow, hpdiv]
          · simp [hpow]
    _ = if p ^ a ∣ n + k then
          Erdos248.fromYWeight R (W * p) v₁ z n else 0 := by
      rw [hone]
    _ = preSievedSquareDivisorWeight H
          (maynardDivisorTupleSupport H R (W * p))
          (maynardCoefficientFromY H R (W * p) z)
          vpow (W * p ^ a) n := hrestrict
    _ = Erdos248.fromYWeight R (W * p ^ a) vpow z n := hlift.symm

/-- A separated prime-power divisibility event is realized by the same
prime-erasing Y-transform as the underlying prime event, with the higher
power appearing only in the outer modulus. -/
theorem indicator_separatedPrimePower_fromYWeight
    {H : Finset ℕ} {R W v p a k n : ℕ}
    {y : (H → ℕ) → ℝ}
    (hp : p.Prime) (ha : 0 < a) (hpW : Nat.Coprime p W)
    (hy : IsSupportedMaynardY H R W y)
    (hk : ∀ h : H, k ≠ h.1)
    (hsep : ∀ h : H, Nat.dist k h.1 < p) :
    (if p ^ a ∣ n + k then Erdos248.fromYWeight R W v y n else 0) =
      Erdos248.fromYWeight R (W * p ^ a)
        (extendPrimePowerEventResidue hpW.symm a v k)
        (Erdos248.erasePrimeY R W p y) n := by
  let v₁ := Erdos248.extendPrimeEventResidue hpW.symm v k
  let vpow := extendPrimePowerEventResidue hpW.symm a v k
  let z := Erdos248.erasePrimeY R W p y
  have hone :
      (if p ∣ n + k then Erdos248.fromYWeight R W v y n else 0) =
        Erdos248.fromYWeight R (W * p) v₁ z n := by
    simpa [v₁, z] using
      (Erdos248.indicator_separatedPrime_fromYWeight
        (R := R) (W := W) (v := v) (p := p) (k := k) (n := n)
        (y := y) hp hpW hy hk hsep)
  have hres : ∀ m : ℕ,
      m ≡ vpow [MOD W * p ^ a] ↔
        m ≡ v₁ [MOD W * p] ∧ p ^ a ∣ m + k := by
    intro m
    simpa [v₁, vpow] using
      (modEq_primePower_iff_primeResidue_and_dvd
        (W := W) (p := p) (a := a) (v := v) (k := k) (n := m)
        hp.pos ha hpW.symm)
  have hrestrict :
      (if p ^ a ∣ n + k then
          Erdos248.fromYWeight R (W * p) v₁ z n else 0) =
        preSievedSquareDivisorWeight H
          (maynardDivisorTupleSupport H R (W * p))
          (maynardCoefficientFromY H R (W * p) z)
          vpow (W * p ^ a) n := by
    have hraw := indicator_fromYWeight_eq_preSieved_of_modEq_iff
      (H := H) (R := R) (W := W * p) (W' := W * p ^ a)
      (v := v₁) (v' := vpow) (n := n) (y := z)
      (P := fun m => p ^ a ∣ m + k) hres
    by_cases hpow : p ^ a ∣ n + k <;>
      simp [hpow] at hraw ⊢ <;> exact hraw
  have hmod : (W * p) * p ^ (a - 1) = W * p ^ a := by
    have hpow : p * p ^ (a - 1) = p ^ a := by
      conv_rhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
      ring
    calc
      (W * p) * p ^ (a - 1) = W * (p * p ^ (a - 1)) := by ring
      _ = W * p ^ a := by rw [hpow]
  have hlift :
      Erdos248.fromYWeight R (W * p ^ a) vpow z n =
        preSievedSquareDivisorWeight H
          (maynardDivisorTupleSupport H R (W * p))
          (maynardCoefficientFromY H R (W * p) z)
          vpow (W * p ^ a) n := by
    have hraw := fromYWeight_mul_pow_eq_preSieved_of_dvd
      (H := H) R (W * p) p (a - 1) vpow (dvd_mul_left p W) z
    simpa [hmod] using congrFun hraw n
  calc
    (if p ^ a ∣ n + k then Erdos248.fromYWeight R W v y n else 0) =
        if p ^ a ∣ n + k then
          (if p ∣ n + k then Erdos248.fromYWeight R W v y n else 0)
        else 0 := by
          by_cases hpow : p ^ a ∣ n + k
          · have hpdiv : p ∣ n + k :=
              (dvd_pow_self p (by omega)).trans hpow
            simp [hpow, hpdiv]
          · simp [hpow]
    _ = if p ^ a ∣ n + k then
          Erdos248.fromYWeight R (W * p) v₁ z n else 0 := by
      rw [hone]
    _ = preSievedSquareDivisorWeight H
          (maynardDivisorTupleSupport H R (W * p))
          (maynardCoefficientFromY H R (W * p) z)
          vpow (W * p ^ a) n := hrestrict
    _ = Erdos248.fromYWeight R (W * p ^ a) vpow z n := hlift.symm

/-- Near a sieve coordinate the same modulus lift applies to the
coordinate-forcing transform. -/
theorem indicator_coordinatePrimePower_fromYWeight
    {H : Finset ℕ} {R W v p a n : ℕ}
    {y : (H → ℕ) → ℝ}
    (hp : p.Prime) (ha : 0 < a) (hpW : Nat.Coprime p W)
    (hy : IsSupportedMaynardY H R W y) (m : H)
    (hsep : ∀ h : H, h ≠ m → Nat.dist m.1 h.1 < p) :
    (if p ^ a ∣ n + m.1 then Erdos248.fromYWeight R W v y n else 0) =
      Erdos248.fromYWeight R (W * p ^ a)
        (extendPrimePowerEventResidue hpW.symm a v m.1)
        (Erdos248.differencePrimeY R W p m y) n := by
  let v₁ := Erdos248.extendPrimeEventResidue hpW.symm v m.1
  let vpow := extendPrimePowerEventResidue hpW.symm a v m.1
  let z := Erdos248.differencePrimeY R W p m y
  have hone :
      (if p ∣ n + m.1 then Erdos248.fromYWeight R W v y n else 0) =
        Erdos248.fromYWeight R (W * p) v₁ z n := by
    simpa [v₁, z] using
      (Erdos248.indicator_coordinatePrime_fromYWeight
        (R := R) (W := W) (v := v) (p := p) (n := n)
        (y := y) hp hpW hy m hsep)
  have hres : ∀ q : ℕ,
      q ≡ vpow [MOD W * p ^ a] ↔
        q ≡ v₁ [MOD W * p] ∧ p ^ a ∣ q + m.1 := by
    intro q
    simpa [v₁, vpow] using
      (modEq_primePower_iff_primeResidue_and_dvd
        (W := W) (p := p) (a := a) (v := v) (k := m.1) (n := q)
        hp.pos ha hpW.symm)
  have hrestrict :
      (if p ^ a ∣ n + m.1 then
          Erdos248.fromYWeight R (W * p) v₁ z n else 0) =
        preSievedSquareDivisorWeight H
          (maynardDivisorTupleSupport H R (W * p))
          (maynardCoefficientFromY H R (W * p) z)
          vpow (W * p ^ a) n := by
    have hraw := indicator_fromYWeight_eq_preSieved_of_modEq_iff
      (H := H) (R := R) (W := W * p) (W' := W * p ^ a)
      (v := v₁) (v' := vpow) (n := n) (y := z)
      (P := fun q => p ^ a ∣ q + m.1) hres
    by_cases hpow : p ^ a ∣ n + m.1 <;>
      simp [hpow] at hraw ⊢ <;> exact hraw
  have hmod : (W * p) * p ^ (a - 1) = W * p ^ a := by
    have hpow : p * p ^ (a - 1) = p ^ a := by
      conv_rhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
      ring
    calc
      (W * p) * p ^ (a - 1) = W * (p * p ^ (a - 1)) := by ring
      _ = W * p ^ a := by rw [hpow]
  have hlift :
      Erdos248.fromYWeight R (W * p ^ a) vpow z n =
        preSievedSquareDivisorWeight H
          (maynardDivisorTupleSupport H R (W * p))
          (maynardCoefficientFromY H R (W * p) z)
          vpow (W * p ^ a) n := by
    have hraw := fromYWeight_mul_pow_eq_preSieved_of_dvd
      (H := H) R (W * p) p (a - 1) vpow (dvd_mul_left p W) z
    simpa [hmod] using congrFun hraw n
  calc
    (if p ^ a ∣ n + m.1 then Erdos248.fromYWeight R W v y n else 0) =
        if p ^ a ∣ n + m.1 then
          (if p ∣ n + m.1 then Erdos248.fromYWeight R W v y n else 0)
        else 0 := by
          by_cases hpow : p ^ a ∣ n + m.1
          · have hpdiv : p ∣ n + m.1 :=
              (dvd_pow_self p (by omega)).trans hpow
            simp [hpow, hpdiv]
          · simp [hpow]
    _ = if p ^ a ∣ n + m.1 then
          Erdos248.fromYWeight R (W * p) v₁ z n else 0 := by
      rw [hone]
    _ = preSievedSquareDivisorWeight H
          (maynardDivisorTupleSupport H R (W * p))
          (maynardCoefficientFromY H R (W * p) z)
          vpow (W * p ^ a) n := hrestrict
    _ = Erdos248.fromYWeight R (W * p ^ a) vpow z n := hlift.symm

/-- If the prime event at an arbitrary shift agrees with the event at one
near coordinate, the coordinate transform still realizes the higher-power
event at the original shift. -/
theorem indicator_coordinatePrimePower_at_shift_fromYWeight
    {H : Finset ℕ} {R W v p a k n : ℕ}
    {y : (H → ℕ) → ℝ}
    (hp : p.Prime) (ha : 0 < a) (hpW : Nat.Coprime p W)
    (hy : IsSupportedMaynardY H R W y) (m : H)
    (hsep : ∀ h : H, h ≠ m → Nat.dist m.1 h.1 < p)
    (hprime : ∀ t : ℕ, p ∣ t + k ↔ p ∣ t + m.1) :
    (if p ^ a ∣ n + k then Erdos248.fromYWeight R W v y n else 0) =
      Erdos248.fromYWeight R (W * p ^ a)
        (extendPrimePowerEventResidue hpW.symm a v k)
        (Erdos248.differencePrimeY R W p m y) n := by
  let v₁ := Erdos248.extendPrimeEventResidue hpW.symm v m.1
  let vpow := extendPrimePowerEventResidue hpW.symm a v k
  let z := Erdos248.differencePrimeY R W p m y
  have hone :
      (if p ∣ n + m.1 then Erdos248.fromYWeight R W v y n else 0) =
        Erdos248.fromYWeight R (W * p) v₁ z n := by
    simpa [v₁, z] using
      (Erdos248.indicator_coordinatePrime_fromYWeight
        (R := R) (W := W) (v := v) (p := p) (n := n)
        (y := y) hp hpW hy m hsep)
  have hres : ∀ t : ℕ,
      t ≡ vpow [MOD W * p ^ a] ↔
        t ≡ v₁ [MOD W * p] ∧ p ^ a ∣ t + k := by
    intro t
    constructor
    · intro ht
      have hdata := (modEq_extendPrimePowerEventResidue_iff
        (W := W) (p := p) (a := a) (v := v) (k := k) (n := t)
        hp.pos ha hpW.symm).mp ht
      have hpm : p ∣ t + m.1 :=
        (hprime t).mp ((dvd_pow_self p (by omega)).trans hdata.2)
      exact ⟨(Erdos248.modEq_extendPrimeEventResidue_iff
        hp.pos hpW.symm).mpr ⟨hdata.1, hpm⟩, hdata.2⟩
    · rintro ⟨ht, hpow⟩
      have htW := (Erdos248.modEq_extendPrimeEventResidue_iff
        hp.pos hpW.symm).mp ht |>.1
      exact (modEq_extendPrimePowerEventResidue_iff
        (W := W) (p := p) (a := a) (v := v) (k := k) (n := t)
        hp.pos ha hpW.symm).mpr ⟨htW, hpow⟩
  have hrestrict :
      (if p ^ a ∣ n + k then
          Erdos248.fromYWeight R (W * p) v₁ z n else 0) =
        preSievedSquareDivisorWeight H
          (maynardDivisorTupleSupport H R (W * p))
          (maynardCoefficientFromY H R (W * p) z)
          vpow (W * p ^ a) n := by
    have hraw := indicator_fromYWeight_eq_preSieved_of_modEq_iff
      (H := H) (R := R) (W := W * p) (W' := W * p ^ a)
      (v := v₁) (v' := vpow) (n := n) (y := z)
      (P := fun t => p ^ a ∣ t + k) hres
    by_cases hpow : p ^ a ∣ n + k <;>
      simp [hpow] at hraw ⊢ <;> exact hraw
  have hmod : (W * p) * p ^ (a - 1) = W * p ^ a := by
    have hpow : p * p ^ (a - 1) = p ^ a := by
      conv_rhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
      ring
    calc
      (W * p) * p ^ (a - 1) = W * (p * p ^ (a - 1)) := by ring
      _ = W * p ^ a := by rw [hpow]
  have hlift :
      Erdos248.fromYWeight R (W * p ^ a) vpow z n =
        preSievedSquareDivisorWeight H
          (maynardDivisorTupleSupport H R (W * p))
          (maynardCoefficientFromY H R (W * p) z)
          vpow (W * p ^ a) n := by
    have hraw := fromYWeight_mul_pow_eq_preSieved_of_dvd
      (H := H) R (W * p) p (a - 1) vpow (dvd_mul_left p W) z
    simpa [hmod] using congrFun hraw n
  calc
    (if p ^ a ∣ n + k then Erdos248.fromYWeight R W v y n else 0) =
        if p ^ a ∣ n + k then
          (if p ∣ n + m.1 then Erdos248.fromYWeight R W v y n else 0)
        else 0 := by
          by_cases hpow : p ^ a ∣ n + k
          · have hpk : p ∣ n + k :=
              (dvd_pow_self p (by omega)).trans hpow
            simp [hpow, (hprime n).mp hpk]
          · simp [hpow]
    _ = if p ^ a ∣ n + k then
          Erdos248.fromYWeight R (W * p) v₁ z n else 0 := by
      rw [hone]
    _ = preSievedSquareDivisorWeight H
          (maynardDivisorTupleSupport H R (W * p))
          (maynardCoefficientFromY H R (W * p) z)
          vpow (W * p ^ a) n := hrestrict
    _ = Erdos248.fromYWeight R (W * p ^ a) vpow z n := hlift.symm

/-- Divisibility of the distance between two shifts makes the corresponding
prime divisibility events identical. -/
theorem dvd_add_iff_of_dvd_dist {p n k h : ℕ}
    (hpdist : p ∣ Nat.dist k h) :
    p ∣ n + k ↔ p ∣ n + h := by
  by_cases hkh : k ≤ h
  · rw [Nat.dist_eq_sub_of_le hkh] at hpdist
    constructor
    · intro hpk
      have hadd : p ∣ (n + k) + (h - k) :=
        dvd_add hpk hpdist
      simpa [Nat.add_assoc, Nat.add_sub_of_le hkh] using hadd
    · intro hph
      have hsub : p ∣ (n + h) - (h - k) :=
        Nat.dvd_sub hph hpdist
      convert hsub using 1 <;> omega
  · have hhk : h ≤ k := le_of_not_ge hkh
    rw [Nat.dist_comm k h, Nat.dist_eq_sub_of_le hhk] at hpdist
    constructor
    · intro hpk
      have hsub : p ∣ (n + k) - (k - h) :=
        Nat.dvd_sub hpk hpdist
      convert hsub using 1 <;> omega
    · intro hph
      have hadd : p ∣ (n + h) + (k - h) :=
        dvd_add hph hpdist
      simpa [Nat.add_assoc, Nat.add_sub_of_le hhk] using hadd

end TaoTeravainen
