/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.PrimeKloostermanBound

/-!
# Complete Kloosterman bounds for squarefree moduli

This file multiplies the prime-field rational Weil estimate through the
exact CRT factorization.  The inverse coefficient is written as a natural
cast times a unit; this makes the local degeneracy product exactly the gcd
with the modulus.
-/

namespace Erdos387

open scoped BigOperators

namespace Kloosterman

private theorem gcd_mul_of_coprime
    {x m n : ℕ} (hcop : Nat.Coprime m n) :
    Nat.gcd x (m * n) = Nat.gcd x m * Nat.gcd x n := by
  apply Nat.dvd_antisymm
  · exact gcd_mul_dvd_mul_gcd x m n
  · apply Nat.dvd_gcd
    · exact (hcop.gcd_both x x).mul_dvd_of_dvd_of_dvd
        (Nat.gcd_dvd_left x m) (Nat.gcd_dvd_left x n)
    · exact Nat.mul_dvd_mul (Nat.gcd_dvd_right x m)
        (Nat.gcd_dvd_right x n)

private theorem prime_gcd_eq_ite
    {p B : ℕ} (hp : p.Prime) :
    Nat.gcd B p = if p ∣ B then p else 1 := by
  by_cases hdiv : p ∣ B
  · rw [if_pos hdiv]
    exact Nat.gcd_eq_right_iff_dvd.mpr hdiv
  · rw [if_neg hdiv]
    exact Nat.coprime_iff_gcd_eq_one.mp
      ((hp.coprime_iff_not_dvd).mpr hdiv).symm

private theorem norm_sum_natCast_mul_unit_squarefree_aux :
    ∀ q : ℕ, ∀ hq0 : q ≠ 0, ∀ B : ℕ,
      Squarefree q →
      (∀ p ∈ q.primeFactors, 2 < p) →
      ∀ (a u : ZMod q), IsUnit u →
        ‖@sum q ⟨hq0⟩ a ((B : ZMod q) * u)‖ ≤
          (4 : ℝ) ^ q.primeFactors.card * Real.sqrt (q : ℝ) *
            Real.sqrt (Nat.gcd B q : ℝ) := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro hq0 B hsq hlarge a u hu
      letI : NeZero q := ⟨hq0⟩
      by_cases hq1 : q = 1
      · subst q
        have htrivial := norm_sum_le_modulus 1 a ((B : ZMod 1) * u)
        simpa using htrivial
      · obtain ⟨p, hpPrime, hpDvd⟩ := Nat.exists_prime_and_dvd hq1
        obtain ⟨m, hqm⟩ := hpDvd
        have hpPos : 0 < p := hpPrime.pos
        have hqeq : q = m * p := by simpa [mul_comm] using hqm
        clear hqm
        have hmp0 : m * p ≠ 0 := by rw [← hqeq]; exact hq0
        have hm0 : m ≠ 0 := (Nat.mul_ne_zero_iff.mp hmp0).1
        have hmPos : 0 < m := Nat.pos_of_ne_zero hm0
        subst q
        have hmLt : m < m * p := by
          simpa using (Nat.mul_lt_mul_left hmPos).2 hpPrime.one_lt
        have hsqmp : Squarefree (m * p) := hsq
        have hparts := Nat.squarefree_mul_iff.mp hsqmp
        have hcop : Nat.Coprime m p := hparts.1
        have hsqm : Squarefree m := hparts.2.1
        have hpMem : p ∈ (m * p).primeFactors := by
          exact hpPrime.mem_primeFactors (Nat.dvd_mul_left p m) hmp0
        have hpLarge : 2 < p := hlarge p hpMem
        have hlargeM : ∀ r ∈ m.primeFactors, 2 < r := by
          intro r hr
          apply hlarge r
          exact Nat.mem_primeFactors.mpr
            ⟨(Nat.mem_primeFactors.mp hr).1,
              (Nat.dvd_of_mem_primeFactors hr).trans (by
                exact Nat.dvd_mul_right m p), hq0⟩
        letI : NeZero m := ⟨hm0⟩
        letI : NeZero p := ⟨hpPrime.ne_zero⟩
        letI : Fact p.Prime := ⟨hpPrime⟩
        let e := ZMod.chineseRemainder hcop
        let aP : ZMod p := (e a).2 * (Nat.gcdA m p : ZMod p)
        let aM : ZMod m := (e a).1 * (Nat.gcdB m p : ZMod m)
        let uP : ZMod p := (e u).2 * (Nat.gcdA m p : ZMod p)
        let uM : ZMod m := (e u).1 * (Nat.gcdB m p : ZMod m)
        have heu : IsUnit (e u) := hu.map e.toRingHom
        have hucoords : IsUnit (e u).1 ∧ IsUnit (e u).2 :=
          Prod.isUnit_iff.mp heu
        have huP : IsUnit uP := hucoords.2.mul (isUnit_gcdA m p hcop)
        have huM : IsUnit uM := hucoords.1.mul (isUnit_gcdB m p hcop)
        have hbP :
            (e ((B : ZMod (m * p)) * u)).2 * (Nat.gcdA m p : ZMod p) =
              (B : ZMod p) * uP := by
          simp only [e, uP, map_mul, Prod.snd_mul]
          rw [show (ZMod.chineseRemainder hcop (B : ZMod (m * p))).2 =
              (B : ZMod p) by
            simp [ZMod.chineseRemainder, ZMod.castHom_apply]]
          ring
        have hbM :
            (e ((B : ZMod (m * p)) * u)).1 * (Nat.gcdB m p : ZMod m) =
              (B : ZMod m) * uM := by
          simp only [e, uM, map_mul, Prod.fst_mul]
          rw [show (ZMod.chineseRemainder hcop (B : ZMod (m * p))).1 =
              (B : ZMod m) by
            simp [ZMod.chineseRemainder, ZMod.castHom_apply]]
          ring
        have hlocalRaw := norm_sum_le_four_sqrt_mul_ite hpLarge
          aP ((B : ZMod p) * uP)
        have hzero : ((B : ZMod p) * uP = 0) ↔ p ∣ B := by
          rw [mul_eq_zero]
          have huP0 : uP ≠ 0 := IsUnit.ne_zero huP
          simp [huP0, ZMod.natCast_eq_zero_iff]
        have hgcdP :
            (if (B : ZMod p) * uP = 0 then Real.sqrt (p : ℝ) else 1) =
              Real.sqrt (Nat.gcd B p : ℝ) := by
          rw [prime_gcd_eq_ite hpPrime]
          by_cases hpB : p ∣ B
          · rw [if_pos hpB, if_pos (hzero.mpr hpB)]
          · rw [if_neg hpB, if_neg (not_congr hzero |>.mpr hpB)]
            simp
        have hlocal :
            ‖sum p aP ((B : ZMod p) * uP)‖ ≤
              4 * Real.sqrt (p : ℝ) * Real.sqrt (Nat.gcd B p : ℝ) := by
          simpa only [hgcdP] using hlocalRaw
        have hind := ih m hmLt hm0 B hsqm hlargeM aM uM huM
        have hfactor := sum_product m p hcop a ((B : ZMod (m * p)) * u)
        rw [hbP, hbM] at hfactor
        simp only [Nat.cast_mul]
        rw [hfactor, norm_mul]
        calc
          ‖sum p aP ((B : ZMod p) * uP)‖ *
              ‖sum m aM ((B : ZMod m) * uM)‖ ≤
            (4 * Real.sqrt (p : ℝ) * Real.sqrt (Nat.gcd B p : ℝ)) *
              ((4 : ℝ) ^ m.primeFactors.card * Real.sqrt (m : ℝ) *
                Real.sqrt (Nat.gcd B m : ℝ)) :=
            mul_le_mul hlocal hind (norm_nonneg _) (by positivity)
          _ = (4 : ℝ) ^ (m * p).primeFactors.card * Real.sqrt (m * p : ℝ) *
              Real.sqrt (Nat.gcd B (m * p) : ℝ) := by
            have hpnot : p ∉ m.primeFactors := by
              intro hpm
              have hpdivm := Nat.dvd_of_mem_primeFactors hpm
              exact hpPrime.ne_one (hcop.symm.eq_one_of_dvd hpdivm)
            have hpfactors :
                (m * p).primeFactors = m.primeFactors ∪ {p} := by
              rw [Nat.primeFactors_mul hm0 hpPrime.ne_zero,
                hpPrime.primeFactors]
            have hcard : (m * p).primeFactors.card = m.primeFactors.card + 1 := by
              rw [hpfactors]
              simp [hpnot]
            have hsqrtQ : Real.sqrt (m * p : ℝ) =
                Real.sqrt (m : ℝ) * Real.sqrt (p : ℝ) := by
              push_cast
              rw [Real.sqrt_mul (Nat.cast_nonneg m)]
            have hgcd : Nat.gcd B (m * p) = Nat.gcd B m * Nat.gcd B p := by
              exact gcd_mul_of_coprime hcop
            have hsqrtGcd : Real.sqrt (Nat.gcd B (m * p) : ℝ) =
                Real.sqrt (Nat.gcd B m : ℝ) *
                  Real.sqrt (Nat.gcd B p : ℝ) := by
              rw [hgcd]
              push_cast
              rw [Real.sqrt_mul (Nat.cast_nonneg (Nat.gcd B m))]
            rw [hcard, pow_succ, hsqrtQ, hsqrtGcd]
            ring_nf

/-- Squarefree complete Kloosterman bound with the usual gcd loss.  The
constant `4^ω(q)` is harmless on the rough subpower moduli used here. -/
theorem norm_sum_natCast_mul_unit_squarefree
    (q B : ℕ) [NeZero q] (hsq : Squarefree q)
    (hlarge : ∀ p ∈ q.primeFactors, 2 < p)
    (a u : ZMod q) (hu : IsUnit u) :
    ‖sum q a ((B : ZMod q) * u)‖ ≤
      (4 : ℝ) ^ q.primeFactors.card * Real.sqrt (q : ℝ) *
        Real.sqrt (Nat.gcd B q : ℝ) :=
  norm_sum_natCast_mul_unit_squarefree_aux q (NeZero.ne q) B hsq hlarge a u hu

/-- Representative-free form of the squarefree estimate. -/
theorem norm_sum_val_squarefree
    (q : ℕ) [NeZero q] (hsq : Squarefree q)
    (hlarge : ∀ p ∈ q.primeFactors, 2 < p)
    (a b : ZMod q) :
    ‖sum q a b‖ ≤
      (4 : ℝ) ^ q.primeFactors.card * Real.sqrt (q : ℝ) *
        Real.sqrt (Nat.gcd b.val q : ℝ) := by
  have h := norm_sum_natCast_mul_unit_squarefree q b.val hsq hlarge
    a (1 : ZMod q) isUnit_one
  simpa [ZMod.natCast_zmod_val] using h

/-- A fixed (possibly powerful) factor can be treated trivially while the
coprime varying squarefree factor receives square-root cancellation. -/
theorem norm_sum_fixed_mul_squarefree
    (M q : ℕ) [NeZero M] [NeZero q]
    (hcop : Nat.Coprime M q) (hsq : Squarefree q)
    (hlarge : ∀ p ∈ q.primeFactors, 2 < p)
    (a b : ZMod (M * q)) :
    ‖sum (M * q) a b‖ ≤
      (4 : ℝ) ^ q.primeFactors.card * Real.sqrt (q : ℝ) *
        Real.sqrt
          (Nat.gcd
            (((ZMod.chineseRemainder hcop b).2 *
              (Nat.gcdA M q : ZMod q)).val) q : ℝ) * M := by
  have hfactor := sum_product M q hcop a b
  let aq : ZMod q :=
    (ZMod.chineseRemainder hcop a).2 * (Nat.gcdA M q : ZMod q)
  let bq : ZMod q :=
    (ZMod.chineseRemainder hcop b).2 * (Nat.gcdA M q : ZMod q)
  let aM : ZMod M :=
    (ZMod.chineseRemainder hcop a).1 * (Nat.gcdB M q : ZMod M)
  let bM : ZMod M :=
    (ZMod.chineseRemainder hcop b).1 * (Nat.gcdB M q : ZMod M)
  have hq := norm_sum_val_squarefree q hsq hlarge aq bq
  have hM := norm_sum_le_modulus M aM bM
  change sum (M * q) a b = sum q aq bq * sum M aM bM at hfactor
  rw [hfactor, norm_mul]
  change _ ≤ (4 : ℝ) ^ q.primeFactors.card * Real.sqrt (q : ℝ) *
    Real.sqrt (Nat.gcd bq.val q : ℝ) * M
  exact mul_le_mul hq hM (norm_nonneg _) (by positivity)

/-- Incomplete interval form with one fixed modulus factor and a varying
squarefree factor. -/
theorem norm_incompleteInterval_fixed_mul_squarefree
    (M q : ℕ) [NeZero M] [NeZero q]
    (hcop : Nat.Coprime M q) (hsq : Squarefree q)
    (hlarge : ∀ p ∈ q.primeFactors, 2 < p)
    (b : ZMod (M * q)) (L : ℤ) (m : ℕ) (hm : m ≤ M * q) :
    ‖incompleteInterval (M * q) b L m‖ ≤
      (Real.log (M * q : ℕ) + 1) *
        ((4 : ℝ) ^ q.primeFactors.card * Real.sqrt (q : ℝ) *
          Real.sqrt
            (Nat.gcd
              (((ZMod.chineseRemainder hcop b).2 *
                (Nat.gcdA M q : ZMod q)).val) q : ℝ) * M) := by
  have hnonneg : 0 ≤
      (4 : ℝ) ^ q.primeFactors.card * Real.sqrt (q : ℝ) *
        Real.sqrt
          (Nat.gcd
            (((ZMod.chineseRemainder hcop b).2 *
              (Nat.gcdA M q : ZMod q)).val) q : ℝ) * M := by
    positivity
  exact norm_incompleteInterval_le_log_of_complete_bound
    (M * q) b L m _ hm hnonneg
      (fun a => norm_sum_fixed_mul_squarefree M q hcop hsq hlarge a b)

end Kloosterman

end Erdos387
