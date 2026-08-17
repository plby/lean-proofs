import ErdosProblems.Erdos49.SecondaryPacking

/-!
# Arithmetic estimates for the secondary set

The chosen secondary cofactor has at most two prime divisors, all much larger
than the distinguished prime.  This file proves the resulting uniform bound
for its totient ratio and records the exact multiplicative formula for
`d * p * s`.
-/

open scoped BigOperators

namespace Erdos49

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The elementary union bound for a finite product of numbers in `[0,1]`. -/
lemma one_sub_sum_le_prod_one_sub {S : Finset ℕ} {f : ℕ → ℝ}
    (hf0 : ∀ q ∈ S, 0 ≤ f q) (hf1 : ∀ q ∈ S, f q ≤ 1) :
    1 - ∑ q ∈ S, f q ≤ ∏ q ∈ S, (1 - f q) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert q S hq ih =>
      simp only [Finset.sum_insert hq, Finset.prod_insert hq]
      have hih := ih (fun r hr ↦ hf0 r (Finset.mem_insert_of_mem hr))
        (fun r hr ↦ hf1 r (Finset.mem_insert_of_mem hr))
      have hfactor : 0 ≤ 1 - f q := sub_nonneg.mpr (hf1 q (by simp))
      have hmul := mul_le_mul_of_nonneg_left hih hfactor
      have hsum0 : 0 ≤ ∑ r ∈ S, f r :=
        Finset.sum_nonneg fun r hr ↦ hf0 r (Finset.mem_insert_of_mem hr)
      calc
        1 - (f q + ∑ r ∈ S, f r) ≤
            (1 - f q) * (1 - ∑ r ∈ S, f r) := by
          nlinarith [mul_nonneg (hf0 q (by simp)) hsum0]
        _ ≤ (1 - f q) * ∏ r ∈ S, (1 - f r) := hmul

/-- Real Euler-product formula for the totient ratio. -/
lemma totient_ratio_real_eq_prod {n : ℕ} (hn : 0 < n) :
    (Nat.totient n : ℝ) / n =
      ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ)) := by
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hQ : (Nat.totient n : ℚ) / n =
      ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℚ)) := by
    rw [Nat.totient_eq_mul_prod_factors, mul_div_cancel_left₀ _ hnQ]
    apply Finset.prod_congr rfl
    intro q hq
    rw [one_div]
  have hR := congrArg (fun z : ℚ ↦ (z : ℝ)) hQ
  simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_prod,
    Rat.cast_sub, Rat.cast_one] using hR

/-- A positive integer with at most two prime divisors, each larger than
`pL`, has totient ratio between `1 - 2/(pL)` and `1`. -/
lemma secondary_cofactor_totient_ratio_bounds
    {L p s : ℕ} (hL : 0 < L) (hp : 0 < p) (hs : 0 < s)
    (hcard : s.primeFactors.card ≤ 2)
    (hlarge : ∀ q ∈ s.primeFactors, p * L < q) :
    1 - 2 / ((p * L : ℕ) : ℝ) ≤ (Nat.totient s : ℝ) / s ∧
      (Nat.totient s : ℝ) / s ≤ 1 := by
  have hpL : 0 < p * L := Nat.mul_pos hp hL
  have hq0 (q : ℕ) (hq : q ∈ s.primeFactors) : 0 < (q : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos
  have hinv0 (q : ℕ) (hq : q ∈ s.primeFactors) :
      0 ≤ 1 / (q : ℝ) := by positivity
  have hinv1 (q : ℕ) (hq : q ∈ s.primeFactors) :
      1 / (q : ℝ) ≤ 1 := by
    exact (div_le_one (hq0 q hq)).2 (by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_le)
  have hinvBound (q : ℕ) (hq : q ∈ s.primeFactors) :
      1 / (q : ℝ) ≤ 1 / ((p * L : ℕ) : ℝ) := by
    exact one_div_le_one_div_of_le (by exact_mod_cast hpL)
      (by exact_mod_cast (hlarge q hq).le)
  have hsum : ∑ q ∈ s.primeFactors, 1 / (q : ℝ) ≤
      2 / ((p * L : ℕ) : ℝ) := by
    calc
      ∑ q ∈ s.primeFactors, 1 / (q : ℝ) ≤
          ∑ _q ∈ s.primeFactors, 1 / ((p * L : ℕ) : ℝ) :=
        Finset.sum_le_sum hinvBound
      _ = (s.primeFactors.card : ℝ) / ((p * L : ℕ) : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        push_cast
        field_simp
      _ ≤ 2 / ((p * L : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast hcard
        · positivity
  rw [totient_ratio_real_eq_prod hs]
  constructor
  · exact (sub_le_sub_left hsum 1).trans
      (one_sub_sum_le_prod_one_sub hinv0 hinv1)
  · apply Finset.prod_le_one
    · intro q hq
      exact sub_nonneg.mpr (hinv1 q hq)
    · intro q hq
      exact sub_le_self 1 (hinv0 q hq)

/-- Exact real factorisation of the totient ratio for a secondary
representation. -/
lemma secondary_totient_ratio_formula
    {d p s : ℕ} (hd : 0 < d) (hp : p.Prime) (hs : 0 < s)
    (hdp : d.Coprime p) (hdps : (d * p).Coprime s) :
    (Nat.totient (d * p * s) : ℝ) / (d * p * s : ℕ) =
      ((Nat.totient d : ℝ) / d) * (1 - 1 / (p : ℝ)) *
        ((Nat.totient s : ℝ) / s) := by
  have hdp0 : (d * p : ℕ) ≠ 0 := Nat.mul_ne_zero hd.ne' hp.ne_zero
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [Nat.totient_mul hdps, Nat.totient_mul hdp, Nat.totient_prime hp]
  push_cast
  rw [Nat.cast_sub hp.one_le]
  field_simp [hd0, hp0, hs0]
  ring

/-- The two explicit scale inequalities used by the secondary argument imply
that the reciprocal-prime gap dominates both the cofactor perturbation and
the outer bucket width. -/
lemma secondary_numeric_gap
    {P V L U X pn pm m : ℕ}
    (hP : 0 < P) (hV : 0 < V) (hL : 0 < L)
    (hpn : P ≤ pn) (hpn' : pn ≤ 2 * P)
    (hpm : P ≤ pm) (hpm' : pm ≤ 2 * P)
    (hpGap : pn + V ≤ pm) (hXm : X ≤ m)
    (houter : 8 * P ^ 2 * U < V * X)
    (hinner : 16 * P < V * L) :
    (U : ℝ) <
      ((1 / (pn : ℝ) - 1 / (pm : ℝ)) -
        2 / ((pm * L : ℕ) : ℝ)) * m := by
  have hpn0 : (0 : ℝ) < pn := by exact_mod_cast hP.trans_le hpn
  have hpm0 : (0 : ℝ) < pm := by exact_mod_cast hP.trans_le hpm
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hV0 : (0 : ℝ) < V := by exact_mod_cast hV
  have hgapR : (V : ℝ) ≤ (pm : ℝ) - pn := by
    rw [le_sub_iff_add_le]
    exact_mod_cast (by omega : V + pn ≤ pm)
  have hden : (pn : ℝ) * pm ≤ 4 * (P : ℝ) ^ 2 := by
    have := mul_le_mul (show (pn : ℝ) ≤ 2 * P by exact_mod_cast hpn')
      (show (pm : ℝ) ≤ 2 * P by exact_mod_cast hpm')
      (by positivity) (by positivity)
    nlinarith
  have hrecip : (V : ℝ) / (4 * (P : ℝ) ^ 2) ≤
      1 / (pn : ℝ) - 1 / (pm : ℝ) := by
    have hfrac : (V : ℝ) / (4 * (P : ℝ) ^ 2) ≤
        ((pm : ℝ) - pn) / ((pn : ℝ) * pm) := by
      exact div_le_div₀ (sub_nonneg.mpr (by linarith)) hgapR
        (mul_pos hpn0 hpm0) hden
    calc
      (V : ℝ) / (4 * (P : ℝ) ^ 2) ≤
          ((pm : ℝ) - pn) / ((pn : ℝ) * pm) := hfrac
      _ = 1 / (pn : ℝ) - 1 / (pm : ℝ) := by
        field_simp
  have herror : 2 / ((pm * L : ℕ) : ℝ) ≤
      2 / ((P * L : ℕ) : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast Nat.mul_le_mul_right L hpm
  have hinnerR : 2 / ((P * L : ℕ) : ℝ) <
      (V : ℝ) / (8 * (P : ℝ) ^ 2) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    push_cast
    have hinnerCast : (16 : ℝ) * P < V * L := by exact_mod_cast hinner
    have hmul := mul_lt_mul_of_pos_right hinnerCast hP0
    nlinarith
  have hdouble : (V : ℝ) / (4 * (P : ℝ) ^ 2) =
      2 * ((V : ℝ) / (8 * (P : ℝ) ^ 2)) := by ring
  rw [hdouble] at hrecip
  have hgap : (V : ℝ) / (8 * (P : ℝ) ^ 2) <
      (1 / (pn : ℝ) - 1 / (pm : ℝ)) -
        2 / ((pm * L : ℕ) : ℝ) := by
    linarith
  have houterR : (U : ℝ) <
      (V : ℝ) * X / (8 * (P : ℝ) ^ 2) := by
    rw [lt_div_iff₀ (by positivity)]
    have houterCast : ((8 * P ^ 2 * U : ℕ) : ℝ) < V * X := by
      exact_mod_cast houter
    push_cast at houterCast
    nlinarith
  have hXmR : (X : ℝ) ≤ m := by exact_mod_cast hXm
  have hVnonneg : 0 ≤ (V : ℝ) := hV0.le
  calc
    (U : ℝ) < (V : ℝ) * X / (8 * (P : ℝ) ^ 2) := houterR
    _ ≤ (V : ℝ) / (8 * (P : ℝ) ^ 2) * m := by
      calc
        (V : ℝ) * X / (8 * (P : ℝ) ^ 2) =
            ((V : ℝ) / (8 * (P : ℝ) ^ 2)) * X := by ring
        _ ≤ ((V : ℝ) / (8 * (P : ℝ) ^ 2)) * m :=
          mul_le_mul_of_nonneg_left hXmR (by positivity)
    _ < ((1 / (pn : ℝ) - 1 / (pm : ℝ)) -
        2 / ((pm * L : ℕ) : ℝ)) * m := by
      exact mul_lt_mul_of_pos_right hgap (by
        have : 0 < X := by
          by_contra hX
          have hX0 : X = 0 := Nat.eq_zero_of_not_pos hX
          simp [hX0] at houter
        exact_mod_cast this.trans_le hXm)

/-- Under Tao's two scale separations, two elements in the same outer bucket
whose distinguished primes lie in separated inner buckets are ordered by
their totients. -/
lemma secondary_cell_order
    {A : Finset ℕ} {d L P U V X : ℕ} {p s : ℕ → ℕ}
    (hmono : TotientMonotoneOn A)
    (hd : 0 < d) (hL : 0 < L) (hP : 0 < P) (hU : 0 < U) (hV : 0 < V)
    (houter : 8 * P ^ 2 * U < V * X)
    (hinner : 16 * P < V * L)
    (hdata : ∀ n ∈ A,
      X ≤ n ∧ P ≤ p n ∧ p n ≤ 2 * P ∧ (p n).Prime ∧
      0 < s n ∧ d.Coprime (p n) ∧ (d * p n).Coprime (s n) ∧
      (s n).primeFactors.card ≤ 2 ∧
      (∀ q ∈ (s n).primeFactors, p n * L < q) ∧
      n = d * p n * s n) :
    ∀ n ∈ A, ∀ m ∈ A, n / U = m / U →
      p n / V + 1 < p m / V → n < m := by
  intro n hn m hm hbucket hpBucket
  rcases hdata n hn with
    ⟨hnX, hpnLow, hpnHigh, hpnPrime, hsnPos, hcopN₁, hcopN₂,
      hcardN, hlargeN, hnfac⟩
  rcases hdata m hm with
    ⟨hmX, hpmLow, hpmHigh, hpmPrime, hsmPos, hcopM₁, hcopM₂,
      hcardM, hlargeM, hmfac⟩
  have hnBounds := quotientBucket_bounds (W := U) (n := n) hU
  have hmBounds := quotientBucket_bounds (W := U) (n := m) hU
  change n / U * U ≤ n ∧ n < n / U * U + U at hnBounds
  change m / U * U ≤ m ∧ m < m / U * U + U at hmBounds
  have hnear : n ≤ m + U := by
    calc
      n ≤ n / U * U + U := hnBounds.2.le
      _ = m / U * U + U := by rw [hbucket]
      _ ≤ m + U := Nat.add_le_add_right hmBounds.1 U
  have hpNBounds := quotientBucket_bounds (W := V) (n := p n) hV
  have hpMBounds := quotientBucket_bounds (W := V) (n := p m) hV
  change p n / V * V ≤ p n ∧ p n < p n / V * V + V at hpNBounds
  change p m / V * V ≤ p m ∧ p m < p m / V * V + V at hpMBounds
  have hpGap : p n + V ≤ p m := by
    calc
      p n + V ≤ (p n / V * V + V) + V := Nat.add_le_add_right hpNBounds.2.le V
      _ = (p n / V + 2) * V := by ring
      _ ≤ (p m / V) * V := Nat.mul_le_mul_right V (by omega)
      _ ≤ p m := hpMBounds.1
  let qd : ℝ := (Nat.totient d : ℝ) / d
  let an : ℝ := (1 - 1 / (p n : ℝ)) * ((Nat.totient (s n) : ℝ) / s n)
  let am : ℝ := (1 - 1 / (p m : ℝ)) * ((Nat.totient (s m) : ℝ) / s m)
  have hsn := secondary_cofactor_totient_ratio_bounds hL hpnPrime.pos hsnPos
    hcardN hlargeN
  have hsm := secondary_cofactor_totient_ratio_bounds hL hpmPrime.pos hsmPos
    hcardM hlargeM
  have hpn0 : (0 : ℝ) < p n := by exact_mod_cast hpnPrime.pos
  have hpm0 : (0 : ℝ) < p m := by exact_mod_cast hpmPrime.pos
  have hfacN0 : 0 ≤ 1 - 1 / (p n : ℝ) := by
    rw [sub_nonneg]
    exact (div_le_one hpn0).2 (by exact_mod_cast hpnPrime.one_le)
  have hfacM0 : 0 ≤ 1 - 1 / (p m : ℝ) := by
    rw [sub_nonneg]
    exact (div_le_one hpm0).2 (by exact_mod_cast hpmPrime.one_le)
  have han0 : 0 ≤ an := by
    dsimp only [an]
    exact mul_nonneg hfacN0 (by positivity)
  have han1 : an ≤ 1 - 1 / (p n : ℝ) := by
    dsimp only [an]
    exact mul_le_of_le_one_right hfacN0 hsn.2
  have herrorM0 : 0 ≤ 2 / ((p m * L : ℕ) : ℝ) := by positivity
  have hamSimple : 1 - 1 / (p m : ℝ) -
      2 / ((p m * L : ℕ) : ℝ) ≤ am := by
    have hprodLower :
        (1 - 1 / (p m : ℝ)) *
            (1 - 2 / ((p m * L : ℕ) : ℝ)) ≤ am := by
      dsimp only [am]
      exact mul_le_mul_of_nonneg_left hsm.1 hfacM0
    calc
      1 - 1 / (p m : ℝ) - 2 / ((p m * L : ℕ) : ℝ) ≤
          (1 - 1 / (p m : ℝ)) *
            (1 - 2 / ((p m * L : ℕ) : ℝ)) := by
        nlinarith [mul_nonneg (by positivity : 0 ≤ 1 / (p m : ℝ)) herrorM0]
      _ ≤ am := hprodLower
  have hdiff : (1 / (p n : ℝ) - 1 / (p m : ℝ)) -
      2 / ((p m * L : ℕ) : ℝ) ≤ am - an := by
    linarith
  have hnumeric := secondary_numeric_gap hP hV hL
    hpnLow hpnHigh hpmLow hpmHigh hpGap hmX houter hinner
  have hgapMul : (U : ℝ) < (am - an) * m :=
    hnumeric.trans_le (mul_le_mul_of_nonneg_right hdiff (by positivity))
  have hanLeOne : an ≤ 1 := han1.trans (sub_le_self 1 (by positivity))
  have hratioOrder : an * n < am * m := by
    have hnearR : (n : ℝ) ≤ m + U := by exact_mod_cast hnear
    calc
      an * n ≤ an * (m + U) := mul_le_mul_of_nonneg_left hnearR han0
      _ = an * m + an * U := by ring
      _ ≤ an * m + U := by
        have hUterm : an * (U : ℝ) ≤ U := by
          simpa using mul_le_mul_of_nonneg_right hanLeOne (Nat.cast_nonneg U)
        linarith
      _ < am * m := by nlinarith
  have hqd : 0 < qd := by
    dsimp only [qd]
    positivity
  have hphiN : (Nat.totient n : ℝ) = qd * an * n := by
    rw [hnfac]
    have hf := secondary_totient_ratio_formula hd hpnPrime hsnPos hcopN₁ hcopN₂
    have hnposNat : 0 < d * p n * s n :=
      Nat.mul_pos (Nat.mul_pos hd hpnPrime.pos) hsnPos
    have hnpos : (0 : ℝ) < ((d * p n * s n : ℕ) : ℝ) := by exact_mod_cast hnposNat
    have hmul := (div_eq_iff hnpos.ne').mp hf
    simpa [qd, an, mul_assoc] using hmul
  have hphiM : (Nat.totient m : ℝ) = qd * am * m := by
    rw [hmfac]
    have hf := secondary_totient_ratio_formula hd hpmPrime hsmPos hcopM₁ hcopM₂
    have hmposNat : 0 < d * p m * s m :=
      Nat.mul_pos (Nat.mul_pos hd hpmPrime.pos) hsmPos
    have hmpos : (0 : ℝ) < ((d * p m * s m : ℕ) : ℝ) := by exact_mod_cast hmposNat
    have hmul := (div_eq_iff hmpos.ne').mp hf
    simpa [qd, am, mul_assoc] using hmul
  have hphi : Nat.totient n < Nat.totient m := by
    exact_mod_cast (show (Nat.totient n : ℝ) < Nat.totient m by
      rw [hphiN, hphiM]
      simpa [mul_assoc] using mul_lt_mul_of_pos_left hratioOrder hqd)
  by_contra hnot
  exact (not_lt_of_ge (hmono hm hn (Nat.le_of_not_gt hnot))) hphi

/-- The canonical secondary anatomy used in Tao's decomposition.  We retain
the coprimality facts explicitly; the anatomy lemma derives them from the
separation of the prime factors. -/
def SecondaryRep (N L n d p s : ℕ) : Prop :=
  1 ≤ d ∧ p.Prime ∧ L < p ∧ 0 < s ∧ p * L < s ∧ d.Coprime p ∧
    (d * p).Coprime s ∧ s.primeFactors.card ≤ 2 ∧
    (∀ q ∈ s.primeFactors, p * L < q) ∧ n = d * p * s ∧ n ≤ N

def secondarySet (N L : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n ↦ ∃ d p s, SecondaryRep N L n d p s

@[simp] lemma mem_secondarySet {N L n : ℕ} :
    n ∈ secondarySet N L ↔
      1 ≤ n ∧ n ≤ N ∧ ∃ d p s, SecondaryRep N L n d p s := by
  simp [secondarySet, and_assoc]

private def secondaryWitness (N L n : ℕ) : ℕ × ℕ × ℕ :=
  if h : ∃ z : ℕ × ℕ × ℕ, SecondaryRep N L n z.1 z.2.1 z.2.2 then
    Classical.choose h
  else (1, 2, 1)

def secondaryD (N L n : ℕ) : ℕ := (secondaryWitness N L n).1
def secondaryP (N L n : ℕ) : ℕ := (secondaryWitness N L n).2.1
def secondaryS (N L n : ℕ) : ℕ := (secondaryWitness N L n).2.2

lemma secondaryWitness_spec {N L n : ℕ} (hn : n ∈ secondarySet N L) :
    SecondaryRep N L n (secondaryD N L n) (secondaryP N L n)
      (secondaryS N L n) := by
  have hex : ∃ z : ℕ × ℕ × ℕ, SecondaryRep N L n z.1 z.2.1 z.2.2 := by
    obtain ⟨d, p, s, hrep⟩ := (mem_secondarySet.mp hn).2.2
    exact ⟨(d, p, s), hrep⟩
  simpa [secondaryD, secondaryP, secondaryS, secondaryWitness, hex] using
    (Classical.choose_spec hex)

/-- Complete packing estimate for one fixed chosen denominator, one dyadic
prime band, and one dyadic integer band. -/
theorem secondary_structured_band_bound
    {N L d₀ P U V X Y : ℕ} {A : Finset ℕ}
    (hAsec : A ⊆ secondarySet N L) (hmono : TotientMonotoneOn A)
    (hd₀ : 0 < d₀) (hP : 0 < P) (hU : 0 < U) (hV : 0 < V)
    (hd : ∀ n ∈ A, secondaryD N L n = d₀)
    (hpBand : ∀ n ∈ A, P ≤ secondaryP N L n ∧ secondaryP N L n ≤ 2 * P)
    (hnBand : ∀ n ∈ A, X ≤ n ∧ n ≤ Y)
    (houter : 8 * P ^ 2 * U < V * X)
    (hinner : 16 * P < V * L) :
    (A.card : ℝ) ≤
      (V : ℝ) * (2 * Y : ℕ) / (d₀ * P : ℕ) +
        (((Y / U + 1) * (2 * P / V + 1) : ℕ) : ℝ) * (3 * V) := by
  let p : ℕ → ℕ := secondaryP N L
  let s : ℕ → ℕ := secondaryS N L
  have hrep : ∀ n ∈ A,
      SecondaryRep N L n d₀ (p n) (s n) := by
    intro n hn
    have hs := secondaryWitness_spec (hAsec hn)
    rw [hd n hn] at hs
    exact hs
  have hdata : ∀ n ∈ A,
      X ≤ n ∧ P ≤ p n ∧ p n ≤ 2 * P ∧ (p n).Prime ∧
      0 < s n ∧ d₀.Coprime (p n) ∧ (d₀ * p n).Coprime (s n) ∧
      (s n).primeFactors.card ≤ 2 ∧
      (∀ q ∈ (s n).primeFactors, p n * L < q) ∧
      n = d₀ * p n * s n := by
    intro n hn
    have hr := hrep n hn
    exact ⟨(hnBand n hn).1, (hpBand n hn).1, (hpBand n hn).2,
      hr.2.1, hr.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2.1⟩
  have hL : 0 < L := by
    by_contra h
    have : L = 0 := Nat.eq_zero_of_not_pos h
    subst L
    simp at hinner
  have horder := secondary_cell_order hmono hd₀ hL hP hU hV
    houter hinner hdata
  have hoverlapAll := secondary_hulls_overlap_two hU horder
  apply secondary_band_bucket_bound
    (N := Y) (P := P) (U := U) (V := V) (d₀ := d₀)
    (p := p) (s := s)
  · intro n hn
    exact Finset.mem_Icc.mpr
      ⟨(hAsec hn |> mem_secondarySet.mp).1,
        (hnBand n hn).2⟩
  · exact hV
  · exact hd₀
  · exact hP
  · intro n hn
    exact (hrep n hn).2.2.2.2.2.2.2.2.2.1
  · exact hpBand
  · intro x hx
    exact hoverlapAll x

#print axioms secondary_cofactor_totient_ratio_bounds
#print axioms secondary_totient_ratio_formula
#print axioms secondary_cell_order
#print axioms secondary_structured_band_bound

end

end Erdos49
