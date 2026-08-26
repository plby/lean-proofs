import ErdosProblems.Erdos394.PrimeSubset

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The exact first moment of a general CRT root box

For distinct primes larger than `K`, a fixed multiplier `j` has `p-1` local
unit multipliers when `p ∣ j`, and `K-1` otherwise.  This file proves the
arithmetic first-moment identity obtained by multiplying those local counts,
and the sharp discrepancy interval of length one after normalization.
-/

open Nat Finset

namespace Erdos394

/-- Product of the local numbers of admissible unit multipliers. -/
def rootBoxLocalWeight (P : Finset ℕ) (K j : ℕ) : ℕ :=
  ∏ p ∈ P, if p ∣ j then p - 1 else K - 1

/-- The unnormalized first moment up to `Y`. -/
def rootBoxFirstMoment (P : Finset ℕ) (K Y : ℕ) : ℕ :=
  ∑ j ∈ Icc 1 Y, rootBoxLocalWeight P K j

/-- Coefficient associated with a set of primes forced to divide `j`. -/
def rootBoxSubsetCoeff (P : Finset ℕ) (K : ℕ) (T : Finset ℕ) : ℕ :=
  (∏ p ∈ T, (p - K)) * (K - 1) ^ (P \ T).card

/-- The product of a finite set of distinct primes divides `j` exactly when
all of its factors divide `j`. -/
theorem primeProduct_dvd_iff_all_dvd (T : Finset ℕ)
    (hprime : ∀ p ∈ T, p.Prime) (j : ℕ) :
    primeProduct T ∣ j ↔ ∀ p ∈ T, p ∣ j := by
  induction T using Finset.induction_on with
  | empty => simp [primeProduct]
  | @insert p T hpT ih =>
      have hp : p.Prime := hprime p (Finset.mem_insert_self p T)
      have hTprime : ∀ r ∈ T, r.Prime := by
        intro r hr
        exact hprime r (Finset.mem_insert_of_mem hr)
      have hcop : p.Coprime (primeProduct T) := by
        rw [hp.coprime_iff_not_dvd]
        intro hdiv
        rw [primeProduct] at hdiv
        obtain ⟨r, hr, hpr⟩ :=
          (_root_.Prime.dvd_finsetProd_iff hp.prime (fun r : ℕ ↦ r)).mp hdiv
        exact hpT (((Nat.prime_dvd_prime_iff_eq hp (hTprime r hr)).mp hpr) ▸ hr)
      rw [primeProduct_insert hpT]
      constructor
      · intro hd r hr
        rcases Finset.mem_insert.mp hr with hpr | hrT
        · subst r
          exact dvd_trans (dvd_mul_right p (primeProduct T)) hd
        · exact dvd_trans (dvd_mul_of_dvd_right
            (Finset.dvd_prod_of_mem (fun z : ℕ ↦ z) hrT) p) hd
      · intro hall
        apply hcop.mul_dvd_of_dvd_of_dvd
        · exact hall p (Finset.mem_insert_self p T)
        · apply (ih hTprime).mpr
          intro r hr
          exact hall r (Finset.mem_insert_of_mem hr)

/-- There are exactly `Y / d` positive multiples of a positive `d` not
exceeding `Y`. -/
theorem card_Icc_filter_dvd {d Y : ℕ} (hd : 0 < d) :
    ((Icc 1 Y).filter (fun j ↦ d ∣ j)).card = Y / d := by
  let s := (Icc 1 Y).filter (fun j ↦ d ∣ j)
  let u := Icc 1 (Y / d)
  have hucard : u.card = Y / d := by
    simp [u, Nat.card_Icc]
  rw [← hucard]
  change s.card = u.card
  apply Finset.card_bij (fun j _ ↦ j / d)
  · intro j hj
    have hjs := Finset.mem_filter.mp hj
    have hjI := Finset.mem_Icc.mp hjs.1
    have hjd := hjs.2
    apply Finset.mem_Icc.mpr
    constructor
    · obtain ⟨a, rfl⟩ := hjd
      have ha : 0 < a := Nat.pos_of_mul_pos_left hjI.1
      rw [Nat.mul_div_cancel_left a hd]
      omega
    · exact Nat.div_le_div_right hjI.2
  · intro a ha b hb hab
    have had := (Finset.mem_filter.mp ha).2
    have hbd := (Finset.mem_filter.mp hb).2
    calc
      a = a / d * d := (Nat.div_mul_cancel had).symm
      _ = b / d * d := by rw [hab]
      _ = b := Nat.div_mul_cancel hbd
  · intro a ha
    have haI := Finset.mem_Icc.mp ha
    refine ⟨d * a, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        constructor
        · exact Nat.mul_pos hd haI.1
        · have := (Nat.le_div_iff_mul_le hd).mp haI.2
          simpa [Nat.mul_comm] using this
      · exact dvd_mul_right d a
    · simp [hd]

/-- Exact positive-multiple indicator sum. -/
theorem sum_Icc_dvd_indicator {d Y : ℕ} (hd : 0 < d) :
    (∑ j ∈ Icc 1 Y, if d ∣ j then 1 else 0) = Y / d := by
  rw [← card_Icc_filter_dvd hd]
  exact (Finset.card_filter (fun j ↦ d ∣ j) (Icc 1 Y)).symm

/-- Pointwise subset expansion of the local CRT weight. -/
theorem rootBoxLocalWeight_subset_expansion (P : Finset ℕ) (K j : ℕ)
    (hK : 1 ≤ K) (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, K ≤ p) :
    rootBoxLocalWeight P K j =
      ∑ T ∈ P.powerset,
        rootBoxSubsetCoeff P K T * (if primeProduct T ∣ j then 1 else 0) := by
  classical
  unfold rootBoxLocalWeight
  calc
    (∏ p ∈ P, if p ∣ j then p - 1 else K - 1) =
        ∏ p ∈ P, ((if p ∣ j then p - K else 0) + (K - 1)) := by
          apply Finset.prod_congr rfl
          intro p hp
          have hpK : K ≤ p := hlarge p hp
          by_cases hpd : p ∣ j
          · simp only [hpd, if_true]
            omega
          · simp [hpd]
    _ = ∑ T ∈ P.powerset,
          (∏ p ∈ T, if p ∣ j then p - K else 0) *
            ∏ _p ∈ P \ T, (K - 1) := by
          exact Finset.prod_add (fun p ↦ if p ∣ j then p - K else 0)
            (fun _p ↦ K - 1) P
    _ = ∑ T ∈ P.powerset,
          rootBoxSubsetCoeff P K T * (if primeProduct T ∣ j then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro T hTP
          have hTsub : T ⊆ P := Finset.mem_powerset.mp hTP
          simp only [Finset.prod_const]
          unfold rootBoxSubsetCoeff
          have hTprime : ∀ p ∈ T, p.Prime :=
            fun p hp ↦ hprime p (hTsub hp)
          by_cases hdiv : primeProduct T ∣ j
          · have hall : ∀ p ∈ T, p ∣ j :=
              (primeProduct_dvd_iff_all_dvd T hTprime j).mp hdiv
            have hprod :
                (∏ p ∈ T, if p ∣ j then p - K else 0) =
                  ∏ p ∈ T, (p - K) := by
              apply Finset.prod_congr rfl
              intro p hp
              simp [hall p hp]
            rw [hprod]
            simp [hdiv, mul_assoc]
          · have hnotall : ¬ ∀ p ∈ T, p ∣ j := by
              intro hall
              exact hdiv ((primeProduct_dvd_iff_all_dvd T hTprime j).mpr hall)
            push_neg at hnotall
            obtain ⟨p, hpT, hpnd⟩ := hnotall
            have hzero :
                (∏ p ∈ T, if p ∣ j then p - K else 0) = 0 := by
              apply Finset.prod_eq_zero hpT
              simp [hpnd]
            rw [hzero]
            simp [hdiv]

/-- Exact divisor-sum formula for the first moment. -/
theorem rootBoxFirstMoment_subset_expansion (P : Finset ℕ) (K Y : ℕ)
    (hK : 1 ≤ K) (hprime : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, K ≤ p) :
    rootBoxFirstMoment P K Y =
      ∑ T ∈ P.powerset, rootBoxSubsetCoeff P K T * (Y / primeProduct T) := by
  classical
  unfold rootBoxFirstMoment
  calc
    (∑ j ∈ Icc 1 Y, rootBoxLocalWeight P K j) =
        ∑ j ∈ Icc 1 Y, ∑ T ∈ P.powerset,
          rootBoxSubsetCoeff P K T *
            (if primeProduct T ∣ j then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact rootBoxLocalWeight_subset_expansion P K j hK hprime hlarge
    _ = ∑ T ∈ P.powerset, ∑ j ∈ Icc 1 Y,
          rootBoxSubsetCoeff P K T *
            (if primeProduct T ∣ j then 1 else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ T ∈ P.powerset,
          rootBoxSubsetCoeff P K T * (Y / primeProduct T) := by
          apply Finset.sum_congr rfl
          intro T hTP
          have hTsub : T ⊆ P := Finset.mem_powerset.mp hTP
          have hdpos : 0 < primeProduct T := by
            unfold primeProduct
            apply Finset.prod_pos
            intro p hp
            exact (hprime p (hTsub hp)).pos
          rw [← Finset.mul_sum]
          congr 1
          exact sum_Icc_dvd_indicator hdpos

/-- Continuous version of the divisor expansion, before replacing floors. -/
noncomputable def rootBoxContinuousFirstMoment (P : Finset ℕ) (K Y : ℕ) : ℝ :=
  ∑ T ∈ P.powerset,
    (rootBoxSubsetCoeff P K T : ℝ) *
      ((Y : ℝ) / (primeProduct T : ℝ))

/-- Product of the local unit-group cardinalities. -/
def primeUnitCount (P : Finset ℕ) : ℕ :=
  ∏ p ∈ P, (p - 1)

/-- A real quotient lies less than one above its natural-number floor. -/
theorem natCast_div_lt_natDiv_add_one {Y d : ℕ} (hd : 0 < d) :
    (Y : ℝ) / (d : ℝ) < (Y / d : ℕ) + 1 := by
  rw [div_lt_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast (show Y < (Y / d + 1) * d by
    simpa [Nat.mul_comm] using Nat.lt_mul_div_succ Y hd)

/-- Replacing every floor by its real quotient only increases the positive
subset expansion. -/
theorem rootBoxFirstMoment_le_continuous (P : Finset ℕ) (K Y : ℕ)
    (hK : 1 ≤ K) (hprime : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, K ≤ p) :
    (rootBoxFirstMoment P K Y : ℝ) ≤ rootBoxContinuousFirstMoment P K Y := by
  classical
  rw [rootBoxFirstMoment_subset_expansion P K Y hK hprime hlarge]
  unfold rootBoxContinuousFirstMoment
  push_cast
  apply Finset.sum_le_sum
  intro T hTP
  gcongr
  exact Nat.cast_div_le

/-- The total floor-replacement error is at most the sum of all subset
coefficients. -/
theorem rootBoxContinuous_le_firstMoment_add_coeffSum
    (P : Finset ℕ) (K Y : ℕ)
    (hK : 1 ≤ K) (hprime : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, K ≤ p) :
    rootBoxContinuousFirstMoment P K Y ≤
      (rootBoxFirstMoment P K Y : ℝ) +
        ∑ T ∈ P.powerset, (rootBoxSubsetCoeff P K T : ℝ) := by
  classical
  rw [rootBoxFirstMoment_subset_expansion P K Y hK hprime hlarge]
  unfold rootBoxContinuousFirstMoment
  push_cast
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro T hTP
  have hTsub : T ⊆ P := Finset.mem_powerset.mp hTP
  have hdpos : 0 < primeProduct T := by
    unfold primeProduct
    apply Finset.prod_pos
    intro p hp
    exact (hprime p (hTsub hp)).pos
  have hfloor := (natCast_div_lt_natDiv_add_one (Y := Y) hdpos).le
  have hc : 0 ≤ (rootBoxSubsetCoeff P K T : ℝ) := by positivity
  nlinarith

/-- The subset coefficients sum exactly to the product of the local unit
cardinalities. -/
theorem sum_rootBoxSubsetCoeff (P : Finset ℕ) (K : ℕ)
    (hK : 1 ≤ K) (hlarge : ∀ p ∈ P, K ≤ p) :
    (∑ T ∈ P.powerset, rootBoxSubsetCoeff P K T) = primeUnitCount P := by
  classical
  unfold rootBoxSubsetCoeff primeUnitCount
  calc
    (∑ T ∈ P.powerset,
        (∏ p ∈ T, (p - K)) * (K - 1) ^ (P \ T).card) =
      ∑ T ∈ P.powerset,
        (∏ p ∈ T, (p - K)) * ∏ _p ∈ P \ T, (K - 1) := by
          apply Finset.sum_congr rfl
          intro T hTP
          simp
    _ = ∏ p ∈ P, ((p - K) + (K - 1)) := by
          rw [Finset.prod_add]
    _ = ∏ p ∈ P, (p - 1) := by
          apply Finset.prod_congr rfl
          intro p hp
          have hpK := hlarge p hp
          omega

/-- A cast subset coefficient divided by its prime product factors
coordinatewise. -/
theorem cast_rootBoxSubsetCoeff_div (P : Finset ℕ) (K : ℕ) (T : Finset ℕ)
    (hTP : T ⊆ P) (hK : 1 ≤ K) (hlarge : ∀ p ∈ P, K ≤ p) :
    (rootBoxSubsetCoeff P K T : ℝ) / (primeProduct T : ℝ) =
      (∏ p ∈ T, ((p - K : ℕ) : ℝ) / (p : ℝ)) *
        ∏ _p ∈ P \ T, ((K - 1 : ℕ) : ℝ) := by
  unfold rootBoxSubsetCoeff primeProduct
  push_cast
  simp only [Finset.prod_const]
  rw [Finset.prod_div_distrib]
  ring

/-- Closed Euler-product form of the continuous first moment. -/
theorem rootBoxContinuousFirstMoment_eq_euler (P : Finset ℕ) (K Y : ℕ)
    (hK : 1 ≤ K) (hlarge : ∀ p ∈ P, K ≤ p)
    (hpos : ∀ p ∈ P, 0 < p) :
    rootBoxContinuousFirstMoment P K Y =
      (Y : ℝ) * ∏ p ∈ P,
        ((K : ℝ) * ((p : ℝ) - 1) / (p : ℝ)) := by
  classical
  unfold rootBoxContinuousFirstMoment
  calc
    (∑ T ∈ P.powerset,
      (rootBoxSubsetCoeff P K T : ℝ) *
        ((Y : ℝ) / (primeProduct T : ℝ))) =
        (Y : ℝ) * ∑ T ∈ P.powerset,
          (rootBoxSubsetCoeff P K T : ℝ) /
            (primeProduct T : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro T hTP
          ring
    _ = (Y : ℝ) * ∑ T ∈ P.powerset,
          (∏ p ∈ T, ((p - K : ℕ) : ℝ) / (p : ℝ)) *
            ∏ _p ∈ P \ T, ((K - 1 : ℕ) : ℝ) := by
          congr 1
          apply Finset.sum_congr rfl
          intro T hTP
          exact cast_rootBoxSubsetCoeff_div P K T
            (Finset.mem_powerset.mp hTP) hK hlarge
    _ = (Y : ℝ) * ∏ p ∈ P,
          (((p - K : ℕ) : ℝ) / (p : ℝ) + ((K - 1 : ℕ) : ℝ)) := by
          rw [Finset.prod_add]
    _ = (Y : ℝ) * ∏ p ∈ P,
          ((K : ℝ) * ((p : ℝ) - 1) / (p : ℝ)) := by
          congr 1
          apply Finset.prod_congr rfl
          intro p hp
          rw [Nat.cast_sub (hlarge p hp), Nat.cast_sub hK]
          have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hpos p hp))
          field_simp
          ring

/-- The continuous Euler product is exactly `K^|P|` times the local-unit
count, divided by the prime product. -/
theorem rootBoxEuler_eq_normalized (P : Finset ℕ) (K : ℕ)
    (hpos : ∀ p ∈ P, 0 < p) :
    (∏ p ∈ P, ((K : ℝ) * ((p : ℝ) - 1) / (p : ℝ))) =
      ((K ^ P.card : ℕ) : ℝ) * (primeUnitCount P : ℝ) /
        (primeProduct P : ℝ) := by
  classical
  calc
    (∏ p ∈ P, ((K : ℝ) * ((p : ℝ) - 1) / (p : ℝ))) =
        (K : ℝ) ^ P.card *
          (∏ p ∈ P, (((p - 1 : ℕ) : ℝ))) /
            ∏ p ∈ P, (p : ℝ) := by
      rw [Finset.prod_div_distrib, Finset.prod_mul_distrib,
        Finset.prod_const]
      congr 2
      apply Finset.prod_congr rfl
      intro p hp
      have hp1 : 1 ≤ p := hpos p hp
      rw [Nat.cast_sub hp1]
      norm_num
    _ = ((K ^ P.card : ℕ) : ℝ) * (primeUnitCount P : ℝ) /
          (primeProduct P : ℝ) := by
      unfold primeUnitCount primeProduct
      push_cast
      rfl

/-- The exact first moment lies in the half-open interval of length
`primeUnitCount P` immediately below its continuous main term. -/
theorem rootBoxFirstMoment_sharp_bounds (P : Finset ℕ) (K Y : ℕ)
    (hK : 1 ≤ K) (hprime : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, K ≤ p) :
    (Y : ℝ) * ∏ p ∈ P,
          ((K : ℝ) * ((p : ℝ) - 1) / (p : ℝ)) -
        (primeUnitCount P : ℝ) ≤
      (rootBoxFirstMoment P K Y : ℝ) ∧
    (rootBoxFirstMoment P K Y : ℝ) ≤
      (Y : ℝ) * ∏ p ∈ P,
          ((K : ℝ) * ((p : ℝ) - 1) / (p : ℝ)) := by
  have hcont := rootBoxContinuousFirstMoment_eq_euler P K Y hK hlarge
    (fun p hp ↦ (hprime p hp).pos)
  constructor
  · have hlow := rootBoxContinuous_le_firstMoment_add_coeffSum
      P K Y hK hprime hlarge
    rw [hcont] at hlow
    have hcoeff := sum_rootBoxSubsetCoeff P K hK hlarge
    have hcoeffR :
        (∑ T ∈ P.powerset, (rootBoxSubsetCoeff P K T : ℝ)) =
          (primeUnitCount P : ℝ) := by
      exact_mod_cast hcoeff
    rw [hcoeffR] at hlow
    linarith
  · rw [← hcont]
    exact rootBoxFirstMoment_le_continuous P K Y hK hprime hlarge

/-- After division by the number of local unit tuples, the first moment differs
from `K^|P| Y / ∏P` by at most one, always on the lower side. -/
theorem normalized_rootBoxFirstMoment_bounds (P : Finset ℕ) (K Y : ℕ)
    (hK : 1 ≤ K) (hprime : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, K ≤ p) :
    (K ^ P.card : ℝ) * (Y : ℝ) / (primeProduct P : ℝ) - 1 ≤
        (rootBoxFirstMoment P K Y : ℝ) / (primeUnitCount P : ℝ) ∧
    (rootBoxFirstMoment P K Y : ℝ) / (primeUnitCount P : ℝ) ≤
        (K ^ P.card : ℝ) * (Y : ℝ) / (primeProduct P : ℝ) := by
  have hphi : 0 < primeUnitCount P := by
    unfold primeUnitCount
    apply Finset.prod_pos
    intro p hp
    have hp2 : 2 ≤ p := (hprime p hp).two_le
    omega
  have hb := rootBoxFirstMoment_sharp_bounds P K Y hK hprime hlarge
  rw [rootBoxEuler_eq_normalized P K (fun p hp ↦ (hprime p hp).pos)] at hb
  rw [Nat.cast_pow] at hb
  have hphiR : (0 : ℝ) < primeUnitCount P := by exact_mod_cast hphi
  constructor
  · apply (le_div_iff₀ hphiR).mpr
    calc
      ((K ^ P.card : ℝ) * (Y : ℝ) / (primeProduct P : ℝ) - 1) *
            (primeUnitCount P : ℝ) =
          (Y : ℝ) *
              ((K : ℝ) ^ P.card * (primeUnitCount P : ℝ) /
                (primeProduct P : ℝ)) -
            (primeUnitCount P : ℝ) := by ring
      _ ≤ (rootBoxFirstMoment P K Y : ℝ) := hb.1
  · apply (div_le_iff₀ hphiR).mpr
    calc
      (rootBoxFirstMoment P K Y : ℝ) ≤
          (Y : ℝ) *
            ((K : ℝ) ^ P.card * (primeUnitCount P : ℝ) /
              (primeProduct P : ℝ)) := hb.2
      _ = ((K ^ P.card : ℝ) * (Y : ℝ) /
            (primeProduct P : ℝ)) * (primeUnitCount P : ℝ) := by ring

/-- Union of the sets hit at one of the positive times up to `Y`. -/
def finiteHitUnion [DecidableEq α] (H : Finset α) (Y : ℕ)
    (hit : α → ℕ → Prop) [DecidableRel hit] : Finset α :=
  (Icc 1 Y).biUnion (fun j ↦ H.filter (fun h ↦ hit h j))

/-- Elements with no hit at any positive time up to `Y`. -/
def finiteNoHit [DecidableEq α] (H : Finset α) (Y : ℕ)
    (hit : α → ℕ → Prop) [DecidableRel hit] : Finset α :=
  H \ finiteHitUnion H Y hit

/-- Elementary finite union bound, stated in the form used for root boxes. -/
theorem card_finiteHitUnion_le_sum [DecidableEq α]
    (H : Finset α) (Y : ℕ) (hit : α → ℕ → Prop) [DecidableRel hit] :
    (finiteHitUnion H Y hit).card ≤
      ∑ j ∈ Icc 1 Y, (H.filter (fun h ↦ hit h j)).card := by
  exact Finset.card_biUnion_le

/-- If the one-time hit counts are the local CRT weights, the first-moment
bound implies that at least three quarters of the finite universe have no hit
up to `Y`.  This is the elementary lower-tail half of the root-box mean lemma. -/
theorem rootBox_three_quarters_noHit [DecidableEq α]
    (H : Finset α) (hit : α → ℕ → Prop) [DecidableRel hit]
    (P : Finset ℕ) (K Y : ℕ)
    (hK : 1 ≤ K) (hprime : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, K ≤ p)
    (hHcard : H.card = primeUnitCount P)
    (hlocal : ∀ j ∈ Icc 1 Y,
      (H.filter (fun h ↦ hit h j)).card = rootBoxLocalWeight P K j)
    (hsmall : 4 * K ^ P.card * Y ≤ primeProduct P) :
    3 * H.card ≤ 4 * (finiteNoHit H Y hit).card := by
  let U := finiteHitUnion H Y hit
  have hUsub : U ⊆ H := by
    intro h hh
    obtain ⟨j, hj, hjH⟩ := Finset.mem_biUnion.mp hh
    exact (Finset.mem_filter.mp hjH).1
  have hUleMoment : U.card ≤ rootBoxFirstMoment P K Y := by
    calc
      U.card ≤ ∑ j ∈ Icc 1 Y,
          (H.filter (fun h ↦ hit h j)).card :=
        card_finiteHitUnion_le_sum H Y hit
      _ = rootBoxFirstMoment P K Y := by
        unfold rootBoxFirstMoment
        apply Finset.sum_congr rfl
        intro j hj
        exact hlocal j hj
  have hfourMoment : 4 * rootBoxFirstMoment P K Y ≤ H.card := by
    rw [hHcard]
    have hq : 0 < primeProduct P := by
      unfold primeProduct
      apply Finset.prod_pos
      intro p hp
      exact (hprime p hp).pos
    have hphi : 0 < primeUnitCount P := by
      unfold primeUnitCount
      apply Finset.prod_pos
      intro p hp
      have hp2 : 2 ≤ p := (hprime p hp).two_le
      omega
    have hu :=
      (normalized_rootBoxFirstMoment_bounds P K Y hK hprime hlarge).2
    have hqR : (0 : ℝ) < primeProduct P := by exact_mod_cast hq
    have hphiR : (0 : ℝ) < primeUnitCount P := by exact_mod_cast hphi
    have hsmallR : (4 : ℝ) * (K ^ P.card : ℝ) * (Y : ℝ) ≤
        (primeProduct P : ℝ) := by exact_mod_cast hsmall
    have hmain : (K ^ P.card : ℝ) * (Y : ℝ) /
        (primeProduct P : ℝ) ≤ 1 / 4 := by
      rw [div_le_iff₀ hqR]
      nlinarith
    have hreal : (4 : ℝ) * (rootBoxFirstMoment P K Y : ℝ) ≤
        (primeUnitCount P : ℝ) := by
      rw [div_le_iff₀ hphiR] at hu
      nlinarith
    exact_mod_cast hreal
  have hfourU : 4 * U.card ≤ H.card := by omega
  have hnohit : finiteNoHit H Y hit = H \ U := by
    rfl
  rw [hnohit]
  have hcarddiff : (H \ U).card = H.card - U.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hUsub]
  rw [hcarddiff]
  omega

/-- If the expected number of hits is at most one quarter, then the exact
unnormalized first moment is at most one quarter of the local-unit universe. -/
theorem four_mul_rootBoxFirstMoment_le (P : Finset ℕ) (K Y : ℕ)
    (hK : 1 ≤ K) (hprime : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, K ≤ p)
    (hsmall : 4 * K ^ P.card * Y ≤ primeProduct P) :
    4 * rootBoxFirstMoment P K Y ≤ primeUnitCount P := by
  have hq : 0 < primeProduct P := by
    unfold primeProduct
    apply Finset.prod_pos
    intro p hp
    exact (hprime p hp).pos
  have hphi : 0 < primeUnitCount P := by
    unfold primeUnitCount
    apply Finset.prod_pos
    intro p hp
    have hp2 : 2 ≤ p := (hprime p hp).two_le
    omega
  have hu := (normalized_rootBoxFirstMoment_bounds P K Y hK hprime hlarge).2
  have hqR : (0 : ℝ) < primeProduct P := by exact_mod_cast hq
  have hphiR : (0 : ℝ) < primeUnitCount P := by exact_mod_cast hphi
  have hsmallR : (4 : ℝ) * (K ^ P.card : ℝ) * (Y : ℝ) ≤
      (primeProduct P : ℝ) := by exact_mod_cast hsmall
  have hmain : (K ^ P.card : ℝ) * (Y : ℝ) /
      (primeProduct P : ℝ) ≤ 1 / 4 := by
    rw [div_le_iff₀ hqR]
    nlinarith
  have : (4 : ℝ) * (rootBoxFirstMoment P K Y : ℝ) ≤
      (primeUnitCount P : ℝ) := by
    rw [div_le_iff₀ hphiR] at hu
    nlinarith
  exact_mod_cast this

end Erdos394
