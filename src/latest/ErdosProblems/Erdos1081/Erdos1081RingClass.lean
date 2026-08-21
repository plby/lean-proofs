import Mathlib.Algebra.Group.Action.Pointwise.Finset
import ErdosProblems.Erdos1081.Erdos1081Core

namespace Erdos1081

open Filter Finset Set

noncomputable section

/-- Once the available prime-ideal classes hit every class, a single sign
change reaches every target in the compatible square class. -/
theorem exists_signedProduct_eq_of_surjective_of_squareClass
    {G : Type*} [CommGroup G] {k : ℕ}
    (x : Fin k → G) (hx : Function.Surjective x) (c : G)
    (hclass :
      (QuotientGroup.mk' (classSquareSubgroup : Subgroup G)) (∏ i, x i) =
        (QuotientGroup.mk' (classSquareSubgroup : Subgroup G)) c) :
    ∃ sigma : Fin k → Bool, signedProduct sigma x = c := by
  classical
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_iff_div_mem] at hclass
  rcases hclass with ⟨y, hy⟩
  obtain ⟨i, hi⟩ := hx y
  let sigma : Fin k → Bool := fun j => decide (j = i)
  let R : G := ∏ j ∈ (Finset.univ.erase i), x j
  refine ⟨sigma, ?_⟩
  have hprod : (∏ j, x j) = x i * R := by
    dsimp [R]
    exact (Finset.mul_prod_erase Finset.univ x (Finset.mem_univ i)).symm
  have hsigned : signedProduct sigma x = (x i)⁻¹ * R := by
    unfold signedProduct
    calc
      (∏ j, if sigma j then (x j)⁻¹ else x j) =
          (if sigma i then (x i)⁻¹ else x i) *
            ∏ j ∈ (Finset.univ.erase i),
              (if sigma j then (x j)⁻¹ else x j) :=
        (Finset.mul_prod_erase Finset.univ
          (fun j => if sigma j then (x j)⁻¹ else x j)
          (Finset.mem_univ i)).symm
      _ = (x i)⁻¹ * R := by
        congr 1
        · simp [sigma]
        · dsimp [R]
          apply Finset.prod_congr rfl
          intro j hj
          have hji : j ≠ i := Finset.ne_of_mem_erase hj
          simp [sigma, hji]
  rw [hsigned, hi]
  change y ^ 2 = (∏ j, x j) / c at hy
  rw [hprod, hi] at hy
  have hrel : y * c = R := by
    calc
      y * c = y⁻¹ * (y ^ 2 * c) := by group
      _ = y⁻¹ * (((y * R) / c) * c) := by rw [hy]
      _ = R := by simp [div_eq_mul_inv, mul_assoc]
  rw [← hrel]
  group

/-- Failure to reach the target class, despite the necessary square-class
condition, forces the tuple of prime-ideal classes to miss an entire class.
This is the finite covering step behind the ring-class exceptional set. -/
theorem exists_missedClass_of_no_signedProduct_of_squareClass
    {G : Type*} [CommGroup G] {k : ℕ}
    (x : Fin k → G) (c : G)
    (hclass :
      (QuotientGroup.mk' (classSquareSubgroup : Subgroup G)) (∏ i, x i) =
        (QuotientGroup.mk' (classSquareSubgroup : Subgroup G)) c)
    (hmiss : ∀ sigma : Fin k → Bool, signedProduct sigma x ≠ c) :
    ∃ g : G, ∀ i : Fin k, x i ≠ g := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨sigma, hsigma⟩ :=
    exists_signedProduct_eq_of_surjective_of_squareClass x h c hclass
  exact hmiss sigma hsigma

/-- The finite parity count is controlled solely by the reciprocal mass of
the chosen prime set.  This generic form is used after adjoining the primes
belonging to one missed ring class to the ordinary inert-prime obstruction
set. -/
theorem parityAdmissibleCount_le_of_obstructionMass
    (L : Finset ℕ) (hLprime : ∀ l ∈ L, l.Prime)
    {N : ℕ} (hN : 2 ≤ N) :
    (parityAdmissibleCount L N : ℝ) ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          ((Erdos469.naturalLinearMertensLower / Real.log (N : ℝ))⁻¹ *
            Real.exp (-obstructionReciprocalMass (N + 1).primesBelow L +
              Erdos469.naturalSquareSeries)) := by
  calc
    (parityAdmissibleCount L N : ℝ) =
        ∑ n ∈ Finset.Icc 1 N, parityWeight L n :=
      (parityWeight_sum_eq_count L N).symm
    _ ≤ (HalberstamScratch.explicitMassConstant 1 1 + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
            ∏ p ∈ (N + 1).primesBelow,
              ∑' j : ℕ, parityWeight L (p ^ j) /
                ((p ^ j : ℕ) : ℝ) :=
      parityWeight_mean_le_euler L hLprime N hN
    _ = (HalberstamScratch.explicitMassConstant 1 1 + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
            ∏ p ∈ (N + 1).primesBelow,
              if p ∈ L then (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹
              else (1 - (p : ℝ)⁻¹)⁻¹ := by
      congr 1
      apply Finset.prod_congr rfl
      intro p hp
      exact parityWeight_eulerFactor hLprime p
        (Nat.prime_of_mem_primesBelow hp)
    _ ≤ (HalberstamScratch.explicitMassConstant 1 1 + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
            ((Erdos469.naturalLinearMertensLower / Real.log (N : ℝ))⁻¹ *
              Real.exp (-obstructionReciprocalMass (N + 1).primesBelow L +
                Erdos469.naturalSquareSeries)) := by
      have hlog : 0 < Real.log (N : ℝ) := by
        exact Real.log_pos (by
          exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hN))
      have hcoef : 0 ≤
          (HalberstamScratch.explicitMassConstant 1 1 + 1) *
            (N : ℝ) / Real.log (N : ℝ) := by
        exact div_nonneg
          (mul_nonneg
            (add_nonneg
              (HalberstamScratch.explicitMassConstant_nonneg
                (by norm_num) (by norm_num))
              (by norm_num))
            (Nat.cast_nonneg N)) hlog.le
      exact mul_le_mul_of_nonneg_left
        (explicitParityEulerProduct_le_of_mass L hN) hcoef

/-- A reciprocal mass `beta * log log N`, up to an additive constant,
turns the generic parity-sieve estimate into the power saving
`N / (log N)^beta`. -/
theorem parityAdmissibleCount_le_rpow_of_obstructionMassLower
    (L : Finset ℕ) (hLprime : ∀ l ∈ L, l.Prime)
    {N : ℕ} {beta C : ℝ} (hN : 3 ≤ N)
    (hmass : beta * Real.log (Real.log (N : ℝ)) - C ≤
      obstructionReciprocalMass (N + 1).primesBelow L) :
    (parityAdmissibleCount L N : ℝ) ≤
      ((HalberstamScratch.explicitMassConstant 1 1 + 1) /
          Erdos469.naturalLinearMertensLower *
        Real.exp (C + Erdos469.naturalSquareSeries)) *
          (N : ℝ) / (Real.log (N : ℝ)) ^ beta := by
  have hlog : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hbase := parityAdmissibleCount_le_of_obstructionMass
    L hLprime (show 2 ≤ N by omega)
  have hexp :
      Real.exp (-obstructionReciprocalMass (N + 1).primesBelow L +
          Erdos469.naturalSquareSeries) ≤
        (Real.log (N : ℝ)) ^ (-beta) *
          Real.exp (C + Erdos469.naturalSquareSeries) := by
    calc
      Real.exp (-obstructionReciprocalMass (N + 1).primesBelow L +
          Erdos469.naturalSquareSeries) ≤
          Real.exp (-beta * Real.log (Real.log (N : ℝ)) + C +
            Erdos469.naturalSquareSeries) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = Real.exp ((-beta) * Real.log (Real.log (N : ℝ))) *
          Real.exp (C + Erdos469.naturalSquareSeries) := by
        rw [show -beta * Real.log (Real.log (N : ℝ)) + C +
            Erdos469.naturalSquareSeries =
              (-beta) * Real.log (Real.log (N : ℝ)) +
                (C + Erdos469.naturalSquareSeries) by ring,
          Real.exp_add]
      _ = (Real.log (N : ℝ)) ^ (-beta) *
          Real.exp (C + Erdos469.naturalSquareSeries) := by
        rw [Real.rpow_def_of_pos hlog]
        congr 2
        ring
  have hinv : 0 ≤
      (Erdos469.naturalLinearMertensLower / Real.log (N : ℝ))⁻¹ := by
    exact inv_nonneg.mpr (div_nonneg
      Erdos469.naturalLinearMertensLower_pos.le hlog.le)
  have hcoef : 0 ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) := by
    exact div_nonneg
      (mul_nonneg
        (add_nonneg
          (HalberstamScratch.explicitMassConstant_nonneg
            (by norm_num) (by norm_num))
          (by norm_num))
        (Nat.cast_nonneg N)) hlog.le
  calc
    (parityAdmissibleCount L N : ℝ) ≤
        (HalberstamScratch.explicitMassConstant 1 1 + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
            ((Erdos469.naturalLinearMertensLower /
              Real.log (N : ℝ))⁻¹ *
              Real.exp (-obstructionReciprocalMass
                (N + 1).primesBelow L +
                Erdos469.naturalSquareSeries)) := hbase
    _ ≤ (HalberstamScratch.explicitMassConstant 1 1 + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
            ((Erdos469.naturalLinearMertensLower /
              Real.log (N : ℝ))⁻¹ *
              ((Real.log (N : ℝ)) ^ (-beta) *
                Real.exp (C + Erdos469.naturalSquareSeries))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hexp hinv) hcoef
    _ = ((HalberstamScratch.explicitMassConstant 1 1 + 1) /
          Erdos469.naturalLinearMertensLower *
        Real.exp (C + Erdos469.naturalSquareSeries)) *
          (N : ℝ) / (Real.log (N : ℝ)) ^ beta := by
      rw [Real.rpow_neg hlog.le]
      field_simp

/-- Any additional positive logarithmic-density contribution beyond the
ordinary half-dimensional obstruction makes the parity-sieved exceptional
set negligible on the Landau scale. -/
theorem eventually_parityAdmissibleCount_le_landauScale_mul_of_massLower
    (L : ℕ → Finset ℕ)
    (hLprime : ∀ N l, l ∈ L N → l.Prime)
    {beta C eta : ℝ} (hbeta : (1 / 2 : ℝ) < beta)
    (heta : 0 < eta)
    (hmass : ∀ᶠ N : ℕ in atTop,
      beta * Real.log (Real.log (N : ℝ)) - C ≤
        obstructionReciprocalMass (N + 1).primesBelow (L N)) :
    ∀ᶠ N : ℕ in atTop,
      (parityAdmissibleCount (L N) N : ℝ) ≤ eta * landauScale N := by
  let delta : ℝ := beta - 1 / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  let K : ℝ :=
    (HalberstamScratch.explicitMassConstant 1 1 + 1) /
        Erdos469.naturalLinearMertensLower *
      Real.exp (C + Erdos469.naturalSquareSeries)
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpowTop : Tendsto
      (fun N : ℕ => (Real.log (N : ℝ)) ^ delta) atTop atTop :=
    (tendsto_rpow_atTop hdelta).comp hlogTop
  have hlarge : ∀ᶠ N : ℕ in atTop,
      K / eta ≤ (Real.log (N : ℝ)) ^ delta :=
    (tendsto_atTop.1 hpowTop) (K / eta)
  filter_upwards [hmass, hlarge, eventually_ge_atTop 3] with
      N hmassN hlargeN hN
  have hlog : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hhalf : 0 < (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hlog _
  have hdeltaPos : 0 < (Real.log (N : ℝ)) ^ delta :=
    Real.rpow_pos_of_pos hlog _
  have hKeta : K ≤ eta * (Real.log (N : ℝ)) ^ delta := by
    simpa [mul_comm] using (div_le_iff₀ heta).mp hlargeN
  have hupper := parityAdmissibleCount_le_rpow_of_obstructionMassLower
    (L N) (hLprime N) hN hmassN
  calc
    (parityAdmissibleCount (L N) N : ℝ) ≤
        K * (N : ℝ) / (Real.log (N : ℝ)) ^ beta := hupper
    _ = K * (N : ℝ) /
        ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ) *
          (Real.log (N : ℝ)) ^ delta) := by
      rw [← Real.rpow_add hlog]
      congr 3
      dsimp [delta]
      ring
    _ ≤ (eta * (Real.log (N : ℝ)) ^ delta) * (N : ℝ) /
        ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ) *
          (Real.log (N : ℝ)) ^ delta) := by
      gcongr
    _ = eta * landauScale N := by
      rw [landauScale, Real.sqrt_eq_rpow]
      field_simp

/-- Reciprocal mass is additive when two disjoint prime collections are
adjoined inside the same ambient set. -/
theorem obstructionReciprocalMass_union_of_disjoint
    (P L B : Finset ℕ) (hdisj : Disjoint L B) :
    obstructionReciprocalMass P (L ∪ B) =
      obstructionReciprocalMass P L + obstructionReciprocalMass P B := by
  classical
  unfold obstructionReciprocalMass
  have hfilter : P.filter (fun p => p ∈ L ∪ B) =
      P.filter (fun p => p ∈ L) ∪ P.filter (fun p => p ∈ B) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  have hd : Disjoint (P.filter (fun p => p ∈ L))
      (P.filter (fun p => p ∈ B)) := by
    apply Finset.disjoint_left.mpr
    intro p hpL hpB
    exact Finset.disjoint_left.mp hdisj
      (Finset.mem_filter.mp hpL).2 (Finset.mem_filter.mp hpB).2
  rw [hfilter, Finset.sum_union hd]

/-- Positive integers satisfying the original parity conditions while
avoiding every prime in `B`. -/
noncomputable def parityAvoidanceValues
    (L B : Finset ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter fun n =>
    ParityAdmissible L n ∧ ∀ q ∈ B, ¬q ∣ n

/-- Avoiding an adjoined prime is stronger than imposing even valuation at
that prime, because the valuation is then zero. -/
theorem parityAvoidanceValues_subset_unionParity
    (L B : Finset ℕ) (hBprime : ∀ q ∈ B, q.Prime) (N : ℕ) :
    ∀ n ∈ parityAvoidanceValues L B N,
      n ∈ Finset.Icc 1 N ∧ ParityAdmissible (L ∪ B) n := by
  classical
  intro n hn
  rw [parityAvoidanceValues, Finset.mem_filter] at hn
  refine ⟨hn.1, ?_⟩
  intro q hq
  rcases Finset.mem_union.mp hq with hqL | hqB
  · exact hn.2.1 q hqL
  · have hqndvd := hn.2.2 q hqB
    rw [padicValNat.eq_zero_of_not_dvd hqndvd]
    exact Even.zero

theorem parityAvoidanceValues_card_le_parityAdmissibleCount
    (L B : Finset ℕ) (hBprime : ∀ q ∈ B, q.Prime) (N : ℕ) :
    (parityAvoidanceValues L B N).card ≤
      parityAdmissibleCount (L ∪ B) N := by
  classical
  unfold parityAdmissibleCount
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter]
  exact parityAvoidanceValues_subset_unionParity L B hBprime N n hn

/-! ## A tilted parity weight for boundedly many exceptional primes -/

/-- The number of primes from `B` dividing `n`, without multiplicity. -/
def primeDivisorCount (B : Finset ℕ) (n : ℕ) : ℕ :=
  (B.filter fun q => q ∣ n).card

theorem primeDivisorCount_mul_of_coprime
    {B : Finset ℕ} (hBprime : ∀ q ∈ B, q.Prime)
    {m n : ℕ} (hcop : m.Coprime n) :
    primeDivisorCount B (m * n) =
      primeDivisorCount B m + primeDivisorCount B n := by
  classical
  let Bm := B.filter fun q => q ∣ m
  let Bn := B.filter fun q => q ∣ n
  have hfilter : B.filter (fun q => q ∣ m * n) = Bm ∪ Bn := by
    ext q
    constructor
    · intro hq
      have hqB : q ∈ B := (Finset.mem_filter.mp hq).1
      rcases (hBprime q hqB).dvd_mul.mp (Finset.mem_filter.mp hq).2 with
        hqm | hqn
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hqB, hqm⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hqB, hqn⟩)
    · intro hq
      rcases Finset.mem_union.mp hq with hqm | hqn
      · exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hqm).1,
            dvd_mul_of_dvd_left (Finset.mem_filter.mp hqm).2 n⟩
      · exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hqn).1,
            dvd_mul_of_dvd_right (Finset.mem_filter.mp hqn).2 m⟩
  have hdisj : Disjoint Bm Bn := by
    apply Finset.disjoint_left.mpr
    intro q hqm hqn
    have hqm' : q ∣ m := (Finset.mem_filter.mp hqm).2
    have hqn' : q ∣ n := (Finset.mem_filter.mp hqn).2
    have hqB : q ∈ B := (Finset.mem_filter.mp hqm).1
    exact (hBprime q hqB).ne_one
      (Nat.eq_one_of_dvd_coprimes hcop hqm' hqn')
  unfold primeDivisorCount
  rw [hfilter, Finset.card_union_of_disjoint hdisj]

/-- The half-tilted multiplicative weight: locally forbidden primes retain
their even-valuation condition, while each prime from `B` which occurs at
all contributes a factor `1/2`. -/
noncomputable def halfTiltedParityWeight
    (L B : Finset ℕ) (n : ℕ) : ℝ := by
  classical
  exact if n = 0 then 0
    else if ParityAdmissible L n then
      (1 / 2 : ℝ) ^ primeDivisorCount B n
    else 0

@[simp] theorem halfTiltedParityWeight_zero (L B : Finset ℕ) :
    halfTiltedParityWeight L B 0 = 0 := by
  simp [halfTiltedParityWeight]

theorem halfTiltedParityWeight_one (L B : Finset ℕ)
    (hBprime : ∀ q ∈ B, q.Prime) :
    halfTiltedParityWeight L B 1 = 1 := by
  have hfilter : B.filter (fun q => q ∣ 1) = ∅ := by
    classical
    apply Finset.filter_eq_empty_iff.mpr
    intro q hq hqdvd
    exact (hBprime q hq).not_dvd_one hqdvd
  have hcount : primeDivisorCount B 1 = 0 := by
    unfold primeDivisorCount
    rw [hfilter]
    rfl
  rw [halfTiltedParityWeight, if_neg one_ne_zero,
    if_pos (by simp [ParityAdmissible]), hcount]
  norm_num

theorem halfTiltedParityWeight_nonneg (L B : Finset ℕ) (n : ℕ) :
    0 ≤ halfTiltedParityWeight L B n := by
  unfold halfTiltedParityWeight
  split_ifs <;> positivity

theorem halfTiltedParityWeight_le_one (L B : Finset ℕ) (n : ℕ) :
    halfTiltedParityWeight L B n ≤ 1 := by
  unfold halfTiltedParityWeight
  split_ifs
  · norm_num
  · exact pow_le_one₀ (by norm_num) (by norm_num)
  · norm_num

theorem halfTiltedParityWeight_mul_of_coprime
    {L B : Finset ℕ}
    (hLprime : ∀ l ∈ L, l.Prime)
    (hBprime : ∀ q ∈ B, q.Prime)
    {m n : ℕ} (hcop : m.Coprime n) :
    halfTiltedParityWeight L B (m * n) =
      halfTiltedParityWeight L B m * halfTiltedParityWeight L B n := by
  by_cases hm : m = 0
  · subst m
    simp [halfTiltedParityWeight]
  by_cases hn : n = 0
  · subst n
    simp [halfTiltedParityWeight]
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  rw [halfTiltedParityWeight, halfTiltedParityWeight,
    halfTiltedParityWeight, if_neg hm, if_neg hn, if_neg hmn]
  have hadm := parityAdmissible_mul_iff_of_coprime hLprime hm hn hcop
  have hcount := primeDivisorCount_mul_of_coprime hBprime hcop
  by_cases hmAdm : ParityAdmissible L m <;>
    by_cases hnAdm : ParityAdmissible L n <;>
      simp [hmAdm, hnAdm, hadm, hcount, pow_add]

theorem halfTiltedParityWeight_prime_pow_le_one
    (L B : Finset ℕ) {p j : ℕ} (_hp : p.Prime) :
    halfTiltedParityWeight L B (p ^ (j + 1)) ≤ (1 : ℝ) * 1 ^ j := by
  simpa using halfTiltedParityWeight_le_one L B (p ^ (j + 1))

/-- Halberstam--Richert applied to the half-tilted weight. -/
theorem halfTiltedParityWeight_mean_le_euler
    (L B : Finset ℕ)
    (hLprime : ∀ l ∈ L, l.Prime)
    (hBprime : ∀ q ∈ B, q.Prime)
    (N : ℕ) (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, halfTiltedParityWeight L B n) ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          ∏ p ∈ (N + 1).primesBelow,
            ∑' j : ℕ, halfTiltedParityWeight L B (p ^ j) /
              ((p ^ j : ℕ) : ℝ) := by
  exact HalberstamComplete448.halberstam_richert_explicit
    (halfTiltedParityWeight L B)
    (halfTiltedParityWeight_zero L B)
    (halfTiltedParityWeight_one L B hBprime)
    (fun {_ _} hcop ↦ halfTiltedParityWeight_mul_of_coprime
      hLprime hBprime hcop)
    (halfTiltedParityWeight_nonneg L B) 1 1
    (by norm_num) (by norm_num) (by norm_num)
    (fun p hp j ↦ halfTiltedParityWeight_prime_pow_le_one L B hp)
    N hN

theorem primeDivisorCount_prime_pow
    {B : Finset ℕ} (hBprime : ∀ q ∈ B, q.Prime)
    (p j : ℕ) (hp : p.Prime) :
    primeDivisorCount B (p ^ j) =
      if p ∈ B ∧ j ≠ 0 then 1 else 0 := by
  classical
  by_cases h : p ∈ B ∧ j ≠ 0
  · rw [if_pos h]
    have hfilter : B.filter (fun q => q ∣ p ^ j) = {p} := by
      ext q
      constructor
      · intro hq
        have hqB := (Finset.mem_filter.mp hq).1
        have hqprime := hBprime q hqB
        have hqp : q ∣ p := hqprime.dvd_of_dvd_pow
          (Finset.mem_filter.mp hq).2
        have hqpEq : q = p :=
          (Nat.prime_dvd_prime_iff_eq hqprime hp).mp hqp
        simpa [hqpEq]
      · intro hq
        have hqpEq : q = p := Finset.mem_singleton.mp hq
        subst q
        exact Finset.mem_filter.mpr
          ⟨h.1, dvd_pow_self p h.2⟩
    unfold primeDivisorCount
    rw [hfilter]
    simp
  · rw [if_neg h]
    have hfilter : B.filter (fun q => q ∣ p ^ j) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro q hqB hqpow
      by_cases hj : j = 0
      · subst j
        exact (hBprime q hqB).not_dvd_one (by simpa using hqpow)
      · have hqprime := hBprime q hqB
        have hqp : q ∣ p := hqprime.dvd_of_dvd_pow hqpow
        have hqpEq : q = p :=
          (Nat.prime_dvd_prime_iff_eq hqprime hp).mp hqp
        subst q
        exact h ⟨hqB, hj⟩
    unfold primeDivisorCount
    rw [hfilter]
    simp

theorem halfTiltedParityWeight_prime_pow
    {L B : Finset ℕ}
    (hLprime : ∀ l ∈ L, l.Prime)
    (hBprime : ∀ q ∈ B, q.Prime)
    (hdisj : Disjoint L B)
    (p j : ℕ) (hp : p.Prime) :
    halfTiltedParityWeight L B (p ^ j) =
      if p ∈ L then (if Even j then 1 else 0)
      else if p ∈ B then (if j = 0 then 1 else (1 / 2 : ℝ))
      else 1 := by
  rw [halfTiltedParityWeight, if_neg (pow_ne_zero _ hp.ne_zero)]
  rw [primeDivisorCount_prime_pow hBprime p j hp]
  by_cases hpL : p ∈ L
  · have hpB : p ∉ B := Finset.disjoint_left.mp hdisj hpL
    rw [if_pos hpL]
    by_cases hj : Even j <;>
      simp [hj, hpB, parityAdmissible_prime_pow_iff hLprime hp, hpL]
  · rw [if_neg hpL]
    by_cases hpB : p ∈ B
    · rw [if_pos hpB]
      by_cases hj0 : j = 0
      · subst j
        simp [ParityAdmissible]
      · simp [hj0, hpB, parityAdmissible_prime_pow_iff hLprime hp, hpL]
    · rw [if_neg hpB]
      simp [hpB, parityAdmissible_prime_pow_iff hLprime hp, hpL]

/-- Exact Euler factor for the half-tilted parity weight. -/
theorem halfTiltedParityWeight_eulerFactor
    {L B : Finset ℕ}
    (hLprime : ∀ l ∈ L, l.Prime)
    (hBprime : ∀ q ∈ B, q.Prime)
    (hdisj : Disjoint L B)
    (p : ℕ) (hp : p.Prime) :
    (∑' j : ℕ,
        halfTiltedParityWeight L B (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
      if p ∈ L then (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹
      else if p ∈ B then
        (1 - (1 / 2 : ℝ) * (p : ℝ)⁻¹) *
          (1 - (p : ℝ)⁻¹)⁻¹
      else (1 - (p : ℝ)⁻¹)⁻¹ := by
  let r : ℝ := (p : ℝ)⁻¹
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact (inv_lt_one₀ (by positivity : (0 : ℝ) < p)).2 hpR
  by_cases hpL : p ∈ L
  · rw [if_pos hpL]
    calc
      (∑' j : ℕ,
          halfTiltedParityWeight L B (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
          ∑' j : ℕ, if Even j then r ^ j else 0 := by
            apply tsum_congr
            intro j
            rw [halfTiltedParityWeight_prime_pow
              hLprime hBprime hdisj p j hp]
            simp [hpL, r, div_eq_mul_inv, inv_pow]
      _ = (1 - r ^ 2)⁻¹ := tsum_even_geometric1081 hr0 hr1
      _ = (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹ := by rfl
  · rw [if_neg hpL]
    by_cases hpB : p ∈ B
    · rw [if_pos hpB]
      have hgeom : Summable (fun j : ℕ => (1 / 2 : ℝ) * r ^ j) :=
        (summable_geometric_of_lt_one hr0 hr1).mul_left _
      have hdelta : Summable (fun j : ℕ =>
          if j = 0 then (1 / 2 : ℝ) else 0) :=
        (hasSum_ite_eq 0 (1 / 2 : ℝ)).summable
      calc
        (∑' j : ℕ,
            halfTiltedParityWeight L B (p ^ j) /
              ((p ^ j : ℕ) : ℝ)) =
            ∑' j : ℕ,
              ((1 / 2 : ℝ) * r ^ j +
                if j = 0 then (1 / 2 : ℝ) else 0) := by
              apply tsum_congr
              intro j
              rw [halfTiltedParityWeight_prime_pow
                hLprime hBprime hdisj p j hp]
              by_cases hj : j = 0
              · subst j
                norm_num
              · simp [hpL, hpB, hj, r, div_eq_mul_inv, inv_pow]
        _ = (1 / 2 : ℝ) * (∑' j : ℕ, r ^ j) + 1 / 2 := by
          rw [hgeom.tsum_add hdelta, tsum_mul_left, tsum_ite_eq]
        _ = (1 / 2 : ℝ) * (1 - r)⁻¹ + 1 / 2 := by
          rw [tsum_geometric_of_lt_one hr0 hr1]
        _ = (1 - (1 / 2 : ℝ) * r) * (1 - r)⁻¹ := by
          have hrne : 1 - r ≠ 0 := sub_ne_zero.mpr (ne_of_gt hr1)
          field_simp
          ring
        _ = (1 - (1 / 2 : ℝ) * (p : ℝ)⁻¹) *
            (1 - (p : ℝ)⁻¹)⁻¹ := by rfl
    · rw [if_neg hpB]
      calc
        (∑' j : ℕ,
            halfTiltedParityWeight L B (p ^ j) /
              ((p ^ j : ℕ) : ℝ)) = ∑' j : ℕ, r ^ j := by
              apply tsum_congr
              intro j
              rw [halfTiltedParityWeight_prime_pow
                hLprime hBprime hdisj p j hp]
              simp [hpL, hpB, r, div_eq_mul_inv, inv_pow]
        _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
        _ = (1 - (p : ℝ)⁻¹)⁻¹ := by rfl

/-- The additional Euler-product penalty for charging a factor `1/2` when
a prime from `B` occurs. -/
noncomputable def halfOccurrencePenalty (B : Finset ℕ) (p : ℕ) : ℝ :=
  if p ∈ B then 1 - (1 / 2 : ℝ) * (p : ℝ)⁻¹ else 1

theorem halfOccurrencePenalty_nonneg
    (B : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    0 ≤ halfOccurrencePenalty B p := by
  unfold halfOccurrencePenalty
  by_cases hpB : p ∈ B
  · rw [if_pos hpB]
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      simpa [one_div] using
        (inv_le_inv₀ (by positivity : (0 : ℝ) < p)
          (by norm_num : (0 : ℝ) < 2)).2 hpR
    nlinarith
  · rw [if_neg hpB]
    norm_num

theorem halfOccurrencePenalty_le_exp
    (B : Finset ℕ) {p : ℕ} (_hp : p.Prime) :
    halfOccurrencePenalty B p ≤
      Real.exp (if p ∈ B then -(1 / 2 : ℝ) * (p : ℝ)⁻¹ else 0) := by
  unfold halfOccurrencePenalty
  by_cases hpB : p ∈ B
  · rw [if_pos hpB, if_pos hpB]
    simpa [sub_eq_add_neg, add_comm] using
      Real.add_one_le_exp (-(1 / 2 : ℝ) * (p : ℝ)⁻¹)
  · simp [hpB]

theorem halfOccurrencePenalty_prod_le_exp
    (P B : Finset ℕ) (hPprime : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, halfOccurrencePenalty B p) ≤
      Real.exp (-(1 / 2 : ℝ) * obstructionReciprocalMass P B) := by
  let S := P.filter fun p => p ∈ B
  have hprod : (∏ p ∈ P, halfOccurrencePenalty B p) ≤
      ∏ p ∈ P,
        Real.exp (if p ∈ B then
          -(1 / 2 : ℝ) * (p : ℝ)⁻¹ else 0) := by
    exact Finset.prod_le_prod
      (fun p hp => halfOccurrencePenalty_nonneg B (hPprime p hp))
      (fun p hp => halfOccurrencePenalty_le_exp B (hPprime p hp))
  calc
    (∏ p ∈ P, halfOccurrencePenalty B p) ≤
        ∏ p ∈ P,
          Real.exp (if p ∈ B then
            -(1 / 2 : ℝ) * (p : ℝ)⁻¹ else 0) := hprod
    _ = Real.exp (∑ p ∈ P,
          if p ∈ B then -(1 / 2 : ℝ) * (p : ℝ)⁻¹ else 0) := by
      rw [Real.exp_sum]
    _ = Real.exp (-(1 / 2 : ℝ) *
          (∑ p ∈ S, (p : ℝ)⁻¹)) := by
      congr 1
      dsimp [S]
      rw [← Finset.sum_filter, Finset.mul_sum]
    _ = Real.exp (-(1 / 2 : ℝ) *
          obstructionReciprocalMass P B) := by rfl

/-- Factor the tilted Euler product into the inverse Mertens product and
the two independent penalties. -/
theorem explicitHalfTiltedEulerProduct_eq
    (L B : Finset ℕ) (hdisj : Disjoint L B) (N : ℕ) :
    (∏ p ∈ (N + 1).primesBelow,
        if p ∈ L then (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹
        else if p ∈ B then
          (1 - (1 / 2 : ℝ) * (p : ℝ)⁻¹) *
            (1 - (p : ℝ)⁻¹)⁻¹
        else (1 - (p : ℝ)⁻¹)⁻¹) =
      ((∏ p ∈ (N + 1).primesBelow,
          Erdos469.mertensLinearFactor p)⁻¹) *
        (∏ p ∈ (N + 1).primesBelow, obstructionPenalty L p) *
        ∏ p ∈ (N + 1).primesBelow, halfOccurrencePenalty B p := by
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime := Nat.prime_of_mem_primesBelow hp
  have hparity := explicitParityEulerFactor_eq_mertens_mul_penalty L hpprime
  by_cases hpL : p ∈ L
  · have hpB : p ∉ B := Finset.disjoint_left.mp hdisj hpL
    rw [if_pos hpL] at hparity
    rw [if_pos hpL]
    simpa [halfOccurrencePenalty, hpB] using hparity
  · rw [if_neg hpL]
    rw [if_neg hpL] at hparity
    by_cases hpB : p ∈ B
    · rw [if_pos hpB]
      rw [hparity]
      simp [halfOccurrencePenalty, hpB]
      ring
    · rw [if_neg hpB]
      simpa [halfOccurrencePenalty, hpB] using hparity

/-- Quantitative upper bound for the tilted Euler product. -/
theorem explicitHalfTiltedEulerProduct_le_of_mass
    (L B : Finset ℕ) (hdisj : Disjoint L B)
    {N : ℕ} (hN : 2 ≤ N) :
    (∏ p ∈ (N + 1).primesBelow,
        if p ∈ L then (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹
        else if p ∈ B then
          (1 - (1 / 2 : ℝ) * (p : ℝ)⁻¹) *
            (1 - (p : ℝ)⁻¹)⁻¹
        else (1 - (p : ℝ)⁻¹)⁻¹) ≤
      (Erdos469.naturalLinearMertensLower / Real.log (N : ℝ))⁻¹ *
        Real.exp (-obstructionReciprocalMass (N + 1).primesBelow L -
          (1 / 2 : ℝ) * obstructionReciprocalMass
            (N + 1).primesBelow B +
          Erdos469.naturalSquareSeries) := by
  let P := (N + 1).primesBelow
  have hlog : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast
      (lt_of_lt_of_le Nat.one_lt_two hN))
  have hbase : 0 < Erdos469.naturalLinearMertensLower /
      Real.log (N : ℝ) :=
    div_pos Erdos469.naturalLinearMertensLower_pos hlog
  have hPeq : P = Erdos469.primesThrough N :=
    primesBelow_succ_eq_primesThrough N
  have hlinearPos : 0 < ∏ p ∈ P, Erdos469.mertensLinearFactor p := by
    rw [hPeq]
    exact Erdos469.linearMertensProduct_pos N
  have hlinearLower : Erdos469.naturalLinearMertensLower /
      Real.log (N : ℝ) ≤ ∏ p ∈ P, Erdos469.mertensLinearFactor p := by
    rw [hPeq]
    exact (Erdos469.natural_linearMertensProduct_bounds hN).1
  have hinv : ((∏ p ∈ P, Erdos469.mertensLinearFactor p)⁻¹) ≤
      (Erdos469.naturalLinearMertensLower /
        Real.log (N : ℝ))⁻¹ :=
    (inv_le_inv₀ hlinearPos hbase).2 hlinearLower
  have hobs := obstructionPenalty_prod_le_exp P L
    (fun p hp => Nat.prime_of_mem_primesBelow hp)
  have hhalf := halfOccurrencePenalty_prod_le_exp P B
    (fun p hp => Nat.prime_of_mem_primesBelow hp)
  rw [explicitHalfTiltedEulerProduct_eq L B hdisj]
  have hobsnonneg : 0 ≤ ∏ p ∈ P, obstructionPenalty L p :=
    Finset.prod_nonneg fun p hp => obstructionPenalty_nonneg L
      (Nat.prime_of_mem_primesBelow hp)
  have hhalfnonneg : 0 ≤ ∏ p ∈ P, halfOccurrencePenalty B p :=
    Finset.prod_nonneg fun p hp => halfOccurrencePenalty_nonneg B
      (Nat.prime_of_mem_primesBelow hp)
  calc
    ((∏ p ∈ P, Erdos469.mertensLinearFactor p)⁻¹) *
          (∏ p ∈ P, obstructionPenalty L p) *
          ∏ p ∈ P, halfOccurrencePenalty B p ≤
        (Erdos469.naturalLinearMertensLower /
            Real.log (N : ℝ))⁻¹ *
          Real.exp (-obstructionReciprocalMass P L +
            Erdos469.naturalSquareSeries) *
          Real.exp (-(1 / 2 : ℝ) * obstructionReciprocalMass P B) := by
      gcongr
    _ = (Erdos469.naturalLinearMertensLower /
            Real.log (N : ℝ))⁻¹ *
          Real.exp (-obstructionReciprocalMass P L -
            (1 / 2 : ℝ) * obstructionReciprocalMass P B +
            Erdos469.naturalSquareSeries) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- Positive integers which satisfy the original parity conditions and have
at most `R` distinct prime divisors from `B`. -/
noncomputable def parityFewPrimeDivisorValues
    (L B : Finset ℕ) (R N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter fun n =>
    ParityAdmissible L n ∧ primeDivisorCount B n ≤ R

theorem parityFewPrimeDivisorValues_card_le_weightedSum
    (L B : Finset ℕ) (R N : ℕ) :
    ((parityFewPrimeDivisorValues L B R N).card : ℝ) ≤
      (2 : ℝ) ^ R *
        ∑ n ∈ Finset.Icc 1 N, halfTiltedParityWeight L B n := by
  classical
  have hpoint : ∀ n ∈ parityFewPrimeDivisorValues L B R N,
      (1 : ℝ) ≤ (2 : ℝ) ^ R * halfTiltedParityWeight L B n := by
    intro n hn
    rw [parityFewPrimeDivisorValues, Finset.mem_filter] at hn
    have hn0 : n ≠ 0 := by
      exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one
        (Finset.mem_Icc.mp hn.1).1)
    rw [halfTiltedParityWeight, if_neg hn0, if_pos hn.2.1]
    have hpow : (1 / 2 : ℝ) ^ R ≤
        (1 / 2 : ℝ) ^ primeDivisorCount B n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn.2.2
    have htwo : 0 ≤ (2 : ℝ) ^ R := by positivity
    calc
      (1 : ℝ) = (2 : ℝ) ^ R * (1 / 2 : ℝ) ^ R := by
        rw [← mul_pow]
        norm_num
      _ ≤ (2 : ℝ) ^ R *
          (1 / 2 : ℝ) ^ primeDivisorCount B n :=
        mul_le_mul_of_nonneg_left hpow htwo
  calc
    ((parityFewPrimeDivisorValues L B R N).card : ℝ) =
        ∑ n ∈ parityFewPrimeDivisorValues L B R N, (1 : ℝ) := by
      simp
    _ ≤ ∑ n ∈ parityFewPrimeDivisorValues L B R N,
        (2 : ℝ) ^ R * halfTiltedParityWeight L B n :=
      Finset.sum_le_sum hpoint
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        (2 : ℝ) ^ R * halfTiltedParityWeight L B n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro n hnIcc hnFew
        exact mul_nonneg (by positivity)
          (halfTiltedParityWeight_nonneg L B n)
    _ = (2 : ℝ) ^ R *
        ∑ n ∈ Finset.Icc 1 N, halfTiltedParityWeight L B n := by
      rw [Finset.mul_sum]

/-- End-to-end finite sieve bound for integers having only boundedly many
prime divisors in the extra obstruction family. -/
theorem parityFewPrimeDivisorValues_card_le_of_mass
    (L B : Finset ℕ)
    (hLprime : ∀ l ∈ L, l.Prime)
    (hBprime : ∀ q ∈ B, q.Prime)
    (hdisj : Disjoint L B)
    (R : ℕ) {N : ℕ} (hN : 2 ≤ N) :
    ((parityFewPrimeDivisorValues L B R N).card : ℝ) ≤
      (2 : ℝ) ^ R *
        ((HalberstamScratch.explicitMassConstant 1 1 + 1) *
          (N : ℝ) / Real.log (N : ℝ)) *
        ((Erdos469.naturalLinearMertensLower / Real.log (N : ℝ))⁻¹ *
          Real.exp (-obstructionReciprocalMass (N + 1).primesBelow L -
            (1 / 2 : ℝ) * obstructionReciprocalMass
              (N + 1).primesBelow B +
            Erdos469.naturalSquareSeries)) := by
  have hweighted := halfTiltedParityWeight_mean_le_euler
    L B hLprime hBprime N hN
  have heval :
      (∏ p ∈ (N + 1).primesBelow,
          ∑' j : ℕ, halfTiltedParityWeight L B (p ^ j) /
            ((p ^ j : ℕ) : ℝ)) =
        ∏ p ∈ (N + 1).primesBelow,
          if p ∈ L then (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹
          else if p ∈ B then
            (1 - (1 / 2 : ℝ) * (p : ℝ)⁻¹) *
              (1 - (p : ℝ)⁻¹)⁻¹
          else (1 - (p : ℝ)⁻¹)⁻¹ := by
    apply Finset.prod_congr rfl
    intro p hp
    exact halfTiltedParityWeight_eulerFactor hLprime hBprime hdisj p
      (Nat.prime_of_mem_primesBelow hp)
  rw [heval] at hweighted
  have hproduct := explicitHalfTiltedEulerProduct_le_of_mass L B hdisj hN
  have hlog : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast
      (lt_of_lt_of_le Nat.one_lt_two hN))
  have hcoef : 0 ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) := by
    exact div_nonneg
      (mul_nonneg
        (add_nonneg
          (HalberstamScratch.explicitMassConstant_nonneg
            (by norm_num) (by norm_num))
          (by norm_num))
        (Nat.cast_nonneg N)) hlog.le
  calc
    ((parityFewPrimeDivisorValues L B R N).card : ℝ) ≤
        (2 : ℝ) ^ R *
          ∑ n ∈ Finset.Icc 1 N,
            halfTiltedParityWeight L B n :=
      parityFewPrimeDivisorValues_card_le_weightedSum L B R N
    _ ≤ (2 : ℝ) ^ R *
        ((HalberstamScratch.explicitMassConstant 1 1 + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
            (∏ p ∈ (N + 1).primesBelow,
              if p ∈ L then (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹
              else if p ∈ B then
                (1 - (1 / 2 : ℝ) * (p : ℝ)⁻¹) *
                  (1 - (p : ℝ)⁻¹)⁻¹
              else (1 - (p : ℝ)⁻¹)⁻¹)) := by
      gcongr
    _ ≤ (2 : ℝ) ^ R *
        ((HalberstamScratch.explicitMassConstant 1 1 + 1) *
          (N : ℝ) / Real.log (N : ℝ)) *
        ((Erdos469.naturalLinearMertensLower / Real.log (N : ℝ))⁻¹ *
          Real.exp (-obstructionReciprocalMass (N + 1).primesBelow L -
            (1 / 2 : ℝ) * obstructionReciprocalMass
              (N + 1).primesBelow B +
            Erdos469.naturalSquareSeries)) := by
      have hinner := mul_le_mul_of_nonneg_left hproduct hcoef
      have hout := mul_le_mul_of_nonneg_left hinner
        (show 0 ≤ (2 : ℝ) ^ R by positivity)
      simpa only [mul_assoc] using hout

/-- Separate lower bounds for the ordinary parity-obstruction mass and the
extra charged-prime mass give a power-saving exponent
`beta + delta / 2`. -/
theorem parityFewPrimeDivisorValues_card_le_rpow
    (L B : Finset ℕ)
    (hLprime : ∀ l ∈ L, l.Prime)
    (hBprime : ∀ q ∈ B, q.Prime)
    (hdisj : Disjoint L B)
    (R : ℕ) {N : ℕ} {beta delta C D : ℝ}
    (hN : 3 ≤ N)
    (hmassL : beta * Real.log (Real.log (N : ℝ)) - C ≤
      obstructionReciprocalMass (N + 1).primesBelow L)
    (hmassB : delta * Real.log (Real.log (N : ℝ)) - D ≤
      obstructionReciprocalMass (N + 1).primesBelow B) :
    ((parityFewPrimeDivisorValues L B R N).card : ℝ) ≤
      ((2 : ℝ) ^ R *
          (HalberstamScratch.explicitMassConstant 1 1 + 1) /
          Erdos469.naturalLinearMertensLower *
        Real.exp (C + (1 / 2 : ℝ) * D +
          Erdos469.naturalSquareSeries)) *
        (N : ℝ) /
          (Real.log (N : ℝ)) ^ (beta + (1 / 2 : ℝ) * delta) := by
  have hlog : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hbase := parityFewPrimeDivisorValues_card_le_of_mass
    L B hLprime hBprime hdisj R (show 2 ≤ N by omega)
  let gamma : ℝ := beta + (1 / 2 : ℝ) * delta
  have hexp :
      Real.exp (-obstructionReciprocalMass (N + 1).primesBelow L -
          (1 / 2 : ℝ) * obstructionReciprocalMass
            (N + 1).primesBelow B +
          Erdos469.naturalSquareSeries) ≤
        (Real.log (N : ℝ)) ^ (-gamma) *
          Real.exp (C + (1 / 2 : ℝ) * D +
            Erdos469.naturalSquareSeries) := by
    calc
      Real.exp (-obstructionReciprocalMass (N + 1).primesBelow L -
          (1 / 2 : ℝ) * obstructionReciprocalMass
            (N + 1).primesBelow B +
          Erdos469.naturalSquareSeries) ≤
          Real.exp (-gamma * Real.log (Real.log (N : ℝ)) +
            C + (1 / 2 : ℝ) * D +
            Erdos469.naturalSquareSeries) := by
        apply Real.exp_le_exp.mpr
        dsimp [gamma]
        linarith
      _ = Real.exp ((-gamma) * Real.log (Real.log (N : ℝ))) *
          Real.exp (C + (1 / 2 : ℝ) * D +
            Erdos469.naturalSquareSeries) := by
        rw [show -gamma * Real.log (Real.log (N : ℝ)) + C +
            (1 / 2 : ℝ) * D + Erdos469.naturalSquareSeries =
              (-gamma) * Real.log (Real.log (N : ℝ)) +
                (C + (1 / 2 : ℝ) * D +
                  Erdos469.naturalSquareSeries) by ring,
          Real.exp_add]
      _ = (Real.log (N : ℝ)) ^ (-gamma) *
          Real.exp (C + (1 / 2 : ℝ) * D +
            Erdos469.naturalSquareSeries) := by
        rw [Real.rpow_def_of_pos hlog]
        congr 2
        ring
  have hinv : 0 ≤
      (Erdos469.naturalLinearMertensLower / Real.log (N : ℝ))⁻¹ := by
    exact inv_nonneg.mpr (div_nonneg
      Erdos469.naturalLinearMertensLower_pos.le hlog.le)
  have hcoef : 0 ≤
      (2 : ℝ) ^ R *
        ((HalberstamScratch.explicitMassConstant 1 1 + 1) *
          (N : ℝ) / Real.log (N : ℝ)) := by
    exact mul_nonneg (by positivity) (div_nonneg
      (mul_nonneg
        (add_nonneg
          (HalberstamScratch.explicitMassConstant_nonneg
            (by norm_num) (by norm_num))
          (by norm_num))
        (Nat.cast_nonneg N)) hlog.le)
  calc
    ((parityFewPrimeDivisorValues L B R N).card : ℝ) ≤
        (2 : ℝ) ^ R *
          ((HalberstamScratch.explicitMassConstant 1 1 + 1) *
            (N : ℝ) / Real.log (N : ℝ)) *
          ((Erdos469.naturalLinearMertensLower /
              Real.log (N : ℝ))⁻¹ *
            Real.exp (-obstructionReciprocalMass
                (N + 1).primesBelow L -
              (1 / 2 : ℝ) * obstructionReciprocalMass
                (N + 1).primesBelow B +
              Erdos469.naturalSquareSeries)) := hbase
    _ ≤ (2 : ℝ) ^ R *
          ((HalberstamScratch.explicitMassConstant 1 1 + 1) *
            (N : ℝ) / Real.log (N : ℝ)) *
          ((Erdos469.naturalLinearMertensLower /
              Real.log (N : ℝ))⁻¹ *
            ((Real.log (N : ℝ)) ^ (-gamma) *
              Real.exp (C + (1 / 2 : ℝ) * D +
                Erdos469.naturalSquareSeries))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hexp hinv) hcoef
    _ = ((2 : ℝ) ^ R *
          (HalberstamScratch.explicitMassConstant 1 1 + 1) /
          Erdos469.naturalLinearMertensLower *
        Real.exp (C + (1 / 2 : ℝ) * D +
          Erdos469.naturalSquareSeries)) *
        (N : ℝ) /
          (Real.log (N : ℝ)) ^ (beta + (1 / 2 : ℝ) * delta) := by
      rw [show beta + (1 / 2 : ℝ) * delta = gamma by rfl,
        Real.rpow_neg hlog.le]
      field_simp

/-- If the combined tilted exponent exceeds `1/2`, integers satisfying the
ordinary local conditions but containing only boundedly many charged primes
are negligible on the Landau scale. -/
theorem eventually_parityFewPrimeDivisorValues_le_landauScale_mul
    (L B : ℕ → Finset ℕ)
    (hLprime : ∀ N l, l ∈ L N → l.Prime)
    (hBprime : ∀ N q, q ∈ B N → q.Prime)
    (hdisj : ∀ N, Disjoint (L N) (B N))
    (R : ℕ) {beta delta C D eta : ℝ}
    (hgamma : (1 / 2 : ℝ) < beta + (1 / 2 : ℝ) * delta)
    (heta : 0 < eta)
    (hmassL : ∀ᶠ N : ℕ in atTop,
      beta * Real.log (Real.log (N : ℝ)) - C ≤
        obstructionReciprocalMass (N + 1).primesBelow (L N))
    (hmassB : ∀ᶠ N : ℕ in atTop,
      delta * Real.log (Real.log (N : ℝ)) - D ≤
        obstructionReciprocalMass (N + 1).primesBelow (B N)) :
    ∀ᶠ N : ℕ in atTop,
      ((parityFewPrimeDivisorValues (L N) (B N) R N).card : ℝ) ≤
        eta * landauScale N := by
  let gamma : ℝ := beta + (1 / 2 : ℝ) * delta
  let excess : ℝ := gamma - 1 / 2
  have hexcess : 0 < excess := by
    dsimp [excess, gamma]
    linarith
  let K : ℝ :=
    (2 : ℝ) ^ R *
        (HalberstamScratch.explicitMassConstant 1 1 + 1) /
        Erdos469.naturalLinearMertensLower *
      Real.exp (C + (1 / 2 : ℝ) * D +
        Erdos469.naturalSquareSeries)
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpowTop : Tendsto
      (fun N : ℕ => (Real.log (N : ℝ)) ^ excess) atTop atTop :=
    (tendsto_rpow_atTop hexcess).comp hlogTop
  have hlarge : ∀ᶠ N : ℕ in atTop,
      K / eta ≤ (Real.log (N : ℝ)) ^ excess :=
    (tendsto_atTop.1 hpowTop) (K / eta)
  filter_upwards [hmassL, hmassB, hlarge, eventually_ge_atTop 3] with
      N hmassLN hmassBN hlargeN hN
  have hlog : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hhalf : 0 < (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hlog _
  have hexcessPos : 0 < (Real.log (N : ℝ)) ^ excess :=
    Real.rpow_pos_of_pos hlog _
  have hKeta : K ≤ eta * (Real.log (N : ℝ)) ^ excess := by
    simpa [mul_comm] using (div_le_iff₀ heta).mp hlargeN
  have hupper := parityFewPrimeDivisorValues_card_le_rpow
    (L N) (B N) (hLprime N) (hBprime N) (hdisj N) R hN
      hmassLN hmassBN
  calc
    ((parityFewPrimeDivisorValues (L N) (B N) R N).card : ℝ) ≤
        K * (N : ℝ) /
          (Real.log (N : ℝ)) ^ gamma := by
      simpa [K, gamma] using hupper
    _ = K * (N : ℝ) /
        ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ) *
          (Real.log (N : ℝ)) ^ excess) := by
      rw [← Real.rpow_add hlog]
      congr 3
      dsimp [excess]
      ring
    _ ≤ (eta * (Real.log (N : ℝ)) ^ excess) * (N : ℝ) /
        ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ) *
          (Real.log (N : ℝ)) ^ excess) := by
      gcongr
    _ = eta * landauScale N := by
      rw [landauScale, Real.sqrt_eq_rpow]
      field_simp

/-- The logarithmic-density hypothesis on the extra primes is stronger than
needed.  Once the ordinary obstruction primes supply the exact
`(1 / 2) * log log N` term, mere divergence of the reciprocal mass of the
extra primes makes the bounded-prime-factor exceptional set `o` of the
Landau scale.  This is the qualitative form needed for fixed ring-class
mixing. -/
theorem eventually_parityFewPrimeDivisorValues_le_landauScale_mul_of_tendstoMass
    (L B : ℕ → Finset ℕ)
    (hLprime : ∀ N l, l ∈ L N → l.Prime)
    (hBprime : ∀ N q, q ∈ B N → q.Prime)
    (hdisj : ∀ N, Disjoint (L N) (B N))
    (R : ℕ) {C eta : ℝ} (heta : 0 < eta)
    (hmassL : ∀ᶠ N : ℕ in atTop,
      (1 / 2 : ℝ) * Real.log (Real.log (N : ℝ)) - C ≤
        obstructionReciprocalMass (N + 1).primesBelow (L N))
    (hmassB : Tendsto
      (fun N : ℕ ↦ obstructionReciprocalMass
        (N + 1).primesBelow (B N)) atTop atTop) :
    ∀ᶠ N : ℕ in atTop,
      ((parityFewPrimeDivisorValues (L N) (B N) R N).card : ℝ) ≤
        eta * landauScale N := by
  let K : ℝ :=
    (2 : ℝ) ^ R *
        (HalberstamScratch.explicitMassConstant 1 1 + 1) /
        Erdos469.naturalLinearMertensLower *
      Real.exp (C + Erdos469.naturalSquareSeries)
  have hdecay : Tendsto
      (fun N : ℕ ↦ K * Real.exp (-(1 / 2 : ℝ) *
        obstructionReciprocalMass (N + 1).primesBelow (B N)))
      atTop (nhds 0) := by
    have hneg : Tendsto
        (fun N : ℕ ↦ -(1 / 2 : ℝ) *
          obstructionReciprocalMass (N + 1).primesBelow (B N))
        atTop atBot :=
      tendsto_const_mul_atBot_of_neg (by norm_num) |>.mpr hmassB
    simpa using (Real.tendsto_exp_atBot.comp hneg).const_mul K
  have hsmall : ∀ᶠ N : ℕ in atTop,
      K * Real.exp (-(1 / 2 : ℝ) *
        obstructionReciprocalMass (N + 1).primesBelow (B N)) < eta :=
    hdecay.eventually (Iio_mem_nhds heta)
  filter_upwards [hmassL, hsmall, eventually_ge_atTop 3] with
      N hmassLN hsmallN hN
  have hlog : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsqrt : 0 < Real.sqrt (Real.log (N : ℝ)) :=
    Real.sqrt_pos.2 hlog
  have hNnonneg : (0 : ℝ) ≤ N := by positivity
  have hbase := parityFewPrimeDivisorValues_card_le_of_mass
    (L N) (B N) (hLprime N) (hBprime N) (hdisj N) R
      (show 2 ≤ N by omega)
  have hexp :
      Real.exp (-obstructionReciprocalMass (N + 1).primesBelow (L N) -
          (1 / 2 : ℝ) * obstructionReciprocalMass
            (N + 1).primesBelow (B N) +
          Erdos469.naturalSquareSeries) ≤
        (Real.log (N : ℝ)) ^ (-(1 / 2 : ℝ)) *
          Real.exp (C + Erdos469.naturalSquareSeries) *
          Real.exp (-(1 / 2 : ℝ) * obstructionReciprocalMass
            (N + 1).primesBelow (B N)) := by
    calc
      Real.exp (-obstructionReciprocalMass (N + 1).primesBelow (L N) -
          (1 / 2 : ℝ) * obstructionReciprocalMass
            (N + 1).primesBelow (B N) +
          Erdos469.naturalSquareSeries) ≤
          Real.exp (-(1 / 2 : ℝ) * Real.log (Real.log (N : ℝ)) + C -
            (1 / 2 : ℝ) * obstructionReciprocalMass
              (N + 1).primesBelow (B N) +
            Erdos469.naturalSquareSeries) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = (Real.log (N : ℝ)) ^ (-(1 / 2 : ℝ)) *
          Real.exp (C + Erdos469.naturalSquareSeries) *
          Real.exp (-(1 / 2 : ℝ) * obstructionReciprocalMass
            (N + 1).primesBelow (B N)) := by
        rw [show -(1 / 2 : ℝ) * Real.log (Real.log (N : ℝ)) + C -
              (1 / 2 : ℝ) * obstructionReciprocalMass
                (N + 1).primesBelow (B N) +
              Erdos469.naturalSquareSeries =
            (-(1 / 2 : ℝ)) * Real.log (Real.log (N : ℝ)) +
              (C + Erdos469.naturalSquareSeries) +
              (-(1 / 2 : ℝ) * obstructionReciprocalMass
                (N + 1).primesBelow (B N)) by ring,
          Real.exp_add, Real.exp_add, Real.rpow_def_of_pos hlog]
        congr 3
        ring
  have hinv : 0 ≤
      (Erdos469.naturalLinearMertensLower / Real.log (N : ℝ))⁻¹ := by
    exact inv_nonneg.mpr (div_nonneg
      Erdos469.naturalLinearMertensLower_pos.le hlog.le)
  have hcoef : 0 ≤
      (2 : ℝ) ^ R *
        ((HalberstamScratch.explicitMassConstant 1 1 + 1) *
          (N : ℝ) / Real.log (N : ℝ)) := by
    have hH : 0 ≤ HalberstamScratch.explicitMassConstant 1 1 + 1 :=
      add_nonneg
        (HalberstamScratch.explicitMassConstant_nonneg (by norm_num) (by norm_num))
        (by norm_num)
    positivity
  calc
    ((parityFewPrimeDivisorValues (L N) (B N) R N).card : ℝ) ≤
        (2 : ℝ) ^ R *
          ((HalberstamScratch.explicitMassConstant 1 1 + 1) *
            (N : ℝ) / Real.log (N : ℝ)) *
          ((Erdos469.naturalLinearMertensLower / Real.log (N : ℝ))⁻¹ *
            Real.exp (-obstructionReciprocalMass
                (N + 1).primesBelow (L N) -
              (1 / 2 : ℝ) * obstructionReciprocalMass
                (N + 1).primesBelow (B N) +
              Erdos469.naturalSquareSeries)) := hbase
    _ ≤ (2 : ℝ) ^ R *
          ((HalberstamScratch.explicitMassConstant 1 1 + 1) *
            (N : ℝ) / Real.log (N : ℝ)) *
          ((Erdos469.naturalLinearMertensLower / Real.log (N : ℝ))⁻¹ *
            ((Real.log (N : ℝ)) ^ (-(1 / 2 : ℝ)) *
              Real.exp (C + Erdos469.naturalSquareSeries) *
              Real.exp (-(1 / 2 : ℝ) * obstructionReciprocalMass
                (N + 1).primesBelow (B N)))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hexp hinv) hcoef
    _ = (K * Real.exp (-(1 / 2 : ℝ) *
          obstructionReciprocalMass (N + 1).primesBelow (B N))) *
          landauScale N := by
      rw [landauScale, Real.sqrt_eq_rpow, Real.rpow_neg hlog.le]
      dsimp [K]
      field_simp
    _ ≤ eta * landauScale N := by
      exact mul_le_mul_of_nonneg_right (le_of_lt hsmallN)
        (div_nonneg hNnonneg hsqrt.le)

/-! ## Sharp reciprocal mass of the basic quadratic obstructions -/

/-- The nonsquare unit residue classes, represented as the complement of
the square subgroup inside all units. -/
noncomputable def nonSquareUnitClasses (p : ℕ) [Fact p.Prime] :
    Finset (ZMod p)ˣ := by
  classical
  exact Finset.univ \ squareUnitClasses p

theorem card_nonSquareUnitClasses {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (nonSquareUnitClasses p).card = (p - 1) / 2 := by
  classical
  have hsquareSub : squareUnitClasses p ⊆ (Finset.univ : Finset (ZMod p)ˣ) :=
    Finset.subset_univ _
  rw [nonSquareUnitClasses, Finset.card_sdiff,
    Finset.inter_eq_left.mpr hsquareSub,
    Finset.card_univ, ZMod.card_units, card_squareUnitClasses hp2]
  have hodd : p % 2 = 1 :=
    (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).2 hp2
  omega

theorem mem_nonSquareUnitClasses_iff
    {p : ℕ} [Fact p.Prime] {u : (ZMod p)ˣ} :
    u ∈ nonSquareUnitClasses p ↔ u ∉ unitSquareSubgroup p := by
  classical
  simp [nonSquareUnitClasses, squareUnitClasses]

/-- The global prime-power remainder is `O(x / log(x)^3)`. -/
theorem exists_eventually_psi_sub_theta_log_saving1081 :
    ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
      Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) ≤
        K * (x : ℝ) / Real.log (x : ℝ) ^ 3 := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hlogTendsto : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpolyRaw :=
    ((isLittleO_rpow_exp_pos_mul_atTop 3
      (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto hlogTendsto).eventuallyLE
  have hpoly : ∀ᶠ x : ℕ in atTop,
      Real.log (x : ℝ) ^ 3 ≤ Real.sqrt (x : ℝ) := by
    filter_upwards [hpolyRaw, eventually_ge_atTop 2] with x hx hx2
    have hlogpos : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    have hxpos : (0 : ℝ) < x := by positivity
    have hx' : Real.rpow (Real.log (x : ℝ)) (3 : ℝ) ≤
        Real.exp ((1 / 2 : ℝ) * Real.log (x : ℝ)) := by
      have hrpowpos : 0 < Real.rpow (Real.log (x : ℝ)) (3 : ℝ) :=
        Real.rpow_pos_of_pos hlogpos _
      change ‖Real.rpow (Real.log (x : ℝ)) (3 : ℝ)‖ ≤
        ‖Real.exp ((1 / 2 : ℝ) * Real.log (x : ℝ))‖ at hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hrpowpos,
        abs_of_pos (Real.exp_pos _)] at hx
      exact hx
    calc
      Real.log (x : ℝ) ^ 3 =
          Real.rpow (Real.log (x : ℝ)) (3 : ℝ) := by
        exact (Real.rpow_natCast _ 3).symm
      _ ≤ Real.exp ((1 / 2 : ℝ) * Real.log (x : ℝ)) := hx'
      _ = Real.sqrt (x : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hxpos]
        congr 1
        ring
  refine ⟨|C|, ?_⟩
  filter_upwards [hpoly, eventually_ge_atTop 2] with x hpolyx hx2
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hsqrt : Real.sqrt (x : ℝ) ^ 2 = (x : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrtBound : Real.sqrt (x : ℝ) ≤
      (x : ℝ) / Real.log (x : ℝ) ^ 3 := by
    rw [le_div_iff₀ (pow_pos hlogpos 3)]
    calc
      Real.sqrt (x : ℝ) * Real.log (x : ℝ) ^ 3 ≤
          Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) :=
        mul_le_mul_of_nonneg_left hpolyx (Real.sqrt_nonneg _)
      _ = (x : ℝ) := by nlinarith
  calc
    Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) ≤
        C * Real.sqrt (x : ℝ) := hC _
    _ ≤ |C| * Real.sqrt (x : ℝ) := by
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
    _ ≤ |C| * ((x : ℝ) / Real.log (x : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left hsqrtBound (abs_nonneg C)
    _ = |C| * (x : ℝ) / Real.log (x : ℝ) ^ 3 := by ring

theorem exists_eventually_fixed_modulus_theta_discrepancy1081
    (q : ℕ) (hq : 1 ≤ q) :
    ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
      BoundedGaps.Maynard.maxCenteredThetaProgressionDiscrepancyUpTo x q ≤
        K * (x : ℝ) / Real.log (x : ℝ) ^ 3 := by
  obtain ⟨Kd, hd⟩ :=
    exists_eventually_fixed_modulus_centered_discrepancy q hq
  obtain ⟨Kr, hr⟩ := exists_eventually_psi_sub_theta_log_saving1081
  refine ⟨Kd + Kr, ?_⟩
  filter_upwards [hd, hr] with x hdx hrx
  calc
    BoundedGaps.Maynard.maxCenteredThetaProgressionDiscrepancyUpTo x q ≤
        BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo x q +
          (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) :=
      BoundedGaps.Maynard.maxCenteredThetaProgressionDiscrepancyUpTo_le hq
    _ ≤ Kd * (x : ℝ) / Real.log (x : ℝ) ^ 3 +
          Kr * (x : ℝ) / Real.log (x : ℝ) ^ 3 :=
      add_le_add hdx hrx
    _ = (Kd + Kr) * (x : ℝ) / Real.log (x : ℝ) ^ 3 := by ring

theorem centeredThetaProgressionDiscrepancy_le_max1081
    {x q a : ℕ} (hx : 2 ≤ x) (hq : 0 < q)
    (haLt : a < q) (haCop : a.Coprime q) :
    |BoundedGaps.Maynard.thetaProgressionSum x q a -
        Chebyshev.theta (x : ℝ) / (q.totient : ℝ)| ≤
      BoundedGaps.Maynard.maxCenteredThetaProgressionDiscrepancyUpTo x q := by
  rw [BoundedGaps.Maynard.maxCenteredThetaProgressionDiscrepancyUpTo_eq_sup_endpoint_residues
    hx hq]
  apply Finset.le_sup'_of_le
    (fun y => (BoundedGaps.Maynard.coprimeResidues q).sup'
      (BoundedGaps.Maynard.coprimeResidues_nonempty hq)
      (fun b => |BoundedGaps.Maynard.thetaProgressionSum y q b -
        Chebyshev.theta (y : ℝ) / (q.totient : ℝ)|))
    (Finset.mem_Icc.mpr ⟨hx, le_rfl⟩)
  apply Finset.le_sup'_of_le
    (fun b => |BoundedGaps.Maynard.thetaProgressionSum x q b -
      Chebyshev.theta (x : ℝ) / (q.totient : ℝ)|)
  · show a ∈ BoundedGaps.Maynard.coprimeResidues q
    rw [BoundedGaps.Maynard.coprimeResidues, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨haLt, haCop⟩
  · exact le_rfl

theorem thetaAP_nat_eq_thetaProgressionSum1081
    {q a Q : ℕ} (ha : a < q) :
    Erdos387.thetaAP q a Q =
      BoundedGaps.Maynard.thetaProgressionSum Q q a := by
  rw [Erdos387.thetaAP_eq_sum_filter]
  unfold BoundedGaps.Maynard.thetaProgressionSum
  rw [Nat.primesLE_eq_filter_Icc_one]
  apply Finset.sum_congr
  · ext l
    simp [Nat.mod_eq_of_lt ha, and_left_comm, and_comm]
    exact fun _ _ hl => hl.one_le
  · intro l hl
    rfl

/-- A sharp PNT lower bound, summed over any fixed finite family of unit
residue classes. -/
theorem exists_eventually_unitClassThetaSum_lower1081
    {p : ℕ} [Fact p.Prime] (R : Finset (ZMod p)ˣ) :
    ∃ K : ℝ, ∀ᶠ Q : ℕ in atTop,
      (R.card : ℝ) * ((Q : ℝ) / (p.totient : ℝ)) -
          K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 ≤
        ∑ u ∈ R, Erdos387.thetaAP p (u.1 : ZMod p).val Q := by
  have hp : p.Prime := Fact.out
  obtain ⟨Kd, hd⟩ :=
    exists_eventually_fixed_modulus_theta_discrepancy1081 p hp.one_le
  obtain ⟨Kpsi, hpsi⟩ := exists_eventually_chebyshevPsi_log_saving
  obtain ⟨Kr, hr⟩ := exists_eventually_psi_sub_theta_log_saving1081
  let E : ℝ := Kd + (Kpsi + Kr) / (p.totient : ℝ)
  let K : ℝ := (R.card : ℝ) * E
  refine ⟨K, ?_⟩
  filter_upwards [hd, hpsi, hr, eventually_ge_atTop 4] with
      Q hdQ hpsiQ hrQ hQ4
  have hphiPos : (0 : ℝ) < p.totient := by
    exact_mod_cast Nat.totient_pos.mpr hp.one_le
  have hthetaGlobal :
      (Q : ℝ) - (Kpsi + Kr) * (Q : ℝ) /
          Real.log (Q : ℝ) ^ 3 ≤ Chebyshev.theta (Q : ℝ) := by
    rw [abs_le] at hpsiQ
    have hpsiLower :
        (Q : ℝ) - Kpsi * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 ≤
          Chebyshev.psi (Q : ℝ) := by
      linarith
    calc
      (Q : ℝ) - (Kpsi + Kr) * (Q : ℝ) /
            Real.log (Q : ℝ) ^ 3 =
          ((Q : ℝ) - Kpsi * (Q : ℝ) /
            Real.log (Q : ℝ) ^ 3) -
            Kr * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 := by ring
      _ ≤ Chebyshev.psi (Q : ℝ) -
            Kr * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 :=
        sub_le_sub_right hpsiLower _
      _ ≤ Chebyshev.theta (Q : ℝ) := by linarith
  have hpoint : ∀ u ∈ R,
      (Q : ℝ) / (p.totient : ℝ) -
          E * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 ≤
        Erdos387.thetaAP p (u.1 : ZMod p).val Q := by
    intro u hu
    have huLt : (u.1 : ZMod p).val < p := ZMod.val_lt _
    have huCop : (u.1 : ZMod p).val.Coprime p :=
      (ZMod.isUnit_iff_coprime _ _).mp (by
        simpa only [ZMod.natCast_zmod_val] using u.isUnit)
    have huDisc := centeredThetaProgressionDiscrepancy_le_max1081
      (x := Q) (q := p) (a := (u.1 : ZMod p).val)
      (by omega) hp.pos huLt huCop
    rw [abs_le] at huDisc
    rw [thetaAP_nat_eq_thetaProgressionSum1081 huLt]
    calc
      (Q : ℝ) / (p.totient : ℝ) -
          E * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 =
          ((Q : ℝ) - (Kpsi + Kr) * (Q : ℝ) /
              Real.log (Q : ℝ) ^ 3) / (p.totient : ℝ) -
            Kd * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 := by
        dsimp [E]
        field_simp
        ring
      _ ≤ Chebyshev.theta (Q : ℝ) / (p.totient : ℝ) -
            Kd * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 := by
        exact sub_le_sub_right
          (div_le_div_of_nonneg_right hthetaGlobal hphiPos.le) _
      _ ≤ BoundedGaps.Maynard.thetaProgressionSum Q p
            (u.1 : ZMod p).val := by
        linarith
  calc
    (R.card : ℝ) * ((Q : ℝ) / (p.totient : ℝ)) -
          K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 =
        (R.card : ℝ) *
          ((Q : ℝ) / (p.totient : ℝ) -
            E * (Q : ℝ) / Real.log (Q : ℝ) ^ 3) := by
      dsimp [K]
      ring
    _ = ∑ _u ∈ R,
          ((Q : ℝ) / (p.totient : ℝ) -
            E * (Q : ℝ) / Real.log (Q : ℝ) ^ 3) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ u ∈ R, Erdos387.thetaAP p (u.1 : ZMod p).val Q :=
      Finset.sum_le_sum hpoint

noncomputable def nonSquareUnitThetaSum
    (p : ℕ) [Fact p.Prime] (Q : ℕ) : ℝ :=
  ∑ u ∈ nonSquareUnitClasses p,
    Erdos387.thetaAP p (u.1 : ZMod p).val Q

theorem exists_eventually_nonSquareUnitThetaSum_sharp_lower
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ K : ℝ, ∀ᶠ Q : ℕ in atTop,
      (1 / 2 : ℝ) * (Q : ℝ) -
          K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 ≤
        nonSquareUnitThetaSum p Q := by
  obtain ⟨K, hK⟩ :=
    exists_eventually_unitClassThetaSum_lower1081
      (nonSquareUnitClasses p)
  refine ⟨K, ?_⟩
  filter_upwards [hK] with Q hQ
  have hphi : p.totient = p - 1 := Nat.totient_prime Fact.out
  have hcard := card_nonSquareUnitClasses (p := p) hp2
  have hpEven : 2 * ((p - 1) / 2) = p - 1 := by
    exact Nat.mul_div_cancel' (by
      have hodd : p % 2 = 1 :=
        (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).2 hp2
      omega)
  have hcardNat : 2 * (nonSquareUnitClasses p).card = p.totient := by
    rw [hcard, hphi]
    exact hpEven
  have hcardReal : 2 * ((nonSquareUnitClasses p).card : ℝ) =
      (p.totient : ℝ) := by exact_mod_cast hcardNat
  have hp : p.Prime := Fact.out
  have hphiPos : (0 : ℝ) < p.totient := by
    exact_mod_cast Nat.totient_pos.mpr hp.one_le
  have hhalf : ((nonSquareUnitClasses p).card : ℝ) *
      ((Q : ℝ) / (p.totient : ℝ)) = (1 / 2 : ℝ) * Q := by
    field_simp
    have hmul := congrArg (fun x : ℝ => (Q : ℝ) * x) hcardReal
    ring_nf at hmul ⊢
    exact hmul
  simpa [nonSquareUnitThetaSum, hhalf] using hQ

/-- Odd primes in nonsquare unit classes, collected without duplication. -/
noncomputable def nonSquareUnitPrimeTail
    (p N : ℕ) [Fact p.Prime] : Finset ℕ :=
  (nonSquareUnitClasses p).biUnion fun u =>
    Erdos387.primeIntervalAP p (u.1 : ZMod p).val 2 N

theorem pairwiseDisjoint_nonSquareUnitPrimeTail
    (p N : ℕ) [Fact p.Prime] :
    (((nonSquareUnitClasses p : Finset (ZMod p)ˣ) : Set (ZMod p)ˣ)).PairwiseDisjoint
      (fun u => Erdos387.primeIntervalAP p (u.1 : ZMod p).val 2 N) := by
  intro u hu v hv huv
  change Disjoint
    (Erdos387.primeIntervalAP p (u.1 : ZMod p).val 2 N)
    (Erdos387.primeIntervalAP p (v.1 : ZMod p).val 2 N)
  rw [Finset.disjoint_left]
  intro l hlu hlv
  have hluMod := (Finset.mem_filter.mp hlu).2.2
  have hlvMod := (Finset.mem_filter.mp hlv).2.2
  apply huv
  apply Units.ext
  apply ZMod.val_injective p
  exact hluMod.symm.trans hlvMod

theorem nonSquareUnitThetaSum_sub_eq_tail_sum
    {p N : ℕ} [Fact p.Prime] (hN : 2 ≤ N) :
    nonSquareUnitThetaSum p N - nonSquareUnitThetaSum p 2 =
      ∑ l ∈ nonSquareUnitPrimeTail p N, Real.log l := by
  classical
  unfold nonSquareUnitThetaSum nonSquareUnitPrimeTail
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ u ∈ nonSquareUnitClasses p,
        (Erdos387.thetaAP p (u.1 : ZMod p).val N -
          Erdos387.thetaAP p (u.1 : ZMod p).val 2)) =
        ∑ u ∈ nonSquareUnitClasses p,
          ∑ l ∈ Erdos387.primeIntervalAP p (u.1 : ZMod p).val 2 N,
            Real.log l := by
      apply Finset.sum_congr rfl
      intro u hu
      exact Erdos387.thetaAP_sub_eq_sum_interval _ _ (by exact_mod_cast hN)
    _ = ∑ l ∈ (nonSquareUnitClasses p).biUnion
          (fun u => Erdos387.primeIntervalAP p (u.1 : ZMod p).val 2 N),
          Real.log l := by
      exact (Finset.sum_biUnion
        (pairwiseDisjoint_nonSquareUnitPrimeTail p N)).symm

theorem obstruction_of_mem_nonSquareUnitAP
    {p l N : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3)
    {u : (ZMod p)ˣ} (hu : u ∈ nonSquareUnitClasses p)
    (hlmem : l ∈ Erdos387.primeIntervalAP p (u.1 : ZMod p).val 2 N) :
    IsQuadraticObstruction (p ^ 3) l := by
  have hp : p.Prime := Fact.out
  have hldata := Finset.mem_filter.mp hlmem
  have hlI := Finset.mem_Ioc.mp hldata.1
  have hl : l.Prime := hldata.2.1
  have hlmod : l % p = (u.1 : ZMod p).val := hldata.2.2
  have hlgt2 : 2 < l := by simpa using hlI.1
  have hl2 : l ≠ 2 := by omega
  have huNSq : ¬ IsSquare (u.1 : ZMod p) := by
    intro husq
    exact (mem_nonSquareUnitClasses_iff.mp hu)
      ((mem_unitSquareSubgroup_iff u).mpr husq)
  have hcast : (l : ZMod p) = (u.1 : ZMod p) := by
    calc
      (l : ZMod p) = ((u.1 : ZMod p).val : ZMod p) := by
        apply (ZMod.natCast_eq_natCast_iff' l (u.1 : ZMod p).val p).2
        simpa [Nat.mod_eq_of_lt (ZMod.val_lt (u.1 : ZMod p))] using hlmod
      _ = (u.1 : ZMod p) := ZMod.natCast_zmod_val _
  have hlsq : ¬ IsSquare (l : ZMod p) := by simpa [hcast] using huNSq
  have hlcast0 : (l : ZMod p) ≠ 0 := by
    rw [hcast]
    exact u.ne_zero
  have hleg : legendreSym p (l : ℤ) = -1 :=
    (legendreSym.eq_neg_one_iff (p := p) (a := (l : ℤ))).2
      (by simpa using hlsq)
  have hpl : p ≠ l := by
    intro h
    subst l
    have huval0 : (u.1 : ZMod p).val = 0 := by simpa using hlmod.symm
    exact u.ne_zero ((ZMod.val_eq_zero _).mp huval0)
  let _ : Fact l.Prime := ⟨hl⟩
  exact (isQuadraticObstruction_primeCube_iff_of_ne_two
    hp4 hl2 hpl).mpr hleg

/-- The finite set of quadratic-obstruction primes through `Q`. -/
noncomputable def specialObstructionPrimesFinite
    (p Q : ℕ) : Finset ℕ := by
  classical
  exact (Q + 1).primesBelow.filter
    (fun l => IsQuadraticObstruction (p ^ 3) l)

@[simp] theorem mem_specialObstructionPrimesFinite {p Q l : ℕ} :
    l ∈ specialObstructionPrimesFinite p Q ↔
      l.Prime ∧ l ≤ Q ∧ IsQuadraticObstruction (p ^ 3) l := by
  classical
  rw [specialObstructionPrimesFinite, Finset.mem_filter,
    Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨hlQ, hl⟩, hobs⟩
    exact ⟨hl, Nat.lt_succ_iff.mp (by simpa using hlQ), hobs⟩
  · rintro ⟨hl, hlQ, hobs⟩
    exact ⟨⟨by simpa using Nat.lt_succ_iff.mpr hlQ, hl⟩, hobs⟩

theorem nonSquareUnitPrimeTail_subset_obstruction
    {p N : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    nonSquareUnitPrimeTail p N ⊆ specialObstructionPrimesFinite p N := by
  intro l hlmem
  rw [nonSquareUnitPrimeTail, Finset.mem_biUnion] at hlmem
  rcases hlmem with ⟨u, hu, hlu⟩
  have hldata := Finset.mem_filter.mp hlu
  have hlI := Finset.mem_Ioc.mp hldata.1
  have hl : l.Prime := hldata.2.1
  have hlN : l ≤ N := by simpa using hlI.2
  rw [mem_specialObstructionPrimesFinite]
  exact ⟨hl, hlN, obstruction_of_mem_nonSquareUnitAP hp4 hu hlu⟩

noncomputable def specialObstructionPrimeLog (p Q : ℕ) : ℝ :=
  ∑ l ∈ specialObstructionPrimesFinite p Q, Real.log l

theorem nonSquareUnitPrimeTail_log_le_specialObstructionPrimeLog
    {p N : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    (∑ l ∈ nonSquareUnitPrimeTail p N, Real.log l) ≤
      specialObstructionPrimeLog p N := by
  classical
  unfold specialObstructionPrimeLog
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (nonSquareUnitPrimeTail_subset_obstruction hp4)
  intro l hl _
  exact Real.log_nonneg (by exact_mod_cast
    (mem_specialObstructionPrimesFinite.mp hl).1.one_le)

theorem exists_eventually_specialObstructionPrimeLog_sharp_lower
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ∃ K C : ℝ, ∀ᶠ Q : ℕ in atTop,
      (1 / 2 : ℝ) * (Q : ℝ) -
          K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 - C ≤
        specialObstructionPrimeLog p Q := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨K, htheta⟩ :=
    exists_eventually_nonSquareUnitThetaSum_sharp_lower (p := p) hp2
  let C : ℝ := nonSquareUnitThetaSum p 2
  refine ⟨K, C, ?_⟩
  filter_upwards [htheta, eventually_ge_atTop 2] with Q hthetaQ hQ2
  have htail := nonSquareUnitThetaSum_sub_eq_tail_sum (p := p) hQ2
  calc
    (1 / 2 : ℝ) * (Q : ℝ) -
        K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 - C ≤
        nonSquareUnitThetaSum p Q - C := sub_le_sub_right hthetaQ C
    _ = ∑ l ∈ nonSquareUnitPrimeTail p Q, Real.log l := htail
    _ ≤ specialObstructionPrimeLog p Q :=
      nonSquareUnitPrimeTail_log_le_specialObstructionPrimeLog hp4

theorem exists_global_specialObstructionPrimeLog_sharp_lower
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
      ∀ Q : ℕ, 3 ≤ Q →
        (1 / 2 : ℝ) * (Q : ℝ) -
            K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 - C ≤
          specialObstructionPrimeLog p Q := by
  obtain ⟨K₀, C₀, hlarge⟩ :=
    exists_eventually_specialObstructionPrimeLog_sharp_lower hp hp4
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.1 hlarge
  let K : ℝ := |K₀|
  let deficit (Q : ℕ) : ℝ :=
    (1 / 2 : ℝ) * (Q : ℝ) -
      K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 -
        specialObstructionPrimeLog p Q
  let D : ℝ := ∑ Q ∈ Finset.Ico 3 Q₀, |deficit Q|
  let C : ℝ := |C₀| + D
  refine ⟨K, C, abs_nonneg _, ?_, ?_⟩
  · exact add_nonneg (abs_nonneg _)
      (Finset.sum_nonneg fun Q hQ => abs_nonneg _)
  intro Q hQ3
  have hlog : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hratio : 0 ≤ (Q : ℝ) / Real.log (Q : ℝ) ^ 3 := by positivity
  by_cases hlate : Q₀ ≤ Q
  · have hbase := hQ₀ Q hlate
    have hK : K₀ ≤ K := le_abs_self K₀
    have hC : C₀ ≤ C := by
      dsimp [C]
      have hD : 0 ≤ D := by
        dsimp [D]
        exact Finset.sum_nonneg fun q hq => abs_nonneg _
      linarith [le_abs_self C₀]
    have hKratio :
        K₀ * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 ≤
          K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 := by
      calc
        K₀ * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 =
            K₀ * ((Q : ℝ) / Real.log (Q : ℝ) ^ 3) := by ring
        _ ≤ K * ((Q : ℝ) / Real.log (Q : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_right hK hratio
        _ = K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 := by ring
    exact hbase.trans' (by linarith)
  · have hQmem : Q ∈ Finset.Ico 3 Q₀ :=
      Finset.mem_Ico.mpr ⟨hQ3, by omega⟩
    have hterm : |deficit Q| ≤ D := by
      dsimp [D]
      exact Finset.single_le_sum
        (fun q hq => abs_nonneg (deficit q)) hQmem
    have hdef : deficit Q ≤ C := by
      dsimp [C]
      linarith [le_abs_self (deficit Q), abs_nonneg C₀]
    dsimp [deficit] at hdef
    exact sub_le_iff_le_add.mpr (by linarith)

noncomputable def specialObstructionPrimeLogIndicator
    (p n : ℕ) : ℝ := by
  classical
  exact if n.Prime ∧ IsQuadraticObstruction (p ^ 3) n then
    Real.log n else 0

noncomputable def specialObstructionPrimeLogHarmonic
    (p n : ℕ) : ℝ :=
  ∑ l ∈ specialObstructionPrimesFinite p n,
    Real.log l / (l : ℝ)

theorem sum_range_specialObstructionPrimeLogIndicator (p n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        specialObstructionPrimeLogIndicator p k) =
      specialObstructionPrimeLog p n := by
  classical
  unfold specialObstructionPrimeLogIndicator specialObstructionPrimeLog
  rw [show specialObstructionPrimesFinite p n =
      (Finset.range (n + 1)).filter
        (fun k => k.Prime ∧ IsQuadraticObstruction (p ^ 3) k) by
      ext k
      rw [mem_specialObstructionPrimesFinite, Finset.mem_filter,
        Finset.mem_range]
      constructor
      · rintro ⟨hkprime, hkn, hkobs⟩
        exact ⟨Nat.lt_succ_iff.mpr hkn, hkprime, hkobs⟩
      · rintro ⟨hkn, hkprime, hkobs⟩
        exact ⟨hkprime, Nat.lt_succ_iff.mp hkn, hkobs⟩,
    Finset.sum_filter]

theorem specialObstructionPrimeLogHarmonic_eq_abel
    (p : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    specialObstructionPrimeLogHarmonic p n =
      reciprocalNatWeight1081 n * specialObstructionPrimeLog p n +
        ∑ k ∈ Finset.Ico 2 n,
          reciprocalNatDifference1081 k * specialObstructionPrimeLog p k := by
  have hparts := Finset.sum_Ico_by_parts reciprocalNatWeight1081
    (specialObstructionPrimeLogIndicator p)
    (show 2 < n + 1 by omega)
  simp only [smul_eq_mul] at hparts
  have hleft :
      (∑ k ∈ Finset.Ico 2 (n + 1),
          reciprocalNatWeight1081 k *
            specialObstructionPrimeLogIndicator p k) =
        specialObstructionPrimeLogHarmonic p n := by
    classical
    unfold specialObstructionPrimeLogHarmonic
    calc
      (∑ k ∈ Finset.Ico 2 (n + 1),
          reciprocalNatWeight1081 k *
            specialObstructionPrimeLogIndicator p k) =
          ∑ k ∈ Finset.Ico 2 (n + 1),
            if k.Prime ∧ IsQuadraticObstruction (p ^ 3) k then
              Real.log k / (k : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        unfold reciprocalNatWeight1081
          specialObstructionPrimeLogIndicator
        by_cases h : k.Prime ∧ IsQuadraticObstruction (p ^ 3) k <;>
          simp [h, div_eq_mul_inv, mul_comm]
      _ = ∑ k ∈ (Finset.Ico 2 (n + 1)).filter
            (fun k => k.Prime ∧ IsQuadraticObstruction (p ^ 3) k),
            Real.log k / (k : ℝ) := by rw [Finset.sum_filter]
      _ = ∑ k ∈ specialObstructionPrimesFinite p n,
            Real.log k / (k : ℝ) := by
        apply Finset.sum_congr
        · ext k
          simp only [Finset.mem_filter, Finset.mem_Ico,
            mem_specialObstructionPrimesFinite]
          constructor
          · rintro ⟨⟨hk2, hkn⟩, hkprime, hkobs⟩
            exact ⟨hkprime, by omega, hkobs⟩
          · rintro ⟨hkprime, hkn, hkobs⟩
            exact ⟨⟨hkprime.two_le, by omega⟩, hkprime, hkobs⟩
        · intro k hk
          rfl
  rw [hleft] at hparts
  have hsum2 :
      (∑ k ∈ Finset.range 2,
        specialObstructionPrimeLogIndicator p k) = 0 := by
    classical
    norm_num [Finset.sum_range_succ,
      specialObstructionPrimeLogIndicator, IsQuadraticObstruction]
  rw [hsum2, mul_zero, sub_zero] at hparts
  simp only [Nat.add_sub_cancel] at hparts
  rw [sum_range_specialObstructionPrimeLogIndicator] at hparts
  rw [hparts, sub_eq_add_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sum_range_specialObstructionPrimeLogIndicator]
  simp only [reciprocalNatDifference1081]
  ring

theorem specialObstructionPrimeLog_nonneg (p Q : ℕ) :
    0 ≤ specialObstructionPrimeLog p Q := by
  classical
  unfold specialObstructionPrimeLog
  apply Finset.sum_nonneg
  intro l hl
  exact Real.log_nonneg (by exact_mod_cast
    (mem_specialObstructionPrimesFinite.mp hl).1.one_le)

theorem exists_specialObstructionPrimeLogHarmonic_lower
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ n : ℕ, 3 ≤ n →
      (1 / 2 : ℝ) * Real.log (n : ℝ) - E ≤
        specialObstructionPrimeLogHarmonic p n := by
  obtain ⟨K, C, hK, hC, htheta⟩ :=
    exists_global_specialObstructionPrimeLog_sharp_lower hp hp4
  let E₀ : ℝ := 2 * K + 2 * C + K / Real.log 2
  let E : ℝ := (1 / 2 : ℝ) * Real.log 4 + E₀
  have hE₀ : 0 ≤ E₀ := by
    dsimp [E₀]
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  refine ⟨E, hE, ?_⟩
  intro n hn
  let main : ℝ :=
    reciprocalNatWeight1081 n * ((1 / 2 : ℝ) * (n : ℝ)) +
      ∑ k ∈ Finset.Ico 3 n,
        reciprocalNatDifference1081 k * ((1 / 2 : ℝ) * (k : ℝ))
  let err : ℝ :=
    reciprocalNatWeight1081 n *
        (K * (n : ℝ) / Real.log (n : ℝ) ^ 3 + C) +
      ∑ k ∈ Finset.Ico 3 n,
        reciprocalNatDifference1081 k *
          (K * (k : ℝ) / Real.log (k : ℝ) ^ 3 + C)
  have hmain : (1 / 2 : ℝ) * Real.log (n : ℝ) -
      (1 / 2 : ℝ) * Real.log 4 ≤ main := by
    exact half_log_le_reciprocalNat_abel_main hn
  have herr : err ≤ E₀ := by
    exact reciprocalNat_abel_error_sum_le hK hC hn
  have hweight : 0 ≤ reciprocalNatWeight1081 n := by
    unfold reciprocalNatWeight1081
    positivity
  have hendpoint := mul_le_mul_of_nonneg_left (htheta n hn) hweight
  have hsum :
      (∑ k ∈ Finset.Ico 3 n,
        reciprocalNatDifference1081 k *
          ((1 / 2 : ℝ) * (k : ℝ) -
            K * (k : ℝ) / Real.log (k : ℝ) ^ 3 - C)) ≤
        ∑ k ∈ Finset.Ico 2 n,
          reciprocalNatDifference1081 k * specialObstructionPrimeLog p k := by
    calc
      _ ≤ ∑ k ∈ Finset.Ico 3 n,
          reciprocalNatDifference1081 k * specialObstructionPrimeLog p k := by
        apply Finset.sum_le_sum
        intro k hk
        have hk3 : 3 ≤ k := (Finset.mem_Ico.mp hk).1
        exact mul_le_mul_of_nonneg_left
          (htheta k hk3)
          (reciprocalNatDifference1081_nonneg
            ((show 1 ≤ 3 by norm_num).trans hk3))
      _ ≤ ∑ k ∈ Finset.Ico 2 n,
          reciprocalNatDifference1081 k * specialObstructionPrimeLog p k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          have hkI := Finset.mem_Ico.mp hk
          have hk2 : 2 ≤ k :=
            (show 2 ≤ 3 by norm_num).trans hkI.1
          exact Finset.mem_Ico.mpr
            ⟨hk2, hkI.2⟩
        · intro k hk hkn
          have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
          exact mul_nonneg
            (reciprocalNatDifference1081_nonneg
              ((show 1 ≤ 2 by norm_num).trans hk2))
            (specialObstructionPrimeLog_nonneg p k)
  have haber : main - err ≤ specialObstructionPrimeLogHarmonic p n := by
    rw [specialObstructionPrimeLogHarmonic_eq_abel p
      ((show 2 ≤ 3 by norm_num).trans hn)]
    have hcombined := add_le_add hendpoint hsum
    have hsumExpand :
        (∑ k ∈ Finset.Ico 3 n,
          reciprocalNatDifference1081 k *
            ((1 / 2 : ℝ) * (k : ℝ) -
              K * (k : ℝ) / Real.log (k : ℝ) ^ 3 - C)) =
        (∑ k ∈ Finset.Ico 3 n,
          reciprocalNatDifference1081 k *
            ((1 / 2 : ℝ) * (k : ℝ))) -
        ∑ k ∈ Finset.Ico 3 n,
          reciprocalNatDifference1081 k *
            (K * (k : ℝ) / Real.log (k : ℝ) ^ 3 + C) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    calc
      main - err =
          reciprocalNatWeight1081 n *
              ((1 / 2 : ℝ) * (n : ℝ) -
                K * (n : ℝ) / Real.log (n : ℝ) ^ 3 - C) +
            ∑ k ∈ Finset.Ico 3 n,
              reciprocalNatDifference1081 k *
                ((1 / 2 : ℝ) * (k : ℝ) -
                  K * (k : ℝ) / Real.log (k : ℝ) ^ 3 - C) := by
        dsimp [main, err]
        rw [hsumExpand]
        ring
      _ ≤ _ := hcombined
  dsimp [E]
  linarith

noncomputable def specialObstructionPrimeLogHarmonicIndicator
    (p n : ℕ) : ℝ := by
  classical
  exact if n.Prime ∧ IsQuadraticObstruction (p ^ 3) n then
    Real.log n / (n : ℝ) else 0

noncomputable def specialObstructionPrimeReciprocal
    (p n : ℕ) : ℝ :=
  ∑ l ∈ specialObstructionPrimesFinite p n, (l : ℝ)⁻¹

theorem sum_range_specialObstructionPrimeLogHarmonicIndicator
    (p n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        specialObstructionPrimeLogHarmonicIndicator p k) =
      specialObstructionPrimeLogHarmonic p n := by
  classical
  unfold specialObstructionPrimeLogHarmonicIndicator
    specialObstructionPrimeLogHarmonic
  rw [show specialObstructionPrimesFinite p n =
      (Finset.range (n + 1)).filter
        (fun k => k.Prime ∧
          IsQuadraticObstruction (p ^ 3) k) by
      ext k
      rw [mem_specialObstructionPrimesFinite, Finset.mem_filter,
        Finset.mem_range]
      constructor
      · rintro ⟨hkprime, hkn, hkobs⟩
        exact ⟨Nat.lt_succ_iff.mpr hkn, hkprime, hkobs⟩
      · rintro ⟨hkn, hkprime, hkobs⟩
        exact ⟨hkprime, Nat.lt_succ_iff.mp hkn, hkobs⟩,
    Finset.sum_filter]

theorem specialObstructionPrimeReciprocal_eq_abel
    (p : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    specialObstructionPrimeReciprocal p n =
      Erdos469.reciprocalLogWeight n *
          specialObstructionPrimeLogHarmonic p n +
        ∑ k ∈ Finset.Ico 2 n,
          Erdos469.reciprocalLogDifference k *
            specialObstructionPrimeLogHarmonic p k := by
  have hparts := Finset.sum_Ico_by_parts Erdos469.reciprocalLogWeight
    (specialObstructionPrimeLogHarmonicIndicator p)
    (show 2 < n + 1 by omega)
  simp only [smul_eq_mul] at hparts
  have hleft :
      (∑ k ∈ Finset.Ico 2 (n + 1),
          Erdos469.reciprocalLogWeight k *
            specialObstructionPrimeLogHarmonicIndicator p k) =
        specialObstructionPrimeReciprocal p n := by
    classical
    unfold specialObstructionPrimeReciprocal
    calc
      (∑ k ∈ Finset.Ico 2 (n + 1),
          Erdos469.reciprocalLogWeight k *
            specialObstructionPrimeLogHarmonicIndicator p k) =
          ∑ k ∈ Finset.Ico 2 (n + 1),
            if k.Prime ∧ IsQuadraticObstruction (p ^ 3) k then
              (k : ℝ)⁻¹ else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
        have hlog : Real.log (k : ℝ) ≠ 0 :=
          ne_of_gt (Real.log_pos (by exact_mod_cast
            (show 1 < k by omega)))
        unfold Erdos469.reciprocalLogWeight
          specialObstructionPrimeLogHarmonicIndicator
        by_cases h : k.Prime ∧
            IsQuadraticObstruction (p ^ 3) k
        · simp [h, div_eq_mul_inv, hlog]
        · simp [h]
      _ = ∑ k ∈ (Finset.Ico 2 (n + 1)).filter
            (fun k => k.Prime ∧
              IsQuadraticObstruction (p ^ 3) k),
            (k : ℝ)⁻¹ := by
        rw [Finset.sum_filter]
      _ = ∑ k ∈ specialObstructionPrimesFinite p n,
            (k : ℝ)⁻¹ := by
        apply Finset.sum_congr
        · ext k
          simp only [Finset.mem_filter, Finset.mem_Ico,
            mem_specialObstructionPrimesFinite]
          constructor
          · rintro ⟨⟨hk2, hkn⟩, hkprime, hkobs⟩
            exact ⟨hkprime, by omega, hkobs⟩
          · rintro ⟨hkprime, hkn, hkobs⟩
            exact ⟨⟨hkprime.two_le, by omega⟩, hkprime, hkobs⟩
        · intro k hk
          rfl
  rw [hleft] at hparts
  have hsum2 :
      (∑ k ∈ Finset.range 2,
        specialObstructionPrimeLogHarmonicIndicator p k) = 0 := by
    classical
    norm_num [Finset.sum_range_succ,
      specialObstructionPrimeLogHarmonicIndicator]
  rw [hsum2, mul_zero, sub_zero] at hparts
  simp only [Nat.add_sub_cancel] at hparts
  rw [sum_range_specialObstructionPrimeLogHarmonicIndicator] at hparts
  rw [hparts]
  rw [sub_eq_add_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sum_range_specialObstructionPrimeLogHarmonicIndicator]
  simp only [Erdos469.reciprocalLogDifference]
  ring

theorem exists_specialObstructionPrimeReciprocal_lower
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ n : ℕ, 3 ≤ n →
      (1 / 2 : ℝ) * Real.log (Real.log (n : ℝ)) - F ≤
        specialObstructionPrimeReciprocal p n := by
  obtain ⟨E, hE, hB⟩ :=
    exists_specialObstructionPrimeLogHarmonic_lower hp hp4
  obtain ⟨D, hD, hmain⟩ := exists_secondAbelMain_logLog_lower
  let w3 : ℝ := Erdos469.reciprocalLogWeight 3
  let F : ℝ := (1 / 2 : ℝ) * D + E * w3
  have hw3 : 0 ≤ w3 := by
    dsimp [w3, Erdos469.reciprocalLogWeight]
    positivity
  have hF : 0 ≤ F := by
    dsimp [F]
    positivity
  refine ⟨F, hF, ?_⟩
  intro n hn
  let main : ℝ :=
    Erdos469.reciprocalLogWeight n * Real.log (n : ℝ) +
      ∑ k ∈ Finset.Ico 3 n,
        Erdos469.reciprocalLogDifference k * Real.log (k : ℝ)
  have hmainLower : Real.log (Real.log (n : ℝ)) - D ≤ main := by
    dsimp [main]
    exact hmain n hn
  have hweightN : 0 ≤ Erdos469.reciprocalLogWeight n := by
    unfold Erdos469.reciprocalLogWeight
    positivity
  have hendpoint :
      Erdos469.reciprocalLogWeight n *
          ((1 / 2 : ℝ) * Real.log (n : ℝ) - E) ≤
        Erdos469.reciprocalLogWeight n *
          specialObstructionPrimeLogHarmonic p n :=
    mul_le_mul_of_nonneg_left (hB n hn) hweightN
  have hsum :
      (∑ k ∈ Finset.Ico 3 n,
        Erdos469.reciprocalLogDifference k *
          ((1 / 2 : ℝ) * Real.log (k : ℝ) - E)) ≤
        ∑ k ∈ Finset.Ico 2 n,
          Erdos469.reciprocalLogDifference k *
            specialObstructionPrimeLogHarmonic p k := by
    calc
      (∑ k ∈ Finset.Ico 3 n,
        Erdos469.reciprocalLogDifference k *
          ((1 / 2 : ℝ) * Real.log (k : ℝ) - E)) ≤
          ∑ k ∈ Finset.Ico 3 n,
            Erdos469.reciprocalLogDifference k *
              specialObstructionPrimeLogHarmonic p k := by
        apply Finset.sum_le_sum
        intro k hk
        have hk3 : 3 ≤ k := (Finset.mem_Ico.mp hk).1
        exact mul_le_mul_of_nonneg_left (hB k hk3)
          (Erdos469.reciprocalLogDifference_nonneg
            ((show 2 ≤ 3 by norm_num).trans hk3))
      _ ≤ ∑ k ∈ Finset.Ico 2 n,
            Erdos469.reciprocalLogDifference k *
              specialObstructionPrimeLogHarmonic p k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          have hkI := Finset.mem_Ico.mp hk
          exact Finset.mem_Ico.mpr
            ⟨(show 2 ≤ 3 by norm_num).trans hkI.1, hkI.2⟩
        · intro k hk hkn
          exact mul_nonneg
            (Erdos469.reciprocalLogDifference_nonneg
              (Finset.mem_Ico.mp hk).1)
            (by
              unfold specialObstructionPrimeLogHarmonic
              apply Finset.sum_nonneg
              intro l hl
              have hlprime :=
                (mem_specialObstructionPrimesFinite.mp hl).1
              exact div_nonneg
                (Real.log_nonneg (by exact_mod_cast hlprime.one_le))
                (by positivity))
  have herrorEq :
      Erdos469.reciprocalLogWeight n * E +
          ∑ k ∈ Finset.Ico 3 n,
            Erdos469.reciprocalLogDifference k * E = E * w3 := by
    have hsum3 := sum_reciprocalLogDifference1081
      (m := 3) (n := n) hn
    have hsumE :
        (∑ k ∈ Finset.Ico 3 n,
          Erdos469.reciprocalLogDifference k * E) =
            (∑ k ∈ Finset.Ico 3 n,
              Erdos469.reciprocalLogDifference k) * E := by
      rw [Finset.sum_mul]
    rw [hsumE, hsum3]
    dsimp [w3]
    ring
  have haber : (1 / 2 : ℝ) * main - E * w3 ≤
      specialObstructionPrimeReciprocal p n := by
    rw [specialObstructionPrimeReciprocal_eq_abel p
      ((show 2 ≤ 3 by norm_num).trans hn)]
    have hcombined := add_le_add hendpoint hsum
    have hexpand :
        Erdos469.reciprocalLogWeight n *
            ((1 / 2 : ℝ) * Real.log (n : ℝ) - E) +
          ∑ k ∈ Finset.Ico 3 n,
            Erdos469.reciprocalLogDifference k *
              ((1 / 2 : ℝ) * Real.log (k : ℝ) - E) =
          (1 / 2 : ℝ) * main - E * w3 := by
      have hsumExpand :
          (∑ k ∈ Finset.Ico 3 n,
            Erdos469.reciprocalLogDifference k *
              ((1 / 2 : ℝ) * Real.log (k : ℝ) - E)) =
            (1 / 2 : ℝ) *
                (∑ k ∈ Finset.Ico 3 n,
                  Erdos469.reciprocalLogDifference k *
                    Real.log (k : ℝ)) -
              ∑ k ∈ Finset.Ico 3 n,
                Erdos469.reciprocalLogDifference k * E := by
        calc
          (∑ k ∈ Finset.Ico 3 n,
            Erdos469.reciprocalLogDifference k *
              ((1 / 2 : ℝ) * Real.log (k : ℝ) - E)) =
              ∑ k ∈ Finset.Ico 3 n,
                ((1 / 2 : ℝ) *
                    (Erdos469.reciprocalLogDifference k *
                      Real.log (k : ℝ)) -
                  Erdos469.reciprocalLogDifference k * E) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ = (∑ k ∈ Finset.Ico 3 n,
                (1 / 2 : ℝ) *
                  (Erdos469.reciprocalLogDifference k *
                    Real.log (k : ℝ))) -
                ∑ k ∈ Finset.Ico 3 n,
                  Erdos469.reciprocalLogDifference k * E := by
            rw [Finset.sum_sub_distrib]
          _ = (1 / 2 : ℝ) *
                (∑ k ∈ Finset.Ico 3 n,
                  Erdos469.reciprocalLogDifference k *
                    Real.log (k : ℝ)) -
                ∑ k ∈ Finset.Ico 3 n,
                  Erdos469.reciprocalLogDifference k * E := by
            rw [Finset.mul_sum]
      dsimp [main]
      rw [hsumExpand]
      rw [← herrorEq]
      ring
    rw [← hexpand]
    exact hcombined
  dsimp [F]
  linarith

theorem obstructionReciprocalMass_specialObstructionPrimesFinite
    (p N : ℕ) :
    obstructionReciprocalMass (N + 1).primesBelow
        (specialObstructionPrimesFinite p N) =
      specialObstructionPrimeReciprocal p N := by
  classical
  unfold obstructionReciprocalMass
    specialObstructionPrimeReciprocal
  apply Finset.sum_congr
  · ext l
    simp only [Finset.mem_filter, Nat.mem_primesBelow,
      mem_specialObstructionPrimesFinite]
    constructor
    · rintro ⟨⟨hlprime, hlN⟩, hlprime', hlN', hlobs⟩
      exact ⟨hlprime', hlN', hlobs⟩
    · rintro ⟨hlprime, hlN, hlobs⟩
      exact ⟨⟨by omega, hlprime⟩, hlprime, hlN, hlobs⟩
  · intro l hl
    rfl

theorem eventually_specialObstructionReciprocalMass_half_lower
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ᶠ N : ℕ in atTop,
      (1 / 2 : ℝ) * Real.log (Real.log (N : ℝ)) - F ≤
        obstructionReciprocalMass (N + 1).primesBelow
          (specialObstructionPrimesFinite p N) := by
  obtain ⟨F, hF, hmass⟩ :=
    exists_specialObstructionPrimeReciprocal_lower hp hp4
  refine ⟨F, hF, ?_⟩
  filter_upwards [eventually_ge_atTop 3] with N hN
  rw [obstructionReciprocalMass_specialObstructionPrimesFinite]
  exact hmass N hN

section SubsetProductStabilizer

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- Left multiplication of a finite subset of a commutative group. -/
def leftMulFinset (a : G) (S : Finset G) : Finset G :=
  S.image fun x => a * x

@[simp] theorem leftMulFinset_one (S : Finset G) :
    leftMulFinset (1 : G) S = S := by
  ext x
  simp [leftMulFinset]

theorem leftMulFinset_mul (a b : G) (S : Finset G) :
    leftMulFinset (a * b) S = leftMulFinset a (leftMulFinset b S) := by
  ext x
  constructor
  · intro hx
    rw [leftMulFinset, Finset.mem_image] at hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [leftMulFinset, Finset.mem_image]
    refine ⟨b * y, ?_, by simp [mul_assoc]⟩
    rw [leftMulFinset, Finset.mem_image]
    exact ⟨y, hy, rfl⟩
  · intro hx
    rw [leftMulFinset, Finset.mem_image] at hx
    rcases hx with ⟨z, hz, rfl⟩
    rw [leftMulFinset, Finset.mem_image] at hz
    rcases hz with ⟨y, hy, rfl⟩
    rw [leftMulFinset, Finset.mem_image]
    exact ⟨y, hy, by simp [mul_assoc]⟩

theorem leftMulFinset_union (a : G) (S T : Finset G) :
    leftMulFinset a (S ∪ T) = leftMulFinset a S ∪ leftMulFinset a T := by
  ext x
  simp only [leftMulFinset, Finset.mem_image, Finset.mem_union]
  constructor
  · rintro ⟨y, hyS | hyT, rfl⟩
    · exact Or.inl ⟨y, hyS, rfl⟩
    · exact Or.inr ⟨y, hyT, rfl⟩
  · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨y, Or.inl hy, rfl⟩
    · exact ⟨y, Or.inr hy, rfl⟩

theorem card_leftMulFinset (a : G) (S : Finset G) :
    (leftMulFinset a S).card = S.card := by
  unfold leftMulFinset
  rw [Finset.card_image_of_injective]
  intro x y hxy
  exact mul_left_cancel hxy

theorem leftMulFinset_injective (a : G) :
    Function.Injective (leftMulFinset a : Finset G → Finset G) := by
  intro S T h
  have h' := congrArg (leftMulFinset a⁻¹) h
  simpa [← leftMulFinset_mul] using h'

/-- The subgroup of multipliers preserving a finite subset. -/
def finsetMulStabilizer (S : Finset G) : Subgroup G where
  carrier := {a | leftMulFinset a S = S}
  one_mem' := leftMulFinset_one S
  mul_mem' := by
    intro a b ha hb
    change leftMulFinset a S = S at ha
    change leftMulFinset b S = S at hb
    change leftMulFinset (a * b) S = S
    rw [leftMulFinset_mul, hb, ha]
  inv_mem' := by
    intro a ha
    change leftMulFinset a S = S at ha
    change leftMulFinset a⁻¹ S = S
    apply leftMulFinset_injective a
    rw [← leftMulFinset_mul]
    simpa [ha]

@[simp] theorem mem_finsetMulStabilizer_iff {S : Finset G} {a : G} :
    a ∈ finsetMulStabilizer S ↔ leftMulFinset a S = S := Iff.rfl

/-- Products of arbitrary sublists, built one coordinate at a time. -/
def subsetProductsList : List G → Finset G
  | [] => {1}
  | a :: l => subsetProductsList l ∪ leftMulFinset a (subsetProductsList l)

@[simp] theorem subsetProductsList_nil :
    subsetProductsList ([] : List G) = {1} := rfl

@[simp] theorem subsetProductsList_cons (a : G) (l : List G) :
    subsetProductsList (a :: l) =
      subsetProductsList l ∪ leftMulFinset a (subsetProductsList l) := rfl

theorem subsetProductsList_nonempty (l : List G) :
    (subsetProductsList l).Nonempty := by
  induction l with
  | nil => simp
  | cons a l ih => exact ih.mono Finset.subset_union_left

/-- The recursive reachable set is exactly the set of products obtained by
choosing any subset of the indexed coordinates. -/
theorem mem_subsetProductsList_ofFn_iff {k : ℕ}
    (x : Fin k → G) (z : G) :
    z ∈ subsetProductsList (List.ofFn x) ↔
      ∃ sigma : Fin k → Bool,
        z = ∏ i, if sigma i then x i else 1 := by
  induction k generalizing z with
  | zero =>
      simp [subsetProductsList]
  | succ k ih =>
      rw [List.ofFn_succ, subsetProductsList_cons, Finset.mem_union]
      constructor
      · intro hz
        rcases hz with hz | hz
        · obtain ⟨sigma, hsigma⟩ :=
            (ih (fun i => x i.succ) z).mp hz
          refine ⟨Fin.cons false sigma, ?_⟩
          rw [Fin.prod_univ_succ]
          simpa using hsigma
        · rw [leftMulFinset, Finset.mem_image] at hz
          rcases hz with ⟨w, hw, hwz⟩
          obtain ⟨sigma, hsigma⟩ :=
            (ih (fun i => x i.succ) w).mp hw
          refine ⟨Fin.cons true sigma, ?_⟩
          rw [Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, if_true]
          rw [← hsigma]
          exact hwz.symm
      · rintro ⟨sigma, rfl⟩
        rw [Fin.prod_univ_succ]
        have htail :
            (∏ i : Fin k, if sigma i.succ then x i.succ else 1) ∈
              subsetProductsList (List.ofFn fun i => x i.succ) := by
          apply (ih (fun i => x i.succ)
            (∏ i : Fin k, if sigma i.succ then x i.succ else 1)).mpr
          exact ⟨fun i => sigma i.succ, rfl⟩
        cases h0 : sigma 0
        · left
          simpa [h0] using htail
        · right
          rw [leftMulFinset, Finset.mem_image]
          refine ⟨∏ i : Fin k, if sigma i.succ then x i.succ else 1, ?_, ?_⟩
          · exact htail
          · simp [h0]

/-- A multiplier stabilizing the old subset-product set continues to
stabilize it after one more coordinate is adjoined. -/
theorem stabilizer_subsetProductsList_mono (a : G) (l : List G) :
    finsetMulStabilizer (subsetProductsList l) ≤
      finsetMulStabilizer (subsetProductsList (a :: l)) := by
  intro g hg
  rw [mem_finsetMulStabilizer_iff] at hg ⊢
  rw [subsetProductsList_cons, leftMulFinset_union, hg]
  rw [← leftMulFinset_mul, mul_comm g a, leftMulFinset_mul, hg]

/-- If adding a coordinate does not enlarge the subset-product set, that
coordinate stabilizes the enlarged set. -/
theorem mem_stabilizer_of_card_subsetProductsList_cons_eq
    (a : G) (l : List G)
    (hcard : (subsetProductsList (a :: l)).card =
      (subsetProductsList l).card) :
    a ∈ finsetMulStabilizer (subsetProductsList (a :: l)) := by
  let S := subsetProductsList l
  let T := subsetProductsList (a :: l)
  have hST : S ⊆ T := by
    dsimp [S, T]
    exact Finset.subset_union_left
  have hTS : T = S := by
    symm
    apply Finset.eq_of_subset_of_card_le hST
    simpa [S, T] using hcard.le
  rw [mem_finsetMulStabilizer_iff]
  change leftMulFinset a T = T
  rw [hTS]
  have haS : leftMulFinset a S ⊆ S := by
    intro z hz
    rw [← hTS]
    dsimp [T, S]
    exact Finset.mem_union_right _ hz
  exact Finset.eq_of_subset_of_card_le haS (by
    rw [card_leftMulFinset])

/-- Number of list coordinates outside a subgroup, with repetitions
counted. -/
noncomputable def countOutsideSubgroup (H : Subgroup G) (l : List G) : ℕ := by
  classical
  exact (l.filter fun a => decide (a ∉ H)).length

@[simp] theorem countOutsideSubgroup_nil (H : Subgroup G) :
    countOutsideSubgroup H ([] : List G) = 0 := by
  simp [countOutsideSubgroup]

theorem countOutsideSubgroup_cons_of_mem (H : Subgroup G)
    (a : G) (l : List G) (ha : a ∈ H) :
    countOutsideSubgroup H (a :: l) = countOutsideSubgroup H l := by
  classical
  simp [countOutsideSubgroup, ha]

theorem countOutsideSubgroup_cons_of_not_mem (H : Subgroup G)
    (a : G) (l : List G) (ha : a ∉ H) :
    countOutsideSubgroup H (a :: l) = countOutsideSubgroup H l + 1 := by
  classical
  simp [countOutsideSubgroup, ha]

/-- Relative to any subgroup containing the stabilizer of the final
subset-product set, fewer than `|R|` coordinates lie outside that subgroup,
where `R` is the final reachable set. -/
theorem length_filter_not_mem_subgroup_lt_card_subsetProductsList
    (l : List G) (H : Subgroup G)
    (hstab : finsetMulStabilizer (subsetProductsList l) ≤ H) :
    countOutsideSubgroup H l < (subsetProductsList l).card := by
  classical
  induction l generalizing H with
  | nil => simp [subsetProductsList]
  | cons a l ih =>
      have hmono := stabilizer_subsetProductsList_mono a l
      have htail : finsetMulStabilizer (subsetProductsList l) ≤ H :=
        hmono.trans hstab
      have ih' := ih H htail
      have hcardle : (subsetProductsList l).card ≤
          (subsetProductsList (a :: l)).card :=
        Finset.card_le_card Finset.subset_union_left
      by_cases ha : a ∈ H
      · rw [countOutsideSubgroup_cons_of_mem H a l ha]
        exact ih'.trans_le hcardle
      · rw [countOutsideSubgroup_cons_of_not_mem H a l ha]
        have hcardlt : (subsetProductsList l).card <
            (subsetProductsList (a :: l)).card := by
          apply lt_of_le_of_ne hcardle
          intro heq
          have hastab := mem_stabilizer_of_card_subsetProductsList_cons_eq
            a l heq.symm
          exact ha (hstab hastab)
        omega

/-- If the reachable subset products do not fill the group, then all but at
most `|G|-1` coordinates lie in one proper stabilizer subgroup. -/
theorem exists_proper_stabilizer_with_few_outside
    (l : List G) (hproper : subsetProductsList l ≠ Finset.univ) :
    ∃ H : Subgroup G, H ≠ ⊤ ∧
      countOutsideSubgroup H l < Fintype.card G := by
  let H := finsetMulStabilizer (subsetProductsList l)
  have hHproper : H ≠ ⊤ := by
    intro htop
    have htrans : ∀ g : G, leftMulFinset g (subsetProductsList l) =
        subsetProductsList l := by
      intro g
      have hg : g ∈ H := by rw [htop]; exact Subgroup.mem_top g
      exact hg
    obtain ⟨z, hz⟩ := subsetProductsList_nonempty l
    have hall : ∀ g : G, g ∈ subsetProductsList l := by
      intro g
      have hgz : g ∈ leftMulFinset (g * z⁻¹)
          (subsetProductsList l) := by
        rw [leftMulFinset, Finset.mem_image]
        refine ⟨z, hz, ?_⟩
        group
      rw [htrans] at hgz
      exact hgz
    apply hproper
    ext g
    simp [hall]
  refine ⟨H, hHproper, ?_⟩
  have hbound := length_filter_not_mem_subgroup_lt_card_subsetProductsList
    l H (le_refl H)
  exact hbound.trans_le (Finset.card_le_univ _)

end SubsetProductStabilizer

section SignedProductConcentration

variable {G : Type*} [CommGroup G]

/-- Product of the coordinate squares selected by a sign pattern. -/
def selectedSquareProduct {k : ℕ}
    (sigma : Fin k → Bool) (x : Fin k → G) : G :=
  ∏ i, if sigma i then x i ^ 2 else 1

theorem signedProduct_mul_selectedSquareProduct {k : ℕ}
    (sigma : Fin k → Bool) (x : Fin k → G) :
    signedProduct sigma x * selectedSquareProduct sigma x = ∏ i, x i := by
  classical
  rw [signedProduct, selectedSquareProduct, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  cases h : sigma i <;> simp [h, pow_two]

theorem signedProduct_eq_iff_selectedSquareProduct_eq {k : ℕ}
    (sigma : Fin k → Bool) (x : Fin k → G) (c : G) :
    signedProduct sigma x = c ↔
      selectedSquareProduct sigma x = (∏ i, x i) / c := by
  have hmul := signedProduct_mul_selectedSquareProduct sigma x
  constructor
  · intro hsigned
    rw [hsigned] at hmul
    calc
      selectedSquareProduct sigma x =
          c⁻¹ * (c * selectedSquareProduct sigma x) := by group
      _ = c⁻¹ * (∏ i, x i) := by rw [hmul]
      _ = (∏ i, x i) / c := by
        rw [div_eq_mul_inv]
        ac_rfl
  · intro hselected
    rw [hselected] at hmul
    calc
      signedProduct sigma x =
          (signedProduct sigma x * ((∏ i, x i) / c)) *
            ((∏ i, x i) / c)⁻¹ := by group
      _ = (∏ i, x i) * ((∏ i, x i) / c)⁻¹ := by rw [hmul]
      _ = c := by
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
        calc
          (∏ i, x i) * (c * (∏ i, x i)⁻¹) =
              c * ((∏ i, x i) * (∏ i, x i)⁻¹) := by ac_rfl
          _ = c := by simp

/-- A coordinate square, regarded as an element of the square subgroup. -/
def classSquareElement (x : G) :
    (classSquareSubgroup : Subgroup G) :=
  ⟨x ^ 2, classSquare_mem x⟩

@[simp] theorem classSquareElement_val (x : G) :
    (classSquareElement x : G) = x ^ 2 := rfl

/-- Failure of all sign choices, subject to the necessary square-class
condition, forces all but fewer than `|G²|` coordinate squares into one
proper subgroup of `G²`. -/
theorem exists_proper_squareSubgroup_with_few_coordinates_of_no_signedProduct
    [Fintype G] [DecidableEq G] {k : ℕ}
    (x : Fin k → G) (c : G)
    (hclass :
      (QuotientGroup.mk' (classSquareSubgroup : Subgroup G)) (∏ i, x i) =
        (QuotientGroup.mk' (classSquareSubgroup : Subgroup G)) c)
    (hmiss : ∀ sigma : Fin k → Bool, signedProduct sigma x ≠ c) :
    ∃ H : Subgroup (classSquareSubgroup : Subgroup G), H ≠ ⊤ ∧
      countOutsideSubgroup H
          (List.ofFn fun i => classSquareElement (x i)) <
        Nat.card (classSquareSubgroup : Subgroup G) := by
  classical
  letI : Fintype (classSquareSubgroup : Subgroup G) := Fintype.ofFinite _
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_iff_div_mem] at hclass
  let target : (classSquareSubgroup : Subgroup G) :=
    ⟨(∏ i, x i) / c, hclass⟩
  have htarget : target ∉ subsetProductsList
      (List.ofFn fun i => classSquareElement (x i)) := by
    intro hmem
    obtain ⟨sigma, hsigma⟩ :=
      (mem_subsetProductsList_ofFn_iff
        (fun i => classSquareElement (x i)) target).mp hmem
    have hsigmaVal := congrArg Subtype.val hsigma
    have hselected : selectedSquareProduct sigma x = (∏ i, x i) / c := by
      rw [selectedSquareProduct]
      calc
        (∏ i, if sigma i then x i ^ 2 else 1) =
            ∏ i, ((if sigma i then classSquareElement (x i) else 1 :
              (classSquareSubgroup : Subgroup G)) : G) := by
          apply Finset.prod_congr rfl
          intro i hi
          cases h : sigma i <;> simp [h]
        _ = (∏ i, x i) / c := by
          simpa [target] using hsigmaVal.symm
    exact hmiss sigma
      ((signedProduct_eq_iff_selectedSquareProduct_eq sigma x c).mpr hselected)
  have hproper : subsetProductsList
      (List.ofFn fun i => classSquareElement (x i)) ≠ Finset.univ := by
    intro hall
    exact htarget (by rw [hall]; exact Finset.mem_univ target)
  simpa only [Nat.card_eq_fintype_card] using
    (exists_proper_stabilizer_with_few_outside _ hproper)

end SignedProductConcentration

end

end Erdos1081
