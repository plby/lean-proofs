import ErdosProblems.Erdos1161.LocalEstimate

open scoped BigOperators Finset

namespace Erdos1161

def logTwoCycleTypes (r : ℕ) : Finset (Multiset ℕ) :=
  (cycleTypes r).filter fun mu ↦ 2 ^ Nat.log 2 r ∈ mu

@[simp] theorem mem_logTwoCycleTypes {r : ℕ} {mu : Multiset ℕ} :
    mu ∈ logTwoCycleTypes r ↔
      mu ∈ cycleTypes r ∧ 2 ^ Nat.log 2 r ∈ mu := by
  simp [logTwoCycleTypes]

theorem logTwoCycleTypes_eq_map_cons {r : ℕ} (hr : 2 ≤ r) :
    logTwoCycleTypes r =
      (cycleTypes (r - 2 ^ Nat.log 2 r)).map
        (consMultisetEmbedding (2 ^ Nat.log 2 r)) := by
  classical
  let q := 2 ^ Nat.log 2 r
  have hqpos : 0 < q := by simp [q]
  have hqle : q ≤ r := Nat.pow_log_le_self 2 (by omega)
  have hrlt : r < 2 * q := by
    simpa [q, pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) r
  have hrsub : r - q < q := by omega
  ext nu
  constructor
  · intro hnu
    rw [mem_logTwoCycleTypes] at hnu
    let mu := nu.erase q
    have hcons : q ::ₘ mu = nu := Multiset.cons_erase hnu.2
    have hmu : mu ∈ cycleTypes (r - q) := by
      rw [mem_cycleTypes]
      constructor
      · have hsum := (mem_cycleTypes.mp hnu.1).1
        rw [← hcons, Multiset.sum_cons] at hsum
        omega
      · intro a ha
        exact (mem_cycleTypes.mp hnu.1).2 a (Multiset.mem_of_mem_erase ha)
    rw [Finset.mem_map]
    refine ⟨mu, by simpa [q] using hmu, ?_⟩
    change q ::ₘ mu = nu
    exact hcons
  · rw [Finset.mem_map]
    rintro ⟨mu, hmu, rfl⟩
    rw [mem_logTwoCycleTypes]
    have hmuData := mem_cycleTypes.mp hmu
    constructor
    · rw [mem_cycleTypes]
      constructor
      · change (q ::ₘ mu).sum ≤ r
        simp only [Multiset.sum_cons]
        omega
      · intro a ha
        rcases Multiset.mem_cons.mp ha with rfl | ha
        · exact (by have : 2 ≤ q := by
                      dsimp [q]
                      have hlog : 1 ≤ Nat.log 2 r :=
                        Nat.le_log_of_pow_le (by omega) (by simpa using hr)
                      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hlog
                    exact this)
        · exact hmuData.2 a ha
    · exact Multiset.mem_cons_self _ _

theorem sum_logTwoCycleTypes_cycleWeight {r : ℕ} (hr : 2 ≤ r) :
    ∑ mu ∈ logTwoCycleTypes r, cycleWeight r mu =
      1 / ((2 ^ Nat.log 2 r : ℕ) : ℚ) := by
  classical
  let q := 2 ^ Nat.log 2 r
  have hqle : q ≤ r := Nat.pow_log_le_self 2 (by omega)
  have hrsub : r - q < q := by
    have hrlt : r < 2 * q := by
      simpa [q, pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) r
    omega
  rw [logTwoCycleTypes_eq_map_cons hr, Finset.sum_map]
  change (cycleTypes (r - q)).sum
      (fun mu ↦ cycleWeight r (q ::ₘ mu)) = 1 / (q : ℚ)
  have hrdecomp : q + (r - q) = r := Nat.add_sub_of_le hqle
  calc
    _ = ∑ mu ∈ cycleTypes (r - q), (1 / (q : ℚ)) * cycleWeight (r - q) mu := by
      apply Finset.sum_congr rfl
      intro mu hmu
      have h := cycleWeight_cons_long hmu hrsub
      rw [hrdecomp] at h
      exact h
    _ = 1 / (q : ℚ) := by
      rw [← Finset.mul_sum, sum_cycleWeight]
      simp

theorem sum_logTwoCycleTypes_cycleWeightReal {r : ℕ} (hr : 2 ≤ r) :
    ∑ mu ∈ logTwoCycleTypes r, cycleWeightReal r mu =
      1 / ((2 ^ Nat.log 2 r : ℕ) : ℝ) := by
  have h := congrArg (fun x : ℚ ↦ (x : ℝ))
    (sum_logTwoCycleTypes_cycleWeight hr)
  simpa [cycleWeight, cycleWeightReal] using h

theorem pow_log_two_dvd_of_dvd_not_dvd_half {r m j : ℕ}
    (hr : 2 ≤ r) (hjm : j ∣ m)
    (hpowm : 2 ^ Nat.log 2 r ∣ m)
    (hnext : ¬ 2 ^ (Nat.log 2 r + 1) ∣ m)
    (hjhalf : ¬ j ∣ m / 2) :
    2 ^ Nat.log 2 r ∣ j := by
  let a := Nat.log 2 r
  have hm0 : m ≠ 0 := by
    intro hm
    subst m
    simp at hjhalf
  have hj0 : j ≠ 0 := by
    intro hj
    subst j
    simp [hm0] at hjm
  have hfa_le : a ≤ m.factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hm0).mp hpowm
  have hfa_succ_not : ¬ a + 1 ≤ m.factorization 2 := by
    intro h
    exact hnext ((Nat.prime_two.pow_dvd_iff_le_factorization hm0).mpr h)
  have hfam : m.factorization 2 = a := by omega
  have h2m : 2 ∣ m := by
    have hq2 : 2 ∣ 2 ^ a := by
      have ha : 1 ≤ a := Nat.le_log_of_pow_le (by omega) (by simpa using hr)
      exact dvd_pow_self 2 (by omega)
    exact hq2.trans hpowm
  have hmhalf0 : m / 2 ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h2m) (by omega)).ne'
  apply (Nat.prime_two.pow_dvd_iff_le_factorization hj0).mpr
  by_contra hnot
  have hfjlt : j.factorization 2 < a := by omega
  apply hjhalf
  rw [← Nat.factorization_prime_le_iff_dvd hj0 hmhalf0]
  intro p hp
  have hfacjm : j.factorization p ≤ m.factorization p := by
    exact (Nat.factorization_prime_le_iff_dvd hj0 hm0).mpr hjm p hp
  have hfacdiv := congrArg (fun f : ℕ →₀ ℕ ↦ f p) (Nat.factorization_div h2m)
  by_cases hp2 : p = 2
  · subst p
    rw [hfacdiv]
    change j.factorization 2 ≤ m.factorization 2 - (2 : ℕ).factorization 2
    rw [Nat.prime_two.factorization_self, hfam]
    omega
  · have hfac2p : (2 : ℕ).factorization p = 0 := by
      rw [Nat.prime_two.factorization]
      simp [hp2]
    rw [hfacdiv]
    change j.factorization p ≤ m.factorization p - (2 : ℕ).factorization p
    rw [hfac2p]
    simpa using hfacjm

theorem lcm_half_eq_iff_not_dvd {m x : ℕ} (hm : 0 < m)
    (heven : 2 ∣ m) (hxm : x ∣ m) :
    Nat.lcm (m / 2) x = m ↔ ¬ x ∣ m / 2 := by
  have hhpos : 0 < m / 2 :=
    Nat.div_pos (Nat.le_of_dvd hm heven) (by omega)
  have htwice : (m / 2) * 2 = m := Nat.div_mul_cancel heven
  constructor
  · intro hlcm hxh
    have : Nat.lcm (m / 2) x = m / 2 :=
      (Nat.lcm_eq_left_iff_dvd).mpr hxh
    omega
  · intro hxnot
    let L := Nat.lcm (m / 2) x
    have hhL : m / 2 ∣ L := Nat.dvd_lcm_left _ _
    have hLm : L ∣ m := Nat.lcm_dvd
      (by exact ⟨2, htwice.symm⟩) hxm
    obtain ⟨c, hc⟩ := hhL
    have hc2 : c ∣ 2 := by
      apply (Nat.mul_dvd_mul_iff_left hhpos).mp
      show (m / 2) * c ∣ (m / 2) * 2
      rw [← hc, htwice]
      exact hLm
    rcases (Nat.dvd_prime Nat.prime_two).mp hc2 with rfl | rfl
    · exfalso
      apply hxnot
      apply (Nat.lcm_eq_left_iff_dvd).mp
      simpa [L] using hc
    · simpa [L, htwice] using hc

theorem exceptionalCycleType_lcm_dvd_lcmUpto {r : ℕ} {mu : Multiset ℕ}
    (hmu : mu ∈ cycleTypes r) : mu.lcm ∣ Nat.lcmUpto r := by
  rw [Multiset.lcm_dvd]
  intro j hj
  have hjle : j ≤ r := by
    have hjsum : j ≤ mu.sum := by
      have hs := congrArg Multiset.sum (Multiset.cons_erase hj)
      calc
        j ≤ j + (mu.erase j).sum := by omega
        _ = mu.sum := by simpa only [Multiset.sum_cons] using hs
    exact hjsum.trans (mem_cycleTypes.mp hmu).1
  exact Nat.dvd_lcmUpto (by have := (mem_cycleTypes.mp hmu).2 j hj; omega) hjle

theorem lcmUpto_dvd_half_of_next_two_pow_dvd {r m : ℕ}
    (hm : 0 < m) (hadm : Nat.lcmUpto r ∣ m)
    (hnext : 2 ^ (Nat.log 2 r + 1) ∣ m) :
    Nat.lcmUpto r ∣ m / 2 := by
  have h2m : 2 ∣ m := by
    have : 2 ∣ 2 ^ (Nat.log 2 r + 1) := dvd_pow_self 2 (by omega)
    exact this.trans hnext
  have hmhalf : m / 2 ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd hm h2m) (by omega)).ne'
  rw [← Nat.factorization_prime_le_iff_dvd (Nat.lcmUpto_ne_zero r) hmhalf]
  intro p hp
  have hfacLm : (Nat.lcmUpto r).factorization p ≤ m.factorization p :=
    (Nat.factorization_prime_le_iff_dvd (Nat.lcmUpto_ne_zero r) hm.ne').mpr hadm p hp
  have hfacdiv := congrArg (fun f : ℕ →₀ ℕ ↦ f p) (Nat.factorization_div h2m)
  by_cases hp2 : p = 2
  · subst p
    have hnextfac : Nat.log 2 r + 1 ≤ m.factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hm.ne').mp hnext
    rw [Nat.factorization_lcmUpto r Nat.prime_two]
    rw [hfacdiv]
    change Nat.log 2 r ≤ m.factorization 2 - (2 : ℕ).factorization 2
    rw [Nat.prime_two.factorization_self]
    omega
  · have hfac2p : (2 : ℕ).factorization p = 0 := by
      rw [Nat.prime_two.factorization]
      simp [hp2]
    rw [hfacdiv]
    change (Nat.lcmUpto r).factorization p ≤
      m.factorization p - (2 : ℕ).factorization p
    rw [hfac2p]
    simpa using hfacLm

theorem cycleType_lcm_not_dvd_half_iff_logTwo_mem {r m : ℕ}
    (hr : 2 ≤ r) (hm : 0 < m) (hadm : Nat.lcmUpto r ∣ m)
    (hnext : ¬ 2 ^ (Nat.log 2 r + 1) ∣ m)
    {mu : Multiset ℕ} (hmu : mu ∈ cycleTypes r) :
    ¬ mu.lcm ∣ m / 2 ↔ 2 ^ Nat.log 2 r ∈ mu := by
  let q := 2 ^ Nat.log 2 r
  have hqpos : 0 < q := by positivity
  have hqle : q ≤ r := Nat.pow_log_le_self 2 (by omega)
  have hrlt : r < 2 * q := by
    simpa [q, pow_succ, Nat.mul_comm] using
      Nat.lt_pow_succ_log_self (by omega : 1 < 2) r
  have hqL : q ∣ Nat.lcmUpto r := Nat.dvd_lcmUpto hqpos hqle
  have hqm : q ∣ m := hqL.trans hadm
  have h2q : 2 ∣ q := by
    have ha : 1 ≤ Nat.log 2 r :=
      Nat.le_log_of_pow_le (by omega) (by simpa using hr)
    exact dvd_pow_self 2 (by omega)
  have h2m : 2 ∣ m := h2q.trans hqm
  constructor
  · intro hlcm
    by_contra hqnot
    apply hlcm
    rw [Multiset.lcm_dvd]
    intro j hj
    by_contra hjhalf
    have hjle : j ≤ r := by
      have hjsum : j ≤ mu.sum := by
        have hs := congrArg Multiset.sum (Multiset.cons_erase hj)
        calc
          j ≤ j + (mu.erase j).sum := by omega
          _ = mu.sum := by simpa only [Multiset.sum_cons] using hs
      exact hjsum.trans (mem_cycleTypes.mp hmu).1
    have hjm : j ∣ m := by
      exact (Nat.dvd_lcmUpto
        (by have := (mem_cycleTypes.mp hmu).2 j hj; omega) hjle).trans hadm
    have hqj : q ∣ j :=
      pow_log_two_dvd_of_dvd_not_dvd_half hr hjm hqm hnext hjhalf
    obtain ⟨c, hc⟩ := hqj
    have hcpos : 0 < c := by
      by_contra hc0
      have hczero : c = 0 := by omega
      have : j = 0 := by
        calc
          j = q * c := hc
          _ = 0 := by simp [hczero]
      have := (mem_cycleTypes.mp hmu).2 j hj
      omega
    have hc_lt : c < 2 := by
      have hjlt : j < 2 * q := hjle.trans_lt hrlt
      rw [hc] at hjlt
      nlinarith
    have hc_one : c = 1 := by omega
    apply hqnot
    have hjeq : j = q := by
      calc
        j = q * c := hc
        _ = q := by simp [hc_one]
    simpa [q, hjeq] using hj
  · intro hqmem hlcm
    have hq_lcm : q ∣ mu.lcm := Multiset.dvd_lcm hqmem
    have hq_half : q ∣ m / 2 := hq_lcm.trans hlcm
    apply hnext
    have htwoq : 2 * q ∣ m := (Nat.dvd_div_iff_mul_dvd h2m).mp hq_half
    simpa [q, pow_succ, Nat.mul_comm] using htwoq

/-- Residual types whose adjoining two `(m/2)`-cycles has order `m`. -/
def exceptionalHalfResidualTypes (r m : ℕ) : Finset (Multiset ℕ) :=
  (cycleTypes r).filter fun mu ↦ Nat.lcm (m / 2) mu.lcm = m

@[simp] theorem mem_exceptionalHalfResidualTypes {r m : ℕ} {mu : Multiset ℕ} :
    mu ∈ exceptionalHalfResidualTypes r m ↔
      mu ∈ cycleTypes r ∧ Nat.lcm (m / 2) mu.lcm = m := by
  simp [exceptionalHalfResidualTypes]

theorem exceptionalHalfResidualTypes_eq {r m : ℕ} (hrhalf : r < m / 2)
    (hadm : Nat.lcmUpto r ∣ m) :
    exceptionalHalfResidualTypes r m =
      if r ≤ 1 ∨ 2 ^ (Nat.log 2 r + 1) ∣ m then ∅
      else logTwoCycleTypes r := by
  classical
  have hmhalf : 0 < m / 2 := hrhalf.trans_le' (Nat.zero_le r)
  have hm : 0 < m := (Nat.div_le_self m 2).trans_lt' hmhalf
  by_cases hrsmall : r ≤ 1
  · rw [if_pos (Or.inl hrsmall)]
    ext mu
    constructor
    · intro hmu
      exfalso
      rw [mem_exceptionalHalfResidualTypes] at hmu
      have hmuzero : mu = 0 := by
        apply Multiset.eq_zero_of_forall_notMem
        intro j hj
        have hjtwo := (mem_cycleTypes.mp hmu.1).2 j hj
        have hjle : j ≤ mu.sum := by
          have hs := congrArg Multiset.sum (Multiset.cons_erase hj)
          calc
            j ≤ j + (mu.erase j).sum := by omega
            _ = mu.sum := by simpa only [Multiset.sum_cons] using hs
        have hsum := (mem_cycleTypes.mp hmu.1).1
        omega
      subst mu
      simp at hmu
      omega
    · intro h
      simpa using h
  · have hr : 2 ≤ r := by omega
    by_cases hnext : 2 ^ (Nat.log 2 r + 1) ∣ m
    · rw [if_pos (Or.inr hnext)]
      ext mu
      constructor
      · intro hmu
        exfalso
        rw [mem_exceptionalHalfResidualTypes] at hmu
        have h2m : 2 ∣ m :=
          (dvd_pow_self 2 (by omega)).trans hnext
        have hmulhalf : mu.lcm ∣ m / 2 :=
          (exceptionalCycleType_lcm_dvd_lcmUpto hmu.1).trans
            (lcmUpto_dvd_half_of_next_two_pow_dvd hm hadm hnext)
        have := (lcm_half_eq_iff_not_dvd hm h2m
          ((exceptionalCycleType_lcm_dvd_lcmUpto hmu.1).trans hadm)).mp hmu.2
        exact this hmulhalf
      · intro h
        simpa using h
    · rw [if_neg (by simp [hrsmall, hnext])]
      ext mu
      rw [mem_exceptionalHalfResidualTypes, mem_logTwoCycleTypes]
      constructor
      · rintro ⟨hmu, horder⟩
        refine ⟨hmu, ?_⟩
        have hqle : 2 ^ Nat.log 2 r ≤ r := Nat.pow_log_le_self 2 (by omega)
        have hqpos : 0 < 2 ^ Nat.log 2 r := by positivity
        have hqm : 2 ^ Nat.log 2 r ∣ m :=
          (Nat.dvd_lcmUpto (by omega) hqle).trans hadm
        have h2m : 2 ∣ m := by
          have ha : 1 ≤ Nat.log 2 r :=
            Nat.le_log_of_pow_le (by omega) (by simpa using hr)
          exact (dvd_pow_self 2 (by omega)).trans hqm
        have hnot : ¬ mu.lcm ∣ m / 2 :=
          (lcm_half_eq_iff_not_dvd hm h2m
            ((exceptionalCycleType_lcm_dvd_lcmUpto hmu).trans hadm)).mp horder
        exact (cycleType_lcm_not_dvd_half_iff_logTwo_mem hr hm hadm hnext hmu).mp hnot
      · rintro ⟨hmu, hqmem⟩
        refine ⟨hmu, ?_⟩
        have hqle : 2 ^ Nat.log 2 r ≤ r := Nat.pow_log_le_self 2 (by omega)
        have hqpos : 0 < 2 ^ Nat.log 2 r := by positivity
        have hqm : 2 ^ Nat.log 2 r ∣ m :=
          (Nat.dvd_lcmUpto (by omega) hqle).trans hadm
        have h2m : 2 ∣ m := by
          have ha : 1 ≤ Nat.log 2 r :=
            Nat.le_log_of_pow_le (by omega) (by simpa using hr)
          exact (dvd_pow_self 2 (by omega)).trans hqm
        apply (lcm_half_eq_iff_not_dvd hm h2m
          ((exceptionalCycleType_lcm_dvd_lcmUpto hmu).trans hadm)).mpr
        exact (cycleType_lcm_not_dvd_half_iff_logTwo_mem hr hm hadm hnext hmu).mpr hqmem

theorem cycleDenominator_cons_two_equal_long {r h : ℕ} {mu : Multiset ℕ}
    (hmu : mu ∈ cycleTypes r) (hrh : r < h) :
    cycleDenominator (2 * h + r) (h ::ₘ h ::ₘ mu) =
      2 * h ^ 2 * cycleDenominator r mu := by
  classical
  have hhnot : h ∉ mu := not_mem_cycleType_of_sum_lt hmu hrh
  have hcount : mu.count h = 0 := Multiset.count_eq_zero.mpr hhnot
  have hsum : mu.sum ≤ r := (mem_cycleTypes.mp hmu).1
  simp only [cycleDenominator, Multiset.sum_cons, Multiset.prod_cons,
    Multiset.toFinset_cons]
  have hfixed : 2 * h + r - (h + (h + mu.sum)) = r - mu.sum := by omega
  rw [hfixed]
  have hcounts :
      ∏ j ∈ mu.toFinset, (Multiset.count j (h ::ₘ h ::ₘ mu)).factorial =
        ∏ j ∈ mu.toFinset, (mu.count j).factorial := by
    apply Finset.prod_congr rfl
    intro j hj
    have hjne : j ≠ h := by
      intro hjh
      subst j
      exact hhnot (Multiset.mem_toFinset.mp hj)
    simp [hjne]
  rw [Finset.insert_idem]
  rw [Finset.prod_insert (by simpa using hhnot)]
  simp only [Multiset.count_cons_self, hcount, zero_add, Nat.factorial_two]
  rw [hcounts]
  simp [cycleDenominator]
  ring

theorem cycleWeightReal_cons_two_equal_long {r h : ℕ} {mu : Multiset ℕ}
    (hmu : mu ∈ cycleTypes r) (hrh : r < h) :
    cycleWeightReal (2 * h + r) (h ::ₘ h ::ₘ mu) =
      (1 / (2 * (h : ℝ) ^ 2)) * cycleWeightReal r mu := by
  rw [cycleWeightReal, cycleWeightReal,
    cycleDenominator_cons_two_equal_long hmu hrh]
  push_cast
  field_simp

/-- Exact cycle-index mass of the order-`m` types consisting of two
`m/2`-cycles and a residual type on `r` letters. -/
noncomputable def exceptionalHalfContribution (r m : ℕ) : ℝ :=
  ∑ mu ∈ exceptionalHalfResidualTypes r m,
    cycleWeightReal (m + r) (m / 2 ::ₘ m / 2 ::ₘ mu)

theorem exceptionalHalfContribution_eq_halfCycleCorrection {r m : ℕ}
    (hrhalf : r < m / 2) (hadm : Nat.lcmUpto r ∣ m) :
    exceptionalHalfContribution r m = halfCycleCorrection (m + r) r := by
  classical
  have hmhalf : 0 < m / 2 := hrhalf.trans_le' (Nat.zero_le r)
  have hm : 0 < m := (Nat.div_le_self m 2).trans_lt' hmhalf
  have hsub : m + r - r = m := Nat.add_sub_cancel_right m r
  by_cases hzero : r ≤ 1 ∨ 2 ^ (Nat.log 2 r + 1) ∣ m
  · rw [exceptionalHalfContribution, exceptionalHalfResidualTypes_eq hrhalf hadm,
      if_pos hzero]
    simp [halfCycleCorrection, hzero, hsub]
  · have hr : 2 ≤ r := by omega
    have hnext : ¬ 2 ^ (Nat.log 2 r + 1) ∣ m := by tauto
    have hqle : 2 ^ Nat.log 2 r ≤ r := Nat.pow_log_le_self 2 (by omega)
    have hqpos : 0 < 2 ^ Nat.log 2 r := by positivity
    have hqm : 2 ^ Nat.log 2 r ∣ m :=
      (Nat.dvd_lcmUpto (by omega) hqle).trans hadm
    have h2m : 2 ∣ m := by
      have ha : 1 ≤ Nat.log 2 r :=
        Nat.le_log_of_pow_le (by omega) (by simpa using hr)
      exact (dvd_pow_self 2 (by omega)).trans hqm
    have htwice : 2 * (m / 2) = m := by
      simpa [Nat.mul_comm] using Nat.div_mul_cancel h2m
    rw [exceptionalHalfContribution, exceptionalHalfResidualTypes_eq hrhalf hadm,
      if_neg hzero]
    calc
      ∑ mu ∈ logTwoCycleTypes r,
          cycleWeightReal (m + r) (m / 2 ::ₘ m / 2 ::ₘ mu) =
          ∑ mu ∈ logTwoCycleTypes r,
            (1 / (2 * ((m / 2 : ℕ) : ℝ) ^ 2)) * cycleWeightReal r mu := by
        apply Finset.sum_congr rfl
        intro mu hmu
        have hw := cycleWeightReal_cons_two_equal_long
          (mem_logTwoCycleTypes.mp hmu).1 hrhalf
        rw [htwice] at hw
        exact hw
      _ = (1 / (2 * ((m / 2 : ℕ) : ℝ) ^ 2)) *
          (1 / ((2 ^ Nat.log 2 r : ℕ) : ℝ)) := by
        rw [← Finset.mul_sum, sum_logTwoCycleTypes_cycleWeightReal hr]
      _ = 2 / (((2 ^ Nat.log 2 r : ℕ) : ℝ) * (m : ℝ) ^ 2) := by
        have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
        have hhalfreal : (0 : ℝ) < (m / 2 : ℕ) := by exact_mod_cast hmhalf
        have hcast : (2 : ℝ) * (m / 2 : ℕ) = m := by exact_mod_cast htwice
        field_simp
        nlinarith
      _ = halfCycleCorrection (m + r) r := by
        rw [halfCycleCorrection]
        simp only [hsub]
        rw [if_neg hzero]

end Erdos1161
