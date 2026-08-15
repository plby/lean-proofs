import Mathlib

/-!
# Geometric scales for the Erdős 266 construction

This file collects the elementary asymptotic and scheduling facts used by the
diagonal construction.  Keeping them separate makes the analytic/block part of
the proof independent of routine power arithmetic.
-/

open Filter
open scoped Topology

namespace Erdos266

noncomputable section

/-- The large scale of block `k`. -/
def N (k : ℕ) : ℕ := 16 ^ (k + 1)

/-- The radius of the integer perturbations in block `k`. -/
def M (k : ℕ) : ℕ := 4 ^ (k + 1)

lemma N_pos (k : ℕ) : 0 < N k := by
  simp [N]

lemma M_pos (k : ℕ) : 0 < M k := by
  simp [M]

lemma N_ne_zero (k : ℕ) : N k ≠ 0 := (N_pos k).ne'

lemma M_ne_zero (k : ℕ) : M k ≠ 0 := (M_pos k).ne'

lemma one_le_N (k : ℕ) : 1 ≤ N k := Nat.one_le_iff_ne_zero.2 (N_ne_zero k)

lemma one_le_M (k : ℕ) : 1 ≤ M k := Nat.one_le_iff_ne_zero.2 (M_ne_zero k)

lemma M_sq (k : ℕ) : M k ^ 2 = N k := by
  simp only [M, N]
  rw [show 16 = 4 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
  congr 1
  omega

lemma N_succ (k : ℕ) : N (k + 1) = 16 * N k := by
  simp [N, pow_succ, mul_comm]

lemma M_succ (k : ℕ) : M (k + 1) = 4 * M k := by
  simp [M, pow_succ, mul_comm]

lemma N_strictMono : StrictMono N := by
  intro a b hab
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

lemma M_strictMono : StrictMono M := by
  intro a b hab
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

lemma M_le_N (k : ℕ) : M k ≤ N k := by
  rw [← M_sq]
  nlinarith [one_le_M k]

/-- For dimensions at most `k + 1`, the perturbation radius fits the local
linearization window. -/
lemma four_mul_dim_mul_M_le_N {d k : ℕ} (hd : d ≤ k + 1) :
    4 * d * M k ≤ N k := by
  rw [← M_sq]
  have hkpow : k + 1 ≤ 4 ^ k := by
    clear d hd
    induction k with
    | zero => norm_num
    | succ k ih =>
        calc
          k + 2 ≤ 4 * (k + 1) := by omega
          _ ≤ 4 * 4 ^ k := Nat.mul_le_mul_left 4 ih
          _ = 4 ^ (k + 1) := by rw [pow_succ]; ring
  have hdk : d ≤ M k / 4 := by
    have : M k / 4 = 4 ^ k := by simp [M, pow_succ]
    rw [this]
    exact hd.trans hkpow
  have h4 : 4 * d ≤ M k := by
    have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mp hdk
    simpa [mul_comm] using this
  nlinarith [M_pos k]

lemma M_le_N_div_four_mul {d k : ℕ} (hd : d ≤ k + 1) (hdpos : 0 < d) :
    M k ≤ N k / (4 * d) := by
  exact (Nat.le_div_iff_mul_le (by positivity : 0 < 4 * d)).2 (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using four_mul_dim_mul_M_le_N hd)

/-- The quotient which occurs after dividing the old block error by the next
block's permitted error.  Since `N = M²`, this is
`N (k+1) ^ (e+1/2) / N k ^ (e+1)` without real square roots. -/
def absorptionRatio (e k : ℕ) : ℝ :=
  (M (k + 1) : ℝ) * (N (k + 1) : ℝ) ^ e / (N k : ℝ) ^ (e + 1)

lemma absorptionRatio_succ (e k : ℕ) :
    absorptionRatio e (k + 1) = absorptionRatio e k * ((1 : ℝ) / 4) := by
  simp only [absorptionRatio, N_succ, M_succ, Nat.cast_mul, Nat.cast_ofNat]
  rw [mul_pow, mul_pow, pow_succ]
  have hNk : (N k : ℝ) ≠ 0 := by exact_mod_cast N_ne_zero k
  have hNks : (N (k + 1) : ℝ) ≠ 0 := by exact_mod_cast N_ne_zero (k + 1)
  field_simp [hNk, hNks]
  ring

lemma absorptionRatio_eq (e k : ℕ) :
    absorptionRatio e k = absorptionRatio e 0 * ((1 : ℝ) / 4) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [absorptionRatio_succ, ih, pow_succ]
      ring

lemma absorptionRatio_zero (e : ℕ) : absorptionRatio e 0 = (16 : ℝ) ^ e := by
  norm_num [absorptionRatio, N, M]
  rw [show (256 : ℝ) = 16 ^ 2 by norm_num, ← pow_mul, pow_succ]
  field_simp
  ring

lemma absorptionRatio_closedForm (e k : ℕ) :
    absorptionRatio e k = (16 : ℝ) ^ (e + 1) / (4 : ℝ) ^ (k + 2) := by
  rw [absorptionRatio_eq, absorptionRatio_zero, one_div_pow, pow_add, pow_succ]
  norm_num
  field_simp
  ring

lemma absorptionRatio_nonneg (e k : ℕ) : 0 ≤ absorptionRatio e k := by
  unfold absorptionRatio
  positivity

lemma absorptionRatio_pos (e k : ℕ) : 0 < absorptionRatio e k := by
  unfold absorptionRatio N M
  positivity

lemma tendsto_absorptionRatio (e : ℕ) :
    Tendsto (absorptionRatio e) atTop (nhds 0) := by
  have hp : Tendsto (fun k : ℕ => ((1 : ℝ) / 4) ^ k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h : Tendsto
      (fun k : ℕ => absorptionRatio e 0 * ((1 : ℝ) / 4) ^ k)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hp
  exact h.congr' (Filter.Eventually.of_forall fun k => (absorptionRatio_eq e k).symm)

lemma tendsto_const_mul_absorptionRatio (C : ℝ) (e : ℕ) :
    Tendsto (fun k => C * absorptionRatio e k) atTop (nhds 0) :=
  by simpa using tendsto_const_nhds.mul (tendsto_absorptionRatio e)

lemma eventually_const_mul_absorptionRatio_lt
    (C : ℝ) (e : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, C * absorptionRatio e k < ε := by
  exact (tendsto_const_mul_absorptionRatio C e).eventually (gt_mem_nhds hε)

lemma eventually_const_mul_absorptionRatio_le
    (C : ℝ) (e : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, C * absorptionRatio e k ≤ ε :=
  (eventually_const_mul_absorptionRatio_lt C e hε).mono fun _ => le_of_lt

/-- A coordinatewise form of the absorption inequality used between adjacent
blocks. -/
lemma eventually_localAbsorption (i : ℕ) {D ε : ℝ}
    (_hD : 0 ≤ D) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      D * (1 / (N k : ℝ) ^ (i + 2) +
          (M k : ℝ) ^ 2 / (N k : ℝ) ^ (i + 3)) ≤
        ε * (M (k + 1) : ℝ) / (N (k + 1) : ℝ) ^ (i + 2) := by
  have hev := eventually_const_mul_absorptionRatio_le
    (2 * D / ε) (i + 1) zero_lt_one
  filter_upwards [hev] with k hk
  have hNk : (N k : ℝ) ≠ 0 := by exact_mod_cast N_ne_zero k
  have hNks : (N (k + 1) : ℝ) ≠ 0 := by exact_mod_cast N_ne_zero (k + 1)
  have hMks : (M (k + 1) : ℝ) ≠ 0 := by exact_mod_cast M_ne_zero (k + 1)
  have hε0 : ε ≠ 0 := hε.ne'
  have hsquare : (M k : ℝ) ^ 2 = (N k : ℝ) := by
    exact_mod_cast M_sq k
  have hsquares : (M (k + 1) : ℝ) ^ 2 = (N (k + 1) : ℝ) := by
    exact_mod_cast M_sq (k + 1)
  calc
    D * (1 / (N k : ℝ) ^ (i + 2) +
          (M k : ℝ) ^ 2 / (N k : ℝ) ^ (i + 3)) =
        (ε * (M (k + 1) : ℝ) / (N (k + 1) : ℝ) ^ (i + 2)) *
          ((2 * D / ε) * absorptionRatio (i + 1) k) := by
            unfold absorptionRatio
            rw [hsquare, ← hsquares]
            field_simp [absorptionRatio, hNk, hNks, hMks, hε0]
            ring
    _ ≤ (ε * (M (k + 1) : ℝ) / (N (k + 1) : ℝ) ^ (i + 2)) * 1 := by
      exact mul_le_mul_of_nonneg_left hk (by positivity)
    _ = ε * (M (k + 1) : ℝ) / (N (k + 1) : ℝ) ^ (i + 2) := by ring

/-- `Absorbs ε D d e k` says that every one of the first `d` coordinates has
enough room at block `k+1` to absorb the error made at block `k`. -/
def Absorbs (ε D : ℕ → ℝ) (d e k : ℕ) : Prop :=
  ∀ i < d,
    D d * (1 / (N k : ℝ) ^ (i + 2) +
        (M k : ℝ) ^ 2 / (N k : ℝ) ^ (i + 3)) ≤
      ε e * (M (k + 1) : ℝ) / (N (k + 1) : ℝ) ^ (i + 2)

lemma eventually_absorbs (ε D : ℕ → ℝ)
    (hε : ∀ e, 0 < ε e) (hD : ∀ d, 0 ≤ D d) (d e : ℕ) :
    ∀ᶠ k : ℕ in atTop, Absorbs ε D d e k := by
  have hi : ∀ i ∈ Finset.range d, ∀ᶠ k : ℕ in atTop,
      D d * (1 / (N k : ℝ) ^ (i + 2) +
          (M k : ℝ) ^ 2 / (N k : ℝ) ^ (i + 3)) ≤
        ε e * (M (k + 1) : ℝ) / (N (k + 1) : ℝ) ^ (i + 2) := by
    intro i hi
    exact eventually_localAbsorption i (hD d) (hε e)
  filter_upwards [(Finset.eventually_all (Finset.range d)).2 hi] with k hk
  intro i hid
  exact hk i (Finset.mem_range.2 hid)

/-- Extract a concrete threshold from an eventual predicate. -/
def eventualThreshold {P : ℕ → Prop} (hP : ∀ᶠ k : ℕ in atTop, P k) : ℕ :=
  Classical.choose (eventually_atTop.1 hP)

lemma eventualThreshold_spec {P : ℕ → Prop} (hP : ∀ᶠ k : ℕ in atTop, P k)
    {k : ℕ} (hk : eventualThreshold hP ≤ k) : P k :=
  Classical.choose_spec (eventually_atTop.1 hP) k hk

/-- A threshold at which both the stationary-dimension and dimension-transition
absorption estimates hold. -/
def absorptionThreshold (ε D : ℕ → ℝ)
    (hε : ∀ e, 0 < ε e) (hD : ∀ d, 0 ≤ D d) (d : ℕ) : ℕ :=
  max d (eventualThreshold
    ((eventually_absorbs ε D hε hD d d).and
      (eventually_absorbs ε D hε hD d (d + 1))))

lemma absorptionThreshold_ge (ε D : ℕ → ℝ)
    (hε : ∀ e, 0 < ε e) (hD : ∀ d, 0 ≤ D d) (d : ℕ) :
    d ≤ absorptionThreshold ε D hε hD d :=
  le_max_left _ _

lemma absorptionThreshold_spec (ε D : ℕ → ℝ)
    (hε : ∀ e, 0 < ε e) (hD : ∀ d, 0 ≤ D d) (d : ℕ) {k : ℕ}
    (hk : absorptionThreshold ε D hε hD d ≤ k) :
    Absorbs ε D d d k ∧ Absorbs ε D d (d + 1) k := by
  let hboth := (eventually_absorbs ε D hε hD d d).and
    (eventually_absorbs ε D hε hD d (d + 1))
  apply @eventualThreshold_spec
    (fun k => Absorbs ε D d d k ∧ Absorbs ε D d (d + 1) k) hboth k
  dsimp [absorptionThreshold] at hk
  exact (le_max_right d _).trans hk

/-- Turn arbitrary lower bounds into a strictly increasing schedule which also
lies above the diagonal. -/
def schedule (threshold : ℕ → ℕ) : ℕ → ℕ
  | 0 => threshold 0
  | d + 1 => max (schedule threshold d + 1) (max (threshold (d + 1)) (d + 1))

lemma threshold_le_schedule (threshold : ℕ → ℕ) (d : ℕ) :
    threshold d ≤ schedule threshold d := by
  cases d with
  | zero => rfl
  | succ d =>
      exact (le_max_left _ _).trans (le_max_right _ _)

lemma index_le_schedule (threshold : ℕ → ℕ) (d : ℕ) :
    d ≤ schedule threshold d := by
  cases d with
  | zero => exact Nat.zero_le _
  | succ d =>
      exact (le_max_right _ _).trans (le_max_right _ _)

lemma schedule_succ (threshold : ℕ → ℕ) (d : ℕ) :
    schedule threshold d + 1 ≤ schedule threshold (d + 1) :=
  le_max_left _ _

lemma schedule_strictMono (threshold : ℕ → ℕ) :
    StrictMono (schedule threshold) := by
  exact strictMono_nat_of_lt_succ fun d => lt_of_lt_of_le (Nat.lt_succ_self _)
    (schedule_succ threshold d)

/-- Largest scheduled dimension which has started by stage `k`. -/
def activeDim (threshold : ℕ → ℕ) (k : ℕ) : ℕ :=
  Nat.findGreatest (fun d => schedule threshold d ≤ k) k

lemma activeDim_le (threshold : ℕ → ℕ) (k : ℕ) :
    activeDim threshold k ≤ k :=
  Nat.findGreatest_le k

lemma le_activeDim (threshold : ℕ → ℕ) {d k : ℕ}
    (hdk : d ≤ k) (hstart : schedule threshold d ≤ k) :
    d ≤ activeDim threshold k :=
  Nat.le_findGreatest hdk hstart

lemma scheduled_le_activeDim (threshold : ℕ → ℕ) {d k : ℕ}
    (hstart : schedule threshold d ≤ k) : d ≤ activeDim threshold k := by
  exact le_activeDim threshold ((index_le_schedule threshold d).trans hstart) hstart

lemma schedule_activeDim_le (threshold : ℕ → ℕ) {k : ℕ}
    (hk : schedule threshold 0 ≤ k) :
    schedule threshold (activeDim threshold k) ≤ k := by
  unfold activeDim
  exact Nat.findGreatest_spec (P := fun d => schedule threshold d ≤ k)
    (Nat.zero_le k) hk

lemma activeDim_mono (threshold : ℕ → ℕ) :
    Monotone (activeDim threshold) := by
  intro k l hkl
  by_cases hk : schedule threshold 0 ≤ k
  · apply le_activeDim threshold
    · exact (activeDim_le threshold k).trans hkl
    · exact (schedule_activeDim_le threshold hk).trans hkl
  · have hzero : activeDim threshold k = 0 := by
      rw [activeDim, Nat.findGreatest_eq_iff]
      refine ⟨Nat.zero_le _, ?_, ?_⟩
      · simp
      · intro n hn hnk hnstart
        apply hk
        exact ((schedule_strictMono threshold).monotone (Nat.zero_le n)).trans hnstart
    simp [hzero]

lemma activeDim_succ_le (threshold : ℕ → ℕ) (k : ℕ) :
    activeDim threshold (k + 1) ≤ activeDim threshold k + 1 := by
  by_cases hzero : activeDim threshold (k + 1) = 0
  · simp [hzero]
  · have hpos : 0 < activeDim threshold (k + 1) := Nat.pos_of_ne_zero hzero
    let d := activeDim threshold (k + 1) - 1
    have hd : d + 1 = activeDim threshold (k + 1) := by
      dsimp [d]
      omega
    have hstarted : schedule threshold (d + 1) ≤ k + 1 := by
      rw [hd]
      have hfg : Nat.findGreatest (fun d => schedule threshold d ≤ k + 1) (k + 1) =
          activeDim threshold (k + 1) := rfl
      exact (Nat.findGreatest_eq_iff.mp hfg).2.1 hzero
    have hdstart : schedule threshold d ≤ k := by
      have := schedule_succ threshold d
      omega
    have hdk : d ≤ k := (index_le_schedule threshold d).trans hdstart
    have hdactive : d ≤ activeDim threshold k := le_activeDim threshold hdk hdstart
    omega

lemma activeDim_succ_eq_or_eq_succ (threshold : ℕ → ℕ) (k : ℕ) :
    activeDim threshold (k + 1) = activeDim threshold k ∨
      activeDim threshold (k + 1) = activeDim threshold k + 1 := by
  have hmono : activeDim threshold k ≤ activeDim threshold (k + 1) := by
    simpa only [Nat.succ_eq_add_one] using activeDim_mono threshold (Nat.le_succ k)
  have hle := activeDim_succ_le threshold k
  omega

lemma tendsto_activeDim (threshold : ℕ → ℕ) :
    Tendsto (activeDim threshold) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro d
  refine ⟨max (schedule threshold d) d, ?_⟩
  intro k hk
  apply le_activeDim threshold
  · exact (le_max_right _ _).trans hk
  · exact (le_max_left _ _).trans hk

/-- If the threshold function was built from `absorptionThreshold`, the active
dimension has both estimates needed to stay fixed or increase by one. -/
lemma activeDim_absorbs (ε D : ℕ → ℝ)
    (hε : ∀ e, 0 < ε e) (hD : ∀ d, 0 ≤ D d) {k : ℕ}
    (hk : schedule (absorptionThreshold ε D hε hD) 0 ≤ k) :
    let d := activeDim (absorptionThreshold ε D hε hD) k
    Absorbs ε D d d k ∧ Absorbs ε D d (d + 1) k := by
  dsimp only
  apply absorptionThreshold_spec ε D hε hD
  exact (threshold_le_schedule (absorptionThreshold ε D hε hD) _).trans
    (schedule_activeDim_le _ hk)

/-- Every polynomial weight is summable against the reciprocal geometric
scale. -/
lemma summable_polynomial_div_N (p : ℕ) :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ p / (N k : ℝ)) := by
  have hbase : Summable (fun k : ℕ => (k : ℝ) ^ p * ((1 : ℝ) / 16) ^ k) := by
    simpa [Real.norm_of_nonneg] using
      (summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) p
        (r := ((1 : ℝ) / 16)) (by norm_num))
  have hshift := (summable_nat_add_iff 1).2 hbase
  apply hshift.congr
  intro k
  simp only [N, Nat.cast_pow, Nat.cast_ofNat]
  change ((k + 1 : ℕ) : ℝ) ^ p * ((1 : ℝ) / 16) ^ (k + 1) =
    ((k + 1 : ℕ) : ℝ) ^ p / (16 : ℝ) ^ (k + 1)
  rw [one_div_pow]
  ring

/-- The same summability remains true with any positive fixed power of `N` in
the denominator. -/
lemma summable_polynomial_div_N_pow (p q : ℕ) (hq : 0 < q) :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ p / (N k : ℝ) ^ q) := by
  apply (summable_polynomial_div_N p).of_nonneg_of_le
  · intro k
    positivity
  · intro k
    have hpowNat : N k ^ 1 ≤ N k ^ q :=
      Nat.pow_le_pow_right (one_le_N k) (by omega)
    have hpow : (N k : ℝ) ≤ (N k : ℝ) ^ q := by
      exact_mod_cast (by simpa using hpowNat)
    exact div_le_div_of_nonneg_left (by positivity)
      (Nat.cast_pos.2 (N_pos k)) hpow

lemma summable_succ_div_N :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) / (N k : ℝ)) := by
  simpa using summable_polynomial_div_N 1

lemma summable_const_mul_polynomial_div_N (C : ℝ) (p : ℕ) :
    Summable (fun k : ℕ => C * (((k + 1 : ℕ) : ℝ) ^ p / (N k : ℝ))) :=
  (summable_polynomial_div_N p).mul_left C

end

end Erdos266
