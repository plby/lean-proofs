import ErdosProblems.Erdos988

open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory Metric Real Set

namespace Erdos991CapSupEnergy

open Erdos988

/-- Inner products with a fixed unit vector are `1`-Lipschitz on the sphere. -/
lemma abs_inner_sub_inner_le_dist (x u v : S2) :
    |inner ℝ (x : E3) (u : E3) - inner ℝ (x : E3) (v : E3)| ≤ dist u v := by
  calc
    |inner ℝ (x : E3) (u : E3) - inner ℝ (x : E3) (v : E3)| =
        |inner ℝ (x : E3) ((u : E3) - (v : E3))| := by rw [inner_sub_right]
    _ ≤ ‖(x : E3)‖ * ‖(u : E3) - (v : E3)‖ := abs_real_inner_le_norm _ _
    _ = dist u v := by
      rw [sphere2_norm, one_mul, Subtype.dist_eq, dist_eq_norm]

/-- Moving the cap center by less than `r` and lowering its threshold by `r`
can only enlarge the cap. -/
lemma sphericalCap_subset_of_dist_lt {u v : S2} {t r : ℝ} (huv : dist u v < r) :
    sphericalCap u t ⊆ sphericalCap v (t - r) := by
  intro x hx
  change t ≤ inner ℝ (x : E3) (u : E3) at hx
  change t - r ≤ inner ℝ (x : E3) (v : E3)
  have habs := abs_inner_sub_inner_le_dist x u v
  have hdiff : inner ℝ (x : E3) (u : E3) - inner ℝ (x : E3) (v : E3) < r :=
    (le_abs_self _).trans_lt (habs.trans_lt huv)
  linarith

lemma sphericalCap_subset_of_near_center {u v : S2} {s t r : ℝ}
    (huv : dist u v < r) (hst : s ≤ t - r) :
    sphericalCap u t ⊆ sphericalCap v s := by
  exact fun x hx ↦ hst.trans (sphericalCap_subset_of_dist_lt huv hx)

/-- Lower persistence of the signed cap error under a small center move and a
one-sided threshold move. -/
lemma signedCapError_lower_near (P : Finset S2) {u v : S2} {s t r : ℝ}
    (huv : dist u v < r) (hs₀ : t - 2 * r ≤ s) (hs₁ : s ≤ t - r) :
    signedCapError P u t - (P.card : ℝ) * r ≤ signedCapError P v s := by
  classical
  have hsub :
      P.filter (fun x ↦ x ∈ sphericalCap u t) ⊆
        P.filter (fun x ↦ x ∈ sphericalCap v s) := by
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, sphericalCap_subset_of_near_center huv hs₁ hx.2⟩
  have hcardNat := Finset.card_le_card hsub
  have hcard :
      ((P.filter (fun x ↦ x ∈ sphericalCap u t)).card : ℝ) ≤
        ((P.filter (fun x ↦ x ∈ sphericalCap v s)).card : ℝ) := by
    exact_mod_cast hcardNat
  have hn : (0 : ℝ) ≤ P.card := by positivity
  unfold signedCapError capArea
  nlinarith

/-- Upper persistence, used when the extremal signed error is negative. -/
lemma signedCapError_upper_near (P : Finset S2) {u v : S2} {s t r : ℝ}
    (huv : dist u v < r) (hs₀ : t + r ≤ s) (hs₁ : s ≤ t + 2 * r) :
    signedCapError P v s ≤ signedCapError P u t + (P.card : ℝ) * r := by
  classical
  have hsub :
      P.filter (fun x ↦ x ∈ sphericalCap v s) ⊆
        P.filter (fun x ↦ x ∈ sphericalCap u t) := by
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    have hdist : dist v u < r := by simpa [dist_comm] using huv
    exact ⟨hx.1, sphericalCap_subset_of_near_center hdist (by linarith) hx.2⟩
  have hcardNat := Finset.card_le_card hsub
  have hcard :
      ((P.filter (fun x ↦ x ∈ sphericalCap v s)).card : ℝ) ≤
        ((P.filter (fun x ↦ x ∈ sphericalCap u t)).card : ℝ) := by
    exact_mod_cast hcardNat
  have hn : (0 : ℝ) ≤ P.card := by positivity
  unfold signedCapError capArea
  nlinarith

/-- A positive cap error forces room between the threshold and `-1`. -/
lemma signedCapError_le_lower_room (P : Finset S2) (u : S2) (t : ℝ) :
    signedCapError P u t ≤ (P.card : ℝ) * (1 + t) / 2 := by
  classical
  have hcardNat := Finset.card_filter_le P (fun x ↦ x ∈ sphericalCap u t)
  have hcard :
      ((P.filter (fun x ↦ x ∈ sphericalCap u t)).card : ℝ) ≤ (P.card : ℝ) := by
    exact_mod_cast hcardNat
  unfold signedCapError capArea
  linarith

/-- A negative cap error forces room between the threshold and `1`. -/
lemma neg_signedCapError_le_upper_room (P : Finset S2) (u : S2) (t : ℝ) :
    -signedCapError P u t ≤ (P.card : ℝ) * (1 - t) / 2 := by
  classical
  have hcard :
      (0 : ℝ) ≤ ((P.filter (fun x ↦ x ∈ sphericalCap u t)).card : ℝ) := by
    positivity
  unfold signedCapError capArea
  linarith

/-- A large positive signed error persists on a product of a center ball and a
threshold interval.  This is the local regularity input behind the
`L²`-to-`L∞` upgrade. -/
lemma innerIntegral_lower_of_signedCapError_gt (P : Finset S2) (u : S2) {t q : ℝ}
    (hn : 0 < P.card) (ht : t ∈ Icc (-1 : ℝ) 1) (hq : 0 < q)
    (herr : q * (P.card : ℝ) < signedCapError P u t) :
    ∀ v ∈ Metric.ball u (q / 16),
      q / 16 * (q * (P.card : ℝ) / 2) ^ 2 ≤
        ∫ s in (-1 : ℝ)..1, analyticCapError P v s ^ 2 := by
  intro v hv
  have hnR : (0 : ℝ) < P.card := by exact_mod_cast hn
  have hr : 0 < q / 16 := by positivity
  have htroom := signedCapError_le_lower_room P u t
  have hqt : q < (1 + t) / 2 := by
    apply lt_of_mul_lt_mul_left (a := (P.card : ℝ)) _ hnR.le
    calc
      (P.card : ℝ) * q = q * (P.card : ℝ) := by ring
      _ < signedCapError P u t := herr
      _ ≤ (P.card : ℝ) * ((1 + t) / 2) := by
        simpa only [mul_div_assoc] using htroom
  have ha : (-1 : ℝ) ≤ t - 2 * (q / 16) := by linarith
  have hb : t - q / 16 ≤ 1 := by nlinarith [ht.2]
  have hab : t - 2 * (q / 16) ≤ t - q / 16 := by linarith
  have hfull := analyticCapError_intervalIntegrable_sq P v
  have hsmall : IntervalIntegrable (fun s : ℝ ↦ analyticCapError P v s ^ 2)
      volume (t - 2 * (q / 16)) (t - q / 16) := by
    apply hfull.mono_set
    rw [uIcc_of_le hab, uIcc_of_le (ha.trans (hab.trans hb))]
    exact Icc_subset_Icc ha hb
  have hconst : IntervalIntegrable (fun _s : ℝ ↦ (q * (P.card : ℝ) / 2) ^ 2)
      volume (t - 2 * (q / 16)) (t - q / 16) :=
    continuous_const.intervalIntegrable _ _
  have hpoint : ∀ s ∈ Icc (t - 2 * (q / 16)) (t - q / 16),
      (q * (P.card : ℝ) / 2) ^ 2 ≤ analyticCapError P v s ^ 2 := by
    intro s hs
    have hpersist := signedCapError_lower_near P
      (u := u) (v := v) (t := t) (s := s) (r := q / 16)
      (by simpa only [mem_ball, dist_comm] using hv) hs.1 hs.2
    have hsigned : q * (P.card : ℝ) / 2 ≤ signedCapError P v s := by
      nlinarith
    rw [analyticCapError_eq_signedCapError]
    exact (pow_le_pow_iff_left₀ (by positivity)
      ((by positivity : 0 ≤ q * (P.card : ℝ) / 2).trans hsigned) two_ne_zero).2 hsigned
  calc
    q / 16 * (q * (P.card : ℝ) / 2) ^ 2 =
        ∫ _s in (t - 2 * (q / 16))..(t - q / 16),
          (q * (P.card : ℝ) / 2) ^ 2 := by
      rw [intervalIntegral.integral_const]
      ring
    _ ≤ ∫ s in (t - 2 * (q / 16))..(t - q / 16),
        analyticCapError P v s ^ 2 :=
      intervalIntegral.integral_mono_on hab hconst hsmall hpoint
    _ ≤ ∫ s in (-1 : ℝ)..1, analyticCapError P v s ^ 2 := by
      apply intervalIntegral.integral_mono_interval ha hab hb
      · filter_upwards [] with s
        exact sq_nonneg _
      · exact hfull

/-- Negative signed errors have the analogous one-sided persistence interval. -/
lemma innerIntegral_lower_of_signedCapError_lt_neg (P : Finset S2) (u : S2) {t q : ℝ}
    (hn : 0 < P.card) (ht : t ∈ Icc (-1 : ℝ) 1) (hq : 0 < q)
    (herr : signedCapError P u t < -(q * (P.card : ℝ))) :
    ∀ v ∈ Metric.ball u (q / 16),
      q / 16 * (q * (P.card : ℝ) / 2) ^ 2 ≤
        ∫ s in (-1 : ℝ)..1, analyticCapError P v s ^ 2 := by
  intro v hv
  have hnR : (0 : ℝ) < P.card := by exact_mod_cast hn
  have hr : 0 < q / 16 := by positivity
  have htroom := neg_signedCapError_le_upper_room P u t
  have hqt : q < (1 - t) / 2 := by
    apply lt_of_mul_lt_mul_left (a := (P.card : ℝ)) _ hnR.le
    calc
      (P.card : ℝ) * q = q * (P.card : ℝ) := by ring
      _ < -signedCapError P u t := by linarith
      _ ≤ (P.card : ℝ) * ((1 - t) / 2) := by
        simpa only [mul_div_assoc] using htroom
  have ha : (-1 : ℝ) ≤ t + q / 16 := by nlinarith [ht.1]
  have hb : t + 2 * (q / 16) ≤ 1 := by linarith
  have hab : t + q / 16 ≤ t + 2 * (q / 16) := by linarith
  have hfull := analyticCapError_intervalIntegrable_sq P v
  have hsmall : IntervalIntegrable (fun s : ℝ ↦ analyticCapError P v s ^ 2)
      volume (t + q / 16) (t + 2 * (q / 16)) := by
    apply hfull.mono_set
    rw [uIcc_of_le hab, uIcc_of_le (ha.trans (hab.trans hb))]
    exact Icc_subset_Icc ha hb
  have hconst : IntervalIntegrable (fun _s : ℝ ↦ (q * (P.card : ℝ) / 2) ^ 2)
      volume (t + q / 16) (t + 2 * (q / 16)) :=
    continuous_const.intervalIntegrable _ _
  have hpoint : ∀ s ∈ Icc (t + q / 16) (t + 2 * (q / 16)),
      (q * (P.card : ℝ) / 2) ^ 2 ≤ analyticCapError P v s ^ 2 := by
    intro s hs
    have hpersist := signedCapError_upper_near P
      (u := u) (v := v) (t := t) (s := s) (r := q / 16)
      (by simpa only [mem_ball, dist_comm] using hv) hs.1 hs.2
    have hsigned : signedCapError P v s ≤ -(q * (P.card : ℝ) / 2) := by
      nlinarith
    rw [analyticCapError_eq_signedCapError]
    have hnegF : 0 ≤ -signedCapError P v s := by
      have hbase : 0 ≤ q * (P.card : ℝ) / 2 := by positivity
      linarith
    calc
      (q * (P.card : ℝ) / 2) ^ 2 ≤ (-signedCapError P v s) ^ 2 :=
        (pow_le_pow_iff_left₀ (by positivity)
          hnegF two_ne_zero).2 (by linarith)
      _ = signedCapError P v s ^ 2 := by ring
  calc
    q / 16 * (q * (P.card : ℝ) / 2) ^ 2 =
        ∫ _s in (t + q / 16)..(t + 2 * (q / 16)),
          (q * (P.card : ℝ) / 2) ^ 2 := by
      rw [intervalIntegral.integral_const]
      ring
    _ ≤ ∫ s in (t + q / 16)..(t + 2 * (q / 16)),
        analyticCapError P v s ^ 2 :=
      intervalIntegral.integral_mono_on hab hconst hsmall hpoint
    _ ≤ ∫ s in (-1 : ℝ)..1, analyticCapError P v s ^ 2 := by
      apply intervalIntegral.integral_mono_interval ha hab hb
      · filter_upwards [] with s
        exact sq_nonneg _
      · exact hfull

/-- The only geometric measure fact used by the qualitative upgrade: every
fixed-radius spherical ball has a center-independent positive lower mass.
For `surfaceProbability` this follows directly from Mathlib's
`Measure.toSphereBallBound_mul_measureReal_unitBall_le_toSphere_ball`. -/
def UniformBallMassLower : Prop :=
  ∀ r : ℝ, 0 < r → ∃ c : ℝ, 0 < c ∧
    ∀ u : S2, c ≤ (surfaceProbability : Measure S2).real (Metric.ball u r)

/-- Faithful statement that the formula `(1-t)/2` used in `signedCapError` is
the actual normalized surface area of the corresponding closed cap. -/
def ExactSphericalCapArea : Prop :=
  ∀ (u : S2) (t : ℝ), t ∈ Icc (-1 : ℝ) 1 →
    (surfaceProbability : Measure S2).real (sphericalCap u t) = capArea t

lemma closedBall_eq_sphericalCap (u : S2) {r : ℝ} (hr : 0 ≤ r) :
    Metric.closedBall u r = sphericalCap u (1 - r ^ 2 / 2) := by
  ext x
  rw [mem_closedBall, mem_sphericalCap_iff_dist_sq_le]
  have hdist : 0 ≤ dist u x := dist_nonneg
  constructor
  · intro h
    have hsq : dist u x ^ 2 ≤ r ^ 2 :=
      (pow_le_pow_iff_left₀ hdist hr two_ne_zero).2 (by simpa [dist_comm] using h)
    nlinarith
  · intro h
    have hsq : dist u x ^ 2 ≤ r ^ 2 := by nlinarith
    have hdr : dist u x ≤ r := (pow_le_pow_iff_left₀ hdist hr two_ne_zero).1 hsq
    simpa [dist_comm] using hdr

/-- Exact cap area supplies the uniform positive ball mass needed above. -/
theorem uniformBallMassLower_of_exactSphericalCapArea
    (harea : ExactSphericalCapArea) : UniformBallMassLower := by
  intro r hr
  let ρ : ℝ := min (r / 2) 1
  have hρ0 : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by positivity) zero_lt_one
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  have hρr : ρ < r := by
    exact (min_le_left (r / 2) 1).trans_lt (half_lt_self hr)
  refine ⟨ρ ^ 2 / 4, by positivity, ?_⟩
  intro u
  have ht : 1 - ρ ^ 2 / 2 ∈ Icc (-1 : ℝ) 1 := by
    have hρsq : ρ ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hρ0.le (sub_nonneg.mpr hρ1)]
    constructor
    · nlinarith
    · nlinarith [sq_nonneg ρ]
  calc
    ρ ^ 2 / 4 = capArea (1 - ρ ^ 2 / 2) := by
      unfold capArea
      ring
    _ = (surfaceProbability : Measure S2).real
        (sphericalCap u (1 - ρ ^ 2 / 2)) := (harea u _ ht).symm
    _ = (surfaceProbability : Measure S2).real (Metric.closedBall u ρ) := by
      rw [closedBall_eq_sphericalCap u hρ0.le]
    _ ≤ (surfaceProbability : Measure S2).real (Metric.ball u r) := by
      exact measureReal_mono (Metric.closedBall_subset_ball hρr)

/-- One large normalized cap error forces a fixed positive normalized energy
deficit.  The constants are deliberately loose; only positivity matters. -/
theorem energy_gap_of_lt_discrepancy_of_ball_mass
    (P : Finset S2) {q c : ℝ}
    (hcmass : ∀ u : S2,
      c ≤ (surfaceProbability : Measure S2).real (Metric.ball u (q / 16)))
    (hn : 0 < P.card) (hq : 0 < q)
    (hdisc : q * (P.card : ℝ) < sphericalCapDiscrepancy P) :
    c * q ^ 3 * (P.card : ℝ) ^ 2 / 16 ≤ energyDeficit P := by
  obtain ⟨e, heSet, he⟩ := exists_lt_of_lt_csSup (capErrorSet_nonempty P) hdisc
  rcases heSet with ⟨u, t, ht, rfl⟩
  have habs : q * (P.card : ℝ) < |signedCapError P u t| := by
    simpa only [capError] using he
  have hlocal : ∀ v ∈ Metric.ball u (q / 16),
      q / 16 * (q * (P.card : ℝ) / 2) ^ 2 ≤
        ∫ s in (-1 : ℝ)..1, analyticCapError P v s ^ 2 := by
    rcases lt_abs.mp habs with hpos | hneg
    · exact innerIntegral_lower_of_signedCapError_gt P u hn ht hq hpos
    · exact innerIntegral_lower_of_signedCapError_lt_neg P u hn ht hq (by linarith)
  let L : ℝ := q / 16 * (q * (P.card : ℝ) / 2) ^ 2
  let F : S2 → ℝ := fun v ↦
    ∫ s in (-1 : ℝ)..1, analyticCapError P v s ^ 2
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hindicInt : Integrable ((Metric.ball u (q / 16)).indicator (fun _v : S2 ↦ L))
      (surfaceProbability : Measure S2) :=
    (integrable_const L).indicator measurableSet_ball
  have hFInt : Integrable F (surfaceProbability : Measure S2) := by
    simpa only [F] using integrable_intervalIntegral_analyticCapError_sq P
  have hpoint : ∀ v : S2,
      (Metric.ball u (q / 16)).indicator (fun _v : S2 ↦ L) v ≤ F v := by
    intro v
    by_cases hv : v ∈ Metric.ball u (q / 16)
    · simpa only [Set.indicator_of_mem hv, L, F] using hlocal v hv
    · simp only [Set.indicator, hv, if_false]
      dsimp only [F]
      apply intervalIntegral.integral_nonneg_of_forall (by norm_num)
      intro s
      exact sq_nonneg _
  have houter :
      (surfaceProbability : Measure S2).real (Metric.ball u (q / 16)) * L ≤
        energyDeficit P / 4 := by
    calc
      (surfaceProbability : Measure S2).real (Metric.ball u (q / 16)) * L =
          ∫ v : S2, (Metric.ball u (q / 16)).indicator (fun _v : S2 ↦ L) v
            ∂(surfaceProbability : Measure S2) := by
        simpa only [smul_eq_mul] using
          (integral_indicator_const (μ := (surfaceProbability : Measure S2)) L
            measurableSet_ball).symm
      _ ≤ ∫ v : S2, F v ∂(surfaceProbability : Measure S2) :=
        MeasureTheory.integral_mono hindicInt hFInt hpoint
      _ = energyDeficit P / 4 := by
        simpa only [F] using finite_stolarsky P
  have hmassL : c * L ≤
      (surfaceProbability : Measure S2).real (Metric.ball u (q / 16)) * L := by
    exact mul_le_mul_of_nonneg_right (hcmass u) hL
  have h := hmassL.trans houter
  calc
    c * q ^ 3 * (P.card : ℝ) ^ 2 / 16 = 4 * (c * L) := by
      dsimp only [L]
      ring
    _ ≤ 4 * (energyDeficit P / 4) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = energyDeficit P := by ring

theorem energy_gap_of_lt_discrepancy
    (hball : UniformBallMassLower) (P : Finset S2) {q : ℝ}
    (hn : 0 < P.card) (hq : 0 < q)
    (hdisc : q * (P.card : ℝ) < sphericalCapDiscrepancy P) :
    ∃ c : ℝ, 0 < c ∧
      c * q ^ 3 * (P.card : ℝ) ^ 2 / 16 ≤ energyDeficit P := by
  obtain ⟨c, hc, hcmass⟩ := hball (q / 16) (by positivity)
  exact ⟨c, hc,
    energy_gap_of_lt_discrepancy_of_ball_mass P hcmass hn hq hdisc⟩

/-- Qualitative `L²`-to-`L∞` transfer.  Thus any sequence whose normalized
Stolarsky energy deficit tends to zero has normalized cap discrepancy tending
to zero. -/
theorem tendsto_discrepancy_div_of_tendsto_energyDeficit_div_sq
    (hball : UniformBallMassLower) (P : ℕ → Finset S2)
    (hcard : ∀ n : ℕ, (P n).card = n)
    (henergy : Tendsto
      (fun n : ℕ ↦ energyDeficit (P n) / (n : ℝ) ^ 2) atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦ sphericalCapDiscrepancy (P n) / (n : ℝ))
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_cases hεlarge : 1 < ε
  · refine ⟨1, ?_⟩
    intro n hn
    have hnpos : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by positivity
    have hD0 := sphericalCapDiscrepancy_nonneg (P n)
    have hDcard := sphericalCapDiscrepancy_le_card (P n)
    rw [hcard n] at hDcard
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hD0 hnR.le)]
    exact (div_le_one hnR).2 hDcard |>.trans_lt hεlarge
  · have hεone : ε ≤ 1 := le_of_not_gt hεlarge
    let q : ℝ := ε / 2
    have hq : 0 < q := by dsimp [q]; positivity
    obtain ⟨c, hc, hcmass⟩ := hball (q / 16) (by positivity)
    have hK : 0 < c * q ^ 3 / 16 := by positivity
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp henergy) (c * q ^ 3 / 16) hK
    refine ⟨max N 1, ?_⟩
    intro n hn
    have hnN : N ≤ n := (le_max_left N 1).trans hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right N 1).trans hn)
    have hnR : (0 : ℝ) < n := by positivity
    have hEclose := hN n hnN
    have hE0 := energyDeficit_nonneg (P n)
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg hE0 (sq_nonneg (n : ℝ)))] at hEclose
    have hD0 := sphericalCapDiscrepancy_nonneg (P n)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hD0 hnR.le)]
    by_contra hnot
    have hratio : ε ≤ sphericalCapDiscrepancy (P n) / (n : ℝ) := le_of_not_gt hnot
    have hεmul : ε * (n : ℝ) ≤ sphericalCapDiscrepancy (P n) :=
      (le_div_iff₀ hnR).mp hratio
    have hqdisc : q * ((P n).card : ℝ) < sphericalCapDiscrepancy (P n) := by
      rw [hcard n]
      dsimp only [q]
      nlinarith
    have hgap := energy_gap_of_lt_discrepancy_of_ball_mass (P n) hcmass
      (by simpa [hcard n] using hnpos) hq hqdisc
    rw [hcard n] at hgap
    have hsqpos : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
    have hconstle : c * q ^ 3 / 16 ≤ energyDeficit (P n) / (n : ℝ) ^ 2 := by
      apply (le_div_iff₀ hsqpos).2
      calc
        c * q ^ 3 / 16 * (n : ℝ) ^ 2 = c * q ^ 3 * (n : ℝ) ^ 2 / 16 := by ring
        _ ≤ energyDeficit (P n) := hgap
    exact (hconstle.trans_lt hEclose).false

theorem discrepancy_isLittleO_of_energyDeficit
    (hball : UniformBallMassLower) (P : ℕ → Finset S2)
    (hcard : ∀ n : ℕ, (P n).card = n)
    (henergy : Tendsto
      (fun n : ℕ ↦ energyDeficit (P n) / (n : ℝ) ^ 2) atTop (nhds 0)) :
    (fun n : ℕ ↦ sphericalCapDiscrepancy (P n)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  refine (Asymptotics.isLittleO_iff_tendsto' ?_).2 ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn hzero
    have hnzero : n ≠ 0 := by omega
    exact (hnzero (Nat.cast_eq_zero.mp hzero)).elim
  · exact tendsto_discrepancy_div_of_tendsto_energyDeficit_div_sq hball P hcard henergy

theorem discrepancy_isLittleO_of_energyDeficit_of_exactSphericalCapArea
    (harea : ExactSphericalCapArea) (P : ℕ → Finset S2)
    (hcard : ∀ n : ℕ, (P n).card = n)
    (henergy : Tendsto
      (fun n : ℕ ↦ energyDeficit (P n) / (n : ℝ) ^ 2) atTop (nhds 0)) :
    (fun n : ℕ ↦ sphericalCapDiscrepancy (P n)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ)) :=
  discrepancy_isLittleO_of_energyDeficit
    (uniformBallMassLower_of_exactSphericalCapArea harea) P hcard henergy

end Erdos991CapSupEnergy
