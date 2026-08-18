/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.Parameters
import ErdosProblems.Erdos186.Asymptotic
import ErdosProblems.Erdos186.PZ.Reduction.BoundedContext
import ErdosProblems.Erdos186.PZ.Reduction.Normalization

/-!
# A canonical admissible CFP scale

The scale used in the Pham--Zakharov replacement process is the integer part
of `m / (scaleDen * (log₂ m)²)`.  For fixed ambient dimension it eventually
dominates every power `m^a` with `0 < a < 1`, while still satisfying the
upper-scale hypothesis of the CFP theorem.  This file also provides the
run-specific selector whose domain records the stronger scale exponent.
-/

namespace Erdos186.PZ.Reduction

open Filter
open scoped Topology

noncomputable section

/-- The real scale before rounding down. -/
def canonicalScaleReal {β η : ℝ} (C : HigherDimensionalContext β η)
    (d m : ℕ) : ℝ :=
  (m : ℝ) /
    ((C.scaleDen d : ℝ) * (Real.logb 2 (m : ℝ)) ^ 2)

/-- The natural-valued scale used in the CFP application. -/
def canonicalScale {β η : ℝ} (C : HigherDimensionalContext β η)
    (d m : ℕ) : ℕ :=
  ⌊canonicalScaleReal C d m⌋₊

/-- Scale exponent used with the population stopping exponent `1-ε/2`.
Their product is exactly the source saving exponent `1-ε`. -/
def guardedScaleExponent (ε : ℝ) : ℝ :=
  (1 - ε) / (1 - ε / 2)

theorem guardedScaleExponent_pos {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) : 0 < guardedScaleExponent ε := by
  exact div_pos (sub_pos.mpr hε1) (sub_pos.mpr (by linarith))

theorem guardedScaleExponent_lt_one {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) : guardedScaleExponent ε < 1 := by
  rw [guardedScaleExponent, div_lt_one (sub_pos.mpr (by linarith))]
  linarith

theorem one_sub_le_guardedScaleExponent {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    1 - ε ≤ guardedScaleExponent ε := by
  rw [guardedScaleExponent, le_div_iff₀ (sub_pos.mpr (by linarith))]
  have hnonneg : 0 ≤ 1 - ε := (sub_pos.mpr hε1).le
  nlinarith

theorem cutoff_mul_guardedScaleExponent {ε : ℝ} (hε : ε < 2) :
    (1 - ε / 2) * guardedScaleExponent ε = 1 - ε := by
  rw [guardedScaleExponent]
  have hden : (2 - ε : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hε)
  field_simp [hden]

/-- Every fixed multiple of `(log₂ m)²` is eventually dominated by every
positive power of `m`. -/
theorem eventually_const_mul_logb_sq_le_nat_rpow (R : ℝ)
    {q : ℝ} (hq : 0 < q) :
    ∀ᶠ m : ℕ in atTop,
      R * (Real.logb 2 (m : ℝ)) ^ 2 ≤ (m : ℝ) ^ q := by
  have hq2 : 0 < q / 2 := half_pos hq
  have hlog := eventually_nat_log_rpow_le_rpow 2 hq2
  have hconst := (nat_rpow_tendsto_atTop hq2).eventually_ge_atTop
    (max 0 (R / (Real.log 2) ^ 2))
  filter_upwards [hlog, hconst,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
    tendsto_natCast_atTop_atTop.eventually_gt_atTop (0 : ℝ)]
      with m hm hmR hlogpos hmpos
  have hlog2 : Real.log (m : ℝ) ^ (2 : ℝ) =
      Real.log (m : ℝ) ^ (2 : ℕ) := by
    rw [Real.rpow_two]
  rw [hlog2] at hm
  have hden : 0 < (Real.log 2) ^ 2 :=
    sq_pos_of_pos (Real.log_pos (by norm_num))
  have hR : R / (Real.log 2) ^ 2 ≤ (m : ℝ) ^ (q / 2) :=
    le_trans (le_max_right _ _) hmR
  have hmhalf : 0 ≤ (m : ℝ) ^ (q / 2) :=
    Real.rpow_nonneg hmpos.le _
  have hlogsq : 0 ≤ Real.log (m : ℝ) ^ 2 := sq_nonneg _
  calc
    R * (Real.logb 2 (m : ℝ)) ^ 2 =
        (R / (Real.log 2) ^ 2) * (Real.log (m : ℝ) ^ 2) := by
      rw [Real.logb]
      field_simp
    _ ≤ (m : ℝ) ^ (q / 2) * (Real.log (m : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_right hR hlogsq
    _ ≤ (m : ℝ) ^ (q / 2) * (m : ℝ) ^ (q / 2) := by
      exact mul_le_mul_of_nonneg_left hm hmhalf
    _ = (m : ℝ) ^ q := by
      rw [← Real.rpow_add hmpos]
      ring_nf

/-- The canonical integer scale eventually dominates any prescribed power
strictly between zero and one. -/
theorem eventually_rpow_le_canonicalScale
    {β η : ℝ} (C : HigherDimensionalContext β η) (d : ℕ)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ᶠ m : ℕ in atTop,
      (m : ℝ) ^ a ≤ (canonicalScale C d m : ℝ) := by
  have hq : 0 < 1 - a := sub_pos.mpr ha1
  have hgrowth := eventually_const_mul_logb_sq_le_nat_rpow
    (R := (2 : ℝ) * (C.scaleDen d : ℝ)) hq
  filter_upwards [hgrowth,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 : ℝ)]
      with m hgrowth hlog hm
  have hmpos : 0 < (m : ℝ) := zero_lt_one.trans_le hm
  have hlogb : 0 < Real.logb 2 (m : ℝ) := by
    exact div_pos hlog (Real.log_pos (by norm_num))
  have hden : 0 < (C.scaleDen d : ℝ) *
      (Real.logb 2 (m : ℝ)) ^ 2 := by
    exact mul_pos (by exact_mod_cast C.scaleDen_pos d)
      (sq_pos_of_pos hlogb)
  have hreal : 2 * (m : ℝ) ^ a ≤ canonicalScaleReal C d m := by
    rw [canonicalScaleReal]
    apply (le_div_iff₀ hden).2
    calc
      2 * (m : ℝ) ^ a *
            ((C.scaleDen d : ℝ) * (Real.logb 2 (m : ℝ)) ^ 2) =
          (m : ℝ) ^ a *
            ((2 : ℝ) * (C.scaleDen d : ℝ) *
              (Real.logb 2 (m : ℝ)) ^ 2) := by ring
      _ ≤ (m : ℝ) ^ a * (m : ℝ) ^ (1 - a) := by
        exact mul_le_mul_of_nonneg_left hgrowth
          (Real.rpow_nonneg hmpos.le _)
      _ = (m : ℝ) := by
        rw [← Real.rpow_add hmpos,
          show a + (1 - a) = (1 : ℝ) by ring, Real.rpow_one]
  have hpow_one : 1 ≤ (m : ℝ) ^ a := by
    simpa using Real.one_rpow a ▸
      Real.rpow_le_rpow (by norm_num) hm ha0.le
  have hbeforeFloor :
      (m : ℝ) ^ a ≤ canonicalScaleReal C d m - 1 := by
    linarith
  have hfloor : canonicalScaleReal C d m - 1 <
      (⌊canonicalScaleReal C d m⌋₊ : ℝ) :=
    Nat.sub_one_lt_floor _
  exact hbeforeFloor.trans hfloor.le

/-- The rounded canonical scale satisfies the CFP upper-scale hypothesis. -/
theorem eventually_canonicalScale_upper
    {β η : ℝ} (C : HigherDimensionalContext β η) (d : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      (C.scaleDen d : ℝ) * (canonicalScale C d m : ℝ) *
          Real.logb 2 (m : ℝ) ≤
        (C.scaleNum d : ℝ) * (m : ℝ) := by
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with m hm
  have hmreal : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogpos : 0 < Real.log (m : ℝ) :=
    Real.log_pos (one_lt_two.trans_le hmreal)
  have hlogb : 0 < Real.logb 2 (m : ℝ) :=
    div_pos hlogpos (Real.log_pos (by norm_num))
  have hlogb_one : 1 ≤ Real.logb 2 (m : ℝ) := by
    rw [Real.logb, le_div_iff₀ (Real.log_pos (by norm_num))]
    simpa using Real.strictMonoOn_log.monotoneOn
      (by norm_num : (0 : ℝ) < 2) (zero_lt_two.trans_le hmreal) hmreal
  have hden : 0 < (C.scaleDen d : ℝ) *
      (Real.logb 2 (m : ℝ)) ^ 2 :=
    mul_pos (by exact_mod_cast C.scaleDen_pos d) (sq_pos_of_pos hlogb)
  have hDne : (C.scaleDen d : ℝ) ≠ 0 := by
    exact_mod_cast (C.scaleDen_pos d).ne'
  have hfloor : (canonicalScale C d m : ℝ) ≤
      canonicalScaleReal C d m := by
    exact Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hden.le)
  have hnum_one : (1 : ℝ) ≤ C.scaleNum d := by
    exact_mod_cast C.scaleNum_pos d
  calc
    (C.scaleDen d : ℝ) * (canonicalScale C d m : ℝ) *
        Real.logb 2 (m : ℝ) ≤
      (C.scaleDen d : ℝ) * canonicalScaleReal C d m *
        Real.logb 2 (m : ℝ) := by
          gcongr
    _ = (m : ℝ) / Real.logb 2 (m : ℝ) := by
      rw [canonicalScaleReal]
      field_simp [hDne, hlogb.ne']
    _ ≤ (m : ℝ) := (div_le_iff₀ hlogb).2 (by nlinarith)
    _ ≤ (C.scaleNum d : ℝ) * (m : ℝ) := by
      nlinarith

/-- The selector whose domain remembers that its chosen CFP scale is at least
the prescribed population power. -/
def HigherDimensionalContext.scaleSelector {β η : ℝ}
    (C : HigherDimensionalContext β η) (exponent : ℝ) :
    BoundedCFPSelector C where
  Eligible := fun {d} A ↦ Nonempty
    {I : EligibleInput C A //
      I.scale = canonicalScale C d A.card ∧
        Real.rpow (A.card : ℝ) exponent ≤ (I.scale : ℝ)}
  input _ hA := (Classical.choice hA).1

/-- A strong-scale eligible input lies in the domain of `scaleSelector`. -/
theorem HigherDimensionalContext.scaleSelector_eligible_of_input
    {β η exponent : ℝ} {C : HigherDimensionalContext β η}
    {d : ℕ} {A : Finset (LatticePoint d)}
    (I : EligibleInput C A)
    (hcanonical : I.scale = canonicalScale C d A.card)
    (hscale : Real.rpow (A.card : ℝ) exponent ≤ (I.scale : ℝ)) :
    (C.scaleSelector exponent).Eligible A :=
  ⟨⟨I, hcanonical, hscale⟩⟩

/-- The scale selected at every point of a canonical run is literally the
rounded canonical scale.  Recording this in the selector's domain prevents
the existential eligibility proof from hiding the upper scale estimate
needed for the CFP core-loss calculation. -/
theorem HigherDimensionalContext.scaleSelector_input_scale
    {β η exponent : ℝ} {C : HigherDimensionalContext β η}
    {d : ℕ} {A : Finset (LatticePoint d)}
    (hA : (C.scaleSelector exponent).Eligible A) :
    ((C.scaleSelector exponent).input A hA).scale =
      canonicalScale C d A.card :=
  (Classical.choice hA).2.1

/-- Every input selected from `scaleSelector` satisfies its named exponent. -/
theorem HigherDimensionalContext.scaleSelector_usesScaleExponent
    {β η exponent : ℝ} (C : HigherDimensionalContext β η) :
    (C.scaleSelector exponent).UsesScaleExponent exponent := by
  intro d A hA
  exact (Classical.choice hA).2.2

/-- A selector built with a stronger exponent also satisfies every weaker
scale exponent, because all eligible finite sets are nonempty. -/
theorem HigherDimensionalContext.scaleSelector_usesScaleExponent_of_le
    {β η lower upper : ℝ} (C : HigherDimensionalContext β η)
    (h : lower ≤ upper) :
    (C.scaleSelector upper).UsesScaleExponent lower := by
  intro d A hA
  have hone : (1 : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast (C.scaleSelector upper).eligible_nonempty hA |>.card_pos
  calc
    Real.rpow (A.card : ℝ) lower ≤ Real.rpow (A.card : ℝ) upper :=
      Real.rpow_le_rpow_of_exponent_le hone h
    _ ≤ ((C.scaleSelector upper).input A hA).scale :=
      C.scaleSelector_usesScaleExponent A hA

/-- A single explicit threshold supplies both lower-scale estimates and the
upper CFP inequality. -/
theorem exists_canonicalScale_threshold
    {β η : ℝ} (C : HigherDimensionalContext β η) (d : ℕ)
    (hη0 : 0 < η) (hη1 : η < 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ m : ℕ, threshold ≤ m →
        (m : ℝ) ^ η ≤ (canonicalScale C d m : ℝ) ∧
        (m : ℝ) ^ (1 - ε) ≤ (canonicalScale C d m : ℝ) ∧
        (C.scaleDen d : ℝ) * (canonicalScale C d m : ℝ) *
            Real.logb 2 (m : ℝ) ≤
          (C.scaleNum d : ℝ) * (m : ℝ) := by
  have hη := eventually_rpow_le_canonicalScale C d hη0 hη1
  have hret := eventually_rpow_le_canonicalScale C d
    (sub_pos.mpr hε1) (sub_lt_self 1 hε0)
  have hupp := eventually_canonicalScale_upper C d
  obtain ⟨t, ht⟩ := eventually_atTop.1 (hη.and (hret.and hupp))
  refine ⟨max 2 t, le_max_left _ _, ?_⟩
  intro m hm
  exact ht m (le_trans (le_max_right _ _) hm)

/-- The canonical-scale threshold can be chosen uniformly over a bounded
range of ambient dimensions. -/
theorem exists_canonicalScale_threshold_boundedDimension
    {β η : ℝ} (C : HigherDimensionalContext β η) (R : ℕ)
    (hη0 : 0 < η) (hη1 : η < 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ d : ℕ, d ≤ R → ∀ m : ℕ, threshold ≤ m →
        (m : ℝ) ^ η ≤ (canonicalScale C d m : ℝ) ∧
        (m : ℝ) ^ (1 - ε) ≤ (canonicalScale C d m : ℝ) ∧
        (C.scaleDen d : ℝ) * (canonicalScale C d m : ℝ) *
            Real.logb 2 (m : ℝ) ≤
          (C.scaleNum d : ℝ) * (m : ℝ) := by
  have hex : ∀ d : ℕ, ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ m : ℕ, threshold ≤ m →
        (m : ℝ) ^ η ≤ (canonicalScale C d m : ℝ) ∧
        (m : ℝ) ^ (1 - ε) ≤ (canonicalScale C d m : ℝ) ∧
        (C.scaleDen d : ℝ) * (canonicalScale C d m : ℝ) *
            Real.logb 2 (m : ℝ) ≤
          (C.scaleNum d : ℝ) * (m : ℝ) :=
    fun d ↦ exists_canonicalScale_threshold C d hη0 hη1 hε0 hε1
  choose t ht using hex
  let threshold := 2 + ∑ d ∈ Finset.range (R + 1), t d
  refine ⟨threshold, by simp [threshold], ?_⟩
  intro d hd m hm
  have hdmem : d ∈ Finset.range (R + 1) := by simp; omega
  have hdt : t d ≤ ∑ i ∈ Finset.range (R + 1), t i := by
    exact Finset.single_le_sum (fun i hi ↦ Nat.zero_le (t i)) hdmem
  apply (ht d).2 m
  dsimp [threshold] at hm
  omega

/-- Beyond the uniform threshold, the canonical scale produces an eligible
CFP input in any supplied containing box and an eligibility proof for the
strong-scale selector. -/
theorem exists_threshold_canonicalEligibleInput
    {β η : ℝ} (C : HigherDimensionalContext β η) (d : ℕ)
    (hη0 : 0 < η) (hη1 : η < 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ (B : CFP.IntegerBox d) (A : Finset (LatticePoint d)),
        threshold ≤ A.card → A ⊆ B.carrier →
        (B.carrier.card : ℝ) ≤ Real.rpow (A.card : ℝ) β →
        ∃ I : EligibleInput C A,
          I.box = B ∧ I.scale = canonicalScale C d A.card ∧
          Real.rpow (A.card : ℝ) (1 - ε) ≤ (I.scale : ℝ) ∧
          (C.scaleSelector (1 - ε)).Eligible A := by
  obtain ⟨threshold, hthreshold, hscale⟩ :=
    exists_canonicalScale_threshold C d hη0 hη1 hε0 hε1
  refine ⟨threshold, hthreshold, ?_⟩
  intro B A hcard hsub hbox
  have hs := hscale A.card hcard
  let I : EligibleInput C A := {
    box := B
    scale := canonicalScale C d A.card
    nonempty := Finset.card_pos.mp
      (lt_of_lt_of_le (by omega : 0 < threshold) hcard)
    subset_box := hsub
    box_card_le := hbox
    scale_lower := hs.1
    scale_upper := hs.2.2 }
  refine ⟨I, rfl, rfl, hs.2.1, ?_⟩
  exact C.scaleSelector_eligible_of_input I rfl hs.2.1

/-- The initial normalized set admits the same canonical strong-scale input.
The context exponent may be larger than the exponent used to bound the
original box; this is the slack used by the replacement process. -/
theorem exists_threshold_normalizedCanonicalEligibleInput
    {β η β₀ : ℝ} (C : HigherDimensionalContext β η) (d : ℕ)
    (hη0 : 0 < η) (hη1 : η < 1) (hβ : β₀ ≤ β)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ (B : CFP.IntegerBox d) (A : Finset (LatticePoint d)),
        threshold ≤ A.card → A ⊆ B.carrier →
        (B.carrier.card : ℝ) ≤ Real.rpow (A.card : ℝ) β₀ →
        ∃ I : EligibleInput C (normalizeSet B A),
          I.box = normalizedBox B ∧
          I.scale = canonicalScale C d A.card ∧
          Real.rpow (A.card : ℝ) (1 - ε) ≤ (I.scale : ℝ) ∧
          (C.scaleSelector (1 - ε)).Eligible (normalizeSet B A) := by
  obtain ⟨threshold, hthreshold, hinput⟩ :=
    exists_threshold_canonicalEligibleInput C d hη0 hη1 hε0 hε1
  refine ⟨threshold, hthreshold, ?_⟩
  intro B A hcard hsub hbox
  have hmone : (1 : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast (le_trans (by omega : 1 ≤ threshold) hcard)
  have hpow : Real.rpow (A.card : ℝ) β₀ ≤
      Real.rpow (A.card : ℝ) β :=
    Real.rpow_le_rpow_of_exponent_le hmone hβ
  have hnormalizedBox : ((normalizedBox B).carrier.card : ℝ) ≤
      Real.rpow ((normalizeSet B A).card : ℝ) β := by
    simpa using hbox.trans hpow
  obtain ⟨I, hIbox, hIscale, hIstrong, hIeligible⟩ :=
    hinput (normalizedBox B) (normalizeSet B A)
      (by simpa using hcard) (normalizeSet_subset_normalized B hsub)
      hnormalizedBox
  refine ⟨I, hIbox, ?_, ?_, hIeligible⟩
  · simpa using hIscale
  · simpa using hIstrong

end

end Erdos186.PZ.Reduction
