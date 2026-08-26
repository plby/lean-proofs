import ErdosProblems.Erdos1038.CircleHaarOverlap
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Layer cake for the logarithmic circle kernel

This file gives the application-specific analytic bridge from the
nonnegative logarithmic deficit

`-log (sin (dist x c / 2))`

to the ball-overlap comparison on `AddCircle (2 * π)`.  Mathlib defines
`Real.log 0 = 0`; this changes the singular kernel at the single point
`x = c`, but that point has Haar measure zero.  Consequently the exact
lower-integral layer-cake formula is unaffected.
-/

open Metric Set MeasureTheory
open scoped ENNReal

namespace Erdos1038

noncomputable section

local notation "AngleCircle" => AddCircle (2 * Real.pi)

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The nonnegative logarithmic deficit with singular center `c`.
At `z = c` its value is the harmless Mathlib convention `0`. -/
def circleLogDeficitAt (c z : AngleCircle) : ℝ :=
  -Real.log (Real.sin (dist z c / 2))

/-- The logarithmic circle kernel centered at the origin. -/
def circleLogDeficit (z : AngleCircle) : ℝ :=
  circleLogDeficitAt 0 z

@[simp]
lemma circleLogDeficitAt_zero (z : AngleCircle) :
    circleLogDeficitAt 0 z = circleLogDeficit z := rfl

/-- Radius of the `t`-superlevel ball of the logarithmic deficit. -/
def circleLogLayerRadius (t : ℝ) : ℝ :=
  2 * Real.arcsin (Real.exp (-t))

/-- Every circular distance lies in the half-circle `[0, π]`. -/
lemma addCircle_dist_le_pi (c z : AngleCircle) :
    dist z c ≤ Real.pi := by
  rw [dist_eq_norm]
  have h := AddCircle.norm_le_half_period
    (2 * Real.pi) (x := z - c) (by positivity)
  rw [abs_of_pos Real.two_pi_pos] at h
  nlinarith

lemma circleLogDeficitAt_nonneg (c z : AngleCircle) :
    0 ≤ circleLogDeficitAt c z := by
  unfold circleLogDeficitAt
  apply neg_nonneg.mpr
  apply Real.log_nonpos
  · apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · have h := addCircle_dist_le_pi c z
      nlinarith [Real.pi_pos]
  · exact Real.sin_le_one _

lemma circleLogDeficit_nonneg (z : AngleCircle) :
    0 ≤ circleLogDeficit z :=
  circleLogDeficitAt_nonneg 0 z

lemma measurable_circleLogDeficitAt (c : AngleCircle) :
    Measurable (circleLogDeficitAt c) := by
  unfold circleLogDeficitAt
  fun_prop

lemma measurable_circleLogDeficit :
    Measurable circleLogDeficit :=
  measurable_circleLogDeficitAt 0

lemma circleLogLayerRadius_pos {t : ℝ} (_ht : 0 < t) :
    0 < circleLogLayerRadius t := by
  unfold circleLogLayerRadius
  have he : 0 < Real.exp (-t) := Real.exp_pos _
  have ha : 0 < Real.arcsin (Real.exp (-t)) :=
    Real.arcsin_pos.mpr he
  linarith

lemma circleLogLayerRadius_lt_pi {t : ℝ} (ht : 0 < t) :
    circleLogLayerRadius t < Real.pi := by
  unfold circleLogLayerRadius
  have he : Real.exp (-t) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have ha : Real.arcsin (Real.exp (-t)) < Real.pi / 2 :=
    Real.arcsin_lt_pi_div_two.mpr he
  linarith

lemma circleLogLayerRadius_nonneg (t : ℝ) :
    0 ≤ circleLogLayerRadius t := by
  unfold circleLogLayerRadius
  exact mul_nonneg zero_le_two
    (Real.arcsin_nonneg.mpr (Real.exp_pos _).le)

lemma circleLogLayerRadius_le_pi (t : ℝ) :
    circleLogLayerRadius t ≤ Real.pi := by
  unfold circleLogLayerRadius
  nlinarith [Real.arcsin_le_pi_div_two (Real.exp (-t))]

private lemma log_sin_lt_iff {a t : ℝ}
    (ha0 : 0 < a) (hapi : a ≤ Real.pi / 2) (ht : 0 < t) :
    t < -Real.log (Real.sin a) ↔
      a < Real.arcsin (Real.exp (-t)) := by
  have ha_pi : a < Real.pi := by linarith [Real.pi_pos]
  have hsin0 : 0 < Real.sin a :=
    Real.sin_pos_of_pos_of_lt_pi ha0 ha_pi
  have hexp0 : 0 < Real.exp (-t) := Real.exp_pos _
  have hexp1 : Real.exp (-t) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have ha_mem : a ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], hapi⟩
  have harcsin_mem : Real.arcsin (Real.exp (-t)) ∈
      Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨Real.neg_pi_div_two_le_arcsin _,
      Real.arcsin_le_pi_div_two _⟩
  constructor
  · intro h
    have hlog : Real.log (Real.sin a) < -t := by linarith
    have hsinexp : Real.sin a < Real.exp (-t) := by
      rw [← Real.exp_log hsin0]
      exact Real.exp_lt_exp.mpr hlog
    have hsin : Real.sin a <
        Real.sin (Real.arcsin (Real.exp (-t))) := by
      rwa [Real.sin_arcsin (by linarith) hexp1.le]
    exact Real.strictMonoOn_sin.lt_iff_lt ha_mem harcsin_mem |>.mp hsin
  · intro h
    have hsin : Real.sin a <
        Real.sin (Real.arcsin (Real.exp (-t))) :=
      Real.strictMonoOn_sin ha_mem harcsin_mem h
    rw [Real.sin_arcsin (by linarith) hexp1.le] at hsin
    have hlog : Real.log (Real.sin a) < -t := by
      have hmono := Real.strictMonoOn_log hsin0 hexp0 hsin
      rwa [Real.log_exp] at hmono
    linarith

/-- The positive superlevel set of the logarithmic deficit is a punctured
open ball.  Its Haar measure therefore agrees with that of the
corresponding closed ball. -/
theorem circleLogDeficitAt_superlevel {c z : AngleCircle} {t : ℝ}
    (ht : 0 < t) :
    t < circleLogDeficitAt c z ↔
      0 < dist z c ∧ dist z c < circleLogLayerRadius t := by
  have hd0 : 0 ≤ dist z c := dist_nonneg
  have hdpi := addCircle_dist_le_pi c z
  rcases hd0.eq_or_lt with hd | hd
  · have hz : z = c := dist_eq_zero.mp hd.symm
    subst z
    constructor
    · intro h
      have hneg : t < 0 := by
        simpa [circleLogDeficitAt] using! h
      linarith
    · rintro ⟨h, _⟩
      exfalso
      have hzero : (0 : ℝ) < 0 := by
        simpa only [dist_self] using! h
      exact lt_irrefl 0 hzero
  · unfold circleLogDeficitAt circleLogLayerRadius
    have hhalf0 : 0 < dist z c / 2 := by positivity
    have hhalfpi : dist z c / 2 ≤ Real.pi / 2 := by linarith
    rw [log_sin_lt_iff hhalf0 hhalfpi ht]
    constructor
    · intro h
      exact ⟨hd, by linarith⟩
    · intro h
      linarith

/-- Closed-ball form of the weak positive superlevel set.  This version
matches the `meas_le` form of Mathlib's layer-cake theorem exactly. -/
theorem circleLogDeficitAt_superlevel_set (c : AngleCircle)
    (t : ℝ) (ht : 0 < t) :
    {z : AngleCircle | t ≤ circleLogDeficitAt c z} =
      closedBall c (circleLogLayerRadius t) \ {c} := by
  ext z
  simp only [mem_ofPred_eq, mem_sdiff, mem_closedBall,
    mem_singleton_iff]
  have hd0 : 0 ≤ dist z c := dist_nonneg
  have hdpi : dist z c ≤ Real.pi := addCircle_dist_le_pi c z
  have hx : dist z c / 2 ∈
      Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hy : Real.exp (-t) ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · linarith [Real.exp_pos (-t)]
    · exact Real.exp_le_one_iff.mpr (by linarith)
  constructor
  · intro h
    have hzc : z ≠ c := by
      intro hzc
      subst z
      simp [circleLogDeficitAt] at h
      linarith
    have hdpos : 0 < dist z c := dist_pos.mpr hzc
    have hspos : 0 < Real.sin (dist z c / 2) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith [Real.pi_pos]
    have hlog :
        Real.log (Real.sin (dist z c / 2)) ≤ -t := by
      unfold circleLogDeficitAt at h
      linarith
    have hsin :
        Real.sin (dist z c / 2) ≤ Real.exp (-t) :=
      (Real.log_le_iff_le_exp hspos).mp hlog
    have hhalf :
        dist z c / 2 ≤ Real.arcsin (Real.exp (-t)) :=
      (Real.le_arcsin_iff_sin_le hx hy).2 hsin
    exact ⟨by
      change dist z c ≤ 2 * Real.arcsin (Real.exp (-t))
      linarith, hzc⟩
  · rintro ⟨hball, hzc⟩
    have hdpos : 0 < dist z c := dist_pos.mpr hzc
    have hspos : 0 < Real.sin (dist z c / 2) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith [Real.pi_pos]
    have hhalf :
        dist z c / 2 ≤ Real.arcsin (Real.exp (-t)) := by
      unfold circleLogLayerRadius at hball
      linarith
    have hsin :
        Real.sin (dist z c / 2) ≤ Real.exp (-t) :=
      (Real.le_arcsin_iff_sin_le hx hy).1 hhalf
    have hlog :
        Real.log (Real.sin (dist z c / 2)) ≤ -t :=
      (Real.log_le_iff_le_exp hspos).2 hsin
    unfold circleLogDeficitAt
    linarith

/-- Haar volume of a singleton on the additive circle is zero. -/
lemma volume_angleCircle_singleton_zero (c : AngleCircle) :
    volume ({c} : Set AngleCircle) = 0 := by
  calc
    volume ({c} : Set AngleCircle) = volume (closedBall c 0) := by
      rw [closedBall_zero]
    _ = ENNReal.ofReal (min (2 * Real.pi) (2 * 0)) :=
      AddCircle.volume_closedBall (2 * Real.pi) 0
    _ = 0 := by simp

/-- Exact layer-cake/Tonelli representation of the logarithmic deficit
integrated over one circular arc. -/
theorem lintegral_circleLogDeficitAt_closedBall
    {c x : AngleCircle} {s : ℝ} :
    (∫⁻ z in closedBall x s,
        ENNReal.ofReal (circleLogDeficitAt c z)) =
      ∫⁻ t in Ioi (0 : ℝ),
        volume
          (closedBall c (circleLogLayerRadius t) ∩ closedBall x s) := by
  have hlayer := lintegral_eq_lintegral_meas_lt
    ((volume : Measure AngleCircle).restrict (closedBall x s))
    (Filter.Eventually.of_forall fun z =>
      circleLogDeficitAt_nonneg c z)
    (measurable_circleLogDeficitAt c).aemeasurable
  rw [hlayer]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have hlevel :
      {z : AngleCircle | t < circleLogDeficitAt c z} =
        ball c (circleLogLayerRadius t) \ {c} := by
    ext z
    rw [mem_ofPred_eq, circleLogDeficitAt_superlevel ht]
    simp only [mem_sdiff, mem_ball, mem_singleton_iff]
    constructor
    · rintro ⟨hd0, hdr⟩
      exact ⟨hdr, dist_ne_zero.mp hd0.ne'⟩
    · rintro ⟨hdr, hne⟩
      exact ⟨dist_pos.mpr hne, hdr⟩
  change
    (volume.restrict (closedBall x s))
        {z : AngleCircle | t < circleLogDeficitAt c z} = _
  rw [Measure.restrict_apply
    (measurableSet_lt measurable_const
      (measurable_circleLogDeficitAt c)), hlevel]
  have hcnull := volume_angleCircle_singleton_zero c
  apply measure_congr
  exact ae_eq_set_inter
    ((sdiff_null_ae_eq_self hcnull).trans
      AddCircle.closedBall_ae_eq_ball.symm)
    (ae_eq_refl _)

/-! ## A second layer cake for the arc-overlap profile -/

/-- Radius of a positive superlevel of `circleArcOverlap r s`.
The clamps make the radius lie in `[0, π]` for every real level; on
positive levels only the geometrically active branch matters. -/
def circleArcOverlapLayerRadius (r s level : ℝ) : ℝ :=
  if level < 2 * (r + s - Real.pi) then Real.pi
  else if level < 2 * r ∧ level < 2 * s then
    max 0 (min Real.pi (r + s - level))
  else 0

lemma circleArcOverlapLayerRadius_nonneg (r s level : ℝ) :
    0 ≤ circleArcOverlapLayerRadius r s level := by
  unfold circleArcOverlapLayerRadius
  split_ifs <;> simp [Real.pi_pos.le]

lemma circleArcOverlapLayerRadius_le_pi (r s level : ℝ) :
    circleArcOverlapLayerRadius r s level ≤ Real.pi := by
  unfold circleArcOverlapLayerRadius
  split_ifs <;> simp [Real.pi_pos.le]

private lemma level_lt_circleArcOverlap_iff {r s d level : ℝ}
    (hlevel : 0 < level) :
    level < circleArcOverlap r s d ↔
      level < 2 * (r + s - Real.pi) ∨
        (level < 2 * r ∧ level < 2 * s ∧
          d < r + s - level) := by
  unfold circleArcOverlap lineArcOverlap
  rw [lt_max_iff, lt_max_iff, lt_min_iff, lt_min_iff]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · linarith
    · exact Or.inr ⟨h.1, h.2.1, by linarith [h.2.2]⟩
  · rintro (h | ⟨hr, hs, hd⟩)
    · exact Or.inl h
    · exact Or.inr <| Or.inr ⟨hr, hs, by linarith⟩

lemma measurable_circleArcOverlap_dist (r s : ℝ) (c : AngleCircle) :
    Measurable fun z : AngleCircle => circleArcOverlap r s (dist z c) := by
  unfold circleArcOverlap lineArcOverlap
  fun_prop

private theorem circleArcOverlap_superlevel_ae_closedBall
    {r s level : ℝ} (c : AngleCircle) (hlevel : 0 < level) :
    {z : AngleCircle |
        level < circleArcOverlap r s (dist z c)} =ᵐ[volume]
      closedBall c (circleArcOverlapLayerRadius r s level) := by
  by_cases hfloor : level < 2 * (r + s - Real.pi)
  · have hleft :
        {z : AngleCircle |
            level < circleArcOverlap r s (dist z c)} = univ := by
      apply eq_univ_iff_forall.mpr
      intro z
      exact (level_lt_circleArcOverlap_iff hlevel).2 (Or.inl hfloor)
    have hradius :
        circleArcOverlapLayerRadius r s level = Real.pi := by
      simp [circleArcOverlapLayerRadius, hfloor]
    have hball : closedBall c Real.pi = univ := by
      apply AddCircle.closedBall_eq_univ_of_half_period_le
        (2 * Real.pi) (by positivity) c
      rw [abs_of_pos Real.two_pi_pos]
      linarith
    rw [hleft, hradius, hball]
    rfl
  · by_cases hcaps : level < 2 * r ∧ level < 2 * s
    · have hrad0 : 0 < r + s - level := by
        nlinarith
      have hradpi : r + s - level ≤ Real.pi := by
        have hfloor' : 2 * (r + s - Real.pi) ≤ level :=
          not_lt.mp hfloor
        linarith
      have hradius :
          circleArcOverlapLayerRadius r s level = r + s - level := by
        simp [circleArcOverlapLayerRadius, hfloor, hcaps,
          max_eq_right hrad0.le, min_eq_right hradpi]
      have hleft :
          {z : AngleCircle |
              level < circleArcOverlap r s (dist z c)} =
            ball c (r + s - level) := by
        ext z
        rw [mem_ofPred_eq, level_lt_circleArcOverlap_iff hlevel,
          mem_ball]
        simp [hfloor, hcaps]
      rw [hleft, hradius]
      exact AddCircle.closedBall_ae_eq_ball.symm
    · have hradius :
          circleArcOverlapLayerRadius r s level = 0 := by
        simp [circleArcOverlapLayerRadius, hfloor, hcaps]
      have hleft :
          {z : AngleCircle |
              level < circleArcOverlap r s (dist z c)} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        rw [mem_ofPred_eq, level_lt_circleArcOverlap_iff hlevel] at hz
        rcases hz with hfloor' | hactive
        · exact hfloor hfloor'
        · exact hcaps ⟨hactive.1, hactive.2.1⟩
      rw [hleft, hradius]
      simpa using!
        (AddCircle.closedBall_ae_eq_ball
          (x := c) (ε := (0 : ℝ))).symm

/-- Integral of one circular-overlap profile over a fixed arc. -/
def circleArcOverlapPotential (r s q d : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in closedBall (0 : AngleCircle) q,
    ENNReal.ofReal
      (circleArcOverlap r s (dist z (d : AngleCircle)))

/-- Layer-cake representation of the circular-overlap profile. -/
theorem circleArcOverlapPotential_eq_layerCake
    (r s q d : ℝ) :
    circleArcOverlapPotential r s q d =
      ∫⁻ level in Ioi (0 : ℝ),
        volume
          (closedBall (0 : AngleCircle) q ∩
            closedBall (d : AngleCircle)
              (circleArcOverlapLayerRadius r s level)) := by
  unfold circleArcOverlapPotential
  have hlayer := lintegral_eq_lintegral_meas_lt
    ((volume : Measure AngleCircle).restrict
      (closedBall (0 : AngleCircle) q))
    (Filter.Eventually.of_forall fun z =>
      circleArcOverlap_nonneg r s (dist z (d : AngleCircle)))
    (measurable_circleArcOverlap_dist
      r s (d : AngleCircle)).aemeasurable
  rw [hlayer]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro level hlevel
  change
    (volume.restrict (closedBall (0 : AngleCircle) q))
        {z : AngleCircle |
          level < circleArcOverlap r s (dist z (d : AngleCircle))} = _
  rw [Measure.restrict_apply
    (measurableSet_lt measurable_const
      (measurable_circleArcOverlap_dist r s (d : AngleCircle)))]
  calc
    volume
        ({z : AngleCircle |
            level < circleArcOverlap r s (dist z (d : AngleCircle))} ∩
          closedBall (0 : AngleCircle) q) =
        volume
          (closedBall (d : AngleCircle)
              (circleArcOverlapLayerRadius r s level) ∩
            closedBall (0 : AngleCircle) q) := by
      apply measure_congr
      exact ae_eq_set_inter
        (circleArcOverlap_superlevel_ae_closedBall
          (d : AngleCircle) hlevel)
        (ae_eq_refl _)
    _ = volume
        (closedBall (0 : AngleCircle) q ∩
          closedBall (d : AngleCircle)
            (circleArcOverlapLayerRadius r s level)) := by
      rw [inter_comm]

/-- The integral of a circular-overlap profile over a fixed arc is
antitone in the distance between their centers. -/
theorem circleArcOverlapPotential_antitoneOn
    {r s q : ℝ} (hq0 : 0 ≤ q) (hqpi : q ≤ Real.pi) :
    AntitoneOn (circleArcOverlapPotential r s q)
      (Icc (0 : ℝ) Real.pi) := by
  apply antitoneOn_of_layerCake_ballOverlap
    (Measure.dirac ())
    ((volume : Measure ℝ).restrict (Ioi 0))
    (fun _ : Unit => q)
    (circleArcOverlapLayerRadius r s)
    (fun _ => hq0) (fun _ => hqpi)
    (circleArcOverlapLayerRadius_nonneg r s)
    (circleArcOverlapLayerRadius_le_pi r s)
  intro d _hd
  rw [circleArcOverlapPotential_eq_layerCake]
  simp only [lintegral_dirac]

/-- The logarithmic potential of a radius-`s` arc whose center is
represented by `d`. -/
def circleLogArcPotential (s d : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in closedBall (d : AngleCircle) s,
    ENNReal.ofReal (circleLogDeficit z)

/-- The potential is exactly the nonnegative mixture of the Haar
overlaps of the arc with the kernel's superlevel balls. -/
theorem circleLogArcPotential_eq_layerCake (s d : ℝ) :
    circleLogArcPotential s d =
      ∫⁻ t in Ioi (0 : ℝ),
        volume
          (closedBall (0 : AngleCircle) (circleLogLayerRadius t) ∩
            closedBall (d : AngleCircle) s) := by
  exact lintegral_circleLogDeficitAt_closedBall

/-- The logarithmic potential of a fixed-radius arc is antitone in the
circular center distance on the half-circle.  This is the direct
instantiation of `antitoneOn_of_layerCake_ballOverlap` with the kernel
superlevel balls and one Dirac-indexed fixed arc layer. -/
theorem circleLogArcPotential_antitoneOn {s : ℝ}
    (hs0 : 0 ≤ s) (hspi : s ≤ Real.pi) :
    AntitoneOn (circleLogArcPotential s) (Icc (0 : ℝ) Real.pi) := by
  apply antitoneOn_of_layerCake_ballOverlap
    ((volume : Measure ℝ).restrict (Ioi 0)) (Measure.dirac ())
    circleLogLayerRadius (fun _ : Unit => s)
    circleLogLayerRadius_nonneg circleLogLayerRadius_le_pi
    (fun _ => hs0) (fun _ => hspi)
  intro d _hd
  unfold circleLogArcPotential circleLogDeficit
  rw [lintegral_circleLogDeficitAt_closedBall]
  simp only [lintegral_dirac]

/-- Nonnegative logarithmic cross-energy of two arcs, with radii `r,s`
and represented center separation `d`. -/
def circleLogTwoArcEnergy (r s d : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in closedBall (0 : AngleCircle) r,
    ∫⁻ y in closedBall (d : AngleCircle) s,
      ENNReal.ofReal (circleLogDeficitAt x y)

/-- Apply the logarithmic layer cake to the inner variable of the
two-arc energy. -/
theorem circleLogTwoArcEnergy_eq_iteratedLayerCake (r s d : ℝ) :
    circleLogTwoArcEnergy r s d =
      ∫⁻ x in closedBall (0 : AngleCircle) r,
        ∫⁻ t in Ioi (0 : ℝ),
          volume
            (closedBall x (circleLogLayerRadius t) ∩
              closedBall (d : AngleCircle) s) := by
  unfold circleLogTwoArcEnergy
  apply lintegral_congr
  intro x
  exact lintegral_circleLogDeficitAt_closedBall

lemma measurable_circleLogOverlapLayer (s : ℝ) (d : AngleCircle)
    (hs0 : 0 ≤ s) (hspi : s ≤ Real.pi) :
    Measurable fun p : AngleCircle × ℝ =>
      volume
        (closedBall p.1 (circleLogLayerRadius p.2) ∩
          closedBall d s) := by
  have hfun : (fun p : AngleCircle × ℝ =>
      volume
        (closedBall p.1 (circleLogLayerRadius p.2) ∩
          closedBall d s)) =
      fun p => ENNReal.ofReal
        (circleArcOverlap (circleLogLayerRadius p.2) s
          (dist p.1 d)) := by
    funext p
    exact volume_inter_addCircle_closedBalls
      (circleLogLayerRadius_nonneg p.2)
      (circleLogLayerRadius_le_pi p.2) hs0 hspi
  rw [hfun]
  apply ENNReal.measurable_ofReal.comp
  unfold circleArcOverlap lineArcOverlap circleLogLayerRadius
  fun_prop

/-- Tonelli form of the two-arc layer cake.  All dependence on the
logarithmic kernel is now isolated in `circleLogLayerRadius`; the
remaining integrand is a Haar overlap of ordinary arcs. -/
theorem circleLogTwoArcEnergy_eq_swappedLayerCake
    (r s d : ℝ) (hs0 : 0 ≤ s) (hspi : s ≤ Real.pi) :
    circleLogTwoArcEnergy r s d =
      ∫⁻ t in Ioi (0 : ℝ),
        ∫⁻ x in closedBall (0 : AngleCircle) r,
          volume
            (closedBall x (circleLogLayerRadius t) ∩
              closedBall (d : AngleCircle) s) := by
  rw [circleLogTwoArcEnergy_eq_iteratedLayerCake]
  apply lintegral_lintegral_swap
  exact (measurable_circleLogOverlapLayer
    s (d : AngleCircle) hs0 hspi).aemeasurable

/-- After the Tonelli swap, the two-arc logarithmic energy is a
positive mixture of the circular-overlap potentials. -/
theorem circleLogTwoArcEnergy_eq_overlapPotentials
    (r s d : ℝ) (hs0 : 0 ≤ s) (hspi : s ≤ Real.pi) :
    circleLogTwoArcEnergy r s d =
      ∫⁻ t in Ioi (0 : ℝ),
        circleArcOverlapPotential
          (circleLogLayerRadius t) s r d := by
  rw [circleLogTwoArcEnergy_eq_swappedLayerCake r s d hs0 hspi]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  unfold circleArcOverlapPotential
  apply setLIntegral_congr_fun measurableSet_closedBall
  intro x _hx
  exact volume_inter_addCircle_closedBalls
    (circleLogLayerRadius_nonneg t)
    (circleLogLayerRadius_le_pi t) hs0 hspi

/-- The logarithmic cross-energy of two fixed-radius arcs is antitone
in their center separation on the half-circle. -/
theorem circleLogTwoArcEnergy_antitoneOn {r s : ℝ}
    (hr0 : 0 ≤ r) (hrpi : r ≤ Real.pi)
    (hs0 : 0 ≤ s) (hspi : s ≤ Real.pi) :
    AntitoneOn (circleLogTwoArcEnergy r s)
      (Icc (0 : ℝ) Real.pi) := by
  intro d hd e he hde
  rw [circleLogTwoArcEnergy_eq_overlapPotentials r s e hs0 hspi,
    circleLogTwoArcEnergy_eq_overlapPotentials r s d hs0 hspi]
  apply setLIntegral_mono' measurableSet_Ioi
  intro t _ht
  exact
    (circleArcOverlapPotential_antitoneOn
      (r := circleLogLayerRadius t) (s := s) (q := r)
      hr0 hrpi) hd he hde

end

end Erdos1038
