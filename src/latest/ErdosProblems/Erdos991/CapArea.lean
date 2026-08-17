import ErdosProblems.Erdos988

open Filter Finset MeasureTheory Metric Set
open scoped BigOperators ENNReal NNReal Pointwise Topology

namespace Erdos991

noncomputable section

abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Euclidean square-radius in the coordinate model of `ℝ³`. -/
def coordNormSq (x : Fin 3 → ℝ) : ℝ := ∑ i, x i ^ 2

lemma norm_toLp_sq (x : Fin 3 → ℝ) :
    ‖WithLp.toLp 2 x‖ ^ 2 = coordNormSq x := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [coordNormSq, Real.norm_eq_abs, sq_abs]

lemma exists_orthonormalBasis_zero_eq (u : E3) (hu : ‖u‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ E3, b 0 = u := by
  let v : Fin 3 → E3 := fun _ ↦ u
  have hv : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict v) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    simpa [v] using hu
  rcases Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℝ) (E := E3) (ι := Fin 3) (by simp) hv with ⟨b, hb⟩
  exact ⟨b, hb 0 (by simp)⟩

lemma volume_E2_ball_sqrt {q : ℝ} (hq : 0 ≤ q) :
    volume (Metric.ball (0 : E2) (Real.sqrt q)) =
      ENNReal.ofReal (Real.pi * q) := by
  rw [InnerProductSpace.volume_ball_of_dim_even (k := 1) (by simp)]
  simp only [Nat.factorial_one, Nat.cast_one, div_one, pow_one]
  rw [show Module.finrank ℝ E2 = 2 by simp, pow_two,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg q),
    Real.mul_self_sqrt hq, ← ENNReal.ofReal_mul hq]
  congr 1
  ring

lemma volume_E2_closedBall_sqrt {q : ℝ} (hq : 0 ≤ q) :
    volume (Metric.closedBall (0 : E2) (Real.sqrt q)) =
      ENNReal.ofReal (Real.pi * q) := by
  rw [InnerProductSpace.volume_closedBall_of_dim_even (k := 1) (by simp)]
  simp only [Nat.factorial_one, Nat.cast_one, div_one, pow_one]
  rw [show Module.finrank ℝ E2 = 2 by simp, pow_two,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg q),
    Real.mul_self_sqrt hq, ← ENNReal.ofReal_mul hq]
  congr 1
  ring

/-- Cross-sectional area of the positive-threshold radial cone. -/
def coneSectionArea (t s : ℝ) : ℝ :=
  if s ∈ Set.Ico 0 t then Real.pi * (s ^ 2 * (1 - t ^ 2) / t ^ 2)
  else if s ∈ Set.Ico t 1 then Real.pi * (1 - s ^ 2)
  else 0

lemma coneSectionArea_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (s : ℝ) :
    0 ≤ coneSectionArea t s := by
  unfold coneSectionArea
  split_ifs with hs hs
  · have ht_sq : t ^ 2 ≤ 1 := by nlinarith
    positivity
  · have hs1 : s ≤ 1 := hs.2.le
    have hs0 : 0 ≤ s := ht0.trans hs.1
    exact mul_nonneg Real.pi_pos.le (by nlinarith)
  · positivity

lemma coneSectionArea_integrable {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Integrable (coneSectionArea t) := by
  let f : ℝ → ℝ := fun s ↦ Real.pi * (s ^ 2 * (1 - t ^ 2) / t ^ 2)
  let g : ℝ → ℝ := fun s ↦ Real.pi * (1 - s ^ 2)
  have hf : IntegrableOn f (Set.Ico 0 t) :=
    ((continuous_const.mul
      ((continuous_id.pow 2).mul continuous_const |>.div_const _)).integrableOn_Icc
      |>.mono_set Set.Ico_subset_Icc_self)
  have hg : IntegrableOn g (Set.Ico t 1) :=
    ((continuous_const.mul (continuous_const.sub (continuous_id.pow 2))).integrableOn_Icc
      |>.mono_set Set.Ico_subset_Icc_self)
  have hfind : Integrable ((Set.Ico 0 t).indicator f) := hf.integrable_indicator measurableSet_Ico
  have hgind : Integrable ((Set.Ico t 1).indicator g) := hg.integrable_indicator measurableSet_Ico
  apply (hfind.add hgind).congr
  filter_upwards [] with s
  simp only [coneSectionArea, Set.indicator, Set.mem_Ico]
  by_cases hst : 0 ≤ s ∧ s < t
  · have hnot : ¬ (t ≤ s ∧ s < 1) := fun h ↦ (not_lt_of_ge h.1) hst.2
    simp [hst, hnot, f, g]
  · by_cases hsu : t ≤ s ∧ s < 1
    · simp [hst, hsu, f, g]
    · simp [hst, hsu, f, g]

lemma integral_coneSectionArea {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∫ s : ℝ, coneSectionArea t s = 2 * Real.pi * (1 - t) / 3 := by
  let f : ℝ → ℝ := fun s ↦ Real.pi * (s ^ 2 * (1 - t ^ 2) / t ^ 2)
  let g : ℝ → ℝ := fun s ↦ Real.pi * (1 - s ^ 2)
  have hf : IntegrableOn f (Set.Ico 0 t) :=
    ((continuous_const.mul
      ((continuous_id.pow 2).mul continuous_const |>.div_const _)).integrableOn_Icc
      |>.mono_set Set.Ico_subset_Icc_self)
  have hg : IntegrableOn g (Set.Ico t 1) :=
    ((continuous_const.mul (continuous_const.sub (continuous_id.pow 2))).integrableOn_Icc
      |>.mono_set Set.Ico_subset_Icc_self)
  have hfun : coneSectionArea t =
      (Set.Ico 0 t).indicator f + (Set.Ico t 1).indicator g := by
    funext s
    simp only [coneSectionArea, Set.indicator, Set.mem_Ico, Pi.add_apply]
    by_cases hst : 0 ≤ s ∧ s < t
    · have hnot : ¬ (t ≤ s ∧ s < 1) := fun h ↦ (not_lt_of_ge h.1) hst.2
      simp [hst, hnot, f, g]
    · by_cases hsu : t ≤ s ∧ s < 1
      · simp [hst, hsu, f, g]
      · simp [hst, hsu, f, g]
  rw [hfun]
  simp only [Pi.add_apply]
  rw [integral_add (hf.integrable_indicator measurableSet_Ico)
    (hg.integrable_indicator measurableSet_Ico),
    integral_indicator measurableSet_Ico, integral_indicator measurableSet_Ico,
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht0.le,
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht1]
  have hpow0t : ∫ s in (0 : ℝ)..t, s ^ 2 = t ^ 3 / 3 := by
    rw [integral_pow]
    ring
  have hpowt1 : ∫ s in t..(1 : ℝ), s ^ 2 = (1 - t ^ 3) / 3 := by
    rw [integral_pow]
    ring
  have hsub : ∫ s in t..(1 : ℝ), 1 - s ^ 2 =
      (1 - t) - (1 - t ^ 3) / 3 := by
    calc
      _ = (∫ _s : ℝ in t..1, (1 : ℝ)) - ∫ s : ℝ in t..1, s ^ 2 := by
        exact intervalIntegral.integral_sub
          (f := fun _ : ℝ ↦ (1 : ℝ)) (g := fun s : ℝ ↦ s ^ 2)
          (continuous_const.intervalIntegrable _ _)
          ((continuous_id.pow 2).intervalIntegrable _ _)
      _ = _ := by rw [intervalIntegral.integral_const, hpowt1]; ring
  dsimp only [f, g]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_mul_const,
    hpow0t,
    hsub]
  field_simp [ht0.ne']
  ring

/-- The Euclidean norm after splitting off one coordinate. -/
def splitNorm (p : ℝ × (Fin 2 → ℝ)) : ℝ :=
  Real.sqrt (p.1 ^ 2 + ‖WithLp.toLp 2 p.2‖ ^ 2)

/-- The unit radial cone whose angular part has first coordinate at least `t`. -/
def coordinateCone (t : ℝ) : Set (ℝ × (Fin 2 → ℝ)) :=
  {p | 0 < splitNorm p ∧ splitNorm p < 1 ∧ t * splitNorm p ≤ p.1}

def coordinateBoundary (t : ℝ) : Set (ℝ × (Fin 2 → ℝ)) :=
  {p | 0 < splitNorm p ∧ splitNorm p < 1 ∧ p.1 = t * splitNorm p}

lemma measurableSet_coordinateCone (t : ℝ) : MeasurableSet (coordinateCone t) := by
  have hcont : Continuous splitNorm := by
    unfold splitNorm
    fun_prop
  change MeasurableSet
    ({p | 0 < splitNorm p} ∩ ({p | splitNorm p < 1} ∩
      {p | t * splitNorm p ≤ p.1}))
  exact (isOpen_lt continuous_const hcont).measurableSet.inter
    ((isOpen_lt hcont continuous_const).measurableSet.inter
      (isClosed_le (continuous_const.mul hcont) continuous_fst).measurableSet)

lemma splitNorm_sq (p : ℝ × (Fin 2 → ℝ)) :
    splitNorm p ^ 2 = p.1 ^ 2 + ‖WithLp.toLp 2 p.2‖ ^ 2 := by
  rw [splitNorm, Real.sq_sqrt]
  positivity

lemma measurableSet_coordinateBoundary (t : ℝ) :
    MeasurableSet (coordinateBoundary t) := by
  have hc : Continuous splitNorm := by
    unfold splitNorm
    fun_prop
  change MeasurableSet
    ({p | 0 < splitNorm p} ∩
      ({p | splitNorm p < 1} ∩ {p | p.1 = t * splitNorm p}))
  exact (isOpen_lt continuous_const hc).measurableSet.inter
    ((isOpen_lt hc continuous_const).measurableSet.inter
      (isClosed_eq continuous_fst (continuous_const.mul hc)).measurableSet)

lemma coordinateBoundary_section_null {t s : ℝ} (ht : t ≠ 0) :
    volume ((Prod.mk s) ⁻¹' coordinateBoundary t) = 0 := by
  let q : ℝ := s ^ 2 / t ^ 2 - s ^ 2
  let circle : Set (Fin 2 → ℝ) :=
    (WithLp.toLp 2) ⁻¹' Metric.sphere (0 : E2) (Real.sqrt q)
  have hsubset : (Prod.mk s) ⁻¹' coordinateBoundary t ⊆ circle := by
    intro z hz
    change 0 < splitNorm (s, z) ∧ splitNorm (s, z) < 1 ∧
      s = t * splitNorm (s, z) at hz
    have hnormSq := splitNorm_sq (s, z)
    have hqeq : ‖WithLp.toLp 2 z‖ ^ 2 = q := by
      dsimp only [q]
      field_simp [ht]
      nlinarith [congrArg (fun x : ℝ ↦ x ^ 2) hz.2.2]
    have hq0 : 0 ≤ q := by rw [← hqeq]; positivity
    change dist (WithLp.toLp 2 z) 0 = Real.sqrt q
    rw [dist_zero_right]
    exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1 (by
      rw [Real.sq_sqrt hq0, hqeq])
  have hcircle : volume circle = 0 := by
    dsimp only [circle]
    rw [(PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
      Metric.isClosed_sphere.measurableSet.nullMeasurableSet]
    exact Measure.addHaar_sphere volume 0 (Real.sqrt q)
  exact measure_mono_null hsubset hcircle

lemma volume_coordinateBoundary (t : ℝ) :
    volume (coordinateBoundary t) = 0 := by
  rw [show (volume : Measure (ℝ × (Fin 2 → ℝ))) =
      (volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ)) by rfl]
  apply Measure.measure_prod_null_of_ae_null (measurableSet_coordinateBoundary t)
  rcases eq_or_ne t 0 with rfl | ht
  · filter_upwards [(volume : Measure ℝ).ae_ne 0] with s hs
    change volume ((Prod.mk s) ⁻¹' coordinateBoundary 0) = 0
    have hempty : (Prod.mk s) ⁻¹' coordinateBoundary 0 = ∅ := by
      ext z
      simp only [Set.mem_preimage, coordinateBoundary, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false]
      constructor
      · intro hz
        exact hs (by simpa using hz.2.2)
      · exact False.elim
    rw [hempty, measure_empty]
  · filter_upwards [] with s
    change volume ((Prod.mk s) ⁻¹' coordinateBoundary t) = 0
    exact coordinateBoundary_section_null ht

private lemma small_height_iff {t s r : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) (hs0 : 0 < s) (hst : s < t) (hr : 0 ≤ r) :
    (0 < Real.sqrt (s ^ 2 + r ^ 2) ∧
      Real.sqrt (s ^ 2 + r ^ 2) < 1 ∧
      t * Real.sqrt (s ^ 2 + r ^ 2) ≤ s) ↔
      r ≤ Real.sqrt (s ^ 2 * (1 - t ^ 2) / t ^ 2) := by
  have ht_sq_pos : 0 < t ^ 2 := sq_pos_of_pos ht0
  have ht_sq : t ^ 2 ≤ 1 := by nlinarith
  have hq : 0 ≤ s ^ 2 * (1 - t ^ 2) / t ^ 2 := by positivity
  have hsum : 0 ≤ s ^ 2 + r ^ 2 := by positivity
  let R := Real.sqrt (s ^ 2 + r ^ 2)
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = s ^ 2 + r ^ 2 := Real.sq_sqrt hsum
  have hqiff : r ^ 2 ≤ s ^ 2 * (1 - t ^ 2) / t ^ 2 ↔
      t ^ 2 * (s ^ 2 + r ^ 2) ≤ s ^ 2 := by
    rw [le_div_iff₀ ht_sq_pos]
    constructor <;> intro h <;> nlinarith
  constructor
  · rintro ⟨hRpos, hRone, hcap⟩
    apply (sq_le_sq₀ hr (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hq, hqiff]
    have hsquare : (t * R) ^ 2 ≤ s ^ 2 :=
      (sq_le_sq₀ (mul_nonneg ht0.le hR0) hs0.le).mpr hcap
    dsimp only [R] at hsquare hR2
    nlinarith
  · intro hball
    have hrsq : r ^ 2 ≤ s ^ 2 * (1 - t ^ 2) / t ^ 2 := by
      rw [← Real.sq_sqrt hq]
      exact (sq_le_sq₀ hr (Real.sqrt_nonneg _)).mpr hball
    have hcore : t ^ 2 * (s ^ 2 + r ^ 2) ≤ s ^ 2 := hqiff.mp hrsq
    have hcap : t * R ≤ s := by
      apply (sq_le_sq₀ (mul_nonneg ht0.le hR0) hs0.le).mp
      dsimp only [R]
      nlinarith
    have hRpos : 0 < R := by
      dsimp only [R]
      exact Real.sqrt_pos.2 (by nlinarith [sq_pos_of_pos hs0])
    have hRone : R < 1 := by
      have hdiv : s / t < 1 := (div_lt_one ht0).2 hst
      have hRle : R ≤ s / t := (le_div_iff₀ ht0).2 (by simpa [mul_comm] using hcap)
      exact hRle.trans_lt hdiv
    exact ⟨hRpos, hRone, hcap⟩

private lemma large_height_iff {t s r : ℝ}
    (ht0 : 0 < t) (hts : t ≤ s) (hs1 : s < 1) (hr : 0 ≤ r) :
    (0 < Real.sqrt (s ^ 2 + r ^ 2) ∧
      Real.sqrt (s ^ 2 + r ^ 2) < 1 ∧
      t * Real.sqrt (s ^ 2 + r ^ 2) ≤ s) ↔
      r < Real.sqrt (1 - s ^ 2) := by
  have hs0 : 0 < s := ht0.trans_le hts
  have hq : 0 ≤ 1 - s ^ 2 := by nlinarith
  have hsum : 0 ≤ s ^ 2 + r ^ 2 := by positivity
  let R := Real.sqrt (s ^ 2 + r ^ 2)
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = s ^ 2 + r ^ 2 := Real.sq_sqrt hsum
  constructor
  · rintro ⟨hRpos, hRone, hcap⟩
    apply (sq_lt_sq₀ hr (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hq]
    nlinarith
  · intro hball
    have hrsq : r ^ 2 < 1 - s ^ 2 := by
      rw [← Real.sq_sqrt hq]
      exact (sq_lt_sq₀ hr (Real.sqrt_nonneg _)).mpr hball
    have hRpos : 0 < R := by
      dsimp only [R]
      exact Real.sqrt_pos.2 (by nlinarith [sq_pos_of_pos hs0])
    have hRone : R < 1 := by
      apply (sq_lt_sq₀ hR0 (by norm_num)).mp
      nlinarith
    have hcap : t * R ≤ s := by
      have hRt : t * R < t := by simpa using mul_lt_mul_of_pos_left hRone ht0
      exact hRt.le.trans hts
    exact ⟨hRpos, hRone, hcap⟩

lemma coordinateCone_section_volume {t s : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    volume ((Prod.mk s) ⁻¹' coordinateCone t) =
      ENNReal.ofReal (coneSectionArea t s) := by
  by_cases hs0 : s = 0
  · subst s
    have hsec : (Prod.mk (0 : ℝ)) ⁻¹' coordinateCone t = ∅ := by
      ext z
      simp only [Set.mem_preimage, coordinateCone, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false]
      constructor
      · intro h
        have hnonneg : 0 ≤ t * splitNorm (0, z) :=
          mul_nonneg ht0.le (Real.sqrt_nonneg _)
        have hpos : 0 < t * splitNorm (0, z) := mul_pos ht0 h.1
        linarith [h.2.2]
      · exact False.elim
    rw [hsec, measure_empty]
    simp [coneSectionArea, ht0]
  · by_cases hsmall : s ∈ Set.Ico 0 t
    · have hspos : 0 < s := lt_of_le_of_ne hsmall.1 (Ne.symm hs0)
      have ht_sq : t ^ 2 ≤ 1 := by nlinarith
      have hq : 0 ≤ s ^ 2 * (1 - t ^ 2) / t ^ 2 := by positivity
      have hset : (Prod.mk s) ⁻¹' coordinateCone t =
          (WithLp.toLp 2) ⁻¹' Metric.closedBall (0 : E2)
            (Real.sqrt (s ^ 2 * (1 - t ^ 2) / t ^ 2)) := by
        ext z
        simp only [Set.mem_preimage, coordinateCone, Set.mem_setOf_eq,
          Metric.mem_closedBall, dist_zero_right]
        simpa only [splitNorm, Prod.fst, Prod.snd] using
          (small_height_iff ht0 ht1 hspos hsmall.2 (norm_nonneg _))
      rw [hset, (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
        measurableSet_closedBall.nullMeasurableSet,
        volume_E2_closedBall_sqrt hq]
      simp [coneSectionArea, hsmall]
    · by_cases hlarge : s ∈ Set.Ico t 1
      · have hs0' : 0 ≤ s := ht0.le.trans hlarge.1
        have hq : 0 ≤ 1 - s ^ 2 := by nlinarith [hlarge.2.le]
        have hset : (Prod.mk s) ⁻¹' coordinateCone t =
            (WithLp.toLp 2) ⁻¹' Metric.ball (0 : E2) (Real.sqrt (1 - s ^ 2)) := by
          ext z
          simp only [Set.mem_preimage, coordinateCone, Set.mem_setOf_eq,
            Metric.mem_ball, dist_zero_right]
          simpa only [splitNorm, Prod.fst, Prod.snd] using
            (large_height_iff ht0 hlarge.1 hlarge.2 (norm_nonneg _))
        rw [hset, (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
          measurableSet_ball.nullMeasurableSet,
          volume_E2_ball_sqrt hq]
        simp [coneSectionArea, hsmall, hlarge]
      · have hsec : (Prod.mk s) ⁻¹' coordinateCone t = ∅ := by
          ext z
          simp only [Set.mem_preimage, coordinateCone, Set.mem_ofPred_eq,
            Set.mem_empty_iff_false]
          constructor
          · intro h
            have hR0 : 0 ≤ splitNorm (s, z) := Real.sqrt_nonneg _
            have hR2 : splitNorm (s, z) ^ 2 =
                s ^ 2 + ‖WithLp.toLp 2 z‖ ^ 2 := splitNorm_sq _
            have hs_cases : s < 0 ∨ 1 ≤ s := by
              simp only [Set.mem_Ico, not_and_or, not_le] at hsmall hlarge
              rcases hsmall with hsneg | hts
              · exact Or.inl hsneg
              · rcases hlarge with hst | hsone
                · exact False.elim (hts hst)
                · exact Or.inr (le_of_not_gt hsone)
            rcases hs_cases with hsneg | hsone
            · have : 0 ≤ t * splitNorm (s, z) := mul_nonneg ht0.le hR0
              linarith [h.2.2]
            · have hsR : s ≤ splitNorm (s, z) := by
                apply (sq_le_sq₀ (by linarith : 0 ≤ s) hR0).mp
                nlinarith [sq_nonneg ‖WithLp.toLp 2 z‖]
              linarith [h.2.1]
          · exact False.elim
        rw [hsec, measure_empty]
        simp [coneSectionArea, hsmall, hlarge]

lemma volume_coordinateCone {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    volume (coordinateCone t) =
      ENNReal.ofReal (2 * Real.pi * (1 - t) / 3) := by
  rw [show (volume : Measure (ℝ × (Fin 2 → ℝ))) =
      (volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ)) by rfl,
    Measure.prod_apply (measurableSet_coordinateCone t)]
  simp_rw [coordinateCone_section_volume ht0 ht1]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (coneSectionArea_integrable ht0.le ht1)
    (Filter.Eventually.of_forall (coneSectionArea_nonneg ht0.le ht1)),
    integral_coneSectionArea ht0 ht1]

/-- Ambient radial cone with axis `u` and angular threshold `t`. -/
def ambientCone (u : E3) (t : ℝ) : Set E3 :=
  {y | 0 < ‖y‖ ∧ ‖y‖ < 1 ∧ t * ‖y‖ ≤ inner ℝ u y}

def ambientBoundary (u : E3) (t : ℝ) : Set E3 :=
  {y | 0 < ‖y‖ ∧ ‖y‖ < 1 ∧ inner ℝ u y = t * ‖y‖}

lemma measurableSet_ambientCone (u : E3) (t : ℝ) : MeasurableSet (ambientCone u t) := by
  change MeasurableSet
    ({y | 0 < ‖y‖} ∩ ({y | ‖y‖ < 1} ∩ {y | t * ‖y‖ ≤ inner ℝ u y}))
  exact (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    ((isOpen_lt continuous_norm continuous_const).measurableSet.inter
      (isClosed_le (continuous_const.mul continuous_norm)
        (Continuous.inner continuous_const continuous_id)).measurableSet)

lemma volume_ambientCone {u : E3} (hu : ‖u‖ = 1) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    volume (ambientCone u t) = ENNReal.ofReal (2 * Real.pi * (1 - t) / 3) := by
  rcases exists_orthonormalBasis_zero_eq u hu with ⟨b, hb⟩
  let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0
  let coord : E3 → ℝ × (Fin 2 → ℝ) :=
    fun y ↦ split (WithLp.ofLp (b.repr y))
  have hcoord : MeasurePreserving coord volume volume := by
    exact (volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).comp
      ((PiLp.volume_preserving_ofLp (Fin 3)).comp b.measurePreserving_repr)
  have hfirst (y : E3) : (coord y).1 = inner ℝ u y := by
    simp [coord, split, ← hb, OrthonormalBasis.repr_apply_apply]
  have hnorm (y : E3) : splitNorm (coord y) = ‖y‖ := by
    let z := b.repr y
    have hnormz : ‖z‖ = ‖y‖ := b.repr.norm_map y
    have hsq : (coord y).1 ^ 2 + ‖WithLp.toLp 2 (coord y).2‖ ^ 2 = ‖z‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
      rw [Fin.sum_univ_succAbove (fun i : Fin 3 ↦ ‖z.ofLp i‖ ^ 2) 0]
      simp [coord, split, z, MeasurableEquiv.piFinSuccAbove_apply,
        Real.norm_eq_abs, sq_abs]
      rfl
    rw [splitNorm, hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg z), hnormz]
  have hpre : ambientCone u t = coord ⁻¹' coordinateCone t := by
    ext y
    simp only [ambientCone, coordinateCone, Set.mem_ofPred_eq, Set.mem_preimage,
      hnorm, hfirst]
  rw [hpre, hcoord.measure_preimage (measurableSet_coordinateCone t).nullMeasurableSet,
    volume_coordinateCone ht0 ht1]

lemma volume_ambientBoundary {u : E3} (hu : ‖u‖ = 1) (t : ℝ) :
    volume (ambientBoundary u t) = 0 := by
  rcases exists_orthonormalBasis_zero_eq u hu with ⟨b, hb⟩
  let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0
  let coord : E3 → ℝ × (Fin 2 → ℝ) :=
    fun y ↦ split (WithLp.ofLp (b.repr y))
  have hcoord : MeasurePreserving coord volume volume := by
    exact (volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).comp
      ((PiLp.volume_preserving_ofLp (Fin 3)).comp b.measurePreserving_repr)
  have hfirst (y : E3) : (coord y).1 = inner ℝ u y := by
    simp [coord, split, ← hb, OrthonormalBasis.repr_apply_apply]
  have hnorm (y : E3) : splitNorm (coord y) = ‖y‖ := by
    let z := b.repr y
    have hnormz : ‖z‖ = ‖y‖ := b.repr.norm_map y
    have hsq : (coord y).1 ^ 2 + ‖WithLp.toLp 2 (coord y).2‖ ^ 2 = ‖z‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
      rw [Fin.sum_univ_succAbove (fun i : Fin 3 ↦ ‖z.ofLp i‖ ^ 2) 0]
      simp [coord, split, z, MeasurableEquiv.piFinSuccAbove_apply,
        Real.norm_eq_abs, sq_abs]
      rfl
    rw [splitNorm, hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg z), hnormz]
  have hpre : ambientBoundary u t = coord ⁻¹' coordinateBoundary t := by
    ext y
    simp only [ambientBoundary, coordinateBoundary, Set.mem_ofPred_eq, Set.mem_preimage,
      hnorm, hfirst]
  rw [hpre, hcoord.measure_preimage (measurableSet_coordinateBoundary t).nullMeasurableSet,
    volume_coordinateBoundary]

def hemisphereSectionArea (s : ℝ) : ℝ :=
  if s ∈ Set.Ico 0 1 then Real.pi * (1 - s ^ 2) else 0

lemma hemisphereSectionArea_nonneg (s : ℝ) : 0 ≤ hemisphereSectionArea s := by
  unfold hemisphereSectionArea
  split_ifs with hs
  · exact mul_nonneg Real.pi_pos.le (by nlinarith [hs.1, hs.2.le])
  · positivity

lemma hemisphereSectionArea_integrable : Integrable hemisphereSectionArea := by
  let g : ℝ → ℝ := fun s ↦ Real.pi * (1 - s ^ 2)
  have hg : IntegrableOn g (Set.Ico 0 1) :=
    ((continuous_const.mul (continuous_const.sub (continuous_id.pow 2))).integrableOn_Icc
      |>.mono_set Set.Ico_subset_Icc_self)
  apply (hg.integrable_indicator measurableSet_Ico).congr
  filter_upwards [] with s
  simp only [hemisphereSectionArea, Set.mem_Ico]
  by_cases hs : 0 ≤ s ∧ s < 1 <;> simp [hs, g]

lemma integral_hemisphereSectionArea :
    ∫ s : ℝ, hemisphereSectionArea s = 2 * Real.pi / 3 := by
  let g : ℝ → ℝ := fun s ↦ Real.pi * (1 - s ^ 2)
  have hg : IntegrableOn g (Set.Ico 0 1) :=
    ((continuous_const.mul (continuous_const.sub (continuous_id.pow 2))).integrableOn_Icc
      |>.mono_set Set.Ico_subset_Icc_self)
  have hfun : hemisphereSectionArea = (Set.Ico 0 1).indicator g := by
    funext s
    simp only [hemisphereSectionArea, Set.indicator, Set.mem_Ico]
    by_cases hs : 0 ≤ s ∧ s < 1 <;> simp [hs, g]
  rw [hfun, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hsub : ∫ s in (0 : ℝ)..1, 1 - s ^ 2 = (2 / 3 : ℝ) := by
    calc
      _ = (∫ _s : ℝ in (0 : ℝ)..1, (1 : ℝ)) -
          ∫ s : ℝ in (0 : ℝ)..1, s ^ 2 := by
        exact intervalIntegral.integral_sub
          (f := fun _ : ℝ ↦ (1 : ℝ)) (g := fun s : ℝ ↦ s ^ 2)
          (continuous_const.intervalIntegrable _ _)
          ((continuous_id.pow 2).intervalIntegrable _ _)
      _ = _ := by rw [intervalIntegral.integral_const, integral_pow]; norm_num
  dsimp only [g]
  rw [intervalIntegral.integral_const_mul, hsub]
  ring

lemma coordinateCone_zero_section_volume (s : ℝ) :
    volume ((Prod.mk s) ⁻¹' coordinateCone 0) =
      ENNReal.ofReal (hemisphereSectionArea s) := by
  by_cases hs0 : s = 0
  · subst s
    have hset : (Prod.mk (0 : ℝ)) ⁻¹' coordinateCone 0 =
        (WithLp.toLp 2) ⁻¹'
          (Metric.ball (0 : E2) 1 \ {(0 : E2)}) := by
      ext z
      simp only [Set.mem_preimage, coordinateCone, Set.mem_ofPred_eq, zero_mul,
        le_refl, and_true, Set.mem_diff, Metric.mem_ball, dist_zero_right,
        Set.mem_singleton_iff]
      rw [splitNorm]
      norm_num only [Prod.fst, Prod.snd, zero_pow, zero_add]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
      constructor
      · rintro ⟨hz0, hz1⟩
        exact ⟨hz1, by simpa using hz0.ne'⟩
      · rintro ⟨hz1, hz0⟩
        exact ⟨lt_of_le_of_ne (norm_nonneg _) (Ne.symm (by simpa using hz0)), hz1⟩
    rw [hset, (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
      ((measurableSet_ball.diff (measurableSet_singleton (0 : E2))).nullMeasurableSet),
      measure_sdiff_null (measure_singleton (0 : E2))]
    convert volume_E2_ball_sqrt (q := (1 : ℝ)) (by norm_num) using 1 <;>
      simp [hemisphereSectionArea]
  · by_cases hs : s ∈ Set.Ico 0 1
    · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
      have hq : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2.le]
      have hset : (Prod.mk s) ⁻¹' coordinateCone 0 =
          (WithLp.toLp 2) ⁻¹' Metric.ball (0 : E2) (Real.sqrt (1 - s ^ 2)) := by
        ext z
        simp only [Set.mem_preimage, coordinateCone, Set.mem_ofPred_eq, zero_mul,
          zero_le, and_true, Metric.mem_ball, dist_zero_right]
        let r := ‖WithLp.toLp 2 z‖
        have hr : 0 ≤ r := norm_nonneg _
        have hsum : 0 ≤ s ^ 2 + r ^ 2 := by positivity
        have hR2 : Real.sqrt (s ^ 2 + r ^ 2) ^ 2 = s ^ 2 + r ^ 2 :=
          Real.sq_sqrt hsum
        have hpos : 0 < Real.sqrt (s ^ 2 + r ^ 2) :=
          Real.sqrt_pos.2 (by nlinarith [sq_pos_of_pos hspos])
        have heq : Real.sqrt (s ^ 2 + r ^ 2) < 1 ↔ r < Real.sqrt (1 - s ^ 2) := by
          constructor
          · intro h
            apply (sq_lt_sq₀ hr (Real.sqrt_nonneg _)).mp
            rw [Real.sq_sqrt hq]
            nlinarith
          · intro h
            have hrsq : r ^ 2 < 1 - s ^ 2 := by
              rw [← Real.sq_sqrt hq]
              exact (sq_lt_sq₀ hr (Real.sqrt_nonneg _)).mpr h
            apply (sq_lt_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
            nlinarith
        constructor
        · rintro ⟨hRpos', hRone, hsnonneg⟩
          exact heq.mp hRone
        · intro hrball
          exact ⟨hpos, heq.mpr hrball, hs.1⟩
      rw [hset, (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
        measurableSet_ball.nullMeasurableSet, volume_E2_ball_sqrt hq]
      simp [hemisphereSectionArea, hs]
    · have hsec : (Prod.mk s) ⁻¹' coordinateCone 0 = ∅ := by
        ext z
        simp only [Set.mem_preimage, coordinateCone, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, zero_mul, zero_le, and_true]
        constructor
        · intro h
          have hR0 : 0 ≤ splitNorm (s, z) := Real.sqrt_nonneg _
          have hR2 : splitNorm (s, z) ^ 2 =
              s ^ 2 + ‖WithLp.toLp 2 z‖ ^ 2 := splitNorm_sq _
          have hs_cases : s < 0 ∨ 1 ≤ s := by
            simp only [Set.mem_Ico, not_and_or, not_le] at hs
            rcases hs with hsneg | hsone
            · exact Or.inl hsneg
            · exact Or.inr (le_of_not_gt hsone)
          rcases hs_cases with hsneg | hsone
          · linarith
          · have hsR : s ≤ splitNorm (s, z) := by
              apply (sq_le_sq₀ (by linarith : 0 ≤ s) hR0).mp
              nlinarith [sq_nonneg ‖WithLp.toLp 2 z‖]
            linarith [h.2]
        · exact False.elim
      rw [hsec, measure_empty]
      simp [hemisphereSectionArea, hs]

lemma volume_coordinateCone_zero :
    volume (coordinateCone 0) = ENNReal.ofReal (2 * Real.pi / 3) := by
  rw [show (volume : Measure (ℝ × (Fin 2 → ℝ))) =
      (volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ)) by rfl,
    Measure.prod_apply (measurableSet_coordinateCone 0)]
  simp_rw [coordinateCone_zero_section_volume]
  rw [← ofReal_integral_eq_lintegral_ofReal hemisphereSectionArea_integrable
    (Filter.Eventually.of_forall hemisphereSectionArea_nonneg),
    integral_hemisphereSectionArea]

lemma volume_ambientCone_zero {u : E3} (hu : ‖u‖ = 1) :
    volume (ambientCone u 0) = ENNReal.ofReal (2 * Real.pi / 3) := by
  rcases exists_orthonormalBasis_zero_eq u hu with ⟨b, hb⟩
  let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0
  let coord : E3 → ℝ × (Fin 2 → ℝ) :=
    fun y ↦ split (WithLp.ofLp (b.repr y))
  have hcoord : MeasurePreserving coord volume volume := by
    exact (volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).comp
      ((PiLp.volume_preserving_ofLp (Fin 3)).comp b.measurePreserving_repr)
  have hfirst (y : E3) : (coord y).1 = inner ℝ u y := by
    simp [coord, split, ← hb, OrthonormalBasis.repr_apply_apply]
  have hnorm (y : E3) : splitNorm (coord y) = ‖y‖ := by
    let z := b.repr y
    have hnormz : ‖z‖ = ‖y‖ := b.repr.norm_map y
    have hsq : (coord y).1 ^ 2 + ‖WithLp.toLp 2 (coord y).2‖ ^ 2 = ‖z‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
      rw [Fin.sum_univ_succAbove (fun i : Fin 3 ↦ ‖z.ofLp i‖ ^ 2) 0]
      simp [coord, split, z, MeasurableEquiv.piFinSuccAbove_apply,
        Real.norm_eq_abs, sq_abs]
      rfl
    rw [splitNorm, hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg z), hnormz]
  have hpre : ambientCone u 0 = coord ⁻¹' coordinateCone 0 := by
    ext y
    simp only [ambientCone, coordinateCone, Set.mem_ofPred_eq, Set.mem_preimage,
      hnorm, hfirst]
  rw [hpre, hcoord.measure_preimage (measurableSet_coordinateCone 0).nullMeasurableSet,
    volume_coordinateCone_zero]

abbrev S2 := Metric.sphere (0 : E3) 1

def localSphericalCap (u : S2) (t : ℝ) : Set S2 :=
  {x | t ≤ inner ℝ (x : E3) (u : E3)}

def localSphericalLevel (u : S2) (t : ℝ) : Set S2 :=
  {x | inner ℝ (x : E3) (u : E3) = t}

lemma S2_norm (x : S2) : ‖(x : E3)‖ = 1 := by
  simpa [Metric.mem_sphere, dist_zero_right] using x.property

lemma measurableSet_localSphericalCap (u : S2) (t : ℝ) :
    MeasurableSet (localSphericalCap u t) := by
  exact (isClosed_le continuous_const
    (Continuous.inner continuous_subtype_val continuous_const)).measurableSet

lemma measurableSet_localSphericalLevel (u : S2) (t : ℝ) :
    MeasurableSet (localSphericalLevel u t) := by
  exact (isClosed_eq
    (Continuous.inner continuous_subtype_val continuous_const)
    continuous_const).measurableSet

lemma radialSector_localSphericalCap (u : S2) (t : ℝ) :
    Set.Ioo (0 : ℝ) 1 • ((↑) '' localSphericalCap u t) =
      ambientCone (u : E3) t := by
  ext y
  constructor
  · rintro ⟨r, hr, z, ⟨x, hx, rfl⟩, rfl⟩
    have hrnorm : ‖r • (x : E3)‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, S2_norm, mul_one]
    have hinner : inner ℝ (u : E3) (r • (x : E3)) =
        r * inner ℝ (u : E3) (x : E3) := by rw [real_inner_smul_right]
    refine ⟨?_, ?_, ?_⟩
    · rw [hrnorm]
      exact hr.1
    · rw [hrnorm]
      exact hr.2
    · rw [hrnorm, hinner]
      change t ≤ inner ℝ (x : E3) (u : E3) at hx
      rw [real_inner_comm] at hx
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hx hr.1.le
  · intro hy
    let r := ‖y‖
    have hr0 : 0 < r := hy.1
    have hr1 : r < 1 := hy.2.1
    let x0 : E3 := r⁻¹ • y
    have hxnorm : ‖x0‖ = 1 := by
      simp [x0, norm_smul, abs_inv, abs_of_pos hr0, r, hr0.ne']
    let x : S2 := ⟨x0, by simpa [Metric.mem_sphere, dist_zero_right] using hxnorm⟩
    have hcap : x ∈ localSphericalCap u t := by
      change t ≤ inner ℝ x0 (u : E3)
      have hmul : r * t ≤ r * inner ℝ x0 (u : E3) := by
        calc
          r * t = t * ‖y‖ := by dsimp only [r]; ring
          _ ≤ inner ℝ (u : E3) y := hy.2.2
          _ = r * inner ℝ x0 (u : E3) := by
            rw [real_inner_comm]
            dsimp only [x0]
            rw [real_inner_smul_left]
            field_simp [hr0.ne']
      nlinarith
    refine ⟨r, ⟨hr0, hr1⟩, (x : E3), ⟨x, hcap, rfl⟩, ?_⟩
    simp [x, x0, r, hr0.ne']

lemma radialSector_localSphericalLevel (u : S2) (t : ℝ) :
    Set.Ioo (0 : ℝ) 1 • ((↑) '' localSphericalLevel u t) =
      ambientBoundary (u : E3) t := by
  ext y
  constructor
  · rintro ⟨r, hr, z, ⟨x, hx, rfl⟩, rfl⟩
    have hrnorm : ‖r • (x : E3)‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, S2_norm, mul_one]
    have hinner : inner ℝ (u : E3) (r • (x : E3)) =
        r * inner ℝ (u : E3) (x : E3) := by rw [real_inner_smul_right]
    refine ⟨?_, ?_, ?_⟩
    · simpa [hrnorm] using hr.1
    · simpa [hrnorm] using hr.2
    · rw [hrnorm, hinner]
      change inner ℝ (x : E3) (u : E3) = t at hx
      rw [real_inner_comm] at hx
      rw [hx]
      ring
  · intro hy
    let r := ‖y‖
    have hr0 : 0 < r := hy.1
    have hr1 : r < 1 := hy.2.1
    let x0 : E3 := r⁻¹ • y
    have hxnorm : ‖x0‖ = 1 := by
      simp [x0, norm_smul, r, hr0.ne']
    let x : S2 := ⟨x0, by simpa [Metric.mem_sphere, dist_zero_right] using hxnorm⟩
    have hlevel : x ∈ localSphericalLevel u t := by
      change inner ℝ x0 (u : E3) = t
      have heq : r * inner ℝ x0 (u : E3) = r * t := by
        calc
          r * inner ℝ x0 (u : E3) = inner ℝ (u : E3) y := by
            dsimp only [x0]
            rw [real_inner_comm, real_inner_smul_right]
            field_simp [hr0.ne']
          _ = t * ‖y‖ := hy.2.2
          _ = r * t := by dsimp only [r]; ring
      exact mul_left_cancel₀ hr0.ne' heq
    refine ⟨r, ⟨hr0, hr1⟩, (x : E3), ⟨x, hlevel, rfl⟩, ?_⟩
    simp [x, x0, r, hr0.ne']

lemma rawSurface_localSphericalLevel (u : S2) (t : ℝ) :
    (volume : Measure E3).toSphere (localSphericalLevel u t) = 0 := by
  rw [Measure.toSphere_apply' volume (measurableSet_localSphericalLevel u t),
    radialSector_localSphericalLevel, volume_ambientBoundary (S2_norm u), mul_zero]

def negS2 (u : S2) : S2 :=
  ⟨-(u : E3), by simpa [Metric.mem_sphere, dist_zero_right, S2_norm u]⟩

lemma localCaps_union (u : S2) (t : ℝ) :
    localSphericalCap u t ∪ localSphericalCap (negS2 u) (-t) = Set.univ := by
  ext x
  simp only [localSphericalCap, Set.mem_union, Set.mem_ofPred_eq, negS2,
    Set.mem_univ, iff_true, inner_neg_right]
  by_cases h : t ≤ inner ℝ (x : E3) (u : E3)
  · exact Or.inl h
  · right
    linarith

lemma localCaps_inter (u : S2) (t : ℝ) :
    localSphericalCap u t ∩ localSphericalCap (negS2 u) (-t) =
      localSphericalLevel u t := by
  ext x
  simp only [localSphericalCap, Set.mem_inter_iff, Set.mem_ofPred_eq, negS2,
    inner_neg_right, localSphericalLevel]
  constructor
  · rintro ⟨h₁, h₂⟩
    linarith
  · intro h
    constructor <;> linarith

lemma rawSurface_univ :
    (volume : Measure E3).toSphere (Set.univ : Set S2) =
      ENNReal.ofReal (4 * Real.pi) := by
  rw [Measure.toSphere_apply_univ]
  simp only [finrank_euclideanSpace_fin, EuclideanSpace.volume_ball_fin_three,
    ENNReal.ofReal_one, one_pow, one_mul, Nat.cast_ofNat]
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 3)]
  congr 1
  ring

lemma rawSurface_localSphericalCap_of_pos (u : S2) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (volume : Measure E3).toSphere (localSphericalCap u t) =
      ENNReal.ofReal (2 * Real.pi * (1 - t)) := by
  rw [Measure.toSphere_apply' volume (measurableSet_localSphericalCap u t),
    radialSector_localSphericalCap,
    volume_ambientCone (S2_norm u) ht0 ht1]
  simp only [finrank_euclideanSpace_fin, Nat.cast_ofNat]
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 3)]
  congr 1
  ring

lemma rawSurface_localSphericalCap_zero (u : S2) :
    (volume : Measure E3).toSphere (localSphericalCap u 0) =
      ENNReal.ofReal (2 * Real.pi) := by
  rw [Measure.toSphere_apply' volume (measurableSet_localSphericalCap u 0),
    radialSector_localSphericalCap,
    volume_ambientCone_zero (S2_norm u)]
  simp only [finrank_euclideanSpace_fin, Nat.cast_ofNat]
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 3)]
  congr 1
  ring

lemma rawSurface_localSphericalCap_of_neg (u : S2) {t : ℝ}
    (htneg : t < 0) (htlower : -1 ≤ t) :
    (volume : Measure E3).toSphere (localSphericalCap u t) =
      ENNReal.ofReal (2 * Real.pi * (1 - t)) := by
  let v := negS2 u
  have hminuspos : 0 < -t := neg_pos.mpr htneg
  have hminusone : -t ≤ 1 := by linarith
  have hplus_nonneg : 0 ≤ 2 * Real.pi * (1 + t) :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (by linarith)
  have hminus_nonneg : 0 ≤ 2 * Real.pi * (1 - t) :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (by linarith)
  have hvpos := rawSurface_localSphericalCap_of_pos v hminuspos hminusone
  have hunion := measure_union_add_inter
    (localSphericalCap u t)
    (measurableSet_localSphericalCap v (-t))
    (μ := (volume : Measure E3).toSphere)
  rw [localCaps_union, localCaps_inter, rawSurface_univ,
    rawSurface_localSphericalLevel, add_zero, hvpos] at hunion
  apply (ENNReal.add_left_inj ENNReal.ofReal_ne_top).mp
  calc
    _ = ENNReal.ofReal (4 * Real.pi) := hunion.symm
    _ = ENNReal.ofReal (2 * Real.pi * (1 - t)) +
        ENNReal.ofReal (2 * Real.pi * (1 + t)) := by
      calc
        ENNReal.ofReal (4 * Real.pi) =
            ENNReal.ofReal
              (2 * Real.pi * (1 - t) + 2 * Real.pi * (1 + t)) :=
          congrArg ENNReal.ofReal (by ring)
        _ = _ := ENNReal.ofReal_add hminus_nonneg hplus_nonneg
    _ = _ := by
      congr 1
      congr 1
      ring

theorem rawSurface_localSphericalCap (u : S2) {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (volume : Measure E3).toSphere (localSphericalCap u t) =
      ENNReal.ofReal (2 * Real.pi * (1 - t)) := by
  rcases lt_trichotomy t 0 with htneg | hzero | htpos
  · exact rawSurface_localSphericalCap_of_neg u htneg ht.1
  · subst t
    simpa using rawSurface_localSphericalCap_zero u
  · exact rawSurface_localSphericalCap_of_pos u htpos ht.2

theorem rawSurface_sphericalCap (u : Erdos988.S2) {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (volume : Measure Erdos988.E3).toSphere (Erdos988.sphericalCap u t) =
      ENNReal.ofReal (2 * Real.pi * (1 - t)) := by
  simpa [Erdos988.sphericalCap, localSphericalCap] using
    rawSurface_localSphericalCap u ht

lemma surfaceFiniteMeasure_ne_zero : Erdos988.surfaceFiniteMeasure ≠ 0 := by
  intro h
  apply (volume : Measure Erdos988.E3).toSphere_ne_zero
  exact congrArg FiniteMeasure.toMeasure h

lemma surfaceFiniteMeasure_mass :
    Erdos988.surfaceFiniteMeasure.mass = ENNReal.ofReal (4 * Real.pi) := by
  rw [FiniteMeasure.ennreal_mass]
  change (volume : Measure Erdos988.E3).toSphere
      (Set.univ : Set Erdos988.S2) = _
  exact rawSurface_univ

theorem surfaceProbability_sphericalCap (u : Erdos988.S2) {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (Erdos988.surfaceProbability : Measure Erdos988.S2)
        (Erdos988.sphericalCap u t) =
      ENNReal.ofReal (Erdos988.capArea t) := by
  change (Erdos988.surfaceFiniteMeasure.normalize : Measure Erdos988.S2)
      (Erdos988.sphericalCap u t) = _
  rw [Erdos988.surfaceFiniteMeasure.toMeasure_normalize_eq_of_nonzero
    surfaceFiniteMeasure_ne_zero]
  rw [Measure.smul_apply, Measure.nnreal_smul_coe_apply,
    ENNReal.coe_inv
      (Erdos988.surfaceFiniteMeasure.mass_nonzero_iff.mpr
        surfaceFiniteMeasure_ne_zero),
    surfaceFiniteMeasure_mass]
  change (ENNReal.ofReal (4 * Real.pi))⁻¹ *
      (volume : Measure Erdos988.E3).toSphere
        (Erdos988.sphericalCap u t) = _
  rw [rawSurface_sphericalCap u ht]
  have hmass : 0 < 4 * Real.pi := by positivity
  rw [← ENNReal.ofReal_inv_of_pos hmass,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hmass.le)]
  apply congrArg ENNReal.ofReal
  unfold Erdos988.capArea
  field_simp [Real.pi_ne_zero]
  ring

theorem normalizedArea_sphericalCap (u : Erdos988.S2) {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    Erdos988.normalizedArea (Erdos988.sphericalCap u t) =
      Erdos988.capArea t := by
  have h := congrArg ENNReal.toReal (surfaceProbability_sphericalCap u ht)
  have hcap_nonneg : 0 ≤ Erdos988.capArea t := by
    unfold Erdos988.capArea
    linarith [ht.2]
  simpa [Erdos988.normalizedArea,
    ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    ENNReal.toReal_ofReal hcap_nonneg] using h

theorem rawSurface_sphericalLevel (u : Erdos988.S2) (t : ℝ) :
    (volume : Measure Erdos988.E3).toSphere
        {x : Erdos988.S2 |
          inner ℝ (x : Erdos988.E3) (u : Erdos988.E3) = t} = 0 := by
  simpa [localSphericalLevel] using rawSurface_localSphericalLevel u t

theorem surfaceProbability_sphericalLevel_null (u : Erdos988.S2) (t : ℝ) :
    (Erdos988.surfaceProbability : Measure Erdos988.S2)
        {x : Erdos988.S2 |
          inner ℝ (x : Erdos988.E3) (u : Erdos988.E3) = t} = 0 := by
  change (Erdos988.surfaceFiniteMeasure.normalize : Measure Erdos988.S2)
      {x : Erdos988.S2 |
        inner ℝ (x : Erdos988.E3) (u : Erdos988.E3) = t} = 0
  rw [Erdos988.surfaceFiniteMeasure.toMeasure_normalize_eq_of_nonzero
    surfaceFiniteMeasure_ne_zero, Measure.smul_apply]
  change Erdos988.surfaceFiniteMeasure.mass⁻¹ •
      (volume : Measure Erdos988.E3).toSphere
        {x : Erdos988.S2 |
          inner ℝ (x : Erdos988.E3) (u : Erdos988.E3) = t} = 0
  rw [rawSurface_sphericalLevel]
  simp

theorem surfaceProbability_singleton_null (u : Erdos988.S2) :
    (Erdos988.surfaceProbability : Measure Erdos988.S2) ({u} : Set Erdos988.S2) = 0 := by
  refine measure_mono_null ?_ (surfaceProbability_sphericalLevel_null u 1)
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst x
  change inner ℝ (u : Erdos988.E3) (u : Erdos988.E3) = 1
  rw [real_inner_self_eq_norm_sq, S2_norm u]
  norm_num

instance surfaceProbability_nullSingletonClass :
    NullSingletonClass (Erdos988.surfaceProbability : Measure Erdos988.S2) where
  measure_singleton := surfaceProbability_singleton_null

theorem surfaceProbability_finset_null (s : Finset Erdos988.S2) :
    (Erdos988.surfaceProbability : Measure Erdos988.S2) (s : Set Erdos988.S2) = 0 :=
  s.measure_zero _

end

end Erdos991
