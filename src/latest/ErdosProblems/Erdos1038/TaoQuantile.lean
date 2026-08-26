import ErdosProblems.Erdos1038.TaoUpperDuality
import ErdosProblems.Erdos1038.TaoUpperClosedTarget
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Expansive quantiles for Tao's upper-bound rearrangement

This file constructs the generalized inverse used in Lemma 2.2 of Tao's
updated note.  The cumulative volume of a measurable target set is
nondecreasing and `1`-Lipschitz.  Its least level-set inverse is therefore
expansive.  We also prove the generalized-inverse distance estimate used by
`TaoUpperDuality`.
-/

open scoped ENNReal NNReal
open Filter MeasureTheory Set Topology

namespace Erdos1038

noncomputable section

/-- Cumulative volume of `E`, starting at the left endpoint `l`. -/
def volumeCumulative (E : Set ℝ) (l x : ℝ) : ℝ :=
  volume.real (E ∩ Icc l x)

lemma volumeCumulative_nonneg (E : Set ℝ) (l x : ℝ) :
    0 ≤ volumeCumulative E l x :=
  measureReal_nonneg

lemma volumeCumulative_mono (E : Set ℝ) (l : ℝ) :
    Monotone (volumeCumulative E l) := by
  intro x y hxy
  apply measureReal_mono
  · intro z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.trans hxy⟩
  · apply ne_of_lt
    apply lt_of_le_of_lt (measure_mono inter_subset_right)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top

lemma volumeCumulative_increment_le (E : Set ℝ) (l : ℝ)
    {x y : ℝ} (hxy : x ≤ y) :
    volumeCumulative E l y - volumeCumulative E l x ≤ y - x := by
  have hsubset : E ∩ Icc l y ⊆
      (E ∩ Icc l x) ∪ Ioc x y := by
    intro z hz
    by_cases hzx : z ≤ x
    · exact Or.inl ⟨hz.1, hz.2.1, hzx⟩
    · exact Or.inr ⟨lt_of_not_ge hzx, hz.2.2⟩
  have hfiniteUnion :
      volume ((E ∩ Icc l x) ∪ Ioc x y) ≠ ∞ := by
    have hset : (E ∩ Icc l x) ∪ Ioc x y ⊆ Icc (min l x) y := by
      intro z hz
      rcases hz with hz | hz
      · exact ⟨(min_le_left l x).trans hz.2.1, hz.2.2.trans hxy⟩
      · exact ⟨(min_le_right l x).trans hz.1.le, hz.2⟩
    have hmeasure := measure_mono (μ := volume) hset
    have hvolume : volume (Icc (min l x) y) < ∞ := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_lt_top
    exact ne_of_lt (hmeasure.trans_lt hvolume)
  have hbound : volumeCumulative E l y ≤
        volume.real ((E ∩ Icc l x) ∪ Ioc x y) :=
      measureReal_mono hsubset hfiniteUnion
  have hunion : volumeCumulative E l y ≤
      volume.real (E ∩ Icc l x) + volume.real (Ioc x y) :=
    hbound.trans (measureReal_union_le _ _)
  have hinterval : volume.real (Ioc x y) = y - x := by
    rw [measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hxy)]
  rw [hinterval] at hunion
  change volumeCumulative E l y ≤
    volumeCumulative E l x + (y - x) at hunion
  change volumeCumulative E l y - volumeCumulative E l x ≤ y - x
  linarith

lemma volumeCumulative_lipschitz (E : Set ℝ) (l : ℝ) :
    LipschitzWith 1 (volumeCumulative E l) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rcases le_total x y with hxy | hyx
  · have hmono := volumeCumulative_mono E l hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hmono),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    simpa only [neg_sub] using! volumeCumulative_increment_le E l hxy
  · have hmono := volumeCumulative_mono E l hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hmono),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact volumeCumulative_increment_le E l hyx

lemma continuous_volumeCumulative (E : Set ℝ) (l : ℝ) :
    Continuous (volumeCumulative E l) :=
  (volumeCumulative_lipschitz E l).continuous

lemma volumeCumulative_self (E : Set ℝ) (l : ℝ) :
    volumeCumulative E l l = 0 := by
  apply le_antisymm
  · calc
      volumeCumulative E l l ≤ volume.real ({l} : Set ℝ) := by
        apply measureReal_mono
        · simpa only [Icc_self] using! inter_subset_right
        · simp
      _ = 0 := by
        rw [measureReal_def, Real.volume_singleton]
        simp
  · exact volumeCumulative_nonneg E l l

/-- A target set of sufficiently large volume reaches the required
cumulative level at some finite cap. -/
theorem exists_volumeCumulative_cap
    (E : Set ℝ) (left upper : ℝ)
    (h_left_upper : left ≤ upper) (hE : E ⊆ Ici left)
    (hmass : ENNReal.ofReal (upper - left) < volume E) :
    ∃ cap : ℝ, left ≤ cap ∧
      upper - left < volumeCumulative E left cap := by
  let S : ℕ → Set ℝ := fun n ↦
    E ∩ Icc left (left + (n : ℝ))
  have hSmono : Monotone S := by
    intro n m hnm z hz
    refine ⟨hz.1, hz.2.1, ?_⟩
    have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    exact hz.2.2.trans (by linarith)
  have hSunion : (⋃ n, S n) = E := by
    ext z
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
      exact hn.1
    · intro hz
      have hzleft : left ≤ z := hE hz
      obtain ⟨n : ℕ, hn⟩ := exists_nat_ge (z - left)
      apply Set.mem_iUnion.mpr
      refine ⟨n, hz, hzleft, ?_⟩
      linarith
  have htend : Tendsto (fun n ↦ volume (S n)) atTop (𝓝 (volume E)) := by
    simpa only [hSunion] using!
      (tendsto_measure_iUnion_atTop (μ := volume) hSmono)
  have hevent : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (upper - left) < volume (S n) :=
    htend (Ioi_mem_nhds hmass)
  obtain ⟨n, hn⟩ := hevent.exists
  let cap : ℝ := left + (n : ℝ)
  have hfinite : volume (S n) ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (measure_mono (μ := volume) inter_subset_right)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hlength : 0 ≤ upper - left := sub_nonneg.mpr h_left_upper
  have hreal : upper - left < (volume (S n)).toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal hlength hfinite).mp hn
  refine ⟨cap, ?_, ?_⟩
  · unfold cap
    exact le_add_of_nonneg_right (Nat.cast_nonneg n)
  · simpa only [cap, S, volumeCumulative, measureReal_def] using! hreal

/-- Non-strict bounded-target variant.  If the target is already contained
in a finite interval, its full mass is attained at the right cap, so a
non-strict mass lower bound suffices. -/
theorem volumeCumulative_at_bounded_cap
    (E : Set ℝ) (left upper cap : ℝ)
    (hEleft : E ⊆ Ici left) (hEcap : E ⊆ Iic cap)
    (hmass : ENNReal.ofReal (upper - left) ≤ volume E) :
    upper - left ≤ volumeCumulative E left cap := by
  have hset : E ∩ Icc left cap = E := by
    apply Set.Subset.antisymm inter_subset_left
    intro x hx
    exact ⟨hx, hEleft hx, hEcap hx⟩
  have hfinite : volume E ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt
      (measure_mono (show E ⊆ Icc left cap by
        intro x hx
        exact ⟨hEleft hx, hEcap hx⟩))
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hreal : upper - left ≤ (volume E).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hmass
  unfold volumeCumulative
  rw [hset, measureReal_def]
  exact hreal

/-- Abstract data needed for a compact cumulative-volume quantile. -/
structure QuantileData where
  left : ℝ
  upper : ℝ
  cap : ℝ
  h_left_upper : left ≤ upper
  h_left_cap : left ≤ cap
  F : ℝ → ℝ
  hcontinuous : Continuous F
  hmono : Monotone F
  h_left : F left = 0
  hincrement : ∀ {x y : ℝ}, x ≤ y → F y - F x ≤ y - x
  htop : upper - left ≤ F cap

/-- Cumulative volume produces quantile data whenever the target set has
enough mass before `cap`. -/
def volumeQuantileData (E : Set ℝ) (left upper cap : ℝ)
    (h_left_upper : left ≤ upper) (h_left_cap : left ≤ cap)
    (htop : upper - left ≤ volumeCumulative E left cap) : QuantileData where
  left := left
  upper := upper
  cap := cap
  h_left_upper := h_left_upper
  h_left_cap := h_left_cap
  F := volumeCumulative E left
  hcontinuous := continuous_volumeCumulative E left
  hmono := volumeCumulative_mono E left
  h_left := volumeCumulative_self E left
  hincrement := fun hxy ↦ volumeCumulative_increment_le E left hxy
  htop := htop

namespace QuantileData

variable (Q : QuantileData)

/-- The compact level set used to define the least generalized inverse. -/
def levelSet (s : Icc Q.left Q.upper) : Set ℝ :=
  Icc Q.left Q.cap ∩ Q.F ⁻¹' {s.1 - Q.left}

lemma levelSet_nonempty (s : Icc Q.left Q.upper) :
    (Q.levelSet s).Nonempty := by
  have hlevel : s.1 - Q.left ∈ Icc (Q.F Q.left) (Q.F Q.cap) := by
    rw [Q.h_left]
    constructor
    · linarith [s.2.1]
    · exact (sub_le_sub_right s.2.2 Q.left).trans Q.htop
  obtain ⟨x, hx, hFx⟩ :=
    (intermediate_value_Icc Q.h_left_cap Q.hcontinuous.continuousOn) hlevel
  exact ⟨x, hx, hFx⟩

lemma levelSet_compact (s : Icc Q.left Q.upper) :
    IsCompact (Q.levelSet s) := by
  exact isCompact_Icc.inter_right
    (isClosed_singleton.preimage Q.hcontinuous)

/-- Least point where the cumulative function reaches level `s-l`. -/
def quantile (s : Icc Q.left Q.upper) : ℝ :=
  Classical.choose ((Q.levelSet_compact s).exists_isLeast
    (Q.levelSet_nonempty s))

lemma quantile_isLeast (s : Icc Q.left Q.upper) :
    IsLeast (Q.levelSet s) (Q.quantile s) :=
  Classical.choose_spec ((Q.levelSet_compact s).exists_isLeast
    (Q.levelSet_nonempty s))

lemma quantile_mem_Icc (s : Icc Q.left Q.upper) :
    Q.quantile s ∈ Icc Q.left Q.cap :=
  (Q.quantile_isLeast s).1.1

lemma F_quantile (s : Icc Q.left Q.upper) :
    Q.F (Q.quantile s) = s.1 - Q.left :=
  (Q.quantile_isLeast s).1.2

lemma strictMono_quantile : StrictMono Q.quantile := by
  intro s t hst
  apply lt_of_not_ge
  intro hreverse
  have hF := Q.hmono hreverse
  rw [Q.F_quantile s, Q.F_quantile t] at hF
  exact (not_le_of_gt hst) (by
    change t.1 ≤ s.1
    linarith)

lemma monotone_quantile : Monotone Q.quantile :=
  Q.strictMono_quantile.monotone

/-- The least-level quantile is expansive. -/
lemma quantile_expansive {s t : Icc Q.left Q.upper} (hst : s ≤ t) :
    t.1 - s.1 ≤ Q.quantile t - Q.quantile s := by
  have hq := Q.monotone_quantile hst
  have hinc := Q.hincrement hq
  rw [Q.F_quantile s, Q.F_quantile t] at hinc
  linarith

lemma self_le_quantile (s : Icc Q.left Q.upper) :
    s.1 ≤ Q.quantile s := by
  have hq := (Q.quantile_mem_Icc s).1
  have hinc := Q.hincrement hq
  rw [Q.h_left, Q.F_quantile s] at hinc
  linarith

/-- For a cumulative-volume quantile, every positive-level quantile point
lies in the closure of the target set.  The possible zero-level endpoint is
irrelevant to the pushed interval measure. -/
theorem quantile_mem_closure_of_volumeCumulative
    (E : Set ℝ) (hF : Q.F = volumeCumulative E Q.left)
    (s : Icc Q.left Q.upper) (hs : Q.left < s.1) :
    Q.quantile s ∈ closure E := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let q := Q.quantile s
  have hqLeft : Q.left < q :=
    hs.trans_le (Q.self_le_quantile s)
  let δ : ℝ := min ε ((q - Q.left) / 2)
  have hδ : 0 < δ := by
    unfold δ
    exact lt_min hε (half_pos (sub_pos.mpr hqLeft))
  have hδeps : δ ≤ ε := min_le_left _ _
  have hδhalf : δ ≤ (q - Q.left) / 2 := min_le_right _ _
  have hqδLeft : Q.left ≤ q - δ := by linarith
  have hsegment : (E ∩ Ioc (q - δ) q).Nonempty := by
    by_cases hnonempty : (E ∩ Ioc (q - δ) q).Nonempty
    · exact hnonempty
    · have hset : E ∩ Icc Q.left (q - δ) =
          E ∩ Icc Q.left q := by
        ext z
        constructor
        · intro hz
          exact ⟨hz.1, hz.2.1, hz.2.2.trans (sub_le_self q hδ.le)⟩
        · intro hz
          refine ⟨hz.1, hz.2.1, ?_⟩
          apply le_of_not_gt
          intro hzδ
          exact hnonempty ⟨z, hz.1, hzδ, hz.2.2⟩
      have hFcumulative : Q.F (q - δ) = Q.F q := by
        rw [hF]
        unfold volumeCumulative
        rw [hset]
      have hqCap : q ≤ Q.cap := (Q.quantile_mem_Icc s).2
      have hlevel : q - δ ∈ Q.levelSet s := by
        constructor
        · exact ⟨hqδLeft, (sub_le_self q hδ.le).trans hqCap⟩
        · change Q.F (q - δ) = s.1 - Q.left
          rw [hFcumulative]
          simpa only [q] using! Q.F_quantile s
      have hleast := (Q.quantile_isLeast s).2 hlevel
      change q ≤ q - δ at hleast
      linarith
  obtain ⟨y, hyE, hyLower, hyUpper⟩ := hsegment
  refine ⟨y, hyE, ?_⟩
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyUpper)]
  linarith

lemma F_nonneg_of_left_le {x : ℝ} (hx : Q.left ≤ x) :
    0 ≤ Q.F x := by
  rw [← Q.h_left]
  exact Q.hmono hx

lemma left_add_F_le {x : ℝ} (hx : Q.left ≤ x) :
    Q.left + Q.F x ≤ x := by
  have hinc := Q.hincrement hx
  rw [Q.h_left] at hinc
  linarith

/-- Generalized-inverse source coordinate associated with a target point. -/
def inverseCoordinate (t : ℝ) : ℝ := Q.left + Q.F t

lemma inverseCoordinate_mem_Icc {t : ℝ}
    (ht : t ∈ Icc Q.left Q.upper) :
    Q.inverseCoordinate t ∈ Icc Q.left Q.upper := by
  constructor
  · unfold inverseCoordinate
    linarith [Q.F_nonneg_of_left_le ht.1]
  · exact (Q.left_add_F_le ht.1).trans ht.2

lemma inverseCoordinate_le {t : ℝ} (ht : Q.left ≤ t) :
    Q.inverseCoordinate t ≤ t :=
  Q.left_add_F_le ht

/-- Tao's global extension of the quantile: identity to the left, the
least-level quantile on the source interval, and the affine slope-one
continuation from the upper endpoint to the right. -/
def rearrangement (x : ℝ) : ℝ :=
  if hleft : x < Q.left then x
  else if hupper : x ≤ Q.upper then
    Q.quantile ⟨x, le_of_not_gt hleft, hupper⟩
  else
    Q.quantile ⟨Q.upper, Q.h_left_upper, le_rfl⟩ + (x - Q.upper)

lemma rearrangement_of_mem {x : ℝ} (hx : x ∈ Icc Q.left Q.upper) :
    Q.rearrangement x = Q.quantile ⟨x, hx⟩ := by
  simp [rearrangement, not_lt_of_ge hx.1, hx.2]

lemma rearrangement_of_lt_left {x : ℝ} (hx : x < Q.left) :
    Q.rearrangement x = x := by
  simp [rearrangement, hx]

lemma rearrangement_of_upper_lt {x : ℝ} (hx : Q.upper < x) :
    Q.rearrangement x =
      Q.quantile ⟨Q.upper, Q.h_left_upper, le_rfl⟩ +
        (x - Q.upper) := by
  have hxLeft : ¬x < Q.left :=
    not_lt_of_ge (Q.h_left_upper.trans hx.le)
  simp [rearrangement, hxLeft, not_le_of_gt hx]

/-- Target coordinate reached by the upper endpoint of the compact
quantile interval. -/
def upperQuantile : ℝ :=
  Q.quantile ⟨Q.upper, Q.h_left_upper, le_rfl⟩

lemma upper_le_upperQuantile : Q.upper ≤ Q.upperQuantile := by
  exact Q.self_le_quantile
    ⟨Q.upper, Q.h_left_upper, le_rfl⟩

/-- The global identity/quantile/affine extension is expansive on all of
`ℝ`, not just on its compact middle interval. -/
theorem rearrangement_expansive {x y : ℝ} (hxy : x ≤ y) :
    y - x ≤ Q.rearrangement y - Q.rearrangement x := by
  by_cases hyLeft : y < Q.left
  · have hxLeft : x < Q.left := hxy.trans_lt hyLeft
    rw [Q.rearrangement_of_lt_left hxLeft,
      Q.rearrangement_of_lt_left hyLeft]
  · have hyLower : Q.left ≤ y := le_of_not_gt hyLeft
    by_cases hxLeft : x < Q.left
    · rw [Q.rearrangement_of_lt_left hxLeft]
      by_cases hyUpper : y ≤ Q.upper
      · have hyMem : y ∈ Icc Q.left Q.upper := ⟨hyLower, hyUpper⟩
        rw [Q.rearrangement_of_mem hyMem]
        linarith [Q.self_le_quantile
          (⟨y, hyMem⟩ : Icc Q.left Q.upper)]
      · have hyUpper' : Q.upper < y := lt_of_not_ge hyUpper
        rw [Q.rearrangement_of_upper_lt hyUpper']
        linarith [Q.self_le_quantile
          (⟨Q.upper, Q.h_left_upper, le_rfl⟩ :
            Icc Q.left Q.upper)]
    · have hxLower : Q.left ≤ x := le_of_not_gt hxLeft
      by_cases hxUpper : x ≤ Q.upper
      · have hxMem : x ∈ Icc Q.left Q.upper := ⟨hxLower, hxUpper⟩
        rw [Q.rearrangement_of_mem hxMem]
        by_cases hyUpper : y ≤ Q.upper
        · have hyMem : y ∈ Icc Q.left Q.upper := ⟨hyLower, hyUpper⟩
          rw [Q.rearrangement_of_mem hyMem]
          exact Q.quantile_expansive
            (show (⟨x, hxMem⟩ : Icc Q.left Q.upper) ≤
                ⟨y, hyMem⟩ from hxy)
        · have hyUpper' : Q.upper < y := lt_of_not_ge hyUpper
          rw [Q.rearrangement_of_upper_lt hyUpper']
          have hmiddle := Q.quantile_expansive
            (show (⟨x, hxMem⟩ : Icc Q.left Q.upper) ≤
                ⟨Q.upper, Q.h_left_upper, le_rfl⟩ from hxUpper)
          linarith
      · have hxUpper' : Q.upper < x := lt_of_not_ge hxUpper
        have hyUpper' : Q.upper < y := hxUpper'.trans_le hxy
        rw [Q.rearrangement_of_upper_lt hxUpper',
          Q.rearrangement_of_upper_lt hyUpper']
        linarith

theorem strictMono_rearrangement : StrictMono Q.rearrangement := by
  intro x y hxy
  have hexpansive := Q.rearrangement_expansive hxy.le
  linarith

/-- Generalized inverse of the globally extended rearrangement.  Before
the upper quantile it is the cumulative-volume coordinate; afterwards it
is the inverse of the affine slope-one continuation. -/
def extendedInverseCoordinate (t : ℝ) : ℝ :=
  if t ≤ Q.upperQuantile then Q.inverseCoordinate t
  else Q.upper + (t - Q.upperQuantile)

lemma left_le_extendedInverseCoordinate {t : ℝ} (ht : Q.left ≤ t) :
    Q.left ≤ Q.extendedInverseCoordinate t := by
  by_cases hbranch : t ≤ Q.upperQuantile
  · rw [extendedInverseCoordinate, if_pos hbranch]
    unfold inverseCoordinate
    linarith [Q.F_nonneg_of_left_le ht]
  · rw [extendedInverseCoordinate, if_neg hbranch]
    have hgap : 0 < t - Q.upperQuantile :=
      sub_pos.mpr (lt_of_not_ge hbranch)
    linarith [Q.h_left_upper]

lemma extendedInverseCoordinate_le {t : ℝ} (ht : Q.left ≤ t) :
    Q.extendedInverseCoordinate t ≤ t := by
  by_cases hbranch : t ≤ Q.upperQuantile
  · rw [extendedInverseCoordinate, if_pos hbranch]
    exact Q.inverseCoordinate_le ht
  · rw [extendedInverseCoordinate, if_neg hbranch]
    linarith [Q.upper_le_upperQuantile]

lemma extendedInverseCoordinate_mem_centeredRootInterval
    (center : ℝ) (hleft : Q.left = center - 1)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Q.extendedInverseCoordinate (t + center) ∈
      Icc (center - 1) (center + 1) := by
  have htLeft : Q.left ≤ t + center := by
    rw [hleft]
    linarith [ht.1]
  constructor
  · rw [← hleft]
    exact Q.left_le_extendedInverseCoordinate htLeft
  · exact (Q.extendedInverseCoordinate_le htLeft).trans (by
      linarith [ht.2])

/-- The extended quantile is Borel measurable. -/
theorem measurable_rearrangement : Measurable Q.rearrangement := by
  let p : ℝ → Icc Q.left Q.upper :=
    projIcc Q.left Q.upper Q.h_left_upper
  have hp : Measurable p := continuous_projIcc.measurable
  have hquantile : Measurable Q.quantile :=
    Q.monotone_quantile.measurable
  let right : ℝ → ℝ := fun x ↦
    Q.quantile ⟨Q.upper, Q.h_left_upper, le_rfl⟩ +
      (x - Q.upper)
  have hright : Measurable right := by
    exact measurable_const.add (measurable_id.sub measurable_const)
  have hrearrangement : Q.rearrangement =
      (Iio Q.left).piecewise id
        ((Iic Q.upper).piecewise
          (fun x ↦ Q.quantile (p x)) right) := by
    funext x
    by_cases hxLeft : x < Q.left
    · simp [rearrangement, hxLeft, Set.piecewise]
    · have hxLower : Q.left ≤ x := le_of_not_gt hxLeft
      by_cases hxUpper : x ≤ Q.upper
      · have hx : x ∈ Icc Q.left Q.upper := ⟨hxLower, hxUpper⟩
        have hxNotIio : x ∉ Iio Q.left := hxLeft
        have hxIic : x ∈ Iic Q.upper := hxUpper
        rw [Q.rearrangement_of_mem hx]
        simp only [Set.piecewise, hxNotIio, hxIic, if_false, if_true]
        exact congrArg Q.quantile
          (projIcc_of_mem Q.h_left_upper hx).symm
      · have hxUpper' : Q.upper < x := lt_of_not_ge hxUpper
        rw [Q.rearrangement_of_upper_lt hxUpper']
        simp [Set.piecewise, hxLeft, hxUpper, right]
  rw [hrearrangement]
  exact Measurable.piecewise measurableSet_Iio measurable_id
    (Measurable.piecewise measurableSet_Iic
      (hquantile.comp hp) hright)

/-- Translate the target output of the rearrangement back by its center.
This lets the concrete trial measures remain at their natural locations
`0` and `2√2`, while the empirical roots remain in `[-1,1]`. -/
def centeredRearrangement (center x : ℝ) : ℝ :=
  Q.rearrangement x - center

theorem measurable_centeredRearrangement (center : ℝ) :
    Measurable (Q.centeredRearrangement center) :=
  Q.measurable_rearrangement.sub measurable_const

theorem strictMono_centeredRearrangement (center : ℝ) :
    StrictMono (Q.centeredRearrangement center) := by
  intro x y hxy
  unfold centeredRearrangement
  exact sub_lt_sub_right (Q.strictMono_rearrangement hxy) center

/-- A centered pushforward gives a finite empirical root set mass zero as
soon as every possible singleton fiber is source-null.  Global strict
monotonicity makes the entire preimage finite. -/
theorem map_centeredRearrangement_rootSet_eq_zero
    (f : Polynomial ℝ) (ν : Measure ℝ) (center : ℝ)
    (hsingleton : ∀ s,
      Q.centeredRearrangement center s ∈ rootSet f → ν {s} = 0) :
    (Measure.map (Q.centeredRearrangement center) ν) (rootSet f) = 0 := by
  rw [Measure.map_apply (Q.measurable_centeredRearrangement center)
    (rootSet_finite f).measurableSet]
  have hinjective : Set.InjOn (Q.centeredRearrangement center)
      ((Q.centeredRearrangement center) ⁻¹' rootSet f) :=
    (Q.strictMono_centeredRearrangement center).injective.injOn
  have hfinite :
      ((Q.centeredRearrangement center) ⁻¹' rootSet f).Finite :=
    Set.Finite.preimage hinjective (rootSet_finite f)
  apply (measure_null_iff_singleton hfinite.countable).mpr
  intro s hs
  exact hsingleton s hs

/-- On its source interval, the rearrangement inherits strict injectivity
from the least-level quantile. -/
lemma rearrangement_injOn_Icc :
    Set.InjOn Q.rearrangement (Icc Q.left Q.upper) := by
  intro x hx y hy hxy
  rw [Q.rearrangement_of_mem hx, Q.rearrangement_of_mem hy] at hxy
  have hsubtype : (⟨x, hx⟩ : Icc Q.left Q.upper) = ⟨y, hy⟩ :=
    Q.strictMono_quantile.injective hxy
  exact congrArg Subtype.val hsubtype

/-- Every preimage of an empirical root lies in the half-open source
interval.  The strict upper gap excludes the identity branch to the right
and also the upper endpoint itself. -/
lemma rearrangement_preimage_rootSet_subset_Ico
    (f : Polynomial ℝ) (hf : IsAdmissible f)
    (hleft : Q.left = -1) (hupper : 1 < Q.upper) :
    Q.rearrangement ⁻¹' rootSet f ⊆ Ico Q.left Q.upper := by
  intro x hx
  have hroot : Q.rearrangement x ∈ Icc (-1 : ℝ) 1 :=
    hf.root_mem_Icc (mem_rootSet_iff.mp hx)
  constructor
  · by_contra hxLeft
    have hlt : x < Q.left := lt_of_not_ge hxLeft
    rw [Q.rearrangement_of_lt_left hlt] at hroot
    rw [hleft] at hlt
    exact (not_lt_of_ge hroot.1) hlt
  · by_contra hxUpper
    have hge : Q.upper ≤ x := le_of_not_gt hxUpper
    rcases hge.eq_or_lt with heq | hlt
    · subst x
      have hmem : Q.upper ∈ Icc Q.left Q.upper :=
        ⟨Q.h_left_upper, le_rfl⟩
      rw [Q.rearrangement_of_mem hmem] at hroot
      have hself := Q.self_le_quantile
        (⟨Q.upper, hmem⟩ : Icc Q.left Q.upper)
      linarith [hroot.2, hupper, hself]
    · rw [Q.rearrangement_of_upper_lt hlt] at hroot
      have hmem : Q.upper ∈ Icc Q.left Q.upper :=
        ⟨Q.h_left_upper, le_rfl⟩
      have hself := Q.self_le_quantile
        (⟨Q.upper, hmem⟩ : Icc Q.left Q.upper)
      linarith [hroot.2, hupper, hself]

/-- A source measure with no atoms on the source interval pushes no mass
onto the finite empirical root set. -/
theorem map_rearrangement_rootSet_eq_zero
    (f : Polynomial ℝ) (hf : IsAdmissible f) (ν : Measure ℝ)
    (hleft : Q.left = -1) (hupper : 1 < Q.upper)
    (hsingleton : ∀ s ∈ Ico Q.left Q.upper, ν {s} = 0) :
    (Measure.map Q.rearrangement ν) (rootSet f) = 0 := by
  rw [Measure.map_apply Q.measurable_rearrangement
    (rootSet_finite f).measurableSet]
  have hsubset := Q.rearrangement_preimage_rootSet_subset_Ico
    f hf hleft hupper
  have hinjective : Set.InjOn Q.rearrangement
      (Q.rearrangement ⁻¹' rootSet f) := by
    intro x hx y hy hxy
    apply Q.rearrangement_injOn_Icc
    · have hxIco := hsubset hx
      exact ⟨hxIco.1, hxIco.2.le⟩
    · have hyIco := hsubset hy
      exact ⟨hyIco.1, hyIco.2.le⟩
    · exact hxy
  have hfinite : (Q.rearrangement ⁻¹' rootSet f).Finite :=
    Set.Finite.preimage hinjective (rootSet_finite f)
  apply (measure_null_iff_singleton hfinite.countable).mpr
  intro x hx
  exact hsingleton x (hsubset hx)

lemma rearrangement_mem_closure_of_volumeCumulative
    (E : Set ℝ) (hF : Q.F = volumeCumulative E Q.left)
    {x : ℝ} (hx : x ∈ Ioc Q.left Q.upper) :
    Q.rearrangement x ∈ closure E := by
  have hxIcc : x ∈ Icc Q.left Q.upper := ⟨hx.1.le, hx.2⟩
  rw [Q.rearrangement_of_mem hxIcc]
  exact Q.quantile_mem_closure_of_volumeCumulative E hF
    ⟨x, hxIcc⟩ hx.1

lemma rearrangement_mem_of_volumeCumulative_of_isClosed
    (E : Set ℝ) (hF : Q.F = volumeCumulative E Q.left)
    (hE : IsClosed E) {x : ℝ} (hx : x ∈ Ioc Q.left Q.upper) :
    Q.rearrangement x ∈ E := by
  rw [← hE.closure_eq]
  exact Q.rearrangement_mem_closure_of_volumeCumulative E hF hx

/-- If the source measure is supported either at already-good fixed points
to the left or on the quantile interval, then its pushforward is supported
on the closed target set. -/
theorem ae_map_rearrangement_mem_of_volumeCumulative_of_isClosed
    (E : Set ℝ) (hF : Q.F = volumeCumulative E Q.left)
    (hE : IsClosed E) (ν : Measure ℝ)
    (hsupport : ∀ᵐ s ∂ν,
      (s < Q.left ∧ s ∈ E) ∨ s ∈ Ioc Q.left Q.upper) :
    ∀ᵐ x ∂(Measure.map Q.rearrangement ν), x ∈ E := by
  apply (ae_map_iff Q.measurable_rearrangement.aemeasurable
    hE.measurableSet).mpr
  filter_upwards [hsupport] with s hs
  rcases hs with hsFixed | hsInterval
  · rw [Q.rearrangement_of_lt_left hsFixed.1]
    exact hsFixed.2
  · exact Q.rearrangement_mem_of_volumeCumulative_of_isClosed
      E hF hE hsInterval

/-- Centered version of closed-target support.  The middle source interval
is rearranged into `sourceTarget`, then translated into `target`; fixed
points to the left are assumed good directly. -/
theorem ae_map_centeredRearrangement_mem_of_volumeCumulative
    (sourceTarget target : Set ℝ) (center : ℝ)
    (hF : Q.F = volumeCumulative sourceTarget Q.left)
    (hsourceClosed : IsClosed sourceTarget)
    (htargetClosed : IsClosed target)
    (htranslate : ∀ x ∈ sourceTarget, x - center ∈ target)
    (ν : Measure ℝ)
    (hsupport : ∀ᵐ s ∂ν,
      (s < Q.left ∧ Q.centeredRearrangement center s ∈ target) ∨
        s ∈ Ioc Q.left Q.upper) :
    ∀ᵐ x ∂(Measure.map (Q.centeredRearrangement center) ν),
      x ∈ target := by
  apply (ae_map_iff
    (Q.measurable_centeredRearrangement center).aemeasurable
    htargetClosed.measurableSet).mpr
  filter_upwards [hsupport] with s hs
  rcases hs with hsFixed | hsInterval
  · exact hsFixed.2
  · apply htranslate (Q.rearrangement s)
    exact Q.rearrangement_mem_of_volumeCumulative_of_isClosed
      sourceTarget hF hsourceClosed hsInterval

/-- Distance estimate for a source point in the quantile interval. -/
theorem abs_inverseCoordinate_sub_le_abs_sub_rearrangement
    {t s : ℝ} (hs : s ∈ Icc Q.left Q.upper) :
    |Q.inverseCoordinate t - s| ≤ |t - Q.rearrangement s| := by
  rw [Q.rearrangement_of_mem hs]
  let ss : Icc Q.left Q.upper := ⟨s, hs⟩
  have hFs : Q.F (Q.quantile ss) = s - Q.left := Q.F_quantile ss
  have hs0 : Q.inverseCoordinate t = Q.left + Q.F t := rfl
  rcases lt_trichotomy s (Q.inverseCoordinate t) with hleft | heq | hright
  · have hqt : Q.quantile ss < t := by
      apply lt_of_not_ge
      intro htq
      have hFmono := Q.hmono htq
      rw [hFs] at hFmono
      unfold inverseCoordinate at hleft
      linarith
    have hinc := Q.hincrement hqt.le
    rw [hFs] at hinc
    rw [abs_of_nonneg (sub_nonneg.mpr hleft.le),
      abs_of_nonneg (sub_nonneg.mpr hqt.le)]
    rw [hs0]
    linarith
  · subst s
    simp
  · have htq : t < Q.quantile ss := by
      apply lt_of_not_ge
      intro hqt
      have hFmono := Q.hmono hqt
      rw [hFs] at hFmono
      unfold inverseCoordinate at hright
      linarith
    have hinc := Q.hincrement htq.le
    rw [hFs] at hinc
    rw [abs_of_nonpos (sub_nonpos.mpr hright.le),
      abs_of_nonpos (sub_nonpos.mpr htq.le)]
    rw [hs0]
    linarith

/-- Distance estimate for a fixed source point to the left of the quantile
interval (the role played by Tao's atom at zero). -/
theorem abs_inverseCoordinate_sub_le_abs_sub_rearrangement_of_lt_left
    {t s : ℝ} (ht : t ∈ Icc Q.left Q.upper)
    (hs : s < Q.left) :
    |Q.inverseCoordinate t - s| ≤ |t - Q.rearrangement s| := by
  rw [Q.rearrangement_of_lt_left hs]
  have hs0Lower : s ≤ Q.inverseCoordinate t := by
    have := (Q.inverseCoordinate_mem_Icc ht).1
    linarith
  have hs0t := Q.inverseCoordinate_le ht.1
  rw [abs_of_nonneg (sub_nonneg.mpr hs0Lower),
    abs_of_nonneg (sub_nonneg.mpr (hs0Lower.trans hs0t))]
  linarith

/-- The extended generalized inverse gives Tao's distance comparison for
every target point to the right of `left`, including points beyond the
compact quantile endpoint. -/
theorem abs_extendedInverseCoordinate_sub_le_abs_sub_rearrangement
    {t s : ℝ} (ht : Q.left ≤ t)
    (hs : s < Q.left ∨ s ∈ Icc Q.left Q.upper) :
    |Q.extendedInverseCoordinate t - s| ≤
      |t - Q.rearrangement s| := by
  by_cases hbranch : t ≤ Q.upperQuantile
  · rcases hs with hsLeft | hsInterval
    · have hsInv : s ≤ Q.extendedInverseCoordinate t :=
        hsLeft.le.trans (Q.left_le_extendedInverseCoordinate ht)
      have hsTarget : s ≤ t := hsLeft.le.trans ht
      rw [Q.rearrangement_of_lt_left hsLeft,
        abs_of_nonneg (sub_nonneg.mpr hsInv),
        abs_of_nonneg (sub_nonneg.mpr hsTarget)]
      exact sub_le_sub_right (Q.extendedInverseCoordinate_le ht) s
    · rw [extendedInverseCoordinate, if_pos hbranch]
      exact Q.abs_inverseCoordinate_sub_le_abs_sub_rearrangement
        hsInterval
  · have hqT : Q.upperQuantile < t := lt_of_not_ge hbranch
    have hsUpper : s ≤ Q.upper := by
      rcases hs with hsLeft | hsInterval
      · exact hsLeft.le.trans Q.h_left_upper
      · exact hsInterval.2
    have hgap : Q.upper - s ≤
        Q.upperQuantile - Q.rearrangement s := by
      rcases hs with hsLeft | hsInterval
      · rw [Q.rearrangement_of_lt_left hsLeft]
        linarith [Q.upper_le_upperQuantile]
      · rw [Q.rearrangement_of_mem hsInterval]
        exact Q.quantile_expansive
          (show (⟨s, hsInterval⟩ : Icc Q.left Q.upper) ≤
              ⟨Q.upper, Q.h_left_upper, le_rfl⟩ from hsInterval.2)
    have hsInv : s ≤ Q.extendedInverseCoordinate t := by
      rw [extendedInverseCoordinate, if_neg hbranch]
      linarith
    have hsTarget : Q.rearrangement s ≤ t := by
      linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hsInv),
      abs_of_nonneg (sub_nonneg.mpr hsTarget),
      extendedInverseCoordinate, if_neg hbranch]
    linarith

/-- Potential comparison using the affine right extension and a translated
target.  Unlike the compact-interval version, the target point may lie to
the right of `Q.upperQuantile`. -/
theorem taoTrialMeasurePotential_map_centeredRearrangement_le
    (ν : Measure ℝ) (center : ℝ) {t : ℝ}
    (ht : Q.left ≤ t + center)
    (hsupport : ∀ᵐ s ∂ν,
      s < Q.left ∨ s ∈ Icc Q.left Q.upper)
    (hsingleton : ν {Q.extendedInverseCoordinate (t + center)} = 0)
    (hsource : Integrable
      (fun s ↦ Real.log |Q.extendedInverseCoordinate (t + center) - s|) ν)
    (htarget : Integrable
      (fun s ↦ Real.log |t - Q.centeredRearrangement center s|) ν) :
    taoTrialMeasurePotential
        (Measure.map (Q.centeredRearrangement center) ν) t ≤
      taoTrialMeasurePotential ν
        (Q.extendedInverseCoordinate (t + center)) := by
  have hne : ∀ᵐ s ∂ν,
      s ≠ Q.extendedInverseCoordinate (t + center) := by
    rw [ae_iff]
    simpa only [not_ne_iff] using! hsingleton
  have hpoint : ∀ᵐ s ∂ν,
      Real.log |Q.extendedInverseCoordinate (t + center) - s| ≤
        Real.log |t - Q.centeredRearrangement center s| := by
    filter_upwards [hsupport, hne] with s hs hsne
    have hdistance :=
      Q.abs_extendedInverseCoordinate_sub_le_abs_sub_rearrangement
        ht hs
    have hdistanceCentered :
        |Q.extendedInverseCoordinate (t + center) - s| ≤
          |t - Q.centeredRearrangement center s| := by
      have heq :
          t + center - Q.rearrangement s =
            t - Q.centeredRearrangement center s := by
        unfold centeredRearrangement
        ring
      rw [← heq]
      exact hdistance
    exact Real.log_le_log
      (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hsne)))
      hdistanceCentered
  have hkernelMeasurable : Measurable
      (fun y : ℝ ↦ Real.log |t - y|) :=
    Real.measurable_log.comp
      (_root_.continuous_abs.measurable.comp
        (measurable_const.sub measurable_id))
  unfold taoTrialMeasurePotential
  rw [integral_map
    (Q.measurable_centeredRearrangement center).aemeasurable
    hkernelMeasurable.aestronglyMeasurable]
  exact neg_le_neg (integral_mono_ae hsource htarget hpoint)

/-- On a finite source measure, source-kernel integrability and the
expansive distance lower bound imply target-kernel integrability whenever
the centered rearrangement lands in the bounded closed polynomial target.
-/
theorem integrable_log_sub_centeredRearrangement
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (f : Polynomial ℝ) (hf : IsAdmissible f) (center : ℝ)
    {t : ℝ} (htRoot : t ∈ Icc (-1 : ℝ) 1)
    (htLeft : Q.left ≤ t + center)
    (hsupport : ∀ᵐ s ∂ν,
      s < Q.left ∨ s ∈ Icc Q.left Q.upper)
    (hsingleton : ν {Q.extendedInverseCoordinate (t + center)} = 0)
    (hsource : Integrable
      (fun s ↦ Real.log |Q.extendedInverseCoordinate (t + center) - s|) ν)
    (htargetMem : ∀ᵐ s ∂ν,
      Q.centeredRearrangement center s ∈ closedUnitSublevelSet f) :
    Integrable
      (fun s ↦ Real.log |t - Q.centeredRearrangement center s|) ν := by
  have htargetMeasurable : Measurable
      (fun s ↦ Real.log |t - Q.centeredRearrangement center s|) :=
    Real.measurable_log.comp
      (_root_.continuous_abs.measurable.comp
        (measurable_const.sub
          (Q.measurable_centeredRearrangement center)))
  have hmajorant : Integrable
      (fun s ↦ abs (Real.log
        |Q.extendedInverseCoordinate (t + center) - s|) + 3) ν := by
    simpa only [Real.norm_eq_abs] using!
      hsource.norm.add (integrable_const (3 : ℝ))
  apply Integrable.mono' hmajorant
    htargetMeasurable.aestronglyMeasurable
  have hne : ∀ᵐ s ∂ν,
      s ≠ Q.extendedInverseCoordinate (t + center) := by
    rw [ae_iff]
    simpa only [not_ne_iff] using! hsingleton
  filter_upwards [hsupport, hne, htargetMem] with s hs hsne hsTarget
  have hdistance :=
    Q.abs_extendedInverseCoordinate_sub_le_abs_sub_rearrangement
      htLeft hs
  have heq :
      t + center - Q.rearrangement s =
        t - Q.centeredRearrangement center s := by
    unfold centeredRearrangement
    ring
  rw [heq] at hdistance
  have hlogLower :
      Real.log |Q.extendedInverseCoordinate (t + center) - s| ≤
        Real.log |t - Q.centeredRearrangement center s| :=
    Real.log_le_log
      (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hsne))) hdistance
  have htargetBounds := closedUnitSublevelSet_subset_Icc hf hsTarget
  have hdistanceUpper :
      |t - Q.centeredRearrangement center s| ≤ 3 := by
    rw [abs_le]
    constructor <;> linarith [htRoot.1, htRoot.2,
      htargetBounds.1, htargetBounds.2]
  have hlogUpper :
      Real.log |t - Q.centeredRearrangement center s| ≤ 3 :=
    (Real.log_le_self (abs_nonneg _)).trans hdistanceUpper
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have hsourceAbs := neg_abs_le
      (Real.log |Q.extendedInverseCoordinate (t + center) - s|)
    linarith [abs_nonneg
      (Real.log |Q.extendedInverseCoordinate (t + center) - s|)]
  · linarith [abs_nonneg
      (Real.log |Q.extendedInverseCoordinate (t + center) - s|)]

/-- Centered arbitrary-measure version of Tao's affine-extended quantile
contradiction.  Trial negativity is used on the translated root interval,
while empirical duality remains on the original roots in `[-1,1]`. -/
theorem not_taoEmpiricalPotential_nonneg_ae_of_centeredQuantile_pushforward
    (f : Polynomial ℝ) (hf : IsAdmissible f) (ν : Measure ℝ)
    (center : ℝ) (hleft : Q.left = center - 1)
    (hsupport : ∀ᵐ s ∂ν,
      s < Q.left ∨ s ∈ Icc Q.left Q.upper)
    (hsingleton : ∀ s ∈ Icc (center - 1) (center + 1),
      ν {s} = 0)
    (hsource : ∀ t ∈ Icc (-1 : ℝ) 1,
      Integrable
        (fun s ↦ Real.log |Q.extendedInverseCoordinate (t + center) - s|) ν)
    (htarget : ∀ t ∈ Icc (-1 : ℝ) 1,
      Integrable
        (fun s ↦ Real.log |t - Q.centeredRearrangement center s|) ν)
    (htrial : ∀ s ∈ Icc (center - 1) (center + 1),
      taoTrialMeasurePotential ν s < 0) :
    ¬ ∀ᵐ x ∂(Measure.map (Q.centeredRearrangement center) ν),
      0 ≤ taoEmpiricalPotential f hf x := by
  have htLeft : ∀ t ∈ Icc (-1 : ℝ) 1,
      Q.left ≤ t + center := by
    intro t ht
    rw [hleft]
    linarith [ht.1]
  have hs₀root : ∀ t ∈ Icc (-1 : ℝ) 1,
      Q.extendedInverseCoordinate (t + center) ∈
        Icc (center - 1) (center + 1) := by
    intro t ht
    exact Q.extendedInverseCoordinate_mem_centeredRootInterval
      center hleft ht
  have hpushed : ∀ t ∈ Icc (-1 : ℝ) 1,
      taoTrialMeasurePotential
          (Measure.map (Q.centeredRearrangement center) ν) t < 0 := by
    intro t ht
    exact (Q.taoTrialMeasurePotential_map_centeredRearrangement_le
      ν center (htLeft t ht) hsupport
      (hsingleton _ (hs₀root t ht))
      (hsource t ht) (htarget t ht)).trans_lt
        (htrial _ (hs₀root t ht))
  have hkernel : ∀ r ∈ f.roots,
      Integrable (fun x ↦ Real.log |x - r|)
        (Measure.map (Q.centeredRearrangement center) ν) := by
    intro r hr
    have hrIcc : r ∈ Icc (-1 : ℝ) 1 := hf.root_mem_Icc hr
    have hmeasurable : Measurable (fun x : ℝ ↦ Real.log |x - r|) :=
      Real.measurable_log.comp
        (_root_.continuous_abs.measurable.comp
          (measurable_id.sub measurable_const))
    apply (integrable_map_measure
      hmeasurable.aestronglyMeasurable
      (Q.measurable_centeredRearrangement center).aemeasurable).mpr
    simpa only [Function.comp_apply, abs_sub_comm] using!
      htarget r hrIcc
  exact not_taoEmpiricalPotential_nonneg_ae_of_measure_trial
    f hf (Measure.map (Q.centeredRearrangement center) ν)
      hkernel hpushed

/-- Full soundness bridge for the centered affine quantile pushforward.
It combines target support, finite-root nullity, closed-target
nonnegativity, and the measure-theoretic duality contradiction. -/
theorem false_of_centeredQuantile_pushforward_closedUnitSublevelSet
    (f : Polynomial ℝ) (hf : IsAdmissible f) (ν : Measure ℝ)
    (center : ℝ) (sourceTarget : Set ℝ)
    (hleft : Q.left = center - 1)
    (hF : Q.F = volumeCumulative sourceTarget Q.left)
    (hsourceClosed : IsClosed sourceTarget)
    (htranslate : ∀ x ∈ sourceTarget,
      x - center ∈ closedUnitSublevelSet f)
    (hsupport : ∀ᵐ s ∂ν,
      (s < Q.left ∧
          Q.centeredRearrangement center s ∈ closedUnitSublevelSet f) ∨
        s ∈ Ioc Q.left Q.upper)
    (hsingleton : ∀ s ∈ Icc (center - 1) (center + 1),
      ν {s} = 0)
    (hfiberSingleton : ∀ s,
      Q.centeredRearrangement center s ∈ rootSet f → ν {s} = 0)
    (hsource : ∀ t ∈ Icc (-1 : ℝ) 1,
      Integrable
        (fun s ↦ Real.log |Q.extendedInverseCoordinate (t + center) - s|) ν)
    (htarget : ∀ t ∈ Icc (-1 : ℝ) 1,
      Integrable
        (fun s ↦ Real.log |t - Q.centeredRearrangement center s|) ν)
    (htrial : ∀ s ∈ Icc (center - 1) (center + 1),
      taoTrialMeasurePotential ν s < 0) :
    False := by
  have hbasicSupport : ∀ᵐ s ∂ν,
      s < Q.left ∨ s ∈ Icc Q.left Q.upper := by
    filter_upwards [hsupport] with s hs
    rcases hs with hsFixed | hsInterval
    · exact Or.inl hsFixed.1
    · exact Or.inr ⟨hsInterval.1.le, hsInterval.2⟩
  have hpushedMem :
      ∀ᵐ x ∂(Measure.map (Q.centeredRearrangement center) ν),
        x ∈ closedUnitSublevelSet f :=
    Q.ae_map_centeredRearrangement_mem_of_volumeCumulative
      sourceTarget (closedUnitSublevelSet f) center hF hsourceClosed
      (isClosed_closedUnitSublevelSet f) htranslate ν hsupport
  have hpushedRoots :
      (Measure.map (Q.centeredRearrangement center) ν) (rootSet f) = 0 :=
    Q.map_centeredRearrangement_rootSet_eq_zero
      f ν center hfiberSingleton
  have hpushedNonnegOn :
      ∀ᵐ x ∂(Measure.map (Q.centeredRearrangement center) ν),
        x ∈ closedUnitSublevelSet f →
          0 ≤ taoEmpiricalPotential f hf x :=
    ae_taoEmpiricalPotential_nonneg_on_closedUnitSublevelSet
      hf (Measure.map (Q.centeredRearrangement center) ν) hpushedRoots
  have hpushedNonneg :
      ∀ᵐ x ∂(Measure.map (Q.centeredRearrangement center) ν),
        0 ≤ taoEmpiricalPotential f hf x := by
    filter_upwards [hpushedMem, hpushedNonnegOn] with x hx hnonneg
    exact hnonneg hx
  exact
    (Q.not_taoEmpiricalPotential_nonneg_ae_of_centeredQuantile_pushforward
      f hf ν center hleft hbasicSupport hsingleton
      hsource htarget htrial) hpushedNonneg

/-- Potential comparison for an arbitrary source trial measure.  A
singleton-null hypothesis removes the sole point where Mathlib's convention
`Real.log 0 = 0` differs from the extended-real logarithmic kernel. -/
theorem taoTrialMeasurePotential_map_rearrangement_le
    (ν : Measure ℝ) (hφ : AEMeasurable Q.rearrangement ν)
    {t : ℝ} (ht : t ∈ Icc Q.left Q.upper)
    (hsupport : ∀ᵐ s ∂ν,
      s < Q.left ∨ s ∈ Icc Q.left Q.upper)
    (hsingleton : ν {Q.inverseCoordinate t} = 0)
    (hsource : Integrable
      (fun s ↦ Real.log |Q.inverseCoordinate t - s|) ν)
    (htarget : Integrable
      (fun s ↦ Real.log |t - Q.rearrangement s|) ν) :
    taoTrialMeasurePotential (Measure.map Q.rearrangement ν) t ≤
      taoTrialMeasurePotential ν (Q.inverseCoordinate t) := by
  have hne : ∀ᵐ s ∂ν, s ≠ Q.inverseCoordinate t := by
    rw [ae_iff]
    simpa only [not_ne_iff] using! hsingleton
  have hpoint : ∀ᵐ s ∂ν,
      Real.log |Q.inverseCoordinate t - s| ≤
        Real.log |t - Q.rearrangement s| := by
    filter_upwards [hsupport, hne] with s hs hsne
    have hdist : |Q.inverseCoordinate t - s| ≤
        |t - Q.rearrangement s| := by
      rcases hs with hsLeft | hsInterval
      · exact Q.abs_inverseCoordinate_sub_le_abs_sub_rearrangement_of_lt_left
          ht hsLeft
      · exact Q.abs_inverseCoordinate_sub_le_abs_sub_rearrangement hsInterval
    exact Real.log_le_log
      (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hsne))) hdist
  have hkernelMeasurable : Measurable
      (fun y : ℝ ↦ Real.log |t - y|) :=
    Real.measurable_log.comp
      (_root_.continuous_abs.measurable.comp
        (measurable_const.sub measurable_id))
  unfold taoTrialMeasurePotential
  rw [integral_map hφ hkernelMeasurable.aestronglyMeasurable]
  exact neg_le_neg (integral_mono_ae hsource htarget hpoint)

/-- General finite-atomic separator.  Trial atoms may occur anywhere in the
quantile interval; only collision with the generalized-inverse coordinate
must be excluded explicitly. -/
theorem rootInterval_separator_general
    {ι : Type*} [Fintype ι] (w a : ι → ℝ)
    (hleft : Q.left = -1) (hupper : 1 ≤ Q.upper)
    (hlocation : ∀ i, 0 < w i →
      a i < Q.left ∨ a i ∈ Icc Q.left Q.upper)
    (hnocollision : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ i, 0 < w i →
      a i ≠ Q.inverseCoordinate t) :
    ∀ t ∈ Icc (-1 : ℝ) 1,
      ∃ s₀ ∈ Icc (-1 : ℝ) 1, ∀ i, 0 < w i →
        0 < |s₀ - a i| ∧
          |s₀ - a i| ≤ |t - Q.rearrangement (a i)| := by
  intro t ht
  have htQ : t ∈ Icc Q.left Q.upper := by
    constructor
    · rw [hleft]
      exact ht.1
    · exact ht.2.trans hupper
  let s₀ := Q.inverseCoordinate t
  have hs₀Q : s₀ ∈ Icc Q.left Q.upper := Q.inverseCoordinate_mem_Icc htQ
  have hs₀t : s₀ ≤ t := Q.inverseCoordinate_le htQ.1
  have hs₀root : s₀ ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · rw [← hleft]
      exact hs₀Q.1
    · exact hs₀t.trans ht.2
  refine ⟨s₀, hs₀root, ?_⟩
  intro i hwi
  have hne : s₀ ≠ a i := Ne.symm (hnocollision t ht i hwi)
  refine ⟨abs_pos.mpr (sub_ne_zero.mpr hne), ?_⟩
  rcases hlocation i hwi with hiLeft | hiInterval
  · exact Q.abs_inverseCoordinate_sub_le_abs_sub_rearrangement_of_lt_left
      htQ hiLeft
  · exact Q.abs_inverseCoordinate_sub_le_abs_sub_rearrangement hiInterval

/-- Arbitrary-measure version of Tao's expansive-quantile contradiction.
This is the form used by the interval-density trials in Cases 2 and 3. -/
theorem not_taoEmpiricalPotential_nonneg_ae_of_quantile_pushforward
    (f : Polynomial ℝ) (hf : IsAdmissible f) (ν : Measure ℝ)
    (hleft : Q.left = -1) (hupper : 1 ≤ Q.upper)
    (hφ : AEMeasurable Q.rearrangement ν)
    (hsupport : ∀ᵐ s ∂ν,
      s < Q.left ∨ s ∈ Icc Q.left Q.upper)
    (hsingleton : ∀ s ∈ Icc (-1 : ℝ) 1, ν {s} = 0)
    (hsource : ∀ t ∈ Icc (-1 : ℝ) 1,
      Integrable (fun s ↦ Real.log |Q.inverseCoordinate t - s|) ν)
    (htarget : ∀ t ∈ Icc (-1 : ℝ) 1,
      Integrable (fun s ↦ Real.log |t - Q.rearrangement s|) ν)
    (htrial : ∀ s ∈ Icc (-1 : ℝ) 1,
      taoTrialMeasurePotential ν s < 0) :
    ¬ ∀ᵐ x ∂(Measure.map Q.rearrangement ν),
      0 ≤ taoEmpiricalPotential f hf x := by
  have htQ : ∀ t ∈ Icc (-1 : ℝ) 1,
      t ∈ Icc Q.left Q.upper := by
    intro t ht
    constructor
    · rw [hleft]
      exact ht.1
    · exact ht.2.trans hupper
  have hs₀root : ∀ t ∈ Icc (-1 : ℝ) 1,
      Q.inverseCoordinate t ∈ Icc (-1 : ℝ) 1 := by
    intro t ht
    have hs₀Q := Q.inverseCoordinate_mem_Icc (htQ t ht)
    constructor
    · rw [← hleft]
      exact hs₀Q.1
    · exact (Q.inverseCoordinate_le (htQ t ht).1).trans ht.2
  have hpushed : ∀ t ∈ Icc (-1 : ℝ) 1,
      taoTrialMeasurePotential (Measure.map Q.rearrangement ν) t < 0 := by
    intro t ht
    exact (Q.taoTrialMeasurePotential_map_rearrangement_le ν hφ
      (htQ t ht) hsupport (hsingleton _ (hs₀root t ht))
      (hsource t ht) (htarget t ht)).trans_lt
        (htrial _ (hs₀root t ht))
  have hkernel : ∀ r ∈ f.roots,
      Integrable (fun x ↦ Real.log |x - r|)
        (Measure.map Q.rearrangement ν) := by
    intro r hr
    have hrIcc : r ∈ Icc (-1 : ℝ) 1 := hf.root_mem_Icc hr
    have hmeasurable : Measurable (fun x : ℝ ↦ Real.log |x - r|) :=
      Real.measurable_log.comp
        (_root_.continuous_abs.measurable.comp
          (measurable_id.sub measurable_const))
    apply (integrable_map_measure
      hmeasurable.aestronglyMeasurable hφ).mpr
    simpa only [Function.comp_apply, abs_sub_comm] using! htarget r hrIcc
  exact not_taoEmpiricalPotential_nonneg_ae_of_measure_trial
    f hf (Measure.map Q.rearrangement ν) hkernel hpushed

/-- Rigorous closed-target form of the quantile contradiction.  The
half-open singleton-null hypothesis is exactly what interval-density trial
measures provide; it simultaneously removes logarithmic collisions and
shows that the pushed measure gives empirical roots mass zero. -/
theorem false_of_quantile_pushforward_closedUnitSublevelSet
    (f : Polynomial ℝ) (hf : IsAdmissible f) (ν : Measure ℝ)
    (hleft : Q.left = -1) (hupper : 1 < Q.upper)
    (hF : Q.F = volumeCumulative (closedUnitSublevelSet f) Q.left)
    (hsupport : ∀ᵐ s ∂ν,
      (s < Q.left ∧ s ∈ closedUnitSublevelSet f) ∨
        s ∈ Ioc Q.left Q.upper)
    (hsingleton : ∀ s ∈ Ico Q.left Q.upper, ν {s} = 0)
    (hsource : ∀ t ∈ Icc (-1 : ℝ) 1,
      Integrable (fun s ↦ Real.log |Q.inverseCoordinate t - s|) ν)
    (htarget : ∀ t ∈ Icc (-1 : ℝ) 1,
      Integrable (fun s ↦ Real.log |t - Q.rearrangement s|) ν)
    (htrial : ∀ s ∈ Icc (-1 : ℝ) 1,
      taoTrialMeasurePotential ν s < 0) :
    False := by
  have hbasicSupport : ∀ᵐ s ∂ν,
      s < Q.left ∨ s ∈ Icc Q.left Q.upper := by
    filter_upwards [hsupport] with s hs
    rcases hs with hsFixed | hsInterval
    · exact Or.inl hsFixed.1
    · exact Or.inr ⟨hsInterval.1.le, hsInterval.2⟩
  have hrootSingleton : ∀ s ∈ Icc (-1 : ℝ) 1, ν {s} = 0 := by
    intro s hs
    apply hsingleton s
    constructor
    · rw [hleft]
      exact hs.1
    · exact hs.2.trans_lt hupper
  have hpushedMem : ∀ᵐ x ∂(Measure.map Q.rearrangement ν),
      x ∈ closedUnitSublevelSet f :=
    Q.ae_map_rearrangement_mem_of_volumeCumulative_of_isClosed
      (closedUnitSublevelSet f) hF
      (isClosed_closedUnitSublevelSet f) ν hsupport
  have hpushedRoots : (Measure.map Q.rearrangement ν) (rootSet f) = 0 :=
    Q.map_rearrangement_rootSet_eq_zero
      f hf ν hleft hupper hsingleton
  have hpushedNonnegOn : ∀ᵐ x ∂(Measure.map Q.rearrangement ν),
      x ∈ closedUnitSublevelSet f →
        0 ≤ taoEmpiricalPotential f hf x :=
    ae_taoEmpiricalPotential_nonneg_on_closedUnitSublevelSet
      hf (Measure.map Q.rearrangement ν) hpushedRoots
  have hpushedNonneg : ∀ᵐ x ∂(Measure.map Q.rearrangement ν),
      0 ≤ taoEmpiricalPotential f hf x := by
    filter_upwards [hpushedMem, hpushedNonnegOn] with x hx hnonneg
    exact hnonneg hx
  exact (Q.not_taoEmpiricalPotential_nonneg_ae_of_quantile_pushforward
    f hf ν hleft hupper.le Q.measurable_rearrangement.aemeasurable
    hbasicSupport hrootSingleton hsource htarget htrial) hpushedNonneg

/-- The exact separator hypothesis required by
`exists_pushed_trial_atom_taoEmpiricalPotential_neg`.  In Tao's trials the
positive-weight atoms are either fixed to the left of the source interval,
or occur at its upper endpoint.  After translating the root interval to
`[-1,1]`, the upper endpoint lies strictly to the right of `1`. -/
theorem rootInterval_separator
    {ι : Type*} [Fintype ι] (w a : ι → ℝ)
    (hleft : Q.left = -1) (hupper : 1 < Q.upper)
    (hlocation : ∀ i, 0 < w i →
      a i < Q.left ∨ a i = Q.upper) :
    ∀ t ∈ Icc (-1 : ℝ) 1,
      ∃ s₀ ∈ Icc (-1 : ℝ) 1, ∀ i, 0 < w i →
        0 < |s₀ - a i| ∧
          |s₀ - a i| ≤ |t - Q.rearrangement (a i)| := by
  intro t ht
  have htQ : t ∈ Icc Q.left Q.upper := by
    constructor
    · rw [hleft]
      exact ht.1
    · exact ht.2.trans hupper.le
  let s₀ := Q.inverseCoordinate t
  have hs₀Q : s₀ ∈ Icc Q.left Q.upper := Q.inverseCoordinate_mem_Icc htQ
  have hs₀t : s₀ ≤ t := Q.inverseCoordinate_le htQ.1
  have hs₀root : s₀ ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · rw [← hleft]
      exact hs₀Q.1
    · exact hs₀t.trans ht.2
  refine ⟨s₀, hs₀root, ?_⟩
  intro i hwi
  rcases hlocation i hwi with hiLeft | hiUpper
  · have hiS : a i < s₀ := hiLeft.trans_le hs₀Q.1
    refine ⟨abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hiS)), ?_⟩
    exact Q.abs_inverseCoordinate_sub_le_abs_sub_rearrangement_of_lt_left
      htQ hiLeft
  · have hs₀Upper : s₀ < a i := by
      rw [hiUpper]
      exact hs₀t.trans_lt (ht.2.trans_lt hupper)
    have hiMem : a i ∈ Icc Q.left Q.upper := by
      rw [hiUpper]
      exact ⟨Q.h_left_upper, le_rfl⟩
    refine ⟨abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hs₀Upper)), ?_⟩
    exact Q.abs_inverseCoordinate_sub_le_abs_sub_rearrangement hiMem

/-- Tao's finite-atomic expansive-quantile contradiction criterion with
the generalized inverse fully constructed. -/
theorem exists_quantile_pushed_trial_atom_taoEmpiricalPotential_neg
    {ι : Type*} [Fintype ι] (f : Polynomial ℝ)
    (hf : IsAdmissible f) (w a : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hleft : Q.left = -1) (hupper : 1 < Q.upper)
    (hlocation : ∀ i, 0 < w i →
      a i < Q.left ∨ a i = Q.upper)
    (htrial : ∀ s ∈ Icc (-1 : ℝ) 1,
      taoFiniteTrialPotential w a s < 0) :
    ∃ i, 0 < w i ∧
      taoEmpiricalPotential f hf (Q.rearrangement (a i)) < 0 := by
  apply exists_pushed_trial_atom_taoEmpiricalPotential_neg
    f hf w a Q.rearrangement hw htrial
  exact Q.rootInterval_separator w a hleft hupper hlocation

end QuantileData

end

end Erdos1038
