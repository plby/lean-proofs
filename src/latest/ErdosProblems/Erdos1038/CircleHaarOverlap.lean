import ErdosProblems.Erdos1038.CircleArcOverlap
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Measure.Haar.Unique



/-!
# Haar measure of overlapping arcs on the additive circle

This file connects the elementary overlap profiles in
`CircleArcOverlap` to the standard Haar volume on
`AddCircle (2 * Real.pi)`.
-/

open Metric Set MeasureTheory
open scoped ENNReal

namespace Erdos1038

noncomputable section

private lemma preimage_closedBall_zero_inter_Icc {r : ℝ}
    (hr0 : 0 ≤ r) (hrpi : r ≤ Real.pi) :
    QuotientAddGroup.mk ⁻¹'
          closedBall (0 : AddCircle (2 * Real.pi)) r ∩
        Icc (-Real.pi) Real.pi =
      Icc (-r) r := by
  change QuotientAddGroup.mk ⁻¹'
        closedBall ((0 : ℝ) : AddCircle (2 * Real.pi)) r ∩
      Icc (-Real.pi) Real.pi = Icc (-r) r
  rw [AddCircle.coe_real_preimage_closedBall_inter_eq]
  · rw [abs_of_pos Real.two_pi_pos]
    have hhalf : 2 * Real.pi / 2 = Real.pi := by ring
    rw [hhalf]
    split_ifs with hr
    · rw [Real.closedBall_eq_Icc, zero_sub, zero_add]
      exact inter_eq_left.mpr (Icc_subset_Icc (neg_le_neg hrpi) hrpi)
    · have : r = Real.pi := le_antisymm hrpi (not_lt.mp hr)
      subst r
      rfl
  · rw [abs_of_pos Real.two_pi_pos]
    have hhalf : 2 * Real.pi / 2 = Real.pi := by ring
    rw [hhalf, Real.closedBall_eq_Icc, zero_sub, zero_add]

private lemma preimage_closedBall_inter_centered_Icc {r s d : ℝ}
    (hrpi : r ≤ Real.pi) (hs0 : 0 ≤ s) (hspi : s ≤ Real.pi)
    (hd0 : 0 ≤ d) (hdpi : d ≤ Real.pi) :
    QuotientAddGroup.mk ⁻¹'
          closedBall (d : AddCircle (2 * Real.pi)) s ∩ Icc (-r) r =
      (Icc (-r) r ∩ Icc (d - s) (d + s)) ∪
        (Icc (-r) r ∩
          Icc (d - 2 * Real.pi - s) (d - 2 * Real.pi + s)) := by
  rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion]
  ext y
  simp only [mem_inter_iff, mem_iUnion, Real.closedBall_eq_Icc,
    mem_Icc, mem_union, zsmul_eq_mul]
  constructor
  · rintro ⟨⟨z, hzlo, hzhi⟩, hyr⟩
    have hylo : -Real.pi ≤ y := (neg_le_neg hrpi).trans hyr.1
    have hyhi : y ≤ Real.pi := hyr.2.trans hrpi
    have hzlo' : (-2 : ℝ) < (z : ℝ) := by
      nlinarith [Real.pi_pos]
    have hzhi' : (z : ℝ) ≤ 1 := by
      nlinarith [Real.pi_pos]
    have hzlo_int : (-2 : ℤ) < z := by exact_mod_cast hzlo'
    have hzhi_int : z ≤ (1 : ℤ) := by exact_mod_cast hzhi'
    have hz_cases : z = -1 ∨ z = 0 ∨ z = 1 := by omega
    rcases hz_cases with (rfl | rfl | rfl)
    · right
      exact ⟨hyr, by simpa [mul_comm, sub_eq_add_neg] using! And.intro hzlo hzhi⟩
    · left
      exact ⟨hyr, by simpa using! And.intro hzlo hzhi⟩
    · left
      norm_num at hzlo hzhi
      exact ⟨hyr, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩⟩
  · rintro (h | h)
    · exact ⟨⟨0, by simpa using! h.2.1, by simpa using! h.2.2⟩, h.1⟩
    · exact ⟨⟨-1, by simpa [mul_comm, sub_eq_add_neg] using! h.2.1,
          by simpa [mul_comm, sub_eq_add_neg] using! h.2.2⟩, h.1⟩

private lemma volume_inter_centeredIntervals_neg {r s d : ℝ}
    (hd : 0 ≤ d) :
    volume (Icc (-r) r ∩ Icc (-d - s) (-d + s)) =
      ENNReal.ofReal (lineArcOverlap r s d) := by
  let S : Set ℝ := Icc (-r) r ∩ Icc (d - s) (d + s)
  have hS : MeasurableSet S := measurableSet_Icc.inter measurableSet_Icc
  have hpreimage :
      (fun x : ℝ => -x) ⁻¹' S =
        Icc (-r) r ∩ Icc (-d - s) (-d + s) := by
    ext x
    simp only [S, mem_preimage, mem_inter_iff, mem_Icc]
    constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
    · exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hneg :
      volume ((fun x : ℝ => -x) ⁻¹' S) = volume S :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).measure_preimage
      hS.nullMeasurableSet
  rw [← hpreimage, hneg]
  exact volume_inter_centeredIntervals hd

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Haar volume of the intersection of two arcs on the circle of
circumference `2 * π`.  The centers are represented by `0` and
`d ∈ [0, π]`; hence `d` is their circular distance. -/
theorem volume_inter_addCircle_closedBall {r s d : ℝ}
    (hr0 : 0 ≤ r) (hrpi : r ≤ Real.pi)
    (hs0 : 0 ≤ s) (hspi : s ≤ Real.pi)
    (hd0 : 0 ≤ d) (hdpi : d ≤ Real.pi) :
    volume
        (closedBall (0 : AddCircle (2 * Real.pi)) r ∩
          closedBall (d : AddCircle (2 * Real.pi)) s) =
      ENNReal.ofReal (circleArcOverlap r s d) := by
  let A : Set ℝ := Icc (-r) r ∩ Icc (d - s) (d + s)
  let B : Set ℝ :=
    Icc (-r) r ∩
      Icc (d - 2 * Real.pi - s) (d - 2 * Real.pi + s)
  have hfund : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have hpreimage :
      QuotientAddGroup.mk ⁻¹'
            (closedBall (0 : AddCircle (2 * Real.pi)) r ∩
              closedBall (d : AddCircle (2 * Real.pi)) s) ∩
          Icc (-Real.pi) Real.pi = A ∪ B := by
    rw [preimage_inter]
    calc
      (QuotientAddGroup.mk ⁻¹'
              closedBall (0 : AddCircle (2 * Real.pi)) r ∩
            QuotientAddGroup.mk ⁻¹'
              closedBall (d : AddCircle (2 * Real.pi)) s) ∩
          Icc (-Real.pi) Real.pi =
          QuotientAddGroup.mk ⁻¹'
              closedBall (d : AddCircle (2 * Real.pi)) s ∩
            (QuotientAddGroup.mk ⁻¹'
                closedBall (0 : AddCircle (2 * Real.pi)) r ∩
              Icc (-Real.pi) Real.pi) := by
          ext x
          simp only [mem_inter_iff]
          tauto
      _ = QuotientAddGroup.mk ⁻¹'
              closedBall (d : AddCircle (2 * Real.pi)) s ∩
            Icc (-r) r := by
          rw [preimage_closedBall_zero_inter_Icc hr0 hrpi]
      _ = A ∪ B := by
          simpa only [A, B] using!
            preimage_closedBall_inter_centered_Icc hrpi hs0 hspi hd0 hdpi
  have hdisjoint : AEDisjoint (volume : Measure ℝ) A B := by
    rw [AEDisjoint]
    apply measure_mono_null (t := {d - Real.pi})
    · intro x hx
      simp only [A, B, mem_inter_iff, mem_Icc] at hx
      simp only [mem_singleton_iff]
      apply le_antisymm
      · linarith
      · linarith
    · exact measure_singleton _
  have hvolA :
      volume A = ENNReal.ofReal (lineArcOverlap r s d) := by
    exact volume_inter_centeredIntervals hd0
  have hwrap0 : 0 ≤ 2 * Real.pi - d := by
    linarith [Real.pi_pos]
  have hvolB :
      volume B =
        ENNReal.ofReal (lineArcOverlap r s (2 * Real.pi - d)) := by
    unfold B
    have hlo :
        d - 2 * Real.pi - s = -(2 * Real.pi - d) - s := by ring
    have hhi :
        d - 2 * Real.pi + s = -(2 * Real.pi - d) + s := by ring
    rw [hlo, hhi]
    exact volume_inter_centeredIntervals_neg hwrap0
  calc
    volume
        (closedBall (0 : AddCircle (2 * Real.pi)) r ∩
          closedBall (d : AddCircle (2 * Real.pi)) s) =
        volume
          (QuotientAddGroup.mk ⁻¹'
                (closedBall (0 : AddCircle (2 * Real.pi)) r ∩
                  closedBall (d : AddCircle (2 * Real.pi)) s) ∩
            Ioc (-Real.pi) Real.pi) := by
      simpa only [hfund] using!
        AddCircle.add_projection_respects_measure
          (2 * Real.pi) (-Real.pi)
          (measurableSet_closedBall.inter measurableSet_closedBall)
    _ = volume
          (QuotientAddGroup.mk ⁻¹'
                (closedBall (0 : AddCircle (2 * Real.pi)) r ∩
                  closedBall (d : AddCircle (2 * Real.pi)) s) ∩
            Icc (-Real.pi) Real.pi) := by
      exact measure_congr
        (ae_eq_set_inter (ae_eq_refl _)
          (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ))))
    _ = volume (A ∪ B) := congr_arg volume hpreimage
    _ = volume A + volume B := by
      exact measure_union₀
        (measurableSet_Icc.inter measurableSet_Icc).nullMeasurableSet
        hdisjoint
    _ = ENNReal.ofReal (lineArcOverlap r s d) +
          ENNReal.ofReal (lineArcOverlap r s (2 * Real.pi - d)) := by
      rw [hvolA, hvolB]
    _ = ENNReal.ofReal
          (lineArcOverlap r s d +
            lineArcOverlap r s (2 * Real.pi - d)) := by
      rw [ENNReal.ofReal_add
        (lineArcOverlap_nonneg r s d)
        (lineArcOverlap_nonneg r s (2 * Real.pi - d))]
    _ = ENNReal.ofReal (circleArcOverlap r s d) := by
      rw [circleArcOverlap_eq_line_add_wrap hr0 hrpi hs0 hspi hd0 hdpi]

private theorem volume_inter_addCircle_closedBall_zero_coe_abs
    {r s q : ℝ}
    (hr0 : 0 ≤ r) (hrpi : r ≤ Real.pi)
    (hs0 : 0 ≤ s) (hspi : s ≤ Real.pi)
    (hqlo : -Real.pi ≤ q) (hqhi : q ≤ Real.pi) :
    volume
        (closedBall (0 : AddCircle (2 * Real.pi)) r ∩
          closedBall (q : AddCircle (2 * Real.pi)) s) =
      ENNReal.ofReal (circleArcOverlap r s |q|) := by
  rcases le_total 0 q with hq0 | hq0
  · simpa [abs_of_nonneg hq0] using!
      volume_inter_addCircle_closedBall
        hr0 hrpi hs0 hspi hq0 hqhi
  · let U : Set (AddCircle (2 * Real.pi)) :=
      closedBall (0 : AddCircle (2 * Real.pi)) r ∩
        closedBall (q : AddCircle (2 * Real.pi)) s
    have hpreimage : Neg.neg ⁻¹' U =
        closedBall (0 : AddCircle (2 * Real.pi)) r ∩
          closedBall ((-q : ℝ) : AddCircle (2 * Real.pi)) s := by
      ext z
      simp [U, mem_closedBall]
    calc
      volume U = volume (Neg.neg ⁻¹' U) :=
        (Measure.measure_preimage_neg volume U).symm
      _ = volume
          (closedBall (0 : AddCircle (2 * Real.pi)) r ∩
            closedBall ((-q : ℝ) : AddCircle (2 * Real.pi)) s) := by
        rw [hpreimage]
      _ = ENNReal.ofReal (circleArcOverlap r s (-q)) := by
        exact volume_inter_addCircle_closedBall
          hr0 hrpi hs0 hspi (by linarith) (by linarith)
      _ = ENNReal.ofReal (circleArcOverlap r s |q|) := by
        rw [abs_of_nonpos hq0]

/-- Fully intrinsic form of the arc-overlap formula: the Haar volume
depends only on the circular distance between arbitrary centers. -/
theorem volume_inter_addCircle_closedBalls
    {x y : AddCircle (2 * Real.pi)} {r s : ℝ}
    (hr0 : 0 ≤ r) (hrpi : r ≤ Real.pi)
    (hs0 : 0 ≤ s) (hspi : s ≤ Real.pi) :
    volume (closedBall x r ∩ closedBall y s) =
      ENNReal.ofReal (circleArcOverlap r s (dist x y)) := by
  let qsub : Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) :=
    AddCircle.equivIoc (2 * Real.pi) (-Real.pi) (y - x)
  let q : ℝ := qsub.1
  have hqmem : q ∈ Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := qsub.2
  have hqlo : -Real.pi ≤ q := hqmem.1.le
  have hqhi : q ≤ Real.pi := by linarith [hqmem.2]
  have hqcoe : (q : AddCircle (2 * Real.pi)) = y - x := by
    change (AddCircle.equivIoc (2 * Real.pi) (-Real.pi)).symm qsub = y - x
    exact Equiv.symm_apply_apply _ _
  have hqnorm : ‖(q : AddCircle (2 * Real.pi))‖ = |q| := by
    apply (AddCircle.norm_coe_eq_abs_iff
      (2 * Real.pi) (by positivity)).2
    rw [abs_of_pos Real.two_pi_pos]
    apply abs_le.2
    constructor <;> linarith
  have hdist : dist x y = |q| := by
    calc
      dist x y = ‖y - x‖ := by rw [dist_comm, dist_eq_norm]
      _ = ‖(q : AddCircle (2 * Real.pi))‖ := by rw [hqcoe]
      _ = |q| := hqnorm
  let U : Set (AddCircle (2 * Real.pi)) :=
    closedBall x r ∩ closedBall y s
  have htranslate : (fun z : AddCircle (2 * Real.pi) => x + z) ⁻¹' U =
      closedBall (0 : AddCircle (2 * Real.pi)) r ∩
        closedBall (y - x) s := by
    simp [U, sub_eq_add_neg]
  calc
    volume U = volume
        ((fun z : AddCircle (2 * Real.pi) => x + z) ⁻¹' U) :=
      (measure_preimage_add volume x U).symm
    _ = volume
        (closedBall (0 : AddCircle (2 * Real.pi)) r ∩
          closedBall (y - x) s) := by
      rw [htranslate]
    _ = volume
        (closedBall (0 : AddCircle (2 * Real.pi)) r ∩
          closedBall (q : AddCircle (2 * Real.pi)) s) := by
      rw [hqcoe]
    _ = ENNReal.ofReal (circleArcOverlap r s |q|) :=
      volume_inter_addCircle_closedBall_zero_coe_abs
        hr0 hrpi hs0 hspi hqlo hqhi
    _ = ENNReal.ofReal (circleArcOverlap r s (dist x y)) := by
      rw [hdist]

/-- Intrinsic distance monotonicity for pairs of arcs with the same
radii. -/
theorem volume_inter_addCircle_closedBalls_mono_distance
    {w x y z : AddCircle (2 * Real.pi)} {r s : ℝ}
    (hr0 : 0 ≤ r) (hrpi : r ≤ Real.pi)
    (hs0 : 0 ≤ s) (hspi : s ≤ Real.pi)
    (hdist : dist w x ≤ dist y z) :
    volume (closedBall y r ∩ closedBall z s) ≤
      volume (closedBall w r ∩ closedBall x s) := by
  rw [volume_inter_addCircle_closedBalls hr0 hrpi hs0 hspi,
    volume_inter_addCircle_closedBalls hr0 hrpi hs0 hspi]
  exact ENNReal.ofReal_le_ofReal
    (circleArcOverlap_mono_distance hdist)

/-- For arcs of fixed radii, Haar overlap is antitone in the circular
distance between their centers. -/
theorem volume_inter_addCircle_closedBall_mono_distance
    {r s d e : ℝ}
    (hr0 : 0 ≤ r) (hrpi : r ≤ Real.pi)
    (hs0 : 0 ≤ s) (hspi : s ≤ Real.pi)
    (hd0 : 0 ≤ d) (hdpi : d ≤ Real.pi)
    (he0 : 0 ≤ e) (hepi : e ≤ Real.pi) (hde : d ≤ e) :
    volume
        (closedBall (0 : AddCircle (2 * Real.pi)) r ∩
          closedBall (e : AddCircle (2 * Real.pi)) s) ≤
      volume
        (closedBall (0 : AddCircle (2 * Real.pi)) r ∩
          closedBall (d : AddCircle (2 * Real.pi)) s) := by
  rw [volume_inter_addCircle_closedBall hr0 hrpi hs0 hspi he0 hepi,
    volume_inter_addCircle_closedBall hr0 hrpi hs0 hspi hd0 hdpi]
  exact ENNReal.ofReal_le_ofReal (circleArcOverlap_mono_distance hde)

/-- A layer cake made of nonnegative ball layers has cross-energy
antitone in the distance between the two layer centers.  No
measurability hypotheses on the radius maps are needed for this order
statement: `lintegral_mono` applies to their upper integrals. -/
theorem layerCake_ballCrossEnergy_mono_distance
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (R : α → ℝ) (S : β → ℝ)
    (hR0 : ∀ a, 0 ≤ R a) (hRpi : ∀ a, R a ≤ Real.pi)
    (hS0 : ∀ b, 0 ≤ S b) (hSpi : ∀ b, S b ≤ Real.pi)
    {d e : ℝ} (hd0 : 0 ≤ d) (hdpi : d ≤ Real.pi)
    (he0 : 0 ≤ e) (hepi : e ≤ Real.pi) (hde : d ≤ e) :
    (∫⁻ a, ∫⁻ b,
        volume
          (closedBall (0 : AddCircle (2 * Real.pi)) (R a) ∩
            closedBall (e : AddCircle (2 * Real.pi)) (S b)) ∂ν ∂μ) ≤
      ∫⁻ a, ∫⁻ b,
        volume
          (closedBall (0 : AddCircle (2 * Real.pi)) (R a) ∩
            closedBall (d : AddCircle (2 * Real.pi)) (S b)) ∂ν ∂μ := by
  apply lintegral_mono
  intro a
  apply lintegral_mono
  intro b
  exact volume_inter_addCircle_closedBall_mono_distance
    (hR0 a) (hRpi a) (hS0 b) (hSpi b)
    hd0 hdpi he0 hepi hde

/-- Abstract layer-cake interface: any `ℝ≥0∞`-valued cross-energy
represented as an iterated nonnegative mixture of ball overlaps is
antitone on the half-circle. -/
theorem antitoneOn_of_layerCake_ballOverlap
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (R : α → ℝ) (S : β → ℝ)
    (hR0 : ∀ a, 0 ≤ R a) (hRpi : ∀ a, R a ≤ Real.pi)
    (hS0 : ∀ b, 0 ≤ S b) (hSpi : ∀ b, S b ≤ Real.pi)
    (E : ℝ → ℝ≥0∞)
    (hE : ∀ d ∈ Icc (0 : ℝ) Real.pi,
      E d = ∫⁻ a, ∫⁻ b,
        volume
          (closedBall (0 : AddCircle (2 * Real.pi)) (R a) ∩
            closedBall (d : AddCircle (2 * Real.pi)) (S b)) ∂ν ∂μ) :
    AntitoneOn E (Icc (0 : ℝ) Real.pi) := by
  intro d hd e he hde
  rw [hE e he, hE d hd]
  exact layerCake_ballCrossEnergy_mono_distance
    μ ν R S hR0 hRpi hS0 hSpi
    hd.1 hd.2 he.1 he.2 hde

end

end Erdos1038
