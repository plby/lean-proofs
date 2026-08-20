module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Tactic.Bound
import Mathlib.Topology.Constructions
import ErdosProblems.Erdos515.External.Ray.Misc.Topology

/-!
## Miscellaneous measure theory lemmas
-/

open Filter (liminf limsup atTop Tendsto)
open Function (curry uncurry)
open MeasureTheory
open Metric (ball closedBall sphere)
open Set (Ioc Icc)
open scoped Real ENNReal Topology
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {V : Type} [NormedAddCommGroup V]
variable [SecondCountableTopology E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {X : Type} [MeasureSpace X] [MetricSpace X] [BorelSpace X]
variable {Y : Type} [MeasureSpace Y] [MetricSpace Y] [BorelSpace Y]
variable {A : Type} [TopologicalSpace A]
variable {M : Type} [MeasureSpace M]
variable {μ : Measure M}

/-- Removing a null set isn't significant measure-wise -/
theorem ae_minus_null {s t : Set M} (tz : volume t = 0) : s =ᵐ[volume] s \ t := by
  simp only [Filter.EventuallyEq, Pi.sdiff_apply, eq_iff_iff]
  have e : ∀ x, x ∉ t → (x ∈ s ↔ x ∈ s \ t) := by
    intro x h; simp only [Set.mem_sdiff, h, not_false_iff, and_true]
  refine Filter.Eventually.mono ?_ e
  exact measure_eq_zero_iff_ae_notMem.mp tz

/-- Removing a point isn't significant measure-wise (if there are no atoms) -/
public theorem ae_minus_point [NullSingletonClass (volume : Measure M)] {s : Set M} {x : M} :
    s =ᵐ[volume] (s \ {x} : Set M) :=
  ae_minus_null (measure_singleton x)

/-- `ℝ × ℝ` has additive Haar measure.
    Lean fails to infer this, so I'm caching it for easy access. -/
public instance ProdRealReal.isAddHaarMeasure_volume :
    (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure :=
  MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _

/-- `ℂ` has additive Haar measure -/
public instance Complex.isAddHaarMeasure_volume : (volume : Measure ℂ).IsAddHaarMeasure := by
  have v : (volume : Measure ℂ) = volume.map Complex.equivRealProdAddHom.symm := by
    have e : (⇑Complex.measurableEquivRealProd.symm : ℝ × ℝ → ℂ) =
        ⇑Complex.equivRealProdAddHom.symm := by
      funext x
      simp only [measurableEquivRealProd, Homeomorph.toMeasurableEquiv_symm_coe,
        ContinuousLinearEquiv.coe_symm_toHomeomorph, Complex.ext_iff,
        equivRealProdCLM_symm_apply_re, equivRealProdAddHom_symm_apply_re,
        equivRealProdCLM_symm_apply_im, equivRealProdAddHom_symm_apply_im, and_self]
    rw [← e]; clear e
    exact (MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod).map_eq.symm
  rw [v]
  have e : (⇑Complex.equivRealProdCLM.symm : ℝ × ℝ → ℂ) =
      ⇑Complex.equivRealProdAddHom.symm.toAddMonoidHom := by
    funext x
    simp only [Complex.ext_iff, AddEquiv.coe_toAddMonoidHom, Complex.equivRealProdCLM_symm_apply_re,
      Complex.equivRealProdAddHom_symm_apply_re, Complex.equivRealProdCLM_symm_apply_im,
      Complex.equivRealProdAddHom_symm_apply_im, and_self_iff]
  apply Measure.isAddHaarMeasure_map (volume : Measure (ℝ × ℝ))
    Complex.equivRealProdAddHom.symm.toAddMonoidHom
  · rw [←e]; apply ContinuousLinearEquiv.continuous
  · apply AddEquiv.surjective
  · rw [←e]; exact Complex.equivRealProdCLM.symm.toHomeomorph.toCocompactMap.cocompact_tendsto'

/-- `ℂ` has no atoms -/
public instance Complex.noAtoms_volume : NullSingletonClass (volume : Measure ℂ) where
  measure_singleton := by
    intro z
    rw [← (MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod).measure_preimage]
    · rw [← MeasurableEquiv.image_eq_preimage_symm, Set.image_singleton,
        MeasureTheory.measure_singleton]
    · apply MeasurableSet.singleton

/-- The property that a set has finite, positive measure.
    This means that multiplication and division by the measure are invertible operations. -/
public structure NiceVolume (s : Set M) : Prop where
  measurable : MeasurableSet s
  finite : volume s < ∞
  pos : volume s > 0

-- Useful lemmas about NiceVolume
public lemma NiceVolume.ne_zero {s : Set M} (sn : NiceVolume s) : volume s ≠ 0 := sn.pos.ne'
public lemma NiceVolume.ne_top {s : Set M} (sn : NiceVolume s) : volume s ≠ ⊤ := sn.finite.ne
public lemma NiceVolume.real_pos {s : Set M} (sn : NiceVolume s) : 0 < volume.real s :=
  ENNReal.toReal_pos_iff.mpr ⟨sn.pos, sn.finite⟩
public lemma NiceVolume.real_nonneg {s : Set M} (sn : NiceVolume s) : volume.real s ≠ 0 :=
  sn.real_pos.ne'

/-- Constants are integrable on NiceVolume sets -/
public theorem NiceVolume.integrableOn_const {s : Set M} (sn : NiceVolume s) (c : ℝ) :
    IntegrableOn (fun _ : M ↦ c) s :=
  MeasureTheory.integrableOn_const (ne_top sn) enorm_ne_top

/-- Uniform limits of continuous functions and integrals commute -/
public theorem TendstoUniformlyOn.integral_tendsto {f : ℕ → X → G} {g : X → G} {s : Set X}
    [SecondCountableTopology G] [IsLocallyFiniteMeasure (volume : Measure X)]
    (u : TendstoUniformlyOn f g atTop s)
    (fc : ∀ n, ContinuousOn (f n) s) (sc : IsCompact s) :
    Tendsto (fun n ↦ ∫ x in s, f n x) atTop (nhds (∫ x in s, g x)) := by
  rcases u.uniformCauchySeqOn.bounded fc sc with ⟨b, _, bh⟩
  apply tendsto_integral_of_dominated_convergence (F := f) (f := g) (fun _ ↦ b)
  · intro n; exact (fc n).aestronglyMeasurable sc.measurableSet
  · exact continuousOn_const.integrableOn_compact sc
  · intro n; specialize bh n; rw [ae_restrict_iff' sc.measurableSet]
    exact ae_of_all _ bh
  · rw [ae_restrict_iff' sc.measurableSet]; apply ae_of_all; intro x xs; exact u.tendsto_at xs

/-- An abbreviation for Ioc 0 (2*π) -/
@[expose] public def itau := Ioc 0 (2 * π)

-- Lemmas about Itau
public theorem itau_volume : volume itau = ENNReal.ofReal (2 * π) := by
  simp only [itau, Real.volume_Ioc, sub_zero]
public theorem itau_real_volume : volume.real itau = 2 * π := by
  simp only [Measure.real, itau_volume, ENNReal.toReal_ofReal Real.two_pi_pos.le]
public theorem NiceVolume.itau : NiceVolume itau :=
  { measurable := by simp only [_root_.itau, measurableSet_Ioc]
    finite := by simp only [itau_volume, ENNReal.ofReal_lt_top]
    pos := by simp only [itau_volume, gt_iff_lt, ENNReal.ofReal_pos, zero_lt_two,
      mul_pos_iff_of_pos_left, Real.pi_pos] }
public theorem measurableSet_itau : MeasurableSet itau := by
  simp only [itau, measurableSet_Ioc]
public theorem tau_mem_itau : 2*π ∈ itau := by
  simp only [itau, Set.mem_Ioc, zero_lt_two, mul_pos_iff_of_pos_left, Real.pi_pos, le_refl,
    and_self]

/-- Continuous functions are integrable on spheres -/
public theorem ContinuousOn.integrableOn_sphere {f : ℂ → V} {c : ℂ} {r : ℝ}
    (fc : ContinuousOn f (closedBall c r)) (rp : 0 < r) :
    IntegrableOn (fun t ↦ f (circleMap c r t)) itau := by
  apply Continuous.integrableOn_Ioc; apply fc.comp_continuous (continuous_circleMap _ _)
  intro t; simp only [Metric.mem_closedBall, Complex.dist_eq, circleMap_sub_center,
    norm_circleMap_zero, abs_of_pos rp, le_refl]

/-- Continuous functions are integrable on `closedBall` -/
public theorem ContinuousOn.integrableOn_closedBall {f : ℂ → V} {c : ℂ} {r : ℝ}
    (fc : ContinuousOn f (closedBall c r)) : IntegrableOn f (closedBall c r) :=
  fc.integrableOn_compact (isCompact_closedBall _ _)

/-- Averages add -/
public theorem Average.add {f g : M → G} {s : Set M} (fi : IntegrableOn f s)
    (gi : IntegrableOn g s) :
    ⨍ z in s, f z + g z = (⨍ z in s, f z) + ⨍ z in s, g z := by
  simp_rw [average_eq, integral_add fi gi, smul_add]

/-- Averages subtract -/
public theorem Average.sub {f g : M → G} {s : Set M} (fi : IntegrableOn f s)
    (gi : IntegrableOn g s) :
    ⨍ z in s, f z - g z = (⨍ z in s, f z) - ⨍ z in s, g z := by
  simp_rw [average_eq, integral_sub fi gi, smul_sub]

/-- Averages commute with linear maps -/
public theorem average_linear_comm [CompleteSpace G] {f : M → G} {s : Set M} (fi : IntegrableOn f s)
    (g : G →L[ℝ] F) : ⨍ x in s, g (f x) = g (⨍ x in s, f x) := by
  simp only [average_eq, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter, map_smul]
  apply congr_arg₂ _ rfl
  exact ContinuousLinearMap.integral_comp_comm _ fi

/-- Averages on a set depend only on ae values within the set -/
public theorem average_congr_on {f g : M → G} {s : Set M} (sn : NiceVolume s)
    (h : ∀ᵐ x, x ∈ s → f x = g x) : ⨍ x in s, f x = ⨍ x in s, g x := by
  simp only [← ae_restrict_iff' sn.measurable] at h; exact average_congr h

/-- Means are at most the values of the function -/
public theorem mean_bound {f : M → ℝ} {s : Set M} {b : ℝ} (sn : NiceVolume s) (fi : IntegrableOn f s)
    (fb : ∀ z, z ∈ s → f z ≤ b) : ⨍ x in s, f x ≤ b := by
  rw [average_eq, smul_eq_mul]
  have bi := sn.integrableOn_const b
  have ib := setIntegral_mono_on fi bi sn.measurable fb
  simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
    smul_eq_mul, ge_iff_le] at ib ⊢
  trans (volume.real s)⁻¹ * ((volume.real s) * b)
  · gcongr
  · rw [← mul_assoc _ _ b, inv_mul_cancel₀ sn.real_nonneg, one_mul]

/-- Sets where each point is near positive volume -/
public def LocalVolumeSet (s : Set X) :=
  ∀ x r, x ∈ s → 0 < r → 0 < volume (s ∩ ball x r)

/-- Sets in the closure of their interior have local volume -/
public theorem LocalVolume.closure_interior {M : Type} [MetricSpace M] [MeasureSpace M] (s : Set M)
    (bp : ∀ (x : M) (r), r > 0 → volume (ball x r) > 0)
    (ci : s ⊆ closure (interior s)) : LocalVolumeSet s := by
  intro x r xs rp
  have xci := ci xs
  rcases Metric.mem_closure_iff.mp xci r rp with ⟨y, ys, xy⟩
  rcases Metric.isOpen_iff.mp isOpen_interior y ys with ⟨e, ep, ye⟩
  set t := min e (r - dist x y)
  have es : ball y t ⊆ s ∩ ball x r := by
    simp only [Set.subset_inter_iff]; constructor
    exact _root_.trans (Metric.ball_subset_ball (by bound)) (_root_.trans ye interior_subset)
    apply Metric.ball_subset_ball'
    trans r - dist x y + dist y x; bound; simp [dist_comm]
  exact lt_of_lt_of_le (bp y t (by bound)) (measure_mono es)

/-- Ioc has local volume -/
public theorem LocalVolume.Ioc {a b : ℝ} : LocalVolumeSet (Set.Ioc a b) := by
  apply LocalVolume.closure_interior
  · intro x r rp
    simp only [Real.volume_ball, gt_iff_lt, ENNReal.ofReal_pos]
    bound
  · by_cases ab : a = b; · simp only [ab, Set.Ioc_self, Set.empty_subset]
    simp only [interior_Ioc, closure_Ioo ab, Set.Ioc_subset_Icc_self]

/-- itau has local volume -/
public theorem LocalVolume.itau : LocalVolumeSet itau := LocalVolume.Ioc

/-- If an interval mean is above b, and each value is below b, then each value is exactly b -/
public theorem mean_squeeze {f : X → ℝ} {s : Set X} {b : ℝ} (sn : NiceVolume s)
    (lv : LocalVolumeSet s) (fc : ContinuousOn f s) (fi : IntegrableOn f s) (lo : b ≤ ⨍ x in s, f x)
    (hi : ∀ x, x ∈ s → f x ≤ b) : ∀ x, x ∈ s → f x = b := by
  contrapose lo; rw [average_eq]
  simp only [smul_eq_mul, not_le]
  simp only [not_forall] at lo
  rcases lo with ⟨x, xs, fx'⟩
  have fx := lt_of_le_of_ne (hi x xs) fx'; clear fx'
  rcases Metric.continuousOn_iff.mp fc x xs ((b - f x) / 2) (by linarith) with ⟨e, ep, he⟩
  have vtp' := lv x e xs ep
  generalize ht : s ∩ ball x e = t; rw [ht] at vtp'
  have ts : t ⊆ s := by rw [← ht]; exact Set.inter_subset_left
  have tf : volume t < ⊤ := lt_of_le_of_lt (measure_mono ts) sn.finite
  have tm : MeasurableSet t := by
    rw [← ht]; exact MeasurableSet.inter sn.measurable measurableSet_ball
  have sc : s \ t ∪ t = s := Set.sdiff_union_of_subset ts
  nth_rw 2 [← sc]
  rw [setIntegral_union]
  simp only [MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter, gt_iff_lt]
  · set m := (b + f x) / 2
    set vs := volume.real s
    set vt := volume.real t
    have vsp : vs > 0 := sn.real_pos
    have vtp : vt > 0 := ENNReal.toReal_pos (vtp'.ne') (lt_top_iff_ne_top.mp tf)
    rw [inv_mul_lt_iff₀' vsp]
    have mb : m < b := by
      calc (b + f x) / 2
        _ < (b + b) / 2 := (div_lt_div_iff_of_pos_right (by norm_num)).mpr (by bound)
        _ = b := by ring
    have i0 : ∫ x in s \ t, f x ≤ (vs - vt) * b := by
      have df : volume (s \ t) < ⊤ := lt_of_le_of_lt (measure_mono Set.sdiff_subset) sn.finite
      have dm : MeasurableSet (s \ t) := MeasurableSet.diff sn.measurable tm
      have fb := setIntegral_mono_on (μ := volume) (f := f) (g := fun _ ↦ b) (s := s \ t)
        (fi.mono Set.sdiff_subset (le_refl _)) (integrableOn_const df.ne_top) dm ?_
      · simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
          MeasureTheory.measureReal_sdiff ts tm sn.ne_top, smul_eq_mul] at fb
        exact fb
      · intro y yd; simp at yd; exact hi y yd.left
    have i1 : ∫ x in t, f x ≤ vt * m := by
      have fm := setIntegral_mono_on (μ := volume) (f := f) (g := fun _ ↦ m) (s := t)
        (fi.mono ts (le_refl _)) (integrableOn_const tf.ne_top) tm ?_
      simp at fm; exact fm
      intro y yt
      rw [← ht] at yt; simp at ht yt
      specialize he y yt.left yt.right
      simp [Real.dist_eq] at he
      calc f y
        _ = f x + (f y - f x) := by ring
        _ ≤ f x + |f y - f x| := by bound
        _ ≤ f x + (b - f x) / 2 := by bound
        _ = (b + f x) / 2 := by ring
    calc (∫ x : X in s \ t, f x) + ∫ x : X in t, f x
      _ ≤ (vs - vt) * b + vt * m := by bound
      _ = vs * b - vt * (b - m) := by ring
      _ < vs * b - 0 := (sub_lt_sub_left (by bound) _)
      _ = b * vs := by ring
  · rw [disjoint_comm]; exact Set.disjoint_sdiff_right
  · exact tm
  · exact fi.mono Set.sdiff_subset (le_refl _)
  · exact fi.mono ts (le_refl _)

public theorem ContinuousOn.intervalIntegral {M : Type} [TopologicalSpace M]
    [FirstCountableTopology M] {f : M → ℝ → G} {s : Set M} {a b : ℝ}
    (fc : ContinuousOn (uncurry f) (s ×ˢ Icc a b)) (sc : IsCompact s) (ab : a ≤ b) :
    ContinuousOn (fun x ↦ ∫ t in a..b, f x t) s := by
  rcases ((sc.prod isCompact_Icc).bddAbove_image fc.norm).exists_ge 0 with ⟨c, _, fb⟩
  simp only [Set.forall_mem_image] at fb
  simp only [Set.forall_prod_set, uncurry] at fb
  have e : ∀ x t, f x t = (uncurry f) (x, t) := by
    simp only [Function.uncurry_apply_pair, forall_const, imp_true_iff]
  intro x xs
  apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ ↦ c)
  · apply eventually_nhdsWithin_of_forall; intro y ys
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    rw [Set.uIoc_of_le ab, (by rfl : f y = fun x ↦ f y x)]; simp_rw [e]; apply fc.comp
    · apply Continuous.continuousOn; exact Continuous.prodMk_right y
    · intro t ts; exact Set.mk_mem_prod ys (Set.Ioc_subset_Icc_self ts)
  · apply eventually_nhdsWithin_of_forall; intro y ys; rw [Set.uIoc_of_le ab]
    apply ae_of_all; intro t ts; apply fb _ ys _ (Set.Ioc_subset_Icc_self ts)
  · exact intervalIntegrable_const
  · apply ae_of_all; intro t ts; simp_rw [e]; apply fc.comp
    · apply Continuous.continuousOn; exact Continuous.prodMk_left t
    · rw [Set.uIoc_of_le ab] at ts
      intro y ys; exact Set.mk_mem_prod ys (Set.Ioc_subset_Icc_self ts)
    · assumption

/-- `liminf` preserves ae measurability, general filter version -/
theorem aEMeasurable_liminf' {I I' : Type} {u : Filter I} {f : I → M → ENNReal} {μ : Measure M}
    {p : I' → Prop} {s : I' → Set I} (fm : ∀ n, AEMeasurable (f n) μ) (uc : u.HasCountableBasis p s)
    (sc : ∀ i, (s i).Countable) : AEMeasurable (fun x ↦ u.liminf fun n ↦ f n x) μ := by
  simp_rw [uc.toHasBasis.liminf_eq_iSup_iInf]
  refine AEMeasurable.biSup _ uc.countable ?_
  intro i _; exact AEMeasurable.biInf _ (sc i) (fun n _ ↦ fm n)

/-- `liminf` preserves ae measurability, `ℕ` version -/
theorem aEMeasurable_liminf {f : ℕ → M → ENNReal} {μ : Measure M} (fm : ∀ n, AEMeasurable (f n) μ) :
    AEMeasurable (fun x ↦ atTop.liminf fun n ↦ f n x) μ :=
  aEMeasurable_liminf' fm Filter.atTop_countable_basis fun _ ↦ Set.to_countable _

public theorem set_lintegral_mono_aEMeasurable {s : Set M} {f g : M → ENNReal}
    (sm : MeasurableSet s) (fg : ∀ x, x ∈ s → f x ≤ g x) : ∫⁻ x in s, f x ≤ ∫⁻ x in s, g x := by
  apply lintegral_mono_ae; rw [ae_restrict_iff' sm]; exact ae_of_all _ fg

public lemma measure_union_eq_left {s t : Set M} (t0 : μ t = 0) : μ (s ∪ t) = μ s := by
  have tm := NullMeasurableSet.of_null t0
  have r := MeasureTheory.measure_union_add_inter₀ (μ := μ) s tm
  have i0 : μ (s ∩ t) = 0 := by
    rw [← le_zero_iff] at t0 ⊢
    exact le_trans (MeasureTheory.measure_mono Set.inter_subset_right) t0
  simpa only [t0, i0, add_zero] using r

public lemma measure_union_eq_right {s t : Set M} (s0 : μ s = 0) : μ (s ∪ t) = μ t := by
  rw [Set.union_comm]
  exact measure_union_eq_left s0

/-- Commute two interval integrals -/
lemma intervalIntegral.integral_integral_comm {f : ℝ × ℝ → G} {a0 a1 b0 b1 : ℝ} {μ ν : Measure ℝ}
    (a01 : a0 ≤ a1) (b01 : b0 ≤ b1) (i : IntegrableOn f (Ioc a0 a1 ×ˢ Ioc b0 b1) (μ.prod ν))
    [SFinite μ] [SFinite ν] :
    ∫ x in a0..a1, ∫ y in b0..b1, f (x,y) ∂ν ∂μ = ∫ y in b0..b1, ∫ x in a0..a1, f (x,y) ∂μ ∂ν := by
  simp only [intervalIntegral.integral_of_le, a01, b01]
  rw [← MeasureTheory.setIntegral_prod _ i, ← MeasureTheory.setIntegral_prod_swap,
    MeasureTheory.setIntegral_prod]
  · rfl
  · exact i.swap
