import ErdosProblems.Erdos1002.GaussTransferContraction
import Mathlib.MeasureTheory.Function.JacobianOneDim

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The normalized Gauss transfer operator as an actual density operator

`GaussTransferContraction` proves a strict Lipschitz contraction for the
explicit normalized inverse-branch kernel.  This file supplies the measure-
theoretic bridge which that estimate needs: the kernel is the
Perron--Frobenius operator for Gauss measure, hence preserves Gauss means.

The first lemma is deliberately stated for a general nonnegative measurable
test function.  Thus the later event identities do not hide an interchange
of a countable branch sum and an integral.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos1002

noncomputable section

/-- Change of variables on one inverse Gauss branch, with an arbitrary
nonnegative measurable integrand. -/
theorem gaussBranch_lintegral_change
    {q : ℕ} (hq : 0 < q) {s : Set ℝ} (hsM : MeasurableSet s)
    (hs : s ⊆ Icc (0 : ℝ) 1) (u : ℝ → ℝ≥0∞) (hu : Measurable u) :
    (∫⁻ x in gaussInverseBranch q '' s, u x ∂gaussMeasure) =
      ∫⁻ y in s,
        ENNReal.ofReal (gaussBranchRatio q y) *
          u (gaussInverseBranch q y) ∂gaussMeasure := by
  have himageM := measurableSet_gaussInverseBranch_image hq hsM hs
  have himage := gaussInverseBranch_image_subset_unit hq hs
  have hcomp : Measurable fun y =>
      ENNReal.ofReal (gaussBranchRatio q y) *
        u (gaussInverseBranch q y) :=
    (measurable_ofReal_gaussBranchRatio q).mul
      (hu.comp (measurable_gaussInverseBranch q))
  rw [gaussMeasure_eq_volume_withDensity,
    setLIntegral_withDensity_eq_setLIntegral_mul volume
      measurable_gaussDensity hu himageM]
  calc
    (∫⁻ x in gaussInverseBranch q '' s,
        (gaussDensity * u) x ∂volume) =
      ∫⁻ y in s,
        ENNReal.ofReal (1 / (((q : ℝ) + y) ^ 2)) *
          ((gaussDensity * u) (gaussInverseBranch q y)) ∂volume := by
      have hchange :=
        lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn
          (f := gaussInverseBranch q)
          (f' := fun y : ℝ => -1 / (((q : ℝ) + y) ^ 2)) hsM
          (fun y hy => by
            have hqR : (0 : ℝ) < q := by exact_mod_cast hq
            exact (hasDerivAt_gaussInverseBranch
              (q := q) (y := y) (by linarith [(hs hy).1])).hasDerivWithinAt)
          (antitoneOn_gaussInverseBranch_of_subset_unit hq hs)
          (gaussDensity * u)
      simpa only [neg_div, neg_neg] using! hchange
    _ = ∫⁻ y in s,
        gaussDensity y *
          (ENNReal.ofReal (gaussBranchRatio q y) *
            u (gaussInverseBranch q y)) ∂volume := by
      have hzero : volume.restrict s ({0} : Set ℝ) = 0 := by
        rw [Measure.restrict_apply (measurableSet_singleton 0)]
        exact measure_mono_null inter_subset_left (measure_singleton 0)
      have hae0 : ∀ᵐ y ∂volume.restrict s, y ∉ ({0} : Set ℝ) :=
        measure_eq_zero_iff_ae_notMem.mp hzero
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hsM, hae0] with y hy hy0
      have hycc : y ∈ Icc (0 : ℝ) 1 := hs hy
      have hyne : y ≠ 0 := by
        simpa only [mem_singleton_iff] using! hy0
      have hyunit : y ∈ Ioc (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne hycc.1 (Ne.symm hyne), hycc.2⟩
      have hyinv := gaussInverseBranch_image_subset_unit hq hs
        ⟨y, hy, rfl⟩
      simp only [Pi.mul_apply]
      rw [gaussDensity_eq_ofReal_on_unit hyunit,
        gaussDensity_eq_ofReal_on_unit hyinv]
      have hcore :
          ENNReal.ofReal (1 / (((q : ℝ) + y) ^ 2)) *
              ENNReal.ofReal
                (gaussDensityReal (gaussInverseBranch q y)) =
            ENNReal.ofReal (gaussDensityReal y) *
              ENNReal.ofReal (gaussBranchRatio q y) := by
        rw [← ENNReal.ofReal_mul (by positivity :
            0 ≤ 1 / (((q : ℝ) + y) ^ 2)),
          inverseBranchJacobian_mul_gaussDensityReal hq hycc,
          gaussBranchDensityReal_eq_ratio_mul_gaussDensityReal hq hycc,
          ENNReal.ofReal_mul (gaussBranchRatio_pos hq hycc).le]
        rw [mul_comm]
      calc
        ENNReal.ofReal (1 / (((q : ℝ) + y) ^ 2)) *
            (ENNReal.ofReal
                (gaussDensityReal (gaussInverseBranch q y)) *
              u (gaussInverseBranch q y)) =
            (ENNReal.ofReal (1 / (((q : ℝ) + y) ^ 2)) *
              ENNReal.ofReal
                (gaussDensityReal (gaussInverseBranch q y))) *
              u (gaussInverseBranch q y) := by rw [mul_assoc]
        _ = (ENNReal.ofReal (gaussDensityReal y) *
              ENNReal.ofReal (gaussBranchRatio q y)) *
              u (gaussInverseBranch q y) := by rw [hcore]
        _ = ENNReal.ofReal (gaussDensityReal y) *
              (ENNReal.ofReal (gaussBranchRatio q y) *
                u (gaussInverseBranch q y)) := by rw [mul_assoc]
    _ = ∫⁻ y in s,
        ENNReal.ofReal (gaussBranchRatio q y) *
          u (gaussInverseBranch q y) ∂volume.withDensity gaussDensity := by
      have hwith := setLIntegral_withDensity_eq_setLIntegral_mul volume
        measurable_gaussDensity hcomp hsM
      exact hwith.symm

/-! ## Countable branch summation -/

/-- The nonnegative version of the normalized transfer operator.  Keeping
this object in `ℝ≥0∞` lets Tonelli's theorem handle the countable branch sum
without any prior integrability assumption. -/
def gaussTransferENN (f : ℝ → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ,
    ENNReal.ofReal (gaussBranchRatio (n + 1) y) *
      f (gaussInverseBranch (n + 1) y)

theorem measurable_gaussTransferENN {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (gaussTransferENN f) := by
  unfold gaussTransferENN
  apply Measurable.ennreal_tsum
  intro n
  exact (measurable_ofReal_gaussBranchRatio (n + 1)).mul
    (hf.comp (measurable_gaussInverseBranch (n + 1)))

/-- The half-open interval used by the inverse-branch parametrization has
full Gauss measure. -/
theorem gaussMeasure_Ico_ae :
    ∀ᵐ y ∂gaussMeasure, y ∈ Ico (0 : ℝ) 1 :=
  (mem_ae_iff_prob_eq_one measurableSet_Ico).2 gaussMeasure_Ico_unit

theorem pairwise_disjoint_gaussInverseBranch_images
    (s : Set ℝ) :
    Pairwise fun m n : ℕ =>
      Disjoint
        (gaussInverseBranch (m + 1) '' (s ∩ Ico (0 : ℝ) 1))
        (gaussInverseBranch (n + 1) '' (s ∩ Ico (0 : ℝ) 1)) := by
  intro m n hmn
  apply (pairwise_disjoint_firstDigitCylinder hmn).mono
  · rw [← gaussMap_preimage_inter_firstDigitCylinder s (m + 1) (by omega)]
    exact inter_subset_right
  · rw [← gaussMap_preimage_inter_firstDigitCylinder s (n + 1) (by omega)]
    exact inter_subset_right

/-- Perron--Frobenius adjoint identity for the normalized Gauss kernel,
stated at the nonnegative integral level.  Both endpoint conventions are
made explicit: branch tails use `[0,1)`, while Gauss measure is supported on
`(0,1]`; the discrepancy consists of null singletons. -/
theorem setLIntegral_gaussTransferENN
    {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    {s : Set ℝ} (hsM : MeasurableSet s) :
    (∫⁻ y in s, gaussTransferENN f y ∂gaussMeasure) =
      ∫⁻ x in gaussMap ⁻¹' s, f x ∂gaussMeasure := by
  let tail : Set ℝ := s ∩ Ico (0 : ℝ) 1
  have htailM : MeasurableSet tail := hsM.inter measurableSet_Ico
  have htail : tail ⊆ Icc (0 : ℝ) 1 := by
    intro y hy
    exact ⟨hy.2.1, hy.2.2.le⟩
  have hsAE : s =ᵐ[gaussMeasure] tail := by
    filter_upwards [gaussMeasure_Ico_ae] with y hy
    apply propext
    constructor
    · intro hys
      exact ⟨hys, hy⟩
    · intro hytail
      exact hytail.1
  have hpreAE : (gaussMap ⁻¹' s : Set ℝ) =ᵐ[gaussMeasure]
      ((gaussMap ⁻¹' s) ∩ Ioc (0 : ℝ) 1 : Set ℝ) := by
    filter_upwards [gaussMeasure_unit_ae] with x hx
    apply propext
    constructor
    · intro hxs
      exact ⟨hxs, hx⟩
    · intro hxinter
      exact hxinter.1
  have himageM : ∀ n : ℕ, MeasurableSet
      (gaussInverseBranch (n + 1) '' tail) := by
    intro n
    exact measurableSet_gaussInverseBranch_image (by omega) htailM htail
  calc
    (∫⁻ y in s, gaussTransferENN f y ∂gaussMeasure) =
        ∫⁻ y in tail, gaussTransferENN f y ∂gaussMeasure := by
      rw [Measure.restrict_congr_set hsAE]
    _ = ∫⁻ y in tail, ∑' n : ℕ,
          ENNReal.ofReal (gaussBranchRatio (n + 1) y) *
            f (gaussInverseBranch (n + 1) y) ∂gaussMeasure := rfl
    _ = ∑' n : ℕ, ∫⁻ y in tail,
          ENNReal.ofReal (gaussBranchRatio (n + 1) y) *
            f (gaussInverseBranch (n + 1) y) ∂gaussMeasure := by
      rw [lintegral_tsum]
      intro n
      exact ((measurable_ofReal_gaussBranchRatio (n + 1)).mul
        (hf.comp (measurable_gaussInverseBranch (n + 1)))).aemeasurable
    _ = ∑' n : ℕ,
        ∫⁻ x in gaussInverseBranch (n + 1) '' tail,
          f x ∂gaussMeasure := by
      apply tsum_congr
      intro n
      exact (gaussBranch_lintegral_change (q := n + 1) (by omega)
        htailM htail f hf).symm
    _ = ∫⁻ x in ⋃ n : ℕ,
        gaussInverseBranch (n + 1) '' tail, f x ∂gaussMeasure := by
      exact (lintegral_iUnion himageM
        (pairwise_disjoint_gaussInverseBranch_images s) f).symm
    _ = ∫⁻ x in gaussMap ⁻¹' s ∩ Ioc (0 : ℝ) 1,
        f x ∂gaussMeasure := by
      rw [gaussMap_preimage_inter_unit]
    _ = ∫⁻ x in gaussMap ⁻¹' s, f x ∂gaussMeasure := by
      rw [Measure.restrict_congr_set hpreAE]

/-- In particular, the nonnegative transfer operator preserves the Gauss
mean. -/
theorem lintegral_gaussTransferENN
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, gaussTransferENN f y ∂gaussMeasure) =
      ∫⁻ x, f x ∂gaussMeasure := by
  have h := setLIntegral_gaussTransferENN hf (s := Set.univ)
    MeasurableSet.univ
  simpa only [Measure.restrict_univ, preimage_univ] using! h

/-- Measurability is retained under every finite iterate of the nonnegative
transfer operator. -/
theorem measurable_gaussTransferENN_iterate
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (m : ℕ) :
    Measurable ((gaussTransferENN^[m]) f) := by
  induction m with
  | zero => simpa using! hf
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact measurable_gaussTransferENN ih

/-- Iterated adjoint identity, with the order of composition written using
the already established Gauss orbit convention. -/
theorem setLIntegral_gaussTransferENN_iterate
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (m : ℕ)
    {s : Set ℝ} (hsM : MeasurableSet s) :
    (∫⁻ y in s, (gaussTransferENN^[m]) f y ∂gaussMeasure) =
      ∫⁻ x in (gaussOrbit m) ⁻¹' s, f x ∂gaussMeasure := by
  induction m generalizing s with
  | zero =>
      have horbit : gaussOrbit 0 = id := by
        funext x
        exact gaussOrbit_zero x
      rw [horbit, Set.preimage_id]
      rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      rw [setLIntegral_gaussTransferENN
        (measurable_gaussTransferENN_iterate hf m) hsM]
      rw [ih (hsM.preimage measurable_gaussMap)]
      have hset : (gaussOrbit m) ⁻¹' (gaussMap ⁻¹' s) =
          (gaussOrbit (m + 1)) ⁻¹' s := by
        ext x
        change (gaussMap (gaussOrbit m x) ∈ s) ↔
          (gaussOrbit (m + 1) x ∈ s)
        rw [gaussOrbit_succ]
      rw [hset]

/-- Every iterate preserves the total Gauss mean. -/
theorem lintegral_gaussTransferENN_iterate
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (m : ℕ) :
    (∫⁻ y, (gaussTransferENN^[m]) f y ∂gaussMeasure) =
      ∫⁻ x, f x ∂gaussMeasure := by
  have h := setLIntegral_gaussTransferENN_iterate hf m
    (s := Set.univ) MeasurableSet.univ
  simpa only [Measure.restrict_univ, preimage_univ] using! h

/-! ## Comparison with the real transfer operator -/

def GaussUnitNonnegative (f : ℝ → ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ Icc (0 : ℝ) 1 → 0 ≤ f x

def GaussUnitUpperBound (A : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ Icc (0 : ℝ) 1 → f x ≤ A

theorem summable_gaussTransfer_branch_of_unit_bounds
    {A : ℝ} {f : ℝ → ℝ}
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    Summable fun n : ℕ =>
      gaussBranchRatio (n + 1) y *
        f (gaussInverseBranch (n + 1) y) := by
  have hweights : Summable fun n : ℕ =>
      gaussBranchRatio (n + 1) y :=
    (hasSum_gaussBranchRatio y hy).summable
  have hmajor : Summable fun n : ℕ =>
      gaussBranchRatio (n + 1) y * A := hweights.mul_right A
  apply Summable.of_norm_bounded hmajor
  intro n
  have hn : 0 < n + 1 := by omega
  have hi := gaussInverseBranch_mem_Icc (n + 1) hn hy
  have hratio : 0 ≤ gaussBranchRatio (n + 1) y :=
    (gaussBranchRatio_pos hn hy).le
  have hterm : 0 ≤ gaussBranchRatio (n + 1) y *
      f (gaussInverseBranch (n + 1) y) :=
    mul_nonneg hratio (hf0 hi)
  rw [Real.norm_eq_abs, abs_of_nonneg hterm]
  exact mul_le_mul_of_nonneg_left (hfA hi) hratio

theorem gaussTransfer_nonnegative_of_unit_bounds
    {f : ℝ → ℝ} (hf0 : GaussUnitNonnegative f) :
    GaussUnitNonnegative (gaussTransfer f) := by
  intro y hy
  unfold gaussTransfer
  exact tsum_nonneg fun n => mul_nonneg
    (gaussBranchRatio_pos (by omega) hy).le
    (hf0 (gaussInverseBranch_mem_Icc (n + 1) (by omega) hy))

theorem gaussTransfer_upperBound_of_unit_bounds
    {A : ℝ} {f : ℝ → ℝ}
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f) :
    GaussUnitUpperBound A (gaussTransfer f) := by
  intro y hy
  have hs := summable_gaussTransfer_branch_of_unit_bounds hf0 hfA hy
  have hweights : Summable fun n : ℕ =>
      gaussBranchRatio (n + 1) y :=
    (hasSum_gaussBranchRatio y hy).summable
  unfold gaussTransfer
  calc
    (∑' n : ℕ, gaussBranchRatio (n + 1) y *
        f (gaussInverseBranch (n + 1) y)) ≤
      ∑' n : ℕ, gaussBranchRatio (n + 1) y * A := by
        exact Summable.tsum_le_tsum (fun n =>
          mul_le_mul_of_nonneg_left
            (hfA (gaussInverseBranch_mem_Icc (n + 1) (by omega) hy))
            (gaussBranchRatio_pos (by omega) hy).le)
          hs (hweights.mul_right A)
    _ = A * ∑' n : ℕ, gaussBranchRatio (n + 1) y := by
      simp_rw [mul_comm (gaussBranchRatio _ _) A]
      rw [tsum_mul_left]
    _ = A := by rw [(hasSum_gaussBranchRatio y hy).tsum_eq, mul_one]

theorem ofReal_gaussTransfer_eq_gaussTransferENN
    {A : ℝ} {f : ℝ → ℝ}
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    ENNReal.ofReal (gaussTransfer f y) =
      gaussTransferENN (fun x => ENNReal.ofReal (f x)) y := by
  have hs := summable_gaussTransfer_branch_of_unit_bounds hf0 hfA hy
  unfold gaussTransfer gaussTransferENN
  rw [ENNReal.ofReal_tsum_of_nonneg]
  · apply tsum_congr
    intro n
    have hn : 0 < n + 1 := by omega
    have hi := gaussInverseBranch_mem_Icc (n + 1) hn hy
    rw [ENNReal.ofReal_mul (gaussBranchRatio_pos hn hy).le]
  · intro n
    exact mul_nonneg (gaussBranchRatio_pos (by omega) hy).le
      (hf0 (gaussInverseBranch_mem_Icc (n + 1) (by omega) hy))
  · exact hs

theorem gaussTransfer_iterate_unit_bounds
    {A : ℝ} {f : ℝ → ℝ}
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    (m : ℕ) :
    GaussUnitNonnegative ((gaussTransfer^[m]) f) ∧
      GaussUnitUpperBound A ((gaussTransfer^[m]) f) := by
  induction m with
  | zero => exact ⟨hf0, hfA⟩
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨gaussTransfer_nonnegative_of_unit_bounds ih.1,
        gaussTransfer_upperBound_of_unit_bounds ih.1 ih.2⟩

theorem ofReal_gaussTransfer_iterate_eq_gaussTransferENN_iterate
    {A : ℝ} {f : ℝ → ℝ}
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    (m : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    ENNReal.ofReal ((gaussTransfer^[m]) f y) =
      (gaussTransferENN^[m]) (fun x => ENNReal.ofReal (f x)) y := by
  induction m generalizing y with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hb := gaussTransfer_iterate_unit_bounds hf0 hfA m
      rw [ofReal_gaussTransfer_eq_gaussTransferENN hb.1 hb.2 hy]
      unfold gaussTransferENN
      apply tsum_congr
      intro n
      congr 1
      exact ih (gaussInverseBranch_mem_Icc (n + 1) (by omega) hy)

/-! ## Lipschitz contraction without an artificial centering hypothesis -/

theorem gaussTransfer_eq_centered_add
    {A : ℝ} {f : ℝ → ℝ}
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    gaussTransfer f y =
      gaussTransfer (fun x => f x - f 0) y + f 0 := by
  let g : ℝ → ℝ := fun x => f x - f 0
  let c : ℕ → ℝ := fun n => gaussBranchRatio (n + 1) y * f 0
  have hsf := summable_gaussTransfer_branch_of_unit_bounds hf0 hfA hy
  have hsc : Summable c :=
    ((hasSum_gaussBranchRatio y hy).summable.mul_right (f 0))
  have hsg : Summable fun n : ℕ =>
      gaussBranchRatio (n + 1) y * g (gaussInverseBranch (n + 1) y) := by
    have hsub := hsf.sub hsc
    apply hsub.congr
    intro n
    dsimp only [g, c]
    ring
  unfold gaussTransfer
  calc
    (∑' n : ℕ, gaussBranchRatio (n + 1) y *
        f (gaussInverseBranch (n + 1) y)) =
      ∑' n : ℕ,
        (gaussBranchRatio (n + 1) y *
            g (gaussInverseBranch (n + 1) y) + c n) := by
      apply tsum_congr
      intro n
      dsimp only [g, c]
      ring
    _ = (∑' n : ℕ, gaussBranchRatio (n + 1) y *
          g (gaussInverseBranch (n + 1) y)) + ∑' n : ℕ, c n := by
      exact hsg.tsum_add hsc
    _ = (∑' n : ℕ, gaussBranchRatio (n + 1) y *
          g (gaussInverseBranch (n + 1) y)) + f 0 := by
      rw [show (∑' n : ℕ, c n) = f 0 by
        dsimp only [c]
        rw [tsum_mul_right, (hasSum_gaussBranchRatio y hy).tsum_eq,
          one_mul]]

theorem gaussTransfer_strict_lipschitz_contraction_general
    {A K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K)
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    (hf : GaussUnitLipschitzBound K f) :
    GaussUnitLipschitzBound ((527 / 540 : ℝ) * K)
      (gaussTransfer f) := by
  let g : ℝ → ℝ := fun x => f x - f 0
  have hg0 : g 0 = 0 := by simp [g]
  have hg : GaussUnitLipschitzBound K g := by
    intro y hy z hz
    simpa only [g, sub_sub_sub_cancel_right] using! hf hy hz
  have hcontract := gaussTransfer_strict_lipschitz_contraction hK hg0 hg
  intro y hy z hz
  rw [gaussTransfer_eq_centered_add hf0 hfA hy,
    gaussTransfer_eq_centered_add hf0 hfA hz]
  simpa only [g, add_sub_add_right_eq_sub] using! hcontract hy hz

theorem gaussTransfer_iterate_lipschitz
    {A K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K)
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    (hf : GaussUnitLipschitzBound K f) (m : ℕ) :
    GaussUnitLipschitzBound ((527 / 540 : ℝ) ^ m * K)
      ((gaussTransfer^[m]) f) := by
  induction m with
  | zero => simpa using! hf
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      have hb := gaussTransfer_iterate_unit_bounds hf0 hfA m
      have hstep := gaussTransfer_strict_lipschitz_contraction_general
        (mul_nonneg (by positivity) hK) hb.1 hb.2 ih
      convert! hstep using 1
      ring

/-! ## Finite one-digit events and their normalized densities -/

/-- The finite digit set is indexed as in `finiteGaussDigitTailDensity`:
`n` denotes the genuine continued-fraction digit `n+1`. -/
def finiteGaussDigitEvent (digits : Finset ℕ) : Set ℝ :=
  ⋃ n ∈ digits, firstDigitCylinder (n + 1)

theorem measurableSet_finiteGaussDigitEvent (digits : Finset ℕ) :
    MeasurableSet (finiteGaussDigitEvent digits) := by
  unfold finiteGaussDigitEvent
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ =>
    measurableSet_Ioc

theorem pairwiseDisjoint_firstDigitCylinder_on_finset (digits : Finset ℕ) :
    (↑digits : Set ℕ).PairwiseDisjoint
      (fun n => firstDigitCylinder (n + 1)) := by
  intro m _hm n _hn hmn
  exact pairwise_disjoint_firstDigitCylinder hmn

theorem gaussMeasure_finiteGaussDigitEvent (digits : Finset ℕ) :
    gaussMeasure (finiteGaussDigitEvent digits) =
      ∑ n ∈ digits, gaussMeasure (firstDigitCylinder (n + 1)) := by
  unfold finiteGaussDigitEvent
  exact measure_biUnion_finset
    (pairwiseDisjoint_firstDigitCylinder_on_finset digits)
    (fun n _ => measurableSet_Ioc)

theorem gaussMeasure_real_finiteGaussDigitEvent (digits : Finset ℕ) :
    gaussMeasure.real (finiteGaussDigitEvent digits) =
      finiteGaussDigitProbability digits := by
  rw [measureReal_def, gaussMeasure_finiteGaussDigitEvent]
  unfold finiteGaussDigitProbability
  rw [ENNReal.toReal_sum (fun n hn => measure_ne_top _ _)]
  apply Finset.sum_congr rfl
  intro n hn
  rfl

theorem measurable_finiteGaussDigitTailDensity (digits : Finset ℕ) :
    Measurable (finiteGaussDigitTailDensity digits) := by
  unfold finiteGaussDigitTailDensity
  have hsum : StronglyMeasurable
      (∑ n ∈ digits, fun y => gaussBranchRatio (n + 1) y) := by
    exact Finset.stronglyMeasurable_sum digits fun n _ =>
      (measurable_gaussBranchRatio (n + 1)).stronglyMeasurable
  convert! hsum.measurable using 1
  funext y
  simp only [Finset.sum_apply]

theorem finiteGaussDigitTailDensity_le_six_mul_probability
    (digits : Finset ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    finiteGaussDigitTailDensity digits y ≤
      6 * finiteGaussDigitProbability digits := by
  unfold finiteGaussDigitTailDensity finiteGaussDigitProbability
  calc
    (∑ n ∈ digits, gaussBranchRatio (n + 1) y) ≤
      ∑ n ∈ digits,
        6 * gaussMeasure.real (firstDigitCylinder (n + 1)) := by
      apply Finset.sum_le_sum
      intro n hn
      have h := ofReal_gaussBranchRatio_le_six_mul_firstDigitMeasure
        (q := n + 1) (by omega) hy
      have hr := ENNReal.toReal_mono (by finiteness) h
      have hpos := gaussBranchRatio_pos (q := n + 1) (Nat.succ_pos n) hy
      rw [ENNReal.toReal_ofReal hpos.le, ENNReal.toReal_mul,
        ENNReal.toReal_ofNat] at hr
      simpa only [measureReal_def] using! hr
    _ = 6 * ∑ n ∈ digits,
        gaussMeasure.real (firstDigitCylinder (n + 1)) := by
      rw [Finset.mul_sum]

theorem lintegral_finiteGaussDigitTailDensity (digits : Finset ℕ) :
    (∫⁻ y, ENNReal.ofReal (finiteGaussDigitTailDensity digits y)
        ∂gaussMeasure) =
      ENNReal.ofReal (finiteGaussDigitProbability digits) := by
  have hunivAE : (Set.univ : Set ℝ) =ᵐ[gaussMeasure] Ico (0 : ℝ) 1 := by
    filter_upwards [gaussMeasure_Ico_ae] with y hy
    apply propext
    constructor
    · intro _
      exact hy
    · intro _
      trivial
  calc
    (∫⁻ y, ENNReal.ofReal (finiteGaussDigitTailDensity digits y)
        ∂gaussMeasure) =
      ∫⁻ y in Ico (0 : ℝ) 1,
        ENNReal.ofReal (finiteGaussDigitTailDensity digits y)
          ∂gaussMeasure := by
      rw [← setLIntegral_univ
        (μ := gaussMeasure)
        (fun y => ENNReal.ofReal
          (finiteGaussDigitTailDensity digits y)),
        Measure.restrict_congr_set hunivAE]
    _ = ∫⁻ y in Ico (0 : ℝ) 1,
        ∑ n ∈ digits, ENNReal.ofReal (gaussBranchRatio (n + 1) y)
          ∂gaussMeasure := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
      unfold finiteGaussDigitTailDensity
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro n hn
      exact (gaussBranchRatio_pos (by omega)
        (show y ∈ Icc (0 : ℝ) 1 from ⟨hy.1, hy.2.le⟩)).le
    _ = ∑ n ∈ digits, ∫⁻ y in Ico (0 : ℝ) 1,
        ENNReal.ofReal (gaussBranchRatio (n + 1) y)
          ∂gaussMeasure := by
      rw [lintegral_finset_sum]
      intro n hn
      exact measurable_ofReal_gaussBranchRatio (n + 1)
    _ = ∑ n ∈ digits,
        gaussMeasure (firstDigitCylinder (n + 1)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (gaussMeasure_firstDigitCylinder_eq_ratio_lintegral
        (q := n + 1) (by omega)).symm
    _ = ENNReal.ofReal (finiteGaussDigitProbability digits) := by
      unfold finiteGaussDigitProbability
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro n hn
        simp only [measureReal_def]
        exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      · intro n hn
        exact measureReal_nonneg

/-- Conditional density given the selected finite first-digit event. -/
def finiteGaussDigitNormalizedDensity (digits : Finset ℕ) (y : ℝ) : ℝ :=
  finiteGaussDigitTailDensity digits y /
    finiteGaussDigitProbability digits

theorem measurable_finiteGaussDigitNormalizedDensity (digits : Finset ℕ) :
    Measurable (finiteGaussDigitNormalizedDensity digits) := by
  unfold finiteGaussDigitNormalizedDensity
  exact (measurable_finiteGaussDigitTailDensity digits).div_const _

theorem finiteGaussDigitNormalizedDensity_nonnegative
    (digits : Finset ℕ) (hprob : 0 < finiteGaussDigitProbability digits) :
    GaussUnitNonnegative (finiteGaussDigitNormalizedDensity digits) := by
  intro y hy
  unfold finiteGaussDigitNormalizedDensity
  exact div_nonneg (finiteGaussDigitTailDensity_nonneg digits hy) hprob.le

theorem finiteGaussDigitNormalizedDensity_upperBound_six
    (digits : Finset ℕ) (hprob : 0 < finiteGaussDigitProbability digits) :
    GaussUnitUpperBound 6 (finiteGaussDigitNormalizedDensity digits) := by
  intro y hy
  unfold finiteGaussDigitNormalizedDensity
  rw [div_le_iff₀ hprob]
  simpa only [mul_comm] using!
    finiteGaussDigitTailDensity_le_six_mul_probability digits hy

theorem finiteGaussDigitNormalizedDensity_lipschitz
    (digits : Finset ℕ) (hprob : 0 < finiteGaussDigitProbability digits) :
    GaussUnitLipschitzBound 6
      (finiteGaussDigitNormalizedDensity digits) :=
  finiteGaussDigitTailDensity_div_probability_lipschitz digits hprob

theorem lintegral_finiteGaussDigitNormalizedDensity
    (digits : Finset ℕ) (hprob : 0 < finiteGaussDigitProbability digits) :
    (∫⁻ y, ENNReal.ofReal (finiteGaussDigitNormalizedDensity digits y)
        ∂gaussMeasure) = 1 := by
  unfold finiteGaussDigitNormalizedDensity
  simp_rw [ENNReal.ofReal_div_of_pos hprob, div_eq_mul_inv]
  rw [lintegral_mul_const]
  · rw [lintegral_finiteGaussDigitTailDensity]
    exact ENNReal.mul_inv_cancel
      (ENNReal.ofReal_ne_zero_iff.mpr hprob) ENNReal.ofReal_ne_top
  · exact (measurable_finiteGaussDigitTailDensity digits).ennreal_ofReal

/-- A nonnegative function whose Gauss mean is one and whose oscillation is
at most `epsilon` differs from one by at most `epsilon` at every state in the
closed unit interval.  This elementary averaging lemma avoids choosing a
point at which an integral is attained. -/
theorem abs_sub_one_le_of_gaussMean_one_of_unit_lipschitz
    {f : ℝ → ℝ} {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hlip : GaussUnitLipschitzBound epsilon f)
    (hmean : (∫⁻ z, ENNReal.ofReal (f z) ∂gaussMeasure) = 1)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    |f y - 1| ≤ epsilon := by
  have hlower : ENNReal.ofReal (f y - epsilon) ≤ 1 := by
    calc
      ENNReal.ofReal (f y - epsilon) =
          ∫⁻ _z, ENNReal.ofReal (f y - epsilon) ∂gaussMeasure := by simp
      _ ≤ ∫⁻ z, ENNReal.ofReal (f z) ∂gaussMeasure := by
        apply lintegral_mono_ae
        filter_upwards [gaussMeasure_unit_ae] with z hz
        apply ENNReal.ofReal_le_ofReal
        have hzcc : z ∈ Icc (0 : ℝ) 1 := ⟨hz.1.le, hz.2⟩
        have h := hlip hy hzcc
        rw [abs_le] at h
        have habs : |y - z| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith [hy.1, hy.2, hzcc.1, hzcc.2]
        have hmul : epsilon * |y - z| ≤ epsilon := by
          simpa only [mul_one] using!
            mul_le_mul_of_nonneg_left habs hepsilon
        linarith
      _ = 1 := hmean
  have hupper : 1 ≤ ENNReal.ofReal (f y + epsilon) := by
    calc
      1 = ∫⁻ z, ENNReal.ofReal (f z) ∂gaussMeasure := hmean.symm
      _ ≤ ∫⁻ _z, ENNReal.ofReal (f y + epsilon) ∂gaussMeasure := by
        apply lintegral_mono_ae
        filter_upwards [gaussMeasure_unit_ae] with z hz
        apply ENNReal.ofReal_le_ofReal
        have hzcc : z ∈ Icc (0 : ℝ) 1 := ⟨hz.1.le, hz.2⟩
        have h := hlip hy hzcc
        rw [abs_le] at h
        have habs : |y - z| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith [hy.1, hy.2, hzcc.1, hzcc.2]
        have hmul : epsilon * |y - z| ≤ epsilon := by
          simpa only [mul_one] using!
            mul_le_mul_of_nonneg_left habs hepsilon
        linarith
      _ = ENNReal.ofReal (f y + epsilon) := by simp
  rw [ENNReal.ofReal_le_one] at hlower
  rw [ENNReal.one_le_ofReal] at hupper
  rw [abs_le]
  constructor <;> linarith

theorem lintegral_finiteGaussDigitNormalizedDensity_iterate
    (digits : Finset ℕ) (hprob : 0 < finiteGaussDigitProbability digits)
    (m : ℕ) :
    (∫⁻ y, ENNReal.ofReal
        ((gaussTransfer^[m])
          (finiteGaussDigitNormalizedDensity digits) y) ∂gaussMeasure) = 1 := by
  let f : ℝ → ℝ := finiteGaussDigitNormalizedDensity digits
  have hf0 := finiteGaussDigitNormalizedDensity_nonnegative digits hprob
  have hf6 := finiteGaussDigitNormalizedDensity_upperBound_six digits hprob
  have hpoint : ∀ᵐ y ∂gaussMeasure,
      ENNReal.ofReal ((gaussTransfer^[m]) f y) =
        (gaussTransferENN^[m]) (fun x => ENNReal.ofReal (f x)) y := by
    filter_upwards [gaussMeasure_unit_ae] with y hy
    exact ofReal_gaussTransfer_iterate_eq_gaussTransferENN_iterate
      (A := 6) hf0 hf6 m ⟨hy.1.le, hy.2⟩
  calc
    (∫⁻ y, ENNReal.ofReal ((gaussTransfer^[m]) f y)
        ∂gaussMeasure) =
      ∫⁻ y, (gaussTransferENN^[m])
        (fun x => ENNReal.ofReal (f x)) y ∂gaussMeasure :=
      lintegral_congr_ae hpoint
    _ = ∫⁻ y, ENNReal.ofReal (f y) ∂gaussMeasure :=
      lintegral_gaussTransferENN_iterate
        (measurable_finiteGaussDigitNormalizedDensity digits).ennreal_ofReal m
    _ = 1 := lintegral_finiteGaussDigitNormalizedDensity digits hprob

/-- The normalized conditional density loses memory at the explicit rate
`6 (527/540)^m`, uniformly on the Gauss state interval. -/
theorem abs_finiteGaussDigitNormalizedDensity_iterate_sub_one_le
    (digits : Finset ℕ) (hprob : 0 < finiteGaussDigitProbability digits)
    (m : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    |(gaussTransfer^[m]) (finiteGaussDigitNormalizedDensity digits) y - 1| ≤
      6 * (527 / 540 : ℝ) ^ m := by
  have hf0 := finiteGaussDigitNormalizedDensity_nonnegative digits hprob
  have hf6 := finiteGaussDigitNormalizedDensity_upperBound_six digits hprob
  have hlip := gaussTransfer_iterate_lipschitz
    (A := 6) (K := 6) (by norm_num) hf0 hf6
      (finiteGaussDigitNormalizedDensity_lipschitz digits hprob) m
  have hlip' : GaussUnitLipschitzBound
      (6 * (527 / 540 : ℝ) ^ m)
      ((gaussTransfer^[m]) (finiteGaussDigitNormalizedDensity digits)) := by
    convert! hlip using 1
    ring
  exact abs_sub_one_le_of_gaussMean_one_of_unit_lipschitz
    (by positivity) hlip'
    (lintegral_finiteGaussDigitNormalizedDensity_iterate digits hprob m) hy

/-! ## Exact finite-event density formula -/

theorem pairwiseDisjoint_firstDigit_inter_gaussMap_preimage_on_finset
    (digits : Finset ℕ) (B : Set ℝ) :
    (↑digits : Set ℕ).PairwiseDisjoint
      (fun n => firstDigitCylinder (n + 1) ∩ gaussMap ⁻¹' B) := by
  intro m _hm n _hn hmn
  exact (pairwise_disjoint_firstDigitCylinder hmn).mono
    inter_subset_left inter_subset_left

theorem gaussMeasure_finiteGaussDigitEvent_inter_preimage
    (digits : Finset ℕ) {B : Set ℝ} (hBM : MeasurableSet B) :
    gaussMeasure (finiteGaussDigitEvent digits ∩ gaussMap ⁻¹' B) =
      ∫⁻ y in B,
        ENNReal.ofReal (finiteGaussDigitTailDensity digits y)
          ∂gaussMeasure := by
  let tail : Set ℝ := B ∩ Ico (0 : ℝ) 1
  have htailM : MeasurableSet tail := hBM.inter measurableSet_Ico
  have htail : tail ⊆ Icc (0 : ℝ) 1 := by
    intro y hy
    exact ⟨hy.2.1, hy.2.2.le⟩
  have hBAE : B =ᵐ[gaussMeasure] tail := by
    filter_upwards [gaussMeasure_Ico_ae] with y hy
    apply propext
    constructor
    · intro hyB
      exact ⟨hyB, hy⟩
    · intro hytail
      exact hytail.1
  have hset : finiteGaussDigitEvent digits ∩ gaussMap ⁻¹' B =
      ⋃ n ∈ digits,
        (firstDigitCylinder (n + 1) ∩ gaussMap ⁻¹' B) := by
    unfold finiteGaussDigitEvent
    rw [iUnion_inter]
    congr 1
    funext n
    rw [iUnion_inter]
  calc
    gaussMeasure (finiteGaussDigitEvent digits ∩ gaussMap ⁻¹' B) =
      ∑ n ∈ digits,
        gaussMeasure
          (firstDigitCylinder (n + 1) ∩ gaussMap ⁻¹' B) := by
      rw [hset]
      exact measure_biUnion_finset
        (pairwiseDisjoint_firstDigit_inter_gaussMap_preimage_on_finset
          digits B)
        (fun n _ => measurableSet_Ioc.inter
          (hBM.preimage measurable_gaussMap))
    _ = ∑ n ∈ digits, ∫⁻ y in tail,
        ENNReal.ofReal (gaussBranchRatio (n + 1) y)
          ∂gaussMeasure := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [inter_comm,
        gaussMap_preimage_inter_firstDigitCylinder B (n + 1) (by omega)]
      exact gaussMeasure_gaussInverseBranch_image_eq_ratio_lintegral
        (q := n + 1) (by omega) htailM htail
    _ = ∫⁻ y in tail,
        ∑ n ∈ digits,
          ENNReal.ofReal (gaussBranchRatio (n + 1) y)
            ∂gaussMeasure := by
      rw [lintegral_finset_sum]
      intro n hn
      exact measurable_ofReal_gaussBranchRatio (n + 1)
    _ = ∫⁻ y in tail,
        ENNReal.ofReal (finiteGaussDigitTailDensity digits y)
          ∂gaussMeasure := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem htailM] with y hy
      unfold finiteGaussDigitTailDensity
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro n hn
      exact (gaussBranchRatio_pos (by omega) (htail hy)).le
    _ = ∫⁻ y in B,
        ENNReal.ofReal (finiteGaussDigitTailDensity digits y)
          ∂gaussMeasure := by
      rw [Measure.restrict_congr_set hBAE]

/-- At a positive gap, the event intersection is exactly the integral of
the iterated conditional density over the future event. -/
theorem gaussMeasure_finiteGaussDigitEvent_inter_gaussOrbit_preimage
    (digits : Finset ℕ) {B : Set ℝ} (hBM : MeasurableSet B)
    {gap : ℕ} (hgap : 0 < gap) :
    gaussMeasure
        (finiteGaussDigitEvent digits ∩ (gaussOrbit gap) ⁻¹' B) =
      ∫⁻ y in B,
        (gaussTransferENN^[gap - 1])
          (fun x => ENNReal.ofReal
            (finiteGaussDigitTailDensity digits x)) y
          ∂gaussMeasure := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : gap ≠ 0)
  have htailM : MeasurableSet ((gaussOrbit m) ⁻¹' B) :=
    hBM.preimage (measurable_gaussOrbit m)
  have hset : gaussMap ⁻¹' ((gaussOrbit m) ⁻¹' B) =
      (gaussOrbit (m + 1)) ⁻¹' B := by
    ext x
    change (gaussOrbit m (gaussMap x) ∈ B) ↔
      (gaussOrbit (m + 1) x ∈ B)
    rw [gaussOrbit_succ_apply_right]
  rw [show m + 1 - 1 = m by omega]
  rw [setLIntegral_gaussTransferENN_iterate
    (measurable_finiteGaussDigitTailDensity digits).ennreal_ofReal m hBM]
  rw [← hset]
  exact gaussMeasure_finiteGaussDigitEvent_inter_preimage digits htailM

/-! ## Normalized form of the density identity -/

theorem gaussTransferENN_const_mul
    (c : ℝ≥0∞) (f : ℝ → ℝ≥0∞) (y : ℝ) :
    gaussTransferENN (fun x => c * f x) y =
      c * gaussTransferENN f y := by
  unfold gaussTransferENN
  calc
    (∑' n : ℕ, ENNReal.ofReal (gaussBranchRatio (n + 1) y) *
        (c * f (gaussInverseBranch (n + 1) y))) =
      ∑' n : ℕ, c *
        (ENNReal.ofReal (gaussBranchRatio (n + 1) y) *
          f (gaussInverseBranch (n + 1) y)) := by
      apply tsum_congr
      intro n
      ac_rfl
    _ = c * ∑' n : ℕ,
        (ENNReal.ofReal (gaussBranchRatio (n + 1) y) *
          f (gaussInverseBranch (n + 1) y)) := by
      rw [ENNReal.tsum_mul_left]

theorem gaussTransferENN_iterate_const_mul
    (c : ℝ≥0∞) (f : ℝ → ℝ≥0∞) (m : ℕ) (y : ℝ) :
    (gaussTransferENN^[m]) (fun x => c * f x) y =
      c * (gaussTransferENN^[m]) f y := by
  induction m generalizing y with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hfun : (gaussTransferENN^[m]) (fun x => c * f x) =
          fun x => c * (gaussTransferENN^[m]) f x := by
        funext x
        exact ih x
      rw [hfun, gaussTransferENN_const_mul]

def GaussENNUnitEq (f g : ℝ → ℝ≥0∞) : Prop :=
  ∀ ⦃x⦄, x ∈ Icc (0 : ℝ) 1 → f x = g x

theorem gaussTransferENN_unit_congr
    {f g : ℝ → ℝ≥0∞} (hfg : GaussENNUnitEq f g) :
    GaussENNUnitEq (gaussTransferENN f) (gaussTransferENN g) := by
  intro y hy
  unfold gaussTransferENN
  apply tsum_congr
  intro n
  congr 1
  exact hfg (gaussInverseBranch_mem_Icc (n + 1) (by omega) hy)

theorem gaussTransferENN_iterate_unit_congr
    {f g : ℝ → ℝ≥0∞} (hfg : GaussENNUnitEq f g) (m : ℕ) :
    GaussENNUnitEq ((gaussTransferENN^[m]) f)
      ((gaussTransferENN^[m]) g) := by
  induction m with
  | zero => exact hfg
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact gaussTransferENN_unit_congr ih

theorem ofReal_finiteTailDensity_eq_probability_mul_normalized_on_unit
    (digits : Finset ℕ) (hprob : 0 < finiteGaussDigitProbability digits) :
    GaussENNUnitEq
      (fun x => ENNReal.ofReal (finiteGaussDigitTailDensity digits x))
      (fun x => ENNReal.ofReal (finiteGaussDigitProbability digits) *
        ENNReal.ofReal (finiteGaussDigitNormalizedDensity digits x)) := by
  intro x hx
  change ENNReal.ofReal (finiteGaussDigitTailDensity digits x) =
    ENNReal.ofReal (finiteGaussDigitProbability digits) *
      ENNReal.ofReal (finiteGaussDigitNormalizedDensity digits x)
  rw [← ENNReal.ofReal_mul hprob.le]
  congr 1
  unfold finiteGaussDigitNormalizedDensity
  field_simp

theorem gaussMeasure_finiteGaussDigitEvent_inter_gaussOrbit_preimage_normalized
    (digits : Finset ℕ) (hprob : 0 < finiteGaussDigitProbability digits)
    {B : Set ℝ} (hBM : MeasurableSet B) {gap : ℕ} (hgap : 0 < gap) :
    gaussMeasure
        (finiteGaussDigitEvent digits ∩ (gaussOrbit gap) ⁻¹' B) =
      ENNReal.ofReal (finiteGaussDigitProbability digits) *
        ∫⁻ y in B, ENNReal.ofReal
          ((gaussTransfer^[gap - 1])
            (finiteGaussDigitNormalizedDensity digits) y)
          ∂gaussMeasure := by
  let p : ℝ := finiteGaussDigitProbability digits
  let g : ℝ → ℝ := finiteGaussDigitNormalizedDensity digits
  let c : ℝ≥0∞ := ENNReal.ofReal p
  let h : ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (finiteGaussDigitTailDensity digits x)
  let gE : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (g x)
  let m : ℕ := gap - 1
  have hunit : GaussENNUnitEq h (fun x => c * gE x) := by
    simpa only [h, c, gE, g, p] using!
      ofReal_finiteTailDensity_eq_probability_mul_normalized_on_unit
        digits hprob
  have hitUnit := gaussTransferENN_iterate_unit_congr hunit m
  have hrealUnit : ∀ ⦃y⦄, y ∈ Icc (0 : ℝ) 1 →
      (gaussTransferENN^[m]) gE y =
        ENNReal.ofReal ((gaussTransfer^[m]) g y) := by
    intro y hy
    exact (ofReal_gaussTransfer_iterate_eq_gaussTransferENN_iterate
      (A := 6)
      (finiteGaussDigitNormalizedDensity_nonnegative digits hprob)
      (finiteGaussDigitNormalizedDensity_upperBound_six digits hprob)
      m hy).symm
  rw [gaussMeasure_finiteGaussDigitEvent_inter_gaussOrbit_preimage
    digits hBM hgap]
  change (∫⁻ y in B, (gaussTransferENN^[m]) h y ∂gaussMeasure) = _
  calc
    (∫⁻ y in B, (gaussTransferENN^[m]) h y ∂gaussMeasure) =
      ∫⁻ y in B, c * (gaussTransferENN^[m]) gE y ∂gaussMeasure := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae gaussMeasure_unit_ae] with y hy
      calc
        (gaussTransferENN^[m]) h y =
            (gaussTransferENN^[m]) (fun x => c * gE x) y :=
          hitUnit ⟨hy.1.le, hy.2⟩
        _ = c * (gaussTransferENN^[m]) gE y :=
          gaussTransferENN_iterate_const_mul c gE m y
    _ = c * ∫⁻ y in B, (gaussTransferENN^[m]) gE y
          ∂gaussMeasure := by
      rw [lintegral_const_mul]
      exact measurable_gaussTransferENN_iterate
        (measurable_finiteGaussDigitNormalizedDensity digits).ennreal_ofReal m
    _ = c * ∫⁻ y in B,
        ENNReal.ofReal ((gaussTransfer^[m]) g y) ∂gaussMeasure := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae gaussMeasure_unit_ae] with y hy
      exact hrealUnit ⟨hy.1.le, hy.2⟩

theorem gaussMeasureReal_finiteGaussDigitEvent_inter_gaussOrbit_preimage_eq
    (digits : Finset ℕ) (hprob : 0 < finiteGaussDigitProbability digits)
    {B : Set ℝ} (hBM : MeasurableSet B) {gap : ℕ} (hgap : 0 < gap) :
    gaussMeasure.real
        (finiteGaussDigitEvent digits ∩ (gaussOrbit gap) ⁻¹' B) =
      finiteGaussDigitProbability digits *
        (∫⁻ y in B, ENNReal.ofReal
          ((gaussTransfer^[gap - 1])
            (finiteGaussDigitNormalizedDensity digits) y)
          ∂gaussMeasure).toReal := by
  have h := congrArg ENNReal.toReal
    (gaussMeasure_finiteGaussDigitEvent_inter_gaussOrbit_preimage_normalized
      digits hprob hBM hgap)
  simpa only [measureReal_def, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hprob.le] using! h

/-- Turning a uniform pointwise density error into the corresponding
relative event-probability error.  The proof stays at the `lintegral` level,
so no hidden measurability claim about a conditionally convergent real series
is needed. -/
theorem abs_setLIntegral_toReal_sub_measureReal_le
    {f : ℝ → ℝ} {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hf0 : GaussUnitNonnegative f)
    (hclose : ∀ ⦃y⦄, y ∈ Icc (0 : ℝ) 1 → |f y - 1| ≤ epsilon)
    {B : Set ℝ} :
    |(∫⁻ y in B, ENNReal.ofReal (f y) ∂gaussMeasure).toReal -
        gaussMeasure.real B| ≤
      epsilon * gaussMeasure.real B := by
  let I : ℝ≥0∞ := ∫⁻ y in B, ENNReal.ofReal (f y) ∂gaussMeasure
  let M : ℝ≥0∞ := gaussMeasure B
  have hupperENN : I ≤ ENNReal.ofReal (1 + epsilon) * M := by
    calc
      I ≤ ∫⁻ _y in B, ENNReal.ofReal (1 + epsilon)
            ∂gaussMeasure := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae gaussMeasure_unit_ae] with y hy
        apply ENNReal.ofReal_le_ofReal
        have hc := hclose ⟨hy.1.le, hy.2⟩
        rw [abs_le] at hc
        linarith
      _ = ENNReal.ofReal (1 + epsilon) * M := by simp [M]
  have hrightTop : ENNReal.ofReal (1 + epsilon) * M ≠ ⊤ := by
    finiteness
  have hITop : I ≠ ⊤ := ne_top_of_le_ne_top hrightTop hupperENN
  have hupperReal := ENNReal.toReal_mono hrightTop hupperENN
  have hupper : I.toReal ≤ (1 + epsilon) * M.toReal := by
    simpa only [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 + epsilon)] using! hupperReal
  have hlowerENN : M ≤ I + ENNReal.ofReal epsilon * M := by
    calc
      M = ∫⁻ _y in B, (1 : ℝ≥0∞) ∂gaussMeasure := by simp [M]
      _ ≤ ∫⁻ y in B,
          (ENNReal.ofReal (f y) + ENNReal.ofReal epsilon)
            ∂gaussMeasure := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae gaussMeasure_unit_ae] with y hy
        have hycc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
        have hc := hclose hycc
        rw [abs_le] at hc
        calc
          (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by norm_num
          _ ≤ ENNReal.ofReal (f y + epsilon) :=
            ENNReal.ofReal_le_ofReal (by linarith)
          _ = ENNReal.ofReal (f y) + ENNReal.ofReal epsilon := by
            rw [ENNReal.ofReal_add (hf0 hycc) hepsilon]
      _ = I + ENNReal.ofReal epsilon * M := by
        rw [lintegral_add_right]
        · simp only [I, M]
          rw [setLIntegral_const]
        · exact measurable_const
  have hepsMTop : ENNReal.ofReal epsilon * M ≠ ⊤ := by finiteness
  have hsumTop : I + ENNReal.ofReal epsilon * M ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hITop, hepsMTop⟩
  have hlowerReal := ENNReal.toReal_mono hsumTop hlowerENN
  have hlower : M.toReal ≤ I.toReal + epsilon * M.toReal := by
    rw [ENNReal.toReal_add hITop hepsMTop,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hepsilon] at hlowerReal
    exact hlowerReal
  change |I.toReal - M.toReal| ≤ epsilon * M.toReal
  rw [abs_le]
  constructor <;> linarith

/-- Explicit exponentially decaying relative mixing for a nonempty finite
first-digit event and an arbitrary measurable future event. -/
theorem gaussMeasureReal_finiteGaussDigitEvent_inter_gaussOrbit_preimage_error_le
    (digits : Finset ℕ) (hprob : 0 < finiteGaussDigitProbability digits)
    {B : Set ℝ} (hBM : MeasurableSet B) {gap : ℕ} (hgap : 0 < gap) :
    |gaussMeasure.real
        (finiteGaussDigitEvent digits ∩ (gaussOrbit gap) ⁻¹' B) -
      gaussMeasure.real (finiteGaussDigitEvent digits) *
        gaussMeasure.real B| ≤
      (6 * (527 / 540 : ℝ) ^ (gap - 1)) *
        gaussMeasure.real (finiteGaussDigitEvent digits) *
          gaussMeasure.real B := by
  let m : ℕ := gap - 1
  let g : ℝ → ℝ := finiteGaussDigitNormalizedDensity digits
  let I : ℝ := (∫⁻ y in B, ENNReal.ofReal
    ((gaussTransfer^[m]) g y) ∂gaussMeasure).toReal
  let p : ℝ := finiteGaussDigitProbability digits
  have hrepr :=
    gaussMeasureReal_finiteGaussDigitEvent_inter_gaussOrbit_preimage_eq
      digits hprob hBM hgap
  have hdev : |I - gaussMeasure.real B| ≤
      (6 * (527 / 540 : ℝ) ^ m) * gaussMeasure.real B := by
    apply abs_setLIntegral_toReal_sub_measureReal_le (by positivity)
      (gaussTransfer_iterate_unit_bounds (A := 6)
        (finiteGaussDigitNormalizedDensity_nonnegative digits hprob)
        (finiteGaussDigitNormalizedDensity_upperBound_six digits hprob) m).1
    intro y hy
    exact abs_finiteGaussDigitNormalizedDensity_iterate_sub_one_le
      digits hprob m hy
  rw [hrepr, gaussMeasure_real_finiteGaussDigitEvent]
  change |p * I - p * gaussMeasure.real B| ≤
    (6 * (527 / 540 : ℝ) ^ m) * p * gaussMeasure.real B
  rw [← mul_sub, abs_mul, abs_of_pos hprob]
  calc
    p * |I - gaussMeasure.real B| ≤
        p * ((6 * (527 / 540 : ℝ) ^ m) *
          gaussMeasure.real B) :=
      mul_le_mul_of_nonneg_left hdev hprob.le
    _ = (6 * (527 / 540 : ℝ) ^ m) * p *
        gaussMeasure.real B := by ring

/-- The same finite-event estimate, including the zero-probability case. -/
theorem gaussMeasureReal_finiteGaussDigitEvent_inter_gaussOrbit_preimage_error_le'
    (digits : Finset ℕ) {B : Set ℝ} (hBM : MeasurableSet B)
    {gap : ℕ} (hgap : 0 < gap) :
    |gaussMeasure.real
        (finiteGaussDigitEvent digits ∩ (gaussOrbit gap) ⁻¹' B) -
      gaussMeasure.real (finiteGaussDigitEvent digits) *
        gaussMeasure.real B| ≤
      (6 * (527 / 540 : ℝ) ^ (gap - 1)) *
        gaussMeasure.real (finiteGaussDigitEvent digits) *
          gaussMeasure.real B := by
  by_cases hp : finiteGaussDigitProbability digits = 0
  · have hevent : gaussMeasure.real (finiteGaussDigitEvent digits) = 0 := by
      rw [gaussMeasure_real_finiteGaussDigitEvent, hp]
    have hinterLe : gaussMeasure.real
        (finiteGaussDigitEvent digits ∩ (gaussOrbit gap) ⁻¹' B) ≤
        gaussMeasure.real (finiteGaussDigitEvent digits) :=
      measureReal_mono inter_subset_left
    have hinter : gaussMeasure.real
        (finiteGaussDigitEvent digits ∩ (gaussOrbit gap) ⁻¹' B) = 0 :=
      le_antisymm (by simpa only [hevent] using! hinterLe) measureReal_nonneg
    rw [hinter, hevent]
    simp
  · exact
      gaussMeasureReal_finiteGaussDigitEvent_inter_gaussOrbit_preimage_error_le
        digits (lt_of_le_of_ne (finiteGaussDigitProbability_nonneg digits)
          (Ne.symm hp)) hBM hgap

/-! ## Passage from finite digit sets to arbitrary one-digit events -/

def truncatedGaussDigitIndices (digits : Set ℕ) (R : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range R).filter fun n => n + 1 ∈ digits

def truncatedGaussOneDigitEvent (digits : Set ℕ) (R : ℕ) : Set ℝ :=
  finiteGaussDigitEvent (truncatedGaussDigitIndices digits R)

theorem truncatedGaussOneDigitEvent_eq_biUnion
    (digits : Set ℕ) (R : ℕ) :
    truncatedGaussOneDigitEvent digits R =
      ⋃ n ∈ Finset.range R, selectedGaussDigitCylinder digits n := by
  ext x
  simp only [truncatedGaussOneDigitEvent, finiteGaussDigitEvent,
    truncatedGaussDigitIndices, Finset.mem_filter, Finset.mem_range,
    mem_iUnion]
  constructor
  · rintro ⟨n, ⟨hnR, hnd⟩, hxcyl⟩
    refine ⟨n, hnR, ?_⟩
    simp only [selectedGaussDigitCylinder, if_pos hnd]
    exact hxcyl
  · rintro ⟨n, hnR, hxsel⟩
    by_cases hnd : n + 1 ∈ digits
    · refine ⟨n, ⟨hnR, hnd⟩, ?_⟩
      simpa only [selectedGaussDigitCylinder, if_pos hnd] using! hxsel
    · simp only [selectedGaussDigitCylinder, if_neg hnd,
        mem_empty_iff_false] at hxsel

theorem monotone_truncatedGaussOneDigitEvent (digits : Set ℕ) :
    Monotone (truncatedGaussOneDigitEvent digits) := by
  intro R S hRS x hx
  rw [truncatedGaussOneDigitEvent_eq_biUnion] at hx ⊢
  obtain ⟨n, hnR, hxn⟩ := mem_iUnion₂.mp hx
  exact mem_iUnion₂.mpr ⟨n, Finset.mem_range.mpr
    ((Finset.mem_range.mp hnR).trans_le hRS), hxn⟩

theorem iUnion_truncatedGaussOneDigitEvent (digits : Set ℕ) :
    (⋃ R : ℕ, truncatedGaussOneDigitEvent digits R) =
      Ioc (0 : ℝ) 1 ∩ gaussFirstDigitNat ⁻¹' digits := by
  rw [← iUnion_selectedGaussDigitCylinder digits]
  ext x
  constructor
  · rintro hx
    obtain ⟨R, hxR⟩ := mem_iUnion.mp hx
    rw [truncatedGaussOneDigitEvent_eq_biUnion] at hxR
    obtain ⟨n, hnR, hxn⟩ := mem_iUnion₂.mp hxR
    exact mem_iUnion.mpr ⟨n, hxn⟩
  · rintro hx
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
    apply mem_iUnion.mpr
    refine ⟨n + 1, ?_⟩
    rw [truncatedGaussOneDigitEvent_eq_biUnion]
    exact mem_iUnion₂.mpr ⟨n, Finset.mem_range.mpr (by omega), hxn⟩

/-- Exponential relative mixing for an arbitrary union of first-digit
cylinders.  The proof is the monotone limit of the finite theorem above; no
spectral statement for an infinite normalized density is assumed. -/
theorem gaussMeasureReal_oneDigitSet_inter_gaussOrbit_preimage_error_le
    (digits : Set ℕ) {B : Set ℝ} (hBM : MeasurableSet B)
    {gap : ℕ} (hgap : 0 < gap) :
    |gaussMeasure.real
        ((Ioc (0 : ℝ) 1 ∩ gaussFirstDigitNat ⁻¹' digits) ∩
          (gaussOrbit gap) ⁻¹' B) -
      gaussMeasure.real
          (Ioc (0 : ℝ) 1 ∩ gaussFirstDigitNat ⁻¹' digits) *
        gaussMeasure.real B| ≤
      (6 * (527 / 540 : ℝ) ^ (gap - 1)) *
        gaussMeasure.real
          (Ioc (0 : ℝ) 1 ∩ gaussFirstDigitNat ⁻¹' digits) *
          gaussMeasure.real B := by
  let A : Set ℝ := Ioc (0 : ℝ) 1 ∩ gaussFirstDigitNat ⁻¹' digits
  let F : Set ℝ := (gaussOrbit gap) ⁻¹' B
  let AR : ℕ → Set ℝ := truncatedGaussOneDigitEvent digits
  let eps : ℝ := 6 * (527 / 540 : ℝ) ^ (gap - 1)
  have hmonoA : Monotone AR := monotone_truncatedGaussOneDigitEvent digits
  have hunionA : (⋃ R : ℕ, AR R) = A := by
    exact iUnion_truncatedGaussOneDigitEvent digits
  have hmonoI : Monotone fun R => AR R ∩ F := by
    intro R S hRS
    exact inter_subset_inter_left F (hmonoA hRS)
  have hunionI : (⋃ R : ℕ, AR R ∩ F) = A ∩ F := by
    ext x
    constructor
    · rintro hx
      obtain ⟨R, hxR⟩ := mem_iUnion.mp hx
      exact ⟨by
        rw [← hunionA]
        exact mem_iUnion.mpr ⟨R, hxR.1⟩, hxR.2⟩
    · rintro ⟨hxA, hxF⟩
      rw [← hunionA] at hxA
      obtain ⟨R, hxR⟩ := mem_iUnion.mp hxA
      exact mem_iUnion.mpr ⟨R, hxR, hxF⟩
  have hAENN := tendsto_measure_iUnion_atTop
    (μ := gaussMeasure) hmonoA
  rw [hunionA] at hAENN
  have hIENN := tendsto_measure_iUnion_atTop
    (μ := gaussMeasure) hmonoI
  rw [hunionI] at hIENN
  have hAreal : Tendsto (fun R => gaussMeasure.real (AR R)) atTop
      (𝓝 (gaussMeasure.real A)) := by
    have h := (ENNReal.continuousAt_toReal (by finiteness)).tendsto.comp hAENN
    simpa only [Function.comp_apply, measureReal_def] using! h
  have hIreal : Tendsto (fun R => gaussMeasure.real (AR R ∩ F)) atTop
      (𝓝 (gaussMeasure.real (A ∩ F))) := by
    have h := (ENNReal.continuousAt_toReal (by finiteness)).tendsto.comp hIENN
    simpa only [Function.comp_apply, measureReal_def] using! h
  have hleft : Tendsto
      (fun R => |gaussMeasure.real (AR R ∩ F) -
        gaussMeasure.real (AR R) * gaussMeasure.real B|) atTop
      (𝓝 |gaussMeasure.real (A ∩ F) -
        gaussMeasure.real A * gaussMeasure.real B|) :=
    (hIreal.sub (hAreal.mul tendsto_const_nhds)).abs
  have hright : Tendsto
      (fun R => eps * gaussMeasure.real (AR R) * gaussMeasure.real B) atTop
      (𝓝 (eps * gaussMeasure.real A * gaussMeasure.real B)) :=
    ((tendsto_const_nhds.mul hAreal).mul tendsto_const_nhds)
  have hfinite : ∀ R : ℕ,
      |gaussMeasure.real (AR R ∩ F) -
        gaussMeasure.real (AR R) * gaussMeasure.real B| ≤
      eps * gaussMeasure.real (AR R) * gaussMeasure.real B := by
    intro R
    exact gaussMeasureReal_finiteGaussDigitEvent_inter_gaussOrbit_preimage_error_le'
      (truncatedGaussDigitIndices digits R) hBM hgap
  exact le_of_tendsto_of_tendsto hleft hright (Filter.Eventually.of_forall hfinite)

/-- Event-form corollary for the exact predicate used by the factorial tuple
replacement module. -/
theorem gaussMeasureReal_isGaussOneDigitEvent_inter_gaussOrbit_preimage_error_le
    {A B : Set ℝ} (hA : IsGaussOneDigitEvent A) (hBM : MeasurableSet B)
    {gap : ℕ} (hgap : 0 < gap) :
    |gaussMeasure.real (A ∩ (gaussOrbit gap) ⁻¹' B) -
      gaussMeasure.real A * gaussMeasure.real B| ≤
      (6 * (527 / 540 : ℝ) ^ (gap - 1)) *
        gaussMeasure.real A * gaussMeasure.real B := by
  obtain ⟨digits, rfl⟩ := hA
  exact gaussMeasureReal_oneDigitSet_inter_gaussOrbit_preimage_error_le
    digits hBM hgap

/-! ## Stationary and sequential forms -/

def gaussDigitExponentialRate (gap : ℕ) : ℝ :=
  6 * (527 / 540 : ℝ) ^ (gap - 1)

theorem gaussDigitExponentialRate_nonnegative (gap : ℕ) :
    0 ≤ gaussDigitExponentialRate gap := by
  unfold gaussDigitExponentialRate
  positivity

theorem gaussDigitExponentialRate_le_of_le
    {gap d : ℕ} (hgap : 0 < gap) (hgd : gap ≤ d) :
    gaussDigitExponentialRate d ≤ gaussDigitExponentialRate gap := by
  unfold gaussDigitExponentialRate
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
    (by omega : gap - 1 ≤ d - 1)

theorem gaussMeasureReal_gaussOrbit_oneDigit_inter_later_exponential_error_le
    {A B : Set ℝ} (hA : IsGaussOneDigitEvent A)
    (hAM : MeasurableSet A) (hBM : MeasurableSet B)
    {m n : ℕ} (hmn : m < n) :
    |gaussMeasure.real
        ((gaussOrbit m) ⁻¹' A ∩ (gaussOrbit n) ⁻¹' B) -
      gaussMeasure.real ((gaussOrbit m) ⁻¹' A) *
        gaussMeasure.real ((gaussOrbit n) ⁻¹' B)| ≤
      gaussDigitExponentialRate (n - m) *
        gaussMeasure.real ((gaussOrbit m) ⁻¹' A) *
          gaussMeasure.real ((gaussOrbit n) ⁻¹' B) := by
  rw [gaussOrbit_preimage_inter_later_preimage m n hmn.le A B]
  have htailM : MeasurableSet ((gaussOrbit (n - m)) ⁻¹' B) :=
    hBM.preimage (measurable_gaussOrbit (n - m))
  have hinterM : MeasurableSet (A ∩ (gaussOrbit (n - m)) ⁻¹' B) :=
    hAM.inter htailM
  rw [gaussMeasure_real_gaussOrbit_preimage m hinterM,
    gaussMeasure_real_gaussOrbit_preimage m hAM,
    gaussMeasure_real_gaussOrbit_preimage n hBM]
  exact gaussMeasureReal_isGaussOneDigitEvent_inter_gaussOrbit_preimage_error_le
    hA hBM (Nat.sub_pos_of_lt hmn)

theorem gaussMeasureReal_gaussOrbit_oneDigit_inter_later_error_le_of_gap
    {A B : Set ℝ} (hA : IsGaussOneDigitEvent A)
    (hAM : MeasurableSet A) (hBM : MeasurableSet B)
    {m n gap : ℕ} (hgap : 0 < gap) (hmn : m + gap ≤ n) :
    |gaussMeasure.real
        ((gaussOrbit m) ⁻¹' A ∩ (gaussOrbit n) ⁻¹' B) -
      gaussMeasure.real ((gaussOrbit m) ⁻¹' A) *
        gaussMeasure.real ((gaussOrbit n) ⁻¹' B)| ≤
      gaussDigitExponentialRate gap *
        gaussMeasure.real ((gaussOrbit m) ⁻¹' A) *
          gaussMeasure.real ((gaussOrbit n) ⁻¹' B) := by
  have hlt : m < n := by omega
  have hbase :=
    gaussMeasureReal_gaussOrbit_oneDigit_inter_later_exponential_error_le
      hA hAM hBM hlt
  have hrate : gaussDigitExponentialRate (n - m) ≤
      gaussDigitExponentialRate gap :=
    gaussDigitExponentialRate_le_of_le hgap (by omega)
  have hprod : 0 ≤
      gaussMeasure.real ((gaussOrbit m) ⁻¹' A) *
        gaussMeasure.real ((gaussOrbit n) ⁻¹' B) :=
    mul_nonneg measureReal_nonneg measureReal_nonneg
  exact hbase.trans (by
    simpa only [mul_assoc] using! mul_le_mul_of_nonneg_right hrate hprod)

/-- Recursive relative-mixing record with the same exponential bound at
every cut of a tuple whose adjacent times are separated by `gap`. -/
theorem exists_sequentialGaussDigitExponential
    {r : ℕ} (times : Fin r → ℕ) (events : Fin r → Set ℝ) (gap : ℕ)
    (hEvents : ∀ i, MeasurableSet (events i))
    (hOneDigit : ∀ i, IsGaussOneDigitEvent (events i))
    (hgap0 : 0 < gap)
    (hgap : ∀ i j, i < j → times i + gap ≤ times j) :
    ∃ errors : List ℝ,
      SequentialEventRelativeMixing gaussMeasure errors
        (List.ofFn fun i => (gaussOrbit (times i)) ⁻¹' events i) ∧
      ∀ epsilon ∈ errors, epsilon = gaussDigitExponentialRate gap := by
  induction r with
  | zero =>
      refine ⟨[], ?_, by simp⟩
      simpa using! (SequentialEventRelativeMixing.nil (mu := gaussMeasure))
  | succ r ih =>
      cases r with
      | zero =>
          refine ⟨[], ?_, by simp⟩
          simpa only [List.ofFn_succ, List.ofFn_zero] using!
            (SequentialEventRelativeMixing.singleton (mu := gaussMeasure)
              ((gaussOrbit (times 0)) ⁻¹' events 0))
      | succ k =>
          let tailTimes : Fin (k + 1) → ℕ := fun i => times i.succ
          let tailEvents : Fin (k + 1) → Set ℝ := fun i => events i.succ
          have hTailEvents : ∀ i, MeasurableSet (tailEvents i) := by
            intro i
            exact hEvents i.succ
          have hTailOne : ∀ i, IsGaussOneDigitEvent (tailEvents i) := by
            intro i
            exact hOneDigit i.succ
          have hTailGap : ∀ i j, i < j →
              tailTimes i + gap ≤ tailTimes j := by
            intro i j hij
            exact hgap i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)
          obtain ⟨errors, htail, herrors⟩ :=
            ih tailTimes tailEvents hTailEvents hTailOne hTailGap
          let base : ℕ := tailTimes 0
          let H : Set ℝ := shiftedGaussTailEvent base tailTimes tailEvents
          have hTailTime : ∀ i j, i < j → tailTimes i < tailTimes j := by
            intro i j hij
            have h := hTailGap i j hij
            omega
          have hbase : ∀ i, base ≤ tailTimes i := by
            intro i
            by_cases hi : i = 0
            · subst i
              exact le_rfl
            · exact (hTailTime 0 i (Fin.pos_iff_ne_zero.mpr hi)).le
          have hHM : MeasurableSet H :=
            measurableSet_shiftedGaussTailEvent hTailEvents
          have hshift :
              (gaussOrbit base) ⁻¹' H =
                orderedEventIntersection (List.ofFn fun i =>
                  (gaussOrbit (tailTimes i)) ⁻¹' tailEvents i) :=
            shiftedGaussTailEvent_preimage hbase
          have ht0base : times 0 + gap ≤ base := by
            exact hgap 0 (Fin.succ 0) (Fin.succ_pos 0)
          have hhead :=
            gaussMeasureReal_gaussOrbit_oneDigit_inter_later_error_le_of_gap
              (hOneDigit 0) (hEvents 0) hHM hgap0 ht0base
          rw [hshift] at hhead
          have htail' :
              SequentialEventRelativeMixing gaussMeasure errors
                (List.ofFn fun i : Fin (k + 1) =>
                  (gaussOrbit (times i.succ)) ⁻¹' events i.succ) := by
            simpa [tailTimes, tailEvents] using! htail
          have hhead' :
              |gaussMeasure.real
                  ((gaussOrbit (times 0)) ⁻¹' events 0 ∩
                    orderedEventIntersection
                      (List.ofFn fun i : Fin (k + 1) =>
                        (gaussOrbit (times i.succ)) ⁻¹' events i.succ)) -
                gaussMeasure.real ((gaussOrbit (times 0)) ⁻¹' events 0) *
                  gaussMeasure.real
                    (orderedEventIntersection
                      (List.ofFn fun i : Fin (k + 1) =>
                        (gaussOrbit (times i.succ)) ⁻¹' events i.succ))| ≤
                gaussDigitExponentialRate gap *
                  gaussMeasure.real
                    ((gaussOrbit (times 0)) ⁻¹' events 0) *
                  gaussMeasure.real
                    (orderedEventIntersection
                      (List.ofFn fun i : Fin (k + 1) =>
                        (gaussOrbit (times i.succ)) ⁻¹' events i.succ)) := by
            simpa [base, tailTimes, tailEvents] using! hhead
          have htailCons := htail'
          rw [List.ofFn_succ] at htailCons
          have hheadCons := hhead'
          rw [List.ofFn_succ] at hheadCons
          refine ⟨gaussDigitExponentialRate gap :: errors, ?_, ?_⟩
          · have hcons :=
              SequentialEventRelativeMixing.cons hheadCons htailCons
            simpa only [List.ofFn_succ] using! hcons
          · intro epsilon hepsilon
            simp only [List.mem_cons] at hepsilon
            rcases hepsilon with rfl | hepsilon
            · rfl
            · exact herrors epsilon hepsilon

/-- Unconditional exponentially decaying `psi`-mixing input consumed by the
factorial tuple replacement argument. -/
theorem gaussDigitPsiMixing_exponential :
    GaussDigitPsiMixing gaussDigitExponentialRate := by
  intro r times events gap hEvents hOneDigit hgap0 hgap
  obtain ⟨errors, hmix, herrors⟩ :=
    exists_sequentialGaussDigitExponential times events gap
      hEvents hOneDigit hgap0 hgap
  refine ⟨errors, hmix, ?_⟩
  intro epsilon hepsilon
  rw [herrors epsilon hepsilon]
  exact ⟨gaussDigitExponentialRate_nonnegative gap, le_rfl⟩

theorem tendsto_gaussDigitExponentialRate :
    Tendsto gaussDigitExponentialRate atTop (𝓝 0) := by
  unfold gaussDigitExponentialRate
  have hsub : Tendsto (fun gap : ℕ => gap - 1) atTop atTop :=
    tendsto_sub_atTop_nat 1
  have hpow : Tendsto (fun gap : ℕ =>
      (527 / 540 : ℝ) ^ (gap - 1)) atTop (𝓝 0) :=
    tendsto_gaussTransferContractionCoefficient_pow.comp hsub
  simpa only [mul_zero] using! tendsto_const_nhds.mul hpow

/-- Paper-facing multi-time consequence.  For a nonempty chronologically
ordered family of one-digit events whose times are separated by `gap`, the
joint probability differs from the product of the marginal probabilities by
the explicit relative factor
`(1 + 6 * (527 / 540) ^ (gap - 1)) ^ (r - 1) - 1`. -/
theorem gaussMeasureReal_iInter_oneDigitEvents_factorization_error_le
    {r : ℕ} (hr : 0 < r) (times : Fin r → ℕ)
    (events : Fin r → Set ℝ) (gap : ℕ)
    (hEvents : ∀ i, MeasurableSet (events i))
    (hOneDigit : ∀ i, IsGaussOneDigitEvent (events i))
    (hgap0 : 0 < gap)
    (hgap : ∀ i j, i < j → times i + gap ≤ times j) :
    |gaussMeasure.real
          (⋂ i, (gaussOrbit (times i)) ⁻¹' events i) -
        ∏ i, gaussMeasure.real (events i)| ≤
      ((1 + gaussDigitExponentialRate gap) ^ (r - 1) - 1) *
        ∏ i, gaussMeasure.real (events i) := by
  obtain ⟨errors, hmix, herrors⟩ :=
    gaussDigitPsiMixing_exponential times events gap
      hEvents hOneDigit hgap0 hgap
  have hne :
      (List.ofFn fun i => (gaussOrbit (times i)) ⁻¹' events i) ≠ [] := by
    intro hempty
    have hlength := congrArg List.length hempty
    simp only [List.length_ofFn, List.length_nil] at hlength
    omega
  have hlength := hmix.length_errors_add_one hne
  have herrorLength : errors.length = r - 1 := by
    simp only [List.length_ofFn] at hlength
    omega
  have hbound := hmix.abs_measure_intersection_sub_product_le_pow
    gaussMeasure (gaussDigitExponentialRate_nonnegative gap) herrors
  rw [herrorLength] at hbound
  have hproduct :
      eventProbabilityProduct gaussMeasure
          (List.ofFn fun i => (gaussOrbit (times i)) ⁻¹' events i) =
        ∏ i, gaussMeasure.real (events i) := by
    simp only [eventProbabilityProduct, List.map_ofFn, Function.comp_apply,
      List.prod_ofFn]
    apply Finset.prod_congr rfl
    intro i _hi
    exact gaussMeasure_real_gaussOrbit_preimage (times i) (hEvents i)
  rw [orderedEventIntersection_ofFn, hproduct] at hbound
  exact hbound

end

end Erdos1002
