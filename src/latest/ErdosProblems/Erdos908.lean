/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 908.
https://www.erdosproblems.com/forum/thread/908

Informal authors:
- Miklós Laczkovich

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos908.md
-/
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.Action.OfMinimal
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Algebra.InfiniteSum.Real
import ErdosProblems.Erdos907
import Mathlib.Tactic

/-!
# Erdős Problem 908

The version supplied in the problem statement asks for a decomposition
`f = g + H + r` in which `g` is continuous.  That version is false.  The
historical theorem of Laczkovich has a *measurable* first summand instead.

Here we formalize the supplied statement exactly and disprove it using the
Heaviside function.  Its unit difference is one on `[-1, 0)` and zero
elsewhere, so it cannot agree almost everywhere with a continuous function.

The detailed mathematical proof and the source correction are in `tex/908.tex`.
-/

namespace Erdos908

open Filter MeasureTheory Set Function
open scoped Pointwise ENNReal

/-- `H` is additive when it satisfies Cauchy's functional equation. -/
def IsAdditiveFn (H : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, H (x + y) = H x + H y

/-- Every positive translate difference of `f` is measurable. -/
def HasMeasurablePositiveDifferences (f : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → AEMeasurable (fun x => f (x + t) - f x) volume

/-- Every translate difference of a function is measurable.  This is the form
used in Laczkovich's theorem; the next lemma shows that the positive-increment
hypothesis from the problem statement is equivalent to it. -/
def HasMeasurableDifferences (f : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, AEMeasurable (fun x => f (x + t) - f x) volume

/-- Positive measurable differences already give measurable differences for
every real increment. -/
lemma hasMeasurableDifferences_of_positive {f : ℝ → ℝ}
    (hf : HasMeasurablePositiveDifferences f) :
    HasMeasurableDifferences f := by
  intro t
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hneg : 0 < -t := by linarith
    have hcomp :
        AEMeasurable
          ((fun x : ℝ => f (x + (-t)) - f x) ∘ fun x : ℝ => x + t)
          volume :=
      (hf (-t) hneg).comp_quasiMeasurePreserving
        ((measurePreserving_add_right volume t).quasiMeasurePreserving)
    convert hcomp.neg using 1
    funext x
    simp only [Function.comp_apply, Pi.neg_apply]
    ring_nf
  · convert (aemeasurable_const :
        AEMeasurable (fun _ : ℝ => (0 : ℝ)) volume) using 1
    funext x
    simp
  · exact hf t ht

/-- Subtracting an additive function preserves measurability of all
difference sections: the new section differs from the old one by a
constant. -/
lemma HasMeasurableDifferences.sub_additive {f H : ℝ → ℝ}
    (hf : HasMeasurableDifferences f) (hH : IsAdditiveFn H) :
    HasMeasurableDifferences (fun x => f x - H x) := by
  intro t
  have hft := hf t
  have hconst :
      AEMeasurable (fun _ : ℝ => H t) volume :=
    aemeasurable_const
  have hdiff := hft.sub hconst
  convert hdiff using 1
  funext x
  dsimp
  rw [hH x t]
  ring_nf

/-- Adding an almost-everywhere measurable function preserves measurable
difference sections.  This is the bookkeeping step used when a periodicized
core is later transferred back to the original function. -/
lemma HasMeasurableDifferences.add_aemeasurable {f g : ℝ → ℝ}
    (hf : HasMeasurableDifferences f) (hg : AEMeasurable g volume) :
    HasMeasurableDifferences (fun x => f x + g x) := by
  intro t
  have hshift :
      AEMeasurable (fun x : ℝ => g (x + t)) volume :=
    hg.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume t).quasiMeasurePreserving
  convert (hf t).add (hshift.sub hg) using 1
  funext x
  simp only [Pi.add_apply, Pi.sub_apply, add_comm]
  ring

/-- Subtracting an almost-everywhere measurable function likewise preserves
measurable difference sections. -/
lemma HasMeasurableDifferences.sub_aemeasurable {f g : ℝ → ℝ}
    (hf : HasMeasurableDifferences f) (hg : AEMeasurable g volume) :
    HasMeasurableDifferences (fun x => f x - g x) := by
  intro t
  have hshift :
      AEMeasurable (fun x : ℝ => g (x + t)) volume :=
    hg.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume t).quasiMeasurePreserving
  convert (hf t).sub (hshift.sub hg) using 1
  funext x
  simp only [Pi.sub_apply, add_comm]
  ring

/-- The one-periodic representative obtained by restricting a function to
the half-open unit interval and extending by fractional part. -/
noncomputable def periodizeOne (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f (Int.fract x)

/-- Periodization by fractional part is genuinely one-periodic. -/
lemma periodizeOne_periodic (f : ℝ → ℝ) :
    Function.Periodic (periodizeOne f) 1 := by
  intro x
  simp [periodizeOne, Int.fract_add_one]

/-- If all differences of f are measurable, the correction made by
one-periodization is measurable.  On each integer unit interval it is one
fixed translate difference. -/
lemma periodizeOne_sub_aemeasurable {f : ℝ → ℝ}
    (hf : HasMeasurableDifferences f) :
    AEMeasurable (fun x => periodizeOne f x - f x) volume := by
  have hcover : (⋃ n : ℤ, Ico (n : ℝ) (n + 1 : ℝ)) = (univ : Set ℝ) := by
    ext x
    simp only [mem_iUnion, mem_Ico, mem_univ, iff_true]
    exact ⟨⌊x⌋, Int.floor_le x, Int.lt_floor_add_one x⟩
  rw [← Measure.restrict_univ (μ := volume), ← hcover, aemeasurable_iUnion_iff]
  intro n
  have hn := hf (-(n : ℝ))
  apply (hn.restrict).congr
  filter_upwards [ae_restrict_mem measurableSet_Ico] with x hxn
  have hfloor : ⌊x⌋ = n := by
    rw [Int.floor_eq_iff]
    exact hxn
  have hfract : Int.fract x = x + (-(n : ℝ)) := by
    rw [Int.fract]
    rw [hfloor]
    ring
  rw [periodizeOne, hfract]

/-- One-periodization preserves measurable differences. -/
lemma periodizeOne_hasMeasurableDifferences {f : ℝ → ℝ}
    (hf : HasMeasurableDifferences f) :
    HasMeasurableDifferences (periodizeOne f) := by
  have hc := periodizeOne_sub_aemeasurable hf
  have hsum := hf.add_aemeasurable hc
  convert hsum using 1
  funext x
  ring

/-- Every translate difference of `r` vanishes almost everywhere.  The
exceptional null set is allowed to depend on `t`. -/
def HasNullIncrements (r : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, ∀ᵐ x ∂volume, r (x + t) - r x = 0

/-- The decomposition requested in the supplied version of Problem 908. -/
def HasDecomposition (f : ℝ → ℝ) : Prop :=
  ∃ g H r : ℝ → ℝ,
    Continuous g ∧
      IsAdditiveFn H ∧
        (∀ x : ℝ, f x = g x + H x + r x) ∧
          HasNullIncrements r

/-- The source-supported conclusion: the regular summand is Lebesgue
measurable, not continuous.  Almost-everywhere measurability for volume is
measurability for the completed Lebesgue measure. -/
def HasMeasurableDecomposition (f : ℝ → ℝ) : Prop :=
  ∃ g H r : ℝ → ℝ,
    AEMeasurable g volume ∧
      IsAdditiveFn H ∧
        (∀ x : ℝ, f x = g x + H x + r x) ∧
          HasNullIncrements r

/-- The universal affirmative assertion made by the supplied wording. -/
def Erdos908Claim : Prop :=
  ∀ f : ℝ → ℝ, HasMeasurablePositiveDifferences f → HasDecomposition f

/-- The corrected universal assertion proved by Laczkovich. -/
def Erdos908MeasurableClaim : Prop :=
  ∀ f : ℝ → ℝ,
    HasMeasurablePositiveDifferences f → HasMeasurableDecomposition f

lemma zero_isAdditiveFn : IsAdditiveFn (fun _ : ℝ => 0) := by
  intro x y
  simp

lemma zero_hasNullIncrements : HasNullIncrements (fun _ : ℝ => 0) := by
  intro t
  filter_upwards [] with x
  simp

/-- A real-valued function is bounded on a positive-measure piece of every
positive-measure set.  This elementary countable-cover lemma is the first
localization input: measurability is needed later only to replace the piece
by a density neighborhood. -/
lemma exists_positiveMeasure_bounded_piece (u : ℝ → ℝ) {s : Set ℝ}
    (hs : 0 < volume s) :
    ∃ n : ℕ, 0 < volume (s ∩ {x : ℝ | |u x| ≤ n}) := by
  let A : ℕ → Set ℝ := fun n => s ∩ {x : ℝ | |u x| ≤ n}
  have hcover : (⋃ n, A n) = s := by
    ext x
    constructor
    · intro hx
      rcases mem_iUnion.mp hx with ⟨n, hx⟩
      exact hx.1
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge |u x|
      exact mem_iUnion.mpr ⟨n, hx, hn⟩
  have hnot : volume (⋃ n, A n) ≠ 0 := by
    rw [hcover]
    exact ne_of_gt hs
  rcases exists_measure_pos_of_not_measure_iUnion_null hnot with ⟨n, hn⟩
  exact ⟨n, hn⟩

/-- A density-one point of a set, expressed using the closed-ball form of
Lebesgue differentiation.  Keeping this as a predicate rather than installing
the density topology makes the later localization lemmas use Mathlib's
existing differentiation API directly. -/
def IsDensityOneAt (s : Set ℝ) (x : ℝ) : Prop :=
  Tendsto (fun r => volume (s ∩ Metric.closedBall x r) /
    volume (Metric.closedBall x r)) (nhdsWithin 0 (Ioi 0)) (nhds 1)

/-- A density-zero point, recorded separately because complements turn
finite intersections of density-one witnesses into finite unions whose
measure ratios are controlled by subadditivity. -/
def IsDensityZeroAt (s : Set ℝ) (x : ℝ) : Prop :=
  Tendsto (fun r => volume (s ∩ Metric.closedBall x r) /
    volume (Metric.closedBall x r)) (nhdsWithin 0 (Ioi 0)) (nhds 0)

/-- A function is essentially bounded on a density neighborhood of a point.
The neighborhood itself is kept explicit because later cocycle steps only
intersect finitely many such witnesses. -/
def HasDensityEssentialBoundAt (u : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ n : ℕ, ∃ s : Set ℝ,
    MeasurableSet s ∧
      IsDensityOneAt s x ∧
        ∀ᵐ y ∂volume.restrict s, |u y| ≤ n

/-- The whole line has density one at every point. -/
lemma densityOne_univ (x : ℝ) : IsDensityOneAt univ x := by
  unfold IsDensityOneAt
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrpos : 0 < r := hr
  simp only [univ_inter, Real.volume_closedBall]
  rw [ENNReal.div_self (by positivity) (by finiteness)]

/-- Density-zero sets are closed under finite unions. -/
lemma densityZero_union {s t : Set ℝ} {x : ℝ}
    (hs : IsDensityZeroAt s x) (ht : IsDensityZeroAt t x) :
    IsDensityZeroAt (s ∪ t) x := by
  unfold IsDensityZeroAt at *
  have hsum :
      Tendsto (fun r =>
        volume (s ∩ Metric.closedBall x r) / volume (Metric.closedBall x r) +
          volume (t ∩ Metric.closedBall x r) / volume (Metric.closedBall x r))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using hs.add ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum
  · exact Eventually.of_forall fun _ => bot_le
  · filter_upwards [] with r
    rw [union_inter_distrib_right]
    have hle :
        volume ((s ∩ Metric.closedBall x r) ∪
            (t ∩ Metric.closedBall x r)) ≤
          volume (s ∩ Metric.closedBall x r) +
            volume (t ∩ Metric.closedBall x r) :=
      measure_union_le _ _
    simpa [ENNReal.add_div] using
      (ENNReal.div_le_div_right hle (volume (Metric.closedBall x r)))

/-- At a measurable density-one point, the complement has density zero. -/
lemma densityZero_compl_of_densityOne {s : Set ℝ} {x : ℝ}
    (hsm : MeasurableSet s) (hs : IsDensityOneAt s x) :
    IsDensityZeroAt sᶜ x := by
  unfold IsDensityOneAt at hs
  unfold IsDensityZeroAt
  have hsub :
      Tendsto
        (fun r =>
          1 - volume (s ∩ Metric.closedBall x r) /
            volume (Metric.closedBall x r))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa [Function.comp_def] using
      ((ENNReal.continuous_sub_left (a := 1) (by simp)).tendsto 1).comp hs
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrpos : 0 < r := hr
  have hball : MeasurableSet (Metric.closedBall x r) :=
    Metric.isClosed_closedBall.measurableSet
  have hdiff :
      sᶜ ∩ Metric.closedBall x r =
        Metric.closedBall x r \ (s ∩ Metric.closedBall x r) := by
    ext y
    simp only [mem_inter_iff, mem_compl_iff, mem_diff]
    tauto
  have hsubball : s ∩ Metric.closedBall x r ⊆ Metric.closedBall x r :=
    inter_subset_right
  have hfinball : volume (Metric.closedBall x r) ≠ ⊤ := by
    rw [Real.volume_closedBall]
    finiteness
  have hfinsub : volume (s ∩ Metric.closedBall x r) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinball (measure_mono hsubball)
  rw [hdiff, measure_diff hsubball
    (hsm.inter hball).nullMeasurableSet hfinsub]
  rw [ENNReal.sub_div]
  · rw [ENNReal.div_self (by
      rw [Real.volume_closedBall]
      positivity) hfinball]
  · intro _hpos _hlt
    rw [Real.volume_closedBall]
    positivity

/-- Conversely, a measurable set whose complement has density zero has
density one. -/
lemma densityOne_of_densityZero_compl {s : Set ℝ} {x : ℝ}
    (hsm : MeasurableSet s) (hs : IsDensityZeroAt sᶜ x) :
    IsDensityOneAt s x := by
  unfold IsDensityZeroAt at hs
  unfold IsDensityOneAt
  have hsub :
      Tendsto
        (fun r =>
          1 - volume (sᶜ ∩ Metric.closedBall x r) /
            volume (Metric.closedBall x r))
        (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    simpa [Function.comp_def] using
      ((ENNReal.continuous_sub_left (a := 1) (by simp)).tendsto 0).comp hs
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrpos : 0 < r := hr
  have hball : MeasurableSet (Metric.closedBall x r) :=
    Metric.isClosed_closedBall.measurableSet
  have hdiff :
      s ∩ Metric.closedBall x r =
        Metric.closedBall x r \ (sᶜ ∩ Metric.closedBall x r) := by
    ext y
    simp only [mem_inter_iff, mem_compl_iff, mem_diff]
    tauto
  have hsubball : sᶜ ∩ Metric.closedBall x r ⊆ Metric.closedBall x r :=
    inter_subset_right
  have hfinball : volume (Metric.closedBall x r) ≠ ⊤ := by
    rw [Real.volume_closedBall]
    finiteness
  have hfinsub : volume (sᶜ ∩ Metric.closedBall x r) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinball (measure_mono hsubball)
  rw [hdiff, measure_diff hsubball
    (hsm.compl.inter hball).nullMeasurableSet hfinsub]
  rw [ENNReal.sub_div]
  · rw [ENNReal.div_self (by
      rw [Real.volume_closedBall]
      positivity) hfinball]
  · intro _hpos _hlt
    rw [Real.volume_closedBall]
    positivity

/-- Finite intersections of measurable density-one neighborhoods remain
density-one neighborhoods. -/
lemma densityOne_inter {s t : Set ℝ} {x : ℝ}
    (hsm : MeasurableSet s) (htm : MeasurableSet t)
    (hs : IsDensityOneAt s x) (ht : IsDensityOneAt t x) :
    IsDensityOneAt (s ∩ t) x := by
  apply densityOne_of_densityZero_compl (hsm.inter htm)
  rw [compl_inter]
  exact densityZero_union
    (densityZero_compl_of_densityOne hsm hs)
    (densityZero_compl_of_densityOne htm ht)

/-- Translation of a set, written with a preimage so measurability is
immediate. -/
def translateSet (s : Set ℝ) (a : ℝ) : Set ℝ :=
  {y | y - a ∈ s}

lemma translateSet_measurable {s : Set ℝ} {a : ℝ}
    (hs : MeasurableSet s) : MeasurableSet (translateSet s a) := by
  exact hs.preimage (measurable_id.sub_const a)

lemma translateSet_inter_ball (s : Set ℝ) (x a r : ℝ) :
    translateSet s a ∩ Metric.closedBall (x + a) r =
      (fun y : ℝ => y + a) '' (s ∩ Metric.closedBall x r) := by
  ext y
  constructor
  · intro hy
    refine ⟨y - a, ?_, by ring⟩
    constructor
    · exact hy.1
    · simpa [Real.dist_eq] using hy.2
  · rintro ⟨z, hz, rfl⟩
    constructor
    · simp [translateSet, hz.1]
    · simpa [Real.dist_eq] using hz.2

/-- Density-one neighborhoods are stable under translation. -/
lemma densityOne_translate {s : Set ℝ} {x a : ℝ}
    (hsm : MeasurableSet s) (hs : IsDensityOneAt s x) :
    IsDensityOneAt (translateSet s a) (x + a) := by
  unfold IsDensityOneAt at *
  refine hs.congr' ?_
  filter_upwards [] with r
  rw [translateSet_inter_ball]
  have himg :
      volume ((fun y : ℝ => y + a) '' (s ∩ Metric.closedBall x r)) =
        volume (s ∩ Metric.closedBall x r) := by
    rw [← measure_preimage_add_right volume (-a)
      (s ∩ Metric.closedBall x r)]
    congr 1
    ext y
    simp
  rw [himg, Real.volume_closedBall, Real.volume_closedBall]

/-- A measurable real function has a bounded positive-measure level piece
with a density-one point inside every positive-measure measurable set.  This
is the pointwise density-neighborhood form used by the measure localization
argument. -/
lemma exists_densityPoint_bounded_piece_of_measurable (u : ℝ → ℝ)
    (hu : Measurable u) {s : Set ℝ}
    (hsm : MeasurableSet s) (hs : 0 < volume s) :
    ∃ n : ℕ, ∃ x : ℝ,
      x ∈ s ∩ {y : ℝ | |u y| ≤ n} ∧
        IsDensityOneAt (s ∩ {y : ℝ | |u y| ≤ n}) x := by
  rcases exists_positiveMeasure_bounded_piece u hs with ⟨n, hn⟩
  let A : Set ℝ := s ∩ {y : ℝ | |u y| ≤ n}
  have hAm : MeasurableSet A := by
    exact hsm.inter (measurableSet_le hu.norm measurable_const)
  have hden :
      ∀ᵐ x ∂volume.restrict A, IsDensityOneAt A x := by
    simpa [IsDensityOneAt] using
      (Besicovitch.ae_tendsto_measure_inter_div volume A)
  rcases Measure.exists_mem_of_measure_ne_zero_of_ae hn.ne' hden with
    ⟨x, hxmem, hxden⟩
  exact ⟨n, x, hxmem, hxden⟩

/-- The preceding density-point lemma in the completed-Lebesgue form used by
the problem hypothesis.  It exposes one measurable representative and keeps
the almost-everywhere identification available for later finite
intersections. -/
lemma exists_densityPoint_bounded_piece_of_aemeasurable (u : ℝ → ℝ)
    (hu : AEMeasurable u volume) {s : Set ℝ}
    (hsm : MeasurableSet s) (hs : 0 < volume s) :
    ∃ v : ℝ → ℝ, ∃ n : ℕ, ∃ x : ℝ,
      Measurable v ∧
        u =ᵐ[volume] v ∧
          x ∈ s ∩ {y : ℝ | |v y| ≤ n} ∧
            IsDensityOneAt (s ∩ {y : ℝ | |v y| ≤ n}) x := by
  let v : ℝ → ℝ := hu.mk u
  have hv : Measurable v := hu.measurable_mk
  rcases exists_densityPoint_bounded_piece_of_measurable v hv hsm hs with
    ⟨n, x, hxmem, hxden⟩
  exact ⟨v, n, x, hv, hu.ae_eq_mk, hxmem, hxden⟩

/-- Every completed-Lebesgue measurable real function is density-locally
essentially bounded at almost every point. -/
lemma ae_hasDensityEssentialBoundAt {u : ℝ → ℝ}
    (hu : AEMeasurable u volume) :
    ∀ᵐ x ∂volume, HasDensityEssentialBoundAt u x := by
  let v : ℝ → ℝ := hu.mk u
  have hv : Measurable v := hu.measurable_mk
  let A : ℕ → Set ℝ := fun n => {y : ℝ | |v y| ≤ n}
  have hAm (n : ℕ) : MeasurableSet (A n) := by
    exact measurableSet_le hv.norm measurable_const
  have hcover : (⋃ n, A n) = (univ : Set ℝ) := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    exact exists_nat_ge |v x|
  have hpiece (n : ℕ) :
      ∀ᵐ x ∂volume.restrict (A n), HasDensityEssentialBoundAt u x := by
    have hden :
        ∀ᵐ x ∂volume.restrict (A n), IsDensityOneAt (A n) x := by
      simpa [IsDensityOneAt] using
        (Besicovitch.ae_tendsto_measure_inter_div volume (A n))
    filter_upwards [hden] with x hxden
    refine ⟨n, A n, hAm n, hxden, ?_⟩
    filter_upwards [ae_restrict_of_ae hu.ae_eq_mk,
      ae_restrict_mem (hAm n)] with y hy hymem
    rw [hy]
    exact hymem
  have hall :
      ∀ᵐ x ∂volume.restrict (⋃ n, A n), HasDensityEssentialBoundAt u x :=
    (ae_restrict_iUnion_iff A _).2 hpiece
  simpa [hcover] using hall

/-- A density-one piece meets every sufficiently small rescaled copy of a
positive-measure measurable set.  This is the concrete replacement for the
density-neighborhood intersection slogan in the localization proof. -/
lemma eventually_nonempty_inter_smul_of_densityOne
    (s t : Set ℝ) (x : ℝ)
    (hs : IsDensityOneAt s x)
    (ht : MeasurableSet t) (htpos : 0 < volume t) :
    ∀ᶠ r : ℝ in nhdsWithin 0 (Ioi 0),
      (s ∩ ({x} + r • t)).Nonempty := by
  simpa [IsDensityOneAt] using
    (Measure.eventually_nonempty_inter_smul_of_density_one
      volume s x hs t ht htpos.ne')

/-- A countable cover of the real parameter line has one member dense on a
nonempty interval.  This is the Baire extraction used after discretizing
measurable difference sections into countably many local pieces. -/
lemma exists_interval_subset_closure_of_iUnion_eq_univ
    (A : ℕ → Set ℝ) (hcover : (⋃ n, A n) = (univ : Set ℝ)) :
    ∃ n : ℕ, ∃ a b : ℝ, a < b ∧ Ioo a b ⊆ closure (A n) := by
  have hclosed : ∀ n : ℕ, IsClosed (closure (A n)) :=
    fun n => isClosed_closure
  have hcover' : (⋃ n, closure (A n)) = (univ : Set ℝ) := by
    have hsub : (⋃ n, A n) ⊆ ⋃ n, closure (A n) :=
      iUnion_mono fun n => subset_closure
    simpa [hcover] using hsub
  rcases nonempty_interior_of_iUnion_of_closed hclosed hcover' with ⟨n, x, hx⟩
  rw [mem_interior_iff_mem_nhds] at hx
  rcases mem_nhds_iff_exists_Ioo_subset.mp hx with ⟨a, b, hxab, hab⟩
  exact ⟨n, a, b, lt_trans hxab.1 hxab.2, hab⟩

/-- Parameters whose difference section has a bounded positive-measure
piece inside a fixed spatial set.  The definition is deliberately
nonmeasurable in the parameter: the Baire step only uses its closure. -/
def boundedDifferenceParameterSet (f : ℝ → ℝ) (s : Set ℝ) (n : ℕ) : Set ℝ :=
  {t : ℝ | 0 < volume (s ∩ {x : ℝ | |f (x + t) - f x| ≤ n})}

/-- For every increment, its real-valued section is bounded on some
positive-measure part of any fixed positive-measure set.  Hence the
countably many bounded-parameter sets cover the whole parameter line. -/
lemma iUnion_boundedDifferenceParameterSet_eq_univ
    (f : ℝ → ℝ) {s : Set ℝ} (hs : 0 < volume s) :
    (⋃ n : ℕ, boundedDifferenceParameterSet f s n) = (univ : Set ℝ) := by
  ext t
  simp only [mem_iUnion, mem_univ, iff_true]
  rcases exists_positiveMeasure_bounded_piece (fun x => f (x + t) - f x) hs with
    ⟨n, hn⟩
  exact ⟨n, hn⟩

/-- A fixed bound works on a parameter set dense in one nonempty interval.
This is the first nontrivial Baire uniformization in the localization
argument. -/
lemma exists_dense_boundedDifferenceParameterSet
    (f : ℝ → ℝ) {s : Set ℝ} (hs : 0 < volume s) :
    ∃ n : ℕ, ∃ a b : ℝ, a < b ∧
      Ioo a b ⊆ closure (boundedDifferenceParameterSet f s n) :=
  exists_interval_subset_closure_of_iUnion_eq_univ _
    (iUnion_boundedDifferenceParameterSet_eq_univ f hs)

/-- A measurable function has the corrected decomposition with zero additive
and null-increment parts.  The hard theorem is needed only because the
original function itself need not be measurable. -/
lemma hasMeasurableDecomposition_of_aemeasurable {f : ℝ → ℝ}
    (hf : AEMeasurable f volume) :
    HasMeasurableDecomposition f := by
  refine ⟨f, fun _ => 0, fun _ => 0, hf, zero_isAdditiveFn, ?_, zero_hasNullIncrements⟩
  intro x
  simp

/-- Adding an almost-everywhere measurable summand to a function with a
measurable decomposition preserves the decomposition. -/
lemma HasMeasurableDecomposition.add_aemeasurable {f g : ℝ → ℝ}
    (hf : HasMeasurableDecomposition f) (hg : AEMeasurable g volume) :
    HasMeasurableDecomposition (fun x => f x + g x) := by
  rcases hf with ⟨u, H, r, hu, hH, hdecomp, hr⟩
  refine ⟨fun x => u x + g x, H, r, hu.add hg, hH, ?_, hr⟩
  intro x
  dsimp
  rw [hdecomp x]
  ring

/-- It is enough to solve the corrected theorem for the one-periodic
reduction: the measurable periodization correction is absorbed into the
regular summand. -/
lemma measurableDecomposition_of_periodizeOne
    {f : ℝ → ℝ} (hf : HasMeasurableDifferences f)
    (hp : HasMeasurableDecomposition (periodizeOne f)) :
    HasMeasurableDecomposition f := by
  have hc : AEMeasurable (fun x => f x - periodizeOne f x) volume := by
    convert (periodizeOne_sub_aemeasurable hf).neg using 1
    funext x
    simp only [Pi.neg_apply]
    ring
  have h := hp.add_aemeasurable hc
  convert h using 1
  funext x
  ring

/-- Once the periodic core is established, the exact positive-increment
statement follows by the preceding reduction. -/
lemma measurableClaim_of_periodic_core
    (hcore : ∀ p : ℝ → ℝ,
      Function.Periodic p 1 →
        HasMeasurableDifferences p →
          HasMeasurableDecomposition p) :
    Erdos908MeasurableClaim := by
  intro f hfpos
  have hf := hasMeasurableDifferences_of_positive hfpos
  apply measurableDecomposition_of_periodizeOne hf
  exact hcore (periodizeOne f) (periodizeOne_periodic f)
    (periodizeOne_hasMeasurableDifferences hf)

/-- Pull a function back along the affine coordinate change used to move a
localization window onto the unit interval. -/
noncomputable def affinePull (f : ℝ → ℝ) (a ρ x : ℝ) : ℝ :=
  f (a + ρ * x)

/-- Nondegenerate affine pullback preserves measurable difference sections.
The section with increment `t` is the old section with increment `ρ * t`
composed with a nonsingular affine map. -/
lemma affinePull_hasMeasurableDifferences {f : ℝ → ℝ} {a ρ : ℝ}
    (hf : HasMeasurableDifferences f) (hρ : ρ ≠ 0) :
    HasMeasurableDifferences (affinePull f a ρ) := by
  intro t
  have hqmul : Measure.QuasiMeasurePreserving (fun x : ℝ => ρ * x) volume volume := by
    simpa [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ)) hρ)
  have hqadd : Measure.QuasiMeasurePreserving (fun x : ℝ => a + x) volume volume :=
    (measurePreserving_add_left volume a).quasiMeasurePreserving
  have hq : Measure.QuasiMeasurePreserving (fun x : ℝ => a + ρ * x) volume volume := by
    simpa [Function.comp_def] using hqadd.comp hqmul
  have hm := (hf (ρ * t)).comp_quasiMeasurePreserving hq
  convert hm using 1
  funext x
  unfold affinePull
  simp only [Function.comp_apply]
  congr 2 <;> ring

/-- A nondegenerate affine map is nonsingular for Lebesgue measure. -/
lemma qmp_affine (a ρ : ℝ) (hρ : ρ ≠ 0) :
    Measure.QuasiMeasurePreserving (fun x : ℝ => a + ρ * x) volume volume := by
  have hqmul : Measure.QuasiMeasurePreserving (fun x : ℝ => ρ * x) volume volume := by
    simpa [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ)) hρ)
  have hqadd : Measure.QuasiMeasurePreserving (fun x : ℝ => a + x) volume volume :=
    (measurePreserving_add_left volume a).quasiMeasurePreserving
  simpa [Function.comp_def] using hqadd.comp hqmul

/-- A measurable decomposition of an affine pullback transports back to the
original function.  The translated constant in the additive component is
absorbed into the measurable summand. -/
lemma measurableDecomposition_of_affinePull {f : ℝ → ℝ} {a ρ : ℝ}
    (hρ : ρ ≠ 0)
    (hf : HasMeasurableDecomposition (affinePull f a ρ)) :
    HasMeasurableDecomposition f := by
  rcases hf with ⟨g, H, r, hg, hH, hdecomp, hr⟩
  let φ : ℝ → ℝ := fun y => (y - a) / ρ
  let g0 : ℝ → ℝ := fun y => g (φ y) - H (a / ρ)
  let H0 : ℝ → ℝ := fun y => H (y / ρ)
  let r0 : ℝ → ℝ := fun y => r (φ y)
  have hqφ : Measure.QuasiMeasurePreserving φ volume volume := by
    have hρi : ρ⁻¹ ≠ 0 := inv_ne_zero hρ
    convert qmp_affine (-a / ρ) ρ⁻¹ hρi using 1
    funext y
    dsimp [φ]
    field_simp
    ring
  have hg0 : AEMeasurable g0 volume := by
    exact (hg.comp_quasiMeasurePreserving hqφ).sub aemeasurable_const
  have hH0 : IsAdditiveFn H0 := by
    intro x y
    dsimp [H0]
    rw [show (x + y) / ρ = x / ρ + y / ρ by ring, hH]
  have hr0 : HasNullIncrements r0 := by
    intro t
    have hrt := hr (t / ρ)
    have hpull := hqφ.ae hrt
    filter_upwards [hpull] with y hy
    dsimp [r0, φ] at hy ⊢
    have harg : (y + t - a) / ρ = (y - a) / ρ + t / ρ := by ring
    rw [harg]
    exact hy
  refine ⟨g0, H0, r0, hg0, hH0, ?_, hr0⟩
  intro y
  have hy := hdecomp ((y - a) / ρ)
  dsimp [affinePull] at hy
  have harg : a + ρ * ((y - a) / ρ) = y := by
    field_simp
    ring
  rw [harg] at hy
  dsimp [g0, H0, r0, φ]
  have hsplit : H ((y - a) / ρ) = H (y / ρ) - H (a / ρ) := by
    have hh := hH (y / ρ) (-a / ρ)
    rw [show y / ρ + -a / ρ = (y - a) / ρ by ring] at hh
    have hneg := hH (a / ρ) (-a / ρ)
    have hzero := hH 0 0
    simp at hzero
    have hneg' : H (-a / ρ) = -H (a / ρ) := by
      rw [show a / ρ + -a / ρ = 0 by ring] at hneg
      linarith
    rw [hh, hneg']
    simp [sub_eq_add_neg]
  calc
    f y = g ((y - a) / ρ) + H ((y - a) / ρ) + r ((y - a) / ρ) := hy
    _ = g ((y - a) / ρ) - H (a / ρ) + H (y / ρ) + r ((y - a) / ρ) := by
      rw [hsplit]
      ring

/-- Therefore localization only has to solve one periodized affine window;
the preceding affine transport and the existing periodization correction do
all of the global bookkeeping. -/
lemma measurableDecomposition_of_affine_periodizeOne {f : ℝ → ℝ} {a ρ : ℝ}
    (hf : HasMeasurableDifferences f) (hρ : ρ ≠ 0)
    (hp : HasMeasurableDecomposition (periodizeOne (affinePull f a ρ))) :
    HasMeasurableDecomposition f := by
  have hfa : HasMeasurableDifferences (affinePull f a ρ) :=
    affinePull_hasMeasurableDifferences hf hρ
  exact measurableDecomposition_of_affinePull hρ
    (measurableDecomposition_of_periodizeOne hfa hp)

/-- Pull a full-measure assertion back through a translation. -/
lemma ae_translate {p : ℝ → Prop} (hp : ∀ᵐ x ∂volume, p x) (t : ℝ) :
    ∀ᵐ x ∂volume, p (x + t) := by
  have hmap : ∀ᵐ x ∂Measure.map (fun x : ℝ => x + t) volume, p x := by
    simpa [(measurePreserving_add_right volume t).map_eq] using hp
  exact ae_of_ae_map (aemeasurable_id'.add_const t) hmap

/-- Null increments are closed under adding two fixed increments. -/
lemma nullIncrement_add {r : ℝ → ℝ} {u v : ℝ}
    (hu : ∀ᵐ x ∂volume, r (x + u) - r x = 0)
    (hv : ∀ᵐ x ∂volume, r (x + v) - r x = 0) :
    ∀ᵐ x ∂volume, r (x + (u + v)) - r x = 0 := by
  filter_upwards [ae_translate hu v, hv] with x hxu hxv
  have harg : x + v + u = x + (u + v) := by ring
  rw [← harg]
  linarith

/-- Null-increment functions are closed under pointwise addition. -/
lemma HasNullIncrements.add {r s : ℝ → ℝ}
    (hr : HasNullIncrements r) (hs : HasNullIncrements s) :
    HasNullIncrements (fun x => r x + s x) := by
  intro t
  filter_upwards [hr t, hs t] with x hxr hxs
  linarith

/-- Null-increment functions are closed under pointwise negation. -/
lemma HasNullIncrements.neg {r : ℝ → ℝ}
    (hr : HasNullIncrements r) :
    HasNullIncrements (fun x => -r x) := by
  intro t
  filter_upwards [hr t] with x hx
  linarith

/-- A full-measure set of real numbers additively generates every real in
two steps. -/
lemma fullMeasure_add_self {Z : Set ℝ} (hZ : ∀ᵐ z ∂volume, z ∈ Z) (h : ℝ) :
    ∃ u ∈ Z, ∃ v ∈ Z, h = u + v := by
  let mn : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    ⟨measurable_neg, Measure.map_neg_eq_self volume⟩
  let m : MeasurePreserving (fun x : ℝ => h + -x) volume volume :=
    (measurePreserving_add_left volume h).comp mn
  have hmap : ∀ᵐ z ∂Measure.map (fun x : ℝ => h + -x) volume, z ∈ Z := by
    simpa [m.map_eq] using hZ
  have hshift : ∀ᵐ x ∂volume, h + -x ∈ Z :=
    ae_of_ae_map ((measurable_const.add measurable_id.neg).aemeasurable) hmap
  have hboth : ∀ᵐ x ∂volume, x ∈ Z ∧ h + -x ∈ Z := hZ.and hshift
  rcases hboth.exists with ⟨u, hu, hv⟩
  refine ⟨u, hu, h + -u, hv, ?_⟩
  ring_nf

/-- If null increments hold on a full-measure set of increments, then they
hold for every increment. -/
lemma hasNullIncrements_of_ae {r : ℝ → ℝ} {Z : Set ℝ}
    (hZ : ∀ᵐ z ∂volume, z ∈ Z)
    (hr : ∀ z ∈ Z, ∀ᵐ x ∂volume, r (x + z) - r x = 0) :
    HasNullIncrements r := by
  intro h
  rcases fullMeasure_add_self hZ h with ⟨u, hu, v, hv, rfl⟩
  exact nullIncrement_add (hr u hu) (hr v hv)

/-- The two-variable difference kernel used in the measurable proof. -/
def differenceKernel (f : ℝ → ℝ) (x t : ℝ) : ℝ :=
  f (x + t) - f x

/-- Difference kernels satisfy the translation cocycle identity pointwise. -/
lemma differenceKernel_cocycle (f : ℝ → ℝ) (x y z : ℝ) :
    differenceKernel f x (y + z) =
      differenceKernel f (x + y) z + differenceKernel f x y := by
  unfold differenceKernel
  ring_nf

/-- A second difference in a fixed spatial direction.  Constants in a
difference section disappear here, which is why these kernels are the
coordinates used by Laczkovich's norm modulo additive summands. -/
def secondDifferenceKernel (f : ℝ → ℝ) (q x t : ℝ) : ℝ :=
  differenceKernel f (x + q) t - differenceKernel f x t

/-- Commuting two differences rewrites a second difference in the parameter
as a translate difference of one fixed measurable section. -/
lemma secondDifferenceKernel_eq (f : ℝ → ℝ) (q x t : ℝ) :
    secondDifferenceKernel f q x t =
      differenceKernel f (x + t) q - differenceKernel f x q := by
  unfold secondDifferenceKernel differenceKernel
  ring

/-- For every fixed spatial shift, the second-difference kernel is jointly
a.e. measurable in base point and parameter.  The original difference
kernel need not be jointly measurable because an additive summand can be
nonmeasurable in the parameter; the second difference removes precisely
that obstruction. -/
lemma secondDifferenceKernel_measurable
    {f : ℝ → ℝ} (hf : HasMeasurableDifferences f) (q : ℝ) :
    AEMeasurable
      (fun p : ℝ × ℝ => secondDifferenceKernel f q p.1 p.2)
      (volume.prod volume) := by
  let u : ℝ → ℝ := fun x => differenceKernel f x q
  have hu : AEMeasurable u volume := hf q
  let v : ℝ → ℝ := hu.mk u
  have hv : Measurable v := hu.measurable_mk
  have huv : u =ᵐ[volume] v := hu.ae_eq_mk
  have hshift :
      ∀ᵐ p : ℝ × ℝ ∂volume.prod volume,
        u (p.1 + p.2) = v (p.1 + p.2) := by
    have hm :
        Measure.QuasiMeasurePreserving
          (fun p : ℝ × ℝ => p.1 + p.2) (volume.prod volume) volume := by
      have hprod :
          MeasurePreserving (fun p : ℝ × ℝ => (p.1, p.1 + p.2))
            (volume.prod volume) (volume.prod volume) :=
        measurePreserving_prod_add volume volume
      have hsnd :
          Measure.QuasiMeasurePreserving (Prod.snd : ℝ × ℝ → ℝ)
            (volume.prod volume) volume :=
        Measure.quasiMeasurePreserving_snd
      convert hsnd.comp hprod.quasiMeasurePreserving using 1
      rfl
    exact hm.ae huv
  have hbase :
      ∀ᵐ p : ℝ × ℝ ∂volume.prod volume, u p.1 = v p.1 := by
    exact Measure.quasiMeasurePreserving_fst.ae huv
  have hmeas :
      Measurable (fun p : ℝ × ℝ => v (p.1 + p.2) - v p.1) :=
    (hv.comp (measurable_fst.add measurable_snd)).sub (hv.comp measurable_fst)
  apply hmeas.aemeasurable.congr
  filter_upwards [hshift, hbase] with p hp hpx
  rw [secondDifferenceKernel_eq]
  symm
  change u (p.1 + p.2) - u p.1 = v (p.1 + p.2) - v p.1
  rw [hp, hpx]

/-- One bounded convergence-in-measure coordinate of Laczkovich's
quotient norm.  The spatial integral is over a unit window and the truncation
keeps it finite for arbitrary measurable difference sections. -/
noncomputable def secondDifferenceEnergy (f : ℝ → ℝ) (q t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioc (0 : ℝ) 1,
    ENNReal.ofReal (min 1 |secondDifferenceKernel f q x t|) ∂volume

/-- Every fixed-shift energy coordinate is a.e. measurable in the increment.
This is Tonelli applied to the preceding jointly measurable second kernel. -/
lemma secondDifferenceEnergy_aemeasurable
    {f : ℝ → ℝ} (hf : HasMeasurableDifferences f) (q : ℝ) :
    AEMeasurable (secondDifferenceEnergy f q) volume := by
  have hsecond :
      AEMeasurable
        (fun p : ℝ × ℝ => secondDifferenceKernel f q p.1 p.2)
        ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) := by
    exact (secondDifferenceKernel_measurable hf q).mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have henergy :
      AEMeasurable
        (fun p : ℝ × ℝ =>
          ENNReal.ofReal (min 1 |secondDifferenceKernel f q p.1 p.2|))
        ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) := by
    exact ((aemeasurable_const.min hsecond.norm).ennreal_ofReal)
  change AEMeasurable
    (fun t : ℝ => ∫⁻ x in Ioc (0 : ℝ) 1,
      ENNReal.ofReal (min 1 |secondDifferenceKernel f q x t|) ∂volume) volume
  exact henergy.lintegral_prod_left'

/-- Vanishing of one energy coordinate means that its second difference
vanishes almost everywhere on the unit window. -/
lemma secondDifferenceEnergy_eq_zero_ae
    {f : ℝ → ℝ} (hf : HasMeasurableDifferences f) (q t : ℝ)
    (hzero : secondDifferenceEnergy f q t = 0) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      secondDifferenceKernel f q x t = 0 := by
  have ht : AEMeasurable (fun x : ℝ => differenceKernel f x t) volume := hf t
  have hshift :
      AEMeasurable (fun x : ℝ => differenceKernel f (x + q) t) volume :=
    ht.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume q).quasiMeasurePreserving
  have hsec :
      AEMeasurable (fun x : ℝ => secondDifferenceKernel f q x t) volume := by
    unfold secondDifferenceKernel
    exact hshift.sub ht
  have henergy :
      AEMeasurable
        (fun x : ℝ =>
          ENNReal.ofReal (min 1 |secondDifferenceKernel f q x t|))
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((aemeasurable_const.min hsec.norm).ennreal_ofReal).restrict
  change (∫⁻ x in Ioc (0 : ℝ) 1,
    ENNReal.ofReal (min 1 |secondDifferenceKernel f q x t|) ∂volume) = 0 at hzero
  have hae :
      (fun x : ℝ =>
          ENNReal.ofReal (min 1 |secondDifferenceKernel f q x t|)) =ᵐ[
            volume.restrict (Ioc (0 : ℝ) 1)] 0 :=
    (lintegral_eq_zero_iff' henergy).1 hzero
  filter_upwards [hae] with x hx
  have hmin : min 1 |secondDifferenceKernel f q x t| = 0 := by
    have hle : min 1 |secondDifferenceKernel f q x t| ≤ 0 :=
      ENNReal.ofReal_eq_zero.mp hx
    exact le_antisymm hle (le_min zero_le_one (abs_nonneg _))
  have habs : |secondDifferenceKernel f q x t| = 0 := by
    by_contra hne
    have hpos : 0 < |secondDifferenceKernel f q x t| :=
      lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    have : 0 < min 1 |secondDifferenceKernel f q x t| :=
      lt_min zero_lt_one hpos
    linarith
  exact abs_eq_zero.mp habs

/-- An a.e. zero assertion for a one-periodic function on one fundamental
interval propagates to the whole real line. -/
lemma periodic_ae_zero_of_Ioc {u : ℝ → ℝ}
    (hu : Function.Periodic u 1)
    (hzero : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), u x = 0) :
    ∀ᵐ x ∂volume, u x = 0 := by
  rw [← Measure.restrict_univ (μ := volume)]
  have hcover : (⋃ n : ℤ, Ioc (n : ℝ) (n + 1 : ℝ)) = (univ : Set ℝ) := by
    ext x
    simp only [mem_iUnion, mem_Ioc, mem_univ, iff_true]
    refine ⟨⌈x⌉ - 1, ?_⟩
    constructor
    · rw [Int.cast_sub, Int.cast_one, sub_lt_iff_lt_add]
      exact Int.ceil_lt_add_one x
    · simpa [Int.cast_sub, Int.cast_one] using Int.le_ceil x
  rw [← hcover, ae_restrict_iUnion_iff]
  intro n
  have hfull :
      ∀ᵐ x ∂volume, x ∈ Ioc (0 : ℝ) 1 → u x = 0 :=
    (ae_restrict_iff' measurableSet_Ioc).1 hzero
  have htrans := ae_translate hfull (-(n : ℝ))
  filter_upwards [ae_restrict_of_ae htrans,
    ae_restrict_mem measurableSet_Ioc] with x hx hmem
  have hxmem : x - (n : ℝ) ∈ Ioc (0 : ℝ) 1 := by
    constructor <;> linarith [hmem.1, hmem.2]
  have hx' : u (x + -(n : ℝ)) = 0 := hx (by simpa [sub_eq_add_neg] using hxmem)
  have hper := hu.zsmul n (x - (n : ℝ))
  have hper' : u x = u (x - (n : ℝ)) := by
    ring_nf at hper
    exact hper
  rw [hper']
  convert hx' using 1 <;> ring

/-- The base-point variable of a second difference inherits the unit period
of the original function. -/
lemma secondDifferenceKernel_periodic_base {p : ℝ → ℝ}
    (hp : Function.Periodic p 1) (q t : ℝ) :
    Function.Periodic (fun x => secondDifferenceKernel p q x t) 1 := by
  intro x
  unfold secondDifferenceKernel differenceKernel
  dsimp
  rw [show x + 1 + q + t = (x + q + t) + 1 by ring,
    show x + 1 + q = (x + q) + 1 by ring,
    show x + 1 + t = (x + t) + 1 by ring, hp, hp, hp, hp]

/-- For a periodic function, zero energy makes the corresponding second
difference vanish almost everywhere globally. -/
lemma secondDifferenceEnergy_eq_zero_ae_full
    {p : ℝ → ℝ} (hpper : Function.Periodic p 1)
    (hp : HasMeasurableDifferences p) (q t : ℝ)
    (hzero : secondDifferenceEnergy p q t = 0) :
    ∀ᵐ x ∂volume, secondDifferenceKernel p q x t = 0 := by
  apply periodic_ae_zero_of_Ioc (secondDifferenceKernel_periodic_base hpper q t)
  exact secondDifferenceEnergy_eq_zero_ae hp q t hzero

/-- A fixed enumeration of the rational shifts used by the countable
quotient energy. -/
noncomputable def rationalShiftAt (n : ℕ) : ℝ :=
  ((Encodable.decode (α := ℚ) n).getD 0 : ℚ)

/-- Laczkovich's countable convergence-in-measure energy modulo constants:
all rational second-difference coordinates are summed with positive
summable weights. -/
noncomputable def laczkovichEnergy (f : ℝ → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ,
    ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) *
      secondDifferenceEnergy f (rationalShiftAt n) t

/-- The aggregate quotient energy remains a.e. measurable in the increment. -/
lemma laczkovichEnergy_aemeasurable
    {f : ℝ → ℝ} (hf : HasMeasurableDifferences f) :
    AEMeasurable (laczkovichEnergy f) volume := by
  unfold laczkovichEnergy
  apply AEMeasurable.tsum
  intro n
  exact aemeasurable_const.mul
    (secondDifferenceEnergy_aemeasurable hf (rationalShiftAt n))

/-- Every rational shift occurs in the chosen enumeration. -/
lemma exists_rationalShiftAt (q : ℚ) :
    ∃ n : ℕ, rationalShiftAt n = (q : ℝ) := by
  let n : ℕ := Encodable.encode q
  refine ⟨n, ?_⟩
  simp [rationalShiftAt, n]

/-- If the aggregate energy is zero, each individual rational coordinate is
zero because its weight is strictly nonzero. -/
lemma secondDifferenceEnergy_eq_zero_of_laczkovichEnergy_eq_zero
    {f : ℝ → ℝ} {t : ℝ} (n : ℕ)
    (hzero : laczkovichEnergy f t = 0) :
    secondDifferenceEnergy f (rationalShiftAt n) t = 0 := by
  have hn :
      ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) *
          secondDifferenceEnergy f (rationalShiftAt n) t = 0 := by
    apply (ENNReal.tsum_eq_zero.mp ?_) n
    exact hzero
  have hweight : ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) ≠ 0 := by
    apply pow_ne_zero
    norm_num
  exact (mul_eq_zero.mp hn).resolve_left hweight

/-- The bounded spatial piece attached to one parameter in the Baire
uniformization. -/
def boundedDifferencePiece (f : ℝ → ℝ) (s : Set ℝ) (n : ℕ) (t : ℝ) : Set ℝ :=
  s ∩ {x : ℝ | |differenceKernel f x t| ≤ n}

lemma volume_translateSet_eq (s : Set ℝ) (a : ℝ) :
    volume (translateSet s a) = volume s := by
  rw [← measure_preimage_add_right volume (-a) s]
  congr 1

/-- Subtracting two sections with the same base point is one translated
difference section. -/
lemma differenceKernel_sub_at_add (f : ℝ → ℝ) (x s t : ℝ) :
    differenceKernel f (x + s) (t - s) =
      differenceKernel f x t - differenceKernel f x s := by
  unfold differenceKernel
  ring_nf

/-- If two bounded section pieces overlap with positive measure, their
parameter difference has a bounded positive-measure piece.  This is the
finite-measure cocycle calculation used after the Baire extraction. -/
lemma positiveMeasure_boundedDifference_of_overlap
    {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {t u : ℝ}
    (hinter :
      0 < volume (boundedDifferencePiece f s n t ∩
        boundedDifferencePiece f s n u)) :
    0 < volume {x : ℝ | |differenceKernel f x (t - u)| ≤ 2 * n} := by
  let A : Set ℝ :=
    translateSet
      (boundedDifferencePiece f s n t ∩ boundedDifferencePiece f s n u) u
  have hApos : 0 < volume A := by
    simpa [A, volume_translateSet_eq] using hinter
  have hAsub : A ⊆ {x : ℝ | |differenceKernel f x (t - u)| ≤ 2 * n} := by
    intro x hx
    have hx' : x - u ∈ boundedDifferencePiece f s n t ∩
        boundedDifferencePiece f s n u := by
      simpa [A, translateSet] using hx
    have ht := hx'.1.2
    have hu := hx'.2.2
    change |differenceKernel f (x - u) t| ≤ n at ht
    change |differenceKernel f (x - u) u| ≤ n at hu
    have hkernel :=
      differenceKernel_sub_at_add f (x - u) u t
    have hxarg : x - u + u = x := by ring
    rw [hxarg] at hkernel
    change |differenceKernel f x (t - u)| ≤ 2 * n
    rw [hkernel]
    rw [abs_le]
    constructor <;>
      nlinarith [abs_le.mp ht, abs_le.mp hu]
  exact lt_of_lt_of_le hApos (measure_mono hAsub)

/-- The density-local relation used in Laczkovich's localization argument:
the difference from one point to another is essentially bounded near the
base point in the density sense. -/
def DensityRelated (f : ℝ → ℝ) (y z : ℝ) : Prop :=
  HasDensityEssentialBoundAt
    (fun x => differenceKernel f x (z - y)) y

/-- The localization relation is reflexive because the zero difference
vanishes identically. -/
lemma densityRelated_refl (f : ℝ → ℝ) (y : ℝ) :
    DensityRelated f y y := by
  refine ⟨0, univ, MeasurableSet.univ, densityOne_univ y, ?_⟩
  filter_upwards [] with x
  simp [differenceKernel]

/-- Two density-local bounds with the same base point compose after
translating the intersection of their witnesses to the first target point.
This is the quantitative cocycle step behind the localization relation. -/
lemma densityRelated_of_common_left {f : ℝ → ℝ} {t y z : ℝ}
    (hy : DensityRelated f t y) (hz : DensityRelated f t z) :
    DensityRelated f y z := by
  rcases hy with ⟨n, s, hsm, hsden, hsbound⟩
  rcases hz with ⟨m, q, hqm, hqden, hqbound⟩
  let a : ℝ := y - t
  let A : Set ℝ := translateSet (s ∩ q) a
  have hAmeas : MeasurableSet A :=
    translateSet_measurable (hsm.inter hqm)
  have hAden : IsDensityOneAt A y := by
    have htranslate :=
      densityOne_translate (hsm.inter hqm)
        (densityOne_inter hsm hqm hsden hqden) (a := a)
    convert htranslate using 1 <;> dsimp [a] <;> ring
  refine ⟨n + m, A, hAmeas, hAden, ?_⟩
  have hsfull :
      ∀ᵐ u ∂volume, u ∈ s →
        |differenceKernel f u (y - t)| ≤ n :=
    (ae_restrict_iff' hsm).1 hsbound
  have hqfull :
      ∀ᵐ u ∂volume, u ∈ q →
        |differenceKernel f u (z - t)| ≤ m :=
    (ae_restrict_iff' hqm).1 hqbound
  have hboth :
      ∀ᵐ u ∂volume, u ∈ s ∩ q →
        |differenceKernel f u (y - t)| ≤ n ∧
          |differenceKernel f u (z - t)| ≤ m := by
    filter_upwards [hsfull, hqfull] with u hus huq hu
    exact ⟨hus hu.1, huq hu.2⟩
  apply (ae_restrict_iff' hAmeas).2
  filter_upwards [ae_translate hboth (-a)] with x hx hxm
  have hmem : x + -a ∈ s ∩ q := by
    have hmem' : x - a ∈ s ∩ q := by
      simpa [A, translateSet] using hxm
    convert hmem' using 1
    ring
  have hbounds := hx hmem
  have hc := differenceKernel_cocycle f (x + -a) (y - t) (z - y)
  have hxarg : x + -a + (y - t) = x := by
    dsimp [a]
    ring
  have hsum :
      differenceKernel f (x + -a) (z - t) =
        differenceKernel f x (z - y) +
          differenceKernel f (x + -a) (y - t) := by
    have hleft : y - t + (z - y) = z - t := by ring
    rw [hleft, hxarg] at hc
    exact hc
  rw [hsum] at hbounds
  rw [Nat.cast_add]
  rw [abs_le]
  constructor <;>
    nlinarith [abs_le.mp hbounds.1, abs_le.mp hbounds.2]

/-- Reversing a density-local relation translates its witness to the other
endpoint and negates the corresponding difference. -/
lemma densityRelated_symm {f : ℝ → ℝ} {y z : ℝ}
    (hyz : DensityRelated f y z) :
    DensityRelated f z y := by
  rcases hyz with ⟨n, s, hsm, hsden, hsbound⟩
  let a : ℝ := z - y
  let A : Set ℝ := translateSet s a
  have hAmeas : MeasurableSet A := translateSet_measurable hsm
  have hAden : IsDensityOneAt A z := by
    have htranslate := densityOne_translate hsm hsden (a := a)
    convert htranslate using 1 <;> dsimp [a] <;> ring
  refine ⟨n, A, hAmeas, hAden, ?_⟩
  have hsfull :
      ∀ᵐ u ∂volume, u ∈ s →
        |differenceKernel f u (z - y)| ≤ n :=
    (ae_restrict_iff' hsm).1 hsbound
  apply (ae_restrict_iff' hAmeas).2
  filter_upwards [ae_translate hsfull (-a)] with x hx hxm
  have hmem : x + -a ∈ s := by
    have hmem' : x - a ∈ s := by
      simpa [A, translateSet] using hxm
    convert hmem' using 1
    ring
  have hbound := hx hmem
  have htarget :
      differenceKernel f x (y - z) =
        -differenceKernel f (x + -a) (z - y) := by
    unfold differenceKernel
    dsimp [a]
    ring_nf
  rw [htarget, abs_neg]
  exact hbound

/-- The density-local relation is transitive. -/
lemma densityRelated_trans {f : ℝ → ℝ} {x y z : ℝ}
    (hxy : DensityRelated f x y) (hyz : DensityRelated f y z) :
    DensityRelated f x z :=
  densityRelated_of_common_left (densityRelated_symm hxy) hyz

/-- For each fixed increment, almost every base point is related to its
translate.  This is the direct bridge from sectionwise measurability to the
density-local relation. -/
lemma ae_densityRelated_add {f : ℝ → ℝ}
    (hf : HasMeasurableDifferences f) (t : ℝ) :
    ∀ᵐ x ∂volume, DensityRelated f x (x + t) := by
  filter_upwards [ae_hasDensityEssentialBoundAt (hf t)] with x hx
  simpa [DensityRelated, differenceKernel, add_comm] using hx

/-- A fixed-radius version of the density-local bound, with an arbitrary
scalar center.  The radius stays visible under composition, which is the
quantitative form needed by the unbounded localization step. -/
def HasDensityCenteredBoundAt (u : ℝ → ℝ) (D x : ℝ) : Prop :=
  ∃ c : ℝ, ∃ s : Set ℝ,
    MeasurableSet s ∧ IsDensityOneAt s x ∧
      ∀ᵐ y ∂volume.restrict s, |u y - c| ≤ D

/-- Every a.e. measurable real function has a centered unit bound at almost
every point: partition the range into unit integer strips and apply the
density theorem on each strip. -/
lemma ae_hasDensityCenteredBoundAt_one {u : ℝ → ℝ}
    (hu : AEMeasurable u volume) :
    ∀ᵐ x ∂volume, HasDensityCenteredBoundAt u 1 x := by
  let v : ℝ → ℝ := hu.mk u
  have hv : Measurable v := hu.measurable_mk
  let A : ℤ → Set ℝ := fun n => {y : ℝ | (n : ℝ) ≤ v y ∧ v y < (n : ℝ) + 1}
  have hAm (n : ℤ) : MeasurableSet (A n) := by
    exact (measurableSet_le measurable_const hv).inter
      (measurableSet_lt hv measurable_const)
  have hcover : (⋃ n, A n) = (univ : Set ℝ) := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    refine ⟨⌊v x⌋, ?_⟩
    exact ⟨Int.floor_le (v x), Int.lt_floor_add_one (v x)⟩
  have hpiece (n : ℤ) :
      ∀ᵐ x ∂volume.restrict (A n), HasDensityCenteredBoundAt u 1 x := by
    have hden : ∀ᵐ x ∂volume.restrict (A n), IsDensityOneAt (A n) x := by
      simpa [IsDensityOneAt] using
        (Besicovitch.ae_tendsto_measure_inter_div volume (A n))
    filter_upwards [hden] with x hxden
    refine ⟨(n : ℝ), A n, hAm n, hxden, ?_⟩
    filter_upwards [ae_restrict_of_ae hu.ae_eq_mk,
      ae_restrict_mem (hAm n)] with y hy hymem
    rw [hy]
    rw [abs_le]
    constructor <;> linarith [hymem.1, hymem.2]
  have hall :
      ∀ᵐ x ∂volume.restrict (⋃ n, A n), HasDensityCenteredBoundAt u 1 x :=
    (ae_restrict_iUnion_iff A _).2 hpiece
  simpa [hcover] using hall

/-- Two points are centered-related with radius D when their difference
kernel has a density-local essential oscillation at most D. -/
def DensityCenteredRelated (f : ℝ → ℝ) (D y z : ℝ) : Prop :=
  HasDensityCenteredBoundAt
    (fun x => differenceKernel f x (z - y)) D y

lemma densityCenteredRelated_refl (f : ℝ → ℝ) (D : ℝ) (hD : 0 ≤ D) (y : ℝ) :
    DensityCenteredRelated f D y y := by
  refine ⟨0, univ, MeasurableSet.univ, densityOne_univ y, ?_⟩
  filter_upwards [] with x
  simp [differenceKernel, hD]

/-- Centered local bounds with a common left endpoint compose, adding their
radii and subtracting their centers. -/
lemma densityCenteredRelated_of_common_left {f : ℝ → ℝ} {D E t y z : ℝ}
    (hy : DensityCenteredRelated f D t y)
    (hz : DensityCenteredRelated f E t z) :
    DensityCenteredRelated f (D + E) y z := by
  rcases hy with ⟨cy, s, hsm, hsden, hsbound⟩
  rcases hz with ⟨cz, q, hqm, hqden, hqbound⟩
  let a : ℝ := y - t
  let A : Set ℝ := translateSet (s ∩ q) a
  have hAmeas : MeasurableSet A :=
    translateSet_measurable (hsm.inter hqm)
  have hAden : IsDensityOneAt A y := by
    have htranslate :=
      densityOne_translate (hsm.inter hqm)
        (densityOne_inter hsm hqm hsden hqden) (a := a)
    convert htranslate using 1 <;> dsimp [a] <;> ring
  refine ⟨cz - cy, A, hAmeas, hAden, ?_⟩
  have hsfull :
      ∀ᵐ u ∂volume, u ∈ s →
        |differenceKernel f u (y - t) - cy| ≤ D :=
    (ae_restrict_iff' hsm).1 hsbound
  have hqfull :
      ∀ᵐ u ∂volume, u ∈ q →
        |differenceKernel f u (z - t) - cz| ≤ E :=
    (ae_restrict_iff' hqm).1 hqbound
  have hboth :
      ∀ᵐ u ∂volume, u ∈ s ∩ q →
        |differenceKernel f u (y - t) - cy| ≤ D ∧
          |differenceKernel f u (z - t) - cz| ≤ E := by
    filter_upwards [hsfull, hqfull] with u hus huq hu
    exact ⟨hus hu.1, huq hu.2⟩
  apply (ae_restrict_iff' hAmeas).2
  filter_upwards [ae_translate hboth (-a)] with x hx hxm
  have hmem : x + -a ∈ s ∩ q := by
    have hmem' : x - a ∈ s ∩ q := by
      simpa [A, translateSet] using hxm
    convert hmem' using 1
    ring
  have hbounds := hx hmem
  have hc := differenceKernel_cocycle f (x + -a) (y - t) (z - y)
  have hxarg : x + -a + (y - t) = x := by
    dsimp [a]
    ring
  have hsum :
      differenceKernel f (x + -a) (z - t) =
        differenceKernel f x (z - y) +
          differenceKernel f (x + -a) (y - t) := by
    have hleft : y - t + (z - y) = z - t := by ring
    rw [hleft, hxarg] at hc
    exact hc
  rw [hsum] at hbounds
  rw [abs_le]
  constructor <;>
    nlinarith [abs_le.mp hbounds.1, abs_le.mp hbounds.2]

lemma densityCenteredRelated_symm {f : ℝ → ℝ} {D y z : ℝ}
    (hyz : DensityCenteredRelated f D y z) :
    DensityCenteredRelated f D z y := by
  rcases hyz with ⟨c, s, hsm, hsden, hsbound⟩
  let a : ℝ := z - y
  let A : Set ℝ := translateSet s a
  have hAmeas : MeasurableSet A := translateSet_measurable hsm
  have hAden : IsDensityOneAt A z := by
    have htranslate := densityOne_translate hsm hsden (a := a)
    convert htranslate using 1 <;> dsimp [a] <;> ring
  refine ⟨-c, A, hAmeas, hAden, ?_⟩
  have hsfull :
      ∀ᵐ u ∂volume, u ∈ s →
        |differenceKernel f u (z - y) - c| ≤ D :=
    (ae_restrict_iff' hsm).1 hsbound
  apply (ae_restrict_iff' hAmeas).2
  filter_upwards [ae_translate hsfull (-a)] with x hx hxm
  have hmem : x + -a ∈ s := by
    have hmem' : x - a ∈ s := by
      simpa [A, translateSet] using hxm
    convert hmem' using 1
    ring
  have hbound := hx hmem
  have htarget :
      differenceKernel f x (y - z) =
        -differenceKernel f (x + -a) (z - y) := by
    unfold differenceKernel
    dsimp [a]
    ring_nf
  rw [htarget]
  have hneg :
      -differenceKernel f (x + -a) (z - y) - -c =
        -(differenceKernel f (x + -a) (z - y) - c) := by
    ring
  rw [hneg, abs_neg]
  exact hbound

lemma densityCenteredRelated_trans {f : ℝ → ℝ} {D E x y z : ℝ}
    (hxy : DensityCenteredRelated f D x y)
    (hyz : DensityCenteredRelated f E y z) :
    DensityCenteredRelated f (D + E) x z :=
  densityCenteredRelated_of_common_left (densityCenteredRelated_symm hxy) hyz

lemma densityCenteredRelated_mono {f : ℝ → ℝ} {D E y z : ℝ}
    (hDE : D ≤ E)
    (hyz : DensityCenteredRelated f D y z) :
    DensityCenteredRelated f E y z := by
  rcases hyz with ⟨c, s, hsm, hsden, hsbound⟩
  exact ⟨c, s, hsm, hsden, hsbound.mono fun _ hx => hx.trans hDE⟩

/-- For a fixed increment, almost every base point is centered-related to
its translate with the same unit radius. -/
lemma ae_densityCenteredRelated_add {f : ℝ → ℝ}
    (hf : HasMeasurableDifferences f) (t : ℝ) :
    ∀ᵐ x ∂volume, DensityCenteredRelated f 1 x (x + t) := by
  filter_upwards [ae_hasDensityCenteredBoundAt_one (hf t)] with x hx
  simpa [DensityCenteredRelated, differenceKernel, add_comm] using hx

/-- One base point can be chosen simultaneously for every rational
increment.  This is the countable full-measure intersection which replaces
the rational skeleton in the category proof of the localization theorem. -/
lemma exists_base_densityCenteredRelated_rat
    {f : ℝ → ℝ} (hf : HasMeasurableDifferences f) :
    ∃ q0 : ℝ, ∀ q : ℚ,
      DensityCenteredRelated f 1 q0 (q0 + q) := by
  have hall :
      ∀ᵐ x ∂volume, ∀ q : ℚ,
        DensityCenteredRelated f 1 x (x + q) := by
    rw [ae_all_iff]
    intro q
    simpa using ae_densityCenteredRelated_add hf (q : ℝ)
  rcases hall.exists with ⟨q0, hq0⟩
  exact ⟨q0, hq0⟩

/-- Translating the rational points preserves their density in the real
line. -/
lemma dense_range_add_rat (q0 : ℝ) :
    Dense (Set.range fun q : ℚ => q0 + (q : ℝ)) := by
  have hdense : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
  rw [dense_iff_inter_open]
  intro U hU hUne
  let V : Set ℝ := (fun x : ℝ => q0 + x) ⁻¹' U
  have hVopen : IsOpen V :=
    hU.preimage (continuous_const.add continuous_id)
  have hVne : V.Nonempty := by
    rcases hUne with ⟨u, hu⟩
    refine ⟨u - q0, ?_⟩
    simpa [V] using hu
  rcases hdense.exists_mem_open hVopen hVne with ⟨x, ⟨q, rfl⟩, hxU⟩
  refine ⟨q0 + (q : ℝ), ?_, ?_⟩
  · simpa [V] using hxU
  · exact ⟨q, rfl⟩

/-- The fixed-radius centered relation therefore has a dense class. -/
lemma dense_centeredClass_of_rationals
    {f : ℝ → ℝ} (hf : HasMeasurableDifferences f) :
    ∃ q0 : ℝ,
      Dense {y : ℝ | DensityCenteredRelated f 1 q0 y} := by
  rcases exists_base_densityCenteredRelated_rat hf with ⟨q0, hq0⟩
  refine ⟨q0, ?_⟩
  apply Dense.mono _ (dense_range_add_rat q0)
  rintro _ ⟨q, rfl⟩
  exact hq0 q

/-- The defect left after replacing a difference kernel by a measurable
two-variable representative. -/
def sectionDefect (f : ℝ → ℝ) (G : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  differenceKernel f x t - G x t

/-- A measurable two-variable function representing almost every measurable
section of a difference kernel. -/
def HasJointDifferenceRepresentative (f : ℝ → ℝ) : Prop :=
  ∃ G : ℝ → ℝ → ℝ,
    Measurable (Function.uncurry G) ∧
      ∀ᵐ t ∂volume, ∀ᵐ x ∂volume, differenceKernel f x t = G x t

/-- The analytic core isolated by Laczkovich: an additive correction makes
the difference sections have a joint measurable representative. -/
def HasCorrectedJointDifferenceRepresentative (f : ℝ → ℝ) : Prop :=
  ∃ H : ℝ → ℝ,
    IsAdditiveFn H ∧
      HasJointDifferenceRepresentative (fun y => f y - H y)

/-- The three-variable cocycle defect depends only on the measurable
representative, not on the original function. -/
lemma sectionDefect_cocycle (f : ℝ → ℝ) (G : ℝ → ℝ → ℝ) (x y z : ℝ) :
    sectionDefect f G x (y + z) -
        sectionDefect f G (x + y) z -
          sectionDefect f G x y =
      -G x (y + z) + G (x + y) z + G x y := by
  unfold sectionDefect
  rw [differenceKernel_cocycle]
  ring_nf

/-- A three-variable Fubini reordering used to choose the good first
coordinate in the cocycle argument. -/
lemma ae_swap_three_of_measurable (L : ℝ → ℝ → ℝ → ℝ)
    (hLm : Measurable fun p : ℝ × (ℝ × ℝ) => L p.1 p.2.2 p.2.1)
    (hL : ∀ᵐ z ∂volume, ∀ᵐ y ∂volume, ∀ᵐ x ∂volume, L x y z = 0) :
    ∀ᵐ x ∂volume, ∀ᵐ z ∂volume, ∀ᵐ y ∂volume, L x y z = 0 := by
  have hsection (z : ℝ) :
      Measurable (fun p : ℝ × ℝ => L p.2 p.1 z) :=
    hLm.comp (measurable_snd.prodMk (measurable_const.prodMk measurable_fst))
  have hzyx :
      ∀ᵐ z ∂volume, ∀ᵐ p ∂volume.prod volume, L p.2 p.1 z = 0 := by
    filter_upwards [hL] with z hz
    exact (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun (hsection z) measurable_const)).2 hz
  have hright :
      ∀ᵐ p ∂volume.prod (volume.prod volume), L p.2.2 p.2.1 p.1 = 0 := by
    have hm :
        Measurable (fun p : ℝ × (ℝ × ℝ) => L p.2.2 p.2.1 p.1) :=
      hLm.comp (measurable_snd.snd.prodMk (measurable_fst.prodMk measurable_snd.fst))
    exact (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun hm measurable_const)).2 hzyx
  have hleft :
      ∀ᵐ p ∂(volume.prod volume).prod volume, L p.2 p.1.2 p.1.1 = 0 := by
    have hmap :
        ∀ᵐ p ∂Measure.map MeasurableEquiv.prodAssoc ((volume.prod volume).prod volume),
          L p.2.2 p.2.1 p.1 = 0 := by
      simpa [Measure.prodAssoc_prod] using hright
    have hpull :=
      ae_of_ae_map MeasurableEquiv.prodAssoc.measurable.aemeasurable hmap
    simpa [MeasurableEquiv.prodAssoc] using hpull
  have hmap :
      ∀ᵐ p ∂Measure.map Prod.swap (volume.prod (volume.prod volume)),
        L p.2 p.1.2 p.1.1 = 0 := by
    simpa [Measure.prod_swap] using hleft
  have hpull := ae_of_ae_map measurable_swap.aemeasurable hmap
  have houter :
      ∀ᵐ p ∂volume.prod (volume.prod volume), L p.1 p.2.2 p.2.1 = 0 := by
    simpa using hpull
  filter_upwards [Measure.ae_ae_of_ae_prod houter] with x hx
  exact Measure.ae_ae_of_ae_prod hx

/-- The Fubini part of Laczkovich's argument reduces the bounded case to
the section data appearing here.  This lemma performs the final algebraic
assembly once that data is available. -/
lemma measurableDecomposition_of_sectionData
    (f : ℝ → ℝ) (G : ℝ → ℝ → ℝ) (x0 : ℝ) (Z : Set ℝ)
    (hG : Measurable (Function.uncurry G))
    (hZ : ∀ᵐ z ∂volume, z ∈ Z)
    (hS : ∀ z ∈ Z, ∀ᵐ y ∂volume, sectionDefect f G (x0 + y) z = 0)
    (hL : ∀ z ∈ Z, ∀ᵐ y ∂volume,
      sectionDefect f G x0 (y + z) -
          sectionDefect f G (x0 + y) z -
            sectionDefect f G x0 y = 0) :
    HasMeasurableDecomposition f := by
  let g : ℝ → ℝ := fun y => f x0 + G x0 (y - x0)
  let r : ℝ → ℝ := fun y => sectionDefect f G x0 (y - x0)
  have hg : AEMeasurable g volume := by
    have hsection :
        Measurable (fun y : ℝ => G x0 (y - x0)) :=
      hG.comp (measurable_const.prodMk (measurable_id.sub_const x0))
    exact (measurable_const.add hsection).aemeasurable
  have hr : HasNullIncrements r := by
    apply hasNullIncrements_of_ae hZ
    intro z hz
    have hLz := ae_translate (hL z hz) (-x0)
    have hSz := ae_translate (hS z hz) (-x0)
    filter_upwards [hLz, hSz] with y hyL hyS
    dsimp [r]
    ring_nf at hyL hyS ⊢
    linarith
  refine ⟨g, fun _ => 0, r, hg, zero_isAdditiveFn, ?_, hr⟩
  intro y
  dsimp [g, r, sectionDefect, differenceKernel]
  ring_nf

/-- A jointly measurable representative of the difference kernel is enough
to produce the corrected decomposition.  The bounded-difference argument
constructs exactly such a representative. -/
lemma measurableDecomposition_of_jointRepresentative
    (f : ℝ → ℝ) (G : ℝ → ℝ → ℝ)
    (hG : Measurable (Function.uncurry G))
    (hKG : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume, differenceKernel f x t = G x t) :
    HasMeasurableDecomposition f := by
  let L : ℝ → ℝ → ℝ → ℝ :=
    fun x y z => -G x (y + z) + G (x + y) z + G x y
  have hLm :
      Measurable fun p : ℝ × (ℝ × ℝ) => L p.1 p.2.2 p.2.1 := by
    have hx : Measurable (fun p : ℝ × (ℝ × ℝ) => p.1) := measurable_fst
    have hy : Measurable (fun p : ℝ × (ℝ × ℝ) => p.2.2) := measurable_snd.snd
    have hz : Measurable (fun p : ℝ × (ℝ × ℝ) => p.2.1) := measurable_snd.fst
    dsimp [L]
    exact
      ((hG.comp (hx.prodMk (hy.add hz))).neg.add
        (hG.comp ((hx.add hy).prodMk hz))).add
          (hG.comp (hx.prodMk hy))
  have hS0 :
      ∀ᵐ t ∂volume, ∀ᵐ x ∂volume, sectionDefect f G x t = 0 := by
    filter_upwards [hKG] with t ht
    filter_upwards [ht] with x hx
    dsimp [sectionDefect]
    rw [hx]
    ring_nf
  have hfirst :
      ∀ᵐ z ∂volume, ∀ᵐ y ∂volume, ∀ᵐ x ∂volume,
        sectionDefect f G x (y + z) = 0 := by
    filter_upwards [] with z
    exact ae_translate hS0 z
  have hsecond :
      ∀ᵐ z ∂volume, ∀ᵐ y ∂volume, ∀ᵐ x ∂volume,
        sectionDefect f G (x + y) z = 0 := by
    filter_upwards [hS0] with z hz
    filter_upwards [] with y
    exact ae_translate hz y
  have hthird :
      ∀ᵐ z : ℝ ∂volume, ∀ᵐ y ∂volume, ∀ᵐ x ∂volume,
        sectionDefect f G x y = 0 := by
    exact (Filter.Eventually.of_forall (fun _z : ℝ => hS0) :
      ∀ᵐ _z : ℝ ∂volume, ∀ᵐ y ∂volume, ∀ᵐ x ∂volume,
        sectionDefect f G x y = 0)
  have hLnested :
      ∀ᵐ z ∂volume, ∀ᵐ y ∂volume, ∀ᵐ x ∂volume, L x y z = 0 := by
    filter_upwards [hfirst, hsecond, hthird] with z hz1 hz2 hz3
    filter_upwards [hz1, hz2, hz3] with y hy1 hy2 hy3
    filter_upwards [hy1, hy2, hy3] with x hx1 hx2 hx3
    have hc := sectionDefect_cocycle f G x y z
    rw [hx1, hx2, hx3] at hc
    simpa [L] using hc.symm
  have hLswap :
      ∀ᵐ x ∂volume, ∀ᵐ z ∂volume, ∀ᵐ y ∂volume, L x y z = 0 :=
    ae_swap_three_of_measurable L hLm hLnested
  rcases hLswap.exists with ⟨x0, hx0⟩
  let Z : Set ℝ :=
    {z | (∀ᵐ y ∂volume, L x0 y z = 0) ∧
      (∀ᵐ y ∂volume, sectionDefect f G y z = 0)}
  have hZ : ∀ᵐ z ∂volume, z ∈ Z := by
    filter_upwards [hx0, hS0] with z hzL hzS
    exact ⟨hzL, hzS⟩
  apply measurableDecomposition_of_sectionData f G x0 Z hG hZ
  · intro z hz
    simpa [add_comm] using ae_translate hz.2 x0
  · intro z hz
    filter_upwards [hz.1] with y hy
    rw [sectionDefect_cocycle]
    simpa [L] using hy

/-- It is enough to find an additive correction whose corrected difference
kernel has a jointly measurable representative. -/
lemma measurableDecomposition_of_additive_jointRepresentative
    (f H : ℝ → ℝ) (hH : IsAdditiveFn H) (G : ℝ → ℝ → ℝ)
    (hG : Measurable (Function.uncurry G))
    (hKG : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
      differenceKernel (fun y => f y - H y) x t = G x t) :
    HasMeasurableDecomposition f := by
  rcases measurableDecomposition_of_jointRepresentative
      (fun y => f y - H y) G hG hKG with
    ⟨g, H0, r, hg, hH0, hdecomp, hr⟩
  have hsum : IsAdditiveFn (fun x => H x + H0 x) := by
    intro x y
    change H (x + y) + H0 (x + y) = (H x + H0 x) + (H y + H0 y)
    rw [hH x y, hH0 x y]
    ring_nf
  refine ⟨g, fun x => H x + H0 x, r, hg, hsum, ?_, hr⟩
  intro x
  have hx := hdecomp x
  linarith

/-- The corrected joint-representative core implies the exact measurable
decomposition claimed by Problem 908. -/
lemma measurableDecomposition_of_corrected_jointRepresentative {f : ℝ → ℝ}
    (hf : HasCorrectedJointDifferenceRepresentative f) :
    HasMeasurableDecomposition f := by
  rcases hf with ⟨H, hH, G, hG, hKG⟩
  exact measurableDecomposition_of_additive_jointRepresentative f H hH G hG hKG

/-- A jointly almost-everywhere measurable difference kernel directly gives
the corrected decomposition. -/
lemma measurableDecomposition_of_joint_aemeasurable_difference (f : ℝ → ℝ)
    (hf : AEMeasurable
      (fun p : ℝ × ℝ => differenceKernel f p.1 p.2) (volume.prod volume)) :
    HasMeasurableDecomposition f := by
  let F : ℝ × ℝ → ℝ :=
    hf.mk (fun p : ℝ × ℝ => differenceKernel f p.1 p.2)
  let G : ℝ → ℝ → ℝ := fun x t => F (x, t)
  have hG : Measurable (Function.uncurry G) := by
    exact hf.measurable_mk
  have hmap :
      ∀ᵐ p ∂Measure.map Prod.swap (volume.prod volume),
        differenceKernel f p.1 p.2 = F p := by
    rw [Measure.prod_swap]
    filter_upwards [hf.ae_eq_mk] with p hp
    exact hp
  have hpull := ae_of_ae_map measurable_swap.aemeasurable hmap
  have hKG :
      ∀ᵐ t ∂volume, ∀ᵐ x ∂volume, differenceKernel f x t = G x t := by
    filter_upwards [Measure.ae_ae_of_ae_prod hpull] with t ht
    filter_upwards [ht] with x hx
    exact hx
  exact measurableDecomposition_of_jointRepresentative f G hG hKG

/-- The exact analytic target of the Laczkovich reduction: after subtracting
one additive function, the corrected kernel is jointly measurable modulo
null sets. -/
lemma measurableDecomposition_of_additive_joint_aemeasurable_difference
    (f H : ℝ → ℝ) (hH : IsAdditiveFn H)
    (hf : AEMeasurable
      (fun p : ℝ × ℝ =>
        differenceKernel (fun y => f y - H y) p.1 p.2) (volume.prod volume)) :
    HasMeasurableDecomposition f := by
  rcases measurableDecomposition_of_joint_aemeasurable_difference
      (fun y => f y - H y) hf with
    ⟨g, H0, r, hg, hH0, hdecomp, hr⟩
  have hsum : IsAdditiveFn (fun x => H x + H0 x) := by
    intro x y
    change H (x + y) + H0 (x + y) = (H x + H0 x) + (H y + H0 y)
    rw [hH x y, hH0 x y]
    ring_nf
  refine ⟨g, fun x => H x + H0 x, r, hg, hsum, ?_, hr⟩
  intro x
  have hx := hdecomp x
  linarith

/-- Hyers stability for an approximately additive real function.  This is the
additive-correction step in Laczkovich's unbounded reduction. -/
lemma hyers_ulam (D : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hD : ∀ x y : ℝ, |D (x + y) - D x - D y| ≤ M) :
    ∃ H : ℝ → ℝ, IsAdditiveFn H ∧ ∀ x : ℝ, |D x - H x| ≤ M := by
  have h_cauchy_seq : ∀ x, CauchySeq (fun n => D (2 ^ n * x) / 2 ^ n) := by
    intro x
    have h_cauchy_seq_step :
        ∀ n, abs (D (2 ^ (n + 1) * x) / 2 ^ (n + 1) -
          D (2 ^ n * x) / 2 ^ n) ≤ M / 2 ^ (n + 1) := by
      intro n
      specialize hD (2 ^ n * x) (2 ^ n * x)
      ring_nf at *
      norm_num at *
      exact abs_le.mpr
        ⟨by
          nlinarith [abs_le.mp hD,
            pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n],
         by
          nlinarith [abs_le.mp hD,
            pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]⟩
    fapply cauchySeq_of_le_geometric
    exacts
      [1 / 2, M / 2, by norm_num, fun n => by
        rw [dist_comm]
        exact le_trans (h_cauchy_seq_step n) (by
          ring_nf
          norm_num)]
  choose H hH using fun x => cauchySeq_tendsto_of_complete (h_cauchy_seq x)
  refine ⟨H, ?_, ?_⟩
  · intros x y
    have h_lim :
        Filter.Tendsto
          (fun n =>
            (D (2 ^ n * (x + y)) - D (2 ^ n * x) - D (2 ^ n * y)) / 2 ^ n)
          Filter.atTop (nhds 0) := by
      have h1 :
          ∀ᶠ n in Filter.atTop,
            ‖(D (2 ^ n * (x + y)) - D (2 ^ n * x) - D (2 ^ n * y)) /
              2 ^ n‖ ≤ M / 2 ^ n :=
        Filter.Eventually.of_forall fun n => by
          simpa [abs_div, mul_add] using
            div_le_div_of_nonneg_right (hD (2 ^ n * x) (2 ^ n * y))
              (by positivity : (0 : ℝ) ≤ 2 ^ n)
      exact squeeze_zero_norm' h1
        (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))
    exact
      tendsto_nhds_unique (hH (x + y))
        (by
          simpa [sub_div] using
            h_lim.add (hH x |> Filter.Tendsto.add <| hH y))
  · intro x
    have h_abs : ∀ n, |D x - D (2 ^ n * x) / 2 ^ n| ≤ M * (1 - 1 / 2 ^ n) := by
      intro n
      have h_abs_step : ∀ k : ℕ, |D (2 ^ k * x) - 2 ^ k * D x| ≤ M * (2 ^ k - 1) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          simp_all +decide [pow_succ', mul_assoc]
          ring_nf at *
          have := hD (x * 2 ^ k) (x * 2 ^ k)
          ring_nf at *
          exact abs_le.mpr
            ⟨by linarith [abs_le.mp ih, abs_le.mp this],
             by linarith [abs_le.mp ih, abs_le.mp this]⟩
      rw [abs_le]
      constructor <;>
        nlinarith [abs_le.mp (h_abs_step n), show (0 : ℝ) < 2 ^ n by positivity,
          div_mul_cancel₀ (D (2 ^ n * x)) (show (2 ^ n : ℝ) ≠ 0 by positivity),
          one_div_mul_cancel (show (2 ^ n : ℝ) ≠ 0 by positivity),
          pow_pos (zero_lt_two' ℝ) n]
    exact
      le_of_tendsto'
        (Filter.Tendsto.abs (tendsto_const_nhds.sub (hH x))) fun n =>
        le_trans (h_abs n)
          (mul_le_of_le_one_right hM (sub_le_self _ (by positivity)))

/-- Uniform essential control of each difference around a scalar mean value. -/
def HasUniformMeanDifferences (f D : ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ t : ℝ, ∀ᵐ x ∂volume, |differenceKernel f x t - D t| ≤ K

/-- The scalar mean values selected in the localization step are
approximately additive. -/
lemma approximate_additive_of_uniform_mean {f D : ℝ → ℝ} {K : ℝ}
    (hmean : HasUniformMeanDifferences f D K) :
    ∀ u v : ℝ, |D (u + v) - D u - D v| ≤ 3 * K := by
  intro u v
  have huv := hmean (u + v)
  have hu := ae_translate (hmean u) v
  have hv := hmean v
  have hgood :
      ∀ᵐ x : ℝ ∂volume, |D (u + v) - D u - D v| ≤ 3 * K := by
    filter_upwards [huv, hu, hv] with x hxuv hxu hxv
    have hc := differenceKernel_cocycle f x v u
    have hsum : differenceKernel f x (u + v) =
        differenceKernel f (x + v) u + differenceKernel f x v := by
      convert hc using 1
      ring_nf
    rw [hsum] at hxuv
    rw [abs_le]
    constructor <;>
      nlinarith [abs_le.mp hxuv, abs_le.mp hxu, abs_le.mp hxv]
  rcases hgood.exists with ⟨_x, hx⟩
  exact hx

/-- Hyers turns uniformly controlled mean values into an additive correction
after which every difference is uniformly essentially bounded. -/
lemma uniformly_bounded_after_hyers {f D : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K)
    (hmean : HasUniformMeanDifferences f D K) :
    ∃ H : ℝ → ℝ, IsAdditiveFn H ∧
      ∀ t : ℝ, ∀ᵐ x ∂volume,
        |differenceKernel (fun y => f y - H y) x t| ≤ 4 * K := by
  have happ := approximate_additive_of_uniform_mean hmean
  rcases hyers_ulam D (3 * K) (by positivity) happ with ⟨H, hH, hDH⟩
  refine ⟨H, hH, ?_⟩
  intro t
  filter_upwards [hmean t] with x hx
  have hDt := hDH t
  have hadd := hH x t
  dsimp [differenceKernel] at hx ⊢
  rw [hadd]
  rw [abs_le]
  constructor <;>
    nlinarith [abs_le.mp hx, abs_le.mp hDt]

/-- The localization output has exactly the two properties needed by the
bounded core: measurable corrected sections and one uniform essential bound. -/
lemma corrected_uniformly_bounded_of_measurable_and_uniform_mean
    {f D : ℝ → ℝ} {K : ℝ}
    (hf : HasMeasurableDifferences f)
    (hK : 0 ≤ K)
    (hmean : HasUniformMeanDifferences f D K) :
    ∃ H : ℝ → ℝ, IsAdditiveFn H ∧
      HasMeasurableDifferences (fun y => f y - H y) ∧
        ∀ t : ℝ, ∀ᵐ x ∂volume,
          |differenceKernel (fun y => f y - H y) x t| ≤ 4 * K := by
  rcases uniformly_bounded_after_hyers hK hmean with ⟨H, hH, hbound⟩
  exact ⟨H, hH, hf.sub_additive hH, hbound⟩

/-! ## The bounded periodic core

For a periodic function with one uniform essential bound on all differences,
an irrational rotation turns the problem into a bounded integer cocycle.  Its
supremum over the integer orbit is a measurable transfer function.  The
remaining differences are invariant under the irrational rotation; ergodicity
of that rotation makes them almost everywhere constant. -/

/-- The rotation by `√2` has infinite order on the unit additive circle. -/
lemma sqrt_two_addOrderOf_unitAddCircle :
    addOrderOf ((Real.sqrt 2 : ℝ) : UnitAddCircle) = 0 := by
  rw [← AddCircle.denseRange_zsmul_iff]
  rw [AddCircle.denseRange_zsmul_coe_iff]
  simpa using irrational_sqrt_two

/-- A periodic lift agrees with the interval representative used by the
measure-preserving quotient map. -/
lemma periodic_lift_eq_liftIoc {u : ℝ → ℝ} (hu : Function.Periodic u 1) :
    hu.lift = AddCircle.liftIoc 1 0 u := by
  funext y
  obtain ⟨x, hx, rfl⟩ := AddCircle.eq_coe_Ioc (p := (1 : ℝ)) y
  rw [hu.lift_coe, AddCircle.liftIoc_coe_apply (by simpa using hx)]

/-- A completed-Lebesgue measurable periodic function descends to an almost
everywhere measurable function on the unit circle. -/
lemma aemeasurable_periodic_lift {u : ℝ → ℝ}
    (hu : Function.Periodic u 1) (hum : AEMeasurable u volume) :
    AEMeasurable hu.lift (volume : Measure UnitAddCircle) := by
  rw [periodic_lift_eq_liftIoc hu]
  have hsub : AEMeasurable (fun x : Ioc (0 : ℝ) (0 + 1) => u x)
      (Measure.comap Subtype.val volume) :=
    (aemeasurable_restrict_iff_comap_subtype measurableSet_Ioc).1 hum.restrict
  have hcomp := hsub.comp_quasiMeasurePreserving
    (AddCircle.measurePreserving_equivIoc 1).quasiMeasurePreserving
  simpa only [AddCircle.liftIoc, Set.domRestrict_def, Function.comp_def] using hcomp

/-- A measurable one-periodic function invariant almost everywhere under the
irrational rotation by `√2` is almost everywhere constant. -/
lemma periodic_invariant_ae_const {u : ℝ → ℝ}
    (hu : Function.Periodic u 1) (hum : AEMeasurable u volume)
    (hinv : ∀ᵐ x ∂volume, u (x + Real.sqrt 2) = u x) :
    ∃ c : ℝ, ∀ᵐ x ∂volume, u x = c := by
  let U : UnitAddCircle → ℝ := hu.lift
  have hUmeas : AEMeasurable U (volume : Measure UnitAddCircle) :=
    aemeasurable_periodic_lift hu hum
  have hUinv : U ∘ (· + ((Real.sqrt 2 : ℝ) : UnitAddCircle))
      =ᵐ[(volume : Measure UnitAddCircle)] U := by
    have hsub : ∀ᵐ x : Ioc (0 : ℝ) (0 + 1) ∂(Measure.comap Subtype.val volume),
        u ((x : ℝ) + Real.sqrt 2) = u x := by
      exact (ae_restrict_iff_subtype measurableSet_Ioc).1 (ae_restrict_of_ae hinv)
    have hcircle := (AddCircle.measurePreserving_equivIoc 1).quasiMeasurePreserving.ae hsub
    filter_upwards [hcircle] with y hy
    let x : Ioc (0 : ℝ) (0 + 1) := AddCircle.equivIoc 1 0 y
    have hxy : (x : UnitAddCircle) = y := AddCircle.coe_equivIoc
    dsimp [U]
    rw [← hxy, ← AddCircle.coe_add, hu.lift_coe]
    exact hy
  have herg : Ergodic (· + ((Real.sqrt 2 : ℝ) : UnitAddCircle)) :=
    (AddCircle.ergodic_add_right).2 sqrt_two_addOrderOf_unitAddCircle
  rcases herg.ae_eq_const_of_ae_eq_comp_ae hUmeas.aestronglyMeasurable hUinv with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  have hmp := UnitAddCircle.measurePreserving_mk 0
  have hpre :
      ∀ᵐ x : ℝ ∂((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)), u x = c := by
    have hpull := hmp.quasiMeasurePreserving.ae hc
    have hpull' : ∀ᵐ x : ℝ ∂((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)),
        U (x : UnitAddCircle) = c := by simpa using hpull
    filter_upwards [hpull', ae_restrict_mem measurableSet_Ioc] with x hx hmem
    simpa [U] using hx
  rw [← Measure.restrict_univ (μ := volume)]
  have hcover : (⋃ n : ℤ, Ioc (n : ℝ) (n + 1 : ℝ)) = (univ : Set ℝ) := by
    ext x
    simp only [mem_iUnion, mem_Ioc, mem_univ, iff_true]
    refine ⟨⌈x⌉ - 1, ?_⟩
    constructor
    · rw [Int.cast_sub, Int.cast_one, sub_lt_iff_lt_add]
      exact Int.ceil_lt_add_one x
    · simpa [Int.cast_sub, Int.cast_one] using Int.le_ceil x
  rw [← hcover, ae_restrict_iUnion_iff]
  intro n
  have hpre_full :
      ∀ᵐ x ∂volume, x ∈ Ioc (0 : ℝ) 1 → u x = c :=
    (ae_restrict_iff' measurableSet_Ioc).1 hpre
  have htrans := ae_translate hpre_full (-(n : ℝ))
  filter_upwards [ae_restrict_of_ae htrans,
    ae_restrict_mem measurableSet_Ioc] with x hx hmem
  have hxmem : x - (n : ℝ) ∈ Ioc (0 : ℝ) 1 := by
    constructor <;> linarith [hmem.1, hmem.2]
  have hx' : u (x + -(n : ℝ)) = c := hx (by simpa [sub_eq_add_neg] using hxmem)
  have hper := hu.zsmul n (x - (n : ℝ))
  have hper' : u x = u (x - (n : ℝ)) := by
    ring_nf at hper
    exact hper
  rw [hper']
  convert hx' using 1 <;> ring

/-- Rational points remain dense after quotienting the real line by the
integer lattice. -/
lemma denseRange_rat_unitAddCircle :
    DenseRange (fun q : ℚ => ((q : ℝ) : UnitAddCircle)) := by
  have hmk : DenseRange (fun x : ℝ => (x : UnitAddCircle)) :=
    QuotientAddGroup.mk_surjective.denseRange
  have hcomp :=
    hmk.comp Rat.denseRange_cast (AddCircle.continuous_mk' (1 : ℝ))
  exact hcomp

/-- A rational translation invariance on the real periodic lift descends to
the same a.e. invariance on the additive circle. -/
lemma periodic_lift_invariant_rat
    {u : ℝ → ℝ} (hu : Function.Periodic u 1)
    (hinv : ∀ q : ℚ, ∀ᵐ x ∂volume, u (x + q) = u x) (q : ℚ) :
    hu.lift ∘ (· + ((q : ℝ) : UnitAddCircle))
      =ᵐ[(volume : Measure UnitAddCircle)] hu.lift := by
  have hsub : ∀ᵐ x : Ioc (0 : ℝ) (0 + 1) ∂(Measure.comap Subtype.val volume),
      u ((x : ℝ) + q) = u x := by
    exact (ae_restrict_iff_subtype measurableSet_Ioc).1
      (ae_restrict_of_ae (hinv q))
  have hcircle := (AddCircle.measurePreserving_equivIoc 1).quasiMeasurePreserving.ae hsub
  filter_upwards [hcircle] with y hy
  let x : Ioc (0 : ℝ) (0 + 1) := AddCircle.equivIoc 1 0 y
  have hxy : (x : UnitAddCircle) = y := AddCircle.coe_equivIoc
  dsimp
  rw [← hxy, ← AddCircle.coe_add, hu.lift_coe]
  exact hy

/-- Every rational sublevel set of a periodic measurable function invariant
under rational shifts is null or conull on the additive circle. -/
lemma periodic_lift_level_const_of_rat_invariant
    {u : ℝ → ℝ} (hu : Function.Periodic u 1)
    (hum : AEMeasurable u volume)
    (hinv : ∀ q : ℚ, ∀ᵐ x ∂volume, u (x + q) = u x)
    (c : ℚ) :
    Filter.EventuallyConst
      {y : UnitAddCircle | hu.lift y < (c : ℝ)}
      (ae (volume : Measure UnitAddCircle)) := by
  let U : UnitAddCircle → ℝ := hu.lift
  let S : Set UnitAddCircle := {y | U y < (c : ℝ)}
  have hUmeas : AEMeasurable U (volume : Measure UnitAddCircle) :=
    aemeasurable_periodic_lift hu hum
  have hS : NullMeasurableSet S (volume : Measure UnitAddCircle) :=
    nullMeasurableSet_lt hUmeas aemeasurable_const
  apply aeconst_of_dense_setOfPred_preimage_vadd_ae
    (M := UnitAddCircle) (X := UnitAddCircle) hS
  apply Dense.mono _ denseRange_rat_unitAddCircle
  rintro _ ⟨q, rfl⟩
  have hUq := periodic_lift_invariant_rat hu hinv q
  filter_upwards [hUq] with y hy
  change (((q : ℝ) : UnitAddCircle) + y ∈ S) = (y ∈ S)
  dsimp [S, U]
  simpa [Function.comp_def, add_comm] using
    congrArg (fun z : ℝ => z < (c : ℝ)) hy

/-- Rational invariance forces invariance under the fixed irrational
rotation.  The proof tests all rational sublevel sets, uses their null/conull
status, and then separates unequal real values by a rational. -/
lemma periodic_lift_invariant_sqrt_two_of_rat_invariant
    {u : ℝ → ℝ} (hu : Function.Periodic u 1)
    (hum : AEMeasurable u volume)
    (hinv : ∀ q : ℚ, ∀ᵐ x ∂volume, u (x + q) = u x) :
    hu.lift ∘ (· + ((Real.sqrt 2 : ℝ) : UnitAddCircle))
      =ᵐ[(volume : Measure UnitAddCircle)] hu.lift := by
  have hall :
      ∀ᵐ y ∂(volume : Measure UnitAddCircle), ∀ c : ℚ,
        (hu.lift (y + ((Real.sqrt 2 : ℝ) : UnitAddCircle)) < (c : ℝ)) ↔
          (hu.lift y < (c : ℝ)) := by
    rw [ae_all_iff]
    intro c
    let S : Set UnitAddCircle := {y | hu.lift y < (c : ℝ)}
    have hconst := periodic_lift_level_const_of_rat_invariant hu hum hinv c
    let a : UnitAddCircle := ((Real.sqrt 2 : ℝ) : UnitAddCircle)
    have hqmp :
        Measure.QuasiMeasurePreserving (fun y : UnitAddCircle => a + y)
          (volume : Measure UnitAddCircle) volume :=
      quasiMeasurePreserving_add_left (G := UnitAddCircle) volume a
    rcases Filter.eventuallyConst_set.mp hconst with hmem | hnot
    · have hshift := hqmp.ae hmem
      filter_upwards [hshift, hmem] with y hy hs
      simpa [S, a, add_comm] using Iff.intro (fun _ => hs) (fun _ => hy)
    · have hshift := hqmp.ae hnot
      filter_upwards [hshift, hnot] with y hy hs
      simpa [S, a, add_comm] using
        Iff.intro (fun h => (hy h).elim) (fun h => (hs h).elim)
  filter_upwards [hall] with y hy
  dsimp
  apply le_antisymm
  · by_contra hnot
    have hlt : hu.lift y < hu.lift (y + ((Real.sqrt 2 : ℝ) : UnitAddCircle)) :=
      lt_of_not_ge hnot
    rcases exists_rat_btwn hlt with ⟨q, hq1, hq2⟩
    have hiff := hy q
    have : hu.lift (y + ((Real.sqrt 2 : ℝ) : UnitAddCircle)) < (q : ℝ) :=
      hiff.mpr hq1
    linarith
  · by_contra hnot
    have hlt : hu.lift (y + ((Real.sqrt 2 : ℝ) : UnitAddCircle)) < hu.lift y :=
      lt_of_not_ge hnot
    rcases exists_rat_btwn hlt with ⟨q, hq1, hq2⟩
    have hiff := hy q
    have : hu.lift y < (q : ℝ) := hiff.mp hq1
    linarith

/-- A measurable one-periodic function invariant a.e. under every rational
shift is a.e. constant. -/
lemma periodic_invariant_ae_const_of_rat_invariant
    {u : ℝ → ℝ} (hu : Function.Periodic u 1)
    (hum : AEMeasurable u volume)
    (hinv : ∀ q : ℚ, ∀ᵐ x ∂volume, u (x + q) = u x) :
    ∃ c : ℝ, ∀ᵐ x ∂volume, u x = c := by
  have hUalpha :=
    periodic_lift_invariant_sqrt_two_of_rat_invariant hu hum hinv
  have hmp := UnitAddCircle.measurePreserving_mk 0
  have hpre :
      ∀ᵐ x : ℝ ∂((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)),
        hu.lift ((x : UnitAddCircle) + ((Real.sqrt 2 : ℝ) : UnitAddCircle)) =
          hu.lift (x : UnitAddCircle) := by
    simpa [Function.comp_def] using hmp.quasiMeasurePreserving.ae hUalpha
  have hzeroIoc :
      ∀ᵐ x : ℝ ∂((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)),
        u (x + Real.sqrt 2) - u x = 0 := by
    filter_upwards [hpre, ae_restrict_mem measurableSet_Ioc] with x hx hxm
    rw [← AddCircle.coe_add, hu.lift_coe, hu.lift_coe] at hx
    linarith
  have hper :
      Function.Periodic (fun x : ℝ => u (x + Real.sqrt 2) - u x) 1 := by
    intro x
    dsimp
    rw [show x + 1 + Real.sqrt 2 = (x + Real.sqrt 2) + 1 by ring, hu, hu]
  have hzero :
      ∀ᵐ x : ℝ ∂volume, u (x + Real.sqrt 2) - u x = 0 :=
    periodic_ae_zero_of_Ioc hper hzeroIoc
  apply periodic_invariant_ae_const hu hum
  filter_upwards [hzero] with x hx
  linarith

/-- Every difference section of a one-periodic function is one-periodic in
its base point. -/
lemma differenceKernel_periodic_base {p : ℝ → ℝ}
    (hp : Function.Periodic p 1) (t : ℝ) :
    Function.Periodic (fun x => differenceKernel p x t) 1 := by
  intro x
  unfold differenceKernel
  dsimp
  rw [show x + 1 + t = (x + t) + 1 by ring, hp, hp]

/-- The countable quotient energy separates sections modulo constants:
for a periodic function, zero energy means that the difference section is
a.e. constant. -/
lemma laczkovichEnergy_eq_zero_section_ae_const
    {p : ℝ → ℝ} (hpper : Function.Periodic p 1)
    (hp : HasMeasurableDifferences p) (t : ℝ)
    (hzero : laczkovichEnergy p t = 0) :
    ∃ c : ℝ, ∀ᵐ x ∂volume, differenceKernel p x t = c := by
  let u : ℝ → ℝ := fun x => differenceKernel p x t
  have huper : Function.Periodic u 1 := differenceKernel_periodic_base hpper t
  have humeas : AEMeasurable u volume := hp t
  have huinv : ∀ q : ℚ, ∀ᵐ x ∂volume, u (x + q) = u x := by
    intro q
    rcases exists_rationalShiftAt q with ⟨n, hn⟩
    have hcoord :
        secondDifferenceEnergy p (rationalShiftAt n) t = 0 :=
      secondDifferenceEnergy_eq_zero_of_laczkovichEnergy_eq_zero n hzero
    have hsecond :=
      secondDifferenceEnergy_eq_zero_ae_full hpper hp (rationalShiftAt n) t hcoord
    rw [hn] at hsecond
    filter_upwards [hsecond] with x hx
    dsimp [u]
    unfold secondDifferenceKernel at hx
    linarith
  exact periodic_invariant_ae_const_of_rat_invariant huper humeas huinv

/-- Strict-majority subsets of a finite index set. -/
def strictMajoritySubsets (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun s => n / 2 < s.card

/-- Maximum of a finite family, with a harmless default for the empty
family. -/
noncomputable def finiteSup {n : ℕ} (s : Finset (Fin n)) (u : Fin n → ℝ) : ℝ :=
  if hs : s.Nonempty then s.sup' hs u else 0

/-- A lower finite median, written as the minimum of maxima over all
strict-majority subsets.  This finite min/max presentation makes
measurability transparent. -/
noncomputable def finiteLowerMedian {n : ℕ} (u : Fin n → ℝ) : ℝ :=
  if hn : 0 < n then
    let A := strictMajoritySubsets n
    A.inf'
      (by
        refine ⟨Finset.univ, ?_⟩
        change Finset.univ ∈ strictMajoritySubsets n
        simp [strictMajoritySubsets]
        omega)
      (fun s => finiteSup s u)
  else 0

lemma measurable_finset_inf'
    {δ ι : Type*} [MeasurableSpace δ] [DecidableEq ι]
    {s : Finset ι} (hs : s.Nonempty) {u : ι → δ → ℝ}
    (hu : ∀ i ∈ s, Measurable (u i)) :
    Measurable (fun x => s.inf' hs (fun i => u i x)) := by
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
      by_cases hsn : s.Nonempty
      · have heq :
            (fun x => (insert a s).inf' hs (fun i => u i x)) =
              (fun x => u a x ⊓ s.inf' hsn (fun i => u i x)) := by
            funext x
            exact Finset.inf'_insert hsn (fun i => u i x)
        rw [heq]
        exact (hu a (by simp)).inf
          (ih hsn (fun i hi => hu i (by simp [hi])))
      · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsn
        subst s
        simpa using hu a (by simp)

lemma finiteSup_measurable
    {δ : Type*} [MeasurableSpace δ] {n : ℕ}
    (s : Finset (Fin n)) {u : Fin n → δ → ℝ}
    (hu : ∀ i, Measurable (u i)) :
    Measurable (fun x => finiteSup s (fun i => u i x)) := by
  unfold finiteSup
  split_ifs with hs
  · have hm : Measurable (s.sup' hs u) :=
      Finset.measurable_sup' hs (fun i _ => hu i)
    convert hm using 1
    funext x
    exact (Finset.sup'_apply hs u x).symm
  · exact measurable_const

lemma finiteLowerMedian_measurable
    {δ : Type*} [MeasurableSpace δ] {n : ℕ}
    {u : Fin n → δ → ℝ} (hu : ∀ i, Measurable (u i)) :
    Measurable (fun x => finiteLowerMedian (fun i => u i x)) := by
  unfold finiteLowerMedian
  split_ifs with hn
  · let A := strictMajoritySubsets n
    have hA : A.Nonempty := by
      refine ⟨Finset.univ, ?_⟩
      change Finset.univ ∈ strictMajoritySubsets n
      simp [strictMajoritySubsets]
      omega
    exact measurable_finset_inf' hA
      (fun s _ => finiteSup_measurable s hu)
  · exact measurable_const

lemma finiteLowerMedian_aemeasurable
    {δ : Type*} [MeasurableSpace δ] {μ : Measure δ} {n : ℕ}
    {u : Fin n → δ → ℝ} (hu : ∀ i, AEMeasurable (u i) μ) :
    AEMeasurable (fun x => finiteLowerMedian (fun i => u i x)) μ := by
  let v : Fin n → δ → ℝ := fun i => (hu i).mk (u i)
  have hv : ∀ i, Measurable (v i) := fun i => (hu i).measurable_mk
  have hmed : Measurable (fun x => finiteLowerMedian (fun i => v i x)) :=
    finiteLowerMedian_measurable hv
  apply hmed.aemeasurable.congr
  have hall : ∀ᵐ x ∂μ, ∀ i : Fin n, u i x = v i x := by
    rw [ae_all_iff]
    intro i
    exact (hu i).ae_eq_mk
  filter_upwards [hall] with x hx
  congr 2
  funext i
  exact (hx i).symm

/-- The dyadic shifts on the unit circle. -/
noncomputable def dyadicShift (n : ℕ) (i : Fin (2 ^ n)) : ℝ :=
  (i : ℝ) / (2 : ℝ) ^ n

/-- Normalize a difference section by subtracting the lower median of its
finite dyadic orbit.  Only second differences appear, so every finite-stage
representative is jointly a.e. measurable. -/
noncomputable def dyadicMedianRepresentative
    (f : ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  -finiteLowerMedian
    (fun i : Fin (2 ^ n) =>
      secondDifferenceKernel f (dyadicShift n i) p.1 p.2)

lemma dyadicMedianRepresentative_aemeasurable
    {f : ℝ → ℝ} (hf : HasMeasurableDifferences f) (n : ℕ) :
    AEMeasurable (dyadicMedianRepresentative f n) (volume.prod volume) := by
  unfold dyadicMedianRepresentative
  apply AEMeasurable.neg
  apply finiteLowerMedian_aemeasurable
  intro i
  exact secondDifferenceKernel_measurable hf (dyadicShift n i)

lemma finiteSup_add_const_of_nonempty {n : ℕ} {s : Finset (Fin n)}
    (hs : s.Nonempty) (u : Fin n → ℝ) (c : ℝ) :
    finiteSup s (fun i => c + u i) = c + finiteSup s u := by
  simp only [finiteSup, dif_pos hs]
  apply le_antisymm
  · apply Finset.sup'_le hs
    intro i hi
    have hle := Finset.le_sup' u hi
    linarith
  · have hle : s.sup' hs u ≤ s.sup' hs (fun i => c + u i) - c := by
      apply Finset.sup'_le hs
      intro i hi
      have hi' := Finset.le_sup' (fun i => c + u i) hi
      linarith
    linarith

lemma finset_inf_add_const {ι : Type*} [DecidableEq ι]
    {s : Finset ι} (hs : s.Nonempty) (u : ι → ℝ) (c : ℝ) :
    s.inf' hs (fun i => c + u i) = c + s.inf' hs u := by
  apply le_antisymm
  · have hle : s.inf' hs (fun i => c + u i) - c ≤ s.inf' hs u := by
      apply Finset.le_inf' hs
      intro i hi
      have hi' := Finset.inf'_le (fun i => c + u i) hi
      linarith
    linarith
  · apply Finset.le_inf' hs
    intro i hi
    have hle := Finset.inf'_le u hi
    linarith

lemma finiteLowerMedian_add_const {n : ℕ} (hn : 0 < n)
    (u : Fin n → ℝ) (c : ℝ) :
    finiteLowerMedian (fun i => c + u i) = c + finiteLowerMedian u := by
  unfold finiteLowerMedian
  simp only [dif_pos hn]
  let A := strictMajoritySubsets n
  have hA : A.Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    change Finset.univ ∈ strictMajoritySubsets n
    simp [strictMajoritySubsets]
    omega
  have hpoint : ∀ s ∈ A,
      finiteSup s (fun i => c + u i) = c + finiteSup s u := by
    intro s hsA
    have hsCard : n / 2 < s.card := by
      simpa [A, strictMajoritySubsets] using hsA
    have hs : s.Nonempty :=
      Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hsCard)
    exact finiteSup_add_const_of_nonempty hs u c
  have hrewrite :
      A.inf' hA (fun s => finiteSup s (fun i => c + u i)) =
        A.inf' hA (fun s => c + finiteSup s u) := by
    apply Finset.inf'_congr hA rfl
    intro s hs
    exact hpoint s hs
  rw [hrewrite]
  exact finset_inf_add_const hA (fun s => finiteSup s u) c

lemma finiteLowerMedian_le_iff_majority {n : ℕ} (hn : 0 < n)
    (u : Fin n → ℝ) (a : ℝ) :
    finiteLowerMedian u ≤ a ↔
      n / 2 < (Finset.univ.filter fun i => u i ≤ a).card := by
  let A := strictMajoritySubsets n
  have hA : A.Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    change Finset.univ ∈ strictMajoritySubsets n
    simp [strictMajoritySubsets]
    omega
  unfold finiteLowerMedian
  simp only [dif_pos hn]
  change A.inf' _ (fun s => finiteSup s u) ≤ a ↔
    n / 2 < (Finset.univ.filter fun i => u i ≤ a).card
  constructor
  · intro hle
    have hmem :
        A.inf' hA (fun s => finiteSup s u) ∈
          (fun s => finiteSup s u) '' (A : Set (Finset (Fin n))) := by
      apply Finset.inf'_mem
      · intro x hx y hy
        rcases hx with ⟨sx, hsx, rfl⟩
        rcases hy with ⟨sy, hsy, rfl⟩
        by_cases hxy : finiteSup sx u ≤ finiteSup sy u
        · exact ⟨sx, hsx, (min_eq_left hxy).symm⟩
        · exact ⟨sy, hsy, (min_eq_right (le_of_not_ge hxy)).symm⟩
      · intro s hs
        exact ⟨s, hs, rfl⟩
    rcases hmem with ⟨s, hsA, hsmed⟩
    have hsCard : n / 2 < s.card := by
      simpa [A, strictMajoritySubsets] using hsA
    have hs : s.Nonempty :=
      Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hsCard)
    have hsup : finiteSup s u ≤ a := by
      rw [← hsmed] at hle
      exact hle
    have hsubset : s ⊆ Finset.univ.filter fun i => u i ≤ a := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hiSup : u i ≤ finiteSup s u := by
        simp [finiteSup, hs, Finset.le_sup' u hi]
      exact le_trans hiSup hsup
    exact lt_of_lt_of_le hsCard (Finset.card_le_card hsubset)
  · intro hmajor
    let s : Finset (Fin n) := Finset.univ.filter fun i => u i ≤ a
    have hsA : s ∈ A := by
      simpa [s, A, strictMajoritySubsets] using hmajor
    have hs : s.Nonempty :=
      Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hmajor)
    have hsup : finiteSup s u ≤ a := by
      simp only [finiteSup, dif_pos hs]
      apply Finset.sup'_le hs
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    exact le_trans (Finset.inf'_le (fun s => finiteSup s u) hsA) hsup

lemma finiteLowerMedian_comp_equiv {n : ℕ} (hn : 0 < n)
    (u : Fin n → ℝ) (e : Fin n ≃ Fin n) :
    finiteLowerMedian (fun i => u (e i)) = finiteLowerMedian u := by
  have hcard (a : ℝ) :
      (Finset.univ.filter fun i => u (e i) ≤ a).card =
        (Finset.univ.filter fun i => u i ≤ a).card := by
    have hfilter :
        Finset.univ.filter (fun i => u (e i) ≤ a) =
          (Finset.univ.filter fun i => u i ≤ a).map e.symm.toEmbedding := by
      ext i
      simp
    rw [hfilter, Finset.card_map]
  apply le_antisymm
  · rw [finiteLowerMedian_le_iff_majority hn]
    rw [hcard]
    exact (finiteLowerMedian_le_iff_majority hn u (finiteLowerMedian u)).1 le_rfl
  · rw [finiteLowerMedian_le_iff_majority hn]
    have hcard' :
        (Finset.univ.filter fun i => u i ≤ finiteLowerMedian (fun i => u (e i))).card =
          (Finset.univ.filter fun i => u (e i) ≤
            finiteLowerMedian (fun i => u (e i))).card := by
      symm
      exact hcard _
    rw [hcard']
    exact (finiteLowerMedian_le_iff_majority hn
      (fun i => u (e i)) (finiteLowerMedian (fun i => u (e i)))).1 le_rfl

/-- Adding two dyadic shifts differs from the corresponding modular finite
sum by an integer period. -/
lemma periodic_dyadic_shift_add {u : ℝ → ℝ}
    (hu : Function.Periodic u 1) (n : ℕ)
    (i j : Fin (2 ^ n)) (x : ℝ) :
    u (x + dyadicShift n (i + j)) =
      u (x + dyadicShift n i + dyadicShift n j) := by
  let q : ℕ := (i.val + j.val) / (2 ^ n)
  have hper := hu.zsmul (q : ℤ) (x + dyadicShift n (i + j))
  symm
  convert hper using 1
  unfold dyadicShift
  rw [Fin.val_add]
  have hmod := Nat.mod_add_div (i.val + j.val) (2 ^ n)
  norm_num at hper ⊢
  congr 1
  field_simp
  have hmodR :
      (((i.val + j.val) % (2 ^ n) : ℕ) : ℝ) +
          ((2 ^ n : ℕ) : ℝ) * (((i.val + j.val) / (2 ^ n) : ℕ) : ℝ) =
        ((i.val + j.val : ℕ) : ℝ) := by
    exact_mod_cast hmod
  norm_num at hmodR
  dsimp [q]
  nlinarith

/-- Finite-stage dyadic median normalization recovers every dyadic
difference already present in its orbit. -/
lemma dyadicMedianRepresentative_shift {p : ℝ → ℝ}
    (hp : Function.Periodic p 1) (n : ℕ)
    (j : Fin (2 ^ n)) (x t : ℝ) :
    dyadicMedianRepresentative p n (x + dyadicShift n j, t) =
      dyadicMedianRepresentative p n (x, t) +
        secondDifferenceKernel p (dyadicShift n j) x t := by
  let u : ℝ → ℝ := fun y => differenceKernel p y t
  have huper : Function.Periodic u 1 := differenceKernel_periodic_base hp t
  letI : NeZero (2 ^ n) := ⟨by positivity⟩
  let e : Fin (2 ^ n) ≃ Fin (2 ^ n) := Equiv.addRight j
  have hpoint : ∀ i : Fin (2 ^ n),
      secondDifferenceKernel p (dyadicShift n i)
          (x + dyadicShift n j) t =
        -secondDifferenceKernel p (dyadicShift n j) x t +
          secondDifferenceKernel p (dyadicShift n (e i)) x t := by
    intro i
    have hshift := periodic_dyadic_shift_add huper n i j x
    dsimp [u] at hshift
    unfold secondDifferenceKernel at *
    dsimp [e]
    have hcomm :
        differenceKernel p (x + dyadicShift n j + dyadicShift n i) t =
          differenceKernel p (x + dyadicShift n i + dyadicShift n j) t := by
      unfold differenceKernel
      congr 1 <;> ring
    rw [hcomm, hshift]
    ring
  unfold dyadicMedianRepresentative
  have hmed :
      finiteLowerMedian
          (fun i : Fin (2 ^ n) =>
            secondDifferenceKernel p (dyadicShift n i)
              (x + dyadicShift n j) t) =
        -secondDifferenceKernel p (dyadicShift n j) x t +
          finiteLowerMedian
            (fun i : Fin (2 ^ n) =>
              secondDifferenceKernel p (dyadicShift n i) x t) := by
    calc
      _ = finiteLowerMedian
          (fun i : Fin (2 ^ n) =>
            -secondDifferenceKernel p (dyadicShift n j) x t +
              secondDifferenceKernel p (dyadicShift n (e i)) x t) := by
            congr 2
            funext i
            exact hpoint i
      _ = -secondDifferenceKernel p (dyadicShift n j) x t +
          finiteLowerMedian
            (fun i : Fin (2 ^ n) =>
              secondDifferenceKernel p (dyadicShift n (e i)) x t) := by
            exact finiteLowerMedian_add_const (by positivity)
              (fun i : Fin (2 ^ n) =>
                secondDifferenceKernel p (dyadicShift n (e i)) x t)
              (-secondDifferenceKernel p (dyadicShift n j) x t)
      _ = _ := by
            rw [finiteLowerMedian_comp_equiv (by positivity)
              (fun i : Fin (2 ^ n) =>
                secondDifferenceKernel p (dyadicShift n i) x t) e]
  rw [hmed]
  ring

/-- View a level-n dyadic index inside a refined level n+k grid. -/
def dyadicRefineIndex (n k : ℕ) (j : Fin (2 ^ n)) : Fin (2 ^ (n + k)) :=
  ⟨j.val * 2 ^ k, by
    have hj := j.isLt
    rw [pow_add]
    nlinarith [show 0 < 2 ^ k by positivity]⟩

lemma dyadicShift_refine (n k : ℕ) (j : Fin (2 ^ n)) :
    dyadicShift (n + k) (dyadicRefineIndex n k j) = dyadicShift n j := by
  unfold dyadicShift dyadicRefineIndex
  dsimp
  rw [pow_add]
  norm_num
  field_simp

/-- Every later refinement retains the exact base-shift identity from each
earlier dyadic level. -/
lemma dyadicMedianRepresentative_refined_shift {p : ℝ → ℝ}
    (hp : Function.Periodic p 1) (n k : ℕ)
    (j : Fin (2 ^ n)) (x t : ℝ) :
    dyadicMedianRepresentative p (n + k) (x + dyadicShift n j, t) =
      dyadicMedianRepresentative p (n + k) (x, t) +
        secondDifferenceKernel p (dyadicShift n j) x t := by
  let j' := dyadicRefineIndex n k j
  have h := dyadicMedianRepresentative_shift hp (n + k) j' x t
  simpa [j', dyadicShift_refine] using h

/-- If the finite dyadic representatives converge almost everywhere, their
limit can be chosen jointly measurable. -/
lemma exists_measurable_dyadicMedian_limit
    {p : ℝ → ℝ}
    (hp : HasMeasurableDifferences p)
    (hlim : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ∃ l : ℝ, Tendsto
        (fun n => dyadicMedianRepresentative p n z) atTop (nhds l)) :
    ∃ G : ℝ × ℝ → ℝ, Measurable G ∧
      ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
        Tendsto (fun n => dyadicMedianRepresentative p n z) atTop (nhds (G z)) := by
  exact measurable_limit_of_tendsto_metrizable_ae
    (fun n => dyadicMedianRepresentative_aemeasurable hp n) hlim

/-- Every exact dyadic shift identity survives in an almost-everywhere
jointly measurable limit of the finite selectors. -/
lemma dyadicMedian_limit_refined_shift
    {p : ℝ → ℝ} {G : ℝ × ℝ → ℝ}
    (hpper : Function.Periodic p 1)
    (hlim : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      Tendsto (fun n => dyadicMedianRepresentative p n z) atTop (nhds (G z)))
    (n : ℕ) (j : Fin (2 ^ n)) :
    ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      G (z.1 + dyadicShift n j, z.2) =
        G z + secondDifferenceKernel p (dyadicShift n j) z.1 z.2 := by
  let T : ℝ × ℝ → ℝ × ℝ :=
    fun z => (z.1 + dyadicShift n j, z.2)
  have hmp :
      MeasurePreserving T (volume.prod volume) (volume.prod volume) := by
    have hprod :=
      (measurePreserving_add_right volume (dyadicShift n j)).prod
        (MeasurePreserving.id (volume : Measure ℝ))
    convert hprod using 1
    rfl
  have hshift := hmp.quasiMeasurePreserving.ae hlim
  filter_upwards [hlim, hshift] with z hz hzshift
  have htail :
      Tendsto
        (fun k => dyadicMedianRepresentative p (n + k) z)
        atTop (nhds (G z)) :=
    by
      simpa [Nat.add_comm] using (tendsto_add_atTop_iff_nat n).2 hz
  have htailShift :
      Tendsto
        (fun k => dyadicMedianRepresentative p (n + k) (T z))
        atTop (nhds (G (T z))) :=
    by
      simpa [Nat.add_comm] using (tendsto_add_atTop_iff_nat n).2 hzshift
  have heq :
      (fun k => dyadicMedianRepresentative p (n + k) (T z)) =
        (fun k => dyadicMedianRepresentative p (n + k) z +
          secondDifferenceKernel p (dyadicShift n j) z.1 z.2) := by
    funext k
    exact dyadicMedianRepresentative_refined_shift hpper n k j z.1 z.2
  rw [heq] at htailShift
  have hconst :
      Tendsto (fun _ : ℕ =>
        secondDifferenceKernel p (dyadicShift n j) z.1 z.2)
        atTop (nhds (secondDifferenceKernel p (dyadicShift n j) z.1 z.2)) :=
    tendsto_const_nhds
  have hright := htail.add hconst
  simpa [T] using tendsto_nhds_unique htailShift hright

/-- For one fixed section, the second-difference definition is exactly the
section value minus the median of its finite dyadic orbit. -/
lemma dyadicMedianRepresentative_eq_sub_orbit_median
    (p : ℝ → ℝ) (n : ℕ) (x t : ℝ) :
    dyadicMedianRepresentative p n (x, t) =
      differenceKernel p x t -
        finiteLowerMedian
          (fun i : Fin (2 ^ n) =>
            differenceKernel p (x + dyadicShift n i) t) := by
  unfold dyadicMedianRepresentative secondDifferenceKernel
  have hmed := finiteLowerMedian_add_const (by positivity)
    (fun i : Fin (2 ^ n) => differenceKernel p (x + dyadicShift n i) t)
    (-differenceKernel p x t)
  rw [show (fun i : Fin (2 ^ n) =>
      differenceKernel p (x + dyadicShift n i) t -
        differenceKernel p x t) =
      (fun i => -differenceKernel p x t +
        differenceKernel p (x + dyadicShift n i) t) by
    funext i
    ring]
  rw [hmed]
  ring

/-- Integer Birkhoff sums of the fixed irrational difference section. -/
noncomputable def integerDifference (p : ℝ → ℝ) (z : ℤ) (x : ℝ) : ℝ :=
  differenceKernel p x ((z : ℝ) * Real.sqrt 2)

/-- The bounded cocycle transfer obtained as the supremum over all integer
orbit differences. -/
noncomputable def boundedTransfer (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  ⨆ z : ℤ, integerDifference p z x

/-- The transfer is almost everywhere measurable because it is a countable
supremum of measurable difference sections. -/
lemma boundedTransfer_aemeasurable {p : ℝ → ℝ}
    (hp : HasMeasurableDifferences p) :
    AEMeasurable (boundedTransfer p) volume := by
  unfold boundedTransfer
  exact AEMeasurable.iSup fun z => hp ((z : ℝ) * Real.sqrt 2)

/-- Translating an integer-indexed bounded family before taking its supremum
subtracts the same constant from the supremum. -/
lemma ciSup_shift_sub {b : ℤ → ℝ} {K c : ℝ}
    (hb : ∀ z, |b z| ≤ K) :
    (⨆ z : ℤ, b (z + 1) - c) = (⨆ z : ℤ, b z) - c := by
  have hB : BddAbove (Set.range b) := by
    refine ⟨K, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact le_trans (le_abs_self _) (hb z)
  have hL : BddAbove (Set.range fun z : ℤ => b (z + 1) - c) := by
    refine ⟨K + |c|, ?_⟩
    rintro _ ⟨z, rfl⟩
    nlinarith [abs_le.mp (hb (z + 1)), neg_le_abs c]
  apply le_antisymm
  · apply ciSup_le
    intro z
    have hz : b (z + 1) ≤ ⨆ w : ℤ, b w := le_ciSup hB (z + 1)
    linarith
  · have hS : (⨆ z : ℤ, b z) ≤ (⨆ z : ℤ, b (z + 1) - c) + c := by
      apply ciSup_le
      intro z
      have hz : b ((z - 1) + 1) - c ≤ ⨆ w : ℤ, b (w + 1) - c :=
        le_ciSup hL (z - 1)
      norm_num at hz ⊢
      linarith
    linarith

/-- The transfer solves the fixed irrational coboundary equation. -/
lemma boundedTransfer_coboundary {p : ℝ → ℝ} {K : ℝ}
    (hbound : ∀ t : ℝ, ∀ᵐ x ∂volume,
      |differenceKernel p x t| ≤ K) :
    ∀ᵐ x ∂volume,
      boundedTransfer p (x + Real.sqrt 2) - boundedTransfer p x =
        -differenceKernel p x (Real.sqrt 2) := by
  have hall : ∀ᵐ x ∂volume, ∀ z : ℤ, |integerDifference p z x| ≤ K := by
    rw [ae_all_iff]
    intro z
    exact hbound ((z : ℝ) * Real.sqrt 2)
  filter_upwards [hall, ae_translate hall (Real.sqrt 2)] with x hx hxshift
  unfold boundedTransfer
  have hshift : ∀ z : ℤ,
      integerDifference p z (x + Real.sqrt 2) =
        integerDifference p (z + 1) x - integerDifference p 1 x := by
    intro z
    unfold integerDifference differenceKernel
    have harg : x + Real.sqrt 2 + (z : ℝ) * Real.sqrt 2 =
        x + ((z + 1 : ℤ) : ℝ) * Real.sqrt 2 := by
      push_cast
      ring
    rw [harg]
    ring
  simp_rw [hshift]
  rw [ciSup_shift_sub hx]
  change ((⨆ z : ℤ, integerDifference p z x) - integerDifference p 1 x) -
      (⨆ z : ℤ, integerDifference p z x) =
        -differenceKernel p x (Real.sqrt 2)
  have hone : integerDifference p 1 x = differenceKernel p x (Real.sqrt 2) := by
    unfold integerDifference
    norm_num
  rw [hone]
  ring

/-- The transfer inherits the unit period of the original function. -/
lemma boundedTransfer_periodic {p : ℝ → ℝ}
    (hp : Function.Periodic p 1) :
    Function.Periodic (boundedTransfer p) 1 := by
  intro x
  unfold boundedTransfer integerDifference differenceKernel
  congr 1
  funext z
  rw [show x + 1 + (z : ℝ) * Real.sqrt 2 =
      (x + (z : ℝ) * Real.sqrt 2) + 1 by ring]
  rw [hp, hp]

/-- A one-periodic function with measurable, uniformly essentially bounded
differences has the corrected measurable decomposition. -/
lemma measurableDecomposition_of_bounded_periodic {p : ℝ → ℝ} {K : ℝ}
    (hpper : Function.Periodic p 1)
    (hp : HasMeasurableDifferences p)
    (hbound : ∀ t : ℝ, ∀ᵐ x ∂volume,
      |differenceKernel p x t| ≤ K) :
    HasMeasurableDecomposition p := by
  let g : ℝ → ℝ := fun x => -boundedTransfer p x
  let r : ℝ → ℝ := fun x => p x - g x
  have hg : AEMeasurable g volume :=
    (boundedTransfer_aemeasurable hp).neg
  have hgper : Function.Periodic g 1 := by
    intro x
    dsimp [g]
    rw [boundedTransfer_periodic hpper]
  have hrper : Function.Periodic r 1 := by
    intro x
    dsimp [r]
    rw [hpper, hgper]
  have hralpha : ∀ᵐ x ∂volume,
      r (x + Real.sqrt 2) - r x = 0 := by
    filter_upwards [boundedTransfer_coboundary hbound] with x hx
    dsimp [r, g]
    unfold differenceKernel at hx
    linarith
  have hrdiff (t : ℝ) : AEMeasurable (fun x => r (x + t) - r x) volume := by
    have hgshift : AEMeasurable (fun x : ℝ => g (x + t)) volume :=
      hg.comp_quasiMeasurePreserving
        (measurePreserving_add_right volume t).quasiMeasurePreserving
    dsimp [r]
    convert (hp t).sub (hgshift.sub hg) using 1
    funext x
    simp only [Pi.sub_apply]
    ring
  have hrdiffper (t : ℝ) :
      Function.Periodic (fun x => r (x + t) - r x) 1 := by
    intro x
    change r (x + 1 + t) - r (x + 1) = r (x + t) - r x
    rw [show x + 1 + t = (x + t) + 1 by ring, hrper, hrper]
  have hrdiffinv (t : ℝ) :
      ∀ᵐ x ∂volume,
        (r (x + Real.sqrt 2 + t) - r (x + Real.sqrt 2)) =
          r (x + t) - r x := by
    filter_upwards [ae_translate hralpha t, hralpha] with x hxt hx
    have harg : x + t + Real.sqrt 2 = x + Real.sqrt 2 + t := by ring
    rw [← harg]
    linarith
  have hconst : ∀ t : ℝ, ∃ c : ℝ,
      ∀ᵐ x ∂volume, r (x + t) - r x = c := by
    intro t
    exact periodic_invariant_ae_const (hrdiffper t) (hrdiff t) (hrdiffinv t)
  choose H hH using hconst
  have hHadd : IsAdditiveFn H := by
    intro u v
    have huv := hH (u + v)
    have hu := ae_translate (hH u) v
    have hv := hH v
    have hall : ∀ᵐ x : ℝ ∂volume, H (u + v) = H u + H v := by
      filter_upwards [huv, hu, hv] with x hxuv hxu hxv
      have hc := differenceKernel_cocycle r x v u
      unfold differenceKernel at hc
      have harg : x + (v + u) = x + (u + v) := by ring
      rw [harg] at hc
      linarith
    rcases (show ∀ᵐ x : ℝ ∂volume, H (u + v) = H u + H v from hall).exists with
      ⟨_, hx⟩
    exact hx
  let r0 : ℝ → ℝ := fun x => r x - H x
  have hr0 : HasNullIncrements r0 := by
    intro t
    filter_upwards [hH t] with x hx
    dsimp [r0]
    rw [hHadd x t]
    linarith
  refine ⟨g, H, r0, hg, hHadd, ?_, hr0⟩
  intro x
  dsimp [r0, r]
  ring

/-- Adding an additive summand back into a measurable decomposition only
enlarges the additive component. -/
lemma HasMeasurableDecomposition.add_additive {f H : ℝ → ℝ}
    (hf : HasMeasurableDecomposition f) (hH : IsAdditiveFn H) :
    HasMeasurableDecomposition (fun x => f x + H x) := by
  rcases hf with ⟨g, A, r, hg, hA, hdecomp, hr⟩
  have hsum : IsAdditiveFn (fun x => H x + A x) := by
    intro x y
    change H (x + y) + A (x + y) = (H x + A x) + (H y + A y)
    rw [hH x y, hA x y]
    ring
  refine ⟨g, fun x => H x + A x, r, hg, hsum, ?_, hr⟩
  intro x
  change f x + H x = g x + (H x + A x) + r x
  rw [hdecomp x]
  ring

/-- If subtracting an additive function from a periodic function has one
uniform essential bound on all differences, then the additive function
vanishes at the period. -/
lemma additive_one_eq_zero_of_periodic_uniform_bound
    {p H : ℝ → ℝ} {C : ℝ}
    (hpper : Function.Periodic p 1) (hH : IsAdditiveFn H)
    (hbound : ∀ t : ℝ, ∀ᵐ x ∂volume,
      |differenceKernel (fun y => p y - H y) x t| ≤ C) :
    H 1 = 0 := by
  by_contra hne
  have hpos : 0 < |H 1| := abs_pos.mpr hne
  have hHn : ∀ n : ℕ, H (n : ℝ) = (n : ℝ) * H 1 := by
    intro n
    induction n with
    | zero =>
        have h0 := hH 0 0
        simp at h0 ⊢
        linarith
    | succ n ih =>
        have hs := hH (n : ℝ) 1
        rw [Nat.cast_succ]
        rw [hs, ih]
        ring
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (C / |H 1|)
  have hbn := hbound (n : ℝ)
  rcases hbn.exists with ⟨x, hx⟩
  have hp : p (x + (n : ℝ)) = p x := by
    simpa [nsmul_eq_mul] using hpper.nsmul n x
  unfold differenceKernel at hx
  change |(p (x + (n : ℝ)) - H (x + (n : ℝ))) - (p x - H x)| ≤ C at hx
  rw [hp, hH x (n : ℝ), hHn n] at hx
  have hle : (n : ℝ) * |H 1| ≤ C := by
    simpa [abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))] using hx
  have hlt : C < (n : ℝ) * |H 1| := by
    rwa [div_lt_iff₀ hpos] at hn
  linarith

/-- Uniformly centered differences on a periodic function are enough for the
corrected measurable decomposition: Hyers supplies an additive correction,
the preceding lemma preserves periodicity, and the bounded periodic core
finishes the argument. -/
lemma measurableDecomposition_of_uniform_mean_periodic
    {p D : ℝ → ℝ} {K : ℝ}
    (hpper : Function.Periodic p 1)
    (hp : HasMeasurableDifferences p)
    (hK : 0 ≤ K)
    (hmean : HasUniformMeanDifferences p D K) :
    HasMeasurableDecomposition p := by
  rcases corrected_uniformly_bounded_of_measurable_and_uniform_mean hp hK hmean with
    ⟨H, hH, hdiff, hbound⟩
  have hH1 : H 1 = 0 :=
    additive_one_eq_zero_of_periodic_uniform_bound hpper hH hbound
  have hqper : Function.Periodic (fun y => p y - H y) 1 := by
    intro x
    change p (x + 1) - H (x + 1) = p x - H x
    rw [hpper, hH x 1, hH1]
    ring
  have hq := measurableDecomposition_of_bounded_periodic hqper hdiff hbound
  have hadd := hq.add_additive hH
  convert hadd using 1
  funext x
  ring

/-- The exact output required from Laczkovich's unbounded localization:
after moving one nondegenerate window to `[0,1)` and periodizing, all
difference sections have scalar centers with one common essential bound. -/
def HasLocalizedUniformMean (f : ℝ → ℝ) : Prop :=
  ∃ a ρ : ℝ, ∃ D : ℝ → ℝ, ∃ K : ℝ,
    ρ ≠ 0 ∧ 0 ≤ K ∧
      HasUniformMeanDifferences (periodizeOne (affinePull f a ρ)) D K

/-- The verified affine, periodic, Hyers, and bounded-rotation stages reduce
the full theorem to the preceding source-faithful localization output. -/
lemma measurableDecomposition_of_localizedUniformMean {f : ℝ → ℝ}
    (hf : HasMeasurableDifferences f) (hloc : HasLocalizedUniformMean f) :
    HasMeasurableDecomposition f := by
  rcases hloc with ⟨a, ρ, D, K, hρ, hK, hmean⟩
  let p : ℝ → ℝ := periodizeOne (affinePull f a ρ)
  have hpper : Function.Periodic p 1 := periodizeOne_periodic _
  have hfa : HasMeasurableDifferences (affinePull f a ρ) :=
    affinePull_hasMeasurableDifferences hf hρ
  have hp : HasMeasurableDifferences p :=
    periodizeOne_hasMeasurableDifferences hfa
  have hpdec : HasMeasurableDecomposition p :=
    measurableDecomposition_of_uniform_mean_periodic hpper hp hK hmean
  exact measurableDecomposition_of_affine_periodizeOne hf hρ hpdec

/-- The Heaviside function, used as the counterexample. -/
noncomputable def heaviside (x : ℝ) : ℝ :=
  if 0 ≤ x then 1 else 0

lemma measurable_heaviside : Measurable heaviside := by
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

lemma heaviside_hasMeasurablePositiveDifferences :
    HasMeasurablePositiveDifferences heaviside := by
  intro t _ht
  exact
    ((measurable_heaviside.comp (measurable_id.add_const t)).sub measurable_heaviside).aemeasurable

/-- A requested decomposition would make each translate difference of `f`
almost everywhere equal to a continuous function. -/
lemma difference_ae_eq_continuous_of_decomposition {f : ℝ → ℝ}
    (hf : HasDecomposition f) (t : ℝ) :
    ∃ q : ℝ → ℝ, Continuous q ∧
      (fun x : ℝ => f (x + t) - f x) =ᵐ[volume] q := by
  rcases hf with ⟨g, H, r, hg, hH, hdecomp, hr⟩
  let q : ℝ → ℝ := fun x => g (x + t) - g x + H t
  refine ⟨q, ((hg.comp (continuous_id.add_const t)).sub hg).add continuous_const, ?_⟩
  filter_upwards [hr t] with x hx
  dsimp [q]
  rw [hdecomp (x + t), hdecomp x, hH x t]
  linarith

/-- The Heaviside function cannot have the decomposition requested in the
supplied statement. -/
theorem heaviside_no_decomposition : ¬ HasDecomposition heaviside := by
  intro hdecomp
  obtain ⟨q, hq, hae⟩ := difference_ae_eq_continuous_of_decomposition hdecomp 1
  -- On the left interval the step difference is one away from the null endpoint.
  have hstep_left :
      (fun x : ℝ => heaviside (x + 1) - heaviside x) =ᵐ[
        volume.restrict (Icc (-1) 0)] (fun _ : ℝ => 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (Measure.ae_ne volume 0)] with x hxI hx0
    rcases hxI with ⟨hxlo, hxhi⟩
    have hxneg : x < 0 := lt_of_le_of_ne hxhi hx0
    have hxshift : 0 ≤ x + 1 := by linarith
    simp [heaviside, hxshift, not_le.mpr hxneg]
  have hq_left :
      q =ᵐ[volume.restrict (Icc (-1) 0)] (fun _ : ℝ => 1) :=
    by
      have hae_left :
          (fun x : ℝ => heaviside (x + 1) - heaviside x) =ᵐ[
            volume.restrict (Icc (-1) 0)] q := ae_restrict_of_ae hae
      exact Filter.EventuallyEq.trans hae_left.symm hstep_left
  have hq0_one : q 0 = 1 := by
    have hEq := Measure.eqOn_Icc_of_ae_eq volume
      (by norm_num : (-1 : ℝ) ≠ 0) hq_left hq.continuousOn continuous_const.continuousOn
    exact hEq (by norm_num)
  -- On the right interval the step difference is identically zero.
  have hstep_right :
      (fun x : ℝ => heaviside (x + 1) - heaviside x) =ᵐ[
        volume.restrict (Icc 0 1)] (fun _ : ℝ => 0) := by
    refine ae_restrict_of_forall_mem measurableSet_Icc ?_
    intro x hxI
    have hxshift : 0 ≤ x + 1 := by linarith [hxI.1]
    simp [heaviside, hxI.1, hxshift]
  have hq_right :
      q =ᵐ[volume.restrict (Icc 0 1)] (fun _ : ℝ => 0) :=
    by
      have hae_right :
          (fun x : ℝ => heaviside (x + 1) - heaviside x) =ᵐ[
            volume.restrict (Icc 0 1)] q := ae_restrict_of_ae hae
      exact Filter.EventuallyEq.trans hae_right.symm hstep_right
  have hq0_zero : q 0 = 0 := by
    have hEq := Measure.eqOn_Icc_of_ae_eq volume
      (by norm_num : (0 : ℝ) ≠ 1) hq_right hq.continuousOn continuous_const.continuousOn
    exact hEq (by norm_num)
  linarith

/-- An explicit witness that satisfies the hypothesis and violates the
requested conclusion. -/
theorem erdos908_counterexample :
    HasMeasurablePositiveDifferences heaviside ∧ ¬ HasDecomposition heaviside :=
  ⟨heaviside_hasMeasurablePositiveDifferences, heaviside_no_decomposition⟩

/-- **Main result for the supplied continuous wording:** the universal
affirmative statement with a continuous first summand is false. -/
theorem not_erdos_908 : ¬ (∀ f : ℝ → ℝ, Erdos908.HasMeasurablePositiveDifferences f → Erdos908.HasDecomposition f) := by
  intro h
  exact heaviside_no_decomposition (h heaviside heaviside_hasMeasurablePositiveDifferences)

/-- Backwards-compatible short name for the continuous-wording counterexample. -/
theorem erdos908 : ¬ Erdos908Claim :=
  not_erdos_908



open Filter MeasureTheory Set Function
open scoped Pointwise ENNReal

/-- Finite averaging over the dyadic subgroup of the unit circle. -/
noncomputable def circleDyadicAverage (u : UnitAddCircle → ℝ) (n : ℕ)
    (x : UnitAddCircle) : ℝ :=
  (∑ i : Fin (2 ^ n),
    u (x + (((i : ℝ) / (2 ^ n : ℝ) : ℝ) : UnitAddCircle))) / (2 ^ n : ℝ)

lemma circleDyadicAverage_measurable {u : UnitAddCircle → ℝ}
    (hu : Measurable u) (n : ℕ) :
    Measurable (circleDyadicAverage u n) := by
  unfold circleDyadicAverage
  apply Measurable.div_const
  apply Finset.measurable_fun_sum
  intro i hi
  exact hu.comp (measurable_id.add_const _)

lemma circleDyadicAverage_bound {u : UnitAddCircle → ℝ} {C : ℝ}
    (hu : ∀ x, |u x| ≤ C) (n : ℕ) (x : UnitAddCircle) :
    |circleDyadicAverage u n x| ≤ C := by
  unfold circleDyadicAverage
  rw [abs_div]
  have hsum :
      |∑ i : Fin (2 ^ n),
          u (x + (((i : ℝ) / (2 ^ n : ℝ) : ℝ) : UnitAddCircle))| ≤
        ∑ _i : Fin (2 ^ n), C := by
    calc
      |∑ i : Fin (2 ^ n),
          u (x + (((i : ℝ) / (2 ^ n : ℝ) : ℝ) : UnitAddCircle))| ≤
          ∑ i : Fin (2 ^ n),
            |u (x + (((i : ℝ) / (2 ^ n : ℝ) : ℝ) : UnitAddCircle))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (2 ^ n), C := by
        gcongr with i
        exact hu _
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hsum ⊢
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  rw [abs_of_pos hpow]
  rw [div_le_iff₀ hpow]
  simpa [mul_comm] using hsum



example (F : (Unit → ℝ) → ℝ) (hF : Continuous F) :
    Tendsto
      (fun n : ℕ ↦
        (∑' x : ↑(((Homeomorph.funUnique Unit ℝ) ⁻¹' Ico 0 1) ∩
          (n : ℝ)⁻¹ • (Submodule.span ℤ (Set.range (Pi.basisFun ℝ Unit)))),
          F x) / n ^ Fintype.card Unit)
      atTop (nhds (∫ x in ((Homeomorph.funUnique Unit ℝ) ⁻¹' Ico 0 1), F x)) := by
  apply tendsto_tsum_div_pow_atTop_integral
    ((Homeomorph.funUnique Unit ℝ) ⁻¹' Ico 0 1) F hF
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, ?_⟩
    intro x hx
    change x default ∈ Ico (0 : ℝ) 1 at hx
    rw [Metric.mem_closedBall, dist_zero_right]
    simpa [Pi.norm_def, abs_of_nonneg hx.1] using (le_of_lt hx.2)
  · exact measurableSet_Ico.preimage (Homeomorph.funUnique Unit ℝ).measurable
  · rw [← (Homeomorph.funUnique Unit ℝ).preimage_frontier]
    change volume ((MeasurableEquiv.funUnique Unit ℝ) ⁻¹' frontier (Ico 0 1)) = 0
    rw [(volume_preserving_funUnique Unit ℝ).measure_preimage]
    · rw [frontier_Ico (by norm_num : (0 : ℝ) < 1)]
      have hzero : volume ({0, 1} : Set ℝ) = 0 := by
        rw [show ({0, 1} : Set ℝ) = ({0} : Set ℝ) ∪ {1} by
          ext y
          simp [or_comm]]
        exact measure_union_null (by simp) (by simp)
      exact hzero
    · simp [frontier_Ico (by norm_num : (0 : ℝ) < 1)]

example (n : ℕ) (hn : 0 < n) (i : Fin n) :
    (fun _ : Unit => (i : ℝ) / (n : ℝ)) ∈
      ((n : ℝ)⁻¹ •
        (Submodule.span ℤ (Set.range (Pi.basisFun ℝ Unit)) : Set (Unit → ℝ))) := by
  have hz :
      (fun _ : Unit => (i : ℝ)) ∈
        (Submodule.span ℤ (Set.range (Pi.basisFun ℝ Unit)) : Set (Unit → ℝ)) := by
    change (fun _ : Unit => (i : ℝ)) ∈
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ Unit))
    rw [(Pi.basisFun ℝ Unit).mem_span_iff_repr_mem ℤ]
    intro j
    refine ⟨(i : ℤ), ?_⟩
    simp
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (by positivity : (n : ℝ)⁻¹ ≠ 0)]
  convert hz using 1
  funext j
  simp
  field_simp

noncomputable def unitGridSet (n : ℕ) : Set (Unit → ℝ) :=
  ((Homeomorph.funUnique Unit ℝ) ⁻¹' Ico 0 1) ∩
    ((n : ℝ)⁻¹ •
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ Unit)) : Set (Unit → ℝ)))

noncomputable def unitGridMap (n : ℕ) (i : Fin n) :
    Unit → ℝ := fun _ => (i : ℝ) / (n : ℝ)

lemma unitGridMap_mem (n : ℕ) (hn : 0 < n) (i : Fin n) :
    unitGridMap n i ∈ unitGridSet n := by
  constructor
  · change (i : ℝ) / (n : ℝ) ∈ Ico (0 : ℝ) 1
    constructor
    · positivity
    · rw [div_lt_one (by positivity)]
      exact_mod_cast i.isLt
  · exact (show
      (fun _ : Unit => (i : ℝ) / (n : ℝ)) ∈
        ((n : ℝ)⁻¹ •
          (Submodule.span ℤ (Set.range (Pi.basisFun ℝ Unit)) :
            Set (Unit → ℝ))) from by
      have hz :
          (fun _ : Unit => (i : ℝ)) ∈
            (Submodule.span ℤ (Set.range (Pi.basisFun ℝ Unit)) :
              Set (Unit → ℝ)) := by
        change (fun _ : Unit => (i : ℝ)) ∈
          Submodule.span ℤ (Set.range (Pi.basisFun ℝ Unit))
        rw [(Pi.basisFun ℝ Unit).mem_span_iff_repr_mem ℤ]
        intro j
        refine ⟨(i : ℤ), ?_⟩
        simp
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ (by positivity : (n : ℝ)⁻¹ ≠ 0)]
      convert hz using 1
      funext j
      simp
      field_simp)

lemma unitGridMap_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (unitGridMap n) := by
  intro i j hij
  apply Fin.ext
  have hval := congrFun hij default
  dsimp [unitGridMap] at hval
  field_simp at hval
  exact_mod_cast hval

lemma unitGridMap_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (fun i : Fin n =>
      (⟨unitGridMap n i, unitGridMap_mem n hn i⟩ : unitGridSet n)) := by
  intro x
  have hxI : x.1 default ∈ Ico (0 : ℝ) 1 := x.2.1
  have hxL : x.1 ∈
      ((n : ℝ)⁻¹ •
        (Submodule.span ℤ (Set.range (Pi.basisFun ℝ Unit)) :
          Set (Unit → ℝ))) := x.2.2
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (by positivity : (n : ℝ)⁻¹ ≠ 0)] at hxL
  have hxL' :
      (fun j : Unit => (n : ℝ) * x.1 j) ∈
        Submodule.span ℤ (Set.range (Pi.basisFun ℝ Unit)) := by
    change ((n : ℝ)⁻¹)⁻¹ • x.1 ∈
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ Unit)) at hxL
    convert hxL using 1
    funext j
    simp
  rw [(Pi.basisFun ℝ Unit).mem_span_iff_repr_mem ℤ] at hxL'
  rcases hxL' default with ⟨z, hz⟩
  have hz' : (z : ℝ) = (n : ℝ) * x.1 default := by
    simpa using hz
  have hznonneg : 0 ≤ z := by
    exact_mod_cast (by nlinarith [hxI.1] : (0 : ℝ) ≤ (z : ℝ))
  have hzlt : z < n := by
    exact_mod_cast (by nlinarith [hxI.2, show (0 : ℝ) < n by positivity] :
      (z : ℝ) < (n : ℝ))
  let i : Fin n := ⟨z.toNat, by
    have : z.toNat < n := (Int.toNat_lt_of_ne_zero hn.ne').2 hzlt
    exact this⟩
  refine ⟨i, Subtype.ext ?_⟩
  funext j
  dsimp [unitGridMap, i]
  have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hznonneg
  have hzr : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast hzcast
  rw [hzr, hz']
  field_simp

noncomputable def unitGridEquiv (n : ℕ) (hn : 0 < n) :
    Fin n ≃ unitGridSet n :=
  Equiv.ofBijective
    (fun i : Fin n => (⟨unitGridMap n i, unitGridMap_mem n hn i⟩ : unitGridSet n))
    ⟨fun _ _ h => unitGridMap_injective n hn (Subtype.ext_iff.mp h),
      unitGridMap_surjective n hn⟩

lemma tsum_unitGrid_eq_sum (F : (Unit → ℝ) → ℝ) (n : ℕ) (hn : 0 < n) :
    (∑' x : unitGridSet n, F x) =
      ∑ i : Fin n, F (unitGridMap n i) := by
  calc
    (∑' x : unitGridSet n, F x) =
        ∑' i : Fin n, F ((unitGridEquiv n hn i : unitGridSet n) : Unit → ℝ) := by
          exact ((unitGridEquiv n hn).tsum_eq
            (fun x : unitGridSet n => F x)).symm
    _ = ∑ i : Fin n, F (unitGridMap n i) := by
          rw [tsum_fintype]
          rfl

lemma tendsto_unitGrid_sum_continuous (F : (Unit → ℝ) → ℝ)
    (hF : Continuous F) :
    Tendsto
      (fun n : ℕ => (∑ i : Fin n, F (unitGridMap n i)) / (n : ℝ))
      atTop
      (nhds (∫ x in ((Homeomorph.funUnique Unit ℝ) ⁻¹' Ico 0 1), F x)) := by
  have hR :
      Tendsto
        (fun n : ℕ ↦
          (∑' x : unitGridSet n, F x) / n ^ Fintype.card Unit)
        atTop
        (nhds (∫ x in ((Homeomorph.funUnique Unit ℝ) ⁻¹' Ico 0 1), F x)) := by
    apply tendsto_tsum_div_pow_atTop_integral
      ((Homeomorph.funUnique Unit ℝ) ⁻¹' Ico 0 1) F hF
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨1, ?_⟩
      intro x hx
      change x default ∈ Ico (0 : ℝ) 1 at hx
      rw [Metric.mem_closedBall, dist_zero_right]
      simpa [Pi.norm_def, abs_of_nonneg hx.1] using (le_of_lt hx.2)
    · exact measurableSet_Ico.preimage (Homeomorph.funUnique Unit ℝ).measurable
    · rw [← (Homeomorph.funUnique Unit ℝ).preimage_frontier]
      change volume ((MeasurableEquiv.funUnique Unit ℝ) ⁻¹' frontier (Ico 0 1)) = 0
      rw [(volume_preserving_funUnique Unit ℝ).measure_preimage]
      · rw [frontier_Ico (by norm_num : (0 : ℝ) < 1)]
        have hzero : volume ({0, 1} : Set ℝ) = 0 := by
          rw [show ({0, 1} : Set ℝ) = ({0} : Set ℝ) ∪ {1} by
            ext y
            simp [or_comm]]
          exact measure_union_null (by simp) (by simp)
        exact hzero
      · simp [frontier_Ico (by norm_num : (0 : ℝ) < 1)]
  apply hR.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < n := hn
  rw [tsum_unitGrid_eq_sum F n hnpos]
  simp

lemma tendsto_dyadic_unitGrid_sum_continuous (F : (Unit → ℝ) → ℝ)
    (hF : Continuous F) :
    Tendsto
      (fun n : ℕ =>
        (∑ i : Fin (2 ^ n), F (unitGridMap (2 ^ n) i)) / (2 ^ n : ℝ))
      atTop
      (nhds (∫ x in ((Homeomorph.funUnique Unit ℝ) ⁻¹' Ico 0 1), F x)) := by
  have h := (tendsto_unitGrid_sum_continuous F hF).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ)))
  simpa [Function.comp_def] using h

lemma circleDyadicAverage_tendsto_integral_of_continuous
    {u : UnitAddCircle → ℝ} (hu : Continuous u) (x : UnitAddCircle) :
    Tendsto (fun n => circleDyadicAverage u n x) atTop
      (nhds (∫ y : UnitAddCircle, u y)) := by
  let F : (Unit → ℝ) → ℝ :=
    fun y => u (x + ((y default : ℝ) : UnitAddCircle))
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have hlim := tendsto_dyadic_unitGrid_sum_continuous F hF
  have hmean :
      (∫ y in ((Homeomorph.funUnique Unit ℝ) ⁻¹' Ico 0 1), F y) =
        ∫ y : UnitAddCircle, u y := by
    calc
      (∫ y in ((Homeomorph.funUnique Unit ℝ) ⁻¹' Ico 0 1), F y) =
          ∫ y in Ico (0 : ℝ) 1, u (x + (y : UnitAddCircle)) := by
            simpa [F] using
              (volume_preserving_funUnique Unit ℝ).setIntegral_preimage_emb
                (MeasurableEquiv.funUnique Unit ℝ).measurableEmbedding
                (fun y : ℝ => u (x + (y : UnitAddCircle))) (Ico 0 1)
      _ = ∫ y in Ioc (0 : ℝ) 1, u (x + (y : UnitAddCircle)) := by
            exact integral_Ico_eq_integral_Ioc
      _ = ∫ y : UnitAddCircle, u (x + y) := by
            simpa using
              (UnitAddCircle.integral_preimage 0
                (fun y : UnitAddCircle => u (x + y)))
      _ = ∫ y : UnitAddCircle, u y := by
            exact (measurePreserving_add_left volume x).integral_comp
              (MeasurableEquiv.addLeft x).measurableEmbedding u
  rw [hmean] at hlim
  convert hlim using 1
  funext n
  simp [circleDyadicAverage, F, unitGridMap]

lemma tendsto_integral_abs_circleDyadicAverage_sub_of_continuous
    {u : UnitAddCircle → ℝ} (hu : Continuous u) :
    Tendsto
      (fun n => ∫ x : UnitAddCircle,
        |circleDyadicAverage u n x - ∫ y : UnitAddCircle, u y|)
      atTop (nhds 0) := by
  let U : C(UnitAddCircle, ℝ) := ⟨u, hu⟩
  let C : ℝ := ‖U‖
  have huC : ∀ x : UnitAddCircle, |u x| ≤ C := by
    intro x
    exact U.norm_coe_le_norm x
  have hmeanC : |∫ y : UnitAddCircle, u y| ≤ C := by
    have h :=
      norm_integral_le_of_norm_le_const
        (μ := (volume : Measure UnitAddCircle))
        (f := u) (C := C) (Filter.Eventually.of_forall huC)
    simpa [C, measureReal_def, UnitAddCircle.measure_univ] using h
  have hmeas :
      ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable
        (fun x : UnitAddCircle =>
          |circleDyadicAverage u n x - ∫ y : UnitAddCircle, u y|) volume := by
    filter_upwards [] with n
    have hm : Measurable (fun x : UnitAddCircle =>
        ‖circleDyadicAverage u n x - ∫ y : UnitAddCircle, u y‖) :=
      ((circleDyadicAverage_measurable hu.measurable n).sub measurable_const).norm
    simpa only [Real.norm_eq_abs] using hm.aestronglyMeasurable
  have hbound :
      ∀ᶠ n : ℕ in atTop, ∀ᵐ x : UnitAddCircle ∂volume,
        ‖|circleDyadicAverage u n x - ∫ y : UnitAddCircle, u y|‖ ≤
          (fun _ : UnitAddCircle => 2 * C) x := by
    filter_upwards [] with n
    filter_upwards [] with x
    simp only [Real.norm_eq_abs, abs_abs]
    calc
      |circleDyadicAverage u n x - ∫ y : UnitAddCircle, u y| =
          |circleDyadicAverage u n x + -(∫ y : UnitAddCircle, u y)| := by
            rw [sub_eq_add_neg]
      _ ≤
          |circleDyadicAverage u n x| + |∫ y : UnitAddCircle, u y| :=
        by simpa using
          (abs_add_le (circleDyadicAverage u n x) (-(∫ y : UnitAddCircle, u y)))
      _ ≤ C + C := add_le_add (circleDyadicAverage_bound huC n x) hmeanC
      _ = 2 * C := by ring
  have hboundInt : Integrable (fun _ : UnitAddCircle => 2 * C) volume :=
    integrable_const _
  have hpoint :
      ∀ᵐ x : UnitAddCircle ∂volume,
        Tendsto
          (fun n => |circleDyadicAverage u n x - ∫ y : UnitAddCircle, u y|)
          atTop (nhds (0 : ℝ)) := by
    filter_upwards [] with x
    have hx := circleDyadicAverage_tendsto_integral_of_continuous hu x
    have hc : Tendsto (fun _ : ℕ => ∫ y : UnitAddCircle, u y) atTop
        (nhds (∫ y : UnitAddCircle, u y)) := tendsto_const_nhds
    simpa using (hx.sub hc).abs
  simpa using tendsto_integral_filter_of_dominated_convergence
    (fun _ : UnitAddCircle => 2 * C) hmeas hbound hboundInt hpoint

lemma integral_abs_circleDyadicAverage_le {u : UnitAddCircle → ℝ}
    (hu : Integrable u volume) (n : ℕ) :
    (∫ x : UnitAddCircle, |circleDyadicAverage u n x|) ≤
      ∫ x : UnitAddCircle, |u x| := by
  let N : ℝ := (2 ^ n : ℕ)
  have hN : 0 < N := by dsimp [N]; positivity
  let a : Fin (2 ^ n) → UnitAddCircle :=
    fun i => (((i : ℝ) / (2 ^ n : ℝ) : ℝ) : UnitAddCircle)
  have hshift_int (i : Fin (2 ^ n)) :
      Integrable (fun x : UnitAddCircle => u (x + a i)) volume := by
    exact (measurePreserving_add_right volume (a i)).integrable_comp_of_integrable hu
  have hsum_int :
      Integrable (fun x : UnitAddCircle =>
        ∑ i : Fin (2 ^ n), |u (x + a i)|) volume := by
    apply integrable_finset_sum
    intro i hi
    exact (hshift_int i).norm
  have havg_int :
      Integrable (fun x : UnitAddCircle => |circleDyadicAverage u n x|) volume := by
    have hraw : Integrable (circleDyadicAverage u n) volume := by
      unfold circleDyadicAverage
      apply Integrable.div_const
      apply integrable_finset_sum
      intro i hi
      exact hshift_int i
    exact hraw.norm
  have hpoint :
      ∀ x : UnitAddCircle,
        |circleDyadicAverage u n x| ≤
          (∑ i : Fin (2 ^ n), |u (x + a i)|) / N := by
    intro x
    unfold circleDyadicAverage
    dsimp [a, N]
    rw [abs_div]
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n)]
    push_cast
    change
      |∑ i : Fin (2 ^ n),
          u (x + (((i : ℝ) / (2 ^ n : ℝ) : ℝ) : UnitAddCircle))| /
          (2 ^ n : ℝ) ≤
        (∑ i : Fin (2 ^ n),
          |u (x + (((i : ℝ) / (2 ^ n : ℝ) : ℝ) : UnitAddCircle))|) /
          (2 ^ n : ℝ)
    apply div_le_div_of_nonneg_right
      (Finset.abs_sum_le_sum_abs _ _)
      (by positivity)
  calc
    (∫ x : UnitAddCircle, |circleDyadicAverage u n x|) ≤
        ∫ x : UnitAddCircle,
          (∑ i : Fin (2 ^ n), |u (x + a i)|) / N := by
      apply integral_mono_ae havg_int (hsum_int.div_const _)
      exact Filter.Eventually.of_forall hpoint
    _ = (∑ i : Fin (2 ^ n),
          ∫ x : UnitAddCircle, |u (x + a i)|) / N := by
      rw [integral_div, integral_finset_sum]
      intro i hi
      exact (hshift_int i).norm
    _ = (∑ _i : Fin (2 ^ n),
          ∫ x : UnitAddCircle, |u x|) / N := by
      congr 2
      funext i
      exact (measurePreserving_add_right volume (a i)).integral_comp
        (MeasurableEquiv.addRight (a i)).measurableEmbedding (fun x => |u x|)
    _ = ∫ x : UnitAddCircle, |u x| := by
      dsimp [N]
      simp

lemma circleDyadicAverage_sub (u v : UnitAddCircle → ℝ) (n : ℕ) (x : UnitAddCircle) :
    circleDyadicAverage (fun y => u y - v y) n x =
      circleDyadicAverage u n x - circleDyadicAverage v n x := by
  simp only [circleDyadicAverage]
  rw [Finset.sum_sub_distrib, sub_div]

lemma circleDyadicAverage_integrable {u : UnitAddCircle → ℝ}
    (hu : Integrable u volume) (n : ℕ) :
    Integrable (circleDyadicAverage u n) volume := by
  unfold circleDyadicAverage
  apply Integrable.div_const
  apply integrable_finset_sum
  intro i hi
  exact (measurePreserving_add_right volume
      (((i : ℝ) / (2 ^ n : ℝ) : ℝ) : UnitAddCircle)).integrable_comp_of_integrable hu

lemma tendsto_integral_abs_circleDyadicAverage_sub_integral
    {u : UnitAddCircle → ℝ} (hu : Integrable u volume) :
    Tendsto
      (fun n => ∫ x : UnitAddCircle,
        |circleDyadicAverage u n x - ∫ y : UnitAddCircle, u y|)
      atTop (nhds 0) := by
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  obtain ⟨g, hug, hg⟩ :=
    hu.exists_boundedContinuous_integral_sub_le (show 0 < ε / 4 by positivity)
  have hgconv :=
    tendsto_integral_abs_circleDyadicAverage_sub_of_continuous g.continuous
  have hgevent :
      ∀ᶠ n : ℕ in atTop,
        ∫ x : UnitAddCircle,
          |circleDyadicAverage g n x - ∫ y : UnitAddCircle, g y| < ε / 4 := by
    rcases (Metric.tendsto_atTop.mp hgconv) (ε / 4) (by positivity) with ⟨N, hN⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnonneg : 0 ≤ ∫ x : UnitAddCircle,
        |circleDyadicAverage g n x - ∫ y : UnitAddCircle, g y| :=
      integral_nonneg fun _ => abs_nonneg _
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hN n hn
  rcases eventually_atTop.1 hgevent with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hgn := hN n hn
  have hui : Integrable (circleDyadicAverage u n) volume :=
    circleDyadicAverage_integrable hu n
  have hgi : Integrable (circleDyadicAverage g n) volume :=
    circleDyadicAverage_integrable hg n
  have hdiffi : Integrable (circleDyadicAverage (fun y => u y - g y) n) volume :=
    circleDyadicAverage_integrable (hu.sub hg) n
  have htargeti : Integrable
      (fun x : UnitAddCircle =>
        |circleDyadicAverage u n x - ∫ y : UnitAddCircle, u y|) volume :=
    (hui.sub (integrable_const _)).norm
  have hmiddlei : Integrable
      (fun x : UnitAddCircle =>
        |circleDyadicAverage g n x - ∫ y : UnitAddCircle, g y|) volume :=
    (hgi.sub (integrable_const _)).norm
  have hrighti : Integrable
      (fun _ : UnitAddCircle =>
        |(∫ y : UnitAddCircle, g y) - ∫ y : UnitAddCircle, u y|) volume :=
    integrable_const _
  have hpoint :
      ∀ x : UnitAddCircle,
        |circleDyadicAverage u n x - ∫ y : UnitAddCircle, u y| ≤
          |circleDyadicAverage (fun y => u y - g y) n x| +
            |circleDyadicAverage g n x - ∫ y : UnitAddCircle, g y| +
              |(∫ y : UnitAddCircle, g y) - ∫ y : UnitAddCircle, u y| := by
    intro x
    rw [circleDyadicAverage_sub]
    have heq :
        circleDyadicAverage u n x - ∫ y : UnitAddCircle, u y =
          (circleDyadicAverage u n x - circleDyadicAverage g n x) +
            (circleDyadicAverage g n x - ∫ y : UnitAddCircle, g y) +
              ((∫ y : UnitAddCircle, g y) - ∫ y : UnitAddCircle, u y) := by
      ring
    rw [heq]
    linarith [abs_add_le
      (circleDyadicAverage u n x - circleDyadicAverage g n x)
      (circleDyadicAverage g n x - ∫ y : UnitAddCircle, g y),
      abs_add_le
        (circleDyadicAverage u n x - circleDyadicAverage g n x +
          (circleDyadicAverage g n x - ∫ y : UnitAddCircle, g y))
        ((∫ y : UnitAddCircle, g y) - ∫ y : UnitAddCircle, u y)]
  have hmean :
      |(∫ y : UnitAddCircle, g y) - ∫ y : UnitAddCircle, u y| ≤
        ∫ y : UnitAddCircle, |u y - g y| := by
    rw [← integral_sub hg hu]
    have h := abs_integral_le_integral_abs (μ := (volume : Measure UnitAddCircle))
      (f := fun y : UnitAddCircle => g y - u y)
    simpa [abs_sub_comm] using h
  have hfirst :
      (∫ x : UnitAddCircle,
        |circleDyadicAverage (fun y => u y - g y) n x|) ≤
        ∫ y : UnitAddCircle, |u y - g y| :=
    integral_abs_circleDyadicAverage_le (hu.sub hg) n
  have htotal :
      (∫ x : UnitAddCircle,
        |circleDyadicAverage u n x - ∫ y : UnitAddCircle, u y|) ≤
        (∫ x : UnitAddCircle,
          |circleDyadicAverage (fun y => u y - g y) n x|) +
          (∫ x : UnitAddCircle,
            |circleDyadicAverage g n x - ∫ y : UnitAddCircle, g y|) +
            |(∫ y : UnitAddCircle, g y) - ∫ y : UnitAddCircle, u y| := by
    calc
      (∫ x : UnitAddCircle,
        |circleDyadicAverage u n x - ∫ y : UnitAddCircle, u y|) ≤
          ∫ x : UnitAddCircle,
            (|circleDyadicAverage (fun y => u y - g y) n x| +
              |circleDyadicAverage g n x - ∫ y : UnitAddCircle, g y| +
                |(∫ y : UnitAddCircle, g y) - ∫ y : UnitAddCircle, u y|) := by
        apply integral_mono_ae htargeti ((hdiffi.norm.add hmiddlei).add hrighti)
        exact Filter.Eventually.of_forall hpoint
      _ = _ := by
        rw [integral_add, integral_add]
        · simp [measureReal_def, UnitAddCircle.measure_univ]
        · exact hdiffi.norm
        · exact hmiddlei
        · exact hdiffi.norm.add hmiddlei
        · exact hrighti
  have hbound :
      (∫ x : UnitAddCircle,
        |circleDyadicAverage u n x - ∫ y : UnitAddCircle, u y|) <
        ε / 4 + ε / 4 + ε / 4 := by
    calc
      _ ≤ (∫ x : UnitAddCircle,
          |circleDyadicAverage (fun y => u y - g y) n x|) +
          (∫ x : UnitAddCircle,
            |circleDyadicAverage g n x - ∫ y : UnitAddCircle, g y|) +
            |(∫ y : UnitAddCircle, g y) - ∫ y : UnitAddCircle, u y| := htotal
      _ ≤ (∫ y : UnitAddCircle, |u y - g y|) +
          (∫ x : UnitAddCircle,
            |circleDyadicAverage g n x - ∫ y : UnitAddCircle, g y|) +
            |(∫ y : UnitAddCircle, g y) - ∫ y : UnitAddCircle, u y| := by
              gcongr
      _ ≤ ε / 4 +
          (∫ x : UnitAddCircle,
            |circleDyadicAverage g n x - ∫ y : UnitAddCircle, g y|) +
            ε / 4 := by
              have hug' : ∫ y : UnitAddCircle, |u y - g y| ≤ ε / 4 := by
                simpa [Real.norm_eq_abs] using hug
              exact add_le_add (add_le_add hug' le_rfl) (hmean.trans hug')
      _ < ε / 4 + ε / 4 + ε / 4 := by linarith
  have hnonneg : 0 ≤ ∫ x : UnitAddCircle,
      |circleDyadicAverage u n x - ∫ y : UnitAddCircle, u y| :=
    integral_nonneg fun _ => abs_nonneg _
  simpa [Real.dist_eq, abs_of_nonneg hnonneg] using
    (show (∫ x : UnitAddCircle,
      |circleDyadicAverage u n x - ∫ y : UnitAddCircle, u y|) < ε by
      linarith)

lemma tendstoInMeasure_circleDyadicAverage_sub_integral
    {u : UnitAddCircle → ℝ} (hu : Integrable u volume) :
    TendstoInMeasure volume
      (fun n x => circleDyadicAverage u n x) atTop
      (fun _ : UnitAddCircle => ∫ y : UnitAddCircle, u y) := by
  have hreal := tendsto_integral_abs_circleDyadicAverage_sub_integral hu
  have hLp :
      Tendsto
        (fun n => eLpNorm
          (fun x : UnitAddCircle =>
            circleDyadicAverage u n x - ∫ y : UnitAddCircle, u y)
          1 volume)
        atTop (nhds 0) := by
    have hof := ENNReal.tendsto_ofReal hreal
    simp only [ENNReal.ofReal_zero] at hof
    convert hof using 1
    funext n
    rw [eLpNorm_one_eq_lintegral_enorm]
    have hd : Integrable
        (fun x : UnitAddCircle =>
          circleDyadicAverage u n x - ∫ y : UnitAddCircle, u y) volume :=
      (circleDyadicAverage_integrable hu n).sub (integrable_const _)
    rw [← ofReal_integral_norm_eq_lintegral_enorm hd]
    congr 2
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := (1 : ℝ≥0∞)) (by simp)
  · intro n
    exact (circleDyadicAverage_integrable hu n).aestronglyMeasurable
  · exact aestronglyMeasurable_const
  · convert hLp using 1
    funext n
    congr 1



open Filter MeasureTheory Set Function
open scoped Pointwise ENNReal

/-- The finite arctangent score whose unique zero is a robust center. -/
noncomputable def finiteSoftScore {n : ℕ} (u : Fin n → ℝ) (c : ℝ) : ℝ :=
  ∑ i : Fin n, Real.arctan (u i - c)

lemma finiteSoftScore_continuous {n : ℕ} (u : Fin n → ℝ) :
    Continuous (finiteSoftScore u) := by
  unfold finiteSoftScore
  fun_prop

lemma finiteSoftScore_strictAnti {n : ℕ} (hn : 0 < n) (u : Fin n → ℝ) :
    StrictAnti (finiteSoftScore u) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  intro a b hab
  unfold finiteSoftScore
  apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
  intro i hi
  apply Real.arctan_strictMono
  linarith

lemma exists_unique_finiteSoftScore_eq_zero {n : ℕ} (hn : 0 < n)
    (u : Fin n → ℝ) :
    ∃! c : ℝ, finiteSoftScore u c = 0 := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let M : ℝ := finiteSup Finset.univ (fun i : Fin n => |u i|) + 1
  have hM (i : Fin n) : |u i| < M := by
    have hi : |u i| ≤ finiteSup Finset.univ (fun i : Fin n => |u i|) := by
      simp [finiteSup, Finset.le_sup' (fun i : Fin n => |u i|) (Finset.mem_univ i)]
    dsimp [M]
    linarith
  have hpos : 0 < finiteSoftScore u (-M) := by
    unfold finiteSoftScore
    apply Finset.sum_pos
    · intro i hi
      rw [Real.arctan_pos]
      have hi := hM i
      linarith [neg_abs_le (u i)]
    · exact Finset.univ_nonempty
  have hneg : finiteSoftScore u M < 0 := by
    unfold finiteSoftScore
    apply Finset.sum_neg
    · intro i hi
      rw [Real.arctan_lt_zero]
      have hi := hM i
      linarith [le_abs_self (u i)]
    · exact Finset.univ_nonempty
  have hMnonneg : 0 ≤ M := by
    let i0 : Fin n := Classical.choice (show Nonempty (Fin n) from inferInstance)
    have hi := hM i0
    linarith [abs_nonneg (u i0)]
  have hzeroMem :
      (0 : ℝ) ∈ Icc (finiteSoftScore u M) (finiteSoftScore u (-M)) :=
    ⟨hneg.le, hpos.le⟩
  rcases (intermediate_value_Icc' (a := -M) (b := M) (by linarith)
      (finiteSoftScore_continuous u).continuousOn) hzeroMem with ⟨c, hcI, hc⟩
  refine ⟨c, hc, ?_⟩
  intro d hd
  exact (finiteSoftScore_strictAnti hn u).injective (hd.trans hc.symm)

/-- The unique arctangent center of a nonempty finite family. -/
noncomputable def finiteSoftCenter {n : ℕ} (u : Fin n → ℝ) : ℝ :=
  if hn : 0 < n then (exists_unique_finiteSoftScore_eq_zero hn u).choose else 0

lemma finiteSoftScore_center_eq_zero {n : ℕ} (hn : 0 < n)
    (u : Fin n → ℝ) :
    finiteSoftScore u (finiteSoftCenter u) = 0 := by
  unfold finiteSoftCenter
  simp only [dif_pos hn]
  exact (exists_unique_finiteSoftScore_eq_zero hn u).choose_spec.1

lemma finiteSoftCenter_le_iff_score_le_zero {n : ℕ} (hn : 0 < n)
    (u : Fin n → ℝ) (a : ℝ) :
    finiteSoftCenter u ≤ a ↔ finiteSoftScore u a ≤ 0 := by
  have hzero := finiteSoftScore_center_eq_zero hn u
  have hanti := finiteSoftScore_strictAnti hn u
  constructor
  · intro hle
    rcases hle.lt_or_eq with hlt | rfl
    · exact (hanti hlt).le.trans_eq hzero
    · exact hzero.le
  · intro hscore
    by_contra hnot
    have hlt : a < finiteSoftCenter u := lt_of_not_ge hnot
    have hstrict := hanti hlt
    rw [hzero] at hstrict
    linarith

lemma finiteSoftCenter_measurable
    {δ : Type*} [MeasurableSpace δ] {n : ℕ}
    {u : Fin n → δ → ℝ} (hu : ∀ i, Measurable (u i)) :
    Measurable (fun x => finiteSoftCenter (fun i => u i x)) := by
  by_cases hn : 0 < n
  · apply measurable_of_Iic
    intro a
    have hpre :
        (fun x => finiteSoftCenter (fun i => u i x)) ⁻¹' Iic a =
          {x | finiteSoftScore (fun i => u i x) a ≤ 0} := by
      ext x
      exact finiteSoftCenter_le_iff_score_le_zero hn (fun i => u i x) a
    rw [hpre]
    apply measurableSet_le
    · unfold finiteSoftScore
      apply Finset.measurable_fun_sum
      intro i hi
      exact Real.continuous_arctan.measurable.comp ((hu i).sub measurable_const)
    · exact measurable_const
  · have hzero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simpa [finiteSoftCenter] using (measurable_const : Measurable (fun _ : δ => (0 : ℝ)))

lemma finiteSoftCenter_add_const {n : ℕ} (hn : 0 < n)
    (u : Fin n → ℝ) (c : ℝ) :
    finiteSoftCenter (fun i => c + u i) = c + finiteSoftCenter u := by
  apply (exists_unique_finiteSoftScore_eq_zero hn (fun i => c + u i)).unique
  · exact finiteSoftScore_center_eq_zero hn (fun i => c + u i)
  · unfold finiteSoftScore
    simpa [finiteSoftScore, show ∀ i : Fin n,
        c + u i - (c + finiteSoftCenter u) = u i - finiteSoftCenter u by
      intro i
      ring] using finiteSoftScore_center_eq_zero hn u

lemma finiteSoftCenter_comp_equiv {n : ℕ} (hn : 0 < n)
    (u : Fin n → ℝ) (e : Fin n ≃ Fin n) :
    finiteSoftCenter (fun i => u (e i)) = finiteSoftCenter u := by
  apply (exists_unique_finiteSoftScore_eq_zero hn (fun i => u (e i))).unique
  · exact finiteSoftScore_center_eq_zero hn (fun i => u (e i))
  · unfold finiteSoftScore
    rw [Equiv.sum_comp e
      (fun i => Real.arctan (u i - finiteSoftCenter u))]
    exact finiteSoftScore_center_eq_zero hn u

lemma finiteSoftCenter_aemeasurable
    {δ : Type*} [MeasurableSpace δ] {μ : Measure δ} {n : ℕ}
    {u : Fin n → δ → ℝ} (hu : ∀ i, AEMeasurable (u i) μ) :
    AEMeasurable (fun x => finiteSoftCenter (fun i => u i x)) μ := by
  let v : Fin n → δ → ℝ := fun i => (hu i).mk (u i)
  have hv : ∀ i, Measurable (v i) := fun i => (hu i).measurable_mk
  have hcenter : Measurable (fun x => finiteSoftCenter (fun i => v i x)) :=
    finiteSoftCenter_measurable hv
  apply hcenter.aemeasurable.congr
  have hall : ∀ᵐ x ∂μ, ∀ i : Fin n, u i x = v i x := by
    rw [ae_all_iff]
    intro i
    exact (hu i).ae_eq_mk
  filter_upwards [hall] with x hx
  congr 2
  funext i
  exact (hx i).symm

/-- The robust finite-stage selector obtained from the unique arctangent
center of the dyadic second-difference orbit. -/
noncomputable def dyadicSoftRepresentative
    (f : ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  -finiteSoftCenter
    (fun i : Fin (2 ^ n) =>
      secondDifferenceKernel f (dyadicShift n i) p.1 p.2)

lemma dyadicSoftRepresentative_aemeasurable
    {f : ℝ → ℝ} (hf : HasMeasurableDifferences f) (n : ℕ) :
    AEMeasurable (dyadicSoftRepresentative f n) (volume.prod volume) := by
  unfold dyadicSoftRepresentative
  apply AEMeasurable.neg
  apply finiteSoftCenter_aemeasurable
  intro i
  exact secondDifferenceKernel_measurable hf (dyadicShift n i)

lemma dyadicSoftRepresentative_shift {p : ℝ → ℝ}
    (hp : Function.Periodic p 1) (n : ℕ)
    (j : Fin (2 ^ n)) (x t : ℝ) :
    dyadicSoftRepresentative p n (x + dyadicShift n j, t) =
      dyadicSoftRepresentative p n (x, t) +
        secondDifferenceKernel p (dyadicShift n j) x t := by
  let u : ℝ → ℝ := fun y => differenceKernel p y t
  have huper : Function.Periodic u 1 := differenceKernel_periodic_base hp t
  letI : NeZero (2 ^ n) := ⟨by positivity⟩
  let e : Fin (2 ^ n) ≃ Fin (2 ^ n) := Equiv.addRight j
  have hpoint : ∀ i : Fin (2 ^ n),
      secondDifferenceKernel p (dyadicShift n i)
          (x + dyadicShift n j) t =
        -secondDifferenceKernel p (dyadicShift n j) x t +
          secondDifferenceKernel p (dyadicShift n (e i)) x t := by
    intro i
    have hshift := periodic_dyadic_shift_add huper n i j x
    dsimp [u] at hshift
    unfold secondDifferenceKernel at *
    dsimp [e]
    have hcomm :
        differenceKernel p (x + dyadicShift n j + dyadicShift n i) t =
          differenceKernel p (x + dyadicShift n i + dyadicShift n j) t := by
      unfold differenceKernel
      congr 1 <;> ring
    rw [hcomm, hshift]
    ring
  unfold dyadicSoftRepresentative
  have hcenter :
      finiteSoftCenter
          (fun i : Fin (2 ^ n) =>
            secondDifferenceKernel p (dyadicShift n i)
              (x + dyadicShift n j) t) =
        -secondDifferenceKernel p (dyadicShift n j) x t +
          finiteSoftCenter
            (fun i : Fin (2 ^ n) =>
              secondDifferenceKernel p (dyadicShift n i) x t) := by
    calc
      _ = finiteSoftCenter
          (fun i : Fin (2 ^ n) =>
            -secondDifferenceKernel p (dyadicShift n j) x t +
              secondDifferenceKernel p (dyadicShift n (e i)) x t) := by
            congr 2
            funext i
            exact hpoint i
      _ = -secondDifferenceKernel p (dyadicShift n j) x t +
          finiteSoftCenter
            (fun i : Fin (2 ^ n) =>
              secondDifferenceKernel p (dyadicShift n (e i)) x t) := by
            exact finiteSoftCenter_add_const (by positivity)
              (fun i : Fin (2 ^ n) =>
                secondDifferenceKernel p (dyadicShift n (e i)) x t)
              (-secondDifferenceKernel p (dyadicShift n j) x t)
      _ = _ := by
            rw [finiteSoftCenter_comp_equiv (by positivity)
              (fun i : Fin (2 ^ n) =>
                secondDifferenceKernel p (dyadicShift n i) x t) e]
  rw [hcenter]
  ring

lemma dyadicSoftRepresentative_refined_shift {p : ℝ → ℝ}
    (hp : Function.Periodic p 1) (n k : ℕ)
    (j : Fin (2 ^ n)) (x t : ℝ) :
    dyadicSoftRepresentative p (n + k) (x + dyadicShift n j, t) =
      dyadicSoftRepresentative p (n + k) (x, t) +
        secondDifferenceKernel p (dyadicShift n j) x t := by
  let j' := dyadicRefineIndex n k j
  have h := dyadicSoftRepresentative_shift hp (n + k) j' x t
  simpa [j', dyadicShift_refine] using h

lemma exists_measurable_dyadicSoft_limit
    {p : ℝ → ℝ}
    (hp : HasMeasurableDifferences p)
    (hlim : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ∃ l : ℝ, Tendsto
        (fun n => dyadicSoftRepresentative p n z) atTop (nhds l)) :
    ∃ G : ℝ × ℝ → ℝ, Measurable G ∧
      ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
        Tendsto (fun n => dyadicSoftRepresentative p n z) atTop (nhds (G z)) := by
  exact measurable_limit_of_tendsto_metrizable_ae
    (fun n => dyadicSoftRepresentative_aemeasurable hp n) hlim

lemma dyadicSoft_limit_refined_shift
    {p : ℝ → ℝ} {G : ℝ × ℝ → ℝ}
    (hpper : Function.Periodic p 1)
    (hlim : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      Tendsto (fun n => dyadicSoftRepresentative p n z) atTop (nhds (G z)))
    (n : ℕ) (j : Fin (2 ^ n)) :
    ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      G (z.1 + dyadicShift n j, z.2) =
        G z + secondDifferenceKernel p (dyadicShift n j) z.1 z.2 := by
  let T : ℝ × ℝ → ℝ × ℝ :=
    fun z => (z.1 + dyadicShift n j, z.2)
  have hmp :
      MeasurePreserving T (volume.prod volume) (volume.prod volume) := by
    have hprod :=
      (measurePreserving_add_right volume (dyadicShift n j)).prod
        (MeasurePreserving.id (volume : Measure ℝ))
    convert hprod using 1
    rfl
  have hshift := hmp.quasiMeasurePreserving.ae hlim
  filter_upwards [hlim, hshift] with z hz hzshift
  have htail :
      Tendsto
        (fun k => dyadicSoftRepresentative p (n + k) z)
        atTop (nhds (G z)) :=
    by
      simpa [Nat.add_comm] using (tendsto_add_atTop_iff_nat n).2 hz
  have htailShift :
      Tendsto
        (fun k => dyadicSoftRepresentative p (n + k) (T z))
        atTop (nhds (G (T z))) :=
    by
      simpa [Nat.add_comm] using (tendsto_add_atTop_iff_nat n).2 hzshift
  have heq :
      (fun k => dyadicSoftRepresentative p (n + k) (T z)) =
        (fun k => dyadicSoftRepresentative p (n + k) z +
          secondDifferenceKernel p (dyadicShift n j) z.1 z.2) := by
    funext k
    exact dyadicSoftRepresentative_refined_shift hpper n k j z.1 z.2
  rw [heq] at htailShift
  have hconst :
      Tendsto (fun _ : ℕ =>
        secondDifferenceKernel p (dyadicShift n j) z.1 z.2)
        atTop (nhds (secondDifferenceKernel p (dyadicShift n j) z.1 z.2)) :=
    tendsto_const_nhds
  have hright := htail.add hconst
  simpa [T] using tendsto_nhds_unique htailShift hright

/-- The population arctangent score on the unit circle. -/
noncomputable def circleSoftScore (u : UnitAddCircle → ℝ) (c : ℝ) : ℝ :=
  ∫ x : UnitAddCircle, Real.arctan (u x - c)

lemma circleSoftScore_integrable {u : UnitAddCircle → ℝ}
    (hu : AEMeasurable u volume) (c : ℝ) :
    Integrable (fun x : UnitAddCircle => Real.arctan (u x - c)) volume := by
  apply Integrable.of_bound
    (Real.continuous_arctan.measurable.comp_aemeasurable
      (hu.sub aemeasurable_const)).aestronglyMeasurable
    (Real.pi / 2)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨(Real.neg_pi_div_two_lt_arctan _).le,
    (Real.arctan_lt_pi_div_two _).le⟩

lemma circleSoftScore_continuous {u : UnitAddCircle → ℝ}
    (hu : AEMeasurable u volume) :
    Continuous (circleSoftScore u) := by
  rw [continuous_iff_continuousAt]
  intro c
  unfold circleSoftScore
  apply tendsto_integral_filter_of_dominated_convergence
    (fun _ : UnitAddCircle => Real.pi / 2)
  · filter_upwards [] with d
    exact (circleSoftScore_integrable hu d).aestronglyMeasurable
  · filter_upwards [] with d
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨(Real.neg_pi_div_two_lt_arctan _).le,
      (Real.arctan_lt_pi_div_two _).le⟩
  · exact integrable_const _
  · filter_upwards [] with x
    exact Real.continuous_arctan.continuousAt.tendsto.comp
      (tendsto_const_nhds.sub tendsto_id)

lemma circleSoftScore_strictAnti {u : UnitAddCircle → ℝ}
    (hu : AEMeasurable u volume) :
    StrictAnti (circleSoftScore u) := by
  intro a b hab
  let d : UnitAddCircle → ℝ := fun x =>
    Real.arctan (u x - a) - Real.arctan (u x - b)
  have hdint : Integrable d volume :=
    (circleSoftScore_integrable hu a).sub (circleSoftScore_integrable hu b)
  have hdnonneg : ∀ x, 0 ≤ d x := by
    intro x
    dsimp [d]
    have harg : u x - b < u x - a := by linarith
    have harc := Real.arctan_strictMono harg
    linarith
  have hdsupp : Function.support d = (univ : Set UnitAddCircle) := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    dsimp [d]
    have harg : u x - b < u x - a := by linarith
    have harc := Real.arctan_strictMono harg
    linarith
  have hdpos : 0 < ∫ x : UnitAddCircle, d x := by
    rw [integral_pos_iff_support_of_nonneg hdnonneg hdint, hdsupp]
    simp [UnitAddCircle.measure_univ]
  change 0 < ∫ x : UnitAddCircle,
    (Real.arctan (u x - a) - Real.arctan (u x - b)) at hdpos
  rw [integral_sub (circleSoftScore_integrable hu a)
    (circleSoftScore_integrable hu b)] at hdpos
  unfold circleSoftScore
  linarith

lemma circleSoftScore_tendsto_atTop {u : UnitAddCircle → ℝ}
    (hu : AEMeasurable u volume) :
    Tendsto (circleSoftScore u) atTop (nhds (-(Real.pi / 2))) := by
  have h : Tendsto
      (fun c : ℝ => ∫ x : UnitAddCircle, Real.arctan (u x - c))
      atTop (nhds (∫ _x : UnitAddCircle, -(Real.pi / 2))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure UnitAddCircle))
      (l := (atTop : Filter ℝ))
      (F := fun c (x : UnitAddCircle) => Real.arctan (u x - c))
      (f := fun _ : UnitAddCircle => -(Real.pi / 2))
      (fun _ : UnitAddCircle => Real.pi / 2)
    · filter_upwards [] with c
      exact (circleSoftScore_integrable hu c).aestronglyMeasurable
    · filter_upwards [] with c
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨(Real.neg_pi_div_two_lt_arctan _).le,
        (Real.arctan_lt_pi_div_two _).le⟩
    · exact integrable_const _
    · filter_upwards [] with x
      have harg : Tendsto (fun c : ℝ => u x - c) atTop atBot := by
        refine tendsto_atBot.2 fun b => ?_
        filter_upwards [eventually_ge_atTop (u x - b)] with c hc
        linarith
      exact (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp harg
  change Tendsto
    (fun c : ℝ => ∫ x : UnitAddCircle, Real.arctan (u x - c))
    atTop (nhds (-(Real.pi / 2)))
  simpa [measureReal_def, UnitAddCircle.measure_univ] using h

lemma circleSoftScore_tendsto_atBot {u : UnitAddCircle → ℝ}
    (hu : AEMeasurable u volume) :
    Tendsto (circleSoftScore u) atBot (nhds (Real.pi / 2)) := by
  have h : Tendsto
      (fun c : ℝ => ∫ x : UnitAddCircle, Real.arctan (u x - c))
      atBot (nhds (∫ _x : UnitAddCircle, Real.pi / 2)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure UnitAddCircle))
      (l := (atBot : Filter ℝ))
      (F := fun c (x : UnitAddCircle) => Real.arctan (u x - c))
      (f := fun _ : UnitAddCircle => Real.pi / 2)
      (fun _ : UnitAddCircle => Real.pi / 2)
    · filter_upwards [] with c
      exact (circleSoftScore_integrable hu c).aestronglyMeasurable
    · filter_upwards [] with c
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨(Real.neg_pi_div_two_lt_arctan _).le,
        (Real.arctan_lt_pi_div_two _).le⟩
    · exact integrable_const _
    · filter_upwards [] with x
      have harg : Tendsto (fun c : ℝ => u x - c) atBot atTop := by
        refine tendsto_atTop.2 fun b => ?_
        filter_upwards [eventually_le_atBot (u x - b)] with c hc
        linarith
      exact (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp harg
  change Tendsto
    (fun c : ℝ => ∫ x : UnitAddCircle, Real.arctan (u x - c))
    atBot (nhds (Real.pi / 2))
  simpa [measureReal_def, UnitAddCircle.measure_univ] using h

lemma exists_unique_circleSoftScore_eq_zero {u : UnitAddCircle → ℝ}
    (hu : AEMeasurable u volume) :
    ∃! c : ℝ, circleSoftScore u c = 0 := by
  have hneg : ∃ b : ℝ, circleSoftScore u b < 0 := by
    have h := (circleSoftScore_tendsto_atTop hu).eventually_lt
      tendsto_const_nhds (by linarith [Real.pi_pos] :
        -(Real.pi / 2) < (0 : ℝ))
    exact (Filter.Eventually.exists h)
  have hpos : ∃ a : ℝ, 0 < circleSoftScore u a := by
    have h := tendsto_const_nhds.eventually_lt
      (circleSoftScore_tendsto_atBot hu) (by linarith [Real.pi_pos] :
        (0 : ℝ) < Real.pi / 2)
    exact (Filter.Eventually.exists h)
  rcases hpos with ⟨a, ha⟩
  rcases hneg with ⟨b, hb⟩
  have hab : a < b := by
    by_contra hnot
    have hba : b ≤ a := le_of_not_gt hnot
    have hanti := (circleSoftScore_strictAnti hu).antitone hba
    linarith
  have hzeroMem :
      (0 : ℝ) ∈ Icc (circleSoftScore u b) (circleSoftScore u a) :=
    ⟨hb.le, ha.le⟩
  rcases (intermediate_value_Icc' (a := a) (b := b) hab.le
      (circleSoftScore_continuous hu).continuousOn) hzeroMem with ⟨c, hcI, hc⟩
  refine ⟨c, hc, ?_⟩
  intro d hd
  exact (circleSoftScore_strictAnti hu).injective (hd.trans hc.symm)

noncomputable def circleSoftCenter (u : UnitAddCircle → ℝ)
    (hu : AEMeasurable u volume) : ℝ :=
  (exists_unique_circleSoftScore_eq_zero hu).choose

lemma circleSoftScore_center_eq_zero {u : UnitAddCircle → ℝ}
    (hu : AEMeasurable u volume) :
    circleSoftScore u (circleSoftCenter u hu) = 0 := by
  unfold circleSoftCenter
  exact (exists_unique_circleSoftScore_eq_zero hu).choose_spec.1

noncomputable def circleFiniteSoftCenter (u : UnitAddCircle → ℝ) (n : ℕ)
    (x : UnitAddCircle) : ℝ :=
  finiteSoftCenter
    (fun i : Fin (2 ^ n) =>
      u (x + (((i : ℝ) / (2 ^ n : ℝ) : ℝ) : UnitAddCircle)))

lemma circleFiniteSoftCenter_measurable {u : UnitAddCircle → ℝ}
    (hu : Measurable u) (n : ℕ) :
    Measurable (circleFiniteSoftCenter u n) := by
  unfold circleFiniteSoftCenter
  apply finiteSoftCenter_measurable
  intro i
  exact hu.comp (measurable_id.add_const _)

lemma circleFiniteSoftCenter_aemeasurable {u : UnitAddCircle → ℝ}
    (hu : AEMeasurable u volume) (n : ℕ) :
    AEMeasurable (circleFiniteSoftCenter u n) volume := by
  unfold circleFiniteSoftCenter
  apply finiteSoftCenter_aemeasurable
  intro i
  exact hu.comp_quasiMeasurePreserving
    (measurePreserving_add_right volume
      (((i : ℝ) / (2 ^ n : ℝ) : ℝ) : UnitAddCircle)).quasiMeasurePreserving

lemma finiteSoftCenter_ge_iff_score_ge_zero {n : ℕ} (hn : 0 < n)
    (u : Fin n → ℝ) (a : ℝ) :
    a ≤ finiteSoftCenter u ↔ 0 ≤ finiteSoftScore u a := by
  have hzero := finiteSoftScore_center_eq_zero hn u
  have hanti := finiteSoftScore_strictAnti hn u
  constructor
  · intro hle
    rcases hle.lt_or_eq with hlt | rfl
    · rw [← hzero]
      exact (hanti hlt).le
    · exact hzero.ge
  · intro hscore
    by_contra hnot
    have hlt : finiteSoftCenter u < a := lt_of_not_ge hnot
    have hstrict := hanti hlt
    rw [hzero] at hstrict
    linarith

lemma circleFiniteSoftScore_div_eq_average
    (u : UnitAddCircle → ℝ) (n : ℕ) (x : UnitAddCircle) (c : ℝ) :
    finiteSoftScore
        (fun i : Fin (2 ^ n) =>
          u (x + (((i : ℝ) / (2 ^ n : ℝ) : ℝ) : UnitAddCircle))) c /
        (2 ^ n : ℝ) =
      circleDyadicAverage (fun y => Real.arctan (u y - c)) n x := by
  rfl

lemma tendstoInMeasure_circleFiniteSoftCenter
    {u : UnitAddCircle → ℝ} (hu : AEMeasurable u volume) :
    TendstoInMeasure volume
      (fun n x => circleFiniteSoftCenter u n x) atTop
      (fun _ : UnitAddCircle => circleSoftCenter u hu) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  let C : ℝ := circleSoftCenter u hu
  let slow : ℝ := circleSoftScore u (C - ε)
  let shigh : ℝ := circleSoftScore u (C + ε)
  have hCzero : circleSoftScore u C = 0 := circleSoftScore_center_eq_zero hu
  have hslow : 0 < slow := by
    dsimp [slow]
    have hlt : C - ε < C := by linarith
    have hs := circleSoftScore_strictAnti hu hlt
    rw [hCzero] at hs
    exact hs
  have hshigh : shigh < 0 := by
    dsimp [shigh]
    have hlt : C < C + ε := by linarith
    have hs := circleSoftScore_strictAnti hu hlt
    rw [hCzero] at hs
    exact hs
  let vlo : UnitAddCircle → ℝ := fun y => Real.arctan (u y - (C - ε))
  let vhi : UnitAddCircle → ℝ := fun y => Real.arctan (u y - (C + ε))
  have hlo :
      TendstoInMeasure volume
        (fun n x => circleDyadicAverage vlo n x) atTop
        (fun _ : UnitAddCircle => slow) := by
    have h := tendstoInMeasure_circleDyadicAverage_sub_integral
      (circleSoftScore_integrable hu (C - ε))
    convert h using 1
    · rfl
  have hhi :
      TendstoInMeasure volume
        (fun n x => circleDyadicAverage vhi n x) atTop
        (fun _ : UnitAddCircle => shigh) := by
    have h := tendstoInMeasure_circleDyadicAverage_sub_integral
      (circleSoftScore_integrable hu (C + ε))
    convert h using 1
    · rfl
  have hloMeasure :
      Tendsto
        (fun n => volume {x : UnitAddCircle |
          slow / 2 ≤ dist (circleDyadicAverage vlo n x) slow})
        atTop (nhds 0) :=
    (tendstoInMeasure_iff_dist.mp hlo) (slow / 2) (by positivity)
  have hhiMeasure :
      Tendsto
        (fun n => volume {x : UnitAddCircle |
          (-shigh) / 2 ≤ dist (circleDyadicAverage vhi n x) shigh})
        atTop (nhds 0) :=
    (tendstoInMeasure_iff_dist.mp hhi) ((-shigh) / 2) (by nlinarith)
  have hsum := hloMeasure.add hhiMeasure
  have hsum0 :
      Tendsto
        (fun n =>
          volume {x : UnitAddCircle |
            slow / 2 ≤ dist (circleDyadicAverage vlo n x) slow} +
          volume {x : UnitAddCircle |
            (-shigh) / 2 ≤ dist (circleDyadicAverage vhi n x) shigh})
        atTop (nhds 0) := by
    simpa using hsum
  change Tendsto
    (fun n => volume {x : UnitAddCircle |
      ε ≤ dist (circleFiniteSoftCenter u n x) C})
    atTop (nhds 0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum0
  · exact Eventually.of_forall fun _ => bot_le
  · filter_upwards [] with n
    let A : Set UnitAddCircle :=
      {x | ε ≤ dist (circleFiniteSoftCenter u n x) C}
    let B : Set UnitAddCircle :=
      {x | slow / 2 ≤ dist (circleDyadicAverage vlo n x) slow}
    let D : Set UnitAddCircle :=
      {x | (-shigh) / 2 ≤ dist (circleDyadicAverage vhi n x) shigh}
    have hsub : A ⊆ B ∪ D := by
      intro x hx
      have hfar : circleFiniteSoftCenter u n x ≤ C - ε ∨
          C + ε ≤ circleFiniteSoftCenter u n x := by
        dsimp [A] at hx
        rw [Real.dist_eq] at hx
        rw [abs_sub_comm] at hx
        by_contra hnot
        push_neg at hnot
        have : |circleFiniteSoftCenter u n x - C| < ε := by
          rw [abs_lt]
          constructor <;> linarith
        exact (not_lt_of_ge hx) (by simpa [abs_sub_comm] using this)
      rcases hfar with hleft | hright
      · left
        dsimp [B, vlo]
        have hsle :
            finiteSoftScore
              (fun i : Fin (2 ^ n) =>
                u (x + (((i : ℝ) / (2 ^ n : ℝ) : ℝ) : UnitAddCircle)))
              (C - ε) ≤ 0 :=
          (finiteSoftCenter_le_iff_score_le_zero (by positivity) _ _).1 hleft
        have havg :
            circleDyadicAverage vlo n x ≤ 0 := by
          rw [← circleFiniteSoftScore_div_eq_average]
          exact div_nonpos_of_nonpos_of_nonneg hsle (by positivity)
        rw [Real.dist_eq]
        have : slow / 2 ≤ |circleDyadicAverage vlo n x - slow| := by
          rw [abs_of_nonpos (by linarith)]
          linarith
        exact this
      · right
        dsimp [D, vhi]
        have hsge :
            0 ≤ finiteSoftScore
              (fun i : Fin (2 ^ n) =>
                u (x + (((i : ℝ) / (2 ^ n : ℝ) : ℝ) : UnitAddCircle)))
              (C + ε) :=
          (finiteSoftCenter_ge_iff_score_ge_zero (by positivity) _ _).1 hright
        have havg :
            0 ≤ circleDyadicAverage vhi n x := by
          rw [← circleFiniteSoftScore_div_eq_average]
          exact div_nonneg hsge (by positivity)
        rw [Real.dist_eq]
        have : (-shigh) / 2 ≤ |circleDyadicAverage vhi n x - shigh| := by
          rw [abs_of_nonneg (by linarith)]
          linarith
        exact this
    calc
      volume A ≤ volume (B ∪ D) := measure_mono hsub
      _ ≤ volume B + volume D := measure_union_le _ _



open Filter MeasureTheory Set Function
open scoped Pointwise ENNReal


lemma tendstoInMeasure_comp_measurePreserving_real
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μa : Measure α} {μb : Measure β} {φ : α → β}
    (hφ : MeasurePreserving φ μa μb)
    {F : ℕ → β → ℝ} {G : β → ℝ}
    (hF : ∀ n, AEMeasurable (F n) μb) (hG : AEMeasurable G μb)
    (h : TendstoInMeasure μb F atTop G) :
    TendstoInMeasure μa (fun n x => F n (φ x)) atTop (fun x => G (φ x)) := by
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  have hh := h ε hε
  apply hh.congr'
  filter_upwards [] with n
  have hs : NullMeasurableSet
      {y : β | ε ≤ dist (F n y) (G y)} μb :=
    nullMeasurableSet_le aemeasurable_const ((hF n).dist hG)
  rw [← hφ.measure_preimage hs]
  rfl

lemma tendstoInMeasure_sub_fixed_real
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {G d : α → ℝ}
    (h : TendstoInMeasure μ F atTop G) :
    TendstoInMeasure μ (fun n x => d x - F n x) atTop
      (fun x => d x - G x) := by
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  have hh := h ε hε
  convert hh using 1
  funext n
  congr 1
  ext x
  simp only [Set.mem_setOf_eq]
  rw [Real.dist_eq, Real.dist_eq]
  rw [show d x - F n x - (d x - G x) = -(F n x - G x) by ring]
  simp only [abs_neg]

lemma tendsto_measure_pair_dist_of_tendstoInMeasure
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {G : α → ℝ}
    (h : TendstoInMeasure μ F atTop G) (ε : ℝ) (hε : 0 < ε) :
    Tendsto
      (fun nm : ℕ × ℕ =>
        μ {x : α | ε ≤ dist (F nm.1 x) (F nm.2 x)})
      (atTop ×ˢ atTop) (nhds 0) := by
  let a : ℕ → ℝ≥0∞ := fun n =>
    μ {x : α | ε / 2 ≤ dist (F n x) (G x)}
  have ha : Tendsto a atTop (nhds 0) := by
    exact (tendstoInMeasure_iff_dist.mp h) (ε / 2) (by linarith)
  have hsum :
      Tendsto (fun nm : ℕ × ℕ => a nm.1 + a nm.2)
        (atTop ×ˢ atTop) (nhds 0) := by
    have h' := (ha.comp tendsto_fst).add (ha.comp tendsto_snd)
    simpa using h'
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum
  · exact Eventually.of_forall fun _ => bot_le
  · filter_upwards [] with nm
    let A : Set α := {x | ε ≤ dist (F nm.1 x) (F nm.2 x)}
    let B : Set α := {x | ε / 2 ≤ dist (F nm.1 x) (G x)}
    let C : Set α := {x | ε / 2 ≤ dist (F nm.2 x) (G x)}
    have hsub : A ⊆ B ∪ C := by
      intro x hx
      by_contra hnot
      have hnotB : x ∉ B := by
        intro hxB
        exact hnot (Or.inl hxB)
      have hnotC : x ∉ C := by
        intro hxC
        exact hnot (Or.inr hxC)
      have hBlt : dist (F nm.1 x) (G x) < ε / 2 := by
        exact lt_of_not_ge (by simpa [B] using hnotB)
      have hClt : dist (F nm.2 x) (G x) < ε / 2 := by
        exact lt_of_not_ge (by simpa [C] using hnotC)
      have htri :
          dist (F nm.1 x) (F nm.2 x) ≤
            dist (F nm.1 x) (G x) + dist (G x) (F nm.2 x) :=
        dist_triangle _ _ _
      have hsymm : dist (G x) (F nm.2 x) = dist (F nm.2 x) (G x) :=
        dist_comm _ _
      dsimp [A] at hx
      rw [hsymm] at htri
      linarith
    calc
      μ A ≤ μ (B ∪ C) := measure_mono hsub
      _ ≤ μ B + μ C := measure_union_le _ _

lemma tendsto_prod_measure_pair_dist_of_section_tendstoInMeasure
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μa : Measure α} {μb : Measure β}
    [IsFiniteMeasure μa] [IsFiniteMeasure μb] [SFinite μa]
    (F : ℕ → β × α → ℝ)
    (hF : ∀ n, Measurable (F n))
    (hsec : ∀ᵐ b ∂μb, ∃ G : α → ℝ,
      TendstoInMeasure μa (fun n a => F n (b, a)) atTop G)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto
      (fun nm : ℕ × ℕ =>
        (μb.prod μa) {z : β × α |
          ε ≤ dist (F nm.1 z) (F nm.2 z)})
      (atTop ×ˢ atTop) (nhds 0) := by
  let B : ℕ × ℕ → β → ℝ≥0∞ := fun nm b =>
    μa {a : α | ε ≤ dist (F nm.1 (b, a)) (F nm.2 (b, a))}
  have hBmeas : ∀ nm, Measurable (B nm) := by
    intro nm
    let S : Set (β × α) :=
      {z | ε ≤ dist (F nm.1 z) (F nm.2 z)}
    have hS : MeasurableSet S := by
      dsimp [S]
      exact measurableSet_le measurable_const ((hF nm.1).dist (hF nm.2))
    have hm := measurable_measure_prodMk_left (ν := μa) hS
    simpa [B, S] using hm
  have hBbound : ∀ nm, ∀ b, B nm b ≤ μa univ := by
    intro nm b
    exact measure_mono (subset_univ _)
  have hBlim : ∀ᵐ b ∂μb,
      Tendsto (fun nm : ℕ × ℕ => B nm b)
        (atTop ×ˢ atTop) (nhds 0) := by
    filter_upwards [hsec] with b hb
    rcases hb with ⟨G, hG⟩
    exact tendsto_measure_pair_dist_of_tendstoInMeasure hG ε hε
  have hlintegral :
      Tendsto
        (fun nm : ℕ × ℕ => ∫⁻ b, B nm b ∂μb)
        (atTop ×ˢ atTop) (nhds 0) := by
    have hD := tendsto_lintegral_filter_of_dominated_convergence
      (μ := μb) (l := atTop ×ˢ atTop)
      (F := B) (f := fun _ : β => 0)
      (fun _ : β => μa univ)
      (Eventually.of_forall hBmeas)
      (Eventually.of_forall fun nm =>
        Eventually.of_forall (hBbound nm))
      (by
        simp only [lintegral_const, Measure.restrict_apply_univ]
        exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
      hBlim
    simpa using hD
  apply hlintegral.congr'
  filter_upwards [] with nm
  let S : Set (β × α) :=
    {z | ε ≤ dist (F nm.1 z) (F nm.2 z)}
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_le measurable_const ((hF nm.1).dist (hF nm.2))
  rw [Measure.prod_apply hS]
  rfl

/-- For one fixed section, the second-difference definition is exactly the
section value minus the soft center of its finite dyadic orbit. -/
lemma dyadicSoftRepresentative_eq_sub_orbit_center
    (p : ℝ → ℝ) (n : ℕ) (x t : ℝ) :
    dyadicSoftRepresentative p n (x, t) =
      differenceKernel p x t -
        finiteSoftCenter
          (fun i : Fin (2 ^ n) =>
            differenceKernel p (x + dyadicShift n i) t) := by
  unfold dyadicSoftRepresentative secondDifferenceKernel
  have hcenter := finiteSoftCenter_add_const (by positivity)
    (fun i : Fin (2 ^ n) => differenceKernel p (x + dyadicShift n i) t)
    (-differenceKernel p x t)
  rw [show (fun i : Fin (2 ^ n) =>
      differenceKernel p (x + dyadicShift n i) t -
        differenceKernel p x t) =
      (fun i => -differenceKernel p x t +
        differenceKernel p (x + dyadicShift n i) t) by
    funext i
    ring]
  rw [hcenter]
  ring

/-- On one fundamental interval, dyadic orbit soft centers converge in
measure to the population soft center of the periodic lift. -/
lemma tendstoInMeasure_periodic_orbit_softCenter
    {u : ℝ → ℝ} (hu : Function.Periodic u 1)
    (hum : AEMeasurable u volume) :
    TendstoInMeasure (volume.restrict (Ioc (0 : ℝ) 1))
      (fun n x =>
        finiteSoftCenter
          (fun i : Fin (2 ^ n) => u (x + dyadicShift n i)))
      atTop
      (fun _ : ℝ =>
        circleSoftCenter hu.lift (aemeasurable_periodic_lift hu hum)) := by
  let U : UnitAddCircle → ℝ := hu.lift
  have hU : AEMeasurable U (volume : Measure UnitAddCircle) :=
    aemeasurable_periodic_lift hu hum
  have hcircle := tendstoInMeasure_circleFiniteSoftCenter hU
  have hcomp := tendstoInMeasure_comp_measurePreserving_real
    (UnitAddCircle.measurePreserving_mk 0)
    (fun n => circleFiniteSoftCenter_aemeasurable hU n)
    aemeasurable_const hcircle
  simp only [zero_add] at hcomp
  convert hcomp using 1
  · funext n x
    unfold circleFiniteSoftCenter
    congr 2

/-- Every fixed periodic difference section has a canonical in-measure limit
for the jointly measurable finite soft representatives. -/
lemma tendstoInMeasure_dyadicSoftRepresentative_section
    {p : ℝ → ℝ} (hpper : Function.Periodic p 1)
    (hp : HasMeasurableDifferences p) (t : ℝ) :
    TendstoInMeasure (volume.restrict (Ioc (0 : ℝ) 1))
      (fun n x => dyadicSoftRepresentative p n (x, t))
      atTop
      (fun x =>
        differenceKernel p x t -
          circleSoftCenter
            (differenceKernel_periodic_base hpper t).lift
            (aemeasurable_periodic_lift
              (differenceKernel_periodic_base hpper t) (hp t))) := by
  let u : ℝ → ℝ := fun x => differenceKernel p x t
  have huper : Function.Periodic u 1 :=
    differenceKernel_periodic_base hpper t
  have humeas : AEMeasurable u volume := hp t
  have hcenter := tendstoInMeasure_periodic_orbit_softCenter huper humeas
  have hsub := tendstoInMeasure_sub_fixed_real
    (d := fun x : ℝ => differenceKernel p x t) hcenter
  refine hsub.congr' ?_ ?_
  · filter_upwards [] with n
    filter_upwards [] with x
    exact (dyadicSoftRepresentative_eq_sub_orbit_center p n x t).symm
  · rfl

/-- A genuinely measurable version of each finite soft representative. -/
noncomputable def measurableDyadicSoftRepresentative
    (p : ℝ → ℝ) (hp : HasMeasurableDifferences p) (n : ℕ) :
    ℝ × ℝ → ℝ :=
  (dyadicSoftRepresentative_aemeasurable hp n).mk
    (dyadicSoftRepresentative p n)

lemma measurable_measurableDyadicSoftRepresentative
    {p : ℝ → ℝ} (hp : HasMeasurableDifferences p) (n : ℕ) :
    Measurable (measurableDyadicSoftRepresentative p hp n) :=
  (dyadicSoftRepresentative_aemeasurable hp n).measurable_mk

lemma ae_eq_measurableDyadicSoftRepresentative
    {p : ℝ → ℝ} (hp : HasMeasurableDifferences p) (n : ℕ) :
    dyadicSoftRepresentative p n =ᵐ[volume.prod volume]
      measurableDyadicSoftRepresentative p hp n :=
  (dyadicSoftRepresentative_aemeasurable hp n).ae_eq_mk

/-- On the fundamental square, the measurable finite soft representatives are
Cauchy in measure. -/
lemma tendsto_fundamentalSquare_pair_dist_dyadicSoftRepresentative
    {p : ℝ → ℝ} (hpper : Function.Periodic p 1)
    (hp : HasMeasurableDifferences p) (ε : ℝ) (hε : 0 < ε) :
    Tendsto
      (fun nm : ℕ × ℕ =>
        ((volume.restrict (Ioc (0 : ℝ) 1)).prod
          (volume.restrict (Ioc (0 : ℝ) 1)))
          {z : ℝ × ℝ |
            ε ≤ dist
              (measurableDyadicSoftRepresentative p hp nm.1 (z.2, z.1))
              (measurableDyadicSoftRepresentative p hp nm.2 (z.2, z.1))})
      (atTop ×ˢ atTop) (nhds 0) := by
  let M : ℕ → ℝ × ℝ → ℝ :=
    fun n => measurableDyadicSoftRepresentative p hp n
  let F : ℕ → ℝ × ℝ → ℝ :=
    fun n z => M n (z.2, z.1)
  have hF : ∀ n, Measurable (F n) := by
    intro n
    exact (measurable_measurableDyadicSoftRepresentative hp n).comp
      (measurable_snd.prodMk measurable_fst)
  have hsectionEq :
      ∀ n : ℕ, ∀ᵐ t ∂volume,
        ∀ᵐ x ∂volume,
          dyadicSoftRepresentative p n (x, t) = M n (x, t) := by
    intro n
    have heq := ae_eq_measurableDyadicSoftRepresentative hp n
    have hmap :
        ∀ᵐ z ∂Measure.map Prod.swap (volume.prod volume),
          dyadicSoftRepresentative p n z = M n z := by
      rw [Measure.prod_swap]
      exact heq
    have hpull := ae_of_ae_map measurable_swap.aemeasurable hmap
    simpa using Measure.ae_ae_of_ae_prod hpull
  have hall :
      ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
        ∀ n : ℕ, ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
          dyadicSoftRepresentative p n (x, t) = M n (x, t) := by
    rw [ae_all_iff]
    intro n
    apply ae_restrict_of_ae
    filter_upwards [hsectionEq n] with t ht
    exact ae_restrict_of_ae ht
  have hsec :
      ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
        ∃ G : ℝ → ℝ,
          TendstoInMeasure (volume.restrict (Ioc (0 : ℝ) 1))
            (fun n x => F n (t, x)) atTop G := by
    filter_upwards [hall] with t ht
    let G : ℝ → ℝ := fun x =>
      differenceKernel p x t -
        circleSoftCenter
          (differenceKernel_periodic_base hpper t).lift
          (aemeasurable_periodic_lift
            (differenceKernel_periodic_base hpper t) (hp t))
    refine ⟨G, ?_⟩
    have hlim := tendstoInMeasure_dyadicSoftRepresentative_section hpper hp t
    refine hlim.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [] with n
    exact ht n
  exact tendsto_prod_measure_pair_dist_of_section_tendstoInMeasure
    F hF hsec ε hε



open Filter MeasureTheory Set Function
open scoped Pointwise ENNReal

lemma exists_measurable_subseq_limit_of_pair_cauchy_in_measure
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : ℕ → α → ℝ) (hF : ∀ n, Measurable (F n))
    (hpair : ∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun nm : ℕ × ℕ =>
          μ {x : α | ε ≤ dist (F nm.1 x) (F nm.2 x)})
        (atTop ×ˢ atTop) (nhds 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∃ G : α → ℝ, Measurable G ∧
        ∀ᵐ x ∂μ, Tendsto (fun k => F (ns k) x) atTop (nhds (G x)) := by
  classical
  let δ : ℕ → ℝ := fun k => (2 : ℝ)⁻¹ ^ (k + 1)
  let e : ℕ → ℝ≥0∞ := fun k => (2 : ℝ≥0∞)⁻¹ ^ (k + 1)
  have hthreshold : ∀ k : ℕ, ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
        μ {x : α | δ k ≤ dist (F n x) (F m x)} < e k := by
    intro k
    have hδ : 0 < δ k := by
      dsimp [δ]
      positivity
    have hsmall :
        ∀ᶠ nm : ℕ × ℕ in atTop ×ˢ atTop,
          μ {x : α | δ k ≤ dist (F nm.1 x) (F nm.2 x)} < e k := by
      have hlim := hpair (δ k) hδ
      exact hlim.eventually_lt tendsto_const_nhds (by
        dsimp [e]
        exact ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _)
    rcases eventually_prod_iff.mp hsmall with ⟨pa, hpa, pb, hpb, hab⟩
    rcases (eventually_atTop.1 hpa) with ⟨Na, hNa⟩
    rcases (eventually_atTop.1 hpb) with ⟨Nb, hNb⟩
    refine ⟨max Na Nb, ?_⟩
    intro n m hn hm
    exact hab (hNa n (le_trans (le_max_left _ _) hn))
      (hNb m (le_trans (le_max_right _ _) hm))
  choose N hN using hthreshold
  let ns : ℕ → ℕ := Nat.rec (N 0)
    (fun k prev => max (prev + 1) (N (k + 1)))
  have hns_strict : StrictMono ns := by
    apply strictMono_nat_of_lt_succ
    intro k
    change ns k < max (ns k + 1) (N (k + 1))
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hnsN : ∀ k : ℕ, N k ≤ ns k := by
    intro k
    cases k with
    | zero => rfl
    | succ k =>
        change N (k + 1) ≤ max (ns k + 1) (N (k + 1))
        exact le_max_right _ _
  let S : ℕ → Set α := fun k =>
    {x | δ k ≤ dist (F (ns k) x) (F (ns (k + 1)) x)}
  have hμS : ∀ k : ℕ, μ (S k) ≤ e k := by
    intro k
    have hnext : N k ≤ ns (k + 1) :=
      le_trans (hnsN k) (hns_strict (Nat.lt_succ_self k)).le
    exact (hN k (ns k) (ns (k + 1)) (hnsN k) hnext).le
  have htsum : (∑' k : ℕ, μ (S k)) ≠ ∞ := by
    apply ne_top_of_le_ne_top
      (show (∑' k : ℕ, e k) ≠ ∞ by
        dsimp [e]
        rw [show (fun k : ℕ => (2 : ℝ≥0∞)⁻¹ ^ (k + 1)) =
            (fun k => (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ ^ k) by
          funext k
          rw [pow_succ']]
        rw [ENNReal.tsum_mul_left]
        simp)
    exact ENNReal.tsum_le_tsum hμS
  have hgood : ∀ᵐ x ∂μ, ∀ᶠ k in atTop, x ∉ S k :=
    ae_eventually_notMem htsum
  have hlim :
      ∀ᵐ x ∂μ, ∃ l : ℝ,
        Tendsto (fun k => F (ns k) x) atTop (nhds l) := by
    filter_upwards [hgood] with x hx
    rcases (eventually_atTop.1 hx) with ⟨K, hK⟩
    let a : ℕ → ℝ := fun n => F (ns (K + n)) x
    have ha_dist : ∀ n : ℕ, dist (a n) (a (n + 1)) ≤ δ n := by
      intro n
      have hnot := hK (K + n) (by omega)
      have hlt : dist (F (ns (K + n)) x) (F (ns (K + n + 1)) x) < δ (K + n) := by
        exact lt_of_not_ge (by simpa [S] using hnot)
      have hδmono : δ (K + n) ≤ δ n := by
        dsimp [δ]
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have hlt' : dist (a n) (a (n + 1)) < δ (K + n) := by
        dsimp [a]
        simpa [Nat.add_assoc] using hlt
      exact le_trans hlt'.le hδmono
    have hδsum : Summable δ := by
      convert (summable_geometric_two' (1 : ℝ)) using 1
      funext n
      dsimp [δ]
      simp [one_div, inv_pow, pow_succ', div_eq_mul_inv]
    have hacauchy : CauchySeq a :=
      cauchySeq_of_dist_le_of_summable δ ha_dist hδsum
    rcases cauchySeq_tendsto_of_complete hacauchy with ⟨l, hl⟩
    refine ⟨l, ?_⟩
    have htail :
        Tendsto (fun n => F (ns (n + K)) x) atTop (nhds l) := by
      simpa [a, Nat.add_comm] using hl
    exact (tendsto_add_atTop_iff_nat K).1 htail
  rcases measurable_limit_of_tendsto_metrizable_ae
      (fun k => (hF (ns k)).aemeasurable) hlim with ⟨G, hG, hGlim⟩
  exact ⟨ns, hns_strict, G, hG, hGlim⟩



open Filter MeasureTheory Set Function
open scoped Pointwise ENNReal

lemma differenceKernel_periodic_increment {p : ℝ → ℝ}
    (hp : Function.Periodic p 1) (x : ℝ) :
    Function.Periodic (fun t => differenceKernel p x t) 1 := by
  intro t
  change differenceKernel p x (t + 1) = differenceKernel p x t
  unfold differenceKernel
  rw [show x + (t + 1) = (x + t) + 1 by ring, hp]

lemma secondDifferenceKernel_periodic_increment {p : ℝ → ℝ}
    (hp : Function.Periodic p 1) (q x : ℝ) :
    Function.Periodic (fun t => secondDifferenceKernel p q x t) 1 := by
  intro t
  change secondDifferenceKernel p q x (t + 1) =
    secondDifferenceKernel p q x t
  unfold secondDifferenceKernel
  rw [show differenceKernel p (x + q) (t + 1) =
      differenceKernel p (x + q) t from
        differenceKernel_periodic_increment hp (x + q) t,
    show differenceKernel p x (t + 1) =
      differenceKernel p x t from
        differenceKernel_periodic_increment hp x t]

lemma dyadicSoftRepresentative_periodic_base {p : ℝ → ℝ}
    (hp : Function.Periodic p 1) (n : ℕ) (t : ℝ) :
    Function.Periodic (fun x => dyadicSoftRepresentative p n (x, t)) 1 := by
  intro x
  change dyadicSoftRepresentative p n (x + 1, t) =
    dyadicSoftRepresentative p n (x, t)
  unfold dyadicSoftRepresentative
  congr 1
  apply congrArg finiteSoftCenter
  funext i
  exact secondDifferenceKernel_periodic_base hp (dyadicShift n i) t x

lemma dyadicSoftRepresentative_periodic_increment {p : ℝ → ℝ}
    (hp : Function.Periodic p 1) (n : ℕ) (x : ℝ) :
    Function.Periodic (fun t => dyadicSoftRepresentative p n (x, t)) 1 := by
  intro t
  change dyadicSoftRepresentative p n (x, t + 1) =
    dyadicSoftRepresentative p n (x, t)
  unfold dyadicSoftRepresentative
  congr 1
  apply congrArg finiteSoftCenter
  funext i
  exact secondDifferenceKernel_periodic_increment hp (dyadicShift n i) x t

/-- The representative of a real number in the half-open interval (0, 1]. -/
noncomputable def iocRepresentative (x : ℝ) : ℝ :=
  x - (⌈x⌉ : ℝ) + 1

lemma iocRepresentative_eq_self {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    iocRepresentative x = x := by
  have hceil : ⌈x⌉ = (1 : ℤ) := by
    rw [Int.ceil_eq_iff]
    constructor <;> norm_num at hx ⊢
    · exact hx.1
    · exact hx.2
  simp [iocRepresentative, hceil]

lemma iocRepresentative_eq_sub_int {x : ℝ} {n : ℤ}
    (hx : x ∈ Ioc (n : ℝ) (n + 1 : ℝ)) :
    iocRepresentative x = x - n := by
  have hceil : ⌈x⌉ = n + 1 := by
    rw [Int.ceil_eq_iff]
    constructor
    · norm_num
      exact hx.1
    · exact_mod_cast hx.2
  unfold iocRepresentative
  rw [hceil]
  push_cast
  ring

lemma iocRepresentative_add_one (x : ℝ) :
    iocRepresentative (x + 1) = iocRepresentative x := by
  unfold iocRepresentative
  rw [Int.ceil_add_one]
  norm_num

lemma measurable_iocRepresentative :
    Measurable iocRepresentative := by
  unfold iocRepresentative
  have hceil : Measurable (fun x : ℝ => (⌈x⌉ : ℝ)) :=
    (measurable_of_countable ((↑) : ℤ → ℝ)).comp Int.measurable_ceil
  exact (measurable_id.sub hceil).add measurable_const

/-- Periodize a two-variable function by taking both coordinates in (0,1]. -/
noncomputable def periodizePlane (G : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  G (iocRepresentative z.1, iocRepresentative z.2)

lemma measurable_periodizePlane {G : ℝ × ℝ → ℝ} (hG : Measurable G) :
    Measurable (periodizePlane G) := by
  unfold periodizePlane
  exact hG.comp
    ((measurable_iocRepresentative.comp measurable_fst).prodMk
      (measurable_iocRepresentative.comp measurable_snd))

lemma periodizePlane_periodic_fst (G : ℝ × ℝ → ℝ) (x : ℝ) :
    Function.Periodic (fun t => periodizePlane G (t, x)) 1 := by
  intro t
  simp [periodizePlane, iocRepresentative_add_one]

lemma periodizePlane_periodic_snd (G : ℝ × ℝ → ℝ) (t : ℝ) :
    Function.Periodic (fun x => periodizePlane G (t, x)) 1 := by
  intro x
  simp [periodizePlane, iocRepresentative_add_one]

lemma dyadicSoftRepresentative_sub_ints {p : ℝ → ℝ}
    (hp : Function.Periodic p 1) (n : ℕ) (a b : ℤ) (x t : ℝ) :
    dyadicSoftRepresentative p n (x, t) =
      dyadicSoftRepresentative p n (x - b, t - a) := by
  have ht :=
    (dyadicSoftRepresentative_periodic_increment hp n x).zsmul a (t - a)
  have hx :=
    (dyadicSoftRepresentative_periodic_base hp n (t - a)).zsmul b (x - b)
  calc
    dyadicSoftRepresentative p n (x, t) =
        dyadicSoftRepresentative p n (x, t - a) := by
          convert ht using 1 <;> push_cast <;> ring
    _ = dyadicSoftRepresentative p n (x - b, t - a) := by
          convert hx using 1 <;> push_cast <;> ring

lemma exists_int_mem_Ioc (x : ℝ) :
    ∃ n : ℤ, x ∈ Ioc (n : ℝ) (n + 1 : ℝ) := by
  refine ⟨⌈x⌉ - 1, ?_⟩
  constructor
  · rw [Int.cast_sub, Int.cast_one, sub_lt_iff_lt_add]
    exact Int.ceil_lt_add_one x
  · simpa [Int.cast_sub, Int.cast_one] using Int.le_ceil x

/-- A periodic subsequential limit on the fundamental square extends to a
global a.e. limit after periodizing the measurable limit. -/
lemma ae_tendsto_periodizePlane_of_fundamentalSquare
    {p : ℝ → ℝ} (hpper : Function.Periodic p 1)
    {ns : ℕ → ℕ} {G : ℝ × ℝ → ℝ}
    (hlim :
      ∀ᵐ z ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod
        (volume.restrict (Ioc (0 : ℝ) 1))),
        Tendsto
          (fun k => dyadicSoftRepresentative p (ns k) (z.2, z.1))
          atTop (nhds (G z))) :
    ∀ᵐ z ∂volume.prod volume,
      Tendsto
        (fun k => dyadicSoftRepresentative p (ns k) (z.2, z.1))
        atTop (nhds (periodizePlane G z)) := by
  let R : Set (ℝ × ℝ) :=
    Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1
  have hRm : MeasurableSet R := measurableSet_Ioc.prod measurableSet_Ioc
  have hlimR :
      ∀ᵐ z ∂(volume.prod volume).restrict R,
        Tendsto
          (fun k => dyadicSoftRepresentative p (ns k) (z.2, z.1))
          atTop (nhds (G z)) := by
    simpa [R, Measure.prod_restrict] using hlim
  have hfull :
      ∀ᵐ z ∂volume.prod volume, z ∈ R →
        Tendsto
          (fun k => dyadicSoftRepresentative p (ns k) (z.2, z.1))
          atTop (nhds (G z)) :=
    (ae_restrict_iff' hRm).1 hlimR
  have hcover :
      (⋃ a : ℤ, ⋃ b : ℤ,
        (Ioc (a : ℝ) (a + 1 : ℝ) ×ˢ
          Ioc (b : ℝ) (b + 1 : ℝ))) = (univ : Set (ℝ × ℝ)) := by
    ext z
    simp only [mem_iUnion, mem_prod, mem_univ, iff_true]
    rcases exists_int_mem_Ioc z.1 with ⟨a, ha⟩
    rcases exists_int_mem_Ioc z.2 with ⟨b, hb⟩
    exact ⟨a, b, ha, hb⟩
  rw [← Measure.restrict_univ (μ := volume.prod volume), ← hcover,
    ae_restrict_iUnion_iff]
  intro a
  rw [ae_restrict_iUnion_iff]
  intro b
  let C : Set (ℝ × ℝ) :=
    Ioc (a : ℝ) (a + 1 : ℝ) ×ˢ Ioc (b : ℝ) (b + 1 : ℝ)
  have hCm : MeasurableSet C := measurableSet_Ioc.prod measurableSet_Ioc
  let T : ℝ × ℝ → ℝ × ℝ :=
    fun z => (z.1 - (a : ℝ), z.2 - (b : ℝ))
  have hmp :
      MeasurePreserving T (volume.prod volume) (volume.prod volume) := by
    have hprod :=
      (measurePreserving_add_right volume (-(a : ℝ))).prod
        (measurePreserving_add_right volume (-(b : ℝ)))
    convert hprod using 1
    funext z
    dsimp [T]
    congr <;> ring
  have htrans := hmp.quasiMeasurePreserving.ae hfull
  apply (ae_restrict_iff' hCm).2
  filter_upwards [htrans] with z hz hmem
  have hTmem : T z ∈ R := by
    dsimp [T, R]
    constructor
    · constructor <;> linarith [hmem.1.1, hmem.1.2]
    · constructor <;> linarith [hmem.2.1, hmem.2.2]
  have hzlim := hz hTmem
  have hseq :
      (fun k => dyadicSoftRepresentative p (ns k) (z.2, z.1)) =
        (fun k => dyadicSoftRepresentative p (ns k) ((T z).2, (T z).1)) := by
    funext k
    dsimp [T]
    exact dyadicSoftRepresentative_sub_ints hpper (ns k) a b z.2 z.1
  rw [hseq]
  convert hzlim using 1
  unfold periodizePlane
  rw [iocRepresentative_eq_sub_int hmem.1,
    iocRepresentative_eq_sub_int hmem.2]

/-- A subsequence of finite soft representatives has a measurable a.e. limit
on the swapped fundamental square. -/
lemma exists_measurable_fundamentalSquare_soft_limit
    {p : ℝ → ℝ} (hpper : Function.Periodic p 1)
    (hp : HasMeasurableDifferences p) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∃ G : ℝ × ℝ → ℝ, Measurable G ∧
        ∀ᵐ z ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod
          (volume.restrict (Ioc (0 : ℝ) 1))),
          Tendsto
            (fun k =>
              dyadicSoftRepresentative p (ns k) (z.2, z.1))
            atTop (nhds (G z)) := by
  let F : ℕ → ℝ × ℝ → ℝ :=
    fun n z => measurableDyadicSoftRepresentative p hp n (z.2, z.1)
  have hF : ∀ n, Measurable (F n) := by
    intro n
    exact (measurable_measurableDyadicSoftRepresentative hp n).comp
      (measurable_snd.prodMk measurable_fst)
  have hpair : ∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun nm : ℕ × ℕ =>
          ((volume.restrict (Ioc (0 : ℝ) 1)).prod
            (volume.restrict (Ioc (0 : ℝ) 1)))
            {z : ℝ × ℝ |
              ε ≤ dist (F nm.1 z) (F nm.2 z)})
        (atTop ×ˢ atTop) (nhds 0) := by
    intro ε hε
    exact tendsto_fundamentalSquare_pair_dist_dyadicSoftRepresentative
      hpper hp ε hε
  rcases exists_measurable_subseq_limit_of_pair_cauchy_in_measure
      F hF hpair with ⟨ns, hns, G, hG, hlim⟩
  have hEq : ∀ n : ℕ,
      ∀ᵐ z ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod
        (volume.restrict (Ioc (0 : ℝ) 1))),
        dyadicSoftRepresentative p n (z.2, z.1) =
          measurableDyadicSoftRepresentative p hp n (z.2, z.1) := by
    intro n
    have heq := ae_eq_measurableDyadicSoftRepresentative hp n
    have hmap :
        ∀ᵐ z ∂Measure.map Prod.swap (volume.prod volume),
          dyadicSoftRepresentative p n z =
            measurableDyadicSoftRepresentative p hp n z := by
      rw [Measure.prod_swap]
      exact heq
    have hpull := ae_of_ae_map measurable_swap.aemeasurable hmap
    rw [Measure.prod_restrict]
    exact ae_restrict_of_ae hpull
  have hall :
      ∀ᵐ z ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod
        (volume.restrict (Ioc (0 : ℝ) 1))),
        ∀ k : ℕ,
          dyadicSoftRepresentative p (ns k) (z.2, z.1) =
            measurableDyadicSoftRepresentative p hp (ns k) (z.2, z.1) := by
    rw [ae_all_iff]
    intro k
    exact hEq (ns k)
  refine ⟨ns, hns, G, hG, ?_⟩
  filter_upwards [hlim, hall] with z hz hzeq
  apply hz.congr'
  filter_upwards [] with k
  exact (hzeq k).symm

/-- Periodizing the fundamental-square limit gives one globally measurable
subsequential limit of the original finite representatives. -/
lemma exists_measurable_global_soft_limit
    {p : ℝ → ℝ} (hpper : Function.Periodic p 1)
    (hp : HasMeasurableDifferences p) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∃ G : ℝ × ℝ → ℝ, Measurable G ∧
        (∀ t : ℝ, Function.Periodic (fun x => G (x, t)) 1) ∧
        (∀ x : ℝ, Function.Periodic (fun t => G (x, t)) 1) ∧
        ∀ᵐ z ∂volume.prod volume,
          Tendsto
            (fun k => dyadicSoftRepresentative p (ns k) (z.2, z.1))
            atTop (nhds (G z)) := by
  rcases exists_measurable_fundamentalSquare_soft_limit hpper hp with
    ⟨ns, hns, G0, hG0, hlim0⟩
  let G : ℝ × ℝ → ℝ := periodizePlane G0
  refine ⟨ns, hns, G, measurable_periodizePlane hG0, ?_, ?_, ?_⟩
  · intro t
    exact periodizePlane_periodic_fst G0 t
  · intro x
    exact periodizePlane_periodic_snd G0 x
  · exact ae_tendsto_periodizePlane_of_fundamentalSquare hpper hlim0

/-- Reorder the preceding global limit back to the usual base and increment
coordinates. -/
lemma exists_measurable_global_soft_limit_original
    {p : ℝ → ℝ} (hpper : Function.Periodic p 1)
    (hp : HasMeasurableDifferences p) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∃ G : ℝ × ℝ → ℝ, Measurable G ∧
        (∀ t : ℝ, Function.Periodic (fun x => G (x, t)) 1) ∧
        (∀ x : ℝ, Function.Periodic (fun t => G (x, t)) 1) ∧
        ∀ᵐ z ∂volume.prod volume,
          Tendsto
            (fun k => dyadicSoftRepresentative p (ns k) z)
            atTop (nhds (G z)) := by
  rcases exists_measurable_global_soft_limit hpper hp with
    ⟨ns, hns, G0, hG0, hG0base, hG0increment, hlim0⟩
  let G : ℝ × ℝ → ℝ := fun z => G0 (z.2, z.1)
  have hG : Measurable G :=
    hG0.comp (measurable_snd.prodMk measurable_fst)
  have hGbase : ∀ t : ℝ, Function.Periodic (fun x => G (x, t)) 1 := by
    intro t
    exact hG0increment t
  have hGincrement : ∀ x : ℝ, Function.Periodic (fun t => G (x, t)) 1 := by
    intro x
    exact hG0base x
  have hmap :
      ∀ᵐ z ∂Measure.map Prod.swap (volume.prod volume),
        Tendsto
          (fun k => dyadicSoftRepresentative p (ns k) (z.2, z.1))
          atTop (nhds (G0 z)) := by
    rw [Measure.prod_swap]
    exact hlim0
  have hpull := ae_of_ae_map measurable_swap.aemeasurable hmap
  refine ⟨ns, hns, G, hG, hGbase, hGincrement, ?_⟩
  filter_upwards [hpull] with z hz
  simpa [G, Prod.swap] using hz

/-- Every dyadic base shift survives in any cofinal subsequential limit. -/
lemma dyadicSoft_subseq_limit_refined_shift
    {p : ℝ → ℝ} {G : ℝ × ℝ → ℝ} {ns : ℕ → ℕ}
    (hpper : Function.Periodic p 1) (hns : StrictMono ns)
    (hlim : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      Tendsto (fun k => dyadicSoftRepresentative p (ns k) z)
        atTop (nhds (G z)))
    (n : ℕ) (j : Fin (2 ^ n)) :
    ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      G (z.1 + dyadicShift n j, z.2) =
        G z + secondDifferenceKernel p (dyadicShift n j) z.1 z.2 := by
  let T : ℝ × ℝ → ℝ × ℝ :=
    fun z => (z.1 + dyadicShift n j, z.2)
  have hmp :
      MeasurePreserving T (volume.prod volume) (volume.prod volume) := by
    have hprod :=
      (measurePreserving_add_right volume (dyadicShift n j)).prod
        (MeasurePreserving.id (volume : Measure ℝ))
    convert hprod using 1
    rfl
  have hshift := hmp.quasiMeasurePreserving.ae hlim
  have hcofinal : Tendsto ns atTop atTop := hns.tendsto_atTop
  have hge : ∀ᶠ k in atTop, n ≤ ns k :=
    hcofinal (eventually_ge_atTop n)
  filter_upwards [hlim, hshift] with z hz hzshift
  have hseq :
      (fun k => dyadicSoftRepresentative p (ns k) (T z)) =ᶠ[atTop]
        (fun k => dyadicSoftRepresentative p (ns k) z +
          secondDifferenceKernel p (dyadicShift n j) z.1 z.2) := by
    filter_upwards [hge] with k hk
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hk
    rw [hm]
    exact dyadicSoftRepresentative_refined_shift hpper n m j z.1 z.2
  have hshiftRight :
      Tendsto
        (fun k => dyadicSoftRepresentative p (ns k) z +
          secondDifferenceKernel p (dyadicShift n j) z.1 z.2)
        atTop (nhds (G (T z))) :=
    hzshift.congr' hseq
  have hright :
      Tendsto
        (fun k => dyadicSoftRepresentative p (ns k) z +
          secondDifferenceKernel p (dyadicShift n j) z.1 z.2)
        atTop
        (nhds (G z +
          secondDifferenceKernel p (dyadicShift n j) z.1 z.2)) :=
    hz.add tendsto_const_nhds
  simpa [T] using tendsto_nhds_unique hshiftRight hright



open Filter MeasureTheory Set Function
open scoped Pointwise ENNReal

def dyadicRationalSet : Set ℝ :=
  Set.range (fun zn : ℤ × ℕ => (zn.1 : ℝ) / (2 : ℝ) ^ zn.2)

lemma dense_dyadicRationalSet : Dense dyadicRationalSet := by
  rw [Metric.dense_iff]
  intro x r hr
  have hpow :
      ∀ᶠ n : ℕ in atTop, 1 / r < (2 : ℝ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℝ))).eventually_gt_atTop
      (1 / r)
  rcases hpow.exists with ⟨n, hn⟩
  let m : ℤ := ⌊(2 : ℝ) ^ n * x⌋
  let y : ℝ := (m : ℝ) / (2 : ℝ) ^ n
  have hpowpos : 0 < (2 : ℝ) ^ n := by positivity
  have hy_le : y ≤ x := by
    dsimp [y, m]
    rw [div_le_iff₀ hpowpos]
    simpa [mul_comm] using Int.floor_le ((2 : ℝ) ^ n * x)
  have hx_lt : x < y + 1 / (2 : ℝ) ^ n := by
    dsimp [y, m]
    rw [← add_div]
    rw [lt_div_iff₀ hpowpos]
    simpa [mul_comm] using Int.lt_floor_add_one ((2 : ℝ) ^ n * x)
  have hinv : 1 / (2 : ℝ) ^ n < r := by
    rw [div_lt_iff₀ hpowpos]
    rw [div_lt_iff₀ hr] at hn
    simpa [mul_comm] using hn
  refine ⟨y, ?_, ⟨⟨m, n⟩, rfl⟩⟩
  rw [Metric.mem_ball, Real.dist_eq]
  have habs : |x - y| = x - y := abs_of_nonneg (sub_nonneg.mpr hy_le)
  rw [abs_sub_comm, habs]
  linarith

lemma denseRange_dyadicRational_unitAddCircle :
    DenseRange (fun zn : ℤ × ℕ =>
      (((zn.1 : ℝ) / (2 : ℝ) ^ zn.2 : ℝ) : UnitAddCircle)) := by
  have hmk : DenseRange (fun x : ℝ => (x : UnitAddCircle)) :=
    QuotientAddGroup.mk_surjective.denseRange
  have hD : DenseRange (fun zn : ℤ × ℕ =>
      (zn.1 : ℝ) / (2 : ℝ) ^ zn.2) := dense_dyadicRationalSet
  exact hmk.comp hD (AddCircle.continuous_mk' (1 : ℝ))

lemma exists_fin_coe_eq_dyadicRational (z : ℤ) (n : ℕ) :
    ∃ j : Fin (2 ^ n),
      (((z : ℝ) / (2 : ℝ) ^ n : ℝ) : UnitAddCircle) =
        ((dyadicShift n j : ℝ) : UnitAddCircle) := by
  let N : ℤ := (2 ^ n : ℕ)
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast (show 0 < 2 ^ n by positivity)
  have hNne : N ≠ 0 := hNpos.ne'
  have hmodnonneg : 0 ≤ z % N := Int.emod_nonneg z hNne
  have hmodlt : z % N < N := by
    have h := Int.emod_lt z hNne
    simpa [N] using h
  let j : Fin (2 ^ n) := ⟨(z % N).toNat, by
    have hzcast : ((z % N).toNat : ℤ) = z % N :=
      Int.toNat_of_nonneg hmodnonneg
    have hlt' : ((z % N).toNat : ℤ) < N := by
      rw [hzcast]
      exact hmodlt
    dsimp [N] at hlt'
    exact_mod_cast hlt'⟩
  refine ⟨j, ?_⟩
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  rw [AddSubgroup.mem_zmultiples_iff]
  refine ⟨z / N, ?_⟩
  have hdecomp := Int.emod_add_mul_ediv z N
  have hjcast : ((j : ℕ) : ℤ) = z % N := by
    dsimp [j]
    exact Int.toNat_of_nonneg hmodnonneg
  simp only [zsmul_eq_mul, mul_one]
  change ((z / N : ℤ) : ℝ) =
    (z : ℝ) / (2 : ℝ) ^ n - dyadicShift n j
  unfold dyadicShift
  rw [show (2 : ℝ) ^ n = (N : ℝ) by
    dsimp [N]
    norm_num]
  rw [show (j : ℝ) = (z % N : ℤ) by exact_mod_cast hjcast]
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hNne
  field_simp
  have hq : z / N * N = z - z % N := by
    rw [mul_comm]
    omega
  exact_mod_cast hq

lemma denseRange_finDyadic_unitAddCircle :
    DenseRange (fun ij : Sigma fun n : ℕ => Fin (2 ^ n) =>
      ((dyadicShift ij.1 ij.2 : ℝ) : UnitAddCircle)) := by
  apply Dense.mono _ denseRange_dyadicRational_unitAddCircle
  rintro _ ⟨⟨z, n⟩, rfl⟩
  rcases exists_fin_coe_eq_dyadicRational z n with ⟨j, hj⟩
  exact ⟨⟨n, j⟩, hj.symm⟩

lemma periodic_lift_invariant_dyadic
    {u : ℝ → ℝ} (hu : Function.Periodic u 1)
    (hinv : ∀ n : ℕ, ∀ j : Fin (2 ^ n),
      ∀ᵐ x ∂volume, u (x + dyadicShift n j) = u x)
    (n : ℕ) (j : Fin (2 ^ n)) :
    hu.lift ∘ (· + ((dyadicShift n j : ℝ) : UnitAddCircle))
      =ᵐ[(volume : Measure UnitAddCircle)] hu.lift := by
  have hsub : ∀ᵐ x : Ioc (0 : ℝ) (0 + 1) ∂(Measure.comap Subtype.val volume),
      u ((x : ℝ) + dyadicShift n j) = u x := by
    exact (ae_restrict_iff_subtype measurableSet_Ioc).1
      (ae_restrict_of_ae (hinv n j))
  have hcircle := (AddCircle.measurePreserving_equivIoc 1).quasiMeasurePreserving.ae hsub
  filter_upwards [hcircle] with y hy
  let x : Ioc (0 : ℝ) (0 + 1) := AddCircle.equivIoc 1 0 y
  have hxy : (x : UnitAddCircle) = y := AddCircle.coe_equivIoc
  dsimp
  rw [← hxy, ← AddCircle.coe_add, hu.lift_coe]
  exact hy

lemma periodic_lift_level_const_of_dyadic_invariant
    {u : ℝ → ℝ} (hu : Function.Periodic u 1)
    (hum : AEMeasurable u volume)
    (hinv : ∀ n : ℕ, ∀ j : Fin (2 ^ n),
      ∀ᵐ x ∂volume, u (x + dyadicShift n j) = u x)
    (c : ℚ) :
    Filter.EventuallyConst
      {y : UnitAddCircle | hu.lift y < (c : ℝ)}
      (ae (volume : Measure UnitAddCircle)) := by
  let U : UnitAddCircle → ℝ := hu.lift
  let S : Set UnitAddCircle := {y | U y < (c : ℝ)}
  have hUmeas : AEMeasurable U (volume : Measure UnitAddCircle) :=
    aemeasurable_periodic_lift hu hum
  have hS : NullMeasurableSet S (volume : Measure UnitAddCircle) :=
    nullMeasurableSet_lt hUmeas aemeasurable_const
  apply aeconst_of_dense_setOfPred_preimage_vadd_ae
    (M := UnitAddCircle) (X := UnitAddCircle) hS
  apply Dense.mono _ denseRange_finDyadic_unitAddCircle
  rintro _ ⟨ij, rfl⟩
  have hUq := periodic_lift_invariant_dyadic hu hinv ij.1 ij.2
  filter_upwards [hUq] with y hy
  change (((dyadicShift ij.1 ij.2 : ℝ) : UnitAddCircle) + y ∈ S) = (y ∈ S)
  dsimp [S, U]
  simpa [Function.comp_def, add_comm] using
    congrArg (fun z : ℝ => z < (c : ℝ)) hy

lemma periodic_lift_invariant_sqrt_two_of_dyadic_invariant
    {u : ℝ → ℝ} (hu : Function.Periodic u 1)
    (hum : AEMeasurable u volume)
    (hinv : ∀ n : ℕ, ∀ j : Fin (2 ^ n),
      ∀ᵐ x ∂volume, u (x + dyadicShift n j) = u x) :
    hu.lift ∘ (· + ((Real.sqrt 2 : ℝ) : UnitAddCircle))
      =ᵐ[(volume : Measure UnitAddCircle)] hu.lift := by
  have hall :
      ∀ᵐ y ∂(volume : Measure UnitAddCircle), ∀ c : ℚ,
        (hu.lift (y + ((Real.sqrt 2 : ℝ) : UnitAddCircle)) < (c : ℝ)) ↔
          (hu.lift y < (c : ℝ)) := by
    rw [ae_all_iff]
    intro c
    let S : Set UnitAddCircle := {y | hu.lift y < (c : ℝ)}
    have hconst := periodic_lift_level_const_of_dyadic_invariant hu hum hinv c
    let a : UnitAddCircle := ((Real.sqrt 2 : ℝ) : UnitAddCircle)
    have hqmp :
        Measure.QuasiMeasurePreserving (fun y : UnitAddCircle => a + y)
          (volume : Measure UnitAddCircle) volume :=
      quasiMeasurePreserving_add_left (G := UnitAddCircle) volume a
    rcases Filter.eventuallyConst_set.mp hconst with hmem | hnot
    · have hshift := hqmp.ae hmem
      filter_upwards [hshift, hmem] with y hy hs
      simpa [S, a, add_comm] using Iff.intro (fun _ => hs) (fun _ => hy)
    · have hshift := hqmp.ae hnot
      filter_upwards [hshift, hnot] with y hy hs
      simpa [S, a, add_comm] using Iff.intro (fun h => (hy h).elim) (fun h => (hs h).elim)
  filter_upwards [hall] with y hy
  dsimp
  apply le_antisymm
  · by_contra hnot
    have hlt : hu.lift y < hu.lift (y + ((Real.sqrt 2 : ℝ) : UnitAddCircle)) :=
      lt_of_not_ge hnot
    rcases exists_rat_btwn hlt with ⟨q, hq1, hq2⟩
    have hiff := hy q
    have : hu.lift (y + ((Real.sqrt 2 : ℝ) : UnitAddCircle)) < (q : ℝ) :=
      hiff.mpr hq1
    linarith
  · by_contra hnot
    have hlt : hu.lift (y + ((Real.sqrt 2 : ℝ) : UnitAddCircle)) < hu.lift y :=
      lt_of_not_ge hnot
    rcases exists_rat_btwn hlt with ⟨q, hq1, hq2⟩
    have hiff := hy q
    have : hu.lift y < (q : ℝ) := hiff.mp hq1
    linarith

lemma periodic_invariant_ae_const_of_dyadic_invariant
    {u : ℝ → ℝ} (hu : Function.Periodic u 1)
    (hum : AEMeasurable u volume)
    (hinv : ∀ n : ℕ, ∀ j : Fin (2 ^ n),
      ∀ᵐ x ∂volume, u (x + dyadicShift n j) = u x) :
    ∃ c : ℝ, ∀ᵐ x ∂volume, u x = c := by
  have hUalpha :=
    periodic_lift_invariant_sqrt_two_of_dyadic_invariant hu hum hinv
  have hmp := UnitAddCircle.measurePreserving_mk 0
  have hpre :
      ∀ᵐ x : ℝ ∂((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)),
        hu.lift ((x : UnitAddCircle) + ((Real.sqrt 2 : ℝ) : UnitAddCircle)) =
          hu.lift (x : UnitAddCircle) := by
    simpa [Function.comp_def] using hmp.quasiMeasurePreserving.ae hUalpha
  have hzeroIoc :
      ∀ᵐ x : ℝ ∂((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)),
        u (x + Real.sqrt 2) - u x = 0 := by
    filter_upwards [hpre, ae_restrict_mem measurableSet_Ioc] with x hx hxm
    rw [← AddCircle.coe_add, hu.lift_coe, hu.lift_coe] at hx
    linarith
  have hper :
      Function.Periodic (fun x : ℝ => u (x + Real.sqrt 2) - u x) 1 := by
    intro x
    dsimp
    rw [show x + 1 + Real.sqrt 2 = (x + Real.sqrt 2) + 1 by ring, hu, hu]
  have hzero :
      ∀ᵐ x : ℝ ∂volume, u (x + Real.sqrt 2) - u x = 0 :=
    periodic_ae_zero_of_Ioc hper hzeroIoc
  apply periodic_invariant_ae_const hu hum
  filter_upwards [hzero] with x hx
  linarith



open Filter MeasureTheory Set Function
open scoped Pointwise ENNReal

/-- A joint measurable representative of all difference sections modulo one
scalar constant in each section. -/
def HasJointDifferenceRepresentativeModuloConstants (f : ℝ → ℝ) : Prop :=
  ∃ G : ℝ → ℝ → ℝ,
    Measurable (Function.uncurry G) ∧
      ∀ᵐ t ∂volume, ∃ c : ℝ,
        ∀ᵐ x ∂volume, differenceKernel f x t = G x t + c

lemma periodic_hasJointDifferenceRepresentativeModuloConstants
    {p : ℝ → ℝ} (hpper : Function.Periodic p 1)
    (hp : HasMeasurableDifferences p) :
    HasJointDifferenceRepresentativeModuloConstants p := by
  rcases exists_measurable_global_soft_limit_original hpper hp with
    ⟨ns, hns, G0, hG0, hGbase, hGincrement, hlim⟩
  let G : ℝ → ℝ → ℝ := fun x t => G0 (x, t)
  have hG : Measurable (Function.uncurry G) := by
    exact hG0
  have hshift :
      ∀ᵐ t ∂volume, ∀ n : ℕ, ∀ j : Fin (2 ^ n),
        ∀ᵐ x ∂volume,
          G0 (x + dyadicShift n j, t) =
            G0 (x, t) +
              secondDifferenceKernel p (dyadicShift n j) x t := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro j
    have h := dyadicSoft_subseq_limit_refined_shift hpper hns hlim n j
    have hmap :
        ∀ᵐ z ∂Measure.map Prod.swap (volume.prod volume),
          G0 (z.1 + dyadicShift n j, z.2) =
            G0 z + secondDifferenceKernel p (dyadicShift n j) z.1 z.2 := by
      rw [Measure.prod_swap]
      exact h
    have hpull := ae_of_ae_map measurable_swap.aemeasurable hmap
    simpa [Prod.swap] using Measure.ae_ae_of_ae_prod hpull
  refine ⟨G, hG, ?_⟩
  filter_upwards [hshift] with t ht
  let u : ℝ → ℝ := fun x => differenceKernel p x t - G0 (x, t)
  have huper : Function.Periodic u 1 := by
    intro x
    dsimp [u]
    rw [show differenceKernel p (x + 1) t = differenceKernel p x t from
        differenceKernel_periodic_base hpper t x,
      show G0 (x + 1, t) = G0 (x, t) from hGbase t x]
  have humeas : AEMeasurable u volume := by
    have hsection : AEMeasurable (fun x : ℝ => G0 (x, t)) volume :=
      (hG0.comp (measurable_id.prodMk measurable_const)).aemeasurable
    exact (hp t).sub hsection
  have huinv :
      ∀ n : ℕ, ∀ j : Fin (2 ^ n),
        ∀ᵐ x ∂volume, u (x + dyadicShift n j) = u x := by
    intro n j
    filter_upwards [ht n j] with x hx
    dsimp [u]
    rw [hx]
    unfold secondDifferenceKernel
    ring
  rcases periodic_invariant_ae_const_of_dyadic_invariant huper humeas huinv with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  dsimp [u] at hx
  dsimp [G]
  linarith



open Filter MeasureTheory Set Function
open scoped Pointwise ENNReal

/-- A choice of the scalar missing from a joint quotient representative. -/
noncomputable def quotientSectionConstant
    (f : ℝ → ℝ) (G : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  by
    classical
    exact if h : ∃ c : ℝ, ∀ᵐ x ∂volume, differenceKernel f x t = G x t + c
      then h.choose
      else 0

lemma quotientSectionConstant_spec
    {f : ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    {t : ℝ}
    (ht : ∃ c : ℝ, ∀ᵐ x ∂volume, differenceKernel f x t = G x t + c) :
    ∀ᵐ x ∂volume,
      differenceKernel f x t = G x t + quotientSectionConstant f G t := by
  classical
  unfold quotientSectionConstant
  simp only [dif_pos ht]
  exact ht.choose_spec

/-- If the scalar part of a quotient representative has continuous
differences, de Bruijn's theorem splits it into a continuous part and an
additive part; the continuous part can be folded back into the joint
representative. -/
lemma measurableDecomposition_of_moduloConstants_continuous_scalar
    (f : ℝ → ℝ) (G : ℝ → ℝ → ℝ) (c : ℝ → ℝ)
    (hG : Measurable (Function.uncurry G))
    (hrel : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
      differenceKernel f x t = G x t + c t)
    (hc : ∀ h : ℝ, Continuous fun t : ℝ => c (t + h) - c t) :
    HasMeasurableDecomposition f := by
  rcases Erdos907.erdos907_of_all_h c hc with
    ⟨b, H, hb, hH, hcdecomp⟩
  have hH' : IsAdditiveFn H := by
    intro x y
    exact hH x y
  let G' : ℝ → ℝ → ℝ := fun x t => G x t + b t
  have hG' : Measurable (Function.uncurry G') := by
    exact hG.add (hb.measurable.comp measurable_snd)
  have hrel' :
      ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
        differenceKernel (fun y => f y - H y) x t = G' x t := by
    filter_upwards [hrel] with t ht
    filter_upwards [ht] with x hx
    dsimp [G']
    unfold differenceKernel at hx
    change (f (x + t) - H (x + t)) - (f x - H x) = G x t + b t
    rw [hH' x t]
    have hct := hcdecomp t
    linarith
  exact measurableDecomposition_of_additive_jointRepresentative
    f H hH' G' hG' hrel'

/-- The exact algebraic interface needed from the scalar localization:
an a.e. measurable scalar part plus one additive scalar part can be folded
back into a joint quotient representative. -/
lemma measurableDecomposition_of_moduloConstants_scalar_split
    (f : ℝ → ℝ) (G : ℝ → ℝ → ℝ) (c : ℝ → ℝ)
    (hG : Measurable (Function.uncurry G))
    (hrel : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
      differenceKernel f x t = G x t + c t)
    (hsplit : ∃ b H : ℝ → ℝ,
      AEMeasurable b volume ∧ IsAdditiveFn H ∧
        ∀ᵐ t ∂volume, c t = b t + H t) :
    HasMeasurableDecomposition f := by
  rcases hsplit with ⟨b, H, hb, hH, hcb⟩
  let b0 : ℝ → ℝ := hb.mk b
  have hb0 : Measurable b0 := hb.measurable_mk
  have hbb0 : ∀ᵐ t ∂volume, b t = b0 t := hb.ae_eq_mk
  let G' : ℝ → ℝ → ℝ := fun x t => G x t + b0 t
  have hG' : Measurable (Function.uncurry G') := by
    exact hG.add (hb0.comp measurable_snd)
  have hrel' :
      ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
        differenceKernel (fun y => f y - H y) x t = G' x t := by
    filter_upwards [hrel, hcb, hbb0] with t ht hct hbt
    filter_upwards [ht] with x hx
    dsimp [G']
    unfold differenceKernel at hx
    change (f (x + t) - H (x + t)) - (f x - H x) = G x t + b0 t
    rw [hH x t]
    linarith
  exact measurableDecomposition_of_additive_jointRepresentative
    f H hH G' hG' hrel'

/-- A null-increment function whose two-variable difference is jointly
measurable is almost everywhere constant.  The pathological residual in the
weak theorem survives only because its exceptional sets cannot in general be
assembled into a measurable subset of the product. -/
lemma ae_const_of_nullIncrements_of_joint_aemeasurable
    {s : ℝ → ℝ}
    (hs : HasNullIncrements s)
    (hjoint : AEMeasurable
      (fun p : ℝ × ℝ => differenceKernel s p.1 p.2)
      (volume.prod volume)) :
    ∃ c : ℝ, ∀ᵐ x ∂volume, s x = c := by
  let u : ℝ × ℝ → ℝ :=
    hjoint.mk (fun p : ℝ × ℝ => differenceKernel s p.1 p.2)
  have hu : Measurable u := hjoint.measurable_mk
  have heq :
      ∀ᵐ p ∂volume.prod volume,
        differenceKernel s p.1 p.2 = u p := hjoint.ae_eq_mk
  have heqswap :
      ∀ᵐ p ∂volume.prod volume,
        differenceKernel s p.2 p.1 = u (p.2, p.1) := by
    have hmap :
        ∀ᵐ p ∂Measure.map Prod.swap (volume.prod volume),
          differenceKernel s p.1 p.2 = u p := by
      rw [Measure.prod_swap]
      exact heq
    simpa [Prod.swap] using
      (ae_of_ae_map measurable_swap.aemeasurable hmap)
  let v : ℝ × ℝ → ℝ := fun p => u (p.2, p.1)
  have hv : Measurable v :=
    hu.comp (measurable_snd.prodMk measurable_fst)
  have hzero :
      ∀ᵐ p ∂volume.prod volume, v p = 0 := by
    have hset : MeasurableSet {p : ℝ × ℝ | v p = 0} :=
      measurableSet_eq_fun hv measurable_const
    apply (Measure.ae_prod_iff_ae_ae hset).2
    filter_upwards [Measure.ae_ae_of_ae_prod heqswap] with t ht
    filter_upwards [hs t, ht] with x hx he
    change u (x, t) = 0
    rw [← he]
    exact hx
  have hrawswap :
      ∀ᵐ p ∂volume.prod volume,
        differenceKernel s p.2 p.1 = 0 := by
    filter_upwards [heqswap, hzero] with p hp hz
    change u (p.2, p.1) = 0 at hz
    rw [hp, hz]
  have hraw :
      ∀ᵐ p ∂volume.prod volume,
        differenceKernel s p.1 p.2 = 0 := by
    have hmap :
        ∀ᵐ p ∂Measure.map Prod.swap (volume.prod volume),
          differenceKernel s p.2 p.1 = 0 := by
      rw [Measure.prod_swap]
      exact hrawswap
    have hpull := ae_of_ae_map measurable_swap.aemeasurable hmap
    simpa [Prod.swap] using hpull
  have hsections :
      ∀ᵐ x ∂volume, ∀ᵐ t ∂volume,
        differenceKernel s x t = 0 :=
    Measure.ae_ae_of_ae_prod hraw
  rcases hsections.exists with ⟨x0, hx0⟩
  refine ⟨s x0, ?_⟩
  have htrans := ae_translate hx0 (-x0)
  filter_upwards [htrans] with y hy
  unfold differenceKernel at hy
  have harg : x0 + (y + -x0) = y := by ring
  rw [harg] at hy
  linarith

/-- The quotient theorem reduces the periodic measurable problem to the
regularity of its scalar section constants. -/
lemma periodic_measurableDecomposition_of_continuous_scalar_constants
    {p : ℝ → ℝ} (hpper : Function.Periodic p 1)
    (hp : HasMeasurableDifferences p)
    (hc : ∀ G : ℝ → ℝ → ℝ,
      Measurable (Function.uncurry G) →
      (∀ᵐ t ∂volume, ∃ c : ℝ,
        ∀ᵐ x ∂volume, differenceKernel p x t = G x t + c) →
      ∀ h : ℝ, Continuous fun t : ℝ =>
        quotientSectionConstant p G (t + h) - quotientSectionConstant p G t) :
    HasMeasurableDecomposition p := by
  rcases periodic_hasJointDifferenceRepresentativeModuloConstants hpper hp with
    ⟨G, hG, hrel⟩
  apply measurableDecomposition_of_moduloConstants_continuous_scalar
    p G (quotientSectionConstant p G) hG
  · filter_upwards [hrel] with t ht
    exact quotientSectionConstant_spec ht
  · exact hc G hG hrel



open Filter MeasureTheory Set Function
open scoped Pointwise ENNReal



open Filter MeasureTheory Set Function
open scoped Pointwise ENNReal

/-- The ordinary Cauchy defect of a scalar function. -/
def cauchyDefect (c : ℝ → ℝ) (s t : ℝ) : ℝ :=
  c (s + t) - c s - c t

/-- The bounded integral used to recover an a.e.-constant real section. -/
noncomputable def arctanSectionIntegral
    (F : ℝ → (ℝ × ℝ) → ℝ) (p : ℝ × ℝ) : ℝ :=
  (∫⁻ x in Ioc (0 : ℝ) 1,
    ENNReal.ofReal (Real.arctan (F x p) + Real.pi / 2) ∂volume).toReal

/-- A bounded integral functional that recovers an a.e.-constant real
section while remaining measurable in all other parameters. -/
noncomputable def arctanSectionValue
    (F : ℝ → (ℝ × ℝ) → ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.tan (arctanSectionIntegral F p - Real.pi / 2)

lemma aemeasurable_arctanSectionIntegrand
    {F : ℝ → (ℝ × ℝ) → ℝ}
    (hF : Measurable (Function.uncurry F)) :
    AEMeasurable
      (fun p : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (Real.arctan (F p.1 p.2) + Real.pi / 2))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod
        (volume.prod volume)) := by
  have hFa :
      AEMeasurable
        (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2)
        ((volume.restrict (Ioc (0 : ℝ) 1)).prod
          (volume.prod volume)) :=
    hF.aemeasurable
  exact ((Real.continuous_arctan.aemeasurable.comp_aemeasurable hFa).add
      aemeasurable_const).ennreal_ofReal

lemma aemeasurable_arctanSectionIntegral'
    {F : ℝ → (ℝ × ℝ) → ℝ}
    (hF : Measurable (Function.uncurry F)) :
    AEMeasurable (arctanSectionIntegral F) (volume.prod volume) := by
  unfold arctanSectionIntegral
  apply AEMeasurable.ennreal_toReal
  exact
    AEMeasurable.lintegral_prod_left'
      (μ := volume.restrict (Ioc (0 : ℝ) 1))
      (ν := volume.prod volume)
      (aemeasurable_arctanSectionIntegrand hF)

lemma aemeasurable_arctanSectionValue
    {F : ℝ → (ℝ × ℝ) → ℝ}
    (hF : Measurable (Function.uncurry F)) :
    AEMeasurable (arctanSectionValue F) (volume.prod volume) := by
  unfold arctanSectionValue
  have hint := aemeasurable_arctanSectionIntegral' hF
  have harg :
      AEMeasurable
        (fun p : ℝ × ℝ => arctanSectionIntegral F p - Real.pi / 2)
        (volume.prod volume) :=
    hint.sub aemeasurable_const
  have htan : Measurable (Real.tan : ℝ → ℝ) := by
    rw [show (Real.tan : ℝ → ℝ) =
        fun x : ℝ => Real.sin x / Real.cos x by
      funext x
      exact Real.tan_eq_sin_div_cos x]
    exact Real.measurable_sin.div Real.measurable_cos
  exact htan.comp_aemeasurable harg

lemma arctanSectionValue_eq_of_ae_const
    {F : ℝ → (ℝ × ℝ) → ℝ} {p : ℝ × ℝ} {a : ℝ}
    (hF : ∀ᵐ x ∂volume, F x p = a) :
    arctanSectionValue F p = a := by
  unfold arctanSectionValue arctanSectionIntegral
  have hrest :
      ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
        ENNReal.ofReal (Real.arctan (F x p) + Real.pi / 2) =
          ENNReal.ofReal (Real.arctan a + Real.pi / 2) := by
    filter_upwards [ae_restrict_of_ae hF] with x hx
    rw [hx]
  rw [lintegral_congr_ae hrest]
  have hpos : 0 ≤ Real.arctan a + Real.pi / 2 := by
    linarith [le_of_lt (Real.neg_pi_div_two_lt_arctan a)]
  simp [hpos]

/-- The measurable expression forced by the cocycle after a difference
section is represented modulo a scalar. -/
def quotientCocycleExpression
    (G : ℝ → ℝ → ℝ) (x : ℝ) (p : ℝ × ℝ) : ℝ :=
  G (x + p.1) p.2 + G x p.1 - G x (p.1 + p.2)

lemma measurable_quotientCocycleExpression
    {G : ℝ → ℝ → ℝ}
    (hG : Measurable (Function.uncurry G)) :
    Measurable (Function.uncurry (quotientCocycleExpression G)) := by
  let hx : ℝ × (ℝ × ℝ) → ℝ := fun p => p.1
  let hs : ℝ × (ℝ × ℝ) → ℝ := fun p => p.2.1
  let ht : ℝ × (ℝ × ℝ) → ℝ := fun p => p.2.2
  change Measurable (fun p : ℝ × (ℝ × ℝ) =>
    G (p.1 + p.2.1) p.2.2 + G p.1 p.2.1 - G p.1 (p.2.1 + p.2.2))
  exact
    ((hG.comp ((measurable_fst.add measurable_snd.fst).prodMk
      measurable_snd.snd)).add
      (hG.comp (measurable_fst.prodMk measurable_snd.fst))).sub
        (hG.comp (measurable_fst.prodMk
          (measurable_snd.fst.add measurable_snd.snd)))

/-- The scalar constants in a joint quotient representative have a jointly
a.e. measurable Cauchy defect.  The section-value functional avoids any
Fubini reordering of the potentially nonmeasurable original kernel. -/
lemma cauchyDefect_aemeasurable_of_moduloConstants
    (f : ℝ → ℝ) (G : ℝ → ℝ → ℝ) (c : ℝ → ℝ)
    (hG : Measurable (Function.uncurry G))
    (hrel : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
      differenceKernel f x t = G x t + c t) :
    ∃ d : ℝ → ℝ → ℝ,
      AEMeasurable (Function.uncurry d) (volume.prod volume) ∧
        ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
          d s t = cauchyDefect c s t := by
  have hadd :
      Measure.QuasiMeasurePreserving
        (fun p : ℝ × ℝ => p.1 + p.2) (volume.prod volume) volume := by
    have hprod :
        MeasurePreserving (fun p : ℝ × ℝ => (p.1, p.1 + p.2))
          (volume.prod volume) (volume.prod volume) :=
      measurePreserving_prod_add volume volume
    exact Measure.quasiMeasurePreserving_snd.comp hprod.quasiMeasurePreserving
  have hsumProd :
      ∀ᵐ p : ℝ × ℝ ∂volume.prod volume,
        ∀ᵐ x ∂volume,
          differenceKernel f x (p.1 + p.2) =
            G x (p.1 + p.2) + c (p.1 + p.2) :=
    hadd.ae hrel
  have hsum :
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
        ∀ᵐ x ∂volume,
          differenceKernel f x (s + t) =
            G x (s + t) + c (s + t) :=
    Measure.ae_ae_of_ae_prod hsumProd
  have hgood :
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
        ∀ᵐ x ∂volume,
          quotientCocycleExpression G x (s, t) =
            cauchyDefect c s t := by
    filter_upwards [hrel, hsum] with s hs hsum_s
    filter_upwards [hrel, hsum_s] with t ht hsum_st
    have htshift := ae_translate ht s
    filter_upwards [hs, hsum_st, htshift] with x hxs hxst hxt
    unfold quotientCocycleExpression cauchyDefect
    have hcoc := differenceKernel_cocycle f x s t
    rw [hxst, hxt, hxs] at hcoc
    linarith
  let F : ℝ → (ℝ × ℝ) → ℝ := quotientCocycleExpression G
  have hF : Measurable (Function.uncurry F) :=
    measurable_quotientCocycleExpression hG
  have hvalue :
      AEMeasurable (arctanSectionValue F) (volume.prod volume) :=
    aemeasurable_arctanSectionValue hF
  let d : ℝ → ℝ → ℝ := fun s t => arctanSectionValue F (s, t)
  refine ⟨d, ?_, ?_⟩
  · exact hvalue
  · filter_upwards [hgood] with s hs
    filter_upwards [hs] with t hst
    exact arctanSectionValue_eq_of_ae_const hst

/-- A full-measure set of measurable increments generates every increment,
so section measurability on that set already gives section measurability
everywhere. -/
lemma hasMeasurableDifferences_of_ae_good_increments
    {c : ℝ → ℝ} {Z : Set ℝ}
    (hZ : ∀ᵐ z ∂volume, z ∈ Z)
    (hgood : ∀ z ∈ Z,
      AEMeasurable (fun x : ℝ => differenceKernel c x z) volume) :
    HasMeasurableDifferences c := by
  intro h
  rcases fullMeasure_add_self hZ h with ⟨u, hu, v, hv, rfl⟩
  have hu' := hgood u hu
  have hv' := hgood v hv
  have hvshift :
      AEMeasurable
        (fun x : ℝ => differenceKernel c (x + u) v) volume :=
    hv'.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume u).quasiMeasurePreserving
  convert hvshift.add hu' using 1
  funext x
  unfold differenceKernel
  change c (x + (u + v)) - c x =
    (c (x + u + v) - c (x + u)) + (c (x + u) - c x)
  congr 2 <;> ring

/-- The quotient constants themselves again have measurable differences;
the new information is that their Cauchy defects have one jointly
measurable representative on an iterated full-measure set. -/
lemma quotientSectionConstant_hasMeasurableDifferences
    (f : ℝ → ℝ) (G : ℝ → ℝ → ℝ) (c : ℝ → ℝ)
    (hG : Measurable (Function.uncurry G))
    (hrel : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
      differenceKernel f x t = G x t + c t) :
    HasMeasurableDifferences c := by
  rcases cauchyDefect_aemeasurable_of_moduloConstants f G c hG hrel with
    ⟨d, hd, hdc⟩
  have hdsec :
      ∀ᵐ z ∂volume,
        AEMeasurable (fun t : ℝ => d z t) volume :=
    hd.aestronglyMeasurable.prodMk_left.mono fun _ hz => hz.aemeasurable
  let Z : Set ℝ :=
    {z | (∀ᵐ t ∂volume, d z t = cauchyDefect c z t) ∧
      AEMeasurable (fun t : ℝ => d z t) volume}
  have hZ : ∀ᵐ z ∂volume, z ∈ Z := hdc.and hdsec
  apply hasMeasurableDifferences_of_ae_good_increments hZ
  intro z hz
  have hmeas :
      AEMeasurable (fun t : ℝ => d z t + c z) volume :=
    hz.2.add aemeasurable_const
  apply hmeas.congr
  filter_upwards [hz.1] with t ht
  unfold differenceKernel
  unfold cauchyDefect at ht
  rw [ht]
  ring

/-- One-parameter version of the bounded section-value selector. -/
noncomputable def arctanRowIntegral (D : ℝ → ℝ → ℝ) (s : ℝ) : ℝ :=
  (∫⁻ t in Ioc (0 : ℝ) 1,
    ENNReal.ofReal (Real.arctan (D s t) + Real.pi / 2) ∂volume).toReal

noncomputable def arctanRowValue (D : ℝ → ℝ → ℝ) (s : ℝ) : ℝ :=
  Real.tan (arctanRowIntegral D s - Real.pi / 2)

lemma measurable_arctanRowIntegrand
    {D : ℝ → ℝ → ℝ}
    (hD : Measurable (Function.uncurry D)) :
    Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Real.arctan (D p.1 p.2) + Real.pi / 2)) := by
  exact ((Real.continuous_arctan.measurable.comp hD).add
    measurable_const).ennreal_ofReal

lemma measurable_arctanRowIntegral
    {D : ℝ → ℝ → ℝ}
    (hD : Measurable (Function.uncurry D)) :
    Measurable (arctanRowIntegral D) := by
  unfold arctanRowIntegral
  apply Measurable.ennreal_toReal
  exact (measurable_arctanRowIntegrand hD).lintegral_prod_right'

lemma measurable_real_tan : Measurable (Real.tan : ℝ → ℝ) := by
  rw [show (Real.tan : ℝ → ℝ) =
      fun x : ℝ => Real.sin x / Real.cos x by
    funext x
    exact Real.tan_eq_sin_div_cos x]
  exact Real.measurable_sin.div Real.measurable_cos

lemma measurable_arctanRowValue
    {D : ℝ → ℝ → ℝ}
    (hD : Measurable (Function.uncurry D)) :
    Measurable (arctanRowValue D) := by
  unfold arctanRowValue
  exact measurable_real_tan.comp
    ((measurable_arctanRowIntegral hD).sub measurable_const)

lemma arctanRowValue_eq_of_ae_const
    {D : ℝ → ℝ → ℝ} {s a : ℝ}
    (hD : ∀ᵐ t ∂volume, D s t = a) :
    arctanRowValue D s = a := by
  unfold arctanRowValue arctanRowIntegral
  have hrest :
      ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
        ENNReal.ofReal (Real.arctan (D s t) + Real.pi / 2) =
          ENNReal.ofReal (Real.arctan a + Real.pi / 2) := by
    filter_upwards [ae_restrict_of_ae hD] with t ht
    rw [ht]
  rw [lintegral_congr_ae hrest]
  have hpos : 0 ≤ Real.arctan a + Real.pi / 2 := by
    linarith [le_of_lt (Real.neg_pi_div_two_lt_arctan a)]
  simp [hpos]

/-- A scalar Cauchy defect has a jointly measurable representative on an
iterated full-measure set.  This is exactly the orientation produced by the
quotient section selector without applying an illicit Fubini swap to the
original nonmeasurable function. -/
def HasNestedMeasurableCauchyDefect (c : ℝ → ℝ) : Prop :=
  ∃ d : ℝ → ℝ → ℝ,
    AEMeasurable (Function.uncurry d) (volume.prod volume) ∧
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
        d s t = cauchyDefect c s t

lemma hasNestedMeasurableCauchyDefect_of_moduloConstants
    (f : ℝ → ℝ) (G : ℝ → ℝ → ℝ) (c : ℝ → ℝ)
    (hG : Measurable (Function.uncurry G))
    (hrel : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
      differenceKernel f x t = G x t + c t) :
    HasNestedMeasurableCauchyDefect c :=
  cauchyDefect_aemeasurable_of_moduloConstants f G c hG hrel

lemma cauchyDefect_aemeasurable_of_aemeasurable
    {g : ℝ → ℝ} (hg : AEMeasurable g volume) :
    AEMeasurable
      (fun p : ℝ × ℝ => cauchyDefect g p.1 p.2)
      (volume.prod volume) := by
  let g0 : ℝ → ℝ := hg.mk g
  have hg0 : Measurable g0 := hg.measurable_mk
  have hgeq : ∀ᵐ x ∂volume, g x = g0 x := hg.ae_eq_mk
  have hsum :
      ∀ᵐ p : ℝ × ℝ ∂volume.prod volume,
        g (p.1 + p.2) = g0 (p.1 + p.2) := by
    have hadd :
        Measure.QuasiMeasurePreserving
          (fun p : ℝ × ℝ => p.1 + p.2) (volume.prod volume) volume := by
      have hprod :
          MeasurePreserving (fun p : ℝ × ℝ => (p.1, p.1 + p.2))
            (volume.prod volume) (volume.prod volume) :=
        measurePreserving_prod_add volume volume
      exact Measure.quasiMeasurePreserving_snd.comp hprod.quasiMeasurePreserving
    exact hadd.ae hgeq
  have hfst :
      ∀ᵐ p : ℝ × ℝ ∂volume.prod volume, g p.1 = g0 p.1 :=
    Measure.quasiMeasurePreserving_fst.ae hgeq
  have hsnd :
      ∀ᵐ p : ℝ × ℝ ∂volume.prod volume, g p.2 = g0 p.2 :=
    Measure.quasiMeasurePreserving_snd.ae hgeq
  have hmeas :
      Measurable (fun p : ℝ × ℝ =>
        cauchyDefect g0 p.1 p.2) := by
    unfold cauchyDefect
    exact (hg0.comp (measurable_fst.add measurable_snd)).sub
      (hg0.comp measurable_fst) |>.sub (hg0.comp measurable_snd)
  apply hmeas.aemeasurable.congr
  filter_upwards [hsum, hfst, hsnd] with p hp hq hr
  unfold cauchyDefect
  rw [hp, hq, hr]

/-- A weak scalar decomposition becomes an a.e. measurable-plus-additive
split as soon as the scalar Cauchy defect has the nested measurable
representative supplied by the quotient construction. -/
lemma scalar_split_of_decomposition_of_nested_defect
    {c : ℝ → ℝ}
    (hcdec : HasMeasurableDecomposition c)
    (hdef : HasNestedMeasurableCauchyDefect c) :
    ∃ b H : ℝ → ℝ,
      AEMeasurable b volume ∧ IsAdditiveFn H ∧
        ∀ᵐ t ∂volume, c t = b t + H t := by
  rcases hcdec with ⟨g, H, r, hg, hH, hdecomp, hr⟩
  rcases hdef with ⟨d, hd, hdc⟩
  let d0 : ℝ × ℝ → ℝ := hd.mk (Function.uncurry d)
  have hd0 : Measurable d0 := hd.measurable_mk
  have hdd0 :
      ∀ᵐ p ∂volume.prod volume,
        Function.uncurry d p = d0 p := hd.ae_eq_mk
  have hdd0sec :
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, d s t = d0 (s, t) :=
    Measure.ae_ae_of_ae_prod hdd0
  let g0 : ℝ → ℝ := hg.mk g
  have hg0 : Measurable g0 := hg.measurable_mk
  have hgg0 : ∀ᵐ x ∂volume, g x = g0 x := hg.ae_eq_mk
  have hsumProd :
      ∀ᵐ p : ℝ × ℝ ∂volume.prod volume,
        g (p.1 + p.2) = g0 (p.1 + p.2) := by
    have hadd :
        Measure.QuasiMeasurePreserving
          (fun p : ℝ × ℝ => p.1 + p.2) (volume.prod volume) volume := by
      have hprod :
          MeasurePreserving (fun p : ℝ × ℝ => (p.1, p.1 + p.2))
            (volume.prod volume) (volume.prod volume) :=
        measurePreserving_prod_add volume volume
      exact Measure.quasiMeasurePreserving_snd.comp hprod.quasiMeasurePreserving
    exact hadd.ae hgg0
  have hsum :
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
        g (s + t) = g0 (s + t) :=
    Measure.ae_ae_of_ae_prod hsumProd
  have hfst :
      ∀ᵐ (s : ℝ) ∂volume, ∀ᵐ (_t : ℝ) ∂volume, g s = g0 s := by
    filter_upwards [hgg0] with s hs
    exact Filter.Eventually.of_forall fun _t : ℝ => hs
  have hsnd :
      ∀ᵐ (_s : ℝ) ∂volume, ∀ᵐ (t : ℝ) ∂volume, g t = g0 t := by
    exact Filter.Eventually.of_forall fun _s : ℝ => hgg0
  let dr : ℝ → ℝ → ℝ := fun s t =>
    d0 (s, t) - cauchyDefect g0 s t
  have hdr : Measurable (Function.uncurry dr) := by
    dsimp [dr]
    exact hd0.sub
      ((hg0.comp (measurable_fst.add measurable_snd)).sub
        (hg0.comp measurable_fst) |>.sub (hg0.comp measurable_snd))
  have hdr_eq :
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
        dr s t = cauchyDefect r s t := by
    filter_upwards [hdc, hdd0sec, hsum, hfst, hsnd] with s
      hcs hds hgs hfs hts
    filter_upwards [hcs, hds, hgs, hfs, hts] with t
      hct hdt hgt hft htt
    dsimp [dr]
    unfold cauchyDefect at hct ⊢
    rw [← hdt, hct, ← hgt, ← hft, ← htt]
    rw [hdecomp (s + t), hdecomp s, hdecomp t]
    rw [hH s t]
    ring
  have hrconst :
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, dr s t = -r s := by
    filter_upwards [hdr_eq] with s hs
    filter_upwards [hs, hr s] with t hst hrt
    unfold cauchyDefect at hst
    have hrt' : r (s + t) - r t = 0 := by
      convert hrt using 1 <;> ring
    linarith
  let b : ℝ → ℝ := fun s => -arctanRowValue dr s
  have hb : AEMeasurable b volume := by
    exact (measurable_arctanRowValue hdr).aemeasurable.neg
  have hrb : ∀ᵐ s ∂volume, r s = b s := by
    filter_upwards [hrconst] with s hs
    have hcenter := arctanRowValue_eq_of_ae_const hs
    dsimp [b]
    linarith
  refine ⟨fun x => g x + b x, H, hg.add hb, hH, ?_⟩
  filter_upwards [hrb] with t ht
  rw [hdecomp t, ht]
  ring

/-- A weak decomposition of the quotient constants is already enough to
finish the original function: the nested defect makes the scalar residual
measurable, and the measurable scalar is absorbed into the joint
representative. -/
lemma measurableDecomposition_of_moduloConstants_scalar_decomposition
    (f : ℝ → ℝ) (G : ℝ → ℝ → ℝ) (c : ℝ → ℝ)
    (hG : Measurable (Function.uncurry G))
    (hrel : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
      differenceKernel f x t = G x t + c t)
    (hcdec : HasMeasurableDecomposition c) :
    HasMeasurableDecomposition f := by
  apply measurableDecomposition_of_moduloConstants_scalar_split f G c hG hrel
  exact scalar_split_of_decomposition_of_nested_defect hcdec
    (hasNestedMeasurableCauchyDefect_of_moduloConstants f G c hG hrel)


/-- The quotient representative can be retained with its exact periodicity
in both variables. -/
def HasPeriodicJointDifferenceRepresentativeModuloConstants (f : ℝ → ℝ) : Prop :=
  ∃ G : ℝ → ℝ → ℝ,
    Measurable (Function.uncurry G) ∧
      (∀ t : ℝ, Function.Periodic (fun x => G x t) 1) ∧
        (∀ x : ℝ, Function.Periodic (fun t => G x t) 1) ∧
          ∀ᵐ t ∂volume, ∃ c : ℝ,
            ∀ᵐ x ∂volume, differenceKernel f x t = G x t + c

lemma periodic_hasPeriodicJointDifferenceRepresentativeModuloConstants
    {p : ℝ → ℝ} (hpper : Function.Periodic p 1)
    (hp : HasMeasurableDifferences p) :
    HasPeriodicJointDifferenceRepresentativeModuloConstants p := by
  rcases exists_measurable_global_soft_limit_original hpper hp with
    ⟨ns, hns, G0, hG0, hGbase, hGincrement, hlim⟩
  let G : ℝ → ℝ → ℝ := fun x t => G0 (x, t)
  have hG : Measurable (Function.uncurry G) := by
    exact hG0
  have hshift :
      ∀ᵐ t ∂volume, ∀ n : ℕ, ∀ j : Fin (2 ^ n),
        ∀ᵐ x ∂volume,
          G0 (x + dyadicShift n j, t) =
            G0 (x, t) +
              secondDifferenceKernel p (dyadicShift n j) x t := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro j
    have h := dyadicSoft_subseq_limit_refined_shift hpper hns hlim n j
    have hmap :
        ∀ᵐ z ∂Measure.map Prod.swap (volume.prod volume),
          G0 (z.1 + dyadicShift n j, z.2) =
            G0 z + secondDifferenceKernel p (dyadicShift n j) z.1 z.2 := by
      rw [Measure.prod_swap]
      exact h
    have hpull := ae_of_ae_map measurable_swap.aemeasurable hmap
    simpa [Prod.swap] using Measure.ae_ae_of_ae_prod hpull
  refine ⟨G, hG, ?_, ?_, ?_⟩
  · intro t
    exact hGbase t
  · intro x
    exact hGincrement x
  · filter_upwards [hshift] with t ht
    let u : ℝ → ℝ := fun x => differenceKernel p x t - G0 (x, t)
    have huper : Function.Periodic u 1 := by
      intro x
      dsimp [u]
      rw [show differenceKernel p (x + 1) t = differenceKernel p x t from
          differenceKernel_periodic_base hpper t x,
        show G0 (x + 1, t) = G0 (x, t) from hGbase t x]
    have humeas : AEMeasurable u volume := by
      have hsection : AEMeasurable (fun x : ℝ => G0 (x, t)) volume :=
        (hG0.comp (measurable_id.prodMk measurable_const)).aemeasurable
      exact (hp t).sub hsection
    have huinv :
        ∀ n : ℕ, ∀ j : Fin (2 ^ n),
          ∀ᵐ x ∂volume, u (x + dyadicShift n j) = u x := by
      intro n j
      filter_upwards [ht n j] with x hx
      dsimp [u]
      rw [hx]
      unfold secondDifferenceKernel
      ring
    rcases periodic_invariant_ae_const_of_dyadic_invariant huper humeas huinv with
      ⟨c, hc⟩
    refine ⟨c, ?_⟩
    filter_upwards [hc] with x hx
    dsimp [u] at hx
    dsimp [G]
    linarith

/-- In the periodic quotient construction, the scalar constants inherit the
unit period almost everywhere. -/
lemma quotientSectionConstant_periodic_ae
    {p : ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hpper : Function.Periodic p 1)
    (hGinc : ∀ x : ℝ, Function.Periodic (fun t => G x t) 1)
    (hrel : ∀ᵐ t ∂volume, ∃ c : ℝ,
      ∀ᵐ x ∂volume, differenceKernel p x t = G x t + c) :
    ∀ᵐ t ∂volume,
      quotientSectionConstant p G (t + 1) = quotientSectionConstant p G t := by
  have hrelshift : ∀ᵐ t ∂volume, ∃ c : ℝ,
      ∀ᵐ x ∂volume, differenceKernel p x (t + 1) = G x (t + 1) + c := by
    exact ae_translate hrel 1
  filter_upwards [hrel, hrelshift] with t ht ht1
  have h0 := quotientSectionConstant_spec ht
  have h1 := quotientSectionConstant_spec ht1
  have heq : ∀ᵐ x ∂volume,
      G x t + quotientSectionConstant p G t =
        G x (t + 1) + quotientSectionConstant p G (t + 1) := by
    filter_upwards [h0, h1] with x hx0 hx1
    rw [← hx0, ← hx1]
    unfold differenceKernel
    rw [show x + (t + 1) = (x + t) + 1 by ring, hpper]
  rcases heq.exists with ⟨x, hx⟩
  have hxper := hGinc x t
  change G x (t + 1) = G x t at hxper
  rw [hxper] at hx
  linarith



open Filter MeasureTheory Set Function
open scoped Pointwise ENNReal

lemma measure_inter_pos_of_gt_half
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAm : (1 / 2 : ℝ≥0∞) < μ A) (hBm : (1 / 2 : ℝ≥0∞) < μ B) :
    0 < μ (A ∩ B) := by
  by_contra hzero
  have hABzero : μ (A ∩ B) = 0 := le_antisymm (not_lt.mp hzero) bot_le
  have hunion := measure_union_add_inter (μ := μ) A hB
  rw [hABzero, add_zero] at hunion
  have huniv : μ (A ∪ B) ≤ μ univ := measure_mono (subset_univ _)
  have hsum : μ A + μ B ≤ 1 := by
    rw [← hunion]
    simpa using huniv
  have hAfin : μ A ≠ ⊤ := measure_ne_top _ _
  have hBfin : μ B ≠ ⊤ := measure_ne_top _ _
  have hAmR : (1 / 2 : ℝ) < (μ A).toReal := by
    have := (ENNReal.toReal_lt_toReal (by finiteness) hAfin).2 hAm
    norm_num at this ⊢
    exact this
  have hBmR : (1 / 2 : ℝ) < (μ B).toReal := by
    have := (ENNReal.toReal_lt_toReal (by finiteness) hBfin).2 hBm
    norm_num at this ⊢
    exact this
  have hsumR :
      (μ A + μ B).toReal ≤ (1 : ℝ≥0∞).toReal :=
    (ENNReal.toReal_le_toReal
      (ENNReal.add_ne_top.mpr ⟨hAfin, hBfin⟩) (by finiteness)).2 hsum
  rw [ENNReal.toReal_add hAfin hBfin] at hsumR
  norm_num at hsumR
  linarith

lemma measure_inter_gt_two_thirds_of_gt_five_sixths
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {A B : Set α} (_hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAm : (5 / 6 : ℝ≥0∞) < μ A) (hBm : (5 / 6 : ℝ≥0∞) < μ B) :
    (2 / 3 : ℝ≥0∞) < μ (A ∩ B) := by
  have hunion := measure_union_add_inter (μ := μ) A hB
  have huniv : μ (A ∪ B) ≤ μ univ := measure_mono (subset_univ _)
  have hAfin : μ A ≠ ⊤ := measure_ne_top _ _
  have hBfin : μ B ≠ ⊤ := measure_ne_top _ _
  have hUfin : μ (A ∪ B) ≠ ⊤ := measure_ne_top _ _
  have hIfin : μ (A ∩ B) ≠ ⊤ := measure_ne_top _ _
  have hAmR : (5 / 6 : ℝ) < (μ A).toReal := by
    have := (ENNReal.toReal_lt_toReal (by finiteness) hAfin).2 hAm
    norm_num at this ⊢
    exact this
  have hBmR : (5 / 6 : ℝ) < (μ B).toReal := by
    have := (ENNReal.toReal_lt_toReal (by finiteness) hBfin).2 hBm
    norm_num at this ⊢
    exact this
  have hunionR := congrArg ENNReal.toReal hunion
  rw [ENNReal.toReal_add hUfin hIfin,
    ENNReal.toReal_add hAfin hBfin] at hunionR
  have hunivR :
      (μ (A ∪ B)).toReal ≤ (1 : ℝ≥0∞).toReal :=
    (ENNReal.toReal_le_toReal hUfin (by finiteness)).2 (by simpa using huniv)
  norm_num at hunivR
  have hIR : (2 / 3 : ℝ) < (μ (A ∩ B)).toReal := by
    linarith
  have hI :
      (2 / 3 : ℝ≥0∞).toReal < (μ (A ∩ B)).toReal := by
    norm_num at hIR ⊢
    exact hIR
  exact (ENNReal.toReal_lt_toReal (by finiteness) hIfin).1 hI

lemma measure_triple_inter_pos_of_gt_two_thirds
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {A B C : Set α} (_hA : MeasurableSet A) (hB : MeasurableSet B)
    (_hC : MeasurableSet C)
    (hAm : (2 / 3 : ℝ≥0∞) < μ A)
    (hBm : (2 / 3 : ℝ≥0∞) < μ B)
    (hCm : (2 / 3 : ℝ≥0∞) < μ C) :
    0 < μ (A ∩ B ∩ C) := by
  have hABunion := measure_union_add_inter (μ := μ) A hB
  have hABunion_le : μ (A ∪ B) ≤ 1 := by
    simpa using (measure_mono (μ := μ) (subset_univ (A ∪ B)))
  have hAfin : μ A ≠ ⊤ := measure_ne_top _ _
  have hBfin : μ B ≠ ⊤ := measure_ne_top _ _
  have hCfin : μ C ≠ ⊤ := measure_ne_top _ _
  have hUfin : μ (A ∪ B) ≠ ⊤ := measure_ne_top _ _
  have hABfin : μ (A ∩ B) ≠ ⊤ := measure_ne_top _ _
  have hAmR : (2 / 3 : ℝ) < (μ A).toReal := by
    have := (ENNReal.toReal_lt_toReal (by finiteness) hAfin).2 hAm
    norm_num at this ⊢
    exact this
  have hBmR : (2 / 3 : ℝ) < (μ B).toReal := by
    have := (ENNReal.toReal_lt_toReal (by finiteness) hBfin).2 hBm
    norm_num at this ⊢
    exact this
  have hABunionR := congrArg ENNReal.toReal hABunion
  rw [ENNReal.toReal_add hUfin hABfin,
    ENNReal.toReal_add hAfin hBfin] at hABunionR
  have hABunionLeR :
      (μ (A ∪ B)).toReal ≤ (1 : ℝ≥0∞).toReal :=
    (ENNReal.toReal_le_toReal hUfin (by finiteness)).2 hABunion_le
  norm_num at hABunionLeR
  have hABR : (1 / 3 : ℝ) < (μ (A ∩ B)).toReal := by
    linarith
  have hAB : (1 / 3 : ℝ≥0∞) < μ (A ∩ B) := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) hABfin).1
    norm_num at hABR ⊢
    exact hABR
  have hABCunion := measure_union_add_inter (μ := μ) (A ∩ B) _hC
  have hABCunion_le : μ ((A ∩ B) ∪ C) ≤ 1 := by
    simpa using (measure_mono (μ := μ) (subset_univ ((A ∩ B) ∪ C)))
  have hUCfin : μ ((A ∩ B) ∪ C) ≠ ⊤ := measure_ne_top _ _
  have hABCfin : μ (A ∩ B ∩ C) ≠ ⊤ := measure_ne_top _ _
  have hABreal : (1 / 3 : ℝ) < (μ (A ∩ B)).toReal := by
    have := (ENNReal.toReal_lt_toReal (by finiteness) hABfin).2 hAB
    norm_num at this ⊢
    exact this
  have hCmR : (2 / 3 : ℝ) < (μ C).toReal := by
    have := (ENNReal.toReal_lt_toReal (by finiteness) hCfin).2 hCm
    norm_num at this ⊢
    exact this
  have hABCunionR := congrArg ENNReal.toReal hABCunion
  rw [ENNReal.toReal_add hUCfin hABCfin,
    ENNReal.toReal_add hABfin hCfin] at hABCunionR
  have hABCunionLeR :
      (μ ((A ∩ B) ∪ C)).toReal ≤ (1 : ℝ≥0∞).toReal :=
    (ENNReal.toReal_le_toReal hUCfin (by finiteness)).2 hABCunion_le
  norm_num at hABCunionLeR
  have hposR : 0 < (μ (A ∩ B ∩ C)).toReal := by
    linarith
  by_contra hnot
  have hzero : μ (A ∩ B ∩ C) = 0 :=
    le_antisymm (not_lt.mp hnot) bot_le
  rw [hzero] at hposR
  simp at hposR

lemma measure_triple_inter_pos_of_gt_two_thirds₀
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {A B C : Set α}
    (hA : NullMeasurableSet A μ) (hB : NullMeasurableSet B μ)
    (hC : NullMeasurableSet C μ)
    (hAm : (2 / 3 : ℝ≥0∞) < μ A)
    (hBm : (2 / 3 : ℝ≥0∞) < μ B)
    (hCm : (2 / 3 : ℝ≥0∞) < μ C) :
    0 < μ (A ∩ B ∩ C) := by
  rcases hA.exists_measurable_subset_ae_eq with ⟨A0, hA0sub, hA0meas, hA0eq⟩
  rcases hB.exists_measurable_subset_ae_eq with ⟨B0, hB0sub, hB0meas, hB0eq⟩
  rcases hC.exists_measurable_subset_ae_eq with ⟨C0, hC0sub, hC0meas, hC0eq⟩
  have hA0m : (2 / 3 : ℝ≥0∞) < μ A0 := by
    rwa [measure_congr hA0eq]
  have hB0m : (2 / 3 : ℝ≥0∞) < μ B0 := by
    rwa [measure_congr hB0eq]
  have hC0m : (2 / 3 : ℝ≥0∞) < μ C0 := by
    rwa [measure_congr hC0eq]
  have hpos :=
    measure_triple_inter_pos_of_gt_two_thirds
      hA0meas hB0meas hC0meas hA0m hB0m hC0m
  apply lt_of_lt_of_le hpos
  apply measure_mono
  exact inter_subset_inter (inter_subset_inter hA0sub hB0sub) hC0sub

/-- If a measurable subset of a probability product has very large measure,
then most first-coordinate sections have large measure. -/
lemma measure_many_large_sections
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [SFinite ν]
    {E : Set (α × β)} (hEmeas : MeasurableSet E)
    (hE : (35 / 36 : ℝ≥0∞) < (μ.prod ν) E) :
    (2 / 3 : ℝ≥0∞) <
      μ {a : α | (5 / 6 : ℝ≥0∞) < ν {b : β | (a, b) ∈ E}} := by
  let F : Set (α × β) := Eᶜ
  have hFmeas : MeasurableSet F := hEmeas.compl
  let q : α → ℝ≥0∞ := fun a => ν {b : β | (a, b) ∈ F}
  have hqmeas : Measurable q := by
    exact measurable_measure_prodMk_left (ν := ν) hFmeas
  have hprodF :
      (μ.prod ν) F = ∫⁻ a, q a ∂μ := by
    rw [Measure.prod_apply hFmeas]
    rfl
  have hFsmall : (μ.prod ν) F < (1 / 36 : ℝ≥0∞) := by
    have hsplit := measure_inter_add_sdiff (μ := μ.prod ν)
      (univ : Set (α × β)) hEmeas
    have hEcompl : univ \ E = F := by
      ext x
      simp [F]
    rw [univ_inter, hEcompl] at hsplit
    have htotal : (μ.prod ν) univ = 1 := by simp
    rw [htotal] at hsplit
    have hsum : (μ.prod ν) E + (μ.prod ν) F = 1 := hsplit
    by_contra hnot
    have hlarge : (1 / 36 : ℝ≥0∞) ≤ (μ.prod ν) F := not_lt.mp hnot
    have hEfin : (μ.prod ν) E ≠ ⊤ := measure_ne_top _ _
    have hFfin : (μ.prod ν) F ≠ ⊤ := measure_ne_top _ _
    have hER : (35 / 36 : ℝ) < ((μ.prod ν) E).toReal := by
      have := (ENNReal.toReal_lt_toReal (by finiteness) hEfin).2 hE
      norm_num at this ⊢
      exact this
    have hFR : (1 / 36 : ℝ) ≤ ((μ.prod ν) F).toReal := by
      have := (ENNReal.toReal_le_toReal (by finiteness) hFfin).2 hlarge
      norm_num at this ⊢
      exact this
    have hsumR := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_add hEfin hFfin] at hsumR
    norm_num at hsumR
    linarith
  let Bad : Set α := {a : α | (1 / 6 : ℝ≥0∞) ≤ q a}
  have hBadmeas : MeasurableSet Bad :=
    measurableSet_le measurable_const hqmeas
  have hmarkov :
      (1 / 6 : ℝ≥0∞) * μ Bad ≤ ∫⁻ a, q a ∂μ := by
    simpa [Bad] using mul_meas_ge_le_lintegral hqmeas (1 / 6 : ℝ≥0∞)
  have hBadsmall : μ Bad < (1 / 6 : ℝ≥0∞) := by
    rw [← hprodF] at hmarkov
    by_contra hnot
    have hlarge : (1 / 6 : ℝ≥0∞) ≤ μ Bad := not_lt.mp hnot
    have hBadfin : μ Bad ≠ ⊤ := measure_ne_top _ _
    have hlargeR : (1 / 6 : ℝ) ≤ (μ Bad).toReal := by
      have := (ENNReal.toReal_le_toReal (by finiteness) hBadfin).2 hlarge
      norm_num at this ⊢
      exact this
    have hmarkovR :
        ((1 / 6 : ℝ≥0∞) * μ Bad).toReal ≤ ((μ.prod ν) F).toReal :=
      (ENNReal.toReal_le_toReal
        (ENNReal.mul_ne_top (by finiteness) hBadfin) (measure_ne_top _ _)).2 hmarkov
    rw [ENNReal.toReal_mul] at hmarkovR
    have hFsmallR : ((μ.prod ν) F).toReal < (1 / 36 : ℝ) := by
      have := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (by finiteness)).2 hFsmall
      norm_num at this ⊢
      exact this
    norm_num at hmarkovR
    linarith
  have hcompl : Badᶜ =
      {a : α | (5 / 6 : ℝ≥0∞) < ν {b : β | (a, b) ∈ E}} := by
    ext a
    change a ∉ Bad ↔ _
    simp only [Bad, mem_setOf_eq, not_le]
    have hseccompl :
        ν {b : β | (a, b) ∈ E} + q a = 1 := by
      have hsplit := measure_inter_add_sdiff (μ := ν) (univ : Set β)
        (show MeasurableSet {b : β | (a, b) ∈ E} from
          measurable_prodMk_left hEmeas)
      have hcomp :
          univ \ {b : β | (a, b) ∈ E} = {b : β | (a, b) ∈ F} := by
        ext b
        simp [F]
      rw [univ_inter, hcomp] at hsplit
      simpa [q] using hsplit
    have hEafin : ν {b : β | (a, b) ∈ E} ≠ ⊤ := measure_ne_top _ _
    have hqfin : q a ≠ ⊤ := measure_ne_top _ _
    have hseccomplR := congrArg ENNReal.toReal hseccompl
    rw [ENNReal.toReal_add hEafin hqfin] at hseccomplR
    norm_num at hseccomplR
    constructor
    · intro hqsmall
      have hqsmallR : (q a).toReal < (1 / 6 : ℝ) := by
        have := (ENNReal.toReal_lt_toReal hqfin (by finiteness)).2 hqsmall
        norm_num at this ⊢
        exact this
      by_contra hnot
      have hle : ν {b : β | (a, b) ∈ E} ≤ 5 / 6 := not_lt.mp hnot
      have hleR : (ν {b : β | (a, b) ∈ E}).toReal ≤ (5 / 6 : ℝ) := by
        have := (ENNReal.toReal_le_toReal hEafin (by finiteness)).2 hle
        norm_num at this ⊢
        exact this
      linarith
    · intro hgood
      have hgoodR : (5 / 6 : ℝ) <
          (ν {b : β | (a, b) ∈ E}).toReal := by
        have := (ENNReal.toReal_lt_toReal (by finiteness) hEafin).2 hgood
        norm_num at this ⊢
        exact this
      by_contra hnot
      have hqbig : (1 / 6 : ℝ≥0∞) ≤ q a := not_lt.mp hnot
      have hqbigR : (1 / 6 : ℝ) ≤ (q a).toReal := by
        have := (ENNReal.toReal_le_toReal (by finiteness) hqfin).2 hqbig
        norm_num at this ⊢
        exact this
      linarith
  rw [← hcompl]
  have hsplit := measure_inter_add_sdiff (μ := μ) (univ : Set α) hBadmeas
  rw [univ_inter, diff_eq, univ_inter] at hsplit
  have htotal : μ univ = 1 := by simp
  rw [htotal] at hsplit
  by_contra hnot
  have hle : μ Badᶜ ≤ (2 / 3 : ℝ≥0∞) := not_lt.mp hnot
  have hBadfin : μ Bad ≠ ⊤ := measure_ne_top _ _
  have hBcfin : μ Badᶜ ≠ ⊤ := measure_ne_top _ _
  have hBadsmallR : (μ Bad).toReal < (1 / 6 : ℝ) := by
    have := (ENNReal.toReal_lt_toReal hBadfin (by finiteness)).2 hBadsmall
    norm_num at this ⊢
    exact this
  have hleR : (μ Badᶜ).toReal ≤ (2 / 3 : ℝ) := by
    have := (ENNReal.toReal_le_toReal hBcfin (by finiteness)).2 hle
    norm_num at this ⊢
    exact this
  have hsplitR := congrArg ENNReal.toReal hsplit
  rw [ENNReal.toReal_add hBadfin hBcfin] at hsplitR
  norm_num at hsplitR
  linarith



open Filter MeasureTheory Set Function Topology
open scoped Pointwise ENNReal

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-- The canonical real representative in the half-open unit interval of a
point of the unit additive circle. -/
noncomputable def circleIocRepresentative (z : UnitAddCircle) : ℝ :=
  (AddCircle.equivIoc 1 0 z : ℝ)

lemma measurable_circleIocRepresentative :
    Measurable circleIocRepresentative := by
  unfold circleIocRepresentative
  exact measurable_subtype_coe.comp
    (AddCircle.measurableEquivIoc 1 0).measurable

/-- Pull a doubly one-periodic real-plane function to the compact torus. -/
noncomputable def circlePlaneLift
    (G : ℝ → ℝ → ℝ) (z : UnitAddCircle × UnitAddCircle) : ℝ :=
  G (circleIocRepresentative z.1) (circleIocRepresentative z.2)

lemma measurable_circlePlaneLift
    {G : ℝ → ℝ → ℝ} (hG : Measurable (Function.uncurry G)) :
    Measurable (circlePlaneLift G) := by
  unfold circlePlaneLift
  exact hG.comp
    ((measurable_circleIocRepresentative.comp measurable_fst).prodMk
      (measurable_circleIocRepresentative.comp measurable_snd))

/-- A finite measurable real function on a probability space is bounded on a
set whose measure is as close to one as desired; this fixed quantitative
version is the one used in the compact quotient argument. -/
lemma exists_large_bounded_level
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {F : α → ℝ} (hF : Measurable F) :
    ∃ n : ℕ, (35 / 36 : ℝ≥0∞) < μ {x : α | |F x| ≤ n} := by
  let E : ℕ → Set α := fun n => {x : α | |F x| ≤ n}
  have hmono : Monotone E := by
    intro m n hmn x hx
    dsimp [E] at hx ⊢
    exact le_trans hx (by exact_mod_cast hmn)
  have hunion : (⋃ n : ℕ, E n) = (univ : Set α) := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    exact ⟨⌈|F x|⌉₊, by
      dsimp [E]
      exact Nat.le_ceil |F x|⟩
  have hlim :
      Tendsto (fun n : ℕ => μ (E n)) atTop (𝓝 (1 : ℝ≥0∞)) := by
    have h :=
      tendsto_measure_iUnion_atTop (μ := μ) hmono
    change Tendsto (fun n : ℕ => μ (E n)) atTop
      (𝓝 (μ (⋃ n : ℕ, E n))) at h
    simpa [hunion] using h
  have hlt : (35 / 36 : ℝ≥0∞) < 1 := by
    rw [ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  have hev : ∀ᶠ n : ℕ in atTop, (35 / 36 : ℝ≥0∞) < μ (E n) :=
    hlim (Ioi_mem_nhds hlt)
  rcases hev.exists with ⟨n, hn⟩
  exact ⟨n, hn⟩

/-- A jointly measurable torus function has one common level that bounds
more than five sixths of almost every section, for more than two thirds of
the increment circle. -/
lemma exists_many_bounded_circle_sections
    {G : ℝ → ℝ → ℝ} (hG : Measurable (Function.uncurry G)) :
    ∃ n : ℕ,
      (2 / 3 : ℝ≥0∞) <
        volume {t : UnitAddCircle |
          (5 / 6 : ℝ≥0∞) <
            volume {x : UnitAddCircle |
              |circlePlaneLift G (x, t)| ≤ n}} := by
  let F : UnitAddCircle × UnitAddCircle → ℝ :=
    fun z => circlePlaneLift G (z.2, z.1)
  have hF : Measurable F :=
    (measurable_circlePlaneLift hG).comp (measurable_snd.prodMk measurable_fst)
  rcases exists_large_bounded_level
      (μ := (volume : Measure (UnitAddCircle × UnitAddCircle))) hF with
    ⟨n, hn⟩
  let E : Set (UnitAddCircle × UnitAddCircle) :=
    {z | |circlePlaneLift G (z.2, z.1)| ≤ n}
  have hEmeas : MeasurableSet E := by
    dsimp [E]
    exact measurableSet_le hF.norm measurable_const
  have hmany := measure_many_large_sections
    (μ := (volume : Measure UnitAddCircle))
    (ν := (volume : Measure UnitAddCircle))
    hEmeas hn
  refine ⟨n, ?_⟩
  simpa [E, circlePlaneLift] using hmany

/-- A set of Haar measure greater than one half in the compact circle
meets each of its translates, hence every circle element is a difference of
two members of the set. -/
lemma exists_sub_eq_of_circle_measure_gt_half
    {A : Set UnitAddCircle} (hAmeas : MeasurableSet A)
    (hA : (1 / 2 : ℝ≥0∞) < volume A) (h : UnitAddCircle) :
    ∃ t ∈ A, ∃ u ∈ A, t - u = h := by
  let B : Set UnitAddCircle := {u | u + h ∈ A}
  have hBmeas : MeasurableSet B := by
    dsimp [B]
    exact hAmeas.preimage (measurable_id.add_const h)
  have hBmeasure : volume B = volume A := by
    change volume ((fun u : UnitAddCircle => u + h) ⁻¹' A) = volume A
    exact measure_preimage_add_right volume h A
  have hB : (1 / 2 : ℝ≥0∞) < volume B := by
    rw [hBmeasure]
    exact hA
  have hinter :
      0 < volume (A ∩ B) :=
    measure_inter_pos_of_gt_half hAmeas hBmeas hA hB
  have hne : (A ∩ B).Nonempty :=
    nonempty_of_measure_ne_zero (ne_of_gt hinter)
  rcases hne with ⟨u, huA, huB⟩
  refine ⟨u + h, huB, u, huA, ?_⟩
  simp




open Filter MeasureTheory Set Function Topology
open scoped Pointwise ENNReal

/-- A one-periodic real function has the same difference kernel for
increments representing the same point of the unit additive circle. -/
lemma differenceKernel_eq_of_circle_increment_eq
    {p : ℝ → ℝ} (hp : Function.Periodic p 1)
    {x a b : ℝ} (hab : (a : UnitAddCircle) = (b : UnitAddCircle)) :
    differenceKernel p x a = differenceKernel p x b := by
  have hzero : ((a - b : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, hab, sub_self]
  rcases (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 hzero with ⟨z, hz⟩
  have habz : a = b + (z : ℝ) := by
    have hz' : (z : ℝ) = a - b := by simpa using hz
    linarith
  rw [habz]
  have hper := (differenceKernel_periodic_increment hp x).zsmul z b
  convert hper using 1 <;> push_cast <;> ring

/-- A one-periodic real function has the same difference kernel for base
points representing the same point of the unit additive circle. -/
lemma differenceKernel_eq_of_circle_base_eq
    {p : ℝ → ℝ} (hp : Function.Periodic p 1)
    {x y t : ℝ} (hxy : (x : UnitAddCircle) = (y : UnitAddCircle)) :
    differenceKernel p x t = differenceKernel p y t := by
  have hzero : ((x - y : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, hxy, sub_self]
  rcases (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 hzero with ⟨z, hz⟩
  have hxyz : x = y + (z : ℝ) := by
    have hz' : (z : ℝ) = x - y := by simpa using hz
    linarith
  rw [hxyz]
  have hper := (differenceKernel_periodic_base hp t).zsmul z y
  convert hper using 1 <;> push_cast <;> ring

/-- The difference kernel of a one-periodic function descended to the
compact torus. -/
noncomputable def circleDifferenceKernel
    (p : ℝ → ℝ) (x t : UnitAddCircle) : ℝ :=
  differenceKernel p (circleIocRepresentative x) (circleIocRepresentative t)

lemma coe_circleIocRepresentative (z : UnitAddCircle) :
    (circleIocRepresentative z : UnitAddCircle) = z := by
  unfold circleIocRepresentative
  exact AddCircle.coe_equivIoc

/-- Restrict a full-Lebesgue-measure real statement to the canonical
fundamental interval and transport it to the unit additive circle. -/
lemma ae_circleIocRepresentative_of_ae
    {P : ℝ → Prop} (hP : ∀ᵐ x ∂volume, P x) :
    ∀ᵐ z : UnitAddCircle ∂volume, P (circleIocRepresentative z) := by
  have hsub :
      ∀ᵐ x : Ioc (0 : ℝ) (0 + 1) ∂(Measure.comap Subtype.val volume),
        P x := by
    exact (ae_restrict_iff_subtype measurableSet_Ioc).1 (ae_restrict_of_ae hP)
  have hcircle :=
    (AddCircle.measurePreserving_equivIoc 1).quasiMeasurePreserving.ae hsub
  simpa [circleIocRepresentative] using hcircle

lemma circleDifferenceKernel_eq_real
    {p : ℝ → ℝ} (hp : Function.Periodic p 1) (x t : ℝ) :
    circleDifferenceKernel p (x : UnitAddCircle) (t : UnitAddCircle) =
      differenceKernel p x t := by
  unfold circleDifferenceKernel
  apply Eq.trans
  · apply differenceKernel_eq_of_circle_increment_eq hp
      (a := circleIocRepresentative (t : UnitAddCircle)) (b := t)
    exact coe_circleIocRepresentative _
  · apply differenceKernel_eq_of_circle_base_eq hp
      (x := circleIocRepresentative (x : UnitAddCircle)) (y := x)
    exact coe_circleIocRepresentative _

lemma circleDifferenceKernel_cocycle
    {p : ℝ → ℝ} (hp : Function.Periodic p 1)
    (x s t : UnitAddCircle) :
    circleDifferenceKernel p x (s + t) =
      circleDifferenceKernel p (x + s) t + circleDifferenceKernel p x s := by
  let xr := circleIocRepresentative x
  let sr := circleIocRepresentative s
  let tr := circleIocRepresentative t
  have hsum :
      circleDifferenceKernel p x (s + t) =
        differenceKernel p xr (sr + tr) := by
    unfold circleDifferenceKernel
    apply differenceKernel_eq_of_circle_increment_eq hp
    dsimp [xr, sr, tr]
    rw [coe_circleIocRepresentative, coe_circleIocRepresentative,
      coe_circleIocRepresentative]
  have hbase :
      circleDifferenceKernel p (x + s) t =
        differenceKernel p (xr + sr) tr := by
    unfold circleDifferenceKernel
    apply differenceKernel_eq_of_circle_base_eq hp
    dsimp [xr, sr, tr]
    rw [coe_circleIocRepresentative, coe_circleIocRepresentative,
      coe_circleIocRepresentative]
  rw [hsum, hbase]
  exact differenceKernel_cocycle p xr sr tr

lemma circleDifferenceKernel_aemeasurable
    {p : ℝ → ℝ} (hp : HasMeasurableDifferences p)
    (t : UnitAddCircle) :
    AEMeasurable (fun x : UnitAddCircle => circleDifferenceKernel p x t) volume := by
  let u : ℝ → ℝ := fun x =>
    differenceKernel p x (circleIocRepresentative t)
  have hu : AEMeasurable u volume := hp (circleIocRepresentative t)
  let v : ℝ → ℝ := hu.mk u
  have hv : Measurable v :=
    hu.measurable_mk
  have huv : ∀ᵐ x ∂volume, u x = v x :=
    hu.ae_eq_mk
  have huvCircle :
      ∀ᵐ x : UnitAddCircle ∂volume,
        u (circleIocRepresentative x) = v (circleIocRepresentative x) :=
    ae_circleIocRepresentative_of_ae
      (P := fun x : ℝ => u x = v x) huv
  have hvCircle :
      AEMeasurable (fun x : UnitAddCircle => v (circleIocRepresentative x)) volume :=
    (hv.comp measurable_circleIocRepresentative).aemeasurable
  apply hvCircle.congr
  filter_upwards [huvCircle] with x hx
  unfold circleDifferenceKernel
  exact hx.symm



open Filter MeasureTheory Set Function Topology
open scoped Pointwise ENNReal

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-- A centered estimate on more than two thirds of the compact circle. -/
def HasCircleMostlyMean
    (K : UnitAddCircle → UnitAddCircle → ℝ)
    (D : UnitAddCircle → ℝ) (M : ℝ) : Prop :=
  ∀ h : UnitAddCircle,
    (2 / 3 : ℝ≥0∞) <
      volume {x : UnitAddCircle | |K x h - D h| ≤ M}

/-- If most sections of a measurable representative are bounded and the
original cocycle equals that representative modulo a scalar, every increment
has one scalar center with a uniform large-measure bound. -/
lemma circleMostlyMean_of_moduloConstants
    (K G : UnitAddCircle → UnitAddCircle → ℝ) (c : UnitAddCircle → ℝ)
    (n : ℕ) (A : Set UnitAddCircle)
    (hG : Measurable (Function.uncurry G))
    (hAmeas : MeasurableSet A)
    (hA : (1 / 2 : ℝ≥0∞) < volume A)
    (hgood : ∀ t ∈ A,
      (5 / 6 : ℝ≥0∞) <
        volume {x : UnitAddCircle | |G x t| ≤ n})
    (hrel : ∀ t ∈ A, ∀ᵐ x ∂volume, K x t = G x t + c t)
    (hcoc : ∀ x s t : UnitAddCircle,
      K x (s + t) = K (x + s) t + K x s) :
    ∃ D : UnitAddCircle → ℝ,
      HasCircleMostlyMean K D (2 * n) := by
  have hrepr : ∀ h : UnitAddCircle,
      ∃ t ∈ A, ∃ u ∈ A, t - u = h :=
    fun h => exists_sub_eq_of_circle_measure_gt_half hAmeas hA h
  choose t ht u hu htu using hrepr
  let D : UnitAddCircle → ℝ := fun h => c (t h) - c (u h)
  refine ⟨D, ?_⟩
  intro h
  let Xt : Set UnitAddCircle := {x | |G x (t h)| ≤ n}
  let Xu : Set UnitAddCircle := {x | |G x (u h)| ≤ n}
  let X : Set UnitAddCircle := Xt ∩ Xu
  have hXtmeas : MeasurableSet Xt := by
    dsimp [Xt]
    exact measurableSet_le
      ((show Measurable (fun x : UnitAddCircle => G x (t h)) from
        hG.comp (measurable_id.prodMk measurable_const)).norm) measurable_const
  have hXumeas : MeasurableSet Xu := by
    dsimp [Xu]
    exact measurableSet_le
      ((show Measurable (fun x : UnitAddCircle => G x (u h)) from
        hG.comp (measurable_id.prodMk measurable_const)).norm) measurable_const
  have hXlarge : (2 / 3 : ℝ≥0∞) < volume X :=
    measure_inter_gt_two_thirds_of_gt_five_sixths
      hXtmeas hXumeas (hgood (t h) (ht h)) (hgood (u h) (hu h))
  let Y : Set UnitAddCircle :=
    {y | |K y h - D h| ≤ 2 * n}
  have hsubae :
      X ≤ᵐ[(volume : Measure UnitAddCircle)]
        (fun x : UnitAddCircle => x + u h) ⁻¹' Y := by
    filter_upwards [hrel (t h) (ht h), hrel (u h) (hu h)] with x hxt hxu hx
    have hsum : u h + h = t h := by
      have hh : t h = h + u h := (sub_eq_iff_eq_add).mp (htu h)
      simpa [add_comm] using hh.symm
    have hk := hcoc x (u h) h
    rw [hsum, hxt, hxu] at hk
    change |K (x + u h) h - (c (t h) - c (u h))| ≤ 2 * n
    change |G x (t h)| ≤ n ∧ |G x (u h)| ≤ n at hx
    rw [abs_le]
    constructor <;>
      nlinarith [abs_le.mp hx.1, abs_le.mp hx.2, hk]
  have hle :
      volume X ≤ volume ((fun x : UnitAddCircle => x + u h) ⁻¹' Y) :=
    measure_mono_ae hsubae
  have hpre :
      volume ((fun x : UnitAddCircle => x + u h) ⁻¹' Y) = volume Y :=
    measure_preimage_add_right volume (u h) Y
  rw [hpre] at hle
  exact lt_of_lt_of_le hXlarge hle

/-- Three large-measure centered cocycle estimates intersect, so their
centers satisfy a uniform Hyers defect bound. -/
lemma approximate_additive_of_circleMostlyMean
    (K : UnitAddCircle → UnitAddCircle → ℝ)
    (D : UnitAddCircle → ℝ) (M : ℝ)
    (hKmeas : ∀ h : UnitAddCircle,
      AEMeasurable (fun x : UnitAddCircle => K x h) volume)
    (hmean : HasCircleMostlyMean K D M)
    (hcoc : ∀ x s t : UnitAddCircle,
      K x (s + t) = K (x + s) t + K x s) :
    ∀ s t : UnitAddCircle, |D (s + t) - D s - D t| ≤ 3 * M := by
  intro s t
  let A : Set UnitAddCircle :=
    {x | |K x (s + t) - D (s + t)| ≤ M}
  let B : Set UnitAddCircle :=
    {x | |K (x + s) t - D t| ≤ M}
  let C : Set UnitAddCircle :=
    {x | |K x s - D s| ≤ M}
  have hAmeas : NullMeasurableSet A (volume : Measure UnitAddCircle) := by
    dsimp [A]
    exact nullMeasurableSet_le
      ((hKmeas (s + t)).sub aemeasurable_const).norm aemeasurable_const
  have hBmeas : NullMeasurableSet B (volume : Measure UnitAddCircle) := by
    dsimp [B]
    have hshift :
        AEMeasurable (fun x : UnitAddCircle => K (x + s) t) volume :=
      (hKmeas t).comp_quasiMeasurePreserving
        (measurePreserving_add_right volume s).quasiMeasurePreserving
    exact nullMeasurableSet_le
      (hshift.sub aemeasurable_const).norm aemeasurable_const
  have hCmeas : NullMeasurableSet C (volume : Measure UnitAddCircle) := by
    dsimp [C]
    exact nullMeasurableSet_le
      ((hKmeas s).sub aemeasurable_const).norm aemeasurable_const
  have hAm : (2 / 3 : ℝ≥0∞) < volume A := hmean (s + t)
  have hCm : (2 / 3 : ℝ≥0∞) < volume C := hmean s
  have hBm : (2 / 3 : ℝ≥0∞) < volume B := by
    let T : Set UnitAddCircle := {x | |K x t - D t| ≤ M}
    have hT : (2 / 3 : ℝ≥0∞) < volume T := hmean t
    have hpre :
        volume ((fun x : UnitAddCircle => x + s) ⁻¹' T) = volume T :=
      measure_preimage_add_right volume s T
    have hBT : B = (fun x : UnitAddCircle => x + s) ⁻¹' T := by
      rfl
    rw [hBT, hpre]
    exact hT
  have hinter : 0 < volume (A ∩ B ∩ C) :=
    measure_triple_inter_pos_of_gt_two_thirds₀
      hAmeas hBmeas hCmeas hAm hBm hCm
  rcases nonempty_of_measure_ne_zero (ne_of_gt hinter) with
    ⟨x, ⟨hxA, hxB⟩, hxC⟩
  have hk := hcoc x s t
  dsimp [A, B, C] at hxA hxB hxC
  rw [hk] at hxA
  rw [abs_le]
  constructor <;>
    nlinarith [abs_le.mp hxA, abs_le.mp hxB, abs_le.mp hxC]



open Filter MeasureTheory Set Function Topology
open scoped Pointwise ENNReal

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-- The quotient relation for a periodic real kernel transports to an
almost-everywhere relation on the compact torus. -/
lemma ae_circleDifferenceKernel_eq_circlePlaneLift_add
    {p : ℝ → ℝ} {G : ℝ → ℝ → ℝ} {c : ℝ → ℝ}
    (hp : Function.Periodic p 1)
    (hrel : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
      differenceKernel p x t = G x t + c t) :
    ∀ᵐ t : UnitAddCircle ∂volume, ∀ᵐ x : UnitAddCircle ∂volume,
      circleDifferenceKernel p x t =
        circlePlaneLift G (x, t) + c (circleIocRepresentative t) := by
  have ht :
      ∀ᵐ t : UnitAddCircle ∂volume,
        ∀ᵐ x ∂volume,
          differenceKernel p x (circleIocRepresentative t) =
            G x (circleIocRepresentative t) + c (circleIocRepresentative t) :=
    ae_circleIocRepresentative_of_ae
      (P := fun t : ℝ =>
        ∀ᵐ x ∂volume,
          differenceKernel p x t = G x t + c t) hrel
  filter_upwards [ht] with t ht
  have hx := ae_circleIocRepresentative_of_ae ht
  filter_upwards [hx] with x hx
  unfold circleDifferenceKernel circlePlaneLift
  exact hx

/-- The parameter set of sections bounded on more than five sixths of the
circle is measurable. -/
lemma measurableSet_many_bounded_circle_sections
    {G : ℝ → ℝ → ℝ} (hG : Measurable (Function.uncurry G)) (n : ℕ) :
    MeasurableSet
      {t : UnitAddCircle |
        (5 / 6 : ℝ≥0∞) <
          volume {x : UnitAddCircle | |circlePlaneLift G (x, t)| ≤ n}} := by
  let E : Set (UnitAddCircle × UnitAddCircle) :=
    {z | |circlePlaneLift G (z.2, z.1)| ≤ n}
  have hEmeas : MeasurableSet E := by
    dsimp [E]
    exact measurableSet_le
      (((measurable_circlePlaneLift hG).comp
        (measurable_snd.prodMk measurable_fst)).norm) measurable_const
  have hsec :
      Measurable (fun t : UnitAddCircle =>
        volume {x : UnitAddCircle | (t, x) ∈ E}) :=
    measurable_measure_prodMk_left (ν := (volume : Measure UnitAddCircle)) hEmeas
  apply measurableSet_lt measurable_const
  convert hsec using 1
  funext t
  congr 1

/-- The compact quotient representative supplies a uniform large-measure
scalar mean for every circle increment. -/
lemma periodic_circleMostlyMean_of_moduloConstants
    {p : ℝ → ℝ} {G : ℝ → ℝ → ℝ} {c : ℝ → ℝ}
    (hp : Function.Periodic p 1)
    (hG : Measurable (Function.uncurry G))
    (hrel : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
      differenceKernel p x t = G x t + c t) :
    ∃ n : ℕ, ∃ D : UnitAddCircle → ℝ,
      HasCircleMostlyMean (circleDifferenceKernel p) D (2 * n) := by
  rcases exists_many_bounded_circle_sections hG with ⟨n, hn⟩
  let B : Set UnitAddCircle :=
    {t : UnitAddCircle |
      (5 / 6 : ℝ≥0∞) <
        volume {x : UnitAddCircle | |circlePlaneLift G (x, t)| ≤ n}}
  have hBmeas : MeasurableSet B :=
    measurableSet_many_bounded_circle_sections hG n
  have hrelCircle :
      ∀ᵐ t : UnitAddCircle ∂volume, ∀ᵐ x : UnitAddCircle ∂volume,
        circleDifferenceKernel p x t =
          circlePlaneLift G (x, t) + c (circleIocRepresentative t) :=
    ae_circleDifferenceKernel_eq_circlePlaneLift_add hp hrel
  let Z : Set UnitAddCircle :=
    {t | ∀ᵐ x : UnitAddCircle ∂volume,
      circleDifferenceKernel p x t =
        circlePlaneLift G (x, t) + c (circleIocRepresentative t)}
  have hZae : ∀ᵐ t : UnitAddCircle ∂volume, t ∈ Z := hrelCircle
  have hZnull : NullMeasurableSet Z (volume : Measure UnitAddCircle) := by
    have hzc : volume Zᶜ = 0 := by
      simpa only [compl_def] using (ae_iff.mp hZae)
    simpa using (NullMeasurableSet.of_null hzc).compl
  rcases hZnull.exists_measurable_subset_ae_eq with
    ⟨Z0, hZ0sub, hZ0meas, hZ0eq⟩
  let A : Set UnitAddCircle := B ∩ Z0
  have hAmeas : MeasurableSet A := hBmeas.inter hZ0meas
  have hAeq : A =ᵐ[(volume : Measure UnitAddCircle)] B := by
    filter_upwards [hZ0eq, hZae] with t ht htz
    apply propext
    change (t ∈ B ∩ Z0) ↔ t ∈ B
    have ht0 : t ∈ Z0 := (Iff.of_eq ht).mpr htz
    simp [ht0]
  have hAmeasure : volume A = volume B := measure_congr hAeq
  have hA : (1 / 2 : ℝ≥0∞) < volume A := by
    rw [hAmeasure]
    have hhalf : (1 / 2 : ℝ≥0∞) < 2 / 3 := by
      apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).1
      norm_num
    exact hhalf.trans hn
  have hgood : ∀ t ∈ A,
      (5 / 6 : ℝ≥0∞) <
        volume {x : UnitAddCircle | |circlePlaneLift G (x, t)| ≤ n} := by
    intro t ht
    exact ht.1
  have hrelA : ∀ t ∈ A, ∀ᵐ x ∂volume,
      circleDifferenceKernel p x t =
        circlePlaneLift G (x, t) + c (circleIocRepresentative t) := by
    intro t ht
    exact hZ0sub ht.2
  rcases circleMostlyMean_of_moduloConstants
      (circleDifferenceKernel p) (fun x t => circlePlaneLift G (x, t))
      (fun t => c (circleIocRepresentative t)) n A
      (measurable_circlePlaneLift hG) hAmeas hA hgood hrelA
      (circleDifferenceKernel_cocycle hp) with ⟨D, hD⟩
  exact ⟨n, D, hD⟩



open Filter MeasureTheory Set Function Topology
open scoped Pointwise ENNReal

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-- A function on the real line obtained from a circle function is
one-periodic. -/
lemma circle_comp_periodic (D : UnitAddCircle → ℝ) :
    Function.Periodic (fun t : ℝ => D (t : UnitAddCircle)) 1 := by
  intro t
  change D ((t + 1 : ℝ) : UnitAddCircle) = D (t : UnitAddCircle)
  congr 1
  rw [AddCircle.coe_add]
  simp

/-- Hyers approximation to a periodic scalar must vanish at the period. -/
lemma additive_one_eq_zero_of_periodic_approximation
    {D H : ℝ → ℝ} {C : ℝ}
    (hDper : Function.Periodic D 1)
    (hH : IsAdditiveFn H)
    (hDH : ∀ t : ℝ, |D t - H t| ≤ C) :
    H 1 = 0 := by
  have hbound : ∀ t : ℝ, ∀ᵐ x ∂volume,
      |differenceKernel (fun y => D y - H y) x t| ≤ 2 * C := by
    intro t
    filter_upwards [] with x
    unfold differenceKernel
    change |(D (x + t) - H (x + t)) - (D x - H x)| ≤ 2 * C
    have h1 := hDH (x + t)
    rw [hH x t] at h1
    have h2 := hDH x
    rw [hH x t]
    rw [abs_le]
    constructor <;>
      nlinarith [abs_le.mp h1, abs_le.mp h2]
  exact additive_one_eq_zero_of_periodic_uniform_bound hDper hH hbound

/-- A Hyers correction to the circle means keeps the corrected periodic
difference sections bounded on more than two thirds of the circle. -/
lemma periodic_corrected_circleMostlyBounded_of_circleMostlyMean
    {p : ℝ → ℝ} {D : UnitAddCircle → ℝ} {M : ℝ}
    (hp : Function.Periodic p 1)
    (hpmeas : HasMeasurableDifferences p)
    (hM : 0 ≤ M)
    (hmean : HasCircleMostlyMean (circleDifferenceKernel p) D M) :
    ∃ H : ℝ → ℝ,
      IsAdditiveFn H ∧ H 1 = 0 ∧
        HasCircleMostlyMean
          (circleDifferenceKernel (fun x => p x - H x))
          (fun _ => 0) (4 * M) := by
  let Dr : ℝ → ℝ := fun t => D (t : UnitAddCircle)
  have hDrper : Function.Periodic Dr 1 := circle_comp_periodic D
  have happ : ∀ s t : ℝ, |Dr (s + t) - Dr s - Dr t| ≤ 3 * M := by
    have happCircle :=
      approximate_additive_of_circleMostlyMean
        (circleDifferenceKernel p) D M
        (circleDifferenceKernel_aemeasurable hpmeas)
        hmean (circleDifferenceKernel_cocycle hp)
    intro s t
    simpa [Dr, AddCircle.coe_add] using
      happCircle (s : UnitAddCircle) (t : UnitAddCircle)
  rcases hyers_ulam Dr (3 * M) (by positivity) happ with ⟨H, hH, hDH⟩
  have hH1 : H 1 = 0 :=
    additive_one_eq_zero_of_periodic_approximation hDrper hH hDH
  refine ⟨H, hH, hH1, ?_⟩
  intro h
  let A : Set UnitAddCircle :=
    {x | |circleDifferenceKernel p x h - D h| ≤ M}
  let B : Set UnitAddCircle :=
    {x |
      |circleDifferenceKernel (fun y => p y - H y) x h| ≤ 4 * M}
  have hA : (2 / 3 : ℝ≥0∞) < volume A := hmean h
  have hsub : A ⊆ B := by
    intro x hx
    dsimp [A] at hx
    unfold circleDifferenceKernel differenceKernel at hx
    dsimp [B]
    unfold circleDifferenceKernel differenceKernel
    change
      |(p (circleIocRepresentative x + circleIocRepresentative h) -
          H (circleIocRepresentative x + circleIocRepresentative h)) -
        (p (circleIocRepresentative x) - H (circleIocRepresentative x))| ≤
        4 * M
    rw [hH (circleIocRepresentative x) (circleIocRepresentative h)]
    have hD : |D h - H (circleIocRepresentative h)| ≤ 3 * M := by
      simpa [Dr, coe_circleIocRepresentative] using hDH (circleIocRepresentative h)
    rw [abs_le]
    constructor <;>
      nlinarith [abs_le.mp hx, abs_le.mp hD]
  simpa [B] using lt_of_lt_of_le hA (measure_mono hsub)



open Filter MeasureTheory Set Function Topology
open scoped Pointwise ENNReal

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

lemma circleSoftCenter_le_iff_score_le_zero
    {u : UnitAddCircle → ℝ} (hu : AEMeasurable u volume) (a : ℝ) :
    circleSoftCenter u hu ≤ a ↔ circleSoftScore u a ≤ 0 := by
  have hzero := circleSoftScore_center_eq_zero hu
  have hanti := circleSoftScore_strictAnti hu
  constructor
  · intro hle
    rcases hle.lt_or_eq with hlt | rfl
    · exact (hanti hlt).le.trans_eq hzero
    · exact hzero.le
  · intro hscore
    by_contra hnot
    have hlt : a < circleSoftCenter u hu := lt_of_not_ge hnot
    have hstrict := hanti hlt
    rw [hzero] at hstrict
    linarith

lemma circleSoftCenter_ge_iff_score_ge_zero
    {u : UnitAddCircle → ℝ} (hu : AEMeasurable u volume) (a : ℝ) :
    a ≤ circleSoftCenter u hu ↔ 0 ≤ circleSoftScore u a := by
  have hzero := circleSoftScore_center_eq_zero hu
  have hanti := circleSoftScore_strictAnti hu
  constructor
  · intro hle
    rcases hle.lt_or_eq with hlt | rfl
    · rw [← hzero]
      exact (hanti hlt).le
    · exact hzero.ge
  · intro hscore
    by_contra hnot
    have hlt : circleSoftCenter u hu < a := lt_of_not_ge hnot
    have hstrict := hanti hlt
    rw [hzero] at hstrict
    linarith

/-- The arctangent score of a torus section. -/
noncomputable def circleSectionSoftScore
    (G : ℝ → ℝ → ℝ) (t : UnitAddCircle) (a : ℝ) : ℝ :=
  ∫ x : UnitAddCircle, Real.arctan (circlePlaneLift G (x, t) - a)

lemma measurable_circleSectionSoftScore
    {G : ℝ → ℝ → ℝ} (hG : Measurable (Function.uncurry G)) (a : ℝ) :
    Measurable (fun t : UnitAddCircle => circleSectionSoftScore G t a) := by
  let F : UnitAddCircle × UnitAddCircle → ℝ :=
    fun z => Real.arctan (circlePlaneLift G (z.2, z.1) - a)
  have hF : Measurable F := by
    dsimp [F]
    exact Real.continuous_arctan.measurable.comp
      (((measurable_circlePlaneLift hG).comp
        (measurable_snd.prodMk measurable_fst)).sub measurable_const)
  unfold circleSectionSoftScore
  exact hF.stronglyMeasurable.integral_prod_right.measurable

/-- The canonical soft center of a measurable torus section. -/
noncomputable def circleSectionSoftCenter
    (G : ℝ → ℝ → ℝ) (hG : Measurable (Function.uncurry G))
    (t : UnitAddCircle) : ℝ :=
  circleSoftCenter
    (fun x : UnitAddCircle => circlePlaneLift G (x, t))
    ((measurable_circlePlaneLift hG).comp
      (measurable_id.prodMk measurable_const)).aemeasurable

lemma circleSectionSoftCenter_score_zero
    {G : ℝ → ℝ → ℝ} (hG : Measurable (Function.uncurry G))
    (t : UnitAddCircle) :
    circleSectionSoftScore G t (circleSectionSoftCenter G hG t) = 0 := by
  unfold circleSectionSoftScore circleSectionSoftCenter
  exact circleSoftScore_center_eq_zero _

lemma measurable_circleSectionSoftCenter
    {G : ℝ → ℝ → ℝ} (hG : Measurable (Function.uncurry G)) :
    Measurable (circleSectionSoftCenter G hG) := by
  apply measurable_of_Iic
  intro a
  have hpre :
      (circleSectionSoftCenter G hG) ⁻¹' Iic a =
        {t : UnitAddCircle | circleSectionSoftScore G t a ≤ 0} := by
    ext t
    exact circleSoftCenter_le_iff_score_le_zero _ a
  rw [hpre]
  exact measurableSet_le (measurable_circleSectionSoftScore hG a) measurable_const



open Filter MeasureTheory Set Function Topology
open scoped Pointwise ENNReal

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-- A zero arctangent score cannot be shifted far past a set of measure
greater than two thirds on which the shifted function is uniformly bounded. -/
lemma const_le_add_one_of_circleSoftScore_zero_of_large_bound
    {u : UnitAddCircle → ℝ} {C L : ℝ}
    (hu : Measurable u) (hL : 0 ≤ L)
    (hscore : circleSoftScore u 0 = 0)
    (hgood : (2 / 3 : ℝ≥0∞) <
      volume {x : UnitAddCircle | |u x + C| ≤ L}) :
    C ≤ L + 1 := by
  by_contra hnot
  have hCL : L + 1 < C := lt_of_not_ge hnot
  let A : Set UnitAddCircle := {x | |u x + C| ≤ L}
  have hAmeas : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_le ((hu.add measurable_const).norm) measurable_const
  let g : UnitAddCircle → ℝ := fun x =>
    if x ∈ A then -(Real.pi / 4) else Real.pi / 2
  have hgmeas : Measurable g := by
    dsimp [g]
    exact Measurable.ite hAmeas measurable_const measurable_const
  have hgint : Integrable g volume :=
    Integrable.of_bound hgmeas.aestronglyMeasurable (Real.pi / 2) (by
      filter_upwards [] with x
      dsimp [g]
      split_ifs <;> rw [abs_le] <;> constructor <;>
        nlinarith [Real.pi_pos])
  have hfint : Integrable (fun x : UnitAddCircle => Real.arctan (u x)) volume := by
    simpa using circleSoftScore_integrable hu.aemeasurable 0
  have hfg : ∀ x : UnitAddCircle, Real.arctan (u x) ≤ g x := by
    intro x
    by_cases hx : x ∈ A
    · simp only [g, hx, ↓reduceIte]
      have hxbound : |u x + C| ≤ L := hx
      have hux : u x ≤ -1 := by
        rw [abs_le] at hxbound
        linarith
      calc
        Real.arctan (u x) ≤ Real.arctan (-1) :=
          (Real.arctan_mono hux)
        _ = -(Real.pi / 4) := by rw [Real.arctan_neg, Real.arctan_one]
    · simp only [g, hx, ↓reduceIte]
      exact (Real.arctan_lt_pi_div_two (u x)).le
  have hintle :
      (∫ x : UnitAddCircle, Real.arctan (u x)) ≤ ∫ x, g x :=
    integral_mono hfint hgint hfg
  have hgintegral :
      (∫ x : UnitAddCircle, g x) =
        volume.real A * (-(Real.pi / 4)) +
          volume.real Aᶜ * (Real.pi / 2) := by
    rw [show g =
        A.indicator (fun _ : UnitAddCircle => -(Real.pi / 4)) +
          Aᶜ.indicator (fun _ : UnitAddCircle => Real.pi / 2) by
      funext x
      by_cases hx : x ∈ A <;> simp [g, hx]]
    change
      (∫ x : UnitAddCircle,
        A.indicator (fun _ : UnitAddCircle => -(Real.pi / 4)) x +
          Aᶜ.indicator (fun _ : UnitAddCircle => Real.pi / 2) x) =
        _
    have hAint :
        Integrable (A.indicator (fun _ : UnitAddCircle => -(Real.pi / 4))) volume :=
      (integrable_const _).indicator hAmeas
    have hAcint :
        Integrable (Aᶜ.indicator (fun _ : UnitAddCircle => Real.pi / 2)) volume :=
      (integrable_const _).indicator hAmeas.compl
    rw [integral_add hAint hAcint,
      integral_indicator_const _ hAmeas,
      integral_indicator_const _ hAmeas.compl]
    simp [smul_eq_mul]
  have hAreal : (2 / 3 : ℝ) < volume.real A := by
    have hAfin : volume A ≠ ⊤ := measure_ne_top _ _
    have h := (ENNReal.toReal_lt_toReal (by finiteness) hAfin).2 hgood
    norm_num at h ⊢
    exact h
  have hAcompReal : volume.real Aᶜ = 1 - volume.real A := by
    have hadd := measureReal_inter_add_sdiff
      (μ := (volume : Measure UnitAddCircle)) (s := (univ : Set UnitAddCircle))
      hAmeas
    rw [univ_inter, show univ \ A = Aᶜ by
      ext x
      simp] at hadd
    norm_num at hadd ⊢
    linarith
  have hgneg : (∫ x : UnitAddCircle, g x) < 0 := by
    rw [hgintegral, hAcompReal]
    nlinarith [Real.pi_pos]
  have hzero : (∫ x : UnitAddCircle, Real.arctan (u x)) = 0 := by
    simpa [circleSoftScore] using hscore
  rw [hzero] at hintle
  linarith

lemma abs_const_le_add_one_of_circleSoftScore_zero_of_large_bound
    {u : UnitAddCircle → ℝ} {C L : ℝ}
    (hu : Measurable u) (hL : 0 ≤ L)
    (hscore : circleSoftScore u 0 = 0)
    (hgood : (2 / 3 : ℝ≥0∞) <
      volume {x : UnitAddCircle | |u x + C| ≤ L}) :
    |C| ≤ L + 1 := by
  have hupper :=
    const_le_add_one_of_circleSoftScore_zero_of_large_bound
      hu hL hscore hgood
  have hnegscore : circleSoftScore (fun x => -u x) 0 = 0 := by
    unfold circleSoftScore at hscore ⊢
    rw [show (fun x : UnitAddCircle => Real.arctan (-u x - 0)) =
        fun x => -Real.arctan (u x - 0) by
      funext x
      simp only [sub_zero]
      rw [Real.arctan_neg]]
    rw [integral_neg]
    linarith
  have hneggood : (2 / 3 : ℝ≥0∞) <
      volume {x : UnitAddCircle | |(-u x) + (-C)| ≤ L} := by
    convert hgood using 1
    congr 1
    ext x
    simp only [mem_setOf_eq]
    rw [show -u x + -C = -(u x + C) by ring, abs_neg]
  have hlowerNeg :=
    const_le_add_one_of_circleSoftScore_zero_of_large_bound
      hu.neg hL hnegscore hneggood
  rw [abs_le]
  constructor <;> linarith



open Filter MeasureTheory Set Function Topology
open scoped Pointwise ENNReal

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-- Pull an almost-everywhere statement on the unit circle back through
fractional part on the real line.  The half-open endpoint mismatch is a
null set, and the remaining real line is the countable union of integer
translates of one fundamental interval. -/
lemma ae_real_fract_circle_of_ae_circleRepresentative
    {P : ℝ → UnitAddCircle → Prop}
    (hP : ∀ᵐ z : UnitAddCircle ∂volume,
      P (circleIocRepresentative z) z) :
    ∀ᵐ x : ℝ ∂volume, P (Int.fract x) (x : UnitAddCircle) := by
  let e := AddCircle.measurableEquivIoc 1 0
  have heq :
      Measure.map e (volume : Measure UnitAddCircle) =
        Measure.comap Subtype.val (volume : Measure ℝ) :=
    (AddCircle.measurePreserving_equivIoc (T := 1) (a := 0)).map_eq
  have hq :
      Measure.QuasiMeasurePreserving e.symm
        (Measure.comap Subtype.val (volume : Measure ℝ))
        (volume : Measure UnitAddCircle) := by
    rw [← heq]
    exact e.quasiMeasurePreserving_symm volume
  have hsub' :
      ∀ᵐ y : Ioc (0 : ℝ) (0 + 1) ∂(Measure.comap Subtype.val volume),
        P (y : ℝ) ((y : ℝ) : UnitAddCircle) := by
    have h := hq.ae hP
    exact h.mono (fun y hy => by
      have hrep : circleIocRepresentative (e.symm y) = (y : ℝ) := by
        unfold circleIocRepresentative
        exact congrArg Subtype.val (e.apply_symm_apply y)
      have hcoe : e.symm y = ((y : ℝ) : UnitAddCircle) := by
        apply e.injective
        rw [e.apply_symm_apply]
        symm
        exact AddCircle.equivIoc_coe_eq y.property
      rw [hrep, hcoe] at hy
      exact hy)
  have hsub :
      ∀ᵐ y : Ioc (0 : ℝ) 1 ∂(Measure.comap Subtype.val volume),
        P (y : ℝ) ((y : ℝ) : UnitAddCircle) := by
    have hs : Ioc (0 : ℝ) (0 + 1) = Ioc (0 : ℝ) 1 := by
      norm_num
    rw [hs] at hsub'
    exact hsub'
  have hIoc :
      ∀ᵐ y ∂volume.restrict (Ioc (0 : ℝ) 1),
        P y (y : UnitAddCircle) :=
    (ae_restrict_iff_subtype measurableSet_Ioc).2 hsub
  have hIco :
      ∀ᵐ y ∂volume.restrict (Ico (0 : ℝ) 1),
        P y (y : UnitAddCircle) := by
    rw [Measure.restrict_congr_set Ico_ae_eq_Ioc]
    exact hIoc
  have hcover : (⋃ n : ℤ, Ico (n : ℝ) (n + 1 : ℝ)) = (univ : Set ℝ) := by
    ext x
    simp only [mem_iUnion, mem_Ico, mem_univ, iff_true]
    exact ⟨⌊x⌋, Int.floor_le x, Int.lt_floor_add_one x⟩
  rw [← Measure.restrict_univ (μ := volume), ← hcover, ae_restrict_iUnion_iff]
  intro n
  have hfull :
      ∀ᵐ y ∂volume, y ∈ Ico (0 : ℝ) 1 →
        P y (y : UnitAddCircle) :=
    (ae_restrict_iff' measurableSet_Ico).1 hIco
  have htrans := ae_translate hfull (-(n : ℝ))
  filter_upwards [ae_restrict_of_ae htrans,
    ae_restrict_mem measurableSet_Ico] with x hx hmem
  have hxmem : x - (n : ℝ) ∈ Ico (0 : ℝ) 1 := by
    constructor <;> linarith [hmem.1, hmem.2]
  have hxP : P (x - (n : ℝ)) ((x - (n : ℝ)) : UnitAddCircle) := by
    apply hx
    simpa [sub_eq_add_neg] using hxmem
  have hfloor : ⌊x⌋ = n := by
    rw [Int.floor_eq_iff]
    exact hmem
  have hfract : Int.fract x = x - (n : ℝ) := by
    rw [Int.fract, hfloor]
  rw [hfract]
  convert hxP using 1
  have hnzero : (((n : ℤ) : ℝ) : UnitAddCircle) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).2
    exact ⟨n, by simp⟩
  rw [hnzero, sub_zero]

/-- Centering every measurable quotient section by its canonical soft
center makes the remaining scalar constants uniformly bounded almost
everywhere on the increment circle. -/
lemma ae_abs_normalized_quotient_constant_le_of_circleMostlyBounded
    {q : ℝ → ℝ} {G : ℝ → ℝ → ℝ} {c : ℝ → ℝ} {L : ℝ}
    (hqper : Function.Periodic q 1)
    (hG : Measurable (Function.uncurry G))
    (hrel : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
      differenceKernel q x t = G x t + c t)
    (hL : 0 ≤ L)
    (hmostly : HasCircleMostlyMean
      (circleDifferenceKernel q) (fun _ => 0) L) :
    ∀ᵐ t : UnitAddCircle ∂volume,
      |c (circleIocRepresentative t) + circleSectionSoftCenter G hG t| ≤ L + 1 := by
  have hrelCircle :=
    ae_circleDifferenceKernel_eq_circlePlaneLift_add hqper hrel
  filter_upwards [hrelCircle] with t ht
  let b : ℝ := circleSectionSoftCenter G hG t
  let u : UnitAddCircle → ℝ :=
    fun x => circlePlaneLift G (x, t) - b
  have hu : Measurable u := by
    dsimp [u, b]
    exact ((measurable_circlePlaneLift hG).comp
      (measurable_id.prodMk measurable_const)).sub measurable_const
  have hscore : circleSoftScore u 0 = 0 := by
    simpa [u, b, circleSoftScore, circleSectionSoftScore] using
      (circleSectionSoftCenter_score_zero hG t)
  have hgood :
      (2 / 3 : ℝ≥0∞) <
        volume {x : UnitAddCircle |
          |u x + (c (circleIocRepresentative t) + b)| ≤ L} := by
    have hpred :
        {x : UnitAddCircle |
          |u x + (c (circleIocRepresentative t) + b)| ≤ L} =ᵐ[
            (volume : Measure UnitAddCircle)]
          {x : UnitAddCircle |
            |circleDifferenceKernel q x t - 0| ≤ L} := by
      filter_upwards [ht] with x hx
      change
        (|u x + (c (circleIocRepresentative t) + b)| ≤ L) =
          (|circleDifferenceKernel q x t - 0| ≤ L)
      rw [hx]
      dsimp [u]
      congr 2
      ring
    rw [measure_congr hpred]
    exact hmostly t
  exact abs_const_le_add_one_of_circleSoftScore_zero_of_large_bound
    hu hL hscore hgood



open Filter MeasureTheory Set Function Topology
open scoped Pointwise ENNReal

/-- Any full-measure real property remains full-measure after fractional
part.  This is the one-variable specialization of the circle transport
lemma. -/
lemma ae_periodizeOne_of_ae {P : ℝ → Prop}
    (hP : ∀ᵐ x ∂volume, P x) :
    ∀ᵐ x ∂volume, P (Int.fract x) := by
  have hcircle :
      ∀ᵐ z : UnitAddCircle ∂volume,
        P (circleIocRepresentative z) :=
    ae_circleIocRepresentative_of_ae hP
  exact ae_real_fract_circle_of_ae_circleRepresentative
    (P := fun y _z => P y) hcircle

/-- A scalar with measurable differences whose periodized version becomes
bounded after adding a measurable periodic center already has the weak
measurable decomposition. -/
lemma measurableDecomposition_of_bounded_periodized_scalar
    {c b : ℝ → ℝ} {B : ℝ}
    (hc : HasMeasurableDifferences c)
    (hb : AEMeasurable b volume)
    (hbper : Function.Periodic b 1)
    (hB : 0 ≤ B)
    (hbound : ∀ᵐ x ∂volume,
      |periodizeOne c x + b x| ≤ B) :
    HasMeasurableDecomposition c := by
  let q : ℝ → ℝ := fun x => periodizeOne c x + b x
  have hqper : Function.Periodic q 1 := by
    intro x
    dsimp [q]
    rw [periodizeOne_periodic c, hbper]
  have hqdiff : HasMeasurableDifferences q := by
    dsimp [q]
    exact (periodizeOne_hasMeasurableDifferences hc).add_aemeasurable hb
  have hdiffbound : ∀ t : ℝ, ∀ᵐ x ∂volume,
      |differenceKernel q x t| ≤ 2 * B := by
    intro t
    have hshift := ae_translate hbound t
    filter_upwards [hbound, hshift] with x hx hxt
    unfold differenceKernel
    dsimp [q]
    rw [abs_le]
    constructor <;>
      nlinarith [abs_le.mp hx, abs_le.mp hxt]
  have hqdec : HasMeasurableDecomposition q :=
    measurableDecomposition_of_bounded_periodic hqper hqdiff hdiffbound
  let r : ℝ → ℝ := fun x => c x - q x
  have hr : AEMeasurable r volume := by
    have hpc : AEMeasurable (fun x => periodizeOne c x - c x) volume :=
      periodizeOne_sub_aemeasurable hc
    dsimp [r, q]
    convert hpc.neg.sub hb using 1
    funext x
    simp only [Pi.neg_apply, Pi.sub_apply]
    ring
  have hadd := hqdec.add_aemeasurable hr
  convert hadd using 1
  funext x
  dsimp [q, r]
  ring

/-- The compact soft-center bound gives a bounded periodized scalar on the
real line. -/
lemma ae_bound_periodized_quotient_constant_of_circleMostlyBounded
    {q : ℝ → ℝ} {G : ℝ → ℝ → ℝ} {c : ℝ → ℝ} {L : ℝ}
    (hqper : Function.Periodic q 1)
    (hG : Measurable (Function.uncurry G))
    (hrel : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
      differenceKernel q x t = G x t + c t)
    (hL : 0 ≤ L)
    (hmostly : HasCircleMostlyMean
      (circleDifferenceKernel q) (fun _ => 0) L) :
    ∀ᵐ t ∂volume,
      |periodizeOne c t +
          circleSectionSoftCenter G hG (t : UnitAddCircle)| ≤ L + 1 := by
  have hcircle :=
    ae_abs_normalized_quotient_constant_le_of_circleMostlyBounded
      hqper hG hrel hL hmostly
  have hreal :=
    ae_real_fract_circle_of_ae_circleRepresentative
      (P := fun y z =>
        |c y + circleSectionSoftCenter G hG z| ≤ L + 1) hcircle
  simpa [periodizeOne] using hreal

/-- A periodic function whose circle differences are mostly bounded has the
correct measurable decomposition.  The quotient scalar is centered on the
circle, periodized, and fed to the bounded periodic core. -/
lemma measurableDecomposition_of_circleMostlyBounded_periodic
    {q : ℝ → ℝ} {L : ℝ}
    (hqper : Function.Periodic q 1)
    (hq : HasMeasurableDifferences q)
    (hL : 0 ≤ L)
    (hmostly : HasCircleMostlyMean
      (circleDifferenceKernel q) (fun _ => 0) L) :
    HasMeasurableDecomposition q := by
  rcases periodic_hasPeriodicJointDifferenceRepresentativeModuloConstants
      hqper hq with ⟨G, hG, _hGbase, _hGinc, hrelExists⟩
  let c : ℝ → ℝ := quotientSectionConstant q G
  have hrel :
      ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
        differenceKernel q x t = G x t + c t := by
    filter_upwards [hrelExists] with t ht
    exact quotientSectionConstant_spec ht
  have hc : HasMeasurableDifferences c :=
    quotientSectionConstant_hasMeasurableDifferences q G c hG hrel
  let b : ℝ → ℝ :=
    fun t => circleSectionSoftCenter G hG (t : UnitAddCircle)
  have hb : AEMeasurable b volume := by
    dsimp [b]
    exact ((measurable_circleSectionSoftCenter hG).comp
      AddCircle.measurable_mk').aemeasurable
  have hbper : Function.Periodic b 1 := by
    intro t
    dsimp [b]
    congr 1
    simp
  have hbound :
      ∀ᵐ t ∂volume, |periodizeOne c t + b t| ≤ L + 1 := by
    exact ae_bound_periodized_quotient_constant_of_circleMostlyBounded
      hqper hG hrel hL hmostly
  have hcdec : HasMeasurableDecomposition c :=
    measurableDecomposition_of_bounded_periodized_scalar hc hb hbper
      (by linarith) hbound
  exact measurableDecomposition_of_moduloConstants_scalar_decomposition
    q G c hG hrel hcdec



open Filter MeasureTheory Set Function Topology
open scoped Pointwise ENNReal

/-- The compact quotient, Hyers correction, and bounded centered scalar
argument solve the full one-periodic measurable-difference problem. -/
lemma measurableDecomposition_of_periodic_measurableDifferences
    {p : ℝ → ℝ}
    (hpper : Function.Periodic p 1)
    (hp : HasMeasurableDifferences p) :
    HasMeasurableDecomposition p := by
  rcases periodic_hasJointDifferenceRepresentativeModuloConstants hpper hp with
    ⟨G, hG, hrelExists⟩
  let c : ℝ → ℝ := quotientSectionConstant p G
  have hrel :
      ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
        differenceKernel p x t = G x t + c t := by
    filter_upwards [hrelExists] with t ht
    exact quotientSectionConstant_spec ht
  rcases periodic_circleMostlyMean_of_moduloConstants hpper hG hrel with
    ⟨n, D, hmean⟩
  rcases periodic_corrected_circleMostlyBounded_of_circleMostlyMean
      hpper hp (M := 2 * (n : ℝ)) (by positivity) hmean with
    ⟨H, hH, hH1, hmostly⟩
  let q : ℝ → ℝ := fun x => p x - H x
  have hqper : Function.Periodic q 1 := by
    intro x
    dsimp [q]
    rw [hpper, hH x 1, hH1]
    ring
  have hq : HasMeasurableDifferences q := by
    intro t
    have ht := hp t
    have hconst : AEMeasurable (fun _ : ℝ => H t) volume :=
      aemeasurable_const
    convert ht.sub hconst using 1
    funext x
    change (p (x + t) - H (x + t)) - (p x - H x) =
      (p (x + t) - p x) - H t
    rw [hH x t]
    ring
  have hqdec : HasMeasurableDecomposition q :=
    measurableDecomposition_of_circleMostlyBounded_periodic hqper hq
      (L := 4 * (2 * (n : ℝ))) (by positivity) hmostly
  have hadd := hqdec.add_additive hH
  convert hadd using 1
  funext x
  dsimp [q]
  ring

/-- **Main result for the source-supported measurable wording:** every
function with measurable positive translate differences is the sum of an
almost-everywhere measurable function, an additive function, and a function
with null translate increments. -/
theorem erdos_908_measurable : (∀ f : ℝ → ℝ,
  Erdos908.HasMeasurablePositiveDifferences f → Erdos908.HasMeasurableDecomposition f) :=
  measurableClaim_of_periodic_core fun _p hpper hp =>
    measurableDecomposition_of_periodic_measurableDifferences hpper hp



end Erdos908

#print axioms Erdos908.erdos908
#print axioms Erdos908.erdos_908_measurable

alias _root_.Erdos908.erdos908_continuous_counterexample := _root_.Erdos908.not_erdos_908

alias _root_.Erdos908.erdos908_measurable := _root_.Erdos908.erdos_908_measurable
