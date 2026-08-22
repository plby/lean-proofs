/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRecursiveProfileRow

/-!
# Weighted substitution in a heterogeneous annular renewal

At the padded asymmetric interface the children of one retained annular
renewal carry different recursive profile trees.  This file records the
finite-kernel algebra for replacing those children, one at a time, by the
unrestricted leaf kernel.  The only input about the surrounding retained
prefix is an oscillation estimate for every baseline suffix continuation.

The statement is deliberately abstract in the inward and escape kernels.
Consequently the same lemma applies when the outer endpoint is several
profile radii away, as required by the logarithmic decorrelation padding.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.AnnularRecursiveWeightedRenewal

open AnnularOffspringKernelRadial
open AnnularRecursiveDecoratedProfileCode AnnularRecursiveProfileRow
open AnnularRecursiveProfileShape AppendixFirstMoment ProfileGapChain

noncomputable section

/-- A chronological renewal with a possibly different child kernel at every
completed inward visit. -/
def heterogeneousRenewalKernel
    {Middle Inner Exit Tree : Type*}
    [Fintype Middle] [Fintype Inner]
    (inward : Middle → Inner → ℝ≥0∞)
    (child : Tree → Inner → Middle → ℝ≥0∞)
    (escape : Middle → Exit → ℝ≥0∞) :
    List Tree → Middle → Exit → ℝ≥0∞
  | [], u, w => escape u w
  | tree :: rest, u, w =>
      ∑ z, inward u z *
        ∑ v, child tree z v *
          heterogeneousRenewalKernel inward child escape rest v w

/-- Replacing heterogeneous children one at a time multiplies their row
losses and pays one continuation-oscillation factor per child. -/
theorem heterogeneousRenewalKernel_le_baseline
    {Middle Inner Exit Tree : Type*}
    [Fintype Middle] [Fintype Inner]
    (inward : Middle → Inner → ℝ≥0∞)
    (selected baseline : Tree → Inner → Middle → ℝ≥0∞)
    (escape : Middle → Exit → ℝ≥0∞)
    (loss : Tree → ℝ≥0∞) (distortion : ℝ≥0∞)
    (hweighted : ∀ (tree : Tree) (z : Inner)
      (continuation : Middle → ℝ≥0∞) (reference : ℝ≥0∞),
      (∀ v, reference ≤ continuation v) →
      (∀ v, continuation v ≤ distortion * reference) →
      (∑ v, selected tree z v * continuation v) ≤
        loss tree * distortion *
          ∑ v, baseline tree z v * continuation v)
    (hsuffix : ∀ (trees : List Tree) (w : Exit),
      ∃ reference : ℝ≥0∞,
        (∀ v, reference ≤
          heterogeneousRenewalKernel inward baseline escape trees v w) ∧
        (∀ v, heterogeneousRenewalKernel inward baseline escape trees v w ≤
          distortion * reference)) :
    ∀ (trees : List Tree) (u : Middle) (w : Exit),
      heterogeneousRenewalKernel inward selected escape trees u w ≤
        (trees.map loss).prod * distortion ^ trees.length *
          heterogeneousRenewalKernel inward baseline escape trees u w := by
  intro trees
  induction trees with
  | nil =>
      intro u w
      simp [heterogeneousRenewalKernel]
  | cons tree rest ih =>
      intro u w
      obtain ⟨reference, hlower, hupper⟩ := hsuffix rest w
      let coefficient : ℝ≥0∞ :=
        (rest.map loss).prod * distortion ^ rest.length
      calc
        heterogeneousRenewalKernel inward selected escape
            (tree :: rest) u w =
            ∑ z, inward u z *
              ∑ v, selected tree z v *
                heterogeneousRenewalKernel inward selected escape rest v w := by
                  rfl
        _ ≤ ∑ z, inward u z *
              ∑ v, selected tree z v *
                (coefficient *
                  heterogeneousRenewalKernel inward baseline escape rest v w) := by
              apply Finset.sum_le_sum
              intro z _
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply Finset.sum_le_sum
              intro v _
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              simpa only [coefficient] using ih v w
        _ = coefficient *
              ∑ z, inward u z *
                ∑ v, selected tree z v *
                  heterogeneousRenewalKernel inward baseline escape rest v w := by
              simp_rw [show ∀ (z : Inner) (v : Middle),
                selected tree z v *
                    (coefficient * heterogeneousRenewalKernel inward baseline
                      escape rest v w) =
                  coefficient * (selected tree z v *
                    heterogeneousRenewalKernel inward baseline escape rest v w)
                  by intros; ac_rfl]
              simp_rw [← Finset.mul_sum]
              simp_rw [show ∀ (z : Inner) (value : ℝ≥0∞),
                inward u z * (coefficient * value) =
                  coefficient * (inward u z * value) by intros; ac_rfl]
              rw [← Finset.mul_sum]
        _ ≤ coefficient *
              ∑ z, inward u z *
                (loss tree * distortion *
                  ∑ v, baseline tree z v *
                    heterogeneousRenewalKernel inward baseline escape rest v w) := by
              gcongr with z
              exact hweighted tree z
                (fun v ↦ heterogeneousRenewalKernel inward baseline escape rest v w)
                reference hlower hupper
        _ = ((tree :: rest).map loss).prod *
              distortion ^ (tree :: rest).length *
                heterogeneousRenewalKernel inward baseline escape
                  (tree :: rest) u w := by
              simp only [List.map_cons, List.prod_cons, List.length_cons,
                pow_succ, heterogeneousRenewalKernel]
              dsimp only [coefficient]
              have hfactor :
                  (∑ z, inward u z *
                    (loss tree * distortion *
                      ∑ v, baseline tree z v *
                        heterogeneousRenewalKernel inward baseline escape
                          rest v w)) =
                    loss tree * distortion *
                      ∑ z, inward u z *
                        ∑ v, baseline tree z v *
                          heterogeneousRenewalKernel inward baseline escape
                            rest v w := by
                simp_rw [show ∀ (z : Inner) (value : ℝ≥0∞),
                  inward u z * (loss tree * distortion * value) =
                    (loss tree * distortion) * (inward u z * value)
                    by intros; ac_rfl]
                rw [← Finset.mul_sum]
              rw [hfactor]
              ac_rfl

/-- A heterogeneous renewal may instead be compared with one global
continuation envelope.  This is the form needed when the retained endpoint
is remote: after the current child is replaced, all possible later offspring
counts are absorbed into the unmarked exit kernel. -/
theorem heterogeneousRenewalKernel_le_envelope
    {Middle Inner Exit Tree : Type*}
    [Fintype Middle] [Fintype Inner]
    (inward : Middle → Inner → ℝ≥0∞)
    (selected baseline : Tree → Inner → Middle → ℝ≥0∞)
    (escape envelope : Middle → Exit → ℝ≥0∞)
    (loss : Tree → ℝ≥0∞) (distortion : ℝ≥0∞)
    (hweighted : ∀ (tree : Tree) (z : Inner) (w : Exit),
      (∑ v, selected tree z v * envelope v w) ≤
        loss tree * distortion *
          ∑ v, baseline tree z v * envelope v w)
    (hescape : ∀ (u : Middle) (w : Exit), escape u w ≤ envelope u w)
    (hstep : ∀ (tree : Tree) (u : Middle) (w : Exit),
      (∑ z, inward u z *
        ∑ v, baseline tree z v * envelope v w) ≤ envelope u w) :
    ∀ (trees : List Tree) (u : Middle) (w : Exit),
      heterogeneousRenewalKernel inward selected escape trees u w ≤
        (trees.map loss).prod * distortion ^ trees.length * envelope u w := by
  intro trees
  induction trees with
  | nil =>
      intro u w
      simpa only [List.map_nil, List.prod_nil, List.length_nil, pow_zero,
        one_mul,
        heterogeneousRenewalKernel] using hescape u w
  | cons tree rest ih =>
      intro u w
      let coefficient : ℝ≥0∞ :=
        (rest.map loss).prod * distortion ^ rest.length
      calc
        heterogeneousRenewalKernel inward selected escape
            (tree :: rest) u w =
            ∑ z, inward u z *
              ∑ v, selected tree z v *
                heterogeneousRenewalKernel inward selected escape
                  rest v w := by rfl
        _ ≤ ∑ z, inward u z *
              ∑ v, selected tree z v *
                (coefficient * envelope v w) := by
              apply Finset.sum_le_sum
              intro z _
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply Finset.sum_le_sum
              intro v _
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              simpa only [coefficient] using ih v w
        _ = coefficient *
              ∑ z, inward u z *
                ∑ v, selected tree z v * envelope v w := by
              simp_rw [show ∀ (z : Inner) (v : Middle),
                selected tree z v * (coefficient * envelope v w) =
                  coefficient * (selected tree z v * envelope v w)
                  by intros; ac_rfl]
              simp_rw [← Finset.mul_sum]
              simp_rw [show ∀ (z : Inner) (value : ℝ≥0∞),
                inward u z * (coefficient * value) =
                  coefficient * (inward u z * value) by intros; ac_rfl]
              rw [← Finset.mul_sum]
        _ ≤ coefficient *
              ∑ z, inward u z *
                (loss tree * distortion *
                  ∑ v, baseline tree z v * envelope v w) := by
              gcongr with z
              exact hweighted tree z w
        _ = coefficient * (loss tree * distortion) *
              (∑ z, inward u z *
                ∑ v, baseline tree z v * envelope v w) := by
              simp_rw [show ∀ (z : Inner) (value : ℝ≥0∞),
                inward u z * (loss tree * distortion * value) =
                  (loss tree * distortion) * (inward u z * value)
                  by intros; ac_rfl]
              rw [← Finset.mul_sum]
              ac_rfl
        _ ≤ coefficient * (loss tree * distortion) * envelope u w := by
              gcongr
              exact hstep tree u w
        _ = ((tree :: rest).map loss).prod *
              distortion ^ (tree :: rest).length * envelope u w := by
              simp only [List.map_cons, List.prod_cons, List.length_cons,
                pow_succ]
              dsimp only [coefficient]
              ac_rfl

/-- Several remote renewal segments traversed in chronological order.  A
tree may be inserted in the current segment, or the current segment may
escape with zero further trees and the same tree list is offered to the next
segment.  Thus the definition sums every weak allocation of one ordered tree
list among the retained segments exactly once. -/
def heterogeneousMultiRenewalKernel
    {Middle Inner Exit Tree : Type*}
    [Fintype Middle] [Fintype Inner]
    (inward : Middle → Inner → ℝ≥0∞)
    (child : Tree → Inner → Middle → ℝ≥0∞)
    (escape : Middle → Exit → ℝ≥0∞) :
    List (Middle × Exit) → List Tree → ℝ≥0∞
  | [], [] => 1
  | [], _ :: _ => 0
  | (u, w) :: segments, [] =>
      escape u w * heterogeneousMultiRenewalKernel inward child escape
        segments []
  | (u, w) :: segments, tree :: rest =>
      escape u w * heterogeneousMultiRenewalKernel inward child escape
        segments (tree :: rest) +
      ∑ z, inward u z *
        ∑ v, child tree z v *
          heterogeneousMultiRenewalKernel inward child escape
            ((v, w) :: segments) rest
termination_by segments trees => segments.length + trees.length

/-- Global-envelope comparison for several renewal segments.  The escape
term and the one-more-child term are kept together until the renewal
inequality is applied; this is what prevents a factor equal to the number of
possible allocations among the segments. -/
theorem heterogeneousMultiRenewalKernel_le_envelope
    {Middle Inner Exit Tree : Type*}
    [Fintype Middle] [Fintype Inner]
    (inward : Middle → Inner → ℝ≥0∞)
    (selected baseline : Tree → Inner → Middle → ℝ≥0∞)
    (escape envelope : Middle → Exit → ℝ≥0∞)
    (loss : Tree → ℝ≥0∞) (distortion : ℝ≥0∞)
    (hweighted : ∀ (tree : Tree) (z : Inner) (w : Exit),
      (∑ v, selected tree z v * envelope v w) ≤
        loss tree * distortion *
          ∑ v, baseline tree z v * envelope v w)
    (hescape : ∀ (u : Middle) (w : Exit), escape u w ≤ envelope u w)
    (hrenew : ∀ (tree : Tree) (u : Middle) (w : Exit),
      escape u w +
          ∑ z, inward u z *
            ∑ v, baseline tree z v * envelope v w ≤
        envelope u w) :
    ∀ (trees : List Tree) (segments : List (Middle × Exit)),
      heterogeneousMultiRenewalKernel inward selected escape segments trees ≤
        (trees.map loss).prod * distortion ^ trees.length *
          (segments.map fun segment ↦ envelope segment.1 segment.2).prod := by
  intro trees
  induction trees with
  | nil =>
      intro segments
      induction segments with
      | nil => simp [heterogeneousMultiRenewalKernel]
      | cons segment segments ih =>
          rcases segment with ⟨u, w⟩
          simpa only [heterogeneousMultiRenewalKernel, List.map_nil,
            List.prod_nil, List.length_nil, pow_zero, one_mul,
            List.map_cons, List.prod_cons] using
              mul_le_mul (hescape u w) ih (by positivity) (by positivity)
  | cons tree rest ihTrees =>
      intro segments
      induction segments with
      | nil => simp [heterogeneousMultiRenewalKernel]
      | cons segment segments ihSegments =>
          rcases segment with ⟨u, w⟩
          let restCoefficient : ℝ≥0∞ :=
            (rest.map loss).prod * distortion ^ rest.length
          let totalCoefficient : ℝ≥0∞ :=
            ((tree :: rest).map loss).prod *
              distortion ^ (tree :: rest).length
          let envelopeTail : ℝ≥0∞ :=
            (segments.map fun segment ↦
              envelope segment.1 segment.2).prod
          have htotal : totalCoefficient =
              restCoefficient * (loss tree * distortion) := by
            simp only [totalCoefficient, restCoefficient, List.map_cons,
              List.prod_cons, List.length_cons, pow_succ]
            ac_rfl
          have hescape :
              escape u w *
                  heterogeneousMultiRenewalKernel inward selected escape
                    segments (tree :: rest) ≤
                totalCoefficient * (escape u w * envelopeTail) := by
            calc
              _ ≤ escape u w *
                    (totalCoefficient * envelopeTail) := by
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  simpa only [totalCoefficient, envelopeTail] using ihSegments
              _ = totalCoefficient * (escape u w * envelopeTail) := by
                  ac_rfl
          have hchild :
              (∑ z, inward u z *
                ∑ v, selected tree z v *
                  heterogeneousMultiRenewalKernel inward selected escape
                    ((v, w) :: segments) rest) ≤
                totalCoefficient *
                  ((∑ z, inward u z *
                    ∑ v, baseline tree z v * envelope v w) *
                    envelopeTail) := by
            calc
              _ ≤ ∑ z, inward u z *
                    ∑ v, selected tree z v *
                      (restCoefficient * (envelope v w * envelopeTail)) := by
                  apply Finset.sum_le_sum
                  intro z _
                  gcongr with v
                  simpa only [restCoefficient, envelopeTail,
                    List.map_cons, List.prod_cons] using
                      ihTrees ((v, w) :: segments)
              _ = restCoefficient *
                    ((∑ z, inward u z *
                      ∑ v, selected tree z v * envelope v w) *
                      envelopeTail) := by
                  simp_rw [show ∀ (z : Inner) (v : Middle),
                    selected tree z v *
                        (restCoefficient * (envelope v w * envelopeTail)) =
                      restCoefficient * envelopeTail *
                        (selected tree z v * envelope v w) by
                    intros; ac_rfl]
                  simp_rw [← Finset.mul_sum]
                  simp_rw [show ∀ (z : Inner) (value : ℝ≥0∞),
                    inward u z * (restCoefficient * envelopeTail * value) =
                      (restCoefficient * envelopeTail) *
                        (inward u z * value) by intros; ac_rfl]
                  rw [← Finset.mul_sum]
                  ac_rfl
              _ ≤ restCoefficient *
                    ((∑ z, inward u z *
                      (loss tree * distortion *
                        ∑ v, baseline tree z v * envelope v w)) *
                      envelopeTail) := by
                  gcongr with z
                  exact hweighted tree z w
              _ = restCoefficient *
                    ((loss tree * distortion *
                      ∑ z, inward u z *
                        ∑ v, baseline tree z v * envelope v w) *
                      envelopeTail) := by
                  simp_rw [show ∀ (z : Inner) (value : ℝ≥0∞),
                    inward u z * (loss tree * distortion * value) =
                      (loss tree * distortion) * (inward u z * value) by
                    intros; ac_rfl]
                  rw [← Finset.mul_sum]
              _ = totalCoefficient *
                    ((∑ z, inward u z *
                      ∑ v, baseline tree z v * envelope v w) *
                      envelopeTail) := by
                  rw [htotal]
                  ac_rfl
          calc
            heterogeneousMultiRenewalKernel inward selected escape
                ((u, w) :: segments) (tree :: rest) =
                escape u w *
                    heterogeneousMultiRenewalKernel inward selected escape
                      segments (tree :: rest) +
                  ∑ z, inward u z *
                    ∑ v, selected tree z v *
                      heterogeneousMultiRenewalKernel inward selected escape
                        ((v, w) :: segments) rest := by
                  rw [heterogeneousMultiRenewalKernel]
            _ ≤ totalCoefficient * (escape u w * envelopeTail) +
                totalCoefficient *
                  ((∑ z, inward u z *
                    ∑ v, baseline tree z v * envelope v w) *
                    envelopeTail) := add_le_add hescape hchild
            _ = totalCoefficient *
                ((escape u w +
                    ∑ z, inward u z *
                      ∑ v, baseline tree z v * envelope v w) *
                  envelopeTail) := by ring
            _ ≤ totalCoefficient * (envelope u w * envelopeTail) := by
                gcongr
                exact hrenew tree u w
            _ = ((tree :: rest).map loss).prod *
                distortion ^ (tree :: rest).length *
                  (((u, w) :: segments).map fun segment ↦
                    envelope segment.1 segment.2).prod := by
                simp only [totalCoefficient, envelopeTail, List.map_cons,
                  List.prod_cons]

/-- Well-founded weight for a list of pending or active remote segments. -/
private def preludeStageWeight {Near Middle Exit : Type*} :
    List ((Near ⊕ Middle) × Exit) → ℕ
  | [] => 0
  | (Sum.inl _, _) :: rest => 2 + preludeStageWeight rest
  | (Sum.inr _, _) :: rest => 1 + preludeStageWeight rest

/-- A list of remote segments with a preliminary entrance layer.  A pending
segment may either exit directly or first enter the active middle boundary;
an active segment then follows the usual child-renewal recursion. -/
def heterogeneousPreludeMultiRenewalKernel
    {Near Middle Inner Exit Tree : Type*}
    [Fintype Middle] [Fintype Inner]
    (enter : Near → Middle → ℝ≥0∞)
    (direct : Near → Exit → ℝ≥0∞)
    (inward : Middle → Inner → ℝ≥0∞)
    (child : Tree → Inner → Middle → ℝ≥0∞)
    (escape : Middle → Exit → ℝ≥0∞) :
    List ((Near ⊕ Middle) × Exit) → List Tree → ℝ≥0∞
  | [], [] => 1
  | [], _ :: _ => 0
  | (Sum.inl start, w) :: segments, trees =>
      direct start w * heterogeneousPreludeMultiRenewalKernel enter direct
        inward child escape segments trees +
      ∑ u, enter start u * heterogeneousPreludeMultiRenewalKernel enter direct
        inward child escape ((Sum.inr u, w) :: segments) trees
  | (Sum.inr u, w) :: segments, [] =>
      escape u w * heterogeneousPreludeMultiRenewalKernel enter direct
        inward child escape segments []
  | (Sum.inr u, w) :: segments, tree :: rest =>
      escape u w * heterogeneousPreludeMultiRenewalKernel enter direct
        inward child escape segments (tree :: rest) +
      ∑ z, inward u z *
        ∑ v, child tree z v *
          heterogeneousPreludeMultiRenewalKernel enter direct inward child
            escape ((Sum.inr v, w) :: segments) rest
termination_by segments trees =>
  preludeStageWeight segments + trees.length
decreasing_by
  all_goals simp [preludeStageWeight]

/-- Global-envelope comparison for the preliminary-entrance renewal.  Exact
or one-sided renewal inequalities are allowed independently at the pending
and active stages. -/
theorem heterogeneousPreludeMultiRenewalKernel_le_envelope
    {Near Middle Inner Exit Tree : Type*}
    [Fintype Middle] [Fintype Inner]
    (enter : Near → Middle → ℝ≥0∞)
    (direct : Near → Exit → ℝ≥0∞)
    (inward : Middle → Inner → ℝ≥0∞)
    (selected baseline : Tree → Inner → Middle → ℝ≥0∞)
    (escape : Middle → Exit → ℝ≥0∞)
    (nearEnvelope : Near → Exit → ℝ≥0∞)
    (middleEnvelope : Middle → Exit → ℝ≥0∞)
    (loss : Tree → ℝ≥0∞) (distortion : ℝ≥0∞)
    (hweighted : ∀ (tree : Tree) (z : Inner) (w : Exit),
      (∑ v, selected tree z v * middleEnvelope v w) ≤
        loss tree * distortion *
          ∑ v, baseline tree z v * middleEnvelope v w)
    (hescape : ∀ (u : Middle) (w : Exit),
      escape u w ≤ middleEnvelope u w)
    (hmiddle : ∀ (tree : Tree) (u : Middle) (w : Exit),
      escape u w +
          ∑ z, inward u z *
            ∑ v, baseline tree z v * middleEnvelope v w ≤
        middleEnvelope u w)
    (hnear : ∀ (start : Near) (w : Exit),
      direct start w + ∑ u, enter start u * middleEnvelope u w ≤
        nearEnvelope start w) :
    ∀ (trees : List Tree) (segments : List ((Near ⊕ Middle) × Exit)),
      heterogeneousPreludeMultiRenewalKernel enter direct inward selected
          escape segments trees ≤
        (trees.map loss).prod * distortion ^ trees.length *
          (segments.map fun segment ↦ match segment.1 with
            | Sum.inl start => nearEnvelope start segment.2
            | Sum.inr u => middleEnvelope u segment.2).prod := by
  intro trees
  induction trees with
  | nil =>
      intro segments
      induction segments with
      | nil => simp [heterogeneousPreludeMultiRenewalKernel]
      | cons segment segments ihSegments =>
          rcases segment with ⟨stage, w⟩
          cases stage with
          | inr u =>
              simpa only [heterogeneousPreludeMultiRenewalKernel,
                List.map_nil, List.prod_nil, List.length_nil, pow_zero,
                one_mul, List.map_cons, List.prod_cons] using
                  mul_le_mul (hescape u w)
                    ihSegments (by positivity) (by positivity)
          | inl start =>
              rw [heterogeneousPreludeMultiRenewalKernel]
              simp only [List.map_nil, List.prod_nil, List.length_nil,
                pow_zero, one_mul, List.map_cons, List.prod_cons]
              calc
                direct start w *
                      heterogeneousPreludeMultiRenewalKernel enter direct
                        inward selected escape segments [] +
                    ∑ u, enter start u *
                      heterogeneousPreludeMultiRenewalKernel enter direct
                        inward selected escape
                        ((Sum.inr u, w) :: segments) [] ≤
                    direct start w *
                        (segments.map fun segment ↦ match segment.1 with
                          | Sum.inl start => nearEnvelope start segment.2
                          | Sum.inr u => middleEnvelope u segment.2).prod +
                      ∑ u, enter start u *
                        (middleEnvelope u w *
                          (segments.map fun segment ↦ match segment.1 with
                            | Sum.inl start => nearEnvelope start segment.2
                            | Sum.inr v => middleEnvelope v segment.2).prod) := by
                    apply add_le_add
                    · exact mul_le_mul_of_nonneg_left
                        (by simpa only [List.map_nil, List.prod_nil,
                          List.length_nil, pow_zero, one_mul] using ihSegments)
                        (by positivity)
                    · apply Finset.sum_le_sum
                      intro u _
                      apply mul_le_mul_of_nonneg_left _ (by positivity)
                      simp only [heterogeneousPreludeMultiRenewalKernel]
                      exact mul_le_mul (hescape u w)
                        (by simpa only [List.map_nil, List.prod_nil,
                          List.length_nil, pow_zero, one_mul] using ihSegments)
                        (by positivity) (by positivity)
                _ = (direct start w +
                      ∑ u, enter start u * middleEnvelope u w) *
                  (segments.map fun segment ↦ match segment.1 with
                      | Sum.inl start => nearEnvelope start segment.2
                      | Sum.inr u => middleEnvelope u segment.2).prod := by
                    rw [add_mul, Finset.sum_mul]
                    apply congrArg₂ ( · + · )
                    · rfl
                    · apply Finset.sum_congr rfl
                      intro u _
                      ac_rfl
                _ ≤ nearEnvelope start w *
                    (segments.map fun segment ↦ match segment.1 with
                      | Sum.inl start => nearEnvelope start segment.2
                      | Sum.inr u => middleEnvelope u segment.2).prod := by
                    gcongr
                    exact hnear start w
  | cons tree rest ihTrees =>
      intro segments
      induction segments with
      | nil => simp [heterogeneousPreludeMultiRenewalKernel]
      | cons segment segments ihSegments =>
          rcases segment with ⟨stage, w⟩
          let restCoefficient : ℝ≥0∞ :=
            (rest.map loss).prod * distortion ^ rest.length
          let totalCoefficient : ℝ≥0∞ :=
            ((tree :: rest).map loss).prod *
              distortion ^ (tree :: rest).length
          let envelopeTail : ℝ≥0∞ :=
            (segments.map fun segment ↦ match segment.1 with
              | Sum.inl start => nearEnvelope start segment.2
              | Sum.inr u => middleEnvelope u segment.2).prod
          have htotal : totalCoefficient =
              restCoefficient * (loss tree * distortion) := by
            simp only [totalCoefficient, restCoefficient, List.map_cons,
              List.prod_cons, List.length_cons, pow_succ]
            ac_rfl
          have hactive (u : Middle) :
              heterogeneousPreludeMultiRenewalKernel enter direct inward
                  selected escape ((Sum.inr u, w) :: segments)
                    (tree :: rest) ≤
                totalCoefficient * (middleEnvelope u w * envelopeTail) := by
            have hescapeTerm :
                escape u w * heterogeneousPreludeMultiRenewalKernel
                    enter direct inward selected escape segments
                      (tree :: rest) ≤
                  totalCoefficient * (escape u w * envelopeTail) := by
              calc
                _ ≤ escape u w * (totalCoefficient * envelopeTail) := by
                  exact mul_le_mul_of_nonneg_left
                    (by simpa only [totalCoefficient, envelopeTail] using
                      ihSegments) (by positivity)
                _ = totalCoefficient * (escape u w * envelopeTail) := by
                  ac_rfl
            have hchildTerm :
                (∑ z, inward u z *
                  ∑ v, selected tree z v *
                    heterogeneousPreludeMultiRenewalKernel enter direct inward
                      selected escape ((Sum.inr v, w) :: segments) rest) ≤
                  totalCoefficient *
                    ((∑ z, inward u z *
                      ∑ v, baseline tree z v * middleEnvelope v w) *
                      envelopeTail) := by
              calc
                _ ≤ ∑ z, inward u z *
                      ∑ v, selected tree z v *
                        (restCoefficient *
                          (middleEnvelope v w * envelopeTail)) := by
                    apply Finset.sum_le_sum
                    intro z _
                    gcongr with v
                    simpa only [restCoefficient, envelopeTail,
                      List.map_cons, List.prod_cons] using
                        ihTrees ((Sum.inr v, w) :: segments)
                _ = restCoefficient *
                      ((∑ z, inward u z *
                        ∑ v, selected tree z v * middleEnvelope v w) *
                        envelopeTail) := by
                    simp_rw [show ∀ (z : Inner) (v : Middle),
                      selected tree z v *
                          (restCoefficient *
                            (middleEnvelope v w * envelopeTail)) =
                        restCoefficient * envelopeTail *
                          (selected tree z v * middleEnvelope v w) by
                        intros; ac_rfl]
                    simp_rw [← Finset.mul_sum]
                    simp_rw [show ∀ (z : Inner) (value : ℝ≥0∞),
                      inward u z * (restCoefficient * envelopeTail * value) =
                        (restCoefficient * envelopeTail) *
                          (inward u z * value) by intros; ac_rfl]
                    rw [← Finset.mul_sum]
                    ac_rfl
                _ ≤ restCoefficient *
                      ((∑ z, inward u z *
                        (loss tree * distortion *
                          ∑ v, baseline tree z v * middleEnvelope v w)) *
                        envelopeTail) := by
                    gcongr with z
                    exact hweighted tree z w
                _ = totalCoefficient *
                      ((∑ z, inward u z *
                        ∑ v, baseline tree z v * middleEnvelope v w) *
                        envelopeTail) := by
                    rw [htotal]
                    simp_rw [show ∀ (z : Inner) (value : ℝ≥0∞),
                      inward u z * (loss tree * distortion * value) =
                        (loss tree * distortion) * (inward u z * value) by
                        intros; ac_rfl]
                    rw [← Finset.mul_sum]
                    ac_rfl
            rw [heterogeneousPreludeMultiRenewalKernel]
            calc
              _ ≤ totalCoefficient * (escape u w * envelopeTail) +
                  totalCoefficient *
                    ((∑ z, inward u z *
                      ∑ v, baseline tree z v * middleEnvelope v w) *
                      envelopeTail) := add_le_add hescapeTerm hchildTerm
              _ = totalCoefficient *
                  ((escape u w + ∑ z, inward u z *
                    ∑ v, baseline tree z v * middleEnvelope v w) *
                    envelopeTail) := by ring
              _ ≤ totalCoefficient *
                  (middleEnvelope u w * envelopeTail) := by
                    gcongr
                    exact hmiddle tree u w
          cases stage with
          | inr u =>
              simpa only [totalCoefficient, envelopeTail, List.map_cons,
                List.prod_cons] using hactive u
          | inl start =>
              calc
                heterogeneousPreludeMultiRenewalKernel enter direct inward
                    selected escape ((Sum.inl start, w) :: segments)
                      (tree :: rest) ≤
                  direct start w * (totalCoefficient * envelopeTail) +
                    ∑ u, enter start u *
                      (totalCoefficient *
                        (middleEnvelope u w * envelopeTail)) := by
                    rw [heterogeneousPreludeMultiRenewalKernel]
                    apply add_le_add
                    · exact mul_le_mul_of_nonneg_left
                        (by simpa only [totalCoefficient, envelopeTail] using
                          ihSegments) (by positivity)
                    · apply Finset.sum_le_sum
                      intro u _
                      exact mul_le_mul_of_nonneg_left (hactive u)
                        (by positivity)
                _ = totalCoefficient *
                    ((direct start w +
                      ∑ u, enter start u * middleEnvelope u w) *
                      envelopeTail) := by
                    simp_rw [show ∀ (u : Middle),
                      enter start u *
                          (totalCoefficient *
                            (middleEnvelope u w * envelopeTail)) =
                        totalCoefficient * envelopeTail *
                          (enter start u * middleEnvelope u w) by
                        intros; ac_rfl]
                    rw [← Finset.mul_sum]
                    calc
                      direct start w * (totalCoefficient * envelopeTail) +
                          totalCoefficient * envelopeTail *
                            (∑ u, enter start u * middleEnvelope u w) =
                        totalCoefficient * (direct start w * envelopeTail) +
                          totalCoefficient *
                            ((∑ u, enter start u * middleEnvelope u w) *
                              envelopeTail) := by
                            apply congrArg₂ ( · + · ) <;> ac_rfl
                      _ = totalCoefficient *
                          (direct start w * envelopeTail +
                            (∑ u, enter start u * middleEnvelope u w) *
                              envelopeTail) := by
                            rw [mul_add]
                      _ = totalCoefficient *
                          ((direct start w +
                            ∑ u, enter start u * middleEnvelope u w) *
                              envelopeTail) := by
                            rw [add_mul]
                _ ≤ totalCoefficient *
                    (nearEnvelope start w * envelopeTail) := by
                    gcongr
                    exact hnear start w
                _ = ((tree :: rest).map loss).prod *
                    distortion ^ (tree :: rest).length *
                      (((Sum.inl start, w) :: segments).map fun segment ↦
                        match segment.1 with
                        | Sum.inl start => nearEnvelope start segment.2
                        | Sum.inr u => middleEnvelope u segment.2).prod := by
                    simp only [totalCoefficient, envelopeTail, List.map_cons,
                      List.prod_cons]

/-- Specialization to recursive profile-gap kernels.  Each selected tree is
replaced by the unrestricted leaf at the same physical child boundary. -/
theorem heterogeneousRecursiveRenewalKernel_le_leaf
    {n k : ℕ} {center : Point} {Exit : Type*}
    (inward : ProfileCycleOuterPoint n k center →
      ProfileCycleMiddlePoint n k center → ℝ≥0∞)
    (escape : ProfileCycleOuterPoint n k center → Exit → ℝ≥0∞)
    (loss : ProfileRefinementTree → ℝ≥0∞)
    (distortion : ℝ≥0∞)
    (hrow : ∀ (tree : ProfileRefinementTree)
      (z : ProfileCycleMiddlePoint n k center),
      ∑ v, recursiveProfileGapKernelENNReal n k center tree z v ≤ loss tree)
    (hsuffix : ∀ (trees : List ProfileRefinementTree) (w : Exit),
      ∃ reference : ℝ≥0∞,
        (∀ v, reference ≤
          heterogeneousRenewalKernel inward
            (fun _ z v ↦ recursiveProfileGapKernelENNReal
              n k center .leaf z v) escape trees v w) ∧
        (∀ v, heterogeneousRenewalKernel inward
            (fun _ z v ↦ recursiveProfileGapKernelENNReal
              n k center .leaf z v) escape trees v w ≤
          distortion * reference))
    (trees : List ProfileRefinementTree)
    (u : ProfileCycleOuterPoint n k center) (w : Exit) :
    heterogeneousRenewalKernel inward
        (recursiveProfileGapKernelENNReal n k center) escape trees u w ≤
      (trees.map loss).prod * distortion ^ trees.length *
        heterogeneousRenewalKernel inward
          (fun _ z v ↦ recursiveProfileGapKernelENNReal
            n k center .leaf z v) escape trees u w := by
  apply heterogeneousRenewalKernel_le_baseline inward
    (recursiveProfileGapKernelENNReal n k center)
    (fun _ z v ↦ recursiveProfileGapKernelENNReal n k center .leaf z v)
    escape loss distortion
  · intro tree z continuation reference hlower hupper
    exact weighted_recursiveProfileGapKernelENNReal_le z continuation
      reference (loss tree) distortion (hrow tree z) hlower hupper
  · exact hsuffix

/-- Fixed-chain form of the padded substitution.  The recursive row losses
collapse to the usual gap-chain reference mass, while the remote-prefix
oscillation is charged once for every top-level child. -/
theorem eventually_profileRefinementChainRenewalKernel_le_leaf :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (k : ℕ), 0 < k →
      ∀ (a : ℕ) (rest : List ℕ), k + rest.length ≤ n →
      ∀ (chain : GapChain (a :: rest)) (center : Point)
        (Exit : Type*)
        (inward : ProfileCycleOuterPoint n k center →
          ProfileCycleMiddlePoint n k center → ℝ≥0∞)
        (escape : ProfileCycleOuterPoint n k center → Exit → ℝ≥0∞)
        (distortion : ℝ≥0∞),
      (∀ (trees : List ProfileRefinementTree) (w : Exit),
        ∃ reference : ℝ≥0∞,
          (∀ v, reference ≤
            heterogeneousRenewalKernel inward
              (fun _ z v ↦ recursiveProfileGapKernelENNReal
                n k center .leaf z v) escape trees v w) ∧
          (∀ v, heterogeneousRenewalKernel inward
              (fun _ z v ↦ recursiveProfileGapKernelENNReal
                n k center .leaf z v) escape trees v w ≤
            distortion * reference)) →
      ∀ (u : ProfileCycleOuterPoint n k center) (w : Exit),
        heterogeneousRenewalKernel inward
            (recursiveProfileGapKernelENNReal n k center) escape
            (List.ofFn fun i : Fin a ↦
              profileRefinementTrees a rest chain i) u w ≤
          ENNReal.ofReal
              ((1 + 1 / (n : ℝ) ^ 6) ^
                  AnnularIntegratedProfileKernel.radialWordLength (a :: rest) *
                gapChainMass (a :: rest) chain) *
            distortion ^ a *
              heterogeneousRenewalKernel inward
                (fun _ z v ↦ recursiveProfileGapKernelENNReal
                  n k center .leaf z v) escape
                (List.ofFn fun i : Fin a ↦
                  profileRefinementTrees a rest chain i) u w := by
  classical
  filter_upwards [eventually_profileRefinementTreeKernel_row_le]
      with n hrow
  intro k hk a rest hdepth chain center Exit inward escape distortion
    hsuffix u w
  let halfRow : ℝ := (1 + 1 / (n : ℝ) ^ 6) / 2
  let tree : Fin a → ProfileRefinementTree := fun i ↦
    profileRefinementTrees a rest chain i
  let trees : List ProfileRefinementTree := List.ofFn tree
  let loss : ProfileRefinementTree → ℝ≥0∞ := fun t ↦
    if ht : ∃ i, tree i = t then
      ENNReal.ofReal (profileRefinementTreeCost halfRow (tree (Classical.choose ht)))
    else ∞
  have hcost0 (i : Fin a) :
      0 ≤ profileRefinementTreeCost halfRow (tree i) := by
    apply profileRefinementTreeCost_nonneg
    dsimp only [halfRow]
    positivity
  have hloss_tree (i : Fin a) : loss (tree i) =
      ENNReal.ofReal (profileRefinementTreeCost halfRow (tree i)) := by
    dsimp only [loss]
    split
    next h =>
      congr 2
      exact Classical.choose_spec h
    next h => exact (h ⟨i, rfl⟩).elim
  have hsubstitute := heterogeneousRecursiveRenewalKernel_le_leaf
    inward escape loss distortion
    (fun t z ↦ by
      by_cases ht : ∃ i, tree i = t
      · let i := Classical.choose ht
        have hi : tree i = t := Classical.choose_spec ht
        rw [← hi, hloss_tree i]
        simpa only [halfRow, tree] using
          hrow k hk a rest hdepth chain i center z
      · simp only [loss, dif_neg ht]
        exact le_top)
    hsuffix trees u w
  have hloss : (trees.map loss).prod =
      ENNReal.ofReal
        ((1 + 1 / (n : ℝ) ^ 6) ^
            AnnularIntegratedProfileKernel.radialWordLength (a :: rest) *
          gapChainMass (a :: rest) chain) := by
    calc
      (trees.map loss).prod =
          ∏ i : Fin a, ENNReal.ofReal
            (profileRefinementTreeCost halfRow (tree i)) := by
              simp only [trees, List.map_ofFn, List.prod_ofFn,
                Function.comp_apply, hloss_tree]
      _ = ENNReal.ofReal
          (∏ i : Fin a, profileRefinementTreeCost halfRow (tree i)) := by
            symm
            apply ENNReal.ofReal_prod_of_nonneg
            intro i _
            exact hcost0 i
      _ = ENNReal.ofReal
          ((1 + 1 / (n : ℝ) ^ 6) ^
              AnnularIntegratedProfileKernel.radialWordLength (a :: rest) *
            gapChainMass (a :: rest) chain) := by
            rw [show (∏ i : Fin a,
              profileRefinementTreeCost halfRow (tree i)) =
                (2 * halfRow) ^
                    AnnularIntegratedProfileKernel.radialWordLength (a :: rest) *
                  gapChainMass (a :: rest) chain by
              exact prod_profileRefinementTreeCost_eq a rest chain halfRow]
            congr 2
            dsimp only [halfRow]
            ring
  simpa only [trees, tree, List.length_ofFn, hloss] using hsubstitute

end

end Erdos1165.AnnularRecursiveWeightedRenewal
