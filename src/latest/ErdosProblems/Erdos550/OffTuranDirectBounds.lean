import Mathlib
import ErdosProblems.Erdos550.HPClusterWeights
import ErdosProblems.Erdos550.HPTrimmedThreshold
import ErdosProblems.Erdos550.OffTuranConstants
import ErdosProblems.Erdos550.OffTuranReducedDegreeData
import ErdosProblems.Erdos550.OffTuranReducedEmbedding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite and scalar bounds for the direct off--Turán instantiation

This file contains the elementary estimates which are independent of the
source tree and the host graph.  They turn the exact equipartition and indexed
matching data into the uniform bounds used in the final direct proof.
-/

open Finset SimpleGraph Finpartition SzemerediRegularity

namespace Erdos550

open Classical

/-- An indexed matching has at most half as many edges as there are ambient
cluster indices. -/
lemma two_mul_matching_card_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (cL cR : κ → ι)
    (hinj : Function.Injective (Sum.elim cL cR)) :
    2 * Fintype.card κ ≤ Fintype.card ι := by
  have h :=
    Fintype.card_le_of_injective (Sum.elim cL cR) hinj
  simpa [Fintype.card_sum, two_mul] using! h

/-- The union of all matching endpoints is no larger than the ambient cluster
type. -/
lemma matchingTargets_card_le
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (cL cR : κ → ι) :
    (offTuranMatchingTargets cL cR).card ≤ Fintype.card ι := by
  exact Finset.card_le_univ _

lemma OffTuranReducedDegreeData.parts_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {ε d base η : ℝ} {m₀ : ℕ}
    (D : OffTuranReducedDegreeData G ε d base η m₀)
    (hε : 0 < ε) :
    0 < D.P.parts.card := by
  have hceil : 0 < ⌈4 / ε⌉₊ := by
    apply Nat.ceil_pos.mpr
    positivity
  exact hceil.trans_le D.lower_parts

/-- The floor of the average part size is a lower bound for every equitable
part. -/
lemma OffTuranReducedDegreeData.floor_le_part
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {ε d base η : ℝ} {m₀ : ℕ}
    (D : OffTuranReducedDegreeData G ε d base η m₀)
    (i : {C // C ∈ D.P.parts}) :
    Fintype.card V / D.P.parts.card ≤ i.1.card := by
  have h := D.equipartition.average_le_card_part i.2
  simpa only [Finset.card_univ] using! h

/-- Exact rounding estimate for the scale retained in reduced-degree data. -/
lemma OffTuranReducedDegreeData.parts_mul_scale_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {ε d base η : ℝ} {m₀ : ℕ}
    (D : OffTuranReducedDegreeData G ε d base η m₀) :
    D.P.parts.card * D.scale ≤
      Fintype.card V + D.P.parts.card := by
  rw [D.scale_eq]
  calc
    D.P.parts.card *
          (Fintype.card V / D.P.parts.card + 1) =
        D.P.parts.card *
            (Fintype.card V / D.P.parts.card) +
          D.P.parts.card := by simp [Nat.mul_add]
    _ ≤ Fintype.card V + D.P.parts.card := by
      exact Nat.add_le_add_right
        (Nat.mul_div_le (Fintype.card V) D.P.parts.card) _

/-- Once the average part size is nonzero, the rounded scale is at most twice
the floor part size. -/
lemma OffTuranReducedDegreeData.scale_le_two_floor
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {ε d base η : ℝ} {m₀ : ℕ}
    (D : OffTuranReducedDegreeData G ε d base η m₀)
    (hfloor : 1 ≤ Fintype.card V / D.P.parts.card) :
    D.scale ≤ 2 * (Fintype.card V / D.P.parts.card) := by
  rw [D.scale_eq]
  omega

/-- The twice-trimmed endpoint threshold fits in the floor part size once its
rounding loss absorbs one vertex. -/
lemma offTuran_threshold_le_floor
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (head target : ι)
    (ε cap : ℝ)
    (hε0 : 0 ≤ ε) (hcap0 : 0 ≤ cap)
    (hcap : cap ≤ (C target).card)
    (hsize : ((C target).card : ℝ) ≤ cap + 1)
    (hround : 1 ≤ 2 * ε * cap) :
    hpTrimmedThreshold
        (hpHeadEndpointWeight G R C head target)
        ε ((C target).card : ℝ) ≤ cap := by
  apply hpTrimmedThreshold_le_rounded_cap
  · exact hpHeadEndpointWeight_le_card G R C head target
  · exact hε0
  · exact hcap0
  · exact hcap
  · exact hsize
  · exact hround

/-- The dynamic threshold used for the low-bad head core is positive. -/
lemma offTuran_bad_threshold_pos
    (ε ell η : ℝ) (hε : 0 < ε) (hell : 0 < ell) (hη : 0 < η) :
    0 < 8 * ε * ell / η := by
  positivity

/-- With `thr = 8 ε ell / η`, the two head-core deletions cost at most
`(ε+η/8)` of the head cluster. -/
lemma offTuran_headCoreLoss_le
    {V ι : Type*} [Fintype V]
    (ε η ell : ℝ) (Tset : Finset ι) (head : Finset V)
    (hε : 0 < ε) (hη : 0 < η) (hell : 0 < ell)
    (hT : (Tset.card : ℝ) ≤ ell) :
    hpHeadCoreLoss ε (8 * ε * ell / η) Tset head ≤
      (ε + η / 8) * (head.card : ℝ) := by
  rw [hpHeadCoreLoss]
  have hhead : (0 : ℝ) ≤ head.card := by positivity
  have hfrac :
      ((Tset.card : ℝ) * ε * (head.card : ℝ)) /
          (8 * ε * ell / η) ≤
        η / 8 * (head.card : ℝ) := by
    rw [div_le_iff₀ (offTuran_bad_threshold_pos ε ell η hε hell hη)]
    have h := mul_le_mul_of_nonneg_right hT
      (mul_nonneg hε.le hhead)
    field_simp
    nlinarith [h, mul_nonneg hη.le hhead]
  nlinarith

/-- A convenient ratio estimate: two nonnegative demands whose sum is below a
common positive lower bound occupy less than one unit of total supply. -/
lemma two_ratio_lt_one_of_sum_lt
    (a b sx sy S : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hS : 0 < S) (hxs : S ≤ sx) (hys : S ≤ sy)
    (hab : a + b < S) :
    a / sx + b / sy < 1 := by
  have hsx : 0 < sx := hS.trans_le hxs
  have hsy : 0 < sy := hS.trans_le hys
  have hax : a / sx ≤ a / S :=
    div_le_div_of_nonneg_left ha hS hxs
  have hby : b / sy ≤ b / S :=
    div_le_div_of_nonneg_left hb hS hys
  have hab' : a / S + b / S < 1 := by
    rw [← add_div, div_lt_one hS]
    exact hab
  linarith

end Erdos550
