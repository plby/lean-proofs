/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 492.
https://www.erdosproblems.com/forum/thread/492

Informal authors:
- Wolfgang M. Schmidt

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos492.md
-/
import Mathlib
import ErdosProblems.Erdos378.WeightedCircleEquidistribution

/-!
# Erdős Problem 492

The problem as printed asks for a strictly increasing sequence of natural
numbers.  Under this literal hypothesis the answer is positive: the endpoint
counting hypothesis in Davenport--Erdős is automatic.  Schmidt's negative
example concerns the original formulation with arbitrary positive real
subdivision points.  The detailed mathematical proof and the source
reconciliation are in `tex/492.tex`.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology ComplexConjugate

namespace Erdos492

noncomputable section

/-- A positive, strictly increasing natural-number subdivision whose
consecutive ratios tend to one. -/
structure NatSubdivision where
  seq : ℕ → ℕ
  pos : ∀ n, 0 < seq n
  strictMono : StrictMono seq
  ratio_tendsto :
    Tendsto (fun n ↦ (seq (n + 1) : ℝ) / (seq n : ℝ)) atTop (𝓝 1)

namespace NatSubdivision

variable (A : NatSubdivision)

lemma add_le_seq (n : ℕ) : A.seq 0 + n ≤ A.seq n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : A.seq n + 1 ≤ A.seq (n + 1) :=
        Nat.succ_le_iff.mpr (A.strictMono (Nat.lt_succ_self n))
      omega

lemma self_lt_seq (n : ℕ) : n < A.seq n := by
  have h0 := A.pos 0
  have h := A.add_le_seq n
  omega

lemma tendsto_seq_atTop : Tendsto A.seq atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b, ?_⟩
  intro n hn
  exact hn.trans (Nat.le_of_lt (A.self_lt_seq n))

lemma exists_lt_seq_succ (x : ℝ) : ∃ i : ℕ, x < A.seq (i + 1) := by
  obtain ⟨n : ℕ, hn : x < n⟩ := exists_nat_gt x
  refine ⟨n, hn.trans_le ?_⟩
  exact_mod_cast (Nat.le_succ n).trans
    (Nat.le_of_lt (A.self_lt_seq (n + 1)))

/-- The least cell whose upper endpoint is strictly above `x`.
It is total; below the first endpoint it returns zero. -/
def cellIndex (x : ℝ) : ℕ :=
  Nat.find (A.exists_lt_seq_succ x)

lemma lt_seq_cellIndex_succ (x : ℝ) :
    x < A.seq (A.cellIndex x + 1) := by
  exact Nat.find_spec (A.exists_lt_seq_succ x)

lemma seq_cellIndex_le {x : ℝ} (hx : (A.seq 0 : ℝ) ≤ x) :
    (A.seq (A.cellIndex x) : ℝ) ≤ x := by
  by_cases hzero : A.cellIndex x = 0
  · simpa [hzero] using hx
  · have hpred : A.cellIndex x - 1 < A.cellIndex x := by omega
    have hmin := Nat.find_min (A.exists_lt_seq_succ x) hpred
    have hs : A.cellIndex x - 1 + 1 = A.cellIndex x := by omega
    have : ¬x < (A.seq (A.cellIndex x) : ℝ) := by
      simpa [hs] using hmin
    exact le_of_not_gt this

lemma cellIndex_eq_of_mem {x : ℝ} {i : ℕ}
    (hlo : (A.seq i : ℝ) ≤ x) (hhi : x < A.seq (i + 1)) :
    A.cellIndex x = i := by
  apply le_antisymm
  · exact Nat.find_min' (A.exists_lt_seq_succ x) hhi
  · by_contra h
    have hlt : A.cellIndex x < i := by omega
    have hmono : A.seq (A.cellIndex x + 1) ≤ A.seq i := by
      exact A.strictMono.monotone (by omega)
    have hcast : (A.seq (A.cellIndex x + 1) : ℝ) ≤ A.seq i := by
      exact_mod_cast hmono
    exact (not_lt_of_ge (hcast.trans hlo)) (A.lt_seq_cellIndex_succ x)

/-- The generalized fractional-position map attached to a subdivision.
The value below the first endpoint is fixed to zero. -/
def fractionalPosition (x : ℝ) : ℝ :=
  if (A.seq 0 : ℝ) ≤ x then
    let i := A.cellIndex x
    (x - A.seq i) / ((A.seq (i + 1) : ℝ) - A.seq i)
  else 0

lemma gap_pos (i : ℕ) :
    (0 : ℝ) < (A.seq (i + 1) : ℝ) - A.seq i := by
  exact sub_pos.mpr (by exact_mod_cast A.strictMono (Nat.lt_succ_self i))

lemma fractionalPosition_eq {x : ℝ} (hx : (A.seq 0 : ℝ) ≤ x) :
    A.fractionalPosition x =
      (x - A.seq (A.cellIndex x)) /
        ((A.seq (A.cellIndex x + 1) : ℝ) - A.seq (A.cellIndex x)) := by
  simp [fractionalPosition, hx]

lemma fractionalPosition_mem_Ico {x : ℝ} (hx : (A.seq 0 : ℝ) ≤ x) :
    A.fractionalPosition x ∈ Ico (0 : ℝ) 1 := by
  rw [A.fractionalPosition_eq hx]
  have hlo := A.seq_cellIndex_le hx
  have hhi := A.lt_seq_cellIndex_succ x
  have hgap := A.gap_pos (A.cellIndex x)
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo) hgap.le
  · exact (div_lt_one hgap).mpr (by linarith)

lemma fractionalPosition_nonneg (x : ℝ) : 0 ≤ A.fractionalPosition x := by
  by_cases hx : (A.seq 0 : ℝ) ≤ x
  · exact (A.fractionalPosition_mem_Ico hx).1
  · simp [fractionalPosition, hx]

lemma fractionalPosition_lt_one (x : ℝ) : A.fractionalPosition x < 1 := by
  by_cases hx : (A.seq 0 : ℝ) ≤ x
  · exact (A.fractionalPosition_mem_Ico hx).2
  · simp [fractionalPosition, hx]

lemma fractionalPosition_lt_iff {x t : ℝ} (hx : (A.seq 0 : ℝ) ≤ x) :
    A.fractionalPosition x < t ↔
      x < (A.seq (A.cellIndex x) : ℝ) +
        t * ((A.seq (A.cellIndex x + 1) : ℝ) - A.seq (A.cellIndex x)) := by
  rw [A.fractionalPosition_eq hx]
  rw [div_lt_iff₀ (A.gap_pos (A.cellIndex x))]
  ring_nf
  constructor <;> intro h <;> linarith

lemma gap_div_tendsto :
    Tendsto
      (fun n ↦ ((A.seq (n + 1) : ℝ) - A.seq n) / A.seq n)
      atTop (𝓝 0) := by
  have h := A.ratio_tendsto.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
  convert h using 1
  · funext n
    have hn : (A.seq n : ℝ) ≠ 0 := by exact_mod_cast (A.pos n).ne'
    field_simp
    <;> ring
  · norm_num

end NatSubdivision

/-- The number of the first `N` terms that lie in `[s,t)`. -/
noncomputable def intervalCount (u : ℕ → ℝ) (N : ℕ) (s t : ℝ) : ℕ :=
  ((Finset.range N).filter fun n ↦ u n ∈ Ico s t).card

/-- Uniform distribution in the half-open unit interval, in the exact
interval-count sense used in the problem. -/
def IsUniformlyDistributed (u : ℕ → ℝ) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
    Tendsto
      (fun N ↦ (intervalCount u N s t : ℝ) / N)
      atTop (𝓝 (t - s))

/-- The sequence from the problem, indexed from the positive integers. -/
def sampledSequence (A : NatSubdivision) (α : ℝ) : ℕ → ℝ :=
  fun n ↦ A.fractionalPosition (α * (n + 1))

/-- The left endpoint of the part of cell `j` corresponding to
fractional positions below `t`. -/
def targetLeft (A : NatSubdivision) (j : ℕ) : ℝ :=
  A.seq j

/-- The right endpoint of the part of cell `j` corresponding to
fractional positions below `t`. -/
def targetRight (A : NatSubdivision) (t : ℝ) (j : ℕ) : ℝ :=
  (A.seq j : ℝ) + t * ((A.seq (j + 1) : ℝ) - A.seq j)

/-- Union of the initial `t`-proportion of every subdivision cell. -/
def targetSet (A : NatSubdivision) (t : ℝ) : Set ℝ :=
  ⋃ j : ℕ, Ico (targetLeft A j) (targetRight A t j)

lemma measurableSet_targetSet (A : NatSubdivision) (t : ℝ) :
    MeasurableSet (targetSet A t) := by
  exact MeasurableSet.iUnion fun _ ↦ measurableSet_Ico

lemma targetRight_le_next (A : NatSubdivision) {t : ℝ} (ht : t ≤ 1) (j : ℕ) :
    targetRight A t j ≤ A.seq (j + 1) := by
  have hgap := A.gap_pos j
  dsimp [targetRight]
  nlinarith

lemma left_le_targetRight (A : NatSubdivision) {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    targetLeft A j ≤ targetRight A t j := by
  have hgap := A.gap_pos j
  dsimp [targetLeft, targetRight]
  nlinarith [mul_nonneg ht hgap.le]

lemma pairwise_disjoint_targetIntervals (A : NatSubdivision) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Pairwise fun i j : ℕ ↦ Disjoint
      (Ico (targetLeft A i) (targetRight A t i))
      (Ico (targetLeft A j) (targetRight A t j)) := by
  have aux : ∀ {i j : ℕ}, i < j → Disjoint
      (Ico (targetLeft A i) (targetRight A t i))
      (Ico (targetLeft A j) (targetRight A t j)) := by
    intro i j hlt
    apply Set.disjoint_left.2
    intro x hxi hxj
    have hir : x < targetRight A t i := hxi.2
    have hinext := targetRight_le_next A ht1 i
    have hmono : A.seq (i + 1) ≤ A.seq j := A.strictMono.monotone (by omega)
    have hcast : (A.seq (i + 1) : ℝ) ≤ A.seq j := by exact_mod_cast hmono
    have hjl : targetLeft A j ≤ x := hxj.1
    dsimp [targetLeft] at hjl
    linarith
  intro i j hij
  by_cases hlt : i < j
  · exact aux hlt
  · have hji : j < i := lt_of_le_of_ne (Nat.le_of_not_gt hlt) hij.symm
    exact (aux hji).symm

lemma fractionalPosition_lt_iff_mem_targetSet (A : NatSubdivision)
    {x t : ℝ} (hx : (A.seq 0 : ℝ) ≤ x) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    A.fractionalPosition x < t ↔ x ∈ targetSet A t := by
  rw [A.fractionalPosition_lt_iff hx]
  constructor
  · intro h
    refine Set.mem_iUnion.2 ⟨A.cellIndex x, ?_⟩
    exact ⟨A.seq_cellIndex_le hx, h⟩
  · intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h
    have hjnext : x < (A.seq (j + 1) : ℝ) :=
      hj.2.trans_le (targetRight_le_next A ht1 j)
    have hindex : A.cellIndex x = j := A.cellIndex_eq_of_mem hj.1 hjnext
    simpa [hindex, targetRight] using hj.2

/-- The exact length of `targetSet A t ∩ [0,Z)` written in terms of the
cell containing `Z`.  It is kept as an explicit real expression so the
asymptotic calculation does not depend on measure normalization details. -/
def targetLength (A : NatSubdivision) (t Z : ℝ) : ℝ :=
  if h : (A.seq 0 : ℝ) ≤ Z then
    let j := A.cellIndex Z
    t * ((A.seq j : ℝ) - A.seq 0) +
      min (Z - A.seq j)
        (t * ((A.seq (j + 1) : ℝ) - A.seq j))
  else 0

lemma targetLength_eq (A : NatSubdivision) {t Z : ℝ}
    (hZ : (A.seq 0 : ℝ) ≤ Z) :
    targetLength A t Z =
      t * ((A.seq (A.cellIndex Z) : ℝ) - A.seq 0) +
        min (Z - A.seq (A.cellIndex Z))
          (t * ((A.seq (A.cellIndex Z + 1) : ℝ) - A.seq (A.cellIndex Z))) := by
  simp [targetLength, hZ]

lemma targetLength_error_le (A : NatSubdivision) {t Z : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hZ : (A.seq 0 : ℝ) ≤ Z) :
    |targetLength A t Z - t * Z| ≤
      A.seq 0 + ((A.seq (A.cellIndex Z + 1) : ℝ) - A.seq (A.cellIndex Z)) := by
  rw [targetLength_eq A hZ]
  let j := A.cellIndex Z
  let r : ℝ := Z - A.seq j
  let g : ℝ := (A.seq (j + 1) : ℝ) - A.seq j
  have hjlo : (A.seq j : ℝ) ≤ Z := A.seq_cellIndex_le hZ
  have hjhi : Z < A.seq (j + 1) := A.lt_seq_cellIndex_succ Z
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hrg : r ≤ g := by dsimp [r, g]; linarith
  have hg0 : 0 ≤ g := (A.gap_pos j).le
  have htg0 : 0 ≤ t * g := mul_nonneg ht0 hg0
  have htgg : t * g ≤ g := by nlinarith
  have hmin0 : 0 ≤ min r (t * g) := le_min hr0 htg0
  have hming : min r (t * g) ≤ g :=
    (min_le_left _ _).trans hrg
  have htr0 : 0 ≤ t * r := mul_nonneg ht0 hr0
  have htrg : t * r ≤ g := by nlinarith
  have hpiece : |min r (t * g) - t * r| ≤ g := by
    rw [abs_le]
    constructor <;> linarith
  have ha0 : (0 : ℝ) ≤ A.seq 0 := by positivity
  have htri := abs_add_le (-t * (A.seq 0 : ℝ)) (min r (t * g) - t * r)
  have hat : |-t * (A.seq 0 : ℝ)| ≤ A.seq 0 := by
    calc
      |-t * (A.seq 0 : ℝ)| = t * A.seq 0 := by
        rw [abs_mul, abs_neg, abs_of_nonneg ht0, abs_of_nonneg ha0]
      _ ≤ A.seq 0 := by nlinarith
  change |t * (↑(A.seq j) - ↑(A.seq 0)) + min r (t * g) - t * Z| ≤ _
  have halg :
      t * (↑(A.seq j) - ↑(A.seq 0)) + min r (t * g) - t * Z =
        -t * (A.seq 0 : ℝ) + (min r (t * g) - t * r) := by
    dsimp [r]
    ring
  rw [halg]
  change _ ≤ (A.seq 0 : ℝ) + g
  exact htri.trans (add_le_add hat hpiece)

lemma tendsto_cellIndex_atTop (A : NatSubdivision) :
    Tendsto A.cellIndex atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨(A.seq b : ℝ), ?_⟩
  intro Z hZ
  by_contra h
  have hlt : A.cellIndex Z < b := by omega
  have hmono : A.seq (A.cellIndex Z + 1) ≤ A.seq b :=
    A.strictMono.monotone (by omega)
  have hcast : (A.seq (A.cellIndex Z + 1) : ℝ) ≤ A.seq b := by
    exact_mod_cast hmono
  exact (not_lt_of_ge (hcast.trans hZ)) (A.lt_seq_cellIndex_succ Z)

lemma gap_cellIndex_div_seq_tendsto (A : NatSubdivision) :
    Tendsto
      (fun Z : ℝ ↦
        ((A.seq (A.cellIndex Z + 1) : ℝ) - A.seq (A.cellIndex Z)) /
          A.seq (A.cellIndex Z))
      atTop (𝓝 0) :=
  A.gap_div_tendsto.comp (tendsto_cellIndex_atTop A)

lemma gap_cellIndex_div_tendsto (A : NatSubdivision) :
    Tendsto
      (fun Z : ℝ ↦
        ((A.seq (A.cellIndex Z + 1) : ℝ) - A.seq (A.cellIndex Z)) / Z)
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (A.seq 0 : ℝ)] with Z hZ
    have ha0 : (0 : ℝ) ≤ A.seq 0 := by positivity
    exact div_nonneg (A.gap_pos (A.cellIndex Z)).le (ha0.trans hZ)
  · filter_upwards [eventually_gt_atTop (0 : ℝ),
      eventually_ge_atTop (A.seq 0 : ℝ)] with Z hZ0 hZ
    have hjle : (A.seq (A.cellIndex Z) : ℝ) ≤ Z := A.seq_cellIndex_le hZ
    have hjpos : (0 : ℝ) < A.seq (A.cellIndex Z) := by
      exact_mod_cast A.pos (A.cellIndex Z)
    have hgap0 := (A.gap_pos (A.cellIndex Z)).le
    exact div_le_div_of_nonneg_left hgap0 hjpos hjle
  · exact gap_cellIndex_div_seq_tendsto A

lemma seq_cellIndex_div_tendsto (A : NatSubdivision) :
    Tendsto
      (fun Z : ℝ ↦ (A.seq (A.cellIndex Z) : ℝ) / Z)
      atTop (𝓝 1) := by
  have hres : Tendsto
      (fun Z : ℝ ↦ (Z - A.seq (A.cellIndex Z)) / Z)
      atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun Z : ℝ ↦
      ((A.seq (A.cellIndex Z + 1) : ℝ) - A.seq (A.cellIndex Z)) / Z)
    · filter_upwards [eventually_gt_atTop (0 : ℝ),
        eventually_ge_atTop (A.seq 0 : ℝ)] with Z hZ0 hZa
      exact div_nonneg (sub_nonneg.mpr (A.seq_cellIndex_le hZa)) hZ0.le
    · filter_upwards [eventually_gt_atTop (0 : ℝ),
        eventually_ge_atTop (A.seq 0 : ℝ)] with Z hZ0 hZa
      have hhi := A.lt_seq_cellIndex_succ Z
      have hlo := A.seq_cellIndex_le hZa
      apply (div_le_div_iff_of_pos_right hZ0).2
      linarith
    · exact gap_cellIndex_div_tendsto A
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1)).sub hres
  have heq : (fun Z : ℝ ↦ 1 - (Z - A.seq (A.cellIndex Z)) / Z) =ᶠ[atTop]
      (fun Z : ℝ ↦ (A.seq (A.cellIndex Z) : ℝ) / Z) := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with Z hZ
    field_simp
    ring
  simpa only [sub_zero] using h.congr' heq

lemma targetLength_div_tendsto (A : NatSubdivision) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Tendsto (fun Z : ℝ ↦ targetLength A t Z / Z) atTop (𝓝 t) := by
  have hinv : Tendsto (fun Z : ℝ ↦ Z⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hbase : Tendsto (fun Z : ℝ ↦ (A.seq 0 : ℝ) / Z) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (A.seq 0 : ℝ)) atTop
        (𝓝 (A.seq 0 : ℝ))).mul hinv)
  have hbound : Tendsto
      (fun Z : ℝ ↦ (A.seq 0 : ℝ) / Z +
        ((A.seq (A.cellIndex Z + 1) : ℝ) - A.seq (A.cellIndex Z)) / Z)
      atTop (𝓝 0) := by
    simpa using hbase.add (gap_cellIndex_div_tendsto A)
  have herr : Tendsto
      (fun Z : ℝ ↦ (targetLength A t Z - t * Z) / Z)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (g := fun Z : ℝ ↦ (A.seq 0 : ℝ) / Z +
      ((A.seq (A.cellIndex Z + 1) : ℝ) - A.seq (A.cellIndex Z)) / Z)
    · exact Filter.Eventually.of_forall fun Z ↦ abs_nonneg _
    · filter_upwards [eventually_gt_atTop (0 : ℝ),
        eventually_ge_atTop (A.seq 0 : ℝ)] with Z hZ hZa
      change |(targetLength A t Z - t * Z) / Z| ≤ _
      rw [abs_div, abs_of_pos hZ]
      have he := targetLength_error_le A ht0 ht1 hZa
      calc
        |targetLength A t Z - t * Z| / Z ≤
            ((A.seq 0 : ℝ) + ((A.seq (A.cellIndex Z + 1) : ℝ) -
              A.seq (A.cellIndex Z))) / Z :=
          (div_le_div_iff_of_pos_right hZ).2 he
        _ = _ := by ring
    · simpa only [Function.comp_apply] using hbound
  have hsum : Tendsto
      (fun Z : ℝ ↦ (targetLength A t Z - t * Z) / Z + t)
      atTop (𝓝 t) := by
    simpa using herr.add tendsto_const_nhds
  apply hsum.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with Z hZ
  field_simp
  <;> ring

/-! ## Metric Weyl lemma for integer frequencies -/

private abbrev UnitCircle := AddCircle (1 : ℝ)

/-- The normalized exponential sum attached to integer frequencies. -/
private def fourierAverage (r : ℕ → ℤ) (h : ℤ) (N : ℕ)
    (z : UnitCircle) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, fourier (h * r n) z

private def fourierPartialSum (r : ℕ → ℤ) (h : ℤ) (N : ℕ)
    (z : UnitCircle) : ℂ :=
  ∑ n ∈ Finset.range N, fourier (h * r n) z

private lemma fourier_memLp (k : ℤ) :
    MemLp (fourier k : UnitCircle → ℂ) 2 AddCircle.haarAddCircle := by
  apply MemLp.of_bound (fourier k).continuous.aestronglyMeasurable 1
  exact Eventually.of_forall fun z ↦ by
    rw [fourier_apply, Circle.norm_coe]

private lemma fourierPartialSum_memLp (r : ℕ → ℤ) (h : ℤ) (N : ℕ) :
    MemLp (fourierPartialSum r h N) 2 AddCircle.haarAddCircle := by
  convert memLp_finsetSum' (Finset.range N)
      (fun n _ ↦ fourier_memLp (h * r n)) using 1
  funext z
  simp [fourierPartialSum]

private lemma fourierPartialSum_toLp (r : ℕ → ℤ) (h : ℤ) (N : ℕ) :
    (fourierPartialSum_memLp r h N).toLp (fourierPartialSum r h N) =
      ∑ n ∈ Finset.range N, fourierLp (T := (1 : ℝ)) 2 (h * r n) := by
  apply Lp.ext (μ := AddCircle.haarAddCircle)
  have hall : ∀ᵐ z ∂AddCircle.haarAddCircle,
      ∀ n ∈ Finset.range N,
        fourierLp (T := (1 : ℝ)) 2 (h * r n) z = fourier (h * r n) z :=
    (Finset.eventually_all (Finset.range N)).2 fun n _ ↦
      coeFn_fourierLp (T := (1 : ℝ)) 2 (h * r n)
  filter_upwards [(fourierPartialSum_memLp r h N).coeFn_toLp,
      Lp.coeFn_fun_finsetSum (Finset.range N)
        (fun n ↦ fourierLp (T := (1 : ℝ)) 2 (h * r n)), hall] with z hz hsum hzall
  rw [hz, hsum]
  exact Finset.sum_congr rfl fun n hn ↦ (hzall n hn).symm

private lemma frequency_injective {r : ℕ → ℤ} (hr : Function.Injective r)
    {h : ℤ} (hh : h ≠ 0) : Function.Injective (fun n ↦ h * r n) := by
  intro i j hij
  apply hr
  exact mul_left_cancel₀ hh hij

private lemma fourierLp_sum_norm_sq (r : ℕ → ℤ) (hr : Function.Injective r)
    (h : ℤ) (hh : h ≠ 0) (N : ℕ) :
    ‖∑ n ∈ Finset.range N,
        fourierLp (T := (1 : ℝ)) 2 (h * r n)‖ ^ 2 = N := by
  let v : ℕ → Lp ℂ 2 AddCircle.haarAddCircle :=
    fun n ↦ fourierLp (T := (1 : ℝ)) 2 (h * r n)
  have hv : Orthonormal ℂ v := by
    simpa [v, Function.comp_def] using
      (orthonormal_fourier (T := (1 : ℝ))).comp (fun n ↦ h * r n)
        (frequency_injective hr hh)
  have hi := hv.inner_sum (fun _ ↦ (1 : ℂ)) (fun _ ↦ (1 : ℂ))
      (Finset.range N)
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  simpa [v] using congrArg Complex.re hi

private lemma integral_fourierPartialSum_norm_sq (r : ℕ → ℤ)
    (hr : Function.Injective r) (h : ℤ) (hh : h ≠ 0) (N : ℕ) :
    ∫ z : UnitCircle, ‖fourierPartialSum r h N z‖ ^ 2
        ∂AddCircle.haarAddCircle = N := by
  let F := (fourierPartialSum_memLp r h N).toLp (fourierPartialSum r h N)
  have hinner := congrArg RCLike.re
    (@L2.inner_def UnitCircle ℂ ℂ _ _ _ _ _ F F)
  rw [← integral_re (L2.integrable_inner F F)] at hinner
  simp only [← norm_sq_eq_re_inner] at hinner
  have hnorm : ‖F‖ ^ 2 = (N : ℝ) := by
    rw [show F = ∑ n ∈ Finset.range N,
        fourierLp (T := (1 : ℝ)) 2 (h * r n) by
      exact fourierPartialSum_toLp r h N]
    exact fourierLp_sum_norm_sq r hr h hh N
  rw [hnorm] at hinner
  calc
    (∫ z : UnitCircle, ‖fourierPartialSum r h N z‖ ^ 2
        ∂AddCircle.haarAddCircle) =
        ∫ z : UnitCircle, ‖F z‖ ^ 2 ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [(fourierPartialSum_memLp r h N).coeFn_toLp] with z hz
      rw [hz]
    _ = N := hinner.symm

private def squareCutoff (k : ℕ) : ℕ := (k + 1) ^ 2

private lemma squareCutoff_pos (k : ℕ) : 0 < squareCutoff k := by
  simp [squareCutoff]

private def fourierSquareBad (r : ℕ → ℤ) (h : ℤ) (ε : ℝ) (k : ℕ) :
    Set UnitCircle :=
  {z | ε ≤ ‖fourierAverage r h (squareCutoff k) z‖}

private lemma norm_fourierAverage (r : ℕ → ℤ) (h : ℤ) {N : ℕ}
    (hN : 0 < N) (z : UnitCircle) :
    ‖fourierAverage r h N z‖ = ‖fourierPartialSum r h N z‖ / N := by
  have hNc : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [fourierAverage, fourierPartialSum, norm_mul, norm_inv,
    Complex.norm_natCast, div_eq_mul_inv]
  ring

private lemma fourierSquareBad_eq (r : ℕ → ℤ) (h : ℤ) {ε : ℝ}
    (hε : 0 < ε) (k : ℕ) :
    fourierSquareBad r h ε k =
      {z | ε ^ 2 * (squareCutoff k : ℝ) ^ 2 ≤
        ‖fourierPartialSum r h (squareCutoff k) z‖ ^ 2} := by
  ext z
  simp only [fourierSquareBad, Set.mem_setOf_eq]
  rw [norm_fourierAverage r h (squareCutoff_pos k) z]
  have hN : (0 : ℝ) < squareCutoff k := by exact_mod_cast squareCutoff_pos k
  constructor <;> intro hz
  · have hs : ε * (squareCutoff k : ℝ) ≤
        ‖fourierPartialSum r h (squareCutoff k) z‖ := by
      rwa [le_div_iff₀ hN] at hz
    simpa only [mul_pow] using
      (sq_le_sq₀ (mul_nonneg hε.le hN.le)
        (norm_nonneg (fourierPartialSum r h (squareCutoff k) z))).2 hs
  · have hs : ε * (squareCutoff k : ℝ) ≤
        ‖fourierPartialSum r h (squareCutoff k) z‖ := by
      apply (sq_le_sq₀ (mul_nonneg hε.le hN.le)
        (norm_nonneg (fourierPartialSum r h (squareCutoff k) z))).1
      simpa only [mul_pow] using hz
    rwa [le_div_iff₀ hN]

private lemma fourierSquareBad_measureReal_le (r : ℕ → ℤ)
    (hr : Function.Injective r) (h : ℤ) (hh : h ≠ 0) {ε : ℝ}
    (hε : 0 < ε) (k : ℕ) :
    AddCircle.haarAddCircle.real (fourierSquareBad r h ε k) ≤
      1 / (ε ^ 2 * squareCutoff k) := by
  rw [fourierSquareBad_eq r h hε k]
  let S := fourierPartialSum r h (squareCutoff k)
  have hS : MemLp S 2 AddCircle.haarAddCircle :=
    fourierPartialSum_memLp r h (squareCutoff k)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := AddCircle.haarAddCircle)
    (f := fun z ↦ ‖S z‖ ^ 2)
    (Eventually.of_forall fun z ↦ sq_nonneg ‖S z‖)
    (hS.integrable_norm_pow (by norm_num))
    (ε ^ 2 * (squareCutoff k : ℝ) ^ 2)
  rw [show (∫ z : UnitCircle, ‖S z‖ ^ 2 ∂AddCircle.haarAddCircle) =
      squareCutoff k by
    exact integral_fourierPartialSum_norm_sq r hr h hh (squareCutoff k)] at hmark
  have hN : (0 : ℝ) < squareCutoff k := by exact_mod_cast squareCutoff_pos k
  have hden : 0 < ε ^ 2 * (squareCutoff k : ℝ) ^ 2 := by positivity
  calc
    AddCircle.haarAddCircle.real
        {z | ε ^ 2 * (squareCutoff k : ℝ) ^ 2 ≤
          ‖fourierPartialSum r h (squareCutoff k) z‖ ^ 2} ≤
        (squareCutoff k : ℝ) /
          (ε ^ 2 * (squareCutoff k : ℝ) ^ 2) := by
      rw [le_div_iff₀ hden]
      simpa only [mul_comm] using hmark
    _ = 1 / (ε ^ 2 * squareCutoff k) := by
      field_simp [hε.ne', hN.ne']

private lemma summable_fourierSquareBad_measureReal (r : ℕ → ℤ)
    (hr : Function.Injective r) (h : ℤ) (hh : h ≠ 0) {ε : ℝ}
    (hε : 0 < ε) :
    Summable (fun k ↦
      AddCircle.haarAddCircle.real (fourierSquareBad r h ε k)) := by
  have hp : Summable (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hshift : Summable (fun k : ℕ ↦ (((k + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
    hp.comp_injective (show Function.Injective (fun k : ℕ ↦ k + 1) by
      intro i j hij
      exact Nat.add_right_cancel hij)
  have hmajor : Summable (fun k : ℕ ↦
      1 / (ε ^ 2 * squareCutoff k : ℝ)) := by
    have := hshift.mul_left (ε ^ 2)⁻¹
    simpa only [squareCutoff, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
      one_div, mul_inv_rev, mul_comm] using this
  apply hmajor.of_nonneg_of_le
  · intro k
    exact measureReal_nonneg
  · intro k
    exact fourierSquareBad_measureReal_le r hr h hh hε k

private lemma tsum_fourierSquareBad_ne_top (r : ℕ → ℤ)
    (hr : Function.Injective r) (h : ℤ) (hh : h ≠ 0) {ε : ℝ}
    (hε : 0 < ε) :
    (∑' k : ℕ, AddCircle.haarAddCircle (fourierSquareBad r h ε k)) ≠ ∞ := by
  rw [show (fun k : ℕ ↦ AddCircle.haarAddCircle (fourierSquareBad r h ε k)) =
      (fun k ↦ ((AddCircle.haarAddCircle
        (fourierSquareBad r h ε k)).toNNReal : ENNReal)) by
    funext k
    exact (ENNReal.coe_toNNReal (measure_ne_top _ _)).symm]
  apply ENNReal.tsum_coe_ne_top_iff_summable_coe.2
  simpa only [Measure.real, ENNReal.coe_toNNReal_eq_toReal] using
    summable_fourierSquareBad_measureReal r hr h hh hε

private theorem ae_fourierAverage_square_tendsto (r : ℕ → ℤ)
    (hr : Function.Injective r) (h : ℤ) (hh : h ≠ 0) :
    ∀ᵐ z ∂AddCircle.haarAddCircle,
      Tendsto (fun k ↦ fourierAverage r h (squareCutoff k) z)
        atTop (𝓝 0) := by
  have hae : ∀ m : ℕ, ∀ᵐ z ∂AddCircle.haarAddCircle,
      ∀ᶠ k : ℕ in atTop,
        z ∉ fourierSquareBad r h (1 / (m + 1 : ℝ)) k := by
    intro m
    exact ae_eventually_notMem
      (tsum_fourierSquareBad_ne_top r hr h hh (by positivity))
  rw [← ae_all_iff] at hae
  filter_upwards [hae] with z hz
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨m : ℕ, hm : 1 / (m + 1 : ℝ) < ε⟩ := exists_nat_one_div_lt hε
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 (hz m)
  refine ⟨K, fun k hk ↦ ?_⟩
  rw [dist_zero_right]
  have hk' : ¬1 / (m + 1 : ℝ) ≤
      ‖fourierAverage r h (squareCutoff k) z‖ := by
    simpa only [fourierSquareBad, Set.mem_setOf_eq] using hK k hk
  exact (lt_of_not_ge hk').trans hm

private lemma fourierPartialSum_norm_le (r : ℕ → ℤ) (h : ℤ)
    (N : ℕ) (z : UnitCircle) :
    ‖fourierPartialSum r h N z‖ ≤ N := by
  rw [fourierPartialSum]
  calc
    ‖∑ n ∈ Finset.range N, fourier (h * r n) z‖ ≤
        ∑ n ∈ Finset.range N, ‖fourier (h * r n) z‖ := norm_sum_le _ _
    _ = N := by
      simp_rw [fourier_apply, Circle.norm_coe]
      simp

private lemma fourierPartialSum_sub_norm_le (r : ℕ → ℤ) (h : ℤ)
    {N M : ℕ} (hNM : N ≤ M) (z : UnitCircle) :
    ‖fourierPartialSum r h M z - fourierPartialSum r h N z‖ ≤ M - N := by
  have hsum : fourierPartialSum r h M z = fourierPartialSum r h N z +
      ∑ i ∈ Finset.range (M - N), fourier (h * r (N + i)) z := by
    rw [fourierPartialSum, fourierPartialSum]
    conv_lhs => rw [show M = N + (M - N) by omega]
    rw [Finset.sum_range_add]
  rw [hsum, add_sub_cancel_left]
  calc
    ‖∑ i ∈ Finset.range (M - N), fourier (h * r (N + i)) z‖ ≤
        ∑ i ∈ Finset.range (M - N), ‖fourier (h * r (N + i)) z‖ :=
      norm_sum_le _ _
    _ = M - N := by
      simp_rw [fourier_apply, Circle.norm_coe]
      simp [Nat.cast_sub hNM]

private lemma fourierAverage_sub_le (r : ℕ → ℤ) (h : ℤ)
    {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M) (z : UnitCircle) :
    ‖fourierAverage r h N z - fourierAverage r h M z‖ ≤
      2 * ((M : ℝ) - N) / M := by
  have hM : 0 < M := hN.trans_le hNM
  let SN : ℂ := fourierPartialSum r h N z
  let SM : ℂ := fourierPartialSum r h M z
  have hSN : ‖SN‖ ≤ (N : ℝ) := fourierPartialSum_norm_le r h N z
  have hdiff : ‖SM - SN‖ ≤ (M : ℝ) - N := by
    simpa only [SN, SM, Nat.cast_sub hNM] using
      fourierPartialSum_sub_norm_le r h hNM z
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  have hMc : (0 : ℝ) < M := by exact_mod_cast hM
  have hNMc : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have halg : fourierAverage r h N z - fourierAverage r h M z =
      (((N : ℂ)⁻¹ - (M : ℂ)⁻¹) * SN) - (M : ℂ)⁻¹ * (SM - SN) := by
    change (N : ℂ)⁻¹ * SN - (M : ℂ)⁻¹ * SM = _
    ring
  rw [halg]
  calc
    ‖(((N : ℂ)⁻¹ - (M : ℂ)⁻¹) * SN) - (M : ℂ)⁻¹ * (SM - SN)‖ ≤
        ‖((N : ℂ)⁻¹ - (M : ℂ)⁻¹) * SN‖ +
          ‖(M : ℂ)⁻¹ * (SM - SN)‖ := norm_sub_le _ _
    _ = |(N : ℝ)⁻¹ - (M : ℝ)⁻¹| * ‖SN‖ +
          (M : ℝ)⁻¹ * ‖SM - SN‖ := by
      rw [norm_mul, norm_mul]
      have hcast : (N : ℂ)⁻¹ - (M : ℂ)⁻¹ =
          (((N : ℝ)⁻¹ - (M : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, norm_inv,
        Complex.norm_natCast]
    _ ≤ (((N : ℝ)⁻¹ - (M : ℝ)⁻¹) * N) +
          (M : ℝ)⁻¹ * ((M : ℝ) - N) := by
      have hinv : (M : ℝ)⁻¹ ≤ (N : ℝ)⁻¹ := inv_anti₀ hNc hNMc
      rw [abs_of_nonneg (sub_nonneg.mpr hinv)]
      gcongr
    _ = 2 * ((M : ℝ) - N) / M := by
      field_simp [hNc.ne', hMc.ne']
      ring

private lemma tendsto_natSqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b ^ 2, fun n hn ↦ ?_⟩
  exact Nat.le_sqrt'.2 hn

private lemma sqrtInterpolationBound_tendsto :
    Tendsto (fun N : ℕ ↦ (4 : ℝ) / (Nat.sqrt N + 1)) atTop (𝓝 0) := by
  have hs : Tendsto (fun N : ℕ ↦ ((Nat.sqrt N : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_natSqrt_atTop
  have hs1 : Tendsto (fun N : ℕ ↦ ((Nat.sqrt N : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 hs
  simpa using tendsto_const_nhds.div_atTop hs1

private lemma fourierAverage_sqrt_interpolation_le (r : ℕ → ℤ) (h : ℤ)
    {N : ℕ} (hN : 0 < N) (z : UnitCircle) :
    ‖fourierAverage r h N z -
        fourierAverage r h (squareCutoff (Nat.sqrt N)) z‖ ≤
      (4 : ℝ) / (Nat.sqrt N + 1) := by
  let s := Nat.sqrt N
  let M := squareCutoff s
  have hNM : N ≤ M := by
    dsimp only [M, s, squareCutoff]
    exact (Nat.lt_succ_sqrt' N).le
  have hbasic := fourierAverage_sub_le r h hN hNM z
  refine hbasic.trans ?_
  have hs0 : (0 : ℝ) < s + 1 := by positivity
  have hsSq : (s : ℝ) ^ 2 ≤ N := by
    exact_mod_cast Nat.sqrt_le' N
  have hM : (M : ℝ) = (s + 1 : ℝ) ^ 2 := by
    simp [M, squareCutoff]
  have hdiff : (M : ℝ) - N ≤ 2 * (s + 1 : ℝ) := by
    rw [hM]
    nlinarith
  rw [hM] at hdiff
  change 2 * ((M : ℝ) - N) / M ≤ (4 : ℝ) / (s + 1)
  rw [hM]
  calc
    2 * ((s + 1 : ℝ) ^ 2 - N) / (s + 1 : ℝ) ^ 2 ≤
        2 * (2 * (s + 1 : ℝ)) / (s + 1 : ℝ) ^ 2 := by
      gcongr
    _ = (4 : ℝ) / (s + 1) := by
      field_simp [hs0.ne']
      ring

private theorem ae_fourierAverage_tendsto (r : ℕ → ℤ)
    (hr : Function.Injective r) (h : ℤ) (hh : h ≠ 0) :
    ∀ᵐ z ∂AddCircle.haarAddCircle,
      Tendsto (fun N ↦ fourierAverage r h N z) atTop (𝓝 0) := by
  filter_upwards [ae_fourierAverage_square_tendsto r hr h hh] with z hz
  have hsquare : Tendsto
      (fun N ↦ fourierAverage r h (squareCutoff (Nat.sqrt N)) z)
      atTop (𝓝 0) := hz.comp tendsto_natSqrt_atTop
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hsquare (ε / 2) (half_pos hε)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1
    sqrtInterpolationBound_tendsto (ε / 2) (half_pos hε)
  refine ⟨max 1 (max N₁ N₂), fun N hN ↦ ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one
    ((le_max_left 1 (max N₁ N₂)).trans hN)
  have hNN₁ : N₁ ≤ N := (le_max_left N₁ N₂).trans
    ((le_max_right 1 (max N₁ N₂)).trans hN)
  have hNN₂ : N₂ ≤ N := (le_max_right N₁ N₂).trans
    ((le_max_right 1 (max N₁ N₂)).trans hN)
  rw [dist_zero_right]
  calc
    ‖fourierAverage r h N z‖ ≤
        ‖fourierAverage r h N z -
          fourierAverage r h (squareCutoff (Nat.sqrt N)) z‖ +
        ‖fourierAverage r h (squareCutoff (Nat.sqrt N)) z‖ := by
      simpa using norm_add_le
        (fourierAverage r h N z -
          fourierAverage r h (squareCutoff (Nat.sqrt N)) z)
        (fourierAverage r h (squareCutoff (Nat.sqrt N)) z)
    _ ≤ (4 : ℝ) / (Nat.sqrt N + 1) +
        ‖fourierAverage r h (squareCutoff (Nat.sqrt N)) z‖ := by
      gcongr
      exact fourierAverage_sqrt_interpolation_le r h hNpos z
    _ < ε / 2 + ε / 2 := by
      have hg := hN₂ N hNN₂
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hg
      have hs := hN₁ N hNN₁
      rw [dist_zero_right] at hs
      linarith
    _ = ε := by ring

/-! The preceding metric Weyl lemma is now converted to the centered
fractional-part average used in the interval-counting identity. -/

private def integerOrbit (r : ℕ → ℕ) (z : UnitCircle) (n : ℕ) : UnitCircle :=
  (r n : ℤ) • z

private lemma fourier_integerOrbit (r : ℕ → ℕ) (z : UnitCircle)
    (h : ℤ) (n : ℕ) :
    fourier h (integerOrbit r z n) = fourier (h * r n) z := by
  simp only [integerOrbit, fourier_apply, smul_smul]

private def orbitCenteredAverage (r : ℕ → ℕ) (z : UnitCircle)
    (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
    Erdos378.WeightedCircleEquidistribution.centeredCoord (integerOrbit r z n)

private theorem ae_orbitCenteredAverage_tendsto (r : ℕ → ℕ)
    (hr : Function.Injective r) :
    ∀ᵐ z ∂AddCircle.haarAddCircle,
      Tendsto (orbitCenteredAverage r z) atTop (𝓝 0) := by
  let rZ : ℕ → ℤ := fun n ↦ r n
  have hrZ : Function.Injective rZ := by
    intro i j hij
    apply hr
    exact Int.ofNat_inj.mp hij
  have hae : ∀ᵐ z ∂AddCircle.haarAddCircle,
      ∀ h : ℤ, h ≠ 0 →
        Tendsto (fun N ↦ fourierAverage rZ h N z) atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro h
    by_cases hh : h = 0
    · exact ae_of_all _ fun _ hne ↦ (hne hh).elim
    · filter_upwards [ae_fourierAverage_tendsto rZ hrZ h hh] with z hz
      exact fun _ ↦ hz
  filter_upwards [hae] with z hz
  let s : ℕ → Finset ℕ := fun N ↦ Finset.range N
  let w : ℕ → ℕ → NNReal := fun _ _ ↦ 1
  let x : ℕ → ℕ → UnitCircle := fun _ n ↦ integerOrbit r z n
  have hweight : ∀ᶠ N : ℕ in atTop,
      Erdos378.WeightedCircleEquidistribution.totalWeight (s N) (w N) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    simp [s, w, Erdos378.WeightedCircleEquidistribution.totalWeight, hN.ne']
  have hmode : ∀ h : ℤ, h ≠ 0 → Tendsto
      (fun N ↦ Erdos378.WeightedCircleEquidistribution.normalizedFourierAverage
        (s N) (w N) (x N) h) atTop (𝓝 0) := by
    intro h hh
    apply (hz h hh).congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    simp only [Erdos378.WeightedCircleEquidistribution.normalizedFourierAverage,
      Erdos378.WeightedCircleEquidistribution.totalWeight, s, w, x,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      NNReal.coe_natCast, one_mul, Complex.ofReal_natCast]
    rw [fourierAverage]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    simpa only [NNReal.coe_one, Complex.ofReal_one, one_mul, rZ] using
      (fourier_integerOrbit r z h n).symm
  have hcenter :=
    Erdos378.WeightedCircleEquidistribution.tendsto_weightedCenteredAverage_of_fourier
      s w x hweight hmode
  apply hcenter.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  simp [orbitCenteredAverage,
    Erdos378.WeightedCircleEquidistribution.normalizedCenteredAverage,
    Erdos378.WeightedCircleEquidistribution.totalWeight, s, w, x]

/-! ## Rational target endpoints -/

/-- After clearing the denominator `q`, these are the left endpoints of
the subdivision cells. -/
private def lowerFrequency (A : NatSubdivision) (q : ℕ) (j : ℕ) : ℕ :=
  q * A.seq j

/-- After clearing the denominator `q`, these are the right endpoints of
the initial `p/q`-part of the subdivision cells. -/
private def upperFrequency (A : NatSubdivision) (p q : ℕ) (j : ℕ) : ℕ :=
  q * A.seq j + p * (A.seq (j + 1) - A.seq j)

private lemma lowerFrequency_injective (A : NatSubdivision) {q : ℕ}
    (hq : 0 < q) : Function.Injective (lowerFrequency A q) := by
  exact (A.strictMono.const_mul hq).injective

private lemma upperFrequency_strictMono (A : NatSubdivision) {p q : ℕ}
    (hpq : p < q) : StrictMono (upperFrequency A p q) := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hmono : A.seq j ≤ A.seq (j + 1) :=
    (A.strictMono (Nat.lt_succ_self j)).le
  have hgap : 0 < A.seq (j + 1) - A.seq j :=
    Nat.sub_pos_of_lt (A.strictMono (Nat.lt_succ_self j))
  have hmul : p * (A.seq (j + 1) - A.seq j) <
      q * (A.seq (j + 1) - A.seq j) :=
    Nat.mul_lt_mul_of_pos_right hpq hgap
  have hlt : upperFrequency A p q j < q * A.seq (j + 1) := by
    dsimp [upperFrequency]
    calc
      q * A.seq j + p * (A.seq (j + 1) - A.seq j) <
          q * A.seq j + q * (A.seq (j + 1) - A.seq j) :=
        Nat.add_lt_add_left hmul _
      _ = q * A.seq (j + 1) := by
        rw [Nat.mul_sub_left_distrib,
          Nat.add_sub_of_le (Nat.mul_le_mul_left q hmono)]
  exact hlt.trans_le (Nat.le_add_right _ _)

private lemma upperFrequency_injective (A : NatSubdivision) {p q : ℕ}
    (hpq : p < q) : Function.Injective (upperFrequency A p q) :=
  (upperFrequency_strictMono A hpq).injective

private def endpointErrorAverage (A : NatSubdivision) (p q : ℕ)
    (z : UnitCircle) (N : ℕ) : ℝ :=
  orbitCenteredAverage (lowerFrequency A q) z N -
    orbitCenteredAverage (upperFrequency A p q) z N

private theorem ae_endpointErrorAverage_tendsto (A : NatSubdivision)
    {p q : ℕ} (hq : 0 < q) (hpq : p < q) :
    ∀ᵐ z ∂AddCircle.haarAddCircle,
      Tendsto (endpointErrorAverage A p q z) atTop (𝓝 0) := by
  filter_upwards [ae_orbitCenteredAverage_tendsto (lowerFrequency A q)
      (lowerFrequency_injective A hq),
    ae_orbitCenteredAverage_tendsto (upperFrequency A p q)
      (upperFrequency_injective A hpq)] with z hlo hup
  change Tendsto
    (fun N ↦ orbitCenteredAverage (lowerFrequency A q) z N -
      orbitCenteredAverage (upperFrequency A p q) z N) atTop (𝓝 0)
  simpa using hlo.sub hup

private lemma haarAddCircle_singleton (z : UnitCircle) :
    AddCircle.haarAddCircle ({z} : Set UnitCircle) = 0 := by
  have hvol : (volume : Measure UnitCircle) = AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  rw [← hvol, ← Metric.closedBall_zero, AddCircle.volume_closedBall]
  norm_num

private theorem ae_nsmul_ne_zero :
    ∀ᵐ z ∂(AddCircle.haarAddCircle : Measure UnitCircle),
      ∀ k : ℕ, 0 < k → k • z ≠ 0 := by
  rw [ae_all_iff]
  intro k
  by_cases hk : 0 < k
  · apply ae_iff.2
    have hfin : {z : UnitCircle | k • z = 0}.Finite := by
      apply (Set.finite_range fun m : Fin k ↦
        (((m : ℝ) / k : ℝ) : UnitCircle)).subset
      intro z hz
      obtain ⟨m, hm, hzm⟩ := (AddCircle.nsmul_eq_zero_iff hk).1 hz
      exact ⟨⟨m, hm⟩, by simpa using hzm⟩
    letI : NullSingletonClass AddCircle.haarAddCircle :=
      ⟨haarAddCircle_singleton⟩
    simpa [hk] using
      hfin.measure_zero AddCircle.haarAddCircle
  · exact ae_of_all _ fun _ hk' ↦ (hk hk').elim

private lemma fract_mul_ne_zero_of_nsmul_ne_zero {γ : ℝ}
    (hz : ∀ k : ℕ, 0 < k → k • (γ : UnitCircle) ≠ 0)
    {r : ℕ} (hr : 0 < r) : Int.fract (γ * r) ≠ 0 := by
  intro hfract
  apply hz r hr
  have hcoe : ((γ * r : ℝ) : UnitCircle) = r • (γ : UnitCircle) := by
    rw [← AddCircle.coe_nsmul]
    congr 1
    push_cast
    ring
  rw [← hcoe, ← AddCircle.coe_fract, hfract]
  simp

private lemma centeredCoord_integerOrbit_eq_fract (r : ℕ → ℕ)
    (γ : ℝ) (n : ℕ) :
    Erdos378.WeightedCircleEquidistribution.centeredCoord
        (integerOrbit r (γ : UnitCircle) n) =
      Int.fract (γ * r n) - 1 / 2 := by
  have horbit : integerOrbit r (γ : UnitCircle) n =
      ((γ * r n : ℝ) : UnitCircle) := by
    change (r n : ℤ) • (γ : UnitCircle) = ((γ * r n : ℝ) : UnitCircle)
    rw [← AddCircle.coe_zsmul]
    congr 1
    norm_num
    ring
  rw [horbit, Erdos378.WeightedCircleEquidistribution.centeredCoord,
    Erdos378.WeightedCircleEquidistribution.unitCoord_coe]

private lemma lowerFrequency_scale (A : NatSubdivision) {q : ℕ}
    (hq : 0 < q) (β : ℝ) (j : ℕ) :
    (β / q) * lowerFrequency A q j = β * A.seq j := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [lowerFrequency, Nat.cast_mul]
  field_simp

private lemma upperFrequency_scale (A : NatSubdivision) {p q : ℕ}
    (hq : 0 < q) (β : ℝ) (j : ℕ) :
    (β / q) * upperFrequency A p q j =
      β * targetRight A ((p : ℝ) / q) j := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hseq : A.seq j ≤ A.seq (j + 1) :=
    (A.strictMono (Nat.lt_succ_self j)).le
  simp only [upperFrequency, targetRight]
  push_cast [Nat.cast_sub hseq]
  field_simp

/-! Integer points in the fully completed target cells.  We use `(x,y]`
when taking floors.  Away from the countable set where an endpoint is an
integer, this contains exactly the same integers as `[x,y)`. -/

private def cellIntegerPoints (A : NatSubdivision) (β t : ℝ) (j : ℕ) :
    Finset ℤ :=
  Finset.Ioc ⌊β * A.seq j⌋ ⌊β * targetRight A t j⌋

private def fullIntegerPoints (A : NatSubdivision) (β t : ℝ) (M : ℕ) :
    Finset ℤ :=
  (Finset.range M).biUnion (cellIntegerPoints A β t)

private lemma card_floor_Ioc_cast {x y : ℝ} (hxy : x ≤ y) :
    ((Finset.Ioc ⌊x⌋ ⌊y⌋).card : ℝ) =
      y - x + (Int.fract x - Int.fract y) := by
  have hfloor : ⌊x⌋ ≤ ⌊y⌋ := Int.floor_mono hxy
  have hcard := Int.card_Ioc_of_le (a := ⌊x⌋) (b := ⌊y⌋) hfloor
  have hcardR : ((Finset.Ioc ⌊x⌋ ⌊y⌋).card : ℝ) =
      (((⌊y⌋ - ⌊x⌋ : ℤ)) : ℝ) := by
    exact_mod_cast hcard
  calc
    ((Finset.Ioc ⌊x⌋ ⌊y⌋).card : ℝ) =
        (((⌊y⌋ - ⌊x⌋ : ℤ)) : ℝ) := hcardR
    _ = y - x + (Int.fract x - Int.fract y) := by
      push_cast
      nlinarith [Int.floor_add_fract x, Int.floor_add_fract y]

private lemma cellIntegerPoints_pairwiseDisjoint (A : NatSubdivision)
    {β t : ℝ} (hβ : 0 ≤ β) (ht : t ≤ 1) (M : ℕ) :
    ((Finset.range M : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (cellIntegerPoints A β t) := by
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · apply Finset.Ioc_disjoint_Ioc_of_le
    apply Int.floor_mono
    apply mul_le_mul_of_nonneg_left _ hβ
    exact (targetRight_le_next A ht i).trans <| by
      exact_mod_cast A.strictMono.monotone (by omega : i + 1 ≤ j)
  · apply (Finset.Ioc_disjoint_Ioc_of_le ?_).symm
    apply Int.floor_mono
    apply mul_le_mul_of_nonneg_left _ hβ
    exact (targetRight_le_next A ht j).trans <| by
      exact_mod_cast A.strictMono.monotone (by omega : j + 1 ≤ i)

private lemma card_cellIntegerPoints (A : NatSubdivision) {β t : ℝ}
    (hβ : 0 ≤ β) (ht0 : 0 ≤ t) (j : ℕ) :
    ((cellIntegerPoints A β t j).card : ℝ) =
      β * t * ((A.seq (j + 1) : ℝ) - A.seq j) +
        (Int.fract (β * A.seq j) -
          Int.fract (β * targetRight A t j)) := by
  rw [cellIntegerPoints, card_floor_Ioc_cast]
  · dsimp [targetRight]
    ring
  · exact mul_le_mul_of_nonneg_left (left_le_targetRight A ht0 j) hβ

private lemma card_fullIntegerPoints (A : NatSubdivision) {β t : ℝ}
    (hβ : 0 ≤ β) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (M : ℕ) :
    ((fullIntegerPoints A β t M).card : ℝ) =
      β * t * ((A.seq M : ℝ) - A.seq 0) +
        ∑ j ∈ Finset.range M,
          (Int.fract (β * A.seq j) -
            Int.fract (β * targetRight A t j)) := by
  rw [fullIntegerPoints,
    Finset.card_biUnion (cellIntegerPoints_pairwiseDisjoint A hβ ht1 M),
    Nat.cast_sum]
  simp_rw [card_cellIntegerPoints A hβ ht0]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  have htel : ∑ j ∈ Finset.range M,
      ((A.seq (j + 1) : ℝ) - A.seq j) = A.seq M - A.seq 0 := by
    have h := Finset.sum_range_sub' (fun j ↦ (A.seq j : ℝ)) M
    calc
      ∑ j ∈ Finset.range M, ((A.seq (j + 1) : ℝ) - A.seq j) =
          -(∑ j ∈ Finset.range M, ((A.seq j : ℝ) - A.seq (j + 1))) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = A.seq M - A.seq 0 := by rw [h]; ring
  rw [htel]

private lemma endpointError_sum_eq (A : NatSubdivision) {p q M : ℕ}
    (hq : 0 < q) (β : ℝ) (hM : 0 < M) :
    (∑ j ∈ Finset.range M,
        (Int.fract (β * A.seq j) -
          Int.fract (β * targetRight A ((p : ℝ) / q) j))) =
      M * endpointErrorAverage A p q ((β / q : ℝ) : UnitCircle) M := by
  have hlow : ∀ j : ℕ,
      Erdos378.WeightedCircleEquidistribution.centeredCoord
          (integerOrbit (lowerFrequency A q)
            ((β / q : ℝ) : UnitCircle) j) =
        Int.fract (β * A.seq j) - 1 / 2 := by
    intro j
    rw [centeredCoord_integerOrbit_eq_fract,
      lowerFrequency_scale A hq]
  have hupp : ∀ j : ℕ,
      Erdos378.WeightedCircleEquidistribution.centeredCoord
          (integerOrbit (upperFrequency A p q)
            ((β / q : ℝ) : UnitCircle) j) =
        Int.fract (β * targetRight A ((p : ℝ) / q) j) - 1 / 2 := by
    intro j
    rw [centeredCoord_integerOrbit_eq_fract,
      upperFrequency_scale A hq]
  simp_rw [endpointErrorAverage, orbitCenteredAverage, hlow, hupp]
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [Finset.sum_sub_distrib]
  field_simp
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-! ## Comparison with the original sample count -/

private def positiveSamplePoints (A : NatSubdivision) (α t : ℝ) (N : ℕ) :
    Finset ℕ :=
  (Finset.Ioc 0 N).filter fun k ↦ A.fractionalPosition (α * k) < t

private def sampleIntegerPoints (A : NatSubdivision) (α t : ℝ) (N : ℕ) :
    Finset ℤ :=
  (Finset.Ioc (0 : ℤ) N).filter fun k ↦
    A.fractionalPosition (α * (k : ℝ)) < t

private lemma card_sampleIntegerPoints (A : NatSubdivision) (α t : ℝ) (N : ℕ) :
    (sampleIntegerPoints A α t N).card =
      (positiveSamplePoints A α t N).card := by
  rw [sampleIntegerPoints, positiveSamplePoints]
  apply Finset.card_bij (fun k _ ↦ k.toNat)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hk ⊢
    have hk0 : 0 ≤ k := hk.1.1.le
    have hkcast : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0
    have hkcastR : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
      exact_mod_cast hkcast
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have : (0 : ℤ) < (k.toNat : ℤ) := by
        rw [hkcast]
        exact hk.1.1
      exact_mod_cast this
    · have : (k.toNat : ℤ) ≤ (N : ℤ) := by
        rw [hkcast]
        exact hk.1.2
      exact_mod_cast this
    · simpa [hkcastR] using hk.2
  · intro k₁ hk₁ k₂ hk₂ h
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hk₁ hk₂
    calc
      k₁ = (k₁.toNat : ℤ) := (Int.toNat_of_nonneg hk₁.1.1.le).symm
      _ = (k₂.toNat : ℤ) := by exact_mod_cast h
      _ = k₂ := Int.toNat_of_nonneg hk₂.1.1.le
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    refine ⟨(n : ℤ), ?_, ?_⟩
    · norm_num
      exact hn
    · simp

private lemma intervalCount_zero_eq_positiveSamplePoints (A : NatSubdivision)
    (α t : ℝ) (N : ℕ) :
    intervalCount (sampledSequence A α) N 0 t =
      (positiveSamplePoints A α t N).card := by
  rw [intervalCount, positiveSamplePoints]
  let s := (Finset.range N).filter fun n ↦
    sampledSequence A α n ∈ Ico (0 : ℝ) t
  let u : Finset ℕ := (Finset.Ioc 0 N).filter fun k : ℕ ↦
    A.fractionalPosition (α * (k : ℝ)) < t
  change s.card = u.card
  apply Finset.card_bij (fun n _ ↦ n + 1)
  · intro n hn
    simp only [s, Finset.mem_filter, Finset.mem_range] at hn
    simp only [u, Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨Nat.zero_lt_succ n, hn.1⟩, ?_⟩
    simpa [sampledSequence] using hn.2.2
  · intro n₁ hn₁ n₂ hn₂ h
    omega
  · intro k hk
    simp only [u, Finset.mem_filter, Finset.mem_Ioc] at hk
    refine ⟨k - 1, ?_, ?_⟩
    · simp only [s, Finset.mem_filter, Finset.mem_range]
      constructor
      · omega
      · have hnonneg := A.fractionalPosition_nonneg (α * k)
        have heq : k - 1 + 1 = k := by omega
        have hcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
          exact_mod_cast heq
        constructor
        · simpa [sampledSequence, hcast] using hnonneg
        · simpa [sampledSequence, hcast] using hk.2
    · omega

private lemma intervalCount_zero_eq_sampleIntegerPoints (A : NatSubdivision)
    (α t : ℝ) (N : ℕ) :
    intervalCount (sampledSequence A α) N 0 t =
      (sampleIntegerPoints A α t N).card := by
  rw [card_sampleIntegerPoints,
    intervalCount_zero_eq_positiveSamplePoints]

private lemma fullIntegerPoints_subset_sampleIntegerPoints
    (A : NatSubdivision) {p q N : ℕ} {α : ℝ}
    (hα : 0 < α) (hp : 0 < p) (hpq : p < q)
    (hZ : (A.seq 0 : ℝ) ≤ α * N)
    (hz : ∀ k : ℕ, 0 < k →
      k • (((α⁻¹ / q : ℝ)) : UnitCircle) ≠ 0) :
    fullIntegerPoints A α⁻¹ ((p : ℝ) / q) (A.cellIndex (α * N)) ⊆
      sampleIntegerPoints A α ((p : ℝ) / q) N := by
  intro k hk
  rw [fullIntegerPoints, Finset.mem_biUnion] at hk
  obtain ⟨j, hjM, hkj⟩ := hk
  have hq : 0 < q := hp.trans hpq
  have hβ : 0 < α⁻¹ := inv_pos.mpr hα
  have hjlt : j < A.cellIndex (α * N) := Finset.mem_range.1 hjM
  have hlowFreq : 0 < lowerFrequency A q j := by
    exact Nat.mul_pos hq (A.pos j)
  have huppFreq : 0 < upperFrequency A p q j := by
    dsimp [upperFrequency]
    exact Nat.add_pos_left (Nat.mul_pos hq (A.pos j)) _
  have hfractLow : Int.fract (α⁻¹ * A.seq j) ≠ 0 := by
    have h := fract_mul_ne_zero_of_nsmul_ne_zero hz hlowFreq
    rwa [lowerFrequency_scale A hq] at h
  have hfractUpp :
      Int.fract (α⁻¹ * targetRight A ((p : ℝ) / q) j) ≠ 0 := by
    have h := fract_mul_ne_zero_of_nsmul_ne_zero hz huppFreq
    rwa [upperFrequency_scale A hq] at h
  have hkreal : (k : ℝ) ∈ Ioc
      (α⁻¹ * A.seq j)
      (α⁻¹ * targetRight A ((p : ℝ) / q) j) := by
    exact Int.cast_mem_Ioc_iff.mpr hkj
  have hkupper : (k : ℝ) <
      α⁻¹ * targetRight A ((p : ℝ) / q) j := by
    exact hkreal.2.lt_of_ne fun hEq ↦ hfractUpp <| by
      rw [← hEq]
      simp
  have hαβ : α * α⁻¹ = 1 := mul_inv_cancel₀ hα.ne'
  have hβα : α⁻¹ * α = 1 := inv_mul_cancel₀ hα.ne'
  have hkposR : (0 : ℝ) < k :=
    (mul_pos hβ (by exact_mod_cast A.pos j)).trans hkreal.1
  have hkpos : (0 : ℤ) < k := by exact_mod_cast hkposR
  have hjnextM : j + 1 ≤ A.cellIndex (α * N) := by omega
  have hrightM : targetRight A ((p : ℝ) / q) j ≤
      A.seq (A.cellIndex (α * N)) := by
    refine (targetRight_le_next A ?_ j).trans ?_
    · have : (p : ℝ) ≤ q := by exact_mod_cast hpq.le
      exact (div_le_one (by exact_mod_cast hq)).2 this
    · exact_mod_cast A.strictMono.monotone hjnextM
  have hMZ : (A.seq (A.cellIndex (α * N)) : ℝ) ≤ α * N :=
    A.seq_cellIndex_le hZ
  have hkNreal : (k : ℝ) ≤ N := by
    calc
      (k : ℝ) ≤ α⁻¹ * targetRight A ((p : ℝ) / q) j := hkreal.2
      _ ≤ α⁻¹ * (α * N) :=
        mul_le_mul_of_nonneg_left (hrightM.trans hMZ) hβ.le
      _ = N := by rw [← mul_assoc, hβα, one_mul]
  have hkN : k ≤ (N : ℤ) := by exact_mod_cast hkNreal
  have hxlow : (A.seq j : ℝ) ≤ α * k := by
    have := hkreal.1.le
    calc
      (A.seq j : ℝ) = α * (α⁻¹ * A.seq j) := by rw [← mul_assoc, hαβ, one_mul]
      _ ≤ α * k := mul_le_mul_of_nonneg_left this hα.le
  have hxupp : α * k < targetRight A ((p : ℝ) / q) j := by
    calc
      α * (k : ℝ) < α * (α⁻¹ * targetRight A ((p : ℝ) / q) j) :=
        mul_lt_mul_of_pos_left hkupper hα
      _ = targetRight A ((p : ℝ) / q) j := by
        rw [← mul_assoc, hαβ, one_mul]
  have hx0 : (A.seq 0 : ℝ) ≤ α * k := by
    have h0j : (A.seq 0 : ℝ) ≤ A.seq j := by
      exact_mod_cast A.strictMono.monotone (Nat.zero_le j)
    exact h0j.trans hxlow
  have ht0 : (0 : ℝ) ≤ (p : ℝ) / q := by positivity
  have ht1 : (p : ℝ) / q ≤ 1 := by
    exact (div_le_one (by exact_mod_cast hq)).2 (by exact_mod_cast hpq.le)
  have hfrac : A.fractionalPosition (α * k) < (p : ℝ) / q :=
    (fractionalPosition_lt_iff_mem_targetSet A hx0 ht0 ht1).2 <|
      Set.mem_iUnion.2 ⟨j, hxlow, hxupp⟩
  simp only [sampleIntegerPoints, Finset.mem_filter, Finset.mem_Ioc]
  exact ⟨⟨hkpos, hkN⟩, hfrac⟩

private def remainderIntegerPoints (A : NatSubdivision) (α : ℝ) (N : ℕ) :
    Finset ℤ :=
  Finset.Ioc 0 ⌊α⁻¹ * A.seq 0⌋ ∪
    Finset.Ioc ⌊α⁻¹ * A.seq (A.cellIndex (α * N))⌋ N

private lemma sample_sdiff_full_subset_remainder
    (A : NatSubdivision) {p q N : ℕ} {α : ℝ}
    (hα : 0 < α) (hp : 0 < p) (hpq : p < q)
    (hZ : (A.seq 0 : ℝ) ≤ α * N)
    (hz : ∀ k : ℕ, 0 < k →
      k • (((α⁻¹ / q : ℝ)) : UnitCircle) ≠ 0) :
    sampleIntegerPoints A α ((p : ℝ) / q) N \
        fullIntegerPoints A α⁻¹ ((p : ℝ) / q) (A.cellIndex (α * N)) ⊆
      remainderIntegerPoints A α N := by
  intro k hk
  rw [Finset.mem_sdiff] at hk
  have hq : 0 < q := hp.trans hpq
  have hβ : 0 < α⁻¹ := inv_pos.mpr hα
  have hαβ : α * α⁻¹ = 1 := mul_inv_cancel₀ hα.ne'
  have ht0 : (0 : ℝ) ≤ (p : ℝ) / q := by positivity
  have ht1 : (p : ℝ) / q ≤ 1 := by
    exact (div_le_one (by exact_mod_cast hq)).2 (by exact_mod_cast hpq.le)
  rw [sampleIntegerPoints, Finset.mem_filter, Finset.mem_Ioc] at hk
  rcases hk.1 with ⟨⟨hkpos, hkN⟩, hfrac⟩
  by_cases hx0 : (A.seq 0 : ℝ) ≤ α * k
  · have htarget :=
      (fractionalPosition_lt_iff_mem_targetSet A hx0 ht0 ht1).1 hfrac
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 htarget
    dsimp [targetLeft] at hj
    have hxN : α * (k : ℝ) ≤ α * N := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hkN) hα.le
    have hjM : j ≤ A.cellIndex (α * N) := by
      by_contra hnot
      have hMlt : A.cellIndex (α * N) < j := by omega
      have hmono : A.seq (A.cellIndex (α * N) + 1) ≤ A.seq j :=
        A.strictMono.monotone (by omega)
      have hcast : (A.seq (A.cellIndex (α * N) + 1) : ℝ) ≤ A.seq j := by
        exact_mod_cast hmono
      have := A.lt_seq_cellIndex_succ (α * N)
      exact (not_lt_of_ge (hcast.trans (hj.1.trans hxN))) this
    have hlowFreq : 0 < lowerFrequency A q j :=
      Nat.mul_pos hq (A.pos j)
    have huppFreq : 0 < upperFrequency A p q j := by
      dsimp [upperFrequency]
      exact Nat.add_pos_left (Nat.mul_pos hq (A.pos j)) _
    have hfractLow : Int.fract (α⁻¹ * A.seq j) ≠ 0 := by
      have h := fract_mul_ne_zero_of_nsmul_ne_zero hz hlowFreq
      rwa [lowerFrequency_scale A hq] at h
    have hfractUpp :
        Int.fract (α⁻¹ * targetRight A ((p : ℝ) / q) j) ≠ 0 := by
      have h := fract_mul_ne_zero_of_nsmul_ne_zero hz huppFreq
      rwa [upperFrequency_scale A hq] at h
    have hscaledLow : α⁻¹ * A.seq j ≤ (k : ℝ) := by
      calc
        α⁻¹ * (A.seq j : ℝ) ≤ α⁻¹ * (α * k) :=
          mul_le_mul_of_nonneg_left hj.1 hβ.le
        _ = k := by
          rw [← mul_assoc, inv_mul_cancel₀ hα.ne', one_mul]
    have hscaledLow' : α⁻¹ * A.seq j < (k : ℝ) :=
      hscaledLow.lt_of_ne fun hEq ↦ hfractLow <| by
        rw [hEq]
        simp
    have hscaledUpp : (k : ℝ) <
        α⁻¹ * targetRight A ((p : ℝ) / q) j := by
      calc
        (k : ℝ) = α⁻¹ * (α * k) := by
          rw [← mul_assoc, inv_mul_cancel₀ hα.ne', one_mul]
        _ < α⁻¹ * targetRight A ((p : ℝ) / q) j :=
          mul_lt_mul_of_pos_left hj.2 hβ
    have hnotlt : ¬j < A.cellIndex (α * N) := by
      intro hjlt
      apply hk.2
      rw [fullIntegerPoints, Finset.mem_biUnion]
      refine ⟨j, Finset.mem_range.2 hjlt, ?_⟩
      rw [cellIntegerPoints]
      apply Int.cast_mem_Ioc_iff.mp
      exact ⟨hscaledLow', hscaledUpp.le⟩
    have hjEq : j = A.cellIndex (α * N) := by omega
    rw [remainderIntegerPoints, Finset.mem_union]
    right
    rw [Finset.mem_Ioc]
    constructor
    · have hmem : k ∈ Finset.Ioc
          ⌊α⁻¹ * A.seq j⌋ ⌊(N : ℝ)⌋ :=
        Int.cast_mem_Ioc_iff.mp ⟨hscaledLow', by exact_mod_cast hkN⟩
      have hmemlow := (Finset.mem_Ioc.1 hmem).1
      simpa [hjEq] using hmemlow
    · exact hkN
  · have hxlt : α * (k : ℝ) < A.seq 0 := lt_of_not_ge hx0
    have hklt : (k : ℝ) < α⁻¹ * A.seq 0 := by
      calc
        (k : ℝ) = α⁻¹ * (α * k) := by
          rw [← mul_assoc, inv_mul_cancel₀ hα.ne', one_mul]
        _ < α⁻¹ * A.seq 0 := mul_lt_mul_of_pos_left hxlt hβ
    rw [remainderIntegerPoints, Finset.mem_union]
    left
    rw [Finset.mem_Ioc]
    exact ⟨hkpos, Int.le_floor.2 hklt.le⟩

private lemma card_Ioc_zero_floor_cast_le {x : ℝ} (hx : 0 ≤ x) :
    ((Finset.Ioc (0 : ℤ) ⌊x⌋).card : ℝ) ≤ x := by
  have hfloor0 : (0 : ℤ) ≤ ⌊x⌋ := (Int.floor_nonneg).2 hx
  have hcard := Int.card_Ioc_of_le (a := (0 : ℤ)) (b := ⌊x⌋) hfloor0
  have hcard' : ((Finset.Ioc (0 : ℤ) ⌊x⌋).card : ℤ) = ⌊x⌋ := by
    simpa using hcard
  have hcardR : ((Finset.Ioc (0 : ℤ) ⌊x⌋).card : ℝ) = (⌊x⌋ : ℝ) := by
    exact_mod_cast hcard'
  rw [hcardR]
  exact Int.floor_le x

private lemma card_Ioc_floor_nat_cast_le {y : ℝ} {N : ℕ}
    (hyN : y ≤ N) :
    ((Finset.Ioc ⌊y⌋ (N : ℤ)).card : ℝ) ≤ (N : ℝ) - y + 1 := by
  have hfloorN : ⌊y⌋ ≤ (N : ℤ) := by
    have : (⌊y⌋ : ℝ) ≤ (N : ℝ) := (Int.floor_le y).trans hyN
    exact_mod_cast this
  have hcard := Int.card_Ioc_of_le (a := ⌊y⌋) (b := (N : ℤ)) hfloorN
  have hcardR : ((Finset.Ioc ⌊y⌋ (N : ℤ)).card : ℝ) =
      (N : ℝ) - (⌊y⌋ : ℝ) := by
    exact_mod_cast hcard
  rw [hcardR]
  linarith [Int.lt_floor_add_one y]

private lemma card_remainderIntegerPoints_le (A : NatSubdivision) {α : ℝ}
    (hα : 0 < α) {N : ℕ} (hZ : (A.seq 0 : ℝ) ≤ α * N) :
    ((remainderIntegerPoints A α N).card : ℝ) ≤
      α⁻¹ * A.seq 0 +
        α⁻¹ * ((A.seq (A.cellIndex (α * N) + 1) : ℝ) -
          A.seq (A.cellIndex (α * N))) + 1 := by
  let M := A.cellIndex (α * N)
  have hβ : 0 < α⁻¹ := inv_pos.mpr hα
  have hβα : α⁻¹ * α = 1 := inv_mul_cancel₀ hα.ne'
  have hMZ : (A.seq M : ℝ) ≤ α * N := A.seq_cellIndex_le hZ
  have hyN : α⁻¹ * A.seq M ≤ (N : ℝ) := by
    calc
      α⁻¹ * (A.seq M : ℝ) ≤ α⁻¹ * (α * N) :=
        mul_le_mul_of_nonneg_left hMZ hβ.le
      _ = N := by rw [← mul_assoc, hβα, one_mul]
  have hfirst := card_Ioc_zero_floor_cast_le
    (mul_nonneg hβ.le (by positivity : (0 : ℝ) ≤ A.seq 0))
  have hsecond := card_Ioc_floor_nat_cast_le hyN
  have hcardUnion : (remainderIntegerPoints A α N).card ≤
      (Finset.Ioc (0 : ℤ) ⌊α⁻¹ * A.seq 0⌋).card +
        (Finset.Ioc ⌊α⁻¹ * A.seq M⌋ (N : ℤ)).card := by
    simpa [remainderIntegerPoints, M] using
      Finset.card_union_le
        (Finset.Ioc (0 : ℤ) ⌊α⁻¹ * A.seq 0⌋)
        (Finset.Ioc ⌊α⁻¹ * A.seq M⌋ (N : ℤ))
  have hZnext : α * N < A.seq (M + 1) := A.lt_seq_cellIndex_succ (α * N)
  have hboundary : (N : ℝ) - α⁻¹ * A.seq M ≤
      α⁻¹ * ((A.seq (M + 1) : ℝ) - A.seq M) := by
    have hNlt : (N : ℝ) < α⁻¹ * A.seq (M + 1) := by
      calc
        (N : ℝ) = α⁻¹ * (α * N) := by rw [← mul_assoc, hβα, one_mul]
        _ < α⁻¹ * A.seq (M + 1) := mul_lt_mul_of_pos_left hZnext hβ
    linarith
  have hcardUnionR : ((remainderIntegerPoints A α N).card : ℝ) ≤
      ((Finset.Ioc (0 : ℤ) ⌊α⁻¹ * A.seq 0⌋).card : ℝ) +
        ((Finset.Ioc ⌊α⁻¹ * A.seq M⌋ (N : ℤ)).card : ℝ) := by
    exact_mod_cast hcardUnion
  change ((remainderIntegerPoints A α N).card : ℝ) ≤ _
  dsimp only [M] at hfirst hsecond hboundary ⊢
  dsimp only [M] at hcardUnionR
  linarith

private lemma tendsto_scaledArgument_atTop {α : ℝ} (hα : 0 < α) :
    Tendsto (fun N : ℕ ↦ α * (N : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.const_mul_atTop hα

private lemma boundaryRatio_tendsto_zero (A : NatSubdivision) {α : ℝ}
    (hα : 0 < α) :
    Tendsto
      (fun N : ℕ ↦
        (α⁻¹ * A.seq 0 +
          α⁻¹ * ((A.seq (A.cellIndex (α * N) + 1) : ℝ) -
            A.seq (A.cellIndex (α * N))) + 1) / N)
      atTop (𝓝 0) := by
  have hZN := tendsto_scaledArgument_atTop hα
  have hgap := (gap_cellIndex_div_tendsto A).comp hZN
  have hconst : Tendsto
      (fun N : ℕ ↦ (α⁻¹ * A.seq 0 + 1) / (N : ℝ))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsum := hconst.add hgap
  have heq : (fun N : ℕ ↦
      (α⁻¹ * A.seq 0 + 1) / (N : ℝ) +
        ((A.seq (A.cellIndex (α * N) + 1) : ℝ) -
          A.seq (A.cellIndex (α * N))) / (α * N)) =ᶠ[atTop]
      (fun N : ℕ ↦
        (α⁻¹ * A.seq 0 +
          α⁻¹ * ((A.seq (A.cellIndex (α * N) + 1) : ℝ) -
            A.seq (A.cellIndex (α * N))) + 1) / N) := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with N hN
    have hαne : α ≠ 0 := hα.ne'
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    field_simp
    ring
  simpa only [add_zero, Function.comp_apply] using hsum.congr' heq

private lemma completedLengthRatio_tendsto (A : NatSubdivision) {α t : ℝ}
    (hα : 0 < α) :
    Tendsto
      (fun N : ℕ ↦
        α⁻¹ * t * ((A.seq (A.cellIndex (α * N)) : ℝ) - A.seq 0) / N)
      atTop (𝓝 t) := by
  have hZN := tendsto_scaledArgument_atTop hα
  have hseq := (seq_cellIndex_div_tendsto A).comp hZN
  have hconst : Tendsto
      (fun N : ℕ ↦ (A.seq 0 : ℝ) / (α * N)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop hZN
  have hdiff : Tendsto
      (fun N : ℕ ↦
        ((A.seq (A.cellIndex (α * N)) : ℝ) - A.seq 0) / (α * N))
      atTop (𝓝 1) := by
    have := hseq.sub hconst
    have heq : (fun N : ℕ ↦
        (A.seq (A.cellIndex (α * N)) : ℝ) / (α * N) -
          (A.seq 0 : ℝ) / (α * N)) =ᶠ[atTop]
        (fun N : ℕ ↦
          ((A.seq (A.cellIndex (α * N)) : ℝ) - A.seq 0) / (α * N)) := by
      filter_upwards [eventually_ne_atTop (0 : ℕ)] with N hN
      have hαne : α ≠ 0 := hα.ne'
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
      field_simp
    simpa only [sub_zero, Function.comp_apply] using this.congr' heq
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ t) atTop (𝓝 t)).mul hdiff
  have heq : (fun N : ℕ ↦
      t * (((A.seq (A.cellIndex (α * N)) : ℝ) - A.seq 0) / (α * N))) =ᶠ[atTop]
      (fun N : ℕ ↦
        α⁻¹ * t * ((A.seq (A.cellIndex (α * N)) : ℝ) - A.seq 0) / N) := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with N hN
    have hαne : α ≠ 0 := hα.ne'
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    field_simp
  simpa only [mul_one] using ht.congr' heq

private lemma endpointErrorRatio_tendsto_zero (A : NatSubdivision)
    {p q : ℕ} {α : ℝ} (hα : 0 < α)
    (havg : Tendsto
      (endpointErrorAverage A p q (((α⁻¹ / q : ℝ)) : UnitCircle))
      atTop (𝓝 0)) :
    Tendsto
      (fun N : ℕ ↦
        (A.cellIndex (α * N) : ℝ) *
          endpointErrorAverage A p q
            (((α⁻¹ / q : ℝ)) : UnitCircle) (A.cellIndex (α * N)) / N)
      atTop (𝓝 0) := by
  have hZN := tendsto_scaledArgument_atTop hα
  have hM : Tendsto (fun N : ℕ ↦ A.cellIndex (α * N)) atTop atTop :=
    (tendsto_cellIndex_atTop A).comp hZN
  have havgM := havg.comp hM
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (g := fun N : ℕ ↦
    α * |endpointErrorAverage A p q
      (((α⁻¹ / q : ℝ)) : UnitCircle) (A.cellIndex (α * N))|)
  · exact Eventually.of_forall fun _ ↦ abs_nonneg _
  · filter_upwards [eventually_ne_atTop (0 : ℕ),
      (hZN.eventually (eventually_ge_atTop (A.seq 0 : ℝ)))] with N hN hNZ
    have hNr : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
    have hMseq := A.self_lt_seq (A.cellIndex (α * N))
    have hseqZ := A.seq_cellIndex_le hNZ
    have hMN : (A.cellIndex (α * N) : ℝ) / N ≤ α := by
      apply (div_le_iff₀ hNr).2
      have hMseqR : (A.cellIndex (α * N) : ℝ) ≤
          A.seq (A.cellIndex (α * N)) := by exact_mod_cast hMseq.le
      exact hMseqR.trans hseqZ
    change |(A.cellIndex (α * N) : ℝ) *
      endpointErrorAverage A p q (((α⁻¹ / q : ℝ)) : UnitCircle)
        (A.cellIndex (α * N)) / N| ≤ _
    rw [abs_div, abs_mul, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ A.cellIndex (α * N)), abs_of_pos hNr]
    calc
      (A.cellIndex (α * N) : ℝ) *
          |endpointErrorAverage A p q (((α⁻¹ / q : ℝ)) : UnitCircle)
            (A.cellIndex (α * N))| / N =
        ((A.cellIndex (α * N) : ℝ) / N) *
          |endpointErrorAverage A p q (((α⁻¹ / q : ℝ)) : UnitCircle)
            (A.cellIndex (α * N))| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hMN (abs_nonneg _)
  · have habs := havgM.abs
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ α) atTop (𝓝 α)).mul habs

private lemma fullIntegerPointsRatio_tendsto (A : NatSubdivision)
    {p q : ℕ} {α : ℝ} (hα : 0 < α) (hp : 0 < p) (hpq : p < q)
    (havg : Tendsto
      (endpointErrorAverage A p q (((α⁻¹ / q : ℝ)) : UnitCircle))
      atTop (𝓝 0)) :
    Tendsto
      (fun N : ℕ ↦
        ((fullIntegerPoints A α⁻¹ ((p : ℝ) / q)
          (A.cellIndex (α * N))).card : ℝ) / N)
      atTop (𝓝 ((p : ℝ) / q)) := by
  have hq : 0 < q := hp.trans hpq
  have hβ : 0 ≤ α⁻¹ := (inv_pos.mpr hα).le
  have ht0 : (0 : ℝ) ≤ (p : ℝ) / q := by positivity
  have ht1 : (p : ℝ) / q ≤ 1 :=
    (div_le_one (by exact_mod_cast hq)).2 (by exact_mod_cast hpq.le)
  have hlen := completedLengthRatio_tendsto A (α := α)
    (t := (p : ℝ) / q) hα
  have herr := endpointErrorRatio_tendsto_zero A hα havg
  have hsum := hlen.add herr
  have hZN := tendsto_scaledArgument_atTop hα
  have hM : Tendsto (fun N : ℕ ↦ A.cellIndex (α * N)) atTop atTop :=
    (tendsto_cellIndex_atTop A).comp hZN
  have heq : (fun N : ℕ ↦
      α⁻¹ * ((p : ℝ) / q) *
          ((A.seq (A.cellIndex (α * N)) : ℝ) - A.seq 0) / N +
        (A.cellIndex (α * N) : ℝ) *
          endpointErrorAverage A p q (((α⁻¹ / q : ℝ)) : UnitCircle)
            (A.cellIndex (α * N)) / N) =ᶠ[atTop]
      (fun N : ℕ ↦
        ((fullIntegerPoints A α⁻¹ ((p : ℝ) / q)
          (A.cellIndex (α * N))).card : ℝ) / N) := by
    filter_upwards [hM.eventually (eventually_gt_atTop 0)] with N hMN
    let M := A.cellIndex (α * N)
    have hcard := card_fullIntegerPoints A hβ ht0 ht1 M
    have herrsum := endpointError_sum_eq A (p := p) (q := q) (M := M)
      hq α⁻¹ hMN
    rw [herrsum] at hcard
    dsimp only [M] at hcard ⊢
    rw [hcard]
    ring
  simpa only [add_zero] using hsum.congr' heq

private theorem rationalAnchored_tendsto (A : NatSubdivision)
    {p q : ℕ} {α : ℝ} (hα : 0 < α) (hp : 0 < p) (hpq : p < q)
    (hz : ∀ k : ℕ, 0 < k →
      k • (((α⁻¹ / q : ℝ)) : UnitCircle) ≠ 0)
    (havg : Tendsto
      (endpointErrorAverage A p q (((α⁻¹ / q : ℝ)) : UnitCircle))
      atTop (𝓝 0)) :
    Tendsto
      (fun N : ℕ ↦
        (intervalCount (sampledSequence A α) N 0 ((p : ℝ) / q) : ℝ) / N)
      atTop (𝓝 ((p : ℝ) / q)) := by
  let t : ℝ := (p : ℝ) / q
  let F : ℕ → Finset ℤ := fun N ↦
    fullIntegerPoints A α⁻¹ t (A.cellIndex (α * N))
  let S : ℕ → Finset ℤ := fun N ↦ sampleIntegerPoints A α t N
  let R : ℕ → Finset ℤ := fun N ↦ remainderIntegerPoints A α N
  have hfull : Tendsto (fun N : ℕ ↦ ((F N).card : ℝ) / N)
      atTop (𝓝 t) := by
    simpa [F, t] using fullIntegerPointsRatio_tendsto A hα hp hpq havg
  have hZN := tendsto_scaledArgument_atTop hα
  have heventZ : ∀ᶠ N : ℕ in atTop, (A.seq 0 : ℝ) ≤ α * N :=
    hZN.eventually (eventually_ge_atTop (A.seq 0 : ℝ))
  have hdiff : Tendsto
      (fun N : ℕ ↦ (((S N \ F N).card : ℝ) / N)) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun N : ℕ ↦
      (α⁻¹ * A.seq 0 +
        α⁻¹ * ((A.seq (A.cellIndex (α * N) + 1) : ℝ) -
          A.seq (A.cellIndex (α * N))) + 1) / N)
    · filter_upwards [eventually_gt_atTop 0] with N hN
      exact div_nonneg (Nat.cast_nonneg _) (by positivity)
    · filter_upwards [eventually_gt_atTop 0, heventZ] with N hN hZ
      have hsub : S N \ F N ⊆ R N := by
        simpa [S, F, R, t] using
          sample_sdiff_full_subset_remainder A hα hp hpq hZ hz
      have hcard : (S N \ F N).card ≤ (R N).card := Finset.card_mono hsub
      have hcardR : (((S N \ F N).card : ℕ) : ℝ) ≤ (R N).card := by
        exact_mod_cast hcard
      have hrem := card_remainderIntegerPoints_le A hα hZ
      exact (div_le_div_iff_of_pos_right (by exact_mod_cast hN)).2
        (hcardR.trans (by simpa [R] using hrem))
    · exact boundaryRatio_tendsto_zero A hα
  have hsum := hfull.add hdiff
  have heq : (fun N : ℕ ↦ ((F N).card : ℝ) / N +
      (((S N \ F N).card : ℝ) / N)) =ᶠ[atTop]
      (fun N : ℕ ↦ ((S N).card : ℝ) / N) := by
    filter_upwards [eventually_gt_atTop 0, heventZ] with N hN hZ
    have hsub : F N ⊆ S N := by
      simpa [F, S, t] using
        fullIntegerPoints_subset_sampleIntegerPoints A hα hp hpq hZ hz
    have hcard := Finset.card_sdiff_add_card_eq_card hsub
    have hcardR : (((S N \ F N).card : ℕ) : ℝ) + (F N).card = (S N).card := by
      exact_mod_cast hcard
    field_simp
    linarith
  have hsamp : Tendsto (fun N : ℕ ↦ ((S N).card : ℝ) / N)
      atTop (𝓝 t) := by
    simpa only [add_zero] using hsum.congr' heq
  apply hsamp.congr'
  exact Eventually.of_forall fun N ↦ by
    simp only [S, t]
    rw [intervalCount_zero_eq_sampleIntegerPoints]

/-! ## Transport of the Haar-null exceptional set to the parameter `α` -/

private theorem ae_real_of_haar {P : UnitCircle → Prop}
    (hP : ∀ᵐ z ∂AddCircle.haarAddCircle, P z) :
    ∀ᵐ x : ℝ ∂volume, P (x : UnitCircle) := by
  have hvol : (volume : Measure UnitCircle) = AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  have hPvol : ∀ᵐ z ∂(volume : Measure UnitCircle), P z := by
    rwa [hvol]
  have hpieces : ∀ m : ℤ,
      ∀ᵐ x : ℝ ∂volume.restrict (Ioc (m : ℝ) (m + 1)),
        P (x : UnitCircle) := by
    intro m
    exact (AddCircle.measurePreserving_mk (1 : ℝ) (m : ℝ)).quasiMeasurePreserving.ae hPvol
  have hall : ∀ᵐ x : ℝ ∂volume.restrict
      (⋃ m : ℤ, Ioc (m : ℝ) (m + 1)), P (x : UnitCircle) :=
    (ae_restrict_iUnion_iff (fun m : ℤ ↦ Ioc (m : ℝ) (m + 1)) _).2 hpieces
  simpa only [iUnion_Ioc_intCast, Measure.restrict_univ] using hall

private lemma exists_mem_invCompactCover {y : ℝ} (hy : y ≠ 0) :
    ∃ n : ℕ,
      y ∈ Icc (1 / (n + 1 : ℝ)) (n + 1 : ℝ) ∪
        Icc (-(n + 1 : ℝ)) (-(1 / (n + 1 : ℝ))) := by
  rcases lt_or_gt_of_ne hy with hyneg | hypos
  · have hu : 0 < -y := neg_pos.mpr hyneg
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hu
    obtain ⟨m, hm⟩ := exists_nat_ge (-y)
    let n := max k m
    refine ⟨n, Or.inr ⟨?_, ?_⟩⟩
    · have hmle : (m : ℝ) ≤ n := by exact_mod_cast le_max_right k m
      dsimp only [n]
      linarith
    · have hkle : (k + 1 : ℝ) ≤ n + 1 := by
        exact_mod_cast Nat.add_le_add_right (le_max_left k m) 1
      have hinv : 1 / (n + 1 : ℝ) ≤ 1 / (k + 1 : ℝ) :=
        one_div_le_one_div_of_le (by positivity) hkle
      dsimp only [n] at hinv ⊢
      linarith
  · obtain ⟨k, hk⟩ := exists_nat_one_div_lt hypos
    obtain ⟨m, hm⟩ := exists_nat_ge y
    let n := max k m
    refine ⟨n, Or.inl ⟨?_, ?_⟩⟩
    · have hkle : (k + 1 : ℝ) ≤ n + 1 := by
        exact_mod_cast Nat.add_le_add_right (le_max_left k m) 1
      exact (one_div_le_one_div_of_le (by positivity) hkle).trans hk.le
    · have hmle : (m : ℝ) ≤ n := by exact_mod_cast le_max_right k m
      dsimp only [n]
      linarith

private lemma volume_inv_image_inter_Icc_eq_zero {s : Set ℝ}
    (hs : volume s = 0) {a b : ℝ} (hzero : (0 : ℝ) ∉ Icc a b) :
    volume ((fun x : ℝ ↦ x⁻¹) '' (s ∩ Icc a b)) = 0 := by
  have hsubset : Icc a b ⊆ ({0} : Set ℝ)ᶜ := by
    intro x hx hxeq
    have hx0 : x = 0 := Set.mem_singleton_iff.1 hxeq
    subst x
    exact hzero hx
  have hcd : ContDiffOn ℝ 1 (fun x : ℝ ↦ x⁻¹) (Icc a b) :=
    (contDiffOn_inv ℝ).mono hsubset
  obtain ⟨K, hK⟩ := hcd.exists_lipschitzOnWith one_ne_zero
    (convex_Icc a b) isCompact_Icc
  have hLip : LipschitzOnWith K (fun x : ℝ ↦ x⁻¹) (s ∩ Icc a b) :=
    hK.mono inter_subset_right
  have himage := hLip.hausdorffMeasure_image_le (d := (1 : ℝ)) zero_le_one
  have hsinter : volume (s ∩ Icc a b) = 0 :=
    measure_mono_null inter_subset_left hs
  rw [MeasureTheory.hausdorffMeasure_real] at himage
  rw [hsinter, mul_zero] at himage
  exact nonpos_iff_eq_zero.1 himage

private theorem quasiMeasurePreserving_inv_real :
    Measure.QuasiMeasurePreserving (fun x : ℝ ↦ x⁻¹) volume volume := by
  refine ⟨measurable_inv, Measure.AbsolutelyContinuous.mk ?_⟩
  intro s hsmeas hs
  rw [Measure.map_apply measurable_inv hsmeas]
  let P : ℕ → Set ℝ := fun n ↦ Icc (1 / (n + 1 : ℝ)) (n + 1 : ℝ)
  let Q : ℕ → Set ℝ := fun n ↦ Icc (-(n + 1 : ℝ)) (-(1 / (n + 1 : ℝ)))
  let U : Set ℝ := {0} ∪ ⋃ n : ℕ,
    ((fun x : ℝ ↦ x⁻¹) '' (s ∩ P n)) ∪
      ((fun x : ℝ ↦ x⁻¹) '' (s ∩ Q n))
  have hP (n : ℕ) : volume ((fun x : ℝ ↦ x⁻¹) '' (s ∩ P n)) = 0 := by
    apply volume_inv_image_inter_Icc_eq_zero hs
    simp only [P, mem_Icc, not_and_or]
    left
    exact not_le_of_gt (by positivity : (0 : ℝ) < 1 / (n + 1 : ℝ))
  have hQ (n : ℕ) : volume ((fun x : ℝ ↦ x⁻¹) '' (s ∩ Q n)) = 0 := by
    apply volume_inv_image_inter_Icc_eq_zero hs
    simp only [Q, mem_Icc, not_and_or]
    right
    exact not_le_of_gt (neg_lt_zero.mpr (by positivity : (0 : ℝ) < 1 / (n + 1 : ℝ)))
  have hU : volume U = 0 := by
    apply measure_union_null
    · exact Real.volume_singleton
    · apply measure_iUnion_null
      intro n
      exact measure_union_null (hP n) (hQ n)
  apply measure_mono_null _ hU
  intro x hx
  by_cases hx0 : x = 0
  · exact Or.inl (by simpa [hx0])
  · have hy : x⁻¹ ∈ s := hx
    obtain ⟨n, hn⟩ := exists_mem_invCompactCover (inv_ne_zero hx0)
    right
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    rcases hn with hn | hn
    · left
      exact ⟨x⁻¹, ⟨hy, hn⟩, inv_inv x⟩
    · right
      exact ⟨x⁻¹, ⟨hy, hn⟩, inv_inv x⟩

private def CircleGood (A : NatSubdivision) (z : UnitCircle) : Prop :=
  (∀ k : ℕ, 0 < k → k • z ≠ 0) ∧
    ∀ p q : ℕ, 0 < p → p < q →
      Tendsto (endpointErrorAverage A p q z) atTop (𝓝 0)

private theorem ae_circleGood (A : NatSubdivision) :
    ∀ᵐ z ∂AddCircle.haarAddCircle, CircleGood A z := by
  have hend : ∀ᵐ z ∂AddCircle.haarAddCircle,
      ∀ p q : ℕ, 0 < p → p < q →
        Tendsto (endpointErrorAverage A p q z) atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro p
    rw [ae_all_iff]
    intro q
    by_cases hp : 0 < p
    · by_cases hpq : p < q
      · filter_upwards [ae_endpointErrorAverage_tendsto A (hp.trans hpq) hpq] with z hz
        exact fun _ _ ↦ hz
      · exact ae_of_all _ fun _ _ hpq' ↦ (hpq hpq').elim
    · exact ae_of_all _ fun _ hp' _ ↦ (hp hp').elim
  filter_upwards [ae_nsmul_ne_zero, hend] with z hz hendz
  exact ⟨hz, hendz⟩

private theorem ae_circleGood_scaled_inv (A : NatSubdivision) :
    ∀ᵐ α : ℝ ∂volume, ∀ p q : ℕ, 0 < p → p < q →
      CircleGood A ((((α⁻¹ / q : ℝ)) : UnitCircle)) := by
  have hreal : ∀ᵐ γ : ℝ ∂volume, CircleGood A (γ : UnitCircle) :=
    ae_real_of_haar (ae_circleGood A)
  rw [ae_all_iff]
  intro p
  rw [ae_all_iff]
  intro q
  by_cases hp : 0 < p
  · by_cases hpq : p < q
    · have hq : 0 < q := hp.trans hpq
      have hqR : ((q : ℝ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast hq.ne')
      have hscale : ∀ᵐ β : ℝ ∂volume,
          CircleGood A ((((q : ℝ)⁻¹ * β : ℝ)) : UnitCircle) :=
        (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) hqR).ae hreal
      have hinv : ∀ᵐ α : ℝ ∂volume,
          CircleGood A ((((q : ℝ)⁻¹ * α⁻¹ : ℝ)) : UnitCircle) :=
        quasiMeasurePreserving_inv_real.ae hscale
      filter_upwards [hinv] with α hgood
      intro _ _
      convert hgood using 1
      congr 1
      rw [div_eq_mul_inv, mul_comm]
    · exact ae_of_all _ fun _ _ hpq' ↦ (hpq hpq').elim
  · exact ae_of_all _ fun _ hp' _ ↦ (hp hp').elim

private theorem ae_rationalAnchored_tendsto (A : NatSubdivision) :
    ∀ᵐ α : ℝ ∂volume, 0 < α →
      ∀ p q : ℕ, 0 < p → p < q →
        Tendsto
          (fun N : ℕ ↦
            (intervalCount (sampledSequence A α) N 0 ((p : ℝ) / q) : ℝ) / N)
          atTop (𝓝 ((p : ℝ) / q)) := by
  filter_upwards [ae_circleGood_scaled_inv A] with α hgood
  intro hα p q hp hpq
  have hg := hgood p q hp hpq
  exact rationalAnchored_tendsto A hα hp hpq hg.1 (hg.2 p q hp hpq)

private lemma intervalCount_mono_right (u : ℕ → ℝ) (N : ℕ)
    {r t : ℝ} (hrt : r ≤ t) : intervalCount u N 0 r ≤ intervalCount u N 0 t := by
  apply Finset.card_le_card
  intro n hn
  simp only [intervalCount, Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.1, hn.2.2.trans_le hrt⟩

private lemma exists_nat_div_eq_rat {r : ℚ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ p q : ℕ, 0 < p ∧ p < q ∧ (p : ℝ) / q = (r : ℝ) := by
  let p := r.num.toNat
  let q := r.den
  have hnum : 0 < r.num := Rat.num_pos.2 hr0
  have hpcast : (p : ℤ) = r.num := Int.toNat_of_nonneg hnum.le
  have hp : 0 < p := by
    have : (0 : ℤ) < (p : ℤ) := by rw [hpcast]; exact hnum
    exact_mod_cast this
  have hnumdenQ : (r.num : ℚ) < (r.den : ℚ) := by
    have h := hr1
    rw [← r.num_div_den] at h
    exact (div_lt_one (by positivity : (0 : ℚ) < r.den)).1 h
  have hpq : p < q := by
    have hnumdenZ : r.num < (r.den : ℤ) := by exact_mod_cast hnumdenQ
    have : (p : ℤ) < (q : ℤ) := by rw [hpcast]; exact hnumdenZ
    exact_mod_cast this
  refine ⟨p, q, hp, hpq, ?_⟩
  have hpcastR : (p : ℝ) = (r.num : ℝ) := by exact_mod_cast hpcast
  rw [hpcastR, Rat.cast_def]

private theorem anchored_tendsto_of_rational (u : ℕ → ℝ)
    (hrat : ∀ p q : ℕ, 0 < p → p < q →
      Tendsto
        (fun N : ℕ ↦ (intervalCount u N 0 ((p : ℝ) / q) : ℝ) / N)
        atTop (𝓝 ((p : ℝ) / q)))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Tendsto (fun N : ℕ ↦ (intervalCount u N 0 t : ℝ) / N)
      atTop (𝓝 t) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hleft : max 0 (t - ε / 4) < t :=
    max_lt ht0 (sub_lt_self t (by positivity))
  have hright : t < min 1 (t + ε / 4) :=
    lt_min ht1 (lt_add_of_pos_right t (by positivity))
  obtain ⟨r : ℚ, hrlo, hrhi⟩ := exists_rat_btwn hleft
  obtain ⟨s : ℚ, hslo, hshi⟩ := exists_rat_btwn hright
  have hr0R : (0 : ℝ) < (r : ℝ) :=
    lt_of_le_of_lt (le_max_left 0 (t - ε / 4)) hrlo
  have hr1R : (r : ℝ) < 1 := hrhi.trans ht1
  have hs0R : (0 : ℝ) < (s : ℝ) := ht0.trans hslo
  have hs1R : (s : ℝ) < 1 :=
    hshi.trans_le (min_le_left 1 (t + ε / 4))
  have hr0 : (0 : ℚ) < r := by exact_mod_cast hr0R
  have hr1 : r < (1 : ℚ) := by exact_mod_cast hr1R
  have hs0 : (0 : ℚ) < s := by exact_mod_cast hs0R
  have hs1 : s < (1 : ℚ) := by exact_mod_cast hs1R
  obtain ⟨pr, qr, hpr, hprq, hrEq⟩ := exists_nat_div_eq_rat hr0 hr1
  obtain ⟨ps, qs, hps, hpsq, hsEq⟩ := exists_nat_div_eq_rat hs0 hs1
  have hrlim := hrat pr qr hpr hprq
  have hslim := hrat ps qs hps hpsq
  obtain ⟨Nr, hNr⟩ := Metric.tendsto_atTop.1 hrlim (ε / 4) (by positivity)
  obtain ⟨Ns, hNs⟩ := Metric.tendsto_atTop.1 hslim (ε / 4) (by positivity)
  refine ⟨max 1 (max Nr Ns), fun N hN ↦ ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one
    ((le_max_left 1 (max Nr Ns)).trans hN)
  have hNrN : Nr ≤ N := (le_max_left Nr Ns).trans
    ((le_max_right 1 (max Nr Ns)).trans hN)
  have hNsN : Ns ≤ N := (le_max_right Nr Ns).trans
    ((le_max_right 1 (max Nr Ns)).trans hN)
  have hrclose := hNr N hNrN
  have hsclose := hNs N hNsN
  rw [Real.dist_eq] at hrclose hsclose ⊢
  rw [abs_lt] at hrclose hsclose ⊢
  have hmonoLow := intervalCount_mono_right u N (show ((pr : ℝ) / qr) ≤ t by
    rw [hrEq]
    exact hrhi.le)
  have hmonoUpp := intervalCount_mono_right u N (show t ≤ ((ps : ℝ) / qs) by
    rw [hsEq]
    exact hslo.le)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hdivLow : (intervalCount u N 0 ((pr : ℝ) / qr) : ℝ) / N ≤
      (intervalCount u N 0 t : ℝ) / N := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hmonoLow) hNreal.le
  have hdivUpp : (intervalCount u N 0 t : ℝ) / N ≤
      (intervalCount u N 0 ((ps : ℝ) / qs) : ℝ) / N := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hmonoUpp) hNreal.le
  rw [hrEq] at hrclose hdivLow
  rw [hsEq] at hsclose hdivUpp
  constructor
  · have hrt : t - ε / 4 < (r : ℝ) :=
      lt_of_le_of_lt (le_max_right 0 (t - ε / 4)) hrlo
    linarith
  · have hst : (s : ℝ) < t + ε / 4 :=
      hshi.trans_le (min_le_right 1 (t + ε / 4))
    linarith

private theorem anchored_tendsto_all (u : ℕ → ℝ)
    (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n < 1)
    (hrat : ∀ p q : ℕ, 0 < p → p < q →
      Tendsto
        (fun N : ℕ ↦ (intervalCount u N 0 ((p : ℝ) / q) : ℝ) / N)
        atTop (𝓝 ((p : ℝ) / q)))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Tendsto (fun N : ℕ ↦ (intervalCount u N 0 t : ℝ) / N)
      atTop (𝓝 t) := by
  rcases ht0.eq_or_lt with rfl | ht0'
  · simpa [intervalCount] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  rcases ht1.eq_or_lt with rfl | ht1'
  · have hcount : ∀ N, intervalCount u N 0 1 = N := by
      intro N
      simp [intervalCount, hu0, hu1]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    rw [hcount N, div_self]
    exact_mod_cast hN.ne'
  · exact anchored_tendsto_of_rational u hrat ht0' ht1'

private lemma intervalCount_cast_eq_sub (u : ℕ → ℝ)
    (hu0 : ∀ n, 0 ≤ u n) (N : ℕ) {s t : ℝ} (hst : s ≤ t) :
    (intervalCount u N s t : ℝ) =
      intervalCount u N 0 t - intervalCount u N 0 s := by
  let T := (Finset.range N).filter fun n ↦ u n ∈ Ico (0 : ℝ) t
  let S := (Finset.range N).filter fun n ↦ u n ∈ Ico (0 : ℝ) s
  let D := (Finset.range N).filter fun n ↦ u n ∈ Ico s t
  have hsubset : S ⊆ T := by
    intro n hn
    simp only [S, T, Finset.mem_filter, Finset.mem_range, mem_Ico] at hn ⊢
    exact ⟨hn.1, hn.2.1, hn.2.2.trans_le hst⟩
  have hdiff : T \ S = D := by
    ext n
    simp only [T, S, D, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_range, mem_Ico]
    constructor
    · rintro ⟨⟨hn, h0, hut⟩, hnot⟩
      refine ⟨hn, ?_, hut⟩
      by_contra hns
      exact hnot ⟨hn, h0, lt_of_not_ge hns⟩
    · rintro ⟨hn, hsu, hut⟩
      refine ⟨⟨hn, hu0 n, hut⟩, ?_⟩
      rintro ⟨_, _, hus⟩
      exact (not_lt_of_ge hsu) hus
  have hcard : (D.card : ℝ) = (T.card : ℝ) - (S.card : ℝ) := by
    rw [← hdiff]
    exact Finset.cast_card_sdiff hsubset
  simpa only [D, T, S, intervalCount] using hcard

private theorem uniformlyDistributed_of_rationalAnchored (A : NatSubdivision)
    (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n < 1)
    (hrat : ∀ p q : ℕ, 0 < p → p < q →
      Tendsto
        (fun N : ℕ ↦ (intervalCount u N 0 ((p : ℝ) / q) : ℝ) / N)
        atTop (𝓝 ((p : ℝ) / q))) :
    IsUniformlyDistributed u := by
  intro s t hs hst ht
  have hs1 : s ≤ 1 := hst.le.trans ht
  have ht0 : 0 ≤ t := hs.trans (le_of_lt hst)
  have hsLim := anchored_tendsto_all u hu0 hu1 hrat hs hs1
  have htLim := anchored_tendsto_all u hu0 hu1 hrat ht0 ht
  have hsub := htLim.sub hsLim
  convert hsub using 1
  ext N
  rw [← sub_div]
  congr 1
  exact intervalCount_cast_eq_sub u hu0 N hst.le

/-- Resolution of Erdős Problem 492 for the statement printed with a
strictly increasing natural-number subdivision.  For almost every positive
scaling parameter, the sampled fractional positions are uniformly
distributed in the half-open unit interval. -/
theorem erdos_492 (A : NatSubdivision) :
    ∀ᵐ α : ℝ ∂volume, 0 < α →
      IsUniformlyDistributed (sampledSequence A α) := by
  filter_upwards [ae_rationalAnchored_tendsto A] with α hrat
  intro hα
  apply uniformlyDistributed_of_rationalAnchored A
  · exact fun n ↦ A.fractionalPosition_nonneg (α * (n + 1))
  · exact fun n ↦ A.fractionalPosition_lt_one (α * (n + 1))
  · exact hrat hα

end

end Erdos492

#print axioms Erdos492.erdos_492
