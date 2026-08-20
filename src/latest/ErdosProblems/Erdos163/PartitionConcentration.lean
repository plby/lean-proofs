/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.Pruning

/-!
# Concentration of unnormalised defect sums under random bucketing

The random variable here is Lee's property (P2): sum the old defect weight
of every base tuple whose coordinates receive their prescribed labels.  We
keep repeated tuples in the statistic.  Injective tuples have exactly the
product probability; the total repeated-tuple weight is isolated as an
explicit diagonal error.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace PartitionConcentration

attribute [local instance] Classical.propDecidable

noncomputable section

universe u v

variable {P : Type u} [Fintype P] [DecidableEq P]

local instance optionMeasurableSpace : MeasurableSpace (Option P) := ⊤
local instance optionMeasurableSingletonClass :
    MeasurableSingletonClass (Option P) := ⟨fun _ => trivial⟩

/-- Unnormalised weight selected by a random labelling. -/
def rawStatistic {N : ℕ} {ι : Type v} [Fintype ι]
    (S : Finset (ι → Fin N)) (prescribed : ι → P)
    (weight : (ι → Fin N) → ℝ) (label : Fin N → Option P) : ℝ :=
  ∑ g ∈ S, if HostPartition.cylinder g prescribed label then weight g else 0

/-- Total tuple weight incident with one host vertex. -/
def incident {N : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]
    (S : Finset (ι → Fin N)) (weight : (ι → Fin N) → ℝ)
    (a : Fin N) : ℝ :=
  ∑ g ∈ S.filter (fun g => Pruning.tupleUses g a), weight g

theorem incident_familyTuples_eq_zero_of_not_mem
    {N : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]
    (base : ι → Finset (Fin N)) (weight : (ι → Fin N) → ℝ)
    (a : Fin N) (ha : ∀ i, a ∉ base i) :
    incident (FiniteDefect.familyTuples base) weight a = 0 := by
  unfold incident
  apply Finset.sum_eq_zero
  intro g hg
  exfalso
  rw [Finset.mem_filter] at hg
  obtain ⟨i, -, hgi⟩ := Finset.mem_image.mp hg.2
  rw [FiniteDefect.mem_familyTuples] at hg
  exact ha i (hgi ▸ hg.1 i)

/-- Coordinate sets obtained by retaining the prescribed label. -/
def selectedCoordinates {N : ℕ} {ι : Type v}
    (base : ι → Finset (Fin N)) (prescribed : ι → P)
    (label : Fin N → Option P) : ι → Finset (Fin N) := fun i =>
  (base i).filter fun a => label a = some (prescribed i)

theorem selectedCoordinates_subset {N : ℕ} {ι : Type v}
    (base : ι → Finset (Fin N)) (prescribed : ι → P)
    (label : Fin N → Option P) (i : ι) :
    selectedCoordinates base prescribed label i ⊆ base i :=
  Finset.filter_subset _ _

theorem cylinder_of_mem_selected_family
    {N : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]
    (base : ι → Finset (Fin N)) (prescribed : ι → P)
    (label : Fin N → Option P) (g : ι → Fin N)
    (hg : g ∈ FiniteDefect.familyTuples
      (selectedCoordinates base prescribed label)) :
    HostPartition.cylinder g prescribed label := by
  intro i
  rw [FiniteDefect.mem_familyTuples] at hg
  have hi := hg i
  exact (Finset.mem_filter.mp hi).2

/-- The selected raw family sum is dominated by the P2 statistic on the
unrestricted coordinate product. -/
theorem rawFamilyMoment_selected_le_rawStatistic
    {N θ s : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (base : ι → Finset (Fin N)) (prescribed : ι → P)
    (label : Fin N → Option P) (T : Finset (Fin N)) :
    HostTools.rawFamilyMoment G θ s
        (selectedCoordinates base prescribed label) T ≤
      rawStatistic (FiniteDefect.familyTuples base) prescribed
        (fun g => FiniteDefect.defectPower G θ g T s) label := by
  unfold HostTools.rawFamilyMoment rawStatistic
  have hsub : FiniteDefect.familyTuples
      (selectedCoordinates base prescribed label) ⊆
      FiniteDefect.familyTuples base := by
    intro g hg
    rw [FiniteDefect.mem_familyTuples] at hg ⊢
    intro i
    exact selectedCoordinates_subset base prescribed label i (hg i)
  calc
    (∑ g ∈ FiniteDefect.familyTuples
        (selectedCoordinates base prescribed label),
        FiniteDefect.defectPower G θ g T s) =
      ∑ g ∈ FiniteDefect.familyTuples
        (selectedCoordinates base prescribed label),
        (if HostPartition.cylinder g prescribed label then
          FiniteDefect.defectPower G θ g T s else 0) := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [if_pos (cylinder_of_mem_selected_family base prescribed label g hg)]
    _ ≤ ∑ g ∈ FiniteDefect.familyTuples base,
        (if HostPartition.cylinder g prescribed label then
          FiniteDefect.defectPower G θ g T s else 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro g hg hnot
      split
      · exact FiniteDefect.defectPower_nonneg G θ g T s
      · exact le_rfl

theorem weightedMean_indicator_eq_eventMass
    {N : ℕ} (q : P → ℝ) (E : Set (Fin N → Option P)) :
    Erdos136.McDiarmid.weightedMean (fun _ : Fin N => HostPartition.labelWeight q)
        (fun x => if x ∈ E then 1 else 0) =
      Erdos136.McDiarmid.eventMass (fun _ : Fin N => HostPartition.labelWeight q) E := by
  unfold Erdos136.McDiarmid.weightedMean Erdos136.McDiarmid.eventMass
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hE : x ∈ E <;> simp [hE]

theorem weightedMean_indicator_nonneg
    {N : ℕ} (q : P → ℝ) (E : Set (Fin N → Option P))
    (hq : ∀ p, 0 ≤ q p) (hqsum : ∑ p, q p ≤ 1) :
    0 ≤ Erdos136.McDiarmid.weightedMean
      (fun _ : Fin N => HostPartition.labelWeight q)
      (fun x => if x ∈ E then 1 else 0) := by
  rw [weightedMean_indicator_eq_eventMass]
  exact Erdos136.McDiarmid.eventMass_nonneg _
    (fun _ => HostPartition.labelWeight_nonneg q hq hqsum) E

theorem weightedMean_indicator_le_one
    {N : ℕ} (q : P → ℝ) (E : Set (Fin N → Option P))
    (hq : ∀ p, 0 ≤ q p) (hqsum : ∑ p, q p ≤ 1) :
    Erdos136.McDiarmid.weightedMean
      (fun _ : Fin N => HostPartition.labelWeight q)
      (fun x => if x ∈ E then 1 else 0) ≤ 1 := by
  rw [weightedMean_indicator_eq_eventMass]
  exact Erdos136.McDiarmid.eventMass_le_one _
    (fun _ => HostPartition.labelWeight_nonneg q hq hqsum)
    (fun _ => HostPartition.labelWeight_sum_one q) E

theorem weightedMean_rawStatistic_eq_sum
    {N : ℕ} {ι : Type v} [Fintype ι]
    (q : P → ℝ) (S : Finset (ι → Fin N)) (prescribed : ι → P)
    (weight : (ι → Fin N) → ℝ) :
    Erdos136.McDiarmid.weightedMean
        (fun _ : Fin N => HostPartition.labelWeight q)
        (rawStatistic S prescribed weight) =
      ∑ g ∈ S,
        Erdos136.McDiarmid.weightedMean
          (fun _ : Fin N => HostPartition.labelWeight q)
          (fun x => if HostPartition.cylinder g prescribed x then 1 else 0) * weight g := by
  unfold rawStatistic Erdos136.McDiarmid.weightedMean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g hg
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hc : HostPartition.cylinder g prescribed x <;> simp [hc]

/-- The mean is a product-probability main term plus the entire diagonal
weight.  No estimate for the diagonal has yet been inserted. -/
theorem weightedMean_rawStatistic_le
    {N : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]
    (q : P → ℝ) (S : Finset (ι → Fin N)) (prescribed : ι → P)
    (weight : (ι → Fin N) → ℝ)
    (hq : ∀ p, 0 ≤ q p) (hqsum : ∑ p, q p ≤ 1)
    (hweight : ∀ g ∈ S, 0 ≤ weight g) :
    Erdos136.McDiarmid.weightedMean
        (fun _ : Fin N => HostPartition.labelWeight q)
        (rawStatistic S prescribed weight) ≤
      (∏ i, q (prescribed i)) *
          (∑ g ∈ S.filter (fun g => Function.Injective g), weight g) +
        ∑ g ∈ S.filter (fun g => ¬Function.Injective g), weight g := by
  rw [weightedMean_rawStatistic_eq_sum]
  calc
    (∑ g ∈ S,
        Erdos136.McDiarmid.weightedMean
          (fun _ : Fin N => HostPartition.labelWeight q)
          (fun x => if HostPartition.cylinder g prescribed x then 1 else 0) * weight g) =
        (∑ g ∈ S.filter (fun g => Function.Injective g),
          Erdos136.McDiarmid.weightedMean
            (fun _ : Fin N => HostPartition.labelWeight q)
            (fun x => if HostPartition.cylinder g prescribed x then 1 else 0) * weight g) +
        ∑ g ∈ S.filter (fun g => ¬Function.Injective g),
          Erdos136.McDiarmid.weightedMean
            (fun _ : Fin N => HostPartition.labelWeight q)
            (fun x => if HostPartition.cylinder g prescribed x then 1 else 0) * weight g := by
      rw [← Finset.sum_filter_add_sum_filter_not S (fun g => Function.Injective g)]
    _ ≤ (∑ g ∈ S.filter (fun g => Function.Injective g),
          (∏ i, q (prescribed i)) * weight g) +
        ∑ g ∈ S.filter (fun g => ¬Function.Injective g), weight g := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro g hg
        have hginj := (Finset.mem_filter.mp hg).2
        rw [HostPartition.weightedMean_cylinder_of_injective q g prescribed hginj]
      · apply Finset.sum_le_sum
        intro g hg
        apply mul_le_of_le_one_left (hweight g (Finset.mem_filter.mp hg).1)
        exact weightedMean_indicator_le_one q
          {x | HostPartition.cylinder g prescribed x} hq hqsum
    _ = (∏ i, q (prescribed i)) *
          (∑ g ∈ S.filter (fun g => Function.Injective g), weight g) +
        ∑ g ∈ S.filter (fun g => ¬Function.Injective g), weight g := by
      rw [Finset.mul_sum]

theorem cylinder_congr_of_not_uses
    {N : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]
    (g : ι → Fin N) (prescribed : ι → P) (a : Fin N)
    (x y : Fin N → Option P) (hxy : ∀ j, j ≠ a → x j = y j)
    (ha : ¬Pruning.tupleUses g a) :
    HostPartition.cylinder g prescribed x ↔
      HostPartition.cylinder g prescribed y := by
  constructor <;> intro h i
  · rw [← h i]
    exact (hxy (g i) fun hia => ha <|
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hia⟩).symm
  · rw [← h i]
    exact hxy (g i) fun hia => ha <|
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hia⟩

/-- Changing one host label changes the raw statistic by at most the total
weight of tuples incident with that host vertex. -/
theorem rawStatistic_oscillation
    {N : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]
    (S : Finset (ι → Fin N)) (prescribed : ι → P)
    (weight : (ι → Fin N) → ℝ) (hweight : ∀ g ∈ S, 0 ≤ weight g)
    (a : Fin N) (x y : Fin N → Option P)
    (hxy : ∀ j, j ≠ a → x j = y j) :
    |rawStatistic S prescribed weight x - rawStatistic S prescribed weight y| ≤
      incident S weight a := by
  unfold rawStatistic incident
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  calc
    |∑ g ∈ S,
        ((if HostPartition.cylinder g prescribed x then weight g else 0) -
          if HostPartition.cylinder g prescribed y then weight g else 0)| ≤
        ∑ g ∈ S,
          |(if HostPartition.cylinder g prescribed x then weight g else 0) -
            if HostPartition.cylinder g prescribed y then weight g else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ g ∈ S,
        if Pruning.tupleUses g a then weight g else 0 := by
      apply Finset.sum_le_sum
      intro g hg
      by_cases huse : Pruning.tupleUses g a
      · simp only [huse, if_true]
        by_cases hx : HostPartition.cylinder g prescribed x <;>
          by_cases hy : HostPartition.cylinder g prescribed y <;>
            simp [hx, hy, abs_of_nonneg (hweight g hg)] <;>
              exact hweight g hg
      · have hc := cylinder_congr_of_not_uses g prescribed a x y hxy huse
        by_cases hx : HostPartition.cylinder g prescribed x
        · have hy := hc.mp hx
          simp [huse, hx, hy]
        · have hy : ¬HostPartition.cylinder g prescribed y := fun h => hx (hc.mpr h)
          simp [huse, hx, hy]
    _ = ∑ g ∈ S,
        if Pruning.tupleUses g a then weight g else 0 := rfl

/-! ## Simultaneous P1/P2 selection -/

theorem exists_labeling_good_with_raw
    {N : ℕ} {J X : Type*} [Fintype X] [DecidableEq J]
    (coord : X → Type*) [∀ a, Fintype (coord a)] [∀ a, DecidableEq (coord a)]
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : J → Finset (Fin N)) (color : P → J) (rootPart : X → P)
    (coordPart : ∀ a, coord a → P)
    (base : ∀ a, coord a → Finset (Fin N))
    (weight : ∀ a, (coord a → Fin N) → ℝ)
    (q : P → ℝ) (bound : X → Fin N → ℝ) (t : X → ℝ)
    (hq : ∀ p, 0 ≤ q p) (hqsum : ∑ p, q p ≤ 1)
    (hweight : ∀ a g, g ∈ FiniteDefect.familyTuples (base a) →
      0 ≤ weight a g)
    (hbound : ∀ a i, 0 ≤ bound a i)
    (hincident : ∀ a i,
      incident (FiniteDefect.familyTuples (base a)) (weight a) i ≤ bound a i)
    (ht : ∀ a, 0 ≤ t a)
    (hfail :
      let active : HostPartition.SamplingTest (P := P) X coord base → Fin N → Prop
        | Sum.inl p => fun v => v ∈ A (color p)
        | Sum.inr z => fun v => v ∈
            FiniteDefect.commonNeighbors G z.2.1 (A (color (rootPart z.1)))
      let which : HostPartition.SamplingTest (P := P) X coord base → P
        | Sum.inl p => p
        | Sum.inr z => rootPart z.1
      (∑ k, Real.exp
        (-2 * (q (which k) * ((Finset.univ.filter (active k)).card : ℝ) / 2) ^ 2 /
          ((Finset.univ.filter (active k)).card : ℝ))) +
      ∑ a : X, Real.exp
        (-2 * (t a) ^ 2 / ∑ i : Fin N, (bound a i) ^ 2) < 1) :
    ∃ label : Fin N → Option P,
      (∀ p, q p * ((A (color p)).card : ℝ) / 2 <
        ((HostPartition.bucket A color label p).card : ℝ)) ∧
      (∀ a (g : coord a → Fin N),
        g ∈ FiniteDefect.familyTuples (base a) →
        q (rootPart a) *
            ((FiniteDefect.commonNeighbors G g
              (A (color (rootPart a)))).card : ℝ) / 2 <
          ((FiniteDefect.commonNeighbors G g
            (HostPartition.bucket A color label (rootPart a))).card : ℝ)) ∧
      ∀ a,
        rawStatistic (FiniteDefect.familyTuples (base a))
            (coordPart a) (weight a) label <
          Erdos136.McDiarmid.weightedMean
            (fun _ : Fin N => HostPartition.labelWeight q)
            (rawStatistic (FiniteDefect.familyTuples (base a))
              (coordPart a) (weight a)) + t a := by
  let active : HostPartition.SamplingTest (P := P) X coord base → Fin N → Prop
    | Sum.inl p => fun v => v ∈ A (color p)
    | Sum.inr z => fun v => v ∈
        FiniteDefect.commonNeighbors G z.2.1 (A (color (rootPart z.1)))
  let which : HostPartition.SamplingTest (P := P) X coord base → P
    | Sum.inl p => p
    | Sum.inr z => rootPart z.1
  let f : X → (Fin N → Option P) → ℝ := fun a =>
    rawStatistic (FiniteDefect.familyTuples (base a))
      (coordPart a) (weight a)
  have hbd : ∀ a i (x y : Fin N → Option P),
      (∀ j, j ≠ i → x j = y j) → |f a x - f a y| ≤ bound a i := by
    intro a i x y hxy
    exact (rawStatistic_oscillation _ _ _ (hweight a) i x y hxy).trans
      (hincident a i)
  obtain ⟨label, hlower, hupper⟩ :=
    HostPartition.exists_assignment_lower_and_upper q active which f bound t
      hq hqsum hbound hbd ht (by simpa [active, which] using hfail)
  refine ⟨label, ?_, ?_, ?_⟩
  · intro p
    have hp := hlower (Sum.inl p)
    simpa [active, which, HostPartition.sampleCount_mem_eq_card] using hp
  · intro a g hg
    let z : Σ a : X, {g // g ∈ FiniteDefect.familyTuples (base a)} :=
      ⟨a, ⟨g, hg⟩⟩
    have hz := hlower (Sum.inr z)
    simpa [active, which, z, HostPartition.sampleCount_common_eq_card] using hz
  · intro a
    exact hupper a

/-- The simultaneous P1/P2 selection with Lee's third event as well: every
selected bucket also has an upper cardinality bound.  The extra statistic is
the bucket cardinality itself, whose bounded-difference constants are the
indicators of the corresponding base set. -/
theorem exists_labeling_good_with_raw_and_size
    {N : ℕ} {J X : Type*} [Fintype X] [DecidableEq J]
    (coord : X → Type*) [∀ a, Fintype (coord a)] [∀ a, DecidableEq (coord a)]
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : J → Finset (Fin N)) (color : P → J) (rootPart : X → P)
    (coordPart : ∀ a, coord a → P)
    (base : ∀ a, coord a → Finset (Fin N))
    (weight : ∀ a, (coord a → Fin N) → ℝ)
    (q : P → ℝ) (bound : X → Fin N → ℝ)
    (rawTail : X → ℝ) (sizeTail : P → ℝ)
    (hq : ∀ p, 0 ≤ q p) (hqsum : ∑ p, q p ≤ 1)
    (hweight : ∀ a g, g ∈ FiniteDefect.familyTuples (base a) →
      0 ≤ weight a g)
    (hbound : ∀ a i, 0 ≤ bound a i)
    (hincident : ∀ a i,
      incident (FiniteDefect.familyTuples (base a)) (weight a) i ≤ bound a i)
    (hrawTail : ∀ a, 0 ≤ rawTail a)
    (hsizeTail : ∀ p, 0 ≤ sizeTail p)
    (hfail :
      let active : HostPartition.SamplingTest (P := P) X coord base → Fin N → Prop
        | Sum.inl p => fun v => v ∈ A (color p)
        | Sum.inr z => fun v => v ∈
            FiniteDefect.commonNeighbors G z.2.1 (A (color (rootPart z.1)))
      let which : HostPartition.SamplingTest (P := P) X coord base → P
        | Sum.inl p => p
        | Sum.inr z => rootPart z.1
      (∑ k, Real.exp
        (-2 * (q (which k) * ((Finset.univ.filter (active k)).card : ℝ) / 2) ^ 2 /
          ((Finset.univ.filter (active k)).card : ℝ))) +
      (∑ p : P, Real.exp
        (-2 * (sizeTail p) ^ 2 / (N : ℝ))) +
      ∑ a : X, Real.exp
        (-2 * (rawTail a) ^ 2 / ∑ i : Fin N, (bound a i) ^ 2) < 1) :
    ∃ label : Fin N → Option P,
      (∀ p, q p * ((A (color p)).card : ℝ) / 2 <
        ((HostPartition.bucket A color label p).card : ℝ)) ∧
      (∀ a (g : coord a → Fin N),
        g ∈ FiniteDefect.familyTuples (base a) →
        q (rootPart a) *
            ((FiniteDefect.commonNeighbors G g
              (A (color (rootPart a)))).card : ℝ) / 2 <
          ((FiniteDefect.commonNeighbors G g
            (HostPartition.bucket A color label (rootPart a))).card : ℝ)) ∧
      (∀ p, ((HostPartition.bucket A color label p).card : ℝ) <
        q p * ((A (color p)).card : ℝ) + sizeTail p) ∧
      ∀ a,
        rawStatistic (FiniteDefect.familyTuples (base a))
            (coordPart a) (weight a) label <
          Erdos136.McDiarmid.weightedMean
            (fun _ : Fin N => HostPartition.labelWeight q)
            (rawStatistic (FiniteDefect.familyTuples (base a))
              (coordPart a) (weight a)) + rawTail a := by
  let active : HostPartition.SamplingTest (P := P) X coord base → Fin N → Prop
    | Sum.inl p => fun v => v ∈ A (color p)
    | Sum.inr z => fun v => v ∈
        FiniteDefect.commonNeighbors G z.2.1 (A (color (rootPart z.1)))
  let which : HostPartition.SamplingTest (P := P) X coord base → P
    | Sum.inl p => p
    | Sum.inr z => rootPart z.1
  let upperStat : Sum P X → (Fin N → Option P) → ℝ
    | Sum.inl p => HostPartition.sampleCount (fun v => v ∈ A (color p)) p
    | Sum.inr a => rawStatistic (FiniteDefect.familyTuples (base a))
        (coordPart a) (weight a)
  let upperBound : Sum P X → Fin N → ℝ
    | Sum.inl _ => fun _ => 1
    | Sum.inr a => bound a
  let upperTail : Sum P X → ℝ
    | Sum.inl p => sizeTail p
    | Sum.inr a => rawTail a
  have hupperBound : ∀ l i, 0 ≤ upperBound l i := by
    intro l i
    cases l with
    | inl p => norm_num [upperBound]
    | inr a => exact hbound a i
  have hupperOsc : ∀ l i (x y : Fin N → Option P),
      (∀ j, j ≠ i → x j = y j) →
        |upperStat l x - upperStat l y| ≤ upperBound l i := by
    intro l i x y hxy
    cases l with
    | inl p =>
        exact (HostPartition.sampleCount_oscillation
          (fun v => v ∈ A (color p)) p i x y hxy).trans (by
            simp only [upperBound]
            split <;> norm_num)
    | inr a =>
        exact (rawStatistic_oscillation _ _ _ (hweight a) i x y hxy).trans
          (hincident a i)
  have hupperTail : ∀ l, 0 ≤ upperTail l := by
    intro l
    cases l with
    | inl p => exact hsizeTail p
    | inr a => exact hrawTail a
  have hfail' :
      (∑ k : HostPartition.SamplingTest (P := P) X coord base, Real.exp
        (-2 * (q (which k) * ((Finset.univ.filter (active k)).card : ℝ) / 2) ^ 2 /
          ((Finset.univ.filter (active k)).card : ℝ))) +
      ∑ l : Sum P X, Real.exp
        (-2 * (upperTail l) ^ 2 / ∑ i : Fin N, (upperBound l i) ^ 2) < 1 := by
    have hupsum :
        (∑ l : Sum P X, Real.exp
          (-2 * (upperTail l) ^ 2 / ∑ i : Fin N, (upperBound l i) ^ 2)) =
        (∑ p : P, Real.exp
          (-2 * (sizeTail p) ^ 2 / (N : ℝ))) +
        ∑ a : X, Real.exp
          (-2 * (rawTail a) ^ 2 / ∑ i : Fin N, (bound a i) ^ 2) := by
      rw [Fintype.sum_sum_type]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      simp only [upperTail, upperBound]
      simp
    rw [hupsum]
    simpa only [active, which, add_assoc] using hfail
  obtain ⟨label, hlower, hupper⟩ :=
    HostPartition.exists_assignment_lower_and_upper q active which upperStat
      upperBound upperTail hq hqsum hupperBound hupperOsc hupperTail hfail'
  refine ⟨label, ?_, ?_, ?_, ?_⟩
  · intro p
    have hp := hlower (Sum.inl p)
    simpa [active, which, HostPartition.sampleCount_mem_eq_card] using hp
  · intro a g hg
    let z : Σ a : X, {g // g ∈ FiniteDefect.familyTuples (base a)} :=
      ⟨a, ⟨g, hg⟩⟩
    have hz := hlower (Sum.inr z)
    simpa [active, which, z, HostPartition.sampleCount_common_eq_card] using hz
  · intro p
    have hp := hupper (Sum.inl p)
    rw [HostPartition.weightedMean_sampleCount] at hp
    simpa [upperStat, upperTail, HostPartition.sampleCount_mem_eq_card] using hp
  · intro a
    exact hupper (Sum.inr a)

/-! ## Union bound for repeated coordinates -/

theorem noninjective_weight_le_pair_sum
    {N : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]
    (S : Finset (ι → Fin N)) (weight : (ι → Fin N) → ℝ)
    (hweight : ∀ g ∈ S, 0 ≤ weight g) :
    (∑ g ∈ S.filter (fun g => ¬Function.Injective g), weight g) ≤
      ∑ a : ι, ∑ b : ι,
        if a ≠ b then
          ∑ g ∈ S.filter (fun g => g a = g b), weight g
        else 0 := by
  let collisionWeight : (ι → Fin N) → ι → ι → ℝ := fun g a b =>
    if a ≠ b ∧ g a = g b then weight g else 0
  have hcollision_nonneg : ∀ g ∈ S, ∀ a b,
      0 ≤ collisionWeight g a b := by
    intro g hg a b
    dsimp [collisionWeight]
    split
    · exact hweight g hg
    · exact le_rfl
  have hpoint : ∀ g ∈ S.filter (fun g => ¬Function.Injective g),
      weight g ≤ ∑ a : ι, ∑ b : ι, collisionWeight g a b := by
    intro g hg
    obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp
      (Finset.mem_filter.mp hg).2
    have hterm : collisionWeight g a b = weight g := by
      simp [collisionWeight, hne, hab]
    calc
      weight g = collisionWeight g a b := hterm.symm
      _ ≤ ∑ z : ι, collisionWeight g a z := by
        exact Finset.single_le_sum
          (fun z hz => hcollision_nonneg g (Finset.mem_filter.mp hg).1 a z)
          (Finset.mem_univ b)
      _ ≤ ∑ y : ι, ∑ z : ι, collisionWeight g y z := by
        exact Finset.single_le_sum
          (fun y hy => Finset.sum_nonneg fun z hz =>
            hcollision_nonneg g (Finset.mem_filter.mp hg).1 y z)
          (Finset.mem_univ a)
  calc
    (∑ g ∈ S.filter (fun g => ¬Function.Injective g), weight g) ≤
        ∑ g ∈ S.filter (fun g => ¬Function.Injective g),
          ∑ a : ι, ∑ b : ι, collisionWeight g a b := by
      exact Finset.sum_le_sum fun g hg => hpoint g hg
    _ = ∑ a : ι, ∑ b : ι,
        ∑ g ∈ S.filter (fun g => ¬Function.Injective g),
          collisionWeight g a b := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ ≤ ∑ a : ι, ∑ b : ι, ∑ g ∈ S, collisionWeight g a b := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro g hg hnot
      exact hcollision_nonneg g hg a b
    _ = ∑ a : ι, ∑ b : ι,
        if a ≠ b then
          ∑ g ∈ S.filter (fun g => g a = g b), weight g
        else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hab : a = b
      · subst b
        simp [collisionWeight]
      · simp [collisionWeight, hab, Finset.sum_filter]

theorem noninjective_weight_le_card_sq_mul
    {N : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]
    (S : Finset (ι → Fin N)) (weight : (ι → Fin N) → ℝ)
    (hweight : ∀ g ∈ S, 0 ≤ weight g) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hdiag : ∀ a b : ι, a ≠ b →
      (∑ g ∈ S.filter (fun g => g a = g b), weight g) ≤ Δ) :
    (∑ g ∈ S.filter (fun g => ¬Function.Injective g), weight g) ≤
      (Fintype.card ι : ℝ) ^ 2 * Δ := by
  calc
    (∑ g ∈ S.filter (fun g => ¬Function.Injective g), weight g) ≤
        ∑ a : ι, ∑ b : ι,
          if a ≠ b then
            ∑ g ∈ S.filter (fun g => g a = g b), weight g
          else 0 := noninjective_weight_le_pair_sum S weight hweight
    _ ≤ ∑ _a : ι, ∑ _b : ι, Δ := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      by_cases hab : a = b
      · simp [hab, hΔ]
      · simpa [hab] using hdiag a b hab
    _ = (Fintype.card ι : ℝ) ^ 2 * Δ := by
      simp [pow_two]
      ring

/-- A convenient dominated form of the P2 mean estimate.  The selected
coordinate family `S` may be a restriction of a larger family `S₀`; both
its total weight and every specified diagonal are estimated in `S₀`. -/
theorem weightedMean_rawStatistic_le_of_domination
    {N : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]
    (q : P → ℝ) (S S₀ : Finset (ι → Fin N)) (prescribed : ι → P)
    (weight weight₀ : (ι → Fin N) → ℝ) (R Δ : ℝ)
    (hq : ∀ p, 0 ≤ q p) (hqsum : ∑ p, q p ≤ 1)
    (hweight : ∀ g ∈ S, 0 ≤ weight g)
    (hweight₀ : ∀ g ∈ S₀, 0 ≤ weight₀ g)
    (hsub : S ⊆ S₀) (hdom : ∀ g ∈ S, weight g ≤ weight₀ g)
    (hraw : (∑ g ∈ S₀, weight₀ g) ≤ R)
    (hΔ : 0 ≤ Δ)
    (hdiag : ∀ a b : ι, a ≠ b →
      (∑ g ∈ S₀.filter (fun g => g a = g b), weight₀ g) ≤ Δ) :
    Erdos136.McDiarmid.weightedMean
        (fun _ : Fin N => HostPartition.labelWeight q)
        (rawStatistic S prescribed weight) ≤
      (∏ i, q (prescribed i)) * R + (Fintype.card ι : ℝ) ^ 2 * Δ := by
  have hqprod : 0 ≤ ∏ i, q (prescribed i) :=
    Finset.prod_nonneg fun i hi => hq (prescribed i)
  have hsum : (∑ g ∈ S.filter (fun g => Function.Injective g), weight g) ≤ R := by
    calc
      (∑ g ∈ S.filter (fun g => Function.Injective g), weight g) ≤
          ∑ g ∈ S, weight g := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro g hg hnot
        exact hweight g hg
      _ ≤ ∑ g ∈ S, weight₀ g :=
        Finset.sum_le_sum fun g hg => hdom g hg
      _ ≤ ∑ g ∈ S₀, weight₀ g := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro g hg hnot
        exact hweight₀ g hg
      _ ≤ R := hraw
  have hdiagS : ∀ a b : ι, a ≠ b →
      (∑ g ∈ S.filter (fun g => g a = g b), weight g) ≤ Δ := by
    intro a b hab
    calc
      (∑ g ∈ S.filter (fun g => g a = g b), weight g) ≤
          ∑ g ∈ S.filter (fun g => g a = g b), weight₀ g := by
        apply Finset.sum_le_sum
        intro g hg
        exact hdom g (Finset.mem_filter.mp hg).1
      _ ≤ ∑ g ∈ S₀.filter (fun g => g a = g b), weight₀ g := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro g hg
          exact Finset.mem_filter.mpr
            ⟨hsub (Finset.mem_filter.mp hg).1, (Finset.mem_filter.mp hg).2⟩
        · intro g hg hnot
          exact hweight₀ g (Finset.mem_filter.mp hg).1
      _ ≤ Δ := hdiag a b hab
  calc
    Erdos136.McDiarmid.weightedMean
        (fun _ : Fin N => HostPartition.labelWeight q)
        (rawStatistic S prescribed weight) ≤
      (∏ i, q (prescribed i)) *
          (∑ g ∈ S.filter (fun g => Function.Injective g), weight g) +
        ∑ g ∈ S.filter (fun g => ¬Function.Injective g), weight g :=
      weightedMean_rawStatistic_le q S prescribed weight hq hqsum hweight
    _ ≤ (∏ i, q (prescribed i)) * R +
        (Fintype.card ι : ℝ) ^ 2 * Δ :=
      add_le_add (mul_le_mul_of_nonneg_left hsum hqprod)
        (noninjective_weight_le_card_sq_mul S weight hweight Δ hΔ hdiagS)

end
end PartitionConcentration
end Erdos163
