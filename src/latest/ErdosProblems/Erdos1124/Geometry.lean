/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1124.TorusTransfer
import ErdosProblems.Erdos1124.ProductGrid

/-!
# The concrete planar geometry for circle squaring

This file supplies the elementary geometric input to the discrepancy part of
the circle-squaring argument.  The grid is the half-open `1 / m` lattice grid.
The intersection count is an honest finite cardinality, formed in an explicit
box known to contain the bounded set in question.

The circle estimate is discrete: in each of the four signed quadrants the
circle is monotone, so the difference of the two sign-oriented grid indices
is injective.  The square estimate assigns each boundary cell to one of its
four sides.  In particular, neither estimate uses an asymptotic or a
measure-theoretic placeholder.
-/

open Set Metric MeasureTheory Bornology
open scoped Pointwise

namespace Erdos1124.Geometry

noncomputable section

/-- The Euclidean plane, with coordinates indexed by `Fin 2`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Integer labels of planar grid squares. -/
abbrev GridIndex := ℤ × ℤ

/-- Read a pair-valued grid index as a `Fin 2`-indexed function. -/
def indexCoord (z : GridIndex) : Fin 2 → ℤ := ![z.1, z.2]

@[simp] lemma indexCoord_zero (z : GridIndex) : indexCoord z 0 = z.1 := rfl
@[simp] lemma indexCoord_one (z : GridIndex) : indexCoord z 1 = z.2 := rfl

/-- The half-open square with lower-left corner `z / m` and side `1 / m`.
Only positive `m` is used below; defining the zero-scale case is harmless and
keeps the object total. -/
def gridSquare (m : ℕ) (z : GridIndex) : Set Plane :=
  {x | ∀ i, ((indexCoord z i : ℤ) : ℝ) / (m : ℝ) ≤ x i ∧
    x i < (((indexCoord z i : ℤ) : ℝ) + 1) / (m : ℝ)}

lemma mem_gridSquare {m : ℕ} {z : GridIndex} {x : Plane} :
    x ∈ gridSquare m z ↔
      ∀ i, ((indexCoord z i : ℤ) : ℝ) / (m : ℝ) ≤ x i ∧
        x i < (((indexCoord z i : ℤ) : ℝ) + 1) / (m : ℝ) := Iff.rfl

lemma measurableSet_gridSquare (m : ℕ) (z : GridIndex) :
    MeasurableSet (gridSquare m z) := by
  unfold gridSquare
  measurability

/-- The grid label of a point, obtained by flooring its scaled coordinates. -/
def gridIndex (m : ℕ) (x : Plane) : GridIndex :=
  (⌊(m : ℝ) * x 0⌋, ⌊(m : ℝ) * x 1⌋)

lemma mem_gridSquare_iff_gridIndex_eq {m : ℕ} (hm : 0 < m)
    {z : GridIndex} {x : Plane} :
    x ∈ gridSquare m z ↔ gridIndex m x = z := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  constructor
  · intro hx
    apply Prod.ext
    · apply (Int.floor_eq_iff).2
      constructor
      · simpa [mul_comm] using (div_le_iff₀ hmR).1 (hx 0).1
      · simpa [mul_comm] using (lt_div_iff₀ hmR).1 (hx 0).2
    · apply (Int.floor_eq_iff).2
      constructor
      · simpa [mul_comm] using (div_le_iff₀ hmR).1 (hx 1).1
      · simpa [mul_comm] using (lt_div_iff₀ hmR).1 (hx 1).2
  · rintro rfl
    intro i
    fin_cases i
    · change ((⌊(m : ℝ) * x 0⌋ : ℤ) : ℝ) / (m : ℝ) ≤ x 0 ∧
        x 0 < (((⌊(m : ℝ) * x 0⌋ : ℤ) : ℝ) + 1) / (m : ℝ)
      exact ⟨(div_le_iff₀ hmR).2 (by simpa [mul_comm] using
          (Int.floor_le ((m : ℝ) * x 0))),
        (lt_div_iff₀ hmR).2 (by simpa [mul_comm] using
          (Int.lt_floor_add_one ((m : ℝ) * x 0)))⟩
    · change ((⌊(m : ℝ) * x 1⌋ : ℤ) : ℝ) / (m : ℝ) ≤ x 1 ∧
        x 1 < (((⌊(m : ℝ) * x 1⌋ : ℤ) : ℝ) + 1) / (m : ℝ)
      exact ⟨(div_le_iff₀ hmR).2 (by simpa [mul_comm] using
          (Int.floor_le ((m : ℝ) * x 1))),
        (lt_div_iff₀ hmR).2 (by simpa [mul_comm] using
          (Int.lt_floor_add_one ((m : ℝ) * x 1)))⟩

lemma mem_gridSquare_gridIndex {m : ℕ} (hm : 0 < m) (x : Plane) :
    x ∈ gridSquare m (gridIndex m x) :=
  (mem_gridSquare_iff_gridIndex_eq hm).2 rfl

lemma gridSquare_disjoint {m : ℕ} (hm : 0 < m) {z w : GridIndex} (hzw : z ≠ w) :
    Disjoint (gridSquare m z) (gridSquare m w) := by
  rw [Set.disjoint_left]
  intro x hxz hxw
  have hz := (mem_gridSquare_iff_gridIndex_eq hm).1 hxz
  have hw := (mem_gridSquare_iff_gridIndex_eq hm).1 hxw
  exact hzw (hz.symm.trans hw)

/-- Every planar `m`-grid square has area `1 / m²`. -/
lemma volume_gridSquare {m : ℕ} (hm : 0 < m) (z : GridIndex) :
    volume (gridSquare m z) = ENNReal.ofReal (1 / (m : ℝ) ^ 2) := by
  let a : Fin 2 → ℝ := fun i ↦ ((indexCoord z i : ℤ) : ℝ) / (m : ℝ)
  let b : Fin 2 → ℝ := fun i ↦ (((indexCoord z i : ℤ) : ℝ) + 1) / (m : ℝ)
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin 2 → ℝ) → Plane) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm.toHomeomorph.measurableEmbedding
  rw [← (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage_emb hemb]
  have hpre :
      (WithLp.toLp 2 : (Fin 2 → ℝ) → Plane) ⁻¹' gridSquare m z =
        Set.pi Set.univ fun i ↦ Set.Ico (a i) (b i) := by
    ext x
    simp only [Set.mem_preimage, mem_gridSquare, Set.mem_pi, Set.mem_univ, forall_const,
      Set.mem_Ico, a, b]
  rw [hpre, Real.volume_pi_Ico, Fin.prod_univ_two]
  have hmR : (m : ℝ) ≠ 0 := by positivity
  simp only [a, b]
  have hdiff (i : Fin 2) :
      (((indexCoord z i : ℤ) : ℝ) + 1) / (m : ℝ) -
          ((indexCoord z i : ℤ) : ℝ) / (m : ℝ) = 1 / (m : ℝ) := by
    field_simp
    ring
  rw [hdiff 0, hdiff 1, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- The integer interval sufficient for a set contained in `[-R,R]²`. -/
def indexInterval (R m : ℕ) : Finset ℤ :=
  Finset.Icc (-((R * m : ℕ) : ℤ)) ((R * m : ℕ) : ℤ)

/-- All grid labels which can meet the coordinate box `[-R,R]²`. -/
def candidateCells (R m : ℕ) : Finset GridIndex :=
  indexInterval R m ×ˢ indexInterval R m

/-- A coordinatewise boundedness certificate. -/
def ContainedInBox (R : ℕ) (E : Set Plane) : Prop :=
  ∀ ⦃x⦄, x ∈ E → ∀ i, |x i| ≤ (R : ℝ)

/-- The finite collection of half-open grid cells which meet `E`, searched in
the explicit box of radius `R`. -/
noncomputable def gridCellsMeeting (R m : ℕ) (E : Set Plane) : Finset GridIndex := by
  classical
  exact (candidateCells R m).filter fun z ↦ (gridSquare m z ∩ E).Nonempty

/-- The finite boundary-intersection count used in the box-dimension estimate. -/
def gridIntersectionCount (R m : ℕ) (E : Set Plane) : ℕ :=
  (gridCellsMeeting R m E).card

@[simp] lemma mem_gridCellsMeeting {R m : ℕ} {E : Set Plane} {z : GridIndex} :
    z ∈ gridCellsMeeting R m E ↔
      z ∈ candidateCells R m ∧ (gridSquare m z ∩ E).Nonempty := by
  simp [gridCellsMeeting]

lemma gridIndex_mem_candidateCells {R m : ℕ} (hm : 0 < m) {E : Set Plane}
    (hE : ContainedInBox R E) {x : Plane} (hx : x ∈ E) :
    gridIndex m x ∈ candidateCells R m := by
  rw [candidateCells, Finset.mem_product]
  constructor <;> rw [indexInterval, Finset.mem_Icc]
  · constructor
    · change -((R * m : ℕ) : ℤ) ≤ ⌊(m : ℝ) * x 0⌋
      rw [Int.le_floor]
      have hx0 := (abs_le.mp (hE hx 0)).1
      push_cast
      nlinarith
    · change ⌊(m : ℝ) * x 0⌋ ≤ ((R * m : ℕ) : ℤ)
      have hx0 := (abs_le.mp (hE hx 0)).2
      rw [Int.floor_le_iff]
      push_cast
      have hmono : (m : ℝ) * x 0 ≤ (m : ℝ) * (R : ℝ) :=
        mul_le_mul_of_nonneg_left hx0 (by positivity)
      nlinarith
  · constructor
    · change -((R * m : ℕ) : ℤ) ≤ ⌊(m : ℝ) * x 1⌋
      rw [Int.le_floor]
      have hx1 := (abs_le.mp (hE hx 1)).1
      push_cast
      nlinarith
    · change ⌊(m : ℝ) * x 1⌋ ≤ ((R * m : ℕ) : ℤ)
      have hx1 := (abs_le.mp (hE hx 1)).2
      rw [Int.floor_le_iff]
      push_cast
      have hmono : (m : ℝ) * x 1 ≤ (m : ℝ) * (R : ℝ) :=
        mul_le_mul_of_nonneg_left hx1 (by positivity)
      nlinarith

/-- For a set certified to lie in `[-R,R]²`, the finite search really
contains every grid cell meeting the set. -/
lemma mem_gridCellsMeeting_of_mem {R m : ℕ} (hm : 0 < m) {E : Set Plane}
    (hE : ContainedInBox R E) {x : Plane} (hx : x ∈ E) :
    gridIndex m x ∈ gridCellsMeeting R m E := by
  rw [mem_gridCellsMeeting]
  exact ⟨gridIndex_mem_candidateCells hm hE hx,
    ⟨x, mem_gridSquare_gridIndex hm x, hx⟩⟩

/-! ## The unit circle -/

/-- Algebraic presentation of the unit circle. -/
def unitCircle : Set Plane := {x | x 0 ^ 2 + x 1 ^ 2 = 1}

/-- The unit closed disk. -/
def unitDisk : Set Plane := closedBall 0 1

lemma unitCircle_eq_sphere : unitCircle = sphere (0 : Plane) 1 := by
  ext x
  rw [unitCircle, mem_setOf_eq, mem_sphere, dist_zero_right]
  constructor
  · intro h
    have hsq : ‖x‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      exact h
    nlinarith [norm_nonneg x]
  · intro h
    calc
      x 0 ^ 2 + x 1 ^ 2 = ‖x‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      _ = 1 := by rw [h]; norm_num

lemma frontier_unitDisk : frontier unitDisk = unitCircle := by
  rw [unitDisk, frontier_closedBall (0 : Plane) one_ne_zero, unitCircle_eq_sphere]

lemma isClosed_unitDisk : IsClosed unitDisk := isClosed_closedBall
lemma measurableSet_unitDisk : MeasurableSet unitDisk := measurableSet_closedBall
lemma isBounded_unitDisk : Bornology.IsBounded unitDisk := isBounded_closedBall

lemma isClosed_unitCircle : IsClosed unitCircle := by
  rw [unitCircle_eq_sphere]
  exact isClosed_sphere

lemma measurableSet_unitCircle : MeasurableSet unitCircle := isClosed_unitCircle.measurableSet

lemma unitCircle_contained : ContainedInBox 1 unitCircle := by
  intro x hx i
  rw [unitCircle_eq_sphere, mem_sphere, dist_zero_right] at hx
  simpa using (PiLp.norm_apply_le x i).trans_eq hx

/-- Turn a sign choice into a nonnegative, sign-oriented real coordinate. -/
def orientedCoord (positive : Bool) (x : ℝ) : ℝ := if positive then x else -x

/-- The corresponding sign-oriented integer grid coordinate. -/
def orientedIndex (positive : Bool) (z : ℤ) : ℤ := if positive then z else -z

lemma orientedIndex_injective (positive : Bool) : Function.Injective (orientedIndex positive) := by
  intro z w h
  cases positive
  · change -z = -w at h
    omega
  · exact h

/-- The closed signed quadrant selected by a pair of booleans. -/
def quadrant (q : Bool × Bool) : Set Plane :=
  {x | 0 ≤ orientedCoord q.1 (x 0) ∧ 0 ≤ orientedCoord q.2 (x 1)}

def circleQuadrant (q : Bool × Bool) : Set Plane := unitCircle ∩ quadrant q

def circleQuadrantCells (m : ℕ) (q : Bool × Bool) : Finset GridIndex :=
  gridCellsMeeting 1 m (circleQuadrant q)

lemma orientedIndex_mono_of_cell {m : ℕ} (hm : 0 < m) (positive : Bool)
    {z w : ℤ} {x y : ℝ}
    (hz : ⌊(m : ℝ) * x⌋ = z) (hw : ⌊(m : ℝ) * y⌋ = w)
    (hxy : orientedCoord positive x ≤ orientedCoord positive y) :
    orientedIndex positive z ≤ orientedIndex positive w := by
  cases positive <;> simp [orientedCoord, orientedIndex] at hxy ⊢
  · have hmul : (m : ℝ) * y ≤ (m : ℝ) * x :=
      mul_le_mul_of_nonneg_left hxy (by positivity)
    have hf := Int.floor_mono hmul
    omega
  · have hmul : (m : ℝ) * x ≤ (m : ℝ) * y :=
      mul_le_mul_of_nonneg_left hxy (by positivity)
    simpa [hz, hw] using Int.floor_mono hmul

lemma circle_quadrant_antitone {q : Bool × Bool} {x y : Plane}
    (hxc : x ∈ circleQuadrant q) (hyc : y ∈ circleQuadrant q)
    (hxy : orientedCoord q.1 (x 0) ≤ orientedCoord q.1 (y 0)) :
    orientedCoord q.2 (y 1) ≤ orientedCoord q.2 (x 1) := by
  have hx0 : 0 ≤ orientedCoord q.1 (x 0) := hxc.2.1
  have hx1 : 0 ≤ orientedCoord q.2 (x 1) := hxc.2.2
  have hy0 : 0 ≤ orientedCoord q.1 (y 0) := hyc.2.1
  have hy1 : 0 ≤ orientedCoord q.2 (y 1) := hyc.2.2
  have hsq0 : orientedCoord q.1 (x 0) ^ 2 ≤ orientedCoord q.1 (y 0) ^ 2 :=
    (sq_le_sq₀ hx0 hy0).2 hxy
  have hxcircle := hxc.1
  have hycircle := hyc.1
  change x 0 ^ 2 + x 1 ^ 2 = 1 at hxcircle
  change y 0 ^ 2 + y 1 ^ 2 = 1 at hycircle
  have horient0x : orientedCoord q.1 (x 0) ^ 2 = x 0 ^ 2 := by
    cases q.1 <;> simp [orientedCoord]
  have horient1x : orientedCoord q.2 (x 1) ^ 2 = x 1 ^ 2 := by
    cases q.2 <;> simp [orientedCoord]
  have horient0y : orientedCoord q.1 (y 0) ^ 2 = y 0 ^ 2 := by
    cases q.1 <;> simp [orientedCoord]
  have horient1y : orientedCoord q.2 (y 1) ^ 2 = y 1 ^ 2 := by
    cases q.2 <;> simp [orientedCoord]
  apply (sq_le_sq₀ hy1 hx1).1
  rw [horient1y, horient1x]
  rw [horient0x, horient0y] at hsq0
  nlinarith

/-- In one signed quadrant, the oriented index difference uniquely identifies
a cell meeting the unit circle. -/
lemma circleQuadrant_indexDiff_injective {m : ℕ} (hm : 0 < m) (q : Bool × Bool) :
    Set.InjOn
      (fun z : GridIndex ↦ orientedIndex q.1 z.1 - orientedIndex q.2 z.2)
      (circleQuadrantCells m q) := by
  intro z hz w hw hdiff
  obtain ⟨x, hxcell, hxc⟩ := (mem_gridCellsMeeting.mp hz).2
  obtain ⟨y, hycell, hyc⟩ := (mem_gridCellsMeeting.mp hw).2
  have hxidx := (mem_gridSquare_iff_gridIndex_eq hm).1 hxcell
  have hyidx := (mem_gridSquare_iff_gridIndex_eq hm).1 hycell
  have hx0 : ⌊(m : ℝ) * x 0⌋ = z.1 := congrArg Prod.fst hxidx
  have hx1 : ⌊(m : ℝ) * x 1⌋ = z.2 := congrArg Prod.snd hxidx
  have hy0 : ⌊(m : ℝ) * y 0⌋ = w.1 := congrArg Prod.fst hyidx
  have hy1 : ⌊(m : ℝ) * y 1⌋ = w.2 := congrArg Prod.snd hyidx
  change orientedIndex q.1 z.1 - orientedIndex q.2 z.2 =
    orientedIndex q.1 w.1 - orientedIndex q.2 w.2 at hdiff
  rcases le_total (orientedCoord q.1 (x 0)) (orientedCoord q.1 (y 0)) with hxy | hyx
  · have h0 := orientedIndex_mono_of_cell hm q.1 hx0 hy0 hxy
    have hanti := circle_quadrant_antitone hxc hyc hxy
    have h1 := orientedIndex_mono_of_cell hm q.2 hy1 hx1 hanti
    have heq0 : orientedIndex q.1 z.1 = orientedIndex q.1 w.1 := by omega
    have heq1 : orientedIndex q.2 z.2 = orientedIndex q.2 w.2 := by omega
    apply Prod.ext
    · exact orientedIndex_injective q.1 heq0
    · exact orientedIndex_injective q.2 heq1
  · have h0 := orientedIndex_mono_of_cell hm q.1 hy0 hx0 hyx
    have hanti := circle_quadrant_antitone hyc hxc hyx
    have h1 := orientedIndex_mono_of_cell hm q.2 hx1 hy1 hanti
    have heq0 : orientedIndex q.1 z.1 = orientedIndex q.1 w.1 := by omega
    have heq1 : orientedIndex q.2 z.2 = orientedIndex q.2 w.2 := by omega
    apply Prod.ext
    · exact orientedIndex_injective q.1 heq0
    · exact orientedIndex_injective q.2 heq1

lemma circleQuadrant_indexDiff_mem {m : ℕ} (q : Bool × Bool) :
    Set.MapsTo
      (fun z : GridIndex ↦ orientedIndex q.1 z.1 - orientedIndex q.2 z.2)
      (circleQuadrantCells m q)
      (Finset.Icc (-2 * (m : ℤ)) (2 * (m : ℤ))) := by
  intro z hz
  have hzcand := (mem_gridCellsMeeting.mp hz).1
  rw [candidateCells, Finset.mem_product] at hzcand
  have hz0 := (Finset.mem_Icc.mp hzcand.1)
  have hz1 := (Finset.mem_Icc.mp hzcand.2)
  apply Finset.mem_Icc.mpr
  have ho0 : -(m : ℤ) ≤ orientedIndex q.1 z.1 ∧
      orientedIndex q.1 z.1 ≤ (m : ℤ) := by
    cases q.1 <;> simp [orientedIndex] <;> omega
  have ho1 : -(m : ℤ) ≤ orientedIndex q.2 z.2 ∧
      orientedIndex q.2 z.2 ≤ (m : ℤ) := by
    cases q.2 <;> simp [orientedIndex] <;> omega
  constructor
  · change -2 * (m : ℤ) ≤ orientedIndex q.1 z.1 - orientedIndex q.2 z.2
    omega
  · change orientedIndex q.1 z.1 - orientedIndex q.2 z.2 ≤ 2 * (m : ℤ)
    omega

lemma card_circleQuadrantCells_le {m : ℕ} (hm : 0 < m) (q : Bool × Bool) :
    (circleQuadrantCells m q).card ≤ 4 * m + 1 := by
  have hle := Finset.card_le_card_of_injOn
    (fun z : GridIndex ↦ orientedIndex q.1 z.1 - orientedIndex q.2 z.2)
    (circleQuadrant_indexDiff_mem (m := m) q)
    (circleQuadrant_indexDiff_injective hm q)
  rw [Int.card_Icc] at hle
  norm_num at hle ⊢
  omega

/-- Every point of the circle belongs to at least one of the four closed
signed quadrants. -/
lemma unitCircle_subset_iUnion_quadrants :
    unitCircle ⊆ ⋃ q : Bool × Bool, circleQuadrant q := by
  intro x hx
  by_cases hx0 : 0 ≤ x 0 <;> by_cases hx1 : 0 ≤ x 1
  · refine mem_iUnion.2 ⟨(true, true), ⟨hx, ?_⟩⟩
    change 0 ≤ x 0 ∧ 0 ≤ x 1
    exact ⟨hx0, hx1⟩
  · refine mem_iUnion.2 ⟨(true, false), ⟨hx, ?_⟩⟩
    change 0 ≤ x 0 ∧ 0 ≤ -x 1
    exact ⟨hx0, by linarith⟩
  · refine mem_iUnion.2 ⟨(false, true), ⟨hx, ?_⟩⟩
    change 0 ≤ -x 0 ∧ 0 ≤ x 1
    exact ⟨by linarith, hx1⟩
  · refine mem_iUnion.2 ⟨(false, false), ⟨hx, ?_⟩⟩
    change 0 ≤ -x 0 ∧ 0 ≤ -x 1
    constructor <;> linarith

lemma circleCells_subset_quadrantCells (m : ℕ) :
    gridCellsMeeting 1 m unitCircle ⊆
      (Finset.univ : Finset (Bool × Bool)).biUnion (circleQuadrantCells m) := by
  intro z hz
  obtain ⟨x, hxcell, hxcircle⟩ := (mem_gridCellsMeeting.mp hz).2
  obtain ⟨q, hxq⟩ := mem_iUnion.mp (unitCircle_subset_iUnion_quadrants hxcircle)
  rw [Finset.mem_biUnion]
  exact ⟨q, Finset.mem_univ q, mem_gridCellsMeeting.mpr
    ⟨(mem_gridCellsMeeting.mp hz).1, ⟨x, hxcell, hxq⟩⟩⟩

/-- **Linear boundary count for the unit disk.**  At grid scale `1 / m`,
at most `20m` half-open grid squares meet its boundary. -/
theorem unitCircle_gridIntersectionCount_le {m : ℕ} (hm : 0 < m) :
    gridIntersectionCount 1 m unitCircle ≤ 20 * m := by
  unfold gridIntersectionCount
  calc
    (gridCellsMeeting 1 m unitCircle).card ≤
        ((Finset.univ : Finset (Bool × Bool)).biUnion
          (circleQuadrantCells m)).card :=
      Finset.card_le_card (circleCells_subset_quadrantCells m)
    _ ≤ ∑ q ∈ (Finset.univ : Finset (Bool × Bool)),
        (circleQuadrantCells m q).card := Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ (Finset.univ : Finset (Bool × Bool)), (4 * m + 1) := by
      exact Finset.sum_le_sum fun q _ ↦ card_circleQuadrantCells_le hm q
    _ = 4 * (4 * m + 1) := by norm_num
    _ ≤ 20 * m := by omega

theorem unitDisk_boundary_gridIntersectionCount_le {m : ℕ} (hm : 0 < m) :
    gridIntersectionCount 1 m (frontier unitDisk) ≤ 20 * m := by
  rw [frontier_unitDisk]
  exact unitCircle_gridIntersectionCount_le hm

/-! ## The equal-area square -/

/-- Half the side length of the square of area `π`. -/
def squareHalfSide : ℝ := Real.sqrt Real.pi / 2

lemma squareHalfSide_pos : 0 < squareHalfSide := by
  unfold squareHalfSide
  positivity

lemma squareHalfSide_lt_one : squareHalfSide < 1 := by
  unfold squareHalfSide
  have hsqrt : Real.sqrt Real.pi < 2 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num [Real.pi_lt_four])
  linarith

lemma squareHalfSide_nonneg : 0 ≤ squareHalfSide := squareHalfSide_pos.le

/-- The origin-centered closed coordinate square with area `π`. -/
def equalAreaSquare : Set Plane :=
  {x | |x 0| ≤ squareHalfSide ∧ |x 1| ≤ squareHalfSide}

lemma isClosed_equalAreaSquare : IsClosed equalAreaSquare := by
  unfold equalAreaSquare
  exact (isClosed_le ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).abs)
      continuous_const).inter
    (isClosed_le ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1).abs)
      continuous_const)

lemma measurableSet_equalAreaSquare : MeasurableSet equalAreaSquare :=
  isClosed_equalAreaSquare.measurableSet

lemma equalAreaSquare_contained : ContainedInBox 1 equalAreaSquare := by
  intro x hx i
  fin_cases i
  · simpa using hx.1.trans squareHalfSide_lt_one.le
  · simpa using hx.2.trans squareHalfSide_lt_one.le

lemma isBounded_equalAreaSquare : Bornology.IsBounded equalAreaSquare := by
  refine (Metric.isBounded_closedBall :
    Bornology.IsBounded (closedBall (0 : Plane) 2)).subset ?_
  intro x hx
  rw [mem_closedBall_zero_iff]
  have hx0 : |x 0| ≤ (1 : ℝ) := by simpa using (equalAreaSquare_contained hx 0)
  have hx1 : |x 1| ≤ (1 : ℝ) := by simpa using (equalAreaSquare_contained hx 1)
  have hx0sq : x 0 ^ 2 ≤ (1 : ℝ) ^ 2 := (sq_le_sq).2 (by simpa using hx0)
  have hx1sq : x 1 ^ 2 ≤ (1 : ℝ) ^ 2 := (sq_le_sq).2 (by simpa using hx1)
  have hsquare : ‖x‖ ^ 2 ≤ 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    nlinarith
  nlinarith [norm_nonneg x]

/-- A vertical side (`axis = true`) or horizontal side (`axis = false`),
with the positive or negative endpoint selected by `positive`. -/
def squareSide (axis positive : Bool) : Set Plane :=
  if axis then
    {x | x 0 = (if positive then squareHalfSide else -squareHalfSide) ∧
      |x 1| ≤ squareHalfSide}
  else
    {x | x 1 = (if positive then squareHalfSide else -squareHalfSide) ∧
      |x 0| ≤ squareHalfSide}

/-- The elementary frontier characterization needed for assigning a boundary
cell to one of the four sides. -/
lemma frontier_equalAreaSquare_subset_sides :
    frontier equalAreaSquare ⊆ ⋃ q : Bool × Bool, squareSide q.1 q.2 := by
  intro x hx
  have hxsq : x ∈ equalAreaSquare := isClosed_equalAreaSquare.frontier_subset hx
  have hxnot : x ∉ interior equalAreaSquare := hx.2
  have hend : |x 0| = squareHalfSide ∨ |x 1| = squareHalfSide := by
    by_contra h
    push_neg at h
    have hx0 : |x 0| < squareHalfSide := lt_of_le_of_ne hxsq.1 h.1
    have hx1 : |x 1| < squareHalfSide := lt_of_le_of_ne hxsq.2 h.2
    have hr : 0 < min (squareHalfSide - |x 0|) (squareHalfSide - |x 1|) := by
      simp [sub_pos.mpr hx0, sub_pos.mpr hx1]
    apply hxnot
    rw [mem_interior_iff_mem_nhds]
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x hr) ?_
    intro y hy
    rw [mem_ball] at hy
    have hcoord (i : Fin 2) : |y i - x i| <
        min (squareHalfSide - |x 0|) (squareHalfSide - |x 1|) := by
      have hnorm := PiLp.norm_apply_le (y - x) i
      have hdist : ‖y - x‖ <
          min (squareHalfSide - |x 0|) (squareHalfSide - |x 1|) := by
        simpa [dist_eq_norm] using hy
      exact lt_of_le_of_lt (by simpa using hnorm) hdist
    constructor
    · have htri := abs_add_le (y 0 - x 0) (x 0)
      have hy0 : |y 0| ≤ |y 0 - x 0| + |x 0| := by
        simpa only [sub_add_cancel] using htri
      have hsum : |y 0 - x 0| + |x 0| < squareHalfSide := by
        have hc := hcoord 0
        have hmin := min_le_left (squareHalfSide - |x 0|)
          (squareHalfSide - |x 1|)
        linarith
      exact (hy0.trans_lt hsum).le
    · have htri := abs_add_le (y 1 - x 1) (x 1)
      have hy1 : |y 1| ≤ |y 1 - x 1| + |x 1| := by
        simpa only [sub_add_cancel] using htri
      have hsum : |y 1 - x 1| + |x 1| < squareHalfSide := by
        have hc := hcoord 1
        have hmin := min_le_right (squareHalfSide - |x 0|)
          (squareHalfSide - |x 1|)
        linarith
      exact (hy1.trans_lt hsum).le
  rcases hend with h0 | h1
  · rcases (abs_eq squareHalfSide_nonneg).1 h0 with hp | hn
    · exact mem_iUnion.2 ⟨(true, true), by simp [squareSide, hp, hxsq.2]⟩
    · exact mem_iUnion.2 ⟨(true, false), by simp [squareSide, hn, hxsq.2]⟩
  · rcases (abs_eq squareHalfSide_nonneg).1 h1 with hp | hn
    · exact mem_iUnion.2 ⟨(false, true), by simp [squareSide, hp, hxsq.1]⟩
    · exact mem_iUnion.2 ⟨(false, false), by simp [squareSide, hn, hxsq.1]⟩

def squareSideCells (m : ℕ) (axis positive : Bool) : Finset GridIndex :=
  gridCellsMeeting 1 m (squareSide axis positive)

def transverseIndex (axis : Bool) (z : GridIndex) : ℤ :=
  if axis then z.2 else z.1

lemma squareSide_transverse_injective {m : ℕ} (hm : 0 < m)
    (axis positive : Bool) :
    Set.InjOn (transverseIndex axis) (squareSideCells m axis positive) := by
  intro z hz w hw htrans
  obtain ⟨x, hxcell, hxside⟩ := (mem_gridCellsMeeting.mp hz).2
  obtain ⟨y, hycell, hyside⟩ := (mem_gridCellsMeeting.mp hw).2
  have hxidx := (mem_gridSquare_iff_gridIndex_eq hm).1 hxcell
  have hyidx := (mem_gridSquare_iff_gridIndex_eq hm).1 hycell
  cases axis
  · have hfixed : z.2 = w.2 := by
      have hz2 : ⌊(m : ℝ) * x 1⌋ = z.2 := congrArg Prod.snd hxidx
      have hw2 : ⌊(m : ℝ) * y 1⌋ = w.2 := congrArg Prod.snd hyidx
      simp only [squareSide, Bool.false_eq_true, if_false, mem_setOf_eq] at hxside hyside
      rw [hxside.1] at hz2
      rw [hyside.1] at hw2
      omega
    apply Prod.ext
    · simpa [transverseIndex] using htrans
    · exact hfixed
  · have hfixed : z.1 = w.1 := by
      have hz1 : ⌊(m : ℝ) * x 0⌋ = z.1 := congrArg Prod.fst hxidx
      have hw1 : ⌊(m : ℝ) * y 0⌋ = w.1 := congrArg Prod.fst hyidx
      simp only [squareSide, if_true, mem_setOf_eq] at hxside hyside
      rw [hxside.1] at hz1
      rw [hyside.1] at hw1
      omega
    apply Prod.ext
    · exact hfixed
    · simpa [transverseIndex] using htrans

lemma squareSide_transverse_mem {m : ℕ} (axis positive : Bool) :
    Set.MapsTo (transverseIndex axis) (squareSideCells m axis positive)
      (Finset.Icc (-(m : ℤ)) (m : ℤ)) := by
  intro z hz
  have hzcand := (mem_gridCellsMeeting.mp hz).1
  rw [candidateCells, Finset.mem_product] at hzcand
  cases axis
  · simpa [transverseIndex, indexInterval] using hzcand.1
  · simpa [transverseIndex, indexInterval] using hzcand.2

lemma card_squareSideCells_le {m : ℕ} (hm : 0 < m) (axis positive : Bool) :
    (squareSideCells m axis positive).card ≤ 2 * m + 1 := by
  have hle := Finset.card_le_card_of_injOn (transverseIndex axis)
    (squareSide_transverse_mem (m := m) axis positive)
    (squareSide_transverse_injective hm axis positive)
  rw [Int.card_Icc] at hle
  norm_num at hle ⊢
  omega

lemma squareBoundaryCells_subset_sideCells (m : ℕ) :
    gridCellsMeeting 1 m (frontier equalAreaSquare) ⊆
      (Finset.univ : Finset (Bool × Bool)).biUnion
        (fun q ↦ squareSideCells m q.1 q.2) := by
  intro z hz
  obtain ⟨x, hxcell, hxfrontier⟩ := (mem_gridCellsMeeting.mp hz).2
  obtain ⟨q, hxside⟩ := mem_iUnion.mp
    (frontier_equalAreaSquare_subset_sides hxfrontier)
  rw [Finset.mem_biUnion]
  exact ⟨q, Finset.mem_univ q, mem_gridCellsMeeting.mpr
    ⟨(mem_gridCellsMeeting.mp hz).1, ⟨x, hxcell, hxside⟩⟩⟩

/-- **Linear boundary count for the equal-area square.** -/
theorem equalAreaSquare_boundary_gridIntersectionCount_le {m : ℕ} (hm : 0 < m) :
    gridIntersectionCount 1 m (frontier equalAreaSquare) ≤ 12 * m := by
  unfold gridIntersectionCount
  calc
    (gridCellsMeeting 1 m (frontier equalAreaSquare)).card ≤
        ((Finset.univ : Finset (Bool × Bool)).biUnion
          (fun q ↦ squareSideCells m q.1 q.2)).card :=
      Finset.card_le_card (squareBoundaryCells_subset_sideCells m)
    _ ≤ ∑ q ∈ (Finset.univ : Finset (Bool × Bool)),
        (squareSideCells m q.1 q.2).card := Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ (Finset.univ : Finset (Bool × Bool)), (2 * m + 1) := by
      exact Finset.sum_le_sum fun q _ ↦ card_squareSideCells_le hm q.1 q.2
    _ = 4 * (2 * m + 1) := by norm_num
    _ ≤ 12 * m := by omega

/-! ## Placement in the torus fundamental square -/

/-- The center of the fundamental square. -/
def torusCenter : Plane := WithLp.toLp 2 (fun _ ↦ (1 / 2 : ℝ))

/-- A common affine embedding which places both compact sets strictly inside
the half-open fundamental square. -/
def torusEmbed (x : Plane) : Plane := torusCenter + (1 / 4 : ℝ) • x

lemma torusEmbed_apply (x : Plane) (i : Fin 2) :
    torusEmbed x i = 1 / 2 + (1 / 4 : ℝ) * x i := rfl

lemma torusEmbed_image_subset_fundamentalCube {E : Set Plane}
    (hE : ContainedInBox 1 E) :
    torusEmbed '' E ⊆ Erdos1124.TorusTransfer.fundamentalCube := by
  rintro y ⟨x, hx, rfl⟩ i
  have hi := abs_le.mp (hE hx i)
  norm_num at hi
  constructor
  · rw [torusEmbed_apply]
    linarith
  · rw [torusEmbed_apply]
    linarith

lemma torusEmbed_unitDisk_subset_fundamentalCube :
    torusEmbed '' unitDisk ⊆ Erdos1124.TorusTransfer.fundamentalCube := by
  apply torusEmbed_image_subset_fundamentalCube
  intro x hx i
  have hnorm : ‖x‖ ≤ 1 := by simpa [unitDisk] using hx
  simpa using (PiLp.norm_apply_le x i).trans hnorm

lemma torusEmbed_equalAreaSquare_subset_fundamentalCube :
    torusEmbed '' equalAreaSquare ⊆ Erdos1124.TorusTransfer.fundamentalCube :=
  torusEmbed_image_subset_fundamentalCube equalAreaSquare_contained

/-- The affine placement is a homeomorphism. -/
def torusEmbedHomeomorph : Plane ≃ₜ Plane :=
  (Homeomorph.smulOfNeZero (1 / 4 : ℝ) (by norm_num)).trans
    (Homeomorph.addLeft torusCenter)

@[simp] lemma torusEmbedHomeomorph_apply (x : Plane) :
    torusEmbedHomeomorph x = torusEmbed x := rfl

lemma measurableSet_torusEmbed_unitDisk : MeasurableSet (torusEmbed '' unitDisk) := by
  change MeasurableSet (torusEmbedHomeomorph '' unitDisk)
  exact torusEmbedHomeomorph.toMeasurableEquiv.measurableSet_image.2 measurableSet_unitDisk

lemma measurableSet_torusEmbed_equalAreaSquare :
    MeasurableSet (torusEmbed '' equalAreaSquare) := by
  change MeasurableSet (torusEmbedHomeomorph '' equalAreaSquare)
  exact torusEmbedHomeomorph.toMeasurableEquiv.measurableSet_image.2
    measurableSet_equalAreaSquare

/-! ## Application-facing volume and boundary-growth facts -/

lemma volume_unitDisk : volume unitDisk = ENNReal.ofReal Real.pi := by
  rw [unitDisk, EuclideanSpace.volume_closedBall_fin_two]
  norm_num

lemma equalAreaSquare_eq_coordinateBox :
    equalAreaSquare =
      (@WithLp.ofLp 2 (Fin 2 → ℝ)) ⁻¹'
        Icc (fun _ ↦ -squareHalfSide) (fun _ ↦ squareHalfSide) := by
  ext x
  simp only [equalAreaSquare, mem_setOf_eq, mem_preimage, mem_Icc, Pi.le_def]
  constructor
  · intro hx
    constructor
    · intro i
      fin_cases i
      · exact (abs_le.mp hx.1).1
      · exact (abs_le.mp hx.2).1
    · intro i
      fin_cases i
      · exact (abs_le.mp hx.1).2
      · exact (abs_le.mp hx.2).2
  · intro hx
    constructor
    · exact abs_le.2 ⟨hx.1 0, hx.2 0⟩
    · exact abs_le.2 ⟨hx.1 1, hx.2 1⟩

lemma volume_equalAreaSquare : volume equalAreaSquare = ENNReal.ofReal Real.pi := by
  rw [equalAreaSquare_eq_coordinateBox,
    (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
      measurableSet_Icc.nullMeasurableSet,
    Real.volume_Icc_pi]
  simp only [Fin.prod_univ_two]
  have hwidth : squareHalfSide - -squareHalfSide = Real.sqrt Real.pi := by
    rw [squareHalfSide]
    ring
  rw [hwidth, ← pow_two, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
    Real.sq_sqrt Real.pi_nonneg]

lemma volume_unitDisk_eq_volume_equalAreaSquare :
    volume unitDisk = volume equalAreaSquare := by
  rw [volume_unitDisk, volume_equalAreaSquare]

lemma torusEmbed_image_eq_translate_smul (E : Set Plane) :
    torusEmbed '' E = (fun y ↦ torusCenter + y) '' ((1 / 4 : ℝ) • E) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(1 / 4 : ℝ) • x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

lemma volume_torusEmbed_image (E : Set Plane) :
    volume (torusEmbed '' E) = ENNReal.ofReal ((1 / 4 : ℝ) ^ 2) * volume E := by
  rw [torusEmbed_image_eq_translate_smul]
  have htranslate (S : Set Plane) :
      volume ((fun y ↦ torusCenter + y) '' S) = volume S := by
    rw [show (fun y ↦ torusCenter + y) '' S =
        (fun y ↦ -torusCenter + y) ⁻¹' S by ext y; simp [eq_comm]]
    exact measure_preimage_add volume (-torusCenter) S
  rw [htranslate]
  simpa using volume.addHaar_smul_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) E

lemma volume_torusEmbed_unitDisk :
    volume (torusEmbed '' unitDisk) = ENNReal.ofReal ((1 / 4 : ℝ) ^ 2 * Real.pi) := by
  rw [volume_torusEmbed_image, volume_unitDisk, ← ENNReal.ofReal_mul (by positivity)]

lemma volume_torusEmbed_equalAreaSquare :
    volume (torusEmbed '' equalAreaSquare) =
      ENNReal.ofReal ((1 / 4 : ℝ) ^ 2 * Real.pi) := by
  rw [volume_torusEmbed_image, volume_equalAreaSquare,
    ← ENNReal.ofReal_mul (by positivity)]

lemma volume_torusEmbed_unitDisk_eq_equalAreaSquare :
    volume (torusEmbed '' unitDisk) = volume (torusEmbed '' equalAreaSquare) := by
  rw [volume_torusEmbed_unitDisk, volume_torusEmbed_equalAreaSquare]

lemma frontier_torusEmbed_image (E : Set Plane) :
    frontier (torusEmbed '' E) = torusEmbed '' frontier E := by
  change frontier (torusEmbedHomeomorph '' E) = torusEmbedHomeomorph '' frontier E
  exact (torusEmbedHomeomorph.image_frontier E).symm

lemma gridIndex_torusEmbed_four_mul (n : ℕ) (x : Plane) :
    gridIndex (4 * n) (torusEmbed x) =
      (((2 * n : ℕ) : ℤ) + (gridIndex n x).1,
        ((2 * n : ℕ) : ℤ) + (gridIndex n x).2) := by
  apply Prod.ext
  · change ⌊((4 * n : ℕ) : ℝ) * (1 / 2 + (1 / 4 : ℝ) * x 0)⌋ =
      ((2 * n : ℕ) : ℤ) + ⌊(n : ℝ) * x 0⌋
    convert Int.floor_natCast_add (2 * n) ((n : ℝ) * x 0) using 1 <;> push_cast <;> ring_nf
  · change ⌊((4 * n : ℕ) : ℝ) * (1 / 2 + (1 / 4 : ℝ) * x 1)⌋ =
      ((2 * n : ℕ) : ℤ) + ⌊(n : ℝ) * x 1⌋
    convert Int.floor_natCast_add (2 * n) ((n : ℝ) * x 1) using 1 <;> push_cast <;> ring_nf

def unshiftEmbeddedIndex (n : ℕ) (z : GridIndex) : GridIndex :=
  (z.1 - ((2 * n : ℕ) : ℤ), z.2 - ((2 * n : ℕ) : ℤ))

lemma unshiftEmbeddedIndex_injective (n : ℕ) :
    Function.Injective (unshiftEmbeddedIndex n) := by
  intro z w h
  apply Prod.ext
  · have := congrArg Prod.fst h
    change z.1 - ((2 * n : ℕ) : ℤ) = w.1 - ((2 * n : ℕ) : ℤ) at this
    omega
  · have := congrArg Prod.snd h
    change z.2 - ((2 * n : ℕ) : ℤ) = w.2 - ((2 * n : ℕ) : ℤ) at this
    omega

lemma unshift_gridIndex_torusEmbed (n : ℕ) (x : Plane) :
    unshiftEmbeddedIndex n (gridIndex (4 * n) (torusEmbed x)) = gridIndex n x := by
  rw [gridIndex_torusEmbed_four_mul]
  apply Prod.ext <;> simp [unshiftEmbeddedIndex]

lemma embeddedBoundaryCells_mapTo {R n : ℕ} (hn : 0 < n) {E : Set Plane}
    (hfront : ContainedInBox R (frontier E)) :
    Set.MapsTo (unshiftEmbeddedIndex n)
      (gridCellsMeeting 1 (4 * n) (frontier (torusEmbed '' E)))
      (gridCellsMeeting R n (frontier E)) := by
  intro z hz
  obtain ⟨y, hycell, hyfront⟩ := (mem_gridCellsMeeting.mp hz).2
  rw [frontier_torusEmbed_image] at hyfront
  obtain ⟨x, hxfront, rfl⟩ := hyfront
  have hzidx := (mem_gridSquare_iff_gridIndex_eq (Nat.mul_pos (by norm_num) hn)).1 hycell
  have hxmem := mem_gridCellsMeeting_of_mem hn hfront hxfront
  rw [← unshift_gridIndex_torusEmbed n x, hzidx] at hxmem
  exact hxmem

lemma embedded_boundary_gridIntersectionCount_le {R n : ℕ} (hn : 0 < n)
    {E : Set Plane} (hfront : ContainedInBox R (frontier E)) :
    gridIntersectionCount 1 (4 * n) (frontier (torusEmbed '' E)) ≤
      gridIntersectionCount R n (frontier E) := by
  unfold gridIntersectionCount
  exact Finset.card_le_card_of_injOn (unshiftEmbeddedIndex n)
    (embeddedBoundaryCells_mapTo hn hfront)
    (unshiftEmbeddedIndex_injective n).injOn

lemma frontier_unitDisk_contained : ContainedInBox 1 (frontier unitDisk) := by
  rw [frontier_unitDisk]
  exact unitCircle_contained

lemma frontier_equalAreaSquare_contained :
    ContainedInBox 1 (frontier equalAreaSquare) := by
  intro x hx i
  exact equalAreaSquare_contained (isClosed_equalAreaSquare.frontier_subset hx) i

theorem torusEmbed_unitDisk_boundary_count_le {n : ℕ} (hn : 0 < n) :
    gridIntersectionCount 1 (4 * n) (frontier (torusEmbed '' unitDisk)) ≤ 20 * n :=
  (embedded_boundary_gridIntersectionCount_le hn frontier_unitDisk_contained).trans
    (unitDisk_boundary_gridIntersectionCount_le hn)

theorem torusEmbed_equalAreaSquare_boundary_count_le {n : ℕ} (hn : 0 < n) :
    gridIntersectionCount 1 (4 * n)
        (frontier (torusEmbed '' equalAreaSquare)) ≤ 12 * n :=
  (embedded_boundary_gridIntersectionCount_le hn frontier_equalAreaSquare_contained).trans
    (equalAreaSquare_boundary_gridIntersectionCount_le hn)

/-! The boundary finset in exactly the type expected by `ProductGrid`. -/

def finGridIndex {m : ℕ} (c : Erdos1124.ProductGrid.GridCell 2 m) : GridIndex :=
  (((c 0).val : ℕ), ((c 1).val : ℕ))

noncomputable def fundamentalBoundaryCells (m : ℕ) (E : Set Plane) :
    Finset (Erdos1124.ProductGrid.GridCell 2 m) := by
  classical
  exact Finset.univ.filter fun c ↦ (gridSquare m (finGridIndex c) ∩ frontier E).Nonempty

lemma finGridIndex_injective {m : ℕ} : Function.Injective (@finGridIndex m) := by
  intro c d h
  funext i
  fin_cases i
  · have h0 := congrArg Prod.fst h
    change ((c 0).val : ℤ) = ((d 0).val : ℤ) at h0
    exact Fin.ext (by exact_mod_cast h0)
  · have h1 := congrArg Prod.snd h
    change ((c 1).val : ℤ) = ((d 1).val : ℤ) at h1
    exact Fin.ext (by exact_mod_cast h1)

lemma fundamentalBoundaryCells_mapTo_integerCells {m : ℕ} :
    Set.MapsTo (@finGridIndex m)
      (↑(fundamentalBoundaryCells m E) : Set (Erdos1124.ProductGrid.GridCell 2 m))
      (↑(gridCellsMeeting 1 m (frontier E)) : Set GridIndex) := by
  classical
  intro c hc
  change c ∈ fundamentalBoundaryCells m E at hc
  rw [fundamentalBoundaryCells, Finset.mem_filter] at hc
  apply mem_gridCellsMeeting.mpr
  constructor
  · change finGridIndex c ∈ candidateCells 1 m
    rw [candidateCells, Finset.mem_product]
    constructor
    · rw [indexInterval, Finset.mem_Icc]
      · constructor
        · unfold finGridIndex
          exact (neg_nonpos.mpr (Int.ofNat_zero_le _)).trans (Int.ofNat_zero_le _)
        · have hc0 : ((c 0).val : ℤ) ≤ (m : ℤ) := by
            exact_mod_cast (c 0).isLt.le
          simpa [finGridIndex] using hc0
    · rw [indexInterval, Finset.mem_Icc]
      constructor
      · unfold finGridIndex
        exact (neg_nonpos.mpr (Int.ofNat_zero_le _)).trans (Int.ofNat_zero_le _)
      · have hc1 : ((c 1).val : ℤ) ≤ (m : ℤ) := by
          exact_mod_cast (c 1).isLt.le
        simpa [finGridIndex] using hc1
  · exact hc.2

lemma card_fundamentalBoundaryCells_le (m : ℕ) (E : Set Plane) :
    (fundamentalBoundaryCells m E).card ≤ gridIntersectionCount 1 m (frontier E) := by
  unfold gridIntersectionCount
  exact Finset.card_le_card_of_injOn finGridIndex
    fundamentalBoundaryCells_mapTo_integerCells finGridIndex_injective.injOn

theorem card_fundamentalBoundaryCells_torusEmbed_unitDisk_le {n : ℕ} (hn : 0 < n) :
    (fundamentalBoundaryCells (4 * n) (torusEmbed '' unitDisk)).card ≤ 20 * n :=
  (card_fundamentalBoundaryCells_le _ _).trans (torusEmbed_unitDisk_boundary_count_le hn)

theorem card_fundamentalBoundaryCells_torusEmbed_equalAreaSquare_le
    {n : ℕ} (hn : 0 < n) :
    (fundamentalBoundaryCells (4 * n) (torusEmbed '' equalAreaSquare)).card ≤ 12 * n :=
  (card_fundamentalBoundaryCells_le _ _).trans
    (torusEmbed_equalAreaSquare_boundary_count_le hn)

/-! ## A concrete robust product-grid sandwich

For a coarse cell `c`, `expandedGridSquare m c` is the union of the cell and
its (up to) eight coordinatewise neighbours.  This is the right robust
object for the product-grid lemma: a point at coordinate distance at most
`1 / m` from any regular point over `c` lies in this expanded square.
-/

/-- The geometric three-by-three neighbourhood of a fundamental grid cell. -/
def expandedGridSquare (m : ℕ)
    (c : Erdos1124.ProductGrid.GridCell 2 m) : Set Plane :=
  {x | ∀ i,
    (((c i).val : ℝ) - 1) / (m : ℝ) ≤ x i ∧
      x i < (((c i).val : ℝ) + 2) / (m : ℝ)}

lemma expandedGridSquare_nonempty {m : ℕ} (hm : 0 < m)
    (c : Erdos1124.ProductGrid.GridCell 2 m) :
    (expandedGridSquare m c).Nonempty := by
  let x : Plane := WithLp.toLp 2 fun i ↦ ((c i).val : ℝ) / (m : ℝ)
  refine ⟨x, ?_⟩
  intro i
  change (((c i).val : ℝ) - 1) / (m : ℝ) ≤ ((c i).val : ℝ) / (m : ℝ) ∧
    ((c i).val : ℝ) / (m : ℝ) < (((c i).val : ℝ) + 2) / (m : ℝ)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  constructor
  · exact (div_le_div_iff_of_pos_right hmR).2 (by norm_num)
  · exact (div_lt_div_iff_of_pos_right hmR).2 (by norm_num)

lemma convex_expandedGridSquare (m : ℕ)
    (c : Erdos1124.ProductGrid.GridCell 2 m) :
    Convex ℝ (expandedGridSquare m c) := by
  intro x hx y hy a b ha hb hab i
  change ∀ i, (((c i).val : ℝ) - 1) / (m : ℝ) ≤ x i ∧
    x i < (((c i).val : ℝ) + 2) / (m : ℝ) at hx
  change ∀ i, (((c i).val : ℝ) - 1) / (m : ℝ) ≤ y i ∧
    y i < (((c i).val : ℝ) + 2) / (m : ℝ) at hy
  change (((c i).val : ℝ) - 1) / (m : ℝ) ≤
      (a • x + b • y : Plane) i ∧
    (a • x + b • y : Plane) i < (((c i).val : ℝ) + 2) / (m : ℝ)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  constructor
  · calc
      (((c i).val : ℝ) - 1) / (m : ℝ) =
          a * ((((c i).val : ℝ) - 1) / (m : ℝ)) +
            b * ((((c i).val : ℝ) - 1) / (m : ℝ)) := by
              rw [← add_mul, hab, one_mul]
      _ ≤ a * x i + b * y i := add_le_add
        (mul_le_mul_of_nonneg_left (hx i).1 ha)
        (mul_le_mul_of_nonneg_left (hy i).1 hb)
  · by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using (hy i).2
    · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      calc
        a * x i + b * y i <
            a * ((((c i).val : ℝ) + 2) / (m : ℝ)) +
              b * ((((c i).val : ℝ) + 2) / (m : ℝ)) :=
          add_lt_add_of_lt_of_le
            (mul_lt_mul_of_pos_left (hx i).2 ha')
            (mul_le_mul_of_nonneg_left (hy i).2.le hb)
        _ = (((c i).val : ℝ) + 2) / (m : ℝ) := by
          rw [← add_mul, hab, one_mul]

/-- Fundamental cells whose whole three-by-three neighbourhood lies in `E`. -/
noncomputable def robustLowerCells (m : ℕ) (E : Set Plane) :
    Finset (Erdos1124.ProductGrid.GridCell 2 m) := by
  classical
  exact Finset.univ.filter fun c ↦ expandedGridSquare m c ⊆ E

/-- Fundamental cells whose three-by-three neighbourhood meets `E`. -/
noncomputable def robustUpperCells (m : ℕ) (E : Set Plane) :
    Finset (Erdos1124.ProductGrid.GridCell 2 m) := by
  classical
  exact Finset.univ.filter fun c ↦ (expandedGridSquare m c ∩ E).Nonempty

/-- The one-dimensional set of valid grid indices at distance at most one. -/
def coordinateNeighbors {m : ℕ} (e : Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun c ↦ c.val ≤ e.val + 1 ∧ e.val ≤ c.val + 1

/-- The coordinatewise one-cell halo. -/
def cellNeighbors {m : ℕ} (e : Erdos1124.ProductGrid.GridCell 2 m) :
    Finset (Erdos1124.ProductGrid.GridCell 2 m) :=
  Fintype.piFinset fun i ↦ coordinateNeighbors (e i)

@[simp] lemma mem_coordinateNeighbors {m : ℕ} {c e : Fin m} :
    c ∈ coordinateNeighbors e ↔ c.val ≤ e.val + 1 ∧ e.val ≤ c.val + 1 := by
  simp [coordinateNeighbors]

@[simp] lemma mem_cellNeighbors {m : ℕ}
    {c e : Erdos1124.ProductGrid.GridCell 2 m} :
    c ∈ cellNeighbors e ↔ ∀ i, c i ∈ coordinateNeighbors (e i) := by
  simp [cellNeighbors]

lemma card_coordinateNeighbors_le_three {m : ℕ} (e : Fin m) :
    (coordinateNeighbors e).card ≤ 3 := by
  let f : Fin m ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  have hmap : Set.MapsTo f
      (↑(coordinateNeighbors e) : Set (Fin m))
      (↑(Finset.Icc (e.val - 1) (e.val + 1)) : Set ℕ) := by
    intro c hc
    change c ∈ coordinateNeighbors e at hc
    rw [mem_coordinateNeighbors] at hc
    change f c ∈ Finset.Icc (e.val - 1) (e.val + 1)
    rw [Finset.mem_Icc]
    dsimp [f]
    omega
  calc
    (coordinateNeighbors e).card ≤ (Finset.Icc (e.val - 1) (e.val + 1)).card :=
      Finset.card_le_card_of_injOn f hmap f.injective.injOn
    _ ≤ 3 := by simp; omega

lemma card_cellNeighbors_le_nine {m : ℕ}
    (e : Erdos1124.ProductGrid.GridCell 2 m) :
    (cellNeighbors e).card ≤ 3 ^ 2 := by
  rw [cellNeighbors, Fintype.card_piFinset, Fin.prod_univ_two]
  exact Nat.mul_le_mul (card_coordinateNeighbors_le_three (e 0))
    (card_coordinateNeighbors_le_three (e 1))

/-- A preconnected set containing a point of `E` and a point outside `E`
must meet the topological boundary of `E`. -/
lemma IsPreconnected.inter_frontier_nonempty {S E : Set Plane}
    (hS : IsPreconnected S) (hin : (S ∩ E).Nonempty)
    (hout : (S ∩ Eᶜ).Nonempty) : (S ∩ frontier E).Nonempty := by
  by_contra hfront
  have hsub : S ⊆ (frontier E)ᶜ := by
    intro x hx hxf
    exact hfront ⟨x, hx, hxf⟩
  rw [compl_frontier_eq_union_interior] at hsub
  have hdisj : Disjoint (interior E) (interior Eᶜ) := by
    apply Set.disjoint_left.2
    intro x hx hx'
    have hxE : x ∈ E := interior_subset hx
    have hxEc : x ∈ Eᶜ := interior_subset hx'
    exact hxEc hxE
  rcases hS.subset_or_subset isOpen_interior isOpen_interior hdisj hsub with h | h
  · obtain ⟨x, hxS, hxE⟩ := hout
    have hxEi : x ∈ interior E := h hxS
    exact hxE (interior_subset hxEi)
  · obtain ⟨x, hxS, hxE⟩ := hin
    have hxEc : x ∈ Eᶜ := interior_subset (h hxS)
    exact hxEc hxE

/-- Every point of the half-open fundamental cube has a unique fundamental
`m`-grid cell.  This existence form avoids introducing a clamped total cell
index outside the cube. -/
lemma exists_fundamentalCell {m : ℕ} (hm : 0 < m) {x : Plane}
    (hx : x ∈ Erdos1124.TorusTransfer.fundamentalCube) :
    ∃ c : Erdos1124.ProductGrid.GridCell 2 m,
      x ∈ gridSquare m (finGridIndex c) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hcoord (i : Fin 2) :
      0 ≤ ⌊(m : ℝ) * x i⌋ ∧ ⌊(m : ℝ) * x i⌋ < (m : ℤ) := by
    constructor
    · rw [Int.le_floor]
      simpa using mul_nonneg hmR.le (hx i).1
    · rw [Int.floor_lt]
      simpa using mul_lt_mul_of_pos_left (hx i).2 hmR
  let c : Erdos1124.ProductGrid.GridCell 2 m := fun i ↦
    ⟨⌊(m : ℝ) * x i⌋.toNat, by
      have hi := (hcoord i).2
      have hmInt : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
      have := (Int.toNat_lt_toNat hmInt).2 hi
      simpa using this⟩
  refine ⟨c, ?_⟩
  rw [mem_gridSquare_iff_gridIndex_eq hm]
  apply Prod.ext
  · change ⌊(m : ℝ) * x 0⌋ = ((c 0).val : ℤ)
    simp only [c]
    exact (Int.toNat_of_nonneg (hcoord 0).1).symm
  · change ⌊(m : ℝ) * x 1⌋ = ((c 1).val : ℤ)
    simp only [c]
    exact (Int.toNat_of_nonneg (hcoord 1).1).symm

lemma gridSquare_subset_expandedGridSquare {m : ℕ} (hm : 0 < m)
    (c : Erdos1124.ProductGrid.GridCell 2 m) :
    gridSquare m (finGridIndex c) ⊆ expandedGridSquare m c := by
  intro x hx i
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hi := hx i
  fin_cases i
  · change ((c 0).val : ℝ) / (m : ℝ) ≤ x 0 ∧
      x 0 < (((c 0).val : ℝ) + 1) / (m : ℝ) at hi
    change (((c 0).val : ℝ) - 1) / (m : ℝ) ≤ x 0 ∧
      x 0 < (((c 0).val : ℝ) + 2) / (m : ℝ)
    constructor
    · exact ((div_le_div_iff_of_pos_right hmR).2 (by norm_num)).trans hi.1
    · exact hi.2.trans ((div_lt_div_iff_of_pos_right hmR).2 (by norm_num))
  · change ((c 1).val : ℝ) / (m : ℝ) ≤ x 1 ∧
      x 1 < (((c 1).val : ℝ) + 1) / (m : ℝ) at hi
    change (((c 1).val : ℝ) - 1) / (m : ℝ) ≤ x 1 ∧
      x 1 < (((c 1).val : ℝ) + 2) / (m : ℝ)
    constructor
    · exact ((div_le_div_iff_of_pos_right hmR).2 (by norm_num)).trans hi.1
    · exact hi.2.trans ((div_lt_div_iff_of_pos_right hmR).2 (by norm_num))

lemma gridSquare_expanded_implies_neighbor {m : ℕ} (hm : 0 < m)
    {c e : Erdos1124.ProductGrid.GridCell 2 m} {x : Plane}
    (hxc : x ∈ expandedGridSquare m c)
    (hxe : x ∈ gridSquare m (finGridIndex e)) :
    c ∈ cellNeighbors e := by
  rw [mem_cellNeighbors]
  intro i
  rw [mem_coordinateNeighbors]
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hc := hxc i
  have he := hxe i
  fin_cases i
  · change (((c 0).val : ℝ) - 1) / (m : ℝ) ≤ x 0 ∧
      x 0 < (((c 0).val : ℝ) + 2) / (m : ℝ) at hc
    change ((e 0).val : ℝ) / (m : ℝ) ≤ x 0 ∧
      x 0 < (((e 0).val : ℝ) + 1) / (m : ℝ) at he
    change (c 0).val ≤ (e 0).val + 1 ∧ (e 0).val ≤ (c 0).val + 1
    have hceR : ((c 0).val : ℝ) - 1 < ((e 0).val : ℝ) + 1 :=
      (div_lt_div_iff_of_pos_right hmR).1 (hc.1.trans_lt he.2)
    have hecR : ((e 0).val : ℝ) < ((c 0).val : ℝ) + 2 :=
      (div_lt_div_iff_of_pos_right hmR).1 (he.1.trans_lt hc.2)
    have hce : (c 0).val < (e 0).val + 2 := by exact_mod_cast (by linarith :
      ((c 0).val : ℝ) < ((e 0).val : ℝ) + 2)
    have hec : (e 0).val < (c 0).val + 2 := by exact_mod_cast hecR
    omega
  · change (((c 1).val : ℝ) - 1) / (m : ℝ) ≤ x 1 ∧
      x 1 < (((c 1).val : ℝ) + 2) / (m : ℝ) at hc
    change ((e 1).val : ℝ) / (m : ℝ) ≤ x 1 ∧
      x 1 < (((e 1).val : ℝ) + 1) / (m : ℝ) at he
    change (c 1).val ≤ (e 1).val + 1 ∧ (e 1).val ≤ (c 1).val + 1
    have hceR : ((c 1).val : ℝ) - 1 < ((e 1).val : ℝ) + 1 :=
      (div_lt_div_iff_of_pos_right hmR).1 (hc.1.trans_lt he.2)
    have hecR : ((e 1).val : ℝ) < ((c 1).val : ℝ) + 2 :=
      (div_lt_div_iff_of_pos_right hmR).1 (he.1.trans_lt hc.2)
    have hce : (c 1).val < (e 1).val + 2 := by exact_mod_cast (by linarith :
      ((c 1).val : ℝ) < ((e 1).val : ℝ) + 2)
    have hec : (e 1).val < (c 1).val + 2 := by exact_mod_cast hecR
    omega

/-- The robust inner/outer families, the actual frontier cells, and the
coordinatewise one-cell halo form the concrete cover required by
`ProductGrid`. -/
noncomputable def robustBoundaryGridCover {m : ℕ} (hm : 0 < m)
    {E : Set Plane}
    (hfront : frontier E ⊆ Erdos1124.TorusTransfer.fundamentalCube) :
    Erdos1124.ProductGrid.BoundaryGridCover 2 m where
  lower := robustLowerCells m E
  upper := robustUpperCells m E
  boundary := fundamentalBoundaryCells m E
  near := cellNeighbors
  lower_subset_upper := by
    classical
    intro c hc
    rw [robustLowerCells, Finset.mem_filter] at hc
    rw [robustUpperCells, Finset.mem_filter]
    refine ⟨Finset.mem_univ c, ?_⟩
    obtain ⟨x, hx⟩ := expandedGridSquare_nonempty hm c
    exact ⟨x, hx, hc.2 hx⟩
  upper_sdiff_lower_subset := by
    classical
    intro c hc
    rw [Finset.mem_sdiff] at hc
    rw [robustUpperCells, Finset.mem_filter] at hc
    have hcLower : ¬ expandedGridSquare m c ⊆ E := by
      intro hsub
      apply hc.2
      rw [robustLowerCells, Finset.mem_filter]
      exact ⟨Finset.mem_univ c, hsub⟩
    obtain ⟨x, hxc, hxE⟩ := hc.1.2
    have hout : (expandedGridSquare m c ∩ Eᶜ).Nonempty := by
      rw [Set.not_subset] at hcLower
      obtain ⟨y, hyc, hyE⟩ := hcLower
      exact ⟨y, hyc, hyE⟩
    have hin : (expandedGridSquare m c ∩ E).Nonempty := ⟨x, hxc, hxE⟩
    obtain ⟨b, hbc, hbfront⟩ :=
      Erdos1124.Geometry.IsPreconnected.inter_frontier_nonempty
        (convex_expandedGridSquare m c).isPreconnected hin hout
    obtain ⟨e, hbe⟩ := exists_fundamentalCell hm (hfront hbfront)
    rw [Finset.mem_biUnion]
    refine ⟨e, ?_, gridSquare_expanded_implies_neighbor hm hbc hbe⟩
    rw [fundamentalBoundaryCells, Finset.mem_filter]
    exact ⟨Finset.mem_univ e, ⟨b, hbe, hbfront⟩⟩
  card_near_le := by
    intro e _
    exact card_cellNeighbors_le_nine e

lemma frontier_torusEmbed_unitDisk_subset_fundamentalCube :
    frontier (torusEmbed '' unitDisk) ⊆
      Erdos1124.TorusTransfer.fundamentalCube := by
  rw [frontier_torusEmbed_image]
  exact torusEmbed_image_subset_fundamentalCube frontier_unitDisk_contained

lemma frontier_torusEmbed_equalAreaSquare_subset_fundamentalCube :
    frontier (torusEmbed '' equalAreaSquare) ⊆
      Erdos1124.TorusTransfer.fundamentalCube := by
  rw [frontier_torusEmbed_image]
  exact torusEmbed_image_subset_fundamentalCube frontier_equalAreaSquare_contained

/-- The application-ready robust cover for the embedded disk. -/
noncomputable def torusEmbedUnitDiskCover (m : ℕ) (hm : 0 < m) :
    Erdos1124.ProductGrid.BoundaryGridCover 2 m :=
  robustBoundaryGridCover hm frontier_torusEmbed_unitDisk_subset_fundamentalCube

/-- The application-ready robust cover for the embedded equal-area square. -/
noncomputable def torusEmbedEqualAreaSquareCover (m : ℕ) (hm : 0 < m) :
    Erdos1124.ProductGrid.BoundaryGridCover 2 m :=
  robustBoundaryGridCover hm frontier_torusEmbed_equalAreaSquare_subset_fundamentalCube

@[simp] lemma torusEmbedUnitDiskCover_boundary (m : ℕ) (hm : 0 < m) :
    (torusEmbedUnitDiskCover m hm).boundary =
      fundamentalBoundaryCells m (torusEmbed '' unitDisk) := rfl

@[simp] lemma torusEmbedEqualAreaSquareCover_boundary (m : ℕ) (hm : 0 < m) :
    (torusEmbedEqualAreaSquareCover m hm).boundary =
      fundamentalBoundaryCells m (torusEmbed '' equalAreaSquare) := rfl

/-- Convert the raw coordinate model used by `ProductGrid` to the Euclidean
space carrying the disk and square. -/
def pointToPlane (y : Erdos1124.ProductGrid.Point 2) : Plane := WithLp.toLp 2 y

@[simp] lemma pointToPlane_apply (y : Erdos1124.ProductGrid.Point 2) (i : Fin 2) :
    pointToPlane y i = y i := rfl

/-- A regular product-grid point lies in its own half-open coarse cell. -/
lemma regularGridPoint_coordinate_bounds {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (p : Erdos1124.ProductGrid.FineIndex 2 m q) (i : Fin 2) :
    ((Erdos1124.ProductGrid.coarseCell p i).val : ℝ) / (m : ℝ) ≤
        Erdos1124.ProductGrid.regularGridPoint p i ∧
      Erdos1124.ProductGrid.regularGridPoint p i <
        (((Erdos1124.ProductGrid.coarseCell p i).val : ℝ) + 1) / (m : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hmqR : (0 : ℝ) < (m : ℝ) * (q : ℝ) := mul_pos hmR hqR
  simp only [Erdos1124.ProductGrid.coarseCell,
    Erdos1124.ProductGrid.regularGridPoint, finProdFinEquiv, Equiv.coe_fn_mk]
  change ((p i).1.val : ℝ) / (m : ℝ) ≤
      (((p i).2.val + q * (p i).1.val : ℕ) : ℝ) / ((m : ℝ) * (q : ℝ)) ∧
    (((p i).2.val + q * (p i).1.val : ℕ) : ℝ) / ((m : ℝ) * (q : ℝ)) <
      (((p i).1.val : ℝ) + 1) / (m : ℝ)
  have hr0 : (0 : ℝ) ≤ ((p i).2.val : ℝ) := by positivity
  have hrq : ((p i).2.val : ℝ) < (q : ℝ) := by exact_mod_cast (p i).2.isLt
  constructor
  · apply (div_le_div_iff₀ hmR hmqR).2
    push_cast
    nlinarith
  · apply (div_lt_div_iff₀ hmqR hmR).2
    push_cast
    nlinarith

/-- A coordinatewise `1/m` perturbation of a regular point stays inside the
three-by-three neighbourhood of its coarse cell. -/
lemma pointToPlane_mem_expandedGridSquare_of_close {m q : ℕ}
    (hm : 0 < m) (hq : 0 < q)
    (p : Erdos1124.ProductGrid.FineIndex 2 m q)
    (y : Erdos1124.ProductGrid.Point 2)
    (hy : ∀ i, |y i - Erdos1124.ProductGrid.regularGridPoint p i| ≤
      1 / (m : ℝ)) :
    pointToPlane y ∈ expandedGridSquare m (Erdos1124.ProductGrid.coarseCell p) := by
  intro i
  change
    (((Erdos1124.ProductGrid.coarseCell p i).val : ℝ) - 1) / (m : ℝ) ≤ y i ∧
      y i < (((Erdos1124.ProductGrid.coarseCell p i).val : ℝ) + 2) / (m : ℝ)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  obtain ⟨hrlow, hrupp⟩ := regularGridPoint_coordinate_bounds hm hq p i
  obtain ⟨hylow, hyupp⟩ := abs_le.mp (hy i)
  constructor
  · have hid :
        (((Erdos1124.ProductGrid.coarseCell p i).val : ℝ) - 1) / (m : ℝ) =
          ((Erdos1124.ProductGrid.coarseCell p i).val : ℝ) / (m : ℝ) -
            1 / (m : ℝ) := by ring
    rw [hid]
    linarith
  · have hid :
        (((Erdos1124.ProductGrid.coarseCell p i).val : ℝ) + 2) / (m : ℝ) =
          ((((Erdos1124.ProductGrid.coarseCell p i).val : ℝ) + 1) / (m : ℝ)) +
            1 / (m : ℝ) := by ring
    rw [hid]
    linarith

/-- Generic robust-lower hypothesis in exactly the form consumed by
`ProductGrid.productGridDiscrepancy_of_intervalDiscrepancy`. -/
lemma robustBoundaryGridCover_lower_stable {m q : ℕ}
    (hm : 0 < m) (hq : 0 < q) {E : Set Plane}
    (hfront : frontier E ⊆ Erdos1124.TorusTransfer.fundamentalCube)
    (p : Erdos1124.ProductGrid.FineIndex 2 m q)
    (hp : Erdos1124.ProductGrid.coarseCell p ∈
      (robustBoundaryGridCover hm hfront).lower)
    (y : Erdos1124.ProductGrid.Point 2)
    (hy : ∀ i, |y i - Erdos1124.ProductGrid.regularGridPoint p i| ≤
      1 / (m : ℝ)) :
    pointToPlane y ∈ E := by
  classical
  change Erdos1124.ProductGrid.coarseCell p ∈ robustLowerCells m E at hp
  rw [robustLowerCells, Finset.mem_filter] at hp
  exact hp.2 (pointToPlane_mem_expandedGridSquare_of_close hm hq p y hy)

/-- Generic robust-upper hypothesis in exactly the form consumed by
`ProductGrid.productGridDiscrepancy_of_intervalDiscrepancy`. -/
lemma robustBoundaryGridCover_upper_stable {m q : ℕ}
    (hm : 0 < m) (hq : 0 < q) {E : Set Plane}
    (hfront : frontier E ⊆ Erdos1124.TorusTransfer.fundamentalCube)
    (p : Erdos1124.ProductGrid.FineIndex 2 m q)
    (y : Erdos1124.ProductGrid.Point 2) (hyE : pointToPlane y ∈ E)
    (hy : ∀ i, |y i - Erdos1124.ProductGrid.regularGridPoint p i| ≤
      1 / (m : ℝ)) :
    Erdos1124.ProductGrid.coarseCell p ∈
      (robustBoundaryGridCover hm hfront).upper := by
  classical
  change Erdos1124.ProductGrid.coarseCell p ∈ robustUpperCells m E
  rw [robustUpperCells, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, pointToPlane y,
    pointToPlane_mem_expandedGridSquare_of_close hm hq p y hy, hyE⟩

/-- The union of the half-open fundamental cells in a finite cell family. -/
def fundamentalCellsUnion {m : ℕ}
    (cells : Finset (Erdos1124.ProductGrid.GridCell 2 m)) : Set Plane :=
  ⋃ c ∈ cells, gridSquare m (finGridIndex c)

lemma volume_fundamentalCellsUnion {m : ℕ} (hm : 0 < m)
    (cells : Finset (Erdos1124.ProductGrid.GridCell 2 m)) :
    volume (fundamentalCellsUnion cells) =
      (cells.card : ENNReal) * ENNReal.ofReal (1 / (m : ℝ) ^ 2) := by
  classical
  have hdisj : (↑cells : Set (Erdos1124.ProductGrid.GridCell 2 m)).PairwiseDisjoint
      fun c ↦ gridSquare m (finGridIndex c) := by
    intro c hc d hd hcd
    exact gridSquare_disjoint hm fun h ↦ hcd (finGridIndex_injective h)
  rw [fundamentalCellsUnion, measure_biUnion_finset hdisj
    (fun b _ ↦ measurableSet_gridSquare m (finGridIndex b))]
  simp only [volume_gridSquare hm]
  simp

lemma volume_fundamentalCellsUnion_toReal {m : ℕ} (hm : 0 < m)
    (cells : Finset (Erdos1124.ProductGrid.GridCell 2 m)) :
    (volume (fundamentalCellsUnion cells)).toReal =
      (cells.card : ℝ) / (m : ℝ) ^ 2 := by
  rw [volume_fundamentalCellsUnion hm, ENNReal.toReal_mul]
  have hnonneg : (0 : ℝ) ≤ 1 / (m : ℝ) ^ 2 := by positivity
  rw [ENNReal.toReal_ofReal hnonneg]
  have hcard : ((cells.card : ENNReal).toReal) = (cells.card : ℝ) := by norm_num
  rw [hcard]
  ring

lemma fundamentalCellsUnion_robustLowerCells_subset {m : ℕ} (hm : 0 < m)
    (E : Set Plane) :
    fundamentalCellsUnion (robustLowerCells m E) ⊆ E := by
  classical
  intro x hx
  rw [fundamentalCellsUnion, Set.mem_iUnion] at hx
  obtain ⟨c, hx⟩ := hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨hc, hxc⟩ := hx
  rw [robustLowerCells, Finset.mem_filter] at hc
  exact hc.2 (gridSquare_subset_expandedGridSquare hm c hxc)

lemma subset_fundamentalCellsUnion_robustUpperCells {m : ℕ} (hm : 0 < m)
    {E : Set Plane} (hE : E ⊆ Erdos1124.TorusTransfer.fundamentalCube) :
    E ⊆ fundamentalCellsUnion (robustUpperCells m E) := by
  classical
  intro x hxE
  obtain ⟨c, hxc⟩ := exists_fundamentalCell hm (hE hxE)
  rw [fundamentalCellsUnion, Set.mem_iUnion]
  refine ⟨c, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨?_, hxc⟩
  rw [robustUpperCells, Finset.mem_filter]
  exact ⟨Finset.mem_univ c, x, gridSquare_subset_expandedGridSquare hm c hxc, hxE⟩

/-- Lower-cell volume bracket, stated over reals for direct use by
`ProductGrid`. -/
lemma robustLowerCells_card_div_le_volume_toReal {m : ℕ} (hm : 0 < m)
    {E : Set Plane} (hEtop : volume E ≠ ⊤) :
    ((robustLowerCells m E).card : ℝ) / (m : ℝ) ^ 2 ≤ (volume E).toReal := by
  rw [← volume_fundamentalCellsUnion_toReal hm]
  exact ENNReal.toReal_mono hEtop
    (measure_mono (fundamentalCellsUnion_robustLowerCells_subset hm E))

/-- Upper-cell volume bracket, stated over reals for direct use by
`ProductGrid`. -/
lemma volume_toReal_le_robustUpperCells_card_div {m : ℕ} (hm : 0 < m)
    {E : Set Plane} (hE : E ⊆ Erdos1124.TorusTransfer.fundamentalCube) :
    (volume E).toReal ≤ ((robustUpperCells m E).card : ℝ) / (m : ℝ) ^ 2 := by
  rw [← volume_fundamentalCellsUnion_toReal hm]
  apply ENNReal.toReal_mono
  · rw [volume_fundamentalCellsUnion hm]
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  · exact measure_mono (subset_fundamentalCellsUnion_robustUpperCells hm hE)

lemma volume_torusEmbed_unitDisk_toReal :
    (volume (torusEmbed '' unitDisk)).toReal = Real.pi / 16 := by
  rw [volume_torusEmbed_unitDisk, ENNReal.toReal_ofReal (by positivity)]
  ring

lemma volume_torusEmbed_equalAreaSquare_toReal :
    (volume (torusEmbed '' equalAreaSquare)).toReal = Real.pi / 16 := by
  rw [volume_torusEmbed_equalAreaSquare, ENNReal.toReal_ofReal (by positivity)]
  ring

/-- The embedded disk cover's lower cell mass is at most its exact area. -/
theorem torusEmbedUnitDiskCover_lower_mass_le (m : ℕ) (hm : 0 < m) :
    (((torusEmbedUnitDiskCover m hm).lower.card : ℝ) / (m : ℝ) ^ 2) ≤
      Real.pi / 16 := by
  change ((robustLowerCells m (torusEmbed '' unitDisk)).card : ℝ) /
      (m : ℝ) ^ 2 ≤ Real.pi / 16
  rw [← volume_torusEmbed_unitDisk_toReal]
  apply robustLowerCells_card_div_le_volume_toReal hm
  rw [volume_torusEmbed_unitDisk]
  exact ENNReal.ofReal_ne_top

/-- The embedded disk cover's upper cell mass is at least its exact area. -/
theorem torusEmbedUnitDiskCover_mass_le_upper (m : ℕ) (hm : 0 < m) :
    Real.pi / 16 ≤
      ((torusEmbedUnitDiskCover m hm).upper.card : ℝ) / (m : ℝ) ^ 2 := by
  change Real.pi / 16 ≤
    ((robustUpperCells m (torusEmbed '' unitDisk)).card : ℝ) / (m : ℝ) ^ 2
  rw [← volume_torusEmbed_unitDisk_toReal]
  exact volume_toReal_le_robustUpperCells_card_div hm
    torusEmbed_unitDisk_subset_fundamentalCube

/-- The embedded square cover's lower cell mass is at most its exact area. -/
theorem torusEmbedEqualAreaSquareCover_lower_mass_le (m : ℕ) (hm : 0 < m) :
    (((torusEmbedEqualAreaSquareCover m hm).lower.card : ℝ) / (m : ℝ) ^ 2) ≤
      Real.pi / 16 := by
  change ((robustLowerCells m (torusEmbed '' equalAreaSquare)).card : ℝ) /
      (m : ℝ) ^ 2 ≤ Real.pi / 16
  rw [← volume_torusEmbed_equalAreaSquare_toReal]
  apply robustLowerCells_card_div_le_volume_toReal hm
  rw [volume_torusEmbed_equalAreaSquare]
  exact ENNReal.ofReal_ne_top

/-- The embedded square cover's upper cell mass is at least its exact area. -/
theorem torusEmbedEqualAreaSquareCover_mass_le_upper (m : ℕ) (hm : 0 < m) :
    Real.pi / 16 ≤
      ((torusEmbedEqualAreaSquareCover m hm).upper.card : ℝ) / (m : ℝ) ^ 2 := by
  change Real.pi / 16 ≤
    ((robustUpperCells m (torusEmbed '' equalAreaSquare)).card : ℝ) / (m : ℝ) ^ 2
  rw [← volume_torusEmbed_equalAreaSquare_toReal]
  exact volume_toReal_le_robustUpperCells_card_div hm
    torusEmbed_equalAreaSquare_subset_fundamentalCube

lemma five_mul_le_rpow_three_halves {m : ℕ} (hm : 25 ≤ m) :
    ((5 * m : ℕ) : ℝ) ≤ (m : ℝ) ^ ((2 : ℝ) - 1 / 2) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by positivity
  have hsqrt : (5 : ℝ) ≤ Real.sqrt (m : ℝ) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    exact_mod_cast hm
  have hrpow : (m : ℝ) ^ ((2 : ℝ) - 1 / 2) =
      (m : ℝ) * Real.sqrt (m : ℝ) := by
    calc
      (m : ℝ) ^ ((2 : ℝ) - 1 / 2) = (m : ℝ) ^ ((1 : ℝ) + 1 / 2) := by norm_num
      _ = (m : ℝ) ^ (1 : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_add hmpos _ _
      _ = (m : ℝ) * Real.sqrt (m : ℝ) := by
        rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hrpow]
  push_cast
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hsqrt hmpos.le

/-- The stronger exponent used by the final quantitative specialization:
`5m ≤ m^(5/4)` once `m ≥ 5^4`. -/
lemma five_mul_le_rpow_five_fourths {m : ℕ} (hm : 625 ≤ m) :
    ((5 * m : ℕ) : ℝ) ≤ (m : ℝ) ^ ((2 : ℝ) - 3 / 4) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by positivity
  have hbase : (625 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h625 : (625 : ℝ) ^ (1 / 4 : ℝ) = 5 := by
    convert Real.pow_rpow_inv_natCast (x := (5 : ℝ)) (n := 4)
      (by positivity) (by norm_num) using 1 <;> norm_num
  have hroot : (5 : ℝ) ≤ (m : ℝ) ^ (1 / 4 : ℝ) := by
    rw [← h625]
    exact Real.rpow_le_rpow (by norm_num) hbase (by norm_num)
  have hrpow : (m : ℝ) ^ ((2 : ℝ) - 3 / 4) =
      (m : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      (m : ℝ) ^ ((2 : ℝ) - 3 / 4) =
          (m : ℝ) ^ ((1 : ℝ) + 1 / 4) := by norm_num
      _ = (m : ℝ) ^ (1 : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ) :=
        Real.rpow_add hmpos _ _
      _ = (m : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ) := by rw [Real.rpow_one]
  rw [hrpow]
  push_cast
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hroot hmpos.le

/-- The exact `k = 2`, `ε = 1/2` boundary exponent needed by the product-grid
discrepancy lemma, at meshes divisible by four. -/
theorem card_fundamentalBoundaryCells_torusEmbed_unitDisk_le_rpow
    {n : ℕ} (hn : 0 < n) (hmesh : 25 ≤ 4 * n) :
    ((fundamentalBoundaryCells (4 * n) (torusEmbed '' unitDisk)).card : ℝ) ≤
      ((4 * n : ℕ) : ℝ) ^ ((2 : ℝ) - 1 / 2) := by
  have hcard := card_fundamentalBoundaryCells_torusEmbed_unitDisk_le hn
  have hcard' :
      ((fundamentalBoundaryCells (4 * n) (torusEmbed '' unitDisk)).card : ℝ) ≤
        ((5 * (4 * n) : ℕ) : ℝ) := by
    exact_mod_cast (hcard.trans (by omega : 20 * n ≤ 5 * (4 * n)))
  exact hcard'.trans (five_mul_le_rpow_three_halves hmesh)

theorem card_fundamentalBoundaryCells_torusEmbed_equalAreaSquare_le_rpow
    {n : ℕ} (hn : 0 < n) (hmesh : 25 ≤ 4 * n) :
    ((fundamentalBoundaryCells (4 * n) (torusEmbed '' equalAreaSquare)).card : ℝ) ≤
      ((4 * n : ℕ) : ℝ) ^ ((2 : ℝ) - 1 / 2) := by
  have hcard := card_fundamentalBoundaryCells_torusEmbed_equalAreaSquare_le hn
  have hcard' :
      ((fundamentalBoundaryCells (4 * n) (torusEmbed '' equalAreaSquare)).card : ℝ) ≤
        ((5 * (4 * n) : ℕ) : ℝ) := by
    exact_mod_cast (hcard.trans (by omega : 12 * n ≤ 5 * (4 * n)))
  exact hcard'.trans (five_mul_le_rpow_three_halves hmesh)

theorem card_fundamentalBoundaryCells_torusEmbed_unitDisk_le_rpow_three_fourths
    {n : ℕ} (hn : 0 < n) (hmesh : 625 ≤ 4 * n) :
    ((fundamentalBoundaryCells (4 * n) (torusEmbed '' unitDisk)).card : ℝ) ≤
      ((4 * n : ℕ) : ℝ) ^ ((2 : ℝ) - 3 / 4) := by
  have hcard := card_fundamentalBoundaryCells_torusEmbed_unitDisk_le hn
  have hcard' :
      ((fundamentalBoundaryCells (4 * n) (torusEmbed '' unitDisk)).card : ℝ) ≤
        ((5 * (4 * n) : ℕ) : ℝ) := by
    exact_mod_cast (hcard.trans (by omega : 20 * n ≤ 5 * (4 * n)))
  exact hcard'.trans (five_mul_le_rpow_five_fourths hmesh)

theorem card_fundamentalBoundaryCells_torusEmbed_equalAreaSquare_le_rpow_three_fourths
    {n : ℕ} (hn : 0 < n) (hmesh : 625 ≤ 4 * n) :
    ((fundamentalBoundaryCells (4 * n) (torusEmbed '' equalAreaSquare)).card : ℝ) ≤
      ((4 * n : ℕ) : ℝ) ^ ((2 : ℝ) - 3 / 4) := by
  have hcard := card_fundamentalBoundaryCells_torusEmbed_equalAreaSquare_le hn
  have hcard' :
      ((fundamentalBoundaryCells (4 * n) (torusEmbed '' equalAreaSquare)).card : ℝ) ≤
        ((5 * (4 * n) : ℕ) : ℝ) := by
    exact_mod_cast (hcard.trans (by omega : 12 * n ≤ 5 * (4 * n)))
  exact hcard'.trans (five_mul_le_rpow_five_fourths hmesh)

/-- Connect the concrete disk boundary finset to an otherwise constructed
`ProductGrid.BoundaryGridCover`. -/
theorem disk_hasBoundaryGridCount_of_boundary_eq {n : ℕ} (hn : 0 < n)
    (hmesh : 25 ≤ 4 * n)
    (C : Erdos1124.ProductGrid.BoundaryGridCover 2 (4 * n))
    (hboundary : C.boundary =
      fundamentalBoundaryCells (4 * n) (torusEmbed '' unitDisk)) :
    Erdos1124.ProductGrid.HasBoundaryGridCount C (1 / 2 : ℝ) := by
  unfold Erdos1124.ProductGrid.HasBoundaryGridCount
  rw [hboundary]
  exact card_fundamentalBoundaryCells_torusEmbed_unitDisk_le_rpow hn hmesh

/-- Connect the concrete square boundary finset to an otherwise constructed
`ProductGrid.BoundaryGridCover`. -/
theorem square_hasBoundaryGridCount_of_boundary_eq {n : ℕ} (hn : 0 < n)
    (hmesh : 25 ≤ 4 * n)
    (C : Erdos1124.ProductGrid.BoundaryGridCover 2 (4 * n))
    (hboundary : C.boundary =
      fundamentalBoundaryCells (4 * n) (torusEmbed '' equalAreaSquare)) :
    Erdos1124.ProductGrid.HasBoundaryGridCount C (1 / 2 : ℝ) := by
  unfold Erdos1124.ProductGrid.HasBoundaryGridCount
  rw [hboundary]
  exact card_fundamentalBoundaryCells_torusEmbed_equalAreaSquare_le_rpow hn hmesh

/-- Application-ready `ε = 3/4` boundary count for the embedded disk cover. -/
theorem torusEmbedUnitDiskCover_hasBoundaryGridCount_three_fourths
    {n : ℕ} (hn : 0 < n) (hmesh : 625 ≤ 4 * n) :
    Erdos1124.ProductGrid.HasBoundaryGridCount
      (torusEmbedUnitDiskCover (4 * n) (Nat.mul_pos (by norm_num) hn))
      (3 / 4 : ℝ) := by
  unfold Erdos1124.ProductGrid.HasBoundaryGridCount
  rw [torusEmbedUnitDiskCover_boundary]
  exact card_fundamentalBoundaryCells_torusEmbed_unitDisk_le_rpow_three_fourths
    hn hmesh

/-- Application-ready `ε = 3/4` boundary count for the embedded square cover. -/
theorem torusEmbedEqualAreaSquareCover_hasBoundaryGridCount_three_fourths
    {n : ℕ} (hn : 0 < n) (hmesh : 625 ≤ 4 * n) :
    Erdos1124.ProductGrid.HasBoundaryGridCount
      (torusEmbedEqualAreaSquareCover (4 * n) (Nat.mul_pos (by norm_num) hn))
      (3 / 4 : ℝ) := by
  unfold Erdos1124.ProductGrid.HasBoundaryGridCount
  rw [torusEmbedEqualAreaSquareCover_boundary]
  exact card_fundamentalBoundaryCells_torusEmbed_equalAreaSquare_le_rpow_three_fourths
    hn hmesh

end

end Erdos1124.Geometry
