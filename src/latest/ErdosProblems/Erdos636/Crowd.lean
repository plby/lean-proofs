/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-!
# A finite particle-follows-the-crowd lemma

This file isolates the exact finite counting argument used in the switching
part of Kwan--Sudakov's proof of Erdős Problem 636.

The informal version partitions the interval of possible particle positions
into short cells and inspects a sparse collection of times.  Three rounding
points matter in a literal finite statement: the number of cells is a
ceiling, time zero is one of the inspection times, and the final union bound
must be strict.  The theorem below therefore uses the exact quantities which
the argument counts: a finite set of inspection times, a finite type of
cells, and the strict inequality

`#inspectionTimes * #cells * μ < #particles`.

The geometric part of an application is the hypothesis `cellFiber_subset`:
all particles in the same short cell at the inspection time remain within
the prescribed neighbourhood at the later time.  A step-size estimate and
the usual choice of inspection stride prove precisely this hypothesis.  This
separation makes the combinatorial lemma independent of any particular
rounding convention for real interval lengths.
-/

open scoped BigOperators

namespace Erdos636.Crowd

variable {R : Type*} [Fintype R]

/-- The particles which have cell label `c` at time `t`. -/
def cellFiber {C : ℕ} (cell : ℕ → R → Fin C) (t : ℕ) (c : Fin C) : Finset R :=
  Finset.univ.filter fun a ↦ cell t a = c

/-- The particles lying in cells of cardinality strictly less than `μ`. -/
def sparseParticles {C : ℕ} (cell : ℕ → R → Fin C) (μ t : ℕ) : Finset R :=
  Finset.univ.filter fun a ↦ (cellFiber cell t (cell t a)).card < μ

/-- Retain a fibre only when it is sparse. -/
private def smallFiber {C : ℕ} (cell : ℕ → R → Fin C) (μ t : ℕ)
    (c : Fin C) : Finset R :=
  if (cellFiber cell t c).card < μ then cellFiber cell t c else ∅

/-- At a fixed inspection time at most `C * μ` particles lie in sparse
cells.  The slightly sharper `C * (μ - 1)` is unnecessary for the outer
argument, while this form also handles `μ = 0` without a case split. -/
lemma card_sparseParticles_le {C : ℕ} (cell : ℕ → R → Fin C) (μ t : ℕ) :
    (sparseParticles cell μ t).card ≤ C * μ := by
  classical
  have hsubset : sparseParticles cell μ t ⊆
      Finset.univ.biUnion (smallFiber cell μ t) := by
    intro a ha
    rw [sparseParticles, Finset.mem_filter] at ha
    rw [Finset.mem_biUnion]
    refine ⟨cell t a, Finset.mem_univ _, ?_⟩
    rw [smallFiber, if_pos ha.2, cellFiber, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  calc
    (sparseParticles cell μ t).card ≤
        (Finset.univ.biUnion (smallFiber cell μ t)).card :=
      Finset.card_le_card hsubset
    _ ≤ (Finset.univ.card : ℕ) * μ := by
      apply Finset.card_biUnion_le_card_mul
      intro c hc
      rw [smallFiber]
      split_ifs with h
      · exact Nat.le_of_lt h
      · simp
    _ = C * μ := by simp

/-- A particle is lonely when its prescribed neighbourhood has fewer than
`μ` particles.  Applications normally include the particle itself in
`nearby t a`. -/
def IsLonely (nearby : ℕ → R → Finset R) (μ t : ℕ) (a : R) : Prop :=
  (nearby t a).card < μ

/-- Particles which are lonely at least once up to and including `last`. -/
noncomputable def everLonely (nearby : ℕ → R → Finset R) (μ last : ℕ) : Finset R := by
  classical
  exact Finset.univ.filter fun a ↦ ∃ t ≤ last, IsLonely nearby μ t a

/-- Metric neighbourhoods for the usual moving-particle application. -/
noncomputable def metricNearby {X : Type*} [PseudoMetricSpace X]
    (position : ℕ → R → X) (σ : ℝ) (t : ℕ) (a : R) : Finset R :=
  Finset.univ.filter fun b ↦ dist (position t a) (position t b) ≤ σ

/-- The exact finite particle-follows-the-crowd lemma.

For every time `t ≤ last`, `sample t` is an inspection time.  The geometric
hypothesis says that the whole cell fibre of a particle at `sample t` lies
inside its neighbourhood at time `t`.  Hence a particle lonely at `t` was in
a sparse cell at `sample t`.  A union bound over inspection times and cells
then leaves a particle which is never lonely. -/
theorem exists_never_lonely
    {C : ℕ} (nearby : ℕ → R → Finset R) (cell : ℕ → R → Fin C)
    (μ last : ℕ) (inspectionTimes : Finset ℕ) (sample : ℕ → ℕ)
    (sample_mem : ∀ t ≤ last, sample t ∈ inspectionTimes)
    (cellFiber_subset : ∀ t ≤ last, ∀ a,
      cellFiber cell (sample t) (cell (sample t) a) ⊆ nearby t a)
    (hcount : inspectionTimes.card * C * μ < Fintype.card R) :
    ∃ a : R, ∀ t ≤ last, μ ≤ (nearby t a).card := by
  classical
  have lonely_imp_sparse : ∀ t ≤ last, ∀ a,
      IsLonely nearby μ t a → a ∈ sparseParticles cell μ (sample t) := by
    intro t ht a hla
    rw [sparseParticles, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hnot
    have hmu : μ ≤ (cellFiber cell (sample t) (cell (sample t) a)).card :=
      Nat.le_of_not_gt hnot
    have hsub := Finset.card_le_card (cellFiber_subset t ht a)
    exact (not_lt_of_ge (hmu.trans hsub)) hla
  have hever_subset : everLonely nearby μ last ⊆
      inspectionTimes.biUnion (sparseParticles cell μ) := by
    intro a ha
    rw [everLonely, Finset.mem_filter] at ha
    rcases ha.2 with ⟨t, ht, hla⟩
    rw [Finset.mem_biUnion]
    exact ⟨sample t, sample_mem t ht, lonely_imp_sparse t ht a hla⟩
  have hever_card : (everLonely nearby μ last).card ≤ inspectionTimes.card * C * μ := by
    calc
      (everLonely nearby μ last).card ≤
          (inspectionTimes.biUnion (sparseParticles cell μ)).card :=
        Finset.card_le_card hever_subset
      _ ≤ ∑ t ∈ inspectionTimes, (sparseParticles cell μ t).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _t ∈ inspectionTimes, C * μ :=
        Finset.sum_le_sum fun t _ ↦ card_sparseParticles_le cell μ t
      _ = inspectionTimes.card * C * μ := by simp [mul_assoc]
  have hlt : (everLonely nearby μ last).card < (Finset.univ : Finset R).card := by
    simpa using lt_of_le_of_lt hever_card hcount
  rcases Finset.exists_mem_notMem_of_card_lt_card hlt with ⟨a, _ha, hnever⟩
  refine ⟨a, fun t ht ↦ ?_⟩
  by_contra hnot
  have hla : IsLonely nearby μ t a := Nat.lt_of_not_ge hnot
  exact hnever (by
    rw [everLonely, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨t, ht, hla⟩⟩)

/-- Geometric adapter for `exists_never_lonely`.

At the inspection assigned to `t`, two particles in the same cell are at
distance at most `cellRadius`.  Each of them travels at most
`travelRadius` before time `t`.  Consequently the whole cell fibre remains
in the radius-`σ` neighbourhood whenever
`cellRadius + 2 * travelRadius ≤ σ`. -/
theorem exists_never_lonely_of_metric_cells
    {X : Type*} [PseudoMetricSpace X] {C : ℕ}
    (position : ℕ → R → X) (cell : ℕ → R → Fin C)
    (μ last : ℕ) (σ cellRadius travelRadius : ℝ)
    (inspectionTimes : Finset ℕ) (sample inspectionTime : ℕ → ℕ)
    (sample_mem : ∀ t ≤ last, sample t ∈ inspectionTimes)
    (sameCell_close : ∀ t ≤ last, ∀ a b,
      cell (sample t) b = cell (sample t) a →
        dist (position (inspectionTime (sample t)) a)
          (position (inspectionTime (sample t)) b) ≤ cellRadius)
    (travel_le : ∀ t ≤ last, ∀ a,
      dist (position t a) (position (inspectionTime (sample t)) a) ≤ travelRadius)
    (hradius : cellRadius + 2 * travelRadius ≤ σ)
    (hcount : inspectionTimes.card * C * μ < Fintype.card R) :
    ∃ a : R, ∀ t ≤ last, μ ≤ (metricNearby position σ t a).card := by
  apply exists_never_lonely (metricNearby position σ) cell μ last inspectionTimes sample
    sample_mem
  · intro t ht a b hb
    rw [cellFiber, Finset.mem_filter] at hb
    rw [metricNearby, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have haTravel := travel_le t ht a
    have hbTravel := travel_le t ht b
    have habCell := sameCell_close t ht a b hb.2
    calc
      dist (position t a) (position t b) ≤
          dist (position t a) (position (inspectionTime (sample t)) a) +
            dist (position (inspectionTime (sample t)) a) (position t b) :=
        dist_triangle _ _ _
      _ ≤ dist (position t a) (position (inspectionTime (sample t)) a) +
          (dist (position (inspectionTime (sample t)) a)
              (position (inspectionTime (sample t)) b) +
            dist (position (inspectionTime (sample t)) b) (position t b)) := by
        gcongr
        exact dist_triangle _ _ _
      _ ≤ travelRadius + (cellRadius + travelRadius) := by
        gcongr
        simpa only [dist_comm] using hbTravel
      _ = cellRadius + 2 * travelRadius := by ring
      _ ≤ σ := hradius
  · exact hcount

/-- Exact specialization to inspections at a fixed stride.  The cell label
`j` represents the inspection at actual time `j * stride`, and a time `t`
is assigned to `t / stride`.  Thus there are exactly
`last / stride + 1` possible inspection labels, including time zero.

For the geometric application one takes a positive stride and proves
`cellFiber_subset` from the step-size bound.  Keeping this implication as a
hypothesis avoids imposing a particular metric or interval-rounding
convention on the finite counting lemma. -/
theorem exists_never_lonely_stride
    {C : ℕ} (nearby : ℕ → R → Finset R) (cell : ℕ → R → Fin C)
    (μ last stride : ℕ)
    (cellFiber_subset : ∀ t ≤ last, ∀ a,
      cellFiber cell (t / stride) (cell (t / stride) a) ⊆ nearby t a)
    (hcount : (last / stride + 1) * C * μ < Fintype.card R) :
    ∃ a : R, ∀ t ≤ last, μ ≤ (nearby t a).card := by
  apply exists_never_lonely nearby cell μ last (Finset.range (last / stride + 1))
    (fun t ↦ t / stride)
  · intro t ht
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right ht)
  · exact cellFiber_subset
  · simpa using hcount

/-! ## Blockwise form -/

/-- The data required to apply `exists_never_lonely` independently on each
time block.  Times inside a block use local coordinates `0, ..., last b`;
this is the form in which switching paths are normally cut into blocks. -/
structure BlockCrowdData (B : Type*) [Fintype B]
    (R : Type*) [Fintype R] where
  cellCount : B → ℕ
  nearby : B → ℕ → R → Finset R
  cell : (b : B) → ℕ → R → Fin (cellCount b)
  threshold : B → ℕ
  last : B → ℕ
  inspectionTimes : B → Finset ℕ
  sample : B → ℕ → ℕ
  sample_mem : ∀ b t, t ≤ last b → sample b t ∈ inspectionTimes b
  cellFiber_subset : ∀ b t, t ≤ last b → ∀ a,
    cellFiber (cell b) (sample b t) (cell b (sample b t) a) ⊆ nearby b t a
  count_lt : ∀ b,
    (inspectionTimes b).card * cellCount b * threshold b < Fintype.card R

/-! ## A concrete fixed-width bucket constructor -/

/-- Number of buckets used for an integer interval of span `span`.  The
extra bucket makes the definition total, including at values outside the
controlled interval; relevant values are proved to lie below it. -/
def natBucketCount (span width : ℕ) : ℕ := span / width + 1

/-- Bucket a natural-valued statistic after subtracting a time-dependent
lower endpoint.  Reduction modulo the positive bucket count makes this a
total function.  On the controlled interval the modulo is inactive. -/
def natBucket (span width base value : ℕ) : Fin (natBucketCount span width) :=
  ⟨((value - base) / width) % natBucketCount span width,
    Nat.mod_lt _ (by simp [natBucketCount])⟩

/-- Two controlled values in the same width-`width` bucket differ by at
most `width`. -/
lemma natDist_le_width_of_natBucket_eq
    {span width base x y : ℕ} (hwidth : 0 < width)
    (hbx : base ≤ x) (hby : base ≤ y)
    (hxs : x < base + span) (hys : y < base + span)
    (hcell : natBucket span width base x = natBucket span width base y) :
    Nat.dist x y ≤ width := by
  have hxs' : x - base < span := by omega
  have hys' : y - base < span := by omega
  have hxq : (x - base) / width < natBucketCount span width := by
    rw [natBucketCount]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt hxs'))
  have hyq : (y - base) / width < natBucketCount span width := by
    rw [natBucketCount]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt hys'))
  have hq : (x - base) / width = (y - base) / width := by
    have hval := Fin.ext_iff.mp hcell
    simpa [natBucket, Nat.mod_eq_of_lt hxq, Nat.mod_eq_of_lt hyq] using hval
  have hxmod : (x - base) % width < width := Nat.mod_lt _ hwidth
  have hymod : (y - base) % width < width := Nat.mod_lt _ hwidth
  have hxdiv := Nat.div_add_mod (x - base) width
  have hydiv := Nat.div_add_mod (y - base) width
  rw [← hq] at hydiv
  unfold Nat.dist
  omega

/-- Radius-`window` neighbourhoods for a natural-valued trajectory. -/
def natTrajectoryNearby {B : Type*}
    (globalTime : B → ℕ → ℕ) (value : ℕ → R → ℕ)
    (window : ℕ) (b : B) (t : ℕ) (a : R) : Finset R :=
  Finset.univ.filter fun y ↦
    Nat.dist (value (globalTime b t) y) (value (globalTime b t) a) ≤ window

/-- Construct the exact blockwise crowd data from a bounded integer
trajectory.

At inspection `j` all values must lie in the half-open interval
`[base b j, base b j + span)`.  A local time `t` uses inspection
`j = t / stride`, whose actual local time is `j * stride`.  Each particle
moves by at most `travel` between those two times.  Therefore a bucket of
width `width` stays inside a degree window of radius
`width + 2 * travel`.

The strict displayed counting premise is the exact finite correction to
the asymptotic crowd inequality: it includes the initial inspection and the
integer bucket count. -/
noncomputable def blockCrowdDataOfNatTrajectory
    {B : Type*} [Fintype B]
    (last : B → ℕ) (globalTime : B → ℕ → ℕ)
    (value : ℕ → R → ℕ) (base : B → ℕ → ℕ)
    (span width threshold window stride travel : ℕ)
    (hwidth : 0 < width) (_hstride : 0 < stride)
    (hcontrolled : ∀ b j, j * stride ≤ last b → ∀ x,
      base b j ≤ value (globalTime b (j * stride)) x ∧
        value (globalTime b (j * stride)) x < base b j + span)
    (htravel : ∀ b t, t ≤ last b → ∀ x,
      Nat.dist (value (globalTime b t) x)
        (value (globalTime b ((t / stride) * stride)) x) ≤ travel)
    (hradius : width + 2 * travel ≤ window)
    (hcount : ∀ b,
      (last b / stride + 1) * natBucketCount span width * threshold <
        Fintype.card R) :
    BlockCrowdData B R where
  cellCount := fun _ ↦ natBucketCount span width
  nearby := natTrajectoryNearby globalTime value window
  cell := fun b j x ↦
    natBucket span width (base b j) (value (globalTime b (j * stride)) x)
  threshold := fun _ ↦ threshold
  last := last
  inspectionTimes := fun b ↦ Finset.range (last b / stride + 1)
  sample := fun _ t ↦ t / stride
  sample_mem := by
    intro b t ht
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right ht)
  cellFiber_subset := by
    intro b t ht a y hy
    rw [cellFiber, Finset.mem_filter] at hy
    rw [natTrajectoryNearby, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hsample : (t / stride) * stride ≤ last b :=
      (Nat.div_mul_le_self t stride).trans ht
    have haControl := hcontrolled b (t / stride) hsample a
    have hyControl := hcontrolled b (t / stride) hsample y
    have hsame : Nat.dist
        (value (globalTime b ((t / stride) * stride)) y)
        (value (globalTime b ((t / stride) * stride)) a) ≤ width :=
      natDist_le_width_of_natBucket_eq hwidth hyControl.1 haControl.1
        hyControl.2 haControl.2 hy.2
    have haTravel := htravel b t ht a
    have hyTravel := htravel b t ht y
    calc
      Nat.dist (value (globalTime b t) y) (value (globalTime b t) a) ≤
          Nat.dist (value (globalTime b t) y)
              (value (globalTime b ((t / stride) * stride)) y) +
            Nat.dist (value (globalTime b ((t / stride) * stride)) y)
              (value (globalTime b t) a) :=
        Nat.dist.triangle_inequality _ _ _
      _ ≤ Nat.dist (value (globalTime b t) y)
              (value (globalTime b ((t / stride) * stride)) y) +
          (Nat.dist (value (globalTime b ((t / stride) * stride)) y)
              (value (globalTime b ((t / stride) * stride)) a) +
            Nat.dist (value (globalTime b ((t / stride) * stride)) a)
              (value (globalTime b t) a)) := by
        gcongr
        exact Nat.dist.triangle_inequality _ _ _
      _ ≤ travel + (width + travel) := by
        gcongr
        simpa only [Nat.dist_comm] using haTravel
      _ ≤ window := by omega
  count_lt := by
    intro b
    simpa using hcount b

/-- Choose, simultaneously for every block, an anchor which is never lonely
throughout that block.  In particular, every local time has a crowd of at
least `threshold b` particles around the chosen anchor. -/
theorem exists_block_anchors
    {B : Type*} [Fintype B]
    (D : BlockCrowdData B R) :
    ∃ anchor : B → R, ∀ b t, t ≤ D.last b →
      D.threshold b ≤ (D.nearby b t (anchor b)).card := by
  have hanchor : ∀ b : B, ∃ a : R, ∀ t ≤ D.last b,
      D.threshold b ≤ (D.nearby b t a).card := by
    intro b
    exact exists_never_lonely (D.nearby b) (D.cell b) (D.threshold b)
      (D.last b) (D.inspectionTimes b) (D.sample b) (D.sample_mem b)
      (D.cellFiber_subset b) (D.count_lt b)
  choose anchor hanchor_spec using hanchor
  exact ⟨anchor, hanchor_spec⟩

/-- Extract explicit crowd finsets from the block anchors.  This is the
shape needed when a switching argument retains a submatching at each time. -/
theorem exists_block_anchors_and_crowds
    {B : Type*} [Fintype B]
    (D : BlockCrowdData B R) :
    ∃ anchor : B → R, ∃ crowd : B → ℕ → Finset R,
      (∀ b t, crowd b t = D.nearby b t (anchor b)) ∧
      ∀ b t, t ≤ D.last b → D.threshold b ≤ (crowd b t).card := by
  rcases exists_block_anchors D with ⟨anchor, hanchor⟩
  refine ⟨anchor, fun b t ↦ D.nearby b t (anchor b), ?_, ?_⟩
  · exact fun _ _ ↦ rfl
  · exact hanchor

end Erdos636.Crowd
