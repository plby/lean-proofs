/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos989.Core
import ErdosProblems.Erdos989.GlobalSelection

/-!
# The periodic consequence of the sharp fixed-radius plane estimate

This module makes precise the scaling obstruction for the literal uniform
square-root lower bound in `Erdos989.Core`.  A finite point pattern in the
half-open unit square is extended periodically, then dilated by the square
root of the number of points.  The dilated set is admissible and has density
one.  Consequently, the universal planar lower bound would give the sharp
`N^(1/4)` discrepancy estimate for one prescribed radius of every periodic
pattern.

No discrepancy lower bound is assumed or proved here.  The final theorem is
an implication whose hypothesis is exactly `HasUniversalSqrtLowerBound`.
-/

namespace Erdos989
namespace PeriodicReduction

open Set
open GlobalSelection

noncomputable section

/-- Read the two coordinates of a point as an ordinary pair. -/
def planeToPair (x : Plane) : ℝ × ℝ := (x 0, x 1)

@[simp] theorem pairToEuclideanPlane_planeToPair (x : Plane) :
    pairToEuclideanPlane (planeToPair x) = x := by
  ext i
  fin_cases i <;> rfl

/-- Periodically extend a finite pattern in the unit square by the integer
lattice. -/
def periodicLift (P : Finset Plane) : Set Plane :=
  Set.range fun a : PlaneCell × {x // x ∈ P} ↦
    latticeLocation (fun x : {x // x ∈ P} ↦ planeToPair x.1) a.1 a.2

/-- The hypothesis that the representatives lie in the half-open unit
square. -/
def InHalfOpenUnitSquare (P : Finset Plane) : Prop :=
  ∀ x ∈ P, 0 ≤ x 0 ∧ x 0 < 1 ∧ 0 ≤ x 1 ∧ x 1 < 1

theorem periodicLift_index_injective {P : Finset Plane}
    (hP : InHalfOpenUnitSquare P) :
    Function.Injective (fun a : PlaneCell × {x // x ∈ P} ↦
      latticeLocation (fun x : {x // x ∈ P} ↦ planeToPair x.1) a.1 a.2) := by
  intro a b hab
  have hoffset : OffsetsInHalfOpenUnitSquare
      (fun x : {x // x ∈ P} ↦ planeToPair x.1) := by
    intro x
    exact hP x.1 x.2
  have hcell : a.1 = b.1 := latticeLocation_cell_separated hoffset hab
  have hx0 := congrArg (fun z : Plane ↦ z 0) hab
  have hx1 := congrArg (fun z : Plane ↦ z 1) hab
  have hpoint : a.2.1 = b.2.1 := by
    ext i
    fin_cases i
    · simpa [hcell, planeToPair] using hx0
    · simpa [hcell, planeToPair] using hx1
  apply Prod.ext hcell
  exact Subtype.ext hpoint

theorem periodicLift_infinite {P : Finset Plane} (hP0 : P.Nonempty)
    (hP : InHalfOpenUnitSquare P) : (periodicLift P).Infinite := by
  obtain ⟨p, hp⟩ := hP0
  let f : PlaneCell → Plane := fun cell ↦
    latticeLocation (fun x : {x // x ∈ P} ↦ planeToPair x.1) cell ⟨p, hp⟩
  have hf : Function.Injective f := by
    intro a b hab
    change latticeLocation (fun x : {x // x ∈ P} ↦ planeToPair x.1)
        a ⟨p, hp⟩ =
      latticeLocation (fun x : {x // x ∈ P} ↦ planeToPair x.1)
        b ⟨p, hp⟩ at hab
    have hpairs := @periodicLift_index_injective P hP
      (a, (⟨p, hp⟩ : {x // x ∈ P}))
      (b, (⟨p, hp⟩ : {x // x ∈ P})) hab
    exact congrArg Prod.fst hpairs
  have hrange : (Set.range f).Infinite := Set.infinite_range_of_injective hf
  apply hrange.mono
  rintro x ⟨cell, rfl⟩
  exact ⟨(cell, ⟨p, hp⟩), rfl⟩

theorem periodicLift_inter_compact_finite {P : Finset Plane}
    (hP : InHalfOpenUnitSquare P) (K : Set Plane) (hK : IsCompact K) :
    (periodicLift P ∩ K).Finite := by
  let offset : {x // x ∈ P} → ℝ × ℝ := fun x ↦ planeToPair x.1
  have hoffset : ∀ q, 0 ≤ (offset q).1 ∧ (offset q).1 ≤ 1 ∧
      0 ≤ (offset q).2 ∧ (offset q).2 ≤ 1 := by
    intro q
    rcases hP q.1 q.2 with ⟨hx0, hx1, hy0, hy1⟩
    exact ⟨hx0, hx1.le, hy0, hy1.le⟩
  have hloc : CandidateTableLocallyFinite (latticeLocation offset) :=
    latticeLocation_candidateTableLocallyFinite hoffset
  obtain ⟨radius, hKr⟩ := hK.isBounded.subset_closedBall (0 : Plane)
  let cells : Set PlaneCell :=
    {cell | ∃ q : {x // x ∈ P},
      latticeLocation offset cell q ∈ Metric.closedBall (0 : Plane) radius}
  have hcells : cells.Finite := hloc 0 radius
  let indices : Set (PlaneCell × {x // x ∈ P}) := cells ×ˢ Set.univ
  have huniv : (Set.univ : Set {x // x ∈ P}).Finite := Set.toFinite _
  have hindices : indices.Finite := hcells.prod huniv
  apply (hindices.image fun a ↦ latticeLocation offset a.1 a.2).subset
  rintro x ⟨⟨a, rfl⟩, hxK⟩
  refine ⟨a, ?_, rfl⟩
  refine ⟨?_, Set.mem_univ _⟩
  exact ⟨a.2, hKr hxK⟩

theorem periodicLift_admissible {P : Finset Plane} (hP0 : P.Nonempty)
    (hP : InHalfOpenUnitSquare P) : IsAdmissible (periodicLift P) := by
  exact ⟨periodicLift_infinite hP0 hP,
    fun K hK ↦ periodicLift_inter_compact_finite hP K hK⟩

/-- Dilation of a point set. -/
def dilate (s : ℝ) (A : Set Plane) : Set Plane := (fun x : Plane ↦ s • x) '' A

theorem dilate_admissible {A : Set Plane} (hA : IsAdmissible A)
    {s : ℝ} (hs : s ≠ 0) : IsAdmissible (dilate s A) := by
  have hinj : Function.Injective (fun x : Plane ↦ s • x) :=
    smul_right_injective Plane hs
  constructor
  · exact hA.infinite.image hinj.injOn
  · intro K hK
    let K' : Set Plane := (fun y : Plane ↦ s⁻¹ • y) '' K
    have hK' : IsCompact K' := hK.image (continuous_const_smul s⁻¹)
    have hfin : (A ∩ K').Finite := hA.inter_compact_finite hK'
    apply (hfin.image fun x : Plane ↦ s • x).subset
    rintro y ⟨⟨x, hxA, rfl⟩, hyK⟩
    refine ⟨x, ⟨hxA, ?_⟩, rfl⟩
    exact ⟨s • x, hyK, by simp [smul_smul, hs]⟩

theorem dilate_inter_closedBall {A : Set Plane} {s : ℝ} (hs : s ≠ 0)
    (x : Plane) (r : ℝ) :
    dilate s A ∩ Metric.closedBall (s • x) (‖s‖ * r) =
      (fun y : Plane ↦ s • y) '' (A ∩ Metric.closedBall x r) := by
  rw [dilate, ← Metric.smul_image_closedBall hs x r]
  exact (Set.image_inter (smul_right_injective Plane hs)).symm

theorem diskCount_dilate {A : Set Plane} {s : ℝ} (hs : s ≠ 0)
    (x : Plane) (r : ℝ) :
    diskCount (dilate s A) (s • x) (‖s‖ * r) = diskCount A x r := by
  rw [diskCount, diskCount, dilate_inter_closedBall hs]
  exact Set.ncard_image_of_injective _ (smul_right_injective Plane hs)

/-- The sharp one-radius periodic consequence, stated without introducing a
quotient model of the flat torus.  The count is the count in the periodic lift
of `P`; after the density-one dilation its expected value is
`P.card * π * ρ²`. -/
def HasSharpPeriodicOneRadius : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, ∀ (P : Finset Plane), P.Nonempty →
    InHalfOpenUnitSquare P → ∀ ρ : ℝ, 0 < ρ →
      R ≤ Real.sqrt P.card * ρ → ∃ y : Plane,
        c * Real.sqrt (Real.sqrt P.card * ρ) ≤
          |(diskCount (periodicLift P) y ρ : ℝ) -
            (P.card : ℝ) * Real.pi * ρ ^ 2|

/-- The standard quarter-radius instance of the sharp periodic problem.  The
normalization is the fourth root of the number of points, written as two
successive square roots to avoid introducing real powers. -/
def HasSharpPeriodicQuarterRadius : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ (P : Finset Plane), P.Nonempty →
    InHalfOpenUnitSquare P → N₀ ≤ (P.card : ℝ) → ∃ y : Plane,
      c * Real.sqrt (Real.sqrt P.card) ≤
        |(diskCount (periodicLift P) y (1 / 4 : ℝ) : ℝ) -
          (P.card : ℝ) * Real.pi * (1 / 4 : ℝ) ^ 2|

/-- The literal uniform planar `c * sqrt r` lower bound implies the sharp
one-prescribed-radius `N^(1/4)` estimate for every finite periodic pattern. -/
theorem sharpPeriodicOneRadius_of_universalSqrtLowerBound
    (h : HasUniversalSqrtLowerBound) : HasSharpPeriodicOneRadius := by
  rcases h with ⟨c, hc, R, hbound⟩
  refine ⟨c, hc, R, ?_⟩
  intro P hP0 hP ρ hρ hlarge
  let s : ℝ := Real.sqrt P.card
  have hcard : 0 < P.card := Finset.card_pos.mpr hP0
  have hs : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast hcard)
  let A : Set Plane := dilate s (periodicLift P)
  have hA : IsAdmissible A :=
    dilate_admissible (periodicLift_admissible hP0 hP) hs.ne'
  obtain ⟨x, hx⟩ := hbound A hA (s * ρ) hlarge
  let y : Plane := s⁻¹ • x
  have hxy : s • y = x := by simp [y, smul_smul, hs.ne']
  refine ⟨y, ?_⟩
  have hnorm : ‖s‖ = s := by rw [Real.norm_eq_abs, abs_of_pos hs]
  have hcount := diskCount_dilate (A := periodicLift P) hs.ne' y ρ
  rw [hnorm, hxy] at hcount
  rw [diskError, show A = dilate s (periodicLift P) by rfl, hcount] at hx
  have hs_sq : s ^ 2 = (P.card : ℝ) := by
    dsimp [s]
    rw [Real.sq_sqrt]
    positivity
  convert hx using 1
  rw [← hs_sq]
  ring_nf

/-- In particular, the literal planar estimate would settle the sharp
quarter-radius periodic discrepancy problem with an absolute constant. -/
theorem sharpPeriodicQuarterRadius_of_universalSqrtLowerBound
    (h : HasUniversalSqrtLowerBound) : HasSharpPeriodicQuarterRadius := by
  rcases sharpPeriodicOneRadius_of_universalSqrtLowerBound h with
    ⟨c, hc, R, hperiodic⟩
  let R₀ : ℝ := max R 0
  refine ⟨c / 2, div_pos hc (by norm_num), (4 * R₀) ^ 2, ?_⟩
  intro P hP0 hP hcard
  have hR₀ : 0 ≤ R₀ := le_max_right _ _
  have hfour : 0 ≤ 4 * R₀ := by positivity
  have hcard0 : 0 ≤ (P.card : ℝ) := by positivity
  have hsqrt_card : 4 * R₀ ≤ Real.sqrt P.card := by
    rw [← Real.sqrt_sq hfour]
    exact Real.sqrt_le_sqrt hcard
  have hlarge : R ≤ Real.sqrt P.card * (1 / 4 : ℝ) := by
    have hRR₀ : R ≤ R₀ := le_max_left _ _
    nlinarith
  obtain ⟨y, hy⟩ := hperiodic P hP0 hP (1 / 4 : ℝ) (by norm_num) hlarge
  refine ⟨y, ?_⟩
  have hsqrt_sqrt_nonneg : 0 ≤ Real.sqrt (Real.sqrt P.card) :=
    Real.sqrt_nonneg _
  have hsqrt_quarter :
      Real.sqrt (Real.sqrt P.card * (1 / 4 : ℝ)) =
        Real.sqrt (Real.sqrt P.card) / 2 := by
    rw [Real.sqrt_mul (Real.sqrt_nonneg _)]
    norm_num
    rw [show Real.sqrt (4 : ℝ) = 2 by
      exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)]
    ring
  rw [hsqrt_quarter] at hy
  convert hy using 1 <;> ring

end

end PeriodicReduction
end Erdos989

#print axioms Erdos989.PeriodicReduction.sharpPeriodicOneRadius_of_universalSqrtLowerBound
#print axioms Erdos989.PeriodicReduction.sharpPeriodicQuarterRadius_of_universalSqrtLowerBound
