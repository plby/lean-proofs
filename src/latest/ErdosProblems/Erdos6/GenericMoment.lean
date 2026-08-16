import ErdosProblems.Erdos6.BFTParameters
import BoundedGaps.Maynard.ConcreteFiniteSimplexRiemann
import BoundedGaps.Maynard.ConcreteIndependentMomentFixedMesh

/-!
# A tuple-generic weighted simplex moment

This is the candidate-independent part of the concrete Maynard `S₁` limit.
It upgrades the already formalized scalar squarefree/totient asymptotic to a
bounded continuous function on a finite simplex by a finite grid squeeze.
-/

namespace Erdos6.Maynard

open Filter Set
open scoped BigOperators

noncomputable section

def tupleNaturalScale (H : Finset ℕ) (alpha : ℝ) (N : ℕ) : ℝ :=
  (BoundedGaps.Maynard.preSieveSingularSeries
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) *
    Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) ^
      Fintype.card H

def tupleNormalizedLogPoint (H : Finset ℕ) (alpha : ℝ) (N : ℕ)
    (u : H → ℕ) : H → ℝ :=
  fun h => Real.log (u h) /
    Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)

def tupleWeightedMoment (H : Finset ℕ) (alpha : ℝ)
    (f : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  ∑ u ∈ BoundedGaps.Maynard.preSievedSimplexTupleSupport H
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N),
    f (tupleNormalizedLogPoint H alpha N u) *
      BoundedGaps.Maynard.reciprocalTotientTupleWeight H u

def normalizedTupleWeightedMoment (H : Finset ℕ) (alpha : ℝ)
    (f : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  tupleWeightedMoment H alpha f N / tupleNaturalScale H alpha N

def tupleInnerGridMoment (H : Finset ℕ) (alpha : ℝ)
    (f : (H → ℝ) → ℝ) (mesh N : ℕ) : ℝ :=
  ∑ u ∈ BoundedGaps.Maynard.engelsmaSimplexInnerGridSupport
      H alpha mesh N,
    f (tupleNormalizedLogPoint H alpha N u) *
      BoundedGaps.Maynard.reciprocalTotientTupleWeight H u

def normalizedTupleInnerGridMoment (H : Finset ℕ) (alpha : ℝ)
    (f : (H → ℝ) → ℝ) (mesh N : ℕ) : ℝ :=
  tupleInnerGridMoment H alpha f mesh N / tupleNaturalScale H alpha N

def tupleCellMoment (H : Finset ℕ) (alpha : ℝ)
    (f : (H → ℝ) → ℝ) (mesh N : ℕ) : ℝ :=
  ∑ j ∈ BoundedGaps.Maynard.fractionalSimplexInnerGridIndex H mesh,
    ∑ u ∈ BoundedGaps.Maynard.engelsmaFractionalTupleShell H alpha
        (BoundedGaps.Maynard.fractionalGridLower mesh j)
        (BoundedGaps.Maynard.fractionalGridUpper mesh j) N,
      f (tupleNormalizedLogPoint H alpha N u) *
        BoundedGaps.Maynard.reciprocalTotientTupleWeight H u

def normalizedTupleCellMoment (H : Finset ℕ) (alpha : ℝ)
    (f : (H → ℝ) → ℝ) (mesh N : ℕ) : ℝ :=
  tupleCellMoment H alpha f mesh N / tupleNaturalScale H alpha N

def normalizedTupleStepMoment (H : Finset ℕ) (alpha : ℝ)
    (f : (H → ℝ) → ℝ) (mesh N : ℕ) : ℝ :=
  ∑ j ∈ BoundedGaps.Maynard.fractionalSimplexInnerGridIndex H mesh,
    f (BoundedGaps.Maynard.fractionalGridLower mesh j) *
      BoundedGaps.Maynard.normalizedEngelsmaFractionalTupleShellMass H alpha
        (BoundedGaps.Maynard.fractionalGridLower mesh j)
        (BoundedGaps.Maynard.fractionalGridUpper mesh j) N

theorem tupleNormalizedLogPoint_mem_finiteSimplex
    {H : Finset ℕ} {alpha : ℝ} {N : ℕ} {u : H → ℕ}
    (hR : 1 < BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (hu : u ∈ BoundedGaps.Maynard.preSievedSimplexTupleSupport H
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N)) :
    tupleNormalizedLogPoint H alpha N u ∈
      BoundedGaps.Maynard.finiteSimplexOf H := by
  have huCommon :=
    (BoundedGaps.Maynard.mem_preSievedSimplexTupleSupport_iff.mp hu).1
  have huBox : u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) := by
    rw [BoundedGaps.Maynard.mem_maynardDivisorTupleBox_iff]
    intro h
    have huh := Fintype.mem_piFinset.mp huCommon h
    have huhData := Finset.mem_filter.mp huh
    exact ⟨huhData.2.1, Finset.mem_range.mp huhData.1⟩
  constructor
  · rw [BoundedGaps.Maynard.maynardCubeOf, Set.mem_pi]
    intro h hh
    simpa [tupleNormalizedLogPoint,
      BoundedGaps.Maynard.normalizedDivisorLogTuple] using
      (BoundedGaps.Maynard.normalizedDivisorLogTuple_mem_Icc_of_mem_maynardDivisorTupleBox
        hR huBox h)
  · apply le_of_lt
    simpa [tupleNormalizedLogPoint,
      BoundedGaps.Maynard.normalizedDivisorLogTuple] using
      ((BoundedGaps.Maynard.divisorTupleProduct_lt_iff_sum_normalizedDivisorLogTuple_lt_one
          hR (fun h =>
            (BoundedGaps.Maynard.mem_maynardDivisorTupleBox_iff.mp huBox h).1)).mp
        (BoundedGaps.Maynard.mem_preSievedSimplexTupleSupport_iff.mp hu).2)

theorem eventually_tupleNaturalScale_pos {H : Finset ℕ}
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop, 0 < tupleNaturalScale H alpha N := by
  have hR := BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius halpha
  filter_upwards [hR] with N hRN
  unfold tupleNaturalScale
  have hS := BoundedGaps.Maynard.preSieveSingularSeries_pos
    (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
  have hlog : 0 < Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) :=
    Real.log_pos (by exact_mod_cast hRN)
  exact pow_pos (mul_pos hS hlog) _

theorem tendsto_normalizedTupleStepMoment
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    {mesh : ℕ} (hmesh : 0 < mesh) (f : (H → ℝ) → ℝ) :
    Tendsto (fun N : ℕ => normalizedTupleStepMoment H alpha f mesh N)
      atTop (nhds (BoundedGaps.Maynard.finiteSimplexInnerGridWeightedSum f mesh)) := by
  let I := BoundedGaps.Maynard.fractionalSimplexInnerGridIndex H mesh
  have hlim :=
    BoundedGaps.Maynard.tendsto_finite_linear_combination_normalizedEngelsmaFractionalTupleShellMass
      halpha I (fun j => f (BoundedGaps.Maynard.fractionalGridLower mesh j))
      (fun j => BoundedGaps.Maynard.fractionalGridLower mesh j)
      (fun j => BoundedGaps.Maynard.fractionalGridUpper mesh j)
      (fun j hj h =>
        (BoundedGaps.Maynard.fractionalSimplexInnerGridIndex_data hmesh hj).1 h |>.1)
      (fun j hj h =>
        (BoundedGaps.Maynard.fractionalSimplexInnerGridIndex_data hmesh hj).1 h |>.2.1)
      (fun j hj h =>
        (BoundedGaps.Maynard.fractionalSimplexInnerGridIndex_data hmesh hj).1 h |>.2.2)
  simpa [I, normalizedTupleStepMoment,
    BoundedGaps.Maynard.finiteSimplexInnerGridWeightedSum] using hlim

theorem eventually_tupleInnerGridMoment_eq_cellMoment
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    {mesh : ℕ} (hmesh : 0 < mesh) (f : (H → ℝ) → ℝ) :
    ∀ᶠ N : ℕ in atTop,
      tupleInnerGridMoment H alpha f mesh N = tupleCellMoment H alpha f mesh N := by
  have hdis :=
    BoundedGaps.Maynard.eventually_engelsmaSimplexInnerGridShells_pairwise_disjoint
      (H := H) halpha hmesh
  filter_upwards [hdis] with N hdisN
  unfold tupleInnerGridMoment tupleCellMoment
  rw [BoundedGaps.Maynard.engelsmaSimplexInnerGridSupport]
  rw [Finset.sum_biUnion]
  intro j hj k hk hjk
  exact hdisN j hj k hk hjk

theorem eventually_normalizedTupleInnerGridMoment_eq_cellMoment
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    {mesh : ℕ} (hmesh : 0 < mesh) (f : (H → ℝ) → ℝ) :
    ∀ᶠ N : ℕ in atTop,
      normalizedTupleInnerGridMoment H alpha f mesh N =
        normalizedTupleCellMoment H alpha f mesh N := by
  filter_upwards [eventually_tupleInnerGridMoment_eq_cellMoment
    halpha hmesh f] with N hN
  unfold normalizedTupleInnerGridMoment normalizedTupleCellMoment
  rw [hN]

theorem normalizedTupleCell_sub_step_le
    {H : Finset ℕ} {alpha epsilon : ℝ} {mesh N : ℕ}
    {f : (H → ℝ) → ℝ}
    (hscale : 0 < tupleNaturalScale H alpha N)
    (hepsilon : 0 ≤ epsilon)
    (hosc : ∀ j ∈ BoundedGaps.Maynard.fractionalSimplexInnerGridIndex H mesh,
      ∀ u ∈ BoundedGaps.Maynard.engelsmaFractionalTupleShell H alpha
        (BoundedGaps.Maynard.fractionalGridLower mesh j)
        (BoundedGaps.Maynard.fractionalGridUpper mesh j) N,
        |f (tupleNormalizedLogPoint H alpha N u) -
          f (BoundedGaps.Maynard.fractionalGridLower mesh j)| ≤ epsilon) :
    |normalizedTupleCellMoment H alpha f mesh N -
        normalizedTupleStepMoment H alpha f mesh N| ≤
      epsilon *
        BoundedGaps.Maynard.normalizedEngelsmaSimplexInnerGridStepMass
          H alpha mesh N := by
  let I := BoundedGaps.Maynard.fractionalSimplexInnerGridIndex H mesh
  have hraw :
      |tupleCellMoment H alpha f mesh N -
          ∑ j ∈ I,
            f (BoundedGaps.Maynard.fractionalGridLower mesh j) *
              BoundedGaps.Maynard.engelsmaFractionalTupleShellMass H alpha
                (BoundedGaps.Maynard.fractionalGridLower mesh j)
                (BoundedGaps.Maynard.fractionalGridUpper mesh j) N| ≤
        epsilon * ∑ j ∈ I,
          BoundedGaps.Maynard.engelsmaFractionalTupleShellMass H alpha
            (BoundedGaps.Maynard.fractionalGridLower mesh j)
            (BoundedGaps.Maynard.fractionalGridUpper mesh j) N := by
    unfold tupleCellMoment
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j ∈ I,
          |(∑ u ∈ BoundedGaps.Maynard.engelsmaFractionalTupleShell H alpha
                (BoundedGaps.Maynard.fractionalGridLower mesh j)
                (BoundedGaps.Maynard.fractionalGridUpper mesh j) N,
              f (tupleNormalizedLogPoint H alpha N u) *
                BoundedGaps.Maynard.reciprocalTotientTupleWeight H u) -
            f (BoundedGaps.Maynard.fractionalGridLower mesh j) *
              BoundedGaps.Maynard.engelsmaFractionalTupleShellMass H alpha
                (BoundedGaps.Maynard.fractionalGridLower mesh j)
                (BoundedGaps.Maynard.fractionalGridUpper mesh j) N| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ I, epsilon *
          BoundedGaps.Maynard.engelsmaFractionalTupleShellMass H alpha
            (BoundedGaps.Maynard.fractionalGridLower mesh j)
            (BoundedGaps.Maynard.fractionalGridUpper mesh j) N := by
        apply Finset.sum_le_sum
        intro j hj
        unfold BoundedGaps.Maynard.engelsmaFractionalTupleShellMass
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        calc
          _ ≤ ∑ u ∈ BoundedGaps.Maynard.engelsmaFractionalTupleShell H alpha
                (BoundedGaps.Maynard.fractionalGridLower mesh j)
                (BoundedGaps.Maynard.fractionalGridUpper mesh j) N,
              |f (tupleNormalizedLogPoint H alpha N u) *
                  BoundedGaps.Maynard.reciprocalTotientTupleWeight H u -
                f (BoundedGaps.Maynard.fractionalGridLower mesh j) *
                  BoundedGaps.Maynard.reciprocalTotientTupleWeight H u| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ u ∈ BoundedGaps.Maynard.engelsmaFractionalTupleShell H alpha
                (BoundedGaps.Maynard.fractionalGridLower mesh j)
                (BoundedGaps.Maynard.fractionalGridUpper mesh j) N,
              epsilon * BoundedGaps.Maynard.reciprocalTotientTupleWeight H u := by
            apply Finset.sum_le_sum
            intro u hu
            rw [← sub_mul, abs_mul, abs_of_nonneg
              (show 0 ≤ BoundedGaps.Maynard.reciprocalTotientTupleWeight H u by
                unfold BoundedGaps.Maynard.reciprocalTotientTupleWeight
                positivity)]
            exact mul_le_mul_of_nonneg_right (hosc j hj u hu)
              (by unfold BoundedGaps.Maynard.reciprocalTotientTupleWeight; positivity)
          _ = _ := by rw [Finset.mul_sum]
      _ = _ := by rw [Finset.mul_sum]
  have hstepEq : normalizedTupleStepMoment H alpha f mesh N =
      (∑ j ∈ I,
        f (BoundedGaps.Maynard.fractionalGridLower mesh j) *
          BoundedGaps.Maynard.engelsmaFractionalTupleShellMass H alpha
            (BoundedGaps.Maynard.fractionalGridLower mesh j)
            (BoundedGaps.Maynard.fractionalGridUpper mesh j) N) /
        tupleNaturalScale H alpha N := by
    unfold normalizedTupleStepMoment
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    unfold BoundedGaps.Maynard.normalizedEngelsmaFractionalTupleShellMass
      tupleNaturalScale
    ring
  have hmassEq :
      BoundedGaps.Maynard.normalizedEngelsmaSimplexInnerGridStepMass
          H alpha mesh N =
        (∑ j ∈ I,
          BoundedGaps.Maynard.engelsmaFractionalTupleShellMass H alpha
            (BoundedGaps.Maynard.fractionalGridLower mesh j)
            (BoundedGaps.Maynard.fractionalGridUpper mesh j) N) /
          tupleNaturalScale H alpha N := by
    unfold BoundedGaps.Maynard.normalizedEngelsmaSimplexInnerGridStepMass
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    unfold BoundedGaps.Maynard.normalizedEngelsmaFractionalTupleShellMass
      tupleNaturalScale
    rfl
  rw [hstepEq, hmassEq]
  unfold normalizedTupleCellMoment
  rw [← sub_div, abs_div, abs_of_pos hscale]
  apply (div_le_div_of_nonneg_right hraw hscale.le).trans_eq
  ring

def normalizedTupleBoundaryMass (H : Finset ℕ) (alpha : ℝ)
    (mesh N : ℕ) : ℝ :=
  BoundedGaps.Maynard.engelsmaSimplexBoundaryGridSupportMass H alpha mesh N /
    tupleNaturalScale H alpha N

theorem eventually_normalizedTupleBoundaryMass_eq_stepMass
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    {mesh : ℕ} (hmesh : 0 < mesh) :
    ∀ᶠ N : ℕ in atTop,
      normalizedTupleBoundaryMass H alpha mesh N =
        BoundedGaps.Maynard.normalizedEngelsmaSimplexBoundaryGridStepMass
          H alpha mesh N := by
  have heq :=
    BoundedGaps.Maynard.eventually_engelsmaSimplexBoundaryGridSupportMass_eq_stepMass
      (H := H) halpha hmesh
  filter_upwards [heq] with N heqN
  unfold normalizedTupleBoundaryMass
    BoundedGaps.Maynard.normalizedEngelsmaSimplexBoundaryGridStepMass
  rw [heqN, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  unfold BoundedGaps.Maynard.normalizedEngelsmaFractionalTupleShellMass
    tupleNaturalScale
  rfl

theorem eventually_normalizedTupleWeightedMoment_sub_inner_le_boundary
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    {mesh : ℕ} (hmesh : 0 < mesh)
    {f : (H → ℝ) → ℝ}
    (hfbounds : ∀ x ∈ BoundedGaps.Maynard.finiteSimplexOf H,
      0 ≤ f x ∧ f x ≤ 1) :
    ∀ᶠ N : ℕ in atTop,
      0 ≤ normalizedTupleWeightedMoment H alpha f N -
          normalizedTupleInnerGridMoment H alpha f mesh N ∧
        normalizedTupleWeightedMoment H alpha f N -
            normalizedTupleInnerGridMoment H alpha f mesh N ≤
          normalizedTupleBoundaryMass H alpha mesh N +
            BoundedGaps.Maynard.normalizedEngelsmaUnitBoundaryBoxUnionMass
              H alpha N := by
  have hsubset :=
    BoundedGaps.Maynard.eventually_engelsmaSimplexInnerGridSupport_subset
      (H := H) halpha hmesh
  have hcover :=
    BoundedGaps.Maynard.eventually_preSievedSimplexTupleSupport_mem_inner_or_boundaryShell
      (H := H) halpha hmesh
  have hscale := eventually_tupleNaturalScale_pos (H := H) halpha
  have hR := BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius halpha
  filter_upwards [hsubset, hcover, hscale, hR] with
      N hsubsetN hcoverN hscaleN hRN
  let S := BoundedGaps.Maynard.preSievedSimplexTupleSupport H
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (BoundedGaps.Maynard.engelsmaMaynardModulus N)
  let A := BoundedGaps.Maynard.engelsmaSimplexInnerGridSupport H alpha mesh N
  let B := BoundedGaps.Maynard.engelsmaSimplexBoundaryGridShellUnion H alpha mesh N
  let U := BoundedGaps.Maynard.engelsmaUnitBoundaryBoxUnion H alpha N
  let g : (H → ℕ) → ℝ := fun u =>
    f (tupleNormalizedLogPoint H alpha N u) *
      BoundedGaps.Maynard.reciprocalTotientTupleWeight H u
  let w : (H → ℕ) → ℝ := fun u =>
    BoundedGaps.Maynard.reciprocalTotientTupleWeight H u
  have hAS : A ⊆ S := hsubsetN
  have hgBounds : ∀ u ∈ S, 0 ≤ g u ∧ g u ≤ w u := by
    intro u hu
    have huCommon :=
      (BoundedGaps.Maynard.mem_preSievedSimplexTupleSupport_iff.mp hu).1
    have huBox : u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) := by
      rw [BoundedGaps.Maynard.mem_maynardDivisorTupleBox_iff]
      intro h
      have huh := Fintype.mem_piFinset.mp huCommon h
      have huhData := Finset.mem_filter.mp huh
      exact ⟨huhData.2.1, Finset.mem_range.mp huhData.1⟩
    have hpoint : tupleNormalizedLogPoint H alpha N u ∈
        BoundedGaps.Maynard.finiteSimplexOf H := by
      constructor
      · rw [BoundedGaps.Maynard.maynardCubeOf, Set.mem_pi]
        intro h hh
        simpa [tupleNormalizedLogPoint,
          BoundedGaps.Maynard.normalizedDivisorLogTuple] using
          (BoundedGaps.Maynard.normalizedDivisorLogTuple_mem_Icc_of_mem_maynardDivisorTupleBox
            hRN huBox h)
      · apply le_of_lt
        simpa [tupleNormalizedLogPoint,
          BoundedGaps.Maynard.normalizedDivisorLogTuple] using
          ((BoundedGaps.Maynard.divisorTupleProduct_lt_iff_sum_normalizedDivisorLogTuple_lt_one
              hRN (fun h =>
                (BoundedGaps.Maynard.mem_maynardDivisorTupleBox_iff.mp huBox h).1)).mp
            (BoundedGaps.Maynard.mem_preSievedSimplexTupleSupport_iff.mp hu).2)
    have hfB := hfbounds _ hpoint
    have hw : 0 ≤ w u := by
      dsimp [w]
      unfold BoundedGaps.Maynard.reciprocalTotientTupleWeight
      positivity
    dsimp [g]
    exact ⟨mul_nonneg hfB.1 hw, mul_le_of_le_one_left hw hfB.2⟩
  have hremSubset : S \ A ⊆ B ∪ U := by
    intro u hu
    have huData := Finset.mem_sdiff.mp hu
    by_cases hunit : ∃ h : H, u h = 1
    · exact Finset.mem_union.mpr (Or.inr
        (BoundedGaps.Maynard.preSievedSimplexUnitBoundary_subset_boxUnion
          huData.1 hunit))
    · have hnoUnit : ∀ h : H, u h ≠ 1 := not_exists.mp hunit
      rcases hcoverN u huData.1 hnoUnit with huInner | huBoundary
      · exact False.elim (huData.2 huInner)
      · exact Finset.mem_union.mpr (Or.inl huBoundary)
  have hremG : (∑ u ∈ S \ A, g u) ≤ ∑ u ∈ S \ A, w u := by
    apply Finset.sum_le_sum
    intro u hu
    exact (hgBounds u (Finset.sdiff_subset hu)).2
  have hremW : (∑ u ∈ S \ A, w u) ≤ ∑ u ∈ B ∪ U, w u := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hremSubset
    intro u hu hnot
    dsimp [w]
    unfold BoundedGaps.Maynard.reciprocalTotientTupleWeight
    positivity
  have hunion : (∑ u ∈ B ∪ U, w u) ≤
      (∑ u ∈ B, w u) + ∑ u ∈ U, w u := by
    have hinter : 0 ≤ ∑ u ∈ B ∩ U, w u := by
      apply Finset.sum_nonneg
      intro u hu
      dsimp [w]
      unfold BoundedGaps.Maynard.reciprocalTotientTupleWeight
      positivity
    have heq := Finset.sum_union_inter (s₁ := B) (s₂ := U) (f := w)
    linarith
  have hrawNonneg : 0 ≤ (∑ u ∈ S, g u) - ∑ u ∈ A, g u := by
    rw [← Finset.sum_sdiff_eq_sub hAS]
    apply Finset.sum_nonneg
    intro u hu
    exact (hgBounds u (Finset.sdiff_subset hu)).1
  have hrawUpper : (∑ u ∈ S, g u) - ∑ u ∈ A, g u ≤
      (∑ u ∈ B, w u) + ∑ u ∈ U, w u := by
    rw [← Finset.sum_sdiff_eq_sub hAS]
    exact hremG.trans (hremW.trans hunion)
  have hnormEq :
      normalizedTupleWeightedMoment H alpha f N -
          normalizedTupleInnerGridMoment H alpha f mesh N =
        ((∑ u ∈ S, g u) - ∑ u ∈ A, g u) /
          tupleNaturalScale H alpha N := by
    unfold normalizedTupleWeightedMoment tupleWeightedMoment
      normalizedTupleInnerGridMoment tupleInnerGridMoment
    dsimp [S, A, g]
    ring
  rw [hnormEq]
  constructor
  · exact div_nonneg hrawNonneg hscaleN.le
  · have hdiv := div_le_div_of_nonneg_right hrawUpper hscaleN.le
    apply hdiv.trans_eq
    unfold normalizedTupleBoundaryMass
      BoundedGaps.Maynard.engelsmaSimplexBoundaryGridSupportMass
      BoundedGaps.Maynard.normalizedEngelsmaUnitBoundaryBoxUnionMass
      BoundedGaps.Maynard.engelsmaUnitBoundaryBoxUnionMass
      tupleNaturalScale
    dsimp [B, U, w]
    ring

theorem exists_large_mesh_eventually_tuple_shell_oscillation
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    {f : (H → ℝ) → ℝ} (hf : Continuous f) (M : ℕ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ mesh : ℕ, M ≤ mesh ∧ 0 < mesh ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ j ∈ BoundedGaps.Maynard.fractionalSimplexInnerGridIndex H mesh,
        ∀ u ∈ BoundedGaps.Maynard.engelsmaFractionalTupleShell H alpha
          (BoundedGaps.Maynard.fractionalGridLower mesh j)
          (BoundedGaps.Maynard.fractionalGridUpper mesh j) N,
          |f (tupleNormalizedLogPoint H alpha N u) -
            f (BoundedGaps.Maynard.fractionalGridLower mesh j)| < epsilon := by
  have hcompact : IsCompact (BoundedGaps.Maynard.maynardCubeOf H) := by
    unfold BoundedGaps.Maynard.maynardCubeOf
    exact isCompact_univ_pi (fun _ => isCompact_Icc)
  have huc : UniformContinuousOn f (BoundedGaps.Maynard.maynardCubeOf H) :=
    hcompact.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨delta, hdelta, hcontrol⟩ :=
    (Metric.uniformContinuousOn_iff.mp huc) epsilon hepsilon
  have hmeshT : Tendsto (fun mesh : ℕ => (2 : ℝ) / mesh)
      atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
  have hmeshEvent := hmeshT.eventually (Iio_mem_nhds hdelta)
  rw [eventually_atTop] at hmeshEvent
  obtain ⟨mesh0, hmesh0⟩ := hmeshEvent
  let mesh := max mesh0 (max M 1)
  have hmesh0mesh : mesh0 ≤ mesh := by simp [mesh]
  have hMmesh : M ≤ mesh := by simp [mesh]
  have hmesh : 0 < mesh := by dsimp [mesh]; omega
  have hmeshSmall : (2 : ℝ) / mesh < delta := hmesh0 mesh hmesh0mesh
  refine ⟨mesh, hMmesh, hmesh, ?_⟩
  have hclose :=
    BoundedGaps.Maynard.eventually_fractionalGridShell_normalizedLog_close
      (H := H) halpha hmesh
  have hsubset :=
    BoundedGaps.Maynard.eventually_engelsmaSimplexInnerGridSupport_subset
      (H := H) halpha hmesh
  have hR := BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius halpha
  filter_upwards [hclose, hsubset, hR] with N hcloseN hsubsetN hRN
      j hj u hu
  have hjGrid := (Finset.mem_filter.mp hj).1
  have huInner : u ∈ BoundedGaps.Maynard.engelsmaSimplexInnerGridSupport
      H alpha mesh N := by
    rw [BoundedGaps.Maynard.engelsmaSimplexInnerGridSupport,
      Finset.mem_biUnion]
    exact ⟨j, hj, hu⟩
  have huPre := hsubsetN huInner
  have huCommon :=
    (BoundedGaps.Maynard.mem_preSievedSimplexTupleSupport_iff.mp huPre).1
  have huBox : u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) := by
    rw [BoundedGaps.Maynard.mem_maynardDivisorTupleBox_iff]
    intro h
    have huh := Fintype.mem_piFinset.mp huCommon h
    have huhData := Finset.mem_filter.mp huh
    exact ⟨huhData.2.1, Finset.mem_range.mp huhData.1⟩
  have hlogCube : tupleNormalizedLogPoint H alpha N u ∈
      BoundedGaps.Maynard.maynardCubeOf H := by
    rw [BoundedGaps.Maynard.maynardCubeOf, Set.mem_pi]
    intro h hh
    simpa [tupleNormalizedLogPoint,
      BoundedGaps.Maynard.normalizedDivisorLogTuple] using
      (BoundedGaps.Maynard.normalizedDivisorLogTuple_mem_Icc_of_mem_maynardDivisorTupleBox
        hRN huBox h)
  have hlowerCube : BoundedGaps.Maynard.fractionalGridLower mesh j ∈
      BoundedGaps.Maynard.maynardCubeOf H := by
    rw [BoundedGaps.Maynard.maynardCubeOf, Set.mem_pi]
    intro h hh
    exact (BoundedGaps.Maynard.fractionalSimplexInnerGridIndex_data hmesh hj).1 h |>.1
  have hdist : dist (tupleNormalizedLogPoint H alpha N u)
      (BoundedGaps.Maynard.fractionalGridLower mesh j) < delta := by
    apply (dist_pi_lt_iff hdelta).mpr
    intro h
    apply lt_trans ?_ hmeshSmall
    have hcoord := hcloseN j hjGrid u hu h
    simpa [tupleNormalizedLogPoint,
      BoundedGaps.Maynard.normalizedDivisorLogTuple, Real.dist_eq] using hcoord
  have hout := hcontrol _ hlogCube _ hlowerCube hdist
  simpa [Real.dist_eq] using hout

theorem tendsto_normalizedTupleWeightedMoment
    {H : Finset ℕ} (h0 : H) {alpha : ℝ} (halpha : 0 < alpha)
    {f : (H → ℝ) → ℝ} (hf : Continuous f)
    (hfbounds : ∀ x ∈ BoundedGaps.Maynard.finiteSimplexOf H,
      0 ≤ f x ∧ f x ≤ 1) :
    Tendsto (fun N : ℕ => normalizedTupleWeightedMoment H alpha f N)
      atTop (nhds (∫ x in BoundedGaps.Maynard.finiteSimplexOf H, f x)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let L := ∫ x in BoundedGaps.Maynard.finiteSimplexOf H, f x
  have he10 : 0 < epsilon / 10 := by linarith
  have he20 : 0 < epsilon / 20 := by linarith
  have hRiemT := BoundedGaps.Maynard.tendsto_finiteSimplexInnerGridWeightedSum
    h0 hf (fun x hx => by
      rw [abs_of_nonneg (hfbounds x hx).1]
      exact (hfbounds x hx).2)
  have hRiem : ∀ᶠ mesh : ℕ in atTop,
      dist (BoundedGaps.Maynard.finiteSimplexInnerGridWeightedSum f mesh) L <
        epsilon / 10 :=
    hRiemT.eventually (Metric.ball_mem_nhds _ he10)
  have hboundaryT := BoundedGaps.Maynard.tendsto_simplexBoundaryGridVolume_zero h0
  have hboundary : ∀ᶠ mesh : ℕ in atTop,
      BoundedGaps.Maynard.simplexBoundaryGridVolume H mesh < epsilon / 20 :=
    hboundaryT.eventually (Iio_mem_nhds he20)
  have hmeshEvent := hRiem.and hboundary
  rw [eventually_atTop] at hmeshEvent
  obtain ⟨M, hM⟩ := hmeshEvent
  obtain ⟨mesh, hMmesh, hmesh, hosc⟩ :=
    exists_large_mesh_eventually_tuple_shell_oscillation
      halpha hf M he20
  have hmeshData := hM mesh hMmesh
  have hgridClose := hmeshData.1
  have hboundaryVolume := hmeshData.2
  have hstepT := tendsto_normalizedTupleStepMoment halpha hmesh f
  have hstep : ∀ᶠ N : ℕ in atTop,
      dist (normalizedTupleStepMoment H alpha f mesh N)
        (BoundedGaps.Maynard.finiteSimplexInnerGridWeightedSum f mesh) <
          epsilon / 10 :=
    hstepT.eventually (Metric.ball_mem_nhds _ he10)
  have hmassT :=
    BoundedGaps.Maynard.tendsto_normalizedEngelsmaSimplexInnerGridStepMass
      (H := H) halpha hmesh
  have hvolumeLe := BoundedGaps.Maynard.simplexInnerGridVolume_le_one_finite
    (H := H) hmesh
  have hvolumeLt : BoundedGaps.Maynard.simplexInnerGridVolume H mesh < 2 := by
    linarith
  have hmass : ∀ᶠ N : ℕ in atTop,
      BoundedGaps.Maynard.normalizedEngelsmaSimplexInnerGridStepMass
        H alpha mesh N < 2 :=
    hmassT.eventually (Iio_mem_nhds hvolumeLt)
  have hboundaryStepT :=
    BoundedGaps.Maynard.tendsto_normalizedEngelsmaSimplexBoundaryGridStepMass
      (H := H) halpha hmesh
  have hboundaryStep : ∀ᶠ N : ℕ in atTop,
      dist (BoundedGaps.Maynard.normalizedEngelsmaSimplexBoundaryGridStepMass
          H alpha mesh N)
        (BoundedGaps.Maynard.simplexBoundaryGridVolume H mesh) < epsilon / 20 :=
    hboundaryStepT.eventually (Metric.ball_mem_nhds _ he20)
  have hboundaryEq :=
    eventually_normalizedTupleBoundaryMass_eq_stepMass (H := H) halpha hmesh
  have hunitT :=
    BoundedGaps.Maynard.tendsto_normalizedEngelsmaUnitBoundaryBoxUnionMass_zero
      (H := H) halpha
  have hunit : ∀ᶠ N : ℕ in atTop,
      dist (BoundedGaps.Maynard.normalizedEngelsmaUnitBoundaryBoxUnionMass
        H alpha N) 0 < epsilon / 10 :=
    hunitT.eventually (Metric.ball_mem_nhds _ he10)
  have hinnerEq :=
    eventually_normalizedTupleInnerGridMoment_eq_cellMoment halpha hmesh f
  have henvelope :=
    eventually_normalizedTupleWeightedMoment_sub_inner_le_boundary
      halpha hmesh hfbounds
  have hscale := eventually_tupleNaturalScale_pos (H := H) halpha
  filter_upwards [hosc, hstep, hmass, hboundaryStep, hboundaryEq,
      hunit, hinnerEq, henvelope, hscale] with N hoscN hstepN hmassN
      hboundaryStepN hboundaryEqN hunitN hinnerEqN henvelopeN hscaleN
  let full := normalizedTupleWeightedMoment H alpha f N
  let inner := normalizedTupleInnerGridMoment H alpha f mesh N
  let cell := normalizedTupleCellMoment H alpha f mesh N
  let step := normalizedTupleStepMoment H alpha f mesh N
  let grid := BoundedGaps.Maynard.finiteSimplexInnerGridWeightedSum f mesh
  let boundary := normalizedTupleBoundaryMass H alpha mesh N
  let unit := BoundedGaps.Maynard.normalizedEngelsmaUnitBoundaryBoxUnionMass
    H alpha N
  have hmassNonneg : 0 ≤
      BoundedGaps.Maynard.normalizedEngelsmaSimplexInnerGridStepMass
        H alpha mesh N := by
    unfold BoundedGaps.Maynard.normalizedEngelsmaSimplexInnerGridStepMass
    apply Finset.sum_nonneg
    intro j hj
    unfold BoundedGaps.Maynard.normalizedEngelsmaFractionalTupleShellMass
    apply div_nonneg
    · unfold BoundedGaps.Maynard.engelsmaFractionalTupleShellMass
      apply Finset.sum_nonneg
      intro u hu
      unfold BoundedGaps.Maynard.reciprocalTotientTupleWeight
      positivity
    · exact hscaleN.le
  have hcellStepRaw := normalizedTupleCell_sub_step_le
    hscaleN he20.le (fun j hj u hu => (hoscN j hj u hu).le)
  have hcellStep : |cell - step| < epsilon / 10 := by
    dsimp [cell, step]
    apply lt_of_le_of_lt hcellStepRaw
    nlinarith
  have hinnerStep : |inner - step| < epsilon / 10 := by
    simpa [inner, cell, step, hinnerEqN] using hcellStep
  have hstepGrid : |step - grid| < epsilon / 10 := by
    simpa [step, grid, Real.dist_eq] using hstepN
  have hgridL : |grid - L| < epsilon / 10 := by
    simpa [grid, Real.dist_eq] using hgridClose
  have hboundarySmall : boundary < epsilon / 10 := by
    dsimp [boundary]
    rw [hboundaryEqN]
    have habs :
        |BoundedGaps.Maynard.normalizedEngelsmaSimplexBoundaryGridStepMass
            H alpha mesh N -
          BoundedGaps.Maynard.simplexBoundaryGridVolume H mesh| <
            epsilon / 20 := by
      simpa [Real.dist_eq] using hboundaryStepN
    linarith [le_abs_self
      (BoundedGaps.Maynard.normalizedEngelsmaSimplexBoundaryGridStepMass
        H alpha mesh N - BoundedGaps.Maynard.simplexBoundaryGridVolume H mesh)]
  have hunitSmall : unit < epsilon / 10 := by
    have habs : |unit| < epsilon / 10 := by
      simpa [unit, Real.dist_eq] using hunitN
    exact (le_abs_self unit).trans_lt habs
  have hfullInnerNonneg : 0 ≤ full - inner := henvelopeN.1
  have hfullInner : |full - inner| < epsilon / 5 := by
    rw [abs_of_nonneg hfullInnerNonneg]
    exact henvelopeN.2.trans_lt (by
      dsimp [boundary, unit] at hboundarySmall hunitSmall ⊢
      linarith)
  rw [Real.dist_eq]
  change |full - L| < epsilon
  calc
    |full - L| = |(full - inner) + (inner - step) +
        (step - grid) + (grid - L)| := by ring_nf
    _ ≤ |full - inner| + |inner - step| +
        |step - grid| + |grid - L| := by
      calc
        _ ≤ |(full - inner) + (inner - step) + (step - grid)| +
            |grid - L| := abs_add_le _ _
        _ ≤ (|(full - inner) + (inner - step)| + |step - grid|) +
            |grid - L| := by gcongr; exact abs_add_le _ _
        _ ≤ ((|full - inner| + |inner - step|) + |step - grid|) +
            |grid - L| := by gcongr; exact abs_add_le _ _
    _ < epsilon := by linarith

end

end Erdos6.Maynard
