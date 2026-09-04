/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1124.CircleOrdering
import ErdosProblems.Erdos1124.ConcreteSets
import ErdosProblems.Erdos1124.DiophantineChoice
import ErdosProblems.Erdos1124.FejerSandwich
import ErdosProblems.Erdos1124.FreeTuple
import ErdosProblems.Erdos1124.ProductOrbit

/-!
# Quantitative discrepancy for the concrete disk and square

This file assembles the analytic and geometric ingredients of the
Laczkovich--Marks--Unger circle-squaring argument.  Its application-facing
endpoint supplies a free family of sixty-four translations of the
two-dimensional unit torus whose dyadic orbit cubes have power-saving
discrepancy for both the embedded disk and the equal-area embedded square.
-/

open scoped BigOperators ENNReal NNReal Topology
open Finset Function MeasureTheory Set Filter

namespace Erdos1124.ConcreteDiscrepancy

noncomputable section

abbrev Circle := OneDimensionalDiscrepancy.Circle

/-! ## Ordered orbit enumerations -/

/-- The canonical bijection from an indexed free orbit box to its underlying
finite set. -/
def negativeOrbitEquiv {d N : ℕ} {u : Fin d → Circle}
    (hu : FreeTuple.CircleFree u) (x : Circle) :
    (Fin d → Fin N) ≃ OneDimensionalDiscrepancy.negativeOrbitFinset u N x :=
  Equiv.ofBijective
    (fun a ↦ ⟨OneDimensionalDiscrepancy.negativeOrbitPoint u x a,
      Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩)
    ⟨fun a b h ↦ OneDimensionalDiscrepancy.negativeOrbitPoint_injective hu x
        (Subtype.ext_iff.mp h),
      fun y ↦ by
        rcases Finset.mem_image.mp y.property with ⟨a, _, ha⟩
        refine ⟨a, Subtype.ext ?_⟩
        exact ha⟩

/-- Reindex the ordered representatives of a free orbit box by any exact
factorization `m*q = N^d`. -/
def orderedOrbitIndexEquiv {d m q N : ℕ} {u : Fin d → Circle}
    (hu : FreeTuple.CircleFree u) (x : Circle) (hmq : m * q = N ^ d) :
    Fin (m * q) ≃ (Fin d → Fin N) :=
  (finCongr (hmq.trans
      (OneDimensionalDiscrepancy.card_negativeOrbitFinset hu N x).symm)).trans
    ((CircleOrdering.orderedEquiv
      (OneDimensionalDiscrepancy.negativeOrbitFinset u N x)).trans
        (negativeOrbitEquiv hu x).symm)

@[simp]
theorem negativeOrbitPoint_orderedOrbitIndexEquiv {d m q N : ℕ}
    {u : Fin d → Circle} (hu : FreeTuple.CircleFree u) (x : Circle)
    (hmq : m * q = N ^ d) (j : Fin (m * q)) :
    OneDimensionalDiscrepancy.negativeOrbitPoint u x
        (orderedOrbitIndexEquiv hu x hmq j) =
      CircleOrdering.orderedEquiv
        (OneDimensionalDiscrepancy.negativeOrbitFinset u N x)
        (finCongr (hmq.trans
          (OneDimensionalDiscrepancy.card_negativeOrbitFinset hu N x).symm) j) := by
  change ((negativeOrbitEquiv hu x)
      ((negativeOrbitEquiv hu x).symm
        (CircleOrdering.orderedEquiv
          (OneDimensionalDiscrepancy.negativeOrbitFinset u N x)
          (finCongr (hmq.trans
            (OneDimensionalDiscrepancy.card_negativeOrbitFinset hu N x).symm) j))) :
      Circle) = _
  rw [Equiv.apply_symm_apply]

/-- The representative of `ProductOrbit.circleOrbitPoint` agrees with the
negative-orbit convention used by the one-dimensional discrepancy theorem. -/
theorem circleOrbitPoint_eq_negativeOrbitPoint
    (u : Fin ProductOrbit.coordinateDimension → Circle) (x : Circle)
    {N : ℕ} (a : Fin ProductOrbit.coordinateDimension → Fin N) :
    ProductOrbit.circleOrbitPoint u x a =
      OneDimensionalDiscrepancy.negativeOrbitPoint u x a := by
  simp only [ProductOrbit.circleOrbitPoint,
    OneDimensionalDiscrepancy.negativeOrbitPoint,
    ProductOrbit.circleDisplacement, Flow.cubeIndex, Pi.neg_apply, neg_zsmul]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- Ordered product-orbit samples are literally the increasing ordered
representatives of their one-dimensional orbit finset. -/
theorem orderedOrbitSamples_eq_orderedRepresentatives
    {m q N : ℕ}
    {u v : Fin ProductOrbit.coordinateDimension → Circle}
    (hu : FreeTuple.CircleFree u) (hv : FreeTuple.CircleFree v)
    (x : TorusAction.Torus 2)
    (hmq : m * q = N ^ ProductOrbit.coordinateDimension)
    (i : Fin 2) (j : Fin (m * q)) :
    ProductOrbit.orderedOrbitSamples u v x
        (orderedOrbitIndexEquiv hu (x 0) hmq)
        (orderedOrbitIndexEquiv hv (x 1) hmq) i j =
      match i with
      | 0 => CircleOrdering.orderedRepresentatives
          (OneDimensionalDiscrepancy.negativeOrbitFinset u N (x 0))
          (finCongr (hmq.trans
            (OneDimensionalDiscrepancy.card_negativeOrbitFinset hu N (x 0)).symm) j)
      | 1 => CircleOrdering.orderedRepresentatives
          (OneDimensionalDiscrepancy.negativeOrbitFinset v N (x 1))
          (finCongr (hmq.trans
            (OneDimensionalDiscrepancy.card_negativeOrbitFinset hv N (x 1)).symm) j) := by
  fin_cases i <;>
    simp only [ProductOrbit.orderedOrbitSamples] <;>
    rw [circleOrbitPoint_eq_negativeOrbitPoint,
      negativeOrbitPoint_orderedOrbitIndexEquiv,
      CircleOrdering.equivIco_orderedEquiv]

private theorem strictMono_finCongr {n m : ℕ} (h : n = m) :
    StrictMono (finCongr h) := by
  intro i j hij
  exact hij

private theorem hasIntervalDiscrepancy_finCongr {n m : ℕ} (h : n = m)
    (y : Fin m → ℝ) (Δ : ℝ)
    (hy : ProductGrid.HasIntervalDiscrepancy y Δ) :
    ProductGrid.HasIntervalDiscrepancy (fun i ↦ y (finCongr h i)) Δ := by
  subst m
  simpa using hy

private theorem hasIntervalDiscrepancy_mono {n : ℕ} {y : Fin n → ℝ}
    {Δ Δ' : ℝ} (hy : ProductGrid.HasIntervalDiscrepancy y Δ)
    (hΔ : Δ ≤ Δ') : ProductGrid.HasIntervalDiscrepancy y Δ' := by
  intro a b ha hab hb
  exact (hy ha hab hb).trans hΔ

/-- Both coordinate lists in the product-orbit reindexing are strictly
increasing. -/
theorem strictMono_orderedOrbitSamples {m q N : ℕ}
    {u v : Fin ProductOrbit.coordinateDimension → Circle}
    (hu : FreeTuple.CircleFree u) (hv : FreeTuple.CircleFree v)
    (x : TorusAction.Torus 2)
    (hmq : m * q = N ^ ProductOrbit.coordinateDimension) :
    ∀ i, StrictMono (ProductOrbit.orderedOrbitSamples u v x
      (orderedOrbitIndexEquiv hu (x 0) hmq)
      (orderedOrbitIndexEquiv hv (x 1) hmq) i) := by
  intro i
  fin_cases i
  · change StrictMono (ProductOrbit.orderedOrbitSamples u v x
      (orderedOrbitIndexEquiv hu (x 0) hmq)
      (orderedOrbitIndexEquiv hv (x 1) hmq) 0)
    rw [show ProductOrbit.orderedOrbitSamples u v x
        (orderedOrbitIndexEquiv hu (x 0) hmq)
        (orderedOrbitIndexEquiv hv (x 1) hmq) 0 =
        fun j ↦ CircleOrdering.orderedRepresentatives
          (OneDimensionalDiscrepancy.negativeOrbitFinset u N (x 0))
          (finCongr (hmq.trans
            (OneDimensionalDiscrepancy.card_negativeOrbitFinset hu N (x 0)).symm) j) by
      funext j
      exact orderedOrbitSamples_eq_orderedRepresentatives hu hv x hmq 0 j]
    exact (CircleOrdering.strictMono_orderedRepresentatives _).comp
      (strictMono_finCongr _)
  · change StrictMono (ProductOrbit.orderedOrbitSamples u v x
      (orderedOrbitIndexEquiv hu (x 0) hmq)
      (orderedOrbitIndexEquiv hv (x 1) hmq) 1)
    rw [show ProductOrbit.orderedOrbitSamples u v x
        (orderedOrbitIndexEquiv hu (x 0) hmq)
        (orderedOrbitIndexEquiv hv (x 1) hmq) 1 =
        fun j ↦ CircleOrdering.orderedRepresentatives
          (OneDimensionalDiscrepancy.negativeOrbitFinset v N (x 1))
          (finCongr (hmq.trans
            (OneDimensionalDiscrepancy.card_negativeOrbitFinset hv N (x 1)).symm) j) by
      funext j
      exact orderedOrbitSamples_eq_orderedRepresentatives hu hv x hmq 1 j]
    exact (CircleOrdering.strictMono_orderedRepresentatives _).comp
      (strictMono_finCongr _)

/-- Every coordinate of every ordered product-orbit sample is in the
half-open fundamental interval. -/
theorem orderedOrbitSamples_mem_Ico {m q N : ℕ}
    {u v : Fin ProductOrbit.coordinateDimension → Circle}
    (hu : FreeTuple.CircleFree u) (hv : FreeTuple.CircleFree v)
    (x : TorusAction.Torus 2)
    (hmq : m * q = N ^ ProductOrbit.coordinateDimension) :
    ∀ i j, ProductOrbit.orderedOrbitSamples u v x
      (orderedOrbitIndexEquiv hu (x 0) hmq)
      (orderedOrbitIndexEquiv hv (x 1) hmq) i j ∈ Set.Ico (0 : ℝ) 1 := by
  intro i j
  rw [orderedOrbitSamples_eq_orderedRepresentatives hu hv x hmq i j]
  split <;> apply CircleOrdering.orderedRepresentatives_mem_Ico

/-- The two ordered coordinate lists inherit twice the intrinsic interval
discrepancy of their respective circle orbit finsets. -/
theorem orderedOrbitSamples_hasIntervalDiscrepancy {m q N : ℕ}
    {u v : Fin ProductOrbit.coordinateDimension → Circle}
    (hu : FreeTuple.CircleFree u) (hv : FreeTuple.CircleFree v)
    (hN : 0 < N) (x : TorusAction.Torus 2)
    (hmq : m * q = N ^ ProductOrbit.coordinateDimension) (i : Fin 2) :
    ProductGrid.HasIntervalDiscrepancy
      (ProductOrbit.orderedOrbitSamples u v x
        (orderedOrbitIndexEquiv hu (x 0) hmq)
        (orderedOrbitIndexEquiv hv (x 1) hmq) i)
      (match i with
       | 0 => 2 * OneDimensionalDiscrepancy.intervalDiscrepancy
          (OneDimensionalDiscrepancy.negativeOrbitFinset u N (x 0))
       | 1 => 2 * OneDimensionalDiscrepancy.intervalDiscrepancy
          (OneDimensionalDiscrepancy.negativeOrbitFinset v N (x 1))) := by
  have huNonempty :
      (OneDimensionalDiscrepancy.negativeOrbitFinset u N (x 0)).Nonempty := by
    apply Finset.card_pos.mp
    rw [OneDimensionalDiscrepancy.card_negativeOrbitFinset hu]
    positivity
  have hvNonempty :
      (OneDimensionalDiscrepancy.negativeOrbitFinset v N (x 1)).Nonempty := by
    apply Finset.card_pos.mp
    rw [OneDimensionalDiscrepancy.card_negativeOrbitFinset hv]
    positivity
  fin_cases i
  · change ProductGrid.HasIntervalDiscrepancy
      (ProductOrbit.orderedOrbitSamples u v x
        (orderedOrbitIndexEquiv hu (x 0) hmq)
        (orderedOrbitIndexEquiv hv (x 1) hmq) 0)
      (2 * OneDimensionalDiscrepancy.intervalDiscrepancy
        (OneDimensionalDiscrepancy.negativeOrbitFinset u N (x 0)))
    rw [show ProductOrbit.orderedOrbitSamples u v x
        (orderedOrbitIndexEquiv hu (x 0) hmq)
        (orderedOrbitIndexEquiv hv (x 1) hmq) 0 =
        fun j ↦ CircleOrdering.orderedRepresentatives
          (OneDimensionalDiscrepancy.negativeOrbitFinset u N (x 0))
          (finCongr (hmq.trans
            (OneDimensionalDiscrepancy.card_negativeOrbitFinset hu N (x 0)).symm) j) by
      funext j
      exact orderedOrbitSamples_eq_orderedRepresentatives hu hv x hmq 0 j]
    exact hasIntervalDiscrepancy_finCongr _ _ _
      (CircleOrdering.orderedRepresentatives_hasIntervalDiscrepancy huNonempty)
  · change ProductGrid.HasIntervalDiscrepancy
      (ProductOrbit.orderedOrbitSamples u v x
        (orderedOrbitIndexEquiv hu (x 0) hmq)
        (orderedOrbitIndexEquiv hv (x 1) hmq) 1)
      (2 * OneDimensionalDiscrepancy.intervalDiscrepancy
        (OneDimensionalDiscrepancy.negativeOrbitFinset v N (x 1)))
    rw [show ProductOrbit.orderedOrbitSamples u v x
        (orderedOrbitIndexEquiv hu (x 0) hmq)
        (orderedOrbitIndexEquiv hv (x 1) hmq) 1 =
        fun j ↦ CircleOrdering.orderedRepresentatives
          (OneDimensionalDiscrepancy.negativeOrbitFinset v N (x 1))
          (finCongr (hmq.trans
            (OneDimensionalDiscrepancy.card_negativeOrbitFinset hv N (x 1)).symm) j) by
      funext j
      exact orderedOrbitSamples_eq_orderedRepresentatives hu hv x hmq 1 j]
    exact hasIntervalDiscrepancy_finCongr _ _ _
      (CircleOrdering.orderedRepresentatives_hasIntervalDiscrepancy hvNonempty)

/-! ## The concrete product-grid estimate at one scale -/

theorem quotientPoint_eq_quotientMap_pointToPlane (y : ProductGrid.Point 2) :
    ProductOrbit.quotientPoint y =
      TorusTransfer.quotientMap (Geometry.pointToPlane y) := rfl

theorem quotientPoint_mem_torusDisk_iff {y : ProductGrid.Point 2}
    (hy : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1) :
    ProductOrbit.quotientPoint y ∈ ConcreteSets.torusDisk ↔
      Geometry.pointToPlane y ∈ ConcreteSets.embeddedDisk := by
  rw [ConcreteSets.mem_torusDisk_iff_representative_mem,
    quotientPoint_eq_quotientMap_pointToPlane,
    TorusTransfer.representative_quotientMap_of_mem]
  exact hy

theorem quotientPoint_mem_torusSquare_iff {y : ProductGrid.Point 2}
    (hy : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1) :
    ProductOrbit.quotientPoint y ∈ ConcreteSets.torusSquare ↔
      Geometry.pointToPlane y ∈ ConcreteSets.embeddedSquare := by
  rw [ConcreteSets.mem_torusSquare_iff_representative_mem,
    quotientPoint_eq_quotientMap_pointToPlane,
    TorusTransfer.representative_quotientMap_of_mem]
  exact hy

/-- At a factored scale, one-dimensional discrepancy at most `Δ/2` in both
coordinates gives the concrete two-dimensional estimate with boundary
exponent `3/4`. -/
theorem concrete_product_discrepancy_at_scale
    {n q N : ℕ} (hn : 0 < n) (hq : 0 < q)
    (hmq : (4 * n) * q = N ^ ProductOrbit.coordinateDimension)
    (hmesh : 625 ≤ 4 * n)
    {u v : Fin ProductOrbit.coordinateDimension → Circle}
    (hu : FreeTuple.CircleFree u) (hv : FreeTuple.CircleFree v)
    (Δ : ℝ) (hΔpos : 0 < Δ)
    (hscale : 1 / (2 * ((4 * n : ℕ) : ℝ)) ≤ Δ)
    (hΔupper : Δ ≤ 1 / ((4 * n : ℕ) : ℝ))
    (huDisc : ∀ z : Circle,
      OneDimensionalDiscrepancy.intervalDiscrepancy
        (OneDimensionalDiscrepancy.negativeOrbitFinset u N z) ≤ Δ / 2)
    (hvDisc : ∀ z : Circle,
      OneDimensionalDiscrepancy.intervalDiscrepancy
        (OneDimensionalDiscrepancy.negativeOrbitFinset v N z) ≤ Δ / 2) :
    ∀ x : TorusAction.Torus 2,
      |TorusAction.cubeDensity (ProductOrbit.productGenerators u v)
          ConcreteSets.torusDisk N x - ConcreteSets.embeddedMass| ≤
        (2 : ℝ) ^ (3 / 4 : ℝ) * (3 : ℝ) ^ (2 : ℕ) * Δ ^ (3 / 4 : ℝ) ∧
      |TorusAction.cubeDensity (ProductOrbit.productGenerators u v)
          ConcreteSets.torusSquare N x - ConcreteSets.embeddedMass| ≤
        (2 : ℝ) ^ (3 / 4 : ℝ) * (3 : ℝ) ^ (2 : ℕ) * Δ ^ (3 / 4 : ℝ) := by
  classical
  intro x
  let e₀ : Fin ((4 * n) * q) ≃
      (Fin ProductOrbit.coordinateDimension → Fin N) :=
    orderedOrbitIndexEquiv hu (x 0) hmq
  let e₁ : Fin ((4 * n) * q) ≃
      (Fin ProductOrbit.coordinateDimension → Fin N) :=
    orderedOrbitIndexEquiv hv (x 1) hmq
  let samples : Fin 2 → Fin ((4 * n) * q) → ℝ :=
    ProductOrbit.orderedOrbitSamples u v x e₀ e₁
  have hsamplesMono : ∀ i, StrictMono (samples i) := by
    exact strictMono_orderedOrbitSamples hu hv x hmq
  have hsamplesIco : ∀ i j, samples i j ∈ Set.Ico (0 : ℝ) 1 := by
    exact orderedOrbitSamples_mem_Ico hu hv x hmq
  have hN : 0 < N := by
    by_contra h
    have hzero : N = 0 := Nat.eq_zero_of_not_pos h
    subst N
    norm_num [ProductOrbit.coordinateDimension] at hmq
    omega
  have hsamplesDisc : ∀ i,
      ProductGrid.HasIntervalDiscrepancy (samples i) Δ := by
    intro i
    apply hasIntervalDiscrepancy_mono
      (orderedOrbitSamples_hasIntervalDiscrepancy hu hv
        hN x hmq i)
    fin_cases i
    · have h := huDisc (x 0)
      norm_num
      linarith
    · have h := hvDisc (x 1)
      norm_num
      linarith
  have hclose (p : ProductGrid.FineIndex 2 (4 * n) q)
      (y : ProductGrid.Point 2)
      (hy : ∀ i, |y i - ProductGrid.regularGridPoint p i| ≤ Δ) :
      ∀ i, |y i - ProductGrid.regularGridPoint p i| ≤
        1 / (((4 * n : ℕ) : ℝ)) := by
    intro i
    exact (hy i).trans hΔupper
  have hsamplePointIco (p : ProductGrid.FineIndex 2 (4 * n) q) :
      ∀ i, ProductGrid.samplePoint samples p i ∈ Set.Ico (0 : ℝ) 1 := by
    intro i
    exact hsamplesIco i _
  have hdiskGrid :
      |ProductGrid.normalizedFineCount
          (fun p : ProductGrid.FineIndex 2 (4 * n) q ↦
            Geometry.pointToPlane (ProductGrid.samplePoint samples p) ∈
              ConcreteSets.embeddedDisk) - ConcreteSets.embeddedMass| ≤
        (2 : ℝ) ^ (3 / 4 : ℝ) * (3 : ℝ) ^ (2 : ℕ) * Δ ^ (3 / 4 : ℝ) := by
    apply ProductGrid.productGridDiscrepancy_of_intervalDiscrepancy
      (Nat.mul_pos (by norm_num) hn) hq
      (Geometry.torusEmbedUnitDiskCover (4 * n) (Nat.mul_pos (by norm_num) hn))
      samples (Geometry.pointToPlane ⁻¹' ConcreteSets.embeddedDisk)
      Δ (3 / 4 : ℝ) ConcreteSets.embeddedMass hΔpos (by norm_num) hscale
      hsamplesMono hsamplesIco hsamplesDisc
    · intro p hp y hy
      exact Geometry.robustBoundaryGridCover_lower_stable
        (Nat.mul_pos (by norm_num) hn) hq
        Geometry.frontier_torusEmbed_unitDisk_subset_fundamentalCube
        p hp y (hclose p y hy)
    · intro p y hyE hy
      exact Geometry.robustBoundaryGridCover_upper_stable
        (Nat.mul_pos (by norm_num) hn) hq
        Geometry.frontier_torusEmbed_unitDisk_subset_fundamentalCube
        p y hyE (hclose p y hy)
    · simpa [ConcreteSets.embeddedMass] using
        Geometry.torusEmbedUnitDiskCover_lower_mass_le
          (4 * n) (Nat.mul_pos (by norm_num) hn)
    · simpa [ConcreteSets.embeddedMass] using
        Geometry.torusEmbedUnitDiskCover_mass_le_upper
          (4 * n) (Nat.mul_pos (by norm_num) hn)
    · exact Geometry.torusEmbedUnitDiskCover_hasBoundaryGridCount_three_fourths
        hn hmesh
  have hsquareGrid :
      |ProductGrid.normalizedFineCount
          (fun p : ProductGrid.FineIndex 2 (4 * n) q ↦
            Geometry.pointToPlane (ProductGrid.samplePoint samples p) ∈
              ConcreteSets.embeddedSquare) - ConcreteSets.embeddedMass| ≤
        (2 : ℝ) ^ (3 / 4 : ℝ) * (3 : ℝ) ^ (2 : ℕ) * Δ ^ (3 / 4 : ℝ) := by
    apply ProductGrid.productGridDiscrepancy_of_intervalDiscrepancy
      (Nat.mul_pos (by norm_num) hn) hq
      (Geometry.torusEmbedEqualAreaSquareCover
        (4 * n) (Nat.mul_pos (by norm_num) hn))
      samples (Geometry.pointToPlane ⁻¹' ConcreteSets.embeddedSquare)
      Δ (3 / 4 : ℝ) ConcreteSets.embeddedMass hΔpos (by norm_num) hscale
      hsamplesMono hsamplesIco hsamplesDisc
    · intro p hp y hy
      exact Geometry.robustBoundaryGridCover_lower_stable
        (Nat.mul_pos (by norm_num) hn) hq
        Geometry.frontier_torusEmbed_equalAreaSquare_subset_fundamentalCube
        p hp y (hclose p y hy)
    · intro p y hyE hy
      exact Geometry.robustBoundaryGridCover_upper_stable
        (Nat.mul_pos (by norm_num) hn) hq
        Geometry.frontier_torusEmbed_equalAreaSquare_subset_fundamentalCube
        p y hyE (hclose p y hy)
    · simpa [ConcreteSets.embeddedMass] using
        Geometry.torusEmbedEqualAreaSquareCover_lower_mass_le
          (4 * n) (Nat.mul_pos (by norm_num) hn)
    · simpa [ConcreteSets.embeddedMass] using
        Geometry.torusEmbedEqualAreaSquareCover_mass_le_upper
          (4 * n) (Nat.mul_pos (by norm_num) hn)
    · exact
        Geometry.torusEmbedEqualAreaSquareCover_hasBoundaryGridCount_three_fourths
          hn hmesh
  constructor
  · rw [ProductOrbit.cubeDensity_eq_normalizedFineCount u v
      ConcreteSets.torusDisk x e₀ e₁]
    have hcount :
        ProductGrid.normalizedFineCount
            (fun p : ProductGrid.FineIndex 2 (4 * n) q ↦
              ProductOrbit.quotientPoint (ProductGrid.samplePoint samples p) ∈
                ConcreteSets.torusDisk) =
          ProductGrid.normalizedFineCount
            (fun p : ProductGrid.FineIndex 2 (4 * n) q ↦
              Geometry.pointToPlane (ProductGrid.samplePoint samples p) ∈
                ConcreteSets.embeddedDisk) := by
      have hf :
          (Finset.univ.filter fun p : ProductGrid.FineIndex 2 (4 * n) q ↦
            ProductOrbit.quotientPoint (ProductGrid.samplePoint samples p) ∈
              ConcreteSets.torusDisk) =
            (Finset.univ.filter fun p : ProductGrid.FineIndex 2 (4 * n) q ↦
              Geometry.pointToPlane (ProductGrid.samplePoint samples p) ∈
                ConcreteSets.embeddedDisk) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact quotientPoint_mem_torusDisk_iff (hsamplePointIco p)
      simp only [ProductGrid.normalizedFineCount, hf]
    change |ProductGrid.normalizedFineCount
      (fun p : ProductGrid.FineIndex 2 (4 * n) q ↦
        ProductOrbit.quotientPoint (ProductGrid.samplePoint samples p) ∈
          ConcreteSets.torusDisk) - ConcreteSets.embeddedMass| ≤ _
    rw [hcount]
    exact hdiskGrid
  · rw [ProductOrbit.cubeDensity_eq_normalizedFineCount u v
      ConcreteSets.torusSquare x e₀ e₁]
    have hcount :
        ProductGrid.normalizedFineCount
            (fun p : ProductGrid.FineIndex 2 (4 * n) q ↦
              ProductOrbit.quotientPoint (ProductGrid.samplePoint samples p) ∈
                ConcreteSets.torusSquare) =
          ProductGrid.normalizedFineCount
            (fun p : ProductGrid.FineIndex 2 (4 * n) q ↦
              Geometry.pointToPlane (ProductGrid.samplePoint samples p) ∈
                ConcreteSets.embeddedSquare) := by
      have hf :
          (Finset.univ.filter fun p : ProductGrid.FineIndex 2 (4 * n) q ↦
            ProductOrbit.quotientPoint (ProductGrid.samplePoint samples p) ∈
              ConcreteSets.torusSquare) =
            (Finset.univ.filter fun p : ProductGrid.FineIndex 2 (4 * n) q ↦
              Geometry.pointToPlane (ProductGrid.samplePoint samples p) ∈
                ConcreteSets.embeddedSquare) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact quotientPoint_mem_torusSquare_iff (hsamplePointIco p)
      simp only [ProductGrid.normalizedFineCount, hf]
    change |ProductGrid.normalizedFineCount
      (fun p : ProductGrid.FineIndex 2 (4 * n) q ↦
        ProductOrbit.quotientPoint (ProductGrid.samplePoint samples p) ∈
          ConcreteSets.torusSquare) - ConcreteSets.embeddedMass| ≤ _
    rw [hcount]
    exact hsquareGrid

/-! ## Dyadic parameter arithmetic -/

/-- The block parameter `n` for a mesh `4*n` at dyadic scale `t`.  The
fixed exponent `S` absorbs the one-dimensional discrepancy constant. -/
def dyadicMeshBlock (S t : ℕ) : ℕ := 2 ^ (2 * t - S - 2)

/-- The complementary within-cell factor, chosen so that the product has
exactly `(2^t)^32` points. -/
def dyadicFineFactor (S t : ℕ) : ℕ := 2 ^ (30 * t + S)

lemma four_mul_dyadicMeshBlock_eq (S t : ℕ) (hS : S + 2 ≤ 2 * t) :
    4 * dyadicMeshBlock S t = 2 ^ (2 * t - S) := by
  rw [dyadicMeshBlock, show 4 = 2 ^ 2 by norm_num, ← pow_add]
  congr 1
  omega

lemma dyadic_mesh_factorization (S t : ℕ) (hS : S + 2 ≤ 2 * t) :
    (4 * dyadicMeshBlock S t) * dyadicFineFactor S t =
      (2 ^ t) ^ ProductOrbit.coordinateDimension := by
  rw [four_mul_dyadicMeshBlock_eq S t hS, dyadicFineFactor, ← pow_add,
    ← pow_mul]
  congr 1
  norm_num [ProductOrbit.coordinateDimension]
  omega

lemma dyadic_mesh_mul_fixedScale (S t : ℕ) (hS : S + 2 ≤ 2 * t) :
    (4 * dyadicMeshBlock S t) * 2 ^ S = (2 ^ t) ^ 2 := by
  rw [four_mul_dyadicMeshBlock_eq S t hS, ← pow_add, ← pow_mul]
  congr 1
  omega

lemma dyadicMeshBlock_pos (S t : ℕ) : 0 < dyadicMeshBlock S t := by
  unfold dyadicMeshBlock
  positivity

lemma dyadicFineFactor_pos (S t : ℕ) : 0 < dyadicFineFactor S t := by
  unfold dyadicFineFactor
  positivity

lemma dyadic_mesh_ge_625 (S t : ℕ) (hS : S + 10 ≤ 2 * t) :
    625 ≤ 4 * dyadicMeshBlock S t := by
  rw [four_mul_dyadicMeshBlock_eq S t (by omega)]
  calc
    625 ≤ 2 ^ 10 := by norm_num
    _ ≤ 2 ^ (2 * t - S) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)

lemma oneDimensional_error_le_half_mesh
    (K : ℝ) (S t : ℕ) (hK : 2 * K ≤ ((2 ^ S : ℕ) : ℝ))
    (hS : S + 2 ≤ 2 * t) :
    K * (((2 ^ t : ℕ) : ℝ) ^ (-(2 : ℝ))) ≤
      (1 / (((4 * dyadicMeshBlock S t : ℕ) : ℝ))) / 2 := by
  have hmeshPos : (0 : ℝ) < ((4 * dyadicMeshBlock S t : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by norm_num) (dyadicMeshBlock_pos S t)
  have hNPos : (0 : ℝ) < ((2 ^ t : ℕ) : ℝ) := by positivity
  have hscalePos : (0 : ℝ) < ((2 ^ S : ℕ) : ℝ) := by positivity
  have hmul :
      ((4 * dyadicMeshBlock S t : ℕ) : ℝ) * ((2 ^ S : ℕ) : ℝ) =
        ((2 ^ t : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast dyadic_mesh_mul_fixedScale S t hS
  rw [Real.rpow_neg hNPos.le, Real.rpow_two]
  change K / (((2 ^ t : ℕ) : ℝ) ^ 2) ≤
    1 / ((4 * dyadicMeshBlock S t : ℕ) : ℝ) / 2
  rw [div_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos hNPos)
    (mul_pos hmeshPos (by norm_num))).2
  have hbound := mul_le_mul_of_nonneg_left hK hmeshPos.le
  nlinarith

lemma mesh_error_rpow_eq_dyadic_decay (S t : ℕ)
    (hS : S + 2 ≤ 2 * t) :
    (1 / (((4 * dyadicMeshBlock S t : ℕ) : ℝ))) ^ (3 / 4 : ℝ) =
      (((2 ^ S : ℕ) : ℝ) ^ (3 / 4 : ℝ)) *
        (((2 ^ t : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
  have hmeshPos : (0 : ℝ) < ((4 * dyadicMeshBlock S t : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by norm_num) (dyadicMeshBlock_pos S t)
  have hNPos : (0 : ℝ) < ((2 ^ t : ℕ) : ℝ) := by positivity
  have hscalePos : (0 : ℝ) < ((2 ^ S : ℕ) : ℝ) := by positivity
  have hmul :
      ((4 * dyadicMeshBlock S t : ℕ) : ℝ) * ((2 ^ S : ℕ) : ℝ) =
        ((2 ^ t : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast dyadic_mesh_mul_fixedScale S t hS
  have hinv :
      1 / ((4 * dyadicMeshBlock S t : ℕ) : ℝ) =
        ((2 ^ S : ℕ) : ℝ) / (((2 ^ t : ℕ) : ℝ) ^ 2) := by
    field_simp
    nlinarith
  rw [hinv, Real.div_rpow hscalePos.le (sq_nonneg _)]
  have hden :
      ((((2 ^ t : ℕ) : ℝ) ^ 2) ^ (3 / 4 : ℝ)) =
        (((2 ^ t : ℕ) : ℝ) ^ (3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNPos.le]
    norm_num
  rw [hden, Real.rpow_neg hNPos.le]
  ring

theorem productCircleFree_of_freeTuple
    {u : Fin ProductOrbit.coordinateDimension → Circle}
    (hu : FreeTuple.CircleFree u) : ProductOrbit.CircleFree u := by
  intro a b hab
  apply hu
  simpa [ProductOrbit.circleDisplacement, FreeTuple.circleDisplacement] using hab

/-- The dyadic specialization of the product-grid estimate.  Its hypotheses
are precisely the uniform `N⁻²` one-dimensional conclusions supplied by the
Fejér/Erdős--Turán argument. -/
theorem exists_eventual_concrete_dyadic_discrepancy_of_oneDimensional
    {u v : Fin ProductOrbit.coordinateDimension → Circle}
    (hu : FreeTuple.CircleFree u) (hv : FreeTuple.CircleFree v)
    (Ku Kv : ℝ) (hKu : 0 < Ku) (hKv : 0 < Kv)
    (huDisc : ∀ N : ℕ, 0 < N → ∀ z : Circle,
      OneDimensionalDiscrepancy.intervalDiscrepancy
        (OneDimensionalDiscrepancy.negativeOrbitFinset u N z) ≤
          Ku * (N : ℝ) ^ (-(2 : ℝ)))
    (hvDisc : ∀ N : ℕ, 0 < N → ∀ z : Circle,
      OneDimensionalDiscrepancy.intervalDiscrepancy
        (OneDimensionalDiscrepancy.negativeOrbitFinset v N z) ≤
          Kv * (N : ℝ) ^ (-(2 : ℝ))) :
    ∃ (q₀ : ℕ) (K : ℝ), 0 < q₀ ∧ 0 < K ∧
      ∀ t : ℕ, q₀ ≤ t → ∀ x : TorusAction.Torus 2,
        |TorusAction.cubeDensity (ProductOrbit.productGenerators u v)
            ConcreteSets.torusDisk (2 ^ t) x - ConcreteSets.embeddedMass| ≤
          K * (((2 ^ t : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ∧
        |TorusAction.cubeDensity (ProductOrbit.productGenerators u v)
            ConcreteSets.torusSquare (2 ^ t) x - ConcreteSets.embeddedMass| ≤
          K * (((2 ^ t : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
  let K₀ : ℝ := max Ku Kv
  have hK₀ : 0 < K₀ := hKu.trans_le (le_max_left _ _)
  have hpow : Tendsto (fun S : ℕ ↦ (2 : ℝ) ^ S) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨S, hS⟩ : ∃ S : ℕ, 2 * K₀ ≤ (2 : ℝ) ^ S := by
    obtain ⟨S, hS⟩ := (eventually_atTop.1 (hpow.eventually_ge_atTop (2 * K₀)))
    exact ⟨S, hS S le_rfl⟩
  let C : ℝ := (2 : ℝ) ^ (3 / 4 : ℝ) * (3 : ℝ) ^ (2 : ℕ)
  let K : ℝ := C * ((2 ^ S : ℕ) : ℝ) ^ (3 / 4 : ℝ)
  refine ⟨S + 10, K, by omega, ?_, ?_⟩
  · dsimp [K, C]
    positivity
  · intro t ht x
    have hSt : S + 10 ≤ 2 * t := by omega
    have hSt2 : S + 2 ≤ 2 * t := by omega
    have hN : 0 < 2 ^ t := by positivity
    have hKuK₀ : Ku ≤ K₀ := le_max_left _ _
    have hKvK₀ : Kv ≤ K₀ := le_max_right _ _
    have hKmesh : 2 * K₀ ≤ (((2 ^ S : ℕ) : ℝ)) := by
      simpa using hS
    have huMesh : ∀ z : Circle,
        OneDimensionalDiscrepancy.intervalDiscrepancy
            (OneDimensionalDiscrepancy.negativeOrbitFinset u (2 ^ t) z) ≤
          (1 / (((4 * dyadicMeshBlock S t : ℕ) : ℝ))) / 2 := by
      intro z
      calc
        OneDimensionalDiscrepancy.intervalDiscrepancy
            (OneDimensionalDiscrepancy.negativeOrbitFinset u (2 ^ t) z) ≤
            Ku * (((2 ^ t : ℕ) : ℝ) ^ (-(2 : ℝ))) := huDisc _ hN z
        _ ≤ K₀ * (((2 ^ t : ℕ) : ℝ) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_right hKuK₀ (Real.rpow_nonneg (by positivity) _)
        _ ≤ (1 / (((4 * dyadicMeshBlock S t : ℕ) : ℝ))) / 2 :=
          oneDimensional_error_le_half_mesh K₀ S t hKmesh hSt2
    have hvMesh : ∀ z : Circle,
        OneDimensionalDiscrepancy.intervalDiscrepancy
            (OneDimensionalDiscrepancy.negativeOrbitFinset v (2 ^ t) z) ≤
          (1 / (((4 * dyadicMeshBlock S t : ℕ) : ℝ))) / 2 := by
      intro z
      calc
        OneDimensionalDiscrepancy.intervalDiscrepancy
            (OneDimensionalDiscrepancy.negativeOrbitFinset v (2 ^ t) z) ≤
            Kv * (((2 ^ t : ℕ) : ℝ) ^ (-(2 : ℝ))) := hvDisc _ hN z
        _ ≤ K₀ * (((2 ^ t : ℕ) : ℝ) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_right hKvK₀ (Real.rpow_nonneg (by positivity) _)
        _ ≤ (1 / (((4 * dyadicMeshBlock S t : ℕ) : ℝ))) / 2 :=
          oneDimensional_error_le_half_mesh K₀ S t hKmesh hSt2
    have hscale :
        1 / (2 * (((4 * dyadicMeshBlock S t : ℕ) : ℝ))) ≤
          1 / (((4 * dyadicMeshBlock S t : ℕ) : ℝ)) := by
      have hm : (0 : ℝ) < ((4 * dyadicMeshBlock S t : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_pos (by norm_num) (dyadicMeshBlock_pos S t)
      apply (div_le_div_iff₀ (mul_pos (by norm_num) hm) hm).2
      nlinarith
    have hproduct := concrete_product_discrepancy_at_scale
      (dyadicMeshBlock_pos S t) (dyadicFineFactor_pos S t)
      (dyadic_mesh_factorization S t hSt2) (dyadic_mesh_ge_625 S t hSt)
      hu hv (1 / (((4 * dyadicMeshBlock S t : ℕ) : ℝ)))
      (one_div_pos.mpr (by
        exact_mod_cast Nat.mul_pos (by norm_num) (dyadicMeshBlock_pos S t)))
      hscale le_rfl huMesh hvMesh x
    rw [mesh_error_rpow_eq_dyadic_decay S t hSt2] at hproduct
    simpa [K, C, mul_assoc] using hproduct

/-! ## Absorbing the finite initial range -/

lemma cubeCount_le_pow {d k : ℕ} (u : Fin d → TorusAction.Torus k)
    (E : Set (TorusAction.Torus k)) (N : ℕ) (x : TorusAction.Torus k) :
    TorusAction.cubeCount u E N x ≤ N ^ d := by
  classical
  let := TorusAction.torusAddAction u
  unfold TorusAction.cubeCount
  calc
    (∑ a : Fin d → Fin N,
        if (-Flow.cubeIndex a +ᵥ x) ∈ E then 1 else 0) ≤
        ∑ _a : Fin d → Fin N, 1 := by
      apply Finset.sum_le_sum
      intro a _
      split <;> omega
    _ = N ^ d := by simp [Fintype.card_fun, Fintype.card_fin]

lemma cubeDensity_mem_Icc {d k : ℕ} (u : Fin d → TorusAction.Torus k)
    (E : Set (TorusAction.Torus k)) {N : ℕ} (hN : 0 < N)
    (x : TorusAction.Torus k) :
    TorusAction.cubeDensity u E N x ∈ Set.Icc (0 : ℝ) 1 := by
  have hden : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  constructor
  · unfold TorusAction.cubeDensity
    positivity
  · rw [TorusAction.cubeDensity, div_le_one hden]
    exact_mod_cast cubeCount_le_pow u E N x

lemma concrete_density_error_le_two
    (u : Fin ProductOrbit.productDimension → TorusAction.Torus 2)
    (E : Set (TorusAction.Torus 2)) {N : ℕ} (hN : 0 < N)
    (x : TorusAction.Torus 2) :
    |TorusAction.cubeDensity u E N x - ConcreteSets.embeddedMass| ≤ 2 := by
  obtain ⟨hd0, hd1⟩ := cubeDensity_mem_Icc u E hN x
  have hm0 : 0 ≤ ConcreteSets.embeddedMass := ConcreteSets.embeddedMass_pos.le
  have hm1 : ConcreteSets.embeddedMass ≤ 1 := by
    unfold ConcreteSets.embeddedMass
    nlinarith [Real.pi_lt_four]
  rw [abs_le]
  constructor <;> linarith

/-- A power estimate beginning at `q₀` becomes uniform after enlarging its
constant by an explicit finite sum. -/
theorem exists_uniform_powerDecay_of_eventually
    {X : Type*} (f : ℕ → X → ℝ) (q₀ : ℕ) (K M δ : ℝ)
    (hK : 0 < K) (hM : 0 ≤ M) (hδ : 0 < δ)
    (heventual : ∀ q : ℕ, q₀ ≤ q → ∀ x : X,
      |f q x| ≤ K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)))
    (hinitial : ∀ q : ℕ, q < q₀ → ∀ x : X, |f q x| ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ x : X,
      |f q x| ≤ C * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)) := by
  let C : ℝ := K + (∑ q ∈ Finset.range q₀,
    M * ((((2 ^ q : ℕ) : ℝ)) ^ (1 + δ)))
  have hterm_nonneg : ∀ q : ℕ,
      0 ≤ M * ((((2 ^ q : ℕ) : ℝ)) ^ (1 + δ)) := by
    intro q
    exact mul_nonneg hM (Real.rpow_nonneg (by positivity) _)
  have hsum_nonneg : 0 ≤ ∑ q ∈ Finset.range q₀,
      M * ((((2 ^ q : ℕ) : ℝ)) ^ (1 + δ)) :=
    Finset.sum_nonneg fun q _ ↦ hterm_nonneg q
  have hC : 0 < C := lt_of_lt_of_le hK (le_add_of_nonneg_right hsum_nonneg)
  refine ⟨C, hC, fun q x ↦ ?_⟩
  by_cases hq : q₀ ≤ q
  · refine (heventual q hq x).trans ?_
    exact mul_le_mul_of_nonneg_right
      (show K ≤ C by exact le_add_of_nonneg_right hsum_nonneg)
      (Real.rpow_nonneg (by positivity) _)
  · have hq' : q < q₀ := Nat.lt_of_not_ge hq
    have hmem : q ∈ Finset.range q₀ := Finset.mem_range.mpr hq'
    have hterm_le_sum :
        M * ((((2 ^ q : ℕ) : ℝ)) ^ (1 + δ)) ≤
          ∑ r ∈ Finset.range q₀,
            M * ((((2 ^ r : ℕ) : ℝ)) ^ (1 + δ)) := by
      exact Finset.single_le_sum (fun r _ ↦ hterm_nonneg r) hmem
    have hterm_le_C :
        M * ((((2 ^ q : ℕ) : ℝ)) ^ (1 + δ)) ≤ C :=
      hterm_le_sum.trans (le_add_of_nonneg_left hK.le)
    have hmul := mul_le_mul_of_nonneg_right hterm_le_C
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ ((2 ^ q : ℕ) : ℝ))
        (-1 - δ))
    refine (hinitial q hq' x).trans ?_
    calc
      M = (M * ((((2 ^ q : ℕ) : ℝ)) ^ (1 + δ))) *
          ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)) := by
        rw [mul_assoc, ← Real.rpow_add (by positivity :
          (0 : ℝ) < ((2 ^ q : ℕ) : ℝ))]
        have hexp : (1 + δ) + (-1 - δ) = 0 := by ring
        rw [hexp, Real.rpow_zero, mul_one]
      _ ≤ C * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)) := hmul

/-- Uniform all-scale concrete discrepancy, conditional only on the two
one-dimensional `N⁻²` estimates. -/
theorem exists_uniform_concrete_dyadic_discrepancy_of_oneDimensional
    {u v : Fin ProductOrbit.coordinateDimension → Circle}
    (hu : FreeTuple.CircleFree u) (hv : FreeTuple.CircleFree v)
    (Ku Kv : ℝ) (hKu : 0 < Ku) (hKv : 0 < Kv)
    (huDisc : ∀ N : ℕ, 0 < N → ∀ z : Circle,
      OneDimensionalDiscrepancy.intervalDiscrepancy
        (OneDimensionalDiscrepancy.negativeOrbitFinset u N z) ≤
          Ku * (N : ℝ) ^ (-(2 : ℝ)))
    (hvDisc : ∀ N : ℕ, 0 < N → ∀ z : Circle,
      OneDimensionalDiscrepancy.intervalDiscrepancy
        (OneDimensionalDiscrepancy.negativeOrbitFinset v N z) ≤
          Kv * (N : ℝ) ^ (-(2 : ℝ))) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℕ, ∀ x : TorusAction.Torus 2,
      |TorusAction.cubeDensity (ProductOrbit.productGenerators u v)
          ConcreteSets.torusDisk (2 ^ t) x - ConcreteSets.embeddedMass| ≤
        K * (((2 ^ t : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ∧
      |TorusAction.cubeDensity (ProductOrbit.productGenerators u v)
          ConcreteSets.torusSquare (2 ^ t) x - ConcreteSets.embeddedMass| ≤
        K * (((2 ^ t : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨q₀, K₀, hq₀, hK₀, heventual⟩ :=
    exists_eventual_concrete_dyadic_discrepancy_of_oneDimensional
      hu hv Ku Kv hKu hKv huDisc hvDisc
  obtain ⟨Kd, hKd, hdbound⟩ := exists_uniform_powerDecay_of_eventually
    (fun t x ↦ TorusAction.cubeDensity (ProductOrbit.productGenerators u v)
      ConcreteSets.torusDisk (2 ^ t) x - ConcreteSets.embeddedMass)
    q₀ K₀ 2 (1 / 2 : ℝ) hK₀ (by norm_num) (by norm_num)
    (fun t ht x ↦ by simpa only [show (-(3 / 2 : ℝ)) = -1 - 1 / 2 by norm_num]
      using (heventual t ht x).1)
    (fun t _ht x ↦ concrete_density_error_le_two
      (ProductOrbit.productGenerators u v) ConcreteSets.torusDisk
      (by positivity) x)
  obtain ⟨Ks, hKs, hsbound⟩ := exists_uniform_powerDecay_of_eventually
    (fun t x ↦ TorusAction.cubeDensity (ProductOrbit.productGenerators u v)
      ConcreteSets.torusSquare (2 ^ t) x - ConcreteSets.embeddedMass)
    q₀ K₀ 2 (1 / 2 : ℝ) hK₀ (by norm_num) (by norm_num)
    (fun t ht x ↦ by simpa only [show (-(3 / 2 : ℝ)) = -1 - 1 / 2 by norm_num]
      using (heventual t ht x).2)
    (fun t _ht x ↦ concrete_density_error_le_two
      (ProductOrbit.productGenerators u v) ConcreteSets.torusSquare
      (by positivity) x)
  refine ⟨max Kd Ks, hKd.trans_le (le_max_left _ _), fun t x ↦ ?_⟩
  have hr : 0 ≤ (((2 ^ t : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.rpow_nonneg (by positivity) _
  constructor
  · have hd :
        |TorusAction.cubeDensity (ProductOrbit.productGenerators u v)
            ConcreteSets.torusDisk (2 ^ t) x - ConcreteSets.embeddedMass| ≤
          Kd * (((2 ^ t : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
      simpa only [show (-1 - 1 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num] using
        hdbound t x
    exact hd.trans (mul_le_mul_of_nonneg_right (le_max_left Kd Ks) hr)
  · have hs :
        |TorusAction.cubeDensity (ProductOrbit.productGenerators u v)
            ConcreteSets.torusSquare (2 ^ t) x - ConcreteSets.embeddedMass| ≤
          Ks * (((2 ^ t : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
      simpa only [show (-1 - 1 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num] using
        hsbound t x
    exact hs.trans (mul_le_mul_of_nonneg_right (le_max_right Kd Ks) hr)

/-- Reusing a free scalar tuple in both coordinate axes gives a free family
of sixty-four translations of the two-torus. -/
theorem free_productGenerators_self
    {u : Fin ProductOrbit.coordinateDimension → Circle}
    (hu : ProductOrbit.CircleFree u) :
    TorusAction.Free (ProductOrbit.productGenerators u u) :=
  ProductOrbit.free_productGenerators hu hu

/-- There is a free family of sixty-four translations of the two-torus for
which both the embedded disk and the equal-area square have uniform dyadic
common-mean discrepancy `O(N⁻³⁄²)`. -/
theorem exists_free_productGenerators_uniform_concrete_dyadic_discrepancy :
    ∃ (w : Fin ProductOrbit.productDimension → TorusAction.Torus 2) (K : ℝ),
      TorusAction.Free w ∧ 0 < K ∧
      ∀ t : ℕ, ∀ x : TorusAction.Torus 2,
        |TorusAction.cubeDensity w ConcreteSets.torusDisk (2 ^ t) x -
            ConcreteSets.embeddedMass| ≤
          K * (((2 ^ t : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ∧
        |TorusAction.cubeDensity w ConcreteSets.torusSquare (2 ^ t) x -
            ConcreteSets.embeddedMass| ≤
          K * (((2 ^ t : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨u, v, cu, cv, hu, hv, hcu, hcv, huProd, hvProd⟩ :=
    DiophantineChoice.exists_two_generators32_free_product_lower
  have huProd' : ∀ h : ℤ, h ≠ 0 →
      cu * |(h : ℝ)| ^ (-(3 : ℝ)) ≤
        OneDimensionalDiscrepancy.distanceProduct u h := by
    intro h hh
    simpa [DiophantineChoice.distanceProduct,
      OneDimensionalDiscrepancy.distanceProduct] using huProd h hh
  have hvProd' : ∀ h : ℤ, h ≠ 0 →
      cv * |(h : ℝ)| ^ (-(3 : ℝ)) ≤
        OneDimensionalDiscrepancy.distanceProduct v h := by
    intro h hh
    simpa [DiophantineChoice.distanceProduct,
      OneDimensionalDiscrepancy.distanceProduct] using hvProd h hh
  obtain ⟨Ku, hKu, huDisc⟩ :=
    OneDimensionalDiscrepancy.exists_uniform_intervalDiscrepancy_negativeOrbitFinset
      hu hcu huProd'
  obtain ⟨Kv, hKv, hvDisc⟩ :=
    OneDimensionalDiscrepancy.exists_uniform_intervalDiscrepancy_negativeOrbitFinset
      hv hcv hvProd'
  obtain ⟨K, hK, hboth⟩ :=
    exists_uniform_concrete_dyadic_discrepancy_of_oneDimensional
      hu hv Ku Kv hKu hKv huDisc hvDisc
  refine ⟨ProductOrbit.productGenerators u v, K, ?_, hK, ?_⟩
  · exact ProductOrbit.free_productGenerators
      (productCircleFree_of_freeTuple hu) (productCircleFree_of_freeTuple hv)
  · exact hboth

/-- The application-facing formulation, with the power saving written as
`N⁻¹⁻δ` for a positive exponent `δ`. -/
theorem exists_free_generators_uniform_concrete_dyadic_decay :
    ∃ (w : Fin ProductOrbit.productDimension → TorusAction.Torus 2)
      (K δ : ℝ), TorusAction.Free w ∧ 0 < K ∧ 0 < δ ∧
      ∀ t : ℕ, ∀ x : TorusAction.Torus 2,
        |TorusAction.cubeDensity w ConcreteSets.torusDisk (2 ^ t) x -
            ConcreteSets.embeddedMass| ≤
          K * (((2 ^ t : ℕ) : ℝ) ^ (-1 - δ)) ∧
        |TorusAction.cubeDensity w ConcreteSets.torusSquare (2 ^ t) x -
            ConcreteSets.embeddedMass| ≤
          K * (((2 ^ t : ℕ) : ℝ) ^ (-1 - δ)) := by
  obtain ⟨w, K, hw, hK, hbound⟩ :=
    exists_free_productGenerators_uniform_concrete_dyadic_discrepancy
  refine ⟨w, K, (1 / 2 : ℝ), hw, hK, by norm_num, ?_⟩
  intro t x
  simpa only [show (-1 - (1 / 2 : ℝ)) = -(3 / 2 : ℝ) by norm_num] using
    hbound t x

end

end Erdos1124.ConcreteDiscrepancy
