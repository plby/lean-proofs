import ErdosProblems.Erdos6.GenericCollision
import ErdosProblems.Erdos6.PrimeTuple
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Transporting the variational candidate to the powers-of-two tuple

The arithmetic sieve is indexed by the subtype of the shift finset, whereas
the certified variational integrals use `Fin largeK`.  Coordinate reindexing
is measure preserving.  A globally continuous clipped product agrees with
the rational product on the unit cube and is therefore the convenient test
function for the tuple-generic Riemann limit.
-/

namespace Erdos6.Maynard

open MeasureTheory Set
open scoped BigOperators

noncomputable section

def largeContinuousG (u : ℝ) : ℝ :=
  (1 + largeA * max u 0)⁻¹

def largeContinuousProduct (t : Fin largeK → ℝ) : ℝ :=
  ∏ i, largeContinuousG (largeK * t i)

def largeTupleContinuousProduct (t : largePowerTuple → ℝ) : ℝ :=
  ∏ h, largeContinuousG (largeK * t h)

noncomputable def largeTupleReindex :
    (largePowerTuple → ℝ) ≃ᵐ (Fin largeK → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin largeK => ℝ) largeTupleIndexEquiv

theorem largeTupleReindex_apply (t : largePowerTuple → ℝ) :
    largeTupleReindex t = fun i => t (largeTupleIndexEquiv.symm i) := by
  ext i
  simp [largeTupleReindex, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft_apply]

theorem continuous_largeContinuousG : Continuous largeContinuousG := by
  unfold largeContinuousG
  apply Continuous.inv₀
  · fun_prop
  · intro u
    have hnonneg : 0 ≤ largeA * max u 0 :=
      mul_nonneg largeA_pos.le (le_max_right _ _)
    linarith

theorem continuous_largeContinuousProduct :
    Continuous largeContinuousProduct := by
  unfold largeContinuousProduct
  simpa only [Function.comp_apply, Pi.mul_apply] using
    (continuous_finsetProd (Finset.univ : Finset (Fin largeK))
      (fun i hi => continuous_largeContinuousG.comp
        (continuous_const.mul (continuous_apply i))))

theorem continuous_reindex {ι κ : Type*}
    (e : ι ≃ κ) : Continuous (fun t : ι → ℝ => fun j => t (e.symm j)) := by
  exact continuous_pi fun j => continuous_apply (e.symm j)

theorem continuous_scaledCoordinateProduct {ι : Type*} [Fintype ι]
    {g : ℝ → ℝ} (hg : Continuous g) (c : ℝ) :
    Continuous (fun t : ι → ℝ => ∏ i, g (c * t i)) := by
  simpa only [Function.comp_apply, Pi.mul_apply] using
    (continuous_finsetProd (Finset.univ : Finset ι)
      (fun i hi => hg.comp (continuous_const.mul (continuous_apply i))))

theorem continuous_largeTupleContinuousProduct :
    Continuous largeTupleContinuousProduct := by
  unfold largeTupleContinuousProduct
  exact continuous_scaledCoordinateProduct continuous_largeContinuousG largeK

theorem largeTupleContinuousProduct_eq_reindex
    (t : largePowerTuple → ℝ) :
    largeTupleContinuousProduct t =
      largeContinuousProduct (fun i => t (largeTupleIndexEquiv.symm i)) := by
  unfold largeTupleContinuousProduct largeContinuousProduct
  exact (largeTupleIndexEquiv.symm.prod_comp
    (fun h => largeContinuousG (largeK * t h))).symm

theorem largeContinuousG_eq_largeG {u : ℝ} (hu : 0 ≤ u) :
    largeContinuousG u = largeG u := by
  simp [largeContinuousG, largeG, max_eq_left hu]

theorem largeContinuousProduct_eq_largeProduct_of_mem_cube
    {t : Fin largeK → ℝ}
    (ht : t ∈ BoundedGaps.Maynard.maynardCube largeK) :
    largeContinuousProduct t = largeProduct t := by
  unfold largeContinuousProduct largeProduct
  apply Finset.prod_congr rfl
  intro i hi
  exact largeContinuousG_eq_largeG
    (mul_nonneg (by positivity) (ht i (Set.mem_univ i)).1)

theorem largeTupleReindex_mem_simplex_iff
    {t : largePowerTuple → ℝ} :
    largeTupleReindex t ∈ BoundedGaps.Maynard.maynardSimplex largeK ↔
      t ∈ BoundedGaps.Maynard.finiteSimplexOf largePowerTuple := by
  constructor
  · intro ht
    constructor
    · rw [BoundedGaps.Maynard.maynardCubeOf, Set.mem_pi]
      intro h hh
      have hi := ht.1 (largeTupleIndexEquiv h) (Set.mem_univ _)
      simpa [largeTupleReindex_apply] using hi
    · have hsum :
          (∑ i : Fin largeK, largeTupleReindex t i) =
            ∑ h : largePowerTuple, t h := by
        simpa [largeTupleReindex_apply] using
          (largeTupleIndexEquiv.symm.sum_comp t)
      rw [← hsum]
      exact ht.2
  · intro ht
    constructor
    · rw [BoundedGaps.Maynard.maynardCube,
        BoundedGaps.Maynard.maynardCubeOf, Set.mem_pi]
      intro i hi
      have hh := ht.1 (largeTupleIndexEquiv.symm i) (Set.mem_univ _)
      simpa [largeTupleReindex_apply] using hh
    · have hsum :
          (∑ i : Fin largeK, largeTupleReindex t i) =
            ∑ h : largePowerTuple, t h := by
        simpa [largeTupleReindex_apply] using
          (largeTupleIndexEquiv.symm.sum_comp t)
      rw [hsum]
      exact ht.2

theorem largeTupleReindex_preimage_simplex :
    largeTupleReindex ⁻¹' BoundedGaps.Maynard.maynardSimplex largeK =
      BoundedGaps.Maynard.finiteSimplexOf largePowerTuple := by
  ext t
  exact largeTupleReindex_mem_simplex_iff

theorem largeTupleReindex_measurePreserving :
    MeasurePreserving largeTupleReindex volume volume := by
  exact MeasureTheory.volume_measurePreserving_piCongrLeft
    (fun _ : Fin largeK => ℝ) largeTupleIndexEquiv

theorem largeTupleContinuousProduct_eq_largeTupleCandidate_of_mem_simplex
    {t : largePowerTuple → ℝ}
    (ht : t ∈ BoundedGaps.Maynard.finiteSimplexOf largePowerTuple) :
    largeTupleContinuousProduct t = largeTupleCandidate t := by
  have hreindex := largeTupleReindex_mem_simplex_iff.mpr ht
  unfold largeTupleCandidate
  have hexplicit : (fun i => t (largeTupleIndexEquiv.symm i)) ∈
      BoundedGaps.Maynard.maynardSimplex largeK := by
    simpa only [largeTupleReindex_apply] using hreindex
  rw [largeTupleContinuousProduct_eq_reindex]
  rw [largeCandidate, if_pos hexplicit]
  exact largeContinuousProduct_eq_largeProduct_of_mem_cube hexplicit.1

theorem largeCandidate_eq_largeProduct_of_mem_simplex
    {t : Fin largeK → ℝ}
    (ht : t ∈ BoundedGaps.Maynard.maynardSimplex largeK) :
    largeCandidate t = largeProduct t := by
  simp only [largeCandidate, if_pos ht]

theorem largeTupleContinuousProduct_nonneg_of_mem_simplex
    {t : largePowerTuple → ℝ}
    (ht : t ∈ BoundedGaps.Maynard.finiteSimplexOf largePowerTuple) :
    0 ≤ largeTupleContinuousProduct t := by
  rw [largeTupleContinuousProduct_eq_largeTupleCandidate_of_mem_simplex ht]
  exact largeCandidate_nonneg _

theorem largeTupleContinuousProduct_le_one_of_mem_simplex
    {t : largePowerTuple → ℝ}
    (ht : t ∈ BoundedGaps.Maynard.finiteSimplexOf largePowerTuple) :
    largeTupleContinuousProduct t ≤ 1 := by
  rw [largeTupleContinuousProduct_eq_largeTupleCandidate_of_mem_simplex ht]
  exact largeCandidate_le_one _

theorem largeTupleContinuousProduct_sq_bounds
    (t : largePowerTuple → ℝ)
    (ht : t ∈ BoundedGaps.Maynard.finiteSimplexOf largePowerTuple) :
    0 ≤ largeTupleContinuousProduct t ^ 2 ∧
      largeTupleContinuousProduct t ^ 2 ≤ 1 := by
  have hnonneg := largeTupleContinuousProduct_nonneg_of_mem_simplex ht
  have hle := largeTupleContinuousProduct_le_one_of_mem_simplex ht
  exact ⟨sq_nonneg _, pow_le_one₀ hnonneg hle⟩

theorem integral_largeTupleContinuousProduct_sq_eq_maynardI :
    (∫ t in BoundedGaps.Maynard.finiteSimplexOf largePowerTuple,
      largeTupleContinuousProduct t ^ 2) =
      BoundedGaps.Maynard.maynardI largeK largeCandidate := by
  have htransport := largeTupleReindex_measurePreserving.setIntegral_preimage_emb
    largeTupleReindex.measurableEmbedding
    (fun s : Fin largeK → ℝ => largeContinuousProduct s ^ 2)
    (BoundedGaps.Maynard.maynardSimplex largeK)
  rw [largeTupleReindex_preimage_simplex] at htransport
  have hleft :
      (fun t : largePowerTuple → ℝ =>
        largeContinuousProduct (largeTupleReindex t) ^ 2) =
      fun t => largeTupleContinuousProduct t ^ 2 := by
    funext t
    rw [largeTupleReindex_apply]
    exact congrArg (fun x : ℝ => x ^ 2)
      (largeTupleContinuousProduct_eq_reindex t).symm
  rw [hleft] at htransport
  rw [htransport]
  have hsimplex : BoundedGaps.Maynard.maynardSimplex largeK ⊆
      BoundedGaps.Maynard.maynardCube largeK := fun _ ht => ht.1
  have hcubeMeas := BoundedGaps.Maynard.maynardCube_measurable largeK
  have hrestrict :
      (∫ t in BoundedGaps.Maynard.maynardCube largeK,
        largeCandidate t ^ 2) =
      ∫ t in BoundedGaps.Maynard.maynardSimplex largeK,
        largeCandidate t ^ 2 := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      hcubeMeas hsimplex
    intro t ht
    simp [largeCandidate, ht.2]
  unfold BoundedGaps.Maynard.maynardI
  rw [hrestrict]
  apply MeasureTheory.setIntegral_congr_fun
    (BoundedGaps.Maynard.maynardSimplex_measurable (k := largeK))
  intro t ht
  change largeContinuousProduct t ^ 2 = largeCandidate t ^ 2
  rw [largeCandidate_eq_largeProduct_of_mem_simplex ht,
    largeContinuousProduct_eq_largeProduct_of_mem_cube ht.1]

end

end Erdos6.Maynard
