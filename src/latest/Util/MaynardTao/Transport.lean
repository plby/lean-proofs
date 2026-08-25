/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Util.MaynardTao.Assembly
import ErdosProblems.Erdos4.Base

/-!
# Transporting the variable Maynard candidate to an arbitrary tuple

The variational family in the mirrored Erdős 4 development is indexed by
Fin K.  The arithmetic sieve is indexed by the subtype of the actual finite
shift set.  Coordinate permutation preserves both the simplex and volume.
-/

namespace MaynardTao

open Filter Set MeasureTheory
open scoped BigOperators

noncomputable section

noncomputable def tupleIndexEquiv (H : Finset ℕ) :
    H ≃ Fin H.card :=
  Fintype.equivFinOfCardEq (by simp)

noncomputable def tupleReindex (H : Finset ℕ) :
    (H → ℝ) ≃ᵐ (Fin H.card → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin H.card => ℝ)
    (tupleIndexEquiv H)

theorem tupleReindex_apply (H : Finset ℕ) (t : H → ℝ) :
    tupleReindex H t =
      fun i => t ((tupleIndexEquiv H).symm i) := by
  ext i
  simp [tupleReindex, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft_apply]

noncomputable def tupleVariableCandidate
    (H : Finset ℕ) (A : ℝ) (t : H → ℝ) : ℝ :=
  Erdos4.VariableMaynard.candidate H.card A (tupleReindex H t)

noncomputable def tupleVariableContinuousProduct
    (H : Finset ℕ) (A : ℝ) (t : H → ℝ) : ℝ :=
  ∏ h, Erdos4.variableContinuousFactor A ((H.card : ℝ) * t h)

theorem continuous_tupleVariableContinuousProduct
    {H : Finset ℕ} {A : ℝ} (hA : 0 < A) :
    Continuous (tupleVariableContinuousProduct H A) := by
  unfold tupleVariableContinuousProduct
  exact Erdos6.Maynard.continuous_scaledCoordinateProduct
    (Erdos4.continuous_variableContinuousFactor hA) H.card

theorem tupleReindex_mem_simplex_iff
    {H : Finset ℕ} {t : H → ℝ} :
    tupleReindex H t ∈ BoundedGaps.Maynard.maynardSimplex H.card ↔
      t ∈ BoundedGaps.Maynard.finiteSimplexOf H := by
  constructor
  · intro ht
    constructor
    · rw [BoundedGaps.Maynard.maynardCubeOf, Set.mem_pi]
      intro h hh
      have hi := ht.1 (tupleIndexEquiv H h) (Set.mem_univ _)
      simpa [tupleReindex_apply] using hi
    · have hsum :
          (∑ i : Fin H.card, tupleReindex H t i) =
            ∑ h : H, t h := by
        simpa [tupleReindex_apply] using
          ((tupleIndexEquiv H).symm.sum_comp t)
      rw [← hsum]
      exact ht.2
  · intro ht
    constructor
    · rw [BoundedGaps.Maynard.maynardCube,
        BoundedGaps.Maynard.maynardCubeOf, Set.mem_pi]
      intro i hi
      have hh := ht.1 ((tupleIndexEquiv H).symm i) (Set.mem_univ _)
      simpa [tupleReindex_apply] using hh
    · have hsum :
          (∑ i : Fin H.card, tupleReindex H t i) =
            ∑ h : H, t h := by
        simpa [tupleReindex_apply] using
          ((tupleIndexEquiv H).symm.sum_comp t)
      rw [hsum]
      exact ht.2

theorem tupleReindex_preimage_simplex (H : Finset ℕ) :
    tupleReindex H ⁻¹'
        BoundedGaps.Maynard.maynardSimplex H.card =
      BoundedGaps.Maynard.finiteSimplexOf H := by
  ext t
  exact tupleReindex_mem_simplex_iff

theorem tupleReindex_measurePreserving (H : Finset ℕ) :
    MeasurePreserving (tupleReindex H) volume volume := by
  exact MeasureTheory.volume_measurePreserving_piCongrLeft
    (fun _ : Fin H.card => ℝ) (tupleIndexEquiv H)

theorem tupleVariableContinuousProduct_eq_candidate_of_mem_simplex
    {H : Finset ℕ} {A : ℝ} {t : H → ℝ}
    (ht : t ∈ BoundedGaps.Maynard.finiteSimplexOf H) :
    tupleVariableContinuousProduct H A t =
      tupleVariableCandidate H A t := by
  have hreindex := tupleReindex_mem_simplex_iff.mpr ht
  unfold tupleVariableCandidate Erdos4.VariableMaynard.candidate
  rw [if_pos hreindex]
  rw [tupleReindex_apply]
  unfold tupleVariableContinuousProduct Erdos4.VariableMaynard.product
  calc
    (∏ h : H,
        Erdos4.variableContinuousFactor A ((H.card : ℝ) * t h)) =
        ∏ h : H,
          Erdos4.VariableMaynard.factor A ((H.card : ℝ) * t h) := by
      apply Finset.prod_congr rfl
      intro h _
      rw [Erdos4.variableContinuousFactor_eq_factor]
      exact mul_nonneg (Nat.cast_nonneg _) (ht.1 h (Set.mem_univ h)).1
    _ = ∏ i : Fin H.card,
        Erdos4.VariableMaynard.factor A
          ((H.card : ℝ) * t ((tupleIndexEquiv H).symm i)) := by
      exact ((tupleIndexEquiv H).symm.prod_comp
        (fun h => Erdos4.VariableMaynard.factor A
          ((H.card : ℝ) * t h))).symm

theorem tupleVariableContinuousProduct_sq_bounds
    {H : Finset ℕ} {A : ℝ} (hA : 0 < A)
    (t : H → ℝ)
    (ht : t ∈ BoundedGaps.Maynard.finiteSimplexOf H) :
    0 ≤ tupleVariableContinuousProduct H A t ^ 2 ∧
      tupleVariableContinuousProduct H A t ^ 2 ≤ 1 := by
  rw [tupleVariableContinuousProduct_eq_candidate_of_mem_simplex ht]
  have hnonneg := Erdos4.VariableMaynard.candidate_nonneg hA (tupleReindex H t)
  have hle := Erdos4.VariableMaynard.candidate_le_one hA (tupleReindex H t)
  exact ⟨sq_nonneg _, pow_le_one₀ hnonneg hle⟩

theorem integral_tupleVariableContinuousProduct_sq_eq_maynardI
    {H : Finset ℕ} {A : ℝ} :
    (∫ t in BoundedGaps.Maynard.finiteSimplexOf H,
      tupleVariableContinuousProduct H A t ^ 2) =
      BoundedGaps.Maynard.maynardI H.card
        (Erdos4.VariableMaynard.candidate H.card A) := by
  have htransport := (tupleReindex_measurePreserving H).setIntegral_preimage_emb
    (tupleReindex H).measurableEmbedding
    (fun s : Fin H.card → ℝ =>
      Erdos4.variableContinuousProduct H.card A s ^ 2)
    (BoundedGaps.Maynard.maynardSimplex H.card)
  rw [tupleReindex_preimage_simplex] at htransport
  have hleft :
      (fun t : H → ℝ =>
        Erdos4.variableContinuousProduct H.card A (tupleReindex H t) ^ 2) =
      fun t => tupleVariableContinuousProduct H A t ^ 2 := by
    funext t
    unfold tupleVariableContinuousProduct Erdos4.variableContinuousProduct
    rw [tupleReindex_apply]
    exact congrArg (fun x : ℝ => x ^ 2)
      ((tupleIndexEquiv H).symm.prod_comp
        (fun h => Erdos4.variableContinuousFactor A
          ((H.card : ℝ) * t h)))
  rw [hleft] at htransport
  rw [htransport]
  have hsimplex : BoundedGaps.Maynard.maynardSimplex H.card ⊆
      BoundedGaps.Maynard.maynardCube H.card := fun _ ht => ht.1
  have hcubeMeas := BoundedGaps.Maynard.maynardCube_measurable H.card
  have hrestrict :
      (∫ t in BoundedGaps.Maynard.maynardCube H.card,
        Erdos4.VariableMaynard.candidate H.card A t ^ 2) =
      ∫ t in BoundedGaps.Maynard.maynardSimplex H.card,
        Erdos4.VariableMaynard.candidate H.card A t ^ 2 := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      hcubeMeas hsimplex
    intro t ht
    simp [Erdos4.VariableMaynard.candidate, ht.2]
  unfold BoundedGaps.Maynard.maynardI
  rw [hrestrict]
  apply MeasureTheory.setIntegral_congr_fun
    (BoundedGaps.Maynard.maynardSimplex_measurable (k := H.card))
  intro t ht
  change Erdos4.variableContinuousProduct H.card A t ^ 2 =
    Erdos4.VariableMaynard.candidate H.card A t ^ 2
  rw [Erdos4.VariableMaynard.candidate, if_pos ht,
    Erdos4.variableContinuousProduct_eq_product_of_mem_cube ht.1]

theorem normalized_tupleVariableDiagonal_eq_independent_sub_collision
    {H : Finset ℕ} {A alpha : ℝ} {N : ℕ}
    (hR : 1 < BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (hscale : Erdos6.Maynard.tupleNaturalScale H alpha N ≠ 0) :
    Erdos6.Maynard.normalizedTupleMaynardDiagonal H alpha
        (tupleVariableCandidate H A) N =
      Erdos6.Maynard.normalizedTupleWeightedMoment H alpha
          (fun t => tupleVariableContinuousProduct H A t ^ 2) N -
        Erdos6.Maynard.normalizedTupleCollisionMoment H alpha
          (fun t => tupleVariableContinuousProduct H A t ^ 2) N := by
  have hsplit := Erdos6.Maynard.tupleWeightedMoment_sq_eq_diagonal_add_collision
    (H := H) (F := tupleVariableCandidate H A)
    (G := tupleVariableContinuousProduct H A) hR
    (fun t ht => tupleVariableContinuousProduct_eq_candidate_of_mem_simplex ht)
  unfold Erdos6.Maynard.normalizedTupleMaynardDiagonal
    Erdos6.Maynard.normalizedTupleWeightedMoment
    Erdos6.Maynard.normalizedTupleCollisionMoment
  rw [hsplit]
  field_simp [hscale]
  ring

theorem tendsto_normalizedTupleVariableDiagonal
    {H : Finset ℕ} (hH : H.Nonempty) {A alpha : ℝ}
    (hA : 0 < A) (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      Erdos6.Maynard.normalizedTupleMaynardDiagonal H alpha
        (tupleVariableCandidate H A) N)
      atTop
      (nhds (BoundedGaps.Maynard.maynardI H.card
        (Erdos4.VariableMaynard.candidate H.card A))) := by
  let h0 : H := ⟨hH.choose, hH.choose_spec⟩
  have hind := Erdos6.Maynard.tendsto_normalizedTupleWeightedMoment
    (f := fun t => tupleVariableContinuousProduct H A t ^ 2)
    h0 halpha
    ((continuous_tupleVariableContinuousProduct hA).pow 2)
    (tupleVariableContinuousProduct_sq_bounds hA)
  rw [integral_tupleVariableContinuousProduct_sq_eq_maynardI] at hind
  have hcoll := Erdos6.Maynard.tendsto_normalizedTupleCollisionMoment_zero
    (H := H) halpha
    (f := fun t => tupleVariableContinuousProduct H A t ^ 2)
    (fun x hx => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (tupleVariableContinuousProduct_sq_bounds hA x hx).2)
  have hdiff := hind.sub hcoll
  simpa using hdiff.congr' (by
    filter_upwards [
      BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius halpha,
      Erdos6.Maynard.eventually_tupleNaturalScale_pos
        (H := H) halpha] with N hR hscale
    exact (normalized_tupleVariableDiagonal_eq_independent_sub_collision
      hR hscale.ne').symm)

theorem tupleVariableCandidate_abs_le_one
    {H : Finset ℕ} {A : ℝ} (hA : 0 < A) (t : H → ℝ) :
    |tupleVariableCandidate H A t| ≤ 1 := by
  unfold tupleVariableCandidate
  rw [abs_of_nonneg]
  · exact Erdos4.VariableMaynard.candidate_le_one hA _
  · exact Erdos4.VariableMaynard.candidate_nonneg hA _

end

end MaynardTao
