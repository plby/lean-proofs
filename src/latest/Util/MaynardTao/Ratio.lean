/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Util.MaynardTao.Kernel
import ErdosProblems.Erdos48.External.Erdos4.Base

/-!
# A parameterized face-mass lower bound for the variable Maynard candidate

The mirrored Erdős 4 proof fixes the half-simplex when it lower-bounds the
variational numerator.  For the sharp cardinal threshold we need a moving
cutoff much closer to one, so this file separates the elementary quotient
calculation from the later concentration estimate.
-/

namespace MaynardTao

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

def variableGoodRegion (q : ℝ) (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  BoundedGaps.Maynard.maynardCubeOf ι ∩
    {t | Erdos4.VariableMaynard.coordinateSum t ≤ q}

theorem variableGoodRegion_measurable (q : ℝ) (ι : Type*) [Fintype ι] :
    MeasurableSet (variableGoodRegion q ι) := by
  unfold variableGoodRegion
  exact (MeasurableSet.pi Set.countable_univ
    (fun _ _ => measurableSet_Icc)).inter
      (measurableSet_Iic.preimage
        (Erdos4.VariableMaynard.measurable_coordinateSum ι))

theorem variableGoodRegion_subset_cube (q : ℝ) (ι : Type*) [Fintype ι] :
    variableGoodRegion q ι ⊆ BoundedGaps.Maynard.maynardCubeOf ι := by
  intro t ht
  exact ht.1

noncomputable def variableShortMass (K : ℕ) (A δ : ℝ) : ℝ :=
  ∫ x : ℝ in Set.Icc (0 : ℝ) δ,
    Erdos4.VariableMaynard.factor A ((K : ℝ) * x)

theorem variableShortMass_eq {K : ℕ} {A δ : ℝ}
    (hK : 0 < K) (hA : 0 < A) (hδ : 0 ≤ δ) :
    variableShortMass K A δ =
      Real.log (1 + A * (K : ℝ) * δ) / (A * (K : ℝ)) := by
  unfold variableShortMass
  exact Erdos4.VariableMaynard.setIntegral_factor_Icc hK hA hδ

theorem variableShortMass_pos {K : ℕ} {A δ : ℝ}
    (hK : 0 < K) (hA : 0 < A) (hδ : 0 < δ) :
    0 < variableShortMass K A δ := by
  rw [variableShortMass_eq hK hA hδ.le]
  have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hlog : 0 < Real.log (1 + A * (K : ℝ) * δ) := by
    apply Real.log_pos
    have hterm : 0 < A * (K : ℝ) * δ := by positivity
    linarith
  exact div_pos hlog (mul_pos hA hKR)

theorem variableCandidate_insert_eq_on_good_interval
    {K : ℕ} {A q δ : ℝ} (hK : 0 < K)
    (m : Fin K) (t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ)
    (ht : t ∈ variableGoodRegion q
      (BoundedGaps.Maynard.maynardFaceIndex K m))
    (hqδ : q + δ ≤ 1) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) δ) :
    Erdos4.VariableMaynard.candidate K A
        (BoundedGaps.Maynard.maynardInsertCoordinate m x t) =
      Erdos4.VariableMaynard.factor A ((K : ℝ) * x) *
        Erdos4.VariableMaynard.faceProduct K A t := by
  have htnonneg : ∀ j, 0 ≤ t j := fun j =>
    (ht.1 j (Set.mem_univ j)).1
  have hsum : x + ∑ j, t j ≤ 1 := by
    have hface := ht.2
    change Erdos4.VariableMaynard.coordinateSum t ≤ q at hface
    change x + Erdos4.VariableMaynard.coordinateSum t ≤ 1
    linarith [hx.2]
  have hsimp := Erdos6.Maynard.maynardInsertCoordinate_mem_simplex_of_pos
    hK m x t hx.1 htnonneg hsum
  rw [Erdos4.VariableMaynard.candidate, if_pos hsimp]
  unfold Erdos4.VariableMaynard.product
  have hp := Erdos6.Maynard.prod_maynardInsertCoordinate_of_pos hK m x t
    (fun y : ℝ => Erdos4.VariableMaynard.factor A ((K : ℝ) * y))
  simpa only [Erdos4.VariableMaynard.faceProduct] using hp

theorem variableShortCandidateIntegral_eq
    {K : ℕ} {A q δ : ℝ} (hK : 0 < K)
    (m : Fin K) (t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ)
    (ht : t ∈ variableGoodRegion q
      (BoundedGaps.Maynard.maynardFaceIndex K m))
    (hqδ : q + δ ≤ 1) (hδ : 0 ≤ δ) :
    (∫ x : ℝ in Set.Icc (0 : ℝ) δ,
      Erdos4.VariableMaynard.candidate K A
        (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) =
      Erdos4.VariableMaynard.faceProduct K A t *
        variableShortMass K A δ := by
  calc
    (∫ x : ℝ in Set.Icc (0 : ℝ) δ,
        Erdos4.VariableMaynard.candidate K A
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) =
        ∫ x : ℝ in Set.Icc (0 : ℝ) δ,
          Erdos4.VariableMaynard.faceProduct K A t *
            Erdos4.VariableMaynard.factor A ((K : ℝ) * x) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      change Erdos4.VariableMaynard.candidate K A
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t) =
        Erdos4.VariableMaynard.faceProduct K A t *
          Erdos4.VariableMaynard.factor A ((K : ℝ) * x)
      rw [variableCandidate_insert_eq_on_good_interval hK m t ht hqδ hx]
      ring
    _ = Erdos4.VariableMaynard.faceProduct K A t *
        variableShortMass K A δ := by
      rw [integral_const_mul]
      rfl

theorem variableFaceInnerIntegral_ge
    {K : ℕ} {A q δ : ℝ} (hK : 0 < K) (hA : 0 < A)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hqδ : q + δ ≤ 1)
    (m : Fin K) (t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ)
    (ht : t ∈ variableGoodRegion q
      (BoundedGaps.Maynard.maynardFaceIndex K m)) :
    Erdos4.VariableMaynard.faceProduct K A t * variableShortMass K A δ ≤
      ∫ x : ℝ in Set.Icc (0 : ℝ) 1,
        Erdos4.VariableMaynard.candidate K A
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t) := by
  have hmono :
      (∫ x : ℝ in Set.Icc (0 : ℝ) δ,
        Erdos4.VariableMaynard.candidate K A
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ≤
      ∫ x : ℝ in Set.Icc (0 : ℝ) 1,
        Erdos4.VariableMaynard.candidate K A
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t) := by
    apply setIntegral_mono_set
      (Erdos4.VariableMaynard.candidate_face_integrableOn hA m t)
    · exact Filter.Eventually.of_forall fun x =>
        Erdos4.VariableMaynard.candidate_nonneg hA _
    · exact Filter.Eventually.of_forall fun _ hx =>
        ⟨hx.1, hx.2.trans hδ1⟩
  rw [← variableShortCandidateIntegral_eq hK m t ht hqδ hδ0]
  exact hmono

theorem variableFaceInnerIntegral_sq_ge
    {K : ℕ} {A q δ : ℝ} (hK : 0 < K) (hA : 0 < A)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hqδ : q + δ ≤ 1)
    (m : Fin K) (t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ)
    (ht : t ∈ variableGoodRegion q
      (BoundedGaps.Maynard.maynardFaceIndex K m)) :
    variableShortMass K A δ ^ 2 *
        Erdos4.VariableMaynard.productDensity K A t ≤
      (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
        Erdos4.VariableMaynard.candidate K A
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2 := by
  have hfacepos : 0 < Erdos4.VariableMaynard.faceProduct K A t :=
    Erdos4.VariableMaynard.faceProduct_pos_of_mem_cube hA ht.1
  have hshortpos : 0 < variableShortMass K A δ :=
    variableShortMass_pos hK hA hδ
  have hlowerpos : 0 < Erdos4.VariableMaynard.faceProduct K A t *
      variableShortMass K A δ := mul_pos hfacepos hshortpos
  have hinner := variableFaceInnerIntegral_ge hK hA hδ.le hδ1 hqδ m t ht
  have hsq : (Erdos4.VariableMaynard.faceProduct K A t *
      variableShortMass K A δ) ^ 2 ≤
      (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
        Erdos4.VariableMaynard.candidate K A
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2 := by
    nlinarith
  calc
    variableShortMass K A δ ^ 2 *
        Erdos4.VariableMaynard.productDensity K A t =
        (Erdos4.VariableMaynard.faceProduct K A t *
          variableShortMass K A δ) ^ 2 := by
      rw [← Erdos4.VariableMaynard.faceProduct_sq_eq_productDensity]
      ring
    _ ≤ _ := hsq

/-- A lower bound for the product density on every moving good face yields a
corresponding lower bound for the Maynard quotient. -/
theorem maynardRatio_variableCandidate_gt_of_goodFaceMass
    {K : ℕ} {A q δ γ : ℝ} (hK2 : 2 ≤ K) (hA : 0 < A)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hqδ : q + δ ≤ 1)
    (hγ : 0 < γ)
    (hgood : ∀ m : Fin K,
      γ * Erdos4.VariableMaynard.baseMass K A ^ (K - 1) <
        ∫ t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ in
          variableGoodRegion q
            (BoundedGaps.Maynard.maynardFaceIndex K m),
          Erdos4.VariableMaynard.productDensity K A t) :
    (K : ℝ) * γ * variableShortMass K A δ ^ 2 /
        Erdos4.VariableMaynard.baseMass K A <
      BoundedGaps.Maynard.maynardRatio K
        (Erdos4.VariableMaynard.candidate K A) := by
  let c : ℝ := variableShortMass K A δ ^ 2
  have hc : 0 < c := sq_pos_of_pos (variableShortMass_pos (by omega) hA hδ)
  have hJ : ∀ m : Fin K,
      γ * variableShortMass K A δ ^ 2 *
          Erdos4.VariableMaynard.baseMass K A ^ (K - 1) <
        BoundedGaps.Maynard.maynardJ K m
          (Erdos4.VariableMaynard.candidate K A) := by
    intro m
    have hscaled := mul_lt_mul_of_pos_left (hgood m) hc
    have hdensityCube : IntegrableOn (fun t :
        BoundedGaps.Maynard.maynardFaceIndex K m → ℝ =>
        c * Erdos4.VariableMaynard.productDensity K A t)
        (BoundedGaps.Maynard.maynardCubeOf
          (BoundedGaps.Maynard.maynardFaceIndex K m)) :=
      (Erdos4.VariableMaynard.productDensity_integrableOn_cube K A hA _).const_mul c
    have hsquareCube : IntegrableOn
        (fun t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ =>
          (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
            Erdos4.VariableMaynard.candidate K A
              (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2)
        (BoundedGaps.Maynard.maynardCubeOf
          (BoundedGaps.Maynard.maynardFaceIndex K m)) :=
      Erdos4.VariableMaynard.candidate_face_integrand_integrableOn hA m
    have hpointwise :
        (∫ t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ in
          variableGoodRegion q
            (BoundedGaps.Maynard.maynardFaceIndex K m),
          c * Erdos4.VariableMaynard.productDensity K A t) ≤
        ∫ t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ in
          variableGoodRegion q
            (BoundedGaps.Maynard.maynardFaceIndex K m),
          (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
            Erdos4.VariableMaynard.candidate K A
              (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2 := by
      apply setIntegral_mono_on
        (hdensityCube.mono_set (variableGoodRegion_subset_cube q _))
        (hsquareCube.mono_set (variableGoodRegion_subset_cube q _))
        (variableGoodRegion_measurable q _)
      intro t ht
      exact variableFaceInnerIntegral_sq_ge (by omega) hA hδ hδ1 hqδ m t ht
    have hsubset :
        (∫ t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ in
          variableGoodRegion q
            (BoundedGaps.Maynard.maynardFaceIndex K m),
          (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
            Erdos4.VariableMaynard.candidate K A
              (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2) ≤
        ∫ t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ in
          BoundedGaps.Maynard.maynardCubeOf
            (BoundedGaps.Maynard.maynardFaceIndex K m),
          (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
            Erdos4.VariableMaynard.candidate K A
              (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2 := by
      apply setIntegral_mono_set hsquareCube
      · exact Filter.Eventually.of_forall fun _ => sq_nonneg _
      · exact Filter.Eventually.of_forall fun _ ht =>
          variableGoodRegion_subset_cube q _ ht
    unfold BoundedGaps.Maynard.maynardJ
    calc
      γ * variableShortMass K A δ ^ 2 *
          Erdos4.VariableMaynard.baseMass K A ^ (K - 1) =
          c * (γ * Erdos4.VariableMaynard.baseMass K A ^ (K - 1)) := by
        unfold c
        ring
      _ < c * (∫ t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ in
          variableGoodRegion q
            (BoundedGaps.Maynard.maynardFaceIndex K m),
          Erdos4.VariableMaynard.productDensity K A t) := hscaled
      _ = (∫ t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ in
          variableGoodRegion q
            (BoundedGaps.Maynard.maynardFaceIndex K m),
          c * Erdos4.VariableMaynard.productDensity K A t) := by
        rw [integral_const_mul]
      _ ≤ _ := hpointwise.trans hsubset
  have huniv : (Finset.univ : Finset (Fin K)).Nonempty := by
    refine ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hsum : (K : ℝ) *
      (γ * variableShortMass K A δ ^ 2 *
        Erdos4.VariableMaynard.baseMass K A ^ (K - 1)) <
      ∑ m : Fin K, BoundedGaps.Maynard.maynardJ K m
        (Erdos4.VariableMaynard.candidate K A) := by
    calc
      (K : ℝ) *
          (γ * variableShortMass K A δ ^ 2 *
            Erdos4.VariableMaynard.baseMass K A ^ (K - 1)) =
          ∑ _m : Fin K, γ * variableShortMass K A δ ^ 2 *
            Erdos4.VariableMaynard.baseMass K A ^ (K - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ < _ := Finset.sum_lt_sum_of_nonempty huniv fun m _ => hJ m
  have hK : 0 < K := by omega
  have hbase : 0 < Erdos4.VariableMaynard.baseMass K A :=
    Erdos4.VariableMaynard.baseMass_pos hK hA
  have hIpos : 0 < BoundedGaps.Maynard.maynardI K
      (Erdos4.VariableMaynard.candidate K A) :=
    Erdos4.VariableMaynard.maynardI_candidate_pos hK hA
  have hIle := Erdos4.VariableMaynard.maynardI_candidate_le hK hA
  have hpow : Erdos4.VariableMaynard.baseMass K A ^ K =
      Erdos4.VariableMaynard.baseMass K A ^ (K - 1) *
        Erdos4.VariableMaynard.baseMass K A := by
    have hexp : K = (K - 1) + 1 := by omega
    calc
      Erdos4.VariableMaynard.baseMass K A ^ K =
          Erdos4.VariableMaynard.baseMass K A ^ ((K - 1) + 1) := by
        exact congrArg (fun n : ℕ =>
          Erdos4.VariableMaynard.baseMass K A ^ n) hexp
      _ = _ := pow_succ _ _
  unfold BoundedGaps.Maynard.maynardRatio
  calc
    (K : ℝ) * γ * variableShortMass K A δ ^ 2 /
        Erdos4.VariableMaynard.baseMass K A =
      ((K : ℝ) *
        (γ * variableShortMass K A δ ^ 2 *
          Erdos4.VariableMaynard.baseMass K A ^ (K - 1))) /
        Erdos4.VariableMaynard.baseMass K A ^ K := by
      rw [hpow]
      field_simp [hbase.ne', pow_ne_zero _ hbase.ne']
    _ ≤ ((K : ℝ) *
        (γ * variableShortMass K A δ ^ 2 *
          Erdos4.VariableMaynard.baseMass K A ^ (K - 1))) /
        BoundedGaps.Maynard.maynardI K
          (Erdos4.VariableMaynard.candidate K A) :=
      div_le_div_of_nonneg_left (by positivity) hIpos hIle
    _ < (∑ m : Fin K, BoundedGaps.Maynard.maynardJ K m
        (Erdos4.VariableMaynard.candidate K A)) /
        BoundedGaps.Maynard.maynardI K
          (Erdos4.VariableMaynard.candidate K A) :=
      div_lt_div_of_pos_right hsum hIpos

end

end MaynardTao
