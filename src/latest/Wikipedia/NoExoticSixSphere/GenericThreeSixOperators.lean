import Wikipedia.NoExoticSixSphere.CorankOneGlobalIsolated
import Wikipedia.NoExoticSixSphere.RankOneAvoidance

/-!
# Generic three-to-six operator families on a four-dimensional source

Almost every translation avoids rank at most one and is transverse to
every chart of a constructed cover of the rank-two stratum. Consequently
the entire singular set is discrete. At each singular point an actual
four-dimensional residual has bijective derivative, and compact subsets
contain only finitely many singular points.
-/

noncomputable section

open Set Function Module
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff

namespace NoExoticSixSphere.OperatorRank

open CorankOne CorankOneCoordinates

variable {X V W : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

abbrev RankTwoCoordinates (V W : Type)
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] :=
  Coordinates V W (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 4))

structure RegularThreeSix (D : X → V →L[ℝ] W) : Prop where
  rank_gt_one : ∀ x, 1 < finrank ℝ (D x).range
  isolated : IsDiscrete {x | ¬ Injective (D x)}
  residual_regular : ∀ x, ¬ Injective (D x) → ∃ c : RankTwoCoordinates V W,
    D x ∈ domain c ∧ residual (operatorEquiv c (D x)) = 0 ∧
      Bijective (fderiv ℝ (fun y ↦ residual (operatorEquiv c (D y))) x)

omit [FiniteDimensional ℝ W] in
theorem singular_iff_rank_two (L : V →L[ℝ] W) (hv : finrank ℝ V = 3)
    (hr : 1 < finrank ℝ L.range) : ¬ Injective L ↔ finrank ℝ L.range = 2 := by
  have hdim := L.toLinearMap.finrank_range_add_finrank_ker
  have hle := LinearMap.finrank_range_le L.toLinearMap
  constructor
  · intro hn
    have hne : finrank ℝ L.range ≠ 3 := by
      intro h
      apply hn
      apply LinearMap.ker_eq_bot.mp
      apply Submodule.finrank_eq_zero.mp
      omega
    omega
  · intro h hi
    have hfull := LinearMap.finrank_range_of_inj (f := L.toLinearMap) hi
    omega

theorem ae_regular_three_six [MeasurableSpace (V →L[ℝ] W)]
    [BorelSpace (V →L[ℝ] W)] (μ : Measure (V →L[ℝ] W)) [IsAddHaarMeasure μ]
    (D : X → V →L[ℝ] W) (hD : ContDiff ℝ ∞ D)
    (hx : finrank ℝ X = 4) (hv : finrank ℝ V = 3) (hw : finrank ℝ W = 6) :
    ∀ᵐ A ∂μ, RegularThreeSix (fun x ↦ D x + A) := by
  let E := EuclideanSpace ℝ (Fin 2)
  let F := EuclideanSpace ℝ (Fin 4)
  have hv' : finrank ℝ V = finrank ℝ E + 1 := by simp [E, hv]
  have hw' : finrank ℝ W = finrank ℝ E + finrank ℝ F := by simp [E, F, hw]
  have hd : finrank ℝ X = finrank ℝ F := by simp [F, hx]
  obtain ⟨C, hC, hcov⟩ := exists_countable_cover hv' hw'
  have hc := ae_regular_countable_coordinates μ C hC D hD
  have hl := ae_rank_gt_one μ D hD (by rw [hx, hv, hw]; norm_num)
  apply (hc.and hl).mono
  rintro A ⟨hreg, hlo⟩
  have hDA : ContDiff ℝ ∞ (fun x ↦ D x + A) := hD.add contDiff_const
  have hdisc := isDiscrete_of_regular_cover (fun x ↦ D x + A) hDA hv' hd C hcov hreg
  have hset : {x | ¬ Injective (D x + A)} =
      {x | finrank ℝ (D x + A).range = finrank ℝ E} := by
    ext x
    simpa only [mem_ofPred_eq, E, finrank_euclideanSpace_fin] using
      singular_iff_rank_two (D x + A) hv (hlo x)
  refine ⟨hlo, hset.symm ▸ hdisc, ?_⟩
  intro x hsing
  have hr : finrank ℝ (D x + A).range = finrank ℝ E := by
    simpa only [E, finrank_euclideanSpace_fin] using
      (singular_iff_rank_two (D x + A) hv (hlo x)).mp hsing
  obtain ⟨c, hcC, hxc⟩ := hcov (D x + A) hr
  have hz : residual (operatorEquiv c (D x + A)) = 0 :=
    (singular_iff_residual_zero hxc).mp
      ((injective_operatorEquiv_iff c (D x + A)).not.mpr hsing)
  have hs := hreg c hcC x hxc hz
  refine ⟨c, hxc, hz, ?_, hs⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hs

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ W] in
theorem RegularThreeSix.finite_singularities_inter {D : X → V →L[ℝ] W}
    (h : RegularThreeSix D) (hD : Continuous D) {K : Set X} (hK : IsCompact K) :
    (K ∩ {x | ¬ Injective (D x)}).Finite := by
  have hc : IsClosed {x | ¬ Injective (D x)} :=
    (ContinuousLinearMap.isOpen_injective.preimage hD).isClosed_compl
  exact (hK.inter_right hc).finite (h.isolated.mono inter_subset_right)

end NoExoticSixSphere.OperatorRank
