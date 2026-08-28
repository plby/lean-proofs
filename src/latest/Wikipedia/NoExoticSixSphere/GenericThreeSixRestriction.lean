import Wikipedia.NoExoticSixSphere.GenericThreeSixOperators
import Wikipedia.NoExoticSixSphere.CorankOneScaledPullback

/-!
# Full three-to-six regularity on a specified region

The singular locus and derivatives remain those of the original operator
family. A smooth scaled pullback covering the region transfers regularity
back to it, without asserting regularity outside the region.
-/

noncomputable section

open Set Function Module Filter Topology
open scoped ContDiff

namespace NoExoticSixSphere.OperatorRank

open CorankOne CorankOneCoordinates

variable {X Y V W : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

structure RegularThreeSixOn (D : X → V →L[ℝ] W) (U : Set X) : Prop where
  rank_gt_one : ∀ x ∈ U, 1 < finrank ℝ (D x).range
  isolated : IsDiscrete (U ∩ {x | ¬ Injective (D x)})
  residual_regular : ∀ x ∈ U, ¬ Injective (D x) → ∃ c : RankTwoCoordinates V W,
    D x ∈ domain c ∧ residual (operatorEquiv c (D x)) = 0 ∧
      Bijective (fderiv ℝ (fun y ↦ residual (operatorEquiv c (D y))) x)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem regularOn_of_rank_residual_at (D : X → V →L[ℝ] W) (U : Set X)
    (hD : ∀ x ∈ U, ContDiffAt ℝ ∞ D x) (hr : ∀ x ∈ U, 1 < finrank ℝ (D x).range)
    (hres : ∀ x ∈ U, ¬ Injective (D x) → ∃ c : RankTwoCoordinates V W,
      D x ∈ domain c ∧ residual (operatorEquiv c (D x)) = 0 ∧
        Bijective (fderiv ℝ (fun y ↦ residual (operatorEquiv c (D y))) x)) :
    RegularThreeSixOn D U := by
  refine ⟨hr, ?_, hres⟩
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  obtain ⟨c, hxc, hz, hb⟩ := hres x hx.1 hx.2
  let R : X → EuclideanSpace ℝ (Fin 4) := fun y ↦ residual (operatorEquiv c (D y))
  have hR : ContDiffAt ℝ ∞ R x :=
    (contDiffAt_residual _ (leading_invertible hxc)).comp
      (f := fun y ↦ operatorEquiv c (D y)) x
      ((operatorEquiv c).contDiff.contDiffAt.comp x (hD x hx.1))
  let L : X ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    (LinearEquiv.ofBijective (fderiv ℝ R x).toLinearMap hb).toContinuousLinearEquiv
  have hL : HasFDerivAt R L.toContinuousLinearMap x :=
    (hR.differentiableAt (by simp)).hasFDerivAt
  let e := hR.toOpenPartialHomeomorph R hL (by simp)
  have hex : x ∈ e.source := hR.mem_toOpenPartialHomeomorph_source hL (by simp)
  have hn : D ⁻¹' (domain c : Set (V →L[ℝ] W)) ∈ 𝓝 x :=
    (hD x hx.1).continuousAt.preimage_mem_nhds ((domain c).isOpen.mem_nhds hxc)
  obtain ⟨N, hNc, hN, hxN⟩ := mem_nhds_iff.mp hn
  refine ⟨e.source ∩ N, e.open_source.inter hN, ?_⟩
  ext y
  constructor
  · rintro ⟨⟨hy, hyc⟩, hyU, hys⟩
    apply mem_singleton_iff.mpr
    apply e.injOn hy hex
    exact ((singular_iff_residual_zero (hNc hyc)).mp
      ((injective_operatorEquiv_iff c (D y)).not.mpr hys)).trans hz.symm
  · rintro rfl
    exact ⟨⟨hex, hxN⟩, hx⟩

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem regularOn_of_rank_residual (D : X → V →L[ℝ] W) (hD : ContDiff ℝ ∞ D)
    (U : Set X) (hr : ∀ x ∈ U, 1 < finrank ℝ (D x).range)
    (hres : ∀ x ∈ U, ¬ Injective (D x) → ∃ c : RankTwoCoordinates V W,
      D x ∈ domain c ∧ residual (operatorEquiv c (D x)) = 0 ∧
        Bijective (fderiv ℝ (fun y ↦ residual (operatorEquiv c (D y))) x)) :
    RegularThreeSixOn D U :=
  regularOn_of_rank_residual_at D U (fun _ _ ↦ hD.contDiffAt) hr hres

omit [FiniteDimensional ℝ Y] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem regularOn_of_scaled_pullback (D : X → V →L[ℝ] W) (hD : ContDiff ℝ ∞ D)
    (φ : Y → X) (hφ : ContDiff ℝ ∞ φ) (a : Y → ℝ) (ha : ContDiff ℝ ∞ a)
    (ha0 : ∀ y, a y ≠ 0) (U : Set X) (hcov : ∀ x ∈ U, ∃ y, φ y = x)
    (hx : finrank ℝ X = 4)
    (hreg : RegularThreeSix (fun y ↦ a y • D (φ y))) : RegularThreeSixOn D U := by
  apply regularOn_of_rank_residual D hD U
  · intro x hxU
    obtain ⟨y, rfl⟩ := hcov x hxU
    have hr := hreg.rank_gt_one y
    change 1 < finrank ℝ (a y • D (φ y)).range at hr
    rw [CorankOne.range_smul_eq _ (ha0 y)] at hr
    exact hr
  · intro x hxU hsing
    obtain ⟨y, rfl⟩ := hcov x hxU
    have hsy : ¬ Injective (a y • D (φ y)) :=
      (injective_smul_iff _ (ha0 y)).not.mpr hsing
    obtain ⟨c, hcy, hzy, hby⟩ := hreg.residual_regular y hsy
    have hc : D (φ y) ∈ domain c := by
      change operatorEquiv c (a y • D (φ y)) ∈ chart at hcy
      rw [map_smul] at hcy
      exact (smul_mem_chart_iff _ (ha0 y)).mp hcy
    have hz : residual (operatorEquiv c (D (φ y))) = 0 :=
      (singular_iff_residual_zero hc).mp
        ((injective_operatorEquiv_iff c (D (φ y))).not.mpr hsing)
    have hs := hby.2
    simp_rw [map_smul] at hs
    have hs' := surjective_residual_of_scaled_pullback
      (fun x ↦ operatorEquiv c (D x)) φ a y
      ((operatorEquiv c).contDiff.comp hD).contDiffAt
      (hφ.differentiable (by simp) y) (ha.differentiable (by simp) y)
      (ha0 y) hc hz hs
    refine ⟨c, hc, hz, ?_, hs'⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa only [finrank_euclideanSpace_fin] using hx)).mpr hs'

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ W] in
theorem RegularThreeSixOn.finite_singularities_inter {D : X → V →L[ℝ] W}
    {U : Set X} (h : RegularThreeSixOn D U) (hD : Continuous D)
    {K : Set X} (hK : IsCompact K) (hKU : K ⊆ U) :
    (K ∩ {x | ¬ Injective (D x)}).Finite := by
  have hc : IsClosed {x | ¬ Injective (D x)} :=
    (ContinuousLinearMap.isOpen_injective.preimage hD).isClosed_compl
  exact (hK.inter_right hc).finite
    (h.isolated.mono (fun _ hx ↦ ⟨hKU hx.1, hx.2⟩))

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem RegularThreeSixOn.global_of_injective_off {D : X → V →L[ℝ] W}
    {U : Set X} (h : RegularThreeSixOn D U) (hv : finrank ℝ V = 3)
    (hoff : ∀ x ∉ U, Injective (D x)) : RegularThreeSix D := by
  have hmem (x : X) (hx : ¬ Injective (D x)) : x ∈ U := by
    by_contra hn
    exact hx (hoff x hn)
  refine ⟨?_, ?_, fun x hx ↦ h.residual_regular x (hmem x hx) hx⟩
  · intro x
    by_cases hx : x ∈ U
    · exact h.rank_gt_one x hx
    · have hr := LinearMap.finrank_range_of_inj (f := (D x).toLinearMap) (hoff x hx)
      change 1 < finrank ℝ (D x).toLinearMap.range
      rw [hr, hv]
      norm_num
  · have he : U ∩ {x | ¬ Injective (D x)} = {x | ¬ Injective (D x)} := by
      ext x
      exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨hmem x hx, hx⟩⟩
    rw [← he]
    exact h.isolated

end NoExoticSixSphere.OperatorRank
