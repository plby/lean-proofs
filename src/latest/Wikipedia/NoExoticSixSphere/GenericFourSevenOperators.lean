import Wikipedia.NoExoticSixSphere.RankTwoAvoidance
import Wikipedia.NoExoticSixSphere.CorankOneLocalRegularity

/-!
# Generic four-to-seven operator families on the actual four-dimensional source

Low-rank factorization excludes ranks at most two. A countable cover of the
actual rank-three stratum gives regular four-dimensional residuals for the
same almost-everywhere set of parameters. Thus all singularities are isolated
rank-three points; compact subsets contain only finitely many. This does not
assert that the singularities are absent or that their number is even.
-/

noncomputable section

open Set Function Module TopologicalSpace
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff

namespace NoExoticSixSphere.OperatorRank

open CorankOne CorankOneCoordinates

variable {X V W : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

abbrev RankThreeCoordinates (V W : Type)
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] :=
  Coordinates V W (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 4))

structure RegularFourSevenOn (D : X → V →L[ℝ] W) (U : Set X) : Prop where
  rank_gt_two : ∀ x ∈ U, 2 < finrank ℝ (D x).range
  isolated : IsDiscrete (U ∩ {x | ¬ Injective (D x)})
  residual_regular : ∀ x ∈ U, ¬ Injective (D x) → ∃ c : RankThreeCoordinates V W,
    D x ∈ domain c ∧ residual (operatorEquiv c (D x)) = 0 ∧
      Bijective (fderiv ℝ (fun y ↦ residual (operatorEquiv c (D y))) x)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem regularFourSevenOn_of_residual_at (D : X → V →L[ℝ] W) (U : Set X)
    (hD : ∀ x ∈ U, ContDiffAt ℝ ∞ D x) (hr : ∀ x ∈ U, 2 < finrank ℝ (D x).range)
    (hres : ∀ x ∈ U, ¬ Injective (D x) → ∃ c : RankThreeCoordinates V W,
      D x ∈ domain c ∧ residual (operatorEquiv c (D x)) = 0 ∧
        Bijective (fderiv ℝ (fun y ↦ residual (operatorEquiv c (D y))) x)) :
    RegularFourSevenOn D U :=
  ⟨hr, CorankOneCoordinates.isDiscrete_singular_on D U hD hres, hres⟩

omit [FiniteDimensional ℝ W] in
theorem singular_iff_rank_three (L : V →L[ℝ] W) (hv : finrank ℝ V = 4)
    (hr : 2 < finrank ℝ L.range) : ¬ Injective L ↔ finrank ℝ L.range = 3 := by
  have hdim := L.toLinearMap.finrank_range_add_finrank_ker
  have hle := LinearMap.finrank_range_le L.toLinearMap
  constructor
  · intro hn
    have hne : finrank ℝ L.range ≠ 4 := by
      intro h
      apply hn
      apply LinearMap.ker_eq_bot.mp
      apply Submodule.finrank_eq_zero.mp
      omega
    omega
  · intro h hi
    have hfull := LinearMap.finrank_range_of_inj (f := L.toLinearMap) hi
    omega

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasurableSpace P] [BorelSpace P]

theorem ae_regular_four_seven_of_submersion (μ : Measure P) [IsAddHaarMeasure μ]
    (D : P × X → V →L[ℝ] W) (U : Opens (P × X)) (hD : ContDiffOn ℝ ∞ D U)
    (hs : ∀ q ∈ U, Surjective (fderiv ℝ D q))
    (hx : finrank ℝ X = 4) (hv : finrank ℝ V = 4) (hw : finrank ℝ W = 7) :
    ∀ᵐ a ∂μ, RegularFourSevenOn (fun x ↦ D (a, x)) {x | (a, x) ∈ U} := by
  let E := EuclideanSpace ℝ (Fin 3)
  let F := EuclideanSpace ℝ (Fin 4)
  have hv' : finrank ℝ V = finrank ℝ E + 1 := by simp [E, hv]
  have hw' : finrank ℝ W = finrank ℝ E + finrank ℝ F := by simp [E, F, hw]
  have hd : finrank ℝ X = finrank ℝ F := by simp [F, hx]
  obtain ⟨C, hC, hcov⟩ := exists_countable_cover hv' hw'
  let : Countable C := hC.to_subtype
  have hc : ∀ᵐ a ∂μ, ∀ c : C, ∀ x, (a, x) ∈ U → D (a, x) ∈ domain c.val →
      residual (operatorEquiv c.val (D (a, x))) = 0 →
        Surjective (fderiv ℝ (fun y ↦ residual (operatorEquiv c.val (D (a, y)))) x) :=
    ae_all_iff.mpr fun c ↦
      CorankOneCoordinates.ae_regular_submersive_coordinates μ D U hD hs c.val
  have hl := ae_rank_gt_two_of_submersion μ D U hD hs (by rw [hx, hv, hw]; norm_num)
  apply (hc.and hl).mono
  rintro a ⟨ha, hlo⟩
  apply regularFourSevenOn_of_residual_at (fun x ↦ D (a, x)) {x | (a, x) ∈ U}
    (fun x hxu ↦ (hD.contDiffAt (U.isOpen.mem_nhds hxu)).comp
      (f := fun y ↦ (a, y)) x (contDiff_const.prodMk contDiff_id).contDiffAt) hlo
  intro x hxu hsing
  have hr : finrank ℝ (D (a, x)).range = finrank ℝ E := by
    simpa only [E, finrank_euclideanSpace_fin] using
      (singular_iff_rank_three (D (a, x)) hv (hlo x hxu)).mp hsing
  obtain ⟨c, hcC, hxc⟩ := hcov (D (a, x)) hr
  have hz : residual (operatorEquiv c (D (a, x))) = 0 :=
    (singular_iff_residual_zero hxc).mp
      ((injective_operatorEquiv_iff c (D (a, x))).not.mpr hsing)
  have hsurj := ha ⟨c, hcC⟩ x hxu hxc hz
  exact ⟨c, hxc, hz,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hsurj, hsurj⟩

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ W] in
theorem RegularFourSevenOn.finite_singularities_inter {D : X → V →L[ℝ] W} {U : Set X}
    (h : RegularFourSevenOn D U) {K : Set X} (hK : IsCompact K) (hKU : K ⊆ U)
    (hD : ContinuousOn D K) : (K ∩ {x | ¬ Injective (D x)}).Finite := by
  have hc : IsClosed (K ∩ {x | ¬ Injective (D x)}) :=
    hD.preimage_isClosed_of_isClosed hK.isClosed ContinuousLinearMap.isOpen_injective.isClosed_compl
  exact (hK.of_isClosed_subset hc inter_subset_left).finite
    (h.isolated.mono (fun _ hx ↦ ⟨hKU hx.1, hx.2⟩))

end NoExoticSixSphere.OperatorRank
