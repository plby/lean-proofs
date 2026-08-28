import Wikipedia.NoExoticSixSphere.FamilyLinearCoordinates
import Wikipedia.NoExoticSixSphere.GenericThreeSixFamily

/-!
# Actual nondegenerate flat germs at generic family singularities

The regularity condition already proved for generic three-to-six families
now supplies rank-adapted linear coordinates and a time-preserving nonlinear
source change. The remaining smooth germ has zero vertical derivative and
bijective derivative of that vertical derivative.

The residual-level coordinate construction permits arbitrary finite-dimensional
parameter and leading-coordinate spaces; the three-to-six results specialize it.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace NoExoticSixSphere.FamilyLinearCoordinates

open CorankOne CorankOneCoordinates OperatorRank FamilyFlattening SymmetricDifference

variable {V W : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem exists_source_coordinates_of_regular_residual
    {T E F : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : T → V → W)
    (hf : ContDiff ℝ ∞ (uncurry f))
    (p : T × V)
    (hres : ∃ c : Coordinates V W E F,
      fderiv ℝ (f p.1) p.2 ∈ CorankOneCoordinates.domain c ∧
      CorankOne.residual (operatorEquiv c (fderiv ℝ (f p.1) p.2)) = 0 ∧
      Bijective (fderiv ℝ
        (fun q : T × V ↦ CorankOne.residual (operatorEquiv c (fderiv ℝ (f q.1) q.2))) p)) :
    ∃ c : Coordinates V W E F, ∃ d : Data (family c f),
      (sourceEquiv c).symm p ∈ d.coord.source ∧
      CorankOne.residual (spatial (family c f) ((sourceEquiv c).symm p)) = 0 ∧
      Bijective (fderiv ℝ (fun r ↦ CorankOne.residual (spatial (family c f) r))
        ((sourceEquiv c).symm p)) := by
  obtain ⟨c, hc, hz, hb⟩ := hres
  let q := (sourceEquiv c).symm p
  have hq : sourceEquiv c q = p := (sourceEquiv c).apply_symm_apply p
  have hsp : spatial (family c f) q = operatorEquiv c (fderiv ℝ (f p.1) p.2) := by
    rw [spatial_family c f hf]
    change operatorEquiv c
      (fderiv ℝ (f (sourceEquiv c q).1) (sourceEquiv c q).2) = _
    rw [hq]
  have hchart : spatial (family c f) q ∈ chart := by
    rw [hsp]
    exact hc
  have hzero : CorankOne.residual (spatial (family c f) q) = 0 := by
    rw [hsp]
    exact hz
  have hbij : Bijective (fderiv ℝ
      (fun r ↦ CorankOne.residual (spatial (family c f) r)) q) := by
    apply bijective_fderiv_residual c f hf q
    · rw [hq]
      exact hc
    · rw [hq]
      exact hb
  obtain ⟨d, hdq⟩ := exists_data (family c f) (contDiff_family c f hf) q hchart
  exact ⟨c, d, hdq, hzero, hbij⟩

theorem exists_regular_source_coordinates (f : ℝ → V → W)
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hreg : RegularThreeSix (fun q : ℝ × V ↦ fderiv ℝ (f q.1) q.2))
    (p : ℝ × V) (hp : ¬ Injective (fderiv ℝ (f p.1) p.2)) :
    ∃ c : RankTwoCoordinates V W, ∃ d : Data (family c f),
      (sourceEquiv c).symm p ∈ d.coord.source ∧
      CorankOne.residual (spatial (family c f) ((sourceEquiv c).symm p)) = 0 ∧
      Bijective (fderiv ℝ (fun r ↦ CorankOne.residual (spatial (family c f) r))
        ((sourceEquiv c).symm p)) :=
  exists_source_coordinates_of_regular_residual f hf p (hreg.residual_regular p hp)

theorem exists_flattened_germ_of_regular_three_six (f : ℝ → V → W)
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hreg : RegularThreeSix (fun q : ℝ × V ↦ fderiv ℝ (f q.1) q.2))
    (p : ℝ × V) (hp : ¬ Injective (fderiv ℝ (f p.1) p.2)) :
    ∃ c : RankTwoCoordinates V W, ∃ d : Data (family c f),
      (sourceEquiv c).symm p ∈ d.coord.source ∧
      ∃ g : (ℝ × EuclideanSpace ℝ (Fin 2)) × ℝ → EuclideanSpace ℝ (Fin 4),
        ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 (d.forward ((sourceEquiv c).symm p))] d.flattened ∧
        vertical g (d.forward ((sourceEquiv c).symm p)) = 0 ∧
        Bijective (fderiv ℝ (vertical g) (d.forward ((sourceEquiv c).symm p))) := by
  obtain ⟨c, d, hd, hz, hb⟩ := exists_regular_source_coordinates f hf hreg p hp
  have hr := d.forward_mem_target hd
  have hfc := contDiff_family c f hf
  obtain ⟨g, hg, he, hv, hD⟩ := exists_global_representative d.target.isOpen hr
    (d.contDiffOn_flattened hfc)
  refine ⟨c, d, hd, g, hg, he, ?_, ?_⟩
  · rw [hv, d.vertical_flattened_eq hfc hr, d.inverse_forward hd]
    exact hz
  · rw [hD]
    apply d.bijective_fderiv_vertical hfc hr
    simpa only [d.inverse_forward hd] using hb

end NoExoticSixSphere.FamilyLinearCoordinates
