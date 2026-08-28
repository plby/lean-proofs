import Wikipedia.NoExoticSixSphere.GenericFamilyFlatGerm
import Wikipedia.NoExoticSixSphere.FlatLocalClosedDoubleCurve

/-!
# The actual closed double curve in constructed generic-family coordinates

At a singular point of a regular three-to-six family, construct the source
coordinates and then the closed-double-curve chart for the actual flattened
map, not just for its global smooth representative. The source topology,
smooth ambient parametrization, and swap involution are all retained.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace NoExoticSixSphere.FamilyLinearCoordinates

open OperatorRank FamilyFlattening SymmetricDifference FlatDoubleCurve

variable {V W : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem exists_flat_closed_curve_of_regular_three_six (f : ℝ → V → W)
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hreg : RegularThreeSix (fun q : ℝ × V ↦ fderiv ℝ (f q.1) q.2))
    (p : ℝ × V) (hp : ¬ Injective (fderiv ℝ (f p.1) p.2)) :
    ∃ c : RankTwoCoordinates V W, ∃ d : Data (family c f),
      (sourceEquiv c).symm p ∈ d.coord.source ∧
      ∃ hc : (d.forward ((sourceEquiv c).symm p), d.forward ((sourceEquiv c).symm p)) ∈
        closure (doublePoints d.flattened),
      ∃ e : OpenPartialHomeomorph (closure (doublePoints d.flattened)) ℝ,
        (⟨(d.forward ((sourceEquiv c).symm p), d.forward ((sourceEquiv c).symm p)), hc⟩ :
          closure (doublePoints d.flattened)) ∈ e.source ∧
        e ⟨(d.forward ((sourceEquiv c).symm p), d.forward ((sourceEquiv c).symm p)), hc⟩ = 0 ∧
        (∀ r ∈ e.source, e r = (r.val.1.2 - r.val.2.2) / 2) ∧
        (∀ r ∈ e.source, swapClosure d.flattened r ∈ e.source) ∧
        (∀ r ∈ e.source, e (swapClosure d.flattened r) = -e r) ∧
        ContDiffOn ℝ ∞ (fun s ↦ (e.symm s).val) e.target := by
  obtain ⟨c, d, hd, g, hg, he, hv, hD⟩ :=
    exists_flattened_germ_of_regular_three_six f hf hreg p hp
  have hveq := vertical_eventuallyEq he
  have hvd : vertical d.flattened (d.forward ((sourceEquiv c).symm p)) = 0 :=
    hveq.eq_of_nhds.symm.trans hv
  have hDd : Bijective
      (fderiv ℝ (vertical d.flattened) (d.forward ((sourceEquiv c).symm p))) := by
    rw [← hveq.fderiv_eq]
    exact hD
  obtain ⟨hc, e, hsource, hzero, happly, hswap, hneg, hsmooth⟩ :=
    exists_local_closed_double_curve_chart d.flattened d.target.isOpen
      (d.contDiffOn_flattened (contDiff_family c f hf))
      (d.forward ((sourceEquiv c).symm p)) (d.forward_mem_target hd) hvd hDd
  exact ⟨c, d, hd, hc, e, hsource, hzero, happly, hswap, hneg, hsmooth⟩

end NoExoticSixSphere.FamilyLinearCoordinates
