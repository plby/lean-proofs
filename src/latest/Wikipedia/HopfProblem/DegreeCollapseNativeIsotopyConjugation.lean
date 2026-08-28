import Wikipedia.SmoothSixDPoincare.AmbientIsotopy

/-! # Transporting actual smooth ambient isotopies through a native diffeomorphism -/

noncomputable section

open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]

theorem isotopicToIdentity_conj (e : Diffeomorph I J M N ∞)
    {d : Diffeomorph I I M M ∞} (hd : IsotopicToIdentity d) :
    IsotopicToIdentity ((e.symm.trans d).trans e) := by
  obtain ⟨A, hA, hA0, hA1, hslices⟩ := hd
  refine ⟨(fun p => e (A (p.1, e.symm p.2))),
    e.contMDiff.comp (hA.comp (contMDiff_fst.prodMk
      (e.symm.contMDiff.comp contMDiff_snd))), ?_, ?_, ?_⟩
  · intro y
    change e (A (0, e.symm y)) = y
    rw [hA0, e.apply_symm_apply]
  · intro y
    change e (A (1, e.symm y)) = e (d (e.symm y))
    rw [hA1]
  · intro t
    obtain ⟨dₜ, hdₜ⟩ := hslices t
    refine ⟨(e.symm.trans dₜ).trans e, ?_⟩
    intro y
    change e (A (t, e.symm y)) = e (dₜ (e.symm y))
    rw [hdₜ]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
