import Wikipedia.NoExoticSixSphere.CenteredChartCoordinates

/-!
# Fixed differential changes between actual centered target charts

At points of the fiber over the fixed target point, the change of
coordinate differential is one fixed continuous linear equivalence.
It is constructed from the actual derivatives of the two partial
diffeomorphisms. No coordinate-transition identity is an extra input.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CenteredChartCoordinates

variable {B H M C K N F G : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace K]
  {J : ModelWithCorners ℝ C K} [TopologicalSpace N] [ChartedSpace K N]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def chartDifferential (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    (b : N) (hb : b ∈ c.source) : C ≃L[ℝ] F :=
  (show IsLocalDiffeomorphAt J 𝓘(ℝ, F) ∞ c b from
    ⟨c, hb, fun _ _ ↦ rfl⟩).mfderivToContinuousLinearEquiv (by simp)

theorem chartDifferential_toContinuousLinearMap
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (b : N) (hb : b ∈ c.source) :
    (chartDifferential c b hb).toContinuousLinearMap = mfderiv J 𝓘(ℝ, F) c b := rfl

def differentialChange (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    (c' : PartialDiffeomorph J 𝓘(ℝ, G) N G ∞) (b : N)
    (hb : b ∈ c.source) (hb' : b ∈ c'.source) : F ≃L[ℝ] G :=
  (chartDifferential c b hb).symm.trans (chartDifferential c' b hb')

theorem differentialChange_comp (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    (c' : PartialDiffeomorph J 𝓘(ℝ, G) N G ∞) (b : N)
    (hb : b ∈ c.source) (hb' : b ∈ c'.source) :
    (differentialChange c c' b hb hb').toContinuousLinearMap.comp
        (chartDifferential c b hb).toContinuousLinearMap =
      (chartDifferential c' b hb').toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    differentialChange, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_apply_apply]

theorem mfderiv_coordinates_at_fiber (f : M → N)
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (b : N) (hb : b ∈ c.source)
    {x : M} (hf : ContMDiffAt I J ∞ f x) (hx : f x = b) :
    mfderiv I 𝓘(ℝ, F) (coordinates f c b) x =
      (chartDifferential c b hb).toContinuousLinearMap.comp (mfderiv I J f x) := by
  subst b
  have hc : IsLocalDiffeomorphAt J 𝓘(ℝ, F) ∞ c (f x) :=
    ⟨c, hb, fun _ _ ↦ rfl⟩
  have hdc := hc.mdifferentiableAt (by simp)
  have hdf := hf.mdifferentiableAt (by simp)
  change mfderiv I 𝓘(ℝ, F) ((c ∘ f) - fun _ ↦ c (f x)) x = _
  rw [mfderiv_sub (hdc.comp x hdf) mdifferentiableAt_const, mfderiv_const]
  let D : B →L[ℝ] F := mfderiv I 𝓘(ℝ, F) (c ∘ f) x
  change D - (0 : B →L[ℝ] F) = _
  rw [sub_zero]
  have hcomp : D =
      (mfderiv J 𝓘(ℝ, F) c (f x) : C →L[ℝ] F).comp (mfderiv I J f x : B →L[ℝ] C) :=
    mfderiv_comp x hdc hdf
  exact hcomp

theorem mfderiv_coordinates_change (f : M → N)
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    (c' : PartialDiffeomorph J 𝓘(ℝ, G) N G ∞) (b : N)
    (hb : b ∈ c.source) (hb' : b ∈ c'.source)
    {x : M} (hf : ContMDiffAt I J ∞ f x) (hx : f x = b) :
    mfderiv I 𝓘(ℝ, G) (coordinates f c' b) x =
      (differentialChange c c' b hb hb').toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ, F) (coordinates f c b) x) := by
  rw [mfderiv_coordinates_at_fiber f c' b hb' hf hx,
    mfderiv_coordinates_at_fiber f c b hb hf hx]
  apply ContinuousLinearMap.ext
  intro v
  let w : C := mfderiv I J f x v
  change chartDifferential c' b hb' w =
    chartDifferential c' b hb' ((chartDifferential c b hb).symm (chartDifferential c b hb w))
  exact (congrArg (chartDifferential c' b hb')
    ((chartDifferential c b hb).symm_apply_apply w)).symm

end NoExoticSixSphere.CenteredChartCoordinates
