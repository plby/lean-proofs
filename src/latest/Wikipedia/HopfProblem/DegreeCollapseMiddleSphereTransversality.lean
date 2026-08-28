import Wikipedia.HopfProblem.DegreeCollapseMiddleSphereDifferentials
import Wikipedia.SmoothSixDPoincare.NativeTransversalityStability

/-!
# Native transversality of the constructed smooth middle sphere families

The two derivative images are the complementary Morse coordinate planes,
with invertible source-tail factors and positive radius scaling. Their sum
is onto. The original chart transports this to the original tangent space.
The exact intersection table then gives transversality at every source pair.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality.SeparatedSystem

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] (D : SeparatedSystem E M)

theorem plane_tail_coprod_surjective (p : D.MiddleLabel) :
    Surjective (((D.negativePlane p).comp tailDerivative).coprod
      ((D.positivePlane p).comp tailDerivative)) := by
  intro w
  let r := (D.windows.data p.val).radius
  obtain ⟨u, hu⟩ := tail_mfderiv_bijective.surjective
    ((D.negativeLinear p.val p.property).symm (r⁻¹ • w.1))
  obtain ⟨v, hv⟩ := tail_mfderiv_bijective.surjective
    ((D.positiveLinear p.val p.property).symm (r⁻¹ • w.2))
  refine ⟨(u, v), ?_⟩
  change D.negativePlane p (tailDerivative u) + D.positivePlane p (tailDerivative v) = w
  rw [hu, hv, D.negativePlane_apply, D.positivePlane_apply,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  apply Prod.ext
  · change r • (r⁻¹ • w.1) + 0 = w.1
    rw [add_zero, smul_inv_smul₀ (D.windows.data p.val).radius_pos.ne']
  · change 0 + r • (r⁻¹ • w.2) = w.2
    rw [zero_add, smul_inv_smul₀ (D.windows.data p.val).radius_pos.ne']

namespace SmoothMiddleFamilies

variable {D} (F : D.SmoothMiddleFamilies)

theorem tangent_sum_surjective (p : D.MiddleLabel) :
    Surjective ((mfderiv (𝓡 3) 𝓘(ℝ, E) (F.descending p) middlePole :
      Hemisphere.Ambient 3 →L[ℝ] E).coprod
      (mfderiv (𝓡 3) 𝓘(ℝ, E) (F.ascending p) middlePole :
        Hemisphere.Ambient 3 →L[ℝ] E)) := by
  let c := (D.windows.data p.val).chart.splitChart
  have hsource : F.descending p middlePole ∈ c.source := by
    rw [F.descending_pole]
    exact (D.windows.data p.val).chart.splitChart_mem_source
  apply ChartMapPerturbation.transverse_of_chart c
    ((F.descending_smooth p).mdifferentiableAt (by simp))
    ((F.ascending_smooth p).mdifferentiableAt (by simp))
    ((F.ascending_pole p).trans (F.descending_pole p).symm) hsource
  rw [F.descending_split_derivative, F.ascending_split_derivative]
  exact D.plane_tail_coprod_surjective p

theorem native_transverse (p q : D.MiddleLabel) (x y : Hemisphere.Sphere 3) :
    NativeTransversality.At (𝓡 3) (𝓡 3) 𝓘(ℝ, E) (F.descending p) (F.ascending q) x y := by
  intro hcross
  obtain ⟨rfl, rfl, rfl⟩ := (F.pair_iff p q x y).mp hcross.symm
  exact F.tangent_sum_surjective p

end SmoothMiddleFamilies
end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality.SeparatedSystem
