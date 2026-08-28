import Wikipedia.NoExoticSixSphere.EquatorDimension
import Wikipedia.NoExoticSixSphere.EuclideanTailSplitting
import Wikipedia.SmoothSixDPoincare.SphereLinearDiffeomorph
import Wikipedia.HopfProblem.SphereHomologyVanishing
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePoint

/-!
# Finite generation of positive-degree homology of every Euclidean unit sphere

This includes the empty sphere of a zero-dimensional model and the two-point
sphere of a one-dimensional model. Their positive homology vanishes by total
disconnectedness. In higher dimensions the actual sphere parametrization
transports the already computed integral sphere homology.
-/

noncomputable section

open Set Metric

namespace NoExoticSixSphere

open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology
open Wikipedia.SmoothSixDPoincare

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem unitSphere_homology_subsingleton_finrank_zero
    (h : Module.finrank ℝ E = 0) (k : ℕ) (hk : k ≠ 0) :
    Subsingleton (SingularHomology (UnitSphere E) k) := by
  let : Subsingleton E := Module.finrank_zero_iff.mp h
  let : IsEmpty (UnitSphere E) := ⟨fun x ↦ by
    have hx : (x : E) = 0 := Subsingleton.elim _ _
    have hn := ClosedHemisphere.unit_norm x
    rw [hx, norm_zero] at hn
    exact zero_ne_one hn⟩
  exact totallyDisconnected_homology_subsingleton _ k hk

theorem unitSphere_homology_subsingleton_finrank_one
    (h : Module.finrank ℝ E = 1) (k : ℕ) (hk : k ≠ 0) :
    Subsingleton (SingularHomology (UnitSphere E) k) := by
  let b := (stdOrthonormalBasis ℝ E).reindex (finCongr h)
  let L : E ≃ₗᵢ[ℝ] ℝ := b.repr.trans EuclideanTailCoordinates.scalar.symm
  have hfin : (sphere (0 : ℝ) 1).Finite := by
    rw [Real.sphere_eq_pair (0 : ℝ) zero_le_one]
    exact Set.toFinite _
  let : Finite (sphere (0 : ℝ) 1) := hfin.to_subtype
  let : Subsingleton (SingularHomology (sphere (0 : ℝ) 1) k) :=
    totallyDisconnected_homology_subsingleton _ k hk
  exact (homeomorphHomologyEquiv (unitSphereCongr L) k).injective.subsingleton

theorem unitSphere_positive_homology_finite (k : ℕ) (hk : k ≠ 0) :
    Module.Finite ℤ (SingularHomology (UnitSphere E) k) := by
  by_cases h0 : Module.finrank ℝ E = 0
  · let := unitSphere_homology_subsingleton_finrank_zero E h0 k hk
    infer_instance
  by_cases h1 : Module.finrank ℝ E = 1
  · let := unitSphere_homology_subsingleton_finrank_one E h1 k hk
    infer_instance
  let n := Module.finrank ℝ E - 2
  have hn : Module.finrank ℝ E = (n + 1) + 1 := by dsimp [n]; omega
  let : Fact (Module.finrank ℝ E = (n + 1) + 1) := ⟨hn⟩
  let H := homeomorphHomologyEquiv
    (SphereCoordinates.standardParametrization E (n + 1)).toHomeomorph k
  exact Module.Finite.of_surjective H.toLinearMap H.surjective

end NoExoticSixSphere
