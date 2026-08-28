import Wikipedia.NoExoticSixSphere.GenericLocalContribution
import Wikipedia.NoExoticSixSphere.GenericThreeSixFamily

/-!
# Local parity for actual generic spatial derivatives

Every singularity of a regular three-to-six family has an actual local
embedded-ball contribution. One arbitrarily small constant linear perturbation
simultaneously gives these parity-one contributions and regular off-diagonal
double points. This does not assert endpoint-relative or manifold genericity.
-/

noncomputable section

open Set Function Metric
open scoped ContDiff

namespace NoExoticSixSphere.GenericFamilyParity

open GLOrthonormalization GenericLocalParity OperatorRank

def spatialFamily (f : ℝ → Vector 3 → Vector 6) : ℝ × Vector 3 → Vector 3 →L[ℝ] Vector 6 :=
  fun p ↦ fderiv ℝ (f p.1) p.2

theorem contDiff_spatialFamily (f : ℝ → Vector 3 → Vector 6)
    (hf : ContDiff ℝ ∞ (uncurry f)) : ContDiff ℝ ∞ (spatialFamily f) :=
  DiskHomotopy.contDiff_spatial_fderiv f hf

theorem has_local_contribution (f : ℝ → Vector 3 → Vector 6)
    (hf : ContDiff ℝ ∞ (uncurry f)) (hreg : RegularThreeSix (spatialFamily f))
    (p : ℝ × Vector 3) (hp : ¬ Injective (fderiv ℝ (f p.1) p.2)) :
    HasLocalContribution (spatialFamily f) (contDiff_spatialFamily f hf).continuous p :=
  hasLocalContribution (spatialFamily f) (contDiff_spatialFamily f hf) hreg p hp

theorem exists_small_generic_family (f : ℝ → Vector 3 → Vector 6)
    (hf : ContDiff ℝ ∞ (uncurry f)) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Vector 3 →L[ℝ] Vector 6, ‖A‖ < ε ∧
    ∃ hA : ContDiff ℝ ∞ (uncurry (DoublePointPerturbation.perturb f A)),
      RegularThreeSix (spatialFamily (DoublePointPerturbation.perturb f A)) ∧
      (∀ q : ℝ × (Vector 3 × Vector 3), q.2.1 ≠ q.2.2 →
        DoublePointPerturbation.difference f A q = 0 →
        Surjective (fderiv ℝ (DoublePointPerturbation.difference f A) q)) ∧
      ∀ p : ℝ × Vector 3,
        ¬ Injective (fderiv ℝ (DoublePointPerturbation.perturb f A p.1) p.2) →
        HasLocalContribution (spatialFamily (DoublePointPerturbation.perturb f A))
          (contDiff_spatialFamily _ hA).continuous p := by
  obtain ⟨A, hsmall, hreg, hoff⟩ := DoublePointPerturbation.exists_small_generic_family f hf
    (by simp [GLOrthonormalization.Vector]) (by simp [GLOrthonormalization.Vector]) hε
  have hA := DoublePointPerturbation.contDiff_perturb f hf A
  refine ⟨A, hsmall, hA, hreg, hoff, ?_⟩
  intro p hp
  exact has_local_contribution _ hA hreg p hp

end NoExoticSixSphere.GenericFamilyParity
