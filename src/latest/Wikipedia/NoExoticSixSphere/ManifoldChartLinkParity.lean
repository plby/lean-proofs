import Wikipedia.NoExoticSixSphere.ManifoldCoordinateChange
import Wikipedia.NoExoticSixSphere.PartialDiffeomorphDifferential
import Wikipedia.NoExoticSixSphere.InjectiveOperatorVaryingCoordinates

/-!
# Actual linking-sphere parity agrees in overlapping manifold charts

Both source and target chart pairs are valid throughout the supplied actual
four-ball. Their genuine transition derivatives and inverse derivatives give
continuous disk-extending coordinate changes. The actual chain rule then
identifies the two boundary operator maps, so their parities agree.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily

open GLOrthonormalization ManifoldAffineSphereFamily Stiefel
open Wikipedia.HopfProblem.DegreeCollapse

def spatialInCharts {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
    (g : ℝ → Sphere 3 → M) (s : SourceChart) (c : TargetChart n M) (q : ℝ × Sphere 3) :
    Vector 3 →L[ℝ] Vector n :=
  fderiv ℝ (fun z ↦ c (g q.1 (s.symm z))) (s q.2)

theorem sphereParity_eq_in_overlapping_charts {M : Type*}
    [TopologicalSpace M] [ChartedSpace (Vector 6) M]
    (g : ℝ → Sphere 3 → M)
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))
    (α : C(DiskCylinder.Disk (E := Vector 4), ℝ × Sphere 3))
    (s t : SourceChart) (c d : TargetChart 6 M)
    (hs : ∀ x, (α x).2 ∈ s.source) (ht : ∀ x, (α x).2 ∈ t.source)
    (hc : ∀ x, g (α x).1 (α x).2 ∈ c.source)
    (hd : ∀ x, g (α x).1 (α x).2 ∈ d.source)
    (F G : C(Sphere 3, Monomorphism.Space 6 3))
    (hF : ∀ v, (F v).val = spatialInCharts g s c (α (DiskCylinder.boundaryToDisk v)))
    (hG : ∀ v, (G v).val = spatialInCharts g t d (α (DiskCylinder.boundaryToDisk v))) :
    Monomorphism.sphereParity 1 G = Monomorphism.sphereParity 1 F := by
  let A := ManifoldCoordinates.transition c d
  let B := ManifoldCoordinates.transition t s
  let R : C(DiskCylinder.Disk (E := Vector 4), A.source) :=
    ⟨fun x ↦ ⟨c (g (α x).1 (α x).2),
      ManifoldCoordinates.mem_transition_source c d _ (hc x) (hd x)⟩,
      (c.toOpenPartialHomeomorph.continuousOn.comp_continuous
        (hg.continuous.comp α.continuous) hc).subtype_mk _⟩
  let Q : C(DiskCylinder.Disk (E := Vector 4), B.source) :=
    ⟨fun x ↦ ⟨t (α x).2, ManifoldCoordinates.mem_transition_source t s _ (ht x) (hs x)⟩,
      (t.toOpenPartialHomeomorph.continuousOn.comp_continuous
        (continuous_snd.comp α.continuous) ht).subtype_mk _⟩
  let U := fun x ↦ ChartDifferential.differential A (R x)
  let V := fun x ↦ ChartDifferential.differential B (Q x)
  apply Monomorphism.sphereParity_extending_linearCoordinates 1 U V
    ((ChartDifferential.continuous_differential A).comp R.continuous)
    ((ChartDifferential.continuous_inverse_differential A).comp R.continuous)
    ((ChartDifferential.continuous_differential B).comp Q.continuous)
    ((ChartDifferential.continuous_inverse_differential B).comp Q.continuous) F G
  intro v
  apply Subtype.ext
  change (G v).val = (U (DiskCylinder.boundaryToDisk v)).toContinuousLinearMap.comp
    ((F v).val.comp (V (DiskCylinder.boundaryToDisk v)).toContinuousLinearMap)
  rw [hG, hF]
  change spatialInCharts g t d (α (DiskCylinder.boundaryToDisk v)) =
    (ChartDifferential.differential A
      (R (DiskCylinder.boundaryToDisk v))).toContinuousLinearMap.comp
      ((spatialInCharts g s c (α (DiskCylinder.boundaryToDisk v))).comp
        (ChartDifferential.differential B
          (Q (DiskCylinder.boundaryToDisk v))).toContinuousLinearMap)
  rw [ChartDifferential.differential_toContinuousLinearMap,
    ChartDifferential.differential_toContinuousLinearMap]
  have hslice : ContMDiff (𝓡 3) (𝓡 6) ∞ (g (α (DiskCylinder.boundaryToDisk v)).1) :=
    hg.comp (contMDiff_const.prodMk contMDiff_id)
  exact ManifoldCoordinates.fderiv_change_charts
    (g (α (DiskCylinder.boundaryToDisk v)).1) (α (DiskCylinder.boundaryToDisk v)).2
    (hslice.mdifferentiableAt (by simp)) s t c d
    (hs _) (ht _) (hc _) (hd _)

end NoExoticSixSphere.SphereFamily
