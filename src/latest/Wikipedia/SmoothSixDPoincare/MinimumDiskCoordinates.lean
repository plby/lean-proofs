import Wikipedia.SmoothSixDPoincare.MorseExtrema
import Wikipedia.SmoothSixDPoincare.MorseHandleModel
import Wikipedia.SmoothSixDPoincare.Hemisphere

/-!
# Canonical Euclidean coordinates for a minimum disk

The zero negative factor shows that the positive factor has the original
manifold dimension. An orthonormal basis then identifies its unit disk
isometrically with the standard Euclidean unit disk, preserving its boundary.
-/

noncomputable section

open Set Metric Manifold
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

open Classical in
/-- The positive factor at a minimum has the original chart dimension. -/
theorem finrank_positive_of_localMin (hmin : IsLocalMin f p) :
    Module.finrank ℝ c.PositiveCoordinates = Module.finrank ℝ E := by
  let : Unique c.NegativeCoordinates :=
    { default := 0, uniq := c.negative_eq_zero_of_localMin hmin }
  let e : (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] c.PositiveCoordinates :=
    (MorseHandle.splitLinearEquiv c.weights).trans
      (LinearEquiv.uniqueProd (R := ℝ) (M := c.PositiveCoordinates) (M₂ := c.NegativeCoordinates))
  simpa using e.finrank_eq.symm

open Classical in
/-- Isometric standard coordinates for the positive factor at a local minimum. -/
def minimumPositiveIsometry (hmin : IsLocalMin f p) :
    c.PositiveCoordinates ≃ₗᵢ[ℝ] Hemisphere.Ambient (Module.finrank ℝ E) :=
  (stdOrthonormalBasis ℝ c.PositiveCoordinates).repr.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (c.finrank_positive_of_localMin hmin)))

open Classical in
/-- The positive-coordinate disk at a minimum is the standard disk of the manifold dimension. -/
def minimumDiskHomeomorph (hmin : IsLocalMin f p) :
    MorseHandle.UnitDisk c.PositiveCoordinates ≃ₜ Hemisphere.Ball (Module.finrank ℝ E) :=
  (c.minimumPositiveIsometry hmin).toHomeomorph.subtype
    (p := fun x => x ∈ closedBall 0 1) (q := fun x => x ∈ closedBall 0 1)
    (fun x => by
      simp only [mem_closedBall_zero_iff, LinearIsometryEquiv.coe_toHomeomorph,
        LinearIsometryEquiv.norm_map])

open Classical in
theorem norm_minimumDiskHomeomorph_symm (hmin : IsLocalMin f p)
    (v : Hemisphere.Ball (Module.finrank ℝ E)) :
    ‖((c.minimumDiskHomeomorph hmin).symm v : c.PositiveCoordinates)‖ =
      ‖(v : Hemisphere.Ambient (Module.finrank ℝ E))‖ := by
  change ‖(c.minimumPositiveIsometry hmin).symm (v : Hemisphere.Ambient (Module.finrank ℝ E))‖ = _
  exact (c.minimumPositiveIsometry hmin).symm.norm_map _

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
