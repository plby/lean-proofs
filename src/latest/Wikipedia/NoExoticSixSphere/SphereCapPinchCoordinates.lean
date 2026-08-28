import Wikipedia.NoExoticSixSphere.SphereSumCapCoordinates
import Wikipedia.NoExoticSixSphere.SphereFoldHemisphereInverse
import Wikipedia.NoExoticSixSphere.SphereCompactificationChart

/-!
# The actual cap coordinates compared with the sphere pinch

The northern fold and the gnomonic hemisphere chart give a full-source
chart omitting precisely the collapsed pole. Compactifying this chart and
the complementary reference chart constructs a homeomorphism of the actual
three-sphere. It carries the polynomial fold to the exact cap map on the
open northern hemisphere, and carries the collapsed pole to the original
reference-chart center. No orientation convention is suppressed here.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

abbrev pinchPole := spherePole 3

theorem pinchPole_height (x : Sphere 3) : SphereFold.height pinchPole x = x.val 0 := by
  simp [SphereFold.height, spherePole, EuclideanSpace.inner_single_left]

def pinchFiniteChart : PartialDiffeomorph (𝓡 3) (𝓡 3) (Vector 3) (Sphere 3) ∞ := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact gnomonicChart.symm.trans (SphereFold.north (n := 3) pinchPole)

theorem pinchFiniteChart_apply (v : Vector 3) :
    pinchFiniteChart v = SphereFold.fold pinchPole (gnomonicInverse v) := rfl

theorem pinchFiniteChart_source : pinchFiniteChart.source = univ := by
  ext v
  change (v ∈ (univ : Set (Vector 3)) ∧
    0 < SphereFold.height pinchPole (gnomonicInverse v)) ↔ v ∈ univ
  rw [pinchPole_height]
  simp only [mem_univ, gnomonicInverse_head_pos, and_self]

theorem pinchFiniteChart_target : pinchFiniteChart.target = {antipode pinchPole}ᶜ := by
  ext x
  change (x ≠ antipode pinchPole ∧ 0 < (SphereFold.northInverse pinchPole x).val 0) ↔
    x ≠ antipode pinchPole
  refine ⟨And.left, fun hx ↦ ⟨hx, ?_⟩⟩
  rw [← pinchPole_height]
  exact SphereFold.height_northInverse_pos pinchPole x hx

def pinchScaling (ε : ℝ) (hε : ε ≠ 0) : Vector 3 ≃L[ℝ] Vector 3 :=
  (LinearEquiv.smulOfNeZero ℝ (Vector 3) ε hε).toContinuousLinearEquiv

def pinchScaledChart (ε : ℝ) (hε : ε ≠ 0) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) (Vector 3) (Sphere 3) ∞ :=
  (pinchScaling ε hε).toDiffeomorph.toPartialDiffeomorph.trans pinchFiniteChart

theorem pinchScaledChart_apply (ε : ℝ) (hε : ε ≠ 0) (v : Vector 3) :
    pinchScaledChart ε hε v = SphereFold.fold pinchPole (gnomonicInverse (ε • v)) := rfl

theorem pinchScaledChart_source (ε : ℝ) (hε : ε ≠ 0) :
    (pinchScaledChart ε hε).source = univ := by
  ext v
  change (v ∈ (univ : Set (Vector 3)) ∧ pinchScaling ε hε v ∈ pinchFiniteChart.source) ↔
    v ∈ univ
  rw [pinchFiniteChart_source]
  simp only [mem_univ, and_self]

theorem pinchScaledChart_target (ε : ℝ) (hε : ε ≠ 0) :
    (pinchScaledChart ε hε).target = {antipode pinchPole}ᶜ := by
  ext x
  change (x ∈ pinchFiniteChart.target ∧ pinchFiniteChart.symm x ∈
    (univ : Set (Vector 3))) ↔ x ∈ {antipode pinchPole}ᶜ
  rw [pinchFiniteChart_target]
  simp only [mem_univ, and_true]

theorem sourceComplementChart_target : sourceComplementChart.target = {sourceChart 0}ᶜ := by
  rw [Wikipedia.SmoothSixDPoincare.SphereCoordinates.referenceComplementChart_target,
    Wikipedia.SmoothSixDPoincare.SphereCoordinates.referenceChart_zero]

def compactifySourceChart
    (c : PartialDiffeomorph (𝓡 3) (𝓡 3) (Vector 3) (Sphere 3) ∞)
    (p : Sphere 3) (hs : c.source = univ) (ht : c.target = {p}ᶜ) :
    OnePoint (Vector 3) ≃ₜ Sphere 3 := by
  have hr : range (c : Vector 3 → Sphere 3) = {p}ᶜ := by
    rw [← ht]
    apply Subset.antisymm
    · rintro _ ⟨v, rfl⟩
      exact c.map_source (by rw [hs]; trivial)
    · intro x hx
      exact ⟨c.symm x, c.right_inv hx⟩
  exact OnePoint.equivOfIsEmbeddingOfRangeEq p c
    (c.toOpenPartialHomeomorph.isEmbedding hs) hr

theorem compactifySourceChart_coe
    (c : PartialDiffeomorph (𝓡 3) (𝓡 3) (Vector 3) (Sphere 3) ∞)
    (p : Sphere 3) (hs : c.source = univ) (ht : c.target = {p}ᶜ) (v : Vector 3) :
    compactifySourceChart c p hs ht (v : OnePoint (Vector 3)) = c v := by
  unfold compactifySourceChart
  exact OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe _ _ _ _ _

theorem compactifySourceChart_infty
    (c : PartialDiffeomorph (𝓡 3) (𝓡 3) (Vector 3) (Sphere 3) ∞)
    (p : Sphere 3) (hs : c.source = univ) (ht : c.target = {p}ᶜ) :
    compactifySourceChart c p hs ht OnePoint.infty = p := by
  unfold compactifySourceChart
  exact OnePoint.equivOfIsEmbeddingOfRangeEq_apply_infty _ _ _ _

def capPinchComparison (ε : ℝ) (hε : ε ≠ 0) : Sphere 3 ≃ₜ Sphere 3 :=
  (compactifySourceChart (pinchScaledChart ε hε) (antipode pinchPole)
    (pinchScaledChart_source ε hε) (pinchScaledChart_target ε hε)).symm.trans
  (compactifySourceChart sourceComplementChart (sourceChart 0)
    sourceComplementChart_source sourceComplementChart_target)

theorem capPinchComparison_finite (ε : ℝ) (hε : ε ≠ 0) (v : Vector 3) :
    capPinchComparison ε hε (pinchScaledChart ε hε v) = sourceComplementChart v := by
  let D := compactifySourceChart (pinchScaledChart ε hε) (antipode pinchPole)
    (pinchScaledChart_source ε hε) (pinchScaledChart_target ε hε)
  let T := compactifySourceChart sourceComplementChart (sourceChart 0)
    sourceComplementChart_source sourceComplementChart_target
  have hd : D (v : OnePoint (Vector 3)) = pinchScaledChart ε hε v :=
    compactifySourceChart_coe _ _ _ _ _
  change T (D.symm (pinchScaledChart ε hε v)) = sourceComplementChart v
  rw [← hd, Homeomorph.symm_apply_apply]
  exact compactifySourceChart_coe _ _ _ _ _

theorem capPinchComparison_base (ε : ℝ) (hε : ε ≠ 0) :
    capPinchComparison ε hε (antipode pinchPole) = sourceChart 0 := by
  let D := compactifySourceChart (pinchScaledChart ε hε) (antipode pinchPole)
    (pinchScaledChart_source ε hε) (pinchScaledChart_target ε hε)
  let T := compactifySourceChart sourceComplementChart (sourceChart 0)
    sourceComplementChart_source sourceComplementChart_target
  have hd : D OnePoint.infty = antipode pinchPole := compactifySourceChart_infty _ _ _ _
  change T (D.symm (antipode pinchPole)) = sourceChart 0
  rw [← hd, Homeomorph.symm_apply_apply]
  exact compactifySourceChart_infty _ _ _ _

theorem capPinchComparison_fold_north (ε : ℝ) (hε : ε ≠ 0) {x : Sphere 3}
    (hx : 0 < x.val 0) :
    capPinchComparison ε hε (SphereFold.fold pinchPole x) = sphereCap ε x := by
  let v := ε⁻¹ • gnomonic x
  have he : pinchScaledChart ε hε v = SphereFold.fold pinchPole x := by
    rw [pinchScaledChart_apply]
    dsimp [v]
    rw [smul_inv_smul₀ hε, gnomonicInverse_gnomonic x hx]
  rw [← he, capPinchComparison_finite]
  rfl

end NoExoticSixSphere.SphereSumNeck
