import Wikipedia.HopfProblem.CuspCircleNormalTrivializationBoundaryMap
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationConifoldNormalization

/-!
# The embedded boundary and the native toric and conifold levels

The actual normal-radius image in the original threefold is homeomorphic
to the literal toric radius level and to the determinant-zero Frobenius
level. These comparisons compose the proved boundary homeomorphisms;
their point formulas retain the original maps and circle parameters.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open SpecialPeriods SpecialPeriods.Threefold
open SpecialPeriods.Threefold.VerticalAction SpecialPeriods.Threefold.Homology

local notation "Circle" => AddCircle (1 : ℝ)

/-- Inverse normal coordinates intertwine the unchanged global circle action. -/
theorem boundaryHomeomorph_symm_circleAction (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (t : Circle) (x : boundaryImage r hr hri) :
    (boundaryHomeomorph r hr hri).symm (boundaryImageCircleAction r hr hri t x) =
      Conifold.productBoundaryCircle (DeltaSweep.circleParameter t : ℂ)
        (FixedCoordinates.CircleOrbit.circleParameter_norm t)
        ((boundaryHomeomorph r hr hri).symm x) := by
  apply (boundaryHomeomorph r hr hri).injective
  simpa only [Homeomorph.apply_symm_apply] using
    boundaryHomeomorph_circleAction r hr hri t ((boundaryHomeomorph r hr hri).symm x)

/-- The actual embedded boundary is homeomorphic to the literal conifold matrix level. -/
def boundaryConifoldHomeomorph (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius) :
    boundaryImage r hr hri ≃ₜ ConifoldStandardBoundary.ConifoldBoundary r :=
  (boundaryHomeomorph r hr hri).symm.trans
    (Conifold.productBoundaryHomeomorph (ne_of_gt hr))

@[simp] theorem boundaryConifoldHomeomorph_apply_val (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (x : boundaryImage r hr hri) :
    (boundaryConifoldHomeomorph r hr hri x).val =
      Conifold.productMap ((boundaryHomeomorph r hr hri).symm x).val := rfl

/-- On the original parametrized image the comparison is exactly the original matrix map. -/
@[simp] theorem boundaryConifoldHomeomorph_boundaryHomeomorph (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (p : Conifold.ProductBoundary r) :
    boundaryConifoldHomeomorph r hr hri (boundaryHomeomorph r hr hri p) =
      Conifold.productBoundaryHomeomorph (ne_of_gt hr) p := by
  simp only [boundaryConifoldHomeomorph, Homeomorph.trans_apply,
    Homeomorph.symm_apply_apply]

/-- The inverse comparison is the actual original threefold boundary map. -/
@[simp] theorem boundaryConifoldHomeomorph_symm_coe (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (M : ConifoldStandardBoundary.ConifoldBoundary r) :
    ((boundaryConifoldHomeomorph r hr hri).symm M : Threefold.Space) =
      boundaryMap r hr hri ((Conifold.productBoundaryHomeomorph (ne_of_gt hr)).symm M) :=
  rfl

/-- The comparison has the literal opposite-weight matrix action of the original circle. -/
theorem boundaryConifoldHomeomorph_circleAction (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (t : Circle) (x : boundaryImage r hr hri) :
    boundaryConifoldHomeomorph r hr hri (boundaryImageCircleAction r hr hri t x) =
      ConifoldStandardBoundary.conifoldCircle (DeltaSweep.circleParameter t : ℂ)
        (FixedCoordinates.CircleOrbit.circleParameter_norm t)
        (boundaryConifoldHomeomorph r hr hri x) := by
  change Conifold.productBoundaryHomeomorph (ne_of_gt hr)
      ((boundaryHomeomorph r hr hri).symm (boundaryImageCircleAction r hr hri t x)) = _
  rw [boundaryHomeomorph_symm_circleAction]
  exact Conifold.productBoundaryHomeomorph_circle (ne_of_gt hr) _ _ _

theorem boundaryConifoldHomeomorph_symm_circleAction (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (t : Circle)
    (M : ConifoldStandardBoundary.ConifoldBoundary r) :
    (boundaryConifoldHomeomorph r hr hri).symm
        (ConifoldStandardBoundary.conifoldCircle (DeltaSweep.circleParameter t : ℂ)
          (FixedCoordinates.CircleOrbit.circleParameter_norm t) M) =
      boundaryImageCircleAction r hr hri t ((boundaryConifoldHomeomorph r hr hri).symm M) := by
  apply (boundaryConifoldHomeomorph r hr hri).injective
  simpa only [Homeomorph.apply_symm_apply] using
    (boundaryConifoldHomeomorph_circleAction r hr hri t
      ((boundaryConifoldHomeomorph r hr hri).symm M)).symm

/-- The actual embedded boundary is homeomorphic to the level in the native toric charts. -/
def boundaryToricHomeomorph (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius) :
    boundaryImage r hr hri ≃ₜ Conifold.ToricBoundary r :=
  (boundaryHomeomorph r hr hri).symm.trans (Conifold.productToricBoundaryHomeomorph r)

@[simp] theorem boundaryToricHomeomorph_apply_val (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (x : boundaryImage r hr hri) :
    (boundaryToricHomeomorph r hr hri x).val =
      toricNeighborhoodDiffeomorph ((boundaryHomeomorph r hr hri).symm x).val := rfl

@[simp] theorem boundaryToricHomeomorph_boundaryHomeomorph (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (p : Conifold.ProductBoundary r) :
    boundaryToricHomeomorph r hr hri (boundaryHomeomorph r hr hri p) =
      Conifold.productToricBoundaryHomeomorph r p := by
  simp only [boundaryToricHomeomorph, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]

@[simp] theorem boundaryToricHomeomorph_symm_coe (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (y : Conifold.ToricBoundary r) :
    ((boundaryToricHomeomorph r hr hri).symm y : Threefold.Space) =
      boundaryMap r hr hri ((Conifold.productToricBoundaryHomeomorph r).symm y) := rfl

/-- The toric comparison preserves the exact native normal-coordinate action. -/
theorem boundaryToricHomeomorph_circleAction (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (t : Circle) (x : boundaryImage r hr hri) :
    boundaryToricHomeomorph r hr hri (boundaryImageCircleAction r hr hri t x) =
      Conifold.toricBoundaryCircle (DeltaSweep.circleParameter t : ℂ)
        (FixedCoordinates.CircleOrbit.circleParameter_norm t)
        (boundaryToricHomeomorph r hr hri x) := by
  change Conifold.productToricBoundaryHomeomorph r
      ((boundaryHomeomorph r hr hri).symm (boundaryImageCircleAction r hr hri t x)) = _
  rw [boundaryHomeomorph_symm_circleAction]
  simp only [Conifold.toricBoundaryCircle, boundaryToricHomeomorph,
    Homeomorph.trans_apply, Homeomorph.symm_apply_apply]

theorem boundaryToricHomeomorph_symm_circleAction (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (t : Circle) (y : Conifold.ToricBoundary r) :
    (boundaryToricHomeomorph r hr hri).symm
        (Conifold.toricBoundaryCircle (DeltaSweep.circleParameter t : ℂ)
          (FixedCoordinates.CircleOrbit.circleParameter_norm t) y) =
      boundaryImageCircleAction r hr hri t ((boundaryToricHomeomorph r hr hri).symm y) := by
  apply (boundaryToricHomeomorph r hr hri).injective
  simpa only [Homeomorph.apply_symm_apply] using
    (boundaryToricHomeomorph_circleAction r hr hri t
      ((boundaryToricHomeomorph r hr hri).symm y)).symm

/-- The two comparisons agree with the original toric matrix map. -/
theorem boundaryConifoldHomeomorph_eq_toric (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (x : boundaryImage r hr hri) :
    boundaryConifoldHomeomorph r hr hri x =
      Conifold.toricBoundaryHomeomorph (ne_of_gt hr) (boundaryToricHomeomorph r hr hri x) := by
  simp only [boundaryConifoldHomeomorph, boundaryToricHomeomorph,
    Conifold.toricBoundaryHomeomorph, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]

/-- Every admissible radius gives the same fixed determinant-one smoothing boundary. -/
def boundaryNormalizedHomeomorph (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius) :
    boundaryImage r hr hri ≃ₜ ConifoldStandardBoundary.SmoothingBoundary 2 :=
  (boundaryHomeomorph r hr hri).symm.trans (Conifold.normalizedProductBoundaryHomeomorph hr)

/-- The normalization uses the original boundary matrix and the explicit radial homothety. -/
@[simp] theorem boundaryNormalizedHomeomorph_apply_val (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (x : boundaryImage r hr hri) :
    (boundaryNormalizedHomeomorph r hr hri x).val =
      ConifoldStandardBoundary.forward 2
        (ConifoldStandardBoundary.rescaleMatrix r 2
          (Conifold.productMap ((boundaryHomeomorph r hr hri).symm x).val)) := rfl

/-- The original unit normal `F/r` is retained explicitly by the normalized comparison. -/
theorem boundaryNormalizedHomeomorph_unitDirection (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (x : boundaryImage r hr hri) :
    (boundaryNormalizedHomeomorph r hr hri x).val =
      ConifoldStandardBoundary.forward 2
        ((2 : ℂ) • Conifold.productMap
          (((boundaryHomeomorph r hr hri).symm x).val.1,
            (r⁻¹ : ℝ) • ((boundaryHomeomorph r hr hri).symm x).val.2)) :=
  Conifold.normalizedProductBoundaryHomeomorph_unitDirection hr
    ((boundaryHomeomorph r hr hri).symm x)

@[simp] theorem boundaryNormalizedHomeomorph_boundaryHomeomorph (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (p : Conifold.ProductBoundary r) :
    boundaryNormalizedHomeomorph r hr hri (boundaryHomeomorph r hr hri p) =
      Conifold.normalizedProductBoundaryHomeomorph hr p := by
  simp only [boundaryNormalizedHomeomorph, Homeomorph.trans_apply,
    Homeomorph.symm_apply_apply]

@[simp] theorem boundaryNormalizedHomeomorph_symm_coe (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (M : ConifoldStandardBoundary.SmoothingBoundary 2) :
    ((boundaryNormalizedHomeomorph r hr hri).symm M : Threefold.Space) =
      boundaryMap r hr hri ((Conifold.normalizedProductBoundaryHomeomorph hr).symm M) :=
  rfl

/-- The actual threefold action becomes the literal smoothing matrix circle action. -/
theorem boundaryNormalizedHomeomorph_circleAction (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (t : Circle) (x : boundaryImage r hr hri) :
    boundaryNormalizedHomeomorph r hr hri (boundaryImageCircleAction r hr hri t x) =
      ConifoldStandardBoundary.smoothingCircle (DeltaSweep.circleParameter t : ℂ)
        (FixedCoordinates.CircleOrbit.circleParameter_norm t)
        (boundaryNormalizedHomeomorph r hr hri x) := by
  change Conifold.normalizedProductBoundaryHomeomorph hr
      ((boundaryHomeomorph r hr hri).symm (boundaryImageCircleAction r hr hri t x)) = _
  rw [boundaryHomeomorph_symm_circleAction]
  exact Conifold.normalizedProductBoundaryHomeomorph_circle hr _ _ _

theorem boundaryNormalizedHomeomorph_symm_circleAction (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (t : Circle)
    (M : ConifoldStandardBoundary.SmoothingBoundary 2) :
    (boundaryNormalizedHomeomorph r hr hri).symm
        (ConifoldStandardBoundary.smoothingCircle (DeltaSweep.circleParameter t : ℂ)
          (FixedCoordinates.CircleOrbit.circleParameter_norm t) M) =
      boundaryImageCircleAction r hr hri t
        ((boundaryNormalizedHomeomorph r hr hri).symm M) := by
  apply (boundaryNormalizedHomeomorph r hr hri).injective
  simpa only [Homeomorph.apply_symm_apply] using
    (boundaryNormalizedHomeomorph_circleAction r hr hri t
      ((boundaryNormalizedHomeomorph r hr hri).symm M)).symm

/-- The normalization factors through the proved actual conifold comparison. -/
theorem boundaryNormalizedHomeomorph_eq_conifold (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (x : boundaryImage r hr hri) :
    boundaryNormalizedHomeomorph r hr hri x =
      ConifoldStandardBoundary.normalizedBoundaryHomeomorph hr
        (boundaryConifoldHomeomorph r hr hri x) := rfl

/-- The same normalization is obtained directly from the native toric level. -/
theorem boundaryNormalizedHomeomorph_eq_toric (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (x : boundaryImage r hr hri) :
    boundaryNormalizedHomeomorph r hr hri x =
      Conifold.normalizedToricBoundaryHomeomorph hr (boundaryToricHomeomorph r hr hri x) := by
  rw [boundaryNormalizedHomeomorph_eq_conifold, boundaryConifoldHomeomorph_eq_toric]
  rfl

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
