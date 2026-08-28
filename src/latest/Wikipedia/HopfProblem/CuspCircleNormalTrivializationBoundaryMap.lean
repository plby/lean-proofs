import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCuspNeighborhoodEquivariance
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationConifoldBoundary

/-!
# Actual normal-radius level images in the original threefold

Every positive radius strictly below the proved injectivity radius gives
a compact, genuinely embedded level in the original threefold. The map
is the restriction of the unchanged normal-product map. Its circle action
is the original threefold action, intertwined with the literal scalar
action on the normal-radius level.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open SpecialPeriods SpecialPeriods.Threefold
open SpecialPeriods.Threefold.VerticalAction SpecialPeriods.Threefold.Homology

local notation "Circle" => AddCircle (1 : ℝ)

attribute [local instance] Threefold.space_t2Space Threefold.chartedSpace

/-- The actual radius level lies inside the original injective round product chart. -/
def boundaryIntoRound (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius)
    (p : Conifold.ProductBoundary r) : roundNormalProduct :=
  ⟨p.val, by
    change radiusSq p.val.2 < injectiveRadius ^ 2
    rw [p.property]
    exact (sq_lt_sq₀ hr.le injectiveRadius_pos.le).mpr hri⟩

@[simp] theorem boundaryIntoRound_coe (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius)
    (p : Conifold.ProductBoundary r) :
    (boundaryIntoRound r hr hri p : RiemannSphere × Fibre) = p.val := rfl

theorem boundaryIntoRound_continuous (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius) :
    Continuous (boundaryIntoRound r hr hri) := continuous_subtype_val.subtype_mk _

theorem boundaryIntoRound_injective (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius) :
    Function.Injective (boundaryIntoRound r hr hri) := by
  intro p q h
  exact Subtype.ext (congrArg (fun z : roundNormalProduct => z.val) h)

/-- The literal normal-radius level map into the original threefold. -/
def boundaryMap (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius) :
    Conifold.ProductBoundary r → Threefold.Space :=
  roundProductMap ∘ boundaryIntoRound r hr hri

@[simp] theorem boundaryMap_eq_round (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius)
    (p : Conifold.ProductBoundary r) :
    boundaryMap r hr hri p = roundProductMap (boundaryIntoRound r hr hri p) := rfl

theorem boundaryMap_continuous (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius) :
    Continuous (boundaryMap r hr hri) :=
  roundProductMap_contMDiff.continuous.comp (boundaryIntoRound_continuous r hr hri)

theorem boundaryMap_injective (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius) :
    Function.Injective (boundaryMap r hr hri) :=
  roundProductMap_injective.comp (boundaryIntoRound_injective r hr hri)

/-- Compactness of the level and Hausdorffness of the original threefold give an embedding. -/
theorem boundaryMap_isClosedEmbedding (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius) :
    IsClosedEmbedding (boundaryMap r hr hri) :=
  (boundaryMap_continuous r hr hri).isClosedEmbedding (boundaryMap_injective r hr hri)

/-- The actual image of the radius level in the original threefold. -/
def boundaryImage (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius) :
    Set Threefold.Space := range (boundaryMap r hr hri)

theorem boundaryImage_isCompact (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius) :
    IsCompact (boundaryImage r hr hri) := isCompact_range (boundaryMap_continuous r hr hri)

theorem boundaryImage_subset_neighborhood (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) : boundaryImage r hr hri ⊆ fixedCurveNeighborhood := by
  rintro _ ⟨p, rfl⟩
  exact mem_range_self (boundaryIntoRound r hr hri p)

/-- The original product radius level is homeomorphic to its actual embedded image. -/
def boundaryHomeomorph (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius) :
    Conifold.ProductBoundary r ≃ₜ boundaryImage r hr hri :=
  (boundaryMap_isClosedEmbedding r hr hri).isEmbedding.toHomeomorph

@[simp] theorem boundaryHomeomorph_coe (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius)
    (p : Conifold.ProductBoundary r) :
    (boundaryHomeomorph r hr hri p : Threefold.Space) = boundaryMap r hr hri p := rfl

/-- The positive radius level avoids the actual named fixed curve. -/
theorem boundaryMap_not_mem_doubleCurve (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius)
    (p : Conifold.ProductBoundary r) : boundaryMap r hr hri p ∉ CuspGeometry.doubleCurve 1 := by
  intro hp
  have hz : p.val.2 = 0 :=
    (roundProductMap_mem_doubleCurve_iff (boundaryIntoRound r hr hri p)).mp hp
  have h := p.property
  rw [hz, radiusSq_zero] at h
  exact (ne_of_gt (sq_pos_of_pos hr)) h.symm

@[simp] theorem boundaryIntoRound_circle (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius)
    (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (p : Conifold.ProductBoundary r) :
    boundaryIntoRound r hr hri (Conifold.productBoundaryCircle (u : ℂ) hu p) =
      roundNormalAction u hu (boundaryIntoRound r hr hri p) := rfl

/-- Exact equivariance with the original multiplicative action on the threefold. -/
theorem boundaryMap_normalAction (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius)
    (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (p : Conifold.ProductBoundary r) :
    actionBiholomorph u (boundaryMap r hr hri p) =
      boundaryMap r hr hri (Conifold.productBoundaryCircle (u : ℂ) hu p) :=
  roundProductMap_normalAction u hu (boundaryIntoRound r hr hri p)

/-- The boundary formula uses the original period-one additive-circle parameter. -/
theorem boundaryMap_circleAction (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius)
    (t : Circle) (p : Conifold.ProductBoundary r) :
    DeltaSweep.actionMap (t, boundaryMap r hr hri p) =
      boundaryMap r hr hri (Conifold.productBoundaryCircle
        (DeltaSweep.circleParameter t : ℂ)
        (FixedCoordinates.CircleOrbit.circleParameter_norm t) p) :=
  boundaryMap_normalAction r hr hri _ _ p

theorem actionMap_mem_boundaryImage (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius)
    (t : Circle) {x : Threefold.Space} (hx : x ∈ boundaryImage r hr hri) :
    DeltaSweep.actionMap (t, x) ∈ boundaryImage r hr hri := by
  obtain ⟨p, rfl⟩ := hx
  exact ⟨Conifold.productBoundaryCircle (DeltaSweep.circleParameter t : ℂ)
    (FixedCoordinates.CircleOrbit.circleParameter_norm t) p,
    (boundaryMap_circleAction r hr hri t p).symm⟩

/-- The unchanged global circle action restricted to the proved invariant radius image. -/
def boundaryImageCircleAction (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius)
    (t : Circle) (x : boundaryImage r hr hri) : boundaryImage r hr hri :=
  ⟨DeltaSweep.actionMap (t, x), actionMap_mem_boundaryImage r hr hri t x.property⟩

@[simp] theorem boundaryImageCircleAction_coe (r : ℝ) (hr : 0 < r)
    (hri : r < injectiveRadius) (t : Circle) (x : boundaryImage r hr hri) :
    (boundaryImageCircleAction r hr hri t x : Threefold.Space) =
      DeltaSweep.actionMap (t, x) := rfl

/-- The actual image homeomorphism preserves the literal circle action. -/
theorem boundaryHomeomorph_circleAction (r : ℝ) (hr : 0 < r) (hri : r < injectiveRadius)
    (t : Circle) (p : Conifold.ProductBoundary r) :
    boundaryImageCircleAction r hr hri t (boundaryHomeomorph r hr hri p) =
      boundaryHomeomorph r hr hri (Conifold.productBoundaryCircle
        (DeltaSweep.circleParameter t : ℂ)
        (FixedCoordinates.CircleOrbit.circleParameter_norm t) p) := by
  apply Subtype.ext
  exact boundaryMap_circleAction r hr hri t p

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
