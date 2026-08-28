import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalRegularBase
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalGeneratorElliptic
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorSourceOrdersCore

/-!
# The actual finite sphere coordinate on the elliptic discs

The original normalized sphere coordinate is pulled back through the actual
full-disc lift to the upper half-plane.  It agrees with the regular-base
coordinate on the punctured disc.  Its centered ambient germ has precisely
the proved elliptic branching order, three or four.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison

open Triangle

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

/-- The actual normalized finite sphere value at each elliptic center. -/
def centerValue : Elliptic.Kind → ℂ
  | .three => 0
  | .four => 1

@[simp] theorem centerValue_three : centerValue .three = 0 := rfl

@[simp] theorem centerValue_four : centerValue .four = 1 := rfl

/-- The genuine global finite coordinate evaluated on the actual elliptic lift. -/
def discCoordinate (j : Elliptic.Kind) (s : Disc) : ℂ :=
  BetaTorsor.sphereFiniteCoordinate
    (triangleSphereUniformization
      (triangleCompactifiedProjection (EllipticFilling.neighborhoodLift j s)))

theorem discCoordinate_eq_finiteProjection (j : Elliptic.Kind) (s : Disc) :
    discCoordinate j s =
      BetaTorsor.finiteProjection triangleSphereUniformization
        (EllipticFilling.neighborhoodLift j s) := rfl

theorem discCoordinate_target_ne_infty (j : Elliptic.Kind) (s : Disc) :
    triangleSphereUniformization
        (triangleCompactifiedProjection (EllipticFilling.neighborhoodLift j s)) ≠
      (∞ : RiemannSphere) :=
  BetaTorsor.finiteOrbitCoordinate_target_ne_infty triangleSphereUniformization
    triangleSphereUniformization_cusp
    (triangleOrbitProjection (EllipticFilling.neighborhoodLift j s))

@[simp] theorem discCoordinate_coe (j : Elliptic.Kind) (s : Disc) :
    (discCoordinate j s : RiemannSphere) =
      triangleSphereUniformization
        (triangleCompactifiedProjection (EllipticFilling.neighborhoodLift j s)) :=
  BetaTorsor.sphereFiniteCoordinate_coe_apply (discCoordinate_target_ne_infty j s)

theorem discCoordinate_holomorphic (j : Elliptic.Kind) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (discCoordinate j) :=
  (BetaTorsor.finiteProjection_holomorphic triangleSphereUniformization
    triangleSphereUniformization_cusp).comp (EllipticFilling.neighborhoodLift_holomorphic j)

theorem finiteProjection_center (j : Elliptic.Kind) :
    BetaTorsor.finiteProjection triangleSphereUniformization (ellipticCenter j) =
      centerValue j := by
  cases j
  · exact MuTorsor.SourceOrders.finiteProjection_centerOne triangleSphereUniformization
      triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
  · exact MuTorsor.SourceOrders.finiteProjection_centerTwo triangleSphereUniformization
      triangleSphereUniformization_cusp triangleSphereUniformization_centerTwo

@[simp] theorem discCoordinate_zero (j : Elliptic.Kind) :
    discCoordinate j discZero = centerValue j := by
  rw [discCoordinate_eq_finiteProjection, EllipticFilling.neighborhoodLift_zero,
    finiteProjection_center]

/-- On the actual punctured lift, this is exactly the regular global coordinate. -/
theorem discCoordinate_localBase (j : Elliptic.Kind) (s : Elliptic.LogGauge.BaseStar) :
    discCoordinate j s.val = GlobalRegular.upstairsCoordinate (EllipticFilling.localBase j s) :=
  rfl

/-- Off the actual center, the finite projection and elliptic lift are both
local biholomorphisms for their existing native atlases. -/
theorem discCoordinate_isLocalDiffeomorphAt (j : Elliptic.Kind) (s : Disc)
    (hs : (s : ℂ) ≠ 0) : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (discCoordinate j) s := by
  have hreg : EllipticFilling.neighborhoodLift j s ∈ triangleRegularLocus :=
    EllipticFilling.localBase_regular j (⟨s, hs⟩ : Elliptic.LogGauge.BaseStar)
  have hp : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω
      (BetaTorsor.finiteProjection triangleSphereUniformization)
      (EllipticFilling.neighborhoodLift j s) :=
    (triangleOrbitProjection_isLocalDiffeomorphAt_of_regular hreg).comp
      (K := 𝓘(ℂ)) (P := ℂ)
      ((BetaTorsor.finiteOrbitBiholomorph triangleSphereUniformization
        triangleSphereUniformization_cusp).isLocalDiffeomorph _)
  exact (GlobalGenerator.neighborhoodLift_isLocalDiffeomorph j s).comp
    (K := 𝓘(ℂ)) (P := ℂ) hp

/-- The ambient function is obtained from the original inverse disc chart. -/
def discCoordinateExtension (j : Elliptic.Kind) : ℂ → ℂ :=
  SectionsUnit.discExtension (discCoordinate j)

@[simp] theorem discCoordinateExtension_coe (j : Elliptic.Kind) (s : Disc) :
    discCoordinateExtension j (s : ℂ) = discCoordinate j s := by
  change discCoordinate j ((chartAt ℂ discZero).symm ((chartAt ℂ discZero) s)) = _
  rw [(chartAt ℂ discZero).left_inv (by trivial)]

@[simp] theorem discCoordinateExtension_zero (j : Elliptic.Kind) :
    discCoordinateExtension j 0 = centerValue j :=
  (SectionsUnit.discExtension_zero (discCoordinate j)).trans (discCoordinate_zero j)

theorem discCoordinateExtension_analyticAt (j : Elliptic.Kind) :
    AnalyticAt ℂ (discCoordinateExtension j) 0 :=
  SectionsUnit.discExtension_analyticAt (discCoordinate_holomorphic j)

theorem discCoordinateExtension_analyticAt_coe (j : Elliptic.Kind) (s : Disc) :
    AnalyticAt ℂ (discCoordinateExtension j) (s : ℂ) := by
  have hs : (s : ℂ) ∈ (chartAt ℂ discZero).target :=
    (chartAt ℂ discZero).map_source (by trivial)
  have hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ discZero).symm (s : ℂ) :=
    contMDiffOn_chart_symm.contMDiffAt ((chartAt ℂ discZero).open_target.mem_nhds hs)
  exact ((discCoordinate_holomorphic j _).comp (s : ℂ) hc).contDiffAt.analyticAt

/-- The ambient extension preserves the genuine punctured-disc local
biholomorphism, since its source coordinate is the original disc chart. -/
theorem discCoordinateExtension_isLocalDiffeomorphAt_coe (j : Elliptic.Kind) (s : Disc)
    (hs : (s : ℂ) ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (discCoordinateExtension j) (s : ℂ) := by
  have hc : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ discZero).symm (s : ℂ) := by
    refine ⟨{
      toPartialEquiv := (chartAt ℂ discZero).symm.toPartialEquiv
      open_source := (chartAt ℂ discZero).open_target
      open_target := (chartAt ℂ discZero).open_source
      contMDiffOn_toFun := contMDiffOn_chart_symm
      contMDiffOn_invFun := contMDiffOn_chart },
      (chartAt ℂ discZero).map_source (by trivial), Set.eqOn_refl _ _⟩
  have he : (chartAt ℂ discZero).symm (s : ℂ) = s :=
    (chartAt ℂ discZero).left_inv (by trivial)
  have hd : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (discCoordinate j)
      ((chartAt ℂ discZero).symm (s : ℂ)) := by
    rw [he]
    exact discCoordinate_isLocalDiffeomorphAt j s hs
  exact hc.comp (K := 𝓘(ℂ)) (P := ℂ) hd

/-- The finite sphere coordinate has its actual elliptic ramification order
in the original full-disc chart, with no supplied order assumption. -/
theorem discCoordinateExtension_centered_order (j : Elliptic.Kind) :
    analyticOrderAt (fun z => discCoordinateExtension j z - centerValue j) 0 =
      (j.order : ℕ∞) := by
  calc
    _ = analyticOrderAt
        (fun z : ℂ => BetaTorsor.finiteProjection triangleSphereUniformization (ofComplex z) -
          centerValue j) (ellipticCenter j : ℂ) :=
      GlobalGenerator.discExtension_neighborhoodLift_order
        (fun z : ℍ => BetaTorsor.finiteProjection triangleSphereUniformization z -
          centerValue j) j
    _ = (j.order : ℕ∞) := by
      simpa only [finiteProjection_center] using
        MuTorsor.SourceOrders.finiteProjection_centered_order_center
          triangleSphereUniformization triangleSphereUniformization_cusp j

theorem discCoordinateExtension_order_three :
    analyticOrderAt (discCoordinateExtension .three) 0 = 3 := by
  simpa only [centerValue_three, sub_zero, Elliptic.Kind.order, Nat.cast_ofNat] using
    discCoordinateExtension_centered_order .three

theorem discCoordinateExtension_sub_one_order_four :
    analyticOrderAt (fun z => discCoordinateExtension .four z - 1) 0 = 4 :=
  discCoordinateExtension_centered_order .four

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison
