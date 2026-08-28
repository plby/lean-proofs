import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfProductImmersion
import Wikipedia.HopfProblem.DegreeCollapseGeneralRegularFiberIdentification
import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfSquareSmooth

/-!
# An unconditional smooth product identification of the actual Hopf-square fiber

Choose the already proved relative smoothing of the actual polynomial Hopf
square. Its entire regular fiber is diffeomorphic to the standard product
S3 × S3. The diffeomorphism retains the specified ambient inclusion, and the
smoothed map agrees with the original map as a germ along that fiber.
The smoothing homotopy is unbased; no new based marking is asserted here.
-/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfProductDiffeomorph

open NoExoticSixSphere QuaternionicHopf QuaternionicHopfProductImmersion

def smoothMap : C(Sphere 16, Sphere 10) :=
  Classical.choose QuaternionicHopfSquareSmooth.exists_smooth_square

theorem smoothMap_contMDiff : ContMDiff (𝓡 16) (𝓡 10) ∞ smoothMap :=
  (Classical.choose_spec QuaternionicHopfSquareSmooth.exists_smooth_square).1

theorem smoothMap_homotopic : (SphereSmash.squareMap suspendedMap).Homotopic smoothMap :=
  (Classical.choose_spec QuaternionicHopfSquareSmooth.exists_smooth_square).2.1

theorem smoothMap_fiber (x : Sphere 16) :
    smoothMap x = QuaternionicHopfProductFiber.point ↔
      SphereSmash.squareMap suspendedMap x = QuaternionicHopfProductFiber.point :=
  (Classical.choose_spec QuaternionicHopfSquareSmooth.exists_smooth_square).2.2.1 x

theorem smoothMap_regular (x : Sphere 16)
    (hx : smoothMap x = QuaternionicHopfProductFiber.point) :
    Function.Surjective (mfderiv (𝓡 16) (𝓡 10) smoothMap x) :=
  (Classical.choose_spec QuaternionicHopfSquareSmooth.exists_smooth_square).2.2.2.1 x hx

theorem smoothMap_germ :
    ∃ U : Set (Sphere 16), IsOpen U ∧
      (SphereSmash.squareMap suspendedMap) ⁻¹' {QuaternionicHopfProductFiber.point} ⊆ U ∧
      EqOn smoothMap (SphereSmash.squareMap suspendedMap) U :=
  (Classical.choose_spec QuaternionicHopfSquareSmooth.exists_smooth_square).2.2.2.2

theorem smoothMap_eventuallyEq_square (x : Sphere 16)
    (hx : smoothMap x = QuaternionicHopfProductFiber.point) :
    (smoothMap : Sphere 16 → Sphere 10) =ᶠ[𝓝 x] SphereSmash.squareMap suspendedMap := by
  obtain ⟨U, hU, hFU, heq⟩ := smoothMap_germ
  exact Filter.eventuallyEq_of_mem (hU.mem_nhds (hFU ((smoothMap_fiber x).mp hx))) heq

theorem smoothMap_mfderiv_eq_square (x : Sphere 16)
    (hx : smoothMap x = QuaternionicHopfProductFiber.point) :
    mfderiv (𝓡 16) (𝓡 10) smoothMap x =
      mfderiv (𝓡 16) (𝓡 10) (SphereSmash.squareMap suspendedMap) x :=
  (smoothMap_eventuallyEq_square x hx).mfderiv_eq

theorem smoothMap_fiber_range (x : Sphere 16) :
    smoothMap x = QuaternionicHopfProductFiber.point ↔ ∃ p, fiberInclusion p = x :=
  (smoothMap_fiber x).trans (fiberInclusion_range x)

theorem smoothMap_fiberInclusion (p : Sphere 3 × Sphere 3) :
    smoothMap (fiberInclusion p) = QuaternionicHopfProductFiber.point :=
  (smoothMap_fiber_range (fiberInclusion p)).mpr ⟨p, rfl⟩

@[instance_reducible]
def fiberAtlas :
    ChartedSpace (V 6) {x : Sphere 16 // smoothMap x = QuaternionicHopfProductFiber.point} :=
  regularFiberAtlas smoothMap smoothMap_contMDiff QuaternionicHopfProductFiber.point
    smoothMap_regular 6 (by simp)

theorem fiber_isManifold : letI := fiberAtlas;
    IsManifold (𝓡 6) ∞ {x : Sphere 16 // smoothMap x = QuaternionicHopfProductFiber.point} :=
  regularFiber_isManifold smoothMap smoothMap_contMDiff QuaternionicHopfProductFiber.point
    smoothMap_regular 6 (by simp)

def fiberDiffeomorph : letI := fiberAtlas;
    (Sphere 3 × Sphere 3) ≃ₘ⟮(𝓡 3).prod (𝓡 3), 𝓡 6⟯
      {x : Sphere 16 // smoothMap x = QuaternionicHopfProductFiber.point} :=
  GeneralRegularFiberIdentification.diffeomorphToFiber smoothMap smoothMap_contMDiff
    QuaternionicHopfProductFiber.point smoothMap_regular 6 (by simp)
    (by simp [Module.finrank_prod]) fiberInclusion contMDiff_fiberInclusion
    fiberInclusion_injective fiberInclusion_mfderiv_injective smoothMap_fiber_range

theorem fiberDiffeomorph_val (p : Sphere 3 × Sphere 3) : letI := fiberAtlas;
    (fiberDiffeomorph p).val = fiberInclusion p := rfl

theorem fiberDiffeomorph_formula (p : Sphere 3 × Sphere 3) : letI := fiberAtlas;
    (fiberDiffeomorph p).val = JamesSphere.pairing 8
      (ProductSphereFiber.slice 7 (QuaternionicHopfSouthFiber.fiberPoint p.1),
        ProductSphereFiber.slice 7 (QuaternionicHopfSouthFiber.fiberPoint p.2)) := rfl

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfProductDiffeomorph
