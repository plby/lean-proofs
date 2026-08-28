import Wikipedia.HopfProblem.DegreeCollapseSphereProductSmoothRegularity
import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfProductFiber
import Wikipedia.NoExoticSixSphere.FiberPreservingSphereSmoothing

/-!
# A smooth representative of the actual Hopf square with its exact regular fiber

The original product suspension and smash square are smooth away from
their based values. The specified S3 × S3 fiber has surjective ORIGINAL
native derivative at every point. Relative smoothing preserves the whole
fiber and the map on a neighborhood, hence also its derivative there.
No product normal-framing or geometric Arf calculation is assumed.
-/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfSquareSmooth

open NoExoticSixSphere QuaternionicHopf
open SphereProductSmoothRegularity

theorem suspended_smoothAway : SmoothAway suspendedMap :=
  product_smoothAway basedMap (fun _ _ ↦ contMDiff_sphereMap.contMDiffAt)

theorem square_smoothAway : SmoothAway (SphereSmash.basedSquare suspendedMap) :=
  SphereProductSmoothRegularity.square_smoothAway suspendedMap suspended_smoothAway

theorem suspended_regular (x : Sphere 8)
    (hx : suspendedMap.val x = QuaternionicHopfProductFiber.suspendedPoint) :
    Function.Surjective (mfderiv (𝓡 8) (𝓡 5) suspendedMap.val x) := by
  obtain ⟨q, hq⟩ := QuaternionicHopfProductFiber.suspendedFiberHomeomorph.surjective ⟨x, hx⟩
  have hv : ProductSphereFiber.slice 7 (QuaternionicHopfSouthFiber.fiberPoint q) = x :=
    (QuaternionicHopfProductFiber.suspendedFiberHomeomorph_val q).symm.trans
      (congrArg Subtype.val hq)
  have hb : basedMap.val (QuaternionicHopfSouthFiber.fiberPoint q) ≠ spherePole 4 := by
    intro h
    exact QuaternionicHopfSouthFiber.point_ne_pole
      ((QuaternionicHopfSouthFiber.sphereMap_fiberPoint q).symm.trans h)
  have hs := QuaternionicHopfSouthRegularity.south_regular
    (QuaternionicHopfSouthFiber.fiberPoint q) (QuaternionicHopfSouthFiber.sphereMap_fiberPoint q)
  have hr := product_regular_at_slice basedMap (QuaternionicHopfSouthFiber.fiberPoint q)
    contMDiff_sphereMap.contMDiffAt hb hs
  exact hv ▸ hr

theorem square_regular (x : Sphere 16)
    (hx : SphereSmash.squareMap suspendedMap x = QuaternionicHopfProductFiber.point) :
    Function.Surjective (mfderiv (𝓡 16) (𝓡 10) (SphereSmash.squareMap suspendedMap) x) := by
  obtain ⟨p, hp⟩ := (QuaternionicHopfProductFiber.square_fiber_range x).mp hx
  let u := ProductSphereFiber.slice 7 (QuaternionicHopfSouthFiber.fiberPoint p.1)
  let v := ProductSphereFiber.slice 7 (QuaternionicHopfSouthFiber.fiberPoint p.2)
  have hu : suspendedMap.val u = QuaternionicHopfProductFiber.suspendedPoint :=
    (QuaternionicHopfProductFiber.suspendedFiberHomeomorph p.1).property
  have hv : suspendedMap.val v = QuaternionicHopfProductFiber.suspendedPoint :=
    (QuaternionicHopfProductFiber.suspendedFiberHomeomorph p.2).property
  have hb : suspendedMap.val u ≠ spherePole 5 :=
    fun h ↦ QuaternionicHopfProductFiber.suspendedPoint_ne_pole (hu.symm.trans h)
  have hc : suspendedMap.val v ≠ spherePole 5 :=
    fun h ↦ QuaternionicHopfProductFiber.suspendedPoint_ne_pole (hv.symm.trans h)
  have hr := square_regular_at_pairing suspendedMap u v
    (suspended_smoothAway u hb) (suspended_smoothAway v hc) hb hc
    (suspended_regular u hu) (suspended_regular v hv)
  exact hp ▸ hr

def smoothDomain : Set (Sphere 16) :=
  {x | SphereSmash.squareMap suspendedMap x ≠ spherePole 10}

theorem smoothDomain_open : IsOpen smoothDomain :=
  isClosed_singleton.isOpen_compl.preimage (SphereSmash.squareMap suspendedMap).continuous

theorem contMDiffOn_square :
    ContMDiffOn (𝓡 16) (𝓡 10) ∞ (SphereSmash.squareMap suspendedMap) smoothDomain :=
  smoothAway_contMDiffOn (SphereSmash.basedSquare suspendedMap) square_smoothAway

theorem fiber_subset_smoothDomain :
    (SphereSmash.squareMap suspendedMap) ⁻¹' {QuaternionicHopfProductFiber.point} ⊆
      smoothDomain := by
  intro x hx
  change SphereSmash.squareMap suspendedMap x = QuaternionicHopfProductFiber.point at hx
  change SphereSmash.squareMap suspendedMap x ≠ spherePole 10
  rw [hx]
  exact QuaternionicHopfProductFiber.point_ne_pole

theorem exists_smooth_square :
    ∃ g : C(Sphere 16, Sphere 10), ContMDiff (𝓡 16) (𝓡 10) ∞ g ∧
      (SphereSmash.squareMap suspendedMap).Homotopic g ∧
      (∀ x, g x = QuaternionicHopfProductFiber.point ↔
        SphereSmash.squareMap suspendedMap x = QuaternionicHopfProductFiber.point) ∧
      (∀ x, g x = QuaternionicHopfProductFiber.point →
        Function.Surjective (mfderiv (𝓡 16) (𝓡 10) g x)) ∧
      ∃ U : Set (Sphere 16), IsOpen U ∧
        (SphereSmash.squareMap suspendedMap) ⁻¹' {QuaternionicHopfProductFiber.point} ⊆ U ∧
        EqOn g (SphereSmash.squareMap suspendedMap) U := by
  obtain ⟨g, hg, H, hfiber, U, hU, hFU, heq⟩ :=
    exists_smoothSphereRepresentative_preserving_fiber (I := 𝓡 16) 10
      (SphereSmash.squareMap suspendedMap) QuaternionicHopfProductFiber.point
      smoothDomain_open contMDiffOn_square fiber_subset_smoothDomain
  refine ⟨g, hg, H, hfiber, ?_, U, hU, hFU, heq⟩
  intro x hx
  have hsq := (hfiber x).mp hx
  have hxU : x ∈ U := hFU hsq
  have hlocal : (g : Sphere 16 → Sphere 10) =ᶠ[𝓝 x] SphereSmash.squareMap suspendedMap :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hxU) heq
  have hd : mfderiv (𝓡 16) (𝓡 10) g x =
      mfderiv (𝓡 16) (𝓡 10) (SphereSmash.squareMap suspendedMap) x := hlocal.mfderiv_eq
  intro z
  obtain ⟨w, hw⟩ := square_regular x hsq z
  exact ⟨w, (congrArg (fun L : V 16 →L[ℝ] V 10 ↦ L w) hd).trans hw⟩

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfSquareSmooth
