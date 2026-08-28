import Wikipedia.NoExoticSixSphere.SphereFourTubeRetraction
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarPositiveCore
import Wikipedia.HopfProblem.OrbitPairImageComplementConnectivity
import Wikipedia.HopfProblem.OrbitPairImageComplementHigherConnectivity
import Wikipedia.HopfProblem.DegreeCollapseH2SphereNullhomotopy
import Wikipedia.HopfProblem.DegreeCollapseSmoothBigonFromLoops

/-!
# Two-connectivity of the actual positive core complement

Apply native image avoidance to the literal smooth three-sphere core
inside the positive interior. The dimension inequalities include the
homotopy direction. Nonemptiness is witnessed by a unit normal tube
point, not assumed. No assertion about the tube exterior is made here.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse
open Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
open Wikipedia.SmoothSixDPoincare
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

variable {M B : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] [TopologicalSpace B]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)
  (hΦ : Φ.source = univ) (t : C(M, ℝ)) (C : TimeCollar t B)
  (hpos : ∀ x ∈ Φ.target, 0 < t x)

def positiveCore : C(Sphere 3, C.positiveInterior) :=
  ⟨fun s ↦ ⟨Φ (s, 0), hpos _ (Φ.toPartialEquiv.map_source (hΦ.symm ▸ mem_univ _))⟩,
    (((contMDiff Φ hΦ).continuous).comp (continuous_id.prodMk continuous_const)).subtype_mk _⟩

theorem contMDiff_positiveCore : ContMDiff (𝓡 3) (𝓡 7) ∞ (positiveCore Φ hΦ t C hpos) :=
  (ContMDiff.subtypeVal_comp_iff C.positiveInterior _).mp
    ((contMDiff Φ hΦ).comp (contMDiff_id.prodMk contMDiff_const))

def positiveCoreComplement : TopologicalSpace.Opens C.positiveInterior :=
  ImageComplement.domain (positiveCore Φ hΦ t C hpos)

theorem mem_range_positiveCore_iff (x : C.positiveInterior) :
    x ∈ range (positiveCore Φ hΦ t C hpos) ↔ x.val ∈ core Φ := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, congrArg (fun y : C.positiveInterior ↦ y.val) hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, Subtype.ext hs⟩

def forgetPositiveComplement : C(positiveCoreComplement Φ hΦ t C hpos, CoreComplement Φ) :=
  ⟨fun x ↦ ⟨x.val.val, fun hx ↦ x.property
      ((mem_range_positiveCore_iff Φ hΦ t C hpos x.val).mpr hx)⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

theorem nonempty_positiveCoreComplement : Nonempty (positiveCoreComplement Φ hΦ t C hpos) := by
  let b : Sphere 3 := SphereHomology.basePoint 3
  have hxT : Φ (b, b.val) ∈ Φ.target :=
    Φ.toPartialEquiv.map_source (hΦ.symm ▸ mem_univ _)
  let x : C.positiveInterior := ⟨Φ (b, b.val), hpos _ hxT⟩
  refine ⟨⟨x, ?_⟩⟩
  intro hx
  have hz := (tube_mem_core_iff Φ hΦ (b, b.val)).mp
    ((mem_range_positiveCore_iff Φ hΦ t C hpos x).mp hx)
  exact ne_zero_of_mem_unit_sphere b hz

theorem simplyConnected_positiveCoreComplement [SimplyConnectedSpace (NonnegativeHalf t)] :
    SimplyConnectedSpace (positiveCoreComplement Φ hΦ t C hpos) := by
  let : SimplyConnectedSpace C.positiveInterior := C.interiorHalfHomotopyEquiv.simplyConnectedSpace
  let : Nonempty (ImageComplement.domain (positiveCore Φ hΦ t C hpos)) :=
    nonempty_positiveCoreComplement Φ hΦ t C hpos
  exact OrbitPair.ImageComplementConnectivity.simplyConnected (positiveCore Φ hΦ t C hpos)
    (contMDiff_positiveCore Φ hΦ t C hpos) (by norm_num [finrank_euclideanSpace_fin])
    ImmersedSource.circle_nullhomotopic_of_simplyConnected

theorem positiveCoreComplement_two_sphere_nullhomotopies
    [SimplyConnectedSpace (NonnegativeHalf t)]
    [Subsingleton (SingularHomology (NonnegativeHalf t) 2)]
    (f : C(Sphere 2, positiveCoreComplement Φ hΦ t C hpos)) :
    ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  let : SimplyConnectedSpace C.positiveInterior := C.interiorHalfHomotopyEquiv.simplyConnectedSpace
  let : Subsingleton (SingularHomology C.positiveInterior 2) :=
    (homotopyEquivHomologyEquiv C.interiorHalfHomotopyEquiv 2).injective.subsingleton
  apply ImageComplement.nullhomotopic_of_ambient_nullhomotopic (I := 𝓡 2)
    (positiveCore Φ hΦ t C hpos) (contMDiff_positiveCore Φ hΦ t C hpos)
    (by norm_num [finrank_euclideanSpace_fin]) f
  let g := (ImageComplement.inclusion (positiveCore Φ hΦ t C hpos)).comp f
  exact ⟨g (SphereCube.point 2), (two_sphere_nullhomotopic_of_homology g).homotopic⟩

theorem pi_two_positiveCoreComplement [SimplyConnectedSpace (NonnegativeHalf t)]
    [Subsingleton (SingularHomology (NonnegativeHalf t) 2)]
    (x : positiveCoreComplement Φ hΦ t C hpos) :
    Subsingleton (π_ 2 (positiveCoreComplement Φ hΦ t C hpos) x) :=
  OrbitPair.SphereNullhomotopy.pi_subsingleton_of_sphere_nullhomotopies (by decide)
    (positiveCoreComplement_two_sphere_nullhomotopies Φ hΦ t C hpos) x

end NoExoticSixSphere.SphereFourTube
