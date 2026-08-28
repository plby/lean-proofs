import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyCapEquiv
import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyCapPartition
import Wikipedia.SmoothSixDPoincare.SmoothBoundaryDisk

/-!
# Native smooth sphere data for a disk cap

Standardness is a property of the open image component with its existing
smooth structure, not of a possibly nonsmooth cap parametrization. It is
preserved by native boundary diffeomorphisms and supplies an actual smooth-
boundary disk for reading the cap in the opposite direction.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} (U : SmoothBoundaryBody J)
  {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
  (j : C(PuncturedHandle.UnitSphere N, U.boundary)) (hopen : IsOpen (range j))

def HasStandardCapSphere : Prop :=
  ∀ n : ℕ, Module.finrank ℝ N = n + 1 →
    Nonempty (Diffeomorph J (𝓡 n) (U.capSphereOpen j hopen) (Hemisphere.Sphere n) ∞)

variable {U} {V : SmoothBoundaryBody J} (e : Equiv U V)
  (j' : C(PuncturedHandle.UnitSphere N, V.boundary)) (hopen' : IsOpen (range j'))
  (hface : ∀ u, e.boundary (j u) = j' u)

omit [NormedSpace ℝ N] in
include hface in
theorem capSphere_mem_iff (x : U.boundary) :
    x ∈ U.capSphereOpen j hopen ↔ e.boundary x ∈ V.capSphereOpen j' hopen' := by
  change x ∈ range j ↔ e.boundary x ∈ range j'
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, (hface u).symm⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, e.boundary.injective ((hface u).trans hu)⟩

def capSphereDiffeomorph :
    Diffeomorph J J (U.capSphereOpen j hopen) (V.capSphereOpen j' hopen') ∞ := by
  let h := e.boundary.toHomeomorph.subtype (capSphere_mem_iff j hopen e j' hopen' hface)
  refine {
    toEquiv := h.toEquiv
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff (V.capSphereOpen j' hopen') _).mp
    exact e.boundary.contMDiff.comp contMDiff_subtype_val
  · apply (ContMDiff.subtypeVal_comp_iff (U.capSphereOpen j hopen) _).mp
    exact e.boundary.symm.contMDiff.comp contMDiff_subtype_val

include hface in
theorem hasStandardCapSphere_transport (hs : U.HasStandardCapSphere j hopen) :
    V.HasStandardCapSphere j' hopen' := by
  intro n hn
  exact (hs n hn).map (fun s => (capSphereDiffeomorph j hopen e j' hopen' hface).symm.trans s)

variable [FiniteDimensional ℝ N]

omit [FiniteDimensional ℝ N] in
theorem hasStandardCapSphere_postcompose (hs : U.HasStandardCapSphere j hopen) :
    V.HasStandardCapSphere (capPostcompose e j) (capPostcompose_isOpen e j hopen) :=
  hasStandardCapSphere_transport j hopen e _ _ (fun _ => rfl) hs

variable (U) (hj : IsClosedEmbedding j)

def capDiskInclusion : C(U.capSphereOpen j hopen, MorseHandle.UnitDisk N) :=
  ⟨fun y => ⟨((U.capSphereCoordinates j hj hopen).symm y).val,
      sphere_subset_closedBall ((U.capSphereCoordinates j hj hopen).symm y).property⟩,
    (continuous_subtype_val.comp (U.capSphereCoordinates j hj hopen).symm.continuous).subtype_mk _⟩

theorem capDiskInclusion_isClosedEmbedding :
    IsClosedEmbedding (U.capDiskInclusion j hopen hj) := by
  let _ : CompactSpace (U.capSphereOpen j hopen) :=
    (U.capSphereCoordinates j hj hopen).compactSpace
  apply (U.capDiskInclusion j hopen hj).continuous.isClosedEmbedding
  intro x y h
  apply (U.capSphereCoordinates j hj hopen).symm.injective
  exact Subtype.ext (congrArg (fun u : MorseHandle.UnitDisk N => u.val) h)

def capDiskBody : SmoothBoundaryBody J := by
  let _ : CompactSpace (U.capSphereOpen j hopen) :=
    (U.capSphereCoordinates j hj hopen).compactSpace
  exact ofEmbedding (U.capDiskInclusion j hopen hj)
    (U.capDiskInclusion_isClosedEmbedding j hopen hj)

def capSmoothDisk (hs : U.HasStandardCapSphere j hopen) : SmoothBoundaryDisk J N where
  space := U.capDiskBody j hopen hj
  bodyCoordinates := Homeomorph.refl _
  boundaryCoordinates := (U.capSphereCoordinates j hj hopen).symm
  boundary_point _ := rfl
  boundarySphere := hs

theorem capSmoothDisk_inclusion (hs : U.HasStandardCapSphere j hopen)
    (u : PuncturedHandle.UnitSphere N) :
    ((U.capSmoothDisk j hopen hj hs).space.inclusion (U.capSphereCoordinates j hj hopen u)).val =
      u.val := by
  change (((U.capSphereCoordinates j hj hopen).symm
    (U.capSphereCoordinates j hj hopen u)).val) = u.val
  rw [Homeomorph.symm_apply_apply]

end Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody
