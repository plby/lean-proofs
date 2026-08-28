import Wikipedia.NoExoticSixSphere.SphereFourTubeExteriorConnectivity
import Wikipedia.HopfProblem.SingularMayerVietoris

/-!
# The actual core-complement and open-tube cover of the old half

The old nonnegative half is covered by its full core complement and the
open unit tube. The latter projects to the original sphere core and has
the literal zero-normal-coordinate section. These are maps of the actual
subspaces, with no homology-equivalence assumption.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
open Wikipedia.HopfProblem.SingularMayerVietoris

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [T2Space M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)

def halfCoreComplement (t : M → ℝ) : Set (NonnegativeHalf t) := {x | x.val ∉ core Φ}

def halfOpenTube (t : M → ℝ) : Set (NonnegativeHalf t) := {x | x.val ∈ openRegion Φ 1}

theorem isOpen_halfCoreComplement (hΦ : Φ.source = univ) (t : M → ℝ) :
    IsOpen (halfCoreComplement Φ t) :=
  (isClosed_core Φ hΦ).isOpen_compl.preimage continuous_subtype_val

theorem isOpen_halfOpenTube (hΦ : Φ.source = univ) (t : M → ℝ) :
    IsOpen (halfOpenTube Φ t) :=
  (isOpen_openRegion Φ hΦ 1).preimage continuous_subtype_val

theorem halfCoreComplement_union_halfOpenTube (t : M → ℝ) :
    halfCoreComplement Φ t ∪ halfOpenTube Φ t = univ := by
  ext x
  constructor
  · intro _
    exact mem_univ x
  · intro _
    by_cases hx : x.val ∈ core Φ
    · exact Or.inr (core_subset_openRegion_one Φ hx)
    · exact Or.inl hx

def forgetHalfCoreComplement (t : M → ℝ) : C(halfCoreComplement Φ t, CoreComplement Φ) :=
  ⟨fun x ↦ ⟨x.val.val, x.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

theorem halfTube_mem_target (hΦ : Φ.source = univ) (t : M → ℝ) (x : halfOpenTube Φ t) :
    x.val.val ∈ Φ.target := ((mem_openRegion_iff Φ hΦ 1 x.val.val).mp x.property).1

def halfTubeInverse (hΦ : Φ.source = univ) (t : M → ℝ) :
    C(halfOpenTube Φ t, Sphere 3 × Vector 4) :=
  ⟨fun x ↦ Φ.symm x.val.val, Φ.contMDiffOn_invFun.continuousOn.comp_continuous
    (continuous_subtype_val.comp continuous_subtype_val) (halfTube_mem_target Φ hΦ t)⟩

def halfTubeProjection (hΦ : Φ.source = univ) (t : M → ℝ) : C(halfOpenTube Φ t, Sphere 3) :=
  ContinuousMap.fst.comp (halfTubeInverse Φ hΦ t)

variable (hΦ : Φ.source = univ) (t : C(M, ℝ)) (hpos : ∀ x ∈ Φ.target, 0 < t x)

def coreInHalf : C(Sphere 3, NonnegativeHalf t) :=
  ⟨fun s ↦ ⟨Φ (s, 0), (hpos _
    (Φ.toPartialEquiv.map_source (hΦ.symm ▸ mem_univ _))).le⟩,
    ((contMDiff Φ hΦ).continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk _⟩

def tubeCore : C(Sphere 3, halfOpenTube Φ t) :=
  ⟨fun s ↦ ⟨coreInHalf Φ hΦ t hpos s, core_subset_openRegion_one Φ ⟨s, rfl⟩⟩,
    (coreInHalf Φ hΦ t hpos).continuous.subtype_mk _⟩

theorem halfTubeProjection_tubeCore :
    (halfTubeProjection Φ hΦ t).comp (tubeCore Φ hΦ t hpos) = ContinuousMap.id (Sphere 3) := by
  apply ContinuousMap.ext
  intro s
  exact congrArg Prod.fst (Φ.toPartialEquiv.left_inv (hΦ.symm ▸ mem_univ (s, 0)))

theorem inclusion_tubeCore :
    (subtypeInclusion (halfOpenTube Φ t)).comp (tubeCore Φ hΦ t hpos) =
      coreInHalf Φ hΦ t hpos := rfl

end NoExoticSixSphere.SphereFourTube
