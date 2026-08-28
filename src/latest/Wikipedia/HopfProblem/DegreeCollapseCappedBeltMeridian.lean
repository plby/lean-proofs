import Wikipedia.HopfProblem.DegreeCollapseMeridianCap
import Wikipedia.HopfProblem.DegreeCollapseBeltMeridianCrossing
import Wikipedia.HopfProblem.DegreeCollapseStandardDiskCoordinates
import Wikipedia.NoExoticSixSphere.SphereCylinderVector

/-!
# An actual capped meridian sphere with one whole-belt intersection

Glue the original meridian disk to the constructed cap in the full belt
complement. The domain is the literal standard two-sphere. Its negative
hemisphere retains the exact smooth disk formula. The resulting map is
continuous globally; global smoothing and embedding are separate steps.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.BeltMeridianSphere

def pole : Hemisphere.Sphere 2 := Hemisphere.point false ⟨0, by simp⟩

def negativeHemisphere : Set (Hemisphere.Sphere 2) := {x | x.val 0 < 0}

theorem negativeHemisphere_open : IsOpen negativeHemisphere :=
  isOpen_lt ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val) continuous_const

theorem pole_mem_negativeHemisphere : pole ∈ negativeHemisphere := by
  change -Hemisphere.radius (⟨0, mem_closedBall_self zero_le_one⟩ : Hemisphere.Ball 2) < 0
  simp [Hemisphere.radius]

theorem smooth_tail : ContMDiff (𝓡 2) 𝓘(ℝ, Hemisphere.Ambient 2) ∞
    (Hemisphere.tail (n := 2)) := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient 3) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have he : (fun x : Hemisphere.Sphere 2 => NoExoticSixSphere.SphereCylinder.tail 1 x.val) =
      Hemisphere.tail := by
    funext x
    ext i
    rfl
  rw [← he]
  exact (NoExoticSixSphere.SphereCylinder.tail 1).contDiff.contMDiff.comp contMDiff_coe_sphere

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem exists_capped_meridian_sphere
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f)
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 1 + 1)]
    [SimplyConnectedSpace (S.data p).LowerLevel]
    (hdim : 6 ≤ Module.finrank ℝ E)
    (L : Hemisphere.Ambient 2 ≃ₗᵢ[ℝ] (S.data p).chart.NegativeCoordinates)
    (v : sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) (hs0 : 0 < (s : ℝ)) :
    let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
    ∃ γ : C(Hemisphere.Sphere 2, (S.data p).UpperLevel),
      (∀ x : Hemisphere.Sphere 2, x.val 0 ≤ 0 →
        γ x = nativeBeltMeridianDisk S p v s hs (L (Hemisphere.tail x))) ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ γ negativeHemisphere ∧
      ∀ x (w : sphere (0 : (S.data p).chart.PositiveCoordinates) 1),
        γ x = (S.data p).surgery.beltSphere w ↔ x = pole ∧ v = w := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.isManifold hf (S.data p).upper_regular
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient 2) = 1 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let e := SphereCoordinates.ofLinearIsometry (n := 1) L
  obtain ⟨K, hKboundary, hKavoid⟩ := S.exists_native_belt_meridian_cap hf p hdim e v s hs0
  let A : C(Hemisphere.Ball 2, (S.data p).UpperLevel) :=
    ⟨fun z => nativeBeltMeridianDisk S p v s hs (L z.val),
      (nativeBeltMeridianDisk_smooth S hf p v s hs).continuous.comp
        (L.continuous.comp continuous_subtype_val)⟩
  have hagree (z : DiskDouble.Boundary (Hemisphere.Ambient 2)) :
      A (DiskDouble.boundary _ z) = K (DiskDouble.boundary _ z) := by
    let w : Hemisphere.Sphere 1 := ⟨z.val, z.property⟩
    exact (nativeBeltMeridianDisk_boundary S p v s hs (e w)).trans (hKboundary w).symm
  let γ := SphereDiskGluing.map A K hagree
  have hformula (x : Hemisphere.Sphere 2) (hx : x.val 0 ≤ 0) :
      γ x = nativeBeltMeridianDisk S p v s hs (L (Hemisphere.tail x)) :=
    SphereDiskGluing.map_of_nonpos A K hagree x hx
  refine ⟨γ, hformula, ?_, ?_⟩
  · have hmodel : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞
        (fun x : Hemisphere.Sphere 2 =>
          nativeBeltMeridianDisk S p v s hs (L (Hemisphere.tail x))) :=
      (nativeBeltMeridianDisk_smooth S hf p v s hs).comp
        (L.contDiff.contMDiff.comp smooth_tail)
    intro x hx
    apply (hmodel.contMDiffAt.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [negativeHemisphere_open.mem_nhds hx] with y hy
    exact hformula y hy.le
  · intro x w
    constructor
    · intro heq
      obtain ⟨b, u, rfl⟩ := Hemisphere.point_jointly_surjective x
      cases b
      · have heq' : nativeBeltMeridianDisk S p v s hs (L u.val) =
            (S.data p).surgery.beltSphere w :=
          (SphereDiskGluing.map_false A K hagree u).symm.trans heq
        obtain ⟨hu, hv⟩ :=
          (nativeBeltMeridianDisk_belt_eq_iff S p v w s hs hs0 (L u.val)).mp heq'
        have hu0 : u = (⟨0, by simp⟩ : Hemisphere.Ball 2) :=
          Subtype.ext (L.injective (hu.trans (map_zero L).symm))
        exact ⟨congrArg (Hemisphere.point false) hu0, hv⟩
      · have heq' : K u = (S.data p).surgery.beltSphere w :=
          (SphereDiskGluing.map_true A K hagree u).symm.trans heq
        exact (hKavoid u ⟨w, heq'.symm⟩).elim
    · rintro ⟨rfl, rfl⟩
      change SphereDiskGluing.map A K hagree (Hemisphere.point false ⟨0, by simp⟩) = _
      rw [SphereDiskGluing.map_false]
      change nativeBeltMeridianDisk S p v s hs (L 0) = _
      rw [map_zero, nativeBeltMeridianDisk_zero]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.BeltMeridianSphere
