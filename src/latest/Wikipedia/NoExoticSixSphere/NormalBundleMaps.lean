import Wikipedia.NoExoticSixSphere.NormalBundle

/-!
# Ambient maps of the normal bundle

The normal bundle's vector component is smooth with values in the actual
ambient Euclidean space. In particular, adding a normal vector to the embedded
base point gives a smooth displacement map. No tubular-neighborhood or global
injectivity claim is made here.
-/

open scoped Manifold ContDiff Topology Bundle
open Bundle Filter

namespace NoExoticSixSphere.EuclideanEmbedding

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  (e : EuclideanEmbedding n M)

/-- The normal vector, as a vector in ambient Euclidean space. -/
def normalVector (v : e.NormalBundle) : EuclideanSpace ℝ (Fin e.ambientDimension) := v.2

/-- The bundle's preferred trivialization is the explicit projection-transport chart. -/
theorem normal_trivializationAt_apply (x₀ : M) (v : e.NormalBundle) :
    trivializationAt e.NormalModel e.NormalSpace x₀ v =
      (v.1, ProjectionBundle.toCoordinates e.normalProjection e.normalModelEquiv x₀ v.1 v.2) :=
  rfl

/-- The ambient normal-vector component is smooth for the constructed bundle topology. -/
theorem contMDiff_normalVector :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞ e.normalVector := by
  intro z
  have hp : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) (𝓡 n) ∞
      (fun v : e.NormalBundle ↦ v.proj) z := Bundle.contMDiffAt_proj e.NormalSpace
  have hc : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) 𝓘(ℝ, e.NormalModel) ∞
      (fun v : e.NormalBundle ↦
        ProjectionBundle.toCoordinates e.normalProjection e.normalModelEquiv z.1 v.1 v.2) z := by
    have h := (Bundle.contMDiffAt_totalSpace
      (IB := 𝓡 n) (IM := (𝓡 n).prod 𝓘(ℝ, e.NormalModel))
      (n := ∞) (f := id) (x₀ := z)).mp contMDiffAt_id
    exact h.2
  have hf := ((ProjectionBundle.contMDiff_ambientFromCoordinates
    e.normalProjection e.normalModelEquiv e.contMDiff_normalProjection z.1).contMDiffAt.comp z
      hp).clm_apply hc
  have heq : e.normalVector =ᶠ[𝓝 z]
      (fun v : e.NormalBundle ↦ ProjectionBundle.ambientFromCoordinates
        e.normalProjection e.normalModelEquiv z.1 v.1
        (ProjectionBundle.toCoordinates e.normalProjection e.normalModelEquiv z.1 v.1 v.2)) := by
    have ho := isOpen_projectionTransportDomain
      e.normalProjection e.contMDiff_normalProjection z.1
    have hn := hp.continuousAt (ho.mem_nhds (mem_projectionTransportDomain
      e.normalProjection e.normalProjection_idempotent z.1))
    filter_upwards [hn] with v hv
    exact (congrArg Subtype.val (ProjectionBundle.fromCoordinates_toCoordinates
      e.normalProjection e.normalProjection_idempotent e.normalModelEquiv z.1 v.1 hv v.2)).symm
  exact heq.contMDiffAt_iff.mpr hf

section Source

variable {N : Type*} [TopologicalSpace N]

/-- Continuity into the normal bundle is exactly continuity of base and ambient vector. -/
theorem continuousAt_normalBundle_iff {f : N → e.NormalBundle} {x : N} :
    ContinuousAt f x ↔ ContinuousAt (fun y ↦ (f y).proj) x ∧
      ContinuousAt (fun y ↦ e.normalVector (f y)) x := by
  constructor
  · intro hf
    exact ⟨(FiberBundle.continuous_proj e.NormalModel e.NormalSpace).continuousAt.comp hf,
      e.contMDiff_normalVector.continuous.continuousAt.comp hf⟩
  · rintro ⟨hp, hv⟩
    apply (FiberBundle.continuousAt_totalSpace e.NormalModel f).mpr
    refine ⟨hp, ?_⟩
    have ho := isOpen_projectionTransportDomain
      e.normalProjection e.contMDiff_normalProjection (f x).proj
    have hm := mem_projectionTransportDomain
      e.normalProjection e.normalProjection_idempotent (f x).proj
    have hts := ProjectionBundle.contMDiffOn_ambientToCoordinates
      e.normalProjection e.normalModelEquiv e.contMDiff_normalProjection (f x).proj
    have ht := hts.contMDiffAt (ho.mem_nhds hm)
    have hc : ContinuousAt (fun y : N ↦ ProjectionBundle.ambientToCoordinates
        e.normalProjection e.normalModelEquiv (f x).proj (f y).proj) x :=
      ContinuousAt.comp (f := fun y : N ↦ (f y).proj) (x := x) ht.continuousAt hp
    simp only [e.normal_trivializationAt_apply, ProjectionBundle.toCoordinates_apply]
    exact hc.clm_apply hv

variable {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [ChartedSpace H N]

/-- Smoothness into the normal bundle is exactly smoothness of its two ambient components. -/
theorem contMDiffAt_normalBundle_iff {f : N → e.NormalBundle} {x : N} :
    ContMDiffAt I ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) ∞ f x ↔
      ContMDiffAt I (𝓡 n) ∞ (fun y ↦ (f y).proj) x ∧
      ContMDiffAt I (𝓡 e.ambientDimension) ∞ (fun y ↦ e.normalVector (f y)) x := by
  constructor
  · intro hf
    exact ⟨(Bundle.contMDiff_proj e.NormalSpace).contMDiffAt.comp x hf,
      e.contMDiff_normalVector.contMDiffAt.comp x hf⟩
  · rintro ⟨hp, hv⟩
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨hp, ?_⟩
    have ho := isOpen_projectionTransportDomain
      e.normalProjection e.contMDiff_normalProjection (f x).proj
    have hm := mem_projectionTransportDomain
      e.normalProjection e.normalProjection_idempotent (f x).proj
    have hts := ProjectionBundle.contMDiffOn_ambientToCoordinates
      e.normalProjection e.normalModelEquiv e.contMDiff_normalProjection (f x).proj
    have ht := hts.contMDiffAt (ho.mem_nhds hm)
    have hc : ContMDiffAt I
        𝓘(ℝ, EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] e.NormalModel) ∞
        (fun y : N ↦ ProjectionBundle.ambientToCoordinates
          e.normalProjection e.normalModelEquiv (f x).proj (f y).proj) x :=
      ContMDiffAt.comp (f := fun y : N ↦ (f y).proj)
        (g := ProjectionBundle.ambientToCoordinates
          e.normalProjection e.normalModelEquiv (f x).proj) x ht hp
    simp only [e.normal_trivializationAt_apply, ProjectionBundle.toCoordinates_apply]
    exact hc.clm_apply hv

end Source

/-- The normal vectors as a subset of base times ambient Euclidean space. -/
def normalLocus : Set (M × EuclideanSpace ℝ (Fin e.ambientDimension)) :=
  {p | e.normalProjection p.1 p.2 = p.2}

/-- The normal-vector locus is closed in base times ambient space. -/
theorem isClosed_normalLocus : IsClosed e.normalLocus :=
  isClosed_eq
    ((e.contMDiff_normalProjection.continuous.comp continuous_fst).clm_apply continuous_snd)
    continuous_snd

/-- The constructed normal-bundle topology is the ordinary topology on actual normal vectors. -/
noncomputable def normalLocusHomeomorph : e.NormalBundle ≃ₜ e.normalLocus where
  toFun v := ⟨(v.proj, e.normalVector v),
    projection_apply_range (e.normalProjection v.proj) (e.normalProjection_idempotent v.proj) v.2⟩
  invFun p := ⟨p.1.1, ⟨p.1.2, ⟨p.1.2, p.2⟩⟩⟩
  left_inv v := by cases v; rfl
  right_inv p := by cases p; rfl
  continuous_toFun :=
    ((FiberBundle.continuous_proj e.NormalModel e.NormalSpace).prodMk
      e.contMDiff_normalVector.continuous).subtype_mk _
  continuous_invFun := by
    apply continuous_iff_continuousAt.mpr
    intro p
    apply e.continuousAt_normalBundle_iff.mpr
    exact ⟨continuous_fst.continuousAt.comp continuous_subtype_val.continuousAt,
      continuous_snd.continuousAt.comp continuous_subtype_val.continuousAt⟩

/-- The natural inclusion of the normal bundle into base times ambient space is closed. -/
theorem normalBundle_isClosedEmbedding :
    Topology.IsClosedEmbedding
      (fun v : e.NormalBundle ↦ (v.proj, e.normalVector v)) :=
  e.isClosed_normalLocus.isClosedEmbedding_subtypeVal.comp
    e.normalLocusHomeomorph.isClosedEmbedding

/-- Project an arbitrary ambient vector onto the normal space at its base point. -/
noncomputable def normalLift (p : M × EuclideanSpace ℝ (Fin e.ambientDimension)) :
    e.NormalBundle :=
  ⟨p.1, (e.normalProjection p.1).rangeRestrict p.2⟩

/-- Orthogonal projection defines a smooth map into the normal bundle. -/
theorem contMDiff_normalLift :
    ContMDiff ((𝓡 n).prod (𝓡 e.ambientDimension)) ((𝓡 n).prod 𝓘(ℝ, e.NormalModel))
      ∞ e.normalLift := by
  intro p
  apply e.contMDiffAt_normalBundle_iff.mpr
  refine ⟨contMDiffAt_fst, ?_⟩
  exact (e.contMDiff_normalProjection.contMDiffAt.comp p contMDiffAt_fst).clm_apply
    contMDiffAt_snd

omit [IsManifold (𝓡 n) ∞ M] in
/-- Normal projection fixes the vectors that already belong to the normal bundle. -/
theorem normalLift_inclusion (v : e.NormalBundle) :
    e.normalLift (v.proj, e.normalVector v) = v := by
  cases v with
  | mk x v =>
    simp only [normalLift, normalVector, TotalSpace.mk_inj]
    apply Subtype.ext
    exact projection_apply_range (e.normalProjection x) (e.normalProjection_idempotent x) v

/-- Move from an embedded point by its normal vector. -/
def normalDisplacement (v : e.NormalBundle) : EuclideanSpace ℝ (Fin e.ambientDimension) :=
  e.toFun v.proj + e.normalVector v

/-- The normal displacement map is smooth. -/
theorem contMDiff_normalDisplacement :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
      e.normalDisplacement :=
  (e.smooth.comp (Bundle.contMDiff_proj e.NormalSpace)).add e.contMDiff_normalVector

omit [IsManifold (𝓡 n) ∞ M] in
/-- On the zero section, normal displacement is the original embedding. -/
theorem normalDisplacement_zero (x : M) :
    e.normalDisplacement (zeroSection e.NormalModel e.NormalSpace x) = e.toFun x := by
  simp [normalDisplacement, normalVector, zeroSection]

end NoExoticSixSphere.EuclideanEmbedding
