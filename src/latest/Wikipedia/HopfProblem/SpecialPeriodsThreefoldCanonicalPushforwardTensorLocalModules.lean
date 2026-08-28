import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsLinear

/-!
# Base holomorphic functions acting on native sections over a full preimage

The open set below is the literal inverse image under the given holomorphic
map. Its section module is the existing module of sections in the original
bundle fibres. Base functions act through actual holomorphic pullback, and
restriction is semilinear over the original holomorphic function restriction.
-/

noncomputable section

open Bundle Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.TensorLocal

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N]

/-- The literal full preimage of a base open set. -/
def preimageOpen (f : M → N) (hf : Continuous f) (U : Opens N) : Opens M :=
  ⟨f ⁻¹' (U : Set N), U.isOpen.preimage hf⟩

@[simp] theorem mem_preimageOpen (f : M → N) (hf : Continuous f)
    (U : Opens N) (x : M) : x ∈ preimageOpen f hf U ↔ f x ∈ U := Iff.rfl

theorem preimageOpen_mono (f : M → N) (hf : Continuous f)
    {U V : Opens N} (h : U ≤ V) : preimageOpen f hf U ≤ preimageOpen f hf V :=
  fun _ hx => h hx

/-- The actual map from the full preimage to the base open set. -/
def basePoint (f : M → N) (hf : Continuous f) (U : Opens N) :
    preimageOpen f hf U → U := fun x => ⟨f (x : M), x.property⟩

@[simp] theorem basePoint_val (f : M → N) (hf : Continuous f)
    (U : Opens N) (x : preimageOpen f hf U) :
    (basePoint f hf U x : N) = f (x : M) := rfl

theorem basePoint_continuous (f : M → N) (hf : Continuous f) (U : Opens N) :
    Continuous (basePoint f hf U) :=
  (hf.comp continuous_subtype_val).subtype_mk _

variable {ι : Type*} (C : VectorBundleCore ℂ M ℂ ι)

variable {E H F K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace K] [ChartedSpace K N]
  (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ F K)
  (f : M → N) (hf : ContMDiff I J ω f)

theorem basePoint_holomorphic (U : Opens N) :
    ContMDiff I J ω (basePoint f hf.continuous U) := by
  intro x
  have h : ContMDiffAt I J ω
      (fun y : preimageOpen f hf.continuous U =>
        (basePoint f hf.continuous U y : N)) x ↔
      ContMDiffAt I J ω (basePoint f hf.continuous U) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact h.mp ((hf.comp contMDiff_subtype_val) x)

/-- Pullback of actual holomorphic scalar functions. -/
def scalarPullback (U : Opens N) :
    HolomorphicFunctionSheaf.Section J N U →ₐ[ℂ]
      HolomorphicFunctionSheaf.Section I M (preimageOpen f hf.continuous U) where
  toFun g := ⟨g ∘ basePoint f hf.continuous U,
    g.contMDiff.comp (basePoint_holomorphic I J f hf U)⟩
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl
  commutes' _ := by ext; rfl

@[simp] theorem scalarPullback_apply (U : Opens N)
    (g : HolomorphicFunctionSheaf.Section J N U)
    (x : preimageOpen f hf.continuous U) :
    scalarPullback I J f hf U g x = g (basePoint f hf.continuous U x) := rfl

/-- Actual scalar pullback commutes with literal restriction. -/
theorem scalarPullback_restrict {U V : Opens N} (h : U ≤ V)
    (g : HolomorphicFunctionSheaf.Section J N V) :
    scalarPullback I J f hf U (HolomorphicFunctionSheaf.restrictionAlgHom J N h g) =
      HolomorphicFunctionSheaf.restrictionAlgHom I M
        (preimageOpen_mono f hf.continuous h) (scalarPullback I J f hf V g) := by
  ext x
  rfl

variable [C.IsContMDiff I ω]

/-- Restriction of scalars along the actual holomorphic pullback.
This is an explicit instance value, so users choose the map defining the action. -/
@[instance_reducible] def baseModule (U : Opens N) :
    Module (HolomorphicFunctionSheaf.Section J N U)
      (NativeBundleSections.Section C I (preimageOpen f hf.continuous U)) :=
  Module.compHom (NativeBundleSections.Section C I (preimageOpen f hf.continuous U))
    (scalarPullback I J f hf U).toRingHom

@[simp] theorem base_smul_apply (U : Opens N)
    (g : HolomorphicFunctionSheaf.Section J N U)
    (s : NativeBundleSections.Section C I (preimageOpen f hf.continuous U))
    (x : preimageOpen f hf.continuous U) :
    letI := baseModule C I J f hf U
    (g • s) x = g (basePoint f hf.continuous U x) • s x := rfl

theorem base_smul_eq_pullback (U : Opens N)
    (g : HolomorphicFunctionSheaf.Section J N U)
    (s : NativeBundleSections.Section C I (preimageOpen f hf.continuous U)) :
    letI := baseModule C I J f hf U
    g • s = scalarPullback I J f hf U g • s := rfl

theorem baseScalarTower (U : Opens N) :
    letI := baseModule C I J f hf U
    IsScalarTower ℂ (HolomorphicFunctionSheaf.Section J N U)
      (NativeBundleSections.Section C I (preimageOpen f hf.continuous U)) := by
  let _ := baseModule C I J f hf U
  refine ⟨?_⟩
  intro c g s
  apply NativeBundleSections.Section.ext C I
  intro x
  exact smul_assoc c (g (basePoint f hf.continuous U x)) (s x)

theorem baseSMulCommClass (U : Opens N) :
    letI := baseModule C I J f hf U
    SMulCommClass ℂ (HolomorphicFunctionSheaf.Section J N U)
      (NativeBundleSections.Section C I (preimageOpen f hf.continuous U)) := by
  let _ := baseModule C I J f hf U
  refine ⟨?_⟩
  intro c g s
  apply NativeBundleSections.Section.ext C I
  intro x
  exact smul_comm c (g (basePoint f hf.continuous U x)) (s x)

/-- Restriction of native sections respects the actual base scalar action. -/
theorem restrict_base_smul {U V : Opens N} (h : U ≤ V)
    (g : HolomorphicFunctionSheaf.Section J N V)
    (s : NativeBundleSections.Section C I (preimageOpen f hf.continuous V)) :
    letI := baseModule C I J f hf U
    letI := baseModule C I J f hf V
    NativeBundleSections.Section.restrict C I (preimageOpen_mono f hf.continuous h)
        (g • s) =
      HolomorphicFunctionSheaf.restrictionAlgHom J N h g •
        NativeBundleSections.Section.restrict C I (preimageOpen_mono f hf.continuous h) s := by
  apply NativeBundleSections.Section.ext C I
  intro x
  rfl

/-- Literal native section restriction as a base-semilinear map. -/
def restrictionBaseSemilinearMap {U V : Opens N} (h : U ≤ V) :
    letI := baseModule C I J f hf U
    letI := baseModule C I J f hf V
    NativeBundleSections.Section C I (preimageOpen f hf.continuous V)
      →ₛₗ[(HolomorphicFunctionSheaf.restrictionAlgHom J N h).toRingHom]
        NativeBundleSections.Section C I (preimageOpen f hf.continuous U) := by
  letI := baseModule C I J f hf U
  letI := baseModule C I J f hf V
  exact
    { __ := NativeBundleSections.Section.restrictionAddHom C I
        (preimageOpen_mono f hf.continuous h)
      map_smul' := restrict_base_smul C I J f hf h }

@[simp] theorem restrictionBaseSemilinearMap_apply {U V : Opens N} (h : U ≤ V)
    (s : NativeBundleSections.Section C I (preimageOpen f hf.continuous V))
    (x : preimageOpen f hf.continuous U) :
    restrictionBaseSemilinearMap C I J f hf h s x = s ⟨(x : M), h x.property⟩ := rfl

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.TensorLocal
