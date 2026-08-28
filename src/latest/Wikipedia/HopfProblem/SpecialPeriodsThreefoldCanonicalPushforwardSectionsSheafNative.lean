import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsNative
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsSheaf

/-!
# The actual canonical section sheaf and its direct image

The sheaf below consists of holomorphic sections of the original
canonical bundle, with its original total-space atlas. Its direct
image is Mathlib's sheaf pushforward along the constructed sphere
projection. Holomorphic base functions act by actual pullback and
pointwise scalar multiplication in the original canonical fibres.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward

open TrianglePeriodFamily.Canonical

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ Model

/-- The genuine sheaf of sections of the original canonical bundle. -/
def canonicalSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of Threefold.Space) :=
  NativeBundleSections.sheaf Threefold.Canonical.bundle IF

theorem canonicalSheaf_obj_eq (V : Opens Threefold.Space) :
    canonicalSheaf.obj.obj (op V) = AddCommGrpCat.of (Section V) := rfl

/-- The actual direct image, not an independently labelled sheaf. -/
def canonicalDirectImage : TopCat.Sheaf AddCommGrpCat (TopCat.of RiemannSphere) :=
  (TopCat.Sheaf.pushforward AddCommGrpCat Threefold.sphereProjectionMap).obj canonicalSheaf

theorem canonicalDirectImage_obj_eq (U : Opens RiemannSphere) :
    canonicalDirectImage.obj.obj (op U) = AddCommGrpCat.of (PreimageSection U) := rfl

/-- A base holomorphic function acts through its actual holomorphic
pullback to the full preimage. -/
instance preimageBaseModule (U : Opens RiemannSphere) :
    Module (Threefold.BaseSection U) (PreimageSection U) :=
  Module.compHom (PreimageSection U) (Threefold.pullbackSection U).toRingHom

@[simp] theorem base_smul_apply (U : Opens RiemannSphere)
    (f : Threefold.BaseSection U) (s : PreimageSection U)
    (x : Threefold.basePreimage U) :
    (f • s) x = f (Threefold.baseProjection U x) • s x := rfl

theorem base_smul_eq_pullback (U : Opens RiemannSphere)
    (f : Threefold.BaseSection U) (s : PreimageSection U) :
    f • s = Threefold.pullbackSection U f • s := rfl

instance preimageBaseScalarTower (U : Opens RiemannSphere) :
    IsScalarTower ℂ (Threefold.BaseSection U) (PreimageSection U) where
  smul_assoc c f s := by
    apply section_ext
    intro x
    exact smul_assoc c (f (Threefold.baseProjection U x)) (s x)

instance preimageBaseSMulCommClass (U : Opens RiemannSphere) :
    SMulCommClass ℂ (Threefold.BaseSection U) (PreimageSection U) where
  smul_comm c f s := by
    apply section_ext
    intro x
    exact smul_comm c (f (Threefold.baseProjection U x)) (s x)

@[simp] theorem restrictPreimageSection_zero {U V : Opens RiemannSphere} (h : U ≤ V) :
    restrictPreimageSection h (0 : PreimageSection V) = 0 := by
  apply section_ext
  intro x
  rfl

@[simp] theorem restrictPreimageSection_add {U V : Opens RiemannSphere} (h : U ≤ V)
    (s t : PreimageSection V) :
    restrictPreimageSection h (s + t) =
      restrictPreimageSection h s + restrictPreimageSection h t := by
  apply section_ext
  intro x
  rfl

@[simp] theorem restrictPreimageSection_complex_smul {U V : Opens RiemannSphere} (h : U ≤ V)
    (c : ℂ) (s : PreimageSection V) :
    restrictPreimageSection h (c • s) = c • restrictPreimageSection h s := by
  apply section_ext
  intro x
  rfl

/-- The scalar action commutes with the literal base restriction. -/
theorem restrictPreimageSection_base_smul {U V : Opens RiemannSphere} (h : U ≤ V)
    (f : Threefold.BaseSection V) (s : PreimageSection V) :
    restrictPreimageSection h (f • s) =
      HolomorphicFunctionSheaf.restrictionAlgHom 𝓘(ℂ) RiemannSphere h f •
        restrictPreimageSection h s := by
  apply section_ext
  intro x
  rfl

def restrictionPreimageAddHom {U V : Opens RiemannSphere} (h : U ≤ V) :
    PreimageSection V →+ PreimageSection U where
  toFun := restrictPreimageSection h
  map_zero' := restrictPreimageSection_zero h
  map_add' := restrictPreimageSection_add h

def restrictionPreimageLinearMap {U V : Opens RiemannSphere} (h : U ≤ V) :
    PreimageSection V →ₗ[ℂ] PreimageSection U where
  __ := restrictionPreimageAddHom h
  map_smul' := restrictPreimageSection_complex_smul h

/-- Direct-image restrictions are semilinear over the actual base
holomorphic function restriction. -/
def restrictionPreimageSemilinearMap {U V : Opens RiemannSphere} (h : U ≤ V) :
    PreimageSection V →ₛₗ[(HolomorphicFunctionSheaf.restrictionAlgHom
      𝓘(ℂ) RiemannSphere h).toRingHom] PreimageSection U where
  __ := restrictionPreimageAddHom h
  map_smul' := restrictPreimageSection_base_smul h

@[simp] theorem restrictionPreimageLinearMap_apply {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : PreimageSection V) :
    restrictionPreimageLinearMap h s = restrictPreimageSection h s := rfl

@[simp] theorem restrictionPreimageSemilinearMap_apply {U V : Opens RiemannSphere}
    (h : U ≤ V) (s : PreimageSection V) :
    restrictionPreimageSemilinearMap h s = restrictPreimageSection h s := rfl

instance canonicalDirectImage_obj_coeFun (U : (Opens (TopCat.of RiemannSphere))ᵒᵖ) :
    CoeFun (canonicalDirectImage.obj.obj U)
      (fun _ => ∀ x : Threefold.basePreimage U.unop, Threefold.Canonical.bundle.Fiber (x :
        Threefold.Space)) where
  coe s := s.toFun

instance canonicalDirectImage_obj_complexModule
    (U : (Opens (TopCat.of RiemannSphere))ᵒᵖ) :
    Module ℂ (canonicalDirectImage.obj.obj U) :=
  inferInstanceAs (Module ℂ (PreimageSection U.unop))

instance canonicalDirectImage_obj_baseModule
    (U : Opens RiemannSphere) :
    Module (Threefold.BaseSection U) (canonicalDirectImage.obj.obj (op U)) :=
  inferInstanceAs (Module (Threefold.BaseSection U) (PreimageSection U))

/-- Identity on actual native sections, now over the base function algebra. -/
def directImageSectionLinearEquiv (U : Opens RiemannSphere) :
    canonicalDirectImage.obj.obj (op U) ≃ₗ[Threefold.BaseSection U] PreimageSection U :=
  LinearEquiv.refl _ _

@[simp] theorem directImageSectionLinearEquiv_apply (U : Opens RiemannSphere)
    (s : canonicalDirectImage.obj.obj (op U)) : directImageSectionLinearEquiv U s = s := rfl

@[simp] theorem canonicalSheaf_map_eq_restrict {V W : Opens Threefold.Space} (h : V ≤ W)
    (s : Section W) :
    canonicalSheaf.obj.map (homOfLE h).op s = restrictSection h s := rfl

@[simp] theorem canonicalDirectImage_map_eq_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : PreimageSection V) :
    canonicalDirectImage.obj.map (homOfLE h).op s = restrictPreimageSection h s := rfl

@[simp] theorem canonicalDirectImage_map_apply {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : PreimageSection V) (x : Threefold.basePreimage U) :
    canonicalDirectImage.obj.map (homOfLE h).op s x = s ⟨x.val, h x.property⟩ := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward
