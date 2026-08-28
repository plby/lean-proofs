import Wikipedia.HopfProblem.StandardSixSphereCircleModelBasic
import Wikipedia.HopfProblem.StandardSixSphereCircleModelBoundary
import Wikipedia.HopfProblem.StandardSixSphereCircleModelSmooth

/-!
# Orthogonal normal-coordinate actions on the native standard sphere model

An actual linear isometry of the last four Euclidean coordinates extends
by the identity on the first three. Its restrictions are diffeomorphisms
in the original sphere and open-subset atlases. The complement chart and
the literal marked boundary points are equivariant for these maps.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.StandardSixSphereCircleModel.Isometries

local notation "ProductModel" => ModelWithCorners.prod 𝓘(ℝ, Base) (𝓡 3)

/-- The actual block isometry `(x,y) ↦ (x,L y)` on Euclidean seven-space. -/
def ambientIsometry (L : Normal ≃ₗᵢ[ℝ] Normal) : Ambient ≃ₗᵢ[ℝ] Ambient where
  toLinearEquiv :=
    (split.toLinearEquiv.trans
      ((LinearEquiv.refl ℝ Base).prodCongr L.toLinearEquiv)).trans split.symm.toLinearEquiv
  norm_map' z := by
    change ‖join (base z) (L (normal z))‖ = ‖z‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [join_norm_sq, L.norm_map, norm_sq_eq]

@[simp] theorem ambientIsometry_apply (L : Normal ≃ₗᵢ[ℝ] Normal) (z : Ambient) :
    ambientIsometry L z = join (base z) (L (normal z)) := rfl

@[simp] theorem base_ambientIsometry (L : Normal ≃ₗᵢ[ℝ] Normal) (z : Ambient) :
    base (ambientIsometry L z) = base z := base_join _ _

@[simp] theorem normal_ambientIsometry (L : Normal ≃ₗᵢ[ℝ] Normal) (z : Ambient) :
    normal (ambientIsometry L z) = L (normal z) := normal_join _ _

@[simp] theorem ambientIsometry_join (L : Normal ≃ₗᵢ[ℝ] Normal) (x : Base) (y : Normal) :
    ambientIsometry L (join x y) = join x (L y) := by
  rw [ambientIsometry_apply, base_join, normal_join]

@[simp] theorem ambientIsometry_symm (L : Normal ≃ₗᵢ[ℝ] Normal) :
    ambientIsometry L.symm = (ambientIsometry L).symm := by
  ext z
  rfl

@[simp] theorem ambientIsometry_refl :
    ambientIsometry (LinearIsometryEquiv.refl ℝ Normal) =
      LinearIsometryEquiv.refl ℝ Ambient := by
  apply LinearIsometryEquiv.ext
  intro z
  exact join_base_normal z

@[simp] theorem ambientIsometry_trans
    (L K : Normal ≃ₗᵢ[ℝ] Normal) :
    ambientIsometry (L.trans K) = (ambientIsometry L).trans (ambientIsometry K) := by
  ext z
  simp only [LinearIsometryEquiv.trans_apply, ambientIsometry_apply, base_join, normal_join]

theorem normalSphereMap_mem (L : Normal ≃ₗᵢ[ℝ] Normal) (u : NormalSphere) :
    L u.val ∈ NormalSphere := by
  simp only [Metric.mem_sphere, dist_zero_right, L.norm_map, normalSphere_norm]

def normalSphereMap (L : Normal ≃ₗᵢ[ℝ] Normal) (u : NormalSphere) : NormalSphere :=
  ⟨L u.val, normalSphereMap_mem L u⟩

@[simp] theorem normalSphereMap_val (L : Normal ≃ₗᵢ[ℝ] Normal) (u : NormalSphere) :
    (normalSphereMap L u).val = L u.val := rfl

theorem contMDiff_normalSphereMap (L : Normal ≃ₗᵢ[ℝ] Normal) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (normalSphereMap L) := by
  have : Fact (Module.finrank ℝ Normal = 3 + 1) := ⟨by simp [Normal]⟩
  have h : ContMDiff (𝓡 3) 𝓘(ℝ, Normal) ∞ (fun u : NormalSphere => L u.val) :=
    L.contDiff.comp_contMDiff (contMDiff_coe_sphere (n := 3))
  exact h.codRestrict_sphere (normalSphereMap_mem L)

def normalSphereDiffeomorph (L : Normal ≃ₗᵢ[ℝ] Normal) :
    NormalSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ NormalSphere where
  toFun := normalSphereMap L
  invFun := normalSphereMap L.symm
  left_inv u := Subtype.ext (L.symm_apply_apply u.val)
  right_inv u := Subtype.ext (L.apply_symm_apply u.val)
  contMDiff_toFun := contMDiff_normalSphereMap L
  contMDiff_invFun := contMDiff_normalSphereMap L.symm

@[simp] theorem normalSphereDiffeomorph_apply (L : Normal ≃ₗᵢ[ℝ] Normal)
    (u : NormalSphere) : normalSphereDiffeomorph L u = normalSphereMap L u := rfl

@[simp] theorem normalSphereDiffeomorph_symm_apply (L : Normal ≃ₗᵢ[ℝ] Normal)
    (u : NormalSphere) :
    (normalSphereDiffeomorph L).symm u = normalSphereMap L.symm u := rfl

theorem sphereMap_mem (L : Normal ≃ₗᵢ[ℝ] Normal) (p : Sphere) :
    ambientIsometry L p.val ∈ Sphere := by
  simp only [Metric.mem_sphere, dist_zero_right, (ambientIsometry L).norm_map, sphere_norm]

def sphereMap (L : Normal ≃ₗᵢ[ℝ] Normal) (p : Sphere) : Sphere :=
  ⟨ambientIsometry L p.val, sphereMap_mem L p⟩

@[simp] theorem sphereMap_val (L : Normal ≃ₗᵢ[ℝ] Normal) (p : Sphere) :
    (sphereMap L p).val = ambientIsometry L p.val := rfl

theorem normal_sphereMap_eq_zero_iff (L : Normal ≃ₗᵢ[ℝ] Normal) (p : Sphere) :
    normal (sphereMap L p).val = 0 ↔ normal p.val = 0 := by
  rw [sphereMap_val, normal_ambientIsometry]
  constructor
  · intro h
    exact L.injective (h.trans (map_zero L).symm)
  · intro h
    rw [h, map_zero]

theorem sphereMap_mem_equator_iff (L : Normal ≃ₗᵢ[ℝ] Normal) (p : Sphere) :
    sphereMap L p ∈ equator ↔ p ∈ equator :=
  normal_sphereMap_eq_zero_iff L p

theorem contMDiff_sphereMap (L : Normal ≃ₗᵢ[ℝ] Normal) :
    ContMDiff (𝓡 6) (𝓡 6) ∞ (sphereMap L) := by
  have : Fact (Module.finrank ℝ Ambient = 6 + 1) := ⟨by simp [Ambient]⟩
  have h : ContMDiff (𝓡 6) 𝓘(ℝ, Ambient) ∞
      (fun p : Sphere => ambientIsometry L p.val) :=
    (ambientIsometry L).contDiff.comp_contMDiff (contMDiff_coe_sphere (n := 6))
  exact h.codRestrict_sphere (sphereMap_mem L)

@[simp] theorem sphereMap_symm_apply_apply (L : Normal ≃ₗᵢ[ℝ] Normal) (p : Sphere) :
    sphereMap L.symm (sphereMap L p) = p := by
  apply Subtype.ext
  change ambientIsometry L.symm (ambientIsometry L p.val) = p.val
  rw [ambientIsometry_symm, LinearIsometryEquiv.symm_apply_apply]

@[simp] theorem sphereMap_apply_symm_apply (L : Normal ≃ₗᵢ[ℝ] Normal) (p : Sphere) :
    sphereMap L (sphereMap L.symm p) = p := by
  apply Subtype.ext
  change ambientIsometry L (ambientIsometry L.symm p.val) = p.val
  rw [ambientIsometry_symm, LinearIsometryEquiv.apply_symm_apply]

def sphereDiffeomorph (L : Normal ≃ₗᵢ[ℝ] Normal) : Sphere ≃ₘ⟮𝓡 6, 𝓡 6⟯ Sphere where
  toFun := sphereMap L
  invFun := sphereMap L.symm
  left_inv := sphereMap_symm_apply_apply L
  right_inv := sphereMap_apply_symm_apply L
  contMDiff_toFun := contMDiff_sphereMap L
  contMDiff_invFun := contMDiff_sphereMap L.symm

@[simp] theorem sphereDiffeomorph_apply (L : Normal ≃ₗᵢ[ℝ] Normal) (p : Sphere) :
    sphereDiffeomorph L p = sphereMap L p := rfl

@[simp] theorem sphereDiffeomorph_symm_apply (L : Normal ≃ₗᵢ[ℝ] Normal) (p : Sphere) :
    (sphereDiffeomorph L).symm p = sphereMap L.symm p := rfl

def complementMap (L : Normal ≃ₗᵢ[ℝ] Normal) (p : Complement) : Complement :=
  ⟨sphereMap L p.val, fun h => p.property ((normal_sphereMap_eq_zero_iff L p.val).mp h)⟩

@[simp] theorem complementMap_val (L : Normal ≃ₗᵢ[ℝ] Normal) (p : Complement) :
    (complementMap L p).val = sphereMap L p.val := rfl

@[simp] theorem complementMap_val_val (L : Normal ≃ₗᵢ[ℝ] Normal) (p : Complement) :
    (complementMap L p).val.val = ambientIsometry L p.val.val := rfl

@[simp] theorem normalRadius_complementMap (L : Normal ≃ₗᵢ[ℝ] Normal) (p : Complement) :
    normalRadius (complementMap L p) = normalRadius p := by
  change ‖normal (ambientIsometry L p.val.val)‖ = ‖normal p.val.val‖
  rw [normal_ambientIsometry, L.norm_map]

theorem contMDiff_complementMap (L : Normal ≃ₗᵢ[ℝ] Normal) :
    ContMDiff (𝓡 6) (𝓡 6) ∞ (complementMap L) := by
  apply (ContMDiff.subtypeVal_comp_iff complement (complementMap L)).mp
  exact (contMDiff_sphereMap L).comp (contMDiff_subtype_val (U := complement))

def complementDiffeomorph (L : Normal ≃ₗᵢ[ℝ] Normal) :
    Complement ≃ₘ⟮𝓡 6, 𝓡 6⟯ Complement where
  toFun := complementMap L
  invFun := complementMap L.symm
  left_inv p := Subtype.ext (sphereMap_symm_apply_apply L p.val)
  right_inv p := Subtype.ext (sphereMap_apply_symm_apply L p.val)
  contMDiff_toFun := contMDiff_complementMap L
  contMDiff_invFun := contMDiff_complementMap L.symm

@[simp] theorem complementDiffeomorph_apply (L : Normal ≃ₗᵢ[ℝ] Normal) (p : Complement) :
    complementDiffeomorph L p = complementMap L p := rfl

@[simp] theorem complementDiffeomorph_symm_apply
    (L : Normal ≃ₗᵢ[ℝ] Normal) (p : Complement) :
    (complementDiffeomorph L).symm p = complementMap L.symm p := rfl

/-- The genuine product diffeomorphism `(a,u) ↦ (a,L u)`. -/
def productDiffeomorph (L : Normal ≃ₗᵢ[ℝ] Normal) :
    (Base × NormalSphere) ≃ₘ⟮ProductModel, ProductModel⟯ Base × NormalSphere :=
  (Diffeomorph.refl 𝓘(ℝ, Base) Base ∞).prodCongr (normalSphereDiffeomorph L)

@[simp] theorem productDiffeomorph_apply (L : Normal ≃ₗᵢ[ℝ] Normal)
    (q : Base × NormalSphere) :
    productDiffeomorph L q = (q.1, normalSphereMap L q.2) := rfl

theorem forward_equivariant (L : Normal ≃ₗᵢ[ℝ] Normal) (p : Complement) :
    forward (complementMap L p) = productDiffeomorph L (forward p) := by
  apply Prod.ext
  · change (normalRadius (complementMap L p))⁻¹ •
        base (ambientIsometry L p.val.val) = (normalRadius p)⁻¹ • base p.val.val
    rw [normalRadius_complementMap, base_ambientIsometry]
  · apply Subtype.ext
    change (normalRadius (complementMap L p))⁻¹ •
        normal (ambientIsometry L p.val.val) =
      L ((normalRadius p)⁻¹ • normal p.val.val)
    rw [normalRadius_complementMap, normal_ambientIsometry, L.map_smul]

theorem inverse_equivariant (L : Normal ≃ₗᵢ[ℝ] Normal) (q : Base × NormalSphere) :
    complementMap L (inverse q) = inverse (productDiffeomorph L q) := by
  apply Subtype.ext
  apply Subtype.ext
  change ambientIsometry L (inverseScale q.1 • join q.1 q.2.val) =
    inverseScale q.1 • join q.1 (L q.2.val)
  rw [(ambientIsometry L).map_smul, ambientIsometry_join]

theorem homeomorph_equivariant (L : Normal ≃ₗᵢ[ℝ] Normal) (p : Complement) :
    homeomorph (complementDiffeomorph L p) = productDiffeomorph L (homeomorph p) :=
  forward_equivariant L p

theorem diffeomorph_equivariant (L : Normal ≃ₗᵢ[ℝ] Normal) (p : Complement) :
    diffeomorph (complementDiffeomorph L p) = productDiffeomorph L (diffeomorph p) :=
  forward_equivariant L p

/-- The marked normal unit vector undergoes exactly the original isometry. -/
theorem forward_snd_complementMap (L : Normal ≃ₗᵢ[ℝ] Normal) (p : Complement) :
    (forward (complementMap L p)).2 = normalSphereMap L (forward p).2 :=
  congrArg Prod.snd (forward_equivariant L p)

theorem complementMap_mem_normalLevel_iff (L : Normal ≃ₗᵢ[ℝ] Normal)
    (r : ℝ) (p : Complement) :
    complementMap L p ∈ normalLevel r ↔ p ∈ normalLevel r := by
  change normalRadius (complementMap L p) = r ↔ normalRadius p = r
  rw [normalRadius_complementMap]

/-- Equivariance of the literal boundary point, with its base marking fixed. -/
theorem complementMap_boundaryPoint (L : Normal ≃ₗᵢ[ℝ] Normal)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (q : BaseSphere × NormalSphere) :
    complementMap L (boundaryPoint r hr hr1 q) =
      boundaryPoint r hr hr1 (q.1, normalSphereMap L q.2) := by
  apply Subtype.ext
  apply Subtype.ext
  change ambientIsometry L
      (join (boundaryBaseRadius r • q.1.val) (r • q.2.val)) =
    join (boundaryBaseRadius r • q.1.val) (r • L q.2.val)
  rw [ambientIsometry_join, L.map_smul]

end Wikipedia.HopfProblem.StandardSixSphereCircleModel.Isometries
