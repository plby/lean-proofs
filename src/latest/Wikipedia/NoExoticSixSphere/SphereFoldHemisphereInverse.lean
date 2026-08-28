import Wikipedia.NoExoticSixSphere.SphereHemisphereFold

/-!
# Exact inverses on the actual fold's two open hemispheres

The northern inverse is normalization of `v + y`, on the sphere with the
antipodal pole deleted. Its height is strictly positive and both inverse
identities are proved from the actual vector formulas. The southern inverse
is its antipode. These are partial diffeomorphisms in the original sphere atlas.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def northInverse (v y : UnitSphere E) : UnitSphere E :=
  SphereRadialRetraction.retract v ((v : E) + (y : E))

theorem pole_add_ne_zero (v y : UnitSphere E) (hy : y ≠ antipode v) :
    (v : E) + (y : E) ≠ 0 := by
  intro h
  apply hy
  apply Subtype.ext
  exact eq_neg_of_add_eq_zero_right h

theorem northInverse_val (v y : UnitSphere E) (hy : y ≠ antipode v) :
    (northInverse v y : E) = NormedSpace.normalize ((v : E) + (y : E)) := by
  simp only [northInverse, SphereRadialRetraction.retract, dif_neg (pole_add_ne_zero v y hy)]

theorem norm_pole_add_sq (v y : UnitSphere E) :
    ‖(v : E) + (y : E)‖ ^ 2 = 2 * (1 + height v y) := by
  rw [norm_add_sq_real, ClosedHemisphere.unit_norm v, ClosedHemisphere.unit_norm y]
  change 1 ^ 2 + 2 * height v y + 1 ^ 2 = _
  ring

theorem twice_height_northInverse (v y : UnitSphere E) (hy : y ≠ antipode v) :
    2 * height v (northInverse v y) = ‖(v : E) + (y : E)‖ := by
  change 2 * inner ℝ (v : E) (northInverse v y : E) = _
  rw [northInverse_val v y hy, NormedSpace.normalize, real_inner_smul_right,
    inner_add_right, real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm v]
  have hn : ‖(v : E) + (y : E)‖ ≠ 0 := norm_ne_zero_iff.mpr (pole_add_ne_zero v y hy)
  have hs := norm_pole_add_sq v y
  change ‖(v : E) + (y : E)‖ ^ 2 = 2 * (1 + inner ℝ (v : E) (y : E)) at hs
  field_simp
  nlinarith

theorem height_northInverse_pos (v y : UnitSphere E) (hy : y ≠ antipode v) :
    0 < height v (northInverse v y) := by
  have h := twice_height_northInverse v y hy
  have hn := norm_pos_iff.mpr (pole_add_ne_zero v y hy)
  linarith

theorem fold_northInverse (v y : UnitSphere E) (hy : y ≠ antipode v) :
    fold v (northInverse v y) = y := by
  apply Subtype.ext
  rw [fold_val, twice_height_northInverse v y hy, northInverse_val v y hy,
    NormedSpace.norm_smul_normalize]
  abel

theorem northInverse_fold (v x : UnitSphere E) (hx : 0 < height v x) :
    northInverse v (fold v x) = x := by
  have hsum : (v : E) + (fold v x : E) = (2 * height v x) • (x : E) := by
    rw [fold_val]
    abel
  have hs : 0 < 2 * height v x := by positivity
  apply Subtype.ext
  rw [northInverse_val v (fold v x) ((fold_eq_antipode_iff v x).not.mpr hx.ne'),
    hsum, NormedSpace.normalize_smul_of_pos hs]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm x)

theorem antipode_northInverse_fold (v x : UnitSphere E) (hx : height v x < 0) :
    antipode (northInverse v (fold v x)) = x := by
  have hp : 0 < height v (antipode x) := by
    rw [height_antipode]
    exact neg_pos.mpr hx
  have h := northInverse_fold v (antipode x) hp
  rw [fold_antipode] at h
  rw [h]
  apply Subtype.ext
  exact neg_neg (x : E)

variable {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

theorem contMDiffOn_northInverse (v : UnitSphere E) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (northInverse v) {y | y ≠ antipode v} := by
  have hx : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (Subtype.val : UnitSphere E → E) :=
    contMDiff_coe_sphere (E := E) (n := n) (m := ∞)
  exact (SphereRadialRetraction.contMDiffOn_retract (n := n) v).comp
    (contMDiff_const.add hx).contMDiffOn (fun y hy ↦ pole_add_ne_zero v y hy)

def north (v : UnitSphere E) : PartialDiffeomorph (𝓡 n) (𝓡 n)
    (UnitSphere E) (UnitSphere E) ∞ where
  toFun := fold v
  invFun := northInverse v
  source := {x | 0 < height v x}
  target := {y | y ≠ antipode v}
  map_source' x hx := fun h ↦ hx.ne' ((fold_eq_antipode_iff v x).mp h)
  map_target' y hy := height_northInverse_pos v y hy
  left_inv' x hx := northInverse_fold v x hx
  right_inv' y hy := fold_northInverse v y hy
  open_source := isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val)
  open_target := isOpen_ne_fun continuous_id continuous_const
  contMDiffOn_toFun := (contMDiff_fold (n := n) v).contMDiffOn
  contMDiffOn_invFun := contMDiffOn_northInverse v

theorem contMDiff_antipode : ContMDiff (𝓡 n) (𝓡 n) ∞ (antipode : UnitSphere E → UnitSphere E) :=
  (contMDiff_coe_sphere (E := E) (n := n) (m := ∞)).neg.codRestrict_sphere
    (fun x ↦ (antipode x).property)

def south (v : UnitSphere E) : PartialDiffeomorph (𝓡 n) (𝓡 n)
    (UnitSphere E) (UnitSphere E) ∞ where
  toFun := fold v
  invFun y := antipode (northInverse v y)
  source := {x | height v x < 0}
  target := {y | y ≠ antipode v}
  map_source' x hx := fun h ↦ hx.ne ((fold_eq_antipode_iff v x).mp h)
  map_target' y hy := by
    change height v (antipode (northInverse v y)) < 0
    rw [height_antipode]
    exact neg_neg_of_pos (height_northInverse_pos v y hy)
  left_inv' x hx := antipode_northInverse_fold v x hx
  right_inv' y hy := (fold_antipode v (northInverse v y)).trans (fold_northInverse v y hy)
  open_source := isOpen_lt (continuous_const.inner continuous_subtype_val) continuous_const
  open_target := isOpen_ne_fun continuous_id continuous_const
  contMDiffOn_toFun := (contMDiff_fold (n := n) v).contMDiffOn
  contMDiffOn_invFun := contMDiff_antipode.comp_contMDiffOn (contMDiffOn_northInverse v)

theorem bijective_mfderiv_fold (v x : UnitSphere E) (hx : height v x ≠ 0) :
    Bijective (mfderiv (𝓡 n) (𝓡 n) (fold v) x) := by
  have hloc : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ (fold v) x := by
    rcases lt_or_gt_of_ne hx with h | h
    · exact ⟨south v, h, fun _ _ ↦ rfl⟩
    · exact ⟨north v, h, fun _ _ ↦ rfl⟩
  exact (hloc.mfderivToContinuousLinearEquiv (by simp)).bijective

end NoExoticSixSphere.SphereFold
