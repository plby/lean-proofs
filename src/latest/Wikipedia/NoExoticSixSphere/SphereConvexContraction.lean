import Wikipedia.NoExoticSixSphere.SphereNormalization

/-!
# Normalized convex contraction away from one antipode

For unit vectors other than the antipode of the chosen center, the entire
convex segment to that center is nonzero. Its normalization gives a jointly
continuous local contraction on the original sphere with the antipode removed.
No contractibility or homotopy-equivalence assumption is used.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace NoExoticSixSphere.SphereConvexContraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def vector (a y : UnitSphere E) (t : I) : E := (1 - (t : ℝ)) • y.val + (t : ℝ) • a.val

theorem vector_ne_zero (a y : UnitSphere E) (hy : y ≠ -a) (t : I) : vector a y t ≠ 0 := by
  intro hzero
  have he : (1 - (t : ℝ)) • y.val = -((t : ℝ) • a.val) :=
    eq_neg_of_add_eq_zero_left hzero
  have hs : 1 - (t : ℝ) = (t : ℝ) := by
    have hn := congrArg norm he
    simpa only [norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr t.2.2), abs_of_nonneg t.2.1,
      ClosedHemisphere.unit_norm, mul_one] using hn
  have ht : (t : ℝ) ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hsm : (t : ℝ) • y.val = (t : ℝ) • (-a.val) := by
    simpa only [hs, smul_neg] using he
  have hv := congrArg (fun v : E ↦ (t : ℝ)⁻¹ • v) hsm
  have hyval : y.val = -a.val := by
    simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using hv
  exact hy (Subtype.ext hyval)

def domain (a : UnitSphere E) : Set (UnitSphere E) := {y | y ≠ -a}

omit [InnerProductSpace ℝ E] in
theorem isOpen_domain (a : UnitSphere E) : IsOpen (domain a) := isOpen_compl_singleton

def vectorMap (a : UnitSphere E) : C(I × domain a, E) := by
  refine ⟨fun z ↦ vector a z.2.val z.1, ?_⟩
  have ht : Continuous (fun z : I × domain a ↦ (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hy : Continuous (fun z : I × domain a ↦ z.2.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  exact ((continuous_const.sub ht).smul hy).add (ht.smul continuous_const)

def localHomotopy (a : UnitSphere E) : C(I × domain a, UnitSphere E) :=
  normalizedSphereMap (vectorMap a) (fun z ↦ vector_ne_zero a z.2.val z.2.property z.1)

theorem localHomotopy_val (a : UnitSphere E) (t : I) (y : domain a) :
    (localHomotopy a (t, y)).val = NormedSpace.normalize (vector a y.val t) := rfl

theorem localHomotopy_zero (a : UnitSphere E) (y : domain a) :
    localHomotopy a (0, y) = y.val := by
  apply Subtype.ext
  rw [localHomotopy_val]
  change NormedSpace.normalize ((1 - (0 : ℝ)) • y.val.val + (0 : ℝ) • a.val) = y.val.val
  rw [sub_zero, one_smul, zero_smul, add_zero]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm y.val)

theorem localHomotopy_one (a : UnitSphere E) (y : domain a) :
    localHomotopy a (1, y) = a := by
  apply Subtype.ext
  rw [localHomotopy_val]
  change NormedSpace.normalize ((1 - (1 : ℝ)) • y.val.val + (1 : ℝ) • a.val) = a.val
  rw [sub_self, zero_smul, one_smul, zero_add]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm a)

end NoExoticSixSphere.SphereConvexContraction
