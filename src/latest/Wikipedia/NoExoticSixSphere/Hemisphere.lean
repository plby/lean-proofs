import Wikipedia.NoExoticSixSphere.ContinuousProjectionHomotopy
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.Homotopy.Contractible

/-!
# Closed hemispheres and their contraction

A closed hemisphere contracts to its pole by normalizing straight segments.
The segment never vanishes, including at equatorial points. This supplies
continuous local framings over hemispheres for the sphere clutching argument.
-/

open scoped Topology
open Set unitInterval

namespace NoExoticSixSphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual unit sphere in a real inner product space. -/
abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] := Metric.sphere (0 : E) 1

/-- The closed hemisphere centered at a unit vector. -/
def closedHemisphere (v : UnitSphere E) : Set (UnitSphere E) :=
  {x | 0 ≤ inner ℝ (v : E) (x : E)}

/-- Points of the closed hemisphere, retaining their actual sphere coordinates. -/
abbrev ClosedHemisphere (v : UnitSphere E) := ↥(closedHemisphere v)

namespace ClosedHemisphere

omit [InnerProductSpace ℝ E] in
/-- Unit-sphere points have norm one. -/
theorem unit_norm (x : UnitSphere E) : ‖(x : E)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using x.property

/-- The pole belongs to its closed hemisphere. -/
def center (v : UnitSphere E) : ClosedHemisphere v := ⟨v, real_inner_self_nonneg⟩

/-- Hemispheres are closed subsets of the sphere. -/
theorem isClosed (v : UnitSphere E) : IsClosed (closedHemisphere v) :=
  isClosed_le continuous_const (continuous_const.inner continuous_subtype_val)

/-- Finite-dimensional closed hemispheres are compact. -/
instance [FiniteDimensional ℝ E] (v : UnitSphere E) : CompactSpace (ClosedHemisphere v) :=
  isCompact_iff_compactSpace.mp (isClosed v).isCompact

/-- The straight segment from a hemisphere point to its pole. -/
noncomputable def blend (v : UnitSphere E) (t : I) (x : ClosedHemisphere v) : E :=
  (1 - (t : ℝ)) • (x.1 : E) + (t : ℝ) • (v : E)

/-- The segment stays on the nonnegative side of the equatorial hyperplane. -/
theorem inner_blend_nonneg (v : UnitSphere E) (t : I) (x : ClosedHemisphere v) :
    0 ≤ inner ℝ (v : E) (blend v t x) := by
  rw [blend, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) x.2)
    (mul_nonneg t.2.1 real_inner_self_nonneg)

/-- The segment cannot pass through zero, even when its initial point is on the equator. -/
theorem blend_ne_zero (v : UnitSphere E) (t : I) (x : ClosedHemisphere v) : blend v t x ≠ 0 := by
  by_cases ht : (t : ℝ) = 0
  · have hx : (x.1 : E) ≠ 0 := norm_pos_iff.mp (by rw [unit_norm]; norm_num)
    simpa only [blend, ht, sub_zero, one_smul, zero_smul, add_zero] using hx
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht)
    have hv : inner ℝ (v : E) (v : E) = 1 := by
      rw [real_inner_self_eq_norm_sq, unit_norm, one_pow]
    have hi : 0 < inner ℝ (v : E) (blend v t x) := by
      rw [blend, inner_add_right, real_inner_smul_right, real_inner_smul_right, hv, mul_one]
      exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr t.2.2) x.2) htpos
    intro hz
    rw [hz, inner_zero_right] at hi
    exact (lt_irrefl 0) hi

/-- Normalize the segment to contract the hemisphere within itself. -/
noncomputable def contract (v : UnitSphere E) (t : I) (x : ClosedHemisphere v) :
    ClosedHemisphere v :=
  ⟨⟨NormedSpace.normalize (blend v t x), by
      simpa only [Metric.mem_sphere, dist_zero_right] using
        NormedSpace.norm_normalize (blend_ne_zero v t x)⟩, by
    change 0 ≤ inner ℝ (v : E) (‖blend v t x‖⁻¹ • blend v t x)
    rw [real_inner_smul_right]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (inner_blend_nonneg v t x)⟩

/-- The normalized-segment contraction is continuous jointly in time and position. -/
theorem continuous_contract (v : UnitSphere E) :
    Continuous (fun p : I × ClosedHemisphere v ↦ contract v p.1 p.2) := by
  have ht : Continuous (fun p : I × ClosedHemisphere v ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun p : I × ClosedHemisphere v ↦ (p.2.1 : E)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  have hb : Continuous (fun p : I × ClosedHemisphere v ↦ blend v p.1 p.2) :=
    ((continuous_const.sub ht).smul hx).add (ht.smul continuous_const)
  have hn : Continuous (fun p : I × ClosedHemisphere v ↦ ‖blend v p.1 p.2‖⁻¹) :=
    hb.norm.inv₀ (fun p ↦ norm_ne_zero_iff.mpr (blend_ne_zero v p.1 p.2))
  exact ((hn.smul hb).subtype_mk _).subtype_mk _

/-- The contraction begins at the original point. -/
theorem contract_zero (v : UnitSphere E) (x : ClosedHemisphere v) : contract v 0 x = x := by
  apply Subtype.ext
  apply Subtype.ext
  change NormedSpace.normalize (blend v 0 x) = (x.1 : E)
  simpa [blend] using NormedSpace.normalize_eq_self_of_norm_eq_one (unit_norm x.1)

/-- The contraction ends at the pole. -/
theorem contract_one (v : UnitSphere E) (x : ClosedHemisphere v) :
    contract v 1 x = center v := by
  apply Subtype.ext
  apply Subtype.ext
  change NormedSpace.normalize (blend v 1 x) = (v : E)
  simpa [blend] using NormedSpace.normalize_eq_self_of_norm_eq_one (unit_norm v)

/-- The explicit contraction as a genuine continuous homotopy. -/
noncomputable def contraction (v : UnitSphere E) :
    (ContinuousMap.id (ClosedHemisphere v)).Homotopy (ContinuousMap.const _ (center v)) where
  toFun p := contract v p.1 p.2
  continuous_toFun := continuous_contract v
  map_zero_left := contract_zero v
  map_one_left := contract_one v

/-- Every closed hemisphere is contractible. -/
instance (v : UnitSphere E) : ContractibleSpace (ClosedHemisphere v) :=
  (contractible_iff_id_nullhomotopic _).mpr ⟨center v, ⟨contraction v⟩⟩

end ClosedHemisphere

end NoExoticSixSphere
