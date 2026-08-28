import Wikipedia.NoExoticSixSphere.Hemisphere
import Mathlib.Analysis.Convex.Contractible

/-!
# Contracting a sphere section of a convex cone avoiding zero

Normalize the straight segment to a selected sphere point. Convexity and the
exclusion of zero make the normalization valid, and invariance under positive
scaling keeps the entire homotopy in the original sphere section.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.NormalizedCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sphereSection (K : Set E) : Set (UnitSphere E) := {x | x.val ∈ K}

variable (K : Set E) (p : sphereSection K)

def blend (t : unitInterval) (x : sphereSection K) : E :=
  (1 - (t : ℝ)) • x.val.val + (t : ℝ) • p.val.val

theorem blend_mem (hK : Convex ℝ K) (t : unitInterval) (x : sphereSection K) :
    blend K p t x ∈ K :=
  hK x.property p.property (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel _ _)

theorem blend_ne_zero (hK : Convex ℝ K) (h0 : (0 : E) ∉ K)
    (t : unitInterval) (x : sphereSection K) : blend K p t x ≠ 0 :=
  fun he ↦ h0 (he ▸ blend_mem K p hK t x)

def contract (hK : Convex ℝ K) (h0 : (0 : E) ∉ K)
    (hscale : ∀ a : ℝ, 0 < a → ∀ x ∈ K, a • x ∈ K)
    (t : unitInterval) (x : sphereSection K) : sphereSection K :=
  ⟨⟨NormedSpace.normalize (blend K p t x), by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      NormedSpace.norm_normalize (blend_ne_zero K p hK h0 t x)⟩,
    hscale _ (inv_pos.mpr (norm_pos_iff.mpr (blend_ne_zero K p hK h0 t x))) _
      (blend_mem K p hK t x)⟩

theorem continuous_contract (hK : Convex ℝ K) (h0 : (0 : E) ∉ K)
    (hscale : ∀ a : ℝ, 0 < a → ∀ x ∈ K, a • x ∈ K) :
    Continuous (fun q : unitInterval × sphereSection K ↦ contract K p hK h0 hscale q.1 q.2) := by
  have ht : Continuous (fun q : unitInterval × sphereSection K ↦ (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun q : unitInterval × sphereSection K ↦ q.2.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  have hb : Continuous (fun q : unitInterval × sphereSection K ↦ blend K p q.1 q.2) :=
    ((continuous_const.sub ht).smul hx).add (ht.smul continuous_const)
  have hn := hb.norm.inv₀ (fun q ↦ norm_ne_zero_iff.mpr (blend_ne_zero K p hK h0 q.1 q.2))
  exact ((hn.smul hb).subtype_mk _).subtype_mk _

theorem contract_zero (hK : Convex ℝ K) (h0 : (0 : E) ∉ K)
    (hscale : ∀ a : ℝ, 0 < a → ∀ x ∈ K, a • x ∈ K) (x : sphereSection K) :
    contract K p hK h0 hscale 0 x = x := by
  apply Subtype.ext
  apply Subtype.ext
  change NormedSpace.normalize (blend K p 0 x) = x.val.val
  simpa [blend] using NormedSpace.normalize_eq_self_of_norm_eq_one
    (ClosedHemisphere.unit_norm x.val)

theorem contract_one (hK : Convex ℝ K) (h0 : (0 : E) ∉ K)
    (hscale : ∀ a : ℝ, 0 < a → ∀ x ∈ K, a • x ∈ K) (x : sphereSection K) :
    contract K p hK h0 hscale 1 x = p := by
  apply Subtype.ext
  apply Subtype.ext
  change NormedSpace.normalize (blend K p 1 x) = p.val.val
  simpa [blend] using NormedSpace.normalize_eq_self_of_norm_eq_one
    (ClosedHemisphere.unit_norm p.val)

def contraction (hK : Convex ℝ K) (h0 : (0 : E) ∉ K)
    (hscale : ∀ a : ℝ, 0 < a → ∀ x ∈ K, a • x ∈ K) :
    (ContinuousMap.id (sphereSection K)).Homotopy (ContinuousMap.const _ p) where
  toFun q := contract K p hK h0 hscale q.1 q.2
  continuous_toFun := continuous_contract K p hK h0 hscale
  map_zero_left := contract_zero K p hK h0 hscale
  map_one_left := contract_one K p hK h0 hscale

include p in
theorem contractibleSpace (hK : Convex ℝ K) (h0 : (0 : E) ∉ K)
    (hscale : ∀ a : ℝ, 0 < a → ∀ x ∈ K, a • x ∈ K) :
    ContractibleSpace (sphereSection K) :=
  (contractible_iff_id_nullhomotopic _).mpr ⟨p, ⟨contraction K p hK h0 hscale⟩⟩

end NoExoticSixSphere.NormalizedCone
