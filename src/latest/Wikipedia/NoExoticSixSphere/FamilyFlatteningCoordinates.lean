import Wikipedia.NoExoticSixSphere.ImplicitCurveCoordinates
import Wikipedia.NoExoticSixSphere.CorankOneChart
import Wikipedia.NoExoticSixSphere.SpatialDerivativeFamily

/-!
# Actual source coordinates for flattening a parameterized map

The leading output replaces the leading spatial coordinates, while time and
the last spatial coordinate are retained exactly. The invertible leading
block of the actual spatial derivative supplies the local inverse.
-/

noncomputable section

open Set Function TopologicalSpace
open scoped ContDiff Manifold

namespace NoExoticSixSphere.FamilyFlattening

open CorankOne

variable {T E F : Type}
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

def sourceOrder : (E × (T × ℝ)) ≃L[ℝ] T × (E × ℝ) where
  toFun q := (q.2.1, (q.1, q.2.2))
  invFun q := (q.2.1, (q.1, q.2.2))
  left_inv q := by rcases q with ⟨x, t, z⟩; rfl
  right_inv q := by rcases q with ⟨t, x, z⟩; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd)
  continuous_invFun := continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd)

def flatOrder : ((T × E) × ℝ) ≃L[ℝ] E × (T × ℝ) where
  toFun q := (q.1.2, (q.1.1, q.2))
  invFun q := ((q.2.1, q.1), q.2.2)
  left_inv q := by rcases q with ⟨⟨t, x⟩, z⟩; rfl
  right_inv q := by rcases q with ⟨x, t, z⟩; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_fst.snd.prodMk (continuous_fst.fst.prodMk continuous_snd)
  continuous_invFun := (continuous_snd.fst.prodMk continuous_fst).prodMk continuous_snd.snd

def head (f : T → E × ℝ → E × F) (q : E × (T × ℝ)) : E := (f q.2.1 (q.1, q.2.2)).1

def tail (f : T → E × ℝ → E × F) (q : E × (T × ℝ)) : F := (f q.2.1 (q.1, q.2.2)).2

def spatial (f : T → E × ℝ → E × F) (q : E × (T × ℝ)) : BlockMap E F :=
  fderiv ℝ (f q.2.1) (q.1, q.2.2)

omit [FiniteDimensional ℝ T] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem contDiff_head (f : T → E × ℝ → E × F) (hf : ContDiff ℝ ∞ (uncurry f)) :
    ContDiff ℝ ∞ (head f) :=
  (hf.comp (sourceOrder (T := T) (E := E)).contDiff).fst

omit [FiniteDimensional ℝ T] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem contDiff_tail (f : T → E × ℝ → E × F) (hf : ContDiff ℝ ∞ (uncurry f)) :
    ContDiff ℝ ∞ (tail f) :=
  (hf.comp (sourceOrder (T := T) (E := E)).contDiff).snd

omit [FiniteDimensional ℝ T] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem contDiff_spatial (f : T → E × ℝ → E × F) (hf : ContDiff ℝ ∞ (uncurry f)) :
    ContDiff ℝ ∞ (spatial f) :=
  (DiskHomotopy.contDiff_spatial_fderiv f hf).comp (sourceOrder (T := T) (E := E)).contDiff

omit [FiniteDimensional ℝ T] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem fderiv_head_slice (f : T → E × ℝ → E × F) (hf : ContDiff ℝ ∞ (uncurry f))
    (q : E × (T × ℝ)) :
    fderiv ℝ (fun x : E ↦ head f (x, q.2)) q.1 = leading (spatial f q) := by
  have ht : ContDiff ℝ ∞ (f q.2.1) := hf.comp (contDiff_const.prodMk contDiff_id)
  have hi : HasFDerivAt (fun x : E ↦ (x, q.2.2))
      (ContinuousLinearMap.inl ℝ E ℝ) q.1 :=
    hasFDerivAt_prodMk_left q.1 q.2.2
  have h := ((ht.differentiable (by simp) (q.1, q.2.2)).hasFDerivAt).comp q.1
    hi
  exact h.fst.fderiv

def domain (f : T → E × ℝ → E × F) (hf : ContDiff ℝ ∞ (uncurry f)) :
    Opens (E × (T × ℝ)) :=
  ⟨spatial f ⁻¹' (chart (E := E) (F := F) : Set (BlockMap E F)),
    (chart (E := E) (F := F)).isOpen.preimage (contDiff_spatial f hf).continuous⟩

structure Data (f : T → E × ℝ → E × F) where
  coord : PartialDiffeomorph 𝓘(ℝ, E × (T × ℝ)) 𝓘(ℝ, E × (T × ℝ))
    (E × (T × ℝ)) (E × (T × ℝ)) ∞
  source_chart : ∀ q ∈ coord.source, spatial f q ∈ chart
  coord_apply : ∀ q, coord q = (head f q, q.2)

omit [FiniteDimensional ℝ F] in
theorem exists_data (f : T → E × ℝ → E × F) (hf : ContDiff ℝ ∞ (uncurry f))
    (q : E × (T × ℝ)) (hq : spatial f q ∈ chart) :
    ∃ d : Data f, q ∈ d.coord.source := by
  have hb : Bijective (fderiv ℝ (fun x : E ↦ head f (x, q.2)) q.1) := by
    rw [fderiv_head_slice f hf]
    exact ⟨(leading_invertible hq).injective, (leading_invertible hq).surjective⟩
  obtain ⟨c, hcq, hcU, hceq⟩ := ImplicitCurve.exists_parameter_coordinates
    (head f) (domain f hf) (domain f hf).isOpen q.1 q.2 hq (contDiff_head f hf).contDiffOn hb
  exact ⟨⟨c, fun r hr ↦ hcU hr, hceq⟩, hcq⟩

end NoExoticSixSphere.FamilyFlattening
