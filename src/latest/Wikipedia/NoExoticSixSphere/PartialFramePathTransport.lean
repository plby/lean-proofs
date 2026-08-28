import Wikipedia.NoExoticSixSphere.ComplementaryOperatorCoordinates
import Wikipedia.NoExoticSixSphere.ProjectionDiskFrame
import Wikipedia.NoExoticSixSphere.SmoothProjection

/-!
# Actual ambient linear transport along a path of partial frames

The normal projections of the given path have a full continuous frame,
constructed by projection transport along the interval contraction. Combining
this with the original columns gives ambient linear equivalences starting at
the identity and carrying every original column to its prescribed path value.
-/

noncomputable section

open scoped Manifold ContDiff unitInterval

namespace NoExoticSixSphere.Stiefel.FramePath

open GLOrthonormalization

variable {N n d : ℕ} (γ : C(I, Space N n))

def normalProjection (t : I) : Vector N →L[ℝ] Vector N := (γ t).val.rangeᗮ.starProjection

theorem normalProjection_eq (t : I) :
    normalProjection γ t = 1 - gramProjection (γ t).val := by
  rw [normalProjection, Submodule.starProjection_orthogonal',
    gramProjection_eq_starProjection _ (Stiefel.injective _)]

theorem continuous_normalProjection : Continuous (normalProjection γ) := by
  have hA : Continuous (fun t ↦ (γ t).val) := continuous_subtype_val.comp γ.continuous
  have hg : Continuous (fun t ↦ gramProjection (γ t).val) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hc : ContinuousAt (gramProjection : (Vector n →L[ℝ] Vector N) →
        Vector N →L[ℝ] Vector N) (γ t).val :=
      (contMDiffAt_gramProjection («I» := 𝓘(ℝ, Vector n →L[ℝ] Vector N))
        (A := id) contMDiffAt_id (Stiefel.injective _)).continuousAt
    exact ContinuousAt.comp (f := fun u : I ↦ (γ u).val) hc hA.continuousAt
  have he : normalProjection γ = fun t ↦ 1 - gramProjection (γ t).val :=
    funext (normalProjection_eq γ)
  rw [he]
  exact continuous_const.sub hg

theorem normalProjection_range (t : I) : (normalProjection γ t).range = (γ t).val.rangeᗮ :=
  (γ t).val.rangeᗮ.range_starProjection

theorem normalProjection_idempotent (t : I) : IsIdempotentElem (normalProjection γ t) :=
  (γ t).val.rangeᗮ.isIdempotentElem_starProjection

theorem exists_normalFrame (hN : n + d = N) :
    ∃ T : C(I, Space N d), ∀ t, (T t).val.range = (γ t).val.rangeᗮ := by
  have hr : Module.finrank ℝ (normalProjection γ 0).range = d := by
    rw [normalProjection_range]
    have hh := (γ 0).val.range.finrank_add_finrank_orthogonal
    rw [LinearMap.finrank_range_of_inj (Stiefel.injective _),
      finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at hh
    omega
  let H : I → I → Vector N →L[ℝ] Vector N := fun t s ↦ normalProjection γ (t * s)
  have hH (t s : I) : IsIdempotentElem (H t s) := normalProjection_idempotent γ _
  have hc : Continuous (fun p : I × I ↦ H p.1 p.2) :=
    (continuous_normalProjection γ).comp continuous_mul
  have hzero : H 0 = fun _ ↦ normalProjection γ 0 := by
    funext s
    change normalProjection γ (0 * s) = _
    rw [zero_mul]
  have hone : H 1 = normalProjection γ := by
    funext s
    change normalProjection γ (1 * s) = _
    rw [one_mul]
  obtain ⟨q⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (show Module.finrank ℝ (Vector d) = Module.finrank ℝ (normalProjection γ 0).range by
      rw [finrank_euclideanSpace_fin, hr])
  have hb : Nonempty (ContinuousRangeFrame (normalProjection γ) (Vector d)) := by
    simpa only [hone] using nonempty_continuousRangeFrame_of_homotopy H hH hc
      0 1 (normalProjection γ 0) hzero q
  obtain ⟨B⟩ := hb
  obtain ⟨T, hT⟩ := ProjectionDisk.exists_frame_of_rangeFrame (normalProjection γ) B
  exact ⟨T, fun t ↦ (hT t).trans (normalProjection_range γ t)⟩

variable (hN : n + d = N)

def normalFrame : C(I, Space N d) := (exists_normalFrame γ hN).choose

theorem normalFrame_range (t : I) :
    (normalFrame γ hN t).val.range = (γ t).val.rangeᗮ :=
  (exists_normalFrame γ hN).choose_spec t

theorem columns_disjoint (t : I) :
    Disjoint (γ t).val.range (normalFrame γ hN t).val.range := by
  rw [normalFrame_range]
  exact (γ t).val.range.orthogonal_disjoint

def fullCoordinates (t : I) : Vector (n + d) ≃L[ℝ] Vector N :=
  OperatorSum.coordinates (γ t).val (normalFrame γ hN t).val
    (Stiefel.injective _) (Stiefel.injective _) (columns_disjoint γ hN t) hN

theorem fullCoordinates_apply (t : I) (v : Vector (n + d)) :
    fullCoordinates γ hN t v = (γ t).val (EuclideanSpace.finAddEquivProd v).1 +
      (normalFrame γ hN t).val (EuclideanSpace.finAddEquivProd v).2 := rfl

theorem fullCoordinates_column (t : I) (v : Vector n) :
    fullCoordinates γ hN t ((EuclideanSpace.finAddEquivProd (n := n) (m := d)).symm (v, 0)) =
      (γ t).val v := by
  rw [fullCoordinates_apply, ContinuousLinearEquiv.apply_symm_apply, map_zero, add_zero]

theorem continuous_fullCoordinates :
    Continuous (fun t ↦ (fullCoordinates γ hN t).toContinuousLinearMap) :=
  OperatorSum.continuous_operator _ _ (continuous_subtype_val.comp γ.continuous)
    (continuous_subtype_val.comp (normalFrame γ hN).continuous)

def transport (t : I) : Vector N ≃L[ℝ] Vector N :=
  (fullCoordinates γ hN 0).symm.trans (fullCoordinates γ hN t)

theorem transport_apply (t : I) (v : Vector N) :
    transport γ hN t v = fullCoordinates γ hN t ((fullCoordinates γ hN 0).symm v) := rfl

theorem continuous_transport : Continuous (fun t ↦ (transport γ hN t).toContinuousLinearMap) := by
  change Continuous (fun t ↦ (fullCoordinates γ hN t).toContinuousLinearMap.comp
    (fullCoordinates γ hN 0).symm.toContinuousLinearMap)
  exact (continuous_fullCoordinates γ hN).clm_comp continuous_const

theorem transport_zero : transport γ hN 0 = ContinuousLinearEquiv.refl ℝ (Vector N) := by
  apply ContinuousLinearEquiv.ext
  funext v
  rw [transport_apply, ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem transport_column (t : I) (v : Vector n) :
    transport γ hN t ((γ 0).val v) = (γ t).val v := by
  rw [transport_apply]
  have he : (fullCoordinates γ hN 0).symm ((γ 0).val v) =
      (EuclideanSpace.finAddEquivProd (n := n) (m := d)).symm (v, 0) := by
    apply (fullCoordinates γ hN 0).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, fullCoordinates_column]
  rw [he, fullCoordinates_column]

end NoExoticSixSphere.Stiefel.FramePath
