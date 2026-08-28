import Wikipedia.HopfProblem.DegreeCollapseStableTwistDiskExtension
import Wikipedia.HopfProblem.DegreeCollapseOrthogonalFrameBlocks
import Wikipedia.HopfProblem.DegreeCollapseEightDimensionalFramedProduct

/-!
# Retwisting an actual framed spanning product

A stable contraction extends the boundary twist after adjoining the old
normal columns. Rotate the full disk-normal frame by that extension and
split it into four transverse columns and the remaining normal columns.
The exact boundary block fixes every old normal column. The existing
thickening theorem then constructs a genuine embedded framed product with
the prescribed transverse twist. The core disk is unchanged.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.NormalFrameRetwisting

open NoExoticSixSphere GLOrthonormalization
open OrthogonalFrameBlocks EightDimensionalFramedProduct

variable {N k : ℕ}

def rotated (C : Vector 4 →L[ℝ] Vector N) (T : Vector k →L[ℝ] Vector N)
    (Q : Vector (4 + k) →L[ℝ] Vector (4 + k)) : Vector (4 + k) →L[ℝ] Vector N :=
  (OperatorSum.operator C T).comp Q

theorem norm_rotated (C : Vector 4 →L[ℝ] Vector N) (T : Vector k →L[ℝ] Vector N)
    (Q : Vector (4 + k) →L[ℝ] Vector (4 + k))
    (hC : ∀ u, ‖C u‖ = ‖u‖) (hT : ∀ v, ‖T v‖ = ‖v‖)
    (ho : C.range ≤ T.rangeᗮ) (hQ : ∀ w, ‖Q w‖ = ‖w‖)
    (w : Vector (4 + k)) : ‖rotated C T Q w‖ = ‖w‖ :=
  (norm_operator C T hC hT ho (Q w)).trans (hQ w)

theorem rotated_normal (D : Vector 4 →L[ℝ] Vector N)
    (C : Vector 4 →L[ℝ] Vector N) (T : Vector k →L[ℝ] Vector N)
    (Q : Vector (4 + k) →L[ℝ] Vector (4 + k))
    (hC : C.range ≤ D.rangeᗮ) (hT : T.range ≤ D.rangeᗮ) :
    (rotated C T Q).range ≤ D.rangeᗮ := by
  have hB : (OperatorSum.operator C T).range ≤ D.rangeᗮ := by
    rw [OperatorSum.range_operator]
    exact sup_le hC hT
  rintro _ ⟨w, rfl⟩
  exact hB ⟨Q w, rfl⟩

theorem left_full_normal_complement (D : Vector 4 →L[ℝ] Vector N)
    (B : Vector (4 + k) →L[ℝ] Vector N)
    (hD : Injective D) (hB : ∀ w, ‖B w‖ = ‖w‖)
    (hBD : B.range ≤ D.rangeᗮ) (hN : k + 4 + 4 = N) :
    (left B).range = (OperatorSum.operator (right B) D).rangeᗮ := by
  have hC := (left_range_le B).trans hBD
  have hT := (right_range_le B).trans hBD
  have hCT := left_right_orthogonal B hB
  have hle : (left B).range ≤ (OperatorSum.operator (right B) D).rangeᗮ := by
    rw [OperatorSum.range_operator, ← Submodule.inf_orthogonal]
    exact le_inf hCT hC
  have hiT : Injective (right B) :=
    Stiefel.injective ⟨right B, norm_right_block B hB⟩
  have hiC : Injective (left B) :=
    Stiefel.injective ⟨left B, norm_left_block B hB⟩
  have hi := OperatorSum.injective_operator (right B) D hiT hD
    (D.range.orthogonal_disjoint.symm.mono_left hT)
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.finrank_range_of_inj hiC, finrank_euclideanSpace_fin]
  have hd := (OperatorSum.operator (right B) D).range.finrank_add_finrank_orthogonal
  rw [LinearMap.finrank_range_of_inj hi, finrank_euclideanSpace_fin,
    finrank_euclideanSpace_fin] at hd
  omega

variable (D : Vector 4 → Vector N) (T : Vector 4 → Vector k →L[ℝ] Vector N)
  (A : FramedProduct D T)

/-- Retwist the transverse boundary frame while keeping the core and all boundary normal columns. -/
theorem exists_retwisted_product_collar
    (hD : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ D x)
    (hinj : InjOn D (closedBall (0 : Vector 4) 1))
    (hiD : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ D x))
    (hN : k + 4 + 4 = N) (hk : 0 < k) (b : Sphere 3)
    (a : C(Sphere 3, OrthogonalOperators 4))
    (ha : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector 4) ∞ (fun s ↦ (a s).1.1))
    (z : UnitSphere (Vector 5))
    (h : (OrthogonalStabilization.stabilizeMap z a).Homotopic
      (ContinuousMap.const _ (OrthogonalPaths.identity 5))) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∃ T' : Vector 4 → Vector k →L[ℝ] Vector N, ∃ B : FramedProduct D T',
      (∀ s : Sphere 3, T' s.val = T s.val) ∧
      (∀ s : Sphere 3, B.transverse s.val = (A.transverse s.val).comp (a s).1.1) ∧
      (∀ s : Sphere 3, B.normalFrame (s.val, 0) = T s.val) ∧
      ∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
        T' x = T x ∧ B.transverse x =
          (A.transverse x).comp (a (SphereRadialRetraction.retract b x)).1.1 := by
  obtain ⟨r, hr, hr1, Q, hQs, hQn, hQc⟩ :=
    StableTwistDiskExtension.exists_smooth_block_collar_extension b z a ha h k hk
  have hQb (s : Sphere 3) : Q s.val = Stiefel.BlockSum.operator k (a s).1.1 := by
    have hs : r ≤ ‖s.val‖ := by rw [ClosedHemisphere.unit_norm]; exact hr1.le
    simpa only [SphereRadialRetraction.retract_coe] using
      hQc s.val (sphere_subset_closedBall s.property) hs
  let F : Vector 4 → Vector (4 + k) →L[ℝ] Vector N :=
    fun x ↦ rotated (A.transverse x) (T x) (Q x)
  have hCs (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      ContDiffAt ℝ ∞ F x :=
    (OperatorSum.contDiffAt_operator (A.smooth_transverse x hx)
      (A.smooth_coreFrame x hx)).clm_comp (hQs x hx)
  have hCT (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      (A.transverse x).range ≤ (T x).rangeᗮ := by
    rw [A.range_transverse x hx, OperatorSum.range_operator, ← Submodule.inf_orthogonal]
    exact inf_le_left
  have hCD (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      (A.transverse x).range ≤ (fderiv ℝ D x).rangeᗮ := by
    rw [A.range_transverse x hx, OperatorSum.range_operator, ← Submodule.inf_orthogonal]
    exact inf_le_right
  have hFn (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      ∀ w, ‖F x w‖ = ‖w‖ :=
    norm_rotated _ _ _ (A.norm_transverse x hx) (A.norm_coreFrame x hx)
      (hCT x hx) (hQn x hx)
  have hFD (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      (F x).range ≤ (fderiv ℝ D x).rangeᗮ :=
    rotated_normal _ _ _ _ (hCD x hx) (A.range_coreFrame x hx)
  let T' : Vector 4 → Vector k →L[ℝ] Vector N := fun x ↦ right (F x)
  let C' : Vector 4 → Vector 4 →L[ℝ] Vector N := fun x ↦ left (F x)
  have hT's (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      ContDiffAt ℝ ∞ T' x := (hCs x hx).clm_comp contDiffAt_const
  have hC's (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      ContDiffAt ℝ ∞ C' x := (hCs x hx).clm_comp contDiffAt_const
  have hT'n (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      ∀ w, ‖T' x w‖ = ‖w‖ := norm_right_block _ (hFn x hx)
  have hC'n (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      ∀ w, ‖C' x w‖ = ‖w‖ := norm_left_block _ (hFn x hx)
  have hT'r (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      (T' x).range ≤ (fderiv ℝ D x).rangeᗮ := (right_range_le _).trans (hFD x hx)
  have hC'r (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      (C' x).range = (OperatorSum.operator (T' x) (fderiv ℝ D x)).rangeᗮ :=
    left_full_normal_complement _ _ (hiD x hx) (hFn x hx) (hFD x hx) hN
  obtain ⟨B, hBC⟩ := exists_framedProduct_of_transverse D T' hD hinj hiD
    hT's hT'n hT'r hN C' hC's hC'n hC'r
  have hFb (s : Sphere 3) : F s.val =
      OperatorSum.operator ((A.transverse s.val).comp (a s).1.1) (T s.val) := by
    change (OperatorSum.operator (A.transverse s.val) (T s.val)).comp (Q s.val) = _
    rw [hQb, OperatorSum.operator_comp_block]
  have hTb (s : Sphere 3) : T' s.val = T s.val := by
    change right (F s.val) = T s.val
    rw [hFb, right_operator]
  refine ⟨r, hr, hr1, T', B, hTb, ?_, ?_, ?_⟩
  · intro s
    rw [hBC]
    change left (F s.val) = _
    rw [hFb, left_operator]
  · intro s
    exact (B.normalFrame_core s.val (sphere_subset_closedBall s.property)).trans (hTb s)
  · intro x hx hxr
    have hFx : F x = OperatorSum.operator
        ((A.transverse x).comp (a (SphereRadialRetraction.retract b x)).1.1) (T x) := by
      change (OperatorSum.operator (A.transverse x) (T x)).comp (Q x) = _
      rw [hQc x hx hxr, OperatorSum.operator_comp_block]
    constructor
    · change right (F x) = T x
      rw [hFx, right_operator]
    · rw [hBC]
      change left (F x) = _
      rw [hFx, left_operator]

end Wikipedia.HopfProblem.DegreeCollapse.NormalFrameRetwisting
