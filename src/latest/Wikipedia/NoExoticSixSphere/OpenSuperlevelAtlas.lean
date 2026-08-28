import Wikipedia.NoExoticSixSphere.SuperlevelBoundary
import Wikipedia.NoExoticSixSphere.SuperlevelDifferential
import Wikipedia.NoExoticSixSphere.ModelAtlasTransport
import Wikipedia.NoExoticSixSphere.OpenSubsetDifferential

/-!
# Open pieces of constructed regular superlevels

A homeomorphism onto an actual open subset of a superlevel transports the
constructed boundary atlas while retaining the given source topology.
The resulting coordinate map has bijective differential, its boundary is
the actual zero set, and smoothness is detected in ambient coordinates.
-/

noncomputable section

open Set Topology TopologicalSpace Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.OpenSuperlevelAtlas

variable {B H M K N : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  {f : M → ℝ} (A : SuperlevelAtlas (K := K) I f)
  (U : Opens {x : M // 0 ≤ f x}) [TopologicalSpace N] (e : N ≃ₜ U)

@[instance_reducible]
def chartedSpace : ChartedSpace (ProductHalfSpace.Space K) N := by
  let := A.chartedSpace
  exact ModelAtlasTransport.atlas e

theorem isManifold : letI := chartedSpace A U e;
    IsManifold (ProductHalfSpace.model K) ∞ N := by
  let := A.chartedSpace
  let := A.isManifold
  exact ModelAtlasTransport.isManifold e (ProductHalfSpace.model K)

def diffeomorph : letI := A.chartedSpace; letI := chartedSpace A U e;
    N ≃ₘ⟮ProductHalfSpace.model K, ProductHalfSpace.model K⟯ U := by
  let := A.chartedSpace
  exact ModelAtlasTransport.diffeomorph e (ProductHalfSpace.model K)

theorem isBoundaryPoint_iff (x : N) : letI := chartedSpace A U e;
    (ProductHalfSpace.model K).IsBoundaryPoint x ↔ f (e x).val.val = 0 := by
  let := A.chartedSpace
  let := A.isManifold
  let := chartedSpace A U e
  let := isManifold A U e
  have h := ((diffeomorph A U e).isLocalDiffeomorph x).isBoundaryPoint_iff (by simp)
  rw [ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val, A.isBoundaryPoint_iff] at h
  exact h

theorem contMDiff_coordinates : letI := chartedSpace A U e;
    ContMDiff (ProductHalfSpace.model K) I ∞ (fun x : N ↦ (e x).val.val) := by
  let := A.chartedSpace
  let := A.isManifold
  let := chartedSpace A U e
  exact (A.contMDiff_subtype_val.comp (_root_.contMDiff_subtype_val (U := U))).comp
    (diffeomorph A U e).contMDiff_toFun

theorem bijective_mfderiv_coordinates (x : N) : letI := chartedSpace A U e;
    Bijective (mfderiv (ProductHalfSpace.model K) I (fun y : N ↦ (e y).val.val) x) := by
  let := A.chartedSpace
  let := A.isManifold
  let := chartedSpace A U e
  let d := diffeomorph A U e
  have hd := (d.mfderivToContinuousLinearEquiv (by simp) x).bijective
  have ho := mfderiv_openSubset_val_bijective (I := ProductHalfSpace.model K) U (d x)
  have hs := A.bijective_mfderiv_subtype_val (d x).val
  have hdd := d.contMDiff_toFun.mdifferentiable (by simp) x
  have hod := (_root_.contMDiff_subtype_val (I := ProductHalfSpace.model K)
    (U := U) (n := ∞)).mdifferentiable (by simp) (d x)
  have hsd := A.contMDiff_subtype_val.mdifferentiable (by simp) (d x).val
  change Bijective (mfderiv (ProductHalfSpace.model K) I
    ((Subtype.val : {x : M // 0 ≤ f x} → M) ∘
      ((Subtype.val : U → {x : M // 0 ≤ f x}) ∘ d)) x)
  rw [mfderiv_comp x hsd (hod.comp x hdd), mfderiv_comp x hod hdd]
  exact hs.comp (ho.comp hd)

variable {B' H' P : Type*} [NormedAddCommGroup B'] [NormedSpace ℝ B']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ B' H'}
  [TopologicalSpace P] [ChartedSpace H' P]

theorem contMDiffAt_iff_coordinates (g : P → N) (x : P) :
    letI := chartedSpace A U e;
    ContMDiffAt J (ProductHalfSpace.model K) ∞ g x ↔
      ContMDiffAt J I ∞ (fun y ↦ (e (g y)).val.val) x := by
  let := A.chartedSpace
  let := A.isManifold
  let := chartedSpace A U e
  constructor
  · intro hg
    exact (contMDiff_coordinates A U e).contMDiffAt.comp x hg
  · intro hg
    let g' := e ∘ g
    have hz : ContMDiffAt J (ProductHalfSpace.model K) ∞ (fun y ↦ (g' y).val) x :=
      (A.contMDiffAt_iff_ambient (fun y ↦ (g' y).val) x).mpr hg
    have hw := (ContMDiffAt.subtypeVal_comp_iff U g' x).mp hz
    have h := (diffeomorph A U e).symm.contMDiff_toFun.contMDiffAt.comp x hw
    change ContMDiffAt J (ProductHalfSpace.model K) ∞ (fun y ↦ e.symm (e (g y))) x at h
    simpa only [Homeomorph.symm_apply_apply] using h

theorem contMDiff_iff_coordinates (g : P → N) : letI := chartedSpace A U e;
    ContMDiff J (ProductHalfSpace.model K) ∞ g ↔
      ContMDiff J I ∞ (fun y ↦ (e (g y)).val.val) := by
  let := chartedSpace A U e
  exact forall_congr' (fun x ↦ contMDiffAt_iff_coordinates A U e g x)

end NoExoticSixSphere.OpenSuperlevelAtlas
