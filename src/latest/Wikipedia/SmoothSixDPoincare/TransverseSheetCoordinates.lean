import Wikipedia.SmoothSixDPoincare.NativeSmoothRetraction
import Wikipedia.SmoothSixDPoincare.LocalInverseIntoManifold

/-!
# Native coordinates adding two intersecting sheets

In a constructed Euclidean realization, add the two sheet maps and subtract
their common base point, then retract to the original manifold. The resulting
map agrees exactly with each sheet on its respective coordinate axis. Its
native derivative at the common point is the sum of the two native sheet
derivatives. This supplies the analytic map for simultaneous straightening.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.TransverseCoordinates

variable {D Z A : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup A] [NormedSpace ℝ A]

def sumMap (f : D → A) (g : Z → A) (q : D × Z) : A := f q.1 + g q.2 - f 0

omit [NormedSpace ℝ D] [NormedSpace ℝ Z] [NormedSpace ℝ A] in
theorem sumMap_left (f : D → A) (g : Z → A) (hzero : g 0 = f 0) (x : D) :
    sumMap f g (x, 0) = f x := by simp [sumMap, hzero]

omit [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedSpace ℝ A] in
theorem sumMap_right (f : D → A) (g : Z → A) (z : Z) :
    sumMap f g (0, z) = g z := by simp [sumMap, add_sub_cancel_left]

theorem contDiffOn_sumMap {f : D → A} {g : Z → A} {U : Set D} {V : Set Z}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g V) :
    ContDiffOn ℝ ∞ (sumMap f g) (U ×ˢ V) :=
  ((hf.comp contDiff_fst.contDiffOn (fun _ hx => hx.1)).add
    (hg.comp contDiff_snd.contDiffOn (fun _ hx => hx.2))).sub contDiffOn_const

theorem hasFDerivAt_sumMap_zero {f : D → A} {g : Z → A}
    (hf : DifferentiableAt ℝ f 0) (hg : DifferentiableAt ℝ g 0) :
    HasFDerivAt (sumMap f g) ((fderiv ℝ f 0).coprod (fderiv ℝ g 0)) (0, 0) := by
  have hfst := (ContinuousLinearMap.fst ℝ D Z).hasFDerivAt (x := (0, 0))
  have hsnd := (ContinuousLinearMap.snd ℝ D Z).hasFDerivAt (x := (0, 0))
  have hd := ((hf.hasFDerivAt.comp (0, 0) hfst).add
    (hg.hasFDerivAt.comp (0, 0) hsnd)).sub (hasFDerivAt_const (f 0) (0, 0))
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro q
  simp [ContinuousLinearMap.coprod_apply]

end Wikipedia.SmoothSixDPoincare.TransverseCoordinates

namespace Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding.SmoothRetraction

variable {E M D Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)

def sheetCoordinates (f : D → M) (g : Z → M) : D × Z → M :=
  r.toFun ∘ TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g)

def sheetCoordinateDomain (f : D → M) (g : Z → M) (U : Set D) (V : Set Z) : Set (D × Z) :=
  (U ×ˢ V) ∩ TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) ⁻¹' r.domain

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedSpace ℝ D] [NormedSpace ℝ Z] in
theorem sheetCoordinates_left (f : D → M) (g : Z → M) (hzero : g 0 = f 0) (x : D) :
    r.sheetCoordinates f g (x, 0) = f x := by
  have hsum := TransverseCoordinates.sumMap_left (e.toFun ∘ f) (e.toFun ∘ g)
    (congrArg e.toFun hzero) x
  change r.toFun (TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) (x, 0)) = f x
  rw [hsum]
  exact r.retract (f x)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
theorem sheetCoordinates_right (f : D → M) (g : Z → M) (z : Z) :
    r.sheetCoordinates f g (0, z) = g z := by
  rw [sheetCoordinates, comp_apply, TransverseCoordinates.sumMap_right]
  exact r.retract (g z)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedSpace ℝ D] [NormedSpace ℝ Z] in
theorem zero_mem_sheetCoordinateDomain (f : D → M) (g : Z → M)
    {U : Set D} {V : Set Z} (hU : (0 : D) ∈ U) (hV : (0 : Z) ∈ V) :
    (0, 0) ∈ r.sheetCoordinateDomain f g U V := by
  refine ⟨⟨hU, hV⟩, ?_⟩
  change TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) (0, 0) ∈ r.domain
  rw [TransverseCoordinates.sumMap_right]
  exact r.contains ⟨g 0, rfl⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem isOpen_sheetCoordinateDomain {f : D → M} {g : Z → M} {U : Set D} {V : Set Z}
    (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g V) :
    IsOpen (r.sheetCoordinateDomain f g U V) :=
  (TransverseCoordinates.contDiffOn_sumMap
    (e.smooth.comp_contMDiffOn hf).contDiffOn
    (e.smooth.comp_contMDiffOn hg).contDiffOn).continuousOn.isOpen_inter_preimage
      (hU.prod hV) r.open_domain

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem contMDiffOn_sheetCoordinates {f : D → M} {g : Z → M} {U : Set D} {V : Set Z}
    (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g V) :
    ContMDiffOn 𝓘(ℝ, D × Z) 𝓘(ℝ, E) ∞ (r.sheetCoordinates f g)
      (r.sheetCoordinateDomain f g U V) :=
  r.smooth.comp ((TransverseCoordinates.contDiffOn_sumMap
    (e.smooth.comp_contMDiffOn hf).contDiffOn
    (e.smooth.comp_contMDiffOn hg).contDiffOn).contMDiffOn.mono inter_subset_left)
      (fun _ hx => hx.2)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The exact native derivative is the sum of the sheet tangent maps, with no chart hypothesis. -/
theorem mfderiv_sheetCoordinates_zero {f : D → M} {g : Z → M} (hzero : g 0 = f 0)
    (hf : ContMDiffAt 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f 0)
    (hg : ContMDiffAt 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g 0) :
    mfderiv 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (r.sheetCoordinates f g) (0, 0) =
      (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0) := by
  have heF := (e.smooth.contMDiffAt.comp 0 hf).contDiffAt
  have heG := (e.smooth.contMDiffAt.comp 0 hg).contDiffAt
  have hsum := TransverseCoordinates.hasFDerivAt_sumMap_zero
    (heF.differentiableAt (by simp)) (heG.differentiableAt (by simp))
  have hbase : TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) (0, 0) =
      e.toFun (f 0) := by
    rw [TransverseCoordinates.sumMap_right]
    exact congrArg e.toFun hzero
  have hr : MDifferentiableAt (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun
      (TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) (0, 0)) := by
    rw [hbase]
    exact (r.smooth.contMDiffAt
      (r.open_domain.mem_nhds (r.contains ⟨f 0, rfl⟩))).mdifferentiableAt (by simp)
  have hdf : fderiv ℝ (e.toFun ∘ f) 0 =
      (mfderiv 𝓘(ℝ, E) (𝓡 e.ambientDimension) e.toFun (f 0)).comp
        (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp 0
      (e.smooth.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  have hdg : fderiv ℝ (e.toFun ∘ g) 0 =
      (mfderiv 𝓘(ℝ, E) (𝓡 e.ambientDimension) e.toFun (f 0)).comp
        (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp 0
      (e.smooth.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))]
    rw [hzero]
  rw [sheetCoordinates, mfderiv_comp (0, 0) hr hsum.differentiableAt.mdifferentiableAt,
    mfderiv_eq_fderiv, hsum.fderiv, hbase, hdf, hdg]
  apply ContinuousLinearMap.ext
  intro q
  have hleft := congrArg (fun L => L ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0) q.1))
    (r.mfderiv_retract_comp (f 0))
  have hright := congrArg (fun L => L ((mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0) q.2))
    (r.mfderiv_retract_comp (f 0))
  let R : EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] E :=
    mfderiv (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (e.toFun (f 0))
  let T : E →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
    mfderiv 𝓘(ℝ, E) (𝓡 e.ambientDimension) e.toFun (f 0)
  let F : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0
  let G : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0
  change R (T (F q.1) + T (G q.2)) = F q.1 + G q.2
  change R (T (F q.1)) = F q.1 at hleft
  change R (T (G q.2)) = G q.2 at hright
  rw [map_add, hleft, hright]

end Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding.SmoothRetraction
