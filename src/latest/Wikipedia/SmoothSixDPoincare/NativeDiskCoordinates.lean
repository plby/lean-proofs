import Wikipedia.SmoothSixDPoincare.NativeSmoothRetraction
import Wikipedia.SmoothSixDPoincare.NormalFrameSplitting
import Wikipedia.SmoothSixDPoincare.FramedDisplacement
import Wikipedia.SmoothSixDPoincare.LocalInverseIntoManifold

/-!
# Actual disk-neighborhood coordinates in the native manifold

Move in the Euclidean realization by the intrinsic disk-normal frame, then
apply the constructed smooth retraction to the original manifold. This gives
a real map into that manifold, equal to the disk on zero normal vectors.
Its derivative is invertible along the immersive disk when the frame spans
the intrinsic normal spaces.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding.SmoothRetraction

variable {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
  {n : ℕ}

/-- Retraction of the actual normal displacement into the original manifold. -/
def diskCoordinates (f : D → M)
    (A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)) :
    D × EuclideanSpace ℝ (Fin n) → M :=
  r.toFun ∘ DiskFraming.displacement (e.toFun ∘ f) A

/-- The genuine domain on which the displacement stays in the smooth retraction neighborhood. -/
def diskCoordinateDomain (f : D → M)
    (A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension))
    (V : Set D) : Set (D × EuclideanSpace ℝ (Fin n)) :=
  (V ×ˢ univ) ∩ DiskFraming.displacement (e.toFun ∘ f) A ⁻¹' r.domain

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ D]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] in
/-- Zero normal vectors give exactly the original disk map, not just a homotopic map. -/
theorem diskCoordinates_zero (f : D → M)
    (A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension))
    (x : D) : r.diskCoordinates f A (x, 0) = f x := by
  rw [diskCoordinates, Function.comp_apply, DiskFraming.displacement_zero]
  exact r.retract (f x)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ D] in
/-- The coordinate domain is open wherever the frame is smooth. -/
theorem isOpen_diskCoordinateDomain {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)}
    {V : Set D} (hV : IsOpen V) (hA : ContDiffOn ℝ ∞ A V) :
    IsOpen (r.diskCoordinateDomain f A V) := by
  have hc := (DiskFraming.contDiffOn_displacement (e.smooth.comp hf).contDiff hA).continuousOn
  exact hc.isOpen_inter_preimage (hV.prod isOpen_univ) r.open_domain

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ D]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] in
/-- Every zero vector based in the frame domain lies in the actual coordinate domain. -/
theorem zero_mem_diskCoordinateDomain (f : D → M)
    (A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension))
    {V : Set D} {x : D} (hx : x ∈ V) : (x, 0) ∈ r.diskCoordinateDomain f A V := by
  refine ⟨⟨hx, mem_univ _⟩, ?_⟩
  change DiskFraming.displacement (e.toFun ∘ f) A (x, 0) ∈ r.domain
  rw [DiskFraming.displacement_zero]
  exact r.contains ⟨f x, rfl⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ D] in
/-- The actual manifold-valued coordinate map is smooth throughout its open domain. -/
theorem contMDiffOn_diskCoordinates {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)}
    {V : Set D} (hA : ContDiffOn ℝ ∞ A V) :
    ContMDiffOn 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞
      (r.diskCoordinates f A) (r.diskCoordinateDomain f A V) :=
  r.smooth.comp
    ((DiskFraming.contDiffOn_displacement (e.smooth.comp hf).contDiff hA).contMDiffOn.mono
      inter_subset_left) (fun _ hp => hp.2)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ D] in
/-- At zero, the native derivative is retraction applied to the tangent-normal sum. -/
theorem mfderiv_diskCoordinates_zero {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)}
    {x : D} (hA : ContDiffAt ℝ ∞ A x) :
    mfderiv 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) (r.diskCoordinates f A) (x, 0) =
      (mfderiv (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (e.toFun (f x))).comp
        ((fderiv ℝ (e.toFun ∘ f) x).coprod (A x)) := by
  have hd := DiskFraming.hasFDerivAt_displacement_zero
    (e.smooth.comp hf).contDiff.contDiffAt hA
  have hr : MDifferentiableAt (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun
      (DiskFraming.displacement (e.toFun ∘ f) A (x, 0)) := by
    rw [DiskFraming.displacement_zero]
    exact (r.smooth.contMDiffAt
      (r.open_domain.mem_nhds (r.contains ⟨f x, rfl⟩))).mdifferentiableAt (by simp)
  rw [diskCoordinates, mfderiv_comp (x, 0) hr hd.differentiableAt.mdifferentiableAt,
    mfderiv_eq_fderiv, hd.fderiv, DiskFraming.displacement_zero]
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The true intrinsic normal-frame condition makes the coordinate derivative invertible. -/
theorem isInvertible_mfderiv_diskCoordinates_zero {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)}
    {x : D} (hA : ContDiffAt ℝ ∞ A x)
    (hi : Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (hAi : Injective (A x)) (hAr : (A x).range = e.diskNormalSpace f x) :
    (mfderiv 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
      (r.diskCoordinates f A) (x, 0)).IsInvertible := by
  let L := e.diskTangentNormalEquiv hf hi (A x) hAi hAr
  let T := L.trans (e.tangentImageEquiv (f x)).symm
  refine ⟨T, ?_⟩
  apply ContinuousLinearMap.ext
  intro q
  rw [r.mfderiv_diskCoordinates_zero hf hA]
  apply e.injective_mvfderiv (f x)
  have hleft := congrArg Subtype.val ((e.tangentImageEquiv (f x)).apply_symm_apply (L q))
  exact hleft.trans (r.embedding_derivative_retract (L q).property).symm

/-- The coordinate map has an actual smooth local inverse at every framed disk point. -/
theorem isLocalDiffeomorphAt_diskCoordinates_zero {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)}
    {V : Set D} (hV : IsOpen V) (hA : ContDiffOn ℝ ∞ A V) {x : D} (hx : x ∈ V)
    (hi : Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (hAi : Injective (A x)) (hAr : (A x).range = e.diskNormalSpace f x) :
    IsLocalDiffeomorphAt 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞
      (r.diskCoordinates f A) (x, 0) :=
  isLocalDiffeomorphAt_of_contMDiffOn (r.isOpen_diskCoordinateDomain hf hV hA)
    (r.zero_mem_diskCoordinateDomain f A hx) (r.contMDiffOn_diskCoordinates hf hA)
    (r.isInvertible_mfderiv_diskCoordinates_zero hf (hA.contDiffAt (hV.mem_nhds hx)) hi hAi hAr)

end Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding.SmoothRetraction
