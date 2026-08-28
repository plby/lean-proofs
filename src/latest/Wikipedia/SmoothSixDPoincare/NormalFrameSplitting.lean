import Wikipedia.SmoothSixDPoincare.DiskNormalFrame

/-!
# The tangent-normal splitting supplied by the constructed disk frame

The disk derivative and its intrinsic normal frame together give exactly the
manifold tangent space. The splitting maps are actual continuous linear
equivalences, with the prescribed derivative-plus-normal-vector formula.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.SmoothSixDPoincare.DiskFraming

variable {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- A tangent parametrization and an intrinsic normal frame identify their product with
the ambient tangent subspace, not with the larger Euclidean ambient space. -/
def normalSplitEquiv (L : D →L[ℝ] F) (A : Z →L[ℝ] F) {V : Submodule ℝ F}
    (hL : Injective L) (hA : Injective A) (hLV : L.range ≤ V)
    (hAr : A.range = L.rangeᗮ ⊓ V) : (D × Z) ≃L[ℝ] V := by
  let a : D × Z →ₗ[ℝ] F := L.toLinearMap.coprod A.toLinearMap
  have har : a.range = V := by
    rw [LinearMap.range_coprod, hAr]
    exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hLV
  have had : Disjoint L.range A.range := by
    rw [hAr]
    exact L.range.orthogonal_disjoint.mono_right inf_le_left
  have hai : Injective a := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range _ _ had,
      LinearMap.ker_eq_bot.mpr hL, LinearMap.ker_eq_bot.mpr hA, Submodule.prod_bot]
  let b : D × Z →ₗ[ℝ] V := a.codRestrict V (fun q => har ▸ LinearMap.mem_range_self a q)
  have hbi : Injective b := fun _ _ h => hai (congrArg Subtype.val h)
  have hbs : Surjective b := by
    intro v
    have hv : (v : F) ∈ a.range := har.symm ▸ v.property
    obtain ⟨q, hq⟩ := hv
    exact ⟨q, Subtype.ext hq⟩
  exact (LinearEquiv.ofBijective b ⟨hbi, hbs⟩).toContinuousLinearEquiv

omit [FiniteDimensional ℝ F] in
/-- The splitting has the claimed explicit tangent-plus-normal formula. -/
theorem normalSplitEquiv_apply (L : D →L[ℝ] F) (A : Z →L[ℝ] F) {V : Submodule ℝ F}
    (hL : Injective L) (hA : Injective A) (hLV : L.range ≤ V)
    (hAr : A.range = L.rangeᗮ ⊓ V) (q : D × Z) :
    (normalSplitEquiv L A hL hA hLV hAr q : F) = L q.1 + A q.2 := rfl

end Wikipedia.SmoothSixDPoincare.DiskFraming

namespace Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding

variable {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] (e : NativeEuclideanEmbedding E M)

/-- The constructed normal frame and actual disk derivative split the manifold tangent image. -/
def diskTangentNormalEquiv {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {x : D}
    (hi : Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension))
    (hA : Injective A) (hAr : A.range = e.diskNormalSpace f x) :
    (D × EuclideanSpace ℝ (Fin n)) ≃L[ℝ] e.tangentImage (f x) :=
  DiskFraming.normalSplitEquiv (fderiv ℝ (e.toFun ∘ f) x) A
    (e.injective_fderiv_comp hf hi) hA (e.diskTangentImage_le hf x) hAr

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The splitting uses the original derivative and the actual frame vectors. -/
theorem diskTangentNormalEquiv_apply {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {x : D}
    (hi : Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension))
    (hA : Injective A) (hAr : A.range = e.diskNormalSpace f x)
    (q : D × EuclideanSpace ℝ (Fin n)) :
    (e.diskTangentNormalEquiv hf hi A hA hAr q : EuclideanSpace ℝ (Fin e.ambientDimension)) =
      (mvfderiv 𝓘(ℝ, E) e.toFun (f x)) ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x) q.1) + A q.2 := by
  change fderiv ℝ (e.toFun ∘ f) x q.1 + A q.2 = _
  rw [e.fderiv_comp_eq hf x]
  rfl

end Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding
