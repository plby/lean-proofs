import Wikipedia.NoExoticSixSphere.SlabBoundaryNeighborhood
import Wikipedia.NoExoticSixSphere.IntervalImmersion

/-!
# The ambient inclusion of a constant-end slab piece is an immersion

In the actual product collar coordinates this is the product of the interval
inclusion and the endpoint regular-fiber inclusion. Both differentials are
injective, including at the two endpoint times.
-/

open scoped Manifold ContDiff
open Set Module TopologicalSpace Function

namespace NoExoticSixSphere.CylinderFiberSlab

variable {B H M C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  (F : C(ℝ × M, N)) (f : C(M, N)) (hf : ContMDiff I J ∞ f) (b : N)
  (hreg : ∀ x, f x = b → Surjective (mfderiv I J f x))
  (k : ℕ) (hd : finrank ℝ B = finrank ℝ C + k)
  (s t : ℝ) [Fact (s < t)] (U : Opens ℝ)
  (hconstant : ∀ r ∈ U, ∀ x, F (r, x) = f x)

theorem boundaryAtlas_injective_mfderiv_ambient (p : timeDomain F b s t U) :
    letI := boundaryAtlas F f hf b hreg k hd s t U hconstant;
    Injective (mfderiv ((𝓡∂ 1).prod (𝓡 k)) ((𝓘(ℝ, ℝ)).prod I)
      (fun q : timeDomain F b s t U ↦ q.val.val.val) p) := by
  let := regularFiberAtlas f hf b hreg k hd
  let := regularFiber_isManifold f hf b hreg k hd
  let := boundaryAtlas F f hf b hreg k hd s t U hconstant
  let g := Prod.map (fun r : timeSlice s t U ↦ r.val.val)
    (Subtype.val : {x : M // f x = b} → M)
  have ht : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (fun r : timeSlice s t U ↦ r.val.val) :=
    contMDiff_subtypeVal_Icc.comp contMDiff_subtype_val
  have hx := regularFiber_contMDiff_subtype_val f hf b hreg k hd
  have hg : ContMDiff ((𝓡∂ 1).prod (𝓡 k)) ((𝓘(ℝ, ℝ)).prod I) ∞ g := ht.prodMap hx
  have hinj (q : timeSlice s t U × {x : M // f x = b}) :
      Injective (mfderiv ((𝓡∂ 1).prod (𝓡 k)) ((𝓘(ℝ, ℝ)).prod I) g q) := by
    rw [show g = Prod.map (fun r : timeSlice s t U ↦ r.val.val)
      (Subtype.val : {x : M // f x = b} → M) from rfl,
      mfderiv_prodMap (ht.mdifferentiable (by simp) q.1) (hx.mdifferentiable (by simp) q.2)]
    intro v w hvw
    apply Prod.ext
    · exact (injective_mfderiv_openIntervalInclusion (timeSlice s t U) q.1) (congrArg Prod.fst hvw)
    · exact (regularFiber_injective_mfderiv_subtype_val f hf b hreg k hd q.2)
        (congrArg Prod.snd hvw)
  let e := ModelAtlasTransport.diffeomorph (homeomorph F b s t f U hconstant)
    ((𝓡∂ 1).prod (𝓡 k))
  change Injective (mfderiv ((𝓡∂ 1).prod (𝓡 k)) ((𝓘(ℝ, ℝ)).prod I) (g ∘ e) p)
  rw [mfderiv_comp p (hg.mdifferentiable (by simp) (e p))
    (e.contMDiff.mdifferentiable (by simp) p)]
  exact (hinj (e p)).comp (e.mfderivToContinuousLinearEquiv (by simp) p).injective

end NoExoticSixSphere.CylinderFiberSlab
