import Wikipedia.NoExoticSixSphere.CylinderFiberSlab
import Wikipedia.NoExoticSixSphere.ModelAtlasTransport
import Wikipedia.NoExoticSixSphere.RegularFiberManifold
import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# Boundary charts on constant-end slab neighborhoods

The actual open subset of a bounded fiber slab receives the product boundary
atlas through its proved homeomorphism to an open part of the closed time
interval times the regular endpoint fiber. Its ambient inclusion is smooth,
and its manifold boundary consists exactly of points at the interval's ends.
Compatibility with a global atlas on the whole slab is a separate step.
-/

open scoped Manifold ContDiff
open Set Module TopologicalSpace

namespace NoExoticSixSphere.CylinderFiberSlab

variable {B H M C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  (F : C(ℝ × M, N)) (f : C(M, N)) (hf : ContMDiff I J ∞ f) (b : N)
  (hreg : ∀ x, f x = b → Function.Surjective (mfderiv I J f x))
  (k : ℕ) (hd : finrank ℝ B = finrank ℝ C + k)
  (s t : ℝ) [Fact (s < t)] (U : Opens ℝ)
  (hconstant : ∀ r ∈ U, ∀ x, F (r, x) = f x)

@[instance_reducible]
noncomputable def boundaryAtlas :
    ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin k)))
      (timeDomain F b s t U) :=
  letI := regularFiberAtlas f hf b hreg k hd
  ModelAtlasTransport.atlas (H := ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin k)))
    (homeomorph F b s t f U hconstant)

theorem boundaryAtlas_isManifold : letI := boundaryAtlas F f hf b hreg k hd s t U hconstant;
    IsManifold ((𝓡∂ 1).prod (𝓡 k)) ∞ (timeDomain F b s t U) := by
  let := regularFiberAtlas f hf b hreg k hd
  let := regularFiber_isManifold f hf b hreg k hd
  exact ModelAtlasTransport.isManifold (homeomorph F b s t f U hconstant) ((𝓡∂ 1).prod (𝓡 k))

theorem boundaryAtlas_contMDiff_ambient :
    letI := boundaryAtlas F f hf b hreg k hd s t U hconstant;
    ContMDiff ((𝓡∂ 1).prod (𝓡 k)) ((𝓘(ℝ, ℝ)).prod I) ∞
      (fun p : timeDomain F b s t U ↦ p.val.val.val) := by
  let := regularFiberAtlas f hf b hreg k hd
  let := boundaryAtlas F f hf b hreg k hd s t U hconstant
  have ht : ContMDiff ((𝓡∂ 1).prod (𝓡 k)) 𝓘(ℝ, ℝ) ∞
      (fun p : timeSlice s t U × {x : M // f x = b} ↦ p.1.val.val) :=
    contMDiff_subtypeVal_Icc.comp (contMDiff_subtype_val.comp contMDiff_fst)
  have hx : ContMDiff ((𝓡∂ 1).prod (𝓡 k)) I ∞
      (fun p : timeSlice s t U × {x : M // f x = b} ↦ p.2.val) :=
    (regularFiber_contMDiff_subtype_val f hf b hreg k hd).comp contMDiff_snd
  exact (ht.prodMk hx).comp
    (ModelAtlasTransport.contMDiff (homeomorph F b s t f U hconstant) ((𝓡∂ 1).prod (𝓡 k)))

theorem boundaryAtlas_isBoundaryPoint_iff (p : timeDomain F b s t U) :
    letI := boundaryAtlas F f hf b hreg k hd s t U hconstant;
    ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p ↔ p.val.val.val.1 = s ∨ p.val.val.val.1 = t := by
  let := regularFiberAtlas f hf b hreg k hd
  let := regularFiber_isManifold f hf b hreg k hd
  let := boundaryAtlas F f hf b hreg k hd s t U hconstant
  let := boundaryAtlas_isManifold F f hf b hreg k hd s t U hconstant
  let e := homeomorph F b s t f U hconstant
  have he := (ModelAtlasTransport.diffeomorph e ((𝓡∂ 1).prod (𝓡 k))).isLocalDiffeomorph p
  have hb := he.isBoundaryPoint_iff (by simp)
  rw [hb]
  change e p ∈ ((𝓡∂ 1).prod (𝓡 k)).boundary
    (timeSlice s t U × {x : M // f x = b}) ↔ _
  rw [ModelWithCorners.boundary_of_boundaryless_right]
  change ((𝓡∂ 1).IsBoundaryPoint (e p).1 ∧ True) ↔ _
  rw [and_true]
  rw [ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val]
  change (e p).1.val ∈ (𝓡∂ 1).boundary (Icc s t) ↔ _
  rw [boundary_Icc]
  simp only [mem_insert_iff, mem_singleton_iff, Subtype.ext_iff]
  rfl

end NoExoticSixSphere.CylinderFiberSlab
