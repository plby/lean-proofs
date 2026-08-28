import Wikipedia.NoExoticSixSphere.SlabBoundaryNeighborhood

/-!
# The ambient smooth-map criterion for slab boundary neighborhoods

For the constructed boundary atlas, a map into a constant-end neighborhood
is smooth exactly when its original ambient cylinder-valued map is smooth.
The closed interval's genuine boundary model and its smooth inclusion are
used, including at the two endpoints.
-/

open scoped Manifold ContDiff
open Module TopologicalSpace Topology

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
  {B' H'' P : Type*} [NormedAddCommGroup B'] [NormedSpace ℝ B']
  [TopologicalSpace H''] {L : ModelWithCorners ℝ B' H''}
  [TopologicalSpace P] [ChartedSpace H'' P]

theorem boundaryAtlas_contMDiff_iff_ambient (g : P → timeDomain F b s t U) :
    letI := boundaryAtlas F f hf b hreg k hd s t U hconstant;
    ContMDiff L ((𝓡∂ 1).prod (𝓡 k)) ∞ g ↔
      ContMDiff L ((𝓘(ℝ, ℝ)).prod I) ∞ (fun x ↦ (g x).val.val.val) := by
  let := regularFiberAtlas f hf b hreg k hd
  let := boundaryAtlas F f hf b hreg k hd s t U hconstant
  constructor
  · intro hg
    exact (boundaryAtlas_contMDiff_ambient F f hf b hreg k hd s t U hconstant).comp hg
  · intro hg
    let e := homeomorph F b s t f U hconstant
    have hgc : Continuous g := by
      apply IsInducing.subtypeVal.continuous_iff.mpr
      apply IsInducing.subtypeVal.continuous_iff.mpr
      apply IsInducing.subtypeVal.continuous_iff.mpr
      exact hg.continuous
    have hc := e.continuous.comp hgc
    have ht : ContMDiff L (𝓡∂ 1) ∞ (fun x ↦ (e (g x)).1.val) :=
      contMDiff_iff_comp_subtypeVal_Icc.mpr
        ⟨continuous_subtype_val.comp hc.fst, contMDiff_fst.comp hg⟩
    have hto : ContMDiff L (𝓡∂ 1) ∞ (fun x ↦ (e (g x)).1) :=
      (ContMDiff.subtypeVal_comp_iff (timeSlice s t U) _).mp ht
    have hx : ContMDiff L (𝓡 k) ∞ (fun x ↦ (e (g x)).2) :=
      (regularFiber_contMDiff_iff_ambient f hf b hreg k hd _).mpr (contMDiff_snd.comp hg)
    have hprod : ContMDiff L ((𝓡∂ 1).prod (𝓡 k)) ∞ (e ∘ g) := hto.prodMk hx
    have h := (ModelAtlasTransport.contMDiff_symm e ((𝓡∂ 1).prod (𝓡 k))).comp hprod
    simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using h

end NoExoticSixSphere.CylinderFiberSlab
