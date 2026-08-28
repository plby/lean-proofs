import Wikipedia.NoExoticSixSphere.ParametricRegularValues
import Wikipedia.NoExoticSixSphere.OpenSubsetDifferential
import Wikipedia.NoExoticSixSphere.SardAlmostEvery

/-!
# Parametric regular values on an actual open parameter–source domain

The domain may couple parameters and source points, as happens in an
invertible-minor chart of a derivative family. The actual zero manifold is
constructed inside this open domain. Its inclusion has the original kernel
as tangent image, so Sard still detects regular spatial zeros.
-/

noncomputable section

open Set Function Module TopologicalSpace
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ParametricRegular

variable {P E F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem ae_parameters_on_of_dimension [MeasurableSpace P] [BorelSpace P]
    (μ : Measure P) [IsAddHaarMeasure μ] (f : P × E → F) (U : Opens (P × E))
    (hf : ContDiffOn ℝ ∞ f U)
    (hreg : ∀ q ∈ U, f q = 0 → Surjective (fderiv ℝ f q))
    (k : ℕ) (hd : finrank ℝ P + finrank ℝ E = finrank ℝ F + k) :
    ∀ᵐ p ∂μ, ∀ x : E, (p, x) ∈ U → f (p, x) = 0 →
      Surjective (fderiv ℝ (fun y ↦ f (p, y)) x) := by
  let e : (P × E) ≃L[ℝ] (Fin (finrank ℝ (P × E)) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_fin_fun ℝ).symm
  let : SecondCountableTopology (P × E) := e.toHomeomorph.secondCountableTopology
  let g : U → F := fun q ↦ f q.val
  let : SecondCountableTopology {q : U // g q = 0} :=
    TopologicalSpace.Subtype.secondCountableTopology {q : U | g q = 0}
  have hg : ContMDiff 𝓘(ℝ, P × E) 𝓘(ℝ, F) ∞ g := by
    intro q
    apply contMDiffAt_subtype_iff.mpr
    exact (hf.contDiffAt (U.isOpen.mem_nhds q.property)).contMDiffAt
  have hi : ContMDiff 𝓘(ℝ, P × E) 𝓘(ℝ, P × E) ∞
      (Subtype.val : U → P × E) := contMDiff_subtype_val
  have hgd (q : U) : mfderiv 𝓘(ℝ, P × E) 𝓘(ℝ, F) g q =
      (fderiv ℝ f q.val).comp (mfderiv 𝓘(ℝ, P × E) 𝓘(ℝ, P × E) Subtype.val q) := by
    have h := mfderiv_comp q
      ((hf.contDiffAt (U.isOpen.mem_nhds q.property)).contMDiffAt.mdifferentiableAt (by simp))
      (hi.mdifferentiable (by simp) q)
    rw [mfderiv_eq_fderiv] at h
    exact h
  have hgr : ∀ q : U, g q = 0 → Surjective (mfderiv 𝓘(ℝ, P × E) 𝓘(ℝ, F) g q) := by
    intro q hq
    rw [hgd]
    exact (hreg q.val q.property hq).comp
      (mfderiv_openSubset_val_bijective (I := 𝓘(ℝ, P × E)) U q).surjective
  have hdim : finrank ℝ (P × E) = finrank ℝ F + k := by
    simpa only [finrank_prod] using hd
  obtain ⟨A⟩ := nonempty_regularLevelAtlas isOpen_univ hg.contMDiffOn
    (subset_univ _) hgr k hdim
  let := A.chartedSpace
  let := A.isManifold
  let inclusion : {q : U // g q = 0} → P × E := fun q ↦ q.val.val
  have hsmooth : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, P × E) ∞ inclusion :=
    hi.comp A.contMDiff_subtype_val
  let projection : {q : U // g q = 0} → P := fun q ↦ q.val.val.1
  have hprojSmooth : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, P) ∞ projection :=
    contDiff_fst.contMDiff.comp hsmooth
  apply (Sard.ae_regularValues μ hprojSmooth).mono
  intro p hp x hx hz
  let q : {q : U // g q = 0} := ⟨⟨(p, x), hx⟩, hz⟩
  let L : P × E →L[ℝ] F := fderiv ℝ f (p, x)
  let J : P × E →L[ℝ] P × E :=
    mfderiv 𝓘(ℝ, P × E) 𝓘(ℝ, P × E) (Subtype.val : U → P × E) q.val
  let S : EuclideanSpace ℝ (Fin k) →L[ℝ] P × E :=
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, P × E)
      (Subtype.val : {q : U // g q = 0} → U) q
  have hS : S.range = (L.comp J).ker := by
    have hd' : finrank ℝ (P × E) = finrank ℝ F +
        finrank ℝ (EuclideanSpace ℝ (Fin k)) := by
      simpa only [finrank_euclideanSpace_fin] using hdim
    have h := A.range_inclusion_eq_kernel q (hg.mdifferentiable (by simp) q.val)
      (hgr q.val q.property) hd'
    rw [hgd] at h
    exact h
  have hJ : Surjective J :=
    (mfderiv_openSubset_val_bijective (I := 𝓘(ℝ, P × E)) U q.val).surjective
  have hT : (J.comp S).range = L.ker := range_composed_inclusion L J S hJ hS
  have hdinc : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, P × E) inclusion q =
      J.comp S :=
    mfderiv_comp q (hi.mdifferentiable (by simp) q.val)
      (A.contMDiff_subtype_val.mdifferentiable (by simp) q)
  have hdproj : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, P) projection q =
      (ContinuousLinearMap.fst ℝ P E).comp (J.comp S) := by
    have h := mfderiv_comp q
      ((contDiff_fst : ContDiff ℝ ∞ (Prod.fst : P × E → P)).contMDiff.mdifferentiable
        (by simp) (p, x)) (hsmooth.mdifferentiable (by simp) q)
    rw [mfderiv_eq_fderiv, fderiv_fst, hdinc] at h
    exact h
  have hpq := hp q rfl
  rw [hdproj] at hpq
  have hv := (surjective_projection_iff L (J.comp S) (hreg (p, x) hx hz) hT).mp hpq
  have hsp := ((hf.contDiffAt (U.isOpen.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.comp
    x (hasFDerivAt_prodMk_right p x)
  change Surjective (fderiv ℝ (f ∘ Prod.mk p) x)
  rw [hsp.fderiv]
  exact hv

theorem dense_parameters_on_of_dimension (f : P × E → F) (U : Opens (P × E))
    (hf : ContDiffOn ℝ ∞ f U)
    (hreg : ∀ q ∈ U, f q = 0 → Surjective (fderiv ℝ f q))
    (k : ℕ) (hd : finrank ℝ P + finrank ℝ E = finrank ℝ F + k) :
    Dense {p : P | ∀ x : E, (p, x) ∈ U → f (p, x) = 0 →
      Surjective (fderiv ℝ (fun y ↦ f (p, y)) x)} := by
  let : MeasurableSpace P := borel P
  let : BorelSpace P := ⟨rfl⟩
  exact Measure.dense_of_ae (ae_parameters_on_of_dimension addHaar f U hf hreg k hd)

theorem ae_parameters_on [MeasurableSpace P] [BorelSpace P]
    (μ : Measure P) [IsAddHaarMeasure μ] (f : P × E → F) (U : Opens (P × E))
    (hf : ContDiffOn ℝ ∞ f U)
    (hreg : ∀ q ∈ U, f q = 0 → Surjective (fderiv ℝ f q)) :
    ∀ᵐ p ∂μ, ∀ x : E, (p, x) ∈ U → f (p, x) = 0 →
      Surjective (fderiv ℝ (fun y ↦ f (p, y)) x) := by
  by_cases hz : ∃ q ∈ U, f q = 0
  · obtain ⟨q, hq, hzero⟩ := hz
    have hd : finrank ℝ F ≤ finrank ℝ P + finrank ℝ E := by
      have h := LinearMap.finrank_le_finrank_of_surjective
        (f := (fderiv ℝ f q).toLinearMap) (hreg q hq hzero)
      simpa only [finrank_prod] using h
    exact ae_parameters_on_of_dimension μ f U hf hreg
      (finrank ℝ P + finrank ℝ E - finrank ℝ F) (by omega)
  · exact Filter.Eventually.of_forall fun p x hx hzero ↦ (hz ⟨(p, x), hx, hzero⟩).elim

theorem dense_parameters_on (f : P × E → F) (U : Opens (P × E))
    (hf : ContDiffOn ℝ ∞ f U)
    (hreg : ∀ q ∈ U, f q = 0 → Surjective (fderiv ℝ f q)) :
    Dense {p : P | ∀ x : E, (p, x) ∈ U → f (p, x) = 0 →
      Surjective (fderiv ℝ (fun y ↦ f (p, y)) x)} := by
  by_cases hz : ∃ q ∈ U, f q = 0
  · obtain ⟨q, hq, hzero⟩ := hz
    have hd : finrank ℝ F ≤ finrank ℝ P + finrank ℝ E := by
      have h := LinearMap.finrank_le_finrank_of_surjective
        (f := (fderiv ℝ f q).toLinearMap) (hreg q hq hzero)
      simpa only [finrank_prod] using h
    exact dense_parameters_on_of_dimension f U hf hreg
      (finrank ℝ P + finrank ℝ E - finrank ℝ F) (by omega)
  · have he : {p : P | ∀ x : E, (p, x) ∈ U → f (p, x) = 0 →
        Surjective (fderiv ℝ (fun y ↦ f (p, y)) x)} = univ := by
      apply eq_univ_of_forall
      intro p x hx hzero
      exact (hz ⟨(p, x), hx, hzero⟩).elim
    rw [he]
    exact dense_univ

theorem ae_parameters_on_countable {ι : Type*} [Countable ι]
    [MeasurableSpace P] [BorelSpace P] (μ : Measure P) [IsAddHaarMeasure μ]
    (f : ι → P × E → F) (U : ι → Opens (P × E))
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (hreg : ∀ i q, q ∈ U i → f i q = 0 → Surjective (fderiv ℝ (f i) q)) :
    ∀ᵐ p ∂μ, ∀ i x, (p, x) ∈ U i → f i (p, x) = 0 →
      Surjective (fderiv ℝ (fun y ↦ f i (p, y)) x) :=
  ae_all_iff.mpr fun i ↦ ae_parameters_on μ (f i) (U i) (hf i) (hreg i)

end NoExoticSixSphere.ParametricRegular
