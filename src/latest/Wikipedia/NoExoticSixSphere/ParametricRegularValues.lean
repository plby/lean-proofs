import Wikipedia.NoExoticSixSphere.ParametricRegularLinear
import Wikipedia.NoExoticSixSphere.RegularLevelDifferential
import Wikipedia.NoExoticSixSphere.SardRegularValues
import Wikipedia.NoExoticSixSphere.SardAlmostEvery

/-!
# Parametric regular values from the actual zero manifold and Sard's theorem

If the total family is regular along its zero set, regular parameters of
the projection from that constructed zero manifold make every spatial zero
regular. Sard's theorem gives density of those parameters. The actual
spatial derivative is used, not an independent formal derivative family.
-/

noncomputable section

open Set Function Module
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ParametricRegular

variable {P E F : Type} {H M : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [I.Boundaryless] [IsManifold I ∞ M] in
theorem spatialDerivative_eq (f : P × M → F)
    (hf : ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) ∞ f) (p : P) (x : M) :
    mfderiv I 𝓘(ℝ, F) (fun y ↦ f (p, y)) x =
      (mfderiv (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) f (p, x)).comp
        (ContinuousLinearMap.inr ℝ P E) := by
  have h := mfderiv_comp x (hf.mdifferentiable (by simp) (p, x))
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  rw [mfderiv_prod_right] at h
  exact h

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [I.Boundaryless] [IsManifold I ∞ M] in
theorem parameterDerivative_eq (f : P × M → F)
    (hf : ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) ∞ f) (p : P) (x : M) :
    mfderiv 𝓘(ℝ, P) 𝓘(ℝ, F) (fun a ↦ f (a, x)) p =
      (mfderiv (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) f (p, x)).comp
        (ContinuousLinearMap.inl ℝ P E) := by
  have h := mfderiv_comp p (hf.mdifferentiable (by simp) (p, x))
    (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  simp only [id_eq] at h
  rw [mfderiv_prod_left] at h
  exact h

variable [SecondCountableTopology M]

theorem ae_parameters_of_dimension [MeasurableSpace P] [BorelSpace P]
    (μ : Measure P) [IsAddHaarMeasure μ] (f : P × M → F)
    (hf : ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) ∞ f)
    (hreg : ∀ q, f q = 0 → Surjective (mfderiv (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) f q))
    (k : ℕ) (hd : finrank ℝ P + finrank ℝ E = finrank ℝ F + k) :
    ∀ᵐ p ∂μ, ∀ x : M, f (p, x) = 0 →
      Surjective (mfderiv I 𝓘(ℝ, F) (fun y ↦ f (p, y)) x) := by
  let e : P ≃L[ℝ] (Fin (finrank ℝ P) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_fin_fun ℝ).symm
  let : SecondCountableTopology P := e.toHomeomorph.secondCountableTopology
  let : SecondCountableTopology (P × M) := inferInstance
  let : SecondCountableTopology {q : P × M // f q = 0} :=
    TopologicalSpace.Subtype.secondCountableTopology {q : P × M | f q = 0}
  have hdim : finrank ℝ (P × E) = finrank ℝ F + k := by
    simpa only [finrank_prod] using hd
  obtain ⟨A⟩ := nonempty_regularLevelAtlas isOpen_univ hf.contMDiffOn
    (subset_univ _) hreg k hdim
  let := A.chartedSpace
  let := A.isManifold
  let g : {q : P × M // f q = 0} → P := fun q ↦ q.val.1
  have hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, P) ∞ g :=
    contMDiff_fst.comp A.contMDiff_subtype_val
  apply (Sard.ae_regularValues μ hg).mono
  intro p hp x hx
  let q : {q : P × M // f q = 0} := ⟨(p, x), hx⟩
  have hpq := hp q rfl
  let T : EuclideanSpace ℝ (Fin k) →L[ℝ] P × E :=
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (𝓘(ℝ, P).prod I)
      (Subtype.val : {q : P × M // f q = 0} → P × M) q
  have hproj : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, P) g q =
      (ContinuousLinearMap.fst ℝ P E).comp T := by
    have h := mfderiv_comp q mdifferentiableAt_fst
      (A.contMDiff_subtype_val.mdifferentiable (by simp) q)
    rw [mfderiv_fst] at h
    exact h
  rw [hproj] at hpq
  have hdim' : finrank ℝ (P × E) = finrank ℝ F +
      finrank ℝ (EuclideanSpace ℝ (Fin k)) := by
    simpa only [finrank_euclideanSpace_fin] using hdim
  have hT := A.range_inclusion_eq_kernel q
    (hf.mdifferentiable (by simp) q.val) (hreg q.val q.property) hdim'
  let L : P × E →L[ℝ] F := mfderiv (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) f q.val
  have hT' : T.range = L.ker := hT
  have hv := (surjective_projection_iff L T (hreg q.val q.property) hT').mp hpq
  rw [spatialDerivative_eq f hf p x]
  exact hv

theorem dense_parameters_of_dimension (f : P × M → F)
    (hf : ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) ∞ f)
    (hreg : ∀ q, f q = 0 → Surjective (mfderiv (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) f q))
    (k : ℕ) (hd : finrank ℝ P + finrank ℝ E = finrank ℝ F + k) :
    Dense {p : P | ∀ x : M, f (p, x) = 0 →
      Surjective (mfderiv I 𝓘(ℝ, F) (fun y ↦ f (p, y)) x)} := by
  let : MeasurableSpace P := borel P
  let : BorelSpace P := ⟨rfl⟩
  exact Measure.dense_of_ae (ae_parameters_of_dimension addHaar f hf hreg k hd)

theorem dense_parameters (f : P × M → F)
    (hf : ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) ∞ f)
    (hreg : ∀ q, f q = 0 → Surjective (mfderiv (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) f q)) :
    Dense {p : P | ∀ x : M, f (p, x) = 0 →
      Surjective (mfderiv I 𝓘(ℝ, F) (fun y ↦ f (p, y)) x)} := by
  by_cases hz : ∃ q, f q = 0
  · obtain ⟨q, hq⟩ := hz
    have hd : finrank ℝ F ≤ finrank ℝ P + finrank ℝ E := by
      let L : P × E →L[ℝ] F := mfderiv (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) f q
      have h := LinearMap.finrank_le_finrank_of_surjective
        (f := L.toLinearMap) (hreg q hq)
      simpa only [finrank_prod] using h
    exact dense_parameters_of_dimension f hf hreg
      (finrank ℝ P + finrank ℝ E - finrank ℝ F) (by omega)
  · have he : {p : P | ∀ x : M, f (p, x) = 0 →
        Surjective (mfderiv I 𝓘(ℝ, F) (fun y ↦ f (p, y)) x)} = univ := by
      apply eq_univ_of_forall
      intro p x hx
      exact (hz ⟨(p, x), hx⟩).elim
    rw [he]
    exact dense_univ

theorem ae_parameters [MeasurableSpace P] [BorelSpace P]
    (μ : Measure P) [IsAddHaarMeasure μ] (f : P × M → F)
    (hf : ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) ∞ f)
    (hreg : ∀ q, f q = 0 → Surjective (mfderiv (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) f q)) :
    ∀ᵐ p ∂μ, ∀ x : M, f (p, x) = 0 →
      Surjective (mfderiv I 𝓘(ℝ, F) (fun y ↦ f (p, y)) x) := by
  by_cases hz : ∃ q, f q = 0
  · obtain ⟨q, hq⟩ := hz
    have hd : finrank ℝ F ≤ finrank ℝ P + finrank ℝ E := by
      let L : P × E →L[ℝ] F := mfderiv (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) f q
      have h := LinearMap.finrank_le_finrank_of_surjective
        (f := L.toLinearMap) (hreg q hq)
      simpa only [finrank_prod] using h
    exact ae_parameters_of_dimension μ f hf hreg
      (finrank ℝ P + finrank ℝ E - finrank ℝ F) (by omega)
  · exact Filter.Eventually.of_forall fun p x hx ↦ (hz ⟨(p, x), hx⟩).elim

end NoExoticSixSphere.ParametricRegular
