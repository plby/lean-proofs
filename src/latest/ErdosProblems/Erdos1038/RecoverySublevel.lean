import ErdosProblems.Erdos1038.EmpiricalApproximation

/-!
# Recovery of polynomial sublevel volumes

This file closes the representative-level gap in the recovery argument.
For an empirical root probability, the `L¹` logarithmic potential agrees
almost everywhere with the normalized finite root sum.  Consequently the
negative-set volume used by potential convergence is exactly the original
polynomial `sublevelVolume`.
-/

open scoped ENNReal Real BigOperators Polynomial
open Filter MeasureTheory Set Polynomial Topology

namespace Erdos1038

noncomputable section

/-- Integration against an empirical root probability for a Banach-valued
function is its normalized finite root-multiset sum. -/
theorem integral_empiricalRootProbability_banach
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : Polynomial ℝ) (hf : IsAdmissible f)
    (g : ℝ → E) :
    ∫ r, g r ∂(empiricalRootProbability f hf : Measure ℝ) =
      (f.natDegree : ℝ)⁻¹ • (f.roots.map g).sum := by
  let p : PMF ℝ := empiricalRootPMF f hf
  have hfinite : p.support.Finite := by
    rw [empiricalRootPMF_support f hf]
    exact rootSet_finite f
  have hintOn : IntegrableOn g p.support p.toMeasure :=
    MeasureTheory.IntegrableOn.of_finite hfinite
  have hint : Integrable g p.toMeasure := by
    rw [← p.restrict_toMeasure_support]
    exact hintOn
  change ∫ r, g r ∂p.toMeasure = _
  rw [PMF.integral_eq_tsum p g hint]
  classical
  rw [tsum_eq_sum (s := f.roots.toFinset)]
  · rw [Finset.sum_multiset_map_count, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    dsimp [p, empiricalRootPMF]
    rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    rw [hf.card_roots_eq_natDegree]
    rw [div_eq_mul_inv, mul_comm]
    simp only [mul_smul, Nat.cast_smul_eq_nsmul]
  · intro r hr
    have hr' : r ∉ f.roots := by simpa using! hr
    dsimp [p, empiricalRootPMF]
    rw [Multiset.count_eq_zero.mpr hr']
    simp

/-- A finite empirical potential belongs to `L¹` on every bounded interval. -/
theorem memLp_empiricalPotential_Icc
    (f : Polynomial ℝ) {a b : ℝ} (hab : a ≤ b) :
    MemLp (empiricalPotential f) 1 (volume.restrict (Icc a b)) := by
  rw [memLp_one_iff_integrable]
  have hsum (s : Multiset ℝ) :
      IntegrableOn (fun x ↦ (s.map fun r ↦ logKernel r x).sum)
        (Icc a b) volume := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons r s ih =>
      simpa only [Multiset.map_cons, Multiset.sum_cons] using!
        (integrableOn_logKernel_Icc (t := r) hab).add ih
  have h := (hsum f.roots).const_mul (f.natDegree : ℝ)⁻¹
  simpa only [empiricalPotential, logKernel] using! h

/-- The `L¹` logarithmic potential of an empirical root probability agrees
almost everywhere with the pointwise empirical potential. -/
theorem logarithmicPotentialLp_empirical_ae
    (f : Polynomial ℝ) (hf : IsAdmissible f) {a b : ℝ} (hab : a ≤ b) :
    logarithmicPotentialLp a b hab (empiricalRootProbability f hf)
        (empiricalRootProbability_supported_Icc f hf) =ᵐ[volume.restrict (Icc a b)]
      empiricalPotential f := by
  rw [logarithmicPotentialLp_eq_integral hab (empiricalRootProbability f hf)
      (empiricalRootProbability_supported_Icc f hf),
    integral_empiricalRootProbability_banach]
  have hsum (s : Multiset ℝ) :
      (s.map fun r ↦ logKernelLp a b r hab).sum =ᵐ[volume.restrict (Icc a b)]
        fun x ↦ (s.map fun r ↦ logKernel r x).sum := by
    induction s using Multiset.induction_on with
    | empty =>
      simpa only [Multiset.map_zero, Multiset.sum_zero] using!
        (Lp.coeFn_zero ℝ 1 (volume.restrict (Icc a b)))
    | cons r s ih =>
      filter_upwards [Lp.coeFn_add (logKernelLp a b r hab)
          (s.map fun r ↦ logKernelLp a b r hab).sum,
        logKernelLp_coeFn hab, ih] with x hadd hr hs
      simpa only [Multiset.map_cons, Multiset.sum_cons] using!
        hadd.trans (congrArg₂ (· + ·) hr hs)
  filter_upwards [Lp.coeFn_smul (f.natDegree : ℝ)⁻¹
      (f.roots.map fun r ↦ logKernelLp a b r hab).sum,
    hsum f.roots] with x hsmul hsumx
  rw [hsmul]
  change (f.natDegree : ℝ)⁻¹ *
      (f.roots.map fun r ↦ logKernelLp a b r hab).sum x = empiricalPotential f x
  rw [hsumx]
  rfl

/-- The empirical-potential negative set of an admissible polynomial is
contained in the fixed recovery interval `[-2,2]`. -/
theorem potentialNegativeSet_subset_Icc_negTwo_two
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    potentialNegativeSet f ⊆ Icc (-2 : ℝ) 2 := by
  intro x hx
  by_cases hroot : x ∈ rootSet f
  · have hxroot : x ∈ f.roots := mem_rootSet_iff.mp hroot
    have hI := hf.root_mem_Icc hxroot
    constructor
    · linarith [hI.1]
    · linarith [hI.2]
  · have hsub : x ∈ sublevelSet f :=
      (empiricalPotential_neg_iff_sublevel hf hroot).mp hx
    exact Ioo_subset_Icc_self (hf.sublevelSet_subset_Ioo hsub)

/-- Exact identification of polynomial sublevel volume with the negative
empirical-potential volume on the recovery interval. -/
theorem sublevelVolume_eq_volume_empiricalPotential_negativeOn_negTwo_two
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    sublevelVolume f =
      volume {x | x ∈ Icc (-2 : ℝ) 2 ∧ empiricalPotential f x < 0} := by
  rw [sublevelVolume_eq_volume_potentialNegativeSet hf]
  congr 1
  ext x
  constructor
  · intro hx
    exact ⟨potentialNegativeSet_subset_Icc_negTwo_two hf hx, hx⟩
  · exact fun hx ↦ hx.2

/-- Exact identification in the `L¹` representative used by the weak
potential-convergence theorem. -/
theorem volume_logarithmicPotentialLp_empirical_negativeOn_negTwo_two
    (f : Polynomial ℝ) (hf : IsAdmissible f) :
    volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
        logarithmicPotentialLp (-2) 2 (by norm_num)
          (empiricalRootProbability f hf)
          (empiricalRootProbability_supported_Icc f hf) x < 0} =
      sublevelVolume f := by
  rw [sublevelVolume_eq_volume_empiricalPotential_negativeOn_negTwo_two hf]
  apply measure_congr
  have hae := logarithmicPotentialLp_empirical_ae f hf (a := -2) (b := 2) (by norm_num)
  change ∀ᵐ x ∂volume.restrict (Icc (-2 : ℝ) 2),
    logarithmicPotentialLp (-2) 2 (by norm_num)
      (empiricalRootProbability f hf)
      (empiricalRootProbability_supported_Icc f hf) x =
        empiricalPotential f x at hae
  have hae' := (ae_restrict_iff' measurableSet_Icc).mp hae
  filter_upwards [hae'] with x hx
  change (x ∈ Icc (-2 : ℝ) 2 ∧
      logarithmicPotentialLp (-2) 2 (by norm_num)
        (empiricalRootProbability f hf)
        (empiricalRootProbability_supported_Icc f hf) x < 0) =
    (x ∈ Icc (-2 : ℝ) 2 ∧ empiricalPotential f x < 0)
  by_cases hmem : x ∈ Icc (-2 : ℝ) 2
  · simp only [hmem, true_and]
    exact propext (by rw [hx hmem])
  · simp only [hmem, false_and]

/-- Sublevel volumes of the explicit recovery polynomials converge to the
negative-set volume of the limiting logarithmic potential. -/
theorem tendsto_sublevelVolume_recoveryPolynomial
    (P : ProbabilityMeasure ℝ) (hP : IsRootIntervalSupported P)
    (hzero : volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
      logarithmicPotentialLp (-2) 2 (by norm_num) P hP x = 0} = 0) :
    Tendsto
      (fun n ↦ sublevelVolume (recoveryPolynomial P hP n)) atTop
      (𝓝 (volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
        logarithmicPotentialLp (-2) 2 (by norm_num) P hP x < 0})) := by
  have h := tendsto_volume_negativeSetOn_negTwo_two_recoveryPotential P hP hzero
  convert! h using 1
  funext n
  symm
  simpa only [recoveryEmpiricalRootProbability] using!
    volume_logarithmicPotentialLp_empirical_negativeOn_negTwo_two
      (recoveryPolynomial P hP n) (recoveryPolynomial_admissible P hP n)

/-- Bundled admissible-polynomial form of recovery of the limiting
negative-set volume. -/
theorem exists_admissiblePolynomials_sublevelVolume_tendsto
    (P : ProbabilityMeasure ℝ) (hP : IsRootIntervalSupported P)
    (hzero : volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
      logarithmicPotentialLp (-2) 2 (by norm_num) P hP x = 0} = 0) :
    ∃ f : ℕ → AdmissiblePolynomial,
      Tendsto (fun n ↦ sublevelVolume (f n).1) atTop
        (𝓝 (volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
          logarithmicPotentialLp (-2) 2 (by norm_num) P hP x < 0})) := by
  let f : ℕ → AdmissiblePolynomial := fun n ↦
    ⟨recoveryPolynomial P hP n, recoveryPolynomial_admissible P hP n⟩
  refine ⟨f, ?_⟩
  simpa only [f] using! tendsto_sublevelVolume_recoveryPolynomial P hP hzero

/-- Recovery with the limiting negative-set volume identified with a named
target value. -/
theorem exists_admissiblePolynomials_sublevelVolume_tendsto_of_eq
    (P : ProbabilityMeasure ℝ) (hP : IsRootIntervalSupported P)
    (hzero : volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
      logarithmicPotentialLp (-2) 2 (by norm_num) P hP x = 0} = 0)
    {V : ℝ≥0∞}
    (hvolume : volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
      logarithmicPotentialLp (-2) 2 (by norm_num) P hP x < 0} = V) :
    ∃ f : ℕ → AdmissiblePolynomial,
      Tendsto (fun n ↦ sublevelVolume (f n).1) atTop (𝓝 V) := by
  simpa only [hvolume] using!
    exists_admissiblePolynomials_sublevelVolume_tendsto P hP hzero

end

end Erdos1038
