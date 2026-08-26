import ErdosProblems.Erdos1038.TaoUpperTwoAtomTrial

/-!
# Finite duality for Tao's sharp upper argument

Tao's duality lemma exchanges two logarithmic-potential integrals.  When
the primal measure is the empirical root probability of a polynomial, the
exchange is a finite identity: both sides are double sums over the root
multiset and the atoms of the trial measure.  This avoids any auxiliary
integrability convention at the logarithmic singularity.

The final theorem is the exact empirical contradiction principle: a
nonnegative finite atomic trial whose potential is strictly negative on
`[-1, 1]` must place a positive-weight atom outside the nonnegative set of
the empirical potential.
-/

open scoped BigOperators
open MeasureTheory Set Polynomial

namespace Erdos1038

noncomputable section

/-- The logarithmic potential of a finite atomic measure with locations
`a i` and (not yet necessarily normalized) weights `w i`. -/
def taoFiniteTrialPotential {ι : Type*} [Fintype ι]
    (w a : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, w i * (-Real.log |t - a i|)

/-- The real-valued logarithmic potential of an arbitrary trial measure.
Applications below assume integrability of the finitely many kernels that
are actually paired with empirical roots. -/
def taoTrialMeasurePotential (ν : Measure ℝ) (t : ℝ) : ℝ :=
  -∫ x, Real.log |t - x| ∂ν

private lemma integrable_multiset_kernel_sum
    (ν : Measure ℝ) (s : Multiset ℝ) (g : ℝ → ℝ → ℝ)
    (hg : ∀ r ∈ s, Integrable (g r) ν) :
    Integrable (fun x ↦ (s.map fun r ↦ g r x).sum) ν := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons r s ih =>
      have hr : Integrable (g r) ν := hg r (by simp)
      have hs : ∀ q ∈ s, Integrable (g q) ν := by
        intro q hq
        exact hg q (by simp [hq])
      simpa only [Multiset.map_cons, Multiset.sum_cons] using! hr.add (ih hs)

private lemma integral_multiset_kernel_sum
    (ν : Measure ℝ) (s : Multiset ℝ) (g : ℝ → ℝ → ℝ)
    (hg : ∀ r ∈ s, Integrable (g r) ν) :
    (∫ x, (s.map fun r ↦ g r x).sum ∂ν) =
      (s.map fun r ↦ ∫ x, g r x ∂ν).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons r s ih =>
      have hr : Integrable (g r) ν := hg r (by simp)
      have hs : ∀ q ∈ s, Integrable (g q) ν := by
        intro q hq
        exact hg q (by simp [hq])
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [integral_add hr (integrable_multiset_kernel_sum ν s g hs), ih hs]

/-- Measure-theoretic form of Tao's duality identity, with an empirical
primal measure and an arbitrary trial measure.  The assumptions are only
the kernel-integrability facts needed for the finitely many empirical
roots; in particular they apply to Tao's interval-density trials. -/
theorem tao_empirical_measure_trial_duality
    (f : Polynomial ℝ) (hf : IsAdmissible f) (ν : Measure ℝ)
    (hkernel : ∀ r ∈ f.roots,
      Integrable (fun x ↦ Real.log |x - r|) ν) :
    (∫ x, taoEmpiricalPotential f hf x ∂ν) =
      (f.natDegree : ℝ)⁻¹ *
        (f.roots.map (taoTrialMeasurePotential ν)).sum := by
  have hkernelNeg : ∀ r ∈ f.roots,
      Integrable (fun x ↦ -Real.log |x - r|) ν := by
    intro r hr
    exact (hkernel r hr).neg
  have hsum := integral_multiset_kernel_sum ν f.roots
    (fun r x ↦ -Real.log |x - r|) hkernelNeg
  calc
    (∫ x, taoEmpiricalPotential f hf x ∂ν) =
        ∫ x, (f.natDegree : ℝ)⁻¹ *
          (f.roots.map fun r ↦ -Real.log |x - r|).sum ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [taoEmpiricalPotential_eq_neg_empiricalPotential,
        empiricalPotential, Multiset.sum_map_neg]
      ring
    _ = (f.natDegree : ℝ)⁻¹ *
        (∫ x, (f.roots.map fun r ↦ -Real.log |x - r|).sum ∂ν) := by
      rw [integral_const_mul]
    _ = (f.natDegree : ℝ)⁻¹ *
        (f.roots.map fun r ↦
          ∫ x, -Real.log |x - r| ∂ν).sum := by
      rw [hsum]
    _ = (f.natDegree : ℝ)⁻¹ *
        (f.roots.map (taoTrialMeasurePotential ν)).sum := by
      congr 1
      congr 1
      apply Multiset.map_congr rfl
      intro r _
      unfold taoTrialMeasurePotential
      rw [integral_neg]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      rw [abs_sub_comm]

/-- Strict-negativity consequence of the measure-theoretic duality
identity. -/
theorem tao_empirical_measure_trial_pairing_neg
    (f : Polynomial ℝ) (hf : IsAdmissible f) (ν : Measure ℝ)
    (hkernel : ∀ r ∈ f.roots,
      Integrable (fun x ↦ Real.log |x - r|) ν)
    (htrial : ∀ t ∈ Icc (-1 : ℝ) 1,
      taoTrialMeasurePotential ν t < 0) :
    (∫ x, taoEmpiricalPotential f hf x ∂ν) < 0 := by
  rw [tao_empirical_measure_trial_duality f hf ν hkernel]
  have hroots : f.roots ≠ 0 := roots_ne_zero hf
  have hsum :
      (f.roots.map (taoTrialMeasurePotential ν)).sum < 0 := by
    have hlt := Multiset.sum_lt_sum_of_nonempty
      (s := f.roots) (f := taoTrialMeasurePotential ν)
      (g := fun _ ↦ (0 : ℝ)) hroots
      (fun r hr ↦ htrial r (hf.root_mem_Icc hr))
    simpa using! hlt
  have hdegree : 0 < (f.natDegree : ℝ) := by
    exact_mod_cast hf.monic.natDegree_pos.mpr hf.ne_one
  exact mul_neg_of_pos_of_neg (inv_pos.mpr hdegree) hsum

/-- **Tao's measure duality lemma (empirical primal form).**  A trial
measure whose potential is strictly negative on the root interval cannot
be concentrated almost everywhere on the nonnegative empirical-potential
set.  This version applies directly to the interval-density trials in
Cases 2 and 3. -/
theorem not_taoEmpiricalPotential_nonneg_ae_of_measure_trial
    (f : Polynomial ℝ) (hf : IsAdmissible f) (ν : Measure ℝ)
    (hkernel : ∀ r ∈ f.roots,
      Integrable (fun x ↦ Real.log |x - r|) ν)
    (htrial : ∀ t ∈ Icc (-1 : ℝ) 1,
      taoTrialMeasurePotential ν t < 0) :
    ¬ ∀ᵐ x ∂ν, 0 ≤ taoEmpiricalPotential f hf x := by
  have hpair := tao_empirical_measure_trial_pairing_neg
    f hf ν hkernel htrial
  intro hnonneg
  exact (not_lt_of_ge (integral_nonneg_of_ae hnonneg)) hpair

private lemma multiset_sum_finset_sum_comm
    {ι α : Type*} [Fintype ι] [AddCommMonoid α]
    (s : Multiset ℝ) (F : ι → ℝ → α) :
    (s.map fun r ↦ ∑ i, F i r).sum =
      ∑ i, (s.map fun r ↦ F i r).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons r s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, ih,
        Finset.sum_add_distrib]

/-- Finite Fubini symmetry for an empirical root measure and an atomic
trial measure.  This is Tao's Lemma 2.1 identity specialized only on the
primal side; the trial weights may be arbitrary real numbers. -/
theorem tao_empirical_finite_trial_duality
    {ι : Type*} [Fintype ι] (f : Polynomial ℝ)
    (hf : IsAdmissible f) (w a : ι → ℝ) :
    (∑ i, w i * taoEmpiricalPotential f hf (a i)) =
      (f.natDegree : ℝ)⁻¹ *
        (f.roots.map (taoFiniteTrialPotential w a)).sum := by
  simp_rw [taoEmpiricalPotential_eq_neg_empiricalPotential,
    empiricalPotential]
  have hcomm := multiset_sum_finset_sum_comm f.roots
    (fun i r ↦ w i * (-Real.log |r - a i|))
  calc
    ∑ i, w i *
        (-((f.natDegree : ℝ)⁻¹ *
          (f.roots.map fun r ↦ Real.log |a i - r|).sum)) =
        (f.natDegree : ℝ)⁻¹ *
          ∑ i, w i *
            (-(f.roots.map fun r ↦ Real.log |a i - r|).sum) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (f.natDegree : ℝ)⁻¹ *
          ∑ i, (f.roots.map fun r ↦
            w i * (-Real.log |r - a i|)).sum := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Multiset.sum_map_mul_left]
      congr 1
      calc
        -(f.roots.map fun r ↦ Real.log |a i - r|).sum =
            (f.roots.map fun r ↦ -Real.log |a i - r|).sum := by
          rw [Multiset.sum_map_neg]
        _ = (f.roots.map fun r ↦ -Real.log |r - a i|).sum := by
          congr 1
          apply Multiset.map_congr rfl
          intro r _
          rw [abs_sub_comm]
    _ = (f.natDegree : ℝ)⁻¹ *
        (f.roots.map (taoFiniteTrialPotential w a)).sum := by
      rw [← hcomm]
      rfl

/-- A trial potential strictly negative on the permitted root interval has
strictly negative pairing with every admissible empirical root measure. -/
theorem tao_empirical_finite_trial_pairing_neg
    {ι : Type*} [Fintype ι] (f : Polynomial ℝ)
    (hf : IsAdmissible f) (w a : ι → ℝ)
    (htrial : ∀ t ∈ Icc (-1 : ℝ) 1,
      taoFiniteTrialPotential w a t < 0) :
    (∑ i, w i * taoEmpiricalPotential f hf (a i)) < 0 := by
  rw [tao_empirical_finite_trial_duality f hf w a]
  have hroots : f.roots ≠ 0 := roots_ne_zero hf
  have hsum :
      (f.roots.map (taoFiniteTrialPotential w a)).sum < 0 := by
    have hlt := Multiset.sum_lt_sum_of_nonempty
      (s := f.roots) (f := taoFiniteTrialPotential w a)
      (g := fun _ ↦ (0 : ℝ)) hroots
      (fun r hr ↦ htrial r (hf.root_mem_Icc hr))
    simpa using! hlt
  have hdegree : 0 < (f.natDegree : ℝ) := by
    exact_mod_cast hf.monic.natDegree_pos.mpr hf.ne_one
  exact mul_neg_of_pos_of_neg (inv_pos.mpr hdegree) hsum

/-- **Tao's empirical duality lemma.**  If nonnegative atomic weights give
a trial potential strictly negative throughout `[-1,1]`, then at least one
positive-weight trial atom has strictly negative empirical potential.  In
particular, the nonnegative empirical-potential set cannot contain the
support of the trial measure. -/
theorem exists_positive_trial_atom_taoEmpiricalPotential_neg
    {ι : Type*} [Fintype ι] (f : Polynomial ℝ)
    (hf : IsAdmissible f) (w a : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (htrial : ∀ t ∈ Icc (-1 : ℝ) 1,
      taoFiniteTrialPotential w a t < 0) :
    ∃ i, 0 < w i ∧ taoEmpiricalPotential f hf (a i) < 0 := by
  have hpair := tao_empirical_finite_trial_pairing_neg f hf w a htrial
  have hex : ∃ i, w i * taoEmpiricalPotential f hf (a i) < 0 := by
    by_cases h : ∃ i, w i * taoEmpiricalPotential f hf (a i) < 0
    · exact h
    · push_neg at h
      exact False.elim
        ((not_lt_of_ge (Finset.sum_nonneg fun i _ ↦ h i)) hpair)
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, ?_, ?_⟩
  · rcases (mul_neg_iff.mp hi) with hcase | hcase
    · exact hcase.1
    · exact False.elim ((not_lt_of_ge (hw i)) hcase.1)
  · rcases (mul_neg_iff.mp hi) with hcase | hcase
    · exact hcase.2
    · exact False.elim ((not_lt_of_ge (hw i)) hcase.1)

/-- Set-theoretic form of the empirical duality lemma. -/
theorem finite_trial_support_not_subset_taoEmpiricalPotential_nonneg
    {ι : Type*} [Fintype ι] (f : Polynomial ℝ)
    (hf : IsAdmissible f) (w a : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (htrial : ∀ t ∈ Icc (-1 : ℝ) 1,
      taoFiniteTrialPotential w a t < 0) :
    ¬ {x | ∃ i, 0 < w i ∧ a i = x} ⊆
      {x | 0 ≤ taoEmpiricalPotential f hf x} := by
  obtain ⟨i, hwi, hi⟩ :=
    exists_positive_trial_atom_taoEmpiricalPotential_neg
      f hf w a hw htrial
  intro hsubset
  exact (not_le_of_gt hi) (hsubset ⟨i, hwi, rfl⟩)

/-- Translation covariance of a finite logarithmic trial potential. -/
theorem taoFiniteTrialPotential_locations_sub
    {ι : Type*} [Fintype ι] (w a : ι → ℝ) (c r : ℝ) :
    taoFiniteTrialPotential w (fun i ↦ a i - c) r =
      taoFiniteTrialPotential w a (r + c) := by
  unfold taoFiniteTrialPotential
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  congr 1
  ring_nf

/-- Translated-support form of Tao's empirical duality lemma.  This is the
form used in the upper proof after the root interval has been moved from
`[-1,1]` to `[c-1,c+1]`: trial atoms at `a i` become the points `a i-c` in
the original polynomial coordinate. -/
theorem exists_translated_trial_atom_taoEmpiricalPotential_neg
    {ι : Type*} [Fintype ι] (f : Polynomial ℝ)
    (hf : IsAdmissible f) (w a : ι → ℝ) (c : ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (htrial : ∀ t ∈ Icc (c - 1) (c + 1),
      taoFiniteTrialPotential w a t < 0) :
    ∃ i, 0 < w i ∧
      taoEmpiricalPotential f hf (a i - c) < 0 := by
  have hshifted : ∀ r ∈ Icc (-1 : ℝ) 1,
      taoFiniteTrialPotential w (fun i ↦ a i - c) r < 0 := by
    intro r hr
    rw [taoFiniteTrialPotential_locations_sub]
    apply htrial (r + c)
    constructor <;> linarith [hr.1, hr.2]
  exact exists_positive_trial_atom_taoEmpiricalPotential_neg
    f hf w (fun i ↦ a i - c) hw hshifted

/-- Weights of Tao's first trial measure `δ₀ + C δ_M`. -/
def taoTwoAtomWeights (C : ℝ) : Fin 2 → ℝ := ![1, C]

/-- Locations of Tao's first trial measure `δ₀ + C δ_M`. -/
def taoTwoAtomLocations (M : ℝ) : Fin 2 → ℝ := ![0, M]

/-- The generic finite-trial potential specializes exactly to the scalar
two-atom expression already used by the case-one certificate. -/
theorem taoFiniteTrialPotential_twoAtom
    {M C t : ℝ} :
    taoFiniteTrialPotential (taoTwoAtomWeights C)
      (taoTwoAtomLocations M) t = taoTwoAtomTrialPotential M C t := by
  have hlog : Real.log (t - M) = Real.log (M - t) := by
    rw [show t - M = -(M - t) by ring, Real.log_neg_eq_log]
  simp [taoFiniteTrialPotential, taoTwoAtomWeights, taoTwoAtomLocations,
    Fin.sum_univ_two, hlog]
  unfold taoTwoAtomTrialPotential
  ring_nf

/-- Direct duality output for Tao's two-atom certificate on a translated
root interval.  One of the two pushed-back trial atoms lies outside the
nonnegative empirical-potential set. -/
theorem exists_twoAtom_taoEmpiricalPotential_neg_of_translated_trial
    (f : Polynomial ℝ) (hf : IsAdmissible f) {M C c : ℝ}
    (hC : 0 ≤ C)
    (htrial : ∀ t ∈ Icc (c - 1) (c + 1),
      taoTwoAtomTrialPotential M C t < 0) :
    ∃ x, (x = -c ∨ x = M - c) ∧
      taoEmpiricalPotential f hf x < 0 := by
  have hw : ∀ i, 0 ≤ taoTwoAtomWeights C i := by
    intro i
    fin_cases i <;> simp [taoTwoAtomWeights, hC]
  have hfinite : ∀ t ∈ Icc (c - 1) (c + 1),
      taoFiniteTrialPotential (taoTwoAtomWeights C)
        (taoTwoAtomLocations M) t < 0 := by
    intro t ht
    rw [taoFiniteTrialPotential_twoAtom]
    exact htrial t ht
  obtain ⟨i, hwi, hi⟩ :=
    exists_translated_trial_atom_taoEmpiricalPotential_neg
      f hf (taoTwoAtomWeights C) (taoTwoAtomLocations M) c hw hfinite
  refine ⟨taoTwoAtomLocations M i - c, ?_, hi⟩
  fin_cases i
  · left
    simp [taoTwoAtomLocations]
  · right
    simp [taoTwoAtomLocations]

/-- The existing checked analytic reduction for Tao's first parameter range
now produces the actual empirical-duality conclusion. -/
theorem exists_tao_case_one_point_taoEmpiricalPotential_neg
    (f : Polynomial ℝ) (hf : IsAdmissible f) {t0 : ℝ}
    (ht0Lower : Real.sqrt 2 < t0)
    (ht0Upper : t0 < taoCaseOneCeiling)
    (hratio :
      -Real.log (t0 - 1) /
          Real.log (taoUpperEdge - (t0 - 1)) <
        Real.log (t0 + 1) /
          (-Real.log (taoUpperEdge - (t0 + 1)))) :
    ∃ x, (x = -t0 ∨ x = taoUpperEdge - t0) ∧
      taoEmpiricalPotential f hf x < 0 := by
  obtain ⟨C, hC, htrial⟩ :=
    exists_tao_case_one_twoAtomTrial ht0Lower ht0Upper hratio
  exact exists_twoAtom_taoEmpiricalPotential_neg_of_translated_trial
    f hf hC htrial

/-- The pointwise analytic step in Tao's expansive-pushforward argument.
If distances from a generalized inverse point `s₀` do not decrease after
applying `φ`, then the pushed trial potential at `t` is no larger than the
original trial potential at `s₀`.  The noncollision hypothesis records the
usual extended-real logarithmic singularity explicitly, since `Real.log 0`
is defined to be zero in Mathlib. -/
theorem taoFiniteTrialPotential_comp_le
    {ι : Type*} [Fintype ι] (w a : ι → ℝ)
    (φ : ℝ → ℝ) {s₀ t : ℝ}
    (hw : ∀ i, 0 ≤ w i)
    (hdistance : ∀ i, 0 < w i →
      0 < |s₀ - a i| ∧ |s₀ - a i| ≤ |t - φ (a i)|) :
    taoFiniteTrialPotential w (φ ∘ a) t ≤
      taoFiniteTrialPotential w a s₀ := by
  unfold taoFiniteTrialPotential
  apply Finset.sum_le_sum
  intro i _
  by_cases hwi : w i = 0
  · simp [hwi]
  · have hwiPos : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hwi)
    have hdist := hdistance i hwiPos
    have hlog :
        Real.log |s₀ - a i| ≤ Real.log |t - φ (a i)| :=
      Real.log_le_log hdist.1 hdist.2
    have hneg :
        -Real.log |t - φ (a i)| ≤ -Real.log |s₀ - a i| :=
      neg_le_neg hlog
    simpa only [Function.comp_apply] using!
      mul_le_mul_of_nonneg_left hneg (hw i)

/-- Empirical form of Tao's expansive-pushforward contradiction criterion
(Lemma 2.2).  The hypothesis `hseparator` is exactly the generalized-inverse
distance estimate supplied by an expansive monotone rearrangement. -/
theorem exists_pushed_trial_atom_taoEmpiricalPotential_neg
    {ι : Type*} [Fintype ι] (f : Polynomial ℝ)
    (hf : IsAdmissible f) (w a : ι → ℝ) (φ : ℝ → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (htrial : ∀ s ∈ Icc (-1 : ℝ) 1,
      taoFiniteTrialPotential w a s < 0)
    (hseparator : ∀ t ∈ Icc (-1 : ℝ) 1,
      ∃ s₀ ∈ Icc (-1 : ℝ) 1, ∀ i, 0 < w i →
        0 < |s₀ - a i| ∧ |s₀ - a i| ≤ |t - φ (a i)|) :
    ∃ i, 0 < w i ∧
      taoEmpiricalPotential f hf (φ (a i)) < 0 := by
  have hpushed : ∀ t ∈ Icc (-1 : ℝ) 1,
      taoFiniteTrialPotential w (φ ∘ a) t < 0 := by
    intro t ht
    obtain ⟨s₀, hs₀, hdistance⟩ := hseparator t ht
    exact (taoFiniteTrialPotential_comp_le w a φ hw hdistance).trans_lt
      (htrial s₀ hs₀)
  simpa only [Function.comp_apply] using!
    exists_positive_trial_atom_taoEmpiricalPotential_neg
      f hf w (φ ∘ a) hw hpushed

/-- Contradiction form: an expansive pushforward satisfying the separator
estimate cannot put every positive-weight atom in the nonnegative empirical
potential set. -/
theorem not_all_pushed_trial_atoms_taoEmpiricalPotential_nonneg
    {ι : Type*} [Fintype ι] (f : Polynomial ℝ)
    (hf : IsAdmissible f) (w a : ι → ℝ) (φ : ℝ → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (htrial : ∀ s ∈ Icc (-1 : ℝ) 1,
      taoFiniteTrialPotential w a s < 0)
    (hseparator : ∀ t ∈ Icc (-1 : ℝ) 1,
      ∃ s₀ ∈ Icc (-1 : ℝ) 1, ∀ i, 0 < w i →
        0 < |s₀ - a i| ∧ |s₀ - a i| ≤ |t - φ (a i)|) :
    ¬ ∀ i, 0 < w i →
      0 ≤ taoEmpiricalPotential f hf (φ (a i)) := by
  obtain ⟨i, hwi, hi⟩ :=
    exists_pushed_trial_atom_taoEmpiricalPotential_neg
      f hf w a φ hw htrial hseparator
  intro hall
  exact (not_le_of_gt hi) (hall i hwi)

end

end Erdos1038
