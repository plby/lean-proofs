import ErdosProblems.Erdos1038.EmpiricalMeasure
import ErdosProblems.Erdos1038.PotentialSublevelConvergence
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Equal-weight empirical approximation

Probability measures on the permitted root interval are weak limits of
uniform measures on nonempty finite root multisets.  Such multisets are also
converted into monic admissible polynomials whose empirical root measures are
the prescribed uniform measures.
-/

open scoped ENNReal Real BigOperators Polynomial BoundedContinuousFunction
open Filter MeasureTheory Set Polynomial Topology

namespace Erdos1038

noncomputable section

section UniformAverages

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The arithmetic mean of a finite multiset in a real vector space.  It is
only used below for nonempty multisets. -/
def multisetAverage (s : Multiset E) : E :=
  (s.card : ℝ)⁻¹ • s.sum

/-- Points which are equal-weight averages of nonempty finite multisets
whose entries belong to `S`. -/
def uniformAverageSet (S : Set E) : Set E :=
  {x | ∃ s : Multiset E, s ≠ 0 ∧ (∀ y ∈ s, y ∈ S) ∧ multisetAverage s = x}

theorem mem_uniformAverageSet_singleton {S : Set E} {x : E} (hx : x ∈ S) :
    x ∈ uniformAverageSet S := by
  refine ⟨{x}, by simp, ?_, by simp [multisetAverage]⟩
  intro y hy
  rw [Multiset.mem_singleton.mp hy]
  exact hx

/-- A rational convex combination of two finite uniform averages is again
a finite uniform average.  Repeating the two multisets clears both their
cardinalities and the denominator of the rational coefficient. -/
theorem mem_uniformAverageSet_rational_segment {S : Set E}
    {x y : E} (hx : x ∈ uniformAverageSet S) (hy : y ∈ uniformAverageSet S)
    {k n : ℕ} (hkn : k ≤ n) (hn : 0 < n) :
    ((k : ℝ) / n) • x + (((n - k : ℕ) : ℝ) / n) • y ∈
      uniformAverageSet S := by
  obtain ⟨s, hs0, hsS, rfl⟩ := hx
  obtain ⟨t, ht0, htS, rfl⟩ := hy
  let u : Multiset E := (k * t.card) • s + ((n - k) * s.card) • t
  have hscard : 0 < s.card := Multiset.card_pos.mpr hs0
  have htcard : 0 < t.card := Multiset.card_pos.mpr ht0
  have hucard : u.card = n * s.card * t.card := by
    simp only [u, Multiset.card_add, Multiset.card_nsmul]
    calc
      k * t.card * s.card + (n - k) * s.card * t.card =
          (k + (n - k)) * s.card * t.card := by ring
      _ = n * s.card * t.card := by rw [Nat.add_sub_of_le hkn]
  have hu0 : u ≠ 0 := by
    apply Multiset.card_pos.mp
    rw [hucard]
    positivity
  refine ⟨u, hu0, ?_, ?_⟩
  · intro z hz
    simp only [u, Multiset.mem_add, Multiset.mem_nsmul] at hz
    rcases hz with ⟨_, hzs⟩ | ⟨_, hzt⟩
    · exact hsS z hzs
    · exact htS z hzt
  · simp only [multisetAverage, u, Multiset.sum_add, Multiset.sum_nsmul, hucard]
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hscard0 : (s.card : ℝ) ≠ 0 := by positivity
    have htcard0 : (t.card : ℝ) ≠ 0 := by positivity
    simp only [Nat.cast_mul, Nat.cast_sub hkn, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_add, smul_smul]
    have hcoef_s :
        ((n : ℝ) * s.card * t.card)⁻¹ * ((k : ℝ) * t.card) =
          ((k : ℝ) / n) * (s.card : ℝ)⁻¹ := by
      field_simp
    have hcoef_t :
        ((n : ℝ) * s.card * t.card)⁻¹ * (((n : ℝ) - k) * s.card) =
          (((n : ℝ) - k) / n) * (t.card : ℝ)⁻¹ := by
      field_simp
    rw [hcoef_s, hcoef_t]

/-- The closure of finite equal-weight averages is convex. -/
theorem convex_closure_uniformAverageSet (S : Set E) :
    Convex ℝ (closure (uniformAverageSet S)) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  obtain ⟨xs, hxs, hxlim⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨ys, hys, hylim⟩ := mem_closure_iff_seq_limit.mp hy
  have ha_one : a ≤ 1 := by linarith
  let q : ℕ → ℝ := fun m ↦
    (⌊a * ((m + 1 : ℕ) : ℝ)⌋₊ : ℝ) / ((m + 1 : ℕ) : ℝ)
  let r : ℕ → ℝ := fun m ↦
    (((m + 1 : ℕ) - ⌊a * ((m + 1 : ℕ) : ℝ)⌋₊ : ℕ) : ℝ) /
      ((m + 1 : ℕ) : ℝ)
  have hcast : Tendsto (fun m : ℕ ↦ ((m + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hq : Tendsto q atTop (𝓝 a) := by
    exact (tendsto_nat_floor_mul_div_atTop ha).comp hcast
  have hfloor (m : ℕ) :
      ⌊a * ((m + 1 : ℕ) : ℝ)⌋₊ ≤ m + 1 := by
    apply Nat.floor_le_of_le
    have hm : 0 ≤ ((m + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have hr : Tendsto r atTop (𝓝 b) := by
    have hsub : Tendsto (fun m ↦ (1 : ℝ) - q m) atTop (𝓝 (1 - a)) :=
      tendsto_const_nhds.sub hq
    have hb_eq : 1 - a = b := by linarith
    rw [hb_eq] at hsub
    convert! hsub using 1
    funext m
    simp only [r, q, Nat.cast_sub (hfloor m)]
    have hm0 : (((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp
  let z : ℕ → E := fun m ↦ q m • xs m + r m • ys m
  have hzmem (m : ℕ) : z m ∈ uniformAverageSet S := by
    exact mem_uniformAverageSet_rational_segment (hxs m) (hys m)
      (hfloor m) (Nat.succ_pos m)
  have hzlim : Tendsto z atTop (𝓝 (a • x + b • y)) :=
    (hq.smul hxlim).add (hr.smul hylim)
  exact mem_closure_iff_seq_limit.mpr ⟨z, hzmem, hzlim⟩

/-- The closed convex hull of a set is already obtained by closing its
finite equal-weight averages. -/
theorem closedConvexHull_subset_closure_uniformAverageSet (S : Set E) :
    closedConvexHull ℝ S ⊆ closure (uniformAverageSet S) := by
  apply closedConvexHull_min
  · intro x hx
    exact subset_closure (mem_uniformAverageSet_singleton hx)
  · exact convex_closure_uniformAverageSet S
  · exact isClosed_closure

end UniformAverages

/-! ## Uniform measures carried by root multisets -/

/-- The equal-weight probability measure carried by a nonempty multiset. -/
def uniformMultisetProbability {α : Type*} [MeasurableSpace α]
    (s : Multiset α) (hs : s ≠ 0) : ProbabilityMeasure α :=
  ⟨(PMF.ofMultiset s hs).toMeasure, inferInstance⟩

/-- Integration against a uniform multiset measure is the corresponding
finite arithmetic mean. -/
theorem integral_uniformMultisetProbability {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (s : Multiset α) (hs : s ≠ 0)
    (g : α → ℝ) :
    ∫ x, g x ∂(uniformMultisetProbability s hs : Measure α) =
      (s.map g).sum / (s.card : ℝ) := by
  classical
  let p : PMF α := PMF.ofMultiset s hs
  have hfinite : p.support.Finite := by
    rw [PMF.support_ofMultiset]
    exact s.toFinset.finite_toSet
  have hintOn : IntegrableOn g p.support p.toMeasure :=
    IntegrableOn.of_finite hfinite
  have hint : Integrable g p.toMeasure := by
    rw [← p.restrict_toMeasure_support]
    exact hintOn
  change ∫ x, g x ∂p.toMeasure = _
  rw [PMF.integral_eq_tsum p g hint]
  rw [tsum_eq_sum (s := s.toFinset)]
  · rw [Finset.sum_multiset_map_count, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x hx
    dsimp [p]
    rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    simp only [nsmul_eq_mul]
    ring
  · intro x hx
    have hx' : x ∉ s := by simpa using! hx
    dsimp [p]
    rw [Multiset.count_eq_zero.mpr hx']
    simp

theorem integral_uniformMultisetProbability_eq_multisetAverage
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (s : Multiset α) (hs : s ≠ 0) (g : α → ℝ) :
    ∫ x, g x ∂(uniformMultisetProbability s hs : Measure α) =
      multisetAverage (s.map g) := by
  rw [integral_uniformMultisetProbability]
  simp only [multisetAverage, Multiset.card_map, smul_eq_mul, inv_mul_eq_div]

/-! ## Simultaneous approximation of moments -/

/-- The vector of the first `d` monomials at a permitted root. -/
def momentVector (d : ℕ) (x : RootInterval) : Fin d → ℝ :=
  fun k ↦ (x.1) ^ (k : ℕ)

theorem continuous_momentVector (d : ℕ) : Continuous (momentVector d) := by
  apply continuous_pi
  intro k
  exact continuous_subtype_val.pow k

abbrev MomentSpace (d : ℕ) := Fin d → ℝ

/-- The moment vector bundled as a bounded continuous function on the
compact root interval. -/
def momentVectorBCF (d : ℕ) : RootInterval →ᵇ MomentSpace d :=
  BoundedContinuousFunction.mkOfCompact ⟨momentVector d, continuous_momentVector d⟩

theorem momentVectorBCF_apply (d : ℕ) (x : RootInterval) :
    momentVectorBCF d x = momentVector d x :=
  rfl

/-- A multiset all of whose entries lie in the range of a map can be lifted
to a multiset in its domain. -/
theorem exists_multiset_map_eq_of_forall_mem_range
    {X Y : Type*} (F : X → Y) (t : Multiset Y)
    (ht : ∀ y ∈ t, y ∈ range F) :
    ∃ s : Multiset X, s.map F = t := by
  induction t using Multiset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @cons y t ih =>
      obtain ⟨x, hx⟩ := ht y (by simp)
      obtain ⟨s, hs⟩ := ih (fun z hz ↦ ht z (by simp [hz]))
      refine ⟨x ::ₘ s, ?_⟩
      simp only [Multiset.map_cons, hx, hs]

/-- The vector of the first `d` moments of a probability measure is in the
closure of equal-weight averages of pointwise moment vectors. -/
theorem integral_momentVector_mem_closure_uniformAverageSet
    (Q : ProbabilityMeasure RootInterval) (d : ℕ) :
    (∫ x, momentVector d x ∂(Q : Measure RootInterval)) ∈
      closure (uniformAverageSet (range (momentVector d))) := by
  apply closedConvexHull_subset_closure_uniformAverageSet
  apply convex_closedConvexHull.integral_mem isClosed_closedConvexHull
  · exact Eventually.of_forall fun x ↦ subset_closedConvexHull (mem_range_self x)
  · simpa only [momentVectorBCF_apply] using! (momentVectorBCF d).integrable (Q : Measure RootInterval)

/-- For every tolerance and every finite list of moments, there is one
nonempty equal-weight root multiset approximating all those moments at once. -/
theorem exists_rootMultiset_moment_approx
    (Q : ProbabilityMeasure RootInterval) (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Multiset RootInterval, s ≠ 0 ∧
      ‖multisetAverage (s.map (momentVector d)) -
        ∫ x, momentVector d x ∂(Q : Measure RootInterval)‖ < ε := by
  have hclosure := integral_momentVector_mem_closure_uniformAverageSet Q d
  obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.mp hclosure ε hε
  obtain ⟨t, ht0, htRange, havg⟩ := hz
  obtain ⟨s, hsmap⟩ := exists_multiset_map_eq_of_forall_mem_range
    (momentVector d) t htRange
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs, Multiset.map_zero] at hsmap
    exact ht0 hsmap.symm
  refine ⟨s, hs0, ?_⟩
  have havg' : multisetAverage (s.map (momentVector d)) = z := by
    rw [hsmap]
    exact havg
  rw [havg']
  simpa only [dist_eq_norm, norm_sub_rev] using! hdist

/-- A canonical choice of a root multiset approximating the first `n + 1`
moments within `1 / (n + 1)`. -/
def approximatingRootMultiset (Q : ProbabilityMeasure RootInterval) (n : ℕ) :
    Multiset RootInterval :=
  Classical.choose (exists_rootMultiset_moment_approx Q (n + 1)
    (show 0 < (1 : ℝ) / (n + 1) by positivity))

theorem approximatingRootMultiset_ne_zero
    (Q : ProbabilityMeasure RootInterval) (n : ℕ) :
    approximatingRootMultiset Q n ≠ 0 :=
  (Classical.choose_spec (exists_rootMultiset_moment_approx Q (n + 1)
    (show 0 < (1 : ℝ) / (n + 1) by positivity))).1

theorem approximatingRootMultiset_moment_error
    (Q : ProbabilityMeasure RootInterval) (n : ℕ) :
    ‖multisetAverage ((approximatingRootMultiset Q n).map (momentVector (n + 1))) -
      ∫ x, momentVector (n + 1) x ∂(Q : Measure RootInterval)‖ <
        (1 : ℝ) / (n + 1) :=
  (Classical.choose_spec (exists_rootMultiset_moment_approx Q (n + 1)
    (show 0 < (1 : ℝ) / (n + 1) by positivity))).2

theorem multisetAverage_map_apply {ι : Type*} [Fintype ι]
    (s : Multiset (ι → ℝ)) (i : ι) :
    multisetAverage (s.map fun f ↦ f i) = multisetAverage s i := by
  have hsum : (s.map fun f ↦ f i).sum = s.sum i := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons f s ih => simp [ih]
  simp only [multisetAverage, Multiset.card_map, smul_eq_mul, Pi.smul_apply]
  rw [hsum]

/-- Every fixed monomial moment of the chosen empirical multisets converges
to the corresponding moment of the target measure. -/
theorem tendsto_multisetAverage_pow_approximatingRootMultiset
    (Q : ProbabilityMeasure RootInterval) (k : ℕ) :
    Tendsto
      (fun n ↦ multisetAverage
        ((approximatingRootMultiset Q n).map fun x ↦ (x.1) ^ k))
      atTop (𝓝 (∫ x, (x.1) ^ k ∂(Q : Measure RootInterval))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hinv : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have heps : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / (n + 1) < ε :=
    hinv.eventually (Iio_mem_nhds hε)
  rw [eventually_atTop] at heps
  obtain ⟨N, hN⟩ := heps
  refine ⟨max N k, ?_⟩
  intro n hn
  have hnε : (1 : ℝ) / (n + 1) < ε := hN n ((le_max_left N k).trans hn)
  have hkn : k ≤ n := (le_max_right N k).trans hn
  let i : Fin (n + 1) := ⟨k, Nat.lt_succ_of_le hkn⟩
  have hint :
      (∫ x, momentVector (n + 1) x ∂(Q : Measure RootInterval)) i =
        ∫ x, (x.1) ^ k ∂(Q : Measure RootInterval) := by
    have hvecint : Integrable (momentVector (n + 1)) (Q : Measure RootInterval) := by
      simpa only [momentVectorBCF_apply] using!
        (momentVectorBCF (n + 1)).integrable (Q : Measure RootInterval)
    simpa only [momentVector, i] using!
      ((ContinuousLinearMap.proj i : (Fin (n + 1) → ℝ) →L[ℝ] ℝ).integral_comp_comm
        hvecint).symm
  have havg :
      multisetAverage
          ((approximatingRootMultiset Q n).map fun x ↦ (x.1) ^ k) =
        multisetAverage
          ((approximatingRootMultiset Q n).map (momentVector (n + 1))) i := by
    simpa only [Multiset.map_map, Function.comp_apply, momentVector, i] using!
      (multisetAverage_map_apply
        ((approximatingRootMultiset Q n).map (momentVector (n + 1))) i)
  rw [dist_eq_norm, havg, ← hint, ← Pi.sub_apply]
  exact (norm_le_pi_norm _ i).trans_lt
    ((approximatingRootMultiset_moment_error Q n).trans hnε)

/-- The sequence of equal-weight probability measures carried by the chosen
root multisets. -/
def empiricalApproximation (Q : ProbabilityMeasure RootInterval) (n : ℕ) :
    ProbabilityMeasure RootInterval :=
  uniformMultisetProbability (approximatingRootMultiset Q n)
    (approximatingRootMultiset_ne_zero Q n)

theorem integral_empiricalApproximation
    (Q : ProbabilityMeasure RootInterval) (n : ℕ) (g : RootInterval → ℝ) :
    ∫ x, g x ∂(empiricalApproximation Q n : Measure RootInterval) =
      multisetAverage ((approximatingRootMultiset Q n).map g) := by
  exact integral_uniformMultisetProbability_eq_multisetAverage _ _ _

theorem tendsto_integral_pow_empiricalApproximation
    (Q : ProbabilityMeasure RootInterval) (k : ℕ) :
    Tendsto
      (fun n ↦ ∫ x, (x.1) ^ k ∂(empiricalApproximation Q n : Measure RootInterval))
      atTop (𝓝 (∫ x, (x.1) ^ k ∂(Q : Measure RootInterval))) := by
  simpa only [integral_empiricalApproximation] using!
    tendsto_multisetAverage_pow_approximatingRootMultiset Q k

theorem integral_polynomial_eval_rootInterval
    (R : ProbabilityMeasure RootInterval) (p : Polynomial ℝ) :
    ∫ x, p.eval x.1 ∂(R : Measure RootInterval) =
      ∑ k ∈ p.support, p.coeff k *
        ∫ x, (x.1) ^ k ∂(R : Measure RootInterval) := by
  classical
  have hfun : (fun x : RootInterval ↦ p.eval x.1) =
      fun x : RootInterval ↦ ∑ k ∈ p.support, p.coeff k * (x.1) ^ k := by
    funext x
    rw [p.eval_eq_sum, Polynomial.sum_def]
  rw [hfun, integral_finsetSum]
  · simp only [integral_const_mul]
  · intro k hk
    let f : RootInterval →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact
        ⟨fun x ↦ p.coeff k * (x.1) ^ k, by fun_prop⟩
    exact f.integrable (R : Measure RootInterval)

/-- Integrals of every polynomial converge along the empirical
approximations. -/
theorem tendsto_integral_polynomial_empiricalApproximation
    (Q : ProbabilityMeasure RootInterval) (p : Polynomial ℝ) :
    Tendsto
      (fun n ↦ ∫ x, p.eval x.1 ∂(empiricalApproximation Q n : Measure RootInterval))
      atTop (𝓝 (∫ x, p.eval x.1 ∂(Q : Measure RootInterval))) := by
  simp_rw [integral_polynomial_eval_rootInterval]
  exact tendsto_finsetSum p.support fun k hk ↦
    (tendsto_integral_pow_empiricalApproximation Q k).const_mul (p.coeff k)

/-- The chosen equal-weight empirical measures converge weakly to the target
probability measure on the root interval. -/
theorem tendsto_empiricalApproximation
    (Q : ProbabilityMeasure RootInterval) :
    Tendsto (empiricalApproximation Q) atTop (𝓝 Q) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  rw [Metric.tendsto_atTop]
  intro ε hε
  let fc : C(RootInterval, ℝ) := ⟨f, f.continuous⟩
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap
    (-1) 1 fc (ε / 3) (by linarith)
  have hpoly := tendsto_integral_polynomial_empiricalApproximation Q p
  rw [Metric.tendsto_atTop] at hpoly
  obtain ⟨N, hN⟩ := hpoly (ε / 3) (by linarith)
  have herror (R : ProbabilityMeasure RootInterval) :
      dist (∫ x, f x ∂(R : Measure RootInterval))
        (∫ x, p.eval x.1 ∂(R : Measure RootInterval)) ≤ ε / 3 := by
    have hfint : Integrable f (R : Measure RootInterval) := f.integrable _
    let pf : RootInterval →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact
        ⟨fun x ↦ p.eval x.1, by fun_prop⟩
    have hpint : Integrable (fun x : RootInterval ↦ p.eval x.1)
        (R : Measure RootInterval) := by
      simpa only [pf] using! pf.integrable (R : Measure RootInterval)
    rw [dist_eq_norm, ← integral_sub hfint hpint]
    calc
      ‖∫ x, f x - p.eval x.1 ∂(R : Measure RootInterval)‖ ≤
          (ε / 3) * (R : Measure RootInterval).real univ := by
        apply norm_integral_le_of_norm_le_const
        exact Eventually.of_forall fun x ↦ by
          have hx :=
            (p.toContinuousMapOn RootInterval - fc).norm_coe_le_norm x
          have hx' := hx.trans (le_of_lt hp)
          simpa only [Polynomial.toContinuousMapOn_apply, fc,
            ContinuousMap.sub_apply, norm_sub_rev] using! hx'
      _ = ε / 3 := by simp
  refine ⟨N, fun n hn ↦ ?_⟩
  calc
    dist (∫ x, f x ∂(empiricalApproximation Q n : Measure RootInterval))
        (∫ x, f x ∂(Q : Measure RootInterval)) ≤
        dist (∫ x, f x ∂(empiricalApproximation Q n : Measure RootInterval))
            (∫ x, p.eval x.1 ∂(empiricalApproximation Q n : Measure RootInterval)) +
          (dist (∫ x, p.eval x.1 ∂(empiricalApproximation Q n : Measure RootInterval))
              (∫ x, p.eval x.1 ∂(Q : Measure RootInterval)) +
            dist (∫ x, p.eval x.1 ∂(Q : Measure RootInterval))
              (∫ x, f x ∂(Q : Measure RootInterval))) := by
      let A := ∫ x, f x ∂(empiricalApproximation Q n : Measure RootInterval)
      let B := ∫ x, p.eval x.1 ∂(empiricalApproximation Q n : Measure RootInterval)
      let C := ∫ x, p.eval x.1 ∂(Q : Measure RootInterval)
      let D := ∫ x, f x ∂(Q : Measure RootInterval)
      change dist A D ≤ dist A B + (dist B C + dist C D)
      calc
        dist A D ≤ dist A B + dist B D := dist_triangle A B D
        _ ≤ dist A B + (dist B C + dist C D) := by
          gcongr
          exact dist_triangle B C D
    _ < ε := by
      have hleft := herror (empiricalApproximation Q n)
      have hmiddle := hN n hn
      have hright :
          dist (∫ x, p.eval x.1 ∂(Q : Measure RootInterval))
            (∫ x, f x ∂(Q : Measure RootInterval)) ≤ ε / 3 := by
        simpa only [dist_comm] using! herror Q
      linarith

/-! ## Conversion to admissible polynomials -/

/-- The monic polynomial whose root multiset is the given multiset of
points of `RootInterval`. -/
def polynomialOfRootMultiset (s : Multiset RootInterval) : Polynomial ℝ :=
  ((s.map ((↑) : RootInterval → ℝ)).map fun r ↦ X - C r).prod

theorem polynomialOfRootMultiset_monic (s : Multiset RootInterval) :
    (polynomialOfRootMultiset s).Monic := by
  exact Polynomial.monic_multisetProd_X_sub_C
    (s.map ((↑) : RootInterval → ℝ))

theorem roots_polynomialOfRootMultiset (s : Multiset RootInterval) :
    (polynomialOfRootMultiset s).roots =
      s.map ((↑) : RootInterval → ℝ) := by
  exact Polynomial.roots_multiset_prod_X_sub_C _

theorem natDegree_polynomialOfRootMultiset (s : Multiset RootInterval) :
    (polynomialOfRootMultiset s).natDegree = s.card := by
  rw [polynomialOfRootMultiset,
    Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map]

theorem polynomialOfRootMultiset_ne_one {s : Multiset RootInterval} (hs : s ≠ 0) :
    polynomialOfRootMultiset s ≠ 1 := by
  intro hone
  have hdegree : (polynomialOfRootMultiset s).natDegree = 0 := by
    rw [hone]
    simp
  rw [natDegree_polynomialOfRootMultiset, Multiset.card_eq_zero] at hdegree
  exact hs hdegree

theorem isAdmissible_polynomialOfRootMultiset
    {s : Multiset RootInterval} (hs : s ≠ 0) :
    IsAdmissible (polynomialOfRootMultiset s) := by
  refine ⟨polynomialOfRootMultiset_monic s,
    polynomialOfRootMultiset_ne_one hs, ?_⟩
  rw [roots_polynomialOfRootMultiset]
  have hfilter :
      (s.map ((↑) : RootInterval → ℝ)).filter
        (fun x ↦ x ∈ Icc (-1 : ℝ) 1) =
          s.map ((↑) : RootInterval → ℝ) := by
    apply Multiset.filter_eq_self.mpr
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
    exact r.2
  rw [hfilter, Multiset.card_map, natDegree_polynomialOfRootMultiset]

/-- The canonical admissible polynomial corresponding to the `n`-th
empirical approximation. -/
def approximatingPolynomial (Q : ProbabilityMeasure RootInterval) (n : ℕ) :
    Polynomial ℝ :=
  polynomialOfRootMultiset (approximatingRootMultiset Q n)

theorem approximatingPolynomial_admissible
    (Q : ProbabilityMeasure RootInterval) (n : ℕ) :
    IsAdmissible (approximatingPolynomial Q n) :=
  isAdmissible_polynomialOfRootMultiset
    (approximatingRootMultiset_ne_zero Q n)

/-- The uniform probability measure on the real values of a nonempty root
multiset. -/
def uniformRealRootMultisetProbability (s : Multiset RootInterval) (hs : s ≠ 0) :
    ProbabilityMeasure ℝ :=
  uniformMultisetProbability (s.map ((↑) : RootInterval → ℝ))
    (fun h ↦ hs (Multiset.map_eq_zero.mp h))

theorem empiricalRootProbability_polynomialOfRootMultiset
    (s : Multiset RootInterval) (hs : s ≠ 0) :
    empiricalRootProbability (polynomialOfRootMultiset s)
        (isAdmissible_polynomialOfRootMultiset hs) =
      uniformRealRootMultisetProbability s hs := by
  apply ProbabilityMeasure.toMeasure_injective
  change (PMF.ofMultiset (polynomialOfRootMultiset s).roots _).toMeasure =
    (PMF.ofMultiset (s.map ((↑) : RootInterval → ℝ)) _).toMeasure
  simp only [roots_polynomialOfRootMultiset]

theorem empiricalRootProbability_approximatingPolynomial
    (Q : ProbabilityMeasure RootInterval) (n : ℕ) :
    empiricalRootProbability (approximatingPolynomial Q n)
        (approximatingPolynomial_admissible Q n) =
      uniformRealRootMultisetProbability (approximatingRootMultiset Q n)
        (approximatingRootMultiset_ne_zero Q n) := by
  exact empiricalRootProbability_polynomialOfRootMultiset _ _

theorem integral_uniformRealRootMultisetProbability
    (s : Multiset RootInterval) (hs : s ≠ 0) (g : ℝ → ℝ) :
    ∫ x, g x ∂(uniformRealRootMultisetProbability s hs : Measure ℝ) =
      multisetAverage (s.map fun r ↦ g r.1) := by
  rw [uniformRealRootMultisetProbability]
  rw [integral_uniformMultisetProbability_eq_multisetAverage]
  congr 1
  simp only [Multiset.map_map, Function.comp_apply]

theorem integral_uniformRealRootMultisetProbability_eq_empiricalApproximation
    (Q : ProbabilityMeasure RootInterval) (n : ℕ) (g : ℝ → ℝ) :
    ∫ x, g x ∂(uniformRealRootMultisetProbability
        (approximatingRootMultiset Q n)
        (approximatingRootMultiset_ne_zero Q n) : Measure ℝ) =
      ∫ r, g r.1 ∂(empiricalApproximation Q n : Measure RootInterval) := by
  rw [integral_uniformRealRootMultisetProbability,
    integral_empiricalApproximation]

theorem integral_probabilityMeasureToRootInterval
    (P : ProbabilityMeasure ℝ) (hP : IsRootIntervalSupported P) (g : ℝ → ℝ) :
    ∫ r, g r.1 ∂(probabilityMeasureToRootInterval P hP : Measure RootInterval) =
      ∫ x, g x ∂(P : Measure ℝ) := by
  change (∫ r : RootInterval, g r.1 ∂(Measure.comap
    ((↑) : RootInterval → ℝ) (P : Measure ℝ))) = ∫ x, g x ∂(P : Measure ℝ)
  rw [integral_subtype_comap measurableSet_Icc g]
  have hmem : ∀ᵐ x ∂(P : Measure ℝ), x ∈ RootInterval :=
    (mem_ae_iff_prob_eq_one measurableSet_Icc).2 hP
  rw [Measure.restrict_eq_self_of_ae_mem hmem]

/-- Every probability measure on `ℝ` supported on `[-1,1]` is the weak
limit of the empirical root probabilities of the explicit sequence of
monic admissible polynomials constructed above. -/
theorem tendsto_empiricalRootProbability_approximatingPolynomial
    (P : ProbabilityMeasure ℝ) (hP : IsRootIntervalSupported P) :
    Tendsto
      (fun n ↦
        let Q := probabilityMeasureToRootInterval P hP
        empiricalRootProbability (approximatingPolynomial Q n)
          (approximatingPolynomial_admissible Q n))
      atTop (𝓝 P) := by
  let Q := probabilityMeasureToRootInterval P hP
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  let fsub : RootInterval →ᵇ ℝ :=
    f.compContinuous ⟨((↑) : RootInterval → ℝ), continuous_subtype_val⟩
  have hsub :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (tendsto_empiricalApproximation Q)) fsub
  have hleft (n : ℕ) :
      (∫ x, f x ∂(empiricalRootProbability (approximatingPolynomial Q n)
        (approximatingPolynomial_admissible Q n) : Measure ℝ)) =
        ∫ r, f r.1 ∂(empiricalApproximation Q n : Measure RootInterval) := by
    rw [empiricalRootProbability_approximatingPolynomial]
    exact integral_uniformRealRootMultisetProbability_eq_empiricalApproximation Q n f
  have hright :
      (∫ r, f r.1 ∂(Q : Measure RootInterval)) =
        ∫ x, f x ∂(P : Measure ℝ) := by
    exact integral_probabilityMeasureToRootInterval P hP f
  simpa only [Q, hleft, hright, fsub,
    BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk] using! hsub

/-- Recovery polynomial associated to a supported probability measure. -/
def recoveryPolynomial (P : ProbabilityMeasure ℝ)
    (hP : IsRootIntervalSupported P) (n : ℕ) : Polynomial ℝ :=
  approximatingPolynomial (probabilityMeasureToRootInterval P hP) n

theorem recoveryPolynomial_admissible (P : ProbabilityMeasure ℝ)
    (hP : IsRootIntervalSupported P) (n : ℕ) :
    IsAdmissible (recoveryPolynomial P hP n) :=
  approximatingPolynomial_admissible _ n

/-- The empirical root probability of the recovery polynomial. -/
def recoveryEmpiricalRootProbability (P : ProbabilityMeasure ℝ)
    (hP : IsRootIntervalSupported P) (n : ℕ) : ProbabilityMeasure ℝ :=
  empiricalRootProbability (recoveryPolynomial P hP n)
    (recoveryPolynomial_admissible P hP n)

theorem recoveryEmpiricalRootProbability_supported (P : ProbabilityMeasure ℝ)
    (hP : IsRootIntervalSupported P) (n : ℕ) :
    IsRootIntervalSupported (recoveryEmpiricalRootProbability P hP n) :=
  empiricalRootProbability_supported_Icc _ _

/-- Clean recovery-facing form of empirical weak density. -/
theorem tendsto_recoveryEmpiricalRootProbability
    (P : ProbabilityMeasure ℝ) (hP : IsRootIntervalSupported P) :
    Tendsto (recoveryEmpiricalRootProbability P hP) atTop (𝓝 P) := by
  simpa only [recoveryEmpiricalRootProbability, recoveryPolynomial] using!
    tendsto_empiricalRootProbability_approximatingPolynomial P hP

/-- Combining empirical density with weak-to-`L¹` potential convergence and
sign-set stability on the recovery interval `[-2,2]`. -/
theorem tendsto_volume_negativeSetOn_negTwo_two_recoveryPotential
    (P : ProbabilityMeasure ℝ) (hP : IsRootIntervalSupported P)
    (hzero : volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
      logarithmicPotentialLp (-2) 2 (by norm_num) P hP x = 0} = 0) :
    Tendsto
      (fun n ↦ volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
        logarithmicPotentialLp (-2) 2 (by norm_num)
          (recoveryEmpiricalRootProbability P hP n)
          (recoveryEmpiricalRootProbability_supported P hP n) x < 0})
      atTop
      (𝓝 (volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
        logarithmicPotentialLp (-2) 2 (by norm_num) P hP x < 0})) := by
  exact tendsto_volume_negativeSetOn_negTwo_two_logarithmicPotentialLp_of_weak
    (tendsto_recoveryEmpiricalRootProbability P hP)
    (recoveryEmpiricalRootProbability_supported P hP) hP hzero

/-- Existential weak-density formulation, with the approximants bundled as
`AdmissiblePolynomial`s for direct use by extremal arguments. -/
theorem exists_admissiblePolynomials_empiricalRootProbability_tendsto
    (P : ProbabilityMeasure ℝ) (hP : IsRootIntervalSupported P) :
    ∃ f : ℕ → AdmissiblePolynomial,
      Tendsto (fun n ↦ empiricalRootProbability (f n).1 (f n).2)
        atTop (𝓝 P) := by
  let Q := probabilityMeasureToRootInterval P hP
  let f : ℕ → AdmissiblePolynomial := fun n ↦
    ⟨approximatingPolynomial Q n, approximatingPolynomial_admissible Q n⟩
  refine ⟨f, ?_⟩
  simpa only [f, Q] using!
    tendsto_empiricalRootProbability_approximatingPolynomial P hP

end

end Erdos1038
