/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.OrderQ

/-!
# Finite Darboux comparisons for Ford's ordered bins

The arithmetic discretizations used around Ford's Lemma 3.5 attach a
nonnegative mass to each one-dimensional bin.  After taking products, a
lattice point has weight equal to the product of its coordinate masses.
This file isolates the measure-theoretic step which compares that weighted
sum with an integral.

The cells are deliberately allowed to have unequal widths.  This is useful
for the exact-mass construction in which a cell associated to a prime `p`
has length proportional to `1 / p`.  The main theorem only asks that each
one-dimensional mass be at most `c` times the corresponding width.
-/

namespace Erdos896.Ford

open MeasureTheory Set
open scoped BigOperators

section DisjointCells

variable {α ι : Type*} [MeasurableSpace α]
  {μ : Measure α}

/-- Integrals over finitely many disjoint measurable cells are bounded by
the integral over a measurable region containing all the cells. -/
theorem sum_setIntegral_le_setIntegral_of_pairwiseDisjoint
    (s : Finset ι) (cell : ι → Set α) (region : Set α) (f : α → ℝ)
    (hcell : ∀ i ∈ s, MeasurableSet (cell i))
    (hdisj : (s : Set ι).PairwiseDisjoint cell)
    (hsub : ∀ i ∈ s, cell i ⊆ region)
    (hregion : MeasurableSet region)
    (hf : IntegrableOn f region μ)
    (hf_nonneg : ∀ x ∈ region, 0 ≤ f x) :
    (∑ i ∈ s, ∫ x in cell i, f x ∂μ) ≤ ∫ x in region, f x ∂μ := by
  classical
  have hfi (i : ι) (hi : i ∈ s) : IntegrableOn f (cell i) μ :=
    hf.mono_set (hsub i hi)
  have hleft : Integrable (fun x ↦ ∑ i ∈ s, (cell i).indicator f x) μ := by
    apply integrable_finsetSum
    intro i hi
    exact (integrable_indicator_iff (hcell i hi)).2 (hfi i hi)
  have hright : Integrable (region.indicator f) μ :=
    (integrable_indicator_iff hregion).2 hf
  have hpoint (x : α) :
      (∑ i ∈ s, (cell i).indicator f x) ≤ region.indicator f x := by
    by_cases hxregion : x ∈ region
    · rw [indicator_of_mem hxregion]
      by_cases hxcell : ∃ i ∈ s, x ∈ cell i
      · obtain ⟨i, hi, hxi⟩ := hxcell
        rw [Finset.sum_eq_single i]
        · rw [indicator_of_mem hxi]
        · intro j hj hji
          rw [indicator_of_notMem]
          intro hxj
          exact Set.disjoint_left.1 (hdisj hj hi hji) hxj hxi
        · simp [hi]
      · have hz : (∑ i ∈ s, (cell i).indicator f x) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          rw [indicator_of_notMem]
          exact fun hxi ↦ hxcell ⟨i, hi, hxi⟩
        rw [hz]
        exact hf_nonneg x hxregion
    · rw [indicator_of_notMem hxregion]
      apply Finset.sum_nonpos
      intro i hi
      have hxi : x ∉ cell i := fun h ↦ hxregion (hsub i hi h)
      simp [indicator_of_notMem hxi]
  have hmono :
      (∫ x, ∑ i ∈ s, (cell i).indicator f x ∂μ) ≤
        ∫ x, region.indicator f x ∂μ :=
    integral_mono_ae hleft hright (Filter.Eventually.of_forall hpoint)
  rw [integral_finsetSum s, integral_indicator hregion] at hmono
  · calc
      (∑ i ∈ s, ∫ x in cell i, f x ∂μ) =
          ∑ i ∈ s, ∫ x, (cell i).indicator f x ∂μ := by
            apply Finset.sum_congr rfl
            intro i hi
            exact (integral_indicator (hcell i hi)).symm
      _ ≤ ∫ x in region, f x ∂μ := hmono
  · intro i hi
    exact (integrable_indicator_iff (hcell i hi)).2 (hfi i hi)

/-- Abstract finite weighted lower-Darboux comparison.

`sample i` is a lower sample for `f` on `cell i`.  The assumption on
`weight` permits a common loss `c` compared with cell volume. -/
theorem weighted_sum_le_mul_setIntegral_of_cells
    (s : Finset ι) (cell : ι → Set α) (sample : ι → α)
    (weight : ι → ℝ) (region : Set α) (f : α → ℝ) (c : ℝ)
    (hc : 0 ≤ c)
    (hcell : ∀ i ∈ s, MeasurableSet (cell i))
    (hcell_finite : ∀ i ∈ s, μ (cell i) ≠ ⊤)
    (hdisj : (s : Set ι).PairwiseDisjoint cell)
    (hsub : ∀ i ∈ s, cell i ⊆ region)
    (hregion : MeasurableSet region)
    (hf : IntegrableOn f region μ)
    (hf_nonneg : ∀ x ∈ region, 0 ≤ f x)
    (hsample_nonneg : ∀ i ∈ s, 0 ≤ f (sample i))
    (hlower : ∀ i ∈ s, ∀ x ∈ cell i, f (sample i) ≤ f x)
    (hweight : ∀ i ∈ s, weight i ≤ c * μ.real (cell i)) :
    (∑ i ∈ s, weight i * f (sample i)) ≤
      c * ∫ x in region, f x ∂μ := by
  classical
  have hfi (i : ι) (hi : i ∈ s) : IntegrableOn f (cell i) μ :=
    hf.mono_set (hsub i hi)
  have hterm (i : ι) (hi : i ∈ s) :
      weight i * f (sample i) ≤ c * ∫ x in cell i, f x ∂μ := by
    calc
      weight i * f (sample i)
          ≤ (c * μ.real (cell i)) * f (sample i) :=
            mul_le_mul_of_nonneg_right (hweight i hi) (hsample_nonneg i hi)
      _ = c * ∫ _x in cell i, f (sample i) ∂μ := by
            rw [setIntegral_const]
            ring
      _ ≤ c * ∫ x in cell i, f x ∂μ := by
            exact mul_le_mul_of_nonneg_left
              (setIntegral_mono_on
                (integrableOn_const (hcell_finite i hi)) (hfi i hi)
                (hcell i hi) (hlower i hi)) hc
  calc
    (∑ i ∈ s, weight i * f (sample i))
        ≤ ∑ i ∈ s, c * ∫ x in cell i, f x ∂μ :=
          Finset.sum_le_sum fun i hi ↦ hterm i hi
    _ = c * ∑ i ∈ s, ∫ x in cell i, f x ∂μ := by
          rw [Finset.mul_sum]
    _ ≤ c * ∫ x in region, f x ∂μ := by
          gcongr
          exact sum_setIntegral_le_setIntegral_of_pairwiseDisjoint
            s cell region f hcell hdisj hsub hregion hf hf_nonneg

end DisjointCells

section OrderedGrid

variable {ι : Type*}

/-- Product weight of a multidimensional lattice point. -/
def gridWeight {k : ℕ} (mass : Fin k → ι → ℝ) (j : Fin k → ι) : ℝ :=
  ∏ r : Fin k, mass r (j r)

/-- Product width of the cell belonging to a multidimensional lattice
point. -/
def gridWidth {k : ℕ} (width : Fin k → ι → ℝ) (j : Fin k → ι) : ℝ :=
  ∏ r : Fin k, width r (j r)

/-- The half-open product cell belonging to a lattice point.  Using `Ioc`
in every coordinate makes adjacent cells genuinely disjoint. -/
def gridIoc {k : ℕ} (lower upper : Fin k → ι → ℝ)
    (j : Fin k → ι) : Set (Fin k → ℝ) :=
  Set.pi Set.univ fun r ↦ Set.Ioc (lower r (j r)) (upper r (j r))

theorem measurableSet_gridIoc {k : ℕ} (lower upper : Fin k → ι → ℝ)
    (j : Fin k → ι) : MeasurableSet (gridIoc lower upper j) := by
  unfold gridIoc
  exact MeasurableSet.pi Set.countable_univ fun _ _ ↦ measurableSet_Ioc

theorem volume_gridIoc_toReal {k : ℕ} (lower upper : Fin k → ι → ℝ)
    (j : Fin k → ι) (hlu : ∀ r, lower r (j r) ≤ upper r (j r)) :
    volume.real (gridIoc lower upper j) =
      gridWidth (fun r t ↦ upper r t - lower r t) j := by
  unfold gridIoc gridWidth Measure.real
  exact Real.volume_pi_Ioc_toReal hlu

theorem volume_gridIoc_ne_top {k : ℕ} (lower upper : Fin k → ι → ℝ)
    (j : Fin k → ι) : volume (gridIoc lower upper j) ≠ ⊤ := by
  rw [gridIoc, Real.volume_pi_Ioc]
  exact ENNReal.prod_ne_top fun _ _ ↦ ENNReal.ofReal_ne_top

/-- Half-open intervals separated in index order are pairwise disjoint.
For adjacent bins one usually proves `upper i ≤ lower j` by transitivity
through the intervening endpoints. -/
theorem pairwiseDisjoint_Ioc_of_separated [LinearOrder ι]
    (lower upper : ι → ℝ)
    (hsep : ∀ i j, i < j → upper i ≤ lower j) :
    Pairwise (Function.onFun Disjoint
      (fun t ↦ Set.Ioc (lower t) (upper t))) := by
  intro i j hij
  apply Set.disjoint_left.2
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact (not_lt_of_ge (hxi.2.trans (hsep i j hij))) hxj.1
  · exact (not_lt_of_ge (hxj.2.trans (hsep j i hji))) hxi.1

/-- Product cells are pairwise disjoint as soon as each coordinate family
of one-dimensional half-open bins is pairwise disjoint. -/
theorem pairwiseDisjoint_gridIoc {k : ℕ} (lower upper : Fin k → ι → ℝ)
    (hbin : ∀ r, Pairwise (Function.onFun Disjoint
      (fun t ↦ Set.Ioc (lower r t) (upper r t)))) :
    Pairwise (Function.onFun Disjoint (gridIoc lower upper)) := by
  classical
  intro j j' hjj'
  change Disjoint
    (Set.pi Set.univ fun r ↦ Set.Ioc (lower r (j r)) (upper r (j r)))
    (Set.pi Set.univ fun r ↦ Set.Ioc (lower r (j' r)) (upper r (j' r)))
  rw [Set.disjoint_pi]
  have hex : ∃ r, j r ≠ j' r := by
    by_contra h
    apply hjj'
    funext r
    exact not_ne_iff.mp (not_exists.mp h r)
  obtain ⟨r, hr⟩ := hex
  exact ⟨r, Set.mem_univ r, hbin r hr⟩

/-- Coordinatewise domination of bin masses multiplies to domination of
the lattice weight. -/
theorem gridWeight_le_pow_mul_gridWidth {k : ℕ}
    (mass width : Fin k → ι → ℝ) (j : Fin k → ι) (c : ℝ)
    (hmass_nonneg : ∀ r, 0 ≤ mass r (j r))
    (hmass : ∀ r, mass r (j r) ≤ c * width r (j r)) :
    gridWeight mass j ≤ c ^ k * gridWidth width j := by
  classical
  unfold gridWeight gridWidth
  calc
    (∏ r : Fin k, mass r (j r))
        ≤ ∏ r : Fin k, c * width r (j r) := by
          exact Finset.prod_le_prod (fun r _ ↦ hmass_nonneg r)
            (fun r _ ↦ hmass r)
    _ = c ^ k * ∏ r : Fin k, width r (j r) := by
          rw [Finset.prod_mul_distrib]
          simp

/-- Multidimensional weighted lower-Darboux comparison on an ordered cube.

The family `cell j` may consist of unequal rectangular cells; the theorem
only uses their volume lower bound.  Monotonicity of the integrand enters
through `hlower`.  Thus the result applies equally to lower endpoints of a
coordinatewise increasing function and upper endpoints of a
coordinatewise decreasing function. -/
theorem weighted_orderedGrid_sum_le_integral
    {k : ℕ} (grid : Finset (Fin k → ι))
    (cell : (Fin k → ι) → Set (Fin k → ℝ))
    (sample : (Fin k → ι) → (Fin k → ℝ))
    (mass width : Fin k → ι → ℝ)
    (a b c : ℝ) (f : (Fin k → ℝ) → ℝ)
    (hc : 0 ≤ c)
    (hmass_nonneg : ∀ j ∈ grid, ∀ r, 0 ≤ mass r (j r))
    (hmass : ∀ j ∈ grid, ∀ r, mass r (j r) ≤ c * width r (j r))
    (hcell : ∀ j ∈ grid, MeasurableSet (cell j))
    (hcell_finite : ∀ j ∈ grid, volume (cell j) ≠ ⊤)
    (hvolume : ∀ j ∈ grid, gridWidth width j ≤ volume.real (cell j))
    (hdisj : (grid : Set (Fin k → ι)).PairwiseDisjoint cell)
    (hsub : ∀ j ∈ grid, cell j ⊆ orderedSimplex k a b)
    (hf : IntegrableOn f (orderedSimplex k a b))
    (hf_nonneg : ∀ x ∈ orderedSimplex k a b, 0 ≤ f x)
    (hsample_nonneg : ∀ j ∈ grid, 0 ≤ f (sample j))
    (hlower : ∀ j ∈ grid, ∀ x ∈ cell j, f (sample j) ≤ f x) :
    (∑ j ∈ grid, gridWeight mass j * f (sample j)) ≤
      c ^ k * ∫ x in orderedSimplex k a b, f x := by
  classical
  apply weighted_sum_le_mul_setIntegral_of_cells grid cell sample
    (gridWeight mass) (orderedSimplex k a b) f (c ^ k)
  · positivity
  · exact hcell
  · exact hcell_finite
  · exact hdisj
  · exact hsub
  · exact measurableSet_orderedSimplex k a b
  · exact hf
  · exact hf_nonneg
  · exact hsample_nonneg
  · exact hlower
  · intro j hj
    calc
      gridWeight mass j ≤ c ^ k * gridWidth width j :=
        gridWeight_le_pow_mul_gridWidth mass width j c
          (hmass_nonneg j hj) (hmass j hj)
      _ ≤ c ^ k * volume.real (cell j) := by
        exact mul_le_mul_of_nonneg_left (hvolume j hj) (pow_nonneg hc k)

/-- Concrete lower-endpoint rule for half-open product cells.  All analytic
cell facts (measurability, finite volume, exact product volume and
disjointness) are discharged here.  A caller only supplies the elementary
endpoint ordering which places its chosen cells in the ordered simplex. -/
theorem weighted_orderedIoc_sum_le_integral_of_monotoneOn
    {k : ℕ} (grid : Finset (Fin k → ι))
    (lower upper mass : Fin k → ι → ℝ)
    (a b c : ℝ) (f : (Fin k → ℝ) → ℝ)
    (hc : 0 ≤ c)
    (hmass_nonneg : ∀ j ∈ grid, ∀ r, 0 ≤ mass r (j r))
    (hlu : ∀ j ∈ grid, ∀ r, lower r (j r) ≤ upper r (j r))
    (hmass : ∀ j ∈ grid, ∀ r,
      mass r (j r) ≤ c * (upper r (j r) - lower r (j r)))
    (hbin : ∀ r, Pairwise (Function.onFun Disjoint
      (fun t ↦ Set.Ioc (lower r t) (upper r t))))
    (hsub : ∀ j ∈ grid,
      gridIoc lower upper j ⊆ orderedSimplex k a b)
    (hsample_mem : ∀ j ∈ grid,
      (fun r ↦ lower r (j r)) ∈ orderedSimplex k a b)
    (hf : IntegrableOn f (orderedSimplex k a b))
    (hf_nonneg : ∀ x ∈ orderedSimplex k a b, 0 ≤ f x)
    (hf_mono : MonotoneOn f (orderedSimplex k a b)) :
    (∑ j ∈ grid, gridWeight mass j * f (fun r ↦ lower r (j r))) ≤
      c ^ k * ∫ x in orderedSimplex k a b, f x := by
  classical
  apply weighted_orderedGrid_sum_le_integral grid (gridIoc lower upper)
    (fun j r ↦ lower r (j r)) mass
    (fun r t ↦ upper r t - lower r t) a b c f hc
  · exact hmass_nonneg
  · exact hmass
  · exact fun j _ ↦ measurableSet_gridIoc lower upper j
  · exact fun j _ ↦ volume_gridIoc_ne_top lower upper j
  · intro j hj
    rw [volume_gridIoc_toReal lower upper j (hlu j hj)]
  · intro j _ j' _ hjj'
    exact pairwiseDisjoint_gridIoc lower upper hbin hjj'
  · exact hsub
  · exact hf
  · exact hf_nonneg
  · intro j hj
    exact hf_nonneg _ (hsample_mem j hj)
  · intro j hj x hx
    apply hf_mono (hsample_mem j hj) (hsub j hj hx)
    intro r
    exact (Set.mem_Ioc.1 (Set.mem_pi.1 hx r (Set.mem_univ r))).1.le

/-- Upper-endpoint counterpart of
`weighted_orderedIoc_sum_le_integral_of_monotoneOn`, for a function which
is coordinatewise decreasing on the ordered simplex. -/
theorem weighted_orderedIoc_sum_le_integral_of_antitoneOn
    {k : ℕ} (grid : Finset (Fin k → ι))
    (lower upper mass : Fin k → ι → ℝ)
    (a b c : ℝ) (f : (Fin k → ℝ) → ℝ)
    (hc : 0 ≤ c)
    (hmass_nonneg : ∀ j ∈ grid, ∀ r, 0 ≤ mass r (j r))
    (hlu : ∀ j ∈ grid, ∀ r, lower r (j r) ≤ upper r (j r))
    (hmass : ∀ j ∈ grid, ∀ r,
      mass r (j r) ≤ c * (upper r (j r) - lower r (j r)))
    (hbin : ∀ r, Pairwise (Function.onFun Disjoint
      (fun t ↦ Set.Ioc (lower r t) (upper r t))))
    (hsub : ∀ j ∈ grid,
      gridIoc lower upper j ⊆ orderedSimplex k a b)
    (hsample_mem : ∀ j ∈ grid,
      (fun r ↦ upper r (j r)) ∈ orderedSimplex k a b)
    (hf : IntegrableOn f (orderedSimplex k a b))
    (hf_nonneg : ∀ x ∈ orderedSimplex k a b, 0 ≤ f x)
    (hf_anti : AntitoneOn f (orderedSimplex k a b)) :
    (∑ j ∈ grid, gridWeight mass j * f (fun r ↦ upper r (j r))) ≤
      c ^ k * ∫ x in orderedSimplex k a b, f x := by
  classical
  apply weighted_orderedGrid_sum_le_integral grid (gridIoc lower upper)
    (fun j r ↦ upper r (j r)) mass
    (fun r t ↦ upper r t - lower r t) a b c f hc
  · exact hmass_nonneg
  · exact hmass
  · exact fun j _ ↦ measurableSet_gridIoc lower upper j
  · exact fun j _ ↦ volume_gridIoc_ne_top lower upper j
  · intro j hj
    rw [volume_gridIoc_toReal lower upper j (hlu j hj)]
  · intro j _ j' _ hjj'
    exact pairwiseDisjoint_gridIoc lower upper hbin hjj'
  · exact hsub
  · exact hf
  · exact hf_nonneg
  · intro j hj
    exact hf_nonneg _ (hsample_mem j hj)
  · intro j hj x hx
    apply hf_anti (hsub j hj hx) (hsample_mem j hj)
    intro r
    exact (Set.mem_Ioc.1 (Set.mem_pi.1 hx r (Set.mem_univ r))).2

end OrderedGrid

end Erdos896.Ford
