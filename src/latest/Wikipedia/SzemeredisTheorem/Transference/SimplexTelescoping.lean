import Mathlib.Algebra.BigOperators.Ring.Finset
import Wikipedia.SzemeredisTheorem.Finite.Bonferroni
import Wikipedia.SzemeredisTheorem.Hypergraph.Simplex

/-!
# Edge-by-edge telescoping for weighted simplex counts

The relative counting lemma compares two products by replacing one edge at a
time.  This file isolates that exact finite algebra.  No boundedness is
required: all analytic work is reduced to bounding one mixed correlation for
each edge colour.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Difference of two finite products, telescoped in the ambient linear
order.  Earlier factors use `f`, later factors use `g`. -/
theorem prod_sub_prod_eq_sum_ordered
    {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (f g : ι → ℝ) :
    (∏ i ∈ s, f i) - ∏ i ∈ s, g i =
      ∑ i ∈ s,
        (f i - g i) *
          (∏ j ∈ s with j < i, f j) *
          ∏ j ∈ s with i < j, g j := by
  have h :=
    Finset.prod_add_ordered s g (fun i => f i - g i)
  have hleft :
      (∏ i ∈ s, (g i + (f i - g i))) =
        ∏ i ∈ s, f i := by
    apply Finset.prod_congr rfl
    intro i _
    ring
  have hlower (i : ι) :
      (∏ j ∈ s with j < i,
          (g j + (f j - g j))) =
        ∏ j ∈ s with j < i, f j := by
    apply Finset.prod_congr rfl
    intro j _
    ring
  rw [hleft] at h
  simp_rw [hlower] at h
  linarith

/-- The mixed term produced while replacing edge colour `j`: earlier
colours come from `H`, later colours from `G`, and colour `j` contributes
their difference. -/
def mixedSimplexTerm {k : ℕ} {V : Fin k → Type*}
    (H G : WeightedSimplexSystem V) (j : Fin k)
    (x : (i : Fin k) → V i) : ℝ :=
  (H.edgeWeight j (deleteCoordinate x j) -
      G.edgeWeight j (deleteCoordinate x j)) *
    (∏ i ∈ (Finset.univ : Finset (Fin k)) with i < j,
      H.edgeWeight i (deleteCoordinate x i)) *
    ∏ i ∈ (Finset.univ : Finset (Fin k)) with j < i,
      G.edgeWeight i (deleteCoordinate x i)

/-- Exact pointwise edge-by-edge telescoping of simplex weights. -/
theorem simplexWeight_sub_eq_sum_mixed
    {k : ℕ} {V : Fin k → Type*}
    (H G : WeightedSimplexSystem V)
    (x : (i : Fin k) → V i) :
    H.simplexWeight x - G.simplexWeight x =
      ∑ j : Fin k, mixedSimplexTerm H G j x := by
  change
    (∏ j : Fin k,
        H.edgeWeight j (deleteCoordinate x j)) -
      ∏ j : Fin k,
        G.edgeWeight j (deleteCoordinate x j) =
      ∑ j : Fin k, mixedSimplexTerm H G j x
  simpa [mixedSimplexTerm] using
    prod_sub_prod_eq_sum_ordered Finset.univ
      (fun j : Fin k =>
        H.edgeWeight j (deleteCoordinate x j))
      (fun j : Fin k =>
        G.edgeWeight j (deleteCoordinate x j))

/-- The normalized mixed correlation attached to one edge replacement. -/
noncomputable def mixedSimplexCorrelation
    {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H G : WeightedSimplexSystem V) (j : Fin k) : ℝ :=
  mean (mixedSimplexTerm H G j)

/-- Exact telescoping identity for normalized simplex counts. -/
theorem simplexCount_sub_eq_sum_mixedCorrelation
    {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H G : WeightedSimplexSystem V) :
    H.simplexCount - G.simplexCount =
      ∑ j : Fin k, mixedSimplexCorrelation H G j := by
  rw [WeightedSimplexSystem.simplexCount,
    WeightedSimplexSystem.simplexCount, ← mean_sub]
  calc
    mean (fun x => H.simplexWeight x - G.simplexWeight x) =
        mean (fun x =>
          ∑ j : Fin k, mixedSimplexTerm H G j x) := by
      apply congrArg mean
      funext x
      exact simplexWeight_sub_eq_sum_mixed H G x
    _ = ∑ j : Fin k, mean (mixedSimplexTerm H G j) :=
      mean_finset_sum Finset.univ
        (fun j => mixedSimplexTerm H G j)
    _ = ∑ j : Fin k, mixedSimplexCorrelation H G j := by
      rfl

/-- Absolute comparison reduces to the sum of the absolute mixed
correlations. -/
theorem abs_simplexCount_sub_le_sum_mixedCorrelation
    {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H G : WeightedSimplexSystem V) :
    |H.simplexCount - G.simplexCount| ≤
      ∑ j : Fin k, |mixedSimplexCorrelation H G j| := by
  rw [simplexCount_sub_eq_sum_mixedCorrelation]
  exact Finset.abs_sum_le_sum_abs _ _

/-- Every mixed edge-replacement correlation is at most `ε`. -/
def MixedSimplexCorrelationLe
    {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H G : WeightedSimplexSystem V) (ε : ℝ) : Prop :=
  ∀ j, |mixedSimplexCorrelation H G j| ≤ ε

/-- Uniform control of the `k` mixed correlations controls the entire
simplex-count difference by `k ε`. -/
theorem simplexCount_abs_sub_le_of_mixedCorrelation
    {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H G : WeightedSimplexSystem V) {ε : ℝ}
    (h : MixedSimplexCorrelationLe H G ε) :
    |H.simplexCount - G.simplexCount| ≤ (k : ℝ) * ε := by
  calc
    |H.simplexCount - G.simplexCount| ≤
        ∑ j : Fin k, |mixedSimplexCorrelation H G j| :=
      abs_simplexCount_sub_le_sum_mixedCorrelation H G
    _ ≤ ∑ _j : Fin k, ε :=
      Finset.sum_le_sum fun j _ => h j
    _ = (k : ℝ) * ε := by
      simp

end Wikipedia.SzemeredisTheorem
