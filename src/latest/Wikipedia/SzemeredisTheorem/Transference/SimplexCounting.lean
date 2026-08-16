import Mathlib.Algebra.Order.BigOperators.Expect
import Wikipedia.SzemeredisTheorem.Hypergraph.Simplex

/-!
# Stable weighted simplex counts

Relative counting will eventually use cut discrepancy and densification.
This file records the elementary endpoint: uniformly close edge weights in
`[0,1]` have close simplex counts.  The proof is the finite telescoping
estimate for products, followed by averaging.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Every edge weight of `H` lies in the unit interval. -/
def EdgeWeightsInUnitInterval {k : ℕ} {V : Fin k → Type*}
    (H : WeightedSimplexSystem V) : Prop :=
  ∀ j x, 0 ≤ H.edgeWeight j x ∧ H.edgeWeight j x ≤ 1

/-- Corresponding edge weights of `H` and `G` differ by at most `ε`. -/
def EdgeSupDistanceLe {k : ℕ} {V : Fin k → Type*}
    (H G : WeightedSimplexSystem V) (ε : ℝ) : Prop :=
  ∀ j x, |H.edgeWeight j x - G.edgeWeight j x| ≤ ε

/-- A telescoping product estimate for two families in `[0,1]`. -/
theorem abs_prod_sub_prod_le_card_mul
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f g : ι → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hf0 : ∀ i ∈ s, 0 ≤ f i)
    (hf1 : ∀ i ∈ s, f i ≤ 1)
    (hg0 : ∀ i ∈ s, 0 ≤ g i)
    (hg1 : ∀ i ∈ s, g i ≤ 1)
    (hfg : ∀ i ∈ s, |f i - g i| ≤ ε) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
      (s.card : ℝ) * ε := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hfa0 : 0 ≤ f a := hf0 a (Finset.mem_insert_self a s)
      have hfa1 : f a ≤ 1 := hf1 a (Finset.mem_insert_self a s)
      have hga0 : 0 ≤ g a := hg0 a (Finset.mem_insert_self a s)
      have hga1 : g a ≤ 1 := hg1 a (Finset.mem_insert_self a s)
      have hdiffa :
          |f a - g a| ≤ ε :=
        hfg a (Finset.mem_insert_self a s)
      have hfprod0 : 0 ≤ ∏ i ∈ s, f i :=
        Finset.prod_nonneg fun i hi => hf0 i (Finset.mem_insert_of_mem hi)
      have hfprod1 : (∏ i ∈ s, f i) ≤ 1 :=
        Finset.prod_le_one
          (fun i hi => hf0 i (Finset.mem_insert_of_mem hi))
          (fun i hi => hf1 i (Finset.mem_insert_of_mem hi))
      have hgprod0 : 0 ≤ ∏ i ∈ s, g i :=
        Finset.prod_nonneg fun i hi => hg0 i (Finset.mem_insert_of_mem hi)
      have hgprod1 : (∏ i ∈ s, g i) ≤ 1 :=
        Finset.prod_le_one
          (fun i hi => hg0 i (Finset.mem_insert_of_mem hi))
          (fun i hi => hg1 i (Finset.mem_insert_of_mem hi))
      have ih' :
          |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
            (s.card : ℝ) * ε :=
        ih
          (fun i hi => hf0 i (Finset.mem_insert_of_mem hi))
          (fun i hi => hf1 i (Finset.mem_insert_of_mem hi))
          (fun i hi => hg0 i (Finset.mem_insert_of_mem hi))
          (fun i hi => hg1 i (Finset.mem_insert_of_mem hi))
          (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
      have hfirst :
          |f a - g a| * |∏ i ∈ s, f i| ≤ ε := by
        calc
          |f a - g a| * |∏ i ∈ s, f i| ≤
              ε * |∏ i ∈ s, f i| :=
            mul_le_mul_of_nonneg_right hdiffa (abs_nonneg _)
          _ ≤ ε * 1 :=
            mul_le_mul_of_nonneg_left
              (by simpa [abs_of_nonneg hfprod0] using hfprod1) hε
          _ = ε := mul_one ε
      have hsecond :
          |g a| *
              |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
            (s.card : ℝ) * ε := by
        calc
          |g a| *
                |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
              1 *
                |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| :=
            mul_le_mul_of_nonneg_right
              (by simpa [abs_of_nonneg hga0] using hga1)
              (abs_nonneg _)
          _ ≤ 1 * ((s.card : ℝ) * ε) :=
            mul_le_mul_of_nonneg_left ih' zero_le_one
          _ = (s.card : ℝ) * ε := one_mul _
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Finset.card_insert_of_notMem ha]
      calc
        |f a * (∏ i ∈ s, f i) -
              g a * ∏ i ∈ s, g i| =
            |(f a - g a) * (∏ i ∈ s, f i) +
              g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| := by
                congr 1
                ring
        _ ≤
            |f a - g a| * |∏ i ∈ s, f i| +
              |g a| *
                |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| := by
          simpa [abs_mul] using
            abs_add_le
              ((f a - g a) * (∏ i ∈ s, f i))
              (g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i))
        _ ≤ ε + (s.card : ℝ) * ε :=
          add_le_add hfirst hsecond
        _ = ((s.card + 1 : ℕ) : ℝ) * ε := by
          push_cast
          ring

/-- Uniformly close unit-interval edge weights give pointwise close simplex
weights. -/
theorem simplexWeight_abs_sub_le
    {k : ℕ} {V : Fin k → Type*}
    (H G : WeightedSimplexSystem V) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hH : EdgeWeightsInUnitInterval H)
    (hG : EdgeWeightsInUnitInterval G)
    (hHG : EdgeSupDistanceLe H G ε)
    (x : (i : Fin k) → V i) :
    |H.simplexWeight x - G.simplexWeight x| ≤ (k : ℝ) * ε := by
  change
    |(∏ j : Fin k, H.edgeWeight j (deleteCoordinate x j)) -
        ∏ j : Fin k, G.edgeWeight j (deleteCoordinate x j)| ≤
      (k : ℝ) * ε
  simpa using
    abs_prod_sub_prod_le_card_mul Finset.univ
      (fun j => H.edgeWeight j (deleteCoordinate x j))
      (fun j => G.edgeWeight j (deleteCoordinate x j))
      hε
      (fun j _ => (hH j (deleteCoordinate x j)).1)
      (fun j _ => (hH j (deleteCoordinate x j)).2)
      (fun j _ => (hG j (deleteCoordinate x j)).1)
      (fun j _ => (hG j (deleteCoordinate x j)).2)
      (fun j _ => hHG j (deleteCoordinate x j))

/-- Sup-norm stability of normalized simplex counts. -/
theorem simplexCount_abs_sub_le
    {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)]
    (H G : WeightedSimplexSystem V) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hH : EdgeWeightsInUnitInterval H)
    (hG : EdgeWeightsInUnitInterval G)
    (hHG : EdgeSupDistanceLe H G ε) :
    |H.simplexCount - G.simplexCount| ≤ (k : ℝ) * ε := by
  rw [WeightedSimplexSystem.simplexCount,
    WeightedSimplexSystem.simplexCount, ← mean_sub]
  calc
    |mean (fun x => H.simplexWeight x - G.simplexWeight x)| ≤
        mean (fun x => |H.simplexWeight x - G.simplexWeight x|) := by
      exact Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun _ => (k : ℝ) * ε) :=
      mean_mono fun x => simplexWeight_abs_sub_le H G hε hH hG hHG x
    _ = (k : ℝ) * ε := mean_const _

end Wikipedia.SzemeredisTheorem
