/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Induction on induced sparse cores. -/

import ErdosProblems.Erdos717.SparseInductionArithmetic
import ErdosProblems.Erdos717.DensityTheorem

open Function Set
open SimpleGraph

namespace Erdos717

/-- Independence number cannot increase on passing to an induced graph. -/
theorem indepNum_induce_finset_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) :
    (G.induce (U : Set V)).indepNum ≤ G.indepNum := by
  classical
  let J := G.induce (U : Set V)
  obtain ⟨I, hI⟩ := J.exists_isNIndepSet_indepNum
  have hI' : (G.induce (U : Set V)).IsNIndepSet J.indepNum I := by
    simpa only [J] using hI
  rw [SimpleGraph.induce_eq_coe_induce_top] at hI'
  let j : {x // x ∈ (U : Set V)} ↪ V :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hambient : G.IsNIndepSet J.indepNum (I.map j) := by
    simpa only [j] using
      (SimpleGraph.isNIndepSet_induce (G := G) (F := (U : Set V))
        (s := I) (n := J.indepNum)).mp hI'
  have hle := hambient.isIndepSet.card_le_indepNum
  rw [hambient.card_eq] at hle
  simpa only [J] using hle

/-- The canonical low-pattern set retains at least one eighth of all
vertices. -/
theorem sparseLowPatternSet_card_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a D b : ℕ) (hind : G.indepNum ≤ a)
    (ha : 16 * a ≤ Fintype.card V)
    (hdegreeCut : 4 * G.edgeFinset.card ≤ Fintype.card V * (D + 1))
    (hpatternCut : 4 * D * a ≤ (b + 1) * Fintype.card V) :
    Fintype.card V / 8 ≤ (sparseLowPatternSet G D b).card := by
  classical
  let P := lowDegreeFinset G D
  let I := sparseIndependentSet G D
  have hIspec : I ⊆ P ∧ G.IsIndepSet I ∧ IndepBoundOn G P I.card := by
    simpa [I, P, sparseIndependentSet] using
      Classical.choose_spec (exists_maximum_independent_subset G
        (lowDegreeFinset G D))
  have hIP : I ⊆ P := hIspec.1
  have hIind : G.IsIndepSet I := hIspec.2.1
  let W := lowPatternFinset G P I b
  have hIcard : I.card ≤ a := hIind.card_le_indepNum.trans hind
  have hPcard : Fintype.card V / 2 ≤ P.card :=
    half_card_le_lowDegreeFinset G D hdegreeCut
  have hXbound := highPattern_card_mul_le G P I D b hIP
    (degree_le_of_mem_lowDegreeFinset G D)
  have hXcard : 4 * (highPatternFinset G P I b).card ≤ Fintype.card V := by
    have hmul : (b + 1) * (4 * (highPatternFinset G P I b).card) ≤
        (b + 1) * Fintype.card V := by
      calc
        (b + 1) * (4 * (highPatternFinset G P I b).card) =
            4 * ((b + 1) * (highPatternFinset G P I b).card) := by ring
        _ ≤ 4 * (D * I.card) := Nat.mul_le_mul_left 4 hXbound
        _ ≤ 4 * D * a := by
          simpa [mul_assoc] using Nat.mul_le_mul_left (4 * D) hIcard
        _ ≤ (b + 1) * Fintype.card V := hpatternCut
    exact Nat.le_of_mul_le_mul_left hmul (by omega)
  have hpart := low_high_pattern_partition G P I hIP b
  change W.card + (highPatternFinset G P I b).card + I.card = P.card at hpart
  have haCard : 16 * I.card ≤ Fintype.card V :=
    (Nat.mul_le_mul_left 16 hIcard).trans ha
  have hW : Fintype.card V / 8 ≤ W.card := by omega
  simpa [W, I, P, sparseLowPatternSet] using hW

/-- The canonical independent set is nonempty whenever its low-degree
ambient set is nonempty. -/
theorem sparseIndependentSet_card_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hP : 0 < (lowDegreeFinset G D).card) :
    0 < (sparseIndependentSet G D).card := by
  classical
  let P := lowDegreeFinset G D
  let I := sparseIndependentSet G D
  have hIspec : I ⊆ P ∧ G.IsIndepSet I ∧ IndepBoundOn G P I.card := by
    simpa [I, P, sparseIndependentSet] using
      Classical.choose_spec (exists_maximum_independent_subset G P)
  obtain ⟨v, hvP⟩ := Finset.card_pos.mp (by simpa only [P] using hP)
  have hsingle : G.IsIndepSet ({v} : Finset V) := by simp
  have hsingleP : ({v} : Finset V) ⊆ P := by simpa using hvP
  have := hIspec.2.2 {v} hsingleP hsingle
  have hI : 0 < I.card := by simpa using this
  simpa [I] using hI

/-- The induced graph on the low-pattern set and its spanning copy have
the same number of edges. -/
theorem card_edgeFinset_induce_sparseLowPatternSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D b : ℕ) :
    (G.induce (sparseLowPatternSet G D b : Set V)).edgeFinset.card =
      (sparseCore G D b).edgeSet.ncard := by
  classical
  let W := sparseLowPatternSet G D b
  let J := G.induce (W : Set V)
  have hcard : J.spanningCoe.edgeFinset.card = J.edgeFinset.card := by
    exact SimpleGraph.card_edgeFinset_map
      (Function.Embedding.subtype fun x => x ∈ (W : Set V)) J
  calc
    (G.induce (sparseLowPatternSet G D b : Set V)).edgeFinset.card =
        J.edgeFinset.card := by rfl
    _ = J.spanningCoe.edgeFinset.card := hcard.symm
    _ = J.spanningCoe.edgeSet.ncard :=
      Erdos718.MaderPrototype.card_edgeFinset_eq_ncard_edgeSet J.spanningCoe
    _ = (sparseCore G D b).edgeSet.ncard := by rfl

/-- The product of edge density and the independence bound is uniformly
bounded below once the latter is at most half the order. -/
theorem one_div_sixtyfour_le_density_mul_indepBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : ℕ)
    (hind : G.indepNum ≤ a) (hn : 0 < Fintype.card V)
    (ha : 2 * a ≤ Fintype.card V) :
    (1 / 64 : ℝ) ≤
      ((G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ^ 2) * a := by
  let n := Fintype.card V
  let m := G.edgeFinset.card
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hsmallA : 16 * a ≤ n
  · have hdensity := card_sq_le_thirtytwo_mul_edges_mul_indepBound
      G a hind (by simpa only [n] using hsmallA)
    have hdensityR : (n : ℝ) ^ 2 ≤ 32 * (m : ℝ) * a := by
      have hcast : (Fintype.card V : ℝ) * Fintype.card V ≤
          32 * (G.edgeFinset.card : ℝ) * a := by
        exact_mod_cast hdensity
      simpa only [n, m, pow_two] using hcast
    change (1 / 64 : ℝ) ≤ ((m : ℝ) / (n : ℝ) ^ 2) * a
    rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hnR)]
    nlinarith
  · have hdom := card_le_indepBound_add_twice_edges G a hind
    have hnm : n ≤ 4 * m := by
      dsimp only [n, m] at hdom ha ⊢
      omega
    have hna : n < 16 * a := by omega
    have hnmR : (n : ℝ) ≤ 4 * m := by exact_mod_cast hnm
    have hnaR : (n : ℝ) < 16 * a := by exact_mod_cast hna
    change (1 / 64 : ℝ) ≤ ((m : ℝ) / (n : ℝ) ^ 2) * a
    rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hnR)]
    nlinarith

/-- In the large-order branch the canonical low-pattern set is a proper
subset of the vertex set, so recursion strictly decreases the order. -/
theorem sparseLowPatternSet_card_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D b : ℕ)
    (hn : 2 ≤ Fintype.card V)
    (hdegreeCut : 4 * G.edgeFinset.card ≤
      Fintype.card V * (D + 1)) :
    (sparseLowPatternSet G D b).card < Fintype.card V := by
  classical
  let P := lowDegreeFinset G D
  let I := sparseIndependentSet G D
  let W := lowPatternFinset G P I b
  have hIspec : I ⊆ P ∧ G.IsIndepSet I ∧ IndepBoundOn G P I.card := by
    simpa [I, P, sparseIndependentSet] using
      Classical.choose_spec (exists_maximum_independent_subset G P)
  have hPcard : Fintype.card V / 2 ≤ P.card :=
    half_card_le_lowDegreeFinset G D hdegreeCut
  have hPpos : 0 < P.card := by omega
  have hIpos : 0 < I.card := by
    simpa only [I, P] using sparseIndependentSet_card_pos G D hPpos
  have hpart := low_high_pattern_partition G P I hIspec.1 b
  change W.card + (highPatternFinset G P I b).card + I.card = P.card at hpart
  have hPupper : P.card ≤ Fintype.card V := Finset.card_le_univ P
  have hWlt : W.card < Fintype.card V := by omega
  simpa [W, I, P, sparseLowPatternSet] using hWlt

/-- If the order drops by a factor of at most nine while the edge count
drops by a factor greater than one thousand, then the edge density drops
by a factor of at least ten. -/
theorem density_ratio_le_one_tenth
    (n n' m m' : ℕ) (hn : 0 < n) (hn' : 0 < n')
    (hm : 0 < m) (hnle : n ≤ 9 * n') (hmle : 1000 * m' < m) :
    (((m' : ℝ) / (n' : ℝ) ^ 2) /
      ((m : ℝ) / (n : ℝ) ^ 2)) ≤ 1 / 10 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn'R : (0 : ℝ) < n' := by exact_mod_cast hn'
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnleR : (n : ℝ) ≤ 9 * n' := by exact_mod_cast hnle
  have hmleR : (1000 : ℝ) * m' < m := by exact_mod_cast hmle
  have hsq : (n : ℝ) ^ 2 ≤ 81 * (n' : ℝ) ^ 2 := by
    calc
      (n : ℝ) ^ 2 ≤ (9 * (n' : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hnR.le hnleR 2
      _ = 81 * (n' : ℝ) ^ 2 := by ring
  have hmweak : (810 : ℝ) * m' ≤ m := by
    calc
      (810 : ℝ) * m' ≤ 1000 * m' := by
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ m := hmleR.le
  have hcross : 10 * ((m' : ℝ) * n ^ 2) ≤ m * (n' : ℝ) ^ 2 := by
    calc
      10 * ((m' : ℝ) * n ^ 2) ≤ 10 * (m' * (81 * (n' : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsq (by positivity)) (by norm_num)
      _ = (810 * m') * (n' : ℝ) ^ 2 := by ring
      _ ≤ m * (n' : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hmweak (by positivity)
  have hratio : (((m' : ℝ) / (n' : ℝ) ^ 2) /
      ((m : ℝ) / (n : ℝ) ^ 2)) =
      ((m' : ℝ) * n ^ 2) / (m * (n' : ℝ) ^ 2) := by
    field_simp
  rw [hratio]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < m * (n' : ℝ) ^ 2)
    (by norm_num : (0 : ℝ) < 10)]
  norm_num
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hcross

/-- Losing at most a factor nine in order loses less than seven in the
logarithm. -/
theorem log_sub_seven_le_of_le_nine
    (n n' : ℕ) (hn : 0 < n) (hn' : 0 < n') (h : n ≤ 9 * n') :
    Real.log (n : ℝ) - 7 ≤ Real.log (n' : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn'R : (0 : ℝ) < n' := by exact_mod_cast hn'
  have hR : (n : ℝ) ≤ 9 * n' := by exact_mod_cast h
  have hmono := Real.strictMonoOn_log.monotoneOn hnR
    (by positivity : (0 : ℝ) < 9 * n') hR
  rw [Real.log_mul (by norm_num : (9 : ℝ) ≠ 0) hn'R.ne'] at hmono
  have hlogThree := Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≠ 1)
  have hlogNine : Real.log (9 : ℝ) < 7 := by
    have heq : Real.log (9 : ℝ) =
        Real.log (3 : ℝ) + Real.log (3 : ℝ) := by
      rw [← Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
        (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
    rw [heq]
    linarith
  linarith

/-- The analytic payload of the low-core branch: a tenfold density drop
preserves the logarithmic hypothesis and increases the induction
potential. -/
theorem sparse_density_drop_transfer
    (n n' m m' a : ℕ)
    (hn : 0 < n) (hn' : 0 < n') (hm : 0 < m) (hm' : 0 < m')
    (ha : 0 < a)
    (hdsmall : (m : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 10 ^ (20 : ℕ))
    (hlogn : 100 ≤ Real.log (n : ℝ))
    (hy : 20 ≤ Real.log (1 / ((m : ℝ) / (n : ℝ) ^ 2)))
    (hA : 0 < ((m : ℝ) / (n : ℝ) ^ 2) * a)
    (hlogCondition :
      ((m : ℝ) / (n : ℝ) ^ 2) * a *
          Real.log (1 / ((m : ℝ) / (n : ℝ) ^ 2)) ≤
        Real.log (n : ℝ) / 10000000000000000)
    (hq : (((m' : ℝ) / (n' : ℝ) ^ 2) /
      ((m : ℝ) / (n : ℝ) ^ 2)) ≤ 1 / 10)
    (hxx' : Real.log (n : ℝ) - 7 ≤ Real.log (n' : ℝ)) :
    (m' : ℝ) / (n' : ℝ) ^ 2 ≤ 1 / 10 ^ (20 : ℕ) ∧
      ((m' : ℝ) / (n' : ℝ) ^ 2) * a *
          Real.log (1 / ((m' : ℝ) / (n' : ℝ) ^ 2)) ≤
        Real.log (n' : ℝ) / 10000000000000000 ∧
      sparsePotential n m a ≤ sparsePotential n' m' a := by
  let d : ℝ := (m : ℝ) / (n : ℝ) ^ 2
  let d' : ℝ := (m' : ℝ) / (n' : ℝ) ^ 2
  let q : ℝ := d' / d
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn'R : (0 : ℝ) < n' := by exact_mod_cast hn'
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm'R : (0 : ℝ) < m' := by exact_mod_cast hm'
  have hd : 0 < d := div_pos hmR (sq_pos_of_pos hnR)
  have hd' : 0 < d' := div_pos hm'R (sq_pos_of_pos hn'R)
  have hqpos : 0 < q := div_pos hd' hd
  have hq' : q ≤ 1 / 10 := by simpa only [q, d', d] using hq
  have hd'Eq : d' = q * d := by
    dsimp only [q]
    rw [div_mul_cancel₀ d' hd.ne']
  have hd'small : d' ≤ 1 / 10 ^ (20 : ℕ) := by
    rw [hd'Eq]
    have hq1 : q ≤ 1 := hq'.trans (by norm_num)
    calc
      q * d ≤ 1 * d := mul_le_mul_of_nonneg_right hq1 hd.le
      _ = d := one_mul d
      _ ≤ 1 / 10 ^ (20 : ℕ) := by simpa only [d] using hdsmall
  have hy' : Real.log (1 / d') =
      Real.log (1 / d) + Real.log (1 / q) := by
    rw [hd'Eq]
    simp only [one_div, mul_inv_rev]
    rw [Real.log_mul (inv_ne_zero hd.ne') (inv_ne_zero hqpos.ne')]
  have hA' : d' * (a : ℝ) = q * (d * a) := by rw [hd'Eq]; ring
  have hlog' : d' * a * Real.log (1 / d') ≤
      Real.log n' / 10000000000000000 := by
    rw [hA', hy']
    exact sparse_log_condition_of_density_drop hlogn hy hqpos hq'
      hxx' (by simpa only [d] using hlogCondition)
  have ht : (10 : ℝ) ≤ 1 / q := by
    rw [le_div_iff₀ hqpos]
    calc
      10 * q ≤ 10 * (1 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hq' (by norm_num)
      _ = 1 := by norm_num
  have hcomp := sparse_low_log_comparison hlogn hy hA
    (by simpa only [d] using hlogCondition) ht hxx'
  have hpot : sparsePotential n m a ≤ sparsePotential n' m' a := by
    rw [sparsePotential_eq_exp_log n m a hn hm ha,
      sparsePotential_eq_exp_log n' m' a hn' hm' ha]
    apply Real.exp_le_exp.mpr
    have hgoal : Real.log n / 2 +
        Real.log n / (1000000000000 * (d * a)) -
        4 * Real.log (1 / d) - 1000 ≤
      Real.log n' / 2 +
        Real.log n' / (1000000000000 * (d' * a)) -
        4 * Real.log (1 / d') - 1000 := by
      rw [hy', hA']
      have hfrac : Real.log n' / (1000000000000 * (q * (d * a))) =
          (1 / q) * Real.log n' / (1000000000000 * (d * a)) := by
        field_simp
      rw [hfrac]
      linarith
    simpa only [d, d', mul_assoc] using hgoal
  exact ⟨by simpa only [d'] using hd'small,
    by simpa only [d'] using hlog', hpot⟩

/-- The `a > n/16` boundary is closed directly by the topological-density
theorem. -/
theorem sparse_boundary_potential_lt
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a k : ℕ)
    (hn : 0 < Fintype.card V) (hm : 0 < G.edgeFinset.card) (ha : 0 < a)
    (hlogn : 100 ≤ Real.log (Fintype.card V : ℝ))
    (hdle : (G.edgeFinset.card : ℝ) /
      (Fintype.card V : ℝ) ^ 2 ≤ 1)
    (halarge : (Fintype.card V : ℝ) < 16 * a)
    (hedgeLarge : (1 : ℝ) ≤
      (((G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ^ 2) ^ 2) *
        Fintype.card V)
    (hk : 2 ≤ k) (hnot : ¬Erdos718.ContainsCliqueSubdivision G k) :
    sparsePotential (Fintype.card V) G.edgeFinset.card a < k := by
  have hbound := five_mul_card_mul_sparsePotential_sq_lt_edges
    (Fintype.card V) G.edgeFinset.card a hn hm ha hlogn hdle halarge hedgeLarge
  by_contra hnotPot
  have hkPot : (k : ℝ) ≤
      sparsePotential (Fintype.card V) G.edgeFinset.card a := le_of_not_gt hnotPot
  have hpotNonneg : 0 ≤ sparsePotential
      (Fintype.card V) G.edgeFinset.card a := by
    simp only [sparsePotential]
    positivity
  have hkSq : (k : ℝ) ^ 2 ≤
      (sparsePotential (Fintype.card V) G.edgeFinset.card a) ^ 2 :=
    (sq_le_sq₀ (by positivity) hpotNonneg).mpr hkPot
  have hedgeReal : (5 : ℝ) * ((k : ℝ) * k) * Fintype.card V ≤
      G.edgeFinset.card := by
    calc
      (5 : ℝ) * ((k : ℝ) * k) * Fintype.card V =
          5 * Fintype.card V * (k : ℝ) ^ 2 := by ring
      _ ≤ 5 * Fintype.card V *
          (sparsePotential (Fintype.card V) G.edgeFinset.card a) ^ 2 :=
        mul_le_mul_of_nonneg_left hkSq (by positivity)
      _ ≤ G.edgeFinset.card := hbound.le
  have hedgeNat : 5 * (k * k) * Fintype.card V ≤ G.edgeFinset.card := by
    exact_mod_cast hedgeReal
  exact hnot
    (Erdos717.ThomasWollanMassed.containsCliqueSubdivision_of_five_mul_sq_mul_card_le_edges
      G k hn hedgeNat)

/-- The Fox--Lee--Sudakov sparse induction in potential form.  The
subdivision order `k` is arbitrary; the assertion says that every graph
with no topological `K_k` has potential strictly below `k`. -/
theorem sparse_graph_potential_lt_forbidden_order
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a k : ℕ) (hind : G.indepNum ≤ a)
    (ha : 2 * a ≤ Fintype.card V)
    (hdsmall :
      (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ^ 2 ≤
        1 / 10 ^ (20 : ℕ))
    (hlogCondition :
      ((G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ^ 2) * a *
          Real.log (1 / ((G.edgeFinset.card : ℝ) /
            (Fintype.card V : ℝ) ^ 2)) ≤
        Real.log (Fintype.card V : ℝ) / 10000000000000000)
    (hk : 2 ≤ k) (hnot : ¬Erdos718.ContainsCliqueSubdivision G k) :
    sparsePotential (Fintype.card V) G.edgeFinset.card a < k := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (W : Type) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj],
      Fintype.card W = n →
      J.indepNum ≤ a →
      2 * a ≤ Fintype.card W →
      (J.edgeFinset.card : ℝ) / (Fintype.card W : ℝ) ^ 2 ≤
        1 / 10 ^ (20 : ℕ) →
      ((J.edgeFinset.card : ℝ) / (Fintype.card W : ℝ) ^ 2) * a *
          Real.log (1 / ((J.edgeFinset.card : ℝ) /
            (Fintype.card W : ℝ) ^ 2)) ≤
        Real.log (Fintype.card W : ℝ) / 10000000000000000 →
      ¬Erdos718.ContainsCliqueSubdivision J k →
      sparsePotential (Fintype.card W) J.edgeFinset.card a < k
  have hmain : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      dsimp only [P]
      intro W _ _ J _ hnCard hindJ haJ hdsmallJ hlogJ hnotJ
      let m := J.edgeFinset.card
      by_cases hnzero : n = 0
      · have haZero : a = 0 := by
          rw [hnCard, hnzero] at haJ
          omega
        have hcardZero : Fintype.card W = 0 := hnCard.trans hnzero
        have hmZero : J.edgeFinset.card = 0 := by
          have hedge : J.edgeFinset.card ≤ 0 := by
            calc
              J.edgeFinset.card ≤ (Fintype.card W).choose 2 :=
                J.card_edgeFinset_le_card_choose_two
              _ = 0 := by rw [hcardZero]; simp
          exact Nat.eq_zero_of_le_zero hedge
        have hpotZero :
            sparsePotential (Fintype.card W) J.edgeFinset.card a = 0 := by
          simp [sparsePotential, hcardZero, hmZero, haZero]
        rw [hpotZero]
        exact_mod_cast (show 0 < k by omega)
      have hn0 : 0 < n := Nat.pos_of_ne_zero hnzero
      have hnW : 0 < Fintype.card W := by simpa only [hnCard] using hn0
      have haPos : 0 < a := by
        let v : W := Classical.choice (Fintype.card_pos_iff.mp hnW)
        have hsingle : J.IsIndepSet ({v} : Finset W) := by simp
        have := hsingle.card_le_indepNum.trans hindJ
        exact Nat.zero_lt_of_lt this
      have hmPos : 0 < m := by
        have hdom := card_le_indepBound_add_twice_edges J a hindJ
        by_contra hm
        have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm
        change Fintype.card W ≤ a + 2 * m at hdom
        rw [hmzero] at hdom
        omega
      let d : ℝ := (m : ℝ) / (n : ℝ) ^ 2
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      have hmR : (0 : ℝ) < m := by exact_mod_cast hmPos
      have haR : (0 : ℝ) < a := by exact_mod_cast haPos
      have hd : 0 < d := by positivity
      have hdsmall' : d ≤ 1 / 10 ^ (20 : ℕ) := by
        simpa only [d, m, hnCard] using hdsmallJ
      have hdle : d ≤ 1 := hdsmall'.trans (by norm_num)
      have hA : (1 / 64 : ℝ) ≤ d * a := by
        simpa only [d, m, hnCard] using
          one_div_sixtyfour_le_density_mul_indepBound
            J a hindJ hnW haJ
      by_cases hnsmall : n < 10 ^ 100
      · have hbase := sparsePotential_lt_one_of_order_small
          n m a hn0 hmPos haPos hA hdle hnsmall
        rw [hnCard]
        exact hbase.trans_le (by exact_mod_cast (show 1 ≤ k by omega))
      have hnHuge : 10 ^ 100 ≤ n := by omega
      have hlogn : 100 ≤ Real.log (n : ℝ) := by
        have hcast : (10 : ℝ) ^ (100 : ℕ) ≤ n := by exact_mod_cast hnHuge
        have hmono := Real.strictMonoOn_log.monotoneOn
          (pow_pos (by norm_num : (0 : ℝ) < 10) _) hnR hcast
        rw [Real.log_pow] at hmono
        have hlogTen : 1 < Real.log (10 : ℝ) := by
          rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 10)]
          exact Real.exp_one_lt_three.trans (by norm_num)
        norm_num at hmono
        nlinarith only [hmono, hlogTen]
      have hy : 20 ≤ Real.log (1 / d) := by
        have hdinv : (10 : ℝ) ^ (20 : ℕ) ≤ 1 / d := by
          rw [le_div_iff₀ hd]
          nlinarith
        have hmono : Real.log ((10 : ℝ) ^ (20 : ℕ)) ≤
            Real.log (1 / d) :=
          Real.strictMonoOn_log.monotoneOn (by norm_num)
            (one_div_pos.mpr hd) hdinv
        rw [Real.log_pow] at hmono
        have hlogTen : 1 < Real.log (10 : ℝ) := by
          rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 10)]
          exact Real.exp_one_lt_three.trans (by norm_num)
        norm_num at hmono
        rw [one_div, Real.log_inv]
        nlinarith
      by_cases hedgeSmall : d ^ 2 * n < 5000000000
      · have hbase := sparsePotential_lt_one_of_edge_square_small
          n m a hn0 hmPos haPos hlogn hA hedgeSmall
        rw [hnCard]
        exact hbase.trans_le (by exact_mod_cast (show 1 ≤ k by omega))
      have hedgeLarge : (5000000000 : ℝ) ≤ d ^ 2 * n := le_of_not_gt hedgeSmall
      by_cases ha16 : 16 * a ≤ n
      · let D := degreeCutParameter m n
        let b := patternParameter D a n
        let H := sparseCore J D b
        let h := H.edgeSet.ncard
        have hdegreeCut : 4 * m ≤ n * (D + 1) := by
          simpa only [D] using degreeCutParameter_spec m n hn0
        have hpatternCut : 4 * D * a ≤ (b + 1) * n := by
          simpa only [b, mul_comm] using patternParameter_spec D a n hn0
        have hWcard : n / 8 ≤ (sparseLowPatternSet J D b).card := by
          simpa only [hnCard, m, D, b] using
            sparseLowPatternSet_card_lower J a D b hindJ
              (by simpa only [hnCard] using ha16)
              (by simpa only [hnCard, m] using hdegreeCut)
              (by simpa only [hnCard] using hpatternCut)
        by_cases hhigh : m ≤ 1000 * h
        · have hLlarge : 5000 * (n * n * n) ≤ h ^ 2 := by
            have hedgeEq : d ^ 2 * (n : ℝ) =
                ((m : ℝ) * m) / ((n : ℝ) * n * n) := by
              dsimp only [d]
              field_simp
            have hmn : (5000000000 : ℝ) * ((n : ℝ) * n * n) ≤
                (m : ℝ) * m := by
              rw [hedgeEq] at hedgeLarge
              rw [le_div_iff₀ (by positivity :
                (0 : ℝ) < (n : ℝ) * n * n)] at hedgeLarge
              exact hedgeLarge
            have hhighR : (m : ℝ) ≤ 1000 * h := by exact_mod_cast hhigh
            have hh : (5000 : ℝ) * ((n : ℝ) * n * n) ≤ (h : ℝ) ^ 2 := by
              nlinarith [sq_nonneg ((m : ℝ) - 1000 * h)]
            exact_mod_cast hh
          have hXlarge : 320 * n ≤ h := by
            by_contra hnotX
            have hlt : h < 320 * n := by omega
            have hltR : (h : ℝ) < 320 * n := by exact_mod_cast hlt
            have hLR : (5000 : ℝ) * ((n : ℝ) * n * n) ≤ h ^ 2 := by
              exact_mod_cast hLlarge
            have hn21 : (21 : ℝ) < n := by
              exact_mod_cast (lt_of_lt_of_le (by norm_num : 21 < 10 ^ 100) hnHuge)
            nlinarith [sq_nonneg ((h : ℝ) - 320 * n)]
          have hlogWeak : d * a * Real.log (1 / d) ≤
              Real.log n / 1000000 := by
            have hstrong : d * a * Real.log (1 / d) ≤
                Real.log n / 10000000000000000 := by
              simpa only [d, m, hnCard] using hlogJ
            have hlogNonneg : 0 ≤ Real.log (n : ℝ) := by
              exact Real.log_nonneg (by exact_mod_cast
                (Nat.one_le_iff_ne_zero.mpr hn0.ne'))
            nlinarith
          have hhigh' : J.edgeSet.ncard ≤ 1000 * H.edgeSet.ncard := by
            rw [← Erdos718.MaderPrototype.card_edgeFinset_eq_ncard_edgeSet]
            simpa only [m, h, H] using hhigh
          have hresult := sparse_high_step_potential J a k hindJ
            (by simpa only [hnCard] using ha16)
            (by simpa only [hnCard] using hnHuge)
            hdsmallJ
            (by simpa only [d, m, hnCard] using hlogWeak)
            (by simpa only [h, H, b, D, m, hnCard] using hhigh')
            (by simpa only [h, H, b, D, m, hnCard] using hXlarge)
            (by simpa only [h, H, b, D, m, hnCard] using hLlarge)
            hk hnotJ
          exact hresult
        · have hlow : 1000 * h < m := by omega
          let U := sparseLowPatternSet J D b
          let J' := J.induce (U : Set W)
          let n' := Fintype.card (U : Set W)
          let m' := J'.edgeFinset.card
          have hn'Eq : n' = U.card := by simp [n']
          have hn'Lower : n / 8 ≤ n' := by simpa only [hn'Eq, U] using hWcard
          have hn'Pos : 0 < n' := by
            have hn8 : 8 ≤ n := (by norm_num : 8 ≤ 10 ^ 100).trans hnHuge
            have : 0 < n / 8 := Nat.div_pos hn8 (by norm_num)
            omega
          have hhalf' : 2 * a ≤ n' := by
            have haDiv : 2 * a ≤ n / 8 := by
              rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 8)]
              nlinarith
            exact haDiv.trans hn'Lower
          have hind' : J'.indepNum ≤ a := by
            exact (indepNum_induce_finset_le J U).trans hindJ
          have hm'Pos : 0 < m' := by
            have hdom := card_le_indepBound_add_twice_edges J' a hind'
            by_contra hm'
            have hm'zero : m' = 0 := Nat.eq_zero_of_not_pos hm'
            change n' ≤ a + 2 * m' at hdom
            rw [hm'zero] at hdom
            omega
          have hm'Eq : m' = h := by
            simpa only [m', J', U, h, H] using
              card_edgeFinset_induce_sparseLowPatternSet J D b
          have hn'Lt : n' < n := by
            have hnTwo : 2 ≤ Fintype.card W := by
              rw [hnCard]
              exact (by omega)
            have := sparseLowPatternSet_card_lt J D b hnTwo
              (by simpa only [hnCard, m] using hdegreeCut)
            simpa only [n', hn'Eq, U, hnCard] using this
          have hnLe : n ≤ 9 * n' := by
            have hn56 : 56 ≤ n := (by norm_num : 56 ≤ 10 ^ 100).trans hnHuge
            omega
          let d' : ℝ := (m' : ℝ) / (n' : ℝ) ^ 2
          have hq : d' / d ≤ 1 / 10 := by
            have hlow' : 1000 * m' < m := by simpa only [hm'Eq] using hlow
            simpa only [d', d] using
              density_ratio_le_one_tenth n n' m m' hn0 hn'Pos hmPos hnLe hlow'
          have hxx' : Real.log n - 7 ≤ Real.log n' :=
            log_sub_seven_le_of_le_nine n n' hn0 hn'Pos hnLe
          have hlogStrong : d * a * Real.log (1 / d) ≤
              Real.log n / 10000000000000000 := by
            simpa only [d, m, hnCard] using hlogJ
          obtain ⟨hd'small, hlog', hpotLe⟩ := sparse_density_drop_transfer
            n n' m m' a hn0 hn'Pos hmPos hm'Pos haPos hdsmall'
            hlogn hy (lt_of_lt_of_le (by norm_num) hA) hlogStrong
            (by simpa only [d', d] using hq) hxx'
          have hnot' : ¬Erdos718.ContainsCliqueSubdivision J' k := by
            intro hsub
            exact hnotJ hsub.liftInduce
          have hrec := ih n' hn'Lt (U : Set W) J' rfl hind'
            (by simpa only [n'] using hhalf')
            (by simpa only [d', m', n'] using hd'small)
            (by simpa only [d', m', n'] using hlog') hnot'
          rw [hnCard]
          exact hpotLe.trans_lt hrec
      · have halarge : (n : ℝ) < 16 * a := by
          exact_mod_cast (show n < 16 * a by omega)
        exact sparse_boundary_potential_lt J a k hnW
          (by simpa only [m] using hmPos) haPos
          (by simpa only [hnCard] using hlogn)
          (by simpa only [d, m, hnCard] using hdle)
          (by simpa only [hnCard] using halarge)
          (by simpa only [d, m, hnCard] using
            (show (1 : ℝ) ≤ d ^ 2 * n by nlinarith))
          hk hnotJ
  exact hmain (Fintype.card V) V G rfl hind ha hdsmall hlogCondition hnot

end Erdos717
