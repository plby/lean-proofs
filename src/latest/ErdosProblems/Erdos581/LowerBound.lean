import ErdosProblems.Erdos581.DenseCore
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Erdős 581: the uniform lower bound

This file combines the stable-cut estimate, the peeling dichotomy, and the
dense-core sampler at the threshold `floor (m^(2/5))`.
-/

open Finset Set
open scoped BigOperators

namespace Erdos581

private lemma sqrt_rpow_two_fifths (m : ℕ) :
    Real.sqrt ((m : ℝ) ^ ((2 : ℝ) / 5)) =
      (m : ℝ) ^ ((1 : ℝ) / 5) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg m)]
  congr 1
  norm_num

private lemma rpow_four_fifths_mul_one_fifth {m : ℕ} (hm : 0 < m) :
    (m : ℝ) ^ ((4 : ℝ) / 5) * (m : ℝ) ^ ((1 : ℝ) / 5) = m := by
  rw [← Real.rpow_add (by positivity : (0 : ℝ) < m)]
  norm_num

private lemma div_sqrt_rpow_two_fifths {m : ℕ} (hm : 0 < m) :
    (m : ℝ) / Real.sqrt ((m : ℝ) ^ ((2 : ℝ) / 5)) =
      (m : ℝ) ^ ((4 : ℝ) / 5) := by
  rw [sqrt_rpow_two_fifths]
  have hpos : 0 < (m : ℝ) ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos (by positivity) _
  rw [div_eq_iff hpos.ne']
  simpa [mul_comm] using (rpow_four_fifths_mul_one_fifth (m := m) hm).symm

private lemma rpow_two_fifths_sq (m : ℕ) :
    ((m : ℝ) ^ ((2 : ℝ) / 5)) ^ 2 =
      (m : ℝ) ^ ((4 : ℝ) / 5) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m)]
  norm_num

private lemma floor_two_fifths_pos {m : ℕ} (hm : 0 < m) :
    0 < ⌊(m : ℝ) ^ ((2 : ℝ) / 5)⌋₊ := by
  have hx : (1 : ℝ) ≤ (m : ℝ) ^ ((2 : ℝ) / 5) := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    exact Real.one_le_rpow hm1 (by norm_num)
  have hfloor : 1 ≤ ⌊(m : ℝ) ^ ((2 : ℝ) / 5)⌋₊ :=
    (Nat.le_floor_iff' (R := ℝ) one_ne_zero).2 (by simpa using hx)
  omega

private lemma floor_two_fifths_le {m : ℕ} :
    (⌊(m : ℝ) ^ ((2 : ℝ) / 5)⌋₊ : ℝ) ≤
      (m : ℝ) ^ ((2 : ℝ) / 5) := by
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg m) _)

private lemma floor_sq_bonus {m : ℕ} (hm : 0 < m) :
    ((m : ℝ) ^ ((4 : ℝ) / 5)) / 1024 ≤
      (⌊(m : ℝ) ^ ((2 : ℝ) / 5)⌋₊ : ℝ) ^ 2 / 200 := by
  let x : ℝ := (m : ℝ) ^ ((2 : ℝ) / 5)
  let D : ℕ := ⌊x⌋₊
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    exact Real.one_le_rpow hm1 (by norm_num)
  have hD1 : (1 : ℝ) ≤ D := by
    exact_mod_cast floor_two_fifths_pos hm
  have hxfloor : x < (D : ℝ) + 1 := Nat.lt_floor_add_one x
  have hxpow : x ^ 2 = (m : ℝ) ^ ((4 : ℝ) / 5) := by
    simpa [x] using rpow_two_fifths_sq m
  rw [← hxpow]
  by_cases hx2 : x < 2
  · have hxnonneg : 0 ≤ x := le_trans (by norm_num) hx1
    have hxsq : x ^ 2 < 4 := by nlinarith
    have hDsq : 1 ≤ (D : ℝ) ^ 2 := by nlinarith
    nlinarith
  · have hx2' : 2 ≤ x := le_of_not_gt hx2
    have hhalf : x / 2 ≤ (D : ℝ) := by nlinarith
    have hxnonneg : 0 ≤ x := hx2'.trans' (by norm_num)
    have hDnonneg : 0 ≤ (D : ℝ) := by positivity
    nlinarith [sq_nonneg (x / 2 - (D : ℝ))]

private theorem exists_cut_extending_induced_set
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (A : Set T) :
    ∃ s : Set V,
      (G.edgeFinset.card : ℝ) / 2 +
          ((cutGraph (G.induce (T : Set V)) A).edgeSet.ncard : ℝ) -
          ((G.induce (T : Set V)).edgeFinset.card : ℝ) / 2 ≤
        ((cutGraph G s).edgeSet.ncard : ℝ) := by
  classical
  let Af : Finset T := Finset.univ.filter fun v ↦ v ∈ A
  have hAf : (Af : Set T) = A := by
    ext v
    simp [Af]
  obtain ⟨s, hs⟩ := exists_cut_extending_induced G T Af
  refine ⟨s, ?_⟩
  have hcard : (cutGraph (G.induce (T : Set V)) A).edgeSet.ncard =
      (cutGraph (G.induce (T : Set V)) A).edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have hfin : inducedCutEdges G T Af =
      (cutGraph (G.induce (T : Set V)) A).edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
        simp [inducedCutEdges, hAf, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet]
  rw [hfin] at hs
  rw [hcard]
  exact hs

/-- Uniform graph-level lower bound, with an explicit absolute constant. -/
theorem exists_cut_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (htri : G.CliqueFree 3) :
    ∃ s : Set V,
      (G.edgeFinset.card : ℝ) / 2 +
          (G.edgeFinset.card : ℝ) ^ ((4 : ℝ) / 5) / 1024 ≤
        ((cutGraph G s).edgeSet.ncard : ℝ) := by
  classical
  let m := G.edgeFinset.card
  by_cases hm0 : m = 0
  · refine ⟨∅, ?_⟩
    simp [m, hm0, Real.zero_rpow (by norm_num : (4 : ℝ) / 5 ≠ 0)]
  have hm : 0 < m := Nat.pos_of_ne_zero hm0
  let D : ℕ := ⌊(m : ℝ) ^ ((2 : ℝ) / 5)⌋₊
  have hD : 0 < D := by simpa [D] using floor_two_fifths_pos hm
  rcases core_or_sum_sqrt_degree G D hD with hcore | hpeel
  · obtain ⟨T, hT, hmin⟩ := hcore
    let K := G.induce (T : Set V)
    have htriK : K.CliqueFree 3 := by
      rw [SimpleGraph.cliqueFree_induce_iff]
      exact htri.cliqueFreeOn
    have hminK : ∀ v, D ≤ K.degree v := by
      intro v
      rw [degree_induce_finset]
      exact hmin v.1 v.2
    obtain ⟨A, hA⟩ := exists_cut_denseCore K hD hT.to_subtype htriK hminK
    obtain ⟨s, hs⟩ := exists_cut_extending_induced_set G T A
    refine ⟨s, ?_⟩
    have hbonus := floor_sq_bonus hm
    change (m : ℝ) / 2 + (m : ℝ) ^ ((4 : ℝ) / 5) / 1024 ≤ _
    change ((K.edgeFinset.card : ℝ) / 2 + (D : ℝ) ^ 2 / 200 ≤
      ((cutGraph K A).edgeSet.ncard : ℝ)) at hA
    change (m : ℝ) / 2 + ((cutGraph K A).edgeSet.ncard : ℝ) -
      (K.edgeFinset.card : ℝ) / 2 ≤ _ at hs
    simpa [D, m] using (le_trans (by nlinarith [hA, hbonus]) hs)
  · obtain ⟨s, hs⟩ := exists_cut_sqrtDegree G htri
    refine ⟨s, ?_⟩
    have hDle : (D : ℝ) ≤ (m : ℝ) ^ ((2 : ℝ) / 5) := by
      simpa [D] using floor_two_fifths_le (m := m)
    have hsqrtle : Real.sqrt (D : ℝ) ≤
        Real.sqrt ((m : ℝ) ^ ((2 : ℝ) / 5)) := Real.sqrt_le_sqrt hDle
    have hsqrtD : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hD)
    have hdiv : (m : ℝ) /
          Real.sqrt ((m : ℝ) ^ ((2 : ℝ) / 5)) ≤
        (m : ℝ) / Real.sqrt D := by
      exact div_le_div_of_nonneg_left (by positivity) hsqrtD hsqrtle
    have hpowSum : (m : ℝ) ^ ((4 : ℝ) / 5) ≤
        ∑ v, Real.sqrt (G.degree v : ℝ) := by
      calc
        (m : ℝ) ^ ((4 : ℝ) / 5) =
            (m : ℝ) / Real.sqrt ((m : ℝ) ^ ((2 : ℝ) / 5)) :=
              (div_sqrt_rpow_two_fifths hm).symm
        _ ≤ (m : ℝ) / Real.sqrt D := hdiv
        _ ≤ ∑ v, Real.sqrt (G.degree v : ℝ) := by simpa [m] using hpeel
    change (m : ℝ) / 2 + (m : ℝ) ^ ((4 : ℝ) / 5) / 1024 ≤ _
    change (m : ℝ) / 2 + (∑ v, Real.sqrt (G.degree v : ℝ)) / 32 ≤ _ at hs
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg m) ((4 : ℝ) / 5)]

/-- The lower half of the resolution of Erdős 581. -/
theorem lower_bound (m : ℕ) :
    (m : ℝ) / 2 + (m : ℝ) ^ ((4 : ℝ) / 5) / 1024 ≤ (f m : ℝ) := by
  classical
  let x : ℝ := (m : ℝ) / 2 + (m : ℝ) ^ ((4 : ℝ) / 5) / 1024
  let k : ℕ := ⌈x⌉₊
  have hguarantees : Guarantees m k := by
    intro V _ G htri hmG
    letI : DecidableEq V := Classical.decEq V
    letI : DecidableRel G.Adj := Classical.decRel _
    obtain ⟨s, hs⟩ := exists_cut_lower G htri
    have hmcard : G.edgeFinset.card = m := by
      calc
        G.edgeFinset.card = G.edgeSet.ncard := by
          rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
        _ = m := hmG
    refine ⟨cutGraph G s, cutGraph_le G s, cutGraph_isBipartite G s, ?_⟩
    exact (Nat.ceil_le (α := ℝ)).2 (by simpa [x, hmcard] using hs)
  have hkf : k ≤ f m := le_f_of_guarantees hguarantees
  calc
    (m : ℝ) / 2 + (m : ℝ) ^ ((4 : ℝ) / 5) / 1024 = x := rfl
    _ ≤ (k : ℝ) := Nat.le_ceil x
    _ ≤ (f m : ℝ) := by exact_mod_cast hkf

end Erdos581
