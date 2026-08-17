import Mathlib

/-!
# The density calculation in the Füredi--Naor--Verstraëte construction

This file isolates the real-arithmetic part of the affine lower construction.
The graph-theoretic input is deliberately represented by a hypothesis in the
last theorem.  Thus none of the results below assert the existence of the
finite-geometric graph before that input has been supplied.

For `q = 2^(2a+1)`, the affine graph has `N = q^3` vertices and
`(q^4-q^2)/2` edges.  Cloning a set of
`K = floor ((sqrt 5 - 2) N)` vertices gives, by averaging, the edge lower
bound recorded in `fnvLower`.  We prove directly (with rational bounds, rather
than asymptotic notation) that this lower bound is greater than
`(2669/5000) n^(4/3)` once `a ≥ 3`.
-/

namespace Erdos59

/-- The prime-power parameter used by the affine FNV construction. -/
def fnvQ (a : ℕ) : ℕ := 2 ^ (2 * a + 1)

/-- The number of vertices in the affine base graph. -/
def fnvN (a : ℕ) : ℕ := fnvQ a ^ 3

/-- The number of vertices cloned in the FNV construction. -/
noncomputable def fnvK (a : ℕ) : ℕ :=
  Nat.floor ((Real.sqrt 5 - 2) * fnvN a)

/-- The number of vertices after cloning. -/
noncomputable def fnvVertices (a : ℕ) : ℕ := fnvN a + fnvK a

/-- The exact number of edges in the affine base graph, viewed in `ℝ`. -/
noncomputable def fnvBaseEdges (a : ℕ) : ℝ :=
  ((fnvQ a : ℝ) ^ 4 - (fnvQ a : ℝ) ^ 2) / 2

/--
The lower bound delivered by the averaging argument.  An old edge acquires
an extra copy with probability
`(K/N) * (2 - (K-1)/(N-1))`.
-/
noncomputable def fnvLower (a : ℕ) : ℝ :=
  fnvBaseEdges a *
    (1 + (fnvK a : ℝ) / fnvN a *
      (2 - ((fnvK a : ℝ) - 1) / ((fnvN a : ℝ) - 1)))

theorem fnv_lower_formula (a : ℕ) :
    fnvLower a = fnvBaseEdges a *
      (1 + (fnvK a : ℝ) / fnvN a *
        (2 - ((fnvK a : ℝ) - 1) / ((fnvN a : ℝ) - 1))) := rfl

private lemma sqrt_five_lower :
    (2360679 / 10000000 : ℝ) < Real.sqrt 5 - 2 := by
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by norm_num
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith [hs]

private lemma sqrt_five_upper :
    Real.sqrt 5 - 2 < (236068 / 1000000 : ℝ) := by
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by norm_num
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith [hs]

private lemma rpow_four_thirds_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ^ 4 ≤ y ^ 3) : x ^ (4 / 3 : ℝ) ≤ y := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hy
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num
  simpa [Real.rpow_natCast] using h

private lemma fnvQ_ge_128 {a : ℕ} (ha : 3 ≤ a) : 128 ≤ fnvQ a := by
  rw [fnvQ, show 128 = 2 ^ 7 by norm_num]
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).2 (by omega)

private lemma fnvN_ge_threshold {a : ℕ} (ha : 3 ≤ a) : 2097152 ≤ fnvN a := by
  rw [fnvN]
  exact Nat.pow_le_pow_left (fnvQ_ge_128 ha) 3

private lemma fnvK_ratio_lower {a : ℕ} (ha : 3 ≤ a) :
    (236067 / 1000000 : ℝ) ≤ (fnvK a : ℝ) / fnvN a := by
  have hNnat := fnvN_ge_threshold ha
  have hN : (2097152 : ℝ) ≤ fnvN a := by exact_mod_cast hNnat
  have hNpos : (0 : ℝ) < fnvN a := by exact_mod_cast (show 0 < fnvN a by
    simp [fnvN, fnvQ])
  have hfloor : (Real.sqrt 5 - 2) * (fnvN a : ℝ) < (fnvK a : ℝ) + 1 := by
    exact Nat.lt_floor_add_one _
  have hs := sqrt_five_lower
  rw [le_div_iff₀ hNpos]
  nlinarith [mul_pos (sub_pos.mpr hs) hNpos]

private lemma fnvK_ratio_upper (a : ℕ) :
    (fnvK a : ℝ) / fnvN a ≤ (236068 / 1000000 : ℝ) := by
  have hNpos : (0 : ℝ) < fnvN a := by
    exact_mod_cast (show 0 < fnvN a by simp [fnvN, fnvQ])
  have hs : 0 ≤ Real.sqrt 5 - 2 := by
    have hs2 : (2 : ℝ) ≤ Real.sqrt 5 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg 5]
    linarith
  have hfloor : (fnvK a : ℝ) ≤
      (Real.sqrt 5 - 2) * (fnvN a : ℝ) := by
    exact Nat.floor_le (mul_nonneg hs (by positivity))
  rw [div_le_iff₀ hNpos]
  nlinarith [sqrt_five_upper, mul_pos hNpos (sub_pos.mpr sqrt_five_upper)]

private lemma fnvK_le_N (a : ℕ) : fnvK a ≤ fnvN a := by
  have hNpos : (0 : ℝ) < fnvN a := by
    exact_mod_cast (show 0 < fnvN a by simp [fnvN, fnvQ])
  have hu := fnvK_ratio_upper a
  rw [div_le_iff₀ hNpos] at hu
  exact_mod_cast (show (fnvK a : ℝ) ≤ fnvN a by nlinarith)

private lemma fnv_sampling_factor_lower {a : ℕ} (ha : 3 ≤ a) :
    (1 + (236067 / 1000000 : ℝ) * (2 - 236068 / 1000000)) ≤
      1 + (fnvK a : ℝ) / fnvN a *
        (2 - ((fnvK a : ℝ) - 1) / ((fnvN a : ℝ) - 1)) := by
  have hNnat := fnvN_ge_threshold ha
  have hN : (1 : ℝ) < fnvN a := by exact_mod_cast (show 1 < fnvN a by omega)
  have hKle : (fnvK a : ℝ) ≤ fnvN a := by exact_mod_cast fnvK_le_N a
  have hratio : ((fnvK a : ℝ) - 1) / ((fnvN a : ℝ) - 1) ≤
      (fnvK a : ℝ) / fnvN a := by
    rw [div_le_div_iff₀ (sub_pos.mpr hN) (by positivity : (0 : ℝ) < fnvN a)]
    nlinarith
  have hlo := fnvK_ratio_lower ha
  have hup := fnvK_ratio_upper a
  have hright : (0 : ℝ) ≤
      2 - ((fnvK a : ℝ) - 1) / ((fnvN a : ℝ) - 1) := by
    nlinarith
  have hconst : (0 : ℝ) ≤ 2 - 236068 / 1000000 := by norm_num
  nlinarith [mul_le_mul hlo (by nlinarith :
      (2 - 236068 / 1000000 : ℝ) ≤
        2 - ((fnvK a : ℝ) - 1) / ((fnvN a : ℝ) - 1)) hconst
      (by positivity : (0 : ℝ) ≤ (fnvK a : ℝ) / fnvN a)]

private lemma fnv_base_edges_lower {a : ℕ} (ha : 3 ≤ a) :
    ((1 - 1 / (128 : ℝ) ^ 2) / 2) * (fnvQ a : ℝ) ^ 4 ≤
      fnvBaseEdges a := by
  have hq : (128 : ℝ) ≤ fnvQ a := by exact_mod_cast fnvQ_ge_128 ha
  have hq0 : (0 : ℝ) ≤ fnvQ a := by positivity
  rw [fnvBaseEdges]
  have hq2 : (128 : ℝ) ^ 2 ≤ (fnvQ a : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hq 2
  nlinarith [sq_nonneg ((fnvQ a : ℝ) ^ 2 - 128 ^ 2)]

private lemma fnv_vertices_rpow_upper (a : ℕ) :
    (fnvVertices a : ℝ) ^ (4 / 3 : ℝ) ≤
      (132655 / 100000 : ℝ) * (fnvQ a : ℝ) ^ 4 := by
  let Q : ℝ := fnvQ a
  let x : ℝ := fnvVertices a
  let y : ℝ := (132655 / 100000 : ℝ) * Q ^ 4
  have hQ : 0 ≤ Q := by positivity
  have hNpos : (0 : ℝ) < fnvN a := by
    exact_mod_cast (show 0 < fnvN a by simp [fnvN, fnvQ])
  have hK := fnvK_ratio_upper a
  rw [div_le_iff₀ hNpos] at hK
  have hx : x ≤ (1236068 / 1000000 : ℝ) * Q ^ 3 := by
    dsimp [x, Q, fnvVertices]
    push_cast
    rw [fnvN, Nat.cast_pow] at hK ⊢
    nlinarith
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by positivity
  apply rpow_four_thirds_le hx0 hy0
  calc
    x ^ 4 ≤ ((1236068 / 1000000 : ℝ) * Q ^ 3) ^ 4 :=
      pow_le_pow_left₀ hx0 hx 4
    _ = (1236068 / 1000000 : ℝ) ^ 4 * Q ^ 12 := by ring
    _ ≤ (132655 / 100000 : ℝ) ^ 3 * Q ^ 12 := by
      gcongr
      norm_num
    _ = y ^ 3 := by dsimp [y]; ring

/-- The full FNV arithmetic estimate, including the floor and affine error. -/
theorem fnvLower_gt {a : ℕ} (ha : 3 ≤ a) :
    fnvLower a > (2669 / 5000 : ℝ) *
      (fnvVertices a : ℝ) ^ (4 / 3 : ℝ) := by
  have hb := fnv_base_edges_lower ha
  have hf := fnv_sampling_factor_lower ha
  have hp := fnv_vertices_rpow_upper a
  have hbase : 0 ≤ fnvBaseEdges a := by
    rw [fnvBaseEdges]
    have hq : (1 : ℝ) ≤ fnvQ a := by
      exact_mod_cast (show 1 ≤ fnvQ a by
        exact Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (by norm_num)))
    have hpow : (fnvQ a : ℝ) ^ 2 ≤ (fnvQ a : ℝ) ^ 4 :=
      pow_le_pow_right₀ hq (by omega)
    linarith
  have hfactor : 0 ≤
      1 + (fnvK a : ℝ) / fnvN a *
        (2 - ((fnvK a : ℝ) - 1) / ((fnvN a : ℝ) - 1)) := by
    exact hf.trans' (by norm_num)
  have hQpos : (0 : ℝ) < (fnvQ a : ℝ) ^ 4 := by
    positivity [show 0 < fnvQ a by simp [fnvQ]]
  have hc :
      ((1 - 1 / (128 : ℝ) ^ 2) / 2) *
          (1 + (236067 / 1000000 : ℝ) * (2 - 236068 / 1000000)) >
        (2669 / 5000 : ℝ) * (132655 / 100000) := by norm_num
  rw [fnvLower]
  calc
    fnvBaseEdges a *
          (1 + (fnvK a : ℝ) / fnvN a *
            (2 - ((fnvK a : ℝ) - 1) / ((fnvN a : ℝ) - 1)))
        ≥ (((1 - 1 / (128 : ℝ) ^ 2) / 2) * (fnvQ a : ℝ) ^ 4) *
          (1 + (236067 / 1000000 : ℝ) * (2 - 236068 / 1000000)) := by
            exact mul_le_mul hb hf (by norm_num) hbase
    _ = (((1 - 1 / (128 : ℝ) ^ 2) / 2) *
          (1 + (236067 / 1000000 : ℝ) * (2 - 236068 / 1000000))) *
          (fnvQ a : ℝ) ^ 4 := by ring
    _ > ((2669 / 5000 : ℝ) * (132655 / 100000)) *
          (fnvQ a : ℝ) ^ 4 := mul_lt_mul_of_pos_right hc hQpos
    _ ≥ (2669 / 5000 : ℝ) *
          (fnvVertices a : ℝ) ^ (4 / 3 : ℝ) := by
            nlinarith

private lemma fnvVertices_unbounded :
    ∀ M : ℕ, ∃ a : ℕ, M ≤ fnvVertices a ∧ 3 ≤ a := by
  intro M
  refine ⟨M + 3, ?_, by omega⟩
  have hMq : M < fnvQ (M + 3) := by
    apply lt_of_le_of_lt (show M ≤ 2 * (M + 3) + 1 by omega)
    simpa [fnvQ] using (2 * (M + 3) + 1).lt_two_pow_self
  have hqN : fnvQ (M + 3) ≤ fnvN (M + 3) := by
    rw [fnvN]
    exact le_self_pow₀ (show 1 ≤ fnvQ (M + 3) by
      exact Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (by norm_num))) (by norm_num)
  exact le_trans hMq.le (hqN.trans (Nat.le_add_right _ _))

/--
The arithmetic lower bounds occur at unbounded vertex counts.  This is the
explicit `∀ M, ∃ n ≥ M` interpretation of "infinitely often".
-/
theorem fnvLower_infinitely_often :
    ∀ M : ℕ, ∃ a : ℕ, M ≤ fnvVertices a ∧
      fnvLower a > (2669 / 5000 : ℝ) *
        (fnvVertices a : ℝ) ^ (4 / 3 : ℝ) := by
  intro M
  obtain ⟨a, hM, ha⟩ := fnvVertices_unbounded M
  exact ⟨a, hM, fnvLower_gt ha⟩

/--
Graph-free adapter for a construction theorem.  `Good n e` can state, for
example, that a graph on `n` vertices with `e` edges is triangle- and
hexagon-free.  The existence of such objects remains an explicit hypothesis.
-/
theorem fnv_construction_infinitely_often
    (Good : ℕ → ℕ → Prop)
    (hconstruction : ∀ a : ℕ, ∃ e : ℕ,
      Good (fnvVertices a) e ∧ fnvLower a ≤ e) :
    ∀ M : ℕ, ∃ n e : ℕ, M ≤ n ∧ Good n e ∧
      (e : ℝ) > (2669 / 5000 : ℝ) * (n : ℝ) ^ (4 / 3 : ℝ) := by
  intro M
  obtain ⟨a, hM, ha⟩ := fnvLower_infinitely_often M
  obtain ⟨e, hgood, he⟩ := hconstruction a
  exact ⟨fnvVertices a, e, hM, hgood, lt_of_lt_of_le ha he⟩

end Erdos59
