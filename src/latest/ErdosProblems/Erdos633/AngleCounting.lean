import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# The angle-counting obstruction in Erdős problem 633

This file proves the finite counting lemma independently of planar geometry.
The counts and local equations are extracted from actual geometric tilings in
`LocalAngleLedger` and applied to this lemma in `ActualAngleCounting`.
-/

namespace Erdos633

open scoped BigOperators

/-- The precise independence hypothesis used when extracting integer corner
counts from an equality of angles. -/
def IntegerIndependentAngles (α β : ℝ) : Prop :=
  ∀ x y : ℤ, (x : ℝ) * α + (y : ℝ) * β = 0 → x = 0 ∧ y = 0

/-- The local equations when the outer corners contain only the first label.
The equation `m * α = total` is kept separate from positivity or geometry. -/
theorem single_outer_local_equations {α β γ total : ℝ}
    (hind : IntegerIndependentAngles α β) (m k a b g : ℕ) (hm : 1 ≤ m)
    (hsum : α + β + γ = total) (houter : (m : ℝ) * α = total)
    (hlocal : a * α + b * β + g * γ = k * total) :
    a + (m - 1) * g = m * k ∧ b = g := by
  have hm' : m = (m - 1) + 1 := by omega
  have hrel : γ = ((m - 1 : ℕ) : ℝ) * α - β := by
    rw [hm'] at houter
    push_cast at houter
    linear_combination hsum - houter
  have hz : (((a : ℤ) + (m - 1 : ℕ) * g - m * k : ℤ) : ℝ) * α +
      (((b : ℤ) - g : ℤ) : ℝ) * β = 0 := by
    push_cast
    linear_combination hlocal - (g : ℝ) * hrel - (k : ℝ) * houter
  obtain ⟨hx, hy⟩ := hind _ _ hz
  constructor
  · exact_mod_cast sub_eq_zero.mp hx
  · exact_mod_cast sub_eq_zero.mp hy

/-- Derive the local counting equations from actual real angle equalities.
Here `k` is one for a flat vertex and two for a full vertex. -/
theorem local_corner_equations {α β γ total : ℝ}
    (hind : IntegerIndependentAngles α β) (p q k a b g : ℕ)
    (hsum : α + β + γ = total)
    (hrel : γ = p * α + q * β)
    (hlocal : a * α + b * β + g * γ = k * total) :
    a + p * g = (p + 1) * k ∧ b + q * g = (q + 1) * k := by
  have htotal : total = ((p : ℝ) + 1) * α + ((q : ℝ) + 1) * β := by
    rw [← hsum, hrel]
    ring
  have hz : (((a : ℤ) + p * g - (p + 1) * k : ℤ) : ℝ) * α +
      (((b : ℤ) + q * g - (q + 1) * k : ℤ) : ℝ) * β = 0 := by
    push_cast
    linear_combination hlocal - (g : ℝ) * hrel + (k : ℝ) * htotal
  obtain ⟨hx, hy⟩ := hind _ _ hz
  constructor
  · exact_mod_cast sub_eq_zero.mp hx
  · exact_mod_cast sub_eq_zero.mp hy

/-- Local nonnegative corner counts exclude more than `k` obtuse-angle
corners when the relation coefficient is at least three and `k ≤ 2`. -/
theorem corner_count_le {p k a g : ℕ} (hp : 3 ≤ p) (hk : k ≤ 2)
    (h : a + p * g = (p + 1) * k) : g ≤ k := by
  by_contra hg
  have hkg : k + 1 ≤ g := by omega
  have hmul := Nat.mul_le_mul_left p hkg
  nlinarith

/-- One coefficient in a one-negative angle relation cannot exceed two.
The three outer corners contribute `p + 1` corners of the first label and
zero of the third label. `A` and `G` are their nonouter totals. -/
theorem angle_relation_coefficient_le_two {ι : Type*} [Fintype ι]
    (p N : ℕ) (a g k : ι → ℕ)
    (hk : ∀ i, k i ≤ 2)
    (hlocal : ∀ i, a i + p * g i = (p + 1) * k i)
    (ha : (∑ i, a i) + (p + 1) = N)
    (hg : (∑ i, g i) = N) : p ≤ 2 := by
  by_contra hp
  have hp3 : 3 ≤ p := by omega
  have hle : (∑ i, g i) ≤ ∑ i, k i := by
    exact Finset.sum_le_sum fun i _ => corner_count_le hp3 (hk i) (hlocal i)
  have hsum := congrArg (fun f : ι → ℕ => ∑ i, f i) (funext hlocal)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  nlinarith

/-- Both coefficients in the one-negative relation are at most two. -/
theorem angle_relation_coefficients_le_two {ι : Type*} [Fintype ι]
    (p q N : ℕ) (a b g k : ι → ℕ)
    (hk : ∀ i, k i ≤ 2)
    (haLocal : ∀ i, a i + p * g i = (p + 1) * k i)
    (hbLocal : ∀ i, b i + q * g i = (q + 1) * k i)
    (ha : (∑ i, a i) + (p + 1) = N)
    (hb : (∑ i, b i) + (q + 1) = N)
    (hg : (∑ i, g i) = N) : p ≤ 2 ∧ q ≤ 2 := by
  exact ⟨angle_relation_coefficient_le_two p N a g k hk haLocal ha hg,
    angle_relation_coefficient_le_two q N b g k hk hbLocal hb hg⟩

/-- The coefficient obstruction with real angle sums as input, rather than
assuming the coefficient equations themselves. -/
theorem angle_relation_bound_of_angle_sums {ι : Type*} [Fintype ι]
    {α β γ total : ℝ} (hind : IntegerIndependentAngles α β)
    (p q N : ℕ) (a b g k : ι → ℕ)
    (hsum : α + β + γ = total) (hrel : γ = p * α + q * β)
    (hk : ∀ i, k i ≤ 2)
    (hlocal : ∀ i, a i * α + b i * β + g i * γ = k i * total)
    (ha : (∑ i, a i) + (p + 1) = N)
    (hb : (∑ i, b i) + (q + 1) = N)
    (hg : (∑ i, g i) = N) : p ≤ 2 ∧ q ≤ 2 := by
  have heq := fun i => local_corner_equations hind p q (k i) (a i) (b i) (g i)
    hsum hrel (hlocal i)
  exact angle_relation_coefficients_le_two p q N a b g k hk
    (fun i => (heq i).1) (fun i => (heq i).2) ha hb hg

/-- Three nonempty rows whose three column sums are one form a permutation
matrix. This is the finite combinatorial content of the all-positive case. -/
theorem corner_matrix_is_permutation (c : Fin 3 → Fin 3 → ℕ)
    (hcol : ∀ k, ∑ j, c j k = 1) (hrow : ∀ j, ∃ k, 0 < c j k) :
    ∃ e : Equiv.Perm (Fin 3), ∀ j k, c j k = if e j = k then 1 else 0 := by
  classical
  have hle (j k : Fin 3) : c j k ≤ 1 := by
    calc
      _ ≤ ∑ i : Fin 3, c i k := Finset.single_le_sum (fun i _ => Nat.zero_le (c i k))
        (Finset.mem_univ j)
      _ = 1 := hcol k
  have hzero (k i j : Fin 3) (hij : i ≠ j) (hi : 0 < c i k) : c j k = 0 := by
    have hpair : c i k + c j k ≤ ∑ l : Fin 3, c l k :=
      Finset.add_le_sum (fun l _ => Nat.zero_le (c l k))
        (Finset.mem_univ i) (Finset.mem_univ j) hij
    rw [hcol k] at hpair
    omega
  choose f hf using hrow
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hi := hf i
    have hj := hf j
    rw [← hij] at hj
    have hz := hzero (f i) i j hne hi
    omega
  let e : Equiv.Perm (Fin 3) :=
    Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, rfl⟩)
  refine ⟨e, ?_⟩
  intro j k
  by_cases hjk : e j = k
  · rw [if_pos hjk]
    have hj := hf j
    change f j = k at hjk
    rw [hjk] at hj
    have hjle := hle j k
    omega
  · rw [if_neg hjk]
    let i := e.symm k
    have hi : 0 < c i k := by
      have h := hf i
      have he : f i = k := e.apply_symm_apply k
      rwa [he] at h
    have hij : i ≠ j := by
      intro h
      apply hjk
      rw [← h]
      exact e.apply_symm_apply k
    exact hzero k i j hij hi

end Erdos633
