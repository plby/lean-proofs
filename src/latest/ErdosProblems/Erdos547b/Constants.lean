/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Tactic

/-!
# Quantitative bookkeeping for Zhao's theorem

This file contains only the constant and natural-number arithmetic used after
the three structural theorems in Section 3 of Zhao's proof have been proved.
The scale `k` is the number of edges of the tree.  Thus Zhao's even host has
order `2 * k`; for a tree on `n` vertices the Ramsey specialization is
`k = n - 1` and the host order is `2 * n - 2`.

No asymptotic notation occurs here.  The separation between successive
regularity parameters is witnessed by a fixed rational factor `100`; any
finite list of strict rational constraints can be accommodated by increasing
that factor before choosing the final natural-number threshold.
-/

namespace ZhaoConstants547

/-- The same hierarchy with an arbitrary rational separation factor. -/
def RationalHierarchyBelowWith
    (K cap ε γ d η ρ α : ℚ) : Prop :=
  0 < ε ∧
  K * ε < γ ∧
  K * γ < d ∧
  K * d < η ∧
  K * η < ρ ∧
  K * ρ < α ∧
  α ≤ cap ∧
  α < 1

/-- A concrete rational replacement for
`0 < ε ≪ γ ≪ d ≪ η ≪ ρ ≪ α`, with an external upper bound on `α`.

The factor `100` is not asserted to encode every estimate in the analytic
part of Zhao's proof.  It gives a reusable finite quantitative hierarchy for
the Section 3 constant selection: the proof-specific estimates may replace
`100` by any fixed factor. -/
def RationalHierarchyBelow
    (cap ε γ d η ρ α : ℚ) : Prop :=
  RationalHierarchyBelowWith 100 cap ε γ d η ρ α

/-- For any prescribed finite multiplicative separation `K > 0`, a positive
rational cap admits a six-level hierarchy.  This is the precise finitary
content of choosing the constants from right to left after all estimates have
been listed: take the divisor `K + 1` at every step. -/
theorem exists_rationalHierarchyBelowWith (K cap : ℚ)
    (hK : 0 < K) (hcap : 0 < cap) :
    ∃ ε γ d η ρ α : ℚ, RationalHierarchyBelowWith K cap ε γ d η ρ α := by
  let α : ℚ := min cap (1 / 2)
  let S : ℚ := K + 1
  let ρ : ℚ := α / S
  let η : ℚ := ρ / S
  let d : ℚ := η / S
  let γ : ℚ := d / S
  let ε : ℚ := γ / S
  have hα : 0 < α := lt_min hcap (by norm_num)
  have hS : 0 < S := by dsimp [S]; linarith
  have hαcap : α ≤ cap := min_le_left _ _
  have hαone : α < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨ε, γ, d, η, ρ, α, ?_⟩
  dsimp [RationalHierarchyBelowWith]
  constructor
  · dsimp [ε, γ, d, η, ρ]
    positivity
  constructor
  · dsimp [ε, γ, d, η, ρ]
    field_simp
    nlinarith
  constructor
  · dsimp [γ, d, η, ρ]
    field_simp
    nlinarith
  constructor
  · dsimp [d, η, ρ]
    field_simp
    nlinarith
  constructor
  · dsimp [η, ρ]
    field_simp
    nlinarith
  constructor
  · dsimp [ρ]
    field_simp
    nlinarith
  exact ⟨hαcap, hαone⟩

/-- Every positive rational cap admits a completely explicit six-level
constant hierarchy below both the cap and `1`.

The construction first sets `α = min cap (1/2)` and then divides successively
by `1000`.  Consequently every requested factor-`100` separation is strict. -/
theorem exists_rationalHierarchyBelow (cap : ℚ) (hcap : 0 < cap) :
    ∃ ε γ d η ρ α : ℚ, RationalHierarchyBelow cap ε γ d η ρ α := by
  exact exists_rationalHierarchyBelowWith 100 cap (by norm_num) hcap

/-- The only error parameter needed to assemble Zhao's dense, sparse, and
stability theorems is the minimum of the two positive extremal tolerances. -/
theorem min_extremal_parameter {c α₂ : ℚ} (hc : 0 < c) (hα₂ : 0 < α₂) :
    0 < min c α₂ ∧ min c α₂ ≤ c ∧ min c α₂ ≤ α₂ := by
  exact ⟨lt_min hc hα₂, min_le_left _ _, min_le_right _ _⟩

/-- The full regularity hierarchy can be chosen below both extremal constants
returned by Proposition 3.1 and Theorem 3.2. -/
theorem exists_rationalHierarchyBelow_extremal_min
    (K c α₂ : ℚ) (hK : 0 < K) (hc : 0 < c) (hα₂ : 0 < α₂) :
    ∃ ε γ d η ρ α : ℚ,
      RationalHierarchyBelowWith K (min c α₂) ε γ d η ρ α ∧
      α ≤ c ∧ α ≤ α₂ := by
  rcases exists_rationalHierarchyBelowWith K (min c α₂) hK (lt_min hc hα₂) with
    ⟨ε, γ, d, η, ρ, α, hHierarchy⟩
  refine ⟨ε, γ, d, η, ρ, α, hHierarchy, ?_, ?_⟩
  · exact hHierarchy.2.2.2.2.2.2.1.trans (min_le_left c α₂)
  · exact hHierarchy.2.2.2.2.2.2.1.trans (min_le_right c α₂)

/-- At `σ = 1/2`, the threshold `2σk` in Proposition 3.1 is exactly `k`. -/
theorem dense_sigma_half_threshold (k : ℕ) :
    (2 : ℚ) * (1 / 2) * k = k := by
  norm_num

/-- A graph with at least `k` high-degree vertices meets the weaker
`(1-ε)k` hypothesis in the stability theorem whenever `ε ≥ 0`. -/
theorem stability_threshold_of_strong_threshold
    (ε : ℚ) (hε : 0 ≤ ε) (k highCount : ℕ) (hhigh : k ≤ highCount) :
    (1 - ε) * k ≤ highCount := by
  have hk : (0 : ℚ) ≤ k := by positivity
  have hweak : (1 - ε) * k ≤ k := by nlinarith
  exact hweak.trans (by exact_mod_cast hhigh)

/-- Three eventual thresholds are simultaneously met at their maximum. -/
theorem thresholds_at_max (n₁ n₂ n₃ n : ℕ)
    (hn : max n₁ (max n₂ n₃) ≤ n) : n₁ ≤ n ∧ n₂ ≤ n ∧ n₃ ≤ n := by
  omega

/- Abstract predicates for the conclusion and the two extremal alternatives.
They make the Section 3 quantifier calculation independent of graph encoding. -/
variable {State : ℕ → Type*}
variable (Good : (k : ℕ) → State k → Prop)
variable (EC₁ EC₂ : ℚ → (k : ℕ) → State k → Prop)

/-- Proposition 3.1 in precisely the form used by the final assembly. -/
def DenseStructuralProperty : Prop :=
  ∃ c : ℚ, 0 < c ∧ c < 1 ∧ ∃ n₁ : ℕ,
    ∀ k : ℕ, n₁ ≤ k → ∀ X : State k, EC₁ c k X → Good k X

/-- Theorem 3.2 in precisely the form used by the final assembly. -/
def SparseStructuralProperty : Prop :=
  ∃ α₂ : ℚ, 0 < α₂ ∧ α₂ < 1 ∧ ∃ n₂ : ℕ,
    ∀ α : ℚ, 0 < α → α ≤ α₂ → ∀ k : ℕ, n₂ ≤ k →
      ∀ X : State k, EC₂ α k X → Good k X

/-- Theorem 3.3 in the disjunctive stability form used by Theorem 1.6. -/
def StabilityStructuralProperty : Prop :=
  ∀ α : ℚ, 0 < α → ∃ n₃ : ℕ, ∀ k : ℕ, n₃ ≤ k →
    ∀ X : State k, Good k X ∨ EC₁ α k X ∨ EC₂ α k X

/-- Monotonicity convention for the dense extremal case: a smaller error
parameter is a stronger density conclusion, and hence implies the case at a
larger error parameter. -/
def DenseCaseMonotone : Prop :=
  ∀ {α β : ℚ}, α ≤ β → ∀ {k : ℕ} {X : State k}, EC₁ α k X → EC₁ β k X

/-- The corresponding monotonicity convention for the sparse extremal case. -/
def SparseCaseMonotone : Prop :=
  ∀ {α β : ℚ}, α ≤ β → ∀ {k : ℕ} {X : State k}, EC₂ α k X → EC₂ β k X

/-- Exact Section 3 assembly.  No rounding, limiting argument, or hidden
choice of constants remains: choose `α = min c α₂` and the maximum threshold. -/
theorem eventual_good_of_structural_theorems
    (hDense : DenseStructuralProperty Good EC₁)
    (hSparse : SparseStructuralProperty Good EC₂)
    (hStability : StabilityStructuralProperty Good EC₁ EC₂)
    (hEC₁ : DenseCaseMonotone EC₁) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ X : State k, Good k X := by
  rcases hDense with ⟨c, hc, _hc_one, n₁, hn₁⟩
  rcases hSparse with ⟨α₂, hα₂, _hα₂_one, n₂, hn₂⟩
  let α : ℚ := min c α₂
  have hα : 0 < α := lt_min hc hα₂
  rcases hStability α hα with ⟨n₃, hn₃⟩
  refine ⟨max n₁ (max n₂ n₃), ?_⟩
  intro k hk X
  have h₁ : n₁ ≤ k := (thresholds_at_max n₁ n₂ n₃ k hk).1
  have h₂ : n₂ ≤ k := (thresholds_at_max n₁ n₂ n₃ k hk).2.1
  have h₃ : n₃ ≤ k := (thresholds_at_max n₁ n₂ n₃ k hk).2.2
  rcases hn₃ k h₃ X with hgood | hcase₁ | hcase₂
  · exact hgood
  · exact hn₁ k h₁ X (hEC₁ (min_le_left c α₂) hcase₁)
  · exact hn₂ α hα (min_le_right c α₂) k h₂ X hcase₂

/-! ## Exact even-host and Ramsey-host arithmetic -/

/-- Natural-number ceiling of half, in the convention used in the main file. -/
def ceilHalf (M : ℕ) : ℕ := (M + 1) / 2

/-- Natural-number floor of half. -/
def floorHalf (M : ℕ) : ℕ := M / 2

/-- The even host order for a `k`-edge tree. -/
def evenHostOrder (k : ℕ) : ℕ := 2 * k

/-- The Ramsey host order for a tree on `n` vertices. -/
def ramseyHostOrder (n : ℕ) : ℕ := 2 * n - 2

/-- The number of edges in a tree on `n` vertices. -/
def ramseyTreeEdges (n : ℕ) : ℕ := n - 1

@[simp] theorem floorHalf_evenHostOrder (k : ℕ) :
    floorHalf (evenHostOrder k) = k := by
  simp [floorHalf, evenHostOrder]

@[simp] theorem ceilHalf_evenHostOrder (k : ℕ) :
    ceilHalf (evenHostOrder k) = k := by
  simp [ceilHalf, evenHostOrder]
  omega

/-- On an odd host of order `2k-1`, the degree threshold in Theorem 1.6 is
`k`.  This is the parity case reduced to order `2k` by adjoining one isolated
vertex in Zhao's proof. -/
@[simp] theorem ceilHalf_two_mul_sub_one (k : ℕ) (hk : 1 ≤ k) :
    ceilHalf (2 * k - 1) = k := by
  simp [ceilHalf]
  omega

/-- The tree-edge allowance on the same odd host is `k-1`. -/
@[simp] theorem floorHalf_two_mul_sub_one (k : ℕ) (hk : 1 ≤ k) :
    floorHalf (2 * k - 1) = k - 1 := by
  simp [floorHalf]
  omega

/-- Adding one vertex to an odd host gives the even host used by the
structural theorems. -/
theorem oddHostOrder_succ (k : ℕ) (hk : 1 ≤ k) :
    (2 * k - 1) + 1 = evenHostOrder k := by
  simp [evenHostOrder]
  omega

/-- Universal floor bound for natural-number halving. -/
theorem two_mul_floorHalf_le (M : ℕ) : 2 * floorHalf M ≤ M := by
  simp [floorHalf]
  omega

/-- Universal strict upper bound dual to `two_mul_floorHalf_le`. -/
theorem lt_two_mul_floorHalf_add_one (M : ℕ) :
    M < 2 * (floorHalf M + 1) := by
  simp [floorHalf]
  omega

/-- Universal lower bound for the ceiling convention `(M+1)/2`. -/
theorem le_two_mul_ceilHalf (M : ℕ) : M ≤ 2 * ceilHalf M := by
  simp [ceilHalf]
  omega

/-- The doubled ceiling exceeds the host order by at most one. -/
theorem two_mul_ceilHalf_le_add_one (M : ℕ) :
    2 * ceilHalf M ≤ M + 1 := by
  simp [ceilHalf]
  omega

/-- Ceiling and floor agree or differ by exactly one. -/
theorem ceilHalf_eq_floorHalf_or_succ (M : ℕ) :
    ceilHalf M = floorHalf M ∨ ceilHalf M = floorHalf M + 1 := by
  simp [ceilHalf, floorHalf]
  omega

/-- Reindexing an `n`-vertex tree by its `n-1` edges gives exactly the Ramsey
host order, including at `n = 0`; both sides use truncated subtraction. -/
theorem evenHostOrder_pred_eq_ramseyHostOrder (n : ℕ) :
    evenHostOrder (ramseyTreeEdges n) = ramseyHostOrder n := by
  simp [evenHostOrder, ramseyTreeEdges, ramseyHostOrder]
  omega

@[simp] theorem floorHalf_ramseyHostOrder (n : ℕ) :
    floorHalf (ramseyHostOrder n) = ramseyTreeEdges n := by
  simp [floorHalf, ramseyHostOrder, ramseyTreeEdges]
  omega

@[simp] theorem ceilHalf_ramseyHostOrder (n : ℕ) :
    ceilHalf (ramseyHostOrder n) = ramseyTreeEdges n := by
  simp [ceilHalf, ramseyHostOrder, ramseyTreeEdges]
  omega

/-- The two rounded halves agree on every Ramsey host. -/
theorem ceilHalf_eq_floorHalf_ramseyHostOrder (n : ℕ) :
    ceilHalf (ramseyHostOrder n) = floorHalf (ramseyHostOrder n) := by
  simp

/-- Passing a threshold on the edge scale to the vertex-order scale costs
exactly one. -/
theorem edge_threshold_of_vertex_threshold (k₀ n : ℕ)
    (hn : k₀ + 1 ≤ n) : k₀ ≤ ramseyTreeEdges n := by
  simp [ramseyTreeEdges]
  omega

/-- Exact threshold shift from the structural scale to tree order. -/
theorem edge_threshold_at_shift (k₀ : ℕ) :
    ramseyTreeEdges (k₀ + 1) = k₀ := by
  simp [ramseyTreeEdges]

/-- Every eventual statement on the `k`-edge scale yields the corresponding
eventual statement for trees on `n` vertices by taking `k = n - 1`. -/
theorem eventually_pred_of_eventually_edges {P : ℕ → Prop}
    (hP : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → P k) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → P (ramseyTreeEdges n) := by
  rcases hP with ⟨k₀, hk₀⟩
  refine ⟨k₀ + 1, ?_⟩
  intro n hn
  exact hk₀ _ (edge_threshold_of_vertex_threshold k₀ n hn)

/-- A deliberately loose but simple threshold converting eventuality in the
host order `M` to eventuality in the Ramsey tree order `n`. -/
theorem host_threshold_of_tree_threshold (M₀ n : ℕ)
    (hn : M₀ + 2 ≤ n) : M₀ ≤ ramseyHostOrder n := by
  simp [ramseyHostOrder]
  omega

/-- Strict version, useful when a source theorem says `M > M₀`. -/
theorem host_strict_threshold_of_tree_threshold (M₀ n : ℕ)
    (hn : M₀ + 2 ≤ n) : M₀ < ramseyHostOrder n := by
  simp [ramseyHostOrder]
  omega

/-- An eventual host-order assertion specializes to Ramsey hosts, with all
ceiling/floor arithmetic exposed by the preceding simp lemmas. -/
theorem eventually_pred_on_ramsey_hosts {P : ℕ → Prop}
    (hP : ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → P M) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → P (ramseyHostOrder n) := by
  rcases hP with ⟨M₀, hM₀⟩
  refine ⟨M₀ + 2, ?_⟩
  intro n hn
  exact hM₀ _ (host_threshold_of_tree_threshold M₀ n hn)

/-- The complete abstract bridge from Zhao's three structural theorems at
scale `k` to the vertex-order formulation used for Erdős 547. -/
theorem eventual_good_on_ramsey_scale_of_structural_theorems
    (hDense : DenseStructuralProperty Good EC₁)
    (hSparse : SparseStructuralProperty Good EC₂)
    (hStability : StabilityStructuralProperty Good EC₁ EC₂)
    (hEC₁ : DenseCaseMonotone EC₁) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ X : State (ramseyTreeEdges n), Good (ramseyTreeEdges n) X := by
  exact eventually_pred_of_eventually_edges
    (P := fun k => ∀ X : State k, Good k X)
    (eventual_good_of_structural_theorems Good EC₁ EC₂
      hDense hSparse hStability hEC₁)

#print axioms exists_rationalHierarchyBelow
#print axioms exists_rationalHierarchyBelowWith
#print axioms min_extremal_parameter
#print axioms eventual_good_of_structural_theorems
#print axioms evenHostOrder_pred_eq_ramseyHostOrder
#print axioms floorHalf_ramseyHostOrder
#print axioms ceilHalf_ramseyHostOrder
#print axioms ceilHalf_two_mul_sub_one
#print axioms floorHalf_two_mul_sub_one
#print axioms ceilHalf_eq_floorHalf_or_succ
#print axioms eventually_pred_of_eventually_edges
#print axioms eventually_pred_on_ramsey_hosts
#print axioms eventual_good_on_ramsey_scale_of_structural_theorems

end ZhaoConstants547
