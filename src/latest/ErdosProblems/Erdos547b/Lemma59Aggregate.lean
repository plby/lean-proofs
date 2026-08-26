/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma59FullOnline

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma59FullOnline

open Finset Fintype SimpleGraph

/-! The finite allocation core of aggregate Zhao Lemma 5.9(2). -/

/-- Matching edges having positive density from a given level-one cluster to
at least one endpoint. -/
def allowedMatchingEdges
    {C K : Type*} [Fintype K] [DecidableEq K]
    (positive : C → K → Fin 2 → Prop) (C0 : C) : Finset K := by
  classical
  exact Finset.univ.filter fun e => ∃ s, positive C0 e s

/-- Endpoint incidences of positive density, the reduced-graph degree form
used in Claim 6.16. -/
def positiveMatchingSides
    {C K : Type*} [Fintype K] [DecidableEq K]
    (positive : C → K → Fin 2 → Prop) (C0 : C) : Finset (K × Fin 2) := by
  classical
  exact Finset.univ.filter fun p => positive C0 p.1 p.2

theorem card_positiveMatchingSides_le_twice_edges
    {C K : Type*} [Fintype K] [DecidableEq K]
    (positive : C → K → Fin 2 → Prop) (C0 : C) :
    #(positiveMatchingSides positive C0) ≤
      2 * #(allowedMatchingEdges positive C0) := by
  classical
  have hsub : positiveMatchingSides positive C0 ⊆
      (allowedMatchingEdges positive C0).product (Finset.univ : Finset (Fin 2)) := by
    rintro ⟨e, s⟩ hes
    have hp : positive C0 e s := (Finset.mem_filter.mp hes).2
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ e, ?_⟩, Finset.mem_univ s⟩
    exact ⟨s, hp⟩
  calc
    #(positiveMatchingSides positive C0) ≤
        #((allowedMatchingEdges positive C0).product
          (Finset.univ : Finset (Fin 2))) := card_le_card hsub
    _ = 2 * #(allowedMatchingEdges positive C0) := by simp [Nat.mul_comm]

/-- The reduced-degree estimate in Claim 6.16: `2m` positive matching-side
incidences ensure at least `m` usable matching edges. -/
theorem card_allowedMatchingEdges_ge_half_side_degree
    {C K : Type*} [Fintype K] [DecidableEq K]
    (positive : C → K → Fin 2 → Prop) (C0 : C) (m : ℕ)
    (hdegree : 2 * m ≤ #(positiveMatchingSides positive C0)) :
    m ≤ #(allowedMatchingEdges positive C0) := by
  have htwo := card_positiveMatchingSides_le_twice_edges positive C0
  omega

/-- Unit items fit arbitrary integral capacities without a per-bin loss. -/
theorem unit_capacity_packing
    {ι κ : Type*} [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (items : Finset ι) (capacity : κ → ℕ)
    (hbudget : #items ≤ ∑ j : κ, capacity j) :
    ∃ assign : ι → κ, ∀ j : κ,
      #(items.filter (assign · = j)) ≤ capacity j := by
  classical
  induction items using Finset.induction_on with
  | empty =>
      exact ⟨fun _ => Classical.choice inferInstance, by simp⟩
  | @insert x s hx ih =>
      have hbudget_s : #s ≤ ∑ j : κ, capacity j := by
        rw [card_insert_of_notMem hx] at hbudget
        omega
      obtain ⟨assign, hassign⟩ := ih hbudget_s
      let load : κ → ℕ := fun j => #(s.filter (assign · = j))
      have hload_sum : ∑ j : κ, load j = #s := by
        simpa only [load, card_eq_sum_ones] using
          (sum_fiberwise s assign (fun _ => 1))
      have hplace : ∃ j : κ, load j < capacity j := by
        by_contra h
        push Not at h
        have hsum : (∑ j : κ, capacity j) ≤ ∑ j : κ, load j :=
          sum_le_sum fun j _ => h j
        rw [hload_sum] at hsum
        rw [card_insert_of_notMem hx] at hbudget
        omega
      obtain ⟨j0, hj0⟩ := hplace
      let assign' : ι → κ := fun i => if i = x then j0 else assign i
      refine ⟨assign', ?_⟩
      intro j
      by_cases hj : j0 = j
      · subst j
        have hfilter : (insert x s).filter (assign' · = j0) =
            insert x (s.filter (assign · = j0)) := by
          ext i
          by_cases hi : i = x
          · subst i
            simp [assign']
          · simp [hi, assign']
        rw [hfilter, card_insert_of_notMem]
        · exact hj0
        · simp [hx]
      · have hfilter : (insert x s).filter (assign' · = j) =
            s.filter (assign · = j) := by
          ext i
          by_cases hi : i = x
          · subst i
            simp [assign', hj, hx]
          · simp [hi, assign']
        rw [hfilter]
        exact hassign j

/-- Allowed-bin packing for the matching stage. Every item has at least `m`
allowed matching edges. A total load at most `m * base` yields an allowed edge
of current load at most `base`; inserting one item costs at most `slack`.
This permits many branch components on one matching edge. -/
theorem allowed_capacity_packing
    {ι κ : Type*} [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (items : Finset ι) (weight : ι → ℕ)
    (allowed : ι → Finset κ) (m base slack : ℕ)
    (hmpos : 0 < m)
    (hallowed : ∀ i ∈ items, m ≤ #(allowed i))
    (hsmall : ∀ i ∈ items, weight i ≤ slack)
    (hbudget : ∑ i ∈ items, weight i ≤ m * base) :
    ∃ assign : ι → κ,
      (∀ i ∈ items, assign i ∈ allowed i) ∧
      ∀ j : κ,
        ∑ i ∈ items.filter (assign · = j), weight i ≤ base + slack := by
  classical
  induction items using Finset.induction_on with
  | empty =>
      exact ⟨fun _ => Classical.choice inferInstance, by simp, by simp⟩
  | @insert x s hx ih =>
      have hallowed_s : ∀ i ∈ s, m ≤ #(allowed i) := by
        intro i hi
        exact hallowed i (mem_insert_of_mem hi)
      have hsmall_s : ∀ i ∈ s, weight i ≤ slack := by
        intro i hi
        exact hsmall i (mem_insert_of_mem hi)
      have hbudget_s : ∑ i ∈ s, weight i ≤ m * base := by
        rw [sum_insert hx] at hbudget
        omega
      obtain ⟨assign, hassignAllowed, hassignLoad⟩ :=
        ih hallowed_s hsmall_s hbudget_s
      let load : κ → ℕ := fun j =>
        ∑ i ∈ s.filter (assign · = j), weight i
      have hload_sum : ∑ j : κ, load j = ∑ i ∈ s, weight i := by
        simpa only [load] using sum_fiberwise s assign weight
      have hxallowedCard : m ≤ #(allowed x) :=
        hallowed x (mem_insert_self x s)
      have hxallowed : (allowed x).Nonempty := by
        rw [nonempty_iff_ne_empty]
        intro he
        rw [he] at hxallowedCard
        simp at hxallowedCard
        omega
      have hplace : ∃ j ∈ allowed x, load j ≤ base := by
        by_contra h
        push Not at h
        have hall : ∀ j ∈ allowed x, base < load j := h
        have hsumLower : #(allowed x) * (base + 1) ≤
            ∑ j ∈ allowed x, load j := by
          calc
            #(allowed x) * (base + 1) =
                ∑ _j ∈ allowed x, (base + 1) := by simp
            _ ≤ ∑ j ∈ allowed x, load j := by
              exact sum_le_sum fun j hj => hall j hj
        have hsumSubset : (∑ j ∈ allowed x, load j) ≤ ∑ j : κ, load j := by
          exact sum_le_sum_of_subset (subset_univ _)
        rw [hload_sum] at hsumSubset
        have hmBaseLt : m * base < #(allowed x) * (base + 1) := by
          have hcardPos : 0 < #(allowed x) := hxallowed.card_pos
          nlinarith
        exact (not_lt_of_ge hbudget_s)
          (hmBaseLt.trans_le (hsumLower.trans hsumSubset))
      obtain ⟨j0, hj0Allowed, hj0Load⟩ := hplace
      let assign' : ι → κ := fun i => if i = x then j0 else assign i
      refine ⟨assign', ?_, ?_⟩
      · intro i hi
        by_cases hix : i = x
        · subst i
          simpa [assign'] using hj0Allowed
        · have his : i ∈ s := by simpa [hix] using hi
          simpa [assign', hix] using hassignAllowed i his
      · intro j
        by_cases hj : j0 = j
        · subst j
          have hfilter : (insert x s).filter (assign' · = j0) =
              insert x (s.filter (assign · = j0)) := by
            ext i
            by_cases hi : i = x
            · subst i
              simp [assign']
            · simp [hi, assign']
          rw [hfilter, sum_insert]
          · change weight x + load j0 ≤ base + slack
            exact Nat.add_le_add (hsmall x (mem_insert_self x s)) hj0Load |>.trans
              (by omega)
          · simp [hx]
        · have hfilter : (insert x s).filter (assign' · = j) =
              s.filter (assign · = j) := by
            ext i
            by_cases hi : i = x
            · subst i
              simp [assign', hj, hx]
            · simp [hi, assign']
          rw [hfilter]
          exact hassignLoad j

/-- The concrete assignment invariant consumed by the aggregate three-layer
embedding. -/
structure AggregateAllocation
    {ι C K : Type*} [DecidableEq ι] [Fintype C] [DecidableEq C]
    [DecidableEq K]
    (items : Finset ι) (weight : ι → ℕ)
    (clusterCapacity : C → ℕ) (allowedEdges : C → Finset K)
    (base slack : ℕ) where
  levelOneCluster : ι → C
  matchingEdge : ι → K
  cluster_load : ∀ C0 : C,
    #(items.filter (levelOneCluster · = C0)) ≤ clusterCapacity C0
  matching_allowed : ∀ i ∈ items,
    matchingEdge i ∈ allowedEdges (levelOneCluster i)
  matching_load : ∀ e : K,
    ∑ i ∈ items.filter (matchingEdge · = e), weight i ≤ base + slack

/-- The two displayed Lemma-5.9(2) budgets construct the full cluster and
allowed-matching-edge assignment. -/
theorem exists_aggregateAllocation
    {ι C K : Type*} [DecidableEq ι]
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype K] [DecidableEq K] [Nonempty K]
    (items : Finset ι) (weight : ι → ℕ)
    (clusterCapacity : C → ℕ) (allowedEdges : C → Finset K)
    (m base slack : ℕ) (hmpos : 0 < m)
    (hlevelOne : #items ≤ ∑ C0 : C, clusterCapacity C0)
    (hadjacent : ∀ C0 : C, m ≤ #(allowedEdges C0))
    (hsmall : ∀ i ∈ items, weight i ≤ slack)
    (hdeep : ∑ i ∈ items, weight i ≤ m * base) :
    Nonempty (AggregateAllocation items weight clusterCapacity allowedEdges
      base slack) := by
  classical
  obtain ⟨cluster, hcluster⟩ :=
    unit_capacity_packing items clusterCapacity hlevelOne
  obtain ⟨edge, hedgeAllowed, hedgeLoad⟩ :=
    allowed_capacity_packing items weight (fun i => allowedEdges (cluster i))
      m base slack hmpos (by
        intro i hi
        exact hadjacent (cluster i)) hsmall hdeep
  exact ⟨
    { levelOneCluster := cluster
      matchingEdge := edge
      cluster_load := hcluster
      matching_allowed := hedgeAllowed
      matching_load := hedgeLoad }⟩

/-- Branch specialization. One branch root consumes one level-one place and
`size j - 1` is its level-at-least-two matching demand. `owner` records the
original root in `A` joined to the branch root. -/
theorem exists_orderedBranchAggregateAllocation
    {r b : ℕ} {C K : Type*}
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype K] [DecidableEq K] [Nonempty K]
    (branches : RegularPair.OrderedRootedForest b)
    (_owner : Fin b → Fin r)
    (clusterCapacity : C → ℕ) (allowedEdges : C → Finset K)
    (m base slack : ℕ) (hmpos : 0 < m)
    (hlevelOne : b ≤ ∑ C0 : C, clusterCapacity C0)
    (hadjacent : ∀ C0 : C, m ≤ #(allowedEdges C0))
    (hsmall : ∀ j : Fin b, branches.size j - 1 ≤ slack)
    (hdeep : ∑ j : Fin b, (branches.size j - 1) ≤ m * base) :
    Nonempty (AggregateAllocation Finset.univ
      (fun j : Fin b => branches.size j - 1)
      clusterCapacity allowedEdges base slack) := by
  apply exists_aggregateAllocation Finset.univ
    (fun j : Fin b => branches.size j - 1)
    clusterCapacity allowedEdges m base slack hmpos
  · simpa using hlevelOne
  · exact hadjacent
  · intro j _hj
    exact hsmall j
  · simpa using hdeep

end Erdos547b.ZhaoLemma59FullOnline

#print axioms Erdos547b.ZhaoLemma59FullOnline.card_positiveMatchingSides_le_twice_edges
#print axioms Erdos547b.ZhaoLemma59FullOnline.card_allowedMatchingEdges_ge_half_side_degree
#print axioms Erdos547b.ZhaoLemma59FullOnline.unit_capacity_packing
#print axioms Erdos547b.ZhaoLemma59FullOnline.allowed_capacity_packing
#print axioms Erdos547b.ZhaoLemma59FullOnline.exists_aggregateAllocation
#print axioms Erdos547b.ZhaoLemma59FullOnline.exists_orderedBranchAggregateAllocation
