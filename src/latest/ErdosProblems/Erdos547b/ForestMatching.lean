/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.RegularPair
import ErdosProblems.Erdos547b.TreePartition
import Mathlib.Combinatorics.Pigeonhole

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ForestMatching

open Finset Fintype SimpleGraph

/-- Sum of the first colour-class sizes in a list of bipartite components. -/
def firstTotal (parts : List (ℕ × ℕ)) : ℕ :=
  (parts.map Prod.fst).sum

/-- Sum of the second colour-class sizes in a list of bipartite components. -/
def secondTotal (parts : List (ℕ × ℕ)) : ℕ :=
  (parts.map Prod.snd).sum

/-- One balancing step: if two current colour classes differ by at most
`slack`, a new bipartite component of order at most `slack` can be oriented
so the same invariant remains true. -/
theorem balanced_orientation_step
    (x y a b slack : ℕ) (hxy : x ≤ y + slack) (hyx : y ≤ x + slack)
    (hab : a + b ≤ slack) :
    (x + a ≤ y + b + slack ∧ y + b ≤ x + a + slack) ∨
      (x + b ≤ y + a + slack ∧ y + a ≤ x + b + slack) := by
  by_cases h₁ : x ≤ y
  · by_cases h₂ : a ≤ b
    · right
      constructor <;> omega
    · left
      constructor <;> omega
  · by_cases h₂ : a ≤ b
    · left
      constructor <;> omega
    · right
      constructor <;> omega

/-- Ordered balancing lemma used in Zhao Lemma 5.4 Parts 1 and 2.  Each small
root-subtree may have its two bipartition classes flipped.  There is a choice
of flips for which the two accumulated classes differ by at most the maximum
component order. -/
theorem exists_balanced_orientations (parts : List (ℕ × ℕ)) (slack : ℕ)
    (hsmall : ∀ p ∈ parts, p.1 + p.2 ≤ slack) :
    ∃ oriented : List (ℕ × ℕ),
      List.Forall₂ (fun p q => q = p ∨ q = (p.2, p.1)) parts oriented ∧
      firstTotal oriented ≤ secondTotal oriented + slack ∧
      secondTotal oriented ≤ firstTotal oriented + slack := by
  induction parts with
  | nil =>
      exact ⟨[], .nil, by simp [firstTotal, secondTotal]⟩
  | cons p parts ih =>
      have hp : p.1 + p.2 ≤ slack := hsmall p (by simp)
      have htail : ∀ q ∈ parts, q.1 + q.2 ≤ slack := by
        intro q hq
        exact hsmall q (by simp [hq])
      obtain ⟨oriented, horient, h₁, h₂⟩ := ih htail
      rcases balanced_orientation_step (firstTotal oriented)
          (secondTotal oriented) p.1 p.2 slack h₁ h₂ hp with h | h
      · refine ⟨p :: oriented, .cons (Or.inl rfl) horient, ?_, ?_⟩
        · simpa [firstTotal, secondTotal, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using h.1
        · simpa [firstTotal, secondTotal, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using h.2
      · refine ⟨(p.2, p.1) :: oriented, .cons (Or.inr rfl) horient, ?_, ?_⟩
        · simpa [firstTotal, secondTotal, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using h.1
        · simpa [firstTotal, secondTotal, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using h.2

theorem total_preserved_of_orientations {parts oriented : List (ℕ × ℕ)}
    (h : List.Forall₂ (fun p q => q = p ∨ q = (p.2, p.1)) parts oriented) :
    firstTotal oriented + secondTotal oriented =
      firstTotal parts + secondTotal parts := by
  induction h with
  | nil => simp [firstTotal, secondTotal]
  | @cons p q parts oriented hpq _ ih =>
      rcases hpq with rfl | rfl <;>
        simp [firstTotal, secondTotal] at ih ⊢ <;> omega

/-- Capacity form of the balancing lemma: after flipping component
bipartitions, twice either total colour-class size is at most the total order
plus one component of slack.  This is the numerical estimate used to fit the
forest into the two sides of a regular pair in Zhao Lemma 5.4 Part 1. -/
theorem exists_balanced_orientations_with_capacity
    (parts : List (ℕ × ℕ)) (slack : ℕ)
    (hsmall : ∀ p ∈ parts, p.1 + p.2 ≤ slack) :
    ∃ oriented : List (ℕ × ℕ),
      List.Forall₂ (fun p q => q = p ∨ q = (p.2, p.1)) parts oriented ∧
      2 * firstTotal oriented ≤ firstTotal parts + secondTotal parts + slack ∧
      2 * secondTotal oriented ≤ firstTotal parts + secondTotal parts + slack := by
  obtain ⟨oriented, horient, h₁, h₂⟩ :=
    exists_balanced_orientations parts slack hsmall
  have htotal := total_preserved_of_orientations horient
  refine ⟨oriented, horient, ?_, ?_⟩ <;> omega

/-! The finite bin-packing step in Zhao's proof of Lemma 5.8.  The items are
the small rooted trees, the bins are the regular pairs of a cluster matching,
and `slack` is the common upper bound on the size of one item. -/

theorem capacity_packing
    {ι κ : Type*} [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (items : Finset ι) (weight : ι → ℕ) (capacity : κ → ℕ) (slack : ℕ)
    (hsmall : ∀ i ∈ items, weight i ≤ slack)
    (hbudget : (∑ i ∈ items, weight i) + Fintype.card κ * slack ≤
      ∑ j : κ, capacity j) :
    ∃ assign : ι → κ, ∀ j : κ,
      ∑ i ∈ items.filter (assign · = j), weight i ≤ capacity j := by
  classical
  induction items using Finset.induction_on with
  | empty =>
      exact ⟨fun _ => Classical.choice inferInstance, by simp⟩
  | @insert x s hx ih =>
      have hsmall_s : ∀ i ∈ s, weight i ≤ slack := by
        intro i hi
        exact hsmall i (mem_insert_of_mem hi)
      have hbudget_s : (∑ i ∈ s, weight i) + Fintype.card κ * slack ≤
          ∑ j : κ, capacity j := by
        rw [sum_insert hx] at hbudget
        omega
      obtain ⟨assign, hassign⟩ := ih hsmall_s hbudget_s
      let load : κ → ℕ := fun j =>
        ∑ i ∈ s.filter (assign · = j), weight i
      have hload_sum : ∑ j : κ, load j = ∑ i ∈ s, weight i := by
        simpa only [load] using sum_fiberwise s assign weight
      have hplace : ∃ j : κ, load j + weight x ≤ capacity j := by
        by_contra h
        push Not at h
        have hall : ∀ j : κ, capacity j < load j + weight x := h
        have hlt : (∑ j : κ, capacity j) < ∑ j : κ, (load j + weight x) := by
          exact sum_lt_sum (fun j _ => (hall j).le) ⟨Classical.choice inferInstance,
            mem_univ _, hall _⟩
        have hsum_upper : (∑ j : κ, (load j + weight x)) ≤
            (∑ i ∈ s, weight i) + Fintype.card κ * slack := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul, hload_sum, card_univ]
          exact Nat.add_le_add_left
            (Nat.mul_le_mul_left (Fintype.card κ)
              (hsmall x (mem_insert_self x s))) _
        exact (not_lt_of_ge (hsum_upper.trans hbudget_s)) hlt
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
        rw [hfilter, sum_insert]
        · simpa [load, add_comm] using hj0
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

/-- Logical assembly form of the packing lemma.  Once a local embedding
lemma is available for every group whose total weight is within one pair's
capacity, the small components can be distributed over all pairs and every
local embedding certificate can be invoked.  This is precisely the
Lemma-5.4-to-Lemma-5.8 passage, separated from graph-specific notation. -/
theorem capacity_packing_with_local_certificates
    {ι κ : Type*} [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (items : Finset ι) (weight : ι → ℕ) (capacity : κ → ℕ) (slack : ℕ)
    (P : κ → Finset ι → Prop)
    (hsmall : ∀ i ∈ items, weight i ≤ slack)
    (hbudget : (∑ i ∈ items, weight i) + Fintype.card κ * slack ≤
      ∑ j : κ, capacity j)
    (hlocal : ∀ j : κ, ∀ group : Finset ι, group ⊆ items →
      (∑ i ∈ group, weight i) ≤ capacity j → P j group) :
    ∃ assign : ι → κ,
      (∀ j : κ, ∑ i ∈ items.filter (assign · = j), weight i ≤ capacity j) ∧
      ∀ j : κ, P j (items.filter (assign · = j)) := by
  obtain ⟨assign, hload⟩ :=
    capacity_packing items weight capacity slack hsmall hbudget
  refine ⟨assign, hload, ?_⟩
  intro j
  exact hlocal j _ (filter_subset _ _) (hload j)

universe u v w

/-- An embedding of a finite indexed family of trees whose component images
are pairwise vertex-disjoint.  This is the literal graph-theoretic content of
embedding a forest: each component is copied into the host, and different
components use different host vertices. -/
structure OrderedForestCopy
    {ι : Type u} (items : Finset ι) (A : ι → Type v)
    (T : ∀ i, SimpleGraph (A i)) {B : Type w} (G : SimpleGraph B) where
  componentCopy : ∀ i, i ∈ items → (T i).Copy G
  disjoint_ranges : ∀ i (hi : i ∈ items) j (hj : j ∈ items), i ≠ j →
    Disjoint (Set.range (componentCopy i hi : A i → B))
      (Set.range (componentCopy j hj : A j → B))

/-- A finite cluster matching: each edge has two cluster sides, and all sides
belonging to distinct matching edges are disjoint.  Disjointness of the two
sides of a single edge is included as well, matching Zhao Definition 5.5. -/
structure ClusterMatching (κ : Type u) (B : Type w) where
  side : κ → Fin 2 → Finset B
  disjoint_sides : ∀ p c q d, p ≠ q ∨ c ≠ d →
    Disjoint (side p c) (side q d)

theorem ClusterMatching.disjoint_of_pair_ne
    {κ : Type u} {B : Type w} (M : ClusterMatching κ B)
    {p q : κ} (hpq : p ≠ q) (c d : Fin 2) :
    Disjoint (M.side p c) (M.side q d) :=
  M.disjoint_sides p c q d (Or.inl hpq)

/-- The local-to-forest embedding core behind Zhao Lemma 5.4.  Each rooted
tree is embedded by the checked greedy two-colour theorem.  Pairwise-disjoint
candidate sets and distinct prescribed root images make the resulting copies
a genuine (globally injective) forest copy. -/
theorem exists_orderedForestCopy_of_disjoint_candidates
    {ι : Type u} [DecidableEq ι] {B : Type w} [Fintype B] [DecidableEq B]
    (items : Finset ι) (A : ι → Type v) [∀ i, Fintype (A i)]
    (T : ∀ i, SimpleGraph (A i)) (hT : ∀ i, (T i).IsTree)
    (root : ∀ i, A i) (G : SimpleGraph B) [DecidableRel G.Adj]
    (candidate : ι → Fin 2 → Finset B) (rootImage : ι → B)
    (hrootDegree : ∀ i ∈ items,
      Fintype.card (A i) ≤
        #{z ∈ candidate i 1 | G.Adj (rootImage i) z})
    (hcross : ∀ i ∈ items, ∀ c d : Fin 2, c ≠ d →
      ∀ z ∈ candidate i c,
        Fintype.card (A i) ≤ #{y ∈ candidate i d | G.Adj z y})
    (hroots_injective : ∀ i ∈ items, ∀ j ∈ items,
      rootImage i = rootImage j → i = j)
    (hroot_outside : ∀ i ∈ items, ∀ j ∈ items, ∀ c,
      rootImage i ∉ candidate j c)
    (hcandidate_disjoint : ∀ i ∈ items, ∀ j ∈ items, i ≠ j →
      ∀ c d, Disjoint (candidate i c) (candidate j d)) :
    Nonempty (OrderedForestCopy items A T G) := by
  classical
  have hcomponent : ∀ i : ι, ∀ hi : i ∈ items,
      ∃ f : (T i).Copy G, f (root i) = rootImage i ∧
        ∀ a, a ≠ root i →
          f a ∈ candidate i ((hT i).coloringTwoOfVert (root i) a) := by
    intro i hi
    exact Erdos547b.RegularPair.exists_rooted_tree_copy (T i) G (hT i) (root i)
      (candidate i) (rootImage i) (hrootDegree i hi) (by
        intro c d hcd z hz
        exact hcross i hi c d hcd z hz)
  -- Restrict the componentwise choice to the requested finite family.
  choose copy hcopyRoot hcopyMem using hcomponent
  refine ⟨
    { componentCopy := fun i hi => copy i hi
      disjoint_ranges := ?_ }⟩
  intro i hi j hj hij
  rw [Set.disjoint_left]
  intro z hzi hzj
  rcases hzi with ⟨a, rfl⟩
  rcases hzj with ⟨b, hab⟩
  by_cases ha : a = root i
  · subst a
    by_cases hb : b = root j
    · subst b
      apply hij
      apply hroots_injective i hi j hj
      calc
        rootImage i = copy i hi (root i) := (hcopyRoot i hi).symm
        _ = copy j hj (root j) := hab.symm
        _ = rootImage j := hcopyRoot j hj
    · have hbmem := hcopyMem j hj b hb
      have heq : rootImage i = copy j hj b := calc
        rootImage i = copy i hi (root i) := (hcopyRoot i hi).symm
        _ = copy j hj b := hab.symm
      exact hroot_outside i hi j hj _ (heq.symm ▸ hbmem)
  · have hamem := hcopyMem i hi a ha
    by_cases hb : b = root j
    · subst b
      have heq : rootImage j = copy i hi a := calc
        rootImage j = copy j hj (root j) := (hcopyRoot j hj).symm
        _ = copy i hi a := hab
      exact hroot_outside j hj i hi _ (heq.symm ▸ hamem)
    · have hbmem := hcopyMem j hj b hb
      have hd := hcandidate_disjoint i hi j hj hij
        ((hT i).coloringTwoOfVert (root i) a)
        ((hT j).coloringTwoOfVert (root j) b)
      exact (Finset.disjoint_left.mp hd) hamem (hab ▸ hbmem)

/-- A matching-indexed specialization of the preceding forest theorem.  It
is the genuine graph embedding core of Zhao Lemma 5.8 in the clean case where
different components have been assigned different matching edges. -/
theorem exists_orderedForestCopy_of_clusterMatching
    {ι : Type u} [DecidableEq ι] {κ : Type v} {B : Type w}
    [Fintype B] [DecidableEq B]
    (items : Finset ι) (A : ι → Type*) [∀ i, Fintype (A i)]
    (T : ∀ i, SimpleGraph (A i)) (hT : ∀ i, (T i).IsTree)
    (root : ∀ i, A i) (G : SimpleGraph B) [DecidableRel G.Adj]
    (M : ClusterMatching κ B) (assign : ι → κ)
    (hassign : ∀ i ∈ items, ∀ j ∈ items, assign i = assign j → i = j)
    (rootImage : ι → B)
    (hrootDegree : ∀ i ∈ items,
      Fintype.card (A i) ≤
        #{z ∈ M.side (assign i) 1 | G.Adj (rootImage i) z})
    (hcross : ∀ i ∈ items, ∀ c d : Fin 2, c ≠ d →
      ∀ z ∈ M.side (assign i) c,
        Fintype.card (A i) ≤
          #{y ∈ M.side (assign i) d | G.Adj z y})
    (hroots_injective : ∀ i ∈ items, ∀ j ∈ items,
      rootImage i = rootImage j → i = j)
    (hroot_outside : ∀ i ∈ items, ∀ p : κ, ∀ c,
      rootImage i ∉ M.side p c) :
    Nonempty (OrderedForestCopy items A T G) := by
  apply exists_orderedForestCopy_of_disjoint_candidates items A T hT root G
    (fun i => M.side (assign i)) rootImage hrootDegree hcross hroots_injective
  · intro i hi j hj c
    exact hroot_outside i hi (assign j) c
  · intro i hi j hj hij c d
    apply M.disjoint_of_pair_ne
    intro hpair
    exact hij (hassign i hi j hj hpair)

#print axioms Erdos547b.ForestMatching.capacity_packing
#print axioms Erdos547b.ForestMatching.exists_balanced_orientations_with_capacity
#print axioms Erdos547b.ForestMatching.capacity_packing_with_local_certificates
#print axioms Erdos547b.ForestMatching.exists_orderedForestCopy_of_disjoint_candidates
#print axioms Erdos547b.ForestMatching.exists_orderedForestCopy_of_clusterMatching

end Erdos547b.ForestMatching
