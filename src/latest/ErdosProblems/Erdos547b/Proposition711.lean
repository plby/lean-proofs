import Mathlib

open scoped BigOperators

namespace ZhaoProp711

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SimpleGraph

variable (T : SimpleGraph V) [DecidableRel T.Adj]

/-- The leaves of a finite graph, in Zhao's convention. -/
def leaves : Finset V := Finset.univ.filter (fun v => T.degree v = 1)

/-- The vertices of degree at least three. -/
def branchingVertices : Finset V := Finset.univ.filter (fun v => 3 ≤ T.degree v)

/-- The degree-two vertices. -/
def degreeTwoVertices : Finset V := Finset.univ.filter (fun v => T.degree v = 2)

@[simp] theorem mem_leaves {v : V} : v ∈ leaves T ↔ T.degree v = 1 := by
  simp [leaves]

@[simp] theorem mem_branchingVertices {v : V} : v ∈ branchingVertices T ↔ 3 ≤ T.degree v := by
  simp [branchingVertices]

@[simp] theorem mem_degreeTwoVertices {v : V} : v ∈ degreeTwoVertices T ↔ T.degree v = 2 := by
  simp [degreeTwoVertices]

/-- Zhao, Proposition 7.11(1), in the exact integer degree-excess form. -/
theorem IsTree.sum_branching_degree_sub_two
    [Nontrivial V] (hT : T.IsTree) :
    ∑ v ∈ branchingVertices T, ((T.degree v : ℤ) - 2) = ((leaves T).card : ℤ) - 2 := by
  have hpos (v : V) : 1 ≤ T.degree v := by
    have hm := T.minDegree_le_degree v
    rw [hT.minDegree_eq_one_of_nontrivial] at hm
    exact hm
  have hpoint (v : V) :
      ((T.degree v : ℤ) - 2) =
        (if T.degree v = 1 then -1 else if 3 ≤ T.degree v then (T.degree v : ℤ) - 2 else 0) := by
    split_ifs with h1 h3
    · omega
    · omega
    · have hp := hpos v
      have hd : T.degree v = 2 := by omega
      simp [hd]
  have hsum : ∑ v : V, ((T.degree v : ℤ) - 2) = -2 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hdegNat := T.sum_degrees_eq_twice_card_edges
    have hedgeNat := hT.card_edgeFinset
    have hdeg : (∑ v : V, (T.degree v : ℤ)) = 2 * (T.edgeFinset.card : ℤ) := by
      exact_mod_cast hdegNat
    have hedge : (T.edgeFinset.card : ℤ) + 1 = Fintype.card V := by
      exact_mod_cast hedgeNat
    omega
  rw [Finset.sum_congr rfl (fun v _ => hpoint v)] at hsum
  rw [Finset.sum_ite] at hsum
  rw [Finset.sum_ite] at hsum
  simp only [Finset.sum_const, Finset.card_filter, nsmul_eq_mul, mul_neg, mul_one,
    Finset.sum_const_zero, add_zero, Finset.filter_filter, branchingVertices, leaves] at hsum ⊢
  have hfilter :
      Finset.filter (fun v => ¬T.degree v = 1 ∧ 3 ≤ T.degree v) Finset.univ =
        Finset.filter (fun v => 3 ≤ T.degree v) Finset.univ := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      constructor
      · omega
      · exact h
  rw [hfilter] at hsum
  omega

/-- A finite greedy packing lemma.  If every member conflicts with at most `r`
members (including itself), a set of size at least `r*k` contains `k`
members with pairwise-disjoint supports. -/
theorem exists_disjoint_support_packing
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (support : α → Finset β) (D : Finset α) (r k : ℕ)
    (hr : 0 < r)
    (hne : ∀ x ∈ D, (support x).Nonempty)
    (hconflict : ∀ x ∈ D,
      (D.filter fun y => ¬Disjoint (support x) (support y)).card ≤ r)
    (hcard : r * k ≤ D.card) :
    ∃ P : Finset α, P ⊆ D ∧ P.card = k ∧ (P : Set α).PairwiseDisjoint support := by
  induction k generalizing D with
  | zero =>
      exact ⟨∅, by simp⟩
  | succ k ih =>
      have hDpos : 0 < D.card := by
        have : r ≤ r * (k + 1) := by nlinarith
        omega
      obtain ⟨x, hxD⟩ := Finset.card_pos.mp hDpos
      let bad := D.filter fun y => ¬Disjoint (support x) (support y)
      let D' := D \ bad
      have hbad_sub : bad ⊆ D := Finset.filter_subset _ _
      have hbad_card : bad.card ≤ r := hconflict x hxD
      have hx_bad : x ∈ bad := by
        simp only [bad, Finset.mem_filter, hxD, true_and]
        intro hdisj
        obtain ⟨b, hb⟩ := hne x hxD
        exact (Finset.disjoint_left.mp hdisj) hb hb
      have hx_not_D' : x ∉ D' := by simp [D', hx_bad]
      have hD'card : r * k ≤ D'.card := by
        dsimp only [D']
        rw [Finset.card_sdiff_of_subset hbad_sub]
        rw [Nat.mul_succ] at hcard
        omega
      have hne' : ∀ y ∈ D', (support y).Nonempty := by
        intro y hy
        exact hne y (Finset.mem_sdiff.mp hy).1
      have hconflict' : ∀ y ∈ D',
          (D'.filter fun z => ¬Disjoint (support y) (support z)).card ≤ r := by
        intro y hy
        apply le_trans (Finset.card_le_card ?_) (hconflict y (Finset.mem_sdiff.mp hy).1)
        intro z hz
        simp only [Finset.mem_filter] at hz ⊢
        exact ⟨(Finset.mem_sdiff.mp hz.1).1, hz.2⟩
      obtain ⟨P, hPD', hPk, hPpair⟩ := ih D' hne' hconflict' hD'card
      have hxP : x ∉ P := fun hxP => hx_not_D' (hPD' hxP)
      have hxdisj : ∀ y ∈ (P : Set α), Disjoint (support x) (support y) := by
        intro y hyP
        have hyD' : y ∈ D' := hPD' hyP
        have hy_not_bad : y ∉ bad := (Finset.mem_sdiff.mp hyD').2
        apply not_not.mp
        intro hnot
        apply hy_not_bad
        exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hyD').1, hnot⟩
      refine ⟨insert x P, ?_, by simp [hPk, hxP], ?_⟩
      · intro y hy
        simp only [Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · exact hxD
        · exact (Finset.mem_sdiff.mp (hPD' hy)).1
      · simpa only [Finset.coe_insert] using hPpair.insert_of_notMem hxP hxdisj

/-- Zhao, Proposition 7.11(1), the stated cardinality consequence. -/
theorem IsTree.card_branchingVertices_le_leaves_sub_two
    [Nontrivial V] (hT : T.IsTree) :
    (branchingVertices T).card ≤ (leaves T).card - 2 := by
  have hsum := IsTree.sum_branching_degree_sub_two (T := T) hT
  have hone : ((branchingVertices T).card : ℤ) ≤
      ∑ v ∈ branchingVertices T, ((T.degree v : ℤ) - 2) := by
    calc
      ((branchingVertices T).card : ℤ) = ∑ _v ∈ branchingVertices T, (1 : ℤ) := by simp
      _ ≤ ∑ v ∈ branchingVertices T, ((T.degree v : ℤ) - 2) := by
        gcongr with v hv
        have hv' : 3 ≤ T.degree v := (mem_branchingVertices (T := T)).mp hv
        omega
  have hleaves : 2 ≤ (leaves T).card := by
    obtain ⟨u, v, huv, hu, hv⟩ := hT.exists_ne_and_degree_eq_one
    have hum : u ∈ leaves T := by simp [hu]
    have hvm : v ∈ leaves T := by simp [hv]
    exact Finset.one_lt_card.mpr ⟨u, hum, v, hvm, huv⟩
  rw [hsum] at hone
  omega

/-- Natural-number form of Proposition 7.11(1), convenient for counting. -/
theorem IsTree.sum_branching_nat_sub_two
    [Nontrivial V] (hT : T.IsTree) :
    ∑ v ∈ branchingVertices T, (T.degree v - 2) = (leaves T).card - 2 := by
  have hz := IsTree.sum_branching_degree_sub_two (T := T) hT
  have hleaves : 2 ≤ (leaves T).card := by
    obtain ⟨u, v, huv, hu, hv⟩ := hT.exists_ne_and_degree_eq_one
    exact Finset.one_lt_card.mpr ⟨u, by simp [hu], v, by simp [hv], huv⟩
  have hcast :
      ((∑ v ∈ branchingVertices T, (T.degree v - 2) : ℕ) : ℤ) =
        ∑ v ∈ branchingVertices T, ((T.degree v : ℤ) - 2) := by
    push_cast
    apply Finset.sum_congr rfl
    intro v hv
    have hv' : 2 ≤ T.degree v := by
      have := (mem_branchingVertices (T := T)).mp hv
      omega
    omega
  rw [← hcast] at hz
  exact_mod_cast hz

/-- The union of the neighborhoods of vertices in `S`. -/
def neighborsOf (S : Finset V) : Finset V := S.biUnion (fun v => T.neighborFinset v)

@[simp] theorem mem_neighborsOf {S : Finset V} {v : V} :
    v ∈ neighborsOf (T := T) S ↔ ∃ u ∈ S, T.Adj u v := by
  simp [neighborsOf]

/-- The three vertices of the 2-path whose midpoint is the degree-two vertex `v`. -/
def twoPathVertices (v : V) : Finset V := insert v (T.neighborFinset v)

/-- A midpoint is special when it has degree two and every vertex adjacent to
one of its two endpoints has degree at most two. -/
def IsSpecialTwoPathCenter (v : V) : Prop :=
  T.degree v = 2 ∧ ∀ x ∈ neighborsOf (T := T) (T.neighborFinset v), T.degree x ≤ 2

@[simp] theorem mem_twoPathVertices {u v : V} :
    u ∈ twoPathVertices T v ↔ u = v ∨ T.Adj v u := by
  simp [twoPathVertices, eq_comm]

theorem card_twoPathVertices {v : V} (hv : T.degree v = 2) :
    (twoPathVertices T v).card = 3 := by
  rw [twoPathVertices, Finset.card_insert_of_notMem]
  · simpa [T.card_neighborFinset_eq_degree, hv]
  · simp

/-- The second neighborhood of a degree-two center has size at most three
when both endpoints have degree at most two. -/
theorem card_neighborsOf_neighborFinset_le_three {v : V}
    (hv : T.degree v = 2)
    (hend : ∀ x, T.Adj v x → T.degree x ≤ 2) :
    (neighborsOf (T := T) (T.neighborFinset v)).card ≤ 3 := by
  have hcardN : (T.neighborFinset v).card = 2 := by
    simpa [T.card_neighborFinset_eq_degree, hv]
  obtain ⟨a, b, hab, hN⟩ := Finset.card_eq_two.mp hcardN
  have hva : T.Adj v a := by
    rw [← T.mem_neighborFinset]
    simp [hN]
  have hvb : T.Adj v b := by
    rw [← T.mem_neighborFinset]
    simp [hN]
  have hdegA := hend a hva
  have hdegB := hend b hvb
  have hinter : 1 ≤ (T.neighborFinset a ∩ T.neighborFinset b).card := by
    exact Finset.card_pos.mpr ⟨v, by simp [hva.symm, hvb.symm]⟩
  have hunion := Finset.card_union_add_card_inter (T.neighborFinset a) (T.neighborFinset b)
  have hrewrite : neighborsOf (T := T) (T.neighborFinset v) =
      T.neighborFinset a ∪ T.neighborFinset b := by
    ext x
    simp [neighborsOf, hN]
  rw [hrewrite]
  rw [T.card_neighborFinset_eq_degree, T.card_neighborFinset_eq_degree] at hunion
  omega

/-- Among degree-two centers in one side of a bipartite graph, if the two
endpoints of `x` have degree at most two, at most three centered 2-paths
can meet the path centered at `x`. -/
theorem card_conflicting_twoPathCenters_le_three
    {A B : Set V} (hbi : T.IsBipartiteWith A B) (D : Finset V)
    (hD : ∀ y ∈ D, y ∈ A ∧ T.degree y = 2)
    {x : V} (hxD : x ∈ D)
    (hend : ∀ u, T.Adj x u → T.degree u ≤ 2) :
    (D.filter fun y => ¬Disjoint (twoPathVertices T x) (twoPathVertices T y)).card ≤ 3 := by
  have hxA := (hD x hxD).1
  have hxdeg := (hD x hxD).2
  have hsame_not_adj {u v : V} (hu : u ∈ A) (hv : v ∈ A) : ¬T.Adj u v := by
    intro huv
    have hvB := hbi.mem_of_mem_adj hu huv
    exact Set.disjoint_left.mp hbi.disjoint hv hvB
  have hsubset :
      D.filter (fun y => ¬Disjoint (twoPathVertices T x) (twoPathVertices T y)) ⊆
        neighborsOf (T := T) (T.neighborFinset x) := by
    intro y hy
    have hyD := (Finset.mem_filter.mp hy).1
    have hyA := (hD y hyD).1
    have hyconf := (Finset.mem_filter.mp hy).2
    by_cases hxy : y = x
    · subst y
      have hpos : 0 < (T.neighborFinset x).card := by
        simpa [T.card_neighborFinset_eq_degree, hxdeg]
      obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
      apply (mem_neighborsOf (T := T)).mpr
      exact ⟨u, hu, (T.mem_neighborFinset x u).mp hu |>.symm⟩
    · obtain ⟨q, hqx, hqy⟩ := Finset.not_disjoint_iff.mp hyconf
      rw [mem_twoPathVertices] at hqx hqy
      rcases hqx with rfl | hxq
      · rcases hqy with hxy' | hyx
        · exact (hxy hxy'.symm).elim
        · exact (hsame_not_adj hyA hxA hyx).elim
      · rcases hqy with rfl | hyq
        · exact (hsame_not_adj hxA hyA hxq).elim
        · apply (mem_neighborsOf (T := T)).mpr
          exact ⟨q, (T.mem_neighborFinset x q).mpr hxq,
            hyq.symm⟩
  exact (Finset.card_le_card hsubset).trans
    (card_neighborsOf_neighborFinset_le_three (T := T) hxdeg hend)

/-- Zhao's set `U'_2`: degree-two vertices of the second bipartition side
which avoid the neighbors of branching vertices in the first side and of `z`. -/
def u2Prime (U1 U2 : Finset V) (z : V) : Finset V :=
  (degreeTwoVertices T ∩ U2) \
    neighborsOf (T := T) ((branchingVertices T ∩ U1) ∪ {z})

/-- Zhao's set `U'_1`. -/
def u1Prime (U1 U2 : Finset V) (z : V) : Finset V :=
  ((degreeTwoVertices T ∩ U1) \ {z}) \
    neighborsOf (T := T) (branchingVertices T ∩ U2)

/-- Zhao's set `U''_2`, whose centered paths are special. -/
def u2SpecialCenters (U1 U2 : Finset V) (z : V) : Finset V :=
  u2Prime T U1 U2 z \
    neighborsOf (T := T) (neighborsOf (T := T) (branchingVertices T ∩ U2))

/-- In a nontrivial tree, every vertex not of degree two is either a leaf or
a branching vertex.  This is the degree partition used in Proposition 7.11. -/
theorem IsTree.card_part_sdiff_degreeTwo_le
    [Nontrivial V] (hT : T.IsTree) (U : Finset V) :
    (U \ degreeTwoVertices T).card ≤
      (U ∩ leaves T).card + (U ∩ branchingVertices T).card := by
  apply le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro v hv
  have hvU := (Finset.mem_sdiff.mp hv).1
  have hvnot2 := (Finset.mem_sdiff.mp hv).2
  have hpos : 1 ≤ T.degree v := by
    have hm := T.minDegree_le_degree v
    rw [hT.minDegree_eq_one_of_nontrivial] at hm
    exact hm
  simp only [Finset.mem_union, Finset.mem_inter, mem_leaves, mem_branchingVertices]
  by_cases h1 : T.degree v = 1
  · exact Or.inl ⟨hvU, h1⟩
  · right
    refine ⟨hvU, ?_⟩
    have hne2 : T.degree v ≠ 2 := by
      intro h2
      exact hvnot2 (by simp [degreeTwoVertices, h2])
    omega

theorem card_inter_le_left (A B : Finset V) : (A ∩ B).card ≤ A.card := by
  exact Finset.card_le_card (Finset.inter_subset_left)

theorem card_inter_le_right (A B : Finset V) : (A ∩ B).card ≤ B.card := by
  exact Finset.card_le_card (Finset.inter_subset_right)

theorem card_le_card_sdiff_add (A B : Finset V) :
    A.card ≤ (A \ B).card + B.card := by
  have heq := Finset.card_sdiff_add_card_inter A B
  have hle := Finset.card_le_card (Finset.inter_subset_right : A ∩ B ⊆ B)
  omega

theorem card_two_disjoint_parts_le {A U1 U2 : Finset V}
    (hdisj : Disjoint U1 U2) :
    (A ∩ U1).card + (A ∩ U2).card ≤ A.card := by
  have hd : Disjoint (A ∩ U1) (A ∩ U2) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.disjoint_left.mp hdisj)
      (Finset.mem_inter.mp hx1).2 (Finset.mem_inter.mp hx2).2
  rw [← Finset.card_union_of_disjoint hd]
  apply Finset.card_le_card
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact (Finset.mem_inter.mp hx).1
  · exact (Finset.mem_inter.mp hx).1

/-- Zhao, Proposition 7.11(2). -/
theorem IsTree.card_neighborsOf_le
    [Nontrivial V] (hT : T.IsTree) (S : Finset V) :
    (neighborsOf (T := T) S).card ≤ 2 * S.card + (leaves T).card - 2 := by
  have hunion : (neighborsOf (T := T) S).card ≤ ∑ v ∈ S, T.degree v := by
    simpa [neighborsOf, T.card_neighborFinset_eq_degree] using
      (Finset.card_biUnion_le (s := S) (t := fun v => T.neighborFinset v))
  have hpoint (v : V) :
      T.degree v ≤ 2 + if 3 ≤ T.degree v then T.degree v - 2 else 0 := by
    split_ifs with h
    · omega
    · omega
  have hdegree : ∑ v ∈ S, T.degree v ≤
      2 * S.card + ∑ v ∈ S.filter (fun v => 3 ≤ T.degree v), (T.degree v - 2) := by
    calc
      ∑ v ∈ S, T.degree v ≤
          ∑ v ∈ S, (2 + if 3 ≤ T.degree v then T.degree v - 2 else 0) := by
            gcongr with v hv
            exact hpoint v
      _ = 2 * S.card + ∑ v ∈ S.filter (fun v => 3 ≤ T.degree v), (T.degree v - 2) := by
        simp [Finset.sum_add_distrib, Finset.sum_ite, mul_comm]
  have hfilter : S.filter (fun v => 3 ≤ T.degree v) ⊆ branchingVertices T := by
    intro v hv
    simpa only [mem_branchingVertices] using (Finset.mem_filter.mp hv).2
  have hsubsum :
      ∑ v ∈ S.filter (fun v => 3 ≤ T.degree v), (T.degree v - 2) ≤
        ∑ v ∈ branchingVertices T, (T.degree v - 2) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hfilter (fun _ _ _ => Nat.zero_le _)
  have hexcess := IsTree.sum_branching_nat_sub_two (T := T) hT
  rw [hexcess] at hsubsum
  have hleaves : 2 ≤ (leaves T).card := by
    obtain ⟨u, v, huv, hu, hv⟩ := hT.exists_ne_and_degree_eq_one
    exact Finset.one_lt_card.mpr ⟨u, by simp [hu], v, by simp [hv], huv⟩
  omega

/-- Zhao's estimate `|U'_2| ≥ |U₂| - 4l`, expressed without
truncated subtraction. -/
theorem IsTree.card_u2_le_card_u2Prime_add_four_leaves
    [Nontrivial V] (hT : T.IsTree) {U1 U2 : Finset V} {z : V}
    (hbi : T.IsBipartiteWith (U1 : Set V) (U2 : Set V)) :
    U2.card ≤ (u2Prime T U1 U2 z).card + 4 * (leaves T).card := by
  let A := degreeTwoVertices T ∩ U2
  let N := neighborsOf (T := T) ((branchingVertices T ∩ U1) ∪ {z})
  have hsplit : U2.card ≤ A.card + (U2 \ degreeTwoVertices T).card := by
    have heq : U2 = A ∪ (U2 \ degreeTwoVertices T) := by
      ext v
      simp [A]
      tauto
    calc
      U2.card = (A ∪ (U2 \ degreeTwoVertices T)).card := congrArg Finset.card heq
      _ ≤ A.card + (U2 \ degreeTwoVertices T).card :=
        Finset.card_union_le A (U2 \ degreeTwoVertices T)
  have hAprime : A.card ≤ (u2Prime T U1 U2 z).card + N.card := by
    simpa only [u2Prime, A, N] using card_le_card_sdiff_add A N
  have hnond2 := IsTree.card_part_sdiff_degreeTwo_le (T := T) hT U2
  have hleafpart : (U2 ∩ leaves T).card ≤ (leaves T).card :=
    card_inter_le_right U2 (leaves T)
  have hbranchparts :
      (branchingVertices T ∩ U1).card + (branchingVertices T ∩ U2).card ≤
        (branchingVertices T).card := by
    apply card_two_disjoint_parts_le
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact Set.disjoint_left.mp hbi.disjoint hx1 hx2
  have hbranchcomm : (U2 ∩ branchingVertices T).card =
      (branchingVertices T ∩ U2).card := by
    rw [Finset.inter_comm]
  have hbranch := IsTree.card_branchingVertices_le_leaves_sub_two (T := T) hT
  have hN := IsTree.card_neighborsOf_le (T := T) hT
    ((branchingVertices T ∩ U1) ∪ {z})
  have hS : ((branchingVertices T ∩ U1) ∪ {z}).card ≤
      (branchingVertices T ∩ U1).card + 1 := by
    simpa using Finset.card_union_le (branchingVertices T ∩ U1) {z}
  have hleaves : 2 ≤ (leaves T).card := by
    obtain ⟨u, v, huv, hu, hv⟩ := hT.exists_ne_and_degree_eq_one
    exact Finset.one_lt_card.mpr ⟨u, by simp [hu], v, by simp [hv], huv⟩
  change N.card ≤
    2 * ((branchingVertices T ∩ U1) ∪ {z}).card + (leaves T).card - 2 at hN
  omega

/-- The symmetric source estimate `|U'_1| ≥ |U₁| - 4l`. -/
theorem IsTree.card_u1_le_card_u1Prime_add_four_leaves
    [Nontrivial V] (hT : T.IsTree) {U1 U2 : Finset V} {z : V}
    (hbi : T.IsBipartiteWith (U1 : Set V) (U2 : Set V)) :
    U1.card ≤ (u1Prime T U1 U2 z).card + 4 * (leaves T).card := by
  let A := degreeTwoVertices T ∩ U1
  let A0 := A \ {z}
  let N := neighborsOf (T := T) (branchingVertices T ∩ U2)
  have hsplit : U1.card ≤ A.card + (U1 \ degreeTwoVertices T).card := by
    have heq : U1 = A ∪ (U1 \ degreeTwoVertices T) := by
      ext v
      simp [A]
      tauto
    calc
      U1.card = (A ∪ (U1 \ degreeTwoVertices T)).card := congrArg Finset.card heq
      _ ≤ A.card + (U1 \ degreeTwoVertices T).card :=
        Finset.card_union_le A (U1 \ degreeTwoVertices T)
  have hA0 : A.card ≤ A0.card + 1 := by
    have h := card_le_card_sdiff_add A {z}
    simpa only [A0, Finset.card_singleton] using h
  have hA0prime : A0.card ≤ (u1Prime T U1 U2 z).card + N.card := by
    simpa only [u1Prime, A0, A, N] using card_le_card_sdiff_add A0 N
  have hnond2 := IsTree.card_part_sdiff_degreeTwo_le (T := T) hT U1
  have hleafpart : (U1 ∩ leaves T).card ≤ (leaves T).card :=
    card_inter_le_right U1 (leaves T)
  have hbranchparts :
      (branchingVertices T ∩ U1).card + (branchingVertices T ∩ U2).card ≤
        (branchingVertices T).card := by
    apply card_two_disjoint_parts_le
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact Set.disjoint_left.mp hbi.disjoint hx1 hx2
  have hbranchcomm : (U1 ∩ branchingVertices T).card =
      (branchingVertices T ∩ U1).card := by
    rw [Finset.inter_comm]
  have hbranch := IsTree.card_branchingVertices_le_leaves_sub_two (T := T) hT
  have hN := IsTree.card_neighborsOf_le (T := T) hT (branchingVertices T ∩ U2)
  have hleaves : 2 ≤ (leaves T).card := by
    obtain ⟨u, v, huv, hu, hv⟩ := hT.exists_ne_and_degree_eq_one
    exact Finset.one_lt_card.mpr ⟨u, by simp [hu], v, by simp [hv], huv⟩
  change N.card ≤ 2 * (branchingVertices T ∩ U2).card + (leaves T).card - 2 at hN
  omega

/-- Zhao's iterated-neighborhood estimate
`|N²(U³₂)| ≤ 7(l-2)`. -/
theorem IsTree.card_second_neighbors_branching_part_le
    [Nontrivial V] (hT : T.IsTree) (U : Finset V) :
    (neighborsOf (T := T) (neighborsOf (T := T) (branchingVertices T ∩ U))).card ≤
      7 * ((leaves T).card - 2) := by
  let B := branchingVertices T ∩ U
  let N1 := neighborsOf (T := T) B
  let N2 := neighborsOf (T := T) N1
  have hB : B.card ≤ (branchingVertices T).card := by
    exact Finset.card_le_card Finset.inter_subset_left
  have hbranch := IsTree.card_branchingVertices_le_leaves_sub_two (T := T) hT
  have hN1 := IsTree.card_neighborsOf_le (T := T) hT B
  have hN2 := IsTree.card_neighborsOf_le (T := T) hT N1
  have hleaves : 2 ≤ (leaves T).card := by
    obtain ⟨u, v, huv, hu, hv⟩ := hT.exists_ne_and_degree_eq_one
    exact Finset.one_lt_card.mpr ⟨u, by simp [hu], v, by simp [hv], huv⟩
  change N1.card ≤ 2 * B.card + (leaves T).card - 2 at hN1
  change N2.card ≤ 2 * N1.card + (leaves T).card - 2 at hN2
  change N2.card ≤ 7 * ((leaves T).card - 2)
  omega

/-- The source estimate `|U''₂| ≥ |U₂| - 11l`. -/
theorem IsTree.card_u2_le_card_special_add_eleven_leaves
    [Nontrivial V] (hT : T.IsTree) {U1 U2 : Finset V} {z : V}
    (hbi : T.IsBipartiteWith (U1 : Set V) (U2 : Set V)) :
    U2.card ≤ (u2SpecialCenters T U1 U2 z).card + 11 * (leaves T).card := by
  let N2 := neighborsOf (T := T)
    (neighborsOf (T := T) (branchingVertices T ∩ U2))
  have hprime := IsTree.card_u2_le_card_u2Prime_add_four_leaves
    (T := T) (z := z) hT hbi
  have hcut : (u2Prime T U1 U2 z).card ≤
      (u2SpecialCenters T U1 U2 z).card + N2.card := by
    simpa only [u2SpecialCenters, N2] using
      card_le_card_sdiff_add (u2Prime T U1 U2 z) N2
  have hN2 := IsTree.card_second_neighbors_branching_part_le (T := T) hT U2
  have hleaves : 2 ≤ (leaves T).card := by
    obtain ⟨u, v, huv, hu, hv⟩ := hT.exists_ne_and_degree_eq_one
    exact Finset.one_lt_card.mpr ⟨u, by simp [hu], v, by simp [hv], huv⟩
  change N2.card ≤ 7 * ((leaves T).card - 2) at hN2
  omega

theorem u2Prime_mem_side_degree {U1 U2 : Finset V} {z y : V}
    (hy : y ∈ u2Prime T U1 U2 z) : y ∈ U2 ∧ T.degree y = 2 := by
  have hy0 := (Finset.mem_sdiff.mp hy).1
  exact ⟨(Finset.mem_inter.mp hy0).2, (mem_degreeTwoVertices (T := T)).mp
    (Finset.mem_inter.mp hy0).1⟩

theorem u1Prime_mem_side_degree {U1 U2 : Finset V} {z y : V}
    (hy : y ∈ u1Prime T U1 U2 z) : y ∈ U1 ∧ T.degree y = 2 := by
  have hy0 := (Finset.mem_sdiff.mp hy).1
  have hy1 := (Finset.mem_sdiff.mp hy0).1
  exact ⟨(Finset.mem_inter.mp hy1).2, (mem_degreeTwoVertices (T := T)).mp
    (Finset.mem_inter.mp hy1).1⟩

theorem u2Prime_endpoint_degree_le {U1 U2 : Finset V} {z y u : V}
    (hbi : T.IsBipartiteWith (U1 : Set V) (U2 : Set V))
    (hy : y ∈ u2Prime T U1 U2 z) (hyu : T.Adj y u) : T.degree u ≤ 2 := by
  have hySide := (u2Prime_mem_side_degree (T := T) hy).1
  have huSide := hbi.symm.mem_of_mem_adj hySide hyu
  have hyNot := (Finset.mem_sdiff.mp hy).2
  by_contra hdeg
  have huBranch : u ∈ branchingVertices T ∩ U1 := by
    apply Finset.mem_inter.mpr
    exact ⟨(mem_branchingVertices (T := T)).mpr (by omega), huSide⟩
  apply hyNot
  apply (mem_neighborsOf (T := T)).mpr
  exact ⟨u, Finset.mem_union_left _ huBranch, hyu.symm⟩

theorem u1Prime_endpoint_degree_le {U1 U2 : Finset V} {z y u : V}
    (hbi : T.IsBipartiteWith (U1 : Set V) (U2 : Set V))
    (hy : y ∈ u1Prime T U1 U2 z) (hyu : T.Adj y u) : T.degree u ≤ 2 := by
  have hySide := (u1Prime_mem_side_degree (T := T) hy).1
  have huSide := hbi.mem_of_mem_adj hySide hyu
  have hyNot := (Finset.mem_sdiff.mp hy).2
  by_contra hdeg
  have huBranch : u ∈ branchingVertices T ∩ U2 := by
    apply Finset.mem_inter.mpr
    exact ⟨(mem_branchingVertices (T := T)).mpr (by omega), huSide⟩
  apply hyNot
  apply (mem_neighborsOf (T := T)).mpr
  exact ⟨u, huBranch, hyu.symm⟩

theorem u2SpecialCenters_isSpecial {U1 U2 : Finset V} {z y : V}
    (hbi : T.IsBipartiteWith (U1 : Set V) (U2 : Set V))
    (hy : y ∈ u2SpecialCenters T U1 U2 z) : IsSpecialTwoPathCenter T y := by
  have hyPrime : y ∈ u2Prime T U1 U2 z := (Finset.mem_sdiff.mp hy).1
  have hyNot := (Finset.mem_sdiff.mp hy).2
  have hySideDeg := u2Prime_mem_side_degree (T := T) hyPrime
  refine ⟨hySideDeg.2, ?_⟩
  intro x hx
  by_contra hxdeg
  have hxBranch : 3 ≤ T.degree x := by omega
  obtain ⟨u, huNy, hux⟩ := (mem_neighborsOf (T := T)).mp hx
  have hyu : T.Adj y u := (T.mem_neighborFinset y u).mp huNy
  have huSide := hbi.symm.mem_of_mem_adj hySideDeg.1 hyu
  have hxSide := hbi.mem_of_mem_adj huSide hux
  have hxBU2 : x ∈ branchingVertices T ∩ U2 := by
    exact Finset.mem_inter.mpr ⟨(mem_branchingVertices (T := T)).mpr hxBranch, hxSide⟩
  apply hyNot
  apply (mem_neighborsOf (T := T)).mpr
  refine ⟨u, ?_, hyu.symm⟩
  apply (mem_neighborsOf (T := T)).mpr
  exact ⟨x, hxBU2, hux.symm⟩

theorem u2SpecialCenters_avoids_z {U1 U2 : Finset V} {z y : V}
    (hbi : T.IsBipartiteWith (U1 : Set V) (U2 : Set V)) (hz : z ∈ U1)
    (hy : y ∈ u2SpecialCenters T U1 U2 z) : z ∉ twoPathVertices T y := by
  have hyPrime : y ∈ u2Prime T U1 U2 z := (Finset.mem_sdiff.mp hy).1
  have hySide := (u2Prime_mem_side_degree (T := T) hyPrime).1
  have hyNot := (Finset.mem_sdiff.mp hyPrime).2
  rw [mem_twoPathVertices]
  rintro (rfl | hyz)
  · exact Set.disjoint_left.mp hbi.disjoint hz hySide
  · apply hyNot
    apply (mem_neighborsOf (T := T)).mpr
    exact ⟨z, Finset.mem_union_right _ (by simp), hyz.symm⟩

theorem u1Prime_avoids_z {U1 U2 : Finset V} {z y : V}
    (hbi : T.IsBipartiteWith (U1 : Set V) (U2 : Set V)) (hz : z ∈ U1)
    (hy : y ∈ u1Prime T U1 U2 z) : z ∉ twoPathVertices T y := by
  have hy0 := (Finset.mem_sdiff.mp hy).1
  have hyNotZ := (Finset.mem_sdiff.mp hy0).2
  have hySide := (u1Prime_mem_side_degree (T := T) hy).1
  rw [mem_twoPathVertices]
  rintro (rfl | hyz)
  · exact hyNotZ (by simp)
  · have hzSide := hbi.mem_of_mem_adj hySide hyz
    exact Set.disjoint_left.mp hbi.disjoint hz hzSide

/-- A family of degree-two paths centered in `U₂` occupies at most two
vertices of `U₁` per path. -/
theorem card_part_inter_pathUnion_le_two_mul
    {U1 U2 P : Finset V}
    (hbi : T.IsBipartiteWith (U1 : Set V) (U2 : Set V))
    (hP : ∀ y ∈ P, y ∈ U2 ∧ T.degree y = 2) :
    (U1 ∩ P.biUnion (twoPathVertices T)).card ≤ 2 * P.card := by
  have hsubset : U1 ∩ P.biUnion (twoPathVertices T) ⊆
      P.biUnion (fun y => T.neighborFinset y) := by
    intro x hx
    have hxU1 := (Finset.mem_inter.mp hx).1
    obtain ⟨y, hyP, hxy⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hx).2
    have hyU2 := (hP y hyP).1
    have hxy' := (mem_twoPathVertices (T := T)).mp hxy
    rcases hxy' with rfl | hyx
    · exact (Set.disjoint_left.mp hbi.disjoint hxU1 hyU2).elim
    · exact Finset.mem_biUnion.mpr ⟨y, hyP, (T.mem_neighborFinset y x).mpr hyx⟩
  have hunion := Finset.card_biUnion_le
    (s := P) (t := fun y => T.neighborFinset y)
  have hsum : ∑ y ∈ P, (T.neighborFinset y).card = 2 * P.card := by
    calc
      ∑ y ∈ P, (T.neighborFinset y).card = ∑ _y ∈ P, 2 := by
        apply Finset.sum_congr rfl
        intro y hy
        simpa [T.card_neighborFinset_eq_degree, (hP y hy).2]
      _ = 2 * P.card := by simp [mul_comm]
  rw [hsum] at hunion
  exact (Finset.card_le_card hsubset).trans hunion

/-- If a `U₁`-centered path meets a `U₂`-centered path, its center is
already a vertex of the latter path. -/
theorem center_mem_of_cross_paths_not_disjoint
    {U1 U2 : Finset V}
    (hbi : T.IsBipartiteWith (U1 : Set V) (U2 : Set V))
    {p q : V} (hp : p ∈ U2) (hq : q ∈ U1)
    (hmeet : ¬Disjoint (twoPathVertices T p) (twoPathVertices T q)) :
    q ∈ twoPathVertices T p := by
  obtain ⟨x, hxp, hxq⟩ := Finset.not_disjoint_iff.mp hmeet
  rw [mem_twoPathVertices] at hxp hxq
  rcases hxp with rfl | hpx
  · rcases hxq with hpq | hqx
    · subst q
      exact (Set.disjoint_left.mp hbi.disjoint hq hp).elim
    · exact (mem_twoPathVertices (T := T)).mpr (Or.inr hqx.symm)
  · rcases hxq with rfl | hqx
    · exact (mem_twoPathVertices (T := T)).mpr (Or.inr hpx)
    · have hxU1 := hbi.symm.mem_of_mem_adj hp hpx
      exact (Set.disjoint_left.mp hbi.disjoint hq
        (hbi.mem_of_mem_adj hxU1 hqx.symm)).elim

/-- Zhao, Proposition 7.11(3), in a center-based representation of 2-paths.
For a degree-two center `v`, `twoPathVertices T v` is exactly its 3-vertex
2-path.  The two returned center sets therefore represent `5l` special
`U₂`-2-paths and `4l` `U₁`-2-paths, all mutually vertex-disjoint and all
avoiding `z`. -/
theorem IsTree.exists_proposition711_path_packing
    [Nontrivial V] (hT : T.IsTree) {U1 U2 : Finset V} {z : V}
    (hbi : T.IsBipartiteWith (U1 : Set V) (U2 : Set V)) (hz : z ∈ U1)
    (hU1 : 26 * (leaves T).card ≤ U1.card)
    (hU2 : 26 * (leaves T).card ≤ U2.card) :
    ∃ P Q : Finset V,
      P ⊆ u2SpecialCenters T U1 U2 z ∧
      P.card = 5 * (leaves T).card ∧
      (P : Set V).PairwiseDisjoint (twoPathVertices T) ∧
      Q ⊆ u1Prime T U1 U2 z ∧
      Q.card = 4 * (leaves T).card ∧
      (Q : Set V).PairwiseDisjoint (twoPathVertices T) ∧
      (∀ p ∈ P, ∀ q ∈ Q,
        Disjoint (twoPathVertices T p) (twoPathVertices T q)) ∧
      (∀ p ∈ P, IsSpecialTwoPathCenter T p) ∧
      (∀ p ∈ P, z ∉ twoPathVertices T p) ∧
      (∀ q ∈ Q, z ∉ twoPathVertices T q) := by
  let l := (leaves T).card
  let D2 := u2SpecialCenters T U1 U2 z
  have hD2side : ∀ y ∈ D2, y ∈ U2 ∧ T.degree y = 2 := by
    intro y hy
    exact u2Prime_mem_side_degree (T := T) (Finset.mem_sdiff.mp hy).1
  have hD2end : ∀ y ∈ D2, ∀ u, T.Adj y u → T.degree u ≤ 2 := by
    intro y hy u hyu
    exact u2Prime_endpoint_degree_le (T := T) hbi (Finset.mem_sdiff.mp hy).1 hyu
  have hD2large0 :=
    IsTree.card_u2_le_card_special_add_eleven_leaves (T := T) (z := z) hT hbi
  have hD2large : 3 * (5 * l) ≤ D2.card := by
    dsimp only [l, D2]
    omega
  have hD2ne : ∀ y ∈ D2, (twoPathVertices T y).Nonempty := by
    intro y hy
    exact ⟨y, by simp [twoPathVertices]⟩
  have hD2conflict : ∀ y ∈ D2,
      (D2.filter fun w => ¬Disjoint (twoPathVertices T y) (twoPathVertices T w)).card ≤ 3 := by
    intro y hy
    exact card_conflicting_twoPathCenters_le_three (T := T) hbi.symm D2 hD2side hy
      (hD2end y hy)
  obtain ⟨P, hPD2, hPcard, hPdisj⟩ :=
    exists_disjoint_support_packing (twoPathVertices T) D2 3 (5 * l)
      (by omega) hD2ne hD2conflict hD2large
  let occupied := P.biUnion (twoPathVertices T)
  let D1 := u1Prime T U1 U2 z \ occupied
  have hPside : ∀ y ∈ P, y ∈ U2 ∧ T.degree y = 2 := by
    intro y hy
    exact hD2side y (hPD2 hy)
  have hoccupied : (U1 ∩ occupied).card ≤ 2 * P.card := by
    exact card_part_inter_pathUnion_le_two_mul (T := T) hbi hPside
  have hprimeLarge :=
    IsTree.card_u1_le_card_u1Prime_add_four_leaves (T := T) (z := z) hT hbi
  have hinter : (u1Prime T U1 U2 z ∩ occupied).card ≤ (U1 ∩ occupied).card := by
    apply Finset.card_le_card
    intro y hy
    have hyPrime := (Finset.mem_inter.mp hy).1
    exact Finset.mem_inter.mpr ⟨(u1Prime_mem_side_degree (T := T) hyPrime).1,
      (Finset.mem_inter.mp hy).2⟩
  have hsplitPrime := Finset.card_sdiff_add_card_inter
    (u1Prime T U1 U2 z) occupied
  have hD1split : D1.card + (u1Prime T U1 U2 z ∩ occupied).card =
      (u1Prime T U1 U2 z).card := by
    simpa only [D1] using hsplitPrime
  have hD1large : 3 * (4 * l) ≤ D1.card := by
    dsimp only [l]
    omega
  have hD1side : ∀ y ∈ D1, y ∈ U1 ∧ T.degree y = 2 := by
    intro y hy
    exact u1Prime_mem_side_degree (T := T) (Finset.mem_sdiff.mp hy).1
  have hD1ne : ∀ y ∈ D1, (twoPathVertices T y).Nonempty := by
    intro y hy
    exact ⟨y, by simp [twoPathVertices]⟩
  have hD1conflict : ∀ y ∈ D1,
      (D1.filter fun w => ¬Disjoint (twoPathVertices T y) (twoPathVertices T w)).card ≤ 3 := by
    intro y hy
    exact card_conflicting_twoPathCenters_le_three (T := T) hbi D1 hD1side hy
      (fun u hyu => u1Prime_endpoint_degree_le (T := T) hbi
        (Finset.mem_sdiff.mp hy).1 hyu)
  obtain ⟨Q, hQD1, hQcard, hQdisj⟩ :=
    exists_disjoint_support_packing (twoPathVertices T) D1 3 (4 * l)
      (by omega) hD1ne hD1conflict hD1large
  have hQprime : Q ⊆ u1Prime T U1 U2 z := by
    intro q hq
    exact (Finset.mem_sdiff.mp (hQD1 hq)).1
  have hcross : ∀ p ∈ P, ∀ q ∈ Q,
      Disjoint (twoPathVertices T p) (twoPathVertices T q) := by
    intro p hp q hq
    by_contra hmeet
    have hqOcc : q ∈ occupied := by
      apply Finset.mem_biUnion.mpr
      exact ⟨p, hp, center_mem_of_cross_paths_not_disjoint (T := T) hbi
        (hPside p hp).1 (hD1side q (hQD1 hq)).1 hmeet⟩
    exact (Finset.mem_sdiff.mp (hQD1 hq)).2 hqOcc
  refine ⟨P, Q, hPD2, ?_, hPdisj, hQprime, ?_, hQdisj, hcross, ?_, ?_, ?_⟩
  · simpa only [l] using hPcard
  · simpa only [l] using hQcard
  · intro p hp
    exact u2SpecialCenters_isSpecial (T := T) hbi (hPD2 hp)
  · intro p hp
    exact u2SpecialCenters_avoids_z (T := T) hbi hz (hPD2 hp)
  · intro q hq
    exact u1Prime_avoids_z (T := T) hbi hz (hQprime hq)

/-- Proposition 7.11(3) with precisely Zhao's stated hypotheses.  The
nontrivial-tree proof above contains the substance; the one-vertex tree has
no leaves and hence asks for two empty families. -/
theorem IsTree.exists_proposition711_path_packing_exact
    (hT : T.IsTree) {U1 U2 : Finset V} {z : V}
    (hbi : T.IsBipartiteWith (U1 : Set V) (U2 : Set V)) (hz : z ∈ U1)
    (hU1 : 26 * (leaves T).card ≤ U1.card)
    (hU2 : 26 * (leaves T).card ≤ U2.card) :
    ∃ P Q : Finset V,
      P ⊆ u2SpecialCenters T U1 U2 z ∧
      P.card = 5 * (leaves T).card ∧
      (P : Set V).PairwiseDisjoint (twoPathVertices T) ∧
      Q ⊆ u1Prime T U1 U2 z ∧
      Q.card = 4 * (leaves T).card ∧
      (Q : Set V).PairwiseDisjoint (twoPathVertices T) ∧
      (∀ p ∈ P, ∀ q ∈ Q,
        Disjoint (twoPathVertices T p) (twoPathVertices T q)) ∧
      (∀ p ∈ P, IsSpecialTwoPathCenter T p) ∧
      (∀ p ∈ P, z ∉ twoPathVertices T p) ∧
      (∀ q ∈ Q, z ∉ twoPathVertices T q) := by
  classical
  cases subsingleton_or_nontrivial V with
  | inr hnontrivial =>
      letI : Nontrivial V := hnontrivial
      exact IsTree.exists_proposition711_path_packing (T := T) hT hbi hz hU1 hU2
  | inl hsubsingleton =>
      letI : Subsingleton V := hsubsingleton
      have hleaf : leaves T = ∅ := by
        ext v
        simp [leaves, T.degree_eq_zero_of_subsingleton]
      refine ⟨∅, ∅, ?_⟩
      simp [hleaf]

/-- Proposition 7.11(3) with a conclusion stated only in semantic path
language (the auxiliary pruning sets are hidden). -/
theorem IsTree.proposition711_part3
    (hT : T.IsTree) {U1 U2 : Finset V} {z : V}
    (hbi : T.IsBipartiteWith (U1 : Set V) (U2 : Set V)) (hz : z ∈ U1)
    (hU1 : 26 * (leaves T).card ≤ U1.card)
    (hU2 : 26 * (leaves T).card ≤ U2.card) :
    ∃ P Q : Finset V,
      P.card = 5 * (leaves T).card ∧
      Q.card = 4 * (leaves T).card ∧
      (P : Set V).PairwiseDisjoint (twoPathVertices T) ∧
      (Q : Set V).PairwiseDisjoint (twoPathVertices T) ∧
      (∀ p ∈ P, ∀ q ∈ Q,
        Disjoint (twoPathVertices T p) (twoPathVertices T q)) ∧
      (∀ p ∈ P, p ∈ U2 ∧ IsSpecialTwoPathCenter T p) ∧
      (∀ q ∈ Q, q ∈ U1 ∧ T.degree q = 2) ∧
      (∀ p ∈ P, z ∉ twoPathVertices T p) ∧
      (∀ q ∈ Q, z ∉ twoPathVertices T q) := by
  obtain ⟨P, Q, hPsub, hPcard, hPdisj, hQsub, hQcard, hQdisj,
    hcross, hPspecial, hPz, hQz⟩ :=
    IsTree.exists_proposition711_path_packing_exact (T := T) hT hbi hz hU1 hU2
  refine ⟨P, Q, hPcard, hQcard, hPdisj, hQdisj, hcross, ?_, ?_, hPz, hQz⟩
  · intro p hp
    exact ⟨(u2Prime_mem_side_degree (T := T)
      (Finset.mem_sdiff.mp (hPsub hp)).1).1, hPspecial p hp⟩
  · intro q hq
    exact u1Prime_mem_side_degree (T := T) (hQsub hq)

/-- Number of neighbors of `v` lying in a prescribed finite set. -/
def degreeInto (v : V) (S : Finset V) : ℕ :=
  (S.filter fun w => T.Adj v w).card

/-- The precise Hall lemma used after Proposition 7.11 in Zhao's proof:
in a balanced bipartite graph, weak half-degree on one side and strict
half-degree on the other give a perfect matching. -/
theorem exists_bijective_adj_of_balanced_half_degrees
    {X Y : Finset V}
    (hcard : X.card = Y.card)
    (hleft : ∀ x ∈ X, X.card < 2 * degreeInto T x Y)
    (hright : ∀ y ∈ Y, X.card ≤ 2 * degreeInto T y X) :
    ∃ f : X → Y, Function.Bijective f ∧ ∀ x : X, T.Adj x (f x) := by
  classical
  let t : X → Finset V := fun x => Y.filter fun y => T.Adj x y
  have hHall : ∀ A : Finset X, A.card ≤ (A.biUnion t).card := by
    intro A
    let N := A.biUnion t
    by_cases hAempty : A = ∅
    · simp [hAempty]
    by_cases hsmall : 2 * A.card ≤ X.card
    · obtain ⟨x, hxA⟩ := Finset.nonempty_iff_ne_empty.mpr hAempty
      have hxX : (x : V) ∈ X := x.property
      have hdeg := hleft x hxX
      have hsub : (t x).card ≤ N.card :=
        Finset.card_le_card (Finset.subset_biUnion_of_mem t hxA)
      change A.card ≤ N.card
      change X.card < 2 * (t x).card at hdeg
      change A.card ≤ N.card
      omega
    · have hlarge : X.card < 2 * A.card := by omega
      have hNY : N = Y := by
        apply Finset.Subset.antisymm
        · intro y hyN
          obtain ⟨x, _hxA, hy⟩ := Finset.mem_biUnion.mp hyN
          exact (Finset.mem_filter.mp hy).1
        · intro y hyY
          by_contra hyN
          have hydeg := hright y hyY
          have hsubset : X.filter (fun x => T.Adj y x) ⊆
              X \ A.image Subtype.val := by
            intro x hx
            have hxX := (Finset.mem_filter.mp hx).1
            have hyx := (Finset.mem_filter.mp hx).2
            apply Finset.mem_sdiff.mpr
            refine ⟨hxX, ?_⟩
            intro hxAimage
            obtain ⟨a, haA, rfl⟩ := Finset.mem_image.mp hxAimage
            apply hyN
            apply Finset.mem_biUnion.mpr
            refine ⟨a, haA, ?_⟩
            exact Finset.mem_filter.mpr ⟨hyY, hyx.symm⟩
          have hdeg_le : degreeInto T y X ≤ X.card - A.card := by
            have hc := Finset.card_le_card hsubset
            rw [Finset.card_sdiff_of_subset] at hc
            · rw [Finset.card_image_of_injective _ Subtype.val_injective] at hc
              simpa only [degreeInto] using hc
            · intro x hx
              obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
              exact a.property
          have hAX : A.card ≤ X.card := by
            simpa using Finset.card_le_univ A
          omega
      change A.card ≤ N.card
      rw [hNY, ← hcard]
      simpa using Finset.card_le_univ A
  obtain ⟨f, hfinj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  let f' : X → Y := fun x => ⟨f x, (Finset.mem_filter.mp (hfmem x)).1⟩
  have hf'inj : Function.Injective f' := by
    intro x x' h
    apply hfinj
    exact congrArg Subtype.val h
  have hf'bij : Function.Bijective f' :=
    (Fintype.bijective_iff_injective_and_card f').mpr
      ⟨hf'inj, by simpa [Fintype.card_coe] using hcard⟩
  refine ⟨f', hf'bij, ?_⟩
  intro x
  exact (Finset.mem_filter.mp (hfmem x)).2

end SimpleGraph

end ZhaoProp711

#print axioms ZhaoProp711.SimpleGraph.IsTree.sum_branching_degree_sub_two
#print axioms ZhaoProp711.SimpleGraph.IsTree.card_neighborsOf_le
#print axioms ZhaoProp711.SimpleGraph.IsTree.exists_proposition711_path_packing_exact
#print axioms ZhaoProp711.SimpleGraph.IsTree.proposition711_part3
#print axioms ZhaoProp711.SimpleGraph.exists_bijective_adj_of_balanced_half_degrees
