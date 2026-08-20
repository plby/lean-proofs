/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.CoreAHT

/-!
# Three components after deleting one vertex give a three-way cut

This is the component-to-certificate half of the elementary three-terminal
path/cut alternative.  It is deliberately stated independently of the
density hypotheses: whenever deletion of a vertex has three different
components, their carriers can be grouped into the three sides required by
`ThreeWayCut`.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Three distinct components of the complement of one vertex canonically
produce a `ThreeWayCut`.  The third side also absorbs every component other
than the first two. -/
theorem threeWayCut_of_three_components (d : V)
    (A B C : G.ComponentCompl ({d} : Set V))
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    Nonempty (ThreeWayCut G) := by
  classical
  let L : Finset V := (A : Set V).toFinset
  let M : Finset V := (B : Set V).toFinset
  let R : Finset V := Finset.univ \ insert d (L ∪ M)
  have hdL : d ∉ L := by
    intro hd
    have hdA : d ∈ (A : Set V) := by simpa only [L, Set.mem_toFinset] using hd
    exact (ComponentCompl.notMem_of_mem hdA) (by simp)
  have hdM : d ∉ M := by
    intro hd
    have hdB : d ∈ (B : Set V) := by simpa only [M, Set.mem_toFinset] using hd
    exact (ComponentCompl.notMem_of_mem hdB) (by simp)
  have hdR : d ∉ R := by simp [R]
  have hLM : Disjoint L M := by
    rw [Finset.disjoint_left]
    intro x hxL hxM
    have hxA : x ∈ (A : Set V) := by simpa only [L, Set.mem_toFinset] using hxL
    have hxB : x ∈ (B : Set V) := by simpa only [M, Set.mem_toFinset] using hxM
    exact Set.disjoint_left.mp (ComponentCompl.pairwise_disjoint hAB) hxA hxB
  have hLR : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro x hxL hxR
    have hxNot : x ∉ insert d (L ∪ M) := (Finset.mem_sdiff.mp hxR).2
    exact hxNot (by simp [hxL])
  have hMR : Disjoint M R := by
    rw [Finset.disjoint_left]
    intro x hxM hxR
    have hxNot : x ∉ insert d (L ∪ M) := (Finset.mem_sdiff.mp hxR).2
    exact hxNot (by simp [hxM])
  have hcover : insert d (L ∪ M ∪ R) = Finset.univ := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hxd : x = d
    · exact Or.inl hxd
    · by_cases hxL : x ∈ L
      · exact Or.inr (Or.inl (Or.inl hxL))
      · by_cases hxM : x ∈ M
        · exact Or.inr (Or.inl (Or.inr hxM))
        · apply Or.inr (Or.inr ?_)
          simp only [R, Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_union, not_or]
          exact ⟨hxd, hxL, hxM⟩
  have hLnonempty : L.Nonempty := by
    obtain ⟨x, hxA⟩ := ComponentCompl.nonempty A
    exact ⟨x, by simpa only [L, Set.mem_toFinset] using hxA⟩
  have hMnonempty : M.Nonempty := by
    obtain ⟨x, hxB⟩ := ComponentCompl.nonempty B
    exact ⟨x, by simpa only [M, Set.mem_toFinset] using hxB⟩
  have hRnonempty : R.Nonempty := by
    obtain ⟨x, hxC⟩ := ComponentCompl.nonempty C
    have hxd : x ≠ d := by
      intro h
      subst x
      exact (ComponentCompl.notMem_of_mem hxC) (by simp)
    have hxA : x ∉ (A : Set V) := by
      intro hxA
      exact Set.disjoint_left.mp (ComponentCompl.pairwise_disjoint hAC) hxA hxC
    have hxB : x ∉ (B : Set V) := by
      intro hxB
      exact Set.disjoint_left.mp (ComponentCompl.pairwise_disjoint hBC) hxB hxC
    refine ⟨x, ?_⟩
    simp only [R, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_union, not_or]
    exact ⟨hxd, by simpa only [L, Set.mem_toFinset],
      by simpa only [M, Set.mem_toFinset]⟩
  have hnotLM :
      ∀ x, x ∈ L → ∀ y, y ∈ M → ¬G.Adj x y := by
    intro x hxL y hyM hxy
    have hxA : x ∈ (A : Set V) := by simpa only [L, Set.mem_toFinset] using hxL
    have hyB : y ∈ (B : Set V) := by simpa only [M, Set.mem_toFinset] using hyM
    have hyK : y ∉ ({d} : Set V) := ComponentCompl.notMem_of_mem hyB
    have hyA : y ∈ (A : Set V) := ComponentCompl.mem_of_adj x y hxA hyK hxy
    exact Set.disjoint_left.mp (ComponentCompl.pairwise_disjoint hAB) hyA hyB
  have hnotLR :
      ∀ x, x ∈ L → ∀ y, y ∈ R → ¬G.Adj x y := by
    intro x hxL y hyR hxy
    have hxA : x ∈ (A : Set V) := by simpa only [L, Set.mem_toFinset] using hxL
    have hyNot : y ∉ insert d (L ∪ M) := (Finset.mem_sdiff.mp hyR).2
    have hyK : y ∉ ({d} : Set V) := by
      simpa only [Set.mem_singleton_iff] using fun hyd ↦ hyNot (by simp [hyd])
    have hyA : y ∈ (A : Set V) := ComponentCompl.mem_of_adj x y hxA hyK hxy
    exact hyNot (by
      apply Finset.mem_insert.mpr
      exact Or.inr (Finset.mem_union_left _ (by
        simpa only [L, Set.mem_toFinset] using hyA)))
  have hnotMR :
      ∀ x, x ∈ M → ∀ y, y ∈ R → ¬G.Adj x y := by
    intro x hxM y hyR hxy
    have hxB : x ∈ (B : Set V) := by simpa only [M, Set.mem_toFinset] using hxM
    have hyNot : y ∉ insert d (L ∪ M) := (Finset.mem_sdiff.mp hyR).2
    have hyK : y ∉ ({d} : Set V) := by
      simpa only [Set.mem_singleton_iff] using fun hyd ↦ hyNot (by simp [hyd])
    have hyB : y ∈ (B : Set V) := ComponentCompl.mem_of_adj x y hxB hyK hxy
    exact hyNot (by
      apply Finset.mem_insert.mpr
      exact Or.inr (Finset.mem_union_right _ (by
        simpa only [M, Set.mem_toFinset] using hyB)))
  exact ⟨
    { cut := d
      left := L
      middle := M
      right := R
      cut_not_left := hdL
      cut_not_middle := hdM
      cut_not_right := hdR
      left_disjoint_middle := hLM
      left_disjoint_right := hLR
      middle_disjoint_right := hMR
      cover := hcover
      left_nonempty := hLnonempty
      middle_nonempty := hMnonempty
      right_nonempty := hRnonempty
      not_adj_left_middle := hnotLM
      not_adj_left_right := hnotLR
      not_adj_middle_right := hnotMR }⟩

/-- Cardinal form: if deleting `d` leaves at least three connected components,
then `G` has a three-way cut. -/
theorem threeWayCut_of_three_le_card_componentCompl (d : V)
    (hthree : 3 ≤ Fintype.card (G.ComponentCompl ({d} : Set V))) :
    Nonempty (ThreeWayCut G) := by
  classical
  have hcard : Fintype.card (Fin 3) ≤
      Fintype.card (G.ComponentCompl ({d} : Set V)) := by simpa using hthree
  obtain ⟨f : Fin 3 ↪ G.ComponentCompl ({d} : Set V)⟩ :=
    Function.Embedding.nonempty_of_card_le hcard
  exact threeWayCut_of_three_components d (f 0) (f 1) (f 2)
    (f.injective.ne (by decide))
    (f.injective.ne (by decide))
    (f.injective.ne (by decide))

/-! ## The arithmetic block-counting core -/

/-- The numerical data supplied by a block decomposition into `k` blocks.

The edge equation says that blocks partition the edges.  The vertex equation
is the standard block identity: a connected block tree with `k` blocks counts
exactly `k - 1` cut vertices twice.  Keeping these two identities explicit
separates the finite arithmetic from the later block-tree construction. -/
structure BlockCountCertificate (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) where
  blocks : Fin k → Finset V
  two_le_card : ∀ i, 2 ≤ (blocks i).card
  vertex_sum_add_one :
    (∑ i : Fin k, (blocks i).card) + 1 = Fintype.card V + k
  edge_sum :
    (∑ i : Fin k,
      (G.induce ((blocks i : Finset V) : Set V)).edgeFinset.card) =
        G.edgeFinset.card

/-- Summing `(2,3)`-sparsity over a block decomposition with `k` blocks gives
the sharp global estimate `e + k + 2 ≤ 2v`. -/
theorem BlockCountCertificate.edge_card_add_k_add_two_le
    {k : ℕ} (D : BlockCountCertificate G k) (hsparse : Is23Sparse G) :
    G.edgeFinset.card + k + 2 ≤ 2 * Fintype.card V := by
  classical
  have hpoint (i : Fin k) :
      (G.induce (((D.blocks i : Finset V) : Set V))).edgeFinset.card + 3 ≤
        2 * (D.blocks i).card :=
    hsparse (D.blocks i) (D.two_le_card i)
  have hsum₀ := Finset.sum_le_sum fun i (_hi : i ∈ (Finset.univ : Finset (Fin k))) ↦
    hpoint i
  have hsum :
      (∑ i : Fin k,
          (G.induce (((D.blocks i : Finset V) : Set V))).edgeFinset.card) +
            3 * k ≤
        2 * (∑ i : Fin k, (D.blocks i).card) := by
    simpa [Finset.sum_add_distrib, Finset.mul_sum, mul_comm] using hsum₀
  rw [D.edge_sum] at hsum
  have hvertices := D.vertex_sum_add_one
  omega

/-- In particular, three or more blocks already give the `2v-5` estimate
needed in the false-twin deletion argument. -/
theorem BlockCountCertificate.edge_card_add_five_le
    {k : ℕ} (D : BlockCountCertificate G k) (hthree : 3 ≤ k)
    (hsparse : Is23Sparse G) :
    G.edgeFinset.card + 5 ≤ 2 * Fintype.card V := by
  have h := D.edge_card_add_k_add_two_le hsparse
  omega

/-! ## Rooted terminal paths -/

/-- A simple path rooted at `r`, ending at one of `a,b`, and containing the
other terminal as well.  This is the splicing-friendly form of the
three-point path theorem used when traversing a chain of blocks. -/
def HasRootedTwoTerminalPath (G : SimpleGraph V) (r a b : V) : Prop :=
  (∃ p : G.Walk r a, p.IsPath ∧ b ∈ p.support) ∨
    (∃ p : G.Walk r b, p.IsPath ∧ a ∈ p.support)

namespace HasRootedTwoTerminalPath

theorem symm {r a b : V} (h : HasRootedTwoTerminalPath G r a b) :
    HasRootedTwoTerminalPath G r b a := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- The root and both terminals occur on the displayed path. -/
theorem exists_path_support {r a b : V}
    (h : HasRootedTwoTerminalPath G r a b) :
    (∃ p : G.Walk r a, p.IsPath ∧ r ∈ p.support ∧
        a ∈ p.support ∧ b ∈ p.support) ∨
      (∃ p : G.Walk r b, p.IsPath ∧ r ∈ p.support ∧
        a ∈ p.support ∧ b ∈ p.support) := by
  rcases h with ⟨p, hp, hb⟩ | ⟨p, hp, ha⟩
  · exact Or.inl ⟨p, hp, p.start_mem_support, p.end_mem_support, hb⟩
  · exact Or.inr ⟨p, hp, p.start_mem_support, ha, p.end_mem_support⟩

end HasRootedTwoTerminalPath

/-! ## Path splicing at a cut vertex -/

/-- Two simple paths whose supports meet only at their common endpoint splice
to a simple path.  This is the walk-level operation used along a block chain. -/
theorem Walk.IsPath.append_of_support_inter_eq_endpoint
    {c r t : V} {q : G.Walk c r} {p : G.Walk r t}
    (hq : q.IsPath) (hp : p.IsPath)
    (hinter : ∀ x, x ∈ q.support → x ∈ p.support → x = r) :
    (q.append p).IsPath := by
  rw [Walk.isPath_def, Walk.support_append]
  apply List.nodup_append.mpr
  refine ⟨hq.support_nodup, hp.support_nodup.tail, ?_⟩
  intro x hxq y hyp hxy
  subst y
  have hxp' : x ∈ p.support := List.mem_of_mem_tail hyp
  have hxr : x = r := hinter x hxq hxp'
  subst x
  have hpN := hp.support_nodup
  rw [p.support_eq_cons] at hpN
  exact (List.nodup_cons.mp hpN).1 hyp

/-- The splice contains every vertex that occurred on either constituent
path. -/
theorem Walk.mem_support_append_of_mem_left
    {c r t x : V} (q : G.Walk c r) (p : G.Walk r t)
    (hx : x ∈ q.support) : x ∈ (q.append p).support := by
  exact q.support_subset_support_append_left p hx

theorem Walk.mem_support_append_of_mem_right
    {c r t x : V} (q : G.Walk c r) (p : G.Walk r t)
    (hx : x ∈ p.support) : x ∈ (q.append p).support := by
  exact q.support_subset_support_append_right p hx

end Erdos916
