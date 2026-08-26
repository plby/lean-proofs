/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos73.UniqueLinkageOrdering

/-!
# Ordered connected columns of a unique spanning linkage

The interval selection used in the linkage lemma is proved directly by
greedy induction. Closed rank intervals give the bound `m + 1`, including
singleton columns. See `tex/73.tex`, the ordered connected columns lemma.
-/

namespace Erdos73

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

/-- A finite family of nonempty closed intervals of overlap at most `d`
has a disjoint subfamily containing at least a `1/d` fraction of it.
The multiplicative conclusion also covers `d = 0` and the empty family. -/
theorem exists_disjoint_intervals_of_bounded_overlap
    {I : Type*} (s : Finset I) (a b : I → ℕ) (d : ℕ)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hload : ∀ t, (s.filter fun i ↦ a i ≤ t ∧ t ≤ b i).card ≤ d) :
    ∃ J ⊆ s, (J : Set I).Pairwise (fun i j ↦ b i < a j ∨ b j < a i) ∧
      s.card ≤ d * J.card := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi, hmin⟩ := s.exists_min_image b hs
      let r := s.filter fun j ↦ b i < a j
      have hrs : r ⊆ s := Finset.filter_subset _ _
      have hir : i ∉ r := by
        intro h
        exact (not_lt_of_ge (hab i hi)) (Finset.mem_filter.mp h).2
      have hrstrict : r ⊂ s := Finset.ssubset_iff_subset_ne.mpr
        ⟨hrs, fun h ↦ hir (h.symm ▸ hi)⟩
      obtain ⟨J, hJr, hJpair, hJcard⟩ := ih r hrstrict
        (fun j hj ↦ hab j (hrs hj)) (fun t ↦
          (Finset.card_le_card (Finset.filter_subset_filter _ hrs)).trans (hload t))
      have hiJ : i ∉ J := fun h ↦ hir (hJr h)
      have hremoved : (s \ r).card ≤ d := by
        apply le_trans (Finset.card_le_card ?_) (hload (b i))
        intro j hj
        obtain ⟨hjs, hjr⟩ := Finset.mem_sdiff.mp hj
        refine Finset.mem_filter.mpr ⟨hjs, ?_, hmin j hjs⟩
        by_contra h
        exact hjr (Finset.mem_filter.mpr ⟨hjs, lt_of_not_ge h⟩)
      refine ⟨insert i J, Finset.insert_subset hi (hJr.trans hrs), ?_, ?_⟩
      · intro j hj k hk hjk
        rcases Finset.mem_insert.mp hj with rfl | hjJ
        · have hkJ := (Finset.mem_insert.mp hk).resolve_left (Ne.symm hjk)
          exact Or.inl (Finset.mem_filter.mp (hJr hkJ)).2
        · rcases Finset.mem_insert.mp hk with rfl | hkJ
          · exact Or.inr (Finset.mem_filter.mp (hJr hjJ)).2
          · exact hJpair hjJ hkJ hjk
      · rw [Finset.card_insert_of_notMem hiJ, Nat.mul_add, Nat.mul_one]
        have hcount := Finset.card_sdiff_add_card_eq_card hrs
        omega
    · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
      · simp
      · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

/-- Disjoint sets that each meet a finite set inject into that set. -/
theorem card_le_of_pairwise_disjoint_hits
    {I V : Type*} (s : Finset I) (Q : I → Finset V) (S : Finset V)
    (hdisj : (s : Set I).Pairwise fun i j ↦ Disjoint (Q i) (Q j))
    (hhit : ∀ i ∈ s, ∃ v ∈ Q i, v ∈ S) : s.card ≤ S.card := by
  choose f hfQ hfS using hhit
  let F : {i // i ∈ s} → {v // v ∈ S} := fun i ↦ ⟨f i i.2, hfS i i.2⟩
  have hF : Function.Injective F := by
    intro i j heq
    apply Subtype.ext
    by_contra hij
    have hv : f i i.2 = f j j.2 := congrArg Subtype.val heq
    exact Finset.disjoint_left.mp (hdisj i.2 j.2 hij)
      (hfQ i i.2) (hv ▸ hfQ j j.2)
  simpa using Fintype.card_le_of_injective F hF

end
end Erdos73

namespace Erdos73Infrastructure.SimpleGraph.PathSlicing.LinkageOrdering

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {V I : Type*} [Fintype V] [Fintype I]
variable {G : _root_.SimpleGraph V} {A B : Finset V}
variable {R : PerfectPathPacking G A B}

/-- A connected column with vertices on both rank sides meets the
threshold separator. -/
theorem connected_inter_separator
    (theta : LinkageOrdering R) (Q : Finset V)
    (hQ : (G.induce (Q : Set V)).Connected) (t : ℕ)
    {x y : V} (hx : x ∈ Q) (hy : y ∈ Q)
    (hxt : theta.rank x < t) (hty : t ≤ theta.rank y) :
    ∃ v ∈ Q, v ∈ theta.separatorSet t := by
  let P := GraphPath.ofConnectedInduce Q hQ x y hx hy
  have hcross : GraphPathCrossesRankThreshold theta.rank t P :=
    ⟨x, P.source_mem_vertexSet, y, P.target_mem_vertexSet, hxt, hty⟩
  obtain ⟨v, hvP, hvS⟩ := theta.separator_blocks t P hcross
  exact ⟨v, GraphPath.ofConnectedInduce_vertexSet_subset Q hQ x y hx hy hvP, hvS⟩

/-- At most one column can have any prescribed minimum rank. -/
theorem card_rank_fiber_le_one
    (theta : LinkageOrdering R) (Q : I → Finset V)
    (hdisj : Pairwise fun i j ↦ Disjoint (Q i) (Q j))
    (x : I → V) (hx : ∀ i, x i ∈ Q i) (t : ℕ) :
    (Finset.univ.filter fun i ↦ theta.rank (x i) = t).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have heq : x i = x j := theta.rank_injective
    ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  by_contra hij
  exact Finset.disjoint_left.mp (hdisj hij) (hx i) (heq ▸ hx j)

/-- Pairwise disjoint connected columns have closed rank intervals with
pointwise overlap at most the number of linkage rows plus one. -/
theorem rank_interval_overlap_le
    (theta : LinkageOrdering R) (Q : I → Finset V)
    (hconn : ∀ i, (G.induce (Q i : Set V)).Connected)
    (hdisj : Pairwise fun i j ↦ Disjoint (Q i) (Q j))
    (x y : I → V) (hx : ∀ i, x i ∈ Q i) (hy : ∀ i, y i ∈ Q i)
    (t : ℕ) :
    (Finset.univ.filter fun i ↦ theta.rank (x i) ≤ t ∧ t ≤ theta.rank (y i)).card
      ≤ R.card + 1 := by
  let C := Finset.univ.filter fun i ↦ theta.rank (x i) < t ∧ t ≤ theta.rank (y i)
  let L := Finset.univ.filter fun i ↦ theta.rank (x i) = t
  have hC : C.card ≤ R.card := by
    apply le_trans (Erdos73.card_le_of_pairwise_disjoint_hits C Q
      (theta.separatorSet t) (fun i _ j _ hij ↦ hdisj hij) ?_)
      (theta.separator_card_le t)
    intro i hi
    exact theta.connected_inter_separator (Q i) (hconn i) t (hx i) (hy i)
      (Finset.mem_filter.mp hi).2.1 (Finset.mem_filter.mp hi).2.2
  have hL : L.card ≤ 1 := theta.card_rank_fiber_le_one Q hdisj x hx t
  have hsub : (Finset.univ.filter fun i ↦
      theta.rank (x i) ≤ t ∧ t ≤ theta.rank (y i)) ⊆ C ∪ L := by
    intro i hi
    obtain ⟨_, hxt, hty⟩ := Finset.mem_filter.mp hi
    rcases lt_or_eq_of_le hxt with hlt | heq
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hlt, hty⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, heq⟩))
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le C L).trans
    (Nat.add_le_add hC hL))

/-- Select many connected columns that are strictly ordered in the
linkage rank. Every vertex of one selected column precedes every vertex
of the other; the direction may depend on the pair. -/
theorem exists_rankOrdered_connected_subfamily
    (theta : LinkageOrdering R) (Q : I → Finset V)
    (hne : ∀ i, (Q i).Nonempty)
    (hconn : ∀ i, (G.induce (Q i : Set V)).Connected)
    (hdisj : Pairwise fun i j ↦ Disjoint (Q i) (Q j)) :
    ∃ J : Finset I, Fintype.card I ≤ (R.card + 1) * J.card ∧
      (J : Set I).Pairwise (fun i j ↦
        (∀ x ∈ Q i, ∀ y ∈ Q j, theta.rank x < theta.rank y) ∨
        (∀ y ∈ Q j, ∀ x ∈ Q i, theta.rank y < theta.rank x)) := by
  have hmin : ∀ i, ∃ x ∈ Q i, ∀ v ∈ Q i, theta.rank x ≤ theta.rank v :=
    fun i ↦ (Q i).exists_min_image theta.rank (hne i)
  have hmax : ∀ i, ∃ y ∈ Q i, ∀ v ∈ Q i, theta.rank v ≤ theta.rank y :=
    fun i ↦ (Q i).exists_max_image theta.rank (hne i)
  choose x hx hxmin using hmin
  choose y hy hymax using hmax
  obtain ⟨J, _, hJpair, hJcard⟩ := Erdos73.exists_disjoint_intervals_of_bounded_overlap
    Finset.univ (fun i ↦ theta.rank (x i)) (fun i ↦ theta.rank (y i)) (R.card + 1)
    (fun i _ ↦ hxmin i (y i) (hy i))
    (theta.rank_interval_overlap_le Q hconn hdisj x y hx hy)
  refine ⟨J, by simpa using hJcard, ?_⟩
  intro i hi j hj hij
  rcases hJpair hi hj hij with h | h
  · exact Or.inl (fun v hv w hw ↦ (hymax i v hv).trans_lt (h.trans_le (hxmin j w hw)))
  · exact Or.inr (fun w hw v hv ↦ (hymax j w hw).trans_lt (h.trans_le (hxmin i v hv)))

/-- Strict rank order on one linkage row implies its ordinary path order. -/
theorem before_of_rank_lt
    (theta : LinkageOrdering R) (r : R.Index) {x y : V}
    (hx : x ∈ (R.path r).vertexSet) (hy : y ∈ (R.path r).vertexSet)
    (hxy : theta.rank x < theta.rank y) : (R.path r).Before x y := by
  apply (R.path r).before_iff_vertexIndex_le.mpr
  refine ⟨hx, hy, ?_⟩
  by_contra h
  have hyx : (R.path r).Before y x := (R.path r).before_iff_vertexIndex_le.mpr
    ⟨hy, hx, (lt_of_not_ge h).le⟩
  have hne : y ≠ x := fun heq ↦ (by simpa [heq] using hxy : False)
  exact (theta.row_strict r hy hx hyx hne).asymm hxy

/-- Select and explicitly enumerate any prescribed number of ordered
columns permitted by the multiplicative cardinality bound. -/
theorem exists_ordered_connected_columns
    (theta : LinkageOrdering R) (Q : I → Finset V)
    (hne : ∀ i, (Q i).Nonempty)
    (hconn : ∀ i, (G.induce (Q i : Set V)).Connected)
    (hdisj : Pairwise fun i j ↦ Disjoint (Q i) (Q j))
    (n : ℕ) (hsize : (R.card + 1) * n ≤ Fintype.card I) :
    ∃ e : Fin n ↪ I, ∀ i j, i < j →
      ∀ x ∈ Q (e i), ∀ y ∈ Q (e j), theta.rank x < theta.rank y := by
  obtain ⟨J, hJcard, hJpair⟩ :=
    theta.exists_rankOrdered_connected_subfamily Q hne hconn hdisj
  have hnJ : n ≤ J.card := Nat.le_of_mul_le_mul_left (hsize.trans hJcard) (by omega)
  choose x hx using hne
  have hkey : Function.Injective (fun i ↦ theta.rank (x i)) := by
    intro i j h
    have hv := theta.rank_injective h
    by_contra hij
    exact Finset.disjoint_left.mp (hdisj hij) (hx i) (hv ▸ hx j)
  letI : LinearOrder I := LinearOrder.lift' (fun i ↦ theta.rank (x i)) hkey
  let e := J.orderEmbOfCardLe hnJ
  refine ⟨e.toEmbedding, ?_⟩
  intro i j hij v hv w hw
  have heij : e i ≠ e j := e.injective.ne hij.ne
  have hijrank : theta.rank (x (e i)) < theta.rank (x (e j)) := e.strictMono hij
  rcases hJpair (J.orderEmbOfCardLe_mem hnJ i) (J.orderEmbOfCardLe_mem hnJ j) heij with
    hforward | hback
  · exact hforward v hv w hw
  · exact ((hback (x (e j)) (hx _) (x (e i)) (hx _)).asymm hijrank).elim

/-- The selected column ordering is simultaneously respected on every
row, not just by the auxiliary rank function. -/
theorem exists_pathOrdered_connected_columns
    (theta : LinkageOrdering R) (Q : I → Finset V)
    (hne : ∀ i, (Q i).Nonempty)
    (hconn : ∀ i, (G.induce (Q i : Set V)).Connected)
    (hdisj : Pairwise fun i j ↦ Disjoint (Q i) (Q j))
    (n : ℕ) (hsize : (R.card + 1) * n ≤ Fintype.card I) :
    ∃ e : Fin n ↪ I, ∀ i j, i < j → ∀ r : R.Index,
      ∀ x ∈ Q (e i), x ∈ (R.path r).vertexSet →
      ∀ y ∈ Q (e j), y ∈ (R.path r).vertexSet → (R.path r).Before x y := by
  obtain ⟨e, he⟩ := theta.exists_ordered_connected_columns Q hne hconn hdisj n hsize
  exact ⟨e, fun i j hij r x hx hxP y hy hyP ↦
    theta.before_of_rank_lt r hxP hyP (he i j hij x hx y hy)⟩

end
end Erdos73Infrastructure.SimpleGraph.PathSlicing.LinkageOrdering
