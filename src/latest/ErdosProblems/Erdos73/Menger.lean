/-
Adapted from the Apache-2.0-licensed polynomial-grid-minor-theorem development,
https://github.com/EdouardBonnet/polynomial-grid-minor-theorem,
commit fe2848173913a00d85c64d2a17af63f2cf0d4fbf,
proofs/Lax17Proofs/Source/Menger.lean.
Local changes: import paths and namespace; Lean 4.33 compatibility changes.
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Find
import ErdosProblems.Erdos73.MengerDefs

namespace Erdos73Infrastructure

universe u v w

/-!
# Finite vertex Menger

This file keeps the reusable, contract-free surface for finite vertex-Menger:

* `(S,T)`-separators, exposed here as `BlocksAllPaths` for compatibility with
  the Chuzhoy--Tan Section 4 code;
* finite families of disjoint `S`-to-`T` paths;
* the weak Menger alternative used downstream;
* the minimum-separator and maximum-packing numbers;
* the easy inequality `maxPackingSize ≤ minSeparatorSize`;
* the endpoint-preserving augmentation theorem, by strong induction on the
  current family's vertex count;
* the reverse min-max inequality and the sharp Menger alternative.

The complete augmentation proof is included below. Its mathematical argument
is recorded in Lemma `finite-menger` of `tex/73.tex`.
-/

namespace SimpleGraph


/-- Compatibility name for ordinary `(S,T)`-separators. -/
abbrev BlocksAllPaths {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (S T J : Finset V) : Prop :=
  STSeparator G S T J

namespace BlocksAllPaths

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T J K : Finset V}

/-- Enlarging a blocking set preserves the blocking property. -/
theorem mono (hJ : BlocksAllPaths G S T J) (hsub : J ⊆ K) :
    BlocksAllPaths G S T K :=
  STSeparator.mono hJ hsub

/-- Shrinking the left terminal set preserves a blocking set. -/
theorem mono_left_terminals {S' : Finset V}
    (hS : S' ⊆ S) (hJ : BlocksAllPaths G S T J) :
    BlocksAllPaths G S' T J := by
  intro P hP
  apply hJ P
  rcases hP with hP | hP
  · exact Or.inl ⟨hS hP.1, hP.2⟩
  · exact Or.inr ⟨hP.1, hS hP.2⟩

/-- Shrinking the right terminal set preserves a blocking set. -/
theorem mono_right_terminals {T' : Finset V}
    (hT : T' ⊆ T) (hJ : BlocksAllPaths G S T J) :
    BlocksAllPaths G S T' J := by
  intro P hP
  apply hJ P
  rcases hP with hP | hP
  · exact Or.inl ⟨hP.1, hT hP.2⟩
  · exact Or.inr ⟨hT hP.1, hP.2⟩

/-- The full vertex set blocks every path. -/
theorem univ [Fintype V] :
    BlocksAllPaths G S T (Finset.univ : Finset V) := by
  intro P _hP
  exact ⟨P.source, GraphPath.source_mem_vertexSet P, by simp⟩

/-- If the left terminal set is empty, every set blocks all `S`-to-`T` paths. -/
theorem empty_left :
    BlocksAllPaths G (∅ : Finset V) T J := by
  intro P hP
  rcases hP with hP | hP <;> simp at hP

/-- If the right terminal set is empty, every set blocks all `S`-to-`T` paths. -/
theorem empty_right :
    BlocksAllPaths G S (∅ : Finset V) J := by
  intro P hP
  rcases hP with hP | hP <;> simp at hP

/-- The left terminal set itself blocks every path from `S` to `T`. -/
theorem left :
    BlocksAllPaths G S T S :=
  STSeparator.left

/-- The right terminal set itself blocks every path from `S` to `T`. -/
theorem right :
    BlocksAllPaths G S T T :=
  STSeparator.right

/-- Every blocker contains `S ∩ T`, because each vertex in the intersection is
a length-zero `S`-to-`T` path. -/
theorem inter_subset (hJ : BlocksAllPaths G S T J) :
    S ∩ T ⊆ J := by
  intro v hv
  rcases hJ (GraphPath.refl G v)
      (Or.inl ⟨(Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩) with
    ⟨w, hwPath, hwJ⟩
  have hw : w = v := by
    simpa [GraphPath.refl_vertexSet] using hwPath
  simpa [hw] using hwJ

/-- If `X` is not an `(S,T)`-separator, then there is an oriented
endpoint-clean `S`-to-`T` path avoiding `X`.  This is the formal version of
taking an arbitrary unblocked path and cutting it from its last `S`-vertex
before its first later `T`-vertex. -/
theorem exists_endpointClean_path_disjoint_of_not_blocks
    (hX : ¬ BlocksAllPaths G S T J) :
    ∃ P : GraphPath G, P.EndpointClean S T ∧ Disjoint P.vertexSet J := by
  classical
  unfold BlocksAllPaths STSeparator at hX
  push Not at hX
  rcases hX with ⟨P, hPconn, hPavoid⟩
  let Q := P.cleanBetweenTerminalSets hPconn
  refine ⟨Q, P.cleanBetweenTerminalSets_endpointClean hPconn, ?_⟩
  rw [Finset.disjoint_left]
  intro v hvQ hvJ
  exact hPavoid v (P.cleanBetweenTerminalSets_vertexSet_subset hPconn hvQ) hvJ

end BlocksAllPaths

/-- Compatibility name for the existence of at least `n` disjoint
`S`-to-`T` paths. -/
abbrev HasAtLeastDisjointPaths {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (S T : Finset V) (n : ℕ) : Prop :=
  HasDisjointSTPaths G S T n

namespace HasAtLeastDisjointPaths

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T J : Finset V} {n : ℕ}

/-- There are always at least zero disjoint paths. -/
theorem zero :
    HasAtLeastDisjointPaths G S T 0 :=
  HasDisjointSTPaths.zero

/-- A packing witnessing `n` disjoint paths cannot exceed the number of left
terminals. -/
theorem le_left_card (h : HasAtLeastDisjointPaths G S T n) :
    n ≤ S.card := by
  rcases h with ⟨P, hP⟩
  exact hP.trans (by
    simpa using Finset.card_le_card P.sourceSet_subset_left)

/-- A packing witnessing `n` disjoint paths cannot exceed the number of right
terminals. -/
theorem le_right_card (h : HasAtLeastDisjointPaths G S T n) :
    n ≤ T.card := by
  rcases h with ⟨P, hP⟩
  exact hP.trans (by
    simpa using Finset.card_le_card P.targetSet_subset_right)

/-- Any `n` vertices in `S ∩ T` give `n` disjoint trivial `S`-to-`T` paths. -/
theorem of_le_inter_card (h : n ≤ (S ∩ T).card) :
    HasAtLeastDisjointPaths G S T n := by
  classical
  rcases Finset.exists_subset_card_eq h with ⟨I, hI, hIcard⟩
  let P₀ := (PerfectPathPacking.refl G I).toPathPacking
  have hIS : I ⊆ S := by
    intro v hv
    exact (Finset.mem_inter.mp (hI hv)).1
  have hIT : I ⊆ T := by
    intro v hv
    exact (Finset.mem_inter.mp (hI hv)).2
  refine ⟨P₀.widenTerminals hIS hIT, ?_⟩
  rw [PathPacking.widenTerminals_card, PerfectPathPacking.toPathPacking_card,
    PerfectPathPacking.refl_card, hIcard]

/-- A linkage of size at least `n` contains a sub-linkage of size exactly `n`. -/
theorem exists_exact (h : HasAtLeastDisjointPaths G S T n) :
    ∃ P : PathPacking G S T, P.card = n := by
  rcases h with ⟨P, hP⟩
  rcases P.exists_indexSet_card_eq hP with ⟨I, _hIcard, hrestrict⟩
  exact ⟨P.restrictIndexSet I, hrestrict⟩

end HasAtLeastDisjointPaths

/-- The finite vertex-Menger alternative used by the Chuzhoy--Tan iteration:
either there are `n` disjoint `S`-to-`T` paths, or a vertex set of size at most
`n` blocks all such paths. -/
def MengerAlternative {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (S T : Finset V) (n : ℕ) : Prop :=
  HasAtLeastDisjointPaths G S T n ∨
    ∃ J : Finset V, J.card ≤ n ∧ BlocksAllPaths G S T J

namespace MengerAlternative

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T : Finset V} {n : ℕ}

/-- The Menger alternative is trivial for `n = 0`. -/
theorem zero :
    MengerAlternative G S T 0 :=
  Or.inl HasAtLeastDisjointPaths.zero

/-- If the left terminal set has size at most `n`, it is a valid separator. -/
theorem of_left_card_le (hS : S.card ≤ n) :
    MengerAlternative G S T n :=
  Or.inr ⟨S, hS, BlocksAllPaths.left⟩

/-- If the right terminal set has size at most `n`, it is a valid separator. -/
theorem of_right_card_le (hT : T.card ≤ n) :
    MengerAlternative G S T n :=
  Or.inr ⟨T, hT, BlocksAllPaths.right⟩

/-- Convert the path side to an exact-size packing when desired. -/
theorem exists_exact_or_separator
    (h : MengerAlternative G S T n) :
    (∃ P : PathPacking G S T, P.card = n) ∨
      ∃ J : Finset V, J.card ≤ n ∧ BlocksAllPaths G S T J := by
  rcases h with hpaths | hsep
  · exact Or.inl hpaths.exists_exact
  · exact Or.inr hsep

end MengerAlternative

/-- The weak finite vertex-Menger theorem used downstream. -/
def FiniteVertexMengerStatement : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (S T : Finset V) (n : ℕ),
      MengerAlternative G S T n

namespace Menger

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {S T J : Finset V}

/-- There is always at least one blocking set, namely the full vertex set. -/
theorem exists_blocking_set :
    ∃ m : ℕ, ∃ J : Finset V, BlocksAllPaths G S T J ∧ J.card = m :=
  ⟨(Finset.univ : Finset V).card, Finset.univ, BlocksAllPaths.univ, rfl⟩

/-- The minimum cardinality of a finite vertex set blocking all `S`-to-`T`
paths. -/
noncomputable def minSeparatorSize
    (G : _root_.SimpleGraph V) (S T : Finset V) : ℕ := by
  classical
  exact Nat.find (exists_blocking_set (G := G) (S := S) (T := T))

/-- A separator attaining `minSeparatorSize` exists. -/
theorem exists_min_separator :
    ∃ J : Finset V,
      BlocksAllPaths G S T J ∧ J.card = minSeparatorSize G S T := by
  classical
  simpa [minSeparatorSize] using
    (Nat.find_spec (exists_blocking_set (G := G) (S := S) (T := T)))

/-- The selected minimum separator. -/
noncomputable def minSeparator
    (G : _root_.SimpleGraph V) (S T : Finset V) : Finset V :=
  Classical.choose (exists_min_separator (G := G) (S := S) (T := T))

theorem minSeparator_blocks :
    BlocksAllPaths G S T (minSeparator G S T) :=
  (Classical.choose_spec
    (exists_min_separator (G := G) (S := S) (T := T))).1

@[simp] theorem minSeparator_card :
    (minSeparator G S T).card = minSeparatorSize G S T :=
  (Classical.choose_spec
    (exists_min_separator (G := G) (S := S) (T := T))).2

/-- Any blocking set bounds the minimum separator size from above. -/
theorem minSeparatorSize_le_of_blocks
    (hJ : BlocksAllPaths G S T J) :
    minSeparatorSize G S T ≤ J.card := by
  classical
  exact Nat.find_min'
    (exists_blocking_set (G := G) (S := S) (T := T)) ⟨J, hJ, rfl⟩

theorem minSeparatorSize_mono_left {S' : Finset V}
    (hS : S ⊆ S') :
    minSeparatorSize G S T ≤ minSeparatorSize G S' T := by
  have hblocks :
      BlocksAllPaths G S T (minSeparator G S' T) :=
    BlocksAllPaths.mono_left_terminals
      (G := G) (S := S') (T := T) (J := minSeparator G S' T)
      hS minSeparator_blocks
  have hle := minSeparatorSize_le_of_blocks
    (G := G) (S := S) (T := T) (J := minSeparator G S' T) hblocks
  simpa using hle

theorem minSeparatorSize_mono_right {T' : Finset V}
    (hT : T ⊆ T') :
    minSeparatorSize G S T ≤ minSeparatorSize G S T' := by
  have hblocks :
      BlocksAllPaths G S T (minSeparator G S T') :=
    BlocksAllPaths.mono_right_terminals
      (G := G) (S := S) (T := T') (J := minSeparator G S T')
      hT minSeparator_blocks
  have hle := minSeparatorSize_le_of_blocks
    (G := G) (S := S) (T := T) (J := minSeparator G S T') hblocks
  simpa using hle

theorem minSeparatorSize_le_left_card :
    minSeparatorSize G S T ≤ S.card :=
  minSeparatorSize_le_of_blocks (G := G) (S := S) (T := T)
    BlocksAllPaths.left

theorem minSeparatorSize_le_right_card :
    minSeparatorSize G S T ≤ T.card :=
  minSeparatorSize_le_of_blocks (G := G) (S := S) (T := T)
    BlocksAllPaths.right

/-- The forced overlap `S ∩ T` is contained in every separator, so its
cardinality is a lower bound on the minimum separator size. -/
theorem inter_card_le_minSeparatorSize :
    (S ∩ T).card ≤ minSeparatorSize G S T := by
  rw [← minSeparator_card (G := G) (S := S) (T := T)]
  exact Finset.card_le_card
    (BlocksAllPaths.inter_subset
      (G := G) (S := S) (T := T) (J := minSeparator G S T)
      minSeparator_blocks)

/-- If an endpoint-clean path system is smaller than the minimum separator,
then its right endpoints do not separate `S` from `T`. -/
theorem EndpointCleanPathPacking.not_blocks_targetSet_of_card_lt_minSeparatorSize
    (P : EndpointCleanPathPacking G S T)
    (hcard : P.card < minSeparatorSize G S T) :
    ¬ BlocksAllPaths G S T P.targetSet := by
  intro hblocks
  have hle := minSeparatorSize_le_of_blocks
    (G := G) (S := S) (T := T) (J := P.targetSet) hblocks
  rw [P.targetSet_card] at hle
  exact (not_lt_of_ge hle) hcard

/-- The first path found in Diestel's augmentation proof: an endpoint-clean
`S`-to-`T` path avoiding the current right endpoint set. -/
theorem EndpointCleanPathPacking.exists_clean_path_disjoint_targetSet
    (P : EndpointCleanPathPacking G S T)
    (hcard : P.card < minSeparatorSize G S T) :
    ∃ R : GraphPath G, R.EndpointClean S T ∧
      Disjoint R.vertexSet P.targetSet :=
  BlocksAllPaths.exists_endpointClean_path_disjoint_of_not_blocks
    (G := G) (S := S) (T := T) (J := P.targetSet)
    (EndpointCleanPathPacking.not_blocks_targetSet_of_card_lt_minSeparatorSize
      (G := G) (S := S) (T := T) P hcard)

omit [Fintype V] in
/-- Easy augmentation branch: a new clean path disjoint from the whole current
system can simply be adjoined. -/
theorem EndpointCleanPathPacking.augment_of_disjoint_path
    (P : EndpointCleanPathPacking G S T) (R : GraphPath G)
    (hR : R.EndpointClean S T)
    (hdisj : Disjoint R.vertexSet P.vertexSet) :
    ∃ Q : EndpointCleanPathPacking G S T,
      Q.card = P.card + 1 ∧ P.Exceeds Q := by
  refine ⟨P.cons R hR hdisj, ?_, ?_⟩
  · simp
  · exact P.exceeds_cons R hR hdisj

omit [Fintype V] in
/-- Hard-branch preparation in Diestel's augmentation proof.  If the clean
avoiding path `R` meets the current system `P`, let `x` be the last vertex of
`R` in the union of `P`.  Replacing the unique old path containing `x` by its
pref to `x`, and enlarging the right terminal set by the two tails from `x`,
produces a valid endpoint-clean system with the same number of paths and a
strictly smaller vertex union. -/
theorem EndpointCleanPathPacking.exists_shorter_system_at_last_intersection
    (P : EndpointCleanPathPacking G S T) (R : GraphPath G)
    (_hR : R.EndpointClean S T)
    (hRtarget : Disjoint R.vertexSet P.targetSet)
    (hmeet : (R.vertexSet ∩ P.vertexSet).Nonempty) :
    ∃ T' : Finset V, ∃ P' : EndpointCleanPathPacking G S T',
      T ⊆ T' ∧ P'.card = P.card ∧ P'.sourceSet = P.sourceSet ∧
        P'.vertexSet.card < P.vertexSet.card := by
  classical
  let x := R.lastHitVertex P.vertexSet hmeet
  have hxR : x ∈ R.vertexSet := by
    simpa [x] using R.lastHitVertex_mem_vertexSet P.vertexSet hmeet
  have hxP : x ∈ P.vertexSet := by
    simpa [x] using R.lastHitVertex_mem_set P.vertexSet hmeet
  rcases P.exists_index_of_mem_vertexSet hxP with ⟨i, hxi⟩
  let suffixP := (P.path i).dropUntil hxi
  let suffixR := R.dropUntil (R.lastHitVertex_mem_vertexSet P.vertexSet hmeet)
  let T' : Finset V := T ∪ suffixP.vertexSet ∪ suffixR.vertexSet
  let pref := (P.path i).takeUntil hxi
  have hx_not_target : x ≠ (P.path i).target := by
    intro hxEq
    have hxTarget : x ∈ P.targetSet := by
      rw [hxEq]
      exact P.target_mem_targetSet i
    exact Finset.disjoint_left.mp hRtarget hxR hxTarget
  have hprefClean : pref.EndpointClean S T' := by
    refine
      { source_mem := ?_
        target_mem := ?_
        left_eq_source := ?_
        right_eq_target := ?_ }
    · simpa [pref] using (P.endpoint_clean i).source_mem
    · have hxSuffixP : x ∈ suffixP.vertexSet := by
        simpa [suffixP] using GraphPath.source_mem_vertexSet suffixP
      exact Finset.mem_union.2 (Or.inl
        (Finset.mem_union.2 (Or.inr hxSuffixP)))
    · intro v hv hvS
      exact (P.endpoint_clean i).left_eq_source
        ((P.path i).takeUntil_vertexSet_subset hxi (by simpa [pref] using hv))
        hvS
    · intro v hv hvT'
      have hvPref : v ∈ ((P.path i).takeUntil hxi).vertexSet := by
        simpa [pref] using hv
      have hvOld : v ∈ (P.path i).vertexSet :=
        (P.path i).takeUntil_vertexSet_subset hxi hvPref
      rcases Finset.mem_union.1 hvT' with hvLeft | hvSuffixR
      · rcases Finset.mem_union.1 hvLeft with hvT | hvSuffixP
        · have hvTarget : v = (P.path i).target :=
            (P.endpoint_clean i).right_eq_target hvOld hvT
          have htargetSuffix :
              (P.path i).target ∈ suffixP.vertexSet := by
            simpa [suffixP] using GraphPath.target_mem_vertexSet suffixP
          have htarget_eq_x :
              (P.path i).target = x :=
            (P.path i).eq_of_mem_takeUntil_and_mem_dropUntil hxi
              (by simpa [hvTarget, pref] using hv)
              (by simpa [suffixP] using htargetSuffix)
          simpa [pref] using hvTarget.trans htarget_eq_x
        · have hvx :
              v = x :=
            (P.path i).eq_of_mem_takeUntil_and_mem_dropUntil hxi
              hvPref (by simpa [suffixP] using hvSuffixP)
          simpa [pref] using hvx
      · have hvx :
            v = x := by
          have hvPsystem : v ∈ P.vertexSet :=
            (P.mem_vertexSet).2 ⟨i, hvOld⟩
          have hvx' :=
            R.eq_source_of_mem_dropUntil_lastHitVertex_of_mem_set P.vertexSet
              hmeet
              (by simpa [suffixR] using hvSuffixR)
              hvPsystem
          simpa [suffixR, x] using hvx'
        simpa [pref] using hvx
  have hold : ∀ j : P.Index, j ≠ i → (P.path j).EndpointClean S T' := by
    intro j hji
    refine
      { source_mem := (P.endpoint_clean j).source_mem
        target_mem := ?_
        left_eq_source := ?_
        right_eq_target := ?_ }
    · exact Finset.mem_union.2 (Or.inl
        (Finset.mem_union.2 (Or.inl (P.endpoint_clean j).target_mem)))
    · intro v hv hvS
      exact (P.endpoint_clean j).left_eq_source hv hvS
    · intro v hv hvT'
      rcases Finset.mem_union.1 hvT' with hvLeft | hvSuffixR
      · rcases Finset.mem_union.1 hvLeft with hvT | hvSuffixP
        · exact (P.endpoint_clean j).right_eq_target hv hvT
        · exfalso
          have hv_i : v ∈ (P.path i).vertexSet :=
            (P.path i).dropUntil_vertexSet_subset hxi
              (by simpa [suffixP] using hvSuffixP)
          exact Finset.disjoint_left.mp
            (P.node_disjoint (by
              intro h
              exact hji h.symm))
            hv_i hv
      · exfalso
        have hvPsystem : v ∈ P.vertexSet := (P.mem_vertexSet).2 ⟨j, hv⟩
        have hvx :
            v = x := by
          have hvx' :=
            R.eq_source_of_mem_dropUntil_lastHitVertex_of_mem_set P.vertexSet
              hmeet
              (by simpa [suffixR] using hvSuffixR)
              hvPsystem
          simpa [suffixR, x] using hvx'
        have hv_i : v ∈ (P.path i).vertexSet := by
          simpa [hvx] using hxi
        exact Finset.disjoint_left.mp
          (P.node_disjoint (by
            intro h
            exact hji h.symm))
          hv_i hv
  let P' := P.replacePath i pref hprefClean hold
    ((P.path i).takeUntil_vertexSet_subset hxi)
  refine ⟨T', P', ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl hv)))
  · simp [P']
  · have hsrc : pref.source = (P.path i).source := rfl
    simp [P', pref,
      EndpointCleanPathPacking.replacePath_sourceSet_eq_of_source_eq
        (P := P) (i₀ := i) (Q := pref) hprefClean hold
        ((P.path i).takeUntil_vertexSet_subset hxi) hsrc]
  · have hproper :
        pref.vertexSet ⊂ (P.path i).vertexSet := by
      simpa [pref] using
        (P.path i).takeUntil_vertexSet_ssubset_of_ne_target hxi hx_not_target
    have hssub :
        P'.vertexSet ⊂ P.vertexSet := by
      simpa [P', pref] using
        P.replacePath_vertexSet_ssubset i pref hprefClean hold
          ((P.path i).takeUntil_vertexSet_subset hxi) hproper
    exact Finset.card_lt_card hssub

/-- The formal induction step up to the recursive call.  A too-small
endpoint-clean system either admits an immediate disjoint augmenting path, or
it can be replaced by a same-size system over a larger target set with strictly
smaller vertex union, while the separator-size inequality remains true. -/
theorem EndpointCleanPathPacking.augment_or_shorter_system
    (P : EndpointCleanPathPacking G S T)
    (hcard : P.card < minSeparatorSize G S T) :
    (∃ Q : EndpointCleanPathPacking G S T,
      Q.card = P.card + 1 ∧ P.Exceeds Q) ∨
    ∃ T' : Finset V, ∃ P' : EndpointCleanPathPacking G S T',
      T ⊆ T' ∧ P'.card = P.card ∧
        P'.vertexSet.card < P.vertexSet.card ∧
        P'.card < minSeparatorSize G S T' := by
  classical
  rcases EndpointCleanPathPacking.exists_clean_path_disjoint_targetSet
      (G := G) (S := S) (T := T) P hcard with
    ⟨R, hRclean, hRtarget⟩
  by_cases hdisj : Disjoint R.vertexSet P.vertexSet
  · exact Or.inl
      (EndpointCleanPathPacking.augment_of_disjoint_path
        (G := G) (S := S) (T := T) P R hRclean hdisj)
  · right
    have hmeet : (R.vertexSet ∩ P.vertexSet).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      apply hdisj
      rw [Finset.disjoint_left]
      intro v hvR hvP
      have hvInter : v ∈ R.vertexSet ∩ P.vertexSet :=
        Finset.mem_inter.2 ⟨hvR, hvP⟩
      simp [hempty] at hvInter
    rcases EndpointCleanPathPacking.exists_shorter_system_at_last_intersection
        (G := G) (S := S) (T := T) P R hRclean hRtarget hmeet with
      ⟨T', P', hTT', hPcard, _hPsource, hPvertices⟩
    refine ⟨T', P', hTT', hPcard, hPvertices, ?_⟩
    rw [hPcard]
    exact hcard.trans_le
      (minSeparatorSize_mono_right
        (G := G) (S := S) (T := T) (T' := T') hTT')

theorem EndpointCleanPathPacking.augment_from_recursive_last_intersection
    (P : EndpointCleanPathPacking G S T) (R : GraphPath G)
    (hRclean : R.EndpointClean S T)
    (hRtarget : Disjoint R.vertexSet P.targetSet)
    (hmeet : (R.vertexSet ∩ P.vertexSet).Nonempty)
    (hcard : P.card < minSeparatorSize G S T)
    (hrec :
      ∀ {T' : Finset V} (P' : EndpointCleanPathPacking G S T'),
        P'.vertexSet.card < P.vertexSet.card →
        P'.card < minSeparatorSize G S T' →
          ∃ Q' : EndpointCleanPathPacking G S T',
            Q'.card = P'.card + 1 ∧ P'.Exceeds Q') :
    ∃ Q : EndpointCleanPathPacking G S T,
      Q.card = P.card + 1 ∧ P.Exceeds Q := by
  classical
  let x := R.lastHitVertex P.vertexSet hmeet
  have hxR : x ∈ R.vertexSet := by
    simpa [x] using R.lastHitVertex_mem_vertexSet P.vertexSet hmeet
  have hxP : x ∈ P.vertexSet := by
    simpa [x] using R.lastHitVertex_mem_set P.vertexSet hmeet
  rcases P.exists_index_of_mem_vertexSet hxP with ⟨i, hxi⟩
  let suffixP := (P.path i).dropUntil hxi
  let suffixR := R.dropUntil (R.lastHitVertex_mem_vertexSet P.vertexSet hmeet)
  let T' : Finset V := T ∪ suffixP.vertexSet ∪ suffixR.vertexSet
  let pref := (P.path i).takeUntil hxi
  have hTT' : T ⊆ T' := by
    intro v hv
    exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl hv)))
  have hx_not_target : x ≠ (P.path i).target := by
    intro hxEq
    have hxTarget : x ∈ P.targetSet := by
      rw [hxEq]
      exact P.target_mem_targetSet i
    exact Finset.disjoint_left.mp hRtarget hxR hxTarget
  have hprefClean : pref.EndpointClean S T' := by
    refine
      { source_mem := ?_
        target_mem := ?_
        left_eq_source := ?_
        right_eq_target := ?_ }
    · simpa [pref] using (P.endpoint_clean i).source_mem
    · have hxSuffixP : x ∈ suffixP.vertexSet := by
        simpa [suffixP] using GraphPath.source_mem_vertexSet suffixP
      exact Finset.mem_union.2 (Or.inl
        (Finset.mem_union.2 (Or.inr hxSuffixP)))
    · intro v hv hvS
      exact (P.endpoint_clean i).left_eq_source
        ((P.path i).takeUntil_vertexSet_subset hxi (by simpa [pref] using hv))
        hvS
    · intro v hv hvT'
      have hvPref : v ∈ ((P.path i).takeUntil hxi).vertexSet := by
        simpa [pref] using hv
      have hvOld : v ∈ (P.path i).vertexSet :=
        (P.path i).takeUntil_vertexSet_subset hxi hvPref
      rcases Finset.mem_union.1 hvT' with hvLeft | hvSuffixR
      · rcases Finset.mem_union.1 hvLeft with hvT | hvSuffixP
        · have hvTarget : v = (P.path i).target :=
            (P.endpoint_clean i).right_eq_target hvOld hvT
          have htargetSuffix :
              (P.path i).target ∈ suffixP.vertexSet := by
            simpa [suffixP] using GraphPath.target_mem_vertexSet suffixP
          have htarget_eq_x :
              (P.path i).target = x :=
            (P.path i).eq_of_mem_takeUntil_and_mem_dropUntil hxi
              (by simpa [hvTarget, pref] using hv)
              (by simpa [suffixP] using htargetSuffix)
          simpa [pref] using hvTarget.trans htarget_eq_x
        · have hvx :
              v = x :=
            (P.path i).eq_of_mem_takeUntil_and_mem_dropUntil hxi
              hvPref (by simpa [suffixP] using hvSuffixP)
          simpa [pref] using hvx
      · have hvx :
            v = x := by
          have hvPsystem : v ∈ P.vertexSet :=
            (P.mem_vertexSet).2 ⟨i, hvOld⟩
          have hvx' :=
            R.eq_source_of_mem_dropUntil_lastHitVertex_of_mem_set P.vertexSet
              hmeet
              (by simpa [suffixR] using hvSuffixR)
              hvPsystem
          simpa [suffixR, x] using hvx'
        simpa [pref] using hvx
  have hold : ∀ j : P.Index, j ≠ i → (P.path j).EndpointClean S T' := by
    intro j hji
    refine
      { source_mem := (P.endpoint_clean j).source_mem
        target_mem := ?_
        left_eq_source := ?_
        right_eq_target := ?_ }
    · exact Finset.mem_union.2 (Or.inl
        (Finset.mem_union.2 (Or.inl (P.endpoint_clean j).target_mem)))
    · intro v hv hvS
      exact (P.endpoint_clean j).left_eq_source hv hvS
    · intro v hv hvT'
      rcases Finset.mem_union.1 hvT' with hvLeft | hvSuffixR
      · rcases Finset.mem_union.1 hvLeft with hvT | hvSuffixP
        · exact (P.endpoint_clean j).right_eq_target hv hvT
        · exfalso
          have hv_i : v ∈ (P.path i).vertexSet :=
            (P.path i).dropUntil_vertexSet_subset hxi
              (by simpa [suffixP] using hvSuffixP)
          exact Finset.disjoint_left.mp
            (P.node_disjoint (by
              intro h
              exact hji h.symm))
            hv_i hv
      · exfalso
        have hvPsystem : v ∈ P.vertexSet := (P.mem_vertexSet).2 ⟨j, hv⟩
        have hvx :
            v = x := by
          have hvx' :=
            R.eq_source_of_mem_dropUntil_lastHitVertex_of_mem_set P.vertexSet
              hmeet
              (by simpa [suffixR] using hvSuffixR)
              hvPsystem
          simpa [suffixR, x] using hvx'
        have hv_i : v ∈ (P.path i).vertexSet := by
          simpa [hvx] using hxi
        exact Finset.disjoint_left.mp
          (P.node_disjoint (by
            intro h
            exact hji h.symm))
          hv_i hv
  let P' := P.replacePath i pref hprefClean hold
    ((P.path i).takeUntil_vertexSet_subset hxi)
  have hP'card : P'.card = P.card := by
    simp [P']
  have hP'source : P'.sourceSet = P.sourceSet := by
    have hsrc : pref.source = (P.path i).source := rfl
    simp [P', pref,
      EndpointCleanPathPacking.replacePath_sourceSet_eq_of_source_eq
        (P := P) (i₀ := i) (Q := pref) hprefClean hold
        ((P.path i).takeUntil_vertexSet_subset hxi) hsrc]
  have hP'vertex : P'.vertexSet.card < P.vertexSet.card := by
    have hproper :
        pref.vertexSet ⊂ (P.path i).vertexSet := by
      simpa [pref] using
        (P.path i).takeUntil_vertexSet_ssubset_of_ne_target hxi hx_not_target
    have hssub :
        P'.vertexSet ⊂ P.vertexSet := by
      simpa [P', pref] using
        P.replacePath_vertexSet_ssubset i pref hprefClean hold
          ((P.path i).takeUntil_vertexSet_subset hxi) hproper
    exact Finset.card_lt_card hssub
  have hP'lt : P'.card < minSeparatorSize G S T' := by
    rw [hP'card]
    exact hcard.trans_le
      (minSeparatorSize_mono_right
        (G := G) (S := S) (T := T) (T' := T') hTT')
  rcases hrec P' hP'vertex hP'lt with ⟨Q', hQ'card, hQ'exceeds⟩
  have hxP'target : x ∈ P'.targetSet := by
    simpa [P', pref] using
      P.replacePath_new_target_mem_targetSet i pref hprefClean hold
        ((P.path i).takeUntil_vertexSet_subset hxi)
  rcases hQ'exceeds.exists_target_index_of_old_target hxP'target with
    ⟨qx, hqx⟩
  rcases hQ'exceeds.exists_new_target_index hQ'card with
    ⟨y, qy, hyNew, hqy, hyUnique⟩
  have hqx_ne_qy : qx ≠ qy :=
    hQ'exceeds.old_target_index_ne_new_target_index
      hxP'target hyNew hqx hqy
  have hy_ne_x : y ≠ x := by
    intro hyx
    exact (Finset.mem_sdiff.mp hyNew).2 (by simpa [hyx] using hxP'target)
  have hx_ne_y : x ≠ y := fun hxy => hy_ne_x hxy.symm
  have hQ'target_old_of_ne_qy :
      ∀ j : Q'.Index, j ≠ qy → (Q'.path j).target ∈ P'.targetSet := by
    intro j hj
    exact hQ'exceeds.target_mem_old_of_ne_new_target_index
      hyUnique hqy hj
  have hQ'target_ne_x_of_ne_qx :
      ∀ j : Q'.Index, j ≠ qx → (Q'.path j).target ≠ x := by
    intro j hj htarget
    have htargets : (Q'.path j).target = (Q'.path qx).target := by
      simpa [hqx] using htarget
    exact hj (Q'.target_injective htargets)
  have hQ'target_ne_y_of_ne_qy :
      ∀ j : Q'.Index, j ≠ qy → (Q'.path j).target ≠ y := by
    intro j hj htarget
    have htargets : (Q'.path j).target = (Q'.path qy).target := by
      simpa [hqy] using htarget
    exact hj (Q'.target_injective htargets)
  have hold_not_suffixP :
      ∀ {z : V}, z ∈ P'.targetSet → z ≠ x → z ∉ suffixP.vertexSet := by
    intro z hz hz_ne_x hzSuffix
    rw [P.mem_targetSet_replacePath_iff i pref hprefClean hold
        ((P.path i).takeUntil_vertexSet_subset hxi)] at hz
    rcases hz with hz | ⟨j, hji, hzj⟩
    · exact hz_ne_x (by simpa [P', pref] using hz)
    · have hz_i : z ∈ (P.path i).vertexSet :=
        (P.path i).dropUntil_vertexSet_subset hxi hzSuffix
      have hz_j : z ∈ (P.path j).vertexSet := by
        rw [hzj]
        exact GraphPath.target_mem_vertexSet (P.path j)
      exact Finset.disjoint_left.mp
        (P.node_disjoint (by
          intro h
          exact hji h))
        hz_j hz_i
  have hold_not_suffixR :
      ∀ {z : V}, z ∈ P'.targetSet → z ≠ x → z ∉ suffixR.vertexSet := by
    intro z hz hz_ne_x hzSuffix
    rw [P.mem_targetSet_replacePath_iff i pref hprefClean hold
        ((P.path i).takeUntil_vertexSet_subset hxi)] at hz
    rcases hz with hz | ⟨j, _hji, hzj⟩
    · exact hz_ne_x (by simpa [P', pref] using hz)
    · have hzPtarget : z ∈ P.targetSet := by
        rw [hzj]
        exact P.target_mem_targetSet j
      have hzR : z ∈ R.vertexSet :=
        R.dropUntil_vertexSet_subset
          (R.lastHitVertex_mem_vertexSet P.vertexSet hmeet)
          (by simpa [suffixR] using hzSuffix)
      exact Finset.disjoint_left.mp hRtarget hzR hzPtarget
  have htargetT_other :
      ∀ j : Q'.Index, j ≠ qx → j ≠ qy → (Q'.path j).target ∈ T := by
    intro j hjx hjy
    exact
      EndpointCleanPathPacking.Exceeds.target_mem_right_of_ne_indices_replacePath
        (P := P) (i₀ := i) (Qrep := pref) (hQrep := hprefClean)
        (hold := hold) (hsub := (P.path i).takeUntil_vertexSet_subset hxi)
        (Qbig := Q') (h := hQ'exceeds)
        (x := x) (y := y) (ix := qx) (iy := qy) (j := j)
        hqx (by simp [pref]) hyUnique hqy hjx hjy
  have htarget_not_suffixP_other :
      ∀ j : Q'.Index, j ≠ qx → j ≠ qy →
        (Q'.path j).target ∉ suffixP.vertexSet := by
    intro j hjx hjy
    exact hold_not_suffixP
      (hQ'target_old_of_ne_qy j hjy)
      (hQ'target_ne_x_of_ne_qx j hjx)
  have htarget_not_suffixR_other :
      ∀ j : Q'.Index, j ≠ qx → j ≠ qy →
        (Q'.path j).target ∉ suffixR.vertexSet := by
    intro j hjx hjy
    exact hold_not_suffixR
      (hQ'target_old_of_ne_qy j hjy)
      (hQ'target_ne_x_of_ne_qx j hjx)
  have htailP_T' : suffixP.vertexSet ⊆ T' := by
    intro v hv
    exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr hv)))
  have htailR_T' : suffixR.vertexSet ⊆ T' := by
    intro v hv
    exact Finset.mem_union.2 (Or.inr hv)
  have htailP_targetT : suffixP.target ∈ T := by
    simpa [suffixP] using (P.endpoint_clean i).target_mem
  have htailR_targetT : suffixR.target ∈ T := by
    simpa [suffixR] using hRclean.target_mem
  have htailP_left :
      ∀ ⦃v : V⦄, v ∈ suffixP.vertexSet → v ∈ S →
        v = (Q'.path qx).target := by
    intro v hv hvS
    have hvx := (P.endpoint_clean i).dropUntil_left_eq_source hxi
      (by simpa [suffixP] using hv) hvS
    simpa [suffixP, hqx] using hvx
  have htailP_right :
      ∀ ⦃v : V⦄, v ∈ suffixP.vertexSet → v ∈ T → v = suffixP.target := by
    intro v hv hvT
    simpa [suffixP] using
      (P.endpoint_clean i).dropUntil_right_eq_target hxi
        (by simpa [suffixP] using hv) hvT
  have htailR_left_at_qx :
      ∀ ⦃v : V⦄, v ∈ suffixR.vertexSet → v ∈ S →
        v = (Q'.path qx).target := by
    intro v hv hvS
    have hvx := hRclean.dropUntil_left_eq_source
      (R.lastHitVertex_mem_vertexSet P.vertexSet hmeet)
      (by simpa [suffixR] using hv) hvS
    simpa [suffixR, hqx, x] using hvx
  have htailR_right :
      ∀ ⦃v : V⦄, v ∈ suffixR.vertexSet → v ∈ T → v = suffixR.target := by
    intro v hv hvT
    simpa [suffixR] using
      hRclean.dropUntil_right_eq_target
        (R.lastHitVertex_mem_vertexSet P.vertexSet hmeet)
        (by simpa [suffixR] using hv) hvT
  have hjoinP_at_qx_T :
      (Q'.path qx).target ∈ T → (Q'.path qx).target = suffixP.target := by
    intro hxT
    have hxx : x ∈ T := by simpa [hqx] using hxT
    have hxOld : x = (P.path i).target :=
      (P.endpoint_clean i).right_eq_target hxi hxx
    simpa [suffixP, hqx] using hxOld
  have hjoinR_at_qx_T :
      (Q'.path qx).target ∈ T → (Q'.path qx).target = suffixR.target := by
    intro hxT
    have hxx : x ∈ T := by simpa [hqx] using hxT
    have hxRt : x = R.target := hRclean.right_eq_target hxR hxx
    simpa [suffixR, hqx] using hxRt
  have hjoinP_at_qx : (Q'.path qx).target = suffixP.source := by
    simp [suffixP, hqx]
  have hjoinR_at_qx : (Q'.path qx).target = suffixR.source := by
    simp [suffixR, hqx, x]
  by_cases hySuffixP : y ∈ suffixP.vertexSet
  · -- The new recursive endpoint lies strictly after `x` on the old path.
    let tailY := (P.path i).dropUntil
      ((P.path i).dropUntil_vertexSet_subset hxi hySuffixP)
    have htailY_T' : tailY.vertexSet ⊆ T' := by
      intro v hv
      have hvSuffixP :
          v ∈ suffixP.vertexSet := by
        have hsub :=
          (P.path i).dropUntil_vertexSet_subset_dropUntil_of_mem_dropUntil
            hxi (by simpa [suffixP] using hySuffixP)
        simpa [tailY, suffixP] using hsub (by simpa [tailY] using hv)
      exact htailP_T' hvSuffixP
    have htailY_targetT : tailY.target ∈ T := by
      simpa [tailY] using (P.endpoint_clean i).target_mem
    have htailY_left :
        ∀ ⦃v : V⦄, v ∈ tailY.vertexSet → v ∈ S →
          v = (Q'.path qy).target := by
      intro v hv hvS
      have hvy := (P.endpoint_clean i).dropUntil_left_eq_source
        ((P.path i).dropUntil_vertexSet_subset hxi hySuffixP)
        (by simpa [tailY] using hv) hvS
      simpa [tailY, hqy] using hvy
    have htailY_right :
        ∀ ⦃v : V⦄, v ∈ tailY.vertexSet → v ∈ T → v = tailY.target := by
      intro v hv hvT
      simpa [tailY] using
        (P.endpoint_clean i).dropUntil_right_eq_target
          ((P.path i).dropUntil_vertexSet_subset hxi hySuffixP)
          (by simpa [tailY] using hv) hvT
    have hjoinY_T :
        (Q'.path qy).target ∈ T → (Q'.path qy).target = tailY.target := by
      intro hyT
      have hyy : y ∈ T := by simpa [hqy] using hyT
      have hyOld : y = (P.path i).target :=
        (P.endpoint_clean i).right_eq_target
          ((P.path i).dropUntil_vertexSet_subset hxi hySuffixP) hyy
      simpa [tailY, hqy] using hyOld
    have hjoinY : (Q'.path qy).target = tailY.source := by
      simp [tailY, hqy]
    have hx_not_tailY : (Q'.path qx).target ∉ tailY.vertexSet := by
      have hx_not :
          x ∉ ((P.path i).dropUntil
            ((P.path i).dropUntil_vertexSet_subset hxi hySuffixP)).vertexSet :=
        (P.path i).not_mem_dropUntil_of_mem_dropUntil_ne hxi
          (by simpa [suffixP] using hySuffixP)
          (by
            intro hyx
            exact hy_ne_x (by simp [hyx]))
      simpa [tailY, hqx] using hx_not
    have hy_not_suffixR : (Q'.path qy).target ∉ suffixR.vertexSet := by
      intro hyR
      have hyPsystem : y ∈ P.vertexSet :=
        (P.mem_vertexSet).2 ⟨i,
          (P.path i).dropUntil_vertexSet_subset hxi hySuffixP⟩
      have hyx :
          y = x := by
        have hyx' :=
            R.eq_source_of_mem_dropUntil_lastHitVertex_of_mem_set P.vertexSet
              hmeet
              (by simpa [suffixR, hqy] using hyR)
              hyPsystem
        simpa [suffixR, x] using hyx'
      exact hy_ne_x hyx
    have hother_not_tailY :
        ∀ j : Q'.Index, j ≠ qx → j ≠ qy →
          (Q'.path j).target ∉ tailY.vertexSet := by
      intro j hjx hjy hmem
      have hmemSuffixP : (Q'.path j).target ∈ suffixP.vertexSet := by
        have hsub :=
          (P.path i).dropUntil_vertexSet_subset_dropUntil_of_mem_dropUntil
            hxi (by simpa [suffixP] using hySuffixP)
        simpa [tailY, suffixP] using hsub (by simpa [tailY] using hmem)
      exact htarget_not_suffixP_other j hjx hjy hmemSuffixP
    have htails_disj : Disjoint suffixR.vertexSet tailY.vertexSet := by
      rw [Finset.disjoint_left]
      intro v hvR hvY
      have hvSuffixP : v ∈ suffixP.vertexSet := by
        have hsub :=
          (P.path i).dropUntil_vertexSet_subset_dropUntil_of_mem_dropUntil
            hxi (by simpa [suffixP] using hySuffixP)
        simpa [tailY, suffixP] using hsub (by simpa [tailY] using hvY)
      have hvPsystem : v ∈ P.vertexSet :=
        (P.mem_vertexSet).2 ⟨i,
          (P.path i).dropUntil_vertexSet_subset hxi hvSuffixP⟩
      have hvx :
          v = x := by
        have hvx' :=
          R.eq_source_of_mem_dropUntil_lastHitVertex_of_mem_set P.vertexSet
            hmeet
            (by simpa [suffixR] using hvR)
            hvPsystem
        simpa [suffixR, x] using hvx'
      exact hx_not_tailY (by simpa [hqx, hvx] using hvY)
    let Q := Q'.spliceTwo qx qy hqx_ne_qy suffixR tailY
      hTT' htailR_T' htailY_T' htailR_targetT htailY_targetT
      htailR_left_at_qx htailY_left htailR_right htailY_right
      hjoinR_at_qx_T hjoinY_T hjoinR_at_qx hjoinY
      htargetT_other htarget_not_suffixR_other hother_not_tailY
      hy_not_suffixR hx_not_tailY htails_disj
    refine ⟨Q, ?_, ?_⟩
    · simp [Q, hQ'card, hP'card]
    · apply EndpointCleanPathPacking.exceeds_of_subset_card_add_one
      · intro v hv
        have hvP' : v ∈ P'.sourceSet := by simpa [hP'source] using hv
        have hvQ' := hQ'exceeds.sourceSet_subset hvP'
        have hsrcQ :
            Q.sourceSet = Q'.sourceSet := by
          simpa [Q] using
            Q'.spliceTwo_sourceSet_eq qx qy hqx_ne_qy suffixR tailY
              hTT' htailR_T' htailY_T' htailR_targetT htailY_targetT
              htailR_left_at_qx htailY_left htailR_right htailY_right
              hjoinR_at_qx_T hjoinY_T hjoinR_at_qx hjoinY
              htargetT_other htarget_not_suffixR_other hother_not_tailY
              hy_not_suffixR hx_not_tailY htails_disj
        simpa [hsrcQ] using hvQ'
      · intro v hv
        rw [EndpointCleanPathPacking.mem_targetSet_spliceTwo_iff
          (P := Q') (i₀ := qx) (i₁ := qy) (hidx := hqx_ne_qy)
          (tail₀ := suffixR) (tail₁ := tailY)
          (hTU := hTT') (htail₀U := htailR_T') (htail₁U := htailY_T')
          (htail₀T := htailR_targetT) (htail₁T := htailY_targetT)
          (htail₀Left := htailR_left_at_qx) (htail₁Left := htailY_left)
          (htail₀Right := htailR_right) (htail₁Right := htailY_right)
          (hjoin₀Target := hjoinR_at_qx_T) (hjoin₁Target := hjoinY_T)
          (hjoin₀ := hjoinR_at_qx) (hjoin₁ := hjoinY)
          (hotherTargetT := htargetT_other)
          (hotherTargetNotTail₀ := htarget_not_suffixR_other)
          (hotherTargetNotTail₁ := hother_not_tailY)
          (hi₁TargetNotTail₀ := hy_not_suffixR)
          (hi₀TargetNotTail₁ := hx_not_tailY)
          (htails := htails_disj)]
        rcases P.exists_index_target_eq_of_mem_targetSet hv with ⟨j, hvj⟩
        by_cases hji : j = i
        · right
          left
          subst j
          simp [tailY, hvj]
        · right
          right
          have hvP' :
              v ∈ P'.targetSet := by
            rw [P.mem_targetSet_replacePath_iff i pref hprefClean hold
                ((P.path i).takeUntil_vertexSet_subset hxi)]
            exact Or.inr ⟨j, hji, hvj.symm⟩
          rcases hQ'exceeds.exists_target_index_of_old_target hvP' with
            ⟨jQ, hjQ⟩
          have hjQ_ne_qx : jQ ≠ qx := by
            intro h
            have hvx : v = x := by
              calc
                v = (Q'.path jQ).target := hjQ.symm
                _ = (Q'.path qx).target := by rw [h]
                _ = x := hqx
            have hx_on_j : x ∈ (P.path j).vertexSet := by
              simp [← hvx, ← hvj]
            exact Finset.disjoint_left.mp
              (P.node_disjoint (by
                intro h'
                exact hji h'.symm))
              hxi hx_on_j
          have hjQ_ne_qy : jQ ≠ qy := by
            intro h
            exact (Finset.mem_sdiff.mp hyNew).2 (by
              have hvy : v = y := by
                calc
                  v = (Q'.path jQ).target := hjQ.symm
                  _ = (Q'.path qy).target := by rw [h]
                  _ = y := hqy
              simpa [hvy] using hvP')
          exact ⟨jQ, hjQ_ne_qx, hjQ_ne_qy, hjQ.symm⟩
      · simp [Q, hQ'card, hP'card]
  · -- The new endpoint is not on `xP`; it is either already in `T` or lies on `xR`.
    by_cases hyT : y ∈ T
    · let tailY := GraphPath.refl G y
      have hyT' : y ∈ T' := by
        exact Q'.targetSet_subset_right (Finset.mem_sdiff.mp hyNew).1
      have htailY_T' : tailY.vertexSet ⊆ T' := by
        intro v hv
        simpa [tailY, GraphPath.refl_vertexSet] using
          (Finset.mem_singleton.mp (by simpa [tailY, GraphPath.refl_vertexSet] using hv) ▸ hyT')
      have htailY_targetT : tailY.target ∈ T := by
        simpa [tailY] using hyT
      have htailY_left :
          ∀ ⦃v : V⦄, v ∈ tailY.vertexSet → v ∈ S →
            v = (Q'.path qy).target := by
        intro v hv _hvS
        have hvy : v = y := by
          simpa [tailY, GraphPath.refl_vertexSet] using hv
        simpa [tailY, hqy] using hvy
      have htailY_right :
          ∀ ⦃v : V⦄, v ∈ tailY.vertexSet → v ∈ T → v = tailY.target := by
        intro v hv _hvT
        simpa [tailY, GraphPath.refl_vertexSet] using hv
      have hjoinY_T :
          (Q'.path qy).target ∈ T → (Q'.path qy).target = tailY.target := by
        intro _h
        simp [tailY, hqy]
      have hjoinY : (Q'.path qy).target = tailY.source := by
        simp [tailY, hqy]
      have hother_not_tailY :
          ∀ j : Q'.Index, j ≠ qx → j ≠ qy →
            (Q'.path j).target ∉ tailY.vertexSet := by
        intro j _hjx hjy hmem
        have htarget : (Q'.path j).target = y := by
          simpa [tailY, GraphPath.refl_vertexSet] using hmem
        exact hQ'target_ne_y_of_ne_qy j hjy htarget
      have hx_not_tailY : (Q'.path qx).target ∉ tailY.vertexSet := by
        intro hmem
        have hxy : x = y := by
          have : (Q'.path qx).target = y := by
            simpa [tailY, GraphPath.refl_vertexSet] using hmem
          simpa [hqx] using this
        exact hx_ne_y hxy
      have htails_disj : Disjoint suffixP.vertexSet tailY.vertexSet := by
        rw [Finset.disjoint_left]
        intro v hvP hvY
        have hvy : v = y := by
          simpa [tailY, GraphPath.refl_vertexSet] using hvY
        exact hySuffixP (by simpa [hvy] using hvP)
      let Q := Q'.spliceTwo qx qy hqx_ne_qy suffixP tailY
        hTT' htailP_T' htailY_T' htailP_targetT htailY_targetT
        htailP_left htailY_left htailP_right htailY_right
        hjoinP_at_qx_T hjoinY_T hjoinP_at_qx hjoinY
        htargetT_other htarget_not_suffixP_other hother_not_tailY
        (by simpa [hqy] using hySuffixP) hx_not_tailY htails_disj
      refine ⟨Q, ?_, ?_⟩
      · simp [Q, hQ'card, hP'card]
      · apply EndpointCleanPathPacking.exceeds_of_subset_card_add_one
        · intro v hv
          have hvP' : v ∈ P'.sourceSet := by simpa [hP'source] using hv
          have hvQ' := hQ'exceeds.sourceSet_subset hvP'
          have hsrcQ :
              Q.sourceSet = Q'.sourceSet := by
            simpa [Q] using
              Q'.spliceTwo_sourceSet_eq qx qy hqx_ne_qy suffixP tailY
                hTT' htailP_T' htailY_T' htailP_targetT htailY_targetT
                htailP_left htailY_left htailP_right htailY_right
                hjoinP_at_qx_T hjoinY_T hjoinP_at_qx hjoinY
                htargetT_other htarget_not_suffixP_other hother_not_tailY
                (by simpa [hqy] using hySuffixP) hx_not_tailY htails_disj
          simpa [hsrcQ] using hvQ'
        · intro v hv
          rw [EndpointCleanPathPacking.mem_targetSet_spliceTwo_iff
            (P := Q') (i₀ := qx) (i₁ := qy) (hidx := hqx_ne_qy)
            (tail₀ := suffixP) (tail₁ := tailY)
            (hTU := hTT') (htail₀U := htailP_T') (htail₁U := htailY_T')
            (htail₀T := htailP_targetT) (htail₁T := htailY_targetT)
            (htail₀Left := htailP_left) (htail₁Left := htailY_left)
            (htail₀Right := htailP_right) (htail₁Right := htailY_right)
            (hjoin₀Target := hjoinP_at_qx_T) (hjoin₁Target := hjoinY_T)
            (hjoin₀ := hjoinP_at_qx) (hjoin₁ := hjoinY)
            (hotherTargetT := htargetT_other)
            (hotherTargetNotTail₀ := htarget_not_suffixP_other)
            (hotherTargetNotTail₁ := hother_not_tailY)
            (hi₁TargetNotTail₀ := by simpa [hqy] using hySuffixP)
            (hi₀TargetNotTail₁ := hx_not_tailY)
            (htails := htails_disj)]
          rcases P.exists_index_target_eq_of_mem_targetSet hv with ⟨j, hvj⟩
          by_cases hji : j = i
          · left
            subst j
            simp [suffixP, hvj]
          · right
            right
            have hvP' :
                v ∈ P'.targetSet := by
              rw [P.mem_targetSet_replacePath_iff i pref hprefClean hold
                  ((P.path i).takeUntil_vertexSet_subset hxi)]
              exact Or.inr ⟨j, hji, hvj.symm⟩
            rcases hQ'exceeds.exists_target_index_of_old_target hvP' with
              ⟨jQ, hjQ⟩
            have hjQ_ne_qx : jQ ≠ qx := by
              intro h
              have hvx : v = x := by
                calc
                  v = (Q'.path jQ).target := hjQ.symm
                  _ = (Q'.path qx).target := by rw [h]
                  _ = x := hqx
              have hx_on_j : x ∈ (P.path j).vertexSet := by
                simp [← hvx, ← hvj]
              exact Finset.disjoint_left.mp
                (P.node_disjoint (by
                  intro h'
                  exact hji h'.symm))
                hxi hx_on_j
            have hjQ_ne_qy : jQ ≠ qy := by
              intro h
              exact (Finset.mem_sdiff.mp hyNew).2 (by
                have hvy : v = y := by
                  calc
                    v = (Q'.path jQ).target := hjQ.symm
                    _ = (Q'.path qy).target := by rw [h]
                    _ = y := hqy
                simpa [hvy] using hvP')
            exact ⟨jQ, hjQ_ne_qx, hjQ_ne_qy, hjQ.symm⟩
        · simp [Q, hQ'card, hP'card]
    · have hyT' : y ∈ T' :=
        Q'.targetSet_subset_right (Finset.mem_sdiff.mp hyNew).1
      have hySuffixR : y ∈ suffixR.vertexSet := by
        rcases Finset.mem_union.1 hyT' with hyLeft | hyR
        · rcases Finset.mem_union.1 hyLeft with hyTmem | hyPmem
          · exact False.elim (hyT hyTmem)
          · exact False.elim (hySuffixP hyPmem)
        · exact hyR
      let tailY := R.dropUntil
        (R.dropUntil_vertexSet_subset
          (R.lastHitVertex_mem_vertexSet P.vertexSet hmeet)
          (by simpa [suffixR] using hySuffixR))
      have htailY_T' : tailY.vertexSet ⊆ T' := by
        intro v hv
        have hvSuffixR : v ∈ suffixR.vertexSet := by
          have hsub :=
            R.dropUntil_vertexSet_subset_dropUntil_of_mem_dropUntil
              (R.lastHitVertex_mem_vertexSet P.vertexSet hmeet)
              (by simpa [suffixR] using hySuffixR)
          simpa [tailY, suffixR] using hsub (by simpa [tailY] using hv)
        exact htailR_T' hvSuffixR
      have htailY_targetT : tailY.target ∈ T := by
        simpa [tailY] using hRclean.target_mem
      have htailY_left :
          ∀ ⦃v : V⦄, v ∈ tailY.vertexSet → v ∈ S →
            v = (Q'.path qy).target := by
        intro v hv hvS
        have hvy := hRclean.dropUntil_left_eq_source
          (R.dropUntil_vertexSet_subset
            (R.lastHitVertex_mem_vertexSet P.vertexSet hmeet)
            (by simpa [suffixR] using hySuffixR))
          (by simpa [tailY] using hv) hvS
        simpa [tailY, hqy] using hvy
      have htailY_right :
          ∀ ⦃v : V⦄, v ∈ tailY.vertexSet → v ∈ T → v = tailY.target := by
        intro v hv hvT
        simpa [tailY] using
          hRclean.dropUntil_right_eq_target
            (R.dropUntil_vertexSet_subset
              (R.lastHitVertex_mem_vertexSet P.vertexSet hmeet)
              (by simpa [suffixR] using hySuffixR))
            (by simpa [tailY] using hv) hvT
      have hjoinY_T :
          (Q'.path qy).target ∈ T → (Q'.path qy).target = tailY.target := by
        intro hyTmem
        have hyy : y ∈ T := by simpa [hqy] using hyTmem
        exact False.elim (hyT hyy)
      have hjoinY : (Q'.path qy).target = tailY.source := by
        simp [tailY, hqy]
      have hx_not_tailY : (Q'.path qx).target ∉ tailY.vertexSet := by
        have hx_not :
            x ∉ (R.dropUntil
              (R.dropUntil_vertexSet_subset
                (R.lastHitVertex_mem_vertexSet P.vertexSet hmeet)
                (by simpa [suffixR] using hySuffixR))).vertexSet :=
          R.not_mem_dropUntil_of_mem_dropUntil_ne
            (R.lastHitVertex_mem_vertexSet P.vertexSet hmeet)
            (by simpa [suffixR] using hySuffixR)
            (by
              intro hyx
              exact hy_ne_x (by simpa [x] using hyx))
        simpa [tailY, hqx, x] using hx_not
      have hother_not_tailY :
          ∀ j : Q'.Index, j ≠ qx → j ≠ qy →
            (Q'.path j).target ∉ tailY.vertexSet := by
        intro j hjx hjy hmem
        have hmemSuffixR : (Q'.path j).target ∈ suffixR.vertexSet := by
          have hsub :=
            R.dropUntil_vertexSet_subset_dropUntil_of_mem_dropUntil
              (R.lastHitVertex_mem_vertexSet P.vertexSet hmeet)
              (by simpa [suffixR] using hySuffixR)
          simpa [tailY, suffixR] using hsub (by simpa [tailY] using hmem)
        exact htarget_not_suffixR_other j hjx hjy hmemSuffixR
      have htails_disj : Disjoint suffixP.vertexSet tailY.vertexSet := by
        rw [Finset.disjoint_left]
        intro v hvP hvY
        have hvSuffixR : v ∈ suffixR.vertexSet := by
          have hsub :=
            R.dropUntil_vertexSet_subset_dropUntil_of_mem_dropUntil
              (R.lastHitVertex_mem_vertexSet P.vertexSet hmeet)
              (by simpa [suffixR] using hySuffixR)
          simpa [tailY, suffixR] using hsub (by simpa [tailY] using hvY)
        have hvPsystem : v ∈ P.vertexSet :=
          (P.mem_vertexSet).2 ⟨i,
            (P.path i).dropUntil_vertexSet_subset hxi hvP⟩
        have hvx :
            v = x := by
          have hvx' :=
            R.eq_source_of_mem_dropUntil_lastHitVertex_of_mem_set P.vertexSet
              hmeet
              (by simpa [suffixR] using hvSuffixR)
              hvPsystem
          simpa [suffixR, x] using hvx'
        exact hx_not_tailY (by simpa [hqx, hvx] using hvY)
      let Q := Q'.spliceTwo qx qy hqx_ne_qy suffixP tailY
        hTT' htailP_T' htailY_T' htailP_targetT htailY_targetT
        htailP_left htailY_left htailP_right htailY_right
        hjoinP_at_qx_T hjoinY_T hjoinP_at_qx hjoinY
        htargetT_other htarget_not_suffixP_other hother_not_tailY
        (by simpa [hqy] using hySuffixP) hx_not_tailY htails_disj
      refine ⟨Q, ?_, ?_⟩
      · simp [Q, hQ'card, hP'card]
      · apply EndpointCleanPathPacking.exceeds_of_subset_card_add_one
        · intro v hv
          have hvP' : v ∈ P'.sourceSet := by simpa [hP'source] using hv
          have hvQ' := hQ'exceeds.sourceSet_subset hvP'
          have hsrcQ :
              Q.sourceSet = Q'.sourceSet := by
            simpa [Q] using
              Q'.spliceTwo_sourceSet_eq qx qy hqx_ne_qy suffixP tailY
                hTT' htailP_T' htailY_T' htailP_targetT htailY_targetT
                htailP_left htailY_left htailP_right htailY_right
                hjoinP_at_qx_T hjoinY_T hjoinP_at_qx hjoinY
                htargetT_other htarget_not_suffixP_other hother_not_tailY
                (by simpa [hqy] using hySuffixP) hx_not_tailY htails_disj
          simpa [hsrcQ] using hvQ'
        · intro v hv
          rw [EndpointCleanPathPacking.mem_targetSet_spliceTwo_iff
            (P := Q') (i₀ := qx) (i₁ := qy) (hidx := hqx_ne_qy)
            (tail₀ := suffixP) (tail₁ := tailY)
            (hTU := hTT') (htail₀U := htailP_T') (htail₁U := htailY_T')
            (htail₀T := htailP_targetT) (htail₁T := htailY_targetT)
            (htail₀Left := htailP_left) (htail₁Left := htailY_left)
            (htail₀Right := htailP_right) (htail₁Right := htailY_right)
            (hjoin₀Target := hjoinP_at_qx_T) (hjoin₁Target := hjoinY_T)
            (hjoin₀ := hjoinP_at_qx) (hjoin₁ := hjoinY)
            (hotherTargetT := htargetT_other)
            (hotherTargetNotTail₀ := htarget_not_suffixP_other)
            (hotherTargetNotTail₁ := hother_not_tailY)
            (hi₁TargetNotTail₀ := by simpa [hqy] using hySuffixP)
            (hi₀TargetNotTail₁ := hx_not_tailY)
            (htails := htails_disj)]
          rcases P.exists_index_target_eq_of_mem_targetSet hv with ⟨j, hvj⟩
          by_cases hji : j = i
          · left
            subst j
            simp [suffixP, hvj]
          · right
            right
            have hvP' :
                v ∈ P'.targetSet := by
              rw [P.mem_targetSet_replacePath_iff i pref hprefClean hold
                  ((P.path i).takeUntil_vertexSet_subset hxi)]
              exact Or.inr ⟨j, hji, hvj.symm⟩
            rcases hQ'exceeds.exists_target_index_of_old_target hvP' with
              ⟨jQ, hjQ⟩
            have hjQ_ne_qx : jQ ≠ qx := by
              intro h
              have hvx : v = x := by
                calc
                  v = (Q'.path jQ).target := hjQ.symm
                  _ = (Q'.path qx).target := by rw [h]
                  _ = x := hqx
              have hx_on_j : x ∈ (P.path j).vertexSet := by
                simp [← hvx, ← hvj]
              exact Finset.disjoint_left.mp
                (P.node_disjoint (by
                  intro h'
                  exact hji h'.symm))
                hxi hx_on_j
            have hjQ_ne_qy : jQ ≠ qy := by
              intro h
              exact (Finset.mem_sdiff.mp hyNew).2 (by
                have hvy : v = y := by
                  calc
                    v = (Q'.path jQ).target := hjQ.symm
                    _ = (Q'.path qy).target := by rw [h]
                    _ = y := hqy
                simpa [hvy] using hvP')
            exact ⟨jQ, hjQ_ne_qx, hjQ_ne_qy, hjQ.symm⟩
        · simp [Q, hQ'card, hP'card]

/-- The strengthened finite-Menger augmentation statement in the endpoint-clean
convention.  This is the induction statement used in Diestel's proof after the
split and replacement lemmas above. -/
def EndpointCleanAugmentationStatement : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (S T : Finset V)
    (P : EndpointCleanPathPacking G S T),
      P.card < minSeparatorSize G S T →
        ∃ Q : EndpointCleanPathPacking G S T,
          Q.card = P.card + 1 ∧ P.Exceeds Q

/-- Diestel's endpoint-clean augmentation theorem for finite vertex-Menger.

The induction is on the number of vertices used by the current disjoint path
system, with the right terminal set allowed to grow in the recursive call. -/
theorem endpointCleanAugmentation :
    EndpointCleanAugmentationStatement.{u} := by
  intro V _instFintype _instDecidableEq G S T P hcard
  classical
  let motive : ℕ → Prop := fun n =>
    ∀ (T : Finset V) (P : EndpointCleanPathPacking G S T),
      P.vertexSet.card = n →
      P.card < minSeparatorSize G S T →
        ∃ Q : EndpointCleanPathPacking G S T,
          Q.card = P.card + 1 ∧ P.Exceeds Q
  have hmain : ∀ n : ℕ, motive n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro T P hn hcard
        rcases EndpointCleanPathPacking.exists_clean_path_disjoint_targetSet
            (G := G) (S := S) (T := T) P hcard with
          ⟨R, hRclean, hRtarget⟩
        by_cases hdisj : Disjoint R.vertexSet P.vertexSet
        · exact EndpointCleanPathPacking.augment_of_disjoint_path
            (G := G) (S := S) (T := T) P R hRclean hdisj
        · have hmeet : (R.vertexSet ∩ P.vertexSet).Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hempty
            apply hdisj
            rw [Finset.disjoint_left]
            intro v hvR hvP
            have hvInter : v ∈ R.vertexSet ∩ P.vertexSet :=
              Finset.mem_inter.2 ⟨hvR, hvP⟩
            simp [hempty] at hvInter
          exact EndpointCleanPathPacking.augment_from_recursive_last_intersection
            (G := G) (S := S) (T := T) P R hRclean hRtarget
            hmeet hcard (by
              intro T' P' hvertices hP'card
              have hlt : P'.vertexSet.card < n := by
                simpa [← hn] using hvertices
              exact ih P'.vertexSet.card hlt T' P' rfl hP'card)
  exact hmain P.vertexSet.card T P rfl hcard

/-- Iterating endpoint-clean augmentation extends any packing to every
attainable intermediate cardinality while retaining all of its old source and
target endpoints.

This is the finite-gammoid basis-extension form used in
Chekuri--Chuzhoy Lemma 2.19: start with the paths whose origins must be
preserved, and augment until the cardinality of a larger witness is reached. -/
theorem EndpointCleanPathPacking.exists_extension_card
    (P : EndpointCleanPathPacking G S T) {k : ℕ}
    (hPk : P.card ≤ k) (hksep : k ≤ minSeparatorSize G S T) :
    ∃ Q : EndpointCleanPathPacking G S T,
      Q.card = k ∧
        P.sourceSet ⊆ Q.sourceSet ∧
          P.targetSet ⊆ Q.targetSet := by
  classical
  induction k, hPk using Nat.le_induction with
  | base =>
      exact ⟨P, rfl, subset_rfl, subset_rfl⟩
  | succ k hPk ih =>
      rcases ih (Nat.le_trans (Nat.le_succ k) hksep) with
        ⟨Q, hQcard, hPsource, hPtarget⟩
      have hQsep : Q.card < minSeparatorSize G S T := by
        rw [hQcard]
        exact Nat.lt_of_succ_le hksep
      rcases endpointCleanAugmentation G S T Q hQsep with
        ⟨R, hRcard, hQR⟩
      refine ⟨R, ?_, hPsource.trans hQR.sourceSet_subset,
        hPtarget.trans hQR.targetSet_subset⟩
      rw [hRcard, hQcard]

/-- The maximum size of a disjoint `S`-to-`T` path packing. -/
noncomputable def maxPackingSize
    (G : _root_.SimpleGraph V) (S T : Finset V) : ℕ := by
  classical
  exact Nat.findGreatest (fun m => HasAtLeastDisjointPaths G S T m) S.card

omit [Fintype V] in
/-- The maximum packing size is itself attainable. -/
theorem maxPackingSize_hasAtLeast :
    HasAtLeastDisjointPaths G S T (maxPackingSize G S T) := by
  classical
  simpa [maxPackingSize] using
    (Nat.findGreatest_spec
      (P := fun m => HasAtLeastDisjointPaths G S T m)
      (m := 0) (n := S.card) (Nat.zero_le S.card)
      (HasAtLeastDisjointPaths.zero (G := G) (S := S) (T := T)))

omit [Fintype V] in
/-- Any attainable packing size is bounded by `maxPackingSize`. -/
theorem le_maxPackingSize_of_hasAtLeast
    {m : ℕ} (hm : HasAtLeastDisjointPaths G S T m) :
    m ≤ maxPackingSize G S T := by
  classical
  simpa [maxPackingSize] using
    (Nat.le_findGreatest
      (P := fun m => HasAtLeastDisjointPaths G S T m)
      (m := m) (n := S.card) hm.le_left_card hm)

omit [Fintype V] in
/-- Every blocking set meets each path in a packing at a distinct vertex, so
the size of the packing is at most the size of the blocking set. -/
theorem PathPacking.card_le_of_blocks
    (P : PathPacking G S T) (hJ : BlocksAllPaths G S T J) :
    P.card ≤ J.card := by
  classical
  let hit : P.Index → V := fun i =>
    Classical.choose (hJ (P.path i) (P.connects i))
  have hhit_mem_path :
      ∀ i : P.Index, hit i ∈ (P.path i).vertexSet := by
    intro i
    exact (Classical.choose_spec (hJ (P.path i) (P.connects i))).1
  have hhit_mem_J :
      ∀ i : P.Index, hit i ∈ J := by
    intro i
    exact (Classical.choose_spec (hJ (P.path i) (P.connects i))).2
  let f : P.Index → J := fun i => ⟨hit i, hhit_mem_J i⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hdisj := P.node_disjoint hne
    have hval : hit i = hit j :=
      congrArg Subtype.val hij
    have hi : hit i ∈ (P.path i).vertexSet := hhit_mem_path i
    have hj : hit i ∈ (P.path j).vertexSet := by
      simpa [hval] using hhit_mem_path j
    exact Finset.disjoint_left.mp hdisj hi hj
  simpa [PathPacking.card] using Fintype.card_le_of_injective f hf

omit [Fintype V] in
/-- Any `n` disjoint paths force every blocking set to have size at least `n`. -/
theorem HasAtLeastDisjointPaths.le_of_blocks
    {n : ℕ} (hpaths : HasAtLeastDisjointPaths G S T n)
    (hJ : BlocksAllPaths G S T J) :
    n ≤ J.card := by
  rcases hpaths with ⟨P, hP⟩
  exact hP.trans (PathPacking.card_le_of_blocks (G := G) (S := S) (T := T)
    (J := J) P hJ)

omit [Fintype V] in
/-- The easy half of Menger: maximum packing size is at most every separator
size. -/
theorem maxPackingSize_le_of_blocks
    (hJ : BlocksAllPaths G S T J) :
    maxPackingSize G S T ≤ J.card :=
  HasAtLeastDisjointPaths.le_of_blocks
    (G := G) (S := S) (T := T)
    maxPackingSize_hasAtLeast hJ

/-- The easy min-max inequality. -/
theorem maxPackingSize_le_minSeparatorSize :
    maxPackingSize G S T ≤ minSeparatorSize G S T := by
  have h :=
    (maxPackingSize_le_of_blocks
      (G := G) (S := S) (T := T)
      (J := minSeparator G S T)
      minSeparator_blocks)
  rw [minSeparator_card] at h
  exact h

omit [Fintype V] in
/-- A maximum packing exists. -/
theorem exists_max_packing :
    ∃ P : PathPacking G S T, P.card = maxPackingSize G S T := by
  rcases maxPackingSize_hasAtLeast (G := G) (S := S) (T := T) with ⟨P, hP⟩
  have hPmax : P.card ≤ maxPackingSize G S T :=
    le_maxPackingSize_of_hasAtLeast (G := G) (S := S) (T := T)
      ⟨P, le_rfl⟩
  exact ⟨P, le_antisymm hPmax hP⟩

/-- The endpoint-clean augmentation statement implies the hard min-max
inequality for finite vertex-Menger. -/
theorem minSeparatorSize_le_maxPackingSize_of_endpointCleanAugmentation
    (haug : EndpointCleanAugmentationStatement.{u}) :
    minSeparatorSize G S T ≤ maxPackingSize G S T := by
  classical
  by_contra hnot
  have hmax_lt : maxPackingSize G S T < minSeparatorSize G S T :=
    Nat.lt_of_not_ge hnot
  rcases exists_max_packing (G := G) (S := S) (T := T) with
    ⟨P₀, hP₀card⟩
  let P := P₀.toEndpointClean
  have hPcard : P.card = maxPackingSize G S T := by
    simp [P, hP₀card]
  rcases haug G S T P (by simpa [hPcard] using hmax_lt) with
    ⟨Q, hQcard, _hQexceeds⟩
  have hpaths : HasAtLeastDisjointPaths G S T (maxPackingSize G S T + 1) := by
    refine ⟨Q.toPathPacking, ?_⟩
    rw [Q.toPathPacking_card, hQcard, hPcard]
  have hle := le_maxPackingSize_of_hasAtLeast
    (G := G) (S := S) (T := T) hpaths
  omega

/-- The hard min-max inequality in finite vertex-Menger. -/
theorem minSeparatorSize_le_maxPackingSize :
    minSeparatorSize G S T ≤ maxPackingSize G S T :=
  minSeparatorSize_le_maxPackingSize_of_endpointCleanAugmentation
    (G := G) (S := S) (T := T) endpointCleanAugmentation

omit [Fintype V] in
/-- The trivial paths on `S ∩ T` give a packing of size `|S ∩ T|`. -/
theorem inter_card_le_maxPackingSize :
    (S ∩ T).card ≤ maxPackingSize G S T :=
  le_maxPackingSize_of_hasAtLeast (G := G) (S := S) (T := T)
    (HasAtLeastDisjointPaths.of_le_inter_card
      (G := G) (S := S) (T := T) le_rfl)

/-- If the forced overlap already reaches the minimum separator size, the hard
min-max inequality is immediate. -/
theorem minSeparatorSize_le_maxPackingSize_of_le_inter_card
    (h : minSeparatorSize G S T ≤ (S ∩ T).card) :
    minSeparatorSize G S T ≤ maxPackingSize G S T :=
  h.trans (inter_card_le_maxPackingSize (G := G) (S := S) (T := T))

/-- The remaining hard direction of finite vertex-Menger min-max. -/
def MinSeparatorLeMaxPackingStatement : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (S T : Finset V),
      minSeparatorSize G S T ≤ maxPackingSize G S T

/-- The hard min-max inequality implies the weak Menger alternative. -/
theorem finite_vertex_menger_of_minSeparator_le_maxPacking
    (hminmax : MinSeparatorLeMaxPackingStatement.{u}) :
    FiniteVertexMengerStatement.{u} := by
  intro V _instFintype _instDecidableEq G S T n
  by_cases hn : n ≤ maxPackingSize G S T
  · rcases maxPackingSize_hasAtLeast (G := G) (S := S) (T := T) with
      ⟨P, hP⟩
    exact Or.inl ⟨P, hn.trans hP⟩
  · rcases exists_min_separator (G := G) (S := S) (T := T) with
      ⟨J, hJ, hJcard⟩
    have hmax_lt : maxPackingSize G S T < n := Nat.lt_of_not_ge hn
    exact Or.inr ⟨J, by
      rw [hJcard]
      exact (hminmax G S T).trans hmax_lt.le, hJ⟩

/-- The hard min-max inequality implies the sharp contract-shaped
finite vertex-Menger alternative. -/
theorem finite_vertex_menger_sharp_of_minSeparator_le_maxPacking
    (hminmax : MinSeparatorLeMaxPackingStatement.{u}) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) (S T : Finset V) (k : ℕ),
        HasDisjointSTPaths G S T k ∨
          ∃ X : Finset V, X.card < k ∧ STSeparator G S T X := by
  intro V _instFintype _instDecidableEq G S T k
  by_cases hk : k ≤ maxPackingSize G S T
  · rcases maxPackingSize_hasAtLeast (G := G) (S := S) (T := T) with
      ⟨P, hP⟩
    exact Or.inl ⟨P, hk.trans hP⟩
  · rcases exists_min_separator (G := G) (S := S) (T := T) with
      ⟨X, hX, hXcard⟩
    have hmax_lt : maxPackingSize G S T < k := Nat.lt_of_not_ge hk
    have hXlt : X.card < k := by
      rw [hXcard]
      exact (hminmax G S T).trans_lt hmax_lt
    exact Or.inr ⟨X, hXlt, hX⟩

/-- Finite vertex-Menger, in the weak alternative form used downstream. -/
theorem finite_vertex_menger :
    FiniteVertexMengerStatement.{u} :=
  finite_vertex_menger_of_minSeparator_le_maxPacking (by
    intro V _instFintype _instDecidableEq G S T
    exact minSeparatorSize_le_maxPackingSize (G := G) (S := S) (T := T))

/-- Finite vertex-Menger in the sharp contract-shaped alternative:
for every `k`, either there are `k` disjoint paths or a separator has size
strictly less than `k`. -/
theorem finite_vertex_menger_sharp :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) (S T : Finset V) (k : ℕ),
        HasDisjointSTPaths G S T k ∨
          ∃ X : Finset V, X.card < k ∧ STSeparator G S T X :=
  finite_vertex_menger_sharp_of_minSeparator_le_maxPacking (by
    intro V _instFintype _instDecidableEq G S T
    exact minSeparatorSize_le_maxPackingSize (G := G) (S := S) (T := T))

end Menger

end SimpleGraph

end Erdos73Infrastructure
