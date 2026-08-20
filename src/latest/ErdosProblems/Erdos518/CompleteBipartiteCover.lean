/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Alternating
import ErdosProblems.Erdos518.Cover

/-!
# Covers of a complete bipartite pair by alternating paths

Suppose that every edge between disjoint finite vertex sets `X` and `Y` belongs to `G`.  A
nonempty block `B ⊆ X` of size at most `|Y| + 1` is covered by one alternating path: choose
`|B| - 1` reusable vertices from `Y` and alternate them with all vertices of `B`.

The main theorem partitions `X` into such blocks.  Its first block has exactly `|Y| + 1`
vertices, and its path uses all of `Y`; subsequent paths may reuse arbitrary subsets of `Y`.
This is precisely the bookkeeping needed in the cut-colouring and empty-exceptional-part cases
of the proof of Erdős Problem 518.
-/

open scoped SimpleGraph

namespace Erdos518

universe u

variable {V : Type u}

section

/-- A nonempty block on the left of a complete bipartite pair, of size at most one more than
the right side, is covered by a single alternating path.  The auxiliary right-hand vertices
used by the path are returned explicitly. -/
lemma exists_alternating_path_for_small_left_block
    [DecidableEq V] {G : SimpleGraph V} {X Y B : Finset V}
    (hBX : B ⊆ X) (hB0 : B.Nonempty) (hcard : B.card ≤ Y.card + 1)
    (hdisj : Disjoint X Y)
    (hadj : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) :
    ∃ T : Finset V, T ⊆ Y ∧ T.card + 1 = B.card ∧
      IsPath G (alternateFinsets B T) ∧
      (∀ x ∈ B, x ∈ alternateFinsets B T) ∧
      pathSupport (alternateFinsets B T) = B ∪ T := by
  have hpred : B.card - 1 ≤ Y.card := by omega
  obtain ⟨T, hTY, hTcard⟩ := Finset.exists_subset_card_eq hpred
  have hBcard : B.card = T.card + 1 := by
    rw [hTcard]
    have hBpos : 0 < B.card := Finset.card_pos.mpr hB0
    omega
  have hBT : Disjoint B T := hdisj.mono hBX hTY
  have hp : IsPath G (alternateFinsets B T) := by
    apply isPath_alternateFinsets_of_card_eq_add_one hBcard hBT
    intro x hx y hy
    exact hadj x (hBX hx) y (hTY hy)
  refine ⟨T, hTY, by omega, hp, ?_, ?_⟩
  · intro x hx
    exact mem_alternateFinsets.mpr (Or.inl hx)
  · simp [pathSupport]

/-- Cover an arbitrary left-hand set by at most `c` alternating paths, allowing vertices of the
right side to be reused between paths.  This is the induction used for all blocks after the
distinguished first block. -/
lemma hasPathCoverOnAtMost_complete_bipartite_blocks
    {G : SimpleGraph V} {X Y B : Finset V} {c : ℕ}
    (hBX : B ⊆ X) (hdisj : Disjoint X Y)
    (hadj : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y)
    (hcard : B.card ≤ c * (Y.card + 1)) :
    HasPathCoverOnAtMost G (B : Set V) c := by
  classical
  induction c generalizing B with
  | zero =>
      have hBcard : B.card = 0 := by simpa using hcard
      have hBempty : B = ∅ := Finset.card_eq_zero.mp hBcard
      subst B
      refine ⟨[], by simp, ?_⟩
      simp [IsPathCoverOn]
  | succ c ih =>
      by_cases hB0 : B.Nonempty
      · by_cases hsmall : B.card ≤ Y.card + 1
        · obtain ⟨T, hTY, hTcard, hp, hBmem, hsupport⟩ :=
            exists_alternating_path_for_small_left_block hBX hB0 hsmall hdisj hadj
          refine ⟨[alternateFinsets B T], by simp, ?_⟩
          constructor
          · intro p hpMem
            have hpEq : p = alternateFinsets B T := by
              simpa only [List.mem_singleton] using hpMem
            subst p
            exact hp
          · intro x hx
            exact ⟨alternateFinsets B T, by simp, hBmem x hx⟩
        · have hmB : Y.card + 1 ≤ B.card := by omega
          obtain ⟨B₀, hB₀B, hB₀card⟩ := Finset.exists_subset_card_eq hmB
          let R : Finset V := B \ B₀
          have hRX : R ⊆ X := by
            exact (Finset.sdiff_subset.trans hBX)
          have hRcard : R.card ≤ c * (Y.card + 1) := by
            change (B \ B₀).card ≤ c * (Y.card + 1)
            rw [Finset.card_sdiff_of_subset hB₀B, hB₀card]
            simp only [Nat.succ_mul] at hcard
            omega
          obtain ⟨qs, hqsLen, hqs⟩ := ih hRX hRcard
          have hB₀pos : B₀.Nonempty := by
            apply Finset.card_pos.mp
            rw [hB₀card]
            omega
          have hB₀X : B₀ ⊆ X := hB₀B.trans hBX
          obtain ⟨T, hTY, hTcard, hp, hB₀mem, hsupport⟩ :=
            exists_alternating_path_for_small_left_block hB₀X hB₀pos
              (by rw [hB₀card]) hdisj hadj
          let p : List V := alternateFinsets B₀ T
          refine ⟨p :: qs, ?_, ?_⟩
          · simp only [List.length_cons]
            omega
          · constructor
            · intro q hq
              rcases List.mem_cons.mp hq with rfl | hq
              · exact hp
              · exact hqs.1 q hq
            · intro x hx
              change x ∈ B at hx
              by_cases hx₀ : x ∈ B₀
              · exact ⟨p, by simp [p], hB₀mem x hx₀⟩
              · have hxR : x ∈ R := by simp [R, hx, hx₀]
                obtain ⟨q, hq, hxq⟩ := hqs.2 x hxR
                exact ⟨q, List.mem_cons_of_mem p hq, hxq⟩
      · have hBempty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB0
        subst B
        refine ⟨[], by simp, ?_⟩
        simp [IsPathCoverOn]

/-- Exact complete-bipartite block cover with a distinguished first path.

The returned `X₀` has exactly `|Y| + 1` vertices.  The displayed path is literally the first
path in the cover, and its support is exactly `X₀ ∪ Y`; hence it uses every vertex of `Y` and
exactly `|Y| + 1` vertices of `X`.  Later paths may reuse vertices of `Y`. -/
theorem exists_complete_bipartite_path_cover
    [DecidableEq V] {G : SimpleGraph V} {X Y : Finset V} {c : ℕ}
    (hdisj : Disjoint X Y)
    (hadj : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y)
    (hlower : Y.card + 1 ≤ X.card)
    (hupper : X.card ≤ c * (Y.card + 1)) :
    ∃ X₀ : Finset V, X₀ ⊆ X ∧ X₀.card = Y.card + 1 ∧
      ∃ qs : List (List V),
        (alternateFinsets X₀ Y :: qs).length ≤ c ∧
        IsPathCoverOn G ((X ∪ Y : Finset V) : Set V)
          (alternateFinsets X₀ Y :: qs) ∧
        pathSupport (alternateFinsets X₀ Y) = X₀ ∪ Y ∧
        (pathSupport (alternateFinsets X₀ Y) ∩ X).card = Y.card + 1 := by
  obtain ⟨X₀, hX₀X, hX₀card⟩ := Finset.exists_subset_card_eq hlower
  refine ⟨X₀, hX₀X, hX₀card, ?_⟩
  cases c with
  | zero =>
      exfalso
      have hXzero : X.card ≤ 0 := by simpa using hupper
      omega
  | succ d =>
      let R : Finset V := X \ X₀
      have hRcard : R.card ≤ d * (Y.card + 1) := by
        change (X \ X₀).card ≤ d * (Y.card + 1)
        rw [Finset.card_sdiff_of_subset hX₀X, hX₀card]
        simp only [Nat.succ_mul] at hupper
        omega
      have hRX : R ⊆ X := Finset.sdiff_subset
      obtain ⟨qs, hqsLen, hqs⟩ :=
        hasPathCoverOnAtMost_complete_bipartite_blocks hRX hdisj hadj hRcard
      have hX₀Y : Disjoint X₀ Y := hdisj.mono hX₀X (by rfl)
      have hp₀ : IsPath G (alternateFinsets X₀ Y) :=
        isPath_alternateFinsets_of_card_eq_add_one hX₀card hX₀Y
          (fun x hx y hy ↦ hadj x (hX₀X hx) y hy)
      have hsupport₀ : pathSupport (alternateFinsets X₀ Y) = X₀ ∪ Y := by
        simp [pathSupport]
      refine ⟨qs, ?_, ?_, hsupport₀, ?_⟩
      · simp only [List.length_cons]
        omega
      · constructor
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hp₀
          · exact hqs.1 p hp
        · intro v hv
          have hv' : v ∈ X ∨ v ∈ Y := by simpa using hv
          rcases hv' with hvX | hvY
          · by_cases hvX₀ : v ∈ X₀
            · exact ⟨alternateFinsets X₀ Y, by simp,
                mem_alternateFinsets.mpr (Or.inl hvX₀)⟩
            · have hvR : v ∈ R := by simp [R, hvX, hvX₀]
              obtain ⟨p, hp, hvp⟩ := hqs.2 v hvR
              exact ⟨p, List.mem_cons_of_mem _ hp, hvp⟩
          · exact ⟨alternateFinsets X₀ Y, by simp,
              mem_alternateFinsets.mpr (Or.inr hvY)⟩
      · have hinter : (X₀ ∪ Y) ∩ X = X₀ := by
          ext v
          constructor
          · intro hv
            have hv' : (v ∈ X₀ ∨ v ∈ Y) ∧ v ∈ X := by simpa using hv
            rcases hv' with ⟨hvX₀ | hvY, hvX⟩
            · exact hvX₀
            · exact (Finset.disjoint_left.mp hdisj hvX hvY).elim
          · intro hv
            have hvX : v ∈ X := hX₀X hv
            simp [hv, hvX]
        rw [hsupport₀, hinter, hX₀card]

/-- The bound-only form of `exists_complete_bipartite_path_cover`. -/
theorem hasPathCoverOnAtMost_complete_bipartite
    [DecidableEq V] {G : SimpleGraph V} {X Y : Finset V} {c : ℕ}
    (hdisj : Disjoint X Y)
    (hadj : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y)
    (hlower : Y.card + 1 ≤ X.card)
    (hupper : X.card ≤ c * (Y.card + 1)) :
    HasPathCoverOnAtMost G ((X ∪ Y : Finset V) : Set V) c := by
  classical
  obtain ⟨X₀, hX₀X, hX₀card, qs, hlen, hcover, hsupport, hfirstCard⟩ :=
    exists_complete_bipartite_path_cover hdisj hadj hlower hupper
  exact ⟨alternateFinsets X₀ Y :: qs, hlen, hcover⟩

end

end Erdos518
