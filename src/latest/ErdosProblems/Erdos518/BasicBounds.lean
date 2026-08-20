/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Configuration
import ErdosProblems.Erdos518.Intersection
import ErdosProblems.Erdos518.LongMono
import ErdosProblems.Erdos518.Rotation
import ErdosProblems.Erdos518.OneLongPath
import ErdosProblems.Erdos518.CompleteBipartiteCover
import ErdosProblems.Erdos518.CaseArithmetic

/-!
# Basic bounds in a normalized counterexample

This file proves Lemma 3.2 in the Chen--Chen resolution of Erdős Problem 518.  For the
normalized globally longest complementary-colour path `Q`, with outside set `Y` of order `w`,
the bounds are

`c ≤ w ≤ r - 2`, `Y1.Nonempty`, and `2*c - 1 - w ≤ a0` (hence `1 ≤ a0`).
-/

open scoped SimpleGraph

namespace Erdos518
namespace Configuration

universe u

variable {V : Type u} [Fintype V] (C : Configuration V)

noncomputable local instance basicBoundsDecidableEq : DecidableEq V := Classical.decEq V

/-- The distinguished path itself witnesses that the ambient type is nonempty. -/
lemma nonempty_vertex_type (C : Configuration V) : Nonempty V := by
  obtain ⟨v, q, hQ⟩ := List.exists_cons_of_ne_nil C.q_isPath.1
  exact ⟨v⟩

/-- A normalized counterexample has positive order. -/
lemma n_pos : 0 < C.n := by
  rw [n]
  exact Fintype.card_pos_iff.mpr C.nonempty_vertex_type

/-- Consequently its integer square root is positive. -/
lemma one_le_c : 1 ≤ C.c := by
  rw [c]
  exact Nat.sqrt_pos.mpr C.n_pos

/-- The order of `Q` is the ambient order minus the number of outside vertices. -/
lemma Q_length_eq_n_sub_w : C.Q.length = C.n - C.w := by
  have h := C.n_eq_Q_length_add_w
  omega

/-- If fewer than `c` vertices lay outside `Q`, `Q` and outside singleton paths would be a
complement-colour cover by at most `c` paths. -/
lemma w_ge_c : C.c ≤ C.w := by
  by_contra! hw
  have hcover : HasPathCoverAtMost C.Gᶜ (1 + C.w) := by
    simpa [Y, X, w, pathSupport] using
      (hasPathCoverAtMost_path_add_compl C.Gᶜ C.q_isPath)
  exact C.cover_failures.2 (hcover.mono (by omega))

/-- The Gerencsér--Gyárfás lower bound applies to the globally longest path `Q`. -/
lemma long_path_lower : C.n * 2 / 3 + 1 ≤ C.Q.length := by
  letI : Nonempty V := C.nonempty_vertex_type
  classical
  obtain ⟨p, hpmono, hplen⟩ := exists_long_monochromatic_path C.G
  exact hplen.trans (C.q_isGloballyLongest.2 p hpmono)

/-- The long-path estimate implies that fewer than half (rounded up) as many vertices lie
outside `Q` as lie on `Q`. -/
lemma w_lt_ceilHalf_card_X : C.w < ceilHalf C.X.card := by
  have hn := C.n_eq_Q_length_add_w
  have hl := C.long_path_lower
  rw [C.card_X, ceilHalf]
  omega

@[simp] lemma blueDegreeToX_eq_zero_iff {y : V} :
    C.blueDegreeToX y = 0 ↔ ∀ x ∈ C.X, ¬ C.Gᶜ.Adj y x := by
  classical
  simp [blueDegreeToX]

/-- Vertices in `Y0` are `G`-adjacent to every vertex of `X`. -/
lemma adj_of_mem_Y0_mem_X {y x : V} (hy : y ∈ C.Y0) (hx : x ∈ C.X) :
    C.G.Adj y x := by
  classical
  have hzero := (C.mem_Y0.mp hy).2
  have hnblue : ¬ C.Gᶜ.Adj y x := by
    intro hblue
    have hmem : x ∈ C.X.filter fun z ↦ C.Gᶜ.Adj y z :=
      Finset.mem_filter.mpr ⟨hx, hblue⟩
    have hpos : 0 < C.blueDegreeToX y := by
      exact Finset.card_pos.mpr ⟨x, hmem⟩
    omega
  by_contra hred
  have hne : y ≠ x := by
    intro h
    subst x
    exact (Finset.disjoint_left.mp C.X_disjoint_Y hx (C.Y0_subset_Y hy)).elim
  exact hnblue ((SimpleGraph.compl_adj C.G y x).2 ⟨hne, hred⟩)

/-- If `Q` is closed, all edges between its support and the outside set have the other colour:
otherwise rotating the cycle and adjoining the outside endpoint makes a longer path. -/
lemma adj_X_Y_of_closed (hclosed : IsClosedPath C.Gᶜ C.Q)
    {x y : V} (hx : x ∈ C.X) (hy : y ∈ C.Y) : C.G.Adj x y := by
  rcases hclosed with ⟨hQ, hends⟩
  have hyQ : y ∉ C.Q := by simpa [C.mem_X] using C.mem_Y.mp hy
  have hmax : IsGloballyLongestMonoPath C.Gᶜ C.Q :=
    (isGloballyLongestMonoPath_compl_iff C.G C.Q).2 C.q_isGloballyLongest
  simpa using
    (compl_cross_of_closed_longest hQ hmax hends hyQ (C.mem_X.mp hx)).symm

/-- The basic arithmetic needed by both complete-bipartite-cover contradictions. -/
lemma complete_bipartite_card_bounds :
    C.w + 1 ≤ C.X.card ∧ C.X.card ≤ C.c * (C.w + 1) := by
  constructor
  · have hhalf := C.w_lt_ceilHalf_card_X
    rw [ceilHalf] at hhalf
    omega
  · have hsum : C.X.card + C.w = C.c ^ 2 + C.r := by
      rw [← C.n_eq_card_X_add_w, ← C.n_eq_c_sq_add_r]
    have hcw := C.w_ge_c
    have hr := C.r_le_two_mul_c
    have hmul := Nat.mul_le_mul_left (C.c + 1) hcw
    nlinarith

/-- Complete `G`-adjacency between `X` and `Y` contradicts the failure of a `c`-path cover. -/
lemma not_complete_bipartite_X_Y
    (hadj : ∀ x ∈ C.X, ∀ y ∈ C.Y, C.G.Adj x y) : False := by
  classical
  obtain ⟨hlower, hupper⟩ := C.complete_bipartite_card_bounds
  have hlocal : HasPathCoverOnAtMost C.G (((C.X ∪ C.Y : Finset V) : Set V)) C.c :=
    hasPathCoverOnAtMost_complete_bipartite C.X_disjoint_Y hadj hlower hupper
  have hcover : HasPathCoverAtMost C.G C.c := by
    rw [hasPathCoverAtMost_iff_on_univ]
    simpa [C.X_union_Y] using hlocal
  exact C.cover_failures.1 hcover

/-- A normalized counterexample is necessarily in the non-cut case. -/
lemma not_isCutColoring : ¬ IsCutColoring C.G := by
  intro hcut
  have hclosed := C.q_closed_if_cut hcut
  apply C.not_complete_bipartite_X_Y
  intro x hx y hy
  exact C.adj_X_Y_of_closed hclosed hx hy

/-- The rotation lemma and the opposite-colour intersection bound give `w ≤ r - 2`. -/
lemma w_le_r_sub_two : C.w ≤ C.r - 2 := by
  letI : Nonempty V := C.nonempty_vertex_type
  classical
  have hQlen : 2 ≤ C.Q.length := by
    have hc := C.one_le_c
    have hcw := C.w_ge_c
    have hhalf := C.w_lt_ceilHalf_card_X
    rw [C.card_X, ceilHalf] at hhalf
    omega
  have hmax : IsGloballyLongestMonoPath C.Gᶜ C.Q :=
    (isGloballyLongestMonoPath_compl_iff C.G C.Q).2 C.q_isGloballyLongest
  have hncut : ¬ IsCutColoring C.Gᶜ := by
    simpa using C.not_isCutColoring
  obtain ⟨P, hP, hPY, hinter⟩ :=
    rotation_strict C.q_isPath hmax hncut hQlen C.Y
      (by simpa [X] using C.X_disjoint_Y.symm)
      (by simpa only [C.w_eq_card_Y, C.card_X, ceilHalf] using
        C.w_lt_ceilHalf_card_X)
  have hP' : IsPath C.G P := by simpa using hP
  have hinter' : C.w + 2 ≤ (pathSupport P ∩ pathSupport C.Q).card := by
    simpa [w, X, pathSupport] using hinter
  have hupper := C.path_inter_Q_card_le hP'
  omega

/-- The first outside part is nonempty.  Otherwise all `X`--`Y` edges have colour `G`, which
is the complete-bipartite contradiction above. -/
lemma Y1_nonempty : C.Y1.Nonempty := by
  by_contra hY1
  have hY10 : C.Y1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hY1
  apply C.not_complete_bipartite_X_Y
  intro x hx y hy
  have hy0 : y ∈ C.Y0 := by
    have : y ∈ C.Y0 ∪ C.Y1 := by simpa [C.Y0_union_Y1] using hy
    simpa [hY10] using this
  exact (C.adj_of_mem_Y0_mem_X hy0 hx).symm

/-- Cardinality form of `Y1_nonempty`. -/
lemma one_le_a1 : 1 ≤ C.a1 := by
  exact Finset.card_pos.mpr C.Y1_nonempty

/-- The one-long-path cover would have size `1 + ceilHalf a1 + a0`; its failure forces that
quantity to exceed `c`. -/
lemma one_long_cover_failure : C.c + 1 ≤ 1 + ceilHalf C.a1 + C.a0 := by
  classical
  have hcover : HasPathCoverAtMost C.Gᶜ (1 + ceilHalf C.a1 + C.a0) := by
    simpa [ceilHalf, X, Y, Y0, Y1, a0, a1] using
      (hasPathCoverAtMost_one_long_path C.Gᶜ C.Q C.q_isPath)
  by_contra h
  exact C.cover_failures.2 (hcover.mono (by omega))

/-- The zero-blue-degree part satisfies `2*c - 1 - w ≤ a0`. -/
lemma a0_lower_bound : 2 * C.c - 1 - C.w ≤ C.a0 := by
  exact cover_failure_forces_a0_sub_bound C.w_eq_a0_add_a1 C.one_long_cover_failure

/-- The zero-blue-degree part is nonempty. -/
lemma one_le_a0 : 1 ≤ C.a0 := by
  exact basic_a0_positive C.one_le_c C.w_le_r_sub_two C.r_le_two_mul_c C.a0_lower_bound

/-- Finset form of the positivity of `a0`. -/
lemma Y0_nonempty : C.Y0.Nonempty := by
  apply Finset.card_pos.mp
  have h := C.one_le_a0
  rw [C.a0_eq_card_Y0] at h
  omega

/-- Trivial but convenient cardinality upper bound. -/
lemma a0_le_w : C.a0 ≤ C.w := by
  have h := C.w_eq_a0_add_a1
  omega

/-- Chen--Chen Lemma 3.2, bundled in the order used by the later case analysis. -/
lemma basic_bounds :
    C.c ≤ C.w ∧ C.w ≤ C.r - 2 ∧ 1 ≤ C.a1 ∧
      2 * C.c - 1 - C.w ≤ C.a0 ∧ 1 ≤ C.a0 := by
  exact ⟨C.w_ge_c, C.w_le_r_sub_two, C.one_le_a1, C.a0_lower_bound, C.one_le_a0⟩

end Configuration
end Erdos518
