/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Configuration
import ErdosProblems.Erdos518.Intersection
import ErdosProblems.Erdos518.PredecessorClique
import ErdosProblems.Erdos518.CliqueExtension

/-!
# The predecessor-clique bound

This file proves Chen--Chen's Lemma 3.3 in a normalized counterexample.  For an outside
vertex `y`, the predecessors on `Q` of its complement-colour neighbours, together with the
last vertex of `Q`, form a clique in `G`.  The opposite-colour intersection bound first rules
out complement degree at least `r`.  In the remaining equality case, degree `r - 1`, we make
the source argument completely explicit: order the clique as a Hamilton path ending at the
last vertex of `Q`, and append a vertex of `Y0` and a vertex of `X` outside the clique.  The
resulting `G`-path contains `r + 1` vertices of `Q`, again a contradiction.
-/

open scoped SimpleGraph

namespace Erdos518
namespace Configuration

universe u

variable {V : Type u} [Fintype V] (C : Configuration V)

noncomputable local instance muBoundDecidableEq : DecidableEq V := Classical.decEq V
noncomputable local instance muBoundDecidableAdj : DecidableRel C.G.Adj := Classical.decRel _
noncomputable local instance muBoundDecidableComplAdj : DecidableRel C.Gᶜ.Adj := Classical.decRel _

/-- The predecessor clique associated to an outside vertex. -/
noncomputable def predCliqueSet (y : V) : Finset V :=
  predecessorClique C.G C.Q C.q_isPath.1 y

/-- The endpoint of `Q` at which the canonical Hamilton order of `predCliqueSet` ends. -/
noncomputable def predCliqueEnd : V := C.Q.getLast C.q_isPath.1

/-- Every vertex of the predecessor clique lies on `Q`. -/
lemma predCliqueSet_subset_X (y : V) : C.predCliqueSet y ⊆ C.X := by
  classical
  simpa [predCliqueSet, X] using
    predecessorClique_subset_toFinset C.G C.Q C.q_isPath.1 y

/-- The final vertex of `Q` belongs to every predecessor clique. -/
@[simp] lemma predCliqueEnd_mem_predCliqueSet (y : V) :
    C.predCliqueEnd ∈ C.predCliqueSet y := by
  classical
  simp [predCliqueEnd, predCliqueSet, predecessorClique]

/-- The predecessor set of an outside vertex is a clique in the `G` colour. -/
lemma predCliqueSet_isClique {y : V} (hy : y ∈ C.Y) :
    C.G.IsClique (C.predCliqueSet y : Set V) := by
  classical
  apply predecessorClique_isClique C.q_isPath C.q_isGloballyLongest
  simpa [C.mem_X] using C.mem_Y.mp hy

/-- The predecessor clique has exactly complement degree plus one vertices. -/
lemma predCliqueSet_card_eq_blueDegree_add_one {y : V} (hy : y ∈ C.Y) :
    (C.predCliqueSet y).card = C.blueDegreeToX y + 1 := by
  classical
  have hyQ : y ∉ C.Q := by simpa [C.mem_X] using C.mem_Y.mp hy
  simpa [predCliqueSet, blueDegreeOnPath, blueNeighborsOnPath, blueDegreeToX, X] using
    predecessorClique_card_eq_blueDegree_add_one
      C.q_isPath C.q_isGloballyLongest hyQ

/-- The last vertex of a globally longest complement-colour path is `G`-adjacent to every
outside vertex. -/
lemma predCliqueEnd_adj_outside {y : V} (hy : y ∈ C.Y) :
    C.G.Adj C.predCliqueEnd y := by
  classical
  have hQrev : IsPath C.Gᶜ C.Q.reverse := isPath_reverse C.q_isPath
  have hlongRev : IsGloballyLongestMonoPath C.G C.Q.reverse := by
    refine ⟨Or.inr hQrev, ?_⟩
    intro p hp
    simpa using C.q_isGloballyLongest.2 p hp
  have hyQ : y ∉ C.Q := by simpa [C.mem_X] using C.mem_Y.mp hy
  have hyRev : y ∉ C.Q.reverse := by simpa using hyQ
  have hnblue := not_compl_adj_head_of_globally_longest hQrev hlongRev hyRev
  have hhead : C.Q.reverse.head hQrev.1 = C.predCliqueEnd := by
    simpa [predCliqueEnd] using List.head_reverse C.q_isPath.1
  rw [hhead] at hnblue
  by_contra hred
  have hne : y ≠ C.predCliqueEnd := by
    intro heq
    apply hyQ
    simpa [predCliqueEnd, heq] using List.getLast_mem C.q_isPath.1
  exact hnblue ((SimpleGraph.compl_adj C.G y C.predCliqueEnd).2
    ⟨hne, fun h ↦ hred h.symm⟩)

/-- A vertex of `Y0` is `G`-adjacent to every vertex on `Q`.  This elementary fact is
recorded locally so that the structural part of Lemma 3.3 does not depend on the later bundle
of basic counterexample bounds. -/
private lemma adj_of_Y0_X {y x : V} (hy : y ∈ C.Y0) (hx : x ∈ C.X) :
    C.G.Adj y x := by
  classical
  have hzero := (C.mem_Y0.mp hy).2
  have hnblue : ¬ C.Gᶜ.Adj y x := by
    intro hblue
    have hmem : x ∈ C.X.filter fun z ↦ C.Gᶜ.Adj y z :=
      Finset.mem_filter.mpr ⟨hx, hblue⟩
    have hposRaw : 0 < (C.X.filter fun z ↦ C.Gᶜ.Adj y z).card :=
      Finset.card_pos.mpr ⟨x, hmem⟩
    have hpos : 0 < C.blueDegreeToX y := by
      simpa [blueDegreeToX] using hposRaw
    omega
  by_contra hred
  have hne : y ≠ x := by
    intro h
    subst x
    exact Finset.disjoint_left.mp C.X_disjoint_Y hx (C.Y0_subset_Y hy)
  exact hnblue ((SimpleGraph.compl_adj C.G y x).2 ⟨hne, hred⟩)

/-- A red path supported on a subset of `X` meets `Q` in exactly that subset. -/
private lemma cliqueHamiltonOrder_inter_Q_card
    {S : Finset V} (hSX : S ⊆ C.X) (hS : C.G.IsClique (S : Set V))
    {e : V} (he : e ∈ S) :
    (pathSupport (cliqueHamiltonOrder S e) ∩ pathSupport C.Q).card = S.card := by
  classical
  have hp : IsPath C.G (cliqueHamiltonOrder S e) :=
    isPath_cliqueHamiltonOrder hS he
  have hsupp : pathSupport (cliqueHamiltonOrder S e) = S := by
    simpa [pathSupport] using toFinset_cliqueHamiltonOrder he
  have hSQ : S ⊆ pathSupport C.Q := by
    simpa [pathSupport, X] using hSX
  rw [hsupp, Finset.inter_eq_left.mpr hSQ]

/-- **Chen--Chen Lemma 3.3, pointwise form.**  Every member of `Y1` has complement degree
at most `r - 2`, written without truncated subtraction as `degree + 2 ≤ r`. -/
theorem blueDegreeToX_add_two_le_r_of_bounds
    (hY0 : C.Y0.Nonempty) (hcTwo : 2 ≤ C.c) (hwTwo : C.w + 2 ≤ C.r)
    {y : V} (hy : y ∈ C.Y1) :
    C.blueDegreeToX y + 2 ≤ C.r := by
  classical
  let S := C.predCliqueSet y
  let e := C.predCliqueEnd
  have hyY : y ∈ C.Y := C.Y1_subset_Y hy
  have hSX : S ⊆ C.X := C.predCliqueSet_subset_X y
  have heS : e ∈ S := C.predCliqueEnd_mem_predCliqueSet y
  have hSclique : C.G.IsClique (S : Set V) := C.predCliqueSet_isClique hyY
  have hScard : S.card = C.blueDegreeToX y + 1 :=
    C.predCliqueSet_card_eq_blueDegree_add_one hyY
  by_contra hdegree
  by_cases hrle : C.r ≤ C.blueDegreeToX y
  · let p := cliqueHamiltonOrder S e
    have hp : IsPath C.G p := isPath_cliqueHamiltonOrder hSclique heS
    have hinter : (pathSupport p ∩ pathSupport C.Q).card = S.card := by
      simpa [p] using C.cliqueHamiltonOrder_inter_Q_card hSX hSclique heS
    have hbound := C.path_inter_Q_card_le hp
    rw [hinter, hScard] at hbound
    omega
  · have hdeq : C.blueDegreeToX y + 1 = C.r := by omega
    have htwoCSq : 2 * C.c ≤ C.c ^ 2 := by
      calc
        2 * C.c = C.c * 2 := by omega
        _ ≤ C.c * C.c := Nat.mul_le_mul_left C.c hcTwo
        _ = C.c ^ 2 := by simp [pow_two]
    have hwlt : C.w < C.c ^ 2 := by
      have hr := C.r_le_two_mul_c
      omega
    have hXcard : C.X.card + C.w = C.c ^ 2 + C.r := by
      rw [← C.n_eq_card_X_add_w, ← C.n_eq_c_sq_add_r]
    have hSltX : S.card < C.X.card := by
      rw [hScard, hdeq]
      omega
    obtain ⟨x₀, hx₀X, hx₀S⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card hSltX
    obtain ⟨y₀, hy₀0⟩ := hY0
    have hy₀Y : y₀ ∈ C.Y := C.Y0_subset_Y hy₀0
    have hy₀x₀ : C.G.Adj y₀ x₀ := C.adj_of_Y0_X hy₀0 hx₀X
    have hey₀ : C.G.Adj e y₀ := by
      simpa [e] using C.predCliqueEnd_adj_outside hy₀Y
    have hy₀x₀ne : y₀ ≠ x₀ := by
      intro h
      subst x₀
      exact Finset.disjoint_left.mp C.X_disjoint_Y hx₀X hy₀Y
    let p := cliqueExtension S e [y₀] [x₀]
    have hp : IsPath C.G p := by
      exact isPath_cliqueExtension hSclique heS
        (by simp)
        (by simp)
        (by simp)
        (by
          rw [List.disjoint_iff_ne]
          intro a ha b hb
          simp only [List.mem_singleton] at ha hb
          subst a
          subst b
          exact hy₀x₀ne)
        (by
          intro z hz hzS
          simp only [List.mem_singleton] at hz
          subst z
          exact Finset.disjoint_left.mp C.X_disjoint_Y (hSX hzS) hy₀Y)
        (by simpa using hx₀S)
        (by simpa using hy₀x₀)
        (by simp)
        (by simpa using hey₀)
    have hinterX : (pathSupport p ∩ C.X).card = S.card + 1 := by
      simpa [p, pathSupport] using
        (cliqueExtension_inter_card (S := S) (X := C.X) heS
          (by simp : ([x₀] : List V).Nodup)
          (by simpa using hx₀S) hSX
          (by
            intro z hz
            simp only [List.mem_singleton] at hz
            subst z
            exact hx₀X)
          (by
            intro z hz
            simp only [List.mem_singleton] at hz
            subst z
            exact C.mem_Y.mp hy₀Y))
    have hinterQ : (pathSupport p ∩ pathSupport C.Q).card = S.card + 1 := by
      simpa [pathSupport, X] using hinterX
    have hbound := C.path_inter_Q_card_le hp
    rw [hinterQ, hScard, hdeq] at hbound
    omega

/-- The maximum complement degree on `Y1` satisfies the non-truncated form of the bound. -/
theorem mu_add_two_le_r_of_bounds
    (hY1 : C.Y1.Nonempty) (hY0 : C.Y0.Nonempty)
    (hcTwo : 2 ≤ C.c) (hwTwo : C.w + 2 ≤ C.r) :
    C.mu + 2 ≤ C.r := by
  obtain ⟨y, hy, hdegree⟩ := C.exists_mem_Y1_blueDegreeToX_eq_mu hY1
  rw [← hdegree]
  exact C.blueDegreeToX_add_two_le_r_of_bounds hY0 hcTwo hwTwo hy

/-- Chen--Chen Lemma 3.3 in the form consumed by the later case analysis. -/
theorem mu_le_r_sub_two_of_bounds
    (hY1 : C.Y1.Nonempty) (hY0 : C.Y0.Nonempty)
    (hcTwo : 2 ≤ C.c) (hwTwo : C.w + 2 ≤ C.r) :
    C.mu ≤ C.r - 2 := by
  have := C.mu_add_two_le_r_of_bounds hY1 hY0 hcTwo hwTwo
  omega

end Configuration
end Erdos518
