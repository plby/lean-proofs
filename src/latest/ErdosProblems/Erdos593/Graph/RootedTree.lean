import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Rooted-tree geometry

Depth and closed-star facts used by the running-intersection reconstruction of
the bridge-block quotient forest.
-/

namespace Erdos593

namespace SimpleGraph

universe u

variable {V : Type u}

theorem eq_of_adj_of_dist_add_one
    {G : _root_.SimpleGraph V} (hG : G.IsTree)
    (root : V) {C D X : V}
    (hCX : G.Adj C X) (hDX : G.Adj D X)
    (hCdepth : G.dist root C + 1 = G.dist root X)
    (hDdepth : G.dist root D + 1 = G.dist root X) :
    C = D := by
  classical
  obtain ⟨pC, hpC, hpCdist⟩ := hG.connected.exists_path_of_dist root C
  obtain ⟨pD, hpD, hpDdist⟩ := hG.connected.exists_path_of_dist root D
  have hXnotC : X ∉ pC.support := by
    intro hX
    have hdist := G.dist_le (pC.takeUntil X hX)
    have htake := pC.length_takeUntil_le_length hX
    omega
  have hXnotD : X ∉ pD.support := by
    intro hX
    have hdist := G.dist_le (pD.takeUntil X hX)
    have htake := pD.length_takeUntil_le_length hX
    omega
  have hpCX : (pC.concat hCX).IsPath := hpC.concat hXnotC hCX
  have hpDX : (pD.concat hDX).IsPath := hpD.concat hXnotD hDX
  have hpaths : pC.concat hCX = pD.concat hDX := by
    exact Subtype.mk.inj (hG.isAcyclic.path_unique ⟨_, hpCX⟩ ⟨_, hpDX⟩)
  have hpenultimate := congrArg (fun p => p.penultimate) hpaths
  simpa using! hpenultimate

/-- In a tree rooted at `root`, if two distinct vertices `C` and `D` lie in the
closed star of `X` and `D` is no deeper than `C`, then the common star points
towards the parent edge of `C`. -/
theorem closedStar_earlier_direction
    {G : _root_.SimpleGraph V} (hG : G.IsTree)
    (root C D X : V)
    (hCD : C ≠ D)
    (hC : C = X ∨ G.Adj C X)
    (hD : D = X ∨ G.Adj D X)
    (hdepth : G.dist root D ≤ G.dist root C) :
    (X = C ∧ G.Adj D C ∧ G.dist root D + 1 = G.dist root C) ∨
      (X ≠ C ∧ G.Adj C X ∧ G.dist root X + 1 = G.dist root C) := by
  rcases hC with (rfl | hCX)
  · left
    have hDC : G.Adj D C := by
      rcases hD with (rfl | hDC)
      · exact (hCD rfl).elim
      · exact hDC
    refine ⟨rfl, hDC, ?_⟩
    rcases hG.dist_eq_dist_add_one_of_adj root hDC with h | h
    · omega
    · exact h.symm
  · right
    refine ⟨hCX.ne', hCX, ?_⟩
    rcases hG.dist_eq_dist_add_one_of_adj root hCX with hCXup | hXup
    · exact hCXup.symm
    · exfalso
      have hDX : G.Adj D X := by
        rcases hD with (rfl | hDX)
        · omega
        · exact hDX
      rcases hG.dist_eq_dist_add_one_of_adj root hDX with hDup | hXupD
      · omega
      · have hDC : D = C :=
          Erdos593.SimpleGraph.eq_of_adj_of_dist_add_one
            hG root hDX hCX hXupD.symm hXup.symm
        exact hCD hDC.symm

end SimpleGraph

end Erdos593
