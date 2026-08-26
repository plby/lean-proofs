import ErdosProblems.Erdos593.Graph.FiniteClosureLayeringConstruction
import ErdosProblems.Erdos593.TripleSystem.LowCodegreeClosure

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Layering the low-codegree completion closure

This module instantiates the finite closure-layering construction with the
two-point low-codegree completion closure.  Its main local consequence is that
a completion of a low pair cannot lie strictly after both endpoints.
-/

namespace Erdos593

universe u v

namespace TripleSystem

variable {W : Type u} {D : Type v}

/-- The finite low-pair completion operator admits a finite closure layering
on every uncountable host vertex type. -/
theorem exists_lowPairClosureLayering_of_uncountable
    (H : TripleSystem W D) (t : Nat)
    (hW : Cardinal.aleph0 < Cardinal.mk W) :
    Nonempty (FiniteClosureLayering 2 (lowPairClosureFinset H t)
      (Cardinal.mk W).ord.ToType) := by
  exact _root_.Erdos593.FiniteClosureLayeringConstruction.exists_finiteClosureLayering_of_uncountable
    (lowPairClosureFinset H t) hW (by decide)

/-- In any layering for the low-pair completion closure, a completion vertex
of a pair that is not high at threshold `t` cannot be strictly later than both
of its endpoints. -/
theorem not_both_rank_lt_of_thirdVertexWitness_of_not_highPair
    {I : Type u} [LinearOrder I]
    {H : TripleSystem W D} {t : Nat} {x y z : W}
    (L : FiniteClosureLayering 2 (lowPairClosureFinset H t) I)
    (p : ThirdVertexWitness H x y z)
    (hxy : Not (HighPair H t x y)) :
    Not (And (L.rank x < L.rank z) (L.rank y < L.rank z)) := by
  classical
  intro hboth
  have hxz : L.rank x < L.rank z := hboth.1
  have hyz : L.rank y < L.rank z := hboth.2
  let s : {q : Finset W // q.card = 2} := by
    exact Subtype.mk ({x, y} : Finset W) (Finset.card_pair p.left_ne_right)
  have hs : (s.1 : Set W) = {x, y} := by
    dsimp only [s]
    ext w
    simp
  have hz : Membership.mem (lowPairClosureFinset H t s) z :=
    mem_lowPairClosureFinset_of_not_highPair_of_pair (H := H) (t := t)
      s hs hxy (Nonempty.intro p)
  have hnot : Not (Membership.mem (lowPairClosureFinset H t s) z) := by
    apply FiniteClosureLayering.not_mem_of_all_rank_lt L z s.1 s.2
    intro w hw
    have hwset : Membership.mem (s.1 : Set W) w := by
      exact hw
    rw [hs] at hwset
    have hw' : Or (w = x) (w = y) := by
      simpa using! hwset
    cases hw' with
    | inl hwx =>
        subst w
        exact hxz
    | inr hwy =>
        subst w
        exact hyz
  exact hnot hz

end TripleSystem

end Erdos593
