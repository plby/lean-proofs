/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LinkReserveAccounting

/-!
# Residual links supported by the crossing reserve

After the preliminary cover has covered every crossing edge outside the
reserved set, every still-uncovered spoke belongs to the reserve.  Therefore
both sides of any balanced residual-link bisection satisfy the spoke-support
hypothesis needed by the reserve-aware law update.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Every graph edge crossing `U` which was not retained in `reserve` has
already been covered by `P`. -/
def CoversCrossingOutsideReserve
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V))
    (P : TripleSystemOn V) : Prop :=
  ∀ v x, v ∉ U → x ∈ U → G.Adj v x → s(v, x) ∉ reserve →
    (coveredGraph P).Adj v x

lemma residualNeighbors_spoke_mem_reserve
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {reserve : Finset (Sym2 V)}
    {P : TripleSystemOn V}
    (hcover : CoversCrossingOutsideReserve G U reserve P)
    {v x : V} (hv : v ∉ U) (hxU : x ∈ U)
    (hx : x ∈ residualNeighbors G P v) : s(v, x) ∈ reserve := by
  by_contra hnot
  have hres := mem_residualNeighbors_iff.mp hx
  exact hres.2 (hcover v x hv hxU hres.1 hnot)

/-- A residual bipartition inherits reserve support on both sides. -/
lemma IsResidualBipartition.spokesIn_of_coversOutsideReserve
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {reserve : Finset (Sym2 V)}
    {P : TripleSystemOn V} {v : V} {K : BipartiteLink V}
    (hK : IsResidualBipartition G P v K)
    (hv : v ∉ U) (hinner : residualNeighbors G P v ⊆ U)
    (hcover : CoversCrossingOutsideReserve G U reserve P) :
    K.SpokesIn reserve := by
  have hleftRes : K.left ⊆ residualNeighbors G P v := by
    intro x hx
    rw [← hK.2.1]
    exact mem_union_left K.right hx
  have hrightRes : K.right ⊆ residualNeighbors G P v := by
    intro x hx
    rw [← hK.2.1]
    exact mem_union_right K.left hx
  constructor
  · intro x hx
    rw [hK.1]
    exact residualNeighbors_spoke_mem_reserve hcover hv
      (hinner (hleftRes hx)) (hleftRes hx)
  · intro x hx
    rw [hK.1]
    exact residualNeighbors_spoke_mem_reserve hcover hv
      (hinner (hrightRes hx)) (hrightRes hx)

end

end Erdos207
