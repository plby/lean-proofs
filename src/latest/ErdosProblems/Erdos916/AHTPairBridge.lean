/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTThreeConnected
import ErdosProblems.Erdos916.AHTConnectivity

/-!
# Bridge between the two AHT two-pair certificate APIs

The source-level Section 6 development uses
`TwoDisjointDegreeThreeFalseTwinPairs`, while the connectivity and torso
development uses the earlier `TwoDisjointFalseTwinPairs` record.  Their
mathematical data are identical.  This file keeps the conversion explicit so
the final Section 7 assembly never relies on the two records being
definitionally equal.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Forget only the source-level name of a two-pair certificate. -/
def TwoDisjointDegreeThreeFalseTwinPairs.toConnectivityPairs
    (T : TwoDisjointDegreeThreeFalseTwinPairs G) :
    TwoDisjointFalseTwinPairs G :=
  { u := T.u
    v := T.v
    x := T.x
    y := T.y
    twins_uv := T.twin_uv
    twins_xy := T.twin_xy
    degree_u := T.degree_u
    degree_x := T.degree_x
    disjoint := T.disjoint }

@[simp] theorem TwoDisjointDegreeThreeFalseTwinPairs.toConnectivityPairs_u
    (T : TwoDisjointDegreeThreeFalseTwinPairs G) :
    T.toConnectivityPairs.u = T.u := rfl

@[simp] theorem TwoDisjointDegreeThreeFalseTwinPairs.toConnectivityPairs_v
    (T : TwoDisjointDegreeThreeFalseTwinPairs G) :
    T.toConnectivityPairs.v = T.v := rfl

@[simp] theorem TwoDisjointDegreeThreeFalseTwinPairs.toConnectivityPairs_x
    (T : TwoDisjointDegreeThreeFalseTwinPairs G) :
    T.toConnectivityPairs.x = T.x := rfl

@[simp] theorem TwoDisjointDegreeThreeFalseTwinPairs.toConnectivityPairs_y
    (T : TwoDisjointDegreeThreeFalseTwinPairs G) :
    T.toConnectivityPairs.y = T.y := rfl

end Erdos916
