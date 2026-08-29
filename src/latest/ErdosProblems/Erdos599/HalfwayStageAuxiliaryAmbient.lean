/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayStageGeometryCore
import ErdosProblems.Erdos599.FiniteDeletion

/-!
# Ambient incidence of the Section 9 stage auxiliaries

The lower-cardinal linkage used in Assertion 9.31 is not selected in an
arbitrary web.  Its auxiliary is obtained from a ladder stage by deleting a
carrier and, when necessary, changing only the target set.  This file records
the resulting edge provenance all the way back to the ambient web.  The
statement is exactly the certificate required by the moving occurrence
request: no edge created by cardinal induction can become a nonambient real
edge after it is lifted.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open CardinalInduction Ladder

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

namespace ClubStageGeometry

variable (C : ClubStageGeometry Gamma Y kappa theta)

/-- Every edge of a ladder stage is an edge of the ambient web.  The two
steps are visible in the proof: the stage is the essential part of a
quotient, and both operations only delete edges. -/
theorem stageWeb_adj_ambient (a : Ladder.Stage theta) {x y : V}
    (hxy : (C.ladder.stageWeb a).graph.Adj x y) :
    Gamma.graph.Adj x y := by
  exact Gamma.quotient_adj_imp
    ((Gamma.quotient (Gamma.terminalFrontier
      (C.ladder.warpAt a))).essentialPart_adj_imp hxy)

/-- Vertex deletion from a ladder stage preserves ambient incidence. -/
theorem deleteStageWeb_adj_ambient (a : Ladder.Stage theta) (X : Set V)
    {x y : V} (hxy : ((C.ladder.stageWeb a).delete X).graph.Adj x y) :
    Gamma.graph.Adj x y := by
  exact C.stageWeb_adj_ambient a
    ((C.ladder.stageWeb a).delete_adj_imp hxy)

/-- Retargeting changes only the distinguished target set, so the actual
old-stage residual/interval auxiliary still has only ambient edges. -/
theorem retargetDeleteStageWeb_adj_ambient
    (a : Ladder.Stage theta) (X T : Set V) {x y : V}
    (hxy : (((C.ladder.stageWeb a).delete X).retarget T).graph.Adj x y) :
    Gamma.graph.Adj x y := by
  exact C.deleteStageWeb_adj_ambient a X hxy

/-- The specialization used by the old-to-new interval transaction. -/
theorem oldResidualInterval_adj_ambient
    {X : Set V} {x y : V}
    (hxy : (((C.ladder.stageWeb C.oldStage).delete X).retarget
      (C.newSlice \ X)).graph.Adj x y) :
    Gamma.graph.Adj x y := by
  exact C.retargetDeleteStageWeb_adj_ambient C.oldStage X
    (C.newSlice \ X) hxy

end ClubStageGeometry

#print axioms ClubStageGeometry.stageWeb_adj_ambient
#print axioms ClubStageGeometry.deleteStageWeb_adj_ambient
#print axioms ClubStageGeometry.retargetDeleteStageWeb_adj_ambient
#print axioms ClubStageGeometry.oldResidualInterval_adj_ambient

end Erdos599.Blueprint.LinkageBlueprint
