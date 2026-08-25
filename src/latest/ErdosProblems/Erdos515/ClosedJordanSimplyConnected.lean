/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.JordanSimplyConnected
import Wikipedia.SchoenfliesTheorem

/-!
# Simply connected closed Jordan domains

The full Jordan--Schönflies extension identifies a Jordan curve together with its bounded
complementary component with a closed square.  This is the closed-disc form needed to contract
a loop that runs on the polygonal boundary as well as through its interior.
-/

open Set

namespace Schoenflies

/-- A Jordan curve together with its bounded complementary component is simply connected. -/
theorem IsJordanCurve.isSimplyConnected_union_inside {S : Set Plane} (hS : IsJordanCurve S) :
    IsSimplyConnected (S ∪ inside S) := by
  let K : Set Plane := S ∪ inside S
  obtain ⟨e⟩ := hS.homeomorph_modelCurve
  obtain ⟨u, v, huv, -⟩ := exists_isHomeoOn_of_homeomorph e
  obtain ⟨F, G, hFG, -⟩ := squareExtension S u v hS huv
  let E : K ≃ₜ Plane.closedSquare 0 1 := hFG.toHomeomorph
  letI : ContractibleSpace (Plane.closedSquare 0 1) :=
    (Plane.convex_closedSquare 0 1).contractibleSpace
      ⟨0, by simp [Plane.closedSquare, Plane.supDist, Plane.supNorm]⟩
  letI : ContractibleSpace K := E.contractibleSpace
  change SimplyConnectedSpace K
  infer_instance

end Schoenflies
