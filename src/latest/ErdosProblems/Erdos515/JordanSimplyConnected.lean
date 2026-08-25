/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Wikipedia.SchoenfliesTheorem.InteriorHomeomorphism
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Simply connected Jordan interiors

This file converts the unbundled restricted homeomorphisms used by the Schönflies development
to Mathlib homeomorphisms of subtypes.  The Jordan--Schönflies interior theorem then identifies
the inside of any Jordan curve with an open square.  Since the latter is convex and nonempty,
the inside is contractible, hence simply connected.
-/

open Set

namespace Schoenflies

/-- An `IsHomeoOn` pair induces a genuine homeomorphism between the corresponding subtypes. -/
noncomputable def IsHomeoOn.toHomeomorph {f g : Plane → Plane} {S T : Set Plane}
    (h : IsHomeoOn f g S T) : S ≃ₜ T where
  toFun x := ⟨f x, h.mapsTo x.2⟩
  invFun y := ⟨g y, h.mapsTo_inv y.2⟩
  left_inv x := Subtype.ext (h.invOn.1 x.2)
  right_inv y := Subtype.ext (h.invOn.2 y.2)
  continuous_toFun := h.continuousOn.domRestrict.subtype_mk (fun x => h.mapsTo x.2)
  continuous_invFun := h.continuousOn_inv.domRestrict.subtype_mk (fun x => h.mapsTo_inv x.2)

/-- The bounded complementary component of a Jordan curve is simply connected. -/
theorem IsJordanCurve.isSimplyConnected_inside {C : Set Plane} (hC : IsJordanCurve C) :
    IsSimplyConnected (inside C) := by
  obtain ⟨F, G, hFG⟩ := exists_isHomeoOn_inside_openSquare hC
  let e : inside C ≃ₜ Plane.openSquare 0 1 := hFG.toHomeomorph
  letI : ContractibleSpace (Plane.openSquare 0 1) :=
    (Plane.convex_openSquare 0 1).contractibleSpace
      ⟨0, by simp [Plane.openSquare, Plane.supDist, Plane.supNorm]⟩
  letI : ContractibleSpace (inside C) := e.contractibleSpace
  show SimplyConnectedSpace (inside C)
  infer_instance

end Schoenflies
