import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-! # Actual induced fundamental-group maps and homotopy equivalences -/

noncomputable section

open Function ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.FundamentalGroupTools

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

theorem map_comp (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    FundamentalGroup.map (g.comp f) x =
      (FundamentalGroup.map g (f x)).comp (FundamentalGroup.map f x) := by
  apply MonoidHom.ext
  intro γ
  obtain ⟨γ⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

theorem map_bijective_of_homotopyEquiv (e : X ≃ₕ Y) (x : X) :
    Bijective (FundamentalGroup.map e.toFun x) := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  exact E.fullyFaithfulFunctor.map_bijective
    (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk x)

/-- A freely moving basepoint does not change which original loops become null-homotopic. -/
theorem map_eq_one_iff_of_homotopy {f g : C(X, Y)} (H : f.Homotopy g) (x : X)
    (γ : FundamentalGroup X x) :
    FundamentalGroup.map f x γ = 1 ↔ FundamentalGroup.map g x γ = 1 := by
  let η := FundamentalGroupoidFunctor.homotopicMapsNatIso H
  have hn := η.naturality γ
  constructor
  · intro hγ
    change (FundamentalGroupoid.map f).map γ = CategoryTheory.CategoryStruct.id _ at hγ
    rw [hγ, CategoryTheory.Category.id_comp] at hn
    apply (CategoryTheory.cancel_epi (η.app (FundamentalGroupoid.mk x))).mp
    exact hn.symm.trans (CategoryTheory.Category.comp_id _).symm
  · intro hγ
    change (FundamentalGroupoid.map g).map γ = CategoryTheory.CategoryStruct.id _ at hγ
    rw [hγ, CategoryTheory.Category.comp_id] at hn
    apply (CategoryTheory.cancel_mono (η.app (FundamentalGroupoid.mk x))).mp
    exact hn.trans (CategoryTheory.Category.id_comp _).symm

/-- The paths are obtained by applying the inverse map and the original homotopy. -/
theorem pathConnected_of_homotopyEquiv [PathConnectedSpace Y] (e : X ≃ₕ Y) :
    PathConnectedSpace X := by
  refine ⟨⟨e.invFun (Classical.arbitrary Y)⟩, ?_⟩
  intro x y
  let H := e.left_inv.some
  exact ⟨(H.evalAt x).symm.trans
    (((PathConnectedSpace.somePath (e x) (e y)).map e.invFun.continuous).trans
      (H.evalAt y))⟩

end Wikipedia.SmoothSixDPoincare.FundamentalGroupTools
