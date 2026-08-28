import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Conjugation from an actual homotopy square

The path traced out by the basepoint during a homotopy conjugates the
induced maps on fundamental groups.  The endpoint equalities are retained
explicitly, and the conjugation uses Mathlib's reversed multiplication
of loop classes.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DiagonalQuotient

/-- An actual homotopy identifies its endpoint maps on fundamental groups
by conjugation along the actual basepoint trajectory. -/
theorem fundamentalGroup_conjugation_of_homotopy
    {F E : Type*} [TopologicalSpace F] [TopologicalSpace E]
    (f₀ f₁ : C(F, E)) (H : f₀.Homotopy f₁)
    (c : F) (e : E) (h₀ : f₀ c = e) (h₁ : f₁ c = e)
    (v : FundamentalGroup F c) :
    let s : FundamentalGroup E e := .mk ((H.evalAt c).cast h₀.symm h₁.symm)
    s * FundamentalGroup.mapOfEq f₀ h₀ v * s⁻¹ =
      FundamentalGroup.mapOfEq f₁ h₁ v := by
  let s : FundamentalGroup E e := .mk ((H.evalAt c).cast h₀.symm h₁.symm)
  change s * FundamentalGroup.mapOfEq f₀ h₀ v * s⁻¹ =
    FundamentalGroup.mapOfEq f₁ h₁ v
  have hsquare : s * FundamentalGroup.mapOfEq f₀ h₀ v =
      FundamentalGroup.mapOfEq f₁ h₁ v * s := by
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective v
    simp only [s, FundamentalGroup.mul_def, FundamentalGroup.mapOfEq_apply,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast,
      ← Path.Homotopic.Quotient.mk_trans]
    apply Path.Homotopic.Quotient.eq.mpr
    have hp := (Path.Homotopic.map_trans_evalAt H p).pathCast h₀.symm h₁.symm
    rw [Path.cast_trans (p.map f₀.continuous) (H.evalAt c) h₀.symm h₀.symm h₁.symm,
      Path.cast_trans (H.evalAt c) (p.map f₁.continuous) h₀.symm h₁.symm h₁.symm] at hp
    exact hp
  rw [hsquare, mul_inv_cancel_right]

/-- Pointed induced maps compose with the actual transported basepoint equalities. -/
theorem fundamentalGroup_mapOfEq_comp
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(B, C)) (a : A) (b : B) (c : C)
    (hf : f a = b) (hg : g b = c) (v : FundamentalGroup A a) :
    FundamentalGroup.mapOfEq (g.comp f) ((congrArg g hf).trans hg) v =
      FundamentalGroup.mapOfEq g hg (FundamentalGroup.mapOfEq f hf v) := by
  simp only [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.map_cast,
    Path.Homotopic.Quotient.map_comp, Path.Homotopic.Quotient.cast_cast]

end Wikipedia.HopfProblem.DiagonalQuotient
