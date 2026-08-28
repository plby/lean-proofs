import Wikipedia.HopfProblem.FundamentalGroupVanKampenTransport

/-!
# Horizontal and vertical paths in a continuous square

These are the literal restrictions of a continuous square.  In particular,
their subpaths use the affine interval parametrization of `Path.subpath`.
-/

noncomputable section

open Set
open scoped unitInterval

namespace Wikipedia.HopfProblem.FundamentalGroupVanKampen

variable {X : Type*} [TopologicalSpace X]

/-- The horizontal path at first coordinate `s` in a continuous square. -/
def squareHorizontal (F : C(I × I, X)) (s : I) : Path (F (s, 0)) (F (s, 1)) where
  toFun t := F (s, t)
  continuous_toFun := F.continuous.comp (continuous_const.prodMk continuous_id)
  source' := rfl
  target' := rfl

/-- The vertical path at second coordinate `t` in a continuous square. -/
def squareVertical (F : C(I × I, X)) (t : I) : Path (F (0, t)) (F (1, t)) where
  toFun s := F (s, t)
  continuous_toFun := F.continuous.comp (continuous_id.prodMk continuous_const)
  source' := rfl
  target' := rfl

@[simp] theorem squareHorizontal_apply (F : C(I × I, X)) (s t : I) :
    squareHorizontal F s t = F (s, t) := rfl

@[simp] theorem squareVertical_apply (F : C(I × I, X)) (s t : I) :
    squareVertical F t s = F (s, t) := rfl

@[simp] theorem squareHorizontal_subpath_apply (F : C(I × I, X)) (s a b u : I) :
    (squareHorizontal F s).subpath a b u = F (s, Icc.convexComb a b u) := rfl

@[simp] theorem squareVertical_subpath_apply (F : C(I × I, X)) (t a b u : I) :
    (squareVertical F t).subpath a b u = F (Icc.convexComb a b u, t) := rfl

end Wikipedia.HopfProblem.FundamentalGroupVanKampen
