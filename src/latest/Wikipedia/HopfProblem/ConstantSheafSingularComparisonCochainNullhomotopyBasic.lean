import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainTopologicalHomotopy
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPresheafAugmentation
import Mathlib.Topology.Homotopy.Contractible

/-!
# Explicit closed-cochain formulas for the actual homotopy operators

The original cochain homotopy equation is evaluated on a closed cochain.
In positive degrees its error is the coboundary of the actual homotopy
component.  In degree zero the two values agree.  Thus pullback of a closed
zero-cochain along a nullhomotopic map is an actual constant cochain.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz

section General

variable {K L : CochainComplex AddCommGrpCat.{0} ℕ} {f g : K ⟶ L}

/-- A closed positive cochain detects the literal degree-lowering homotopy component. -/
theorem homotopy_apply_closed_succ (h : Homotopy f g) (n : ℕ)
    (c : K.X (n + 1)) (hc : K.d (n + 1) (n + 2) c = 0) :
    f.f (n + 1) c = L.d n (n + 1) (h.hom (n + 1) n c) + g.f (n + 1) c := by
  have he := h.comm (n + 1)
  rw [dNext_eq h.hom (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from rfl),
    prevD_eq h.hom (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)] at he
  have hv := ConcreteCategory.congr_hom he c
  change f.f (n + 1) c =
    h.hom (n + 2) (n + 1) (K.d (n + 1) (n + 2) c) +
      L.d n (n + 1) (h.hom (n + 1) n c) + g.f (n + 1) c at hv
  rw [hc, map_zero, zero_add] at hv
  exact hv

/-- A closed zero-cochain has equal values under homotopic cochain maps. -/
theorem homotopy_apply_closed_zero (h : Homotopy f g)
    (c : K.X 0) (hc : K.d 0 1 c = 0) : f.f 0 c = g.f 0 c := by
  have he := h.comm 0
  rw [dNext_eq h.hom (show (ComplexShape.up ℕ).Rel 0 1 from rfl),
    prevD_eq_zero h.hom 0 (by simp)] at he
  have hv := ConcreteCategory.congr_hom he c
  change f.f 0 c = h.hom 1 0 (K.d 0 1 c) + 0 + g.f 0 c at hv
  rw [hc, map_zero, zero_add, zero_add] at hv
  exact hv

end General

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable (A : AddCommGrpCat.{0})

/-- Genuine continuous-map pullback preserves the original cocycle equation. -/
theorem singularPullback_closed (f : C(X, Y)) (i j : ℕ)
    (c : Cochains Y A i) (hc : (singularCochainComplex Y A).d i j c = 0) :
    (singularCochainComplex X A).d i j ((singularPullback A f).f i c) = 0 := by
  have he := ConcreteCategory.congr_hom ((singularPullback A f).comm i j) c
  change (singularCochainComplex X A).d i j ((singularPullback A f).f i c) =
    (singularPullback A f).f j ((singularCochainComplex Y A).d i j c) at he
  exact he.trans (by rw [hc, map_zero])

/-- Pulling a zero-cochain back along an actual constant map gives its value
on the corresponding original singular vertex. -/
theorem singularPullback_const_zero (y : Y) (c : Cochains Y A 0) :
    (singularPullback A (ContinuousMap.const X y)).f 0 c =
      constantCochain X A (c (simplexChain Y 0 (ContinuousMap.const (Simplex 0) y))) := by
  apply cochain_ext X A 0
  intro σ
  rw [singularPullback_simplex, constantCochain_simplex]
  rfl

/-- The pullback of a closed zero-cochain along a nullhomotopic map is an
actual constant, with no connectedness assumption on its source. -/
theorem nullhomotopic_pullback_closed_zero (f : C(X, Y)) (hf : f.Nullhomotopic)
    (c : Cochains Y A 0) (hc : (singularCochainComplex Y A).d 0 1 c = 0) :
    ∃ a : A, (singularPullback A f).f 0 c = constantCochain X A a := by
  obtain ⟨y, ⟨H⟩⟩ := hf
  refine ⟨c (simplexChain Y 0 (ContinuousMap.const (Simplex 0) y)), ?_⟩
  exact (homotopy_apply_closed_zero (singularCochainHomotopy A H) c hc).trans
    (singularPullback_const_zero A y c)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
