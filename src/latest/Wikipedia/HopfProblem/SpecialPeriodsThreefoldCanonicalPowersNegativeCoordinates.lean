import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalBasePullback
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalBaseTwistIdealFrames

/-!
# Dual coordinates of the actual pulled-back ideal line

The original ideal frames of `O(-infinity)` are the functions `1` and
`w`.  Their pullbacks obey the inverse coefficient cocycle of the
constructed line, on the entire overlap.  They therefore give genuine
dual-frame coefficients, whose zero set is exactly the actual cusp fibre.
Analyticity is asserted on the original chart domains, not for the
scalar obtained by choosing a preferred frame at every point.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersNegative

open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

attribute [local instance] Threefold.chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The unchanged cocycle of the actual pulled-back ideal line. -/
abbrev data := GlobalBasePullback.cartier.transitions

/-- The pullback of the actual ideal frame's value in each original chart. -/
def dualCoefficient (b : Bool) (x : Threefold.Space) : ℂ :=
  GlobalBasePullback.cartier.denominator b x

@[simp] theorem dualCoefficient_false (x : Threefold.Space) :
    dualCoefficient false x = 1 := rfl

@[simp] theorem dualCoefficient_true (x : Threefold.Space) :
    dualCoefficient true x =
      CanonicalGlobal.BaseTwist.infinityCoordinate (Threefold.projectionSphere x) := rfl

/-- This is the literal pullback of the previously constructed ideal frame. -/
theorem dualCoefficient_eq_idealFrameValue (b : Bool) (x : Threefold.Space) :
    dualCoefficient b x =
      CanonicalGlobal.BaseTwist.idealFrameValue b (Threefold.projectionSphere x) := by
  cases b <;> rfl

theorem mem_baseSet (b : Bool) (x : Threefold.Space) :
    x ∈ data.baseSet b ↔ Threefold.projectionSphere x ∈ frameChart b := Iff.rfl

@[simp] theorem mem_baseSet_false (x : Threefold.Space) :
    x ∈ data.baseSet false ↔ Threefold.projectionSphere x ≠ (∞ : RiemannSphere) :=
  mem_finiteChart (Threefold.projectionSphere x)

@[simp] theorem mem_baseSet_true (x : Threefold.Space) :
    x ∈ data.baseSet true ↔ Threefold.projectionSphere x ≠ ((0 : ℂ) : RiemannSphere) :=
  mem_infinityChart (Threefold.projectionSphere x)

@[simp] theorem mem_genericSet (x : Threefold.Space) :
    x ∈ GlobalBasePullback.cartier.genericSet ↔
      Threefold.projectionSphere x ≠ (∞ : RiemannSphere) :=
  mem_finiteChart (Threefold.projectionSphere x)

/-- Evaluation of the genuine ideal-sheaf frame, not just a named denominator. -/
theorem dualCoefficient_eq_chartFrame_value (b : Bool) (x : Threefold.Space)
    (hx : x ∈ data.baseSet b) :
    dualCoefficient b x = (chartFrame b (frameChart b) le_rfl).val
      ⟨Threefold.projectionSphere x, (mem_baseSet b x).mp hx⟩ := by
  rw [CanonicalGlobal.BaseTwist.chartFrame_value, dualCoefficient_eq_idealFrameValue]

theorem dualCoefficient_holomorphicOn (b : Bool) :
    ContMDiffOn IF 𝓘(ℂ) ω (dualCoefficient b) (data.baseSet b) :=
  GlobalBasePullback.cartier.denominator_holomorphic b

theorem dualCoefficient_holomorphicAt (b : Bool) {x : Threefold.Space}
    (hx : x ∈ data.baseSet b) : ContMDiffAt IF 𝓘(ℂ) ω (dualCoefficient b) x :=
  (dualCoefficient_holomorphicOn b).contMDiffAt ((data.isOpen_baseSet b).mem_nhds hx)

/-- The inverse cocycle holds also at zeros, with no generic-locus hypothesis. -/
theorem dualCoefficient_transition (i j : Bool) (x : Threefold.Space)
    (hij : x ∈ data.baseSet i ∩ data.baseSet j) :
    dualCoefficient j x * (data.transition i j x : ℂ) = dualCoefficient i x := by
  have h := GlobalBasePullback.cartier.ratio i j x hij
  change (1 : ℂ) * dualCoefficient i x =
    (data.transition i j x : ℂ) * 1 * dualCoefficient j x at h
  simp only [one_mul, mul_one] at h
  exact (mul_comm _ _).trans h.symm

theorem dualCoefficient_ne_zero (b : Bool) (x : Threefold.Space)
    (hb : x ∈ data.baseSet b) (hx : x ∈ GlobalBasePullback.cartier.genericSet) :
    dualCoefficient b x ≠ 0 :=
  GlobalBasePullback.cartier.denominator_ne_zero b x hb hx

theorem dualCoefficient_ne_zero_of_projection_ne_infty (b : Bool) (x : Threefold.Space)
    (hb : x ∈ data.baseSet b) (hx : Threefold.projectionSphere x ≠ (∞ : RiemannSphere)) :
    dualCoefficient b x ≠ 0 :=
  dualCoefficient_ne_zero b x hb ((mem_genericSet x).mpr hx)

/-- Every cusp point belongs to the unchanged reciprocal chart. -/
theorem mem_baseSet_true_of_projection_infty (x : Threefold.Space)
    (hx : Threefold.projectionSphere x = (∞ : RiemannSphere)) :
    x ∈ data.baseSet true := by
  apply (mem_baseSet true x).mpr
  change Threefold.projectionSphere x ∈ infinityChart
  rw [hx]
  exact infty_mem_infinityChart

theorem dualCoefficient_true_eq_zero_of_projection_infty (x : Threefold.Space)
    (hx : Threefold.projectionSphere x = (∞ : RiemannSphere)) :
    dualCoefficient true x = 0 := by
  rw [dualCoefficient_true, hx, CanonicalGlobal.BaseTwist.infinityCoordinate_infty]

theorem dualCoefficient_eq_zero_of_projection_infty (b : Bool) (x : Threefold.Space)
    (hb : x ∈ data.baseSet b) (hx : Threefold.projectionSphere x = (∞ : RiemannSphere)) :
    dualCoefficient b x = 0 := by
  have h := dualCoefficient_transition b true x
    ⟨hb, mem_baseSet_true_of_projection_infty x hx⟩
  rw [dualCoefficient_true_eq_zero_of_projection_infty x hx, zero_mul] at h
  exact h.symm

/-- On every valid chart the dual coefficient vanishes exactly on the cusp fibre. -/
theorem dualCoefficient_eq_zero_iff (b : Bool) (x : Threefold.Space)
    (hb : x ∈ data.baseSet b) :
    dualCoefficient b x = 0 ↔ Threefold.projectionSphere x = (∞ : RiemannSphere) := by
  constructor
  · intro hz
    by_contra hx
    exact dualCoefficient_ne_zero_of_projection_ne_infty b x hb hx hz
  · exact dualCoefficient_eq_zero_of_projection_infty b x hb

/-- A chosen scalar coordinate; no global holomorphy is asserted for this frame choice. -/
def preferredDualCoefficient (x : Threefold.Space) : ℂ :=
  dualCoefficient (data.indexAt x) x

theorem preferredDualCoefficient_ne_zero (x : Threefold.Space)
    (hx : x ∈ GlobalBasePullback.cartier.genericSet) : preferredDualCoefficient x ≠ 0 :=
  dualCoefficient_ne_zero _ x (data.mem_baseSet_at x) hx

theorem preferredDualCoefficient_eq_zero_iff (x : Threefold.Space) :
    preferredDualCoefficient x = 0 ↔ Threefold.projectionSphere x = (∞ : RiemannSphere) :=
  dualCoefficient_eq_zero_iff _ x (data.mem_baseSet_at x)

theorem preferredDualCoefficient_eq_zero_of_mem_support {x : Threefold.Space}
    (hx : x ∈ GlobalCusp.support) : preferredDualCoefficient x = 0 :=
  (preferredDualCoefficient_eq_zero_iff x).mpr hx

theorem preferredDualCoefficient_ne_zero_of_not_mem_support {x : Threefold.Space}
    (hx : x ∉ GlobalCusp.support) : preferredDualCoefficient x ≠ 0 :=
  (preferredDualCoefficient_eq_zero_iff x).not.mpr hx

theorem preferredDualCoefficient_zeroSet :
    {x : Threefold.Space | preferredDualCoefficient x = 0} = GlobalCusp.support := by
  ext x
  exact preferredDualCoefficient_eq_zero_iff x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersNegative
