import Wikipedia.HopfProblem.SpecialPeriodsTriangleCompactifiedOrders

/-!
# The three actual marked charts used for the threefold fillings

The index consists of the added cusp and the two genuine elliptic orbit
centers.  Its coordinates are the already constructed exponential cusp
chart and the normalized Cayley-power quotient charts.  Their analytic
inverse maps and their positive disc targets belong to the actual compact
triangle curve; no abstract charts or uniformization are assumed.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

attribute [local instance] triangleCompactifiedChartedSpace

/-- The cusp (`none`) and the two elliptic points (`some j`). -/
abbrev Puncture := Option Elliptic.Kind

def puncturePoint : Puncture → TriangleCompactifiedOrbitSpace
  | none => triangleCuspPoint
  | some j => Triangle.ellipticCompactifiedCenter j

@[simp] theorem puncturePoint_cusp : puncturePoint none = triangleCuspPoint := rfl

@[simp] theorem puncturePoint_elliptic (j : Elliptic.Kind) :
    puncturePoint (some j) = Triangle.ellipticCompactifiedCenter j := rfl

/-- These are three distinct actual points, independently of a sphere
coordinate on the compact quotient. -/
theorem puncturePoint_injective : Function.Injective puncturePoint := by
  intro i j h
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some j => exact (Triangle.ellipticCompactifiedCenter_ne_cusp j h.symm).elim
  | some i =>
      cases j with
      | none => exact (Triangle.ellipticCompactifiedCenter_ne_cusp i h).elim
      | some j =>
          congr 1
          cases i <;> cases j
          · rfl
          · exact (triangleCompactifiedCenterOne_ne_centerTwo h).elim
          · exact (triangleCompactifiedCenterOne_ne_centerTwo h.symm).elim
          · rfl

/-- The actual local quotient coordinates, with no further normalization. -/
def punctureChart : Puncture → OpenPartialHomeomorph TriangleCompactifiedOrbitSpace ℂ
  | none => Triangle.cuspFullChart Triangle.width le_rfl
  | some j => Triangle.ellipticCompactifiedChart j

@[simp] theorem punctureChart_cusp :
    punctureChart none = Triangle.cuspFullChart Triangle.width le_rfl := rfl

@[simp] theorem punctureChart_elliptic (j : Elliptic.Kind) :
    punctureChart (some j) = Triangle.ellipticCompactifiedChart j := rfl

/-- Each chart already has a genuine round-disc target of this radius. -/
def punctureChartRadius : Puncture → ℝ
  | none => Triangle.cuspRadius Triangle.width
  | some _ => 1

theorem punctureChartRadius_pos (i : Puncture) : 0 < punctureChartRadius i := by
  cases i with
  | none => exact Triangle.cuspRadius_pos Triangle.width
  | some j => norm_num [punctureChartRadius]

theorem punctureChart_target (i : Puncture) :
    (punctureChart i).target = Metric.ball 0 (punctureChartRadius i) := by
  cases i with
  | none => exact Triangle.cuspFullChart_target Triangle.width le_rfl
  | some j => exact Triangle.ellipticCompactifiedChart_target j

theorem puncturePoint_mem_source (i : Puncture) :
    puncturePoint i ∈ (punctureChart i).source := by
  cases i with
  | none => exact Triangle.cuspPoint_mem_cuspNeighborhood Triangle.width
  | some j => exact Triangle.ellipticCompactifiedChart_center_mem_source j

@[simp] theorem punctureChart_point (i : Puncture) :
    punctureChart i (puncturePoint i) = 0 := by
  cases i with
  | none => exact Triangle.cuspFullChart_cuspPoint Triangle.width le_rfl
  | some j => exact Triangle.ellipticCompactifiedChart_center j

@[simp] theorem punctureChart_symm_zero (i : Puncture) :
    (punctureChart i).symm 0 = puncturePoint i := by
  rw [← punctureChart_point i]
  exact (punctureChart i).left_inv (puncturePoint_mem_source i)

theorem punctureChart_eq_zero_iff (i : Puncture) {x : TriangleCompactifiedOrbitSpace}
    (hx : x ∈ (punctureChart i).source) :
    punctureChart i x = 0 ↔ x = puncturePoint i := by
  constructor
  · intro h
    apply (punctureChart i).injOn hx (puncturePoint_mem_source i)
    exact h.trans (punctureChart_point i).symm
  · rintro rfl
    exact punctureChart_point i

theorem punctureChart_holomorphic (i : Puncture) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (punctureChart i) (punctureChart i).source := by
  cases i with
  | none => exact triangleCompactified_cuspChart_holomorphic
  | some j => exact Triangle.ellipticCompactifiedChart_holomorphic j

theorem punctureChart_symm_holomorphic (i : Puncture) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (punctureChart i).symm (punctureChart i).target := by
  cases i with
  | none => exact triangleCompactified_cuspChart_symm_holomorphic
  | some j => exact Triangle.ellipticCompactifiedChart_symm_holomorphic j

/-- The same genuine coordinate as an analytic partial biholomorphism. -/
def puncturePartial (i : Puncture) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleCompactifiedOrbitSpace ℂ ω where
  toPartialEquiv := (punctureChart i).toPartialEquiv
  open_source := (punctureChart i).open_source
  open_target := (punctureChart i).open_target
  contMDiffOn_toFun := punctureChart_holomorphic i
  contMDiffOn_invFun := punctureChart_symm_holomorphic i

@[simp] theorem puncturePartial_toOpenPartialHomeomorph (i : Puncture) :
    (puncturePartial i).toOpenPartialHomeomorph = punctureChart i := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
