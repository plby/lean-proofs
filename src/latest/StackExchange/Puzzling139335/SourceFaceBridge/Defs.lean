import StackExchange.Puzzling139335.Definitions
import StackExchange.Puzzling139335.ProperRotation.Model

/-!
# Concrete source-face data for the remaining two-double-corner case

The primitive geometric inputs below are containment, actual membership of
the source base and distinguished endpoints, and containment of two explicit
affine images in the square.  No crossing conclusion, scalar obstruction,
Jordan theorem, or impossible configuration is included among the inputs.
-/

open Set

namespace Puzzling139335.SourceFaceBridge

noncomputable section

def point (x y : ℝ) : Plane := !₂[x, y]

@[simp] theorem point_zero (x y : ℝ) : point x y 0 = x := rfl
@[simp] theorem point_one (x y : ℝ) : point x y 1 = y := rfl

theorem point_ext {p q : Plane} (h₀ : p 0 = q 0) (h₁ : p 1 = q 1) : p = q := by
  ext i
  fin_cases i <;> assumption

def lowerHalfSquare : Set Plane :=
  {p | p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 ∈ Icc (0 : ℝ) (1 / 2)}

/-- The two upper source normals are `(-cos α,sin α)` and
`(cos β,sin β)`, the reversed-straddle case left by the earlier reductions. -/
structure FaceData where
  α : ℝ
  β : ℝ
  a : ℝ
  b : ℝ
  M₁ : Plane
  M₂ : Plane

namespace FaceData

def normal₁ (d : FaceData) (p : Plane) : ℝ :=
  -Real.cos d.α * p 0 + Real.sin d.α * p 1

def tangent₁ (d : FaceData) (p : Plane) : ℝ :=
  -Real.sin d.α * p 0 - Real.cos d.α * p 1

def normal₂ (d : FaceData) (p : Plane) : ℝ :=
  Real.cos d.β * p 0 + Real.sin d.β * p 1

def tangent₂ (d : FaceData) (p : Plane) : ℝ :=
  -Real.sin d.β * p 0 + Real.cos d.β * p 1

def right (d : FaceData) (p : Plane) : Plane :=
  point (1 + d.normal₁ p - d.normal₁ d.M₁)
    (1 / 2 + d.tangent₁ p - d.tangent₁ d.M₁)

def leftProper (d : FaceData) (p : Plane) : Plane :=
  point (d.normal₂ d.M₂ - d.normal₂ p)
    (1 / 2 - d.tangent₂ p + d.tangent₂ d.M₂)

def leftGlide (d : FaceData) (p : Plane) : Plane :=
  point (d.normal₂ d.M₂ - d.normal₂ p)
    (1 / 2 + d.tangent₂ p - d.tangent₂ d.M₂)

def left (d : FaceData) (reversed : Bool) : Plane → Plane :=
  if reversed then d.leftGlide else d.leftProper

def face₁minus (d : FaceData) : Plane :=
  point (d.M₁ 0 - (1 / 2 - d.b) * Real.sin d.α)
    (d.M₁ 1 - (1 / 2 - d.b) * Real.cos d.α)

def face₁plus (d : FaceData) : Plane :=
  point (d.M₁ 0 + (1 / 2 - d.b) * Real.sin d.α)
    (d.M₁ 1 + (1 / 2 - d.b) * Real.cos d.α)

def face₂minus (d : FaceData) : Plane :=
  point (d.M₂ 0 + (1 / 2 - d.a) * Real.sin d.β)
    (d.M₂ 1 - (1 / 2 - d.a) * Real.cos d.β)

def face₂plus (d : FaceData) : Plane :=
  point (d.M₂ 0 - (1 / 2 - d.a) * Real.sin d.β)
    (d.M₂ 1 + (1 / 2 - d.a) * Real.cos d.β)

def scalarData (d : FaceData) : ProperRotation.Data where
  c := Real.cos d.α
  s := Real.sin d.α
  d := Real.cos d.β
  q := Real.sin d.β
  a := d.a
  b := d.b
  u := d.normal₁ d.M₁
  v := d.tangent₁ d.M₁
  w := d.normal₂ d.M₂
  z := d.tangent₂ d.M₂

@[simp] theorem scalarData_x1 (d : FaceData) : d.scalarData.x1 = d.M₁ 0 := by
  dsimp [scalarData, ProperRotation.Data.x1, normal₁, tangent₁]
  calc
    _ = (Real.cos d.α ^ 2 + Real.sin d.α ^ 2) * d.M₁ 0 := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring

@[simp] theorem scalarData_y1 (d : FaceData) : d.scalarData.y1 = d.M₁ 1 := by
  dsimp [scalarData, ProperRotation.Data.y1, normal₁, tangent₁]
  calc
    _ = (Real.cos d.α ^ 2 + Real.sin d.α ^ 2) * d.M₁ 1 := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring

@[simp] theorem scalarData_x2 (d : FaceData) : d.scalarData.x2 = d.M₂ 0 := by
  dsimp [scalarData, ProperRotation.Data.x2, normal₂, tangent₂]
  calc
    _ = (Real.cos d.β ^ 2 + Real.sin d.β ^ 2) * d.M₂ 0 := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring

@[simp] theorem scalarData_y2 (d : FaceData) : d.scalarData.y2 = d.M₂ 1 := by
  dsimp [scalarData, ProperRotation.Data.y2, normal₂, tangent₂]
  calc
    _ = (Real.cos d.β ^ 2 + Real.sin d.β ^ 2) * d.M₂ 1 := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring

end FaceData

/-- Concrete normalized source geometry, for either left-placement parity. -/
structure SupportedSource (d : FaceData) (reversed : Bool) (P : Set Plane) : Prop where
  alpha_pos : 0 < d.α
  alpha_lt_half_pi : d.α < Real.pi / 2
  beta_pos : 0 < d.β
  beta_lt_half_pi : d.β < Real.pi / 2
  a_pos : 0 < d.a
  a_lt_half : d.a < 1 / 2
  b_pos : 0 < d.b
  b_lt_half : d.b < 1 / 2
  source_subset : P ⊆ lowerHalfSquare
  base_mem : ∀ t ∈ Icc (0 : ℝ) 1, point t 0 ∈ P
  left_top_mem : point 0 d.a ∈ P
  right_top_mem : point 1 d.b ∈ P
  face₁minus_mem : d.face₁minus ∈ P
  face₁plus_mem : d.face₁plus ∈ P
  face₂minus_mem : d.face₂minus ∈ P
  face₂plus_mem : d.face₂plus ∈ P
  right_fits : MapsTo d.right P unitSquare
  left_fits : MapsTo (d.left reversed) P unitSquare

end

end Puzzling139335.SourceFaceBridge
