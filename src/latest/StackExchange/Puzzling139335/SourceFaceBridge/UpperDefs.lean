import StackExchange.Puzzling139335.SourceFaceBridge.Defs

/-!
# Actual source data for arbitrary upper support normals

The angles here range over the whole open upper half-plane.  In particular,
the signs of their horizontal components are not selected in advance.
The square containments imply all support and tangent-strip inequalities.
-/

open Set

namespace Puzzling139335.SourceFaceBridge

noncomputable section

structure UpperFaceData where
  φ : ℝ
  ψ : ℝ
  a : ℝ
  b : ℝ
  M₁ : Plane
  M₂ : Plane

namespace UpperFaceData

def normal₁ (d : UpperFaceData) (p : Plane) : ℝ :=
  Real.cos d.φ * p 0 + Real.sin d.φ * p 1

def tangent₁ (d : UpperFaceData) (p : Plane) : ℝ :=
  -Real.sin d.φ * p 0 + Real.cos d.φ * p 1

def normal₂ (d : UpperFaceData) (p : Plane) : ℝ :=
  Real.cos d.ψ * p 0 + Real.sin d.ψ * p 1

def tangent₂ (d : UpperFaceData) (p : Plane) : ℝ :=
  -Real.sin d.ψ * p 0 + Real.cos d.ψ * p 1

def right (d : UpperFaceData) (p : Plane) : Plane :=
  point (1 + d.normal₁ p - d.normal₁ d.M₁)
    (1 / 2 + d.tangent₁ p - d.tangent₁ d.M₁)

def leftProper (d : UpperFaceData) (p : Plane) : Plane :=
  point (d.normal₂ d.M₂ - d.normal₂ p)
    (1 / 2 - d.tangent₂ p + d.tangent₂ d.M₂)

def leftGlide (d : UpperFaceData) (p : Plane) : Plane :=
  point (d.normal₂ d.M₂ - d.normal₂ p)
    (1 / 2 + d.tangent₂ p - d.tangent₂ d.M₂)

def left (d : UpperFaceData) (reversed : Bool) : Plane → Plane :=
  if reversed then d.leftGlide else d.leftProper

def face₁minus (d : UpperFaceData) : Plane :=
  point (d.M₁ 0 + (1 / 2 - d.b) * Real.sin d.φ)
    (d.M₁ 1 - (1 / 2 - d.b) * Real.cos d.φ)

def face₁plus (d : UpperFaceData) : Plane :=
  point (d.M₁ 0 - (1 / 2 - d.b) * Real.sin d.φ)
    (d.M₁ 1 + (1 / 2 - d.b) * Real.cos d.φ)

def face₂minus (d : UpperFaceData) : Plane :=
  point (d.M₂ 0 + (1 / 2 - d.a) * Real.sin d.ψ)
    (d.M₂ 1 - (1 / 2 - d.a) * Real.cos d.ψ)

def face₂plus (d : UpperFaceData) : Plane :=
  point (d.M₂ 0 - (1 / 2 - d.a) * Real.sin d.ψ)
    (d.M₂ 1 + (1 / 2 - d.a) * Real.cos d.ψ)

end UpperFaceData

/-- Explicit source memberships and square containments for two upper normals. -/
structure UpperSupportedSource (d : UpperFaceData) (reversed : Bool)
    (P : Set Plane) : Prop where
  phi_pos : 0 < d.φ
  phi_lt_pi : d.φ < Real.pi
  psi_pos : 0 < d.ψ
  psi_lt_pi : d.ψ < Real.pi
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

namespace UpperSupportedSource

variable {d : UpperFaceData} {reversed : Bool} {P : Set Plane}

theorem right_inverse_box (h : UpperSupportedSource d reversed P)
    {p : Plane} (hp : p ∈ P) :
    -1 ≤ d.normal₁ p - d.normal₁ d.M₁ ∧
      d.normal₁ p - d.normal₁ d.M₁ ≤ 0 ∧
      -(1 / 2 : ℝ) ≤ d.tangent₁ p - d.tangent₁ d.M₁ ∧
      d.tangent₁ p - d.tangent₁ d.M₁ ≤ 1 / 2 := by
  have hfit := h.right_fits hp
  change (0 ≤ 1 + d.normal₁ p - d.normal₁ d.M₁ ∧
    1 + d.normal₁ p - d.normal₁ d.M₁ ≤ 1) ∧
    (0 ≤ 1 / 2 + d.tangent₁ p - d.tangent₁ d.M₁ ∧
      1 / 2 + d.tangent₁ p - d.tangent₁ d.M₁ ≤ 1) at hfit
  constructor
  · linarith only [hfit.1.1]
  constructor
  · linarith only [hfit.1.2]
  constructor
  · linarith only [hfit.2.1]
  · linarith only [hfit.2.2]

theorem left_inverse_box (h : UpperSupportedSource d reversed P)
    {p : Plane} (hp : p ∈ P) :
    -1 ≤ d.normal₂ p - d.normal₂ d.M₂ ∧
      d.normal₂ p - d.normal₂ d.M₂ ≤ 0 ∧
      -(1 / 2 : ℝ) ≤ d.tangent₂ p - d.tangent₂ d.M₂ ∧
      d.tangent₂ p - d.tangent₂ d.M₂ ≤ 1 / 2 := by
  have hfit := h.left_fits hp
  cases reversed
  · change (0 ≤ d.normal₂ d.M₂ - d.normal₂ p ∧
      d.normal₂ d.M₂ - d.normal₂ p ≤ 1) ∧
      (0 ≤ 1 / 2 - d.tangent₂ p + d.tangent₂ d.M₂ ∧
        1 / 2 - d.tangent₂ p + d.tangent₂ d.M₂ ≤ 1) at hfit
    constructor
    · linarith only [hfit.1.2]
    constructor
    · linarith only [hfit.1.1]
    constructor
    · linarith only [hfit.2.2]
    · linarith only [hfit.2.1]
  · change (0 ≤ d.normal₂ d.M₂ - d.normal₂ p ∧
      d.normal₂ d.M₂ - d.normal₂ p ≤ 1) ∧
      (0 ≤ 1 / 2 + d.tangent₂ p - d.tangent₂ d.M₂ ∧
        1 / 2 + d.tangent₂ p - d.tangent₂ d.M₂ ≤ 1) at hfit
    constructor
    · linarith only [hfit.1.2]
    constructor
    · linarith only [hfit.1.1]
    constructor
    · linarith only [hfit.2.1]
    · linarith only [hfit.2.2]

theorem source_supports (h : UpperSupportedSource d reversed P) {p : Plane}
    (hp : p ∈ P) :
    d.normal₁ p ≤ d.normal₁ d.M₁ ∧ d.normal₂ p ≤ d.normal₂ d.M₂ := by
  have h₁ := (h.right_inverse_box hp).2.1
  have h₂ := (h.left_inverse_box hp).2.1
  exact ⟨by linarith only [h₁], by linarith only [h₂]⟩

end UpperSupportedSource

end

end Puzzling139335.SourceFaceBridge
