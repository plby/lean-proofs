import StackExchange.Puzzling139335.ThreeCorners
import StackExchange.Puzzling139335.ReflectionSeparation
import StackExchange.Puzzling139335.N4Midline.FrameCoordinates
import StackExchange.Puzzling139335.N4Midline.BottomCoverage
import StackExchange.Puzzling139335.RectangularHull.Interlacing

/-!
# Normalized actual data for the diagonal-reflection case

The prototype and its reflected copy occupy the opposite corners zero and
two. The remaining two actual affine isometries place two distinct full
corner types at corners one and three, in either order. Supporting-frame
and triangle bounds are recorded only after being derived geometrically.
-/

open Set

namespace Puzzling139335.N4Diagonal

open ThreeCorners

noncomputable section

/-- The closed half-square below the anti-diagonal. -/
def lowerTriangle : Set Plane := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}

theorem lowerTriangle_subset_unitSquare : lowerTriangle ⊆ unitSquare := by
  intro x hx
  exact ⟨⟨hx.1, by linarith [hx.2.1, hx.2.2]⟩,
    ⟨hx.2.1, by linarith [hx.1, hx.2.2]⟩⟩

/-- The four actual images, indexed with the reflected pair at zero and two. -/
def pieces (P : Set Plane) (e f : Plane ≃ᵃⁱ[ℝ] Plane) : Fin 4 → Set Plane :=
  ![P, e '' P, ReflectionSeparation.antiDiagonal '' P, f '' P]

/-- A normalized frame model with actual set coverage and actual isometries.
No separation, side-contact classification, or impossibility is postulated. -/
structure Model where
  P : Set Plane
  p : Plane
  q : Plane
  θ : ℝ
  β : ℝ
  e : Plane ≃ᵃⁱ[ℝ] Plane
  f : Plane ≃ᵃⁱ[ℝ] Plane
  firstCorner : Fin 4
  lastCorner : Fin 4
  jordan : IsJordanRegion P
  triangle : P ⊆ lowerTriangle
  origin_mem : (0 : Plane) ∈ P
  origin_full : UnitPairs.IsFullSquareCorner P 0
  p_mem : p ∈ P
  q_mem : q ∈ P
  p_ne_origin : p ≠ 0
  q_ne_origin : q ≠ 0
  p_ne_q : p ≠ q
  p_full : UnitPairs.IsFullSquareCorner P p
  q_full : UnitPairs.IsFullSquareCorner P q
  theta_bounds : θ ∈ Icc (0 : ℝ) (Real.pi / 2)
  beta_bounds : β ∈ Icc θ (Real.pi / 2)
  first_support : ∀ x ∈ P,
    0 ≤ inner ℝ (perpRay θ) (x - p) ∧ inner ℝ (ray θ) (x - p) ≤ 0
  last_support : ∀ x ∈ P,
    inner ℝ (ray β) (x - q) ≤ 0 ∧ inner ℝ (perpRay β) (x - q) ≤ 0
  first_subset : e '' P ⊆ unitSquare
  last_subset : f '' P ⊆ unitSquare
  first_corner : e p = corner firstCorner
  last_corner : f q = corner lastCorner
  corner_order : (firstCorner = 1 ∧ lastCorner = 3) ∨
    (firstCorner = 3 ∧ lastCorner = 1)
  origin_only_corner : ∀ j : Fin 4, corner j ∈ P → j = 0
  first_only_corner : ∀ j : Fin 4, corner j ∈ e '' P → j = firstCorner
  last_only_corner : ∀ j : Fin 4, corner j ∈ f '' P → j = lastCorner
  cover : ∀ x ∈ unitSquare,
    x ∈ P ∨ x ∈ ReflectionSeparation.antiDiagonal '' P ∨ x ∈ e '' P ∨ x ∈ f '' P
  disjoint : Pairwise fun i j : Fin 4 =>
    Disjoint (interior (pieces P e f i)) (interior (pieces P e f j))

namespace Model

def piece (m : Model) : Fin 4 → Set Plane := pieces m.P m.e m.f

theorem subset_square (m : Model) : m.P ⊆ unitSquare :=
  m.triangle.trans lowerTriangle_subset_unitSquare

theorem beta_nonneg (m : Model) : 0 ≤ m.β :=
  m.theta_bounds.1.trans m.beta_bounds.1

def firstFrame (m : Model) : SupportCorner m.P m.p where
  mem := m.p_mem
  firstNormal := ray m.θ
  secondNormal := -perpRay m.θ
  norm_firstNormal := norm_ray m.θ
  norm_secondNormal := by simp only [norm_neg, norm_perpRay]
  orthogonal := by simp only [inner_neg_right, ray_inner_perpRay, neg_zero]
  first_support := fun x hx => (m.first_support x hx).2
  second_support := by
    intro x hx
    simpa only [inner_neg_left] using neg_nonpos.mpr (m.first_support x hx).1

def lastFrame (m : Model) : SupportCorner m.P m.q where
  mem := m.q_mem
  firstNormal := ray m.β
  secondNormal := perpRay m.β
  norm_firstNormal := norm_ray m.β
  norm_secondNormal := norm_perpRay m.β
  orthogonal := ray_inner_perpRay m.β
  first_support := fun x hx => (m.last_support x hx).1
  second_support := fun x hx => (m.last_support x hx).2

theorem first_center (m : Model) :
    m.e.symm squareCenter = m.p + (1 / 2 : ℝ) • (perpRay m.θ - ray m.θ) := by
  rw [m.p_full.symm_center_eq m.firstFrame m.e m.firstCorner m.first_subset m.first_corner]
  simp only [firstFrame, SupportCorner.bisector, smul_add, smul_neg, sub_eq_add_neg]
  abel

theorem last_center (m : Model) :
    m.f.symm squareCenter = m.q - (1 / 2 : ℝ) • (ray m.β + perpRay m.β) := by
  rw [m.q_full.symm_center_eq m.lastFrame m.f m.lastCorner m.last_subset m.last_corner]
  rfl

theorem first_mem_iff (m : Model) (x : Plane) : x ∈ m.e '' m.P ↔ m.e.symm x ∈ m.P := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [m.e.symm_apply_apply] using hy
  · intro hx
    exact ⟨m.e.symm x, hx, m.e.apply_symm_apply x⟩

theorem last_mem_iff (m : Model) (x : Plane) : x ∈ m.f '' m.P ↔ m.f.symm x ∈ m.P := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [m.f.symm_apply_apply] using hy
  · intro hx
    exact ⟨m.f.symm x, hx, m.f.apply_symm_apply x⟩

end Model

/-- The orientation-preserving first-corner placement at corner one or three. -/
def firstPlus (j : Fin 4) (p : Plane) (θ : ℝ) (x : Plane) : Plane :=
  SquareSymmetry.cornerFlip j
    !₂[-inner ℝ (ray θ) (x - p), inner ℝ (perpRay θ) (x - p)]

def firstMinus (j : Fin 4) (p : Plane) (θ : ℝ) (x : Plane) : Plane :=
  ReflectionSeparation.antiDiagonal (firstPlus j p θ x)

/-- The orientation-preserving last-corner placement at corner one or three. -/
def lastPlus (j : Fin 4) (q : Plane) (β : ℝ) (x : Plane) : Plane :=
  SquareSymmetry.cornerFlip j
    !₂[-inner ℝ (perpRay β) (x - q), -inner ℝ (ray β) (x - q)]

def lastMinus (j : Fin 4) (q : Plane) (β : ℝ) (x : Plane) : Plane :=
  ReflectionSeparation.antiDiagonal (lastPlus j q β x)

end

end Puzzling139335.N4Diagonal
