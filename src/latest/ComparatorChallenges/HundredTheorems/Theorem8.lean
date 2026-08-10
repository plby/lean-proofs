import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

namespace Theorem8

inductive Constructible : ℝ → Prop
  | rat (q : ℚ) :
      Constructible (q : ℝ)
  | add {x y : ℝ} (hx : Constructible x) (hy : Constructible y) :
      Constructible (x + y)
  | neg {x : ℝ} (hx : Constructible x) :
      Constructible (-x)
  | mul {x y : ℝ} (hx : Constructible x) (hy : Constructible y) :
      Constructible (x * y)
  | inv {x : ℝ} (hx : Constructible x) (hx0 : x ≠ 0) :
      Constructible x⁻¹
  | sqrt {x : ℝ} (hx : Constructible x) (hx0 : 0 ≤ x) :
      Constructible (Real.sqrt x)

def ConstructibleAngle (θ : ℝ) : Prop :=
  Constructible (Real.cos θ)

theorem freek_08 :
    (¬ (∀ θ : ℝ, ConstructibleAngle θ → ConstructibleAngle (θ / 3))) ∧
    (¬ ∃ x : ℝ, x ^ 3 = (2 : ℝ) ∧ Constructible x) := by
  sorry

open scoped EuclideanGeometry

abbrev Point : Type := EuclideanSpace ℝ (Fin 2)

namespace RulerCompass

def line (A B : Point) : Set Point :=
  {P : Point | ∃ t : ℝ, P = (1 - t) • A + t • B}

def circle (C : Point) (r : ℝ) : Set Point :=
  {P : Point | (dist : Point → Point → ℝ) P C = r}

def circleThrough (C D : Point) : Set Point :=
  circle C ((dist : Point → Point → ℝ) C D)

structure RCBase where
  O : Point
  E : Point
  hOE : O ≠ E
  unit : (dist : Point → Point → ℝ) O E = 1

inductive RCPoint (cfg : RCBase) : Point → Prop
  | base_O :
      RCPoint cfg (RCBase.O cfg)
  | base_E :
      RCPoint cfg (RCBase.E cfg)
  | line_line
      {A B C D P : Point}
      (hA : RCPoint cfg A) (hB : RCPoint cfg B)
      (hC : RCPoint cfg C) (hD : RCPoint cfg D)
      (hAB : A ≠ B) (hCD : C ≠ D)
      (hLines : line A B ≠ line C D)
      (hP₁ : P ∈ line A B) (hP₂ : P ∈ line C D) :
      RCPoint cfg P
  | line_circle
      {A B C D P : Point}
      (hA : RCPoint cfg A) (hB : RCPoint cfg B)
      (hC : RCPoint cfg C) (hD : RCPoint cfg D)
      (hAB : A ≠ B) (hCD : C ≠ D)
      (hP₁ : P ∈ line A B)
      (hP₂ : P ∈ circleThrough C D) :
      RCPoint cfg P
  | circle_circle
      {A B C D P : Point}
      (hA : RCPoint cfg A) (hB : RCPoint cfg B)
      (hC : RCPoint cfg C) (hD : RCPoint cfg D)
      (hAB : A ≠ B) (hCD : C ≠ D)
      (hCircles : circleThrough A B ≠ circleThrough C D)
      (hP₁ : P ∈ circleThrough A B)
      (hP₂ : P ∈ circleThrough C D) :
      RCPoint cfg P

noncomputable def segmentLength (cfg : RCBase) (P : Point) : ℝ :=
  (dist : Point → Point → ℝ) (RCBase.O cfg) P

noncomputable def baseAngle (cfg : RCBase) (P : Point) : ℝ :=
  ∠ (RCBase.E cfg) (RCBase.O cfg) P

def RCConstructibleAngle (cfg : RCBase) (θ : ℝ) : Prop :=
  ∃ P : Point, RCPoint cfg P ∧ baseAngle cfg P = θ

theorem freek_08_plane (cfg : RCBase) :
    (¬ (∀ θ : ℝ,
          RCConstructibleAngle cfg θ →
          RCConstructibleAngle cfg (θ / 3))) ∧
    (¬ ∃ P : Point, RCPoint cfg P ∧ (segmentLength cfg P) ^ 3 = (2 : ℝ)) := by
  sorry

end RulerCompass

end Theorem8
