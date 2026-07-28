import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine

namespace Theorem84

open EuclideanGeometry Real InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]
variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P] [Nonempty P]

structure Similarity (P : Type*) [MetricSpace P] where
  toFun : P → P
  r : ℝ
  r_pos : r > 0
  dist_eq : ∀ x y, dist (toFun x) (toFun y) = r * dist x y

instance (P : Type*) [MetricSpace P] : CoeFun (Similarity P) (fun _ => P → P) :=
  ⟨Similarity.toFun⟩

noncomputable def lineIntersection (p1 : P) (v1 : V) (p2 : P) (v2 : V) : P :=
  Classical.epsilon (fun p =>
    p ∈ AffineSubspace.mk' p1 (Submodule.span ℝ {v1}) ∧
    p ∈ AffineSubspace.mk' p2 (Submodule.span ℝ {v2}))

noncomputable def trisectorVector (A B C : P) : V :=
  let angle_val : ℝ := (oangle B A C).toReal / 3
  Orientation.rotation (Module.Oriented.positiveOrientation)
    (angle_val : Real.Angle) (B -ᵥ A)

noncomputable def morleyTriangle (A B C : P) : P × P × P :=
  let R := lineIntersection A (trisectorVector A B C) B (trisectorVector B A C)
  let P := lineIntersection B (trisectorVector B C A) C (trisectorVector C B A)
  let Q := lineIntersection C (trisectorVector C A B) A (trisectorVector A C B)
  (P, Q, R)

def isEquilateral (A B C : P) : Prop :=
  dist A B = dist B C ∧ dist B C = dist C A

def NondegenerateTriangle (A B C : P) : Prop :=
  ¬Collinear ℝ {A, B, C}

theorem morley_triangle_similarity_invariance (f : Similarity P) (A B C : P)
    (h_nd : NondegenerateTriangle A B C) :
    let (P, Q, R) := morleyTriangle A B C
    let (P', Q', R') := morleyTriangle (f A) (f B) (f C)
    P' = f P ∧ Q' = f Q ∧ R' = f R := by
  sorry

theorem morley_theorem (A B C : P) (h_nd : NondegenerateTriangle A B C) :
    let (P_tri, Q_tri, R_tri) := morleyTriangle A B C
    isEquilateral P_tri Q_tri R_tri := by
  sorry

end Theorem84
