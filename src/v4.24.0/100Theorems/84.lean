/-

This is a Lean formalization of

84: Morley’s Theorem

following John Horton Conway's elementary proof.


This was proven by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

-/

/-
Formalization of Morley's Trisector Theorem using Conway's proof. We prove that in any nondegenerate triangle, the Morley triangle is equilateral. The proof proceeds by constructing a reference triangle with the desired angles and an equilateral Morley triangle, then showing it is similar to the original triangle.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0

noncomputable section

/-
For an angle measure $\theta$, define $\theta\plus := \theta + 60\dg$ and $\theta\plusplus := \theta + 120\dg$.
-/
open EuclideanGeometry Real

/-- Angle shift: theta plus 60 degrees. -/
def angleShift (θ : ℝ) : ℝ := θ + π / 3

/-- Angle shift: theta plus 120 degrees. -/
def angleShiftTwo (θ : ℝ) : ℝ := θ + 2 * π / 3

/-
Define the internal trisectors of a triangle and the Morley triangle. The trisectors of angle A are the two rays from A that subdivide angle A into three equal angles. R is the intersection of the trisector of A adjacent to AB with the trisector of B adjacent to BA. P and Q are defined cyclically. The triangle PQR is the Morley triangle.
-/
open EuclideanGeometry Real InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]
variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P] [Nonempty P]

/-- Intersection of two lines defined by points and direction vectors. -/
def lineIntersection (p1 : P) (v1 : V) (p2 : P) (v2 : V) : P :=
  Classical.epsilon (fun p =>
    p ∈ AffineSubspace.mk' p1 (Submodule.span ℝ {v1}) ∧
    p ∈ AffineSubspace.mk' p2 (Submodule.span ℝ {v2}))

/-- The direction vector of the trisector of angle `∠ B A C` adjacent to `AB`. -/
def trisectorVector (A B C : P) : V :=
  let angle_val : ℝ := (oangle B A C).toReal / 3
  Orientation.rotation (Module.Oriented.positiveOrientation) (angle_val : Real.Angle) (B -ᵥ A)

/-- The Morley triangle of a triangle ABC, defined by the vertices P, Q, R. -/
def morleyTriangle (A B C : P) : P × P × P :=
  let R := lineIntersection A (trisectorVector A B C) B (trisectorVector B A C)
  let P := lineIntersection B (trisectorVector B C A) C (trisectorVector C B A)
  let Q := lineIntersection C (trisectorVector C A B) A (trisectorVector A C B)
  (P, Q, R)

/-- A triangle is equilateral if all sides are equal. -/
def isEquilateral (A B C : P) : Prop :=
  dist A B = dist B C ∧ dist B C = dist C A

/-
A similarity is a map that scales distances by a positive factor r.
-/
structure Similarity (P : Type*) [MetricSpace P] where
  toFun : P → P
  r : ℝ
  r_pos : r > 0
  dist_eq : ∀ x y, dist (toFun x) (toFun y) = r * dist x y

instance (P : Type*) [MetricSpace P] : CoeFun (Similarity P) (fun _ => P → P) := ⟨Similarity.toFun⟩

#check Collinear

#check Similarity
#check morleyTriangle
#check isEquilateral

/-
A triangle is nondegenerate if its vertices are not collinear.
-/
def NondegenerateTriangle (A B C : P) : Prop := ¬ Collinear ℝ {A, B, C}

#check Orientation.rotation
#check Module.Oriented.positiveOrientation
#check VAdd.vadd

#check VAdd.vadd

/-
Construct a triangle vertex given a base and angles, using the Law of Sines and rotation.
-/
/-- Given two points P1, P2 and angles, construct the third vertex of a triangle "outside" the segment P1 P2.
    We assume P1, P2 are oriented such that the "outside" is to the right (clockwise).
    So we rotate P1 -> P2 by -angle_at_P1.
    The length is determined by the Law of Sines: side_opp_P2 / sin(angle_at_P1) = side_opp_vertex / sin(angle_at_vertex) = side_P1P2 / sin(angle_opp).
    So side_opp_P2 (distance from P1 to vertex) = side_P1P2 * sin(angle_at_P2) / sin(angle_opp).
-/
def conwaySmallTriangleVertex (P1 P2 : P) (angle_at_P1 angle_at_P2 angle_opp : ℝ) : P :=
  let dist_P1_V := dist P1 P2 * Real.sin angle_at_P2 / Real.sin angle_opp
  let vec := P2 -ᵥ P1
  let rotated_vec := Orientation.rotation (Module.Oriented.positiveOrientation) (-angle_at_P1 : Real.Angle) vec
  (dist_P1_V / ‖vec‖) • rotated_vec +ᵥ P1

/-
The distance from P1 to the constructed vertex is given by the Law of Sines formula.
-/
theorem conwaySmallTriangleVertex_dist_P1 (P1 P2 : P) (a1 a2 ao : ℝ)
  (h_pos : dist P1 P2 > 0)
  (h_sin_ao : Real.sin ao > 0)
  (h_sin_a2 : Real.sin a2 > 0) :
  dist P1 (conwaySmallTriangleVertex P1 P2 a1 a2 ao) = dist P1 P2 * Real.sin a2 / Real.sin ao := by
    -- By definition of `conwaySmallTriangleVertex`, we can write the vector from P1 to the vertex as a scalar multiple of the rotated vector.
    have h_vector : (conwaySmallTriangleVertex P1 P2 a1 a2 ao -ᵥ P1) = (dist P1 P2 * Real.sin a2 / Real.sin ao / ‖P2 -ᵥ P1‖) • (Orientation.rotation (Module.Oriented.positiveOrientation) (-a1 : Real.Angle) (P2 -ᵥ P1)) := by
      exact?;
    -- Since rotation is a linear isometry, the norm of the rotated vector is the same as the norm of the original vector.
    have h_norm : ‖(Orientation.rotation (Module.Oriented.positiveOrientation) (-a1 : Real.Angle) (P2 -ᵥ P1))‖ = ‖P2 -ᵥ P1‖ := by
      exact LinearIsometry.norm_map _ _;
    rw [ dist_eq_norm_vsub ];
    rw [ ← norm_neg, neg_vsub_eq_vsub_rev, h_vector, norm_smul, Real.norm_of_nonneg ( div_nonneg ( div_nonneg ( mul_nonneg h_pos.le h_sin_a2.le ) h_sin_ao.le ) ( norm_nonneg _ ) ), h_norm, div_mul_cancel₀ ] ; aesop

/-
A trigonometric identity needed for the Law of Cosines application in Conway's proof.
-/
lemma conway_trig_identity (a1 a2 : ℝ) :
  Real.sin (a1 + a2) ^ 2 - 2 * Real.sin a2 * Real.sin (a1 + a2) * Real.cos a1 + Real.sin a2 ^ 2 = Real.sin a1 ^ 2 := by
    rw [ show a1 + a2 = a1 + a2 by ring ] ; norm_num [ Real.sin_add, Real.cos_add, Real.sin_sq ] ; ring;
    simpa only [ Real.sin_sq ] using by ring;

/-
Algebraic identity derived from the trigonometric identity by dividing by $\sin^2 a_o$.
-/
lemma conway_algebraic_identity (a1 a2 ao : ℝ) (h_sin_ao : Real.sin ao ≠ 0) (h_sum : a1 + a2 + ao = π) :
  1 - 2 * (Real.sin a2 / Real.sin ao) * Real.cos a1 + (Real.sin a2 / Real.sin ao) ^ 2 = (Real.sin a1 / Real.sin ao) ^ 2 := by
    field_simp;
    rw [ show a1 = Real.pi - a2 - ao by linarith ] ; repeat norm_num [ Real.sin_sq, Real.sin_sub, Real.cos_sub ] <;> ring;

/-
Helper lemma for the squared distance calculation in Conway's proof.
-/
lemma conway_dist_sq_lemma (v : V) (a1 k : ℝ) :
  ‖-v + k • (Orientation.rotation (Module.Oriented.positiveOrientation) (-a1 : Real.Angle) v)‖^2 = ‖v‖^2 * (1 - 2 * k * Real.cos a1 + k^2) := by
    -- Calculate the squared norm of the vector $-v + k • (positiveOrientation.rotation (-↑a1)) v$.
    have h_norm_sq : ‖-v + k • (positiveOrientation.rotation (-↑a1)) v‖ ^ 2 = ⟪-v + k • (positiveOrientation.rotation (-↑a1)) v, -v + k • (positiveOrientation.rotation (-↑a1)) v⟫_ℝ := by
      rw [ ← real_inner_self_eq_norm_sq ];
    -- Calculate the inner product $\langle v, R_{-a_1} v \rangle$.
    have h_inner : ⟪v, (positiveOrientation.rotation (-↑a1)) v⟫_ℝ = ‖v‖ ^ 2 * Real.cos a1 := by
      have h_inner : ⟪v, (positiveOrientation.rotation (-↑a1)) v⟫_ℝ = ⟪positiveOrientation.rotation a1 v, v⟫_ℝ := by
        rw [Orientation.rotation_apply, Orientation.rotation_apply];
        simp +decide [ inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Real.cos_neg, Real.sin_neg ];
      rw [ h_inner, Orientation.rotation_apply ];
      simp +decide [ inner_add_left, inner_smul_left, inner_self_eq_norm_sq_to_K ] ; ring;
    simp_all +decide [ inner_add_left, inner_add_right, inner_smul_left, inner_smul_right ];
    rw [ real_inner_comm ] ; rw [ h_inner ] ; rw [ real_inner_self_eq_norm_sq ] ; ring;

/-
The distance from P2 to the constructed vertex is given by the Law of Sines formula (with positive sines).
-/
theorem conwaySmallTriangleVertex_dist_P2_pos (P1 P2 : P) (a1 a2 ao : ℝ)
  (h_pos : dist P1 P2 > 0)
  (h_sin_ao_pos : Real.sin ao > 0)
  (h_sin_a1_pos : Real.sin a1 > 0)
  (h_sin_a2_pos : Real.sin a2 > 0)
  (h_sum : a1 + a2 + ao = π) :
  dist P2 (conwaySmallTriangleVertex P1 P2 a1 a2 ao) = dist P1 P2 * Real.sin a1 / Real.sin ao := by
    have h_dist_P2_vertex : dist P2 (conwaySmallTriangleVertex P1 P2 a1 a2 ao) ^ 2 = (dist P1 P2 * Real.sin a1 / Real.sin ao) ^ 2 := by
      have h_dist_P2_vertex : ‖P2 -ᵥ (conwaySmallTriangleVertex P1 P2 a1 a2 ao)‖^2 = ‖P2 -ᵥ P1‖^2 * (1 - 2 * (Real.sin a2 / Real.sin ao) * Real.cos a1 + (Real.sin a2 / Real.sin ao) ^ 2) := by
        unfold conwaySmallTriangleVertex;
        convert conway_dist_sq_lemma ( P2 -ᵥ P1 ) a1 ( ( dist P1 P2 * Real.sin a2 / Real.sin ao ) / ‖P2 -ᵥ P1‖ ) using 1;
        · rw [ ← norm_neg ] ; simp +decide [ neg_vsub_eq_vsub_rev, vadd_vsub_assoc ] ;
          rw [ add_comm ];
        · rw [ dist_eq_norm_vsub' ];
          rw [ mul_div_assoc, mul_div_cancel_left₀ _ ( ne_of_gt ( norm_pos_iff.mpr ( vsub_ne_zero.mpr ( by aesop_cat ) ) ) ) ];
      have h_dist_P2_vertex : 1 - 2 * (Real.sin a2 / Real.sin ao) * Real.cos a1 + (Real.sin a2 / Real.sin ao) ^ 2 = (Real.sin a1 / Real.sin ao) ^ 2 := by
        convert conway_algebraic_identity a1 a2 ao ( ne_of_gt h_sin_ao_pos ) ( by linarith ) using 1;
      simp_all +decide [ dist_eq_norm_vsub ];
      rw [ show P2 -ᵥ P1 = - ( P1 -ᵥ P2 ) by rw [ neg_vsub_eq_vsub_rev ], norm_neg ] ; ring;
    rwa [ sq_eq_sq₀ ( dist_nonneg ) ( div_nonneg ( mul_nonneg h_pos.le h_sin_a1_pos.le ) h_sin_ao_pos.le ) ] at h_dist_P2_vertex

/-
Definitions of the vertices A, B, C in Conway's construction.
-/
def conwayVertexA (Q R : P) (a b c : ℝ) : P :=
  conwaySmallTriangleVertex Q R (angleShift c) (angleShift b) a

def conwayVertexB (R P_pt : P) (a b c : ℝ) : P :=
  conwaySmallTriangleVertex R P_pt (angleShift a) (angleShift c) b

def conwayVertexC (P_pt Q : P) (a b c : ℝ) : P :=
  conwaySmallTriangleVertex P_pt Q (angleShift b) (angleShift a) c

#check Orientation.oangle

/-
Definitions of the side lengths of the "large" triangles in Conway's proof, derived from the Law of Sines.
For example, in the large triangle BPC (Step 2i), we scale so PY=PZ=1.
The side BP is opposite angle BZP = a+. The angle at B is b.
So BP / sin(a+) = PZ / sin(b) = 1 / sin(b).
Thus BP = sin(a+) / sin(b).
Similarly for the others.
-/
def conwayLargeSideBP (a b : ℝ) : ℝ := Real.sin (angleShift a) / Real.sin b
def conwayLargeSideCP (a c : ℝ) : ℝ := Real.sin (angleShift a) / Real.sin c
def conwayLargeSideQA (b a : ℝ) : ℝ := Real.sin (angleShift b) / Real.sin a
def conwayLargeSideQC (b c : ℝ) : ℝ := Real.sin (angleShift b) / Real.sin c
def conwayLargeSideRA (c a : ℝ) : ℝ := Real.sin (angleShift c) / Real.sin a
def conwayLargeSideRB (c b : ℝ) : ℝ := Real.sin (angleShift c) / Real.sin b

/-
Step 3: Matching of shared edges (BP).
The length of the side BP in the small triangle BRP (constructed by `conwayVertexB`) matches the length required by the large triangle BPC.
-/
theorem conway_step3_BP_matches (R P_pt : P) (a b c : ℝ)
  (h_side : dist R P_pt = 1)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_sum : a + b + c = π / 3) :
  dist P_pt (conwayVertexB R P_pt a b c) = conwayLargeSideBP a b := by
    convert conwaySmallTriangleVertex_dist_P2_pos R P_pt ( angleShift a ) ( angleShift c ) b _ _ _ _ _ using 1 <;> norm_num [ h_side, h_a_pos, h_b_pos, h_c_pos, h_sum ];
    · rfl;
    · exact Real.sin_pos_of_pos_of_lt_pi h_b_pos ( by linarith );
    · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith );
    · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith [ Real.pi_pos ] ) ( by unfold angleShift; linarith [ Real.pi_pos ] );
    · unfold angleShift; linarith

/-
Step 3: Matching of shared edges (CP).
The length of the side CP in the small triangle CPQ (constructed by `conwayVertexC`) matches the length required by the large triangle BPC.
-/
theorem conway_step3_CP_matches (P_pt Q : P) (a b c : ℝ)
  (h_side : dist P_pt Q = 1)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_sum : a + b + c = π / 3) :
  dist P_pt (conwayVertexC P_pt Q a b c) = conwayLargeSideCP a c := by
    unfold conwayLargeSideCP conwayVertexC;
    convert conwaySmallTriangleVertex_dist_P1 P_pt Q ( angleShift b ) ( angleShift a ) c _ _ _ using 1;
    · rw [ h_side, one_mul ];
    · linarith;
    · exact Real.sin_pos_of_pos_of_lt_pi h_c_pos ( by linarith );
    · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith )

/-
Step 3: Matching of shared edges (QA).
The length of the side QA in the small triangle AQR (constructed by `conwayVertexA`) matches the length required by the large triangle CQA.
-/
theorem conway_step3_QA_matches (Q R : P) (a b c : ℝ)
  (h_side : dist Q R = 1)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_sum : a + b + c = π / 3) :
  dist Q (conwayVertexA Q R a b c) = conwayLargeSideQA b a := by
    convert conwaySmallTriangleVertex_dist_P1 Q R _ _ _ _ _ _ using 1 <;> norm_num [ h_side ];
    · rfl;
    · exact Real.sin_pos_of_pos_of_lt_pi h_a_pos ( by linarith );
    · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith )

/-
Step 3: Matching of shared edges (QC).
The length of the side QC in the small triangle CPQ (constructed by `conwayVertexC`) matches the length required by the large triangle CQA.
-/
theorem conway_step3_QC_matches (P_pt Q : P) (a b c : ℝ)
  (h_side : dist P_pt Q = 1)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_sum : a + b + c = π / 3) :
  dist Q (conwayVertexC P_pt Q a b c) = conwayLargeSideQC b c := by
    -- Let's simplify the goal using the definitions of `conwaySmallTriangleVertex` and `conwayLargeSideQC`.
    simp [conwayVertexC, conwayLargeSideQC];
    convert conwaySmallTriangleVertex_dist_P2_pos P_pt Q ( angleShift b ) ( angleShift a ) c _ _ _ _ using 1;
    · unfold angleShift; ring_nf; aesop;
      exact Or.inl ( by linarith );
    · linarith;
    · exact Real.sin_pos_of_pos_of_lt_pi h_c_pos ( by linarith );
    · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith );
    · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith )

/-
Step 3: Matching of shared edges (RA).
The length of the side RA in the small triangle AQR (constructed by `conwayVertexA`) matches the length required by the large triangle ARB.
-/
theorem conway_step3_RA_matches (Q R : P) (a b c : ℝ)
  (h_side : dist Q R = 1)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_sum : a + b + c = π / 3) :
  dist R (conwayVertexA Q R a b c) = conwayLargeSideRA c a := by
    convert conwaySmallTriangleVertex_dist_P2_pos Q R ( angleShift c ) ( angleShift b ) a _ _ _ _ _ using 1;
    all_goals norm_num [ angleShift ];
    any_goals linarith [ Real.sin_pos_of_pos_of_lt_pi h_a_pos ( by linarith ), Real.sin_pos_of_pos_of_lt_pi h_b_pos ( by linarith ), Real.sin_pos_of_pos_of_lt_pi h_c_pos ( by linarith ) ];
    · unfold conwayLargeSideRA; rw [ h_side ] ; ring;
      unfold angleShift; ring;
    · aesop;
    · exact Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by linarith );
    · exact Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by linarith [ Real.pi_pos ] )

/-
Step 3: Matching of shared edges (RB).
The length of the side RB in the small triangle BRP (constructed by `conwayVertexB`) matches the length required by the large triangle ARB.
-/
theorem conway_step3_RB_matches (R P_pt : P) (a b c : ℝ)
  (h_side : dist R P_pt = 1)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_sum : a + b + c = π / 3) :
  dist R (conwayVertexB R P_pt a b c) = conwayLargeSideRB c b := by
    convert conwaySmallTriangleVertex_dist_P1 R P_pt _ _ _ _ _ _ using 1;
    · aesop;
    · linarith;
    · exact Real.sin_pos_of_pos_of_lt_pi h_b_pos ( by linarith );
    · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith )

/-
Definitions of the angles of the "large" triangles at the vertices P, Q, R.
For example, the large triangle BPC has angle a++ at P.
a++ is defined as a + 120 degrees.
-/
def conwayLargeAngleP (a : ℝ) : ℝ := angleShiftTwo a
def conwayLargeAngleQ (b : ℝ) : ℝ := angleShiftTwo b
def conwayLargeAngleR (c : ℝ) : ℝ := angleShiftTwo c

/-
Step 4: The pieces fill the gaps at P.
We prove that the sum of the angles around the internal vertex P is exactly $2\pi$ (360 degrees), ensuring that the triangles fit together in the plane.
-/
theorem conway_angle_sum_at_P (a b c : ℝ) (h_sum : a + b + c = π / 3) :
  π / 3 + angleShift c + angleShift b + conwayLargeAngleP a = 2 * π := by
    unfold angleShift conwayLargeAngleP; ring;
    unfold angleShiftTwo; linarith;

/-
Step 4: The pieces fill the gaps at Q.
We prove that the sum of the angles around the internal vertex Q is exactly $2\pi$ (360 degrees), ensuring that the triangles fit together in the plane.
-/
theorem conway_angle_sum_at_Q (a b c : ℝ) (h_sum : a + b + c = π / 3) :
  π / 3 + angleShift a + angleShift c + conwayLargeAngleQ b = 2 * π := by
    -- Substitute the definitions of angleShift and conwayLargeAngleQ.
    simp [angleShift, conwayLargeAngleQ];
    unfold angleShiftTwo; linarith;

/-
Step 4: The pieces fill the gaps at R.
We prove that the sum of the angles around the internal vertex R is exactly $2\pi$ (360 degrees), ensuring that the triangles fit together in the plane.
-/
theorem conway_angle_sum_at_R (a b c : ℝ) (h_sum : a + b + c = π / 3) :
  π / 3 + angleShift b + angleShift a + conwayLargeAngleR c = 2 * π := by
    unfold angleShift conwayLargeAngleR;
    unfold angleShiftTwo; linarith;

#check angle

/-
Helper lemma: Uniqueness of triangle angles given two sides and the included angle (SAS for angles).
If the ratio of two sides matches the ratio of sines of two proposed angles that sum to the correct amount, then those are indeed the angles of the triangle.
-/
lemma unique_angles_of_sides_ratio (A B C : P) (gamma beta delta : ℝ)
  (h_angle_A : angle B A C = gamma)
  (h_sum : beta + delta + gamma = π)
  (h_pos_beta : 0 < beta) (h_lt_beta : beta < π)
  (h_pos_delta : 0 < delta) (h_lt_delta : delta < π)
  (h_pos_gamma : 0 < gamma) (h_lt_gamma : gamma < π)
  (h_ratio : dist A C / dist A B = Real.sin beta / Real.sin delta) :
  angle A B C = beta ∧ angle A C B = delta := by
    -- By the Law of Sines, we know that in any triangle, the ratio of the lengths of two sides is equal to the ratio of the sines of the angles opposite those sides.
    have h_law_of_sines : Real.sin (EuclideanGeometry.angle A B C) / Real.sin (EuclideanGeometry.angle A C B) = dist A C / dist A B := by
      rw [ div_eq_div_iff ];
      · have h_law_of_sines : dist A C ^ 2 = dist A B ^ 2 + dist B C ^ 2 - 2 * dist A B * dist B C * Real.cos (EuclideanGeometry.angle A B C) ∧ dist A B ^ 2 = dist A C ^ 2 + dist B C ^ 2 - 2 * dist A C * dist B C * Real.cos (EuclideanGeometry.angle A C B) := by
          constructor <;> rw [ EuclideanGeometry.angle, dist_eq_norm_vsub, dist_eq_norm_vsub, dist_eq_norm_vsub ];
          · rw [ show A -ᵥ C = ( A -ᵥ B ) + ( B -ᵥ C ) by rw [ vsub_add_vsub_cancel ], norm_add_sq_real ];
            rw [ InnerProductGeometry.cos_angle ];
            by_cases h : ‖A -ᵥ B‖ = 0 <;> by_cases h' : ‖C -ᵥ B‖ = 0 <;> simp_all +decide [ mul_assoc, mul_div_cancel₀ ];
            simp ( config := { decide := Bool.true } ) [ mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, norm_sub_rev, h, h' ];
            rw [ show C -ᵥ B = - ( B -ᵥ C ) by rw [ neg_vsub_eq_vsub_rev ], inner_neg_right ] ; ring;
            simp ( config := { decide := Bool.true } ) [ norm_neg, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( norm_pos_iff.mpr ( vsub_ne_zero.mpr h' ) ) ];
            rw [ ← norm_neg, neg_vsub_eq_vsub_rev, mul_inv_cancel₀ ( norm_ne_zero_iff.mpr ( vsub_ne_zero.mpr h' ) ), mul_one ];
          · rw [ show A -ᵥ B = ( A -ᵥ C ) - ( B -ᵥ C ) by simp ( config := { decide := Bool.true } ) [ sub_eq_add_neg, add_comm, add_left_comm, add_assoc ], @norm_sub_sq ℝ ];
            rw [ InnerProductGeometry.cos_angle ];
            by_cases h : ‖A -ᵥ C‖ = 0 <;> by_cases h' : ‖B -ᵥ C‖ = 0 <;> simp_all ( config := { decide := Bool.true } ) [ mul_assoc, mul_div_cancel₀ ] ; ring;
        have h_sin_eq : Real.sin (EuclideanGeometry.angle A B C) ^ 2 * dist A B ^ 2 = Real.sin (EuclideanGeometry.angle A C B) ^ 2 * dist A C ^ 2 := by
          rw [ Real.sin_sq, Real.sin_sq ] ; ring_nf at *;
          have h_cos_eq : Real.cos (EuclideanGeometry.angle A B C) = (dist A B ^ 2 + dist B C ^ 2 - dist A C ^ 2) / (2 * dist A B * dist B C) ∧ Real.cos (EuclideanGeometry.angle A C B) = (dist A C ^ 2 + dist B C ^ 2 - dist A B ^ 2) / (2 * dist A C * dist B C) := by
            constructor <;> rw [ eq_div_iff ] <;> first | linarith | intro h ; simp_all +singlePass ;
            · rcases h with ( rfl | rfl ) <;> norm_num at *;
              · exact absurd ( h_ratio.resolve_left ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi h_pos_beta h_lt_beta ) ) ) ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi h_pos_delta h_lt_delta ) );
              · rw [ EuclideanGeometry.angle ] at h_angle_A ; aesop;
                rw [ InnerProductGeometry.angle_self ] at h_pos_gamma ; linarith;
                aesop;
                · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi h_pos_beta h_lt_beta ) h;
                · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi h_pos_delta h_lt_delta ) h_1;
            · rcases h with ( rfl | rfl ) <;> norm_num at *;
              · exact absurd ( h_ratio.resolve_left ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi h_pos_beta h_lt_beta ) ) ) ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi h_pos_delta h_lt_delta ) );
              · rw [ EuclideanGeometry.angle ] at h_angle_A ; aesop;
                rw [ InnerProductGeometry.angle_self ] at h_pos_gamma ; linarith;
                aesop;
                · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi h_pos_beta h_lt_beta ) h;
                · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi h_pos_delta h_lt_delta ) h_1;
          grind;
        field_simp;
        rw [ ← sq_eq_sq₀ ];
        · linarith;
        · exact mul_nonneg ( Real.sin_nonneg_of_nonneg_of_le_pi ( EuclideanGeometry.angle_nonneg _ _ _ ) ( EuclideanGeometry.angle_le_pi _ _ _ ) ) ( dist_nonneg );
        · exact mul_nonneg ( dist_nonneg ) ( Real.sin_nonneg_of_nonneg_of_le_pi ( EuclideanGeometry.angle_nonneg _ _ _ ) ( EuclideanGeometry.angle_le_pi _ _ _ ) );
      · simp +decide [ EuclideanGeometry.angle ];
        rw [ Real.sin_eq_zero_iff_of_lt_of_lt ] <;> try linarith [ InnerProductGeometry.angle_nonneg ( A -ᵥ C ) ( B -ᵥ C ), InnerProductGeometry.angle_le_pi ( A -ᵥ C ) ( B -ᵥ C ) ];
        · rw [ InnerProductGeometry.angle_eq_zero_iff ];
          rintro ⟨ h, r, hr, h' ⟩;
          simp_all +decide [ dist_eq_norm, vsub_eq_sub ];
          rw [ EuclideanGeometry.angle ] at h_angle_A;
          rw [ show B -ᵥ A = r • ( A -ᵥ C ) + ( C -ᵥ A ) by rw [ ← h', vsub_add_vsub_cancel ] ] at h_angle_A;
          rw [ show r • ( A -ᵥ C ) + ( C -ᵥ A ) = ( r - 1 ) • ( A -ᵥ C ) by
                simp +decide [ sub_smul, vsub_eq_sub ];
                rw [ sub_eq_add_neg, neg_vsub_eq_vsub_rev ] ] at h_angle_A;
          rw [ InnerProductGeometry.angle_smul_left_of_pos ] at h_angle_A;
          · rw [ show C -ᵥ A = - ( A -ᵥ C ) by rw [ neg_vsub_eq_vsub_rev ], InnerProductGeometry.angle_neg_right ] at h_angle_A ; aesop;
          · contrapose! h_angle_A;
            rw [ InnerProductGeometry.angle_smul_left_of_neg ] <;> norm_num;
            · rw [ InnerProductGeometry.angle_self ] ; linarith;
              exact vsub_ne_zero.mpr ( Ne.symm h );
            · cases lt_or_eq_of_le h_angle_A <;> simp_all +decide [ sub_eq_iff_eq_add ];
              exact absurd h_ratio ( ne_of_lt ( div_pos ( Real.sin_pos_of_pos_of_lt_pi ( by linarith ) ( by linarith ) ) ( Real.sin_pos_of_pos_of_lt_pi ( by linarith ) ( by linarith ) ) ) );
        · refine' lt_of_le_of_ne ( InnerProductGeometry.angle_le_pi _ _ ) _;
          rw [ Ne.eq_def, InnerProductGeometry.angle_eq_pi_iff ];
          rintro ⟨ h₁, r, hr, h₂ ⟩;
          simp_all +decide [ EuclideanGeometry.angle, sub_eq_iff_eq_add ];
          rw [ show B -ᵥ A = ( r - 1 ) • ( A -ᵥ C ) by rw [ sub_smul, one_smul, ← h₂ ] ; simp +decide [ sub_smul, vsub_sub_vsub_cancel_right ] ] at h_angle_A;
          rw [ InnerProductGeometry.angle_smul_left_of_neg ] at h_angle_A <;> aesop;
          · rw [ InnerProductGeometry.angle_self ] at h_pos_gamma ; linarith;
            aesop;
          · linarith;
      · aesop;
        exact absurd h_ratio ( ne_of_lt ( div_pos ( Real.sin_pos_of_pos_of_lt_pi ( by linarith ) ( by linarith ) ) ( Real.sin_pos_of_pos_of_lt_pi ( by linarith ) ( by linarith ) ) ) );
    -- Since $\angle A B C + \angle A C B + \angle B A C = \pi$, we have $\angle A B C + \angle A C B = \pi - \gamma$.
    have h_sum_angles : EuclideanGeometry.angle A B C + EuclideanGeometry.angle A C B = Real.pi - gamma := by
      have h_sum_angles : EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A + EuclideanGeometry.angle C A B = Real.pi := by
        apply EuclideanGeometry.angle_add_angle_add_angle_eq_pi;
        aesop;
        exact absurd h_ratio ( ne_of_lt ( div_pos ( Real.sin_pos_of_pos_of_lt_pi ( by linarith ) ( by linarith ) ) ( Real.sin_pos_of_pos_of_lt_pi ( by linarith ) ( by linarith ) ) ) );
      rw [ ← h_angle_A, ← h_sum_angles ] ; ring!;
      simp +decide [ EuclideanGeometry.angle_comm ];
    -- Since $\angle A B C + \angle A C B = \pi - \gamma$, we have $\angle A B C = \beta$ and $\angle A C B = \delta$.
    have h_angle_eq : EuclideanGeometry.angle A B C = beta := by
      have h_sin_eq : Real.sin (EuclideanGeometry.angle A B C) * Real.sin (Real.pi - gamma - beta) = Real.sin beta * Real.sin (Real.pi - gamma - EuclideanGeometry.angle A B C) := by
        rw [ div_eq_iff ] at h_law_of_sines <;> aesop;
        · rw [ show Real.pi - ∠ B A C - beta = delta by linarith, show Real.pi - ∠ B A C - ∠ A B C = ∠ A C B by linarith ] ; ring;
          rw [ mul_inv_cancel_right₀ ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi h_pos_delta h_lt_delta ) ) ];
        · linarith [ Real.sin_pos_of_pos_of_lt_pi ( show 0 < beta by linarith [ Real.sin_pos_of_pos_of_lt_pi ( show 0 < delta by linarith ) h_lt_delta ] ) h_lt_beta, Real.sin_pos_of_pos_of_lt_pi ( show 0 < delta by linarith [ Real.sin_pos_of_pos_of_lt_pi ( show 0 < beta by linarith [ Real.sin_pos_of_pos_of_lt_pi ( show 0 < delta by linarith ) h_lt_delta ] ) h_lt_beta ] ) h_lt_delta, div_pos ( Real.sin_pos_of_pos_of_lt_pi ( show 0 < beta by linarith [ Real.sin_pos_of_pos_of_lt_pi ( show 0 < delta by linarith ) h_lt_delta ] ) h_lt_beta ) ( Real.sin_pos_of_pos_of_lt_pi ( show 0 < delta by linarith [ Real.sin_pos_of_pos_of_lt_pi ( show 0 < beta by linarith [ Real.sin_pos_of_pos_of_lt_pi ( show 0 < delta by linarith ) h_lt_delta ] ) h_lt_beta ] ) h_lt_delta ) ];
      have h_sin_eq : Real.sin (EuclideanGeometry.angle A B C - beta) = 0 := by
        simp_all +decide [ Real.sin_sub, Real.sin_add, Real.cos_sub, Real.cos_add ];
        nlinarith [ Real.sin_pos_of_pos_of_lt_pi h_pos_gamma h_lt_gamma ];
      rw [ Real.sin_eq_zero_iff_of_lt_of_lt ] at h_sin_eq <;> linarith [ Real.pi_pos, EuclideanGeometry.angle_nonneg A B C, EuclideanGeometry.angle_le_pi A B C, EuclideanGeometry.angle_nonneg A C B, EuclideanGeometry.angle_le_pi A C B ];
    exact ⟨ h_angle_eq, by linarith ⟩

/-
Step 5a: Angle properties of the large triangle at P.
Using the helper lemma `unique_angles_of_sides_ratio`, we prove that the angles of the large triangle at P are indeed `b` and `c`.
-/
theorem conway_large_triangle_P_angles (B C P_pt : P) (a b c : ℝ)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_sum : a + b + c = π / 3)
  (h_PB : dist P_pt B = conwayLargeSideBP a b)
  (h_PC : dist P_pt C = conwayLargeSideCP a c)
  (h_angle : angle B P_pt C = conwayLargeAngleP a) :
  angle P_pt B C = b ∧ angle P_pt C B = c := by
    -- We apply the helper lemma `unique_angles_of_sides_ratio` with `gamma = conwayLargeAngleP a`, `beta = b`, and `delta = c`.
    have h_apply_hyperbola : (dist P_pt C / dist P_pt B) = Real.sin b / Real.sin c := by
      rw [ h_PB, h_PC, conwayLargeSideBP, conwayLargeSideCP, div_eq_div_iff ] <;> ring <;> norm_num [ ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi h_a_pos ( by linarith ) ), ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi h_b_pos ( by linarith ) ), ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi h_c_pos ( by linarith ) ) ];
      exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith ) );
    apply unique_angles_of_sides_ratio P_pt B C ( conwayLargeAngleP a ) b c;
    all_goals unfold conwayLargeAngleP at *; try linarith [ Real.pi_pos ];
    · unfold angleShiftTwo; linarith;
    · exact add_pos h_a_pos ( by positivity );
    · unfold angleShiftTwo; linarith [ Real.pi_pos ]

/-
Step 5a: Angle properties of the large triangle at Q.
Using the helper lemma `unique_angles_of_sides_ratio`, we prove that the angles of the large triangle at Q are indeed `c` and `a`.
-/
theorem conway_large_triangle_Q_angles (C A Q : P) (a b c : ℝ)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_sum : a + b + c = π / 3)
  (h_QC : dist Q C = conwayLargeSideQC b c)
  (h_QA : dist Q A = conwayLargeSideQA b a)
  (h_angle : angle C Q A = conwayLargeAngleQ b) :
  angle Q C A = c ∧ angle Q A C = a := by
    apply_rules [ unique_angles_of_sides_ratio, Or.inl ];
    any_goals linarith [ Real.pi_pos, angleShiftTwo b ];
    · unfold conwayLargeAngleQ;
      unfold angleShiftTwo; linarith;
    · exact add_pos h_b_pos ( by positivity );
    · exact show angleShiftTwo b < Real.pi from by unfold angleShiftTwo; linarith [ Real.pi_pos ] ;
    · unfold conwayLargeSideQC conwayLargeSideQA at *;
      rw [ h_QA, h_QC, div_div_div_comm ];
      rw [ div_self ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith ) ) ), one_div_div ]

/-
Step 5a: Angle properties of the large triangle at R.
Using the helper lemma `unique_angles_of_sides_ratio`, we prove that the angles of the large triangle at R are indeed `a` and `b`.
-/
theorem conway_large_triangle_R_angles (A B R : P) (a b c : ℝ)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_sum : a + b + c = π / 3)
  (h_RA : dist R A = conwayLargeSideRA c a)
  (h_RB : dist R B = conwayLargeSideRB c b)
  (h_angle : angle A R B = conwayLargeAngleR c) :
  angle R A B = a ∧ angle R B A = b := by
    apply unique_angles_of_sides_ratio;
    all_goals norm_num [ h_angle, conwayLargeAngleR, angleShiftTwo ];
    any_goals exact c + 2 * Real.pi / 3;
    any_goals linarith [ Real.pi_pos ];
    aesop;
    unfold conwayLargeSideRB conwayLargeSideRA;
    rw [ div_div_div_comm, div_self ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith ) ) ) ];
    rw [ one_div_div ]

/-
Placeholder to reset thought process.
-/
theorem conway_gap_angle_P (B C P_pt : P) (a b c : ℝ)
  (h_sum : a + b + c = π / 3)
  (h_B : B = conwayVertexB (conwayVertexA (conwayVertexC P_pt B a b c) P_pt a b c) P_pt a b c) -- This is circular and wrong.
  : True := by
    trivial

/-
Step 5a: Angle properties of the large triangle at P.
Using the helper lemma `unique_angles_of_sides_ratio`, we prove that the angles of the large triangle at P are indeed `b` and `c`.
-/
theorem conway_large_triangle_P_angles_proof (B C P_pt : P) (a b c : ℝ)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_sum : a + b + c = π / 3)
  (h_PB : dist P_pt B = conwayLargeSideBP a b)
  (h_PC : dist P_pt C = conwayLargeSideCP a c)
  (h_angle : angle B P_pt C = conwayLargeAngleP a) :
  angle P_pt B C = b ∧ angle P_pt C B = c := by
    convert conway_large_triangle_P_angles B C P_pt a b c h_a_pos h_b_pos h_c_pos h_sum _ _ _ using 2;
    · exact h_PB;
    · exact h_PC;
    · exact h_angle

/-
Step 5a: Angle properties of the large triangle at Q.
Using the helper lemma `unique_angles_of_sides_ratio`, we prove that the angles of the large triangle at Q are indeed `c` and `a`.
-/
theorem conway_large_triangle_Q_angles_proof (C A Q : P) (a b c : ℝ)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_sum : a + b + c = π / 3)
  (h_QC : dist Q C = conwayLargeSideQC b c)
  (h_QA : dist Q A = conwayLargeSideQA b a)
  (h_angle : angle C Q A = conwayLargeAngleQ b) :
  angle Q C A = c ∧ angle Q A C = a := by
    exact?

#check InnerProductGeometry.angle

/-
Lemma: The unoriented angle between a vector and its rotation by $\theta$ is $|\theta|$, provided $|\theta| \le \pi$.
-/
lemma angle_rotation_eq_abs (v : V) (theta : ℝ) (h_v : v ≠ 0) (h_theta_abs : |theta| ≤ π) :
  InnerProductGeometry.angle v ((Orientation.rotation Module.Oriented.positiveOrientation (theta : Real.Angle)) v) = |theta| := by
    rw [ InnerProductGeometry.angle, ];
    -- By definition of rotation, we know that $\langle v, R_\theta v \rangle = \|v\|^2 \cos(\theta)$.
    have h_inner : ⟪v, (positiveOrientation.rotation theta) v⟫_ℝ = ‖v‖^2 * Real.cos theta := by
      rw [ sq, ← real_inner_self_eq_norm_mul_norm ];
      rw [ @Orientation.rotation ];
      simp +decide [ mul_comm, inner_smul_left, inner_smul_right ];
      rw [ inner_add_right, inner_smul_right, inner_smul_right ] ; ring;
      simp +decide [ real_inner_comm, real_inner_self_eq_norm_sq ];
    -- By definition of rotation, we know that $\|R_\theta v\| = \|v\|$.
    have h_norm : ‖(positiveOrientation.rotation theta) v‖ = ‖v‖ := by
      exact?;
    rw [ h_inner, h_norm, sq, mul_div_mul_comm ];
    rw [ mul_div_cancel_left₀ _ ( norm_ne_zero_iff.mpr h_v ), mul_div_cancel₀ _ ( norm_ne_zero_iff.mpr h_v ) ];
    rw [ ← Real.cos_abs, Real.arccos_cos ] <;> cases abs_cases theta <;> linarith [ Real.pi_pos ]

#check Module.Oriented.positiveOrientation
#check Orientation.rotation

/-
Lemma: The angle between a vector and a positive scalar multiple of its rotation is the absolute value of the rotation angle.
-/
lemma angle_smul_rotation (v : V) (theta k : ℝ) (h_v : v ≠ 0) (h_k_pos : k > 0) (h_theta_abs : |theta| ≤ π) :
  InnerProductGeometry.angle v (k • (Orientation.rotation Module.Oriented.positiveOrientation (theta : Real.Angle)) v) = |theta| := by
    -- Apply the lemma that the angle between a vector and its rotation is the absolute value of the rotation angle.
    have := angle_rotation_eq_abs v theta h_v h_theta_abs;
    rw [ InnerProductGeometry.angle_smul_right_of_pos ] <;> simp_all +decide [ h_k_pos.ne' ]

/-
Lemma: The scaling factor used in `conwaySmallTriangleVertex` is positive.
-/
lemma conwaySmallTriangle_scale_pos (P1 P2 : P) (a1 a2 ao : ℝ)
  (h_pos : dist P1 P2 > 0)
  (h_sin_ao : Real.sin ao > 0)
  (h_sin_a2 : Real.sin a2 > 0) :
  (dist P1 P2 * Real.sin a2 / Real.sin ao) / ‖P2 -ᵥ P1‖ > 0 := by
    -- Since the denominator ‖P2 -ᵥ P1‖ is positive, the entire expression is positive.
    have h_denom_pos : ‖P2 -ᵥ P1‖ > 0 := by
      rwa [ dist_eq_norm_vsub' ] at h_pos;
    positivity

/-
The vector from P1 to the constructed vertex is a scaled rotation of the vector from P1 to P2.
-/
lemma conwaySmallTriangleVertex_vector_eq (P1 P2 : P) (a1 a2 ao : ℝ) :
  (conwaySmallTriangleVertex P1 P2 a1 a2 ao) -ᵥ P1 =
  (dist P1 P2 * Real.sin a2 / Real.sin ao / ‖P2 -ᵥ P1‖) •
  (Orientation.rotation (Module.Oriented.positiveOrientation) (-a1 : Real.Angle) (P2 -ᵥ P1)) := by
    exact?

/-
The angle at P1 in the constructed small triangle is a1, given bounds on a1.
-/
lemma conwaySmallTriangleVertex_angle_P1_eq (P1 P2 : P) (a1 a2 ao : ℝ)
  (h_pos : dist P1 P2 > 0)
  (h_sin_ao_pos : Real.sin ao > 0)
  (h_sin_a2_pos : Real.sin a2 > 0)
  (h_a1_bound : 0 < a1 ∧ a1 < π) :
  angle P2 P1 (conwaySmallTriangleVertex P1 P2 a1 a2 ao) = a1 := by
    have h_angle : InnerProductGeometry.angle (P2 -ᵥ P1) ((conwaySmallTriangleVertex P1 P2 a1 a2 ao) -ᵥ P1) = a1 := by
      rw [ conwaySmallTriangleVertex_vector_eq, InnerProductGeometry.angle_smul_right_of_pos ];
      · convert angle_rotation_eq_abs ( P2 -ᵥ P1 ) ( -a1 ) _ _ using 1 <;> aesop;
        · rw [ abs_of_pos left ];
        · rw [ abs_of_pos ] <;> linarith;
      · aesop;
    exact?

/-
The angle at P2 in the constructed small triangle is a2.
-/
lemma conwaySmallTriangleVertex_angle_P2_eq (P1 P2 : P) (a1 a2 ao : ℝ)
  (h_pos : dist P1 P2 > 0)
  (h_sin_ao_pos : Real.sin ao > 0)
  (h_sin_a1_pos : Real.sin a1 > 0)
  (h_sin_a2_pos : Real.sin a2 > 0)
  (h_sum : a1 + a2 + ao = π)
  (h_a1_bound : 0 < a1 ∧ a1 < π)
  (h_a2_bound : 0 < a2 ∧ a2 < π) :
  angle P1 P2 (conwaySmallTriangleVertex P1 P2 a1 a2 ao) = a2 := by
    have := @unique_angles_of_sides_ratio;
    specialize this P1 P2 ( conwaySmallTriangleVertex P1 P2 a1 a2 ao ) a1 a2 ao;
    aesop;
    have h_angle_P1 : ∠ P2 P1 (conwaySmallTriangleVertex P1 P2 a1 a2 ao) = a1 := by
      apply conwaySmallTriangleVertex_angle_P1_eq;
      · exact dist_pos.mpr h_pos;
      · exact h_sin_ao_pos;
      · exact h_sin_a2_pos;
      · exact ⟨ left, right ⟩;
    apply (this h_angle_P1 (by linarith) (by
    contrapose! h_sin_ao_pos;
    rw [ ← Real.cos_pi_div_two_sub ] ; exact Real.cos_nonpos_of_pi_div_two_le_of_le ( by linarith ) ( by linarith )) (by
    linarith) (by
    rw [ conwaySmallTriangleVertex_dist_P1 ];
    · rw [ div_eq_iff ( dist_ne_zero.mpr h_pos ) ] ; ring;
    · exact dist_pos.mpr h_pos;
    · exact h_sin_ao_pos;
    · exact h_sin_a2_pos)).left

/-
The angle at the constructed vertex in the small triangle is ao.
-/
lemma conwaySmallTriangleVertex_angle_V_eq (P1 P2 : P) (a1 a2 ao : ℝ)
  (h_pos : dist P1 P2 > 0)
  (h_sin_ao_pos : Real.sin ao > 0)
  (h_sin_a1_pos : Real.sin a1 > 0)
  (h_sin_a2_pos : Real.sin a2 > 0)
  (h_sum : a1 + a2 + ao = π)
  (h_a1_bound : 0 < a1 ∧ a1 < π)
  (h_a2_bound : 0 < a2 ∧ a2 < π) :
  angle P1 (conwaySmallTriangleVertex P1 P2 a1 a2 ao) P2 = ao := by
    -- The angle at the constructed vertex in the small triangle is ao, given bounds on ao.
    have h_angle_sum : angle P1 P2 (conwaySmallTriangleVertex P1 P2 a1 a2 ao) + angle P2 P1 (conwaySmallTriangleVertex P1 P2 a1 a2 ao) + angle P1 (conwaySmallTriangleVertex P1 P2 a1 a2 ao) P2 = Real.pi := by
      rw [ add_assoc, EuclideanGeometry.angle_comm P2 P1 ];
      rw [ EuclideanGeometry.angle_comm _ P2, EuclideanGeometry.angle_comm _ P1 ];
      rw [ add_comm, EuclideanGeometry.angle_add_angle_add_angle_eq_pi ];
      aesop;
    linarith [ conwaySmallTriangleVertex_angle_P1_eq P1 P2 a1 a2 ao h_pos h_sin_ao_pos h_sin_a2_pos h_a1_bound, conwaySmallTriangleVertex_angle_P2_eq P1 P2 a1 a2 ao h_pos h_sin_ao_pos h_sin_a1_pos h_sin_a2_pos h_sum h_a1_bound h_a2_bound ]

/-
The three triangles meeting at vertex B each contribute an angle b.
-/
theorem conway_angles_at_B (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π) (h_b_lt : b < π) (h_c_lt : c < π)
  (h_gap_P : angle (conwayVertexB R P_pt a b c) P_pt (conwayVertexC P_pt Q a b c) = conwayLargeAngleP a)
  (h_gap_R : angle (conwayVertexA Q R a b c) R (conwayVertexB R P_pt a b c) = conwayLargeAngleR c) :
  let A := conwayVertexA Q R a b c
  let B := conwayVertexB R P_pt a b c
  let C := conwayVertexC P_pt Q a b c
  angle A B R = b ∧ angle R B P_pt = b ∧ angle P_pt B C = b := by
    have := conway_gap_angle_P P_pt Q R a b c h_sum ; aesop;
    · have h_large_R_angles : angle R A B = a ∧ angle R B A = b := by
        apply conway_large_triangle_R_angles;
        any_goals assumption;
        · apply conway_step3_RA_matches;
          · rw [ ← h_side, h_equilateral.2 ];
            rw [ h_equilateral.1, h_equilateral.2 ];
          · exact h_a_pos;
          · exact h_b_pos;
          · exact?;
          · exact h_sum;
        · apply conway_step3_RB_matches;
          · bound;
            rw [ ← h_equilateral.2, dist_comm ];
            rw [ ← h_side, h_equilateral.1 ];
            exact dist_comm _ _;
          · exact h_a_pos;
          · exact h_b_pos;
          · exact?;
          · exact h_sum;
      rw [ EuclideanGeometry.angle_comm ] ; aesop;
    · -- Apply the lemma that states the angle at the constructed vertex in the small triangle is `ao`.
      have := conwaySmallTriangleVertex_angle_V_eq R P_pt (angleShift a) (angleShift c) b; aesop;
      unfold angleShift at *;
      contrapose! this;
      refine' ⟨ _, Real.sin_pos_of_pos_of_lt_pi h_b_pos h_b_lt, Real.sin_pos_of_pos_of_lt_pi ( by linarith ) ( by linarith ), Real.sin_pos_of_pos_of_lt_pi ( by linarith ) ( by linarith ), _, _, _, _ ⟩ <;> try linarith;
      · rintro rfl; simp_all ( config := { decide := Bool.true } ) [ isEquilateral ];
        aesop;
      · exact ⟨ by linarith, by linarith, by simpa only [ conwayVertexB ] using this ⟩;
    · have := conway_large_triangle_P_angles (conwayVertexB R P_pt a b c) (conwayVertexC P_pt Q a b c) P_pt a b c h_a_pos h_b_pos h_c_pos h_sum; aesop;
      have := conway_step3_BP_matches R P_pt a b c; have := conway_step3_CP_matches P_pt Q a b c; aesop;
      have := h_equilateral.1; have := h_equilateral.2; aesop;

/-
Definitions of the vertices of the constructed triangle ABC.
-/
def conwayConstructedVertexA (P_pt Q R : P) (a b c : ℝ) : P := conwayVertexA Q R a b c
def conwayConstructedVertexB (P_pt Q R : P) (a b c : ℝ) : P := conwayVertexB R P_pt a b c
def conwayConstructedVertexC (P_pt Q R : P) (a b c : ℝ) : P := conwayVertexC P_pt Q a b c

/-
The three triangles meeting at vertex C each contribute an angle c.
-/
theorem conway_angles_at_C (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π) (h_b_lt : b < π) (h_c_lt : c < π)
  (h_gap_Q : angle (conwayVertexC P_pt Q a b c) Q (conwayVertexA Q R a b c) = conwayLargeAngleQ b)
  (h_gap_P : angle (conwayVertexB R P_pt a b c) P_pt (conwayVertexC P_pt Q a b c) = conwayLargeAngleP a) :
  let A := conwayVertexA Q R a b c
  let B := conwayVertexB R P_pt a b c
  let C := conwayVertexC P_pt Q a b c
  angle B C P_pt = c ∧ angle P_pt C Q = c ∧ angle Q C A = c := by
    aesop;
    · convert ( conway_large_triangle_P_angles ( conwayVertexB R P_pt a b c ) ( conwayVertexC P_pt Q a b c ) P_pt a b c h_a_pos h_b_pos h_c_pos h_sum ?_ ?_ ?_ ).2 using 1;
      · rw [ EuclideanGeometry.angle_comm ];
      · apply conway_step3_BP_matches;
        · cases h_equilateral ; aesop;
        · exact h_a_pos;
        · exact h_b_pos;
        · exact?;
        · exact?;
      · convert conway_step3_CP_matches P_pt Q a b c h_side h_a_pos h_b_pos h_c_pos h_sum using 1;
      · exact h_gap_P;
    · convert conwaySmallTriangleVertex_angle_V_eq P_pt Q ( angleShift b ) ( angleShift a ) c ?_ ?_ ?_ ?_ ?_ ?_ ?_ using 1;
      any_goals unfold angleShift; constructor <;> linarith;
      · linarith;
      · exact Real.sin_pos_of_pos_of_lt_pi h_c_pos h_c_lt;
      · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith );
      · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith );
      · unfold angleShift; linarith;
    · have := conway_large_triangle_Q_angles C A Q a b c h_a_pos h_b_pos h_c_pos h_sum ?_ ?_ h_gap_Q;
      · exact this.1;
      · convert conway_step3_QC_matches P_pt Q a b c h_side h_a_pos h_b_pos h_c_pos h_sum;
      · convert conway_step3_QA_matches Q R a b c _ h_a_pos h_b_pos h_c_pos h_sum using 1;
        have := h_equilateral.1; aesop;

/-
The three triangles meeting at vertex A each contribute an angle a.
-/
theorem conway_angles_at_A (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π) (h_b_lt : b < π) (h_c_lt : c < π)
  (h_gap_R : angle (conwayVertexA Q R a b c) R (conwayVertexB R P_pt a b c) = conwayLargeAngleR c)
  (h_gap_Q : angle (conwayVertexC P_pt Q a b c) Q (conwayVertexA Q R a b c) = conwayLargeAngleQ b) :
  let A := conwayVertexA Q R a b c
  let B := conwayVertexB R P_pt a b c
  let C := conwayVertexC P_pt Q a b c
  angle C A Q = a ∧ angle Q A R = a ∧ angle R A B = a := by
    simp +zetaDelta at *;
    apply And.intro;
    · rw [ EuclideanGeometry.angle_comm ];
      have h_large_triangle_Q_angles : angle (conwayVertexC P_pt Q a b c) Q (conwayVertexA Q R a b c) = conwayLargeAngleQ b := by
        exact h_gap_Q;
      have := conway_large_triangle_Q_angles (conwayVertexC P_pt Q a b c) (conwayVertexA Q R a b c) Q a b c;
      apply (this h_a_pos h_b_pos h_c_pos h_sum (conway_step3_QC_matches P_pt Q a b c h_side h_a_pos h_b_pos h_c_pos h_sum) (conway_step3_QA_matches Q R a b c (by
      rw [ ← h_side, h_equilateral.1 ]) h_a_pos h_b_pos h_c_pos h_sum) h_large_triangle_Q_angles).right;
    · apply And.intro;
      · apply conwaySmallTriangleVertex_angle_V_eq;
        any_goals unfold angleShift; constructor <;> linarith [ Real.pi_pos ];
        · unfold isEquilateral at h_equilateral; aesop;
        · exact Real.sin_pos_of_pos_of_lt_pi h_a_pos h_a_lt;
        · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith );
        · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith );
        · unfold angleShift; linarith;
      · apply (conway_large_triangle_R_angles (conwayVertexA Q R a b c) (conwayVertexB R P_pt a b c) R a b c h_a_pos h_b_pos h_c_pos h_sum _ _ h_gap_R).left;
        · apply conway_step3_RA_matches;
          · rw [ ← h_side, h_equilateral.1.symm ];
          · exact h_a_pos;
          · exact h_b_pos;
          · exact h_c_pos;
          · exact h_sum;
        · apply conway_step3_RB_matches;
          · cases h_equilateral ; aesop;
          · exact h_a_pos;
          · exact h_b_pos;
          · exact h_c_pos;
          · exact h_sum

/-
The oriented angle at P1 is -a1.
-/
lemma conwaySmallTriangleVertex_oangle_P1_V (P1 P2 : P) (a1 a2 ao : ℝ)
  (h_pos : dist P1 P2 > 0)
  (h_sin_ao_pos : Real.sin ao > 0)
  (h_sin_a2_pos : Real.sin a2 > 0)
  (h_a1_bound : 0 < a1 ∧ a1 < π) :
  Orientation.oangle Module.Oriented.positiveOrientation (P2 -ᵥ P1) ((conwaySmallTriangleVertex P1 P2 a1 a2 ao) -ᵥ P1) = (-a1 : Real.Angle) := by
    rw [ conwaySmallTriangleVertex_vector_eq ];
    erw [ Orientation.oangle_smul_right_of_pos ];
    · erw [ Orientation.oangle_rotation_self_right ];
      aesop;
    · aesop

/-
Definition of 60 degrees as a Real.Angle.
-/
def angle60 : Real.Angle := (Real.pi / 3 : ℝ)

/-
Geometric lemma calculating the oriented angle at the second vertex of a triangle constructed by rotation and scaling.
-/
lemma oangle_of_constructed_triangle_variant (u : V) (a b c : ℝ)
  (h_u : u ≠ 0)
  (h_sum : a + b + c = π)
  (h_pos_a : 0 < a ∧ a < π)
  (h_pos_b : 0 < b ∧ b < π)
  (h_pos_c : 0 < c ∧ c < π)
  (v : V)
  (h_v : v = (Real.sin b / Real.sin c) • Orientation.rotation Module.Oriented.positiveOrientation (-a : Real.Angle) u) :
  Orientation.oangle Module.Oriented.positiveOrientation (-u) (v - u) = (b : Real.Angle) := by
    aesop;
    -- We'll use that $v - u$ is a negative scalar multiple of the rotation of $u$ by $b$.
    have h_v_u : (Real.sin b / Real.sin c) • (Orientation.rotation (Module.Oriented.positiveOrientation) (-a : Real.Angle)) u - u = -(Real.sin a / Real.sin c) • (Orientation.rotation (Module.Oriented.positiveOrientation) b u) := by
      have h_v_u : (Real.sin b / Real.sin c) • (Orientation.rotation (Module.Oriented.positiveOrientation) (-a : Real.Angle)) u - u = -(Real.sin a / Real.sin c) • (Orientation.rotation (Module.Oriented.positiveOrientation) b u) := by
        have h_trig_identity : Real.sin b * Real.cos a - Real.sin c = -Real.sin a * Real.cos b := by
          rw [ show c = Real.pi - a - b by linarith ] ; norm_num [ Real.sin_sub, Real.cos_sub ] ; ring;
        have h_trig_identity : (Real.sin b * Real.cos a / Real.sin c - 1) • u - (Real.sin b * Real.sin a / Real.sin c) • (Orientation.rightAngleRotation (Module.Oriented.positiveOrientation) u) = -(Real.sin a * Real.cos b / Real.sin c) • u - (Real.sin a * Real.sin b / Real.sin c) • (Orientation.rightAngleRotation (Module.Oriented.positiveOrientation) u) := by
          have h_trig_identity : (Real.sin b * Real.cos a / Real.sin c - 1) = -(Real.sin a * Real.cos b / Real.sin c) := by
            rw [ div_sub_one, div_eq_iff ] <;> nlinarith [ Real.sin_pos_of_pos_of_lt_pi left_2 right_2, mul_div_cancel₀ ( Real.sin a * Real.cos b ) ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi left_2 right_2 ) ) ];
          grind;
        convert h_trig_identity using 1 <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Real.sin_neg, Real.cos_neg, Orientation.rotation ] ; abel_nf;
        · simp +decide [ add_smul, smul_smul, mul_comm ] ; abel_nf;
        · simp +decide [ mul_assoc, mul_comm, mul_left_comm, smul_smul ] ; abel_nf;
      exact h_v_u;
    have h_oangle_pos : positiveOrientation.oangle u ((Real.sin a / Real.sin c) • (Orientation.rotation (Module.Oriented.positiveOrientation) b u)) = positiveOrientation.oangle u ((Orientation.rotation (Module.Oriented.positiveOrientation) b u)) := by
      rw [ Orientation.oangle_smul_right_of_pos ];
      exact div_pos ( Real.sin_pos_of_pos_of_lt_pi left right ) ( Real.sin_pos_of_pos_of_lt_pi left_2 right_2 );
    aesop

/-
The angle R P B is equal to c+.
-/
lemma angle_R_P_B_eq (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3) :
  let B := conwayConstructedVertexB P_pt Q R a b c
  angle R P_pt B = angleShift c := by
    aesop;
    apply conwaySmallTriangleVertex_angle_P2_eq;
    all_goals norm_num [ angleShift, angleShiftTwo ] at *;
    any_goals constructor <;> linarith [ Real.pi_pos ];
    · rintro rfl;
      cases h_equilateral ; aesop;
    · exact Real.sin_pos_of_pos_of_lt_pi h_b_pos ( by linarith );
    · exact Real.sin_pos_of_pos_of_lt_pi ( by linarith ) ( by linarith );
    · exact Real.sin_pos_of_pos_of_lt_pi ( by linarith ) ( by linarith );
    · linarith

/-
The angle P R B is equal to a+.
-/
lemma angle_P_R_B_eq (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3) :
  let B := conwayConstructedVertexB P_pt Q R a b c
  angle P_pt R B = angleShift a := by
    unfold isEquilateral at h_equilateral;
    rename_i h;
    norm_num +zetaDelta at *;
    apply_rules [ conwaySmallTriangleVertex_angle_P1_eq ];
    · linarith;
    · exact Real.sin_pos_of_pos_of_lt_pi h_b_pos ( by linarith );
    · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith );
    · exact ⟨ by unfold angleShift; linarith, by unfold angleShift; linarith ⟩

/-
The angle Q P C is equal to b+.
-/
lemma angle_Q_P_C_eq (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3) :
  let C := conwayConstructedVertexC P_pt Q R a b c
  angle Q P_pt C = angleShift b := by
  have h_dist_PQ : dist P_pt Q = 1 := h_side
  apply conwaySmallTriangleVertex_angle_P1_eq
  · rw [h_dist_PQ]; norm_num
  · apply Real.sin_pos_of_pos_of_lt_pi
    · exact h_c_pos
    · linarith
  · apply Real.sin_pos_of_pos_of_lt_pi
    · unfold angleShift; linarith
    · unfold angleShift; linarith
  · constructor
    · unfold angleShift; linarith
    · unfold angleShift; linarith

/-
The angle P Q C is equal to a+.
-/
lemma angle_P_Q_C_eq (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3) :
  let C := conwayConstructedVertexC P_pt Q R a b c
  angle P_pt Q C = angleShift a := by
  have h_dist_PQ : dist P_pt Q = 1 := h_side
  apply conwaySmallTriangleVertex_angle_P2_eq
  · rw [h_dist_PQ]; norm_num
  · apply Real.sin_pos_of_pos_of_lt_pi
    · exact h_c_pos
    · linarith
  · apply Real.sin_pos_of_pos_of_lt_pi
    · unfold angleShift; linarith
    · unfold angleShift; linarith
  · apply Real.sin_pos_of_pos_of_lt_pi
    · unfold angleShift; linarith
    · unfold angleShift; linarith
  · unfold angleShift; linarith
  · constructor
    · unfold angleShift; linarith
    · unfold angleShift; linarith
  · constructor
    · unfold angleShift; linarith
    · unfold angleShift; linarith

/-
The angle R Q A is equal to c+.
-/
lemma angle_R_Q_A_eq (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  angle R Q A = angleShift c := by
    apply conwaySmallTriangleVertex_angle_P1_eq;
    · exact dist_pos.mpr ( by rintro rfl; have := h_equilateral.1; aesop );
    · exact Real.sin_pos_of_pos_of_lt_pi h_a_pos ( by linarith );
    · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith );
    · exact ⟨ by unfold angleShift; linarith, by unfold angleShift; linarith ⟩

/-
The angle Q R A is equal to b+.
-/
lemma angle_Q_R_A_eq (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  angle Q R A = angleShift b := by
    convert ( conwaySmallTriangleVertex_angle_P2_eq Q R ( angleShift c ) ( angleShift b ) a ) _ _ _ _ _ _ _ using 1 <;> norm_num;
    any_goals unfold angleShift; constructor <;> linarith;
    · cases h_equilateral ; aesop;
    · exact Real.sin_pos_of_pos_of_lt_pi h_a_pos ( by linarith );
    · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith );
    · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith );
    · unfold angleShift; linarith

/-
The oriented angle at P2 is a2.
-/
lemma conwaySmallTriangleVertex_oangle_P2_V (P1 P2 : P) (a1 a2 ao : ℝ)
  (h_pos : dist P1 P2 > 0)
  (h_sin_ao_pos : Real.sin ao > 0)
  (h_sin_a1_pos : Real.sin a1 > 0)
  (h_sin_a2_pos : Real.sin a2 > 0)
  (h_sum : a1 + a2 + ao = π)
  (h_a1_bound : 0 < a1 ∧ a1 < π)
  (h_a2_bound : 0 < a2 ∧ a2 < π) :
  Orientation.oangle Module.Oriented.positiveOrientation (P1 -ᵥ P2) ((conwaySmallTriangleVertex P1 P2 a1 a2 ao) -ᵥ P2) = (a2 : Real.Angle) := by
    have h_ao_bound : 0 < ao ∧ ao < Real.pi := by
      constructor <;> contrapose! h_sin_ao_pos;
      · exact Real.sin_nonpos_of_nonnpos_of_neg_pi_le h_sin_ao_pos ( by linarith );
      · linarith [ Real.sin_pos_of_pos_of_lt_pi h_a1_bound.1 h_a1_bound.2, Real.sin_pos_of_pos_of_lt_pi h_a2_bound.1 h_a2_bound.2 ];
    -- Let's set $u = P2 - P1$ and $v = V - P1$.
    set u : V := P2 -ᵥ P1
    set v : V := (conwaySmallTriangleVertex P1 P2 a1 a2 ao) -ᵥ P1;
    have h_oangle : Orientation.oangle Module.Oriented.positiveOrientation (-u) (v - u) = a2 := by
      have h_v_eq : v = (Real.sin a2 / Real.sin ao) • (Orientation.rotation Module.Oriented.positiveOrientation (-a1 : Real.Angle)) u := by
        convert conwaySmallTriangleVertex_vector_eq P1 P2 a1 a2 ao using 1;
        rw [ dist_eq_norm_vsub' ];
        rw [ mul_div_assoc, mul_div_cancel_left₀ _ ( norm_ne_zero_iff.mpr <| by aesop ) ]
      convert oangle_of_constructed_triangle_variant u a1 a2 ao _ _ _ _ _ _ using 1 <;> aesop;
    aesop

/-
The oriented angle at P2 is a2.
-/
lemma conwaySmallTriangleVertex_oangle_P2_V_proven (P1 P2 : P) (a1 a2 ao : ℝ)
  (h_pos : dist P1 P2 > 0)
  (h_sin_ao_pos : Real.sin ao > 0)
  (h_sin_a1_pos : Real.sin a1 > 0)
  (h_sin_a2_pos : Real.sin a2 > 0)
  (h_sum : a1 + a2 + ao = π)
  (h_a1_bound : 0 < a1 ∧ a1 < π)
  (h_a2_bound : 0 < a2 ∧ a2 < π) :
  Orientation.oangle Module.Oriented.positiveOrientation (P1 -ᵥ P2) ((conwaySmallTriangleVertex P1 P2 a1 a2 ao) -ᵥ P2) = (a2 : Real.Angle) := by
    exact?

/-
The oriented angle from PR to PB is c+.
-/
lemma conway_oangle_R_P_B (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3) :
  let B := conwayConstructedVertexB P_pt Q R a b c
  Orientation.oangle Module.Oriented.positiveOrientation (R -ᵥ P_pt) (B -ᵥ P_pt) = (angleShift c : Real.Angle) := by
    unfold conwayConstructedVertexB at *;
    convert conwaySmallTriangleVertex_oangle_P2_V_proven R P_pt ( angleShift a ) ( angleShift c ) b _ _ _ _ _ _ _ using 1;
    any_goals unfold angleShift; constructor <;> linarith;
    · simp_all +decide [ isEquilateral ];
      aesop;
    · exact Real.sin_pos_of_pos_of_lt_pi h_b_pos ( by linarith );
    · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith );
    · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith );
    · unfold angleShift; linarith

/-
The oriented angle from PQ to PC is -b+.
-/
lemma conway_oangle_Q_P_C (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3) :
  let C := conwayConstructedVertexC P_pt Q R a b c
  Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (C -ᵥ P_pt) = - (angleShift b : Real.Angle) := by
    apply conwaySmallTriangleVertex_oangle_P1_V;
    · linarith;
    · exact Real.sin_pos_of_pos_of_lt_pi h_c_pos ( by linarith );
    · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith );
    · exact ⟨ by unfold angleShift; linarith, by unfold angleShift; linarith ⟩

/-
Arithmetic identity for angles involved in Conway's proof.
-/
lemma conway_angle_arithmetic_P (a b c : ℝ) (h_sum : a + b + c = π / 3) :
  -(angleShift c : Real.Angle) - ((π / 3 : ℝ) : Real.Angle) - (angleShift b : Real.Angle) = (angleShiftTwo a : Real.Angle) := by
    norm_num [ angleShift, angleShiftTwo ];
    norm_num [ show a = Real.pi / 3 - b - c by linarith ] ; group;
    erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] ; ring;
    exact ⟨ -1, by ring ⟩

/-
The oriented angle B P C is equal to a++.
-/
lemma conway_oangle_gap_P (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ)) :
  let B := conwayConstructedVertexB P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ P_pt) (C -ᵥ P_pt) = (angleShiftTwo a : Real.Angle) := by
    bound;
    have h_sum_angles : (positiveOrientation.oangle (B -ᵥ P_pt) (R -ᵥ P_pt)) + (positiveOrientation.oangle (R -ᵥ P_pt) (Q -ᵥ P_pt)) + (positiveOrientation.oangle (Q -ᵥ P_pt) (C -ᵥ P_pt)) = (positiveOrientation.oangle (B -ᵥ P_pt) (C -ᵥ P_pt)) := by
      rw [ add_assoc, Orientation.oangle_add ];
      · rw [ Orientation.oangle_add ];
        · intro h;
          have := conway_step3_BP_matches R P_pt a b c ( by linarith [ h_equilateral.1, h_equilateral.2 ] ) h_a_pos h_b_pos h_c_pos h_sum; aesop;
          unfold conwayConstructedVertexB at h; aesop;
          rw [ eq_comm ] at this ; aesop;
          unfold conwayLargeSideBP at this; aesop;
          · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith ) ) h_1;
          · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi h_b_pos ( by linarith ) ) h_2;
        · intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
          rw [ eq_comm, Real.Angle.coe_eq_zero_iff ] at h_orientation ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at h <;> nlinarith only [ Real.pi_pos, h ];
        · intro h;
          have h_dist : dist P_pt C = conwayLargeSideCP a c := by
            convert conway_step3_CP_matches P_pt Q a b c h_side h_a_pos h_b_pos h_c_pos h_sum using 1;
          simp_all +decide [ conwayLargeSideCP ];
          exact absurd h_dist ( ne_of_lt ( div_pos ( Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith ) ) ( Real.sin_pos_of_pos_of_lt_pi ( by linarith ) ( by linarith ) ) ) );
      · intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
        rw [ eq_comm, Real.Angle.coe_eq_zero_iff ] at h_orientation ; aesop;
        rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at h <;> nlinarith only [ Real.pi_pos, h ];
      · exact vsub_ne_zero.mpr ( by rintro rfl; norm_num at h_side );
      · intro h;
        have h_dist : dist P_pt C = conwayLargeSideCP a c := by
          convert conway_step3_CP_matches P_pt Q a b c h_side h_a_pos h_b_pos h_c_pos h_sum using 1;
        simp_all +decide [ conwayLargeSideCP ];
        exact absurd h_dist ( ne_of_lt ( div_pos ( Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith ) ) ( Real.sin_pos_of_pos_of_lt_pi ( by linarith ) ( by linarith ) ) ) );
    have h_angle_R_P_B : (positiveOrientation.oangle (B -ᵥ P_pt) (R -ᵥ P_pt)) = -(angleShift c : Real.Angle) := by
      have h_angle_R_P_B : (positiveOrientation.oangle (R -ᵥ P_pt) (B -ᵥ P_pt)) = (angleShift c : Real.Angle) := by
        apply conway_oangle_R_P_B;
        all_goals assumption;
      rw [ ← h_angle_R_P_B, Orientation.oangle_rev ]
    have h_angle_Q_P_C : (positiveOrientation.oangle (Q -ᵥ P_pt) (C -ᵥ P_pt)) = -(angleShift b : Real.Angle) := by
      convert conway_oangle_Q_P_C P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt using 1;
    have h_final : (positiveOrientation.oangle (B -ᵥ P_pt) (C -ᵥ P_pt)) = -(angleShift c : Real.Angle) - (Real.pi / 3 : ℝ) - (angleShift b : Real.Angle) := by
      have h_final : (positiveOrientation.oangle (R -ᵥ P_pt) (Q -ᵥ P_pt)) = -(Real.pi / 3 : ℝ) := by
        rw [ ← h_orientation, Orientation.oangle_rev ];
      exact h_sum_angles ▸ h_angle_R_P_B.symm ▸ h_angle_Q_P_C.symm ▸ h_final.symm ▸ by abel1;
    exact h_final.trans ( conway_angle_arithmetic_P a b c h_sum )

/-
The angle B P C is equal to a++.
-/
theorem conway_gap_angle_P_correct (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ)) :
  let B := conwayConstructedVertexB P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  angle B P_pt C = conwayLargeAngleP a := by
    have h_angle_P : let B := conwayConstructedVertexB P_pt Q R a b c
      let C := conwayConstructedVertexC P_pt Q R a b c
      (Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ P_pt) (C -ᵥ P_pt) : Real.Angle) = (angleShiftTwo a : Real.Angle) := by
        exact?;
    convert congr_arg Real.Angle.toReal h_angle_P using 1;
    · unfold angle;
      rw [ Orientation.oangle_eq_angle_of_sign_eq_one ];
      · rw [ Real.Angle.toReal_coe ];
        rw [ eq_comm, toIocMod_eq_iff ];
        exact ⟨ ⟨ by linarith [ Real.pi_pos, InnerProductGeometry.angle_nonneg ( conwayConstructedVertexB P_pt Q R a b c -ᵥ P_pt ) ( conwayConstructedVertexC P_pt Q R a b c -ᵥ P_pt ) ], by linarith [ Real.pi_pos, InnerProductGeometry.angle_le_pi ( conwayConstructedVertexB P_pt Q R a b c -ᵥ P_pt ) ( conwayConstructedVertexC P_pt Q R a b c -ᵥ P_pt ) ] ⟩, 0, by simp +decide ⟩;
      · aesop;
        unfold angleShiftTwo; norm_num [ Real.Angle.sign ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ] ;
        erw [ Real.Angle.sin_coe ] ; norm_num ; exact ( by rw [ ← Real.cos_sub_pi_div_two ] ; exact ( by rw [ sign_eq_one_iff ] ; exact Real.cos_pos_of_mem_Ioo ⟨ by linarith, by linarith ⟩ ) ) ;
    · unfold conwayLargeAngleP;
      unfold angleShiftTwo; norm_num [ Real.pi_pos.le ] ; ring;
      erw [ Real.Angle.toReal_coe ] ; norm_num;
      rw [ eq_comm, toIocMod_eq_iff ];
      exact ⟨ ⟨ by linarith, by linarith ⟩, 0, by norm_num ⟩

/-
The oriented angle from QP to QC is a+.
-/
lemma conway_oangle_C_Q_P (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3) :
  let C := conwayConstructedVertexC P_pt Q R a b c
  Orientation.oangle Module.Oriented.positiveOrientation (P_pt -ᵥ Q) (C -ᵥ Q) = (angleShift a : Real.Angle) := by
  rw [conwayConstructedVertexC]
  apply conwaySmallTriangleVertex_oangle_P2_V_proven
  · rw [h_side]; norm_num
  · exact Real.sin_pos_of_pos_of_lt_pi h_c_pos (by linarith)
  · exact Real.sin_pos_of_pos_of_lt_pi (by unfold angleShift; linarith) (by unfold angleShift; linarith)
  · exact Real.sin_pos_of_pos_of_lt_pi (by unfold angleShift; linarith) (by unfold angleShift; linarith)
  · unfold angleShift; linarith
  · constructor <;> unfold angleShift <;> linarith
  · constructor <;> unfold angleShift <;> linarith

/-
The oriented angle from QP to QC is a+.
-/
lemma conway_oangle_P_Q_C (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3) :
  let C := conwayConstructedVertexC P_pt Q R a b c
  Orientation.oangle Module.Oriented.positiveOrientation (P_pt -ᵥ Q) (C -ᵥ Q) = (angleShift a : Real.Angle) := by
  rw [conwayConstructedVertexC]
  apply conwaySmallTriangleVertex_oangle_P2_V_proven
  · rw [h_side]; norm_num
  · exact Real.sin_pos_of_pos_of_lt_pi h_c_pos (by linarith)
  · exact Real.sin_pos_of_pos_of_lt_pi (by unfold angleShift; linarith) (by unfold angleShift; linarith)
  · exact Real.sin_pos_of_pos_of_lt_pi (by unfold angleShift; linarith) (by unfold angleShift; linarith)
  · unfold angleShift; linarith
  · constructor <;> unfold angleShift <;> linarith
  · constructor <;> unfold angleShift <;> linarith

/-
The oriented angle from QR to QA is -c+.
-/
lemma conway_oangle_R_Q_A (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  Orientation.oangle Module.Oriented.positiveOrientation (R -ᵥ Q) (A -ᵥ Q) = - (angleShift c : Real.Angle) := by
    apply conwaySmallTriangleVertex_oangle_P1_V;
    · cases h_equilateral ; aesop;
    · exact Real.sin_pos_of_pos_of_lt_pi h_a_pos ( by linarith );
    · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith );
    · exact ⟨ by unfold angleShift; linarith, by unfold angleShift; linarith ⟩

/-
Arithmetic identity for angles involved in Conway's proof (gap at Q).
-/
lemma conway_angle_arithmetic_Q (a b c : ℝ) (h_sum : a + b + c = π / 3) :
  -(angleShift a : Real.Angle) - ((π / 3 : ℝ) : Real.Angle) - (angleShift c : Real.Angle) = (angleShiftTwo b : Real.Angle) := by
  norm_num [ angleShift, angleShiftTwo ];
  norm_num [ show b = Real.pi / 3 - a - c by linarith ] ; group;
  erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] ; ring;
  exact ⟨ -1, by ring ⟩

/-
In an equilateral triangle, the oriented angles at the vertices are equal.
-/
lemma equilateral_oangle_cyclic (P_pt Q R : P)
  (h_equilateral : isEquilateral P_pt Q R) :
  Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) =
  Orientation.oangle Module.Oriented.positiveOrientation (R -ᵥ Q) (P_pt -ᵥ Q) := by
    -- Apply the fact that rotations of equilateral triangles preserve angles.
    obtain ⟨r, hr⟩ := h_equilateral;
    simp_all +decide [ dist_eq_norm_vsub, EuclideanGeometry.angle ];
    rw [ ← eq_comm, Orientation.oangle ];
    rw [ Orientation.oangle ];
    simp +zetaDelta at *;
    -- By the properties of the kahler form and the fact that the triangle is equilateral, we can show that the arguments are equal.
    have h_arg_eq : ∀ (u v : V), (positiveOrientation.kahler u v).arg = (positiveOrientation.kahler (-u) (-v)).arg := by
      simp +decide [ Complex.arg ];
    convert h_arg_eq _ _ using 2 ; simp +decide [ hr, vsub_sub_vsub_cancel_left ];
    rw [ show Q -ᵥ P_pt = ( Q -ᵥ R ) + ( R -ᵥ P_pt ) by rw [ vsub_add_vsub_cancel ] ];
    rw [ add_comm ];
    simp +decide [ add_mul, mul_add, hr ];
    ring

/-
The oriented angle C Q A is equal to b++.
-/
lemma conway_oangle_gap_Q (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ)) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ Q) (A -ᵥ Q) = (angleShiftTwo b : Real.Angle) := by
    convert ( conway_oangle_gap_P Q R P_pt b c a _ _ _ _ _ _ _ _ _ ) using 1;
    any_goals assumption;
    · rw [ ← equilateral_oangle_cyclic P_pt Q R h_equilateral ] at * ; aesop;
    · unfold isEquilateral at *; aesop;
    · rw [ ← h_side, h_equilateral.1 ];
    · linarith

/-
The angle C Q A is equal to b++.
-/
theorem conway_gap_angle_Q_correct (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ)) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  angle C Q A = conwayLargeAngleQ b := by
    bound;
    -- Apply the lemma `conway_oangle_gap_Q` to conclude the proof.
    have h_angle_Q : ∠ C Q A = (angleShiftTwo b : Real.Angle) := by
      have := conway_oangle_gap_Q P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation
      rw [ ← this, EuclideanGeometry.angle ];
      rw [ Orientation.oangle_eq_angle_of_sign_eq_one ];
      rw [ this, Real.Angle.sign ];
      unfold angleShiftTwo; norm_num [ Real.sin_add ];
      erw [ sign_eq_one_iff ];
      erw [ Real.Angle.sin_coe ] ; exact Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by linarith );
    erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] at h_angle_Q ; aesop;
    rcases w with ⟨ w | w ⟩ <;> norm_num at *;
    · exact eq_of_sub_eq_zero h;
    · norm_num [ angleShiftTwo ] at *;
      nlinarith [ Real.pi_pos, show ( ∠ C Q A : ℝ ) ≤ Real.pi by exact Real.arccos_le_pi _ ];
    · nlinarith! [ Real.pi_pos, EuclideanGeometry.angle_nonneg C Q A, EuclideanGeometry.angle_le_pi C Q A, show angleShiftTwo b = b + 2 * Real.pi / 3 by rfl ]

/-
A similarity transformation preserves the unoriented angle at a vertex.
-/
lemma similarity_preserves_angle (f : Similarity P) (A B C : P) (h_distinct : A ≠ B ∧ A ≠ C) :
  angle (f B) (f A) (f C) = angle B A C := by
    simp +decide [ EuclideanGeometry.angle, f.dist_eq ];
    -- By definition of similarity, we know that the inner product of the vectors is preserved up to a scale factor.
    have h_inner_preserved : ∀ (u v : V), inner ℝ (f.toFun (u +ᵥ A) -ᵥ f.toFun A) (f.toFun (v +ᵥ A) -ᵥ f.toFun A) = f.r^2 * inner ℝ u v := by
      have h_inner_preserved : ∀ (u v : V), ‖f.toFun (u +ᵥ A) -ᵥ f.toFun A‖ = f.r * ‖u‖ ∧ ‖f.toFun (v +ᵥ A) -ᵥ f.toFun A‖ = f.r * ‖v‖ ∧ ‖(f.toFun (u +ᵥ A) -ᵥ f.toFun A) - (f.toFun (v +ᵥ A) -ᵥ f.toFun A)‖ = f.r * ‖u - v‖ := by
        have := f.dist_eq;
        simp_all +decide [ dist_eq_norm_vsub ];
      intro u v;
      have := h_inner_preserved u v;
      have := norm_sub_sq_real ( f.toFun ( u +ᵥ A ) -ᵥ f.toFun A ) ( f.toFun ( v +ᵥ A ) -ᵥ f.toFun A ) ; simp_all +decide [ mul_pow, norm_sub_rev ] ;
      have := norm_sub_sq_real u v; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
      nlinarith [ show 0 < f.r ^ 2 by exact sq_pos_of_pos f.r_pos ];
    have h_norm_preserved : ∀ (v : V), ‖f.toFun (v +ᵥ A) -ᵥ f.toFun A‖ = f.r * ‖v‖ := by
      intro v; specialize h_inner_preserved v v; simp_all +decide [ inner_self_eq_norm_sq_to_K ] ;
      rw [ ← sq_eq_sq₀ ( norm_nonneg _ ) ( mul_nonneg f.r_pos.le ( norm_nonneg _ ) ), h_inner_preserved, mul_pow ];
    have := h_inner_preserved ( B -ᵥ A ) ( C -ᵥ A ) ; have := h_norm_preserved ( B -ᵥ A ) ; have := h_norm_preserved ( C -ᵥ A ) ; simp_all +decide [ InnerProductGeometry.angle ];
    ring_nf;
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt f.r_pos ]

/-
Characterization of collinearity using distances.
-/
lemma collinear_iff_dist_sum (A B C : P) :
  Collinear ℝ {A, B, C} ↔
  dist A B + dist B C = dist A C ∨
  dist A C + dist C B = dist A B ∨
  dist B A + dist A C = dist B C := by
    rw [ collinear_iff_exists_forall_eq_smul_vadd ] ; aesop;
    · simp +decide only [dist_eq_norm, norm_sub_rev];
      simp +decide [ ← sub_smul, norm_smul ];
      cases abs_cases ( w_2 - w_3 ) <;> cases abs_cases ( w_3 - w_4 ) <;> cases abs_cases ( w_2 - w_4 ) <;> first | exact Or.inl <| by nlinarith [ norm_nonneg w_1 ] | exact Or.inr <| Or.inl <| by nlinarith [ norm_nonneg w_1 ] | exact Or.inr <| Or.inr <| by nlinarith [ norm_nonneg w_1 ] ;
    · -- By the triangle inequality, if the sum of the distances from A to B and from B to C equals the distance from A to C, then B must lie on the line segment AC.
      have h_collinear : Collinear ℝ ({A, B, C} : Set P) := by
        rw [ collinear_iff_exists_forall_eq_smul_vadd ] ; use A ; aesop;
        -- By the properties of the metric space, since dist A B + dist B C = dist A C, the points A, B, and C are collinear.
        have h_collinear : ∃ t : ℝ, B = t • (C -ᵥ A) +ᵥ A := by
          have h_collinear : ‖B -ᵥ A‖ + ‖C -ᵥ B‖ = ‖C -ᵥ A‖ := by
            simp_all +decide [ dist_eq_norm_vsub' ];
          -- By the properties of the inner product and the norm, we can deduce that $B$ lies on the line segment connecting $A$ and $C$.
          have h_inner : inner ℝ (B -ᵥ A) (C -ᵥ A) = ‖B -ᵥ A‖ * ‖C -ᵥ A‖ := by
            have h_inner : ‖B -ᵥ A‖^2 + 2 * inner ℝ (B -ᵥ A) (C -ᵥ B) + ‖C -ᵥ B‖^2 = ‖C -ᵥ A‖^2 := by
              rw [ ← h_collinear, add_sq ];
              have h_collinear : ‖(B -ᵥ A) + (C -ᵥ B)‖^2 = ‖C -ᵥ A‖^2 := by
                simp +decide [ add_comm, add_left_comm, add_assoc ];
                rw [ ← vsub_add_vsub_cancel ];
                rw [ vsub_add_vsub_cancel, add_comm ];
                · rw [ vsub_add_vsub_cancel ];
                · exact A;
              rw [ @norm_add_sq ℝ ] at h_collinear ; aesop;
              nlinarith [ norm_nonneg ( B -ᵥ A ), norm_nonneg ( C -ᵥ B ) ];
            rw [ show C -ᵥ A = ( C -ᵥ B ) + ( B -ᵥ A ) by rw [ vsub_add_vsub_cancel ], inner_add_right ] at * ; aesop;
            rw [ real_inner_self_eq_norm_sq ] at * ; nlinarith [ norm_nonneg ( B -ᵥ A ), norm_nonneg ( C -ᵥ B ), norm_nonneg ( C -ᵥ A ) ] ;
          have h_inner : ‖B -ᵥ A - (‖B -ᵥ A‖ / ‖C -ᵥ A‖) • (C -ᵥ A)‖ = 0 := by
            by_cases h : ‖C -ᵥ A‖ = 0 <;> simp_all +decide [ norm_smul, inner_smul_right ];
            · exact eq_of_dist_eq_zero ( by linarith [ @dist_nonneg _ _ A B, @dist_nonneg _ _ B A ] );
            · have h_inner : ‖B -ᵥ A - (‖B -ᵥ A‖ / ‖C -ᵥ A‖) • (C -ᵥ A)‖ ^ 2 = 0 := by
                rw [ @norm_sub_sq ℝ ] ; simp +decide [ *, inner_smul_right, inner_smul_left ] ; ring;
                simp +decide [ norm_smul, h, mul_assoc, mul_comm, mul_left_comm ] ; ring;
              exact norm_eq_zero.mp ( sq_eq_zero_iff.mp h_inner );
          simp +zetaDelta at *;
          exact ⟨ ‖B -ᵥ A‖ / ‖C -ᵥ A‖, by rw [ sub_eq_zero ] at h_inner; rw [ ← h_inner ] ; simp +decide [ add_comm ] ⟩;
        exact ⟨ C -ᵥ A, ⟨ 0, by simp ( config := { decide := Bool.true } ) ⟩, ⟨ h_collinear.choose, h_collinear.choose_spec ⟩, ⟨ 1, by simp ( config := { decide := Bool.true } ) ⟩ ⟩
      generalize_proofs at *;
      rw [ collinear_iff_exists_forall_eq_smul_vadd ] at h_collinear ; aesop;
    · refine' ⟨ A, B -ᵥ A, ⟨ 0, by simp ( config := { decide := Bool.true } ) ⟩, ⟨ 1, by simp ( config := { decide := Bool.true } ) ⟩, _ ⟩;
      -- By the properties of the distance function and the definition of collinearity, we can find such an $r$.
      obtain ⟨r, hr⟩ : ∃ r : ℝ, dist A C = r * dist A B ∧ dist C B = (1 - r) * dist A B := by
        by_cases hAB : dist A B = 0;
        · simp_all +decide [ dist_comm ];
        · exact ⟨ dist A C / dist A B, by rw [ div_mul_cancel₀ _ hAB ], by rw [ sub_mul, div_mul_cancel₀ _ hAB, one_mul, ← h, add_sub_cancel_left ] ⟩;
      have h_dist_eq : ‖(C -ᵥ A) - r • (B -ᵥ A)‖ = 0 := by
        have h_dist_eq : ‖C -ᵥ A - r • (B -ᵥ A)‖ ^ 2 = ‖C -ᵥ A‖ ^ 2 + r ^ 2 * ‖B -ᵥ A‖ ^ 2 - 2 * r * inner ℝ (C -ᵥ A) (B -ᵥ A) := by
          rw [ @norm_sub_sq ℝ ] ; ring;
          simp ( config := { decide := Bool.true } ) [ norm_smul, inner_smul_right ] ; ring;
          norm_num [ mul_comm ];
        have h_inner_eq : inner ℝ (C -ᵥ A) (B -ᵥ A) = (‖C -ᵥ A‖^2 + ‖B -ᵥ A‖^2 - ‖C -ᵥ B‖^2) / 2 := by
          rw [ show C -ᵥ B = ( C -ᵥ A ) - ( B -ᵥ A ) by rw [ vsub_sub_vsub_cancel_right ] ] ; rw [ @norm_sub_sq ℝ ] ; ring;
          exact?;
        simp_all +decide [ dist_eq_norm_vsub ];
        simp_all +decide [ norm_sub_rev ];
        rw [ show C -ᵥ A = - ( A -ᵥ C ) by rw [ neg_vsub_eq_vsub_rev ], norm_neg ] at * ; aesop;
        rw [ show B -ᵥ A = - ( A -ᵥ B ) by rw [ neg_vsub_eq_vsub_rev ], norm_neg ] at * ; ring_nf at * ; aesop;
        rw [ sub_eq_zero, eq_comm ] at * ; aesop;
      exact ⟨ r, by rw [ ← eq_comm ] ; exact eq_of_sub_eq_zero ( norm_eq_zero.mp h_dist_eq ) ▸ by simp +decide [ vadd_eq_add, add_comm ] ⟩;
    · rw [ dist_eq_norm_vsub, dist_eq_norm_vsub, dist_eq_norm_vsub ] at h_2;
      -- If the sum of the norms of two vectors is equal to the norm of their sum, then the vectors are collinear.
      have h_collinear : ∀ (u v : V), ‖u‖ + ‖v‖ = ‖u + v‖ → ∃ r : ℝ, u = r • v ∨ v = r • u := by
        intro u v huv
        have h_collinear : ∃ r : ℝ, u = r • v ∨ v = r • u := by
          have h_eq : ‖u + v‖^2 = (‖u‖ + ‖v‖)^2 := by
            rw [ huv ]
          have h_eq : inner ℝ u v = ‖u‖ * ‖v‖ := by
            linarith [ norm_add_sq_real u v ];
          by_cases hv : v = 0 <;> simp_all +decide [ inner_self_eq_norm_sq_to_K ];
          · exact ⟨ 0, Or.inr ( by simp +decide ) ⟩;
          · have h_collinear : ‖u - (‖u‖ / ‖v‖) • v‖^2 = 0 := by
              rw [ @norm_sub_sq ℝ ];
              simp_all +decide [ norm_smul, inner_smul_right ];
              ring_nf; norm_num [ hv ];
            exact ⟨ ‖u‖ / ‖v‖, Or.inl <| sub_eq_zero.mp <| norm_eq_zero.mp <| sq_eq_zero_iff.mp h_collinear ⟩;
        exact h_collinear;
      specialize h_collinear ( B -ᵥ A ) ( A -ᵥ C ) ; aesop;
      · use C, A -ᵥ C;
        exact ⟨ ⟨ 1, by simp +decide ⟩, ⟨ w + 1, by simp +decide [ add_smul, ← h_1 ] ⟩, ⟨ 0, by simp +decide ⟩ ⟩;
      · refine' ⟨ A, B -ᵥ A, ⟨ 0, _ ⟩, ⟨ 1, _ ⟩, ⟨ -w, _ ⟩ ⟩ <;> simp +decide [ h_3 ];
        rw [ ← h_3, neg_vsub_eq_vsub_rev, vsub_vadd ]

/-
A similarity transformation preserves collinearity of three points.
-/
lemma similarity_preserves_collinear (f : Similarity P) (A B C : P) :
  Collinear ℝ {A, B, C} ↔ Collinear ℝ {f A, f B, f C} := by
    -- By definition of collinearity, we need to show that $A$, $B$, and $C$ are collinear if and only if $f(A)$, $f(B)$, and $f(C)$ are collinear.
    simp [collinear_iff_dist_sum];
    have h_dist_eq : dist (f.toFun A) (f.toFun B) = f.r * dist A B ∧ dist (f.toFun B) (f.toFun C) = f.r * dist B C ∧ dist (f.toFun A) (f.toFun C) = f.r * dist A C := by
      exact ⟨ f.dist_eq A B, f.dist_eq B C, f.dist_eq A C ⟩;
    simp_all +decide [ dist_comm ];
    norm_num [ ← mul_add, f.r_pos.ne' ]

#check VAdd
#check LinearIsometryEquiv

/-
A similarity transformation can be decomposed into a translation, a scaling, and a linear isometry.
-/
lemma similarity_decomposition (f : Similarity P) (O : P) :
  ∃ (L : V ≃ₗᵢ[ℝ] V), ∀ v, f (v +ᵥ O) = (f.r • L v) +ᵥ f O := by
    have hL : ∃ L : V →ₗ[ℝ] V, ∀ v : V, f.toFun (v +ᵥ O) = f.r • L v +ᵥ f.toFun O := by
      -- Let's denote the similarity transformation as $g(v) = f(v +ᵥ O) -ᵥ f(O)$.
      set g : V → V := fun v => f.toFun (v +ᵥ O) -ᵥ f.toFun O;
      -- Since $g$ is a similarity transformation, it preserves the norm.
      have hg_norm : ∀ v : V, ‖g v‖ = f.r * ‖v‖ := by
        aesop;
        simpa [ dist_eq_norm_vsub ] using f.dist_eq ( v +ᵥ O ) O;
      -- Since $g$ is a similarity transformation, it preserves the inner product.
      have hg_inner : ∀ u v : V, inner ℝ (g u) (g v) = f.r^2 * inner ℝ u v := by
        have hg_inner : ∀ u v : V, ‖g u - g v‖^2 = f.r^2 * ‖u - v‖^2 := by
          intro u v
          have h_dist : dist (f.toFun (u +ᵥ O)) (f.toFun (v +ᵥ O)) = f.r * dist (u +ᵥ O) (v +ᵥ O) := by
            exact f.dist_eq _ _;
          simp_all +decide [ dist_eq_norm, norm_sub_rev ];
          rw [ ← mul_pow, ← h_dist, dist_eq_norm_vsub ];
          norm_num +zetaDelta at *;
        simp_all +decide [ @norm_sub_sq ℝ, @norm_add_sq ℝ ];
        intro u v; linarith [ hg_inner u v ] ;
      -- Since $g$ is a similarity transformation, it is linear.
      have hg_linear : ∀ u v : V, g (u + v) = g u + g v := by
        intros u v
        have h_inner : inner ℝ (g (u + v) - (g u + g v)) (g (u + v) - (g u + g v)) = 0 := by
          simp_all +decide [ inner_sub_left, inner_sub_right, inner_add_left, inner_add_right ];
          ring;
        exact sub_eq_zero.mp ( by simpa [ inner_self_eq_norm_sq_to_K ] using h_inner );
      have hg_smul : ∀ (c : ℝ) (v : V), g (c • v) = c • g v := by
        intro c v
        have h_inner : inner ℝ (g (c • v) - c • g v) (g (c • v) - c • g v) = 0 := by
          simp_all +decide [ inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right ];
          ring;
        exact sub_eq_zero.mp ( by simpa [ inner_self_eq_norm_sq_to_K ] using h_inner );
      refine' ⟨ { toFun := fun v => ( 1 / f.r ) • g v, map_add' := _, map_smul' := _ }, _ ⟩ <;> aesop;
      · rw [ SMulCommClass.smul_comm ];
      · simp +decide [ ← smul_assoc, f.r_pos.ne' ];
    aesop;
    have hL_iso : ∀ v : V, ‖w v‖ = ‖v‖ := by
      intro v; have := f.dist_eq ( v +ᵥ O ) O; aesop;
      rw [ norm_smul, Real.norm_of_nonneg f.r_pos.le ] at this ; nlinarith [ f.r_pos ];
    -- Since w is linear and preserves the norm, it is an isometry.
    have hL_iso : ∀ v₁ v₂ : V, ‖w v₁ - w v₂‖ = ‖v₁ - v₂‖ := by
      simp_all ( config := { decide := Bool.true } ) [ ← map_sub ];
    have hL_iso : Isometry w := by
      exact isometry_iff_dist_eq.mpr fun v₁ v₂ => by simpa [ dist_eq_norm ] using hL_iso v₁ v₂;
    have hL_iso : Function.Bijective w := by
      have hL_iso : Function.Injective w := by
        exact hL_iso.injective;
      have hL_iso : FiniteDimensional ℝ V := by
        exact FiniteDimensional.of_finrank_pos ( by linarith [ Fact.out ( p := Module.finrank ℝ V = 2 ) ] );
      exact ⟨ by assumption, LinearMap.surjective_of_injective ‹_› ⟩;
    exact ⟨ { toLinearEquiv := LinearEquiv.ofBijective w hL_iso, norm_map' := by aesop }, fun v => rfl ⟩

/-
A linear isometry in 2D either preserves or negates oriented angles.
-/
lemma linear_isometry_oangle_eq_or_neg (L : V ≃ₗᵢ[ℝ] V) (u v : V) :
  Orientation.oangle Module.Oriented.positiveOrientation (L u) (L v) = Orientation.oangle Module.Oriented.positiveOrientation u v ∨
  Orientation.oangle Module.Oriented.positiveOrientation (L u) (L v) = - Orientation.oangle Module.Oriented.positiveOrientation u v := by
    -- Since $L$ is a linear isometry, it preserves the lengths of vectors and the angles between them.
    have h_angle_preserved : ∀ (u v : V), inner ℝ (L u) (L v) = inner ℝ u v := by
      exact fun u v => L.inner_map_map u v ▸ rfl;
    by_cases hu : u = 0 <;> by_cases hv : v = 0 <;> simp_all +decide [ oangle ];
    -- Since $L$ is a linear isometry, it preserves the inner product and the norm, so the cosine of the angle between $L(u)$ and $L(v)$ is the same as the cosine of the angle between $u$ and $v$.
    have h_cos : Real.cos (positiveOrientation.oangle (L u) (L v)).toReal = Real.cos (positiveOrientation.oangle u v).toReal := by
      have h_cos : Real.cos (positiveOrientation.oangle (L u) (L v)).toReal = (inner ℝ (L u) (L v)) / (‖L u‖ * ‖L v‖) ∧ Real.cos (positiveOrientation.oangle u v).toReal = (inner ℝ u v) / (‖u‖ * ‖v‖) := by
        have h_cos : ∀ (u v : V), u ≠ 0 → v ≠ 0 → Real.cos (positiveOrientation.oangle u v).toReal = (inner ℝ u v) / (‖u‖ * ‖v‖) := by
          bound;
          rw [ Real.Angle.cos_toReal ];
          exact?;
        exact ⟨ h_cos _ _ ( by simpa using hu ) ( by simpa using hv ), h_cos _ _ hu hv ⟩;
      aesop;
    norm_num +zetaDelta at *;
    exact?

#check oangle
#check EuclideanGeometry.angle

/-
The determinant of a linear isometry is 1 or -1.
-/
lemma linear_isometry_det_eq_one_or_neg_one (L : V ≃ₗᵢ[ℝ] V) :
  LinearMap.det (L.toLinearEquiv : V →ₗ[ℝ] V) = 1 ∨ LinearMap.det (L.toLinearEquiv : V →ₗ[ℝ] V) = -1 := by
    have h_det : LinearMap.det (L : V →ₗ[ℝ] V) ^ 2 = 1 := by
      have h_det : ∀ (u v : V), inner ℝ (L u) (L v) = inner ℝ u v := by
        exact fun u v => L.inner_map_map u v;
      have h_det : ∀ (u v : V), inner ℝ (L u) (L v) = inner ℝ u v := by
        exact h_det;
      have h_det : ∀ (B : OrthonormalBasis (Fin 2) ℝ V), Matrix.det (LinearMap.toMatrix B.toBasis B.toBasis (L : V →ₗ[ℝ] V)) ^ 2 = 1 := by
        intros B
        have h_det : Matrix.det (LinearMap.toMatrix B.toBasis B.toBasis (L : V →ₗ[ℝ] V)) ^ 2 = Matrix.det (Matrix.transpose (LinearMap.toMatrix B.toBasis B.toBasis (L : V →ₗ[ℝ] V)) * LinearMap.toMatrix B.toBasis B.toBasis (L : V →ₗ[ℝ] V)) := by
          rw [ Matrix.det_mul, Matrix.det_transpose, sq ];
        have h_det : Matrix.transpose (LinearMap.toMatrix B.toBasis B.toBasis (L : V →ₗ[ℝ] V)) * LinearMap.toMatrix B.toBasis B.toBasis (L : V →ₗ[ℝ] V) = 1 := by
          ext i j;
          simp +decide [ Matrix.mul_apply, LinearMap.toMatrix_apply ];
          have h_det : ∀ (u v : V), inner ℝ u v = ∑ i, B.repr u i * B.repr v i := by
            intro u v; rw [ ← B.sum_repr u, ← B.sum_repr v ] ; simp +decide [ inner_sum, sum_inner ] ;
            simp +decide [ inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, B.orthonormal.1 ];
            ring;
          have := ‹∀ ( u v : V ), ⟪L u, L v⟫_ℝ = ⟪u, v⟫_ℝ› ( B i ) ( B j ) ; simp_all +decide [ Fin.sum_univ_two ] ;
          fin_cases i <;> fin_cases j <;> simp +decide [ Matrix.one_apply ];
        aesop;
      obtain ⟨B, hB⟩ : ∃ B : OrthonormalBasis (Fin 2) ℝ V, True := by
        have h_orthonormal_basis : ∃ (B : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V), True := by
          have h_finite_dim : FiniteDimensional ℝ V := by
            exact FiniteDimensional.of_finrank_pos ( by linarith [ Fact.out ( p := Module.finrank ℝ V = 2 ) ] )
          simp +zetaDelta at *;
          exact ⟨ by exact? ⟩;
        exact ⟨ h_orthonormal_basis.choose.reindex ( Fintype.equivOfCardEq ( by simp +decide [ Fact.out ( p := Module.finrank ℝ V = 2 ) ] ) ), trivial ⟩;
      convert h_det B;
      simp +zetaDelta at *;
    exact sq_eq_one_iff.mp h_det

#check Orientation.oangle_map
#check Orientation.map_eq_neg_iff_det_neg

#check Orientation.oangle_neg_orientation_eq_neg
#check Orientation.map_eq_neg_iff_det_neg

/-
If a linear isometry has determinant -1, it negates oriented angles.
-/
lemma oangle_map_eq_neg_oangle_of_det_neg_one (L : V ≃ₗᵢ[ℝ] V)
  (h : LinearMap.det (L.toLinearEquiv : V →ₗ[ℝ] V) = -1) (u v : V) :
  Orientation.oangle Module.Oriented.positiveOrientation (L u) (L v) = - Orientation.oangle Module.Oriented.positiveOrientation u v := by
    -- Apply `Orientation.map_eq_neg_iff_det_neg` with `f = L.toLinearEquiv` and `x = positiveOrientation`.
    have h_map : (Orientation.map (Fin 2) L.toLinearEquiv Module.Oriented.positiveOrientation) = -Module.Oriented.positiveOrientation := by
      convert Orientation.map_eq_neg_iff_det_neg _ _ _ |>.2 _;
      exacts [ inferInstance, by simp +decide [ ← Fact.out ( p := Module.finrank ℝ V = 2 ) ], by linarith ];
    have h_angle : (-positiveOrientation).oangle (L u) (L v) = positiveOrientation.oangle u v := by
      rw [ ← h_map, Orientation.oangle_map ];
      simp +decide;
    rw [ ← h_angle, Orientation.oangle_neg_orientation_eq_neg ];
    norm_num

/-
If a linear isometry has determinant 1, it preserves oriented angles.
-/
lemma oangle_map_eq_oangle_of_det_one (L : V ≃ₗᵢ[ℝ] V)
  (h : LinearMap.det (L.toLinearEquiv : V →ₗ[ℝ] V) = 1) (u v : V) :
  Orientation.oangle Module.Oriented.positiveOrientation (L u) (L v) = Orientation.oangle Module.Oriented.positiveOrientation u v := by
    have := @Orientation.oangle_map;
    specialize this positiveOrientation ( L u ) ( L v ) L;
    have h_det : LinearMap.det (L : V →ₗ[ℝ] V) = 1 → (Orientation.map (Fin 2) L.toLinearEquiv) positiveOrientation = positiveOrientation := by
      cases' h_pos : LinearMap.det ( L.toLinearEquiv : V →ₗ[ℝ] V ) with h h <;> aesop;
      convert Orientation.map_eq_iff_det_pos _ _ _ |>.2 _;
      all_goals try infer_instance;
      · exact FiniteDimensional.of_finrank_pos ( by linarith [ Fact.out ( p := Module.finrank ℝ V = 2 ) ] );
      · exact Eq.symm ( Fact.out : Module.finrank ℝ V = 2 );
      · exact h_pos.symm ▸ zero_lt_one;
    aesop;
    convert h_det h |> fun h => ?_;
    convert h.symm ▸ Orientation.oangle_map _ _ _ _;
    · simp ( config := { decide := Bool.true } );
    · simp ( config := { decide := Bool.true } )

/-
If a linear isometry has determinant 1, it commutes with rotation.
-/
lemma linear_isometry_rotation_commute_of_det_one (L : V ≃ₗᵢ[ℝ] V)
  (h : LinearMap.det (L.toLinearEquiv : V →ₗ[ℝ] V) = 1) (θ : Real.Angle) (v : V) :
  L (Orientation.rotation Module.Oriented.positiveOrientation θ v) = Orientation.rotation Module.Oriented.positiveOrientation θ (L v) := by
    -- Since L is a linear isometry with determinant 1, it preserves the orientation and the angles.
    have h_orientation : ∀ u v : V, Orientation.oangle Module.Oriented.positiveOrientation (L u) (L v) = Orientation.oangle Module.Oriented.positiveOrientation u v := by
      apply oangle_map_eq_oangle_of_det_one; assumption;
    have h_rotation_preserved : ∀ (v : V), v ≠ 0 → L ((Orientation.rotation Module.Oriented.positiveOrientation θ) v) = (Orientation.rotation Module.Oriented.positiveOrientation θ) (L v) := by
      intro v hv_nonzero
      have h_rotate : ‖L ((Orientation.rotation Module.Oriented.positiveOrientation θ) v)‖ = ‖(Orientation.rotation Module.Oriented.positiveOrientation θ) (L v)‖ := by
        simp +decide [ LinearIsometryEquiv.norm_map ];
      have h_rotate_eq : ∀ (u v : V), u ≠ 0 → v ≠ 0 → ‖u‖ = ‖v‖ → Orientation.oangle Module.Oriented.positiveOrientation u v = 0 → u = v := by
        intros u v hu hv huv hangle;
        rw [ Orientation.oangle_eq_zero_iff_angle_eq_zero ] at hangle;
        · rw [ InnerProductGeometry.angle_eq_zero_iff ] at hangle ; aesop;
          rw [ norm_smul, Real.norm_of_nonneg left_1.le ] at huv ; aesop;
        · exact hu;
        · exact hv;
      specialize h_rotate_eq ( L ( ( positiveOrientation.rotation θ ) v ) ) ( ( positiveOrientation.rotation θ ) ( L v ) ) ; aesop;
    by_cases hv : v = 0 <;> simp_all +decide

/-
If a linear isometry has determinant -1, it anti-commutes with rotation (maps rotation by theta to rotation by -theta).
-/
lemma linear_isometry_rotation_anticommute_of_det_neg_one (L : V ≃ₗᵢ[ℝ] V)
  (h : LinearMap.det (L.toLinearEquiv : V →ₗ[ℝ] V) = -1) (θ : Real.Angle) (v : V) :
  L (Orientation.rotation Module.Oriented.positiveOrientation θ v) = Orientation.rotation Module.Oriented.positiveOrientation (-θ) (L v) := by
    -- Apply the lemma that states a linear isometry with determinant -1 negates oriented angles.
    have h_neg_oangle : ∀ (u v : V), Orientation.oangle Module.Oriented.positiveOrientation (L u) (L v) = -Orientation.oangle Module.Oriented.positiveOrientation u v := by
      exact?;
    have h_rot : ∀ (v : V), v ≠ 0 → L (Orientation.rotation Module.Oriented.positiveOrientation θ v) = Orientation.rotation Module.Oriented.positiveOrientation (-θ) (L v) := by
      intro v hv_nonzero
      have h_norm : ‖L (Orientation.rotation Module.Oriented.positiveOrientation θ v)‖ = ‖L v‖ := by
        simp +decide [ L.norm_map ]
      have h_angle : Orientation.oangle Module.Oriented.positiveOrientation (L v) (L (Orientation.rotation Module.Oriented.positiveOrientation θ v)) = -θ := by
        aesop
      rw [ ← h_angle, eq_comm ];
      simp +zetaDelta at *;
    by_cases hv : v = 0 <;> aesop

/-
For an angle not equal to pi, the real value of its negation is the negation of its real value.
-/
lemma toReal_neg_eq_neg_toReal (θ : Real.Angle) (h : θ ≠ π) : (-θ).toReal = - θ.toReal := by
  by_contra! h';
  -- Since θ.toReal is not equal to π, we have θ.toReal ∈ (-π, π).
  have h_interval : -Real.pi < θ.toReal ∧ θ.toReal < Real.pi := by
    have h_interval : -Real.pi < θ.toReal ∧ θ.toReal ≤ Real.pi := by
      exact ⟨ by linarith [ Real.pi_pos, θ.toReal_mem_Ioc.1 ], by linarith [ Real.pi_pos, θ.toReal_mem_Ioc.2 ] ⟩;
    cases lt_or_eq_of_le h_interval.2 <;> aesop;
  exact h' ( by rw [ show ( -θ : Angle ) = -θ from rfl ] ; exact (by
  rw [ ← Real.Angle.coe_toReal θ ];
  erw [ Real.Angle.toReal_coe, Real.Angle.toReal_coe ] ; norm_num;
  rw [ toIocMod_eq_iff ] ; aesop;
  linarith) )

/-
A linear isometry maps the trisector vector construction appropriately, handling both orientation-preserving and orientation-reversing cases.
-/
lemma linear_isometry_map_trisector_vector (L : V ≃ₗᵢ[ℝ] V) (u w : V)
  (h_u : u ≠ 0) (h_w : w ≠ 0)
  (h_not_pi : Orientation.oangle Module.Oriented.positiveOrientation u w ≠ (π : Real.Angle)) :
  L (Orientation.rotation Module.Oriented.positiveOrientation (↑((Orientation.oangle Module.Oriented.positiveOrientation u w).toReal / 3) : Real.Angle) u) =
  Orientation.rotation Module.Oriented.positiveOrientation (↑((Orientation.oangle Module.Oriented.positiveOrientation (L u) (L w)).toReal / 3) : Real.Angle) (L u) := by
    -- Consider two cases: when the determinant of L is 1 and when it is -1.
    by_cases h_det : LinearMap.det (L.toLinearEquiv : V →ₗ[ℝ] V) = 1;
    · -- Since L preserves orientation, the rotation by the angle between u and w is the same as the rotation by the angle between L u and L w.
      have h_rotation_eq : (positiveOrientation.oangle (L u) (L w)).toReal = (positiveOrientation.oangle u w).toReal := by
        exact oangle_map_eq_oangle_of_det_one L h_det u w ▸ rfl;
      convert linear_isometry_rotation_commute_of_det_one L h_det _ _ using 1;
      rw [ h_rotation_eq ];
    · have h_det_neg : LinearMap.det (L.toLinearEquiv : V →ₗ[ℝ] V) = -1 := by
        exact Or.resolve_left ( linear_isometry_det_eq_one_or_neg_one L ) h_det;
      -- Since L is orientation-reversing, we have L (rotation θ u) = rotation (-θ) (L u).
      have h_orient_rev : ∀ (θ : Real.Angle) (u : V), L (positiveOrientation.rotation θ u) = positiveOrientation.rotation (-θ) (L u) := by
        exact?;
      have h_neg_oangle : positiveOrientation.oangle (L u) (L w) = -positiveOrientation.oangle u w := by
        exact?;
      have h_neg_oangle_toReal : (-positiveOrientation.oangle u w).toReal = - (positiveOrientation.oangle u w).toReal := by
        exact?;
      aesop;
      norm_num [ neg_div ]

/-
A similarity transformation maps the trisector vector of a nondegenerate triangle to the trisector vector of the image triangle.
-/
lemma similarity_map_trisectorVector (f : Similarity P) (A B C : P)
  (h_nd : NondegenerateTriangle A B C) :
  f (trisectorVector A B C +ᵥ A) -ᵥ f A = trisectorVector (f A) (f B) (f C) := by
    -- By Lemma~\ref{lem:similarity_decomposition}, the transformation is a composition of translation, scaling, and linear isometry.
    obtain ⟨L, hL⟩ : ∃ L : V ≃ₗᵢ[ℝ] V, ∀ v, f (v +ᵥ A) = (f.r • L v) +ᵥ f A := by
      exact?;
    -- By Lemma~\ref{lem:linear_isometry_map_trisector_vector}, `L (rot (ang/3) (B -ᵥ A)) = rot (ang'/3) (L (B -ᵥ A))`.
    have hL_trisector : L (Orientation.rotation Module.Oriented.positiveOrientation (↑((Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)).toReal / 3) : Real.Angle) (B -ᵥ A)) = Orientation.rotation Module.Oriented.positiveOrientation (↑((Orientation.oangle Module.Oriented.positiveOrientation (L (B -ᵥ A)) (L (C -ᵥ A))).toReal / 3) : Real.Angle) (L (B -ᵥ A)) := by
      apply_rules [ linear_isometry_map_trisector_vector ];
      · unfold NondegenerateTriangle at h_nd; aesop;
        exact h_nd <| collinear_pair ℝ B C;
      · contrapose! h_nd;
        simp_all +decide [ NondegenerateTriangle ];
        exact collinear_pair _ _ _;
      · unfold NondegenerateTriangle at h_nd; aesop;
        rw [ collinear_iff_exists_forall_eq_smul_vadd ] at h_nd;
        refine' h_nd ⟨ A, C -ᵥ A, fun p hp => _ ⟩ ; aesop;
        · exact ⟨ 0, by simp +decide ⟩;
        · rw [ Orientation.oangle_eq_pi_iff_oangle_rev_eq_pi ] at a;
          rw [ Orientation.oangle_eq_pi_iff_angle_eq_pi ] at a;
          rw [ InnerProductGeometry.angle_eq_pi_iff ] at a;
          exact ⟨ a.2.choose, by rw [ ← a.2.choose_spec.2, vsub_vadd ] ⟩;
        · exact ⟨ 1, by simp +decide ⟩;
    unfold trisectorVector;
    have := hL ( B -ᵥ A ) ; have := hL ( C -ᵥ A ) ; simp_all +decide [ vadd_vsub_assoc ] ;
    convert congr_arg ( fun x => f.r • x ) hL_trisector using 1;
    simp +decide [ EuclideanGeometry.oangle, vadd_vsub_assoc ];
    simp +decide [ o.oangle_smul_left_of_pos, f.r_pos ]

/-
A similarity transformation maps a line defined by a point and a vector to the line defined by the image point and the image vector difference.
-/
lemma similarity_map_line_eq (f : Similarity P) (p : P) (v : V) :
  f '' (AffineSubspace.mk' p (Submodule.span ℝ {v}) : Set P) =
  (AffineSubspace.mk' (f p) (Submodule.span ℝ {f (v +ᵥ p) -ᵥ f p}) : Set P) := by
    -- By definition of similarity transformation, we know that $f(t • v +ᵥ p) = f.r • L(t • v) +ᵥ f p$ for some linear isometry $L$.
    obtain ⟨L, hL⟩ : ∃ L : V ≃ₗᵢ[ℝ] V, ∀ t : ℝ, f (t • v +ᵥ p) = f.r • L (t • v) +ᵥ f p := by
      have := similarity_decomposition f p;
      exact ⟨ this.choose, fun t => this.choose_spec _ ⟩;
    apply Set.eq_of_subset_of_subset;
    · rintro _ ⟨ x, hx, rfl ⟩ ; simp_all +decide [ Submodule.mem_span_singleton ] ;
      obtain ⟨ a, ha ⟩ := hx; use a; have := hL a; simp_all +decide [ ← eq_sub_iff_add_eq', ← smul_assoc ] ;
      have := hL 1; simp_all +decide [ mul_comm, smul_smul ] ;
    · intro x hx
      aesop;
      rw [ Submodule.mem_span_singleton ] at hx ; aesop;
      refine' ⟨ w • v +ᵥ p, _, _ ⟩;
      · simp +decide [ Submodule.mem_span_singleton ];
      · simp_all ( config := { decide := Bool.true } ) [ zsmul_eq_smul, smul_smul ];
        have := hL 1; simp_all +decide [ mul_comm, smul_smul ] ;

/-
A similarity transformation maps the intersection of two lines (assuming unique intersection) to the intersection of the image lines.
-/
lemma similarity_map_lineIntersection (f : Similarity P) (p1 : P) (v1 : V) (p2 : P) (v2 : V)
  (h_unique : ∃! p, p ∈ AffineSubspace.mk' p1 (Submodule.span ℝ {v1}) ∧ p ∈ AffineSubspace.mk' p2 (Submodule.span ℝ {v2})) :
  f (lineIntersection p1 v1 p2 v2) = lineIntersection (f p1) (f (v1 +ᵥ p1) -ᵥ f p1) (f p2) (f (v2 +ᵥ p2) -ᵥ f p2) := by
    -- By the properties of similarity transformations, the image of the intersection point is the intersection of the images.
    have h_image : ∃! p, p ∈ (AffineSubspace.mk' (f.toFun p1) (Submodule.span ℝ {f.toFun (v1 +ᵥ p1) -ᵥ f.toFun p1} : Submodule ℝ V) : Set P) ∧ p ∈ (AffineSubspace.mk' (f.toFun p2) (Submodule.span ℝ {f.toFun (v2 +ᵥ p2) -ᵥ f.toFun p2} : Submodule ℝ V) : Set P) := by
      have h_image : f '' (AffineSubspace.mk' p1 (Submodule.span ℝ {v1}) : Set P) = AffineSubspace.mk' (f.toFun p1) (Submodule.span ℝ {f.toFun (v1 +ᵥ p1) -ᵥ f.toFun p1} : Submodule ℝ V) := by
        convert similarity_map_line_eq f p1 v1;
      have h_image' : f '' (AffineSubspace.mk' p2 (Submodule.span ℝ {v2}) : Set P) = AffineSubspace.mk' (f.toFun p2) (Submodule.span ℝ {f.toFun (v2 +ᵥ p2) -ᵥ f.toFun p2} : Submodule ℝ V) := by
        convert similarity_map_line_eq f p2 v2 using 1;
      rw [ ← h_image, ← h_image' ] at *; aesop;
      obtain ⟨ p, hp₁, hp₂ ⟩ := h_unique;
      refine' ⟨ f.toFun p, _, _ ⟩;
      · exact ⟨ ⟨ p, hp₁.1, rfl ⟩, ⟨ p, hp₁.2, rfl ⟩ ⟩;
      · rintro y ⟨ ⟨ x, hx₁, rfl ⟩, ⟨ y, hy₁, hy₂ ⟩ ⟩ ; specialize hp₂ x ; aesop;
        cases f ; aesop;
        specialize dist_eq y x; aesop;
    have h_image : f.toFun (lineIntersection p1 v1 p2 v2) ∈ (AffineSubspace.mk' (f.toFun p1) (Submodule.span ℝ {f.toFun (v1 +ᵥ p1) -ᵥ f.toFun p1} : Submodule ℝ V) : Set P) ∧ f.toFun (lineIntersection p1 v1 p2 v2) ∈ (AffineSubspace.mk' (f.toFun p2) (Submodule.span ℝ {f.toFun (v2 +ᵥ p2) -ᵥ f.toFun p2} : Submodule ℝ V) : Set P) := by
      have h_image : f.toFun (lineIntersection p1 v1 p2 v2) ∈ f '' (AffineSubspace.mk' p1 (Submodule.span ℝ {v1}) : Set P) ∧ f.toFun (lineIntersection p1 v1 p2 v2) ∈ f '' (AffineSubspace.mk' p2 (Submodule.span ℝ {v2}) : Set P) := by
        exact ⟨ Set.mem_image_of_mem _ ( Classical.epsilon_spec ( h_unique.exists ) |>.1 ), Set.mem_image_of_mem _ ( Classical.epsilon_spec ( h_unique.exists ) |>.2 ) ⟩;
      convert h_image using 1;
      · rw [ similarity_map_line_eq ];
      · rw [ similarity_map_line_eq ];
    convert ExistsUnique.unique ‹_› _ _ <;> aesop;
    · convert h_image_1.exists.choose_spec.1;
      exact h_image_1.unique ( Classical.epsilon_spec ( show ∃ p, p ∈ AffineSubspace.mk' ( f.toFun p1 ) ( Submodule.span ℝ { f.toFun ( v1 +ᵥ p1 ) -ᵥ f.toFun p1 } ) ∧ p ∈ AffineSubspace.mk' ( f.toFun p2 ) ( Submodule.span ℝ { f.toFun ( v2 +ᵥ p2 ) -ᵥ f.toFun p2 } ) from ⟨ _, left, right ⟩ ) ) h_image_1.exists.choose_spec;
    · exact Classical.epsilon_spec h_image_1.exists |>.2

/-
The oriented angle between a rotated vector and a rotated negative vector is the difference of angles plus pi.
-/
lemma oangle_rotation_neg (u : V) (a b : Real.Angle) (h : u ≠ 0) :
  Orientation.oangle Module.Oriented.positiveOrientation (Orientation.rotation Module.Oriented.positiveOrientation a u) (Orientation.rotation Module.Oriented.positiveOrientation b (-u)) = b - a + π := by
    -- We know that $-u$ is the rotation of $u$ by $\pi$.
    have h_neg_u : -u = (positiveOrientation.rotation Real.pi) u := by
      simp +decide [ Orientation.rotation ];
    -- The angle between $\text{rot}(a, u)$ and $\text{rot}(b + \pi, u)$ is $(b + \pi) - a = b - a + \pi$.
    have h_angle : positiveOrientation.oangle ((positiveOrientation.rotation a) u) ((positiveOrientation.rotation (b + Real.pi)) u) = (b + Real.pi) - a := by
      simp ( config := { decide := Bool.true } ) [ h, oangle ];
      abel1;
    rw [ h_neg_u, add_comm ];
    convert h_angle using 1;
    · simp +decide [ ← h_neg_u, Orientation.rotation ];
    · abel1

/-
Arithmetic lemma showing that a specific linear combination of angles is not 0 or pi modulo 2pi.
-/
lemma trisector_angle_arithmetic (a b : ℝ)
  (ha : 0 < |a| ∧ |a| < π)
  (hb : 0 < |b| ∧ |b| < π)
  (h_sign : a * b < 0)
  (h_sum : |a| + |b| < π) :
  (↑(b/3 - a/3 + π) : Real.Angle) ≠ 0 ∧ (↑(b/3 - a/3 + π) : Real.Angle) ≠ π := by
    constructor <;> norm_num [ Real.Angle ];
    · erw [ QuotientAddGroup.eq_zero_iff ] ; norm_num [ Real.Angle ];
      intros H;
      obtain ⟨ k, hk ⟩ := H ; rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos, abs_lt.mp ha.2, abs_lt.mp hb.2 ];
    · -- Since $a$ and $b$ have opposite signs and their absolute values sum to less than $\pi$, we can deduce that $b - a$ is positive.
      have h_pos : b - a ≠ 0 := by
        cases abs_cases a <;> cases abs_cases b <;> nlinarith;
      erw [ sub_eq_zero, Real.Angle.angle_eq_iff_two_pi_dvd_sub ];
      exact fun ⟨ k, hk ⟩ => h_pos <| by rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos, abs_lt.mp ha.2, abs_lt.mp hb.2 ] ;

/-
The oriented angle between the two adjacent trisectors is the difference of their defining angles plus pi.
-/
lemma oangle_trisector_vectors_eq (A B C : P) (h_nd : NondegenerateTriangle A B C) :
  Orientation.oangle Module.Oriented.positiveOrientation (trisectorVector A B C) (trisectorVector B A C) =
  (↑((Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ B) (C -ᵥ B)).toReal / 3) : Real.Angle) -
  (↑((Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)).toReal / 3) : Real.Angle) + π := by
    unfold trisectorVector;
    -- Let's simplify the expression using the properties of rotations and angles.
    have h_simplify : ∀ (u : V) (a b : Real.Angle), u ≠ 0 → Orientation.oangle Module.Oriented.positiveOrientation (Orientation.rotation Module.Oriented.positiveOrientation a u) (Orientation.rotation Module.Oriented.positiveOrientation b (-u)) = b - a + Real.pi := by
      exact?;
    convert h_simplify ( B -ᵥ A ) ( ↑ ( ( ∡ B A C ).toReal / 3 ) ) ( ↑ ( ( ∡ A B C ).toReal / 3 ) ) _ using 1;
    · rw [ neg_vsub_eq_vsub_rev ];
    · simp_all ( config := { decide := Bool.true } ) [ sub_eq_zero, NondegenerateTriangle ];
      rintro rfl; simp_all ( config := { decide := Bool.true } ) [ collinear_pair ]

/-
Arithmetic identity for angles involved in Conway's proof (gap at R).
-/
lemma conway_angle_arithmetic_R (a b c : ℝ) (h_sum : a + b + c = π / 3) :
  -(angleShift b : Real.Angle) - ((π / 3 : ℝ) : Real.Angle) - (angleShift a : Real.Angle) = (angleShiftTwo c : Real.Angle) := by
    simp_all +decide [ angleShift, angleShiftTwo, Real.Angle ];
    erw [ QuotientAddGroup.eq_iff_sub_mem ] ; ring_nf ; norm_num [ Real.Angle, Real.pi_pos.le ];
    exact ⟨ -1, by norm_num; linarith ⟩

/-
The oriented angle A R B is equal to c++.
-/
lemma conway_oangle_gap_R (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ)) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let B := conwayConstructedVertexB P_pt Q R a b c
  Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ R) (B -ᵥ R) = (angleShiftTwo c : Real.Angle) := by
    have h_quad_v : (∀ (θ θ' : Real.Angle), θ = θ' → (θ : Real.Angle) = (θ' : Real.Angle)) := by
      exact?;
    contrapose! h_quad_v;
    norm_num [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ];
    apply h_quad_v;
    convert conway_oangle_gap_Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _;
    all_goals try assumption;
    · unfold isEquilateral at *; aesop;
    · exact h_equilateral.1.symm ▸ h_side;
    · linarith;
    · convert h_orientation using 1;
      rw [ ← equilateral_oangle_cyclic ];
      exact h_equilateral

/-
The angle A R B is equal to c++.
-/
theorem conway_gap_angle_R_correct (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ)) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let B := conwayConstructedVertexB P_pt Q R a b c
  angle A R B = conwayLargeAngleR c := by
    -- Apply the lemma `conway_oangle_gap_R` to conclude the proof.
    apply conway_gap_angle_P_correct;
    any_goals assumption;
    · unfold isEquilateral at *; aesop;
    · simp_all +decide [ dist_comm ];
      unfold isEquilateral at h_equilateral ; aesop;
      exact dist_comm _ _;
    · linarith;
    · rw [ ← h_orientation ];
      apply_rules [ equilateral_oangle_cyclic ];
      unfold isEquilateral at *; aesop;

/-
The oriented angle at a vertex of a nondegenerate triangle is not 0 or pi.
-/
lemma triangle_angle_ne_zero_or_pi (A B C : P) (h_nd : NondegenerateTriangle A B C) :
  let val_A := (Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)).toReal
  val_A ≠ 0 ∧ val_A ≠ π ∧ val_A ≠ -π := by
    simp_all +decide [ sub_eq_zero, NondegenerateTriangle ];
    refine' ⟨ _, _, _ ⟩;
    · rw [ Orientation.oangle_eq_zero_iff_angle_eq_zero ];
      · rw [ InnerProductGeometry.angle_eq_zero_iff ];
        contrapose! h_nd;
        rw [ collinear_iff_exists_forall_eq_smul_vadd ] ; use A ; aesop;
        refine' ⟨ B -ᵥ A, ⟨ 0, by simp +decide ⟩, ⟨ 1, by simp +decide ⟩, ⟨ w, by simpa [ vsub_eq_sub ] using right.symm ▸ by simp +decide [ left_1.ne' ] ⟩ ⟩;
      · exact vsub_ne_zero.mpr ( by rintro rfl; exact h_nd <| by simp +decide [ collinear_pair ] );
      · exact fun h => h_nd <| by rw [ show C = A by simpa [ sub_eq_zero ] using h ] ; norm_num [ collinear_pair ] ;
    · aesop;
      rw [ collinear_iff_exists_forall_eq_smul_vadd ] at h_nd;
      refine' h_nd ⟨ A, B -ᵥ A, _ ⟩;
      aesop;
      · exact ⟨ 0, by simp +decide ⟩;
      · exact ⟨ 1, by simp +decide ⟩;
      · rw [ Orientation.oangle_eq_pi_iff_oangle_rev_eq_pi ] at a;
        rw [ Orientation.oangle_eq_pi_iff_angle_eq_pi ] at a;
        rw [ InnerProductGeometry.angle_eq_pi_iff ] at a;
        aesop;
        exact ⟨ 1 / w, by simp ( config := { decide := Bool.true } ) [ left_1.ne, smul_smul ] ⟩;
    · linarith [ Real.pi_pos, ( Set.mem_Ioc.mp ( Real.Angle.toReal_mem_Ioc ( positiveOrientation.oangle ( B -ᵥ A ) ( C -ᵥ A ) ) ) ) ]

/-
The area form of u and v-u is equal to the area form of u and v.
-/
lemma areaForm_sub_right (u v : V) :
  (Orientation.areaForm Module.Oriented.positiveOrientation) u (v - u) =
  (Orientation.areaForm Module.Oriented.positiveOrientation) u v := by
    have := ( positiveOrientation.areaForm u ) ; aesop;

/-
The sine of the oriented angle is the area form divided by the product of the norms.
-/
lemma sin_oangle_eq_areaForm_div_norm_mul_norm (u v : V) :
  Real.sin (Orientation.oangle Module.Oriented.positiveOrientation u v).toReal =
  (Orientation.areaForm Module.Oriented.positiveOrientation u v) / (‖u‖ * ‖v‖) := by
    by_cases hu : u = 0 <;> by_cases hv : v = 0 <;> simp ( config := { decide := true } ) [ hu, hv, Orientation.oangle ];
    rw [ Complex.sin_arg ];
    -- By definition of the kahler form, we have that its magnitude is the product of the norms of u and v.
    have h_kahler_magnitude : ‖(positiveOrientation.kahler u) v‖ = ‖u‖ * ‖v‖ := by
      exact?;
    aesop;
    unfold Orientation.kahler at *; aesop;

/-
The sign of the oriented angle between u and v-u is the same as the sign of the oriented angle between u and v.
-/
lemma oangle_toReal_sign_sub_right_eq (u v : V) (h : ¬Collinear ℝ {0, u, v}) :
  Real.sign (Orientation.oangle Module.Oriented.positiveOrientation u (v - u)).toReal = Real.sign (Orientation.oangle Module.Oriented.positiveOrientation u v).toReal := by
    -- Apply `areaForm_sub_right` to rewrite the area form in terms of the original vectors.
    have h_area : (Orientation.areaForm Module.Oriented.positiveOrientation) u (v - u) = (Orientation.areaForm Module.Oriented.positiveOrientation) u v := by
      exact?;
    -- Substitute the area form into the sine expressions.
    have h_sin_eq : Real.sin (Orientation.oangle Module.Oriented.positiveOrientation u (v - u)).toReal = (Orientation.areaForm Module.Oriented.positiveOrientation u v) / (‖u‖ * ‖v - u‖) ∧ Real.sin (Orientation.oangle Module.Oriented.positiveOrientation u v).toReal = (Orientation.areaForm Module.Oriented.positiveOrientation u v) / (‖u‖ * ‖v‖) := by
      exact ⟨ by rw [ ← h_area, sin_oangle_eq_areaForm_div_norm_mul_norm ], by rw [ sin_oangle_eq_areaForm_div_norm_mul_norm ] ⟩;
    by_cases hu : u = 0 <;> by_cases hv : v = 0 <;> simp_all +decide [ div_eq_mul_inv ];
    · exact h ( collinear_pair ℝ _ _ );
    · cases eq_or_ne ( Orientation.areaForm Module.Oriented.positiveOrientation u v ) 0 <;> simp_all +decide [ Real.sign ];
      · -- Since the sine of the oangle is zero, the oangle itself must be zero or π. However, since u and v are not collinear, the oangle can't be π. Therefore, the oangle must be zero.
        have h_oangle_zero : (positiveOrientation.oangle u v).toReal = 0 ∨ (positiveOrientation.oangle u v).toReal = Real.pi := by
          have h_oangle_zero : Real.sin (Orientation.oangle Module.Oriented.positiveOrientation u v).toReal = 0 := by
            aesop;
          norm_num +zetaDelta at *;
          rw [ Real.Angle.sin_eq_zero_iff ] at h_oangle_zero ; aesop;
        cases h_oangle_zero <;> simp_all +decide [ Real.sin_eq_zero_iff ];
        · have h_oangle_zero : ∃ k : ℝ, v = k • u := by
            have h_oangle_zero : ∃ k : ℝ, v = k • u := by
              have h_oangle_zero : (positiveOrientation.oangle u v) = 0 := by
                assumption
              rw [ Orientation.oangle_eq_zero_iff_sameRay ] at h_oangle_zero;
              rw [ SameRay ] at h_oangle_zero ; aesop;
              exact ⟨ w / w_1, by rw [ div_eq_inv_mul, MulAction.mul_smul, right, inv_smul_smul₀ ( ne_of_gt left_1 ) ] ⟩;
            exact h_oangle_zero;
          obtain ⟨ k, rfl ⟩ := h_oangle_zero; simp_all +decide [ collinear_pair ] ;
          contrapose! h;
          rw [ collinear_iff_exists_forall_eq_smul_vadd ] ; use 0 ; simp +decide [ hu, hv ];
          exact ⟨ u, ⟨ 0, by simp +decide ⟩, ⟨ 1, by simp +decide ⟩, ⟨ k, by simp +decide ⟩ ⟩;
        · have h_collinear : Collinear ℝ {0, u, v} := by
            rw [ collinear_iff_exists_forall_eq_smul_vadd ];
            use 0, u;
            aesop;
            · exact ⟨ 0, by simp +decide ⟩;
            · exact ⟨ 1, by simp +decide ⟩;
            · rw [ Orientation.oangle_eq_pi_iff_oangle_rev_eq_pi ] at h_2;
              rw [ Orientation.oangle_eq_pi_iff_angle_eq_pi ] at h_2;
              rw [ InnerProductGeometry.angle_eq_pi_iff ] at h_2;
              rcases h_2.2 with ⟨ r, hr, rfl ⟩ ; exact ⟨ r⁻¹, by simp +decide [ hr.ne ] ⟩;
          contradiction;
      · -- Since the norms are positive, the signs of the sines are the same.
        have h_sin_sign : Real.sin (Orientation.oangle Module.Oriented.positiveOrientation u (v - u)).toReal * Real.sin (Orientation.oangle Module.Oriented.positiveOrientation u v).toReal > 0 := by
          simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
          rw [ sub_eq_zero ] ; aesop;
        split_ifs <;> norm_num;
        any_goals nlinarith [ Real.sin_nonneg_of_nonneg_of_le_pi ( show 0 ≤ ( positiveOrientation.oangle u ( v - u ) |> Real.Angle.toReal ) by linarith ) ( show ( positiveOrientation.oangle u ( v - u ) |> Real.Angle.toReal ) ≤ Real.pi by linarith [ Real.pi_pos, Real.Angle.toReal_le_pi ( positiveOrientation.oangle u ( v - u ) ) ] ), Real.sin_neg_of_neg_of_neg_pi_lt ( show ( positiveOrientation.oangle u v |> Real.Angle.toReal ) < 0 by linarith ) ( show -Real.pi < ( positiveOrientation.oangle u v |> Real.Angle.toReal ) by linarith [ Real.pi_pos, Real.Angle.neg_pi_lt_toReal ( positiveOrientation.oangle u v ) ] ) ];
        · exact h_sin_sign.not_le ( mul_nonpos_of_nonpos_of_nonneg ( Real.sin_nonpos_of_nonpos_of_neg_pi_le ( by linarith ) ( by linarith [ Real.pi_pos, Real.Angle.neg_pi_lt_toReal ( positiveOrientation.oangle u ( v - u ) ) ] ) ) ( Real.sin_nonneg_of_nonneg_of_le_pi ( by linarith ) ( by linarith [ Real.pi_pos, Real.Angle.toReal_le_pi ( positiveOrientation.oangle u v ) ] ) ) );
        · norm_num [ show ( positiveOrientation.oangle u v |> Real.Angle.toReal ) = 0 by linarith ] at *;
        · norm_num [ show ( positiveOrientation.oangle u v |> Real.Angle.toReal ) = 0 by linarith ] at h_sin_sign;
        · exact h_sin_sign.not_le ( mul_nonpos_of_nonpos_of_nonneg ( Real.sin_nonpos_of_nonpos_of_neg_pi_le ( by linarith ) ( by linarith [ Real.pi_pos, Real.Angle.neg_pi_lt_toReal ( positiveOrientation.oangle u ( v - u ) ) ] ) ) ( Real.sin_nonneg_of_nonneg_of_le_pi ( by linarith ) ( by linarith [ Real.pi_pos, Real.Angle.toReal_le_pi ( positiveOrientation.oangle u v ) ] ) ) )

/-
Two vectors obtained by rotating $u$ by $a$ and $-u$ by $-b$ are linearly independent if $0 < a, b$ and $a+b < \pi$.
-/
lemma linear_independent_rotated_vectors (u : V) (a b : ℝ)
  (hu : u ≠ 0)
  (ha : 0 < a) (hb : 0 < b) (hab : a + b < π) :
  LinearIndependent ℝ ![
    Orientation.rotation Module.Oriented.positiveOrientation (a : Real.Angle) u,
    Orientation.rotation Module.Oriented.positiveOrientation (-b : Real.Angle) (-u)
  ] := by
    -- Since the angle difference is non-zero modulo 2π, the vectors are linearly independent.
    have h_angle_diff : (Orientation.oangle Module.Oriented.positiveOrientation (Orientation.rotation Module.Oriented.positiveOrientation a u) (Orientation.rotation Module.Oriented.positiveOrientation (-b) (-u))) ≠ 0 ∧ (Orientation.oangle Module.Oriented.positiveOrientation (Orientation.rotation Module.Oriented.positiveOrientation a u) (Orientation.rotation Module.Oriented.positiveOrientation (-b) (-u))) ≠ Real.pi := by
      -- The angle between the two vectors is (π - b) - a, which is not 0 or π modulo 2π.
      have h_angle : (Orientation.oangle Module.Oriented.positiveOrientation (Orientation.rotation Module.Oriented.positiveOrientation a u) (Orientation.rotation Module.Oriented.positiveOrientation (-b) (-u))) = ((Real.pi - b) - a : Real.Angle) := by
        simp +zetaDelta at *;
        convert oangle_rotation_neg u a ( -b ) hu using 1;
        · simp ( config := { decide := Bool.true } ) [ Orientation.rotation ];
          rw [ add_comm ( - ( cos b • u ) ) ];
        · grind;
      constructor <;> intro H <;> simp_all ( config := { decide := Bool.true } ) [ sub_eq_add_neg ];
      · erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] at H;
        obtain ⟨ k, hk ⟩ := H; rcases k with ⟨ _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos ] ;
      · erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] at H ; obtain ⟨ k, hk ⟩ := H ; rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos ];
    by_contra h_contra;
    -- If the vectors are linearly dependent, then their angle must be 0 or π modulo 2π.
    obtain ⟨k, hk⟩ : ∃ k : ℝ, (Orientation.rotation Module.Oriented.positiveOrientation (-b) (-u)) = k • (Orientation.rotation Module.Oriented.positiveOrientation a u) := by
      rw [ Fintype.not_linearIndependent_iff ] at h_contra;
      obtain ⟨ g, hg₁, i, hi ⟩ := h_contra; use -g 0 / g 1; simp_all +decide [ div_eq_inv_mul, Fin.sum_univ_succ ] ;
      fin_cases i <;> simp_all +decide [ add_eq_zero_iff_eq_neg, smul_smul ];
      · rw [ mul_smul, hg₁, smul_smul, inv_mul_cancel₀ ( show g 1 ≠ 0 from fun h => by simp_all +decide [ ne_of_gt ] ) ] ; simp +decide;
      · simp_all +decide [ mul_assoc, MulAction.mul_smul ];
    cases' lt_or_gt_of_ne ( show k ≠ 0 from by rintro rfl; simp_all +decide [ ne_of_gt ] ) with hk hk <;> simp_all +decide [ ne_of_gt, Real.pi_pos ]

/-
Two vectors obtained by rotating $u$ by $-a$ and $-u$ by $b$ are linearly independent if $0 < a, b$ and $a+b < \pi$.
-/
lemma linear_independent_rotated_vectors_variant (u : V) (a b : ℝ)
  (hu : u ≠ 0)
  (ha : 0 < a) (hb : 0 < b) (hab : a + b < π) :
  LinearIndependent ℝ ![
    Orientation.rotation Module.Oriented.positiveOrientation (-a : Real.Angle) u,
    Orientation.rotation Module.Oriented.positiveOrientation (b : Real.Angle) (-u)
  ] := by
    have := @linear_independent_rotated_vectors;
    specialize this u b a hu hb ha (by linarith);
    rw [ Fintype.linearIndependent_iff ] at this ⊢;
    intro g hg; specialize this ( fun i => if i = 0 then g 1 else g 0 ) ; simp_all +decide [ add_eq_zero_iff_eq_neg ] ;

#check triangle_angle_ne_zero_or_pi

#check 1

#check oangle_add_oangle_add_oangle_eq_pi

/-
The oriented angle R B P_pt is -b.
-/
lemma conway_oangle_R_B_P (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3) :
  let B := conwayVertexB R P_pt a b c
  Orientation.oangle Module.Oriented.positiveOrientation (R -ᵥ B) (P_pt -ᵥ B) = (-b : Real.Angle) := by
    bound;
    -- Apply the lemma `conwaySmallTriangleVertex_oangle_P2_V` with `P1=R, P2=P_pt`.
    have h_oangle_B_P_pt_R : positiveOrientation.oangle (R -ᵥ P_pt) (B -ᵥ P_pt) = angleShift c := by
      apply_rules [ conway_oangle_R_P_B ];
    -- Apply the lemma `conwaySmallTriangleVertex_oangle_P1_V` with `P1=R, P2=P_pt`.
    have h_oangle_P_pt_R_B : positiveOrientation.oangle (P_pt -ᵥ R) (B -ᵥ R) = -angleShift a := by
      -- Apply the lemma `conwaySmallTriangleVertex_oangle_P1_V` with `P1=R, P2=P_pt` to get the oriented angle.
      have h_oangle_P_pt_R_B : positiveOrientation.oangle (P_pt -ᵥ R) (B -ᵥ R) = - angleShift a := by
        have h_pos : dist R P_pt > 0 := by
          unfold isEquilateral at h_equilateral; aesop;
        have h_sin_ao_pos : Real.sin (angleShiftTwo a) > 0 := by
          exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShiftTwo; linarith ) ( by unfold angleShiftTwo; linarith )
        have h_sin_a2_pos : Real.sin (angleShift b) > 0 := by
          exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith )
        have h_a1_bound : 0 < angleShift a ∧ angleShift a < Real.pi := by
          exact ⟨ by unfold angleShift; linarith, by unfold angleShift; linarith ⟩
        exact (by
        apply_rules [ conwaySmallTriangleVertex_oangle_P1_V ];
        · exact Real.sin_pos_of_pos_of_lt_pi h_b_pos ( by linarith );
        · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith ));
      exact h_oangle_P_pt_R_B;
    -- Apply the lemma `oangle_add_oangle_add_oangle_eq_pi` to the triangle `B R P_pt`.
    have h_oangle_sum : positiveOrientation.oangle (R -ᵥ B) (P_pt -ᵥ B) + positiveOrientation.oangle (B -ᵥ P_pt) (R -ᵥ P_pt) + positiveOrientation.oangle (P_pt -ᵥ R) (B -ᵥ R) = Real.pi := by
      convert oangle_add_oangle_add_oangle_eq_pi _ _ _ using 1;
      · intro h;
        norm_num +zetaDelta at *;
        simp_all +decide [ angleShift ];
        erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] at h_oangle_P_pt_R_B ; aesop;
        rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at h_1 <;> nlinarith [ Real.pi_pos ];
      · intro h;
        norm_num [ h ] at *;
        rw [ eq_comm ] at h_oangle_B_P_pt_R ; aesop;
        erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] at * ; aesop;
        rcases w with ⟨ _ | _ | w ⟩ <;> norm_num [ angleShift ] at h <;> nlinarith [ Real.pi_pos ];
      · rintro rfl;
        simp_all +decide [ angleShift ];
        erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] at h_oangle_P_pt_R_B;
        rcases h_oangle_P_pt_R_B with ⟨ k, hk ⟩ ; rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos ];
    -- Substitute the known values of the oriented angles into the sum equation.
    have h_subst : positiveOrientation.oangle (R -ᵥ B) (P_pt -ᵥ B) + (-angleShift c) + (-angleShift a) = Real.pi := by
      have h_oangle_B_P_pt_R_neg : positiveOrientation.oangle (B -ᵥ P_pt) (R -ᵥ P_pt) = -angleShift c := by
        rw [ ← h_oangle_B_P_pt_R, Orientation.oangle_rev ];
      aesop;
    -- Substitute the known values of the oriented angles into the sum equation and simplify.
    have h_simplified : positiveOrientation.oangle (R -ᵥ B) (P_pt -ᵥ B) = Real.pi + angleShift c + angleShift a := by
      exact eq_of_sub_eq_zero ( by rw [ ← h_subst ] ; abel1 );
    rw [ h_simplified ];
    unfold angleShift;
    norm_num [ Real.Angle, ← Real.Angle.coe_add, ← Real.Angle.coe_sub ];
    rw [ show Real.pi + ( c + Real.pi / 3 ) + ( a + Real.pi / 3 ) = -b + 2 * Real.pi by linarith ] ; norm_num [ Real.Angle, two_mul, add_assoc ]

/-
The sum of the angles a++, b, and c is pi.
-/
lemma conway_angle_arithmetic_P_sum (a b c : ℝ) (h_sum : a + b + c = π / 3) :
  (angleShiftTwo a : Real.Angle) + (b : Real.Angle) + (c : Real.Angle) = π := by
    rw [ angleShiftTwo ] ; ring;
    rw [ ← @Real.Angle.coe_add, ← @Real.Angle.coe_add ];
    exact congr_arg _ ( by linarith )

/-
If x is b or -b, y is c or -c, and x+y = b+c, then x=b and y=c, assuming b, c are small positive angles.
-/
lemma conway_angle_arithmetic_lemma (b c : ℝ)
  (hb : 0 < b ∧ b < π / 3)
  (hc : 0 < c ∧ c < π / 3)
  (x y : Real.Angle)
  (hx : x = (b : Real.Angle) ∨ x = -(b : Real.Angle))
  (hy : y = (c : Real.Angle) ∨ y = -(c : Real.Angle))
  (h_sum : x + y = (b : Real.Angle) + (c : Real.Angle)) :
  x = (b : Real.Angle) ∧ y = (c : Real.Angle) := by
    cases hx <;> cases hy <;> simp_all +decide;
    erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] at h_sum ; aesop;
    · rcases w with ⟨ w | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
    · rcases w with ⟨ w | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ]

/-
The oriented angle is equal to the unoriented angle or its negation.
-/
lemma oangle_eq_angle_or_neg_angle (A B C : P) (hAB : A ≠ B) (hCB : C ≠ B) :
  Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ B) (C -ᵥ B) = (angle A B C : Real.Angle) ∨
  Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ B) (C -ᵥ B) = -(angle A B C : Real.Angle) := by
    -- By definition of oriented angle, we know that it is the absolute value of the real representative of the unoriented angle.
    have h_oangle_abs : abs ((Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ B) (C -ᵥ B)).toReal) = angle A B C := by
      rw [ EuclideanGeometry.angle_eq_abs_oangle_toReal ];
      · exact?;
      · exact hAB;
      · assumption;
    cases abs_cases ( ( positiveOrientation.oangle ( A -ᵥ B ) ( C -ᵥ B ) |> Real.Angle.toReal ) ) <;> [ left; right ] <;> aesop;
    · rw [ ← h_oangle_abs, Real.Angle.coe_toReal ];
    · rw [ ← h_oangle_abs ] ; norm_num [ Real.Angle, right ]

/-
If a triangle has oriented angle alpha at A and unoriented angles beta, gamma at B, C, and alpha+beta+gamma=pi, then oriented angle at B is -beta.
-/
lemma conway_triangle_orientation_lemma (A B C : P) (alpha beta gamma : ℝ)
  (h_distinct : A ≠ B ∧ B ≠ C ∧ C ≠ A)
  (h_sum : alpha + beta + gamma = π)
  (h_pos_beta : 0 < beta ∧ beta < π / 3)
  (h_pos_gamma : 0 < gamma ∧ gamma < π / 3)
  (h_oangle_A : Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A) = (alpha : Real.Angle))
  (h_angle_B : angle A B C = beta)
  (h_angle_C : angle B C A = gamma) :
  Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ B) (C -ᵥ B) = (-beta : Real.Angle) := by
    by_contra hb_ne_neg_beta;
    have h_oangle_B : (positiveOrientation.oangle (A -ᵥ B) (C -ᵥ B) = (beta : Real.Angle) ∨ positiveOrientation.oangle (A -ᵥ B) (C -ᵥ B) = - (beta : Real.Angle)) := by
      have h_oangle_B : (positiveOrientation.oangle (A -ᵥ B) (C -ᵥ B) = (EuclideanGeometry.angle A B C : Real.Angle) ∨ positiveOrientation.oangle (A -ᵥ B) (C -ᵥ B) = - (EuclideanGeometry.angle A B C : Real.Angle)) := by
        apply_rules [ oangle_eq_angle_or_neg_angle ];
        · tauto;
        · tauto;
      aesop;
    have h_oangle_C : (positiveOrientation.oangle (B -ᵥ C) (A -ᵥ C) = (gamma : Real.Angle) ∨ positiveOrientation.oangle (B -ᵥ C) (A -ᵥ C) = - (gamma : Real.Angle)) := by
      unfold EuclideanGeometry.angle at h_angle_C; aesop;
      apply oangle_eq_angle_or_neg_angle;
      · assumption;
      · tauto;
    have h_contra : -(positiveOrientation.oangle (A -ᵥ B) (C -ᵥ B)) + -(positiveOrientation.oangle (B -ᵥ C) (A -ᵥ C)) = beta + gamma := by
      have h_contra : positiveOrientation.oangle (A -ᵥ B) (C -ᵥ B) + positiveOrientation.oangle (B -ᵥ C) (A -ᵥ C) + positiveOrientation.oangle (C -ᵥ A) (B -ᵥ A) = Real.pi := by
        apply oangle_add_oangle_add_oangle_eq_pi;
        · tauto;
        · tauto;
        · grind;
      have h_contra : positiveOrientation.oangle (C -ᵥ A) (B -ᵥ A) = -positiveOrientation.oangle (B -ᵥ A) (C -ᵥ A) := by
        rw [ Orientation.oangle_rev ];
      aesop;
      · erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] at * ; aesop;
        rcases w_1 with ⟨ _ | _ | w_1 ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
      · erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] at * ; aesop;
        rcases w_1 with ⟨ _ | w_1 ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
    cases h_oangle_B <;> cases h_oangle_C <;> simp_all +decide;
    erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] at h_contra ; obtain ⟨ k, hk ⟩ := h_contra ; rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos ]

/-
The oriented angle P_pt B C is -b.
-/
lemma conway_oangle_P_B_C (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ)) :
  let B := conwayVertexB R P_pt a b c
  let C := conwayVertexC P_pt Q a b c
  Orientation.oangle Module.Oriented.positiveOrientation (P_pt -ᵥ B) (C -ᵥ B) = (-b : Real.Angle) := by
    -- By definition of $conwayVertexB$ and $conwayVertexC$, we can express their coordinates in terms of $a$, $b$, and $c$.
    set B := conwayVertexB R P_pt a b c
    set C := conwayVertexC P_pt Q a b c;
    -- Apply the lemma `conway_large_triangle_P_angles` to the triangle `P_pt B C`.
    have h_angles : angle P_pt B C = b ∧ angle B C P_pt = c := by
      have h_angles : dist P_pt B = conwayLargeSideBP a b ∧ dist P_pt C = conwayLargeSideCP a c ∧ angle B P_pt C = conwayLargeAngleP a := by
        apply And.intro;
        · apply conway_step3_BP_matches;
          · unfold isEquilateral at h_equilateral; aesop;
          · exact h_a_pos;
          · exact h_b_pos;
          · exact h_c_pos;
          · exact h_sum;
        · apply And.intro;
          · apply conway_step3_CP_matches;
            · exact h_side;
            · exact h_a_pos;
            · exact h_b_pos;
            · exact h_c_pos;
            · exact h_sum;
          · apply conway_gap_angle_P_correct P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation;
      apply And.intro;
      · apply (conway_large_triangle_P_angles B C P_pt a b c h_a_pos h_b_pos h_c_pos h_sum h_angles.left h_angles.right.left h_angles.right.right).left;
      · convert conway_large_triangle_P_angles B C P_pt a b c h_a_pos h_b_pos h_c_pos h_sum _ _ _ using 1;
        · bound;
          · convert conway_large_triangle_P_angles B C P_pt a b c h_a_pos h_b_pos h_c_pos h_sum _ _ _ |>.1 using 1;
            · exact left;
            · exact left_1;
            · exact right;
          · rw [ ← a_1, EuclideanGeometry.angle_comm ];
          · rw [ EuclideanGeometry.angle_comm ] ; aesop;
        · exact h_angles.1;
        · exact h_angles.2.1;
        · exact h_angles.2.2;
    have h_oangle_B_P_C : Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ P_pt) (C -ᵥ P_pt) = (angleShiftTwo a : Real.Angle) := by
      apply conway_oangle_gap_P;
      all_goals assumption;
    have h_oangle_P_B_C : Orientation.oangle Module.Oriented.positiveOrientation (P_pt -ᵥ B) (C -ᵥ B) = -b := by
      have h_distinct : P_pt ≠ B ∧ B ≠ C ∧ C ≠ P_pt := by
        refine' ⟨ _, _, _ ⟩ <;> intro h <;> simp_all +decide [ EuclideanGeometry.angle ];
        · linarith [ Real.pi_pos ];
        · linarith [ Real.pi_pos ];
        · linarith
      apply conway_triangle_orientation_lemma;
      any_goals tauto;
      unfold angleShiftTwo; ring;
      grind;
    exact h_oangle_P_B_C

/-
The sum of the angles c++, a, and b is pi.
-/
lemma conway_angle_arithmetic_R_sum (a b c : ℝ) (h_sum : a + b + c = π / 3) :
  (angleShiftTwo c : Real.Angle) + (a : Real.Angle) + (b : Real.Angle) = π := by
    unfold angleShiftTwo; norm_num [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] ; ring_nf at *; aesop;
    erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] ; ring_nf at * ; aesop;
    exact ⟨ 0, by ring_nf at *; linarith ⟩

/-
The oriented angle R A B is -a.
-/
lemma conway_oangle_R_A_B (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ)) :
  let A := conwayVertexA Q R a b c
  let B := conwayVertexB R P_pt a b c
  Orientation.oangle Module.Oriented.positiveOrientation (R -ᵥ A) (B -ᵥ A) = (-a : Real.Angle) := by
    have h_angle : let A := conwayVertexA Q R a b c
      let B := conwayVertexB R P_pt a b c
      angle A R B = conwayLargeAngleR c := by
        -- Apply the lemma conway_gap_angle_R_correct to conclude the proof.
        apply conway_gap_angle_R_correct P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt;
        exact h_orientation;
    have h_distinct : let A := conwayVertexA Q R a b c
      let B := conwayVertexB R P_pt a b c
      A ≠ R ∧ B ≠ R ∧ A ≠ B := by
        refine' ⟨ _, _, _ ⟩;
        · intro h;
          simp_all +decide [ conwayLargeAngleR ];
          unfold angleShiftTwo at h_angle;
          linarith;
        · intro h;
          simp_all +decide [ conwayLargeAngleR ];
          unfold angleShiftTwo at h_angle;
          linarith;
        · intro h_eq;
          simp_all +decide [ conwayLargeAngleR ];
          unfold angleShiftTwo at h_angle;
          unfold EuclideanGeometry.angle at h_angle;
          rw [ InnerProductGeometry.angle_self ] at h_angle ; linarith [ Real.pi_pos ];
          intro h; simp_all +decide [ InnerProductGeometry.angle ];
          linarith;
    have h_angle_A : let A := conwayVertexA Q R a b c
      let B := conwayVertexB R P_pt a b c
      angle R A B = a := by
        apply (conway_large_triangle_R_angles (conwayVertexA Q R a b c) (conwayVertexB R P_pt a b c) R a b c h_a_pos h_b_pos h_c_pos h_sum (conway_step3_RA_matches Q R a b c (by
        exact h_equilateral.1.symm ▸ h_side ▸ rfl) h_a_pos h_b_pos h_c_pos h_sum) (conway_step3_RB_matches R P_pt a b c (by
        rw [ h_equilateral.2.symm ];
        exact h_equilateral.1.symm ▸ h_side ▸ rfl) h_a_pos h_b_pos h_c_pos h_sum) h_angle).left;
    have h_angle_B : let A := conwayVertexA Q R a b c
      let B := conwayVertexB R P_pt a b c
      angle R B A = b := by
        apply (conway_large_triangle_R_angles (conwayVertexA Q R a b c) (conwayVertexB R P_pt a b c) R a b c h_a_pos h_b_pos h_c_pos h_sum (conway_step3_RA_matches Q R a b c (by
        exact h_equilateral.1.symm ▸ h_side) h_a_pos h_b_pos h_c_pos h_sum) (conway_step3_RB_matches R P_pt a b c (by
        unfold isEquilateral at h_equilateral; aesop;) h_a_pos h_b_pos h_c_pos h_sum) h_angle).right;
    apply conway_triangle_orientation_lemma;
    exact ⟨ h_distinct.1.symm, h_distinct.2.2, h_distinct.2.1 ⟩;
    rotate_left;
    exact ⟨ h_a_pos, h_a_lt ⟩;
    exact ⟨ h_b_pos, h_b_lt ⟩;
    rotate_left;
    exact h_angle_A;
    convert h_angle_B using 1;
    rw [ EuclideanGeometry.angle_comm ];
    exact angleShiftTwo c;
    · unfold angleShiftTwo; ring;
      grind;
    · convert conway_oangle_gap_R P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation using 1

/-
The oriented angle A B R is -b.
-/
lemma conway_oangle_A_B_R (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ)) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let B := conwayConstructedVertexB P_pt Q R a b c
  Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ B) (R -ᵥ B) = (-b : Real.Angle) := by
    have h1 : let A := conwayConstructedVertexA P_pt Q R a b c;
      let B := conwayConstructedVertexB P_pt Q R a b c;
      positiveOrientation.oangle (R -ᵥ A) (B -ᵥ A) = (-a : Real.Angle) := by
        convert conway_oangle_R_A_B P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation using 1;
    have h2 : let A := conwayConstructedVertexA P_pt Q R a b c;
      let B := conwayConstructedVertexB P_pt Q R a b c;
      positiveOrientation.oangle (A -ᵥ R) (B -ᵥ R) = (angleShiftTwo c : Real.Angle) := by
        apply_rules [ conway_oangle_gap_R ];
    have h3 : let A := conwayConstructedVertexA P_pt Q R a b c;
      let B := conwayConstructedVertexB P_pt Q R a b c;
      positiveOrientation.oangle (B -ᵥ A) (R -ᵥ A) + positiveOrientation.oangle (R -ᵥ B) (A -ᵥ B) + positiveOrientation.oangle (A -ᵥ R) (B -ᵥ R) = Real.pi := by
        have h3 : ∀ (A B C : P), A ≠ B → B ≠ C → C ≠ A →
          positiveOrientation.oangle (B -ᵥ A) (C -ᵥ A) + positiveOrientation.oangle (C -ᵥ B) (A -ᵥ B) + positiveOrientation.oangle (A -ᵥ C) (B -ᵥ C) = Real.pi := by
            intros A B C hAB hBC hCA;
            convert oangle_add_oangle_add_oangle_eq_pi _ _ _ using 1;
            congr! 1;
            · exact add_comm _ _;
            · exact hBC;
            · exact hAB;
            · exact hCA;
        apply h3;
        · intro h;
          simp_all +decide [ conwayConstructedVertexA, conwayConstructedVertexB ];
          unfold angleShiftTwo at h2;
          erw [ eq_comm, Real.Angle.angle_eq_iff_two_pi_dvd_sub ] at h2 ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at h_1 <;> nlinarith [ Real.pi_pos ];
        · intro h;
          simp_all +decide [ conwayConstructedVertexB ];
          rw [ eq_comm ] at h2;
          erw [ QuotientAddGroup.eq_zero_iff ] at h2;
          obtain ⟨ k, hk ⟩ := h2;
          rcases k with ⟨ _ | _ | k ⟩ <;> norm_num [ angleShiftTwo ] at hk <;> nlinarith [ Real.pi_pos ];
        · contrapose! h1;
          simp +decide [ ← h1 ];
          rw [ Real.Angle.coe_eq_zero_iff ];
          exact fun ⟨ n, hn ⟩ => by rcases n with ⟨ _ | n ⟩ <;> norm_num at hn <;> nlinarith [ Real.pi_pos ] ;
    have h4 : let A := conwayConstructedVertexA P_pt Q R a b c;
      let B := conwayConstructedVertexB P_pt Q R a b c;
      positiveOrientation.oangle (R -ᵥ B) (A -ᵥ B) = (b : Real.Angle) := by
        simp_all +decide [ add_assoc ];
        unfold angleShiftTwo at *; norm_num at *;
        rw [ show positiveOrientation.oangle ( conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c ) ( R -ᵥ conwayConstructedVertexA P_pt Q R a b c ) = - ( positiveOrientation.oangle ( R -ᵥ conwayConstructedVertexA P_pt Q R a b c ) ( conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c ) ) from ?_ ] at h3;
        · rw [ h1 ] at h3;
          erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] at * ; aesop;
          grind;
        · exact?;
    convert congr_arg Neg.neg h4 using 1;
    exact?

/-
The oriented angle B C P is -c.
-/
lemma conway_oangle_B_C_P (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ)) :
  let B := conwayConstructedVertexB P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ C) (P_pt -ᵥ C) = (-c : Real.Angle) := by
    have h_oangle_P_B_C : let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c; positiveOrientation.oangle (P_pt -ᵥ B) (C -ᵥ B) = -b := by
      apply_rules [ conway_oangle_P_B_C ];
    have h_oangle_gap_P : let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c; positiveOrientation.oangle (B -ᵥ P_pt) (C -ᵥ P_pt) = angleShiftTwo a := by
      apply_rules [ conway_oangle_gap_P ];
    have h_oangle_P_C_B : let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c; positiveOrientation.oangle (B -ᵥ C) (P_pt -ᵥ C) + positiveOrientation.oangle (C -ᵥ P_pt) (B -ᵥ P_pt) + positiveOrientation.oangle (P_pt -ᵥ B) (C -ᵥ B) = Real.pi := by
      convert oangle_add_oangle_add_oangle_eq_pi _ _ _ using 1;
      · have := h_oangle_P_B_C.symm; simp_all +decide [ sub_eq_zero ] ;
        rw [ eq_comm ] at h_oangle_gap_P ; aesop;
        rw [ Real.Angle.coe_eq_zero_iff ] at this;
        obtain ⟨ n, hn ⟩ := this; rcases n with ⟨ _ | _ | n ⟩ <;> norm_num at hn <;> nlinarith [ Real.pi_pos ] ;
      · intro h;
        rw [ eq_comm ] at h;
        unfold conwayConstructedVertexC at h;
        unfold conwayVertexC at h;
        unfold conwaySmallTriangleVertex at h;
        rw [ ← vsub_eq_zero_iff_eq ] at h ; aesop;
        · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith ) ) h;
        · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi h_c_pos ( by linarith ) ) h_2;
      · intro h;
        simp_all +decide [ conwayConstructedVertexB ];
        rw [ eq_comm ] at h_oangle_gap_P;
        rw [ Real.Angle.coe_eq_zero_iff ] at h_oangle_gap_P;
        obtain ⟨ n, hn ⟩ := h_oangle_gap_P;
        rcases n with ⟨ _ | _ | n ⟩ <;> norm_num [ angleShiftTwo ] at hn <;> nlinarith [ Real.pi_pos ];
    have h_oangle_P_C_B : let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c; positiveOrientation.oangle (C -ᵥ P_pt) (B -ᵥ P_pt) = -angleShiftTwo a := by
      field_simp;
      rw [ ← h_oangle_gap_P, Orientation.oangle_rev ];
    have h_oangle_P_C_B : let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c; positiveOrientation.oangle (B -ᵥ C) (P_pt -ᵥ C) = Real.pi - (-↑(angleShiftTwo a)) - (-b) := by
      simp_all +decide [ ← eq_sub_iff_add_eq' ];
    norm_num [ h_oangle_P_C_B, angleShiftTwo ];
    rw [ show c = Real.pi / 3 - a - b by linarith ] ; ring;
    erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] ; ring ; norm_num [ Real.pi_pos.ne' ]

/-
The oriented angle Q C A is -c.
-/
lemma conway_oangle_Q_C_A (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ)) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ C) (A -ᵥ C) = (-c : Real.Angle) := by
    apply conway_oangle_P_B_C;
    all_goals try linarith;
    · unfold isEquilateral at *; aesop;
    · convert h_side using 1;
      exact h_equilateral.1.symm;
    · convert h_orientation using 1;
      rw [ ← equilateral_oangle_cyclic P_pt Q R h_equilateral ]

/-
The oriented angle C A Q is -a.
-/
lemma conway_oangle_C_A_Q (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ)) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ A) (Q -ᵥ A) = (-a : Real.Angle) := by
    have h_oangle_Q_C_A_neg : let A := conwayConstructedVertexA P_pt Q R a b c;
      let C := conwayConstructedVertexC P_pt Q R a b c;
      positiveOrientation.oangle (Q -ᵥ C) (A -ᵥ C) = -c := by
        exact?;
    have h_cyclic_sum : let A := conwayConstructedVertexA P_pt Q R a b c;
      let C := conwayConstructedVertexC P_pt Q R a b c;
      positiveOrientation.oangle (C -ᵥ Q) (A -ᵥ Q) + positiveOrientation.oangle (A -ᵥ C) (Q -ᵥ C) + positiveOrientation.oangle (Q -ᵥ A) (C -ᵥ A) = ↑Real.pi := by
        convert oangle_add_oangle_add_oangle_eq_pi _ _ _ using 1;
        congr! 1;
        · exact?;
        · erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] at h_oangle_Q_C_A_neg ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
        · intro h_eq;
          rw [ eq_comm ] at h_eq;
          simp_all +decide [ conwayConstructedVertexC ];
          erw [ Real.Angle.coe_eq_zero_iff ] at h_oangle_Q_C_A_neg ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
        · intro h;
          simp_all +decide [ conwayConstructedVertexA ];
          rw [ Real.Angle.coe_eq_zero_iff ] at h_oangle_Q_C_A_neg ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
    have h_oangle_gap_Q : let A := conwayConstructedVertexA P_pt Q R a b c;
      let C := conwayConstructedVertexC P_pt Q R a b c;
      positiveOrientation.oangle (C -ᵥ Q) (A -ᵥ Q) = angleShiftTwo b := by
        apply_rules [ conway_oangle_gap_Q ];
    have h_oangle_Q_C_A : let A := conwayConstructedVertexA P_pt Q R a b c;
      let C := conwayConstructedVertexC P_pt Q R a b c;
      positiveOrientation.oangle (A -ᵥ C) (Q -ᵥ C) = c := by
        convert congr_arg Neg.neg h_oangle_Q_C_A_neg using 1;
        · rw [ ← Orientation.oangle_rev ];
        · norm_num;
    have h_oangle_Q_A_C : let A := conwayConstructedVertexA P_pt Q R a b c;
      let C := conwayConstructedVertexC P_pt Q R a b c;
      positiveOrientation.oangle (Q -ᵥ A) (C -ᵥ A) = a := by
        have h_oangle_Q_A_C : let A := conwayConstructedVertexA P_pt Q R a b c;
          let C := conwayConstructedVertexC P_pt Q R a b c;
          positiveOrientation.oangle (Q -ᵥ A) (C -ᵥ A) = Real.pi - (angleShiftTwo b + c) := by
            rw [ ← h_cyclic_sum, h_oangle_gap_Q, h_oangle_Q_C_A ] ; abel1;
        convert h_oangle_Q_A_C using 1;
        unfold angleShiftTwo;
        rw [ show a = Real.pi - ( b + 2 * Real.pi / 3 ) - c by linarith ] ; norm_num [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ];
        norm_num [ sub_sub ];
    rw [ ← h_oangle_Q_A_C ];
    simp +decide [ oangle ];
    exact?

/-
The oriented angle Q A R is -a.
-/
lemma conway_oangle_Q_A_R (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ A) (R -ᵥ A) = (-a : Real.Angle) := by
    have h_sum_angles : Orientation.oangle Module.Oriented.positiveOrientation (R -ᵥ Q) (conwayConstructedVertexA P_pt Q R a b c -ᵥ Q) + Orientation.oangle Module.Oriented.positiveOrientation (conwayConstructedVertexA P_pt Q R a b c -ᵥ R) (Q -ᵥ R) + Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ conwayConstructedVertexA P_pt Q R a b c) (R -ᵥ conwayConstructedVertexA P_pt Q R a b c) = Real.pi := by
      convert oangle_add_oangle_add_oangle_eq_pi _ _ _ using 1;
      congr! 1;
      · rw [ add_comm, EuclideanGeometry.oangle, EuclideanGeometry.oangle ];
      · unfold conwayConstructedVertexA;
        unfold conwayVertexA;
        unfold conwaySmallTriangleVertex;
        intro h;
        rw [ eq_comm ] at h;
        replace h := congr_arg ( fun x => x -ᵥ Q ) h ; simp_all +decide [ dist_eq_norm_vsub ];
        replace h := congr_arg ( fun x => ‖x‖ ) h ; simp_all +decide [ norm_smul, Real.norm_of_nonneg ( Real.sin_nonneg_of_nonneg_of_le_pi ( show 0 ≤ angleShift b by exact add_nonneg h_b_pos.le ( by positivity ) ) ( by linarith [ Real.pi_pos, show angleShift b ≤ Real.pi by exact le_of_lt ( by unfold angleShift; linarith [ Real.pi_pos ] ) ] ) ) ];
        rw [ div_mul_cancel₀ ] at h;
        · rw [ abs_of_pos ( Real.sin_pos_of_pos_of_lt_pi h_a_pos ( by linarith ) ), div_eq_iff ] at h;
          · rw [ show Q -ᵥ R = - ( R -ᵥ Q ) by rw [ neg_vsub_eq_vsub_rev ], norm_neg ] at h;
            aesop;
            · unfold angleShift at h_1;
              rw [ Real.sin_eq_sin_iff ] at h_1;
              rcases h_1 with ⟨ k, hk | hk ⟩ <;> rcases k with ⟨ _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos ];
            · unfold isEquilateral at h_equilateral;
              simp_all +decide [ dist_comm ];
          · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi h_a_pos ( by linarith ) );
        · aesop;
          unfold isEquilateral at h_equilateral;
          simp_all +decide [ dist_comm ];
      · rintro rfl; simp_all +decide [ isEquilateral ];
      · have h_distinct : dist (conwayConstructedVertexA P_pt Q R a b c) Q > 0 := by
          unfold conwayConstructedVertexA;
          unfold conwayVertexA;
          unfold conwaySmallTriangleVertex;
          simp +decide [ dist_eq_norm, norm_smul ];
          rw [ div_mul_cancel₀ ];
          · refine' div_pos ( mul_pos ( dist_pos.mpr _ ) ( abs_pos.mpr _ ) ) ( abs_pos.mpr _ );
            · rintro rfl; simp_all +decide [ isEquilateral ];
            · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith ) );
            · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi h_a_pos ( by linarith ) );
          · unfold isEquilateral at h_equilateral ; aesop;
        aesop;
    have h_oangle_R_Q_A : Orientation.oangle Module.Oriented.positiveOrientation (R -ᵥ Q) (conwayConstructedVertexA P_pt Q R a b c -ᵥ Q) = -(angleShift c : Real.Angle) := by
      -- By definition of $conwayConstructedVertexA$, we know that $R -ᵥ Q$ and $conwayConstructedVertexA P_pt Q R a b c -ᵥ Q$ form an angle of $-(angleShift c)$.
      apply conway_oangle_R_Q_A P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt;
    have h_oangle_A_R_Q : Orientation.oangle Module.Oriented.positiveOrientation (conwayConstructedVertexA P_pt Q R a b c -ᵥ R) (Q -ᵥ R) = -(angleShift b : Real.Angle) := by
      have h_oangle_A_R_Q : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ R) (conwayConstructedVertexA P_pt Q R a b c -ᵥ R) = angleShift b := by
        apply conwaySmallTriangleVertex_oangle_P2_V;
        all_goals norm_num [ angleShift ];
        any_goals constructor <;> linarith [ Real.pi_pos ];
        · rintro rfl; simp_all +decide [ isEquilateral ];
        · exact Real.sin_pos_of_pos_of_lt_pi h_a_pos ( by linarith );
        · exact Real.sin_pos_of_pos_of_lt_pi ( by linarith ) ( by linarith );
        · exact Real.sin_pos_of_pos_of_lt_pi ( by linarith ) ( by linarith );
        · linarith;
      rw [ ← h_oangle_A_R_Q, Orientation.oangle_rev ];
    simp_all +decide [ angleShift ];
    erw [ ← eq_sub_iff_add_eq' ] at h_sum ; aesop;
    erw [ ← eq_sub_iff_add_eq' ] at h_sum_angles ; ring_nf at * ; aesop;
    erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] ; norm_num ; ring_nf at * ; aesop

/-
The oriented angle B A C is 3a.
-/
lemma conway_oangle_B_A_C (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ)) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let B := conwayConstructedVertexB P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A) = (↑(3 * a) : Real.Angle) := by
    have h_conway_oangle_R_A_B : let A := conwayConstructedVertexA P_pt Q R a b c; let B := conwayConstructedVertexB P_pt Q R a b c; positiveOrientation.oangle (R -ᵥ A) (B -ᵥ A) = -(a : Real.Angle) := by
      apply_rules [ conway_oangle_R_A_B ];
    have h_conway_oangle_Q_A_R : let A := conwayConstructedVertexA P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c; positiveOrientation.oangle (Q -ᵥ A) (R -ᵥ A) = -(a : Real.Angle) := by
      apply_rules [ conway_oangle_Q_A_R ];
    have h_conway_oangle_C_A_Q : let A := conwayConstructedVertexA P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c; positiveOrientation.oangle (C -ᵥ A) (Q -ᵥ A) = -(a : Real.Angle) := by
      convert conway_oangle_C_A_Q P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation using 1;
    have h_conway_oangle_B_A_C : let A := conwayConstructedVertexA P_pt Q R a b c; let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c; positiveOrientation.oangle (B -ᵥ A) (C -ᵥ A) = positiveOrientation.oangle (B -ᵥ A) (R -ᵥ A) + positiveOrientation.oangle (R -ᵥ A) (Q -ᵥ A) + positiveOrientation.oangle (Q -ᵥ A) (C -ᵥ A) := by
      simp +decide [ add_assoc ];
      rw [ ← add_assoc, Orientation.oangle_add ];
      · rw [ ← Orientation.oangle_add ];
        · intro h; simp_all +decide [ sub_eq_zero ];
          rw [ Real.Angle.coe_eq_zero_iff ] at h_conway_oangle_R_A_B ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
        · intro h;
          rw [ vsub_eq_zero_iff_eq ] at h;
          rw [ eq_comm ] at h;
          simp_all +decide [ conwayConstructedVertexA ];
          erw [ Real.Angle.coe_eq_zero_iff ] at h_conway_oangle_Q_A_R ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
        · intro h; simp_all +decide [ sub_eq_zero ];
          rw [ Real.Angle.coe_eq_zero_iff ] at h_conway_oangle_C_A_Q ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
      · intro h; simp_all +decide [ sub_eq_zero ];
        rw [ Real.Angle.coe_eq_zero_iff ] at h_conway_oangle_R_A_B ; aesop;
        rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
      · intro h;
        simp +zetaDelta at *;
        rw [ eq_comm ] at h;
        simp_all +decide [ conwayConstructedVertexA ];
        rw [ Real.Angle.coe_eq_zero_iff ] at h_conway_oangle_R_A_B;
        obtain ⟨ n, hn ⟩ := h_conway_oangle_R_A_B;
        rcases n with ⟨ _ | _ | n ⟩ <;> norm_num at hn <;> nlinarith [ Real.pi_pos ];
      · intro h;
        rw [ vsub_eq_zero_iff_eq ] at h;
        rw [ eq_comm ] at h;
        simp_all +decide [ conwayConstructedVertexA ];
        erw [ Real.Angle.coe_eq_zero_iff ] at h_conway_oangle_Q_A_R ; aesop;
        rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
    have h_conway_oangle_B_A_C : let A := conwayConstructedVertexA P_pt Q R a b c; let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c; positiveOrientation.oangle (B -ᵥ A) (R -ᵥ A) = a ∧ positiveOrientation.oangle (R -ᵥ A) (Q -ᵥ A) = a ∧ positiveOrientation.oangle (Q -ᵥ A) (C -ᵥ A) = a := by
      have h_conway_oangle_B_A_C : let A := conwayConstructedVertexA P_pt Q R a b c; let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c; positiveOrientation.oangle (B -ᵥ A) (R -ᵥ A) = -positiveOrientation.oangle (R -ᵥ A) (B -ᵥ A) ∧ positiveOrientation.oangle (R -ᵥ A) (Q -ᵥ A) = -positiveOrientation.oangle (Q -ᵥ A) (R -ᵥ A) ∧ positiveOrientation.oangle (Q -ᵥ A) (C -ᵥ A) = -positiveOrientation.oangle (C -ᵥ A) (Q -ᵥ A) := by
        exact ⟨ by rw [ ← Orientation.oangle_rev ], by rw [ ← Orientation.oangle_rev ], by rw [ ← Orientation.oangle_rev ] ⟩;
      aesop;
    aesop;
    erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] ; ring_nf ; norm_num

/-
The oriented angle B A C is 3a.
-/
lemma conway_oangle_B_A_C_final (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ)) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let B := conwayConstructedVertexB P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A) = (↑(3 * a) : Real.Angle) := by
    convert conway_oangle_B_A_C P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation using 1

/-
The oriented angle Q C P is c.
-/
lemma conway_oangle_Q_C_P (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3) :
  let C := conwayConstructedVertexC P_pt Q R a b c
  Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ C) (P_pt -ᵥ C) = (c : Real.Angle) := by
    have hQC : let C := conwayConstructedVertexC P_pt Q R a b c;
      Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ C) (P_pt -ᵥ C) = -(angleShift a : Real.Angle) - (angleShift b : Real.Angle) + Real.pi := by
        have hQC : let C := conwayConstructedVertexC P_pt Q R a b c;
          Orientation.oangle Module.Oriented.positiveOrientation (P_pt -ᵥ Q) (C -ᵥ Q) = angleShift a ∧
          Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (C -ᵥ P_pt) = -angleShift b := by
            apply And.intro;
            · convert conway_oangle_P_Q_C P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt using 1;
            · convert conway_oangle_Q_P_C P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt using 1;
        have hQC : let C := conwayConstructedVertexC P_pt Q R a b c;
          Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ P_pt) (Q -ᵥ P_pt) + Orientation.oangle Module.Oriented.positiveOrientation (P_pt -ᵥ Q) (C -ᵥ Q) + Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ C) (P_pt -ᵥ C) = Real.pi := by
            apply oangle_add_oangle_add_oangle_eq_pi;
            · intro h;
              rw [ eq_comm ] at h;
              aesop;
              rw [ eq_comm, Real.Angle.coe_eq_zero_iff ] at left ; aesop;
              rcases w with ⟨ _ | _ | w ⟩ <;> norm_num [ angleShift ] at h_1 <;> nlinarith [ Real.pi_pos ];
            · aesop;
            · intro h; simp_all +decide [ conwayConstructedVertexC ] ;
              unfold angleShift at hQC;
              rw [ eq_comm, Real.Angle.coe_eq_zero_iff ] at hQC ; aesop;
              rcases w with ⟨ w | w ⟩ <;> norm_num at h_1 <;> nlinarith [ Real.pi_pos ];
        have hQC : positiveOrientation.oangle (conwayConstructedVertexC P_pt Q R a b c -ᵥ P_pt) (Q -ᵥ P_pt) = -positiveOrientation.oangle (Q -ᵥ P_pt) (conwayConstructedVertexC P_pt Q R a b c -ᵥ P_pt) := by
          rw [ Orientation.oangle_rev ];
        grind;
    convert hQC using 1;
    bound;
    exact a_1.trans ( by rw [ show c = - ( angleShift a : ℝ ) - ( angleShift b : ℝ ) + Real.pi by norm_num [ angleShift ] ; linarith ] ; norm_num )

/-
The oriented angle C B A is 3b.
-/
lemma conway_oangle_C_B_A (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ)) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let B := conwayConstructedVertexB P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B) = (↑(3 * b) : Real.Angle) := by
    have h_sum_angles : let A := conwayConstructedVertexA P_pt Q R a b c
      let B := conwayConstructedVertexB P_pt Q R a b c
      let C := conwayConstructedVertexC P_pt Q R a b c
      positiveOrientation.oangle (C -ᵥ B) (P_pt -ᵥ B) = b ∧
      positiveOrientation.oangle (P_pt -ᵥ B) (R -ᵥ B) = b ∧
      positiveOrientation.oangle (R -ᵥ B) (A -ᵥ B) = b := by
        aesop;
        · have h_sum_angles : let A := conwayConstructedVertexA P_pt Q R a b c
            let B := conwayConstructedVertexB P_pt Q R a b c
            let C := conwayConstructedVertexC P_pt Q R a b c
            positiveOrientation.oangle (P_pt -ᵥ B) (C -ᵥ B) = -b := by
              apply_rules [ conway_oangle_P_B_C ];
          convert congr_arg Neg.neg h_sum_angles using 1;
          · exact?;
          · norm_num;
        · -- Apply the lemma that states the oriented angle P_pt B R is -b.
          have h_angle_P_B_R : positiveOrientation.oangle (R -ᵥ conwayVertexB R P_pt a b c) (P_pt -ᵥ conwayVertexB R P_pt a b c) = -b := by
            convert conway_oangle_R_B_P P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt using 1;
          rw [ ← neg_inj, ← h_angle_P_B_R, Orientation.oangle_rev ];
          norm_num [ conwayConstructedVertexB, conwayVertexB ];
        · have h_oangle_A_B_R : positiveOrientation.oangle (A -ᵥ B) (R -ᵥ B) = -b := by
            exact?;
          rw [ ← neg_neg ( b : Real.Angle ), ← h_oangle_A_B_R, Orientation.oangle_rev ];
    have h_sum_angles : let A := conwayConstructedVertexA P_pt Q R a b c
      let B := conwayConstructedVertexB P_pt Q R a b c
      let C := conwayConstructedVertexC P_pt Q R a b c
      positiveOrientation.oangle (C -ᵥ B) (A -ᵥ B) = positiveOrientation.oangle (C -ᵥ B) (P_pt -ᵥ B) + positiveOrientation.oangle (P_pt -ᵥ B) (R -ᵥ B) + positiveOrientation.oangle (R -ᵥ B) (A -ᵥ B) := by
        bound;
        rw [ add_assoc, Orientation.oangle_add ];
        · rw [ ← Orientation.oangle_add ];
          · aesop;
            rw [ eq_comm ] at left ; aesop;
            rw [ Real.Angle.coe_eq_zero_iff ] at left ; aesop;
            rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
          · intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
            simp +zetaDelta at *;
            rw [ eq_comm ] at h;
            simp_all +decide [ conwayConstructedVertexB ];
            rw [ eq_comm ] at left ; aesop;
            rw [ Real.Angle.coe_eq_zero_iff ] at left ; aesop;
            rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
          · aesop;
            rw [ eq_comm ] at right ; aesop;
            rw [ Real.Angle.coe_eq_zero_iff ] at right ; aesop;
            rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
        · intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
          simp +zetaDelta at *;
          rw [ eq_comm ] at h;
          simp_all +decide [ conwayConstructedVertexB ];
          rw [ eq_comm ] at left ; aesop;
          rw [ Real.Angle.coe_eq_zero_iff ] at left ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
        · simp +zetaDelta at *;
          intro h;
          rw [ eq_comm ] at h;
          simp_all +decide [ conwayConstructedVertexB ];
          rw [ eq_comm, Real.Angle.coe_eq_zero_iff ] at left_1 ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
        · aesop;
          rw [ eq_comm ] at right ; aesop;
          rw [ Real.Angle.coe_eq_zero_iff ] at right ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
    simp_all +decide [ Real.Angle.coe_eq_zero_iff ];
    norm_num [ ← Real.Angle.coe_add ] ; ring

/-
The oriented angle A C B is 3c.
-/
lemma conway_oangle_A_C_B (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ)) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let B := conwayConstructedVertexB P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ C) (B -ᵥ C) = (↑(3 * c) : Real.Angle) := by
    -- We decompose the angle at C into three parts:
    have h_decomp : let A := conwayConstructedVertexA P_pt Q R a b c;
      let B := conwayConstructedVertexB P_pt Q R a b c;
      let C := conwayConstructedVertexC P_pt Q R a b c;
      positiveOrientation.oangle (A -ᵥ C) (B -ᵥ C) =
        positiveOrientation.oangle (A -ᵥ C) (Q -ᵥ C) +
        positiveOrientation.oangle (Q -ᵥ C) (P_pt -ᵥ C) +
        positiveOrientation.oangle (P_pt -ᵥ C) (B -ᵥ C) := by
          have h_nonzero : let A := conwayConstructedVertexA P_pt Q R a b c;
            let B := conwayConstructedVertexB P_pt Q R a b c;
            let C := conwayConstructedVertexC P_pt Q R a b c;
            (A -ᵥ C) ≠ 0 ∧ (Q -ᵥ C) ≠ 0 ∧ (P_pt -ᵥ C) ≠ 0 ∧ (B -ᵥ C) ≠ 0 := by
              refine' ⟨ _, _, _, _ ⟩;
              · bound;
                have := conway_oangle_gap_Q P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation; simp_all +decide [ sub_eq_zero ] ;
                rw [ eq_comm, Real.Angle.coe_eq_zero_iff ] at this ; aesop;
                rcases w with ⟨ _ | _ | w ⟩ <;> norm_num [ angleShiftTwo ] at h <;> nlinarith [ Real.pi_pos ];
              · -- By definition of $conwayConstructedVertexC$, we know that $Q \neq conwayConstructedVertexC P_pt Q R a b c$.
                have h_neq : Q ≠ conwayConstructedVertexC P_pt Q R a b c := by
                  have := conway_oangle_Q_P_C P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt;
                  contrapose! this;
                  rw [ ← this ] ; norm_num [ Real.pi_pos.ne' ];
                  erw [ Real.Angle.coe_eq_zero_iff ];
                  norm_num [ angleShift ];
                  rintro ⟨ _ | _ | x ⟩ <;> norm_num <;> nlinarith [ Real.pi_pos ];
                exact fun h => h_neq ( eq_of_vsub_eq_zero h );
              · rw [ conwayConstructedVertexC ];
                -- Since $a$ is positive, the vector $(Q - P_pt)$ is non-zero, and the rotation by $a$ preserves the length, so $(conwayVertexC P_pt Q a b c -ᵥ P_pt)$ is non-zero.
                have h_nonzero : (conwayVertexC P_pt Q a b c -ᵥ P_pt) ≠ 0 := by
                  rw [ conwayVertexC ];
                  unfold conwaySmallTriangleVertex; aesop;
                  · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith ) ) a_1;
                  · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi h_c_pos ( by linarith ) ) a_1;
                exact fun h => h_nonzero ( by rw [ ← neg_vsub_eq_vsub_rev, neg_eq_zero ] at *; aesop );
              · have := conway_oangle_P_B_C P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation;
                unfold conwayConstructedVertexB conwayConstructedVertexC at * ; aesop;
                rw [ Real.Angle.coe_eq_zero_iff ] at this ; aesop;
                rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
          simp_all +decide [ add_assoc ];
    -- We have:
    -- 1. `oangle (A - C) (Q - C) = - oangle (Q - C) (A - C) = -(-c) = c` (from `conway_oangle_Q_C_A`).
    -- 2. `oangle (Q - C) (P - C) = c` (from `conway_oangle_Q_C_P`).
    -- 3. `oangle (P - C) (B - C) = - oangle (B - C) (P - C) = -(-c) = c` (from `conway_oangle_B_C_P`).
    have h_parts : let A := conwayConstructedVertexA P_pt Q R a b c;
      let B := conwayConstructedVertexB P_pt Q R a b c;
      let C := conwayConstructedVertexC P_pt Q R a b c;
      positiveOrientation.oangle (A -ᵥ C) (Q -ᵥ C) = (c : Real.Angle) ∧
      positiveOrientation.oangle (Q -ᵥ C) (P_pt -ᵥ C) = (c : Real.Angle) ∧
      positiveOrientation.oangle (P_pt -ᵥ C) (B -ᵥ C) = (c : Real.Angle) := by
        refine' ⟨ _, _, _ ⟩;
        · convert congr_arg Neg.neg ( conway_oangle_Q_C_A P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation ) using 1;
          · rw [ Orientation.oangle_rev ];
          · norm_num;
        · apply_rules [ conway_oangle_Q_C_P ];
        · have h_oangle_B_C_P : positiveOrientation.oangle (conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexC P_pt Q R a b c) (P_pt -ᵥ conwayConstructedVertexC P_pt Q R a b c) = -c := by
            apply_rules [ conway_oangle_B_C_P ];
          rw [ ← neg_neg ( c : Real.Angle ), ← h_oangle_B_C_P, Orientation.oangle_rev ];
    simp_all +decide [ mul_comm ];
    rw [ ← Real.Angle.coe_add, ← Real.Angle.coe_add ] ; ring

/-
If a point lies on two lines and is the unique such point, then `lineIntersection` returns it.
-/
lemma lineIntersection_eq {p1 p2 : P} {v1 v2 : V} {p : P}
  (h1 : p ∈ AffineSubspace.mk' p1 (Submodule.span ℝ {v1}))
  (h2 : p ∈ AffineSubspace.mk' p2 (Submodule.span ℝ {v2}))
  (h_unique : ∀ q, q ∈ AffineSubspace.mk' p1 (Submodule.span ℝ {v1}) → q ∈ AffineSubspace.mk' p2 (Submodule.span ℝ {v2}) → q = p) :
  lineIntersection p1 v1 p2 v2 = p := by
    exact h_unique _ ( Classical.epsilon_spec ( show ∃ q, q ∈ AffineSubspace.mk' p1 ( Submodule.span ℝ { v1 } ) ∧ q ∈ AffineSubspace.mk' p2 ( Submodule.span ℝ { v2 } ) from ⟨ p, h1, h2 ⟩ ) |>.1 ) ( Classical.epsilon_spec ( show ∃ q, q ∈ AffineSubspace.mk' p1 ( Submodule.span ℝ { v1 } ) ∧ q ∈ AffineSubspace.mk' p2 ( Submodule.span ℝ { v2 } ) from ⟨ p, h1, h2 ⟩ ) |>.2 )

/-
The constructed triangle has angles 3a, 3b, 3c.
-/
theorem conway_constructed_triangle_angles (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ))
  (h_gap_P : angle (conwayVertexB R P_pt a b c) P_pt (conwayVertexC P_pt Q a b c) = conwayLargeAngleP a)
  (h_gap_Q : angle (conwayVertexC P_pt Q a b c) Q (conwayVertexA Q R a b c) = conwayLargeAngleQ b)
  (h_gap_R : angle (conwayVertexA Q R a b c) R (conwayVertexB R P_pt a b c) = conwayLargeAngleR c) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let B := conwayConstructedVertexB P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  angle C A B = 3 * a ∧ angle A B C = 3 * b ∧ angle B C A = 3 * c := by
    aesop;
    · convert congr_arg Real.Angle.toReal ( conway_oangle_B_A_C P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation ) using 1;
      · rw [ EuclideanGeometry.angle, eq_comm ];
        rw [ InnerProductGeometry.angle_comm ];
        rw [ Orientation.oangle_eq_angle_of_sign_eq_one ];
        · rw [ Real.Angle.toReal_coe_eq_self_iff ];
          exact ⟨ by linarith [ Real.pi_pos, InnerProductGeometry.angle_nonneg ( conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c ) ( conwayConstructedVertexC P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c ) ], by linarith [ Real.pi_pos, InnerProductGeometry.angle_le_pi ( conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c ) ( conwayConstructedVertexC P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c ) ] ⟩;
        · rw [ conway_oangle_B_A_C ( P_pt := P_pt ) ( Q := Q ) ( R := R ) a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation ] ; norm_num [ Real.Angle.sign ];
          exact sign_eq_one_iff.mpr ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by linarith ) );
      · exact Eq.symm ( Real.Angle.toReal_coe_eq_self_iff.mpr ⟨ by linarith, by linarith ⟩ );
    · convert congr_arg Real.Angle.toReal ( conway_oangle_C_B_A P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation ) using 1;
      · rw [ eq_comm, EuclideanGeometry.angle ];
        rw [ InnerProductGeometry.angle_comm ];
        rw [ InnerProductGeometry.angle ];
        rw [ Orientation.oangle_eq_angle_of_sign_eq_one ];
        · rw [ InnerProductGeometry.angle ];
          rw [ Real.Angle.toReal_coe ];
          rw [ toIocMod_eq_iff ];
          exact ⟨ ⟨ by linarith [ Real.pi_pos, Real.arccos_nonneg ( ⟪conwayConstructedVertexC P_pt Q R a b c -ᵥ conwayConstructedVertexB P_pt Q R a b c, conwayConstructedVertexA P_pt Q R a b c -ᵥ conwayConstructedVertexB P_pt Q R a b c⟫_ℝ / ( ‖conwayConstructedVertexC P_pt Q R a b c -ᵥ conwayConstructedVertexB P_pt Q R a b c‖ * ‖conwayConstructedVertexA P_pt Q R a b c -ᵥ conwayConstructedVertexB P_pt Q R a b c‖ ) ) ], by linarith [ Real.pi_pos, Real.arccos_le_pi ( ⟪conwayConstructedVertexC P_pt Q R a b c -ᵥ conwayConstructedVertexB P_pt Q R a b c, conwayConstructedVertexA P_pt Q R a b c -ᵥ conwayConstructedVertexB P_pt Q R a b c⟫_ℝ / ( ‖conwayConstructedVertexC P_pt Q R a b c -ᵥ conwayConstructedVertexB P_pt Q R a b c‖ * ‖conwayConstructedVertexA P_pt Q R a b c -ᵥ conwayConstructedVertexB P_pt Q R a b c‖ ) ) ] ⟩, 0, by norm_num ⟩;
        · convert congr_arg Real.Angle.sign ( conway_oangle_C_B_A P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation ) using 1;
          rw [ Real.Angle.sign ];
          rw [ eq_comm, sign_eq_one_iff ];
          exact Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by linarith );
      · rw [ Real.Angle.toReal_coe_eq_self_iff.mpr ];
        constructor <;> linarith;
    · convert conway_oangle_A_C_B P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt using 1;
      simp +decide [ EuclideanGeometry.angle, h_orientation ];
      constructor <;> intro h;
      · convert conway_oangle_A_C_B P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt using 1;
        aesop;
      · rw [ InnerProductGeometry.angle_comm ];
        convert congr_arg Real.Angle.toReal h using 1;
        · rw [ InnerProductGeometry.angle ];
          rw [ Orientation.oangle_eq_angle_of_sign_eq_one ];
          · rw [ InnerProductGeometry.angle ];
            field_simp;
            rw [ Real.Angle.toReal_coe ];
            rw [ eq_comm, toIocMod_eq_iff ];
            exact ⟨ ⟨ by linarith [ Real.pi_pos, Real.arccos_nonneg ( ⟪conwayConstructedVertexA P_pt Q R a b c -ᵥ conwayConstructedVertexC P_pt Q R a b c, conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexC P_pt Q R a b c⟫_ℝ / ( ‖conwayConstructedVertexA P_pt Q R a b c -ᵥ conwayConstructedVertexC P_pt Q R a b c‖ * ‖conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexC P_pt Q R a b c‖ ) ) ], by linarith [ Real.pi_pos, Real.arccos_le_pi ( ⟪conwayConstructedVertexA P_pt Q R a b c -ᵥ conwayConstructedVertexC P_pt Q R a b c, conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexC P_pt Q R a b c⟫_ℝ / ( ‖conwayConstructedVertexA P_pt Q R a b c -ᵥ conwayConstructedVertexC P_pt Q R a b c‖ * ‖conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexC P_pt Q R a b c‖ ) ) ] ⟩, 0, by norm_num ⟩;
          · rw [ h, Real.Angle.sign ];
            rw [ sign_eq_one_iff ];
            exact Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by linarith );
        · exact Eq.symm ( Real.Angle.toReal_coe_eq_self_iff.mpr ⟨ by linarith, by linarith ⟩ )

/-
The area form of the vectors forming the angles of a triangle is cyclically invariant (twice the signed area).
-/
lemma areaForm_triangle_cyclic (A B C : P) :
  (Orientation.areaForm Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)) =
  (Orientation.areaForm Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)) ∧
  (Orientation.areaForm Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)) =
  (Orientation.areaForm Module.Oriented.positiveOrientation (A -ᵥ C) (B -ᵥ C)) := by
    constructor;
    · -- By the properties of the area form, we can split the terms and simplify.
      have h_split : (positiveOrientation.areaForm (B -ᵥ A)) (C -ᵥ A) = (positiveOrientation.areaForm (B -ᵥ A)) ((C -ᵥ B) + (B -ᵥ A)) ∧ (positiveOrientation.areaForm (C -ᵥ B)) (A -ᵥ B) = (positiveOrientation.areaForm (C -ᵥ B)) ((A -ᵥ C) + (C -ᵥ B)) := by
        constructor <;> congr <;> simp +decide [ sub_eq_add_neg, add_assoc ];
      simp +decide [ h_split, add_comm, add_left_comm, add_assoc ];
      norm_num [ add_comm, add_left_comm, add_assoc ];
      rw [ ← neg_vsub_eq_vsub_rev A B ];
      rw [ Orientation.areaForm_swap ];
      rw [ map_neg ] ; norm_num;
    · -- By definition of area form, we know that it is linear in both arguments.
      have h_area_form_linear : ∀ (u v : V), (positiveOrientation.areaForm u v) = -(positiveOrientation.areaForm v u) := by
        exact?;
      rw [ h_area_form_linear ];
      rw [ show A -ᵥ B = ( A -ᵥ C ) + ( C -ᵥ B ) by rw [ vsub_add_vsub_cancel ] ];
      rw [ show B -ᵥ C = - ( C -ᵥ B ) by rw [ neg_vsub_eq_vsub_rev ], map_neg ];
      rw [ map_add, add_comm ];
      -- By definition of area form, we know that it is linear in both arguments. Therefore, we can split the expression into two parts.
      simp [add_comm, add_left_comm]

/-
The sines of the oriented angles of a nondegenerate triangle have the same sign.
-/
lemma sin_oangle_triangle_same_sign (A B C : P) (h_nd : NondegenerateTriangle A B C) :
  Real.sign (Real.sin (Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)).toReal) =
  Real.sign (Real.sin (Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)).toReal) ∧
  Real.sign (Real.sin (Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)).toReal) =
  Real.sign (Real.sin (Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ C) (B -ᵥ C)).toReal) := by
    have h_area_form : (Orientation.areaForm Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)) = (Orientation.areaForm Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)) ∧
                        (Orientation.areaForm Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)) = (Orientation.areaForm Module.Oriented.positiveOrientation (A -ᵥ C) (B -ᵥ C)) := by
                          exact?;
    -- Since the norms are positive, the sign of the sine is the same as the sign of the area form.
    have h_sign_eq : ∀ (u v : V), u ≠ 0 → v ≠ 0 → (Real.sin (Orientation.oangle Module.Oriented.positiveOrientation u v).toReal).sign = (Orientation.areaForm Module.Oriented.positiveOrientation u v).sign := by
      intros u v hu hv
      have h_sin_eq_area_form : Real.sin (Orientation.oangle Module.Oriented.positiveOrientation u v).toReal = (Orientation.areaForm Module.Oriented.positiveOrientation u v) / (‖u‖ * ‖v‖) := by
        rw [ sin_oangle_eq_areaForm_div_norm_mul_norm ];
      rw [ h_sin_eq_area_form, Real.sign, Real.sign ];
      split_ifs <;> nlinarith [ norm_pos_iff.2 hu, norm_pos_iff.2 hv, mul_pos ( norm_pos_iff.2 hu ) ( norm_pos_iff.2 hv ), div_mul_cancel₀ ( ( positiveOrientation.areaForm u ) v ) ( mul_ne_zero ( norm_ne_zero_iff.2 hu ) ( norm_ne_zero_iff.2 hv ) ) ];
    simp_all +decide [ NondegenerateTriangle ];
    rw [ h_sign_eq ( B -ᵥ A ) ( C -ᵥ A ) ( by intro h; simp_all +decide [ sub_eq_zero, collinear_pair ] ), h_sign_eq ( C -ᵥ B ) ( A -ᵥ B ) ( by intro h; simp_all +decide [ sub_eq_zero, collinear_pair ] ), h_sign_eq ( A -ᵥ C ) ( B -ᵥ C ) ( by intro h; simp_all +decide [ sub_eq_zero, collinear_pair ] ) ];
    · aesop;
    · intro h; simp_all +decide [ sub_eq_zero, collinear_pair ];
    · exact vsub_ne_zero.mpr ( by rintro rfl; simp_all +decide [ collinear_pair ] );
    · intro h; simp_all +decide [ sub_eq_zero, collinear_pair ] ;

/-
The oriented angles of a nondegenerate triangle are either all positive or all negative.
-/
lemma oangle_triangle_sign_consistent (A B C : P) (h_nd : NondegenerateTriangle A B C) :
  let α := (Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)).toReal
  let β := (Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)).toReal
  let γ := (Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ C) (B -ᵥ C)).toReal
  (0 < α ∧ 0 < β ∧ 0 < γ) ∨ (α < 0 ∧ β < 0 ∧ γ < 0) := by
    have h_signs : Real.sin (positiveOrientation.oangle (B -ᵥ A) (C -ᵥ A)).toReal > 0 ∧ Real.sin (positiveOrientation.oangle (C -ᵥ B) (A -ᵥ B)).toReal > 0 ∧ Real.sin (positiveOrientation.oangle (A -ᵥ C) (B -ᵥ C)).toReal > 0 ∨ Real.sin (positiveOrientation.oangle (B -ᵥ A) (C -ᵥ A)).toReal < 0 ∧ Real.sin (positiveOrientation.oangle (C -ᵥ B) (A -ᵥ B)).toReal < 0 ∧ Real.sin (positiveOrientation.oangle (A -ᵥ C) (B -ᵥ C)).toReal < 0 := by
      have h_signs : Real.sin (positiveOrientation.oangle (B -ᵥ A) (C -ᵥ A)).toReal * Real.sin (positiveOrientation.oangle (C -ᵥ B) (A -ᵥ B)).toReal > 0 ∧ Real.sin (positiveOrientation.oangle (C -ᵥ B) (A -ᵥ B)).toReal * Real.sin (positiveOrientation.oangle (A -ᵥ C) (B -ᵥ C)).toReal > 0 := by
        have := sin_oangle_triangle_same_sign A B C h_nd; aesop;
        · rw [ Real.sign ] at * ; aesop;
          any_goals nlinarith;
          rw [ eq_comm ] at right ; aesop;
          cases h_2.eq_or_lt <;> cases h_3.eq_or_lt <;> first | linarith | aesop;
          have := triangle_angle_ne_zero_or_pi A B C h_nd; simp_all +decide [ Real.sin_eq_zero_iff_cos_eq ] ;
          rw [ Real.Angle.sin_eq_zero_iff ] at * ; aesop;
        · rw [ Real.sign ] at * ; aesop;
          any_goals linarith;
          · rw [ eq_comm, Real.sign ] at right ; aesop;
            · exact absurd ( right h_2.le ) ( by norm_num );
            · nlinarith;
          · rw [ eq_comm, Real.sign ] at right ; aesop;
            norm_num at right;
          · rw [ eq_comm ] at right ; aesop;
            cases h_2.eq_or_lt <;> cases h_3.eq_or_lt <;> first | linarith | aesop;
            have := triangle_angle_ne_zero_or_pi A B C h_nd; simp_all +decide [ Real.sin_eq_zero_iff_cos_eq ] ;
            rw [ Real.Angle.sin_eq_zero_iff ] at * ; aesop;
      cases le_or_gt 0 ( Real.sin ( positiveOrientation.oangle ( B -ᵥ A ) ( C -ᵥ A ) |> Real.Angle.toReal ) ) <;> cases le_or_gt 0 ( Real.sin ( positiveOrientation.oangle ( C -ᵥ B ) ( A -ᵥ B ) |> Real.Angle.toReal ) ) <;> cases le_or_gt 0 ( Real.sin ( positiveOrientation.oangle ( A -ᵥ C ) ( B -ᵥ C ) |> Real.Angle.toReal ) ) <;> first | exact Or.inl ⟨ by nlinarith, by nlinarith, by nlinarith ⟩ | exact Or.inr ⟨ by nlinarith, by nlinarith, by nlinarith ⟩ ;
    aesop;
    · refine' Or.inl ⟨ _, _, _ ⟩;
      · contrapose! left;
        rw [ ← Real.Angle.sin_toReal ];
        exact Real.sin_nonpos_of_nonpos_of_neg_pi_le left ( by linarith [ Real.pi_pos, ( show ( positiveOrientation.oangle ( B -ᵥ A ) ( C -ᵥ A ) |> Real.Angle.toReal ) ≥ -Real.pi from by linarith [ Real.pi_pos, ( show ( positiveOrientation.oangle ( B -ᵥ A ) ( C -ᵥ A ) |> Real.Angle.toReal ) ≥ -Real.pi from by linarith [ Real.pi_pos, ( show ( positiveOrientation.oangle ( B -ᵥ A ) ( C -ᵥ A ) |> Real.Angle.toReal ) ≥ -Real.pi from by linarith [ Real.pi_pos, ( show ( positiveOrientation.oangle ( B -ᵥ A ) ( C -ᵥ A ) |> Real.Angle.toReal ) ≥ -Real.pi from by linarith [ Real.pi_pos, Real.Angle.neg_pi_lt_toReal ( positiveOrientation.oangle ( B -ᵥ A ) ( C -ᵥ A ) ) ] ) ] ) ] ) ] ) ] );
      · contrapose! left_1;
        have h_sin_le_zero : Real.sin (positiveOrientation.oangle (C -ᵥ B) (A -ᵥ B)).toReal ≤ 0 := by
          exact Real.sin_nonpos_of_nonpos_of_neg_pi_le left_1 ( by linarith [ Real.pi_pos, ( Angle.toReal_le_pi ( positiveOrientation.oangle ( C -ᵥ B ) ( A -ᵥ B ) ) ), ( Angle.neg_pi_lt_toReal ( positiveOrientation.oangle ( C -ᵥ B ) ( A -ᵥ B ) ) ) ] );
        simp_all +decide [ Real.Angle.sin ];
      · contrapose! right;
        rw [ ← Real.Angle.sin_toReal ] ; exact Real.sin_nonpos_of_nonpos_of_neg_pi_le right ( by linarith [ Real.pi_pos, Real.Angle.neg_pi_lt_toReal ( positiveOrientation.oangle ( A -ᵥ C ) ( B -ᵥ C ) ) ] );
    · have h_neg_angle : ∀ θ : Real.Angle, Real.sin θ.toReal < 0 → θ.toReal < 0 := by
        intro θ hθ_neg
        by_contra hθ_pos;
        exact hθ_neg.not_le ( Real.sin_nonneg_of_nonneg_of_le_pi ( le_of_not_gt hθ_pos ) ( by linarith [ Real.pi_pos, Real.pi_ne_zero, Angle.toReal_le_pi θ ] ) );
      aesop

/-
The trisector vectors at adjacent vertices of a nondegenerate triangle are linearly independent.
-/
lemma trisector_vectors_linear_independent (A B C : P) (h_nd : NondegenerateTriangle A B C) :
  LinearIndependent ℝ ![trisectorVector A B C, trisectorVector B A C] := by
    have h_sign : Real.sign (Real.sin ((Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)).toReal)) = Real.sign (Real.sin ((Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)).toReal)) := by
      exact sin_oangle_triangle_same_sign A B C h_nd |>.1;
    by_cases h_pos : 0 < (Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)).toReal ∧ 0 < (Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)).toReal;
    · convert linear_independent_rotated_vectors ( B -ᵥ A ) ( ( Orientation.oangle Module.Oriented.positiveOrientation ( B -ᵥ A ) ( C -ᵥ A ) |> Real.Angle.toReal ) / 3 ) ( ( Orientation.oangle Module.Oriented.positiveOrientation ( C -ᵥ B ) ( A -ᵥ B ) |> Real.Angle.toReal ) / 3 ) _ _ _ _ using 1;
      · ext i;
        rw [ show ( positiveOrientation.oangle ( C -ᵥ B ) ( A -ᵥ B ) |> Real.Angle.toReal ) = - ( positiveOrientation.oangle ( A -ᵥ B ) ( C -ᵥ B ) |> Real.Angle.toReal ) from ?_ ];
        · simp +decide [ neg_div ];
          rfl;
        · rw [ ← neg_eq_iff_eq_neg ];
          rw [ ← neg_neg ( positiveOrientation.oangle ( C -ᵥ B ) ( A -ᵥ B ) ), neg_eq_iff_eq_neg ];
          rw [ neg_neg, Orientation.oangle_rev ];
          rw [ toReal_neg_eq_neg_toReal ];
          aesop;
          rw [ Orientation.oangle_eq_pi_iff_oangle_rev_eq_pi ] at a;
          aesop;
          rw [ Real.Angle.sin_eq_zero_iff ] at h_sign ; aesop;
          have := triangle_angle_ne_zero_or_pi A B C h_nd; aesop;
      · exact vsub_ne_zero.mpr ( by aesop );
      · linarith;
      · linarith;
      · linarith [ Real.pi_pos, ( show ( Orientation.oangle Module.Oriented.positiveOrientation ( B -ᵥ A ) ( C -ᵥ A ) |> Real.Angle.toReal ) < Real.pi from by
                                    have := triangle_angle_ne_zero_or_pi A B C h_nd;
                                    exact lt_of_le_of_ne ( Real.Angle.toReal_le_pi _ ) this.2.1 ), ( show ( Orientation.oangle Module.Oriented.positiveOrientation ( C -ᵥ B ) ( A -ᵥ B ) |> Real.Angle.toReal ) < Real.pi from by
                                                                                                                                                                            apply lt_of_le_of_ne;
                                                                                                                                                                            · apply Real.Angle.toReal_le_pi;
                                                                                                                                                                            · aesop;
                                                                                                                                                                              rw [ Real.Angle.sin_eq_zero_iff ] at h_sign ; aesop;
                                                                                                                                                                              have := triangle_angle_ne_zero_or_pi A B C h_nd; aesop; ) ];
    · have h_neg : (Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)).toReal < 0 ∧ (Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)).toReal < 0 := by
        have := oangle_triangle_sign_consistent A B C h_nd;
        grind;
      have := linear_independent_rotated_vectors_variant ( B -ᵥ A ) ( - ( ( positiveOrientation.oangle ( B -ᵥ A ) ( C -ᵥ A ) ).toReal ) / 3 ) ( - ( ( positiveOrientation.oangle ( C -ᵥ B ) ( A -ᵥ B ) ).toReal ) / 3 ) ?_ ?_ ?_ ?_ <;> simp_all +decide [ div_eq_mul_inv ];
      · convert this using 2 ; norm_num [ trisectorVector ];
        congr;
        rw [ show ( ∡ A B C : Real.Angle ) = Real.Angle.toReal ( - ( positiveOrientation.oangle ( C -ᵥ B ) ( A -ᵥ B ) ) ) from ?_ ] ; norm_num ; ring;
        · field_simp;
          rw [ toReal_neg_eq_neg_toReal ];
          aesop;
          linarith [ Real.pi_pos ];
        · simp +decide [ EuclideanGeometry.angle, oangle ];
          exact?;
      · rintro rfl; simp_all +decide [ NondegenerateTriangle ];
      · exact mul_neg_of_neg_of_pos h_neg.1 ( by norm_num );
      · exact mul_neg_of_neg_of_pos h_neg.2 ( by norm_num );
      · linarith [ Real.pi_pos, show ( positiveOrientation.oangle ( B -ᵥ A ) ( C -ᵥ A ) |> Real.Angle.toReal ) ≥ -Real.pi from by linarith [ Real.pi_pos, Real.Angle.neg_pi_lt_toReal ( positiveOrientation.oangle ( B -ᵥ A ) ( C -ᵥ A ) ) ], show ( positiveOrientation.oangle ( C -ᵥ B ) ( A -ᵥ B ) |> Real.Angle.toReal ) ≥ -Real.pi from by linarith [ Real.pi_pos, Real.Angle.neg_pi_lt_toReal ( positiveOrientation.oangle ( C -ᵥ B ) ( A -ᵥ B ) ) ] ]

/-
Two lines in a 2D plane with linearly independent direction vectors intersect at a unique point.
-/
lemma lines_intersect_unique_of_linearIndependent (p1 p2 : P) (v1 v2 : V)
  (h_indep : LinearIndependent ℝ ![v1, v2]) :
  ∃! p, p ∈ AffineSubspace.mk' p1 (Submodule.span ℝ {v1}) ∧
        p ∈ AffineSubspace.mk' p2 (Submodule.span ℝ {v2}) := by
          -- Since the dimension of V is 2 and v1, v2 are linearly independent, they form a basis. Thus any vector (specifically p2 - p1) can be written uniquely as a linear combination of v1 and v2.
          have h_basis : ∀ (x : V), ∃! (c : Fin 2 → ℝ), x = c 0 • v1 + c 1 • v2 := by
            have h_basis : ∀ (x : V), ∃ (c : Fin 2 → ℝ), x = c 0 • v1 + c 1 • v2 := by
              have h_basis : Submodule.span ℝ {v1, v2} = ⊤ := by
                have h_basis : FiniteDimensional ℝ V := by
                  exact FiniteDimensional.of_finrank_pos ( by linarith [ Fact.out ( p := Module.finrank ℝ V = 2 ) ] );
                have h_basis : Module.finrank ℝ (Submodule.span ℝ {v1, v2}) = 2 := by
                  convert finrank_span_eq_card h_indep;
                  · aesop;
                  · aesop;
                  · aesop;
                exact Submodule.eq_top_of_finrank_eq ( by simp +decide [ h_basis, ( Fact.out : Module.finrank ℝ V = 2 ) ] );
              intro x; have := Submodule.mem_span_pair.mp ( h_basis.symm ▸ Submodule.mem_top : x ∈ Submodule.span ℝ { v1, v2 } ) ; aesop;
              exact ⟨ fun i => if i = 0 then w else w_1, rfl ⟩;
            intro x
            obtain ⟨c, hc⟩ := h_basis x
            use c
            aesop;
            rw [ Fintype.linearIndependent_iff ] at h_indep;
            ext i; specialize h_indep ( fun i => c i - y i ) ( by simpa [ sub_smul ] using sub_eq_zero.2 a ) i; fin_cases i <;> simp_all +decide [ sub_eq_iff_eq_add ] ;
          obtain ⟨ c, hc1, hc2 ⟩ := h_basis ( p2 -ᵥ p1 );
          refine' ⟨ c 0 • v1 +ᵥ p1, _, _ ⟩ <;> simp +decide [ *, AffineSubspace.mem_mk' ];
          · simp +decide [ hc1, Submodule.mem_span_singleton ];
            refine' ⟨ -c 1, _ ⟩ ; simp +decide [ hc1, vadd_vsub_assoc ];
            rw [ show p1 -ᵥ p2 = - ( p2 -ᵥ p1 ) by rw [ neg_vsub_eq_vsub_rev ], hc1 ] ; abel_nf;
          · intro y hy1 hy2
            obtain ⟨a, ha⟩ : ∃ a : ℝ, y -ᵥ p1 = a • v1 := by
              exact Submodule.mem_span_singleton.mp hy1 |> fun ⟨ a, ha ⟩ => ⟨ a, ha.symm ⟩
            obtain ⟨b, hb⟩ : ∃ b : ℝ, y -ᵥ p2 = b • v2 := by
              rw [ Submodule.mem_span_singleton ] at hy2 ; tauto
            have h_eq : a • v1 - b • v2 = p2 -ᵥ p1 := by
              rw [ ← ha, ← hb, vsub_sub_vsub_cancel_left ]
            have h_comb : a = c 0 ∧ b = -c 1 := by
              have := hc2 ( fun i => if i = 0 then a else -b ) ?_ <;> aesop;
              exact h_eq.symm ▸ by abel1;
            aesop;
            rw [ ← ha, vsub_vadd ]

/-
If $\triangle ABC$ and $\triangle A'B'C'$ are similar, then their Morley triangles are similar. In particular, the vertices of the Morley triangle of the image are the images of the vertices of the Morley triangle.
-/
theorem morley_triangle_similarity_invariance (f : Similarity P) (A B C : P)
  (h_nd : NondegenerateTriangle A B C) :
  let (P, Q, R) := morleyTriangle A B C
  let (P', Q', R') := morleyTriangle (f A) (f B) (f C)
  P' = f P ∧ Q' = f Q ∧ R' = f R := by
    apply And.intro;
    · rw [ similarity_map_lineIntersection ];
      · rw [ similarity_map_trisectorVector, similarity_map_trisectorVector ];
        · unfold NondegenerateTriangle at *; aesop;
          simp_all +decide [ collinear_iff_exists_forall_eq_smul_vadd ];
          rcases a with ⟨ p₀, v, ⟨ r₁, hr₁ ⟩, ⟨ r₂, hr₂ ⟩, ⟨ r₃, hr₃ ⟩ ⟩ ; exact h_nd p₀ v r₃ hr₃ r₂ hr₂ r₁ hr₁;
        · unfold NondegenerateTriangle at *; aesop;
          rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
          aesop;
      · apply lines_intersect_unique_of_linearIndependent;
        apply trisector_vectors_linear_independent;
        unfold NondegenerateTriangle at *; aesop;
        rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
        aesop;
    · constructor <;> rw [ similarity_map_lineIntersection ];
      · rw [ similarity_map_trisectorVector, similarity_map_trisectorVector ];
        · unfold NondegenerateTriangle at *; aesop;
          rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
          aesop;
        · unfold NondegenerateTriangle at *; aesop;
          rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
          aesop;
      · apply_rules [ lines_intersect_unique_of_linearIndependent ];
        convert trisector_vectors_linear_independent C A B ( by
          unfold NondegenerateTriangle at *; aesop;
          rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
          aesop ) using 1;
      · congr! 1;
        · exact?;
        · convert similarity_map_trisectorVector f B A C _ |> Eq.symm using 1;
          unfold NondegenerateTriangle at *; aesop;
          exact h_nd ( by rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *; aesop );
      · have := lines_intersect_unique_of_linearIndependent A B ( trisectorVector A B C ) ( trisectorVector B A C ) ( trisector_vectors_linear_independent A B C h_nd );
        exact this

/-
There exists an equilateral triangle with side length 1 and positive orientation.
-/
lemma exists_equilateral_triangle_with_orientation :
  ∃ (P_pt Q R : P), isEquilateral P_pt Q R ∧ dist P_pt Q = 1 ∧
  Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (↑(Real.pi / 3) : Real.Angle) := by
    obtain ⟨ v, hv ⟩ : ∃ v : V, ‖v‖ = 1 := by
      field_simp;
      -- Since V is a Hilbert space with dimension 2, it is nontrivial.
      have h_nontrivial : Nontrivial V := by
        exact Module.nontrivial_of_finrank_pos ( by linarith [ Fact.out ( p := Module.finrank ℝ V = 2 ) ] );
      obtain ⟨ v, hv ⟩ := exists_ne ( 0 : V ) ; exact ⟨ ‖v‖⁻¹ • v, by simp +decide [ norm_smul, hv ] ⟩ ;
    use Classical.arbitrary P, v +ᵥ Classical.arbitrary P, (Orientation.rotation Module.Oriented.positiveOrientation (↑(Real.pi / 3)) v) +ᵥ Classical.arbitrary P;
    aesop;
    · unfold isEquilateral;
      simp +decide [ dist_eq_norm', hv ];
      rw [ eq_comm, norm_sub_rev ];
      simp +decide [ hv, norm_sub_rev, inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq ];
      rw [ @norm_sub_rev ];
      rw [ @norm_sub_rev, @norm_eq_sqrt_real_inner ];
      simp +decide [ inner_sub_left, inner_sub_right, hv ];
      norm_num [ inner_self_eq_norm_sq_to_K, hv ];
      rw [ real_inner_comm ] ; ring;
      rw [ Orientation.rotation_apply ] ; norm_num [ hv, inner_self_eq_norm_sq_to_K ] ; ring;
      norm_num [ mul_div, inner_add_right, inner_smul_right, hv ];
      norm_num [ real_inner_self_eq_norm_sq, hv ];
    · rw [ Orientation.oangle_rotation_self_right ];
      aesop

/-
The point P lies on the trisector of B adjacent to BC.
-/
lemma conway_P_on_trisector_B (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ))
  (h_gap_P : angle (conwayVertexB R P_pt a b c) P_pt (conwayVertexC P_pt Q a b c) = conwayLargeAngleP a)
  (h_gap_Q : angle (conwayVertexC P_pt Q a b c) Q (conwayVertexA Q R a b c) = conwayLargeAngleQ b)
  (h_gap_R : angle (conwayVertexA Q R a b c) R (conwayVertexB R P_pt a b c) = conwayLargeAngleR c) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let B := conwayConstructedVertexB P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  P_pt ∈ AffineSubspace.mk' B (Submodule.span ℝ {trisectorVector B C A}) := by
    let A := conwayConstructedVertexA P_pt Q R a b c
    let B := conwayConstructedVertexB P_pt Q R a b c
    let C := conwayConstructedVertexC P_pt Q R a b c
    have h1 : Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (P_pt -ᵥ B) = (b : Real.Angle) := by
      -- By definition of $conwayVertexB$, we know that $P_pt$ lies on the trisector of angle $B$ in triangle $ABC$ because $P_pt$ is obtained by rotating $C - B$ by $-b$.
      have hP_trisector : (Orientation.oangle Module.Oriented.positiveOrientation (P_pt -ᵥ B) (C -ᵥ B) : Real.Angle) = -b := by
        apply_rules [ conway_oangle_P_B_C ];
      rw [ ← neg_inj, ← hP_trisector, Orientation.oangle_rev ];
      norm_num
    have h2 : Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (trisectorVector B C A) = (b : Real.Angle) := by
      have h2 : (Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) ((Orientation.rotation Module.Oriented.positiveOrientation (↑((Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)).toReal / 3) : Real.Angle) (C -ᵥ B)) : V)) = (↑((Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)).toReal / 3) : Real.Angle) := by
        by_cases h : C -ᵥ B = 0 <;> simp +decide [ h ];
      have h3 : (Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)).toReal = 3 * b := by
        have := conway_oangle_C_B_A P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt;
        aesop;
        rw [ Real.Angle.toReal_coe_eq_self_iff ];
        constructor <;> linarith;
      convert h2 using 1;
      rw [ h3, mul_div_cancel_left₀ _ ( by norm_num ) ]
    have h3 : Orientation.oangle Module.Oriented.positiveOrientation (trisectorVector B C A) (P_pt -ᵥ B) = 0 := by
      have h3 : Orientation.oangle Module.Oriented.positiveOrientation (trisectorVector B C A) (P_pt -ᵥ B) = -b + b := by
        have h3 : Orientation.oangle Module.Oriented.positiveOrientation (trisectorVector B C A) (P_pt -ᵥ B) = Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (P_pt -ᵥ B) - Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (trisectorVector B C A) := by
          rw [ eq_sub_iff_add_eq', Orientation.oangle_add ];
          · rw [ eq_comm ] at h1 ; aesop;
            rw [ Real.Angle.coe_eq_zero_iff ] at h1 ; aesop;
            rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
          · rw [ eq_comm ] at h2 ; aesop;
            rw [ Real.Angle.coe_eq_zero_iff ] at h2 ; aesop;
            rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
          · intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
            erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] at h1 ; obtain ⟨ k, hk ⟩ := h1 ; rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos ]
        aesop;
      aesop
    rw [ Orientation.oangle_eq_zero_iff_angle_eq_zero ] at h3;
    · rw [ InnerProductGeometry.angle_eq_zero_iff ] at h3;
      aesop;
    · rw [ eq_comm ] at h2 ; aesop;
      rw [ Real.Angle.coe_eq_zero_iff ] at h2 ; aesop;
      rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
    · intro h; simp_all +decide [ sub_eq_iff_eq_add ];
      erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] at h1 ; obtain ⟨ k, hk ⟩ := h1 ; rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos ]

/-
The point P lies on the trisector of C adjacent to CB.
-/
lemma conway_P_on_trisector_C (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ))
  (h_gap_P : angle (conwayVertexB R P_pt a b c) P_pt (conwayVertexC P_pt Q a b c) = conwayLargeAngleP a)
  (h_gap_Q : angle (conwayVertexC P_pt Q a b c) Q (conwayVertexA Q R a b c) = conwayLargeAngleQ b)
  (h_gap_R : angle (conwayVertexA Q R a b c) R (conwayVertexB R P_pt a b c) = conwayLargeAngleR c) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let B := conwayConstructedVertexB P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  P_pt ∈ AffineSubspace.mk' C (Submodule.span ℝ {trisectorVector C B A}) := by
    let A := conwayConstructedVertexA P_pt Q R a b c
    let B := conwayConstructedVertexB P_pt Q R a b c
    let C := conwayConstructedVertexC P_pt Q R a b c
    have h1 : Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ C) (P_pt -ᵥ C) = (-c : Real.Angle) := by
      apply_rules [ conway_oangle_B_C_P ]
    have h2 : Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ C) (trisectorVector C B A) = (-c : Real.Angle) := by
      rw [ show trisectorVector C B A = Orientation.rotation Module.Oriented.positiveOrientation ( ↑ ( ( positiveOrientation.oangle ( B -ᵥ C ) ( A -ᵥ C ) |> Real.Angle.toReal ) / 3 ) ) ( B -ᵥ C ) from rfl ];
      -- From `conway_oangle_A_C_B`, we have `oangle (A - C) (B - C) = 3c`. So `oangle (B - C) (A - C) = -3c`.
      have h3 : (Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ C) (A -ᵥ C)).toReal = -3 * c := by
        have h_angle_BCA : (Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ C) (B -ᵥ C)) = (↑(3 * c) : Real.Angle) := by
          apply_rules [ conway_oangle_A_C_B ];
        -- Since the orientation is positive, the oangle from (A - C) to (B - C) is the negative of the oangle from (B - C) to (A - C).
        have h_neg : (Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ C) (B -ᵥ C)) = - (Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ C) (A -ᵥ C)) := by
          rw [ ← Orientation.oangle_rev ];
        rw [ h_neg ] at h_angle_BCA;
        rw [ neg_eq_iff_eq_neg ] at h_angle_BCA ; aesop;
        erw [ Real.Angle.toReal_coe_eq_self_iff ];
        constructor <;> linarith;
      by_cases h : B -ᵥ C = 0 <;> simp +decide [ h ] at h3 ⊢;
      · linarith;
      · simp +decide [ h3, neg_div ]
    have h3 : Orientation.oangle Module.Oriented.positiveOrientation (trisectorVector C B A) (P_pt -ᵥ C) = 0 := by
      have h3 : Orientation.oangle Module.Oriented.positiveOrientation (trisectorVector C B A) (P_pt -ᵥ C) = Orientation.oangle Module.Oriented.positiveOrientation (trisectorVector C B A) (B -ᵥ C) + Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ C) (P_pt -ᵥ C) := by
        by_cases h : trisectorVector C B A = 0 <;> by_cases h' : B -ᵥ C = 0 <;> simp +decide [ *, add_comm ];
        · aesop;
        · aesop;
          rw [ Real.Angle.coe_eq_zero_iff ] at h1 ; aesop;
          rcases w with ⟨ w | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
        · rw [ ← h1, ← Orientation.oangle_add ];
          · exact h;
          · exact h';
          · intro h''; simp_all +decide [ sub_eq_zero ] ;
            rw [ Real.Angle.coe_eq_zero_iff ] at h1;
            obtain ⟨ n, hn ⟩ := h1; rcases n with ⟨ _ | n ⟩ <;> norm_num at hn <;> nlinarith [ Real.pi_pos ] ;
      rw [ h3, h1, ← h2, Orientation.oangle_rev ] ; norm_num
    have h4 : ∃ k : ℝ, P_pt -ᵥ C = k • trisectorVector C B A := by
      have h_nonzero : trisectorVector C B A ≠ 0 := by
        intro h; simp_all +decide [ trisectorVector ] ;
        rw [ Real.Angle.coe_eq_zero_iff ] at h1 ; aesop;
        rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ]
      rw [ Orientation.oangle_eq_zero_iff_sameRay ] at h3;
      rcases h3 with ( h | h | ⟨ k, hk ⟩ ) <;> simp_all +decide [ eq_comm ];
      · exact ⟨ 0, by simp +decide [ ← h ] ⟩;
      · rcases hk with ⟨ hk₁, x, hx₁, hx₂ ⟩;
        exact ⟨ x⁻¹ * k, by rw [ MulAction.mul_smul, hx₂, smul_smul, inv_mul_cancel₀ hx₁.ne', one_smul ] ⟩;
    aesop

/-
The constructed triangle in Conway's proof is nondegenerate.
-/
lemma conway_constructed_triangle_nondegenerate (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ))
  (h_gap_P : angle (conwayVertexB R P_pt a b c) P_pt (conwayVertexC P_pt Q a b c) = conwayLargeAngleP a)
  (h_gap_Q : angle (conwayVertexC P_pt Q a b c) Q (conwayVertexA Q R a b c) = conwayLargeAngleQ b)
  (h_gap_R : angle (conwayVertexA Q R a b c) R (conwayVertexB R P_pt a b c) = conwayLargeAngleR c) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let B := conwayConstructedVertexB P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  NondegenerateTriangle A B C := by
    unfold NondegenerateTriangle;
    aesop;
    -- Since $A$, $B$, and $C$ are collinear, the area of $\triangle ABC$ is zero.
    have h_area_zero : (Orientation.areaForm Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)) = 0 := by
      rw [ collinear_iff_exists_forall_eq_smul_vadd ] at a_1;
      aesop;
    have h_sin_zero : Real.sin (Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)).toReal = 0 := by
      rw [ sin_oangle_eq_areaForm_div_norm_mul_norm ] ; aesop;
    have h_angle_zero : (Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)).toReal = 3 * a := by
      convert congr_arg Real.Angle.toReal ( conway_oangle_B_A_C_final P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation ) using 1;
      norm_num [ Real.Angle.toReal ];
      exact Eq.symm ( Real.Angle.toReal_coe_eq_self_iff.mpr ⟨ by linarith, by linarith ⟩ );
    exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by linarith ) ( by linarith ) ) ( h_angle_zero ▸ h_sin_zero )

/-
The point P in Conway's construction is the intersection of the adjacent trisectors of B and C.
-/
theorem conway_P_is_morley_vertex (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ))
  (h_gap_P : angle (conwayVertexB R P_pt a b c) P_pt (conwayVertexC P_pt Q a b c) = conwayLargeAngleP a)
  (h_gap_Q : angle (conwayVertexC P_pt Q a b c) Q (conwayVertexA Q R a b c) = conwayLargeAngleQ b)
  (h_gap_R : angle (conwayVertexA Q R a b c) R (conwayVertexB R P_pt a b c) = conwayLargeAngleR c) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let B := conwayConstructedVertexB P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  P_pt = lineIntersection B (trisectorVector B C A) C (trisectorVector C B A) := by
    have h_trisector_vectors_linear_independent : LinearIndependent ℝ ![trisectorVector (conwayConstructedVertexB P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c) (conwayConstructedVertexA P_pt Q R a b c), trisectorVector (conwayConstructedVertexC P_pt Q R a b c) (conwayConstructedVertexB P_pt Q R a b c) (conwayConstructedVertexA P_pt Q R a b c)] := by
      apply trisector_vectors_linear_independent;
      apply conway_constructed_triangle_nondegenerate;
      all_goals repeat' assumption;
      · unfold isEquilateral at *; aesop;
      · rw [ ← h_side, h_equilateral.1 ];
      · linarith;
      · have := equilateral_oangle_cyclic P_pt Q R h_equilateral; aesop;
    apply Eq.symm;
    apply lineIntersection_eq;
    · convert conway_P_on_trisector_B P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation h_gap_P h_gap_Q h_gap_R;
    · convert conway_P_on_trisector_C P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation h_gap_P h_gap_Q h_gap_R using 1;
    · have := lines_intersect_unique_of_linearIndependent (conwayConstructedVertexB P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c) (trisectorVector (conwayConstructedVertexB P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c) (conwayConstructedVertexA P_pt Q R a b c)) (trisectorVector (conwayConstructedVertexC P_pt Q R a b c) (conwayConstructedVertexB P_pt Q R a b c) (conwayConstructedVertexA P_pt Q R a b c)) h_trisector_vectors_linear_independent;
      exact fun q hq₁ hq₂ => this.unique ⟨ hq₁, hq₂ ⟩ ⟨ conway_P_on_trisector_B P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation h_gap_P h_gap_Q h_gap_R, conway_P_on_trisector_C P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation h_gap_P h_gap_Q h_gap_R ⟩

/-
If a point lies on two lines with linearly independent direction vectors, it is the unique intersection point returned by `lineIntersection`.
-/
lemma lineIntersection_unique_of_linearIndependent {p1 p2 : P} {v1 v2 : V} {p : P}
  (h1 : p ∈ AffineSubspace.mk' p1 (Submodule.span ℝ {v1}))
  (h2 : p ∈ AffineSubspace.mk' p2 (Submodule.span ℝ {v2}))
  (h_indep : LinearIndependent ℝ ![v1, v2]) :
  lineIntersection p1 v1 p2 v2 = p := by
    apply lineIntersection_eq;
    · exact h1;
    · exact h2;
    · -- By definition of `lines_intersect_unique_of_linearIndependent`, if a point lies on two lines with linearly independent direction vectors, it is the unique intersection point returned by `lineIntersection`.
      have h_unique : ∀ (q : P), q ∈ AffineSubspace.mk' p1 (Submodule.span ℝ {v1}) → q ∈ AffineSubspace.mk' p2 (Submodule.span ℝ {v2}) → q = p := by
        intro q hq1 hq2
        have h_unique : ∃! p, p ∈ AffineSubspace.mk' p1 (Submodule.span ℝ {v1}) ∧ p ∈ AffineSubspace.mk' p2 (Submodule.span ℝ {v2}) := by
          exact?
        exact h_unique.unique ⟨ hq1, hq2 ⟩ ⟨ h1, h2 ⟩;
      exact h_unique

/-
The point Q lies on the trisector of C adjacent to CA.
-/
lemma conway_Q_on_trisector_C (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ))
  (h_gap_P : angle (conwayVertexB R P_pt a b c) P_pt (conwayVertexC P_pt Q a b c) = conwayLargeAngleP a)
  (h_gap_Q : angle (conwayVertexC P_pt Q a b c) Q (conwayVertexA Q R a b c) = conwayLargeAngleQ b)
  (h_gap_R : angle (conwayVertexA Q R a b c) R (conwayVertexB R P_pt a b c) = conwayLargeAngleR c) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let B := conwayConstructedVertexB P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  Q ∈ AffineSubspace.mk' C (Submodule.span ℝ {trisectorVector C A B}) := by
    -- By definition of trisectorVector, we have:
    set A := conwayConstructedVertexA P_pt Q R a b c
    set B := conwayConstructedVertexB P_pt Q R a b c
    set C := conwayConstructedVertexC P_pt Q R a b c
    simp [trisectorVector];
    have hQ_on_trisector_C : positiveOrientation.oangle (A -ᵥ C) (Q -ᵥ C) = c := by
      have h_oangle_A_C_Q : positiveOrientation.oangle (Q -ᵥ C) (A -ᵥ C) = -(c : Real.Angle) := by
        convert conway_oangle_Q_C_A P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation using 1;
      rw [ ← neg_neg ( c : Real.Angle ), ← h_oangle_A_C_Q, Orientation.oangle_rev ];
    have hQ_on_trisector_C : positiveOrientation.oangle (A -ᵥ C) (positiveOrientation.rotation (↑((positiveOrientation.oangle (A -ᵥ C) (B -ᵥ C)).toReal / 3)) (A -ᵥ C)) = ↑c := by
      have hQ_on_trisector_C : positiveOrientation.oangle (A -ᵥ C) (B -ᵥ C) = ↑(3 * c) := by
        apply conway_oangle_A_C_B P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation;
      rw [ hQ_on_trisector_C, Real.Angle.toReal_coe ];
      rw [ show toIocMod two_pi_pos ( -Real.pi ) ( 3 * c ) = 3 * c by
            rw [ toIocMod_eq_iff ] ; norm_num ; constructor <;> linarith [ Real.pi_pos ] ; ] ; norm_num [ mul_div_cancel_left₀ ];
      rw [ Orientation.oangle_rotation_self_right ];
      intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
      rw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] at hQ_on_trisector_C ; aesop;
      rcases w with ⟨ w | w ⟩ <;> norm_num at h_1 <;> nlinarith [ Real.pi_pos ];
    have hQ_on_trisector_C : positiveOrientation.oangle (positiveOrientation.rotation (↑((positiveOrientation.oangle (A -ᵥ C) (B -ᵥ C)).toReal / 3)) (A -ᵥ C)) (Q -ᵥ C) = 0 := by
      by_cases h : A -ᵥ C = 0 <;> simp_all +decide;
      by_cases h : Q -ᵥ C = 0 <;> simp_all +decide;
    rw [ Submodule.mem_span_singleton ];
    rw [ Orientation.oangle_eq_zero_iff_angle_eq_zero ] at hQ_on_trisector_C;
    · rw [ InnerProductGeometry.angle_eq_zero_iff ] at hQ_on_trisector_C;
      exact ⟨ hQ_on_trisector_C.2.choose, hQ_on_trisector_C.2.choose_spec.2.symm ⟩;
    · intro h;
      simp_all +decide [ sub_eq_zero ];
      rw [ eq_comm, Real.Angle.coe_eq_zero_iff ] at hQ_on_trisector_C ; aesop;
      rcases w with ⟨ w | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
    · intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
      rw [ eq_comm ] at * ; aesop;
      rw [ Real.Angle.coe_eq_zero_iff ] at hQ_on_trisector_C ; aesop;
      rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ]

/-
The point R lies on the trisector of A adjacent to AB.
-/
lemma conway_R_on_trisector_A (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ))
  (h_gap_P : angle (conwayVertexB R P_pt a b c) P_pt (conwayVertexC P_pt Q a b c) = conwayLargeAngleP a)
  (h_gap_Q : angle (conwayVertexC P_pt Q a b c) Q (conwayVertexA Q R a b c) = conwayLargeAngleQ b)
  (h_gap_R : angle (conwayVertexA Q R a b c) R (conwayVertexB R P_pt a b c) = conwayLargeAngleR c) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let B := conwayConstructedVertexB P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  R ∈ AffineSubspace.mk' A (Submodule.span ℝ {trisectorVector A B C}) := by
    have := conway_oangle_R_A_B P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation;
    have := conway_oangle_B_A_C P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation; simp_all +decide [ neg_div, mul_div_cancel₀ ] ;
    rw [ Submodule.mem_span_singleton ];
    have h_oangle_zero : Orientation.oangle Module.Oriented.positiveOrientation (trisectorVector (conwayConstructedVertexA P_pt Q R a b c) (conwayConstructedVertexB P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c)) (R -ᵥ conwayConstructedVertexA P_pt Q R a b c) = 0 := by
      have h_oangle_zero : Orientation.oangle Module.Oriented.positiveOrientation (trisectorVector (conwayConstructedVertexA P_pt Q R a b c) (conwayConstructedVertexB P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c)) (conwayVertexB R P_pt a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c) = -a := by
        have h_oangle_zero : Orientation.oangle Module.Oriented.positiveOrientation (conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c) (trisectorVector (conwayConstructedVertexA P_pt Q R a b c) (conwayConstructedVertexB P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c)) = a := by
          have h_oangle_zero : trisectorVector (conwayConstructedVertexA P_pt Q R a b c) (conwayConstructedVertexB P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c) = (Orientation.rotation Module.Oriented.positiveOrientation (a : Real.Angle)) (conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c) := by
            have h_oangle_zero : (Orientation.oangle Module.Oriented.positiveOrientation (conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c)).toReal = 3 * a := by
              rw [ this, Real.Angle.toReal_coe_eq_self_iff ];
              constructor <;> linarith;
            simp +decide [ trisectorVector, h_oangle_zero ];
            rw [ show ( ∡ ( conwayConstructedVertexB P_pt Q R a b c ) ( conwayConstructedVertexA P_pt Q R a b c ) ( conwayConstructedVertexC P_pt Q R a b c ) ).toReal / 3 = a by linarith! ];
          rw [ h_oangle_zero, Orientation.oangle ];
          rw [ Complex.arg ];
          simp +decide [ Complex.ext_iff, Orientation.rotation ];
          norm_cast ; norm_num [ Complex.normSq, Complex.sq_norm ];
          rw [ if_pos ];
          · norm_num [ Complex.normSq, Complex.norm_def ];
            norm_cast ; norm_num [ Complex.normSq, Complex.sq_norm ];
            rw [ show ( cos a * ‖conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c‖ ^ 2 * ( cos a * ‖conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c‖ ^ 2 ) + sin a * ‖conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c‖ ^ 2 * ( sin a * ‖conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c‖ ^ 2 ) ) = ( ‖conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c‖ ^ 2 ) ^ 2 by nlinarith only [ Real.sin_sq_add_cos_sq a ] ] ; norm_num [ Real.sin_arcsin, Real.cos_arcsin, h_a_pos.le, h_a_lt.le ];
            by_cases h : ‖conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c‖ = 0 <;> simp_all +decide [ mul_div_cancel_left₀ ];
            · rw [ eq_comm ] at this ; aesop;
              rw [ Real.Angle.coe_eq_zero_iff ] at this ; aesop;
              rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at h_1 <;> nlinarith [ Real.pi_pos ];
            · rw [ Real.arcsin_sin ] <;> norm_cast <;> linarith;
          · exact mul_nonneg ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith, by linarith ⟩ ) ( sq_nonneg _ );
        rw [ ← neg_eq_iff_eq_neg, ← h_oangle_zero, Orientation.oangle_rev ];
        simp +decide [ conwayConstructedVertexA, conwayConstructedVertexB, conwayConstructedVertexC, conwayVertexB, conwayVertexC ];
      have h_oangle_zero : Orientation.oangle Module.Oriented.positiveOrientation (conwayVertexB R P_pt a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c) (R -ᵥ conwayConstructedVertexA P_pt Q R a b c) = a := by
        have h_oangle_zero : Orientation.oangle Module.Oriented.positiveOrientation (R -ᵥ conwayVertexA Q R a b c) (conwayVertexB R P_pt a b c -ᵥ conwayVertexA Q R a b c) = -a := by
          assumption;
        rw [ ← neg_inj, ← h_oangle_zero, ← Orientation.oangle_rev ];
        unfold conwayConstructedVertexA conwayVertexA; aesop;
      have h_oangle_zero : Orientation.oangle Module.Oriented.positiveOrientation (trisectorVector (conwayConstructedVertexA P_pt Q R a b c) (conwayConstructedVertexB P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c)) (R -ᵥ conwayConstructedVertexA P_pt Q R a b c) = Orientation.oangle Module.Oriented.positiveOrientation (trisectorVector (conwayConstructedVertexA P_pt Q R a b c) (conwayConstructedVertexB P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c)) (conwayVertexB R P_pt a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c) + Orientation.oangle Module.Oriented.positiveOrientation (conwayVertexB R P_pt a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c) (R -ᵥ conwayConstructedVertexA P_pt Q R a b c) := by
        rw [ ← Orientation.oangle_add ];
        · intro h;
          rw [ h ] at ‹positiveOrientation.oangle ( trisectorVector ( conwayConstructedVertexA P_pt Q R a b c ) ( conwayConstructedVertexB P_pt Q R a b c ) ( conwayConstructedVertexC P_pt Q R a b c ) ) ( conwayVertexB R P_pt a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c ) = -↑a›; simp_all +decide [ Real.Angle ] ;
          rw [ Real.Angle.coe_eq_zero_iff ] at * ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
        · intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
          exact absurd h_oangle_zero ( by rw [ Real.Angle.coe_eq_zero_iff ] ; exact by rintro ⟨ k, hk ⟩ ; rcases k with ⟨ _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos ] );
        · rw [ Ne.eq_def, vsub_eq_zero_iff_eq ];
          intro h;
          rw [ eq_comm ] at h;
          simp_all +decide [ conwayConstructedVertexA ];
          rw [ Real.Angle.coe_eq_zero_iff ] at * ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
      grind;
    rw [ Orientation.oangle_eq_zero_iff_sameRay ] at h_oangle_zero;
    rcases h_oangle_zero with ( h | h | ⟨ r, hr, hr' ⟩ );
    · simp_all +decide [ trisectorVector ];
      rw [ eq_comm, Real.Angle.coe_eq_zero_iff ] at this ; aesop;
      rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at h_1 <;> nlinarith only [ h_1, h_a_pos, h_b_pos, h_c_pos, h_a_lt, h_b_lt, h_c_lt, Real.pi_pos ];
    · exact ⟨ 0, by simp +decide [ h ] ⟩;
    · refine' ⟨ hr⁻¹ * r, _ ⟩;
      simp_all +decide [ mul_assoc, MulAction.mul_smul, ne_of_gt ]

/-
The point Q lies on the trisector of A adjacent to AC.
-/
lemma conway_Q_on_trisector_A (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ))
  (h_gap_P : angle (conwayVertexB R P_pt a b c) P_pt (conwayVertexC P_pt Q a b c) = conwayLargeAngleP a)
  (h_gap_Q : angle (conwayVertexC P_pt Q a b c) Q (conwayVertexA Q R a b c) = conwayLargeAngleQ b)
  (h_gap_R : angle (conwayVertexA Q R a b c) R (conwayVertexB R P_pt a b c) = conwayLargeAngleR c) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let B := conwayConstructedVertexB P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  Q ∈ AffineSubspace.mk' A (Submodule.span ℝ {trisectorVector A C B}) := by
    field_simp;
    -- By definition of `conway_oangle_C_A_Q`, we know that `oangle (C - A) (Q - A) = -a`.
    have h_oangle_C_A_Q : Orientation.oangle Module.Oriented.positiveOrientation ((conwayConstructedVertexC P_pt Q R a b c) -ᵥ (conwayConstructedVertexA P_pt Q R a b c)) ((Q -ᵥ (conwayConstructedVertexA P_pt Q R a b c))) = (-a : Real.Angle) := by
      convert conway_oangle_C_A_Q P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation using 1;
    have h_oangle_trisectorVector_C_A : Orientation.oangle Module.Oriented.positiveOrientation ((conwayConstructedVertexC P_pt Q R a b c) -ᵥ (conwayConstructedVertexA P_pt Q R a b c)) (trisectorVector (conwayConstructedVertexA P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c) (conwayConstructedVertexB P_pt Q R a b c)) = (-a : Real.Angle) := by
      have h_oangle_trisectorVector_C_A : trisectorVector (conwayConstructedVertexA P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c) (conwayConstructedVertexB P_pt Q R a b c) = Orientation.rotation Module.Oriented.positiveOrientation (-a : Real.Angle) ((conwayConstructedVertexC P_pt Q R a b c) -ᵥ (conwayConstructedVertexA P_pt Q R a b c)) := by
        unfold trisectorVector;
        have h_oangle_B_A_C : Orientation.oangle Module.Oriented.positiveOrientation (conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c) = (3 * a : ℝ) := by
          exact?;
        have h_oangle_trisectorVector_C_A : (Orientation.oangle Module.Oriented.positiveOrientation (conwayConstructedVertexC P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c) (conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c)).toReal = -3 * a := by
          field_simp;
          rw [ Orientation.oangle_rev ];
          rw [ h_oangle_B_A_C, ← Real.Angle.coe_neg, Real.Angle.toReal_coe_eq_self_iff ];
          constructor <;> linarith;
        simp +zetaDelta at *;
        exact congr_arg₂ _ ( by rw [ show ( ∡ ( conwayConstructedVertexC P_pt Q R a b c ) ( conwayConstructedVertexA P_pt Q R a b c ) ( conwayConstructedVertexB P_pt Q R a b c ) ).toReal / 3 = -a by linarith! ] ; norm_num ) rfl;
      rw [ h_oangle_trisectorVector_C_A, Orientation.oangle_rotation_right ];
      · rw [ Orientation.oangle_self, zero_add ];
      · intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
        rw [ Real.Angle.coe_eq_zero_iff ] at h_oangle_C_A_Q ; aesop;
        rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
      · intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
        rw [ Real.Angle.coe_eq_zero_iff ] at h_oangle_C_A_Q ; aesop;
        rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
    have h_oangle_trisectorVector_Q_A : Orientation.oangle Module.Oriented.positiveOrientation (trisectorVector (conwayConstructedVertexA P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c) (conwayConstructedVertexB P_pt Q R a b c)) (Q -ᵥ (conwayConstructedVertexA P_pt Q R a b c)) = 0 := by
      have h_oangle_trisectorVector_Q_A : Orientation.oangle Module.Oriented.positiveOrientation (trisectorVector (conwayConstructedVertexA P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c) (conwayConstructedVertexB P_pt Q R a b c)) (Q -ᵥ (conwayConstructedVertexA P_pt Q R a b c)) = Orientation.oangle Module.Oriented.positiveOrientation (trisectorVector (conwayConstructedVertexA P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c) (conwayConstructedVertexB P_pt Q R a b c)) ((conwayConstructedVertexC P_pt Q R a b c) -ᵥ (conwayConstructedVertexA P_pt Q R a b c)) + Orientation.oangle Module.Oriented.positiveOrientation ((conwayConstructedVertexC P_pt Q R a b c) -ᵥ (conwayConstructedVertexA P_pt Q R a b c)) (Q -ᵥ (conwayConstructedVertexA P_pt Q R a b c)) := by
        rw [ ← Orientation.oangle_add ];
        · intro h; simp_all +decide [ trisectorVector ] ;
          rw [ Real.Angle.coe_eq_zero_iff ] at h_oangle_C_A_Q ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
        · intro h; simp_all +decide [ sub_eq_zero ] ;
          rw [ Real.Angle.coe_eq_zero_iff ] at h_oangle_C_A_Q ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
        · norm_num +zetaDelta at *;
          intro h;
          rw [ eq_comm ] at h;
          simp_all +decide [ conwayConstructedVertexA ];
          rw [ Real.Angle.coe_eq_zero_iff ] at h_oangle_C_A_Q ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
      rw [ h_oangle_trisectorVector_Q_A, h_oangle_C_A_Q ];
      rw [ ← h_oangle_trisectorVector_C_A ];
      rw [ add_comm, Orientation.oangle_rev ] ; norm_num;
    rw [ Orientation.oangle_eq_zero_iff_angle_eq_zero ] at h_oangle_trisectorVector_Q_A;
    · rw [ InnerProductGeometry.angle_eq_zero_iff ] at h_oangle_trisectorVector_Q_A;
      exact h_oangle_trisectorVector_Q_A.2.elim fun r hr => by rw [ AffineSubspace.mem_mk' ] ; exact Submodule.mem_span_singleton.mpr ⟨ r, by simp +decide [ hr.2 ] ⟩ ;
    · intro h;
      simp_all +decide [ trisectorVector ];
      rw [ Real.Angle.coe_eq_zero_iff ] at h_oangle_C_A_Q ; aesop;
      rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
    · rw [ vsub_ne_zero ];
      intro h;
      norm_num [ ← h ] at *;
      rw [ Real.Angle.coe_eq_zero_iff ] at h_oangle_C_A_Q ; aesop;
      rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ]

/-
The point R lies on the trisector of B adjacent to BA.
-/
lemma conway_R_on_trisector_B (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ))
  (h_gap_P : angle (conwayVertexB R P_pt a b c) P_pt (conwayVertexC P_pt Q a b c) = conwayLargeAngleP a)
  (h_gap_Q : angle (conwayVertexC P_pt Q a b c) Q (conwayVertexA Q R a b c) = conwayLargeAngleQ b)
  (h_gap_R : angle (conwayVertexA Q R a b c) R (conwayVertexB R P_pt a b c) = conwayLargeAngleR c) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let B := conwayConstructedVertexB P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  R ∈ AffineSubspace.mk' B (Submodule.span ℝ {trisectorVector B A C}) := by
    have h_rotated : trisectorVector (conwayConstructedVertexB P_pt Q R a b c) (conwayConstructedVertexA P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c) = Orientation.rotation Module.Oriented.positiveOrientation (-(b : Real.Angle)) (conwayConstructedVertexA P_pt Q R a b c -ᵥ conwayConstructedVertexB P_pt Q R a b c) := by
      have h_rotated : (Orientation.oangle Module.Oriented.positiveOrientation (conwayConstructedVertexA P_pt Q R a b c -ᵥ conwayConstructedVertexB P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c -ᵥ conwayConstructedVertexB P_pt Q R a b c)).toReal = -3 * b := by
        have h_oangle : (Orientation.oangle Module.Oriented.positiveOrientation (conwayConstructedVertexA P_pt Q R a b c -ᵥ conwayConstructedVertexB P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c -ᵥ conwayConstructedVertexB P_pt Q R a b c)) = - (↑(3 * b) : Real.Angle) := by
          have := conway_oangle_C_B_A P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation;
          rw [ ← this, Orientation.oangle_rev ];
        aesop;
        erw [ Real.Angle.toReal_coe_eq_self_iff ];
        constructor <;> linarith;
      unfold trisectorVector; aesop;
      rw [ show ( ∡ ( conwayConstructedVertexA P_pt Q R a b c ) ( conwayConstructedVertexB P_pt Q R a b c ) ( conwayConstructedVertexC P_pt Q R a b c ) |> Real.Angle.toReal ) / 3 = -b by linarith! ] ; norm_num;
    have h_collinear_R_Q : let A := conwayConstructedVertexA P_pt Q R a b c; let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c; Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ B) (R -ᵥ B) = -b := by
      apply_rules [ conway_oangle_A_B_R ];
    have h_collinear_R_Q : let A := conwayConstructedVertexA P_pt Q R a b c; let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c; Orientation.oangle Module.Oriented.positiveOrientation (trisectorVector B A C) (R -ᵥ B) = 0 := by
      have h_collinear_R_Q : let A := conwayConstructedVertexA P_pt Q R a b c; let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c; Orientation.oangle Module.Oriented.positiveOrientation (trisectorVector B A C) (A -ᵥ B) = b := by
        aesop;
        rw [ Orientation.oangle_rev, Orientation.oangle_rotation_self_right ];
        · norm_num;
        · intro h;
          simp_all +decide [ sub_eq_zero ];
          rw [ Real.Angle.coe_eq_zero_iff ] at h_collinear_R_Q ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
      have h_collinear_R_Q : let A := conwayConstructedVertexA P_pt Q R a b c; let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c; Orientation.oangle Module.Oriented.positiveOrientation (trisectorVector B A C) (R -ᵥ B) = Orientation.oangle Module.Oriented.positiveOrientation (trisectorVector B A C) (A -ᵥ B) + Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ B) (R -ᵥ B) := by
        field_simp;
        rw [ Orientation.oangle_add ];
        · aesop;
          rw [ Real.Angle.coe_eq_zero_iff ] at h_collinear_R_Q_1 ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
        · intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
          rw [ Real.Angle.coe_eq_zero_iff ] at h_collinear_R_Q ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
        · simp +zetaDelta at *;
          intro h;
          rw [ eq_comm ] at h;
          simp_all +decide [ trisectorVector ];
          rw [ Real.Angle.coe_eq_zero_iff ] at h_collinear_R_Q ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
      aesop;
    rw [ @Orientation.oangle_eq_zero_iff_sameRay ] at h_collinear_R_Q;
    cases h_collinear_R_Q <;> simp_all +decide [ Submodule.mem_span_singleton ];
    · rw [ eq_comm ] at h_rotated ; aesop;
      rw [ Real.Angle.coe_eq_zero_iff ] at h_collinear_R_Q ; aesop;
      rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
    · rcases ‹_› with ( h | ⟨ r₁, hr₁, x, hx, h ⟩ );
      · rw [ eq_comm ] at h;
        simp_all +decide [ conwayConstructedVertexB ];
      · exact ⟨ r₁ / x, by rw [ div_eq_inv_mul, MulAction.mul_smul, h, smul_smul, inv_mul_cancel₀ hx.ne', one_smul ] ⟩

/-
The point Q in Conway's construction is the intersection of the adjacent trisectors of C and A.
-/
theorem conway_Q_is_morley_vertex (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ))
  (h_gap_P : angle (conwayVertexB R P_pt a b c) P_pt (conwayVertexC P_pt Q a b c) = conwayLargeAngleP a)
  (h_gap_Q : angle (conwayVertexC P_pt Q a b c) Q (conwayVertexA Q R a b c) = conwayLargeAngleQ b)
  (h_gap_R : angle (conwayVertexA Q R a b c) R (conwayVertexB R P_pt a b c) = conwayLargeAngleR c) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let B := conwayConstructedVertexB P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  Q = lineIntersection C (trisectorVector C A B) A (trisectorVector A C B) := by
    apply Eq.symm;
    apply lineIntersection_unique_of_linearIndependent;
    · exact?;
    · convert conway_Q_on_trisector_A P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation h_gap_P h_gap_Q h_gap_R using 1;
    · apply trisector_vectors_linear_independent;
      unfold NondegenerateTriangle;
      intro h;
      have h_contra : ∃ A B C : P, NondegenerateTriangle A B C ∧ Collinear ℝ ({ A, B, C } : Set P) := by
        use conwayConstructedVertexA P_pt Q R a b c, conwayConstructedVertexB P_pt Q R a b c, conwayConstructedVertexC P_pt Q R a b c;
        apply And.intro;
        · apply_rules [ conway_constructed_triangle_nondegenerate ];
        · rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
          exact ⟨ h.choose, h.choose_spec.choose, fun p hp => h.choose_spec.choose_spec p <| by aesop ⟩;
      exact h_contra.elim fun A hA => hA.elim fun B hB => hB.elim fun C hC => hC.1 hC.2 |> fun h => by tauto;

/-
The point R in Conway's construction is the intersection of the adjacent trisectors of A and B.
-/
theorem conway_R_is_morley_vertex (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ))
  (h_gap_P : angle (conwayVertexB R P_pt a b c) P_pt (conwayVertexC P_pt Q a b c) = conwayLargeAngleP a)
  (h_gap_Q : angle (conwayVertexC P_pt Q a b c) Q (conwayVertexA Q R a b c) = conwayLargeAngleQ b)
  (h_gap_R : angle (conwayVertexA Q R a b c) R (conwayVertexB R P_pt a b c) = conwayLargeAngleR c) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let B := conwayConstructedVertexB P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  R = lineIntersection A (trisectorVector A B C) B (trisectorVector B A C) := by
    refine' Eq.symm _;
    apply lineIntersection_unique_of_linearIndependent;
    · exact?;
    · apply conway_R_on_trisector_B;
      all_goals assumption;
    · apply trisector_vectors_linear_independent;
      apply conway_constructed_triangle_nondegenerate P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation h_gap_P h_gap_Q h_gap_R

/-
The equilateral triangle PQR used in Conway's construction is indeed the Morley triangle of the constructed triangle ABC.
-/
theorem conway_PQR_is_morley (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ))
  (h_gap_P : angle (conwayVertexB R P_pt a b c) P_pt (conwayVertexC P_pt Q a b c) = conwayLargeAngleP a)
  (h_gap_Q : angle (conwayVertexC P_pt Q a b c) Q (conwayVertexA Q R a b c) = conwayLargeAngleQ b)
  (h_gap_R : angle (conwayVertexA Q R a b c) R (conwayVertexB R P_pt a b c) = conwayLargeAngleR c) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let B := conwayConstructedVertexB P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  morleyTriangle A B C = (P_pt, Q, R) := by
    congr! 1;
    · unfold morleyTriangle;
      exact?;
    · congr! 1;
      · convert conway_Q_is_morley_vertex P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation h_gap_P h_gap_Q h_gap_R |> Eq.symm using 1;
      · unfold morleyTriangle; aesop;
        exact?

/-
A similarity transformation preserves the property of being an equilateral triangle.
-/
lemma similarity_preserves_isEquilateral (f : Similarity P) (A B C : P)
  (h : isEquilateral A B C) : isEquilateral (f A) (f B) (f C) := by
    unfold isEquilateral at *;
    cases f ; aesop

#check Affine.Triangle

/-
The sine of the unoriented angle between two vectors is the absolute value of the area form divided by the product of the norms.
-/
lemma sin_angle_eq_abs_areaForm_div_norms (u v : V) (hu : u ≠ 0) (hv : v ≠ 0) :
  Real.sin (InnerProductGeometry.angle u v) = |Orientation.areaForm Module.Oriented.positiveOrientation u v| / (‖u‖ * ‖v‖) := by
    -- By definition of the unoriented angle, we know that it is non-negative.
    have h_sin_nonneg : 0 ≤ Real.sin (InnerProductGeometry.angle u v) := by
      exact Real.sin_nonneg_of_nonneg_of_le_pi ( InnerProductGeometry.angle_nonneg _ _ ) ( InnerProductGeometry.angle_le_pi _ _ );
    -- We know that `Real.sin (angle u v)` squared equals `1 - Real.cos (angle u v)` squared, and `Real.cos (angle u v) = Real.cos (oangle u v)`.
    have h_sin_sq : (Real.sin (InnerProductGeometry.angle u v))^2 = 1 - (Real.cos (Orientation.oangle Module.Oriented.positiveOrientation u v).toReal)^2 := by
      rw [ Real.sin_sq, ← Real.cos_sq_add_sin_sq ];
      congr! 1;
      · congr! 1;
        -- By definition of the unoriented angle, we know that it is equal to the absolute value of the oriented angle.
        have h_angle_eq : InnerProductGeometry.angle u v = |(Orientation.oangle Module.Oriented.positiveOrientation u v).toReal| := by
          exact?;
        rw [ h_angle_eq, Real.cos_abs ];
      · exact 0;
    -- Since `Real.sin (oangle u v)` is the area form divided by the product of the norms, we can substitute this into our equation.
    have h_sin_oangle : Real.sin (Orientation.oangle Module.Oriented.positiveOrientation u v).toReal = (Orientation.areaForm Module.Oriented.positiveOrientation u v) / (‖u‖ * ‖v‖) := by
      field_simp;
      rw [ sin_oangle_eq_areaForm_div_norm_mul_norm ];
      rw [ mul_assoc, div_mul_cancel₀ _ ( mul_ne_zero ( norm_ne_zero_iff.mpr hu ) ( norm_ne_zero_iff.mpr hv ) ) ];
    rw [ ← Real.sqrt_sq h_sin_nonneg, h_sin_sq, ← Real.sqrt_sq_eq_abs ];
    rw [ ← Real.sqrt_sq ( by positivity : 0 ≤ ‖u‖ * ‖v‖ ), Real.cos_sq' _, h_sin_oangle ];
    rw [ ← Real.sqrt_div ( by positivity ) ] ; ring

/-
The ratio of a side length to the sine of the opposite angle is equal to the product of the three side lengths divided by the absolute value of the area form of the vectors at the vertex.
-/
lemma dist_div_sin_eq_prod_dist_div_abs_area (A B C : P)
  (h_nd : NondegenerateTriangle A B C) :
  dist A B / Real.sin (angle B C A) = (dist A B * dist B C * dist C A) / |Orientation.areaForm Module.Oriented.positiveOrientation (B -ᵥ C) (A -ᵥ C)| := by
    have h_sin_angle : Real.sin (InnerProductGeometry.angle (B -ᵥ C) (A -ᵥ C)) = |Orientation.areaForm Module.Oriented.positiveOrientation (B -ᵥ C) (A -ᵥ C)| / (dist B C * dist A C) := by
      convert sin_angle_eq_abs_areaForm_div_norms _ _ _ _ using 1;
      rw [ dist_eq_norm_vsub, dist_eq_norm_vsub ];
      · bound;
        unfold NondegenerateTriangle at h_nd; aesop;
        exact h_nd ( collinear_pair ℝ _ _ );
      · unfold NondegenerateTriangle at h_nd ; aesop;
        exact h_nd ( collinear_pair ℝ _ _ );
    convert congr_arg ( fun x : ℝ => dist A B / x ) h_sin_angle using 1;
    rw [ div_div_eq_mul_div, mul_assoc, dist_comm C A ]

/-
Law of Sines: in a nondegenerate triangle, the ratio of the length of a side to the sine of the opposite angle is constant.
-/
lemma dist_div_sin_eq_dist_div_sin (A B C : P)
  (h_nd : NondegenerateTriangle A B C) :
  dist A B / Real.sin (angle B C A) = dist B C / Real.sin (angle C A B) ∧
  dist B C / Real.sin (angle C A B) = dist C A / Real.sin (angle A B C) := by
    constructor;
    · have h_eq : dist A B / Real.sin (angle B C A) = (dist A B * dist B C * dist C A) / |Orientation.areaForm Module.Oriented.positiveOrientation (B -ᵥ C) (A -ᵥ C)| ∧ dist B C / Real.sin (angle C A B) = (dist A B * dist B C * dist C A) / |Orientation.areaForm Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)| := by
        apply And.intro;
        · exact?;
        · convert dist_div_sin_eq_prod_dist_div_abs_area B C A _ using 1;
          · rw [ Orientation.areaForm_swap ];
            norm_num [ mul_assoc, mul_comm, mul_left_comm ];
          · unfold NondegenerateTriangle at *; aesop;
            exact h_nd ( by rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *; aesop );
      have h_area_form : Orientation.areaForm Module.Oriented.positiveOrientation (B -ᵥ C) (A -ᵥ C) = -Orientation.areaForm Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A) := by
        rw [ show B -ᵥ C = ( B -ᵥ A ) + ( A -ᵥ C ) by rw [ vsub_add_vsub_cancel ] ] ; simp +decide [ add_comm, add_left_comm, add_assoc, sub_eq_add_neg ];
        rw [ show A -ᵥ C = - ( C -ᵥ A ) by rw [ neg_vsub_eq_vsub_rev ], map_neg ];
      aesop;
    · rw [ dist_div_sin_eq_prod_dist_div_abs_area, dist_div_sin_eq_prod_dist_div_abs_area ];
      · simp +decide [ mul_assoc, mul_comm, mul_left_comm, areaForm_triangle_cyclic ];
      · unfold NondegenerateTriangle at *; aesop;
        exact h_nd ( by rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *; obtain ⟨ p ⟩ := a; aesop );
      · unfold NondegenerateTriangle at *; aesop;
        exact h_nd ( by rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *; aesop )

/-
If two nondegenerate triangles have equal angles, then the ratios of corresponding side lengths are equal.
-/
lemma side_ratios_eq_of_equal_angles (A B C A' B' C' : P)
  (h_nd : NondegenerateTriangle A B C)
  (h_nd' : NondegenerateTriangle A' B' C')
  (h_A : angle C A B = angle C' A' B')
  (h_B : angle A B C = angle A' B' C')
  (h_C : angle B C A = angle B' C' A') :
  dist A B / dist A' B' = dist B C / dist B' C' ∧ dist B C / dist B' C' = dist C A / dist C' A' := by
    -- By the Law of Sines, we have the following equalities:
    have h_sines : dist A B / Real.sin (angle B C A) = dist B C / Real.sin (angle C A B) ∧ dist B C / Real.sin (angle C A B) = dist C A / Real.sin (angle A B C) ∧ dist A' B' / Real.sin (angle B' C' A') = dist B' C' / Real.sin (angle C' A' B') ∧ dist B' C' / Real.sin (angle C' A' B') = dist C' A' / Real.sin (angle A' B' C') := by
      exact ⟨ dist_div_sin_eq_dist_div_sin A B C h_nd |>.1, dist_div_sin_eq_dist_div_sin A B C h_nd |>.2, dist_div_sin_eq_dist_div_sin A' B' C' h_nd' |>.1, dist_div_sin_eq_dist_div_sin A' B' C' h_nd' |>.2 ⟩;
    simp_all +decide [ div_eq_mul_inv ];
    simp_all +decide [ ← div_eq_mul_inv ];
    by_cases hB : Real.sin ( ∠ C' A' B' ) = 0 <;> by_cases hC : Real.sin ( ∠ A' B' C' ) = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc ];
    · cases h_sines.1 <;> cases h_sines.2 <;> simp_all +decide [ dist_comm ];
      · unfold NondegenerateTriangle at h_nd ; aesop;
        · simp_all +decide [ collinear_pair ];
        · simp_all ( config := { decide := Bool.true } ) [ collinear_pair ];
      · have h_contra : ∠ C' A' B' = 0 ∨ ∠ C' A' B' = Real.pi := by
          rw [ Real.sin_eq_zero_iff ] at hB ; aesop;
          rcases w with ⟨ _ | _ | w ⟩ <;> norm_num at * <;> first | left; nlinarith [ Real.pi_pos, angle_nonneg C' A' B', angle_le_pi C' A' B' ] | right; nlinarith [ Real.pi_pos, angle_nonneg C' A' B', angle_le_pi C' A' B' ] ;
        cases h_contra <;> simp_all +decide [ angle ];
        · rw [ InnerProductGeometry.angle_eq_zero_iff ] at *;
          cases ‹C' -ᵥ A' ≠ 0 ∧ _›.2 ; aesop;
          · have h_collinear : Collinear ℝ {A', B', C'} := by
              rw [ collinear_iff_exists_forall_eq_smul_vadd ];
              exact ⟨ A', C' -ᵥ A', fun p hp => by rcases hp with ( rfl | rfl | rfl ) <;> [ exact ⟨ 0, by simp +decide ⟩ ; exact ⟨ w_1, by simp +decide [ ← right_1 ] ⟩ ; exact ⟨ 1, by simp +decide ⟩ ] ⟩;
            exact?;
          · have h_collinear : Collinear ℝ {A', B', C'} := by
              rw [ collinear_iff_exists_forall_eq_smul_vadd ];
              exact ⟨ A', C' -ᵥ A', fun p hp => by rcases hp with ( rfl | rfl | rfl ) <;> [ exact ⟨ 0, by simp +decide ⟩ ; exact ⟨ w_1, by simp +decide [ ← right_1 ] ⟩ ; exact ⟨ 1, by simp +decide ⟩ ] ⟩;
            exact?;
        · rw [ InnerProductGeometry.angle_eq_pi_iff ] at * ; aesop;
          · contrapose! h_nd';
            unfold NondegenerateTriangle; simp_all ( config := { decide := Bool.true } ) [ sub_eq_iff_eq_add ] ;
            rw [ collinear_iff_exists_forall_eq_smul_vadd ] ; use A' ; aesop;
            exact ⟨ C' -ᵥ A', ⟨ 0, by simp ( config := { decide := Bool.true } ) ⟩, ⟨ w, by rw [ ← right, vsub_vadd ] ⟩, ⟨ 1, by simp ( config := { decide := Bool.true } ) ⟩ ⟩;
          · have h_collinear : Collinear ℝ {A', B', C'} := by
              rw [ collinear_iff_exists_forall_eq_smul_vadd ] ; use A' ; aesop;
              exact ⟨ C' -ᵥ A', ⟨ 0, by simp ( config := { decide := Bool.true } ) ⟩, ⟨ w, by rw [ ← right, vsub_vadd ] ⟩, ⟨ 1, by simp ( config := { decide := Bool.true } ) ⟩ ⟩;
            exact False.elim ( h_nd' h_collinear );
    · norm_num [ mul_div ] at hB;
    · norm_num [ mul_div ] at hC;
    · field_simp;
      rw [ div_eq_div_iff ] <;> aesop;
      · grind;
      · rw [ div_eq_div_iff ] <;> first | linarith | simp_all +decide [ dist_comm ] ;
        · rw [ ← div_eq_mul_inv, ← div_eq_mul_inv ] at *;
          grind;
        · rintro rfl; simp_all +decide [ NondegenerateTriangle ];
          exact h_nd' ( collinear_singleton _ _ );
        · rintro rfl; simp_all ( config := { decide := Bool.true } ) [ NondegenerateTriangle ];
          exact h_nd' ( collinear_singleton _ _ );
      · simp_all ( config := { decide := Bool.true } ) [ NondegenerateTriangle ];
        exact h_nd' ( collinear_singleton _ _ );
      · unfold NondegenerateTriangle at h_nd' ; aesop;
        exact h_nd' ( collinear_singleton _ _ )

#check AffineMap.homothety

#check LinearIsometry.extend

/-
If two pairs of vectors have equal norms and equal distance, their inner products are equal.
-/
lemma inner_products_eq_of_norms_and_dist_eq (u v u' v' : V)
  (hu : ‖u‖ = ‖u'‖)
  (hv : ‖v‖ = ‖v'‖)
  (hdist : dist u v = dist u' v') :
  inner ℝ u u = inner ℝ u' u' ∧ inner ℝ v v = inner ℝ v' v' ∧ inner ℝ u v = inner ℝ u' v' := by
    simp_all +decide [ dist_eq_norm, inner_self_eq_norm_sq_to_K ];
    have := norm_sub_sq_real u v; have := norm_sub_sq_real u' v'; simp_all +decide [ Real.sq_sqrt ( norm_nonneg _ ) ] ;

/-
If two families of vectors have the same Gram matrix, there exists a linear isometry from the span of the first family to the ambient space mapping the first family to the second.
-/
lemma exists_linear_isometry_of_gram_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → V) (v' : ι → V)
  (h : ∀ i j, inner ℝ (v i) (v j) = inner ℝ (v' i) (v' j)) :
  ∃ f : (Submodule.span ℝ (Set.range v)) →ₗᵢ[ℝ] V, ∀ i, f ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ = v' i := by
    have h_gram : ∀ (l : ι → ℝ), ‖∑ i, l i • v i‖ = ‖∑ i, l i • v' i‖ := by
      intro l
      have h_norm_sq : ‖∑ i, l i • v i‖ ^ 2 = ‖∑ i, l i • v' i‖ ^ 2 := by
        simp +decide only [norm_eq_sqrt_real_inner];
        simp +decide only [inner_sum, inner_smul_right, sum_inner, inner_smul_left, h];
      rwa [ sq_eq_sq₀ ( norm_nonneg _ ) ( norm_nonneg _ ) ] at h_norm_sq
    generalize_proofs at *;
    have h_linear_map : ∃ f : (Submodule.span ℝ (Set.range v)) →ₗ[ℝ] V, ∀ i, f ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ = v' i := by
      have h_linear_map : ∀ (l : ι →₀ ℝ), ∑ i, l i • v' i = 0 → ∑ i, l i • v i = 0 := by
        intro l hl; specialize h_gram l; aesop;
      generalize_proofs at *;
      have h_linear_map : ∃ f : (Submodule.span ℝ (Set.range v)) →ₗ[ℝ] V, ∀ l : ι →₀ ℝ, f (⟨∑ i, l i • v i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))⟩) = ∑ i, l i • v' i := by
        have h_linear_map : ∀ (l : ι →₀ ℝ), ∑ i, l i • v i = 0 → ∑ i, l i • v' i = 0 := by
          intro l hl; specialize h_gram ( fun i => l i ) ; aesop;
          exact norm_eq_zero.mp h_gram.symm
        generalize_proofs at *;
        have h_linear_map : ∃ f : (Submodule.span ℝ (Set.range v)) →ₗ[ℝ] V, ∀ l : ι →₀ ℝ, f (⟨∑ i, l i • v i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))⟩) = ∑ i, l i • v' i := by
          have h_surjective : ∀ x ∈ Submodule.span ℝ (Set.range v), ∃ l : ι →₀ ℝ, x = ∑ i, l i • v i := by
            intro x hx
            have h_exists_l : ∃ l : ι →₀ ℝ, x = ∑ i, l i • v i := by
              rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at hx
              generalize_proofs at *;
              exact ⟨ hx.choose, by simpa [ Finsupp.sum_fintype ] using hx.choose_spec.symm ⟩
            generalize_proofs at *;
            exact h_exists_l
            skip
          have h_linear_map : ∀ (x : Submodule.span ℝ (Set.range v)), ∃ y : V, ∀ l : ι →₀ ℝ, x = ∑ i, l i • v i → y = ∑ i, l i • v' i := by
            intro x
            generalize_proofs at *;
            obtain ⟨ l, hl ⟩ := h_surjective x x.2
            generalize_proofs at *;
            use ∑ i, l i • v' i
            intro l' hl'
            generalize_proofs at *;
            have h_eq : ∑ i, (l' - l) i • v i = 0 := by
              simp_all +decide [ sub_smul, Finset.sum_sub_distrib ]
            generalize_proofs at *;
            have h_eq' : ∑ i, (l' - l) i • v' i = 0 := by
              exact h_linear_map _ h_eq
            generalize_proofs at *;
            simp_all +decide [ sub_eq_zero, Finset.sum_sub_distrib, sub_smul ] ;
          generalize_proofs at *;
          choose f hf using h_linear_map
          generalize_proofs at *;
          refine' ⟨ { toFun := f, map_add' := _, map_smul' := _ }, fun l => hf _ _ rfl ⟩
          generalize_proofs at *;
          · intro x y
            obtain ⟨l₁, hl₁⟩ := h_surjective x x.2
            obtain ⟨l₂, hl₂⟩ := h_surjective y y.2
            have h_sum : f (x + y) = ∑ i, (l₁ i + l₂ i) • v' i := by
              convert hf ( x + y ) ( l₁ + l₂ ) _ using 1
              generalize_proofs at *;
              simp +decide [ hl₁, hl₂, Finset.sum_add_distrib, add_smul ]
            generalize_proofs at *;
            simp +decide [ h_sum, hf x l₁ hl₁, hf y l₂ hl₂, add_smul, Finset.sum_add_distrib ];
          · intro m x
            obtain ⟨l, hl⟩ := h_surjective x x.2
            generalize_proofs at *;
            rw [ hf ( m • x ) ( m • l ) ] <;> simp +decide [ hl, hf x l hl, Finset.smul_sum, smul_smul ]
        generalize_proofs at *;
        exact h_linear_map
      generalize_proofs at *;
      obtain ⟨ f, hf ⟩ := h_linear_map;
      refine' ⟨ f, fun i => _ ⟩;
      convert hf ( Finsupp.single i 1 ) using 1 <;> simp +decide [ Finsupp.single_apply ];
    obtain ⟨ f, hf ⟩ := h_linear_map
    generalize_proofs at *;
    have h_isometry : ∀ x : Submodule.span ℝ (Set.range v), ‖f x‖ = ‖x‖ := by
      intro x
      obtain ⟨l, hl⟩ : ∃ l : ι → ℝ, x = ∑ i, l i • v i := by
        have := x.2; rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at this; aesop;
        exact ⟨ w, by simp +decide [ Finsupp.sum_fintype ] ⟩
      generalize_proofs at *;
      have h_linear_map : f x = ∑ i, l i • v' i := by
        have h_fx : f x = f (∑ i, l i • ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩) := by
          congr
          generalize_proofs at *;
          exact Subtype.ext ( by simpa [ Submodule.coe_sum ] using hl )
        generalize_proofs at *; (
        simp +decide [ h_fx, hf, map_sum, LinearMap.map_smul ];
        exact Finset.sum_congr rfl fun i _ => by rw [ ← hf i, ← map_smul ] ; rfl;)
      generalize_proofs at *;
      simp_all +decide [ norm_eq_sqrt_real_inner ] ;
    generalize_proofs at *;
    refine' ⟨ { toLinearMap := f, norm_map' := h_isometry }, hf ⟩

/-
For a nondegenerate triangle, the trisected angles are strictly between 0 and 60 degrees, and their sum is 60 degrees.
-/
lemma angles_bounds_of_nondegenerate (A B C : P) (h_nd : NondegenerateTriangle A B C) :
  let a := (angle C A B) / 3
  let b := (angle A B C) / 3
  let c := (angle B C A) / 3
  0 < a ∧ a < π/3 ∧ 0 < b ∧ b < π/3 ∧ 0 < c ∧ c < π/3 ∧ a + b + c = π/3 := by
    have h_trisected_angles : 0 < ∠ C A B ∧ ∠ C A B < Real.pi ∧ 0 < ∠ A B C ∧ ∠ A B C < Real.pi ∧ 0 < ∠ B C A ∧ ∠ B C A < Real.pi ∧ ∠ C A B + ∠ A B C + ∠ B C A = Real.pi := by
      by_contra h_contra;
      unfold NondegenerateTriangle at h_nd;
      refine' h_contra ⟨ _, _, _, _, _, _, _ ⟩;
      all_goals have := angle_pos_of_not_collinear h_nd; have := angle_lt_pi_of_not_collinear h_nd; simp_all +decide [ dist_eq_norm_vsub ];
      · apply_rules [ angle_pos_of_not_collinear ];
        rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
        exact fun ⟨ p₀, v, hv ⟩ => h_nd ⟨ p₀, v, by simpa [ or_comm, or_left_comm, or_assoc ] using hv ⟩;
      · rw [ angle_comm ];
        apply_rules [ angle_lt_pi_of_not_collinear ];
        rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
        exact fun ⟨ p₀, v, hv ⟩ => h_nd ⟨ p₀, v, fun p hp => by aesop ⟩;
      · rw [ angle_comm ];
        apply_rules [ angle_pos_of_not_collinear ];
        rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
        aesop;
      · apply_rules [ angle_lt_pi_of_not_collinear ];
        rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
        exact fun ⟨ p₀, v, hv ⟩ => h_nd ⟨ p₀, v, by simpa [ or_comm, or_left_comm, or_assoc ] using hv ⟩;
      · rw [ add_assoc, add_comm, angle_add_angle_add_angle_eq_pi ];
        rintro rfl; simp_all +decide [ collinear_pair ];
    exact ⟨ by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith ⟩

/-
An affine isometry is a similarity with ratio 1.
-/
/-- An affine isometry is a similarity with ratio 1. -/
def affineIsometryToSimilarity (f : P →ᵃⁱ[ℝ] P) : Similarity P :=
  { toFun := f
    r := 1
    r_pos := Real.zero_lt_one
    dist_eq := by
      intro x y
      simp only [AffineIsometry.dist_map, one_mul] }

theorem affineIsometryToSimilarity_apply (f : P →ᵃⁱ[ℝ] P) (x : P) :
  (affineIsometryToSimilarity f) x = f x := rfl

#check LinearIsometry.extend

/-
A linear isometry from a finite-dimensional inner product space to itself can be upgraded to a linear isometry equivalence.
-/
lemma linear_isometry_equiv_of_isometry_endomorphism (f : V →ₗᵢ[ℝ] V) :
  ∃ g : V ≃ₗᵢ[ℝ] V, g.toLinearIsometry = f := by
    have h_surjective : Function.Surjective f := by
      have h_inj : Function.Injective f := by
        exact f.injective
      have h_surj : FiniteDimensional ℝ V := by
        exact FiniteDimensional.of_finrank_pos ( by linarith [ Fact.out ( p := Module.finrank ℝ V = 2 ) ] );
      exact LinearMap.surjective_of_injective h_inj;
    exact ⟨ LinearIsometryEquiv.ofSurjective f h_surjective, rfl ⟩

/-
Any linear isometry from a subspace of a finite-dimensional inner product space to the space itself can be extended to a global linear isometry equivalence.
-/
lemma extend_isometry_to_equiv (S : Submodule ℝ V) (f : S →ₗᵢ[ℝ] V) :
  ∃ L : V ≃ₗᵢ[ℝ] V, ∀ x : S, L x = f x := by
    by_contra h_contra
    generalize_proofs at *;
    -- Let $g = \text{LinearIsometry.extend } f$. This gives a linear isometry $g : V \to V$.
    obtain ⟨g, hg⟩ : ∃ g : V →ₗᵢ[ℝ] V, ∀ x : S, g x = f x := by
      have h_extend : ∃ g : V →ₗᵢ[ℝ] V, ∀ x : S, g x = f x := by
        have h_finite_dim : FiniteDimensional ℝ V := by
          exact FiniteDimensional.of_finrank_pos ( by linarith [ Fact.out ( p := Module.finrank ℝ V = 2 ) ] )
        exact ⟨ _, fun x => LinearIsometry.extend_apply f x ⟩;
      exact h_extend;
    obtain ⟨ L, hL ⟩ := linear_isometry_equiv_of_isometry_endomorphism g;
    exact h_contra ⟨ L, fun x => by simpa [ ← hL ] using hg x ⟩

/-
If two pairs of vectors have the same norms and the same distance between them, there exists a global linear isometry mapping the first pair to the second.
-/
lemma exists_linearIsometry_of_congruent_vectors (u v u' v' : V)
  (hu : ‖u‖ = ‖u'‖)
  (hv : ‖v‖ = ‖v'‖)
  (hdist : dist u v = dist u' v') :
  ∃ L : V ≃ₗᵢ[ℝ] V, L u = u' ∧ L v = v' := by
    -- By `exists_linear_isometry_of_gram_eq`, there is a linear isometry $f$ from the span of $\{u, v\}$ to $V$ such that $f(u) = u'$ and $f(v) = v'$.
    obtain ⟨f, hf⟩ : ∃ f : (Submodule.span ℝ (Set.range ![u, v])) →ₗᵢ[ℝ] V, f ⟨u, Submodule.subset_span (Set.mem_range_self 0)⟩ = u' ∧ f ⟨v, Submodule.subset_span (Set.mem_range_self 1)⟩ = v' := by
      have h_gram : ∀ i j : Fin 2, inner ℝ (![u, v] i) (![u, v] j) = inner ℝ (![u', v'] i) (![u', v'] j) := by
        have := inner_products_eq_of_norms_and_dist_eq u v u' v' hu hv hdist;
        simp +decide [ Fin.forall_fin_two, this ];
        rw [ real_inner_comm, this.2.2, real_inner_comm ];
      have := exists_linear_isometry_of_gram_eq ![u, v] ![u', v'] h_gram;
      exact ⟨ this.choose, this.choose_spec 0, this.choose_spec 1 ⟩;
    obtain ⟨ L, hL ⟩ := extend_isometry_to_equiv ( Submodule.span ℝ ( Set.range ![ u, v ] ) ) f;
    exact ⟨ L, by simpa [ hf ] using hL ⟨ u, Submodule.subset_span ( Set.mem_range_self 0 ) ⟩, by simpa [ hf ] using hL ⟨ v, Submodule.subset_span ( Set.mem_range_self 1 ) ⟩ ⟩

/-
If two pairs of vectors have the same norms and the same distance between them, there exists a linear isometry from the span of the first pair to the whole space mapping the first pair to the second.
-/
lemma exists_isometry_on_span_range (u v u' v' : V)
  (hu : ‖u‖ = ‖u'‖)
  (hv : ‖v‖ = ‖v'‖)
  (hdist : dist u v = dist u' v') :
  ∃ f : (Submodule.span ℝ (Set.range ![u, v])) →ₗᵢ[ℝ] V,
    f ⟨u, Submodule.subset_span (Set.mem_range_self (0 : Fin 2))⟩ = u' ∧
    f ⟨v, Submodule.subset_span (Set.mem_range_self (1 : Fin 2))⟩ = v' := by
      have h_exists_linearIsometry_of_gram_eq : ∀ i j : Fin 2, inner ℝ ( ![u, v] i ) ( ![u, v] j ) = inner ℝ ( ![u', v'] i ) ( ![u', v'] j ) := by
        have := inner_products_eq_of_norms_and_dist_eq u v u' v' hu hv hdist;
        simp +decide [ Fin.forall_fin_two, this ];
        rw [ real_inner_comm, this.2.2, real_inner_comm ]
      generalize_proofs at *;
      have := exists_linear_isometry_of_gram_eq ( ![u, v] : Fin 2 → V ) ( ![u', v'] : Fin 2 → V ) h_exists_linearIsometry_of_gram_eq;
      exact ⟨ this.choose, this.choose_spec 0, this.choose_spec 1 ⟩

/-
If two pairs of vectors have the same norms and the same distance between them, there exists a global linear isometry mapping the first pair to the second.
-/
lemma exists_linearIsometry_of_congruent_vectors_v2 (u v u' v' : V)
  (hu : ‖u‖ = ‖u'‖)
  (hv : ‖v‖ = ‖v'‖)
  (hdist : dist u v = dist u' v') :
  ∃ L : V ≃ₗᵢ[ℝ] V, L u = u' ∧ L v = v' := by
    exact?

/-
If two nondegenerate triangles have equal angles, there exists a similarity transformation mapping the vertices of the first to the vertices of the second.
-/
lemma exists_similarity_of_equal_angles (A B C A' B' C' : P)
  (h_nd : NondegenerateTriangle A B C)
  (h_nd' : NondegenerateTriangle A' B' C')
  (h_A : angle C A B = angle C' A' B')
  (h_B : angle A B C = angle A' B' C')
  (h_C : angle B C A = angle B' C' A') :
  ∃ f : Similarity P, f A = A' ∧ f B = B' ∧ f C = C' := by
    have := side_ratios_eq_of_equal_angles A B C A' B' C' h_nd h_nd' h_A h_B h_C;
    -- Let $k = A'B'/AB$. Then $A'B' = k AB$, $B'C' = k BC$, $C'A' = k CA$.
    obtain ⟨k, hk⟩ : ∃ k : ℝ, 0 < k ∧ dist A' B' = k * dist A B ∧ dist B' C' = k * dist B C ∧ dist C' A' = k * dist C A := by
      have h_pos : 0 < dist A B ∧ 0 < dist B C ∧ 0 < dist C A ∧ 0 < dist A' B' ∧ 0 < dist B' C' ∧ 0 < dist C' A' := by
        simp_all +decide [ NondegenerateTriangle, dist_pos ];
        exact ⟨ by rintro rfl; exact h_nd <| by simp +decide [ collinear_pair ], by rintro rfl; exact h_nd <| by simp +decide [ collinear_pair ], by rintro rfl; exact h_nd <| by simp +decide [ collinear_pair ], by rintro rfl; exact h_nd' <| by simp +decide [ collinear_pair ], by rintro rfl; exact h_nd' <| by simp +decide [ collinear_pair ], by rintro rfl; exact h_nd' <| by simp +decide [ collinear_pair ] ⟩;
      refine' ⟨ dist A' B' / dist A B, _, _, _, _ ⟩;
      · exact div_pos h_pos.2.2.2.1 h_pos.1;
      · rw [ div_mul_cancel₀ _ h_pos.1.ne' ];
      · grind;
      · grind;
    have := exists_linearIsometry_of_congruent_vectors ( k • ( B -ᵥ A ) ) ( k • ( C -ᵥ A ) ) ( B' -ᵥ A' ) ( C' -ᵥ A' ) ?_ ?_ ?_ <;> simp_all +decide [ norm_smul, mul_div_mul_left ];
    · obtain ⟨ L, hL₁, hL₂ ⟩ := this;
      refine' ⟨ _, _ ⟩;
      constructor;
      exact hk.1;
      rotate_left;
      exact fun x => ( k • L ( x -ᵥ A ) ) +ᵥ A';
      all_goals simp_all +decide [ dist_eq_norm_vsub ];
      simp +decide [ ← smul_sub, norm_smul, hk.1.le ];
      intro x y; rw [ abs_of_pos hk.1 ] ; rw [ ← L.map_sub ] ; simp +decide [ hk.1.le ] ;
    · rw [ abs_of_pos hk.1, ← dist_eq_norm_vsub, ← dist_eq_norm_vsub ];
      rw [ dist_comm B A, dist_comm B' A', hk.2.1 ];
    · rw [ abs_of_pos hk.1, ← dist_eq_norm_vsub, ← dist_eq_norm_vsub, hk.2.2.2 ];
    · simp +decide [ dist_eq_norm, ← smul_sub, norm_smul, abs_of_pos hk.1 ];
      exact Or.inl ( by rw [ dist_eq_norm_vsub ] )

/-
Given an equilateral triangle PQR and angles a, b, c, the constructed triangle ABC is nondegenerate, has angles 3a, 3b, 3c, and its Morley triangle is PQR.
-/
lemma conway_triangle_properties (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3)
  (h_orientation : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (π / 3 : ℝ)) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  let B := conwayConstructedVertexB P_pt Q R a b c
  let C := conwayConstructedVertexC P_pt Q R a b c
  NondegenerateTriangle A B C ∧
  angle C A B = 3 * a ∧
  angle A B C = 3 * b ∧
  angle B C A = 3 * c ∧
  morleyTriangle A B C = (P_pt, Q, R) := by
    have h_triangle : (NondegenerateTriangle (conwayConstructedVertexA P_pt Q R a b c) (conwayConstructedVertexB P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c)) := by
      apply_rules [ conway_constructed_triangle_nondegenerate ];
      · apply_rules [ conway_gap_angle_P_correct ];
      · apply_rules [ conway_gap_angle_Q_correct ];
      · apply conway_gap_angle_R_correct P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation;
    have h_gap_P := conway_gap_angle_P_correct P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation
    have h_gap_Q := conway_gap_angle_Q_correct P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation
    have h_gap_R := conway_gap_angle_R_correct P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation;
    exact ⟨ h_triangle, by simpa using conway_constructed_triangle_angles P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation h_gap_P h_gap_Q h_gap_R |>.1, by simpa using conway_constructed_triangle_angles P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation h_gap_P h_gap_Q h_gap_R |>.2.1, by simpa using conway_constructed_triangle_angles P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation h_gap_P h_gap_Q h_gap_R |>.2.2, by simpa using conway_PQR_is_morley P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation h_gap_P h_gap_Q h_gap_R ⟩

/-
Morley's Trisector Theorem: In any nondegenerate triangle, the Morley triangle is equilateral.
-/
theorem morley_theorem (A B C : P) (h_nd : NondegenerateTriangle A B C) :
  let (P_tri, Q_tri, R_tri) := morleyTriangle A B C
  isEquilateral P_tri Q_tri R_tri := by
    have h_angles_bounds : ∃ a b c : ℝ, 0 < a ∧ a < Real.pi / 3 ∧ 0 < b ∧ b < Real.pi / 3 ∧ 0 < c ∧ c < Real.pi / 3 ∧ a + b + c = Real.pi / 3 ∧ angle C A B = 3 * a ∧ angle A B C = 3 * b ∧ angle B C A = 3 * c := by
      have h_angles_bounds : let a := (angle C A B) / 3; let b := (angle A B C) / 3; let c := (angle B C A) / 3; 0 < a ∧ a < Real.pi / 3 ∧ 0 < b ∧ b < Real.pi / 3 ∧ 0 < c ∧ c < Real.pi / 3 ∧ a + b + c = Real.pi / 3 := by
        have := angles_bounds_of_nondegenerate A B C h_nd; aesop;
      exact ⟨ _, _, _, h_angles_bounds.1, h_angles_bounds.2.1, h_angles_bounds.2.2.1, h_angles_bounds.2.2.2.1, h_angles_bounds.2.2.2.2.1, h_angles_bounds.2.2.2.2.2.1, h_angles_bounds.2.2.2.2.2.2, by ring, by ring, by ring ⟩;
    -- Apply the existence of an equilateral triangle with the given angles.
    obtain ⟨a, b, c, ha_pos, ha_lt, hb_pos, hb_lt, hc_pos, hc_lt, habc_sum, habc_angles⟩ := h_angles_bounds;
    obtain ⟨P_pt, Q, R, h_equilateral, h_side, h_orientation⟩ : ∃ P_pt Q R : P, isEquilateral P_pt Q R ∧ dist P_pt Q = 1 ∧ Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (Real.pi / 3 : ℝ) := by
      apply exists_equilateral_triangle_with_orientation;
    obtain ⟨A', B', C', hA'B'C', hA'B'C'_angles⟩ : ∃ A' B' C' : P, NondegenerateTriangle A' B' C' ∧ angle C' A' B' = 3 * a ∧ angle A' B' C' = 3 * b ∧ angle B' C' A' = 3 * c ∧ morleyTriangle A' B' C' = (P_pt, Q, R) := by
      use conwayConstructedVertexA P_pt Q R a b c, conwayConstructedVertexB P_pt Q R a b c, conwayConstructedVertexC P_pt Q R a b c;
      apply_rules [ conway_triangle_properties ];
    -- By `exists_similarity_of_equal_angles`, there exists a similarity transformation $f$ such that $f(A') = A$, $f(B') = B$, $f(C') = C$.
    obtain ⟨f, hf⟩ : ∃ f : Similarity P, f A' = A ∧ f B' = B ∧ f C' = C := by
      apply exists_similarity_of_equal_angles A' B' C' A B C hA'B'C' h_nd;
      · linarith;
      · linarith;
      · linarith;
    -- By `morley_triangle_similarity_invariance`, the Morley triangle of $ABC$ is the image of the Morley triangle of $A'B'C'$ under $f$.
    have h_morley_image : morleyTriangle A B C = (f P_pt, f Q, f R) := by
      have := morley_triangle_similarity_invariance f A' B' C' hA'B'C'; aesop;
    -- Since $f$ is a similarity transformation, it preserves the property of being equilateral.
    have h_similarity_preserves_equilateral : ∀ (A B C : P), isEquilateral A B C → isEquilateral (f A) (f B) (f C) := by
      exact?;
    exact h_morley_image.symm ▸ h_similarity_preserves_equilateral _ _ _ h_equilateral
