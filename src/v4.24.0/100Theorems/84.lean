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
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0

noncomputable section

open EuclideanGeometry Real InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]
variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P] [Nonempty P]

/-
A similarity is a map that scales distances by a positive factor r.
-/
structure Similarity (P : Type*) [MetricSpace P] where
  toFun : P → P
  r : ℝ
  r_pos : r > 0
  dist_eq : ∀ x y, dist (toFun x) (toFun y) = r * dist x y

instance (P : Type*) [MetricSpace P] : CoeFun (Similarity P) (fun _ => P → P) := ⟨Similarity.toFun⟩
/-- Angle shift: theta plus 60 degrees. -/
def angleShift (θ : ℝ) : ℝ := θ + π / 3

/-- Angle shift: theta plus 120 degrees. -/
def angleShiftTwo (θ : ℝ) : ℝ := θ + 2 * π / 3

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
A triangle is nondegenerate if its vertices are not collinear.
-/
def NondegenerateTriangle (A B C : P) : Prop := ¬ Collinear ℝ {A, B, C}

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
  unfold conwaySmallTriangleVertex;
  norm_num [ dist_eq_norm ];
  rw [ norm_smul, Real.norm_of_nonneg ];
  · rw [ div_mul_eq_mul_div, div_eq_iff ] <;> aesop;
  · exact div_nonneg ( div_nonneg ( mul_nonneg h_pos.le h_sin_a2.le ) h_sin_ao.le ) ( norm_nonneg _ )

/-
Algebraic identity derived from the trigonometric identity by dividing by $\sin^2 a_o$.
-/
lemma conway_algebraic_identity (a1 a2 ao : ℝ) (h_sin_ao : Real.sin ao ≠ 0) (h_sum : a1 + a2 + ao = π) :
  1 - 2 * (Real.sin a2 / Real.sin ao) * Real.cos a1 + (Real.sin a2 / Real.sin ao) ^ 2 = (Real.sin a1 / Real.sin ao) ^ 2 := by
  field_simp;
  rw [ show ao = Real.pi - a1 - a2 by linarith ] ; repeat norm_num [ Real.sin_sq, Real.sin_sub, Real.cos_sub ] ; ring;

/-
Helper lemma for the squared distance calculation in Conway's proof.
-/
lemma conway_dist_sq_lemma (v : V) (a1 k : ℝ) :
  ‖-v + k • (Orientation.rotation (Module.Oriented.positiveOrientation) (-a1 : Real.Angle) v)‖^2 = ‖v‖^2 * (1 - 2 * k * Real.cos a1 + k^2) := by
  rw [ @norm_add_sq ℝ ] ; norm_num ; ring;
  norm_num [ norm_smul, inner_smul_right ] ; ring;
  rw [ show ⟪v, ( Module.Oriented.positiveOrientation.rotation ( - ( a1 : Real.Angle ) ) : V → V ) v⟫_ℝ = ‖v‖ ^ 2 * Real.cos a1 by
        rw [ Orientation.rotation ];
        simp +decide [ Real.Angle.cos_neg, Real.Angle.sin_neg, inner_sub_left, inner_smul_left, inner_smul_right ];
        rw [ inner_add_right, inner_smul_right, inner_neg_right ] ; ring;
        rw [ inner_smul_right ];
        simp +decide [ real_inner_self_eq_norm_sq ] ] ; norm_num ; ring

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
  convert ( conwaySmallTriangleVertex_dist_P2_pos R P_pt _ _ _ ?_ ?_ ?_ ?_ ?_ ) using 1;
  all_goals norm_num [ angleShift, h_side ];
  · exact rfl;
  · exact Real.sin_pos_of_pos_of_lt_pi h_b_pos ( by linarith );
  · exact Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by linarith );
  · exact Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by linarith );
  · grind

/-
Step 3: Matching of shared edges (CP).
The length of the side CP in the small triangle CPQ (constructed by `conwayVertexC`) matches the length required by the large triangle BPC.
-/
theorem conway_step3_CP_matches (P_pt Q : P) (a b c : ℝ)
  (h_side : dist P_pt Q = 1)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_sum : a + b + c = π / 3) :
  dist P_pt (conwayVertexC P_pt Q a b c) = conwayLargeSideCP a c := by
  unfold conwayVertexC conwayLargeSideCP;
  rw [ conwaySmallTriangleVertex_dist_P1 ];
  · rw [ h_side, one_mul ];
  · exact h_side.symm ▸ zero_lt_one;
  · exact Real.sin_pos_of_pos_of_lt_pi h_c_pos ( by linarith );
  · exact Real.sin_pos_of_pos_of_lt_pi ( add_pos h_a_pos ( by positivity ) ) ( by unfold angleShift; linarith )

/-
Step 3: Matching of shared edges (RA).
The length of the side RA in the small triangle AQR (constructed by `conwayVertexA`) matches the length required by the large triangle ARB.
-/
theorem conway_step3_RA_matches (Q R : P) (a b c : ℝ)
  (h_side : dist Q R = 1)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_sum : a + b + c = π / 3) :
  dist R (conwayVertexA Q R a b c) = conwayLargeSideRA c a := by
  convert conwaySmallTriangleVertex_dist_P2_pos Q R ( angleShift c ) ( angleShift b ) ( a ) _ _ _ _ _ using 1 <;> norm_num [ h_side, h_a_pos, h_b_pos, h_c_pos, h_sum ];
  · rfl;
  · exact Real.sin_pos_of_pos_of_lt_pi h_a_pos ( by linarith );
  · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith );
  · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith );
  · unfold angleShift; linarith

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
  apply unique_angles_of_sides_ratio;
  all_goals try linarith [ Real.pi_pos ];
  · unfold conwayLargeAngleP;
    unfold angleShiftTwo; linarith;
  · exact add_pos h_a_pos ( by positivity );
  · unfold conwayLargeAngleP;
    unfold angleShiftTwo; linarith [ Real.pi_pos ];
  · rw [ h_PB, h_PC, conwayLargeSideBP, conwayLargeSideCP ];
    rw [ div_div_div_comm, div_self ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith ) ) ) ] ; ring;
    norm_num [ mul_comm ]

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
Definitions of the vertices of the constructed triangle ABC.
-/
def conwayConstructedVertexA (P_pt Q R : P) (a b c : ℝ) : P := conwayVertexA Q R a b c

def conwayConstructedVertexB (P_pt Q R : P) (a b c : ℝ) : P := conwayVertexB R P_pt a b c

def conwayConstructedVertexC (P_pt Q R : P) (a b c : ℝ) : P := conwayVertexC P_pt Q a b c

/-
The oriented angle at P1 is -a1.
-/
lemma conwaySmallTriangleVertex_oangle_P1_V (P1 P2 : P) (a1 a2 ao : ℝ)
  (h_pos : dist P1 P2 > 0)
  (h_sin_ao_pos : Real.sin ao > 0)
  (h_sin_a2_pos : Real.sin a2 > 0)
  (h_a1_bound : 0 < a1 ∧ a1 < π) :
  Orientation.oangle Module.Oriented.positiveOrientation (P2 -ᵥ P1) ((conwaySmallTriangleVertex P1 P2 a1 a2 ao) -ᵥ P1) = (-a1 : Real.Angle) := by
  unfold conwaySmallTriangleVertex;
  by_cases h : P2 -ᵥ P1 = 0 <;> simp_all +decide [ neg_div, div_neg ]

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
  simp +zetaDelta at *;
  unfold conwaySmallTriangleVertex;
  have h_angle_P2_V : Orientation.oangle Module.Oriented.positiveOrientation (- (P2 -ᵥ P1)) ((dist P1 P2 * Real.sin a2 / Real.sin ao / ‖P2 -ᵥ P1‖) • (Orientation.rotation (Module.Oriented.positiveOrientation) (-a1 : Real.Angle) (P2 -ᵥ P1)) - (P2 -ᵥ P1)) = (a2 : Real.Angle) := by
    convert oangle_of_constructed_triangle_variant ( P2 -ᵥ P1 ) a1 a2 ( Real.pi - a1 - a2 ) _ _ _ _ _ using 1 <;> norm_num [ h_sum ];
    · rw [ show ao = Real.pi - a1 - a2 by linarith ];
      rw [ dist_eq_norm_vsub' ];
      rw [ mul_div_assoc, mul_div_cancel_left₀ _ ( norm_ne_zero_iff.mpr ( vsub_ne_zero.mpr ( Ne.symm h_pos ) ) ) ];
    · exact Ne.symm h_pos;
    · exact h_a1_bound;
    · exact h_a2_bound;
    · exact ⟨ by linarith [ Real.pi_pos, show ao > 0 from not_le.mp fun h => h_sin_ao_pos.not_le <| Real.sin_nonpos_of_nonpos_of_neg_pi_le h <| by linarith ], by linarith [ Real.pi_pos, show ao > 0 from not_le.mp fun h => h_sin_ao_pos.not_le <| Real.sin_nonpos_of_nonpos_of_neg_pi_le h <| by linarith ] ⟩;
  convert h_angle_P2_V using 1;
  simp +decide [ vadd_vsub_assoc, sub_eq_add_neg ]

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
  exact
    conwaySmallTriangleVertex_oangle_P2_V P1 P2 a1 a2 ao h_pos h_sin_ao_pos h_sin_a1_pos
      h_sin_a2_pos h_sum h_a1_bound h_a2_bound

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
  -- Apply the lemma that states the oriented angle at P2 is a2.
  apply conwaySmallTriangleVertex_oangle_P2_V_proven;
  any_goals unfold angleShift; constructor <;> linarith [ Real.pi_pos ];
  · unfold isEquilateral at h_equilateral; aesop;
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
  unfold angleShift angleShiftTwo; ring;
  erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ];
  exact ⟨ -1, by push_cast; linarith ⟩

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
  fapply conway_gap_angle_P_correct;
  any_goals assumption;
  · unfold isEquilateral at *; aesop;
  · exact h_side ▸ h_equilateral.1.symm;
  · linarith;
  · have := equilateral_oangle_cyclic P_pt Q R h_equilateral;
    exact this ▸ h_orientation

/-
A similarity transformation can be decomposed into a translation, a scaling, and a linear isometry.
-/
lemma similarity_decomposition (f : Similarity P) (O : P) :
  ∃ (L : V ≃ₗᵢ[ℝ] V), ∀ v, f (v +ᵥ O) = (f.r • L v) +ᵥ f O := by
  have h_map : ∃ L : V →ₗᵢ[ℝ] V, ∀ v : V, f.toFun (v +ᵥ O) = f.r • L v +ᵥ f.toFun O := by
    have h_map : ∀ v : V, dist (f.toFun (v +ᵥ O)) (f.toFun O) = f.r * ‖v‖ := by
      intro v
      have h_dist : dist (f.toFun (v +ᵥ O)) (f.toFun O) = f.r * dist (v +ᵥ O) O := by
        exact f.dist_eq _ _;
      aesop;
    have h_map : ∀ v : V, ∃ w : V, f.toFun (v +ᵥ O) = f.r • w +ᵥ f.toFun O ∧ ‖w‖ = ‖v‖ := by
      intro v
      obtain ⟨w, hw⟩ : ∃ w : V, f.toFun (v +ᵥ O) = f.r • w +ᵥ f.toFun O := by
        use (1 / f.r) • (f.toFun (v +ᵥ O) -ᵥ f.toFun O);
        simp +decide [ ← smul_assoc, f.r_pos.ne' ];
      have := h_map v; simp_all +decide [ dist_eq_norm_vsub ] ;
      rw [ norm_smul, Real.norm_of_nonneg f.r_pos.le ] at this ; aesop;
    choose w hw hw' using h_map;
    have h_map : ∀ v u : V, inner ℝ (w v) (w u) = inner ℝ v u := by
      intro v u
      have h_dist : dist (f.toFun (v +ᵥ O)) (f.toFun (u +ᵥ O)) = f.r * dist (v +ᵥ O) (u +ᵥ O) := by
        exact f.dist_eq _ _;
      have h_dist : ‖f.r • (w v - w u)‖ = f.r * ‖v - u‖ := by
        simp_all +decide [ dist_eq_norm_vsub ];
        simpa only [ smul_sub ] using h_dist;
      have h_dist : ‖w v - w u‖ = ‖v - u‖ := by
        rw [ norm_smul, Real.norm_of_nonneg f.r_pos.le ] at h_dist ; nlinarith [ f.r_pos ];
      have := norm_sub_sq_real ( w v ) ( w u ) ; have := norm_sub_sq_real v u ; simp_all +decide [ inner_sub_left, inner_sub_right ] ;
    have h_map : ∀ v u : V, w (v + u) = w v + w u := by
      intro v u
      have h_eq : ‖w (v + u) - (w v + w u)‖^2 = 0 := by
        simp_all +decide [ norm_sub_sq_real, inner_add_left, inner_add_right ];
        simp_all +decide [ norm_add_sq_real, inner_add_left, inner_add_right ];
        simp_all +decide [ real_inner_comm, real_inner_self_eq_norm_sq ] ; ring;
      exact sub_eq_zero.mp ( norm_eq_zero.mp ( sq_eq_zero_iff.mp h_eq ) );
    have h_map : ∀ v : V, ∀ c : ℝ, w (c • v) = c • w v := by
      intro v c
      have h_map : ‖w (c • v) - c • w v‖ = 0 := by
        have h_map : ‖w (c • v) - c • w v‖^2 = 0 := by
          simp_all +decide [ norm_sub_sq_real, inner_smul_left, inner_smul_right ];
          simp_all +decide [ norm_smul, inner_self_eq_norm_sq_to_K ];
          cases abs_cases c <;> simp +decide [ * ] <;> ring;
        exact sq_eq_zero_iff.mp h_map;
      exact sub_eq_zero.mp ( norm_eq_zero.mp h_map );
    refine' ⟨ { toFun := w, map_add' := _, map_smul' := _, norm_map' := _ }, hw ⟩ <;> aesop;
  obtain ⟨ L, hL ⟩ := h_map;
  -- Since L is a linear isometry, it is bijective, and hence an equivalence.
  have hL_equiv : Function.Bijective L := by
    have hL_surjective : Function.Surjective L := by
      have hL_surjective : FiniteDimensional ℝ V := by
        exact FiniteDimensional.of_finrank_pos ( by linarith [ Fact.out ( p := Module.finrank ℝ V = 2 ) ] );
      exact LinearMap.surjective_of_injective ( L.injective );
    exact ⟨ L.injective, hL_surjective ⟩;
  exact ⟨ { Equiv.ofBijective L hL_equiv with map_add' := L.map_add, map_smul' := L.map_smul, norm_map' := L.norm_map }, hL ⟩

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

/-
If a linear isometry has determinant -1, it negates oriented angles.
-/
lemma oangle_map_eq_neg_oangle_of_det_neg_one (L : V ≃ₗᵢ[ℝ] V)
  (h : LinearMap.det (L.toLinearEquiv : V →ₗ[ℝ] V) = -1) (u v : V) :
  Orientation.oangle Module.Oriented.positiveOrientation (L u) (L v) = - Orientation.oangle Module.Oriented.positiveOrientation u v := by
  have h_map : Orientation.map (Fin 2) L.toLinearEquiv Module.Oriented.positiveOrientation = -Module.Oriented.positiveOrientation := by
    refine' ( Orientation.map_eq_neg_iff_det_neg _ _ _ ).mpr _;
    · simp +decide [ Fact.out ( p := Module.finrank ℝ V = 2 ) ];
    · linarith;
  -- Apply the fact that the orientation map is -o to rewrite the left-hand side of the equation.
  have h_lhs : (-Module.Oriented.positiveOrientation).oangle (L u) (L v) = Module.Oriented.positiveOrientation.oangle u v := by
    rw [ ← h_map, Orientation.oangle_map ];
    simp +decide;
  rw [ ← h_lhs, Orientation.oangle_neg_orientation_eq_neg ];
  rw [ neg_neg ]

/-
If a linear isometry has determinant 1, it preserves oriented angles.
-/
lemma oangle_map_eq_oangle_of_det_one (L : V ≃ₗᵢ[ℝ] V)
  (h : LinearMap.det (L.toLinearEquiv : V →ₗ[ℝ] V) = 1) (u v : V) :
  Orientation.oangle Module.Oriented.positiveOrientation (L u) (L v) = Orientation.oangle Module.Oriented.positiveOrientation u v := by
  have h_det_L_eq_one : ∀ (L : V ≃ₗᵢ[ℝ] V), LinearMap.det (L.toLinearEquiv : V →ₗ[ℝ] V) = 1 → ∀ (u v : V), Module.Oriented.positiveOrientation.oangle (L u) (L v) = Module.Oriented.positiveOrientation.oangle u v := by
    intros L hL u v
    have h_det_L_eq_one : LinearMap.det (L.toLinearEquiv : V →ₗ[ℝ] V) = 1 := by
      exact hL;
    cases' ‹Module.Oriented ℝ V ( Fin 2 ) › with b hb;
    simp +zetaDelta at *;
    rw [ Orientation.oangle, Orientation.oangle ];
    have h_det_L_eq_one : ∀ (u v : V), b.kahler (L u) (L v) = b.kahler u v := by
      intro u v;
      have := b.areaForm_comp_linearIsometryEquiv L;
      simp_all +decide [ Orientation.kahler ];
      exact L.inner_map_map u v;
    rw [ h_det_L_eq_one ];
  exact h_det_L_eq_one L h u v

/-
If a linear isometry has determinant 1, it commutes with rotation.
-/
lemma linear_isometry_rotation_commute_of_det_one (L : V ≃ₗᵢ[ℝ] V)
  (h : LinearMap.det (L.toLinearEquiv : V →ₗ[ℝ] V) = 1) (θ : Real.Angle) (v : V) :
  L (Orientation.rotation Module.Oriented.positiveOrientation θ v) = Orientation.rotation Module.Oriented.positiveOrientation θ (L v) := by
  have h_comm : ∀ u v : V, Orientation.oangle Module.Oriented.positiveOrientation (L u) (L v) = Orientation.oangle Module.Oriented.positiveOrientation u v := by
    apply oangle_map_eq_oangle_of_det_one;
    exact h;
  cases' eq_or_ne v 0 with hv hv <;> simp_all +decide;
  have h_comm : ∀ θ : Real.Angle, ∀ v : V, v ≠ 0 → L (Module.Oriented.positiveOrientation.rotation θ v) = Module.Oriented.positiveOrientation.rotation θ (L v) := by
    intro θ v hv
    have h_comm : Orientation.oangle Module.Oriented.positiveOrientation (L v) (L (Module.Oriented.positiveOrientation.rotation θ v)) = θ := by
      rw [ h_comm, Orientation.oangle_rotation_self_right ];
      exact hv;
    have h_comm : ∀ u v : V, u ≠ 0 → v ≠ 0 → Orientation.oangle Module.Oriented.positiveOrientation u v = θ → ‖u‖ = ‖v‖ → v = Module.Oriented.positiveOrientation.rotation θ u := by
      intro u v hu hv hθ hnorm
      have h_comm : v = Module.Oriented.positiveOrientation.rotation θ u := by
        rw [ ← hθ, eq_comm ];
        exact (Orientation.rotation_oangle_eq_iff_norm_eq positiveOrientation u v).mpr hnorm
      exact h_comm;
    apply h_comm;
    · exact L.map_ne_zero_iff.mpr hv;
    · simp_all +decide [ LinearIsometryEquiv.map_eq_zero_iff ];
    · assumption;
    · simp +decide [ hv, L.norm_map ];
  exact h_comm θ v hv

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
  have h_det : LinearMap.det (L.toLinearEquiv : V →ₗ[ℝ] V) = 1 ∨ LinearMap.det (L.toLinearEquiv : V →ₗ[ℝ] V) = -1 := by
    exact linear_isometry_det_eq_one_or_neg_one L;
  cases' h_det with h_det h_det;
  · -- Since L is orientation-preserving, the angle between Lu and Lw is the same as the angle between u and w.
    have h_angle_eq : (Module.Oriented.positiveOrientation.oangle (L u) (L w)).toReal = (Module.Oriented.positiveOrientation.oangle u w).toReal := by
      apply (oangle_map_eq_oangle_of_det_one L h_det) u w |> congr_arg Real.Angle.toReal;
    rw [ h_angle_eq, linear_isometry_rotation_commute_of_det_one L h_det ];
  · have h_anticausal : ∀ u w : V, u ≠ 0 → w ≠ 0 → Module.Oriented.positiveOrientation.oangle u w ≠ Real.pi → Orientation.oangle Module.Oriented.positiveOrientation (L u) (L w) = -Orientation.oangle Module.Oriented.positiveOrientation u w := by
      exact fun u w a a a ↦ oangle_map_eq_neg_oangle_of_det_neg_one L h_det u w;
    rw [ h_anticausal u w h_u h_w h_not_pi, toReal_neg_eq_neg_toReal ];
    · convert linear_isometry_rotation_anticommute_of_det_neg_one L h_det _ _ using 2 ; ring;
      norm_num [ neg_div ];
    · exact h_not_pi

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
  refine' Set.Subset.antisymm _ _;
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy;
    simp_all +decide [ AffineSubspace.mem_mk', Submodule.mem_span_singleton ];
    obtain ⟨ a, ha ⟩ := hx;
    -- By definition of similarity, we know that $f(x) = f(p) + r \cdot L(v)$ for some linear isometry $L$.
    obtain ⟨ L, hL ⟩ := similarity_decomposition f p;
    use a;
    rw [ show x = a • v +ᵥ p by rw [ ha, vsub_vadd ] ] ; simp +decide [ hL ] ;
    rw [ SMulCommClass.smul_comm ];
  · simp +decide [ Set.subset_def, AffineSubspace.mem_mk', Submodule.mem_span_singleton ];
    intro x a ha;
    -- By definition of similarity, we know that $f.toFun (a • v +ᵥ p) = a • (f.toFun (v +ᵥ p) -ᵥ f.toFun p) +ᵥ f.toFun p$.
    have h_sim : f.toFun (a • v +ᵥ p) = a • (f.toFun (v +ᵥ p) -ᵥ f.toFun p) +ᵥ f.toFun p := by
      have := similarity_decomposition f p;
      obtain ⟨ L, hL ⟩ := this; simp +decide [ hL, smul_smul ] ;
      rw [ mul_comm ];
    aesop

/-
A similarity transformation maps the intersection of two lines (assuming unique intersection) to the intersection of the image lines.
-/
lemma similarity_map_lineIntersection (f : Similarity P) (p1 : P) (v1 : V) (p2 : P) (v2 : V)
  (h_unique : ∃! p, p ∈ AffineSubspace.mk' p1 (Submodule.span ℝ {v1}) ∧ p ∈ AffineSubspace.mk' p2 (Submodule.span ℝ {v2})) :
  f (lineIntersection p1 v1 p2 v2) = lineIntersection (f p1) (f (v1 +ᵥ p1) -ᵥ f p1) (f p2) (f (v2 +ᵥ p2) -ᵥ f p2) := by
  have h_image : f.toFun '' (AffineSubspace.mk' p1 (Submodule.span ℝ {v1})) = AffineSubspace.mk' (f.toFun p1) (Submodule.span ℝ {f.toFun (v1 +ᵥ p1) -ᵥ f.toFun p1}) := by
    exact similarity_map_line_eq f p1 v1;
  have h_image2 : f.toFun '' (AffineSubspace.mk' p2 (Submodule.span ℝ {v2})) = AffineSubspace.mk' (f.toFun p2) (Submodule.span ℝ {f.toFun (v2 +ᵥ p2) -ᵥ f.toFun p2}) := by
    exact similarity_map_line_eq f p2 v2;
  -- Since the intersection point is unique, the image must be the same as the intersection of the images.
  have h_unique_image : ∃! p : P, p ∈ AffineSubspace.mk' (f.toFun p1) (Submodule.span ℝ {f.toFun (v1 +ᵥ p1) -ᵥ f.toFun p1}) ∧ p ∈ AffineSubspace.mk' (f.toFun p2) (Submodule.span ℝ {f.toFun (v2 +ᵥ p2) -ᵥ f.toFun p2}) := by
    obtain ⟨ p, hp₁, hp₂ ⟩ := h_unique;
    refine' ⟨ f.toFun p, _, _ ⟩;
    · exact ⟨ h_image.subset ⟨ p, hp₁.1, rfl ⟩, h_image2.subset ⟨ p, hp₁.2, rfl ⟩ ⟩;
    · intro y hy;
      obtain ⟨ x, hx₁, hx₂ ⟩ := h_image.symm.subset hy.1;
      obtain ⟨ z, hz₁, hz₂ ⟩ := h_image2.symm.subset hy.2;
      have := f.dist_eq x z; simp_all +decide ;
      cases this <;> simp_all +decide [ f.r_pos.ne' ];
  have h_unique_image : f.toFun (lineIntersection p1 v1 p2 v2) ∈ AffineSubspace.mk' (f.toFun p1) (Submodule.span ℝ {f.toFun (v1 +ᵥ p1) -ᵥ f.toFun p1}) ∧ f.toFun (lineIntersection p1 v1 p2 v2) ∈ AffineSubspace.mk' (f.toFun p2) (Submodule.span ℝ {f.toFun (v2 +ᵥ p2) -ᵥ f.toFun p2}) := by
    have h_unique_image : lineIntersection p1 v1 p2 v2 ∈ AffineSubspace.mk' p1 (Submodule.span ℝ {v1}) ∧ lineIntersection p1 v1 p2 v2 ∈ AffineSubspace.mk' p2 (Submodule.span ℝ {v2}) := by
      exact Classical.epsilon_spec h_unique.exists;
    exact ⟨ h_image.subset ⟨ _, h_unique_image.1, rfl ⟩, h_image2.subset ⟨ _, h_unique_image.2, rfl ⟩ ⟩;
  exact ExistsUnique.unique ‹_› h_unique_image ( Classical.epsilon_spec ( show ∃ p : P, p ∈ AffineSubspace.mk' ( f.toFun p1 ) ( Submodule.span ℝ { f.toFun ( v1 +ᵥ p1 ) -ᵥ f.toFun p1 } ) ∧ p ∈ AffineSubspace.mk' ( f.toFun p2 ) ( Submodule.span ℝ { f.toFun ( v2 +ᵥ p2 ) -ᵥ f.toFun p2 } ) from ⟨ _, h_unique_image ⟩ ) )

/-
The oriented angle between a rotated vector and a rotated negative vector is the difference of angles plus pi.
-/
lemma oangle_rotation_neg (u : V) (a b : Real.Angle) (h : u ≠ 0) :
  Orientation.oangle Module.Oriented.positiveOrientation (Orientation.rotation Module.Oriented.positiveOrientation a u) (Orientation.rotation Module.Oriented.positiveOrientation b (-u)) = b - a + π := by
  have h_rot_neg : ∀ (u : V) (θ : Real.Angle), (Module.Oriented.positiveOrientation.rotation θ) (-u) = (Module.Oriented.positiveOrientation.rotation (θ + Real.pi)) u := by
    simp +decide [ Orientation.rotation ];
  simp_all +decide [ sub_add, add_comm, add_left_comm, add_assoc ];
  abel1

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
  convert conway_oangle_gap_Q Q R P_pt b c a _ _ _ _ _ _ _ using 1;
  any_goals linarith;
  · exact ⟨ fun h _ _ _ => h, fun h => h ( by linarith ) ( by linarith ) ( by
      convert h_orientation using 1;
      rw [ ← equilateral_oangle_cyclic ];
      exact h_equilateral ) ⟩;
  · unfold isEquilateral at *; aesop;
  · cases h_equilateral ; aesop

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
The sine of the oriented angle is the area form divided by the product of the norms.
-/
lemma sin_oangle_eq_areaForm_div_norm_mul_norm (u v : V) :
  Real.sin (Orientation.oangle Module.Oriented.positiveOrientation u v).toReal =
  (Orientation.areaForm Module.Oriented.positiveOrientation u v) / (‖u‖ * ‖v‖) := by
  simp ( config := { decide := Bool.true } ) [ Orientation.oangle ];
  rw [ Complex.sin_arg ];
  congr;
  · simp ( config := { decide := Bool.true } ) [ Orientation.areaForm, Orientation.kahler ];
  · exact Orientation.norm_kahler positiveOrientation u v

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
  have := @linear_independent_rotated_vectors ( V );
  specialize this ( -u ) ( b : ℝ ) ( a : ℝ ) ; simp_all +decide [ add_comm, neg_smul ];
  rw [ Fintype.linearIndependent_iff ] at *;
  intro g hg i; specialize this ( fun i => g ( 1 - i ) ) ( by simpa [ Fin.sum_univ_succ ] using by simpa [ add_comm, Fin.sum_univ_succ ] using hg ) ( 1 - i ) ; fin_cases i <;> tauto;

/-
The oriented angle is equal to the unoriented angle or its negation.
-/
lemma oangle_eq_angle_or_neg_angle (A B C : P) (hAB : A ≠ B) (hCB : C ≠ B) :
  Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ B) (C -ᵥ B) = (angle A B C : Real.Angle) ∨
  Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ B) (C -ᵥ B) = -(angle A B C : Real.Angle) := by
  by_contra! h;
  simp_all +decide [ EuclideanGeometry.angle ];
  have := @oangle_eq_angle_or_eq_neg_angle V;
  exact h.2 ( this hAB hCB |> Or.resolve_left <| h.1 )

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
  have hRA : dist R (conwayVertexA Q R a b c) = conwayLargeSideRA c a := by
    apply conway_step3_RA_matches;
    · cases h_equilateral ; aesop;
    · exact h_a_pos;
    · exact h_b_pos;
    · exact h_c_pos;
    · exact h_sum
  have hRB : dist R (conwayVertexB R P_pt a b c) = conwayLargeSideRB c b := by
    apply conway_step3_RB_matches;
    · simp_all +decide [ dist_comm, isEquilateral ];
    · exact h_a_pos;
    · exact h_b_pos;
    · exact h_c_pos;
    · exact h_sum
  have hRAB : angle (conwayVertexA Q R a b c) R (conwayVertexB R P_pt a b c) = conwayLargeAngleR c := by
    convert conway_gap_angle_R_correct P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation using 1
  have hRAB_a : angle R (conwayVertexA Q R a b c) (conwayVertexB R P_pt a b c) = a := by
    apply (conway_large_triangle_R_angles (conwayVertexA Q R a b c) (conwayVertexB R P_pt a b c) R a b c h_a_pos h_b_pos h_c_pos h_sum hRA hRB hRAB).left;
  have h_distinct : R ≠ conwayVertexA Q R a b c ∧ conwayVertexA Q R a b c ≠ conwayVertexB R P_pt a b c ∧ conwayVertexB R P_pt a b c ≠ R := by
    refine' ⟨ _, _, _ ⟩;
    · intro h;
      norm_num [ ← h ] at *;
      linarith;
    · rintro h; simp_all +decide [ dist_comm ];
      linarith;
    · rintro h; simp_all +decide [ conwayLargeSideRB ];
      exact absurd hRB ( ne_of_lt ( div_pos ( Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith ) ) ( Real.sin_pos_of_pos_of_lt_pi ( by linarith ) ( by linarith ) ) ) );
  apply conway_triangle_orientation_lemma;
  exact h_distinct;
  rotate_left;
  exact ⟨ h_a_pos, h_a_lt ⟩;
  exact ⟨ h_b_pos, h_b_lt ⟩;
  rotate_left;
  exact hRAB_a;
  have hRAB_b : angle (conwayVertexA Q R a b c) (conwayVertexB R P_pt a b c) R = b := by
    have := conway_large_triangle_R_angles (conwayVertexA Q R a b c) (conwayVertexB R P_pt a b c) R a b c h_a_pos h_b_pos h_c_pos h_sum hRA hRB hRAB
    rw [ ← this.2, angle_comm ];
    grind;
  exact hRAB_b;
  exact c + 2 * Real.pi / 3;
  · linarith;
  · convert conway_oangle_gap_R P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation using 1

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
If a point lies on two lines and is the unique such point, then `lineIntersection` returns it.
-/
lemma lineIntersection_eq {p1 p2 : P} {v1 v2 : V} {p : P}
  (h1 : p ∈ AffineSubspace.mk' p1 (Submodule.span ℝ {v1}))
  (h2 : p ∈ AffineSubspace.mk' p2 (Submodule.span ℝ {v2}))
  (h_unique : ∀ q, q ∈ AffineSubspace.mk' p1 (Submodule.span ℝ {v1}) → q ∈ AffineSubspace.mk' p2 (Submodule.span ℝ {v2}) → q = p) :
  lineIntersection p1 v1 p2 v2 = p := by
    exact h_unique _ ( Classical.epsilon_spec ( show ∃ q, q ∈ AffineSubspace.mk' p1 ( Submodule.span ℝ { v1 } ) ∧ q ∈ AffineSubspace.mk' p2 ( Submodule.span ℝ { v2 } ) from ⟨ p, h1, h2 ⟩ ) |>.1 ) ( Classical.epsilon_spec ( show ∃ q, q ∈ AffineSubspace.mk' p1 ( Submodule.span ℝ { v1 } ) ∧ q ∈ AffineSubspace.mk' p2 ( Submodule.span ℝ { v2 } ) from ⟨ p, h1, h2 ⟩ ) |>.2 )

/-
The area form of the vectors forming the angles of a triangle is cyclically invariant (twice the signed area).
-/
lemma areaForm_triangle_cyclic (A B C : P) :
  (Orientation.areaForm Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)) =
  (Orientation.areaForm Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)) ∧
  (Orientation.areaForm Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)) =
  (Orientation.areaForm Module.Oriented.positiveOrientation (A -ᵥ C) (B -ᵥ C)) := by
  constructor;
  · have h_area_form : ∀ u v : V, (Module.Oriented.positiveOrientation.areaForm : V → V →ₗ[ℝ] ℝ) u v = - (Module.Oriented.positiveOrientation.areaForm v u) := by
      exact fun u v ↦ Orientation.areaForm_swap positiveOrientation u v;
    rw [ show C -ᵥ A = ( C -ᵥ B ) + ( B -ᵥ A ) by rw [ vsub_add_vsub_cancel ] ] ; simp +decide [ add_comm, add_left_comm, add_assoc ];
    rw [ h_area_form ];
    rw [ show A -ᵥ B = - ( B -ᵥ A ) by rw [ neg_vsub_eq_vsub_rev ], map_neg ];
  · have := Orientation.areaForm_swap Module.Oriented.positiveOrientation ( C -ᵥ B ) ( A -ᵥ B );
    have := Orientation.areaForm_swap Module.Oriented.positiveOrientation ( A -ᵥ C ) ( B -ᵥ C ) ; simp_all +decide [ sub_eq_iff_eq_add ];
    rw [ show A -ᵥ B = ( A -ᵥ C ) + ( C -ᵥ B ) by simp +decide [ sub_add_sub_cancel ], map_add ] ; simp +decide;
    rw [ show C -ᵥ B = - ( B -ᵥ C ) by simp +decide, map_neg ] ; ring;
    linarith

/-
The sines of the oriented angles of a nondegenerate triangle have the same sign.
-/
lemma sin_oangle_triangle_same_sign (A B C : P) (h_nd : NondegenerateTriangle A B C) :
  Real.sign (Real.sin (Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)).toReal) =
  Real.sign (Real.sin (Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)).toReal) ∧
  Real.sign (Real.sin (Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)).toReal) =
  Real.sign (Real.sin (Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ C) (B -ᵥ C)).toReal) := by
  have h_cyclic : (Orientation.areaForm Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)) = (Orientation.areaForm Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)) ∧ (Orientation.areaForm Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)) = (Orientation.areaForm Module.Oriented.positiveOrientation (A -ᵥ C) (B -ᵥ C)) := by
    exact areaForm_triangle_cyclic A B C;
  have h_sign_eq : ∀ (u v : V), u ≠ 0 → v ≠ 0 → Real.sign (Real.sin (Orientation.oangle Module.Oriented.positiveOrientation u v).toReal) = Real.sign (Orientation.areaForm Module.Oriented.positiveOrientation u v) := by
    intro u v hu hv; rw [ sin_oangle_eq_areaForm_div_norm_mul_norm u v ] ;
    simp +decide [ Real.sign, hu, hv ];
    split_ifs <;> first | linarith | nlinarith [ norm_pos_iff.2 hu, norm_pos_iff.2 hv, mul_pos ( norm_pos_iff.2 hu ) ( norm_pos_iff.2 hv ), div_mul_cancel₀ ( ( Module.Oriented.positiveOrientation.areaForm u ) v ) ( mul_ne_zero ( norm_ne_zero_iff.2 hu ) ( norm_ne_zero_iff.2 hv ) ) ] ;
  by_cases hA : A = B <;> by_cases hB : B = C <;> by_cases hC : A = C <;> simp_all +decide [ sub_eq_zero ];
  rw [ h_sign_eq, h_sign_eq ] <;> simp_all +decide [ sub_eq_zero ];
  · tauto;
  · exact Ne.symm hA;
  · tauto

/-
The oriented angles of a nondegenerate triangle are either all positive or all negative.
-/
lemma oangle_triangle_sign_consistent (A B C : P) (h_nd : NondegenerateTriangle A B C) :
  let α := (Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)).toReal
  let β := (Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)).toReal
  let γ := (Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ C) (B -ᵥ C)).toReal
  (0 < α ∧ 0 < β ∧ 0 < γ) ∨ (α < 0 ∧ β < 0 ∧ γ < 0) := by
  have h_quad : Real.sign (Real.sin (Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)).toReal) = Real.sign (Real.sin (Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)).toReal) ∧
                     Real.sign (Real.sin (Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)).toReal) = Real.sign (Real.sin (Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ C) (B -ᵥ C)).toReal) := by
                       exact sin_oangle_triangle_same_sign A B C h_nd;
  unfold Real.sign at h_quad;
  split_ifs at h_quad <;> norm_num at h_quad;
  · refine' Or.inr ⟨ _, _, _ ⟩ <;> contrapose! h_quad;
    · exact absurd ‹Real.sin _ < 0› ( not_lt_of_ge ( Real.sin_nonneg_of_nonneg_of_le_pi h_quad ( by linarith [ Real.pi_pos, Real.Angle.toReal_le_pi ( Module.Oriented.positiveOrientation.oangle ( B -ᵥ A ) ( C -ᵥ A ) ) ] ) ) );
    · exact ‹Real.sin ( Module.Oriented.positiveOrientation.oangle ( C -ᵥ B ) ( A -ᵥ B ) |> Real.Angle.toReal ) < 0›.not_le ( Real.sin_nonneg_of_nonneg_of_le_pi h_quad ( by linarith [ Real.pi_pos, ( show ( Module.Oriented.positiveOrientation.oangle ( C -ᵥ B ) ( A -ᵥ B ) |> Real.Angle.toReal ) ≤ Real.pi from by linarith [ Real.pi_pos, ( show ( Module.Oriented.positiveOrientation.oangle ( C -ᵥ B ) ( A -ᵥ B ) |> Real.Angle.toReal ) ≤ Real.pi from by linarith [ Real.pi_pos, ( show ( Module.Oriented.positiveOrientation.oangle ( C -ᵥ B ) ( A -ᵥ B ) |> Real.Angle.toReal ) ≤ Real.pi from by linarith [ Real.pi_pos, ( show ( Module.Oriented.positiveOrientation.oangle ( C -ᵥ B ) ( A -ᵥ B ) |> Real.Angle.toReal ) ≤ Real.pi from by linarith [ Real.pi_pos, Real.Angle.toReal_le_pi ( Module.Oriented.positiveOrientation.oangle ( C -ᵥ B ) ( A -ᵥ B ) ) ] ) ] ) ] ) ] ) ] ) );
    · exact ‹Real.sin ( Module.Oriented.positiveOrientation.oangle ( A -ᵥ C ) ( B -ᵥ C ) |> Real.Angle.toReal ) < 0›.not_le ( Real.sin_nonneg_of_nonneg_of_le_pi h_quad ( by linarith [ Real.pi_pos, Real.Angle.toReal_le_pi ( Module.Oriented.positiveOrientation.oangle ( A -ᵥ C ) ( B -ᵥ C ) ) ] ) );
  · have h_angles_pos : ∀ θ : Real.Angle, 0 < Real.sin θ.toReal → 0 < θ.toReal := by
      intro θ hθ_pos
      by_contra hθ_neg;
      exact hθ_pos.not_le ( Real.sin_nonpos_of_nonpos_of_neg_pi_le ( le_of_not_gt hθ_neg ) ( by linarith [ Real.pi_pos, θ.toReal_mem_Ioc.1 ] ) );
    exact Or.inl ⟨ h_angles_pos _ ‹_›, h_angles_pos _ ‹_›, h_angles_pos _ ‹_› ⟩;
  · have h_sin_pos : Real.sin (Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)).toReal ≠ 0 := by
      have := triangle_angle_ne_zero_or_pi A B C h_nd;
      simp +zetaDelta at *;
      rw [ Real.Angle.sin_eq_zero_iff ];
      tauto;
    exact False.elim ( h_sin_pos ( by linarith ) )

/-
The trisector vectors at adjacent vertices of a nondegenerate triangle are linearly independent.
-/
lemma trisector_vectors_linear_independent (A B C : P) (h_nd : NondegenerateTriangle A B C) :
  LinearIndependent ℝ ![trisectorVector A B C, trisectorVector B A C] := by
  have h_a_pos : 0 < (oangle B A C).toReal / 3 ∧ 0 < -(oangle A B C).toReal / 3 ∨ 0 < -(oangle B A C).toReal / 3 ∧ 0 < (oangle A B C).toReal / 3 := by
    have h_angle_signs : let α := (Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A)).toReal; let β := (Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)).toReal; let γ := (Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ C) (B -ᵥ C)).toReal; (0 < α ∧ 0 < β ∧ 0 < γ) ∨ (α < 0 ∧ β < 0 ∧ γ < 0) := by
      exact
        let α := (positiveOrientation.oangle (B -ᵥ A) (C -ᵥ A)).toReal;
        let β := (positiveOrientation.oangle (C -ᵥ B) (A -ᵥ B)).toReal;
        let γ := (positiveOrientation.oangle (A -ᵥ C) (B -ᵥ C)).toReal;
        oangle_triangle_sign_consistent A B C h_nd;
    cases' h_angle_signs with h_pos h_neg;
    · have h_neg : (Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ B) (C -ᵥ B)).toReal = - (Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)).toReal := by
        rw [ Orientation.oangle_rev ];
        rw [ toReal_neg_eq_neg_toReal ];
        intro h;
        have := oangle_eq_pi_iff_angle_eq_pi.mp h;
        rw [ EuclideanGeometry.angle, ] at this;
        rw [ InnerProductGeometry.angle_eq_pi_iff ] at this;
        obtain ⟨ r, hr, hr' ⟩ := this.2;
        have h_collinear : Collinear ℝ {A, B, C} := by
          rw [ collinear_iff_exists_forall_eq_smul_vadd ];
          use B, C -ᵥ B;
          simp +zetaDelta at *;
          exact ⟨ ⟨ r, by rw [ ← hr', vsub_vadd ] ⟩, ⟨ 0, by simp +decide ⟩, ⟨ 1, by simp +decide ⟩ ⟩;
        exact h_nd h_collinear;
      exact Or.inl ⟨ by linarith!, by linarith! ⟩;
    · simp_all +decide [ oangle ];
      have h_angle_signs : (Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ B) (C -ᵥ B)).toReal = - (Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B)).toReal := by
        rw [ Orientation.oangle_rev ];
        rw [ toReal_neg_eq_neg_toReal ];
        intro h;
        rw [ h ] at h_neg ; norm_num at h_neg;
        linarith [ Real.pi_pos ];
      exact Or.inr ( by linarith! );
  rcases h_a_pos with h|h <;> simp_all +decide [ trisectorVector ];
  · convert linear_independent_rotated_vectors ( B -ᵥ A ) ( ( ∡ B A C |> Real.Angle.toReal ) / 3 ) ( - ( ∡ A B C |> Real.Angle.toReal ) / 3 ) _ _ _ _ using 1 <;> norm_num [ h ];
    · norm_num [ div_eq_mul_inv, Real.Angle.coe_neg ];
    · rintro rfl; simp_all +decide [ NondegenerateTriangle ];
    · linarith [ Real.pi_pos, Real.Angle.toReal_le_pi ( ∡ B A C ), Real.Angle.toReal_le_pi ( ∡ A B C ), Real.Angle.neg_pi_lt_toReal ( ∡ B A C ), Real.Angle.neg_pi_lt_toReal ( ∡ A B C ) ];
  · convert linear_independent_rotated_vectors_variant ( B -ᵥ A ) ( - ( ( ∡ B A C |> Real.Angle.toReal ) / 3 ) ) ( ( ∡ A B C |> Real.Angle.toReal ) / 3 ) ?_ ?_ ?_ using 1;
    · constructor <;> intro h';
      · intro h''; convert h' using 1; ext i; fin_cases i <;> simp +decide [ * ] ;
      · convert h' ( by linarith [ Real.pi_pos, ( show ( ∡ B A C |> Real.Angle.toReal ) ≥ -Real.pi from by linarith [ Real.pi_pos, ( show ( ∡ B A C |> Real.Angle.toReal ) ≥ -Real.pi from by linarith [ Real.pi_pos, Real.Angle.neg_pi_lt_toReal ( ∡ B A C ) ] ) ] ), ( show ( ∡ A B C |> Real.Angle.toReal ) ≤ Real.pi from by linarith [ Real.pi_pos, ( show ( ∡ A B C |> Real.Angle.toReal ) ≤ Real.pi from by linarith [ Real.pi_pos, Real.Angle.toReal_le_pi ( ∡ A B C ) ] ) ] ) ] ) using 1;
        norm_num [ neg_div, neg_sub ];
    · exact vsub_ne_zero.mpr ( by aesop );
    · linarith;
    · linarith

/-
Two lines in a 2D plane with linearly independent direction vectors intersect at a unique point.
-/
lemma lines_intersect_unique_of_linearIndependent (p1 p2 : P) (v1 v2 : V)
  (h_indep : LinearIndependent ℝ ![v1, v2]) :
  ∃! p, p ∈ AffineSubspace.mk' p1 (Submodule.span ℝ {v1}) ∧
        p ∈ AffineSubspace.mk' p2 (Submodule.span ℝ {v2}) := by
  have h_unique : ∀ (p q : P), p ∈ AffineSubspace.mk' p1 (Submodule.span ℝ {v1}) → p ∈ AffineSubspace.mk' p2 (Submodule.span ℝ {v2}) → q ∈ AffineSubspace.mk' p1 (Submodule.span ℝ {v1}) → q ∈ AffineSubspace.mk' p2 (Submodule.span ℝ {v2}) → p = q := by
    intro p q hp hp' hq hq'
    have h_eq : p -ᵥ p1 ∈ Submodule.span ℝ {v1} ∧ p -ᵥ p2 ∈ Submodule.span ℝ {v2} ∧ q -ᵥ p1 ∈ Submodule.span ℝ {v1} ∧ q -ᵥ p2 ∈ Submodule.span ℝ {v2} := by
      exact ⟨ by simpa using hp, by simpa using hp', by simpa using hq, by simpa using hq' ⟩;
    simp_all +decide [ Submodule.mem_span_singleton ];
    obtain ⟨ ⟨ a, ha ⟩, ⟨ b, hb ⟩, ⟨ c, hc ⟩, ⟨ d, hd ⟩ ⟩ := h_eq;
    have h_eq : (a - c) • v1 + (d - b) • v2 = 0 := by
      simp +decide [ sub_smul, ha, hb, hc, hd ];
    have := Fintype.linearIndependent_iff.mp h_indep;
    specialize this ( fun i => if i = 0 then a - c else d - b ) ; simp_all +decide [ sub_eq_iff_eq_add ];
  -- Since the directions are independent, the lines intersect at exactly one point.
  obtain ⟨p, hp⟩ : ∃ p : P, p ∈ AffineSubspace.mk' p1 (Submodule.span ℝ {v1}) ∧ p ∈ AffineSubspace.mk' p2 (Submodule.span ℝ {v2}) := by
    -- Since $v1$ and $v2$ are linearly independent, there exist scalars $a$ and $b$ such that $a * v1 + b * v2 = v$, where $v$ is the vector from $p1$ to $p2$.
    obtain ⟨a, b, hv⟩ : ∃ a b : ℝ, a • v1 + b • v2 = p2 -ᵥ p1 := by
      have h_basis : Submodule.span ℝ (Set.range ![v1, v2]) = ⊤ := by
        convert Submodule.eq_top_of_finrank_eq ( _ );
        · exact FiniteDimensional.of_finrank_pos ( by linarith [ Fact.out ( p := Module.finrank ℝ V = 2 ) ] );
        · rw [ finrank_span_eq_card ] <;> norm_num [ h_indep ];
          exact Eq.symm ( Fact.out : Module.finrank ℝ V = 2 );
      have := Submodule.mem_span_range_iff_exists_fun ℝ |>.1 ( show p2 -ᵥ p1 ∈ Submodule.span ℝ ( Set.range ![v1, v2] ) from h_basis.symm ▸ Submodule.mem_top ) ; aesop;
    refine' ⟨ a • v1 +ᵥ p1, _, _ ⟩ <;> simp_all +decide [ AffineSubspace.mem_mk' ];
    · exact Submodule.smul_mem _ _ ( Submodule.mem_span_singleton_self _ );
    · simp_all +decide [ ← eq_sub_iff_add_eq', vsub_vadd_eq_vsub_sub ];
      simp_all +decide [ Submodule.mem_span_singleton, vadd_vsub_assoc ];
      exact ⟨ -b, by simp +decide [ hv, add_comm, add_left_comm, add_assoc, sub_eq_add_neg ] ⟩;
  exact ⟨ p, hp, fun q hq => h_unique q p hq.1 hq.2 hp.1 hp.2 ⟩

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
If a point lies on two lines with linearly independent direction vectors, it is the unique intersection point returned by `lineIntersection`.
-/
lemma lineIntersection_unique_of_linearIndependent {p1 p2 : P} {v1 v2 : V} {p : P}
  (h1 : p ∈ AffineSubspace.mk' p1 (Submodule.span ℝ {v1}))
  (h2 : p ∈ AffineSubspace.mk' p2 (Submodule.span ℝ {v2}))
  (h_indep : LinearIndependent ℝ ![v1, v2]) :
  lineIntersection p1 v1 p2 v2 = p := by
  apply_rules [ lineIntersection_eq ];
  intro q hq1 hq2;
  simp_all +decide [ AffineSubspace.mem_mk', Submodule.mem_span_singleton ];
  obtain ⟨ a, ha ⟩ := h1
  obtain ⟨ b, hb ⟩ := h2
  obtain ⟨ c, hc ⟩ := hq1
  obtain ⟨ d, hd ⟩ := hq2;
  have h_eq : (c - a) • v1 = (d - b) • v2 := by
    simp_all +decide [ sub_smul, vsub_vadd_eq_vsub_sub ];
  have := linearIndependent_iff'.mp h_indep;
  specialize this { 0, 1 } ( fun i => if i = 0 then c - a else - ( d - b ) ) ; simp_all +decide [ sub_eq_iff_eq_add ];
  simp_all +decide [ sub_smul, add_smul ]

/-
A similarity transformation preserves the property of being an equilateral triangle.
-/
lemma similarity_preserves_isEquilateral (f : Similarity P) (A B C : P)
  (h : isEquilateral A B C) : isEquilateral (f A) (f B) (f C) := by
    unfold isEquilateral at *;
    cases f ; aesop

/-
The sine of the unoriented angle between two vectors is the absolute value of the area form divided by the product of the norms.
-/
lemma sin_angle_eq_abs_areaForm_div_norms (u v : V) (hu : u ≠ 0) (hv : v ≠ 0) :
  Real.sin (InnerProductGeometry.angle u v) = |Orientation.areaForm Module.Oriented.positiveOrientation u v| / (‖u‖ * ‖v‖) := by
  have h_sin_area : (Module.Oriented.positiveOrientation.areaForm u v) ^ 2 = (‖u‖ * ‖v‖ * Real.sin (InnerProductGeometry.angle u v)) ^ 2 := by
    rw [ mul_pow, Real.sin_sq, mul_pow, mul_comm ];
    have := oangle_eq_angle_or_neg_angle u 0 v;
    cases' this hu hv with h h <;> rw [ ← Real.sin_sq ];
    · have := @sin_oangle_eq_areaForm_div_norm_mul_norm;
      have := @this V _ _ _ _ u v; rw [ eq_div_iff ( mul_ne_zero ( norm_ne_zero_iff.mpr hu ) ( norm_ne_zero_iff.mpr hv ) ) ] at this; rw [ ← this ] ; ring;
      simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
      simp +decide [ EuclideanGeometry.angle, hu, hv ];
    · have := sin_oangle_eq_areaForm_div_norm_mul_norm u v; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
      rw [ eq_div_iff ( mul_ne_zero ( norm_ne_zero_iff.mpr hu ) ( norm_ne_zero_iff.mpr hv ) ) ] at this;
      rw [ ← this ] ; ring;
      rw [ mul_assoc, mul_comm ];
      simp +decide [ EuclideanGeometry.angle, Real.sin_arccos ];
  rw [ ← sq_eq_sq₀, div_pow ];
  · rw [ eq_div_iff ( by positivity ), mul_pow ] ; rw [ sq_abs ] ; linarith;
  · exact Real.sin_nonneg_of_nonneg_of_le_pi ( InnerProductGeometry.angle_nonneg u v ) ( InnerProductGeometry.angle_le_pi u v );
  · positivity

/-
The ratio of a side length to the sine of the opposite angle is equal to the product of the three side lengths divided by the absolute value of the area form of the vectors at the vertex.
-/
lemma dist_div_sin_eq_prod_dist_div_abs_area (A B C : P)
  (h_nd : NondegenerateTriangle A B C) :
  dist A B / Real.sin (angle B C A) = (dist A B * dist B C * dist C A) / |Orientation.areaForm Module.Oriented.positiveOrientation (B -ᵥ C) (A -ᵥ C)| := by
  have := @sin_angle_eq_abs_areaForm_div_norms;
  specialize @this V _ _ _ _ ( B -ᵥ C ) ( A -ᵥ C ) ; simp_all +decide [ dist_eq_norm_vsub ];
  rw [ show ∠ B C A = InnerProductGeometry.angle ( B -ᵥ C ) ( A -ᵥ C ) by rfl, this ];
  · field_simp;
    rw [ ← norm_neg ( C -ᵥ A ), neg_vsub_eq_vsub_rev ];
  · -- Since $A$, $B$, and $C$ are distinct points forming a nondegenerate triangle, $B$ cannot be equal to $C$.
    intro h_eq
    have := h_nd
    simp_all +decide [ NondegenerateTriangle ];
    exact h_nd ( collinear_pair ℝ A C );
  · rintro rfl; simp_all +decide [ NondegenerateTriangle ];
    exact h_nd ( collinear_pair ℝ _ _ )

/-
Law of Sines: in a nondegenerate triangle, the ratio of the length of a side to the sine of the opposite angle is constant.
-/
lemma dist_div_sin_eq_dist_div_sin (A B C : P)
  (h_nd : NondegenerateTriangle A B C) :
  dist A B / Real.sin (angle B C A) = dist B C / Real.sin (angle C A B) ∧
  dist B C / Real.sin (angle C A B) = dist C A / Real.sin (angle A B C) := by
  have h_law_of_sines : (dist A B / Real.sin (angle B C A)) = (dist C A / Real.sin (angle A B C)) ∧ (dist B C / Real.sin (angle C A B)) = (dist C A / Real.sin (angle A B C)) := by
    constructor <;> rw [ dist_div_sin_eq_prod_dist_div_abs_area, dist_div_sin_eq_prod_dist_div_abs_area ];
    all_goals simp_all +decide [ NondegenerateTriangle, dist_comm ];
    · rw [ show ( B -ᵥ C : V ) = ( A -ᵥ C ) - ( A -ᵥ B ) by rw [ vsub_sub_vsub_cancel_left ], map_sub ] ; norm_num ; ring;
      rw [ show C -ᵥ B = - ( B -ᵥ C ) by rw [ neg_vsub_eq_vsub_rev ], map_neg ] ; norm_num;
      rw [ show B -ᵥ C = ( A -ᵥ C ) - ( A -ᵥ B ) by rw [ vsub_sub_vsub_cancel_left ], map_sub ] ; norm_num;
    · rw [ collinear_iff_exists_forall_eq_smul_vadd ] at * ; aesop;
    · rw [ show ( A -ᵥ B ) = - ( B -ᵥ A ) by rw [ neg_vsub_eq_vsub_rev ], show ( C -ᵥ B ) = ( C -ᵥ A ) + ( A -ᵥ B ) by rw [ vsub_add_vsub_cancel ], map_add ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
      rw [ show ( A -ᵥ B ) = - ( B -ᵥ A ) by rw [ neg_vsub_eq_vsub_rev ], map_neg ] ; simp +decide [ mul_comm ];
      exact congrArg _ ( by rw [ show ( Module.Oriented.positiveOrientation.areaForm ( C -ᵥ A ) ) ( B -ᵥ A ) = - ( Module.Oriented.positiveOrientation.areaForm ( B -ᵥ A ) ( C -ᵥ A ) ) by exact ( Module.Oriented.positiveOrientation.areaForm_swap _ _ ) ] ; rw [ abs_neg ] );
    · rw [ collinear_iff_exists_forall_eq_smul_vadd ] at * ; aesop;
    · simp_all +decide [ collinear_iff_exists_forall_eq_smul_vadd ];
      exact fun x v a ha b hb c hc => h_nd x v c hc a ha b hb;
  aesop

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
  have := dist_div_sin_eq_dist_div_sin A B C h_nd;
  have := dist_div_sin_eq_dist_div_sin A' B' C' h_nd'; simp_all +decide only [dist_comm];
  by_cases ha : Real.sin ( angle A' B' C' ) = 0 <;> by_cases hb : Real.sin ( angle B' C' A' ) = 0 <;> simp_all +decide [ division_def, mul_assoc, mul_comm, mul_left_comm ];
  · rw [ Real.sin_eq_zero_iff_of_lt_of_lt ] at ha hb <;> linarith [ angle_pos_of_not_collinear ( show ¬Collinear ℝ { A', B', C' } by tauto ), angle_lt_pi_of_not_collinear ( show ¬Collinear ℝ { A', B', C' } by tauto ) ];
  · aesop;
  · cases this.1 <;> simp_all +decide [ angle ];
  · by_cases hc : Real.sin ( angle C' A' B' ) = 0;
    · have := triangle_angle_ne_zero_or_pi A' B' C' h_nd'; aesop;
    · grind

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
  have := h_nd;
  unfold NondegenerateTriangle at this;
  have h_sum : ∠ C A B + ∠ A B C + ∠ B C A = Real.pi := by
    rw [ angle_add_angle_add_angle_eq_pi ];
    rintro rfl; simp_all +decide [ collinear_pair ];
  have h_pos : 0 < ∠ C A B ∧ ∠ C A B < Real.pi ∧ 0 < ∠ A B C ∧ ∠ A B C < Real.pi ∧ 0 < ∠ B C A ∧ ∠ B C A < Real.pi := by
    have h_pos : ∀ (A B C : P), ¬Collinear ℝ {A, B, C} → 0 < ∠ C A B ∧ ∠ C A B < Real.pi := by
      intros A B C h_not_collinear
      have h_pos : 0 < InnerProductGeometry.angle (B -ᵥ A) (C -ᵥ A) ∧ InnerProductGeometry.angle (B -ᵥ A) (C -ᵥ A) < Real.pi := by
        refine' ⟨ _, _ ⟩;
        · refine' lt_of_le_of_ne ( InnerProductGeometry.angle_nonneg _ _ ) ( Ne.symm _ );
          intro h;
          rw [ InnerProductGeometry.angle_eq_zero_iff ] at h;
          refine' h_not_collinear _;
          rw [ collinear_iff_exists_forall_eq_smul_vadd ];
          use A, B -ᵥ A;
          simp +zetaDelta at *;
          exact ⟨ ⟨ 0, by simp +decide ⟩, ⟨ 1, by simp +decide ⟩, ⟨ h.2.choose, by rw [ ← h.2.choose_spec.2, vsub_vadd ] ⟩ ⟩;
        · refine' lt_of_le_of_ne ( InnerProductGeometry.angle_le_pi _ _ ) _;
          rw [ Ne.eq_def, InnerProductGeometry.angle_eq_pi_iff ];
          contrapose! h_not_collinear;
          rw [ collinear_iff_exists_forall_eq_smul_vadd ];
          use A, B -ᵥ A;
          simp +zetaDelta at *;
          exact ⟨ ⟨ 0, by simp +decide ⟩, ⟨ 1, by simp +decide ⟩, by obtain ⟨ r, hr, hr' ⟩ := h_not_collinear.2; exact ⟨ r, by rw [ ← hr', vsub_vadd ] ⟩ ⟩;
      rw [ angle_comm ];
      bound;
    have h_pos' : ¬Collinear ℝ {B, C, A} := by
      rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
      exact fun ⟨ p₀, v, hv ⟩ => this ⟨ p₀, v, by simpa [ or_comm, or_left_comm, or_assoc ] using hv ⟩;
    have h_pos'' : ¬Collinear ℝ {C, A, B} := by
      rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
      exact fun ⟨ p₀, v, hv ⟩ => h_pos' ⟨ p₀, v, fun p hp => by rcases hp with ( rfl | rfl | rfl ) <;> [ exact hv _ ( by simp +decide ) ; exact hv _ ( by simp +decide ) ; exact hv _ ( by simp +decide ) ] ⟩;
    exact ⟨ h_pos A B C this |>.1, h_pos A B C this |>.2, h_pos B C A h_pos' |>.1, h_pos B C A h_pos' |>.2, h_pos C A B h_pos'' |>.1, h_pos C A B h_pos'' |>.2 ⟩;
  exact ⟨ by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith ⟩

lemma finiteDimensional_of_fact_finrank_eq_two {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)] : FiniteDimensional ℝ V := by
  -- Since the dimension is 2, which is a natural number, the space is finite-dimensional.
  have h_fin_dim : FiniteDimensional ℝ V := by
    have h_dim : Module.finrank ℝ V = 2 := by
      -- Since the finrank is 2, we can conclude that the space is finite-dimensional.
      apply Fact.out
    exact FiniteDimensional.of_finrank_pos (by linarith);
  -- Since the finrank of V is 2, which is a natural number, we can conclude that V is finite-dimensional by using the fact that a space with a finite dimension is finite-dimensional.
  convert h_fin_dim using 1

lemma extend_isometry_to_equiv (S : Submodule ℝ V) (f : S →ₗᵢ[ℝ] V) :
  ∃ L : V ≃ₗᵢ[ℝ] V, ∀ x : S, L x = f x := by
  have h_finite : FiniteDimensional ℝ V := by
    exact finiteDimensional_of_fact_finrank_eq_two;
  obtain ⟨L, hL⟩ : ∃ L : V →ₗᵢ[ℝ] V, ∀ x : S, L x = f x := by
    exact ⟨ f.extend, fun x => LinearIsometry.extend_apply f x ⟩;
  have h_surjective : Function.Surjective L := by
    exact LinearMap.surjective_of_injective L.injective;
  exact ⟨ LinearIsometryEquiv.ofSurjective L h_surjective, hL ⟩

/-
If two pairs of vectors have the same norms and the same distance between them, there exists a global linear isometry mapping the first pair to the second.
-/
lemma exists_linearIsometry_of_congruent_vectors (u v u' v' : V)
  (hu : ‖u‖ = ‖u'‖)
  (hv : ‖v‖ = ‖v'‖)
  (hdist : dist u v = dist u' v') :
  ∃ L : V ≃ₗᵢ[ℝ] V, L u = u' ∧ L v = v' := by
  by_contra h_contra;
  -- By definition of isometry, the inner products of $u$ and $v$ with themselves and each other are equal to those of $u'$ and $v'$.
  have h_inner : inner ℝ u u = inner ℝ u' u' ∧ inner ℝ v v = inner ℝ v' v' ∧ inner ℝ u v = inner ℝ u' v' := by
    exact inner_products_eq_of_norms_and_dist_eq u v u' v' hu hv hdist;
  have := exists_linear_isometry_of_gram_eq ![u, v] ![u', v'] ; simp_all +decide [ dist_eq_norm', LinearIsometryEquiv ] ;
  obtain ⟨ f, hf₁, hf₂ ⟩ := this ( by rw [ real_inner_comm, h_inner.2.2, real_inner_comm ] );
  obtain ⟨ g, hg ⟩ := extend_isometry_to_equiv ( Submodule.span ℝ ( Set.range ![u, v] ) ) f;
  exact h_contra g ( by simpa using hg ⟨ u, Submodule.subset_span ( Set.mem_range_self 0 ) ⟩ |> fun h => h.trans hf₁ ) ( by simpa using hg ⟨ v, Submodule.subset_span ( Set.mem_range_self 1 ) ⟩ |> fun h => h.trans hf₂ )

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
Geometric lemma relating oriented angles in a triangle: angle at A equals angle at R minus angle at Q plus pi. Requires distinct points.
-/
lemma conway_oangle_triangle_variant (A Q R : P) (alpha beta : Real.Angle)
  (h_QA : Q ≠ A) (h_RA : R ≠ A) (h_QR : Q ≠ R)
  (h1 : Orientation.oangle Module.Oriented.positiveOrientation (R -ᵥ Q) (A -ᵥ Q) = alpha)
  (h2 : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ R) (A -ᵥ R) = beta) :
  Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ A) (R -ᵥ A) = beta - alpha + π := by
    have h_chasles : Module.Oriented.positiveOrientation.oangle (Q -ᵥ A) (R -ᵥ A) = Module.Oriented.positiveOrientation.oangle (Q -ᵥ A) (R -ᵥ Q) + Module.Oriented.positiveOrientation.oangle (R -ᵥ Q) (R -ᵥ A) := by
      rw [ Orientation.oangle_add ];
      · exact vsub_ne_zero.mpr h_QA;
      · exact vsub_ne_zero.mpr ( Ne.symm h_QR );
      · exact vsub_ne_zero.mpr h_RA;
    have h_chasles_alternate : Module.Oriented.positiveOrientation.oangle (Q -ᵥ A) (R -ᵥ Q) = -alpha + Real.pi := by
      have h_chasles_alternate : Module.Oriented.positiveOrientation.oangle (Q -ᵥ A) (R -ᵥ Q) = Module.Oriented.positiveOrientation.oangle (A -ᵥ Q) (-(R -ᵥ Q)) := by
        rw [ ← Module.Oriented.positiveOrientation.oangle_neg_neg ] ; simp +decide [ neg_vsub_eq_vsub_rev ] ;
      rw [ h_chasles_alternate, ← h1, Orientation.oangle_neg_right ];
      · rw [ Orientation.oangle_rev ];
      · exact vsub_ne_zero.mpr (id (Ne.symm h_QA));
      · exact vsub_ne_zero.mpr h_QR.symm;
    have h_chasles_alternate : Module.Oriented.positiveOrientation.oangle (R -ᵥ Q) (R -ᵥ A) = beta := by
      rw [ ← h2, ← Orientation.oangle_neg_neg ] ; aesop;
    grind

lemma conway_oangle_Q_A_R (P_pt Q R : P) (a b c : ℝ)
  (h_equilateral : isEquilateral P_pt Q R)
  (h_side : dist P_pt Q = 1)
  (h_sum : a + b + c = π / 3)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (h_c_pos : 0 < c)
  (h_a_lt : a < π/3) (h_b_lt : b < π/3) (h_c_lt : c < π/3) :
  let A := conwayConstructedVertexA P_pt Q R a b c
  Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ A) (R -ᵥ A) = (-a : Real.Angle) := by
  have h_periodic : (Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ conwayConstructedVertexA P_pt Q R a b c) (R -ᵥ conwayConstructedVertexA P_pt Q R a b c) = (2 * Real.pi - a : ℝ)) := by
    have h_alpha : Orientation.oangle Module.Oriented.positiveOrientation (R -ᵥ Q) (conwayConstructedVertexA P_pt Q R a b c -ᵥ Q) = -(angleShift c : ℝ) := by
      apply conwaySmallTriangleVertex_oangle_P1_V;
      · exact dist_pos.mpr ( by rintro rfl; exact absurd ( h_equilateral.1 ) ( by norm_num [ h_side ] ) );
      · exact Real.sin_pos_of_pos_of_lt_pi h_a_pos ( by linarith );
      · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith );
      · exact ⟨ by unfold angleShift; linarith, by unfold angleShift; linarith ⟩
    have h_beta : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ R) (conwayConstructedVertexA P_pt Q R a b c -ᵥ R) = (b + Real.pi / 3 : ℝ) := by
      convert conwaySmallTriangleVertex_oangle_P2_V Q R ( c + Real.pi / 3 ) ( b + Real.pi / 3 ) a _ _ _ _ _ _ _ using 1 <;> norm_num;
      any_goals constructor <;> linarith;
      · rintro rfl; simp_all +decide [ isEquilateral ];
      · exact Real.sin_pos_of_pos_of_lt_pi h_a_pos ( by linarith );
      · exact Real.sin_pos_of_pos_of_lt_pi ( by linarith ) ( by linarith );
      · exact Real.sin_pos_of_pos_of_lt_pi ( by linarith ) ( by linarith );
      · linarith
    have h_QA : Q ≠ conwayConstructedVertexA P_pt Q R a b c := by
      have h_QA : dist Q (conwayConstructedVertexA P_pt Q R a b c) = dist Q R * Real.sin (angleShift b) / Real.sin a := by
        apply conwaySmallTriangleVertex_dist_P1;
        · have := h_equilateral.1.symm; aesop;
        · exact Real.sin_pos_of_pos_of_lt_pi h_a_pos ( by linarith );
        · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith );
      have h_dist_pos : 0 < dist Q R * Real.sin (angleShift b) / Real.sin a := by
        apply_rules [ div_pos, mul_pos ];
        · have := h_equilateral.symm;
          linarith;
        · exact Real.sin_pos_of_pos_of_lt_pi ( by unfold angleShift; linarith ) ( by unfold angleShift; linarith );
        · exact Real.sin_pos_of_pos_of_lt_pi h_a_pos ( by linarith );
      exact fun h => h_dist_pos.ne' ( h_QA ▸ h ▸ dist_self _ )
    have h_RA : R ≠ conwayConstructedVertexA P_pt Q R a b c := by
      intro h;
      norm_num [ ← h ] at *;
      erw [ QuotientAddGroup.eq_zero_iff ] at h_alpha ; norm_num at h_alpha;
      obtain ⟨ k, hk ⟩ := h_alpha;
      rcases k with ⟨ _ | _ | k ⟩ <;> norm_num [ angleShift ] at hk <;> nlinarith [ Real.pi_pos ]
    have h_QR : Q ≠ R := by
      rintro rfl;
      simp_all +decide [ isEquilateral ];
    have h_angle_sum : Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ conwayConstructedVertexA P_pt Q R a b c) (R -ᵥ conwayConstructedVertexA P_pt Q R a b c) = (b + Real.pi / 3 : ℝ) - (-(angleShift c : ℝ)) + Real.pi := by
      rw [ ← h_alpha, ← h_beta ];
      apply_rules [ conway_oangle_triangle_variant ];
    field_simp;
    exact h_angle_sum.trans ( by rw [ show 2 * Real.pi - a = ( b + Real.pi / 3 ) - ( - ( c + Real.pi / 3 ) ) + Real.pi by linarith ] ; rfl );
  aesop

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
  have := @conway_oangle_B_A_C_final;
  convert this Q R P_pt b c a _ _ _ _ _ _ _ _ _ using 1;
  all_goals try linarith;
  · apply Iff.intro;
    · bound;
    · intro h;
      convert h _ using 1;
      convert h_orientation using 1;
      rw [ ← equilateral_oangle_cyclic ];
      exact h_equilateral;
  · unfold isEquilateral at *; aesop;
  · unfold isEquilateral at h_equilateral; aesop;

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
  -- Using the theorem `EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi`, we can write
  have h_sum : let A := conwayConstructedVertexA P_pt Q R a b c; let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c;
    Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ B) (C -ᵥ B) + Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ C) (A -ᵥ C) + Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ A) (B -ᵥ A) = Real.pi := by
      have h_distinct : conwayConstructedVertexA P_pt Q R a b c ≠ conwayConstructedVertexB P_pt Q R a b c ∧ conwayConstructedVertexB P_pt Q R a b c ≠ conwayConstructedVertexC P_pt Q R a b c ∧ conwayConstructedVertexC P_pt Q R a b c ≠ conwayConstructedVertexA P_pt Q R a b c := by
        refine' ⟨ _, _, _ ⟩ <;> intro h;
        · have := conway_oangle_B_A_C P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation;
          simp_all +decide [ sub_eq_iff_eq_add ];
          rw [ eq_comm ] at this;
          rw [ Real.Angle.coe_eq_zero_iff ] at this;
          obtain ⟨ n, hn ⟩ := this; rcases n with ⟨ _ | _ | n ⟩ <;> norm_num at hn <;> nlinarith [ Real.pi_pos ] ;
        · have := conway_gap_angle_P_correct P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation;
          simp_all +decide [ conwayLargeAngleP ];
          unfold angleShiftTwo at this;
          simp_all +decide [ EuclideanGeometry.angle ];
          rw [ InnerProductGeometry.angle_self ] at this ; linarith [ Real.pi_pos ];
          intro h'; simp_all +decide [ InnerProductGeometry.angle ] ; linarith [ Real.pi_pos ] ;
        · have := conway_oangle_Q_C_A P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt;
          simp_all +decide [ Real.Angle ];
          erw [ QuotientAddGroup.eq_zero_iff ] at this;
          obtain ⟨ k, hk ⟩ := this;
          rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos ];
      convert EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi _ _ _ using 1;
      · tauto;
      · tauto;
      · exact h_distinct.2.2.symm;
  -- Note that $\measuredangle C A B = - \measuredangle B A C$. From `conway_oangle_B_A_C`, $\measuredangle B A C = 3a$, so $\measuredangle C A B = -3a$.
  have h_CAB : let A := conwayConstructedVertexA P_pt Q R a b c; let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c;
    Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ A) (B -ᵥ A) = -Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A) := by
      field_simp;
      exact
        Orientation.oangle_rev positiveOrientation
          (conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c)
          (conwayConstructedVertexC P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c);
  have h_ABC : let A := conwayConstructedVertexA P_pt Q R a b c; let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c;
    Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ B) (C -ᵥ B) = -Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B) := by
      simp +decide [ Real.Angle, EuclideanGeometry.oangle ];
      rw [ Orientation.oangle_rev ];
  have h_BC_A : let A := conwayConstructedVertexA P_pt Q R a b c; let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c;
    Orientation.oangle Module.Oriented.positiveOrientation (C -ᵥ B) (A -ᵥ B) = (↑(3 * b) : Real.Angle) := by
      apply conway_oangle_C_B_A P_pt Q R a b c h_equilateral h_side ‹_› h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation;
  -- Substitute the known values into the sum equation.
  have h_sub : let A := conwayConstructedVertexA P_pt Q R a b c; let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c;
    - (↑(3 * b) : Real.Angle) + Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ C) (A -ᵥ C) - (↑(3 * a) : Real.Angle) = Real.pi := by
      have h_BAC : let A := conwayConstructedVertexA P_pt Q R a b c; let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c;
        Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ A) (C -ᵥ A) = (↑(3 * a) : Real.Angle) := by
          apply conway_oangle_B_A_C_final P_pt Q R a b c h_equilateral h_side ‹_› h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation;
      aesop;
  -- Solve for $\measuredangle B C A$: $\measuredangle B C A = 3a + 3b + \pi$.
  have h_BC_A_sol : let A := conwayConstructedVertexA P_pt Q R a b c; let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c;
    Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ C) (A -ᵥ C) = (↑(3 * a + 3 * b + Real.pi) : Real.Angle) := by
      norm_num [ Real.Angle.coe_add, Real.Angle.coe_sub ] at *;
      exact eq_of_sub_eq_zero ( by rw [ ← h_sub ] ; abel1 );
  -- Note that $\measuredangle A C B = - \measuredangle B C A$. From `h_BC_A_sol`, $\measuredangle B C A = 3a + 3b + \pi$, so $\measuredangle A C B = -(3a + 3b + \pi)$.
  have h_AC_B : let A := conwayConstructedVertexA P_pt Q R a b c; let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c;
    Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ C) (B -ᵥ C) = -(↑(3 * a + 3 * b + Real.pi) : Real.Angle) := by
      have h_AC_B : let A := conwayConstructedVertexA P_pt Q R a b c; let B := conwayConstructedVertexB P_pt Q R a b c; let C := conwayConstructedVertexC P_pt Q R a b c;
        Orientation.oangle Module.Oriented.positiveOrientation (A -ᵥ C) (B -ᵥ C) = -Orientation.oangle Module.Oriented.positiveOrientation (B -ᵥ C) (A -ᵥ C) := by
          simp +decide [ oangle ];
          exact
            Orientation.oangle_rev positiveOrientation
              (conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexC P_pt Q R a b c)
              (conwayConstructedVertexA P_pt Q R a b c -ᵥ conwayConstructedVertexC P_pt Q R a b c);
      aesop;
  convert h_AC_B using 1;
  rw [ show 3 * c = - ( 3 * a + 3 * b + Real.pi ) + 2 * Real.pi by linarith ] ; norm_num [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ]

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
  apply conway_P_on_trisector_B;
  any_goals tauto;
  · unfold isEquilateral at *; aesop;
  · have := h_equilateral.symm; aesop;
  · linarith;
  · convert h_orientation using 1;
    rw [ ← equilateral_oangle_cyclic ];
    exact h_equilateral

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
  unfold conwayConstructedVertexA conwayConstructedVertexB conwayConstructedVertexC;
  simp +decide [ AffineSubspace.mem_mk', Submodule.mem_span_singleton ];
  -- From `conway_oangle_B_A_C`, we know that the oriented angle BAC is 3a.
  have h_oangle_BAC : (Orientation.oangle Module.Oriented.positiveOrientation (conwayVertexB R P_pt a b c -ᵥ conwayVertexA Q R a b c) (conwayVertexC P_pt Q a b c -ᵥ conwayVertexA Q R a b c)).toReal = 3 * a := by
    convert congr_arg Real.Angle.toReal ( conway_oangle_B_A_C P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation ) using 1;
    exact Eq.symm ( Real.Angle.toReal_coe_eq_self_iff.mpr ⟨ by linarith, by linarith ⟩ );
  -- From `conway_oangle_R_A_B`, we know that the oriented angle from RA to BA is -a.
  have h_oangle_RA_BA : (Orientation.oangle Module.Oriented.positiveOrientation (R -ᵥ conwayVertexA Q R a b c) (conwayVertexB R P_pt a b c -ᵥ conwayVertexA Q R a b c)).toReal = -a := by
    have h_oangle_RA_BA : (Orientation.oangle Module.Oriented.positiveOrientation (R -ᵥ conwayVertexA Q R a b c) (conwayVertexB R P_pt a b c -ᵥ conwayVertexA Q R a b c)) = (-a : Real.Angle) := by
      have := conway_oangle_R_A_B P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation
      exact this;
    field_simp;
    convert congr_arg Real.Angle.toReal h_oangle_RA_BA using 1;
    erw [ Real.Angle.toReal_coe ];
    rw [ eq_comm, toIocMod_eq_iff ] ; norm_num;
    constructor <;> linarith;
  unfold trisectorVector;
  -- Since the oriented angles are equal, the vectors are collinear.
  have h_collinear : ∃ k : ℝ, R -ᵥ conwayVertexA Q R a b c = k • (Module.Oriented.positiveOrientation.rotation (↑a : Real.Angle) (conwayVertexB R P_pt a b c -ᵥ conwayVertexA Q R a b c)) := by
    have h_parallel : ∃ k : ℝ, R -ᵥ conwayVertexA Q R a b c = k • (Orientation.rotation Module.Oriented.positiveOrientation (a : Real.Angle) (conwayVertexB R P_pt a b c -ᵥ conwayVertexA Q R a b c)) := by
      have h_oangle_eq : (Orientation.oangle Module.Oriented.positiveOrientation (R -ᵥ conwayVertexA Q R a b c) (Orientation.rotation Module.Oriented.positiveOrientation (a : Real.Angle) (conwayVertexB R P_pt a b c -ᵥ conwayVertexA Q R a b c))).toReal = 0 := by
        have h_parallel : (Orientation.oangle Module.Oriented.positiveOrientation (R -ᵥ conwayVertexA Q R a b c) (Orientation.rotation Module.Oriented.positiveOrientation (a : Real.Angle) (conwayVertexB R P_pt a b c -ᵥ conwayVertexA Q R a b c))) = (Orientation.oangle Module.Oriented.positiveOrientation (R -ᵥ conwayVertexA Q R a b c) (conwayVertexB R P_pt a b c -ᵥ conwayVertexA Q R a b c)) + (a : Real.Angle) := by
          have h_parallel : ∀ (u v : V), u ≠ 0 → v ≠ 0 → (Orientation.oangle Module.Oriented.positiveOrientation u (Orientation.rotation Module.Oriented.positiveOrientation (a : Real.Angle) v)) = (Orientation.oangle Module.Oriented.positiveOrientation u v) + (a : Real.Angle) := by
            intros u v hu hv;
            have h_parallel : ∀ (u v : V), u ≠ 0 → v ≠ 0 → (Orientation.oangle Module.Oriented.positiveOrientation u (Orientation.rotation Module.Oriented.positiveOrientation (a : Real.Angle) v)) = (Orientation.oangle Module.Oriented.positiveOrientation u v) + (a : Real.Angle) := by
              intros u v hu hv
              have h_rotation : ∀ (θ : Real.Angle), (Orientation.oangle Module.Oriented.positiveOrientation u (Orientation.rotation Module.Oriented.positiveOrientation θ v)) = (Orientation.oangle Module.Oriented.positiveOrientation u v) + θ := by
                intro θ;
                induction θ using Real.Angle.induction_on ; aesop
              exact h_rotation (a : Real.Angle);
            exact h_parallel u v hu hv;
          apply h_parallel;
          · intro h_zero
            have h_contra : (Orientation.oangle Module.Oriented.positiveOrientation (R -ᵥ conwayVertexA Q R a b c) (conwayVertexB R P_pt a b c -ᵥ conwayVertexA Q R a b c)).toReal = 0 := by
              simp [h_zero]
            linarith [h_oangle_RA_BA];
          · intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
        rw [ h_parallel, ← Real.Angle.coe_toReal ( Module.Oriented.positiveOrientation.oangle ( R -ᵥ conwayVertexA Q R a b c ) ( conwayVertexB R P_pt a b c -ᵥ conwayVertexA Q R a b c ) ) ] ; aesop
      have h_parallel : ∃ k : ℝ, R -ᵥ conwayVertexA Q R a b c = k • (Orientation.rotation Module.Oriented.positiveOrientation (a : Real.Angle) (conwayVertexB R P_pt a b c -ᵥ conwayVertexA Q R a b c)) := by
        have h_oangle_eq : (Orientation.oangle Module.Oriented.positiveOrientation (R -ᵥ conwayVertexA Q R a b c) (Orientation.rotation Module.Oriented.positiveOrientation (a : Real.Angle) (conwayVertexB R P_pt a b c -ᵥ conwayVertexA Q R a b c))) = 0 := by
          rw [ ← Real.Angle.toReal_inj ] ; aesop
        rw [ Orientation.oangle_eq_zero_iff_sameRay ] at h_oangle_eq;
        rw [ SameRay ] at h_oangle_eq;
        rcases h_oangle_eq with h | h | ⟨ r₁, r₂, hr₁, hr₂, h ⟩;
        · exact ⟨ 0, by simpa using h ⟩;
        · have := LinearIsometryEquiv.norm_map ( Module.Oriented.positiveOrientation.rotation ( a : Real.Angle ) ) ( conwayVertexB R P_pt a b c -ᵥ conwayVertexA Q R a b c ) ; simp_all +decide;
        · exact ⟨ r₂ / r₁, by rw [ div_eq_inv_mul, MulAction.mul_smul, ← h, inv_smul_smul₀ hr₁.ne' ] ⟩;
      exact h_parallel;
    exact h_parallel;
  norm_num +zetaDelta at *;
  rw [ show ( ∡ ( conwayVertexB R P_pt a b c ) ( conwayVertexA Q R a b c ) ( conwayVertexC P_pt Q a b c ) ).toReal / 3 = a by linarith! ] ; aesop;

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
  convert conway_P_on_trisector_C R P_pt Q c a b ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ using 1;
  all_goals try linarith;
  · have h_orientation_symm : Module.Oriented.positiveOrientation.oangle (P_pt -ᵥ R) (Q -ᵥ R) = Module.Oriented.positiveOrientation.oangle (Q -ᵥ P_pt) (R -ᵥ P_pt) := by
      convert equilateral_oangle_cyclic R P_pt Q _ using 1;
      unfold isEquilateral at *; aesop;
    aesop;
  · unfold isEquilateral at *; aesop;
  · unfold isEquilateral at h_equilateral; aesop

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
  apply Eq.symm;
  apply lineIntersection_unique_of_linearIndependent;
  · exact
    conway_R_on_trisector_A P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt
      h_b_lt h_c_lt h_orientation h_gap_P h_gap_Q h_gap_R;
  · apply_rules [ conway_R_on_trisector_B ];
  · apply trisector_vectors_linear_independent;
    apply conway_constructed_triangle_nondegenerate P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation h_gap_P h_gap_Q h_gap_R

/-
If the oriented angle between u and v is theta, then v is in the span of the rotation of u by theta.
-/
lemma mem_span_of_oangle_eq_rotation {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)] (u v : V) (theta : Real.Angle) (hu : u ≠ 0) (hv : v ≠ 0) (h_angle : Orientation.oangle Module.Oriented.positiveOrientation u v = theta) : v ∈ Submodule.span ℝ {Orientation.rotation Module.Oriented.positiveOrientation theta u} := by
  have h_rotate : Module.Oriented.positiveOrientation.rotation theta u = (‖u‖ / ‖v‖) • v := by
    have h_rotate : ‖Module.Oriented.positiveOrientation.rotation theta u‖ = ‖u‖ ∧ Module.Oriented.positiveOrientation.oangle u (Module.Oriented.positiveOrientation.rotation theta u) = theta := by
      aesop;
    have h_rotate : Module.Oriented.positiveOrientation.oangle (Module.Oriented.positiveOrientation.rotation theta u) v = 0 := by
      aesop;
    have h_rotate : ∃ c : ℝ, Module.Oriented.positiveOrientation.rotation theta u = c • v := by
      rw [ Orientation.oangle_eq_zero_iff_angle_eq_zero ] at h_rotate;
      · rw [ InnerProductGeometry.angle_eq_zero_iff ] at h_rotate;
        rcases h_rotate.2 with ⟨ r, hr, hr' ⟩ ; exact ⟨ r⁻¹, by simp +decide [ hr', hr.ne' ] ⟩ ;
      · aesop;
      · exact hv;
    obtain ⟨ c, hc ⟩ := h_rotate;
    have h_c : ‖c • v‖ = ‖u‖ := by
      aesop;
    rw [ norm_smul, Real.norm_eq_abs ] at h_c;
    rw [ ← h_c, mul_div_cancel_right₀ _ ( norm_ne_zero_iff.mpr hv ), abs_of_nonneg ];
    · exact hc;
    · contrapose! h_rotate;
      rw [ hc, Module.Oriented.positiveOrientation.oangle_smul_left_of_neg ] <;> simp +decide [ h_rotate, hv ];
      exact ne_of_apply_ne Real.Angle.toReal ( by simp +decide [ Real.pi_ne_zero ] );
  rw [ h_rotate, Submodule.mem_span_singleton ];
  refine' ⟨ ‖v‖ / ‖u‖, _ ⟩;
  simp +decide [ ← smul_assoc, div_mul_div_cancel₀, norm_ne_zero_iff, hu, hv ]

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
  -- By definition of `conwayConstructedVertexA`, we know that `Q` lies on the line defined by rotating `A`'s trisector vector by `-a`.
  have hQ_trisector : Q -ᵥ (conwayConstructedVertexA P_pt Q R a b c) ∈ Submodule.span ℝ {Orientation.rotation Module.Oriented.positiveOrientation (-a : Real.Angle) (conwayConstructedVertexC P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c)} := by
    have hQ_trisector : Orientation.oangle Module.Oriented.positiveOrientation (conwayConstructedVertexC P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c) (Q -ᵥ conwayConstructedVertexA P_pt Q R a b c) = -a := by
      convert conway_oangle_C_A_Q P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation using 1;
    apply mem_span_of_oangle_eq_rotation;
    · intro h;
      have := conway_constructed_triangle_nondegenerate P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation h_gap_P h_gap_Q h_gap_R; simp_all +decide [ NondegenerateTriangle ] ;
      exact this ( collinear_pair ℝ _ _ );
    · by_contra hQ_eq_A;
      norm_num [ hQ_eq_A ] at hQ_trisector;
      exact absurd hQ_trisector ( by rw [ Real.Angle.coe_eq_zero_iff ] ; exact fun h => by obtain ⟨ k, hk ⟩ := h; rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos ] );
    · exact hQ_trisector;
  -- By definition of `trisectorVector`, we know that `trisectorVector A C B` is equal to `Orientation.rotation Module.Oriented.positiveOrientation (-a : Real.Angle) (conwayConstructedVertexC P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c)`.
  have h_trisector_vector : trisectorVector (conwayConstructedVertexA P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c) (conwayConstructedVertexB P_pt Q R a b c) = Orientation.rotation Module.Oriented.positiveOrientation (-a : Real.Angle) (conwayConstructedVertexC P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c) := by
    unfold trisectorVector; simp +decide [ *, angle ] ;
    have h_trisector_vector : (Module.Oriented.positiveOrientation.oangle (conwayConstructedVertexC P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c) (conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c)).toReal = -3 * a := by
      have := conway_oangle_B_A_C P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation;
      rw [ show ( Module.Oriented.positiveOrientation.oangle ( conwayConstructedVertexC P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c ) ( conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c ) ) = - ( Module.Oriented.positiveOrientation.oangle ( conwayConstructedVertexB P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c ) ( conwayConstructedVertexC P_pt Q R a b c -ᵥ conwayConstructedVertexA P_pt Q R a b c ) ) from ?_ ];
      · rw [ this ];
        erw [ Real.Angle.toReal_coe ];
        rw [ toIocMod_eq_iff ];
        exact ⟨ ⟨ by linarith, by linarith ⟩, 0, by norm_num ⟩;
      · rw [ Orientation.oangle_rev ];
    rw [ show ( ∡ ( conwayConstructedVertexC P_pt Q R a b c ) ( conwayConstructedVertexA P_pt Q R a b c ) ( conwayConstructedVertexB P_pt Q R a b c ) ).toReal / 3 = -a by linarith! ] ; norm_num;
  aesop

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
  norm_num +zetaDelta at *;
  refine' Eq.symm _;
  apply lineIntersection_unique_of_linearIndependent;
  · convert conway_Q_on_trisector_C P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation h_gap_P h_gap_Q h_gap_R using 1;
  · apply_rules [ conway_Q_on_trisector_A ];
  · apply trisector_vectors_linear_independent;
    unfold NondegenerateTriangle;
    intro h;
    have := conway_constructed_triangle_nondegenerate P_pt Q R a b c h_equilateral h_side h_sum h_a_pos h_b_pos h_c_pos h_a_lt h_b_lt h_c_lt h_orientation h_gap_P h_gap_Q h_gap_R;
    unfold NondegenerateTriangle at this;
    simp_all +decide [ collinear_iff_exists_forall_eq_smul_vadd ];
    grind

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
  -- Obtain the angles a, b, c from the nondegenerate triangle A B C.
  obtain ⟨a, b, c, h_angles⟩ : ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a < Real.pi / 3 ∧ b < Real.pi / 3 ∧ c < Real.pi / 3 ∧ a + b + c = Real.pi / 3 ∧ angle C A B = 3 * a ∧ angle A B C = 3 * b ∧ angle B C A = 3 * c := by
    use (angle C A B) / 3, (angle A B C) / 3, (angle B C A) / 3;
    have := angles_bounds_of_nondegenerate A B C h_nd;
    exact ⟨ this.1, this.2.2.1, this.2.2.2.2.1, this.2.1, this.2.2.2.1, this.2.2.2.2.2.1, this.2.2.2.2.2.2, by ring, by ring, by ring ⟩;
  -- Obtain the equilateral triangle PQR from a, b, c.
  obtain ⟨P_pt, Q, R, h_equilateral, h_side, h_orientation⟩ : ∃ P_pt Q R : P, isEquilateral P_pt Q R ∧ dist P_pt Q = 1 ∧ Orientation.oangle Module.Oriented.positiveOrientation (Q -ᵥ P_pt) (R -ᵥ P_pt) = (Real.pi / 3 : ℝ) := by
    exact exists_equilateral_triangle_with_orientation
  generalize_proofs at *;
  -- Apply the lemma that states the constructed triangle is nondegenerate and has the correct angles.
  have h_conway_triangle : let A := conwayConstructedVertexA P_pt Q R a b c
    let B := conwayConstructedVertexB P_pt Q R a b c
    let C := conwayConstructedVertexC P_pt Q R a b c
    NondegenerateTriangle A B C ∧
    angle C A B = 3 * a ∧
    angle A B C = 3 * b ∧
    angle B C A = 3 * c ∧
    morleyTriangle A B C = (P_pt, Q, R) := by
      apply conway_triangle_properties P_pt Q R a b c h_equilateral h_side h_angles.2.2.2.2.2.2.1 h_angles.1 h_angles.2.1 h_angles.2.2.1 h_angles.2.2.2.1 h_angles.2.2.2.2.1 h_angles.2.2.2.2.2.1 h_orientation
      skip
  generalize_proofs at *;
  -- Apply the lemma that states any equilateral triangle is similar to another equilateral triangle with a specific side length and orientation.
  obtain ⟨f, hf⟩ : ∃ f : Similarity P, f (conwayConstructedVertexA P_pt Q R a b c) = A ∧ f (conwayConstructedVertexB P_pt Q R a b c) = B ∧ f (conwayConstructedVertexC P_pt Q R a b c) = C := by
    apply exists_similarity_of_equal_angles
    generalize_proofs at *;
    · exact h_conway_triangle.1;
    · exact h_nd;
    · aesop;
    · aesop;
    · aesop
  generalize_proofs at *;
  have h_morley_triangle : morleyTriangle A B C = (f P_pt, f Q, f R) := by
    have := morley_triangle_similarity_invariance f (conwayConstructedVertexA P_pt Q R a b c) (conwayConstructedVertexB P_pt Q R a b c) (conwayConstructedVertexC P_pt Q R a b c) h_conway_triangle.1; aesop;
  exact h_morley_triangle.symm ▸ similarity_preserves_isEquilateral f P_pt Q R h_equilateral

#print axioms morley_theorem
-- 'morley_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
