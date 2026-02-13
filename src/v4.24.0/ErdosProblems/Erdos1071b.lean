/-
We have proved the existence of finite maximal disjoint collections of unit segments in both the open unit square and the closed unit square.

For the open unit square `Region_Square`, we showed that `S_finite` (consisting of 5 segments) is a maximal disjoint collection.
The proof involved showing that `S_finite` blocks `Region_Square`. We decomposed `Region_Square` into `Region12345` and `Region6_Total`, showed that `S_finite` blocks each (using provided lemmas), and that the intersection of these regions within `Region_Square` is covered by `S_finite`.

For the closed unit square `UnitSquare`, we showed that `S_total` (the union of `S_finite` and the 4 sides `S_sides`) is a maximal disjoint collection.
The proof relied on the fact that any unit segment in `UnitSquare` disjoint from `S_sides` must be contained in `Region_Square` (since it cannot contain corners), and thus is blocked by `S_finite`.
-/

import Mathlib

namespace Erdos1071b

set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.refine false
set_option linter.style.induction false
set_option linter.style.cases false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false

open scoped Classical

set_option maxHeartbeats 0

abbrev Point := EuclideanSpace ℝ (Fin 2)

def IsUnitSegment (s : Set Point) : Prop :=
  ∃ x y : Point, dist x y = 1 ∧ s = openSegment ℝ x y

def IsDisjointCollection (S : Set (Set Point)) : Prop :=
  (∀ s ∈ S, IsUnitSegment s) ∧ (∀ s t, s ∈ S → t ∈ S → s ≠ t → Disjoint s t)

def IsInRegion (S : Set (Set Point)) (R : Set Point) : Prop :=
  ∀ s ∈ S, s ⊆ R

def UnitSquare : Set Point := {p | ∀ i, 0 ≤ p i ∧ p i ≤ 1}

def IsBlocking (S : Set (Set Point)) (R : Set Point) : Prop :=
  ∀ L, IsUnitSegment L → L ⊆ R → ∃ s ∈ S, ¬Disjoint s L

open Set

def V_L : Set Point := openSegment ℝ ![0, 0] ![0, 1]

def V_R : Set Point := openSegment ℝ ![1, 0] ![1, 1]

def H_bot : Set Point := openSegment ℝ ![0, 0] ![1, 0]

def H_top : Set Point := openSegment ℝ ![0, 1] ![1, 1]

/-
Define the points O(0,0), O'(1,1/2), and A_0(1,0).
-/
def O_point : Point := ![0, 0]

def A_0 : Point := ![1, 0]

/-
Definitions for Corollary 2: The open unit square, the shifted collection, and the combined collection S_cor2.
-/
def Region_Square : Set Point := {p | 0 < p 0 ∧ p 0 < 1 ∧ 0 < p 1 ∧ p 1 < 1}

/-
Define the set of sides of the unit square and the collection S_cor3.
-/
def S_sides : Set (Set Point) := {V_L, V_R, H_bot, H_top}

/-
Define the boundary of the unit square.
-/
def SquareBoundary : Set Point := {p | p ∈ UnitSquare ∧ (p 0 = 0 ∨ p 0 = 1 ∨ p 1 = 0 ∨ p 1 = 1)}

/-
Define the point V_point (x0, y0) by x0 = (Sqrt[6]+Sqrt[2])/4 and y0 = (Sqrt[6]-Sqrt[2])/4.
-/
noncomputable def V_point : Point := ![(Real.sqrt 6 + Real.sqrt 2) / 4, (Real.sqrt 6 - Real.sqrt 2) / 4]

/-
Define the polynomial for x1.
-/
def poly_X (x : ℝ) : ℝ :=
  1 - 64 * x + 1184 * x^2 - 5312 * x^3 + 9536 * x^4 - 8192 * x^5 + 4480 * x^6 + 384 * x^7 -
  6880 * x^8 + 5632 * x^9 - 256 * x^10 - 1024 * x^11 + 4352 * x^12 - 8192 * x^13 +
  6144 * x^14 - 2048 * x^15 + 256 * x^16

/-
There exists a root x1 of poly_X in the interval (0.95, 0.96).
-/
theorem exists_root_x1 : ∃ x, 0.95 < x ∧ x < 0.96 ∧ poly_X x = 0 := by
  -- By the Intermediate Value Theorem, since $f(0.95) > 0$ and $f(0.96) < 0$, there exists some $c \in (0.95, 0.96)$ such that $f(c) = 0$.
  have h_ivt : ∃ c ∈ Set.Ioo (0.95 : ℝ) (0.96 : ℝ), poly_X c = 0 := by
    apply_rules [ intermediate_value_Ioo' ] <;> norm_num [ poly_X ];
    exact Continuous.continuousOn ( by unfold poly_X; continuity );
  aesop

/-
Define x1 as a root of poly_X in (0.95, 0.96).
-/
noncomputable def x1 : ℝ := Classical.choose exists_root_x1

theorem x1_prop : 0.95 < x1 ∧ x1 < 0.96 ∧ poly_X x1 = 0 := Classical.choose_spec exists_root_x1

/-
Define the point X_point (x1, 0).
-/
noncomputable def X_point : Point := ![x1, 0]

/-
Define y1 based on V_point and x1.
-/
noncomputable def y1 : ℝ := (V_point 1) * (1 - x1) / (V_point 0 - x1)

/-
Define the point Y_point (1, y1).
-/
noncomputable def Y_point : Point := ![1, y1]

/-
Define the x/y reflection called sigma as (x,y) maps to (y,x).
-/
def sigma (p : Point) : Point := ![p 1, p 0]

/-
Define the five segments.
-/
def segment1 : Set Point := openSegment ℝ O_point V_point

def segment2 : Set Point := openSegment ℝ O_point (sigma V_point)

def segment3 : Set Point := openSegment ℝ V_point (sigma V_point)

def segment4 : Set Point := openSegment ℝ X_point Y_point

def segment5 : Set Point := openSegment ℝ (sigma X_point) (sigma Y_point)

/-
Define the finite collection S_finite consisting of the five segments.
-/
def S_finite : Set (Set Point) := {segment1, segment2, segment3, segment4, segment5}

/-
V_point lies on segment4.
-/
theorem V_on_segment4 : V_point ∈ segment4 := by
  -- By definition of $V_point$, we know that $V_point = ![x1, y1]$.
  have hV_point_eq : V_point ∈ openSegment ℝ X_point Y_point := by
    have h1 : (V_point 0 - X_point 0) / (Y_point 0 - X_point 0) = (V_point 1 - X_point 1) / (Y_point 1 - X_point 1) := by
      unfold Y_point X_point V_point;
      unfold y1; norm_num; ring_nf;
      unfold V_point; norm_num; ring_nf;
      grind
    have h2 : 0 < (V_point 0 - X_point 0) / (Y_point 0 - X_point 0) ∧ (V_point 0 - X_point 0) / (Y_point 0 - X_point 0) < 1 := by
      unfold V_point X_point Y_point at * ; norm_num at *;
      -- We'll use that $x1 \approx 0.955$ to estimate the bounds.
      have hx1_approx : 0.95 < x1 ∧ x1 < 0.96 := by
        exact ⟨ by have := x1_prop; norm_num at *; linarith, by have := x1_prop; norm_num at *; linarith ⟩;
      exact ⟨ div_pos ( by nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ] ) ( by linarith ), by rw [ div_lt_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ] ⟩
    -- By definition of $t$, we can write $V_point$ as $(1-t) \cdot X_point + t \cdot Y_point$.
    set t : ℝ := (V_point 0 - X_point 0) / (Y_point 0 - X_point 0)
    have ht : V_point = (1 - t) • X_point + t • Y_point := by
      ext i; fin_cases i <;> norm_num [ h1 ] ; ring_nf;
      · grind;
      · grind;
    exact ht.symm ▸ ⟨ 1 - t, t, by norm_num; linarith, by linarith, by norm_num ⟩;
  exact hV_point_eq

/-
sigma(V_point) lies on segment5.
-/
theorem sigma_V_on_segment5 : sigma V_point ∈ segment5 := by
  convert Set.mem_image_of_mem sigma ( V_on_segment4 ) using 1;
  ext; simp
  constructor;
  · rintro ⟨ a, ha, b, hb, hab, rfl ⟩;
    refine' ⟨ _, ⟨ a, ha, b, hb, hab, rfl ⟩, _ ⟩;
    ext i ; fin_cases i <;> norm_num [ sigma ];
  · rintro ⟨ x, ⟨ a, ha, b, hb, hab, rfl ⟩, rfl ⟩;
    exact ⟨ a, ha, b, hb, hab, by ext i; fin_cases i <;> norm_num [ sigma ] ⟩

/-
The distance between any two points in a triangle is at most the maximum length of its sides.
-/
theorem dist_le_max_vertices (A B C : Point) (x y : Point)
  (hx : x ∈ convexHull ℝ {A, B, C}) (hy : y ∈ convexHull ℝ {A, B, C}) :
  dist x y ≤ max (dist A B) (max (dist B C) (dist C A)) := by
    -- Let $x = \sum_{i=0}^2 \alpha_i A_i$ and $y = \sum_{i=0}^2 \beta_i A_i$ with $\alpha_i, \beta_i \geq 0$ and $\sum \alpha_i = \sum \beta_i = 1$.
    obtain ⟨α, hα⟩ : ∃ α : Fin 3 → ℝ, 0 ≤ α ∧ ∑ i, α i = 1 ∧ x = ∑ i, α i • ![A, B, C] i := by
      rw [ mem_convexHull_iff ] at hx;
      specialize hx ( { x | ∃ α : Fin 3 → ℝ, 0 ≤ α ∧ ∑ i, α i = 1 ∧ x = ∑ i, α i • ![A, B, C] i } ) ?_ ?_;
      · rintro x ( rfl | rfl | rfl ) <;> [ exact ⟨ fun i => if i = 0 then 1 else 0, fun i => by positivity, by simp +decide, by simp +decide ⟩ ; exact ⟨ fun i => if i = 1 then 1 else 0, fun i => by positivity, by simp +decide, by simp +decide ⟩ ; exact ⟨ fun i => if i = 2 then 1 else 0, fun i => by positivity, by simp +decide, by simp +decide ⟩ ];
      · rintro x ⟨ α, hα₀, hα₁, rfl ⟩ y ⟨ β, hβ₀, hβ₁, rfl ⟩ a b ha hb hab;
        refine' ⟨ fun i => a * α i + b * β i, _, _, _ ⟩ <;> simp_all +decide [ Fin.sum_univ_three ];
        · exact fun i => add_nonneg ( mul_nonneg ha ( hα₀ i ) ) ( mul_nonneg hb ( hβ₀ i ) );
        · linear_combination' hab * 1 + hα₁ * a + hβ₁ * b;
        · ext ; norm_num ; ring;
      · exact hx
    obtain ⟨β, hβ⟩ : ∃ β : Fin 3 → ℝ, 0 ≤ β ∧ ∑ i, β i = 1 ∧ y = ∑ i, β i • ![A, B, C] i := by
      simp_all +decide [ convexHull_insert ];
      rcases hy with ⟨ i, hi, hy ⟩ ; rcases hy with ⟨ a, b, ha, hb, hab, rfl ⟩ ; rcases hi with ⟨ c, d, hc, hd, hcd, rfl ⟩ ; use fun j => if j = 0 then a else if j = 1 then b * c else b * d; simp_all +decide [ Fin.sum_univ_three ] ;
      exact ⟨ fun _ => by positivity, by nlinarith, by ext; simp +decide [ MulAction.mul_smul ] ; ring ⟩;
    -- By the triangle inequality, we have $dist x y \leq \sum_{i=0}^2 (\alpha_i + \beta_i) dist A_i y$.
    have h_triangle : dist x y ≤ ∑ i, (α i) * (∑ j, (β j) * dist (![A, B, C] i) (![A, B, C] j)) := by
      have h_triangle : dist x y ≤ ∑ i, ∑ j, α i * β j * dist (![A, B, C] i) (![A, B, C] j) := by
        have h_triangle : dist x y ≤ ∑ i, ∑ j, dist (α i • β j • ![A, B, C] i) (α i • β j • ![A, B, C] j) := by
          have h_triangle : dist x y ≤ ∑ i, dist (α i • ![A, B, C] i) (α i • (∑ j, β j • ![A, B, C] j)) := by
            rw [ hα.2.2, hβ.2.2 ];
            simp +decide [ dist_eq_norm ];
            convert norm_sum_le _ _ using 2 ; simp +decide
            rw [ ← Finset.sum_smul, hα.2.1, one_smul ];
          refine le_trans h_triangle ?_;
          refine Finset.sum_le_sum fun i _ => ?_;
          have h_triangle : dist (α i • ![A, B, C] i) (α i • (∑ j, β j • ![A, B, C] j)) ≤ ∑ j, dist (α i • β j • ![A, B, C] i) (α i • β j • ![A, B, C] j) := by
            have h_triangle : α i • ![A, B, C] i - α i • (∑ j, β j • ![A, B, C] j) = ∑ j, (α i • β j • ![A, B, C] i - α i • β j • ![A, B, C] j) := by
              simp +decide [ ← Finset.smul_sum, ← Finset.sum_smul, hβ.2.1 ]
            rw [ dist_eq_norm ];
            rw [ h_triangle ];
            exact le_trans ( norm_sum_le _ _ ) ( Finset.sum_le_sum fun j _ => by rw [ dist_eq_norm ] );
          exact h_triangle;
        simp_all +decide [ dist_eq_norm ];
        refine le_trans h_triangle ?_;
        refine' Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => _;
        convert norm_smul_le ( α i * β j ) ( ![A, B, C] i - ![A, B, C] j ) using 1 ; norm_num [ mul_assoc, smul_smul ];
        · rw [ smul_sub ];
        · rw [ Real.norm_of_nonneg ( mul_nonneg ( hα.1 i ) ( hβ.1 j ) ) ];
      simpa only [ mul_assoc, Finset.mul_sum _ _ _ ] using h_triangle;
    -- Since $\sum_{i=0}^2 (\alpha_i + \beta_i) = 2$, we can bound the expression by the maximum distance between any two points in $\{A, B, C\}$.
    have h_bound : ∑ i, (α i) * (∑ j, (β j) * dist (![A, B, C] i) (![A, B, C] j)) ≤ ∑ i, (α i) * (∑ j, (β j) * max (dist A B) (max (dist B C) (dist C A))) := by
      gcongr with i hi j hj ; aesop;
      · exact hβ.1 j;
      · fin_cases i <;> fin_cases j <;> simp +decide [ dist_comm ];
    simp_all +decide [ ← Finset.sum_mul ];
    exact Or.imp ( fun h => le_trans h_triangle h ) ( Or.imp ( fun h => le_trans h_triangle h ) ( fun h => le_trans h_triangle h ) ) h_bound

/-
If a point x in a triangle is at distance 1 from a vertex V, and all sides connected to V are length <= 1, then x must be a vertex.
-/
theorem dist_eq_one_implies_vertex (A B C : Point) (V : Point) (hV : V ∈ ({A, B, C} : Set Point))
    (hAB : dist A B ≤ 1) (hBC : dist B C ≤ 1) (hCA : dist C A ≤ 1)
    (x : Point) (hx : x ∈ convexHull ℝ {A, B, C}) (hdist : dist x V = 1) :
    x ∈ ({A, B, C} : Set Point) := by
      -- By the distances, $convexHull {A, B, C} \subseteq B(V, 1)$.
      have h_convexHull_ball : convexHull ℝ {A, B, C} ⊆ Metric.closedBall V (1 : ℝ) := by
        refine' convexHull_min _ _;
        · simp_all +decide [ Set.insert_subset_iff, dist_comm ];
          rcases hV with ( rfl | rfl | rfl ) <;> simp_all +decide [ dist_comm ];
        · exact convex_closedBall _ _;
      -- By the distances, $convexHull {A, B, C}$ is a subset of $B(V, 1)$, and since $x$ is on the boundary of $B(V, 1)$, $x$ must be an extreme point of $convexHull {A, B, C}$.
      have h_extreme : x ∈ Set.extremePoints ℝ (convexHull ℝ {A, B, C}) := by
        refine' ⟨ hx, _ ⟩;
        intro y hy z hz hxy
        have hxy_ball : y ∈ Metric.closedBall V (1 : ℝ) ∧ z ∈ Metric.closedBall V (1 : ℝ) := by
          exact ⟨ h_convexHull_ball hy, h_convexHull_ball hz ⟩;
        have h_eq : ‖y - V‖ = 1 ∧ ‖z - V‖ = 1 := by
          obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hxy;
          have h_eq : ‖a • (y - V) + b • (z - V)‖ = 1 := by
            convert hdist using 1;
            rw [ dist_eq_norm ] ; rw [ ← eq_sub_iff_add_eq' ] at hab ; subst_vars ; ring_nf;
            exact congr_arg Norm.norm ( by ext ; simpa using by ring );
          have h_eq : ‖a • (y - V) + b • (z - V)‖ ≤ a * ‖y - V‖ + b * ‖z - V‖ := by
            exact norm_add_le_of_le ( by rw [ norm_smul, Real.norm_of_nonneg ha.le ] ) ( by rw [ norm_smul, Real.norm_of_nonneg hb.le ] );
          constructor <;> nlinarith [ show ‖y - V‖ ≤ 1 from by simpa using hxy_ball.1, show ‖z - V‖ ≤ 1 from by simpa using hxy_ball.2 ];
        obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hxy;
        have h_eq : ‖a • (y - V) + b • (z - V)‖ = 1 := by
          convert hdist using 1;
          rw [ dist_eq_norm ] ; rw [ show a • y + b • z = a • ( y - V ) + b • ( z - V ) + V by ext i; simpa using by rw [ ← eq_sub_iff_add_eq' ] at hab; rw [ hab ] ; ring ] ; simp +decide
        have h_eq : ‖a • (y - V) + b • (z - V)‖^2 = ‖a • (y - V)‖^2 + ‖b • (z - V)‖^2 + 2 * a * b * inner ℝ (y - V) (z - V) := by
          rw [ @norm_add_sq ℝ ];
          simp +decide [ inner_smul_left, inner_smul_right, mul_assoc, mul_comm, mul_left_comm ] ; ring;
        simp_all +decide [ norm_smul ];
        have h_eq : inner ℝ (y - V) (z - V) = 1 := by
          nlinarith [ mul_pos ha hb ];
        have h_eq : ‖(y - V) - (z - V)‖^2 = 0 := by
          rw [ @norm_sub_sq ℝ ] ; norm_num [ h_eq ];
          nlinarith;
        norm_num [ ← ‹1 = a ^ 2 + b ^ 2 + 2 * a * b * inner ℝ ( y - V ) ( z - V ) › ] at *;
        norm_num [ sub_eq_zero.mp h_eq ] at *;
        rw [ ← add_smul, hab, one_smul ];
      -- By the distances, $convexHull {A, B, C}$ is a subset of $B(V, 1)$, and since $x$ is on the boundary of $B(V, 1)$, $x$ must be an extreme point of $convexHull {A, B, C}$, which means $x$ must be one of $A$, $B$, or $C$.
      have h_extreme_points : Set.extremePoints ℝ (convexHull ℝ {A, B, C}) ⊆ {A, B, C} := by
        exact extremePoints_convexHull_subset;
      exact h_extreme_points h_extreme

/-
If two points in a triangle with sides <= 1 are at distance 1, they must be vertices.
-/
theorem unit_segment_endpoints_are_vertices (A B C : Point)
    (hAB : dist A B ≤ 1) (hBC : dist B C ≤ 1) (hCA : dist C A ≤ 1)
    (x y : Point) (hx : x ∈ convexHull ℝ {A, B, C}) (hy : y ∈ convexHull ℝ {A, B, C})
    (hdist : dist x y = 1) :
    x ∈ ({A, B, C} : Set Point) ∧ y ∈ ({A, B, C} : Set Point) := by
      -- Apply the lemma h_dist_le_max_vertices to get a vertex V such that dist(V, y) ≥ 1.
      obtain ⟨V, hV⟩ : ∃ V ∈ ({A, B, C} : Set Point), dist V y ≥ 1 := by
        have h_dist_le_max_vertices : dist x y ≤ max (dist A y) (max (dist B y) (dist C y)) := by
          have h_dist_le : dist x y ≤ max (dist A y) (max (dist B y) (dist C y)) := by
            have h_convex : ∀ x y : Point, x ∈ convexHull ℝ {A, B, C} → y ∈ convexHull ℝ {A, B, C} → dist x y ≤ max (dist A y) (max (dist B y) (dist C y)) := by
              intros x y hx hy
              have h_max : dist x y ≤ max (dist A y) (max (dist B y) (dist C y)) := by
                have h_convex : ∀ (x : Point), x ∈ convexHull ℝ {A, B, C} → ∀ (y : Point), dist x y ≤ max (dist A y) (max (dist B y) (dist C y)) := by
                  intros x hx y
                  have h_convex : ∀ (x : Point), x ∈ convexHull ℝ {A, B, C} → ∀ (y : Point), dist x y ≤ max (dist A y) (max (dist B y) (dist C y)) := by
                    intros x hx y
                    have h_convex : ∃ (a b c : ℝ), a + b + c = 1 ∧ 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ x = a • A + b • B + c • C := by
                      rw [ convexHull_insert ] at hx;
                      · simp +decide [ segment_eq_image ] at hx;
                        rcases hx with ⟨ i, hi, j, hj, rfl ⟩ ; exact ⟨ 1 - j, j * ( 1 - i ), j * i, by ring, by nlinarith, by nlinarith, by nlinarith, by ext ; simpa using by ring ⟩ ;
                      · norm_num
                    obtain ⟨ a, b, c, habc, ha, hb, hc, rfl ⟩ := h_convex;
                    -- Apply the triangle inequality to each term in the sum.
                    have h_triangle : dist (a • A + b • B + c • C) y ≤ a * dist A y + b * dist B y + c * dist C y := by
                      rw [ dist_eq_norm, dist_eq_norm, dist_eq_norm, dist_eq_norm ];
                      convert norm_add_le ( a • ( A - y ) ) ( b • ( B - y ) + c • ( C - y ) ) |> le_trans <| add_le_add_left ( norm_add_le _ _ ) _ using 1;
                      · exact congr_arg Norm.norm ( by ext ; simpa using by rw [ ← eq_sub_iff_add_eq' ] at habc ; rw [ habc ] ; ring );
                      · rw [ norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb, Real.norm_of_nonneg hc ] ; ring;
                    cases max_cases ( dist A y ) ( max ( dist B y ) ( dist C y ) ) <;> cases max_cases ( dist B y ) ( dist C y ) <;> nlinarith [ @dist_nonneg _ _ A y, @dist_nonneg _ _ B y, @dist_nonneg _ _ C y ];
                  exact h_convex x hx y
                exact h_convex x hx y
              exact h_max
            exact h_convex x y hx hy;
          exact h_dist_le;
        grind;
      -- Since $y$ is in the convex hull of $\{A, B, C\}$ and $dist(V, y) = 1$, by the lemma $dist_eq_one_implies_vertex$, $y$ must be a vertex.
      have hy_vertex : y ∈ ({A, B, C} : Set Point) := by
        have hy_vertex : dist y V ≤ 1 := by
          have hy_vertex : dist y V ≤ max (dist A B) (max (dist B C) (dist C A)) := by
            apply dist_le_max_vertices;
            · assumption;
            · exact subset_convexHull ℝ _ hV.1;
          exact hy_vertex.trans ( max_le hAB ( max_le hBC hCA ) );
        apply dist_eq_one_implies_vertex A B C V hV.left hAB hBC hCA y hy (by
        linarith [ dist_comm y V ]);
      -- Since $x$ is in the convex hull of $\{A, B, C\}$ and $dist(x, y) = 1$, by the lemma $dist_eq_one_implies_vertex$, $x$ must be a vertex.
      have hx_vertex : x ∈ ({A, B, C} : Set Point) := by
        apply dist_eq_one_implies_vertex A B C y hy_vertex hAB hBC hCA x hx hdist
      exact ⟨hx_vertex, hy_vertex⟩

/-
Triangle diameter lemma: if a triangle's sides are all at most unit length, then the only unit line segments in that closed triangle are possibly the sides.
-/
theorem triangle_diameter_lemma (A B C : Point) (hAB : dist A B ≤ 1) (hBC : dist B C ≤ 1) (hCA : dist C A ≤ 1)
    (S : Set Point) (hS : IsUnitSegment S) (hS_sub : S ⊆ convexHull ℝ {A, B, C}) :
    S = openSegment ℝ A B ∨ S = openSegment ℝ B C ∨ S = openSegment ℝ C A := by
      -- By the lemma "unit_segment_endpoints_are_vertices", if two points in a triangle with sides at most 1 are separated by a distance of 1, then both points must be vertices of the triangle.
      obtain ⟨x, y, hx, hy, h_dist⟩ : ∃ x y : Point, x ∈ convexHull ℝ {A, B, C} ∧ y ∈ convexHull ℝ {A, B, C} ∧ dist x y = 1 ∧ openSegment ℝ x y = S := by
        obtain ⟨ x, y, hxy, rfl ⟩ := hS;
        have h_closed : closure (openSegment ℝ x y) ⊆ convexHull ℝ {A, B, C} := by
          have h_closure : IsClosed (convexHull ℝ {A, B, C}) := by
            have h_closed : IsCompact (convexHull ℝ {A, B, C}) := by
              have h_finite : Set.Finite {A, B, C} := by
                norm_num
              exact h_finite.isCompact_convexHull;
            exact h_closed.isClosed;
          exact h_closure.closure_subset_iff.mpr hS_sub;
        have h_closed : x ∈ closure (openSegment ℝ x y) ∧ y ∈ closure (openSegment ℝ x y) := by
          have h_closed : ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 - t) • x + t • y ∈ closure (openSegment ℝ x y) := by
            intro t ht
            have h_seq : ∃ seq : ℕ → ℝ, (∀ n, seq n ∈ Set.Ioo (0 : ℝ) 1) ∧ Filter.Tendsto seq Filter.atTop (nhds t) := by
              by_cases ht0 : t = 0 ∨ t = 1;
              · cases ht0 <;> simp_all +decide;
                · exact ⟨ fun n => 1 / ( n + 2 ), fun n => ⟨ by positivity, by rw [ div_lt_iff₀ ] <;> linarith ⟩, tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ⟩;
                · exact ⟨ fun n => 1 - 1 / ( n + 2 ), fun n => ⟨ by nlinarith [ div_mul_cancel₀ 1 ( by linarith : ( n + 2 : ℝ ) ≠ 0 ) ], by nlinarith [ div_mul_cancel₀ 1 ( by linarith : ( n + 2 : ℝ ) ≠ 0 ) ] ⟩, by exact le_trans ( tendsto_const_nhds.sub ( tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) <| by norm_num ⟩;
              · exact ⟨ fun _ => t, fun _ => ⟨ lt_of_le_of_ne ht.1 ( Ne.symm <| by tauto ), lt_of_le_of_ne ht.2 ( by tauto ) ⟩, tendsto_const_nhds ⟩;
            obtain ⟨ seq, hseq₁, hseq₂ ⟩ := h_seq;
            have h_seq : Filter.Tendsto (fun n => (1 - seq n) • x + seq n • y) Filter.atTop (nhds ((1 - t) • x + t • y)) := by
              exact Filter.Tendsto.add ( Filter.Tendsto.smul ( tendsto_const_nhds.sub hseq₂ ) tendsto_const_nhds ) ( Filter.Tendsto.smul hseq₂ tendsto_const_nhds );
            exact mem_closure_of_tendsto h_seq ( Filter.Eventually.of_forall fun n => ⟨ 1 - seq n, seq n, by linarith [ hseq₁ n |>.1, hseq₁ n |>.2 ], by linarith [ hseq₁ n |>.1, hseq₁ n |>.2 ], by simp +decide ⟩ );
          exact ⟨ by simpa using h_closed 0 ( by norm_num ), by simpa using h_closed 1 ( by norm_num ) ⟩;
        aesop;
      -- By the lemma "unit_segment_endpoints_are_vertices", since x and y are in the convex hull and dist x y = 1, x and y must be vertices of the triangle.
      have h_vertices : x ∈ ({A, B, C} : Set Point) ∧ y ∈ ({A, B, C} : Set Point) := by
        apply unit_segment_endpoints_are_vertices A B C hAB hBC hCA x y hx hy h_dist.left;
      rcases h_vertices with ⟨ rfl | rfl | rfl, rfl | rfl | rfl ⟩ <;> norm_num [ ← h_dist.2 ] at *;
      · rw [ openSegment_symm ] ; tauto;
      · exact Or.inl <| by rw [ openSegment_symm ] ;
      · exact Or.inr <| Or.inl <| by rw [ openSegment_symm ] ;

/-
The distance from O to V is 1.
-/
theorem dist_O_V : dist O_point V_point = 1 := by
  norm_num [ EuclideanSpace.dist_eq, V_point ];
  norm_num [ dist_eq_norm, O_point ] ; ring_nf ; norm_num;
  ring_nf; norm_num;

/-
The distance between V and sigma(V) is 1.
-/
theorem dist_V_sigma_V : dist V_point (sigma V_point) = 1 := by
  unfold sigma V_point;
  norm_num [ EuclideanSpace.norm_eq, dist_eq_norm ] ; ring_nf ; norm_num

/-
The distance condition is equivalent to an algebraic equation involving x1 and V_point 0.
-/
lemma dist_X_Y_iff_Q : dist X_point Y_point = 1 ↔ (1 - x1)^2 * (1 - 2 * V_point 0 * x1 + x1^2) = (V_point 0 - x1)^2 := by
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
  -- Substitute the definitions of X_point and Y_point into the distance formula.
  simp [X_point, Y_point, V_point];
  unfold y1;
  field_simp;
  rw [ add_div', div_eq_iff ] <;> norm_num [ V_point ];
  · grind;
  · have := x1_prop;
    nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
  · have := x1_prop;
    nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ]

/-
The x-coordinate of V_point.
-/
lemma V_point_0_val : V_point 0 = (Real.sqrt 6 + Real.sqrt 2) / 4 := by
  rfl

/-
Define the parametric polynomial Q and the semi-product.
-/
noncomputable def poly_Q_param (c : ℝ) (x : ℝ) : ℝ :=
  (1 - c^2) - 2 * x + (1 + 4 * c) * x^2 - (2 + 2 * c) * x^3 + x^4

noncomputable def poly_Q_pos (x : ℝ) : ℝ := poly_Q_param (V_point 0) x

noncomputable def poly_Q_neg (x : ℝ) : ℝ := poly_Q_param (-(V_point 0)) x

noncomputable def poly_semi (x : ℝ) : ℝ := poly_Q_pos x * poly_Q_neg x

/-
Define the full product polynomial.
-/
noncomputable def poly_Q_pos_prime (x : ℝ) : ℝ := poly_Q_param (V_point 1) x

noncomputable def poly_Q_neg_prime (x : ℝ) : ℝ := poly_Q_param (-(V_point 1)) x

noncomputable def poly_semi_prime (x : ℝ) : ℝ := poly_Q_pos_prime x * poly_Q_neg_prime x

noncomputable def poly_full (x : ℝ) : ℝ := poly_semi x * poly_semi_prime x

/-
poly_X is 256 times poly_full.
-/
lemma poly_X_eq_256_mul_poly_full : ∀ x, poly_X x = 256 * poly_full x := by
  unfold poly_X poly_full poly_semi poly_semi_prime poly_Q_pos poly_Q_neg poly_Q_pos_prime poly_Q_neg_prime poly_Q_param;
  -- By definition of $V_point$, we know that $V_point 0 = (Real.sqrt 6 + Real.sqrt 2) / 4$ and $V_point 1 = (Real.sqrt 6 - Real.sqrt 2) / 4$.
  have hV_point : V_point 0 = (Real.sqrt 6 + Real.sqrt 2) / 4 ∧ V_point 1 = (Real.sqrt 6 - Real.sqrt 2) / 4 := by
    exact ⟨ rfl, rfl ⟩;
  grind

/-
The distance condition is equivalent to poly_Q_pos x1 = 0.
-/
lemma dist_eq_one_iff_poly_Q_pos_eq_zero : dist X_point Y_point = 1 ↔ poly_Q_pos x1 = 0 := by
  convert dist_X_Y_iff_Q using 1;
  unfold poly_Q_pos;
  unfold poly_Q_param; ring_nf;
  constructor <;> intro h <;> linear_combination h

/-
The other factors of poly_full are negative in the interval [0.95, 0.96].
-/
lemma other_factors_neg (x : ℝ) (hx : 0.95 ≤ x ∧ x ≤ 0.96) :
  poly_Q_neg x < 0 ∧ poly_Q_pos_prime x < 0 ∧ poly_Q_neg_prime x < 0 := by
    -- Calculate the approximations for V_point 0 and V_point 1.
    have h_approx : (V_point 0) > 0.9659 ∧ (V_point 0) < 0.9661 ∧ (V_point 1) > 0.2588 ∧ (V_point 1) < 0.2589 := by
      unfold V_point; norm_num [ ← List.ofFn_inj ] ; ring_nf;
      exact ⟨ by nlinarith only [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ], by nlinarith only [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ], by nlinarith only [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ], by nlinarith only [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ] ⟩;
    unfold poly_Q_neg poly_Q_pos_prime poly_Q_neg_prime;
    unfold poly_Q_param;
    exact ⟨ by nlinarith [ pow_nonneg ( sub_nonneg.2 hx.1 ) 3 ], by nlinarith [ pow_nonneg ( sub_nonneg.2 hx.1 ) 3 ], by nlinarith [ pow_nonneg ( sub_nonneg.2 hx.1 ) 3 ] ⟩

/-
The distance between X and Y is 1.
-/
theorem dist_X_Y : dist X_point Y_point = 1 := by
  convert dist_eq_one_iff_poly_Q_pos_eq_zero.mpr _;
  have h_poly_Q_pos_zero : poly_X x1 = 256 * poly_Q_pos x1 * poly_Q_neg x1 * poly_Q_pos_prime x1 * poly_Q_neg_prime x1 := by
    convert poly_X_eq_256_mul_poly_full x1 using 1 ; ring_nf;
    unfold poly_full poly_semi poly_semi_prime; ring;
  have h_poly_Q_pos_zero : poly_Q_pos x1 * poly_Q_neg x1 * poly_Q_pos_prime x1 * poly_Q_neg_prime x1 = 0 := by
    linarith [ x1_prop.2.2 ];
  have h_poly_Q_pos_zero : poly_Q_neg x1 < 0 ∧ poly_Q_pos_prime x1 < 0 ∧ poly_Q_neg_prime x1 < 0 := by
    exact other_factors_neg x1 ⟨ by exact le_of_lt ( x1_prop.1 ), by exact le_of_lt ( x1_prop.2.1 ) ⟩;
  aesop

/-
Define the regions that subdivide the square.
-/
def Region1 : Set Point := convexHull ℝ {O_point, V_point, sigma V_point}

def Region2 : Set Point := convexHull ℝ {O_point, V_point, X_point}

def Region3 : Set Point := convexHull ℝ {O_point, sigma V_point, sigma X_point}

def Region4 : Set Point := convexHull ℝ {X_point, A_0, Y_point}

def Region5 : Set Point := convexHull ℝ {sigma X_point, sigma A_0, sigma Y_point}

def Region6a : Set Point := convexHull ℝ {V_point, sigma V_point, Y_point}

def Region6b : Set Point := convexHull ℝ {sigma V_point, Y_point, sigma Y_point}

/-
If a point is in an open segment (endpoints distinct), its distance to an endpoint is strictly less than the segment length.
-/
lemma mem_openSegment_implies_dist_lt {A B P : Point} (hAB : A ≠ B) (h : P ∈ openSegment ℝ A B) : dist A P < dist A B := by
  rcases h with ⟨ u, v, hu, hv, huv, rfl ⟩;
  rw [ show v = 1 - u by linarith ];
  rw [ dist_eq_norm, dist_eq_norm ];
  rw [ show A - ( u • A + ( 1 - u ) • B ) = ( 1 - u ) • ( A - B ) by ext ; simpa using by ring ] ; rw [ norm_smul, Real.norm_of_nonneg ( by linarith ) ] ; exact mul_lt_of_lt_one_left ( norm_pos_iff.mpr <| sub_ne_zero.mpr hAB ) <| by linarith;

/-
sigma is an isometry.
-/
theorem sigma_isometry (p q : Point) : dist (sigma p) (sigma q) = dist p q := by
  simp +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
  exact congrArg Real.sqrt ( by ring! )

/-
The distance from O to sigma(V) is 1.
-/
theorem dist_O_sigma_V : dist O_point (sigma V_point) = 1 := by
  convert dist_O_V using 1;
  convert sigma_isometry O_point V_point using 1

/-
The distance from O to X is less than 1.
-/
theorem dist_O_X_lt_1 : dist O_point X_point < 1 := by
  unfold O_point X_point;
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
  rw [ Real.sqrt_sq ] <;> have := x1_prop <;> norm_num at this ⊢ <;> nlinarith

/-
The distance from V to X is less than 1.
-/
theorem dist_V_X_lt_1 : dist V_point X_point < 1 := by
  -- By the lemma `mem_openSegment_implies_dist_lt`, since $V$ is in the open segment $XY$, we have $dist(X, V) < dist(X, Y)$.
  have h_dist_X_V_lt_dist_X_Y : dist X_point V_point < dist X_point Y_point := by
    convert mem_openSegment_implies_dist_lt _ _;
    · unfold X_point Y_point; norm_num [ ← List.ofFn_inj ] ;
      exact ne_of_apply_ne ( fun p => p 0 ) ( by norm_num; linarith [ x1_prop ] );
    · convert V_on_segment4 using 1;
  rwa [ dist_comm, dist_X_Y ] at h_dist_X_V_lt_dist_X_Y

/-
The distance from X to A0 is less than 1.
-/
theorem dist_X_A0_lt_1 : dist X_point A_0 < 1 := by
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
  unfold X_point A_0 ; norm_num [ X_point, A_0 ];
  rw [ Real.sqrt_sq_eq_abs, abs_lt ] ; constructor <;> nlinarith [ x1_prop ]

/-
The distance from A0 to Y is less than 1.
-/
theorem dist_A0_Y_lt_1 : dist A_0 Y_point < 1 := by
  -- By definition of Y_point, we have Y_point = ![1, y1].
  have hY : dist A_0 Y_point = Real.sqrt (y1^2) := by
    norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two ];
    unfold A_0 Y_point; norm_num;
  -- From the equation above, y1^2 = 1 - (1 - x1)^2.
  have hy1_sq : y1^2 = 1 - (1 - x1)^2 := by
    -- By definition of Y_point, we have Y_point = ![1, y1]. We know dist(X, Y) = 1.
    have h_dist_X_Y : dist X_point Y_point = 1 := by
      exact dist_X_Y;
    norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
    unfold X_point Y_point at * ; norm_num at * ; linarith!;
  rw [ hY, Real.sqrt_lt' ] <;> nlinarith [ show 0 < 1 - x1 by nlinarith [ x1_prop ] ]

/-
The distance from V to Y is less than 1.
-/
theorem dist_V_Y_lt_1 : dist V_point Y_point < 1 := by
  -- Since $V_point$ is on the segment $XY$, we have $dist(V_point, Y_point) = dist(X_point, Y_point) - dist(X_point, V_point)$.
  have h_dist_V_X : dist V_point Y_point = dist X_point Y_point - dist X_point V_point := by
    rw [ dist_comm X_point V_point, eq_sub_iff_add_eq' ];
    -- Since $V$ is on the segment $XY$, we can apply the triangle inequality to get $dist X Y = dist X V + dist V Y$.
    have h_triangle : dist X_point Y_point = dist X_point V_point + dist V_point Y_point := by
      have h_collinear : Collinear ℝ {X_point, V_point, Y_point} := by
        rw [ collinear_iff_exists_forall_eq_smul_vadd ];
        use X_point, Y_point - X_point;
        norm_num [ X_point, Y_point, V_point ];
        constructor;
        · use ( ( Real.sqrt 6 + Real.sqrt 2 ) / 4 - x1 ) / ( 1 - x1 );
          ext i ; fin_cases i <;> norm_num [ y1 ];
          · rw [ div_mul_cancel₀ ] <;> linarith [ x1_prop ];
          · rw [ div_mul_div_comm, eq_div_iff ];
            · rw [ show V_point 0 = ( Real.sqrt 6 + Real.sqrt 2 ) / 4 by rfl, show V_point 1 = ( Real.sqrt 6 - Real.sqrt 2 ) / 4 by rfl ] ; ring;
            · norm_num [ V_point ];
              constructor <;> nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), x1_prop ];
        · exact ⟨ 1, by ext i; fin_cases i <;> norm_num ⟩
      rw [ dist_comm X_point V_point, dist_eq_norm, dist_eq_norm, dist_eq_norm ];
      -- Since $V$ is on the segment $XY$, we can apply the triangle inequality to get $‖X - Y‖ = ‖X - V‖ + ‖V - Y‖$.
      have h_triangle : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ V_point = (1 - t) • X_point + t • Y_point := by
        have h_collinear : V_point ∈ openSegment ℝ X_point Y_point := by
          convert V_on_segment4 using 1;
        rw [ openSegment_eq_image ] at h_collinear;
        exact ⟨ h_collinear.choose, h_collinear.choose_spec.1.1.le, h_collinear.choose_spec.1.2.le, h_collinear.choose_spec.2.symm ⟩;
      obtain ⟨ t, ht₀, ht₁, ht₂ ⟩ := h_triangle;
      rw [ ht₂ ];
      rw [ show ( 1 - t ) • X_point + t • Y_point - X_point = t • ( Y_point - X_point ) by ext ; simpa using by ring, show ( 1 - t ) • X_point + t • Y_point - Y_point = ( 1 - t ) • ( X_point - Y_point ) by ext ; simpa using by ring, norm_smul, norm_smul ] ; norm_num [ ht₀, ht₁ ];
      rw [ norm_sub_rev Y_point X_point, abs_of_nonneg ht₀, abs_of_nonneg ( sub_nonneg_of_le ht₁ ) ] ; ring;
    rw [ h_triangle, dist_comm ];
  linarith [ show 0 < dist X_point V_point from dist_pos.mpr <| by
              unfold X_point V_point; norm_num [ ← List.ofFn_inj ] ;
              exact ne_of_apply_ne ( fun p => p 1 ) ( by norm_num; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ] ), dist_X_Y ]

/-
The distance between sigma(X) and sigma(Y) is 1.
-/
theorem dist_sigma_X_sigma_Y : dist (sigma X_point) (sigma Y_point) = 1 := by
  rw [sigma_isometry, dist_X_Y]

/-
Numeric bounds for V_point.
-/
lemma V_bounds : 0.96 < V_point 0 ∧ V_point 0 < 0.97 ∧ 0.25 < V_point 1 ∧ V_point 1 < 0.26 := by
  unfold V_point; norm_num [ ← List.ofFn_inj ] ; ring_nf;
  exact ⟨ by nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ], by nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ], by nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ], by nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ] ⟩

/-
Every segment in S_finite is a unit segment.
-/
theorem S_finite_consists_of_unit_segments : ∀ s ∈ S_finite, IsUnitSegment s := by
  unfold S_finite;
  simp +zetaDelta at *;
  refine' ⟨ _, _, _, _, _ ⟩;
  · exact ⟨ O_point, V_point, dist_O_V, rfl ⟩;
  · exact ⟨ O_point, sigma V_point, by simpa using dist_O_sigma_V, rfl ⟩;
  · use V_point, sigma V_point;
    exact ⟨ dist_V_sigma_V, rfl ⟩;
  · exact ⟨ X_point, Y_point, dist_X_Y, rfl ⟩;
  · exact ⟨ _, _, dist_sigma_X_sigma_Y, rfl ⟩

/-
V_point is in the open unit square.
-/
lemma V_in_Region_Square : V_point ∈ Region_Square := by
  exact ⟨ by linarith [ V_bounds ], by linarith [ V_bounds ], by linarith [ V_bounds ], by linarith [ V_bounds ] ⟩

/-
sigma(V_point) is in the open unit square.
-/
lemma sigma_V_in_Region_Square : sigma V_point ∈ Region_Square := by
  exact ⟨ by have := V_bounds; norm_num [ sigma ] at *; linarith, by have := V_bounds; norm_num [ sigma ] at *; linarith, by have := V_bounds; norm_num [ sigma ] at *; linarith, by have := V_bounds; norm_num [ sigma ] at *; linarith ⟩

/-
The open segment from O to a point inside the square is inside the square.
-/
lemma segment_from_corner_in_square (v : Point) (hv : v ∈ Region_Square) : openSegment ℝ O_point v ⊆ Region_Square := by
  intro p hp;
  obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hp;
  exact ⟨ by simpa [ show O_point = 0 from by ext i; fin_cases i <;> rfl ] using by nlinarith [ hv.1, hv.2.1 ], by simpa [ show O_point = 0 from by ext i; fin_cases i <;> rfl ] using by nlinarith [ hv.1, hv.2.1 ], by simpa [ show O_point = 0 from by ext i; fin_cases i <;> rfl ] using by nlinarith [ hv.2.2.1, hv.2.2.2 ], by simpa [ show O_point = 0 from by ext i; fin_cases i <;> rfl ] using by nlinarith [ hv.2.2.1, hv.2.2.2 ] ⟩

/-
The open segment between two points in the square is in the square.
-/
lemma segment_inside_square (u v : Point) (hu : u ∈ Region_Square) (hv : v ∈ Region_Square) : openSegment ℝ u v ⊆ Region_Square := by
  -- Since $u$ and $v$ are in $Region_Square$, we have $0 < u 0 < 1$, $0 < u 1 < 1$, $0 < v 0 < 1$, and $0 < v 1 < 1$.
  have h_bounds : 0 < u 0 ∧ u 0 < 1 ∧ 0 < u 1 ∧ u 1 < 1 ∧ 0 < v 0 ∧ v 0 < 1 ∧ 0 < v 1 ∧ v 1 < 1 := by
    exact ⟨ hu.1, hu.2.1, hu.2.2.1, hu.2.2.2, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2 ⟩;
  rintro w ⟨ a, b, ha, hb, hab, rfl ⟩;
  exact ⟨ by simpa using by nlinarith, by simpa using by nlinarith, by simpa using by nlinarith, by simpa using by nlinarith ⟩

/-
y1 is strictly between 0 and 1.
-/
lemma y1_bounds : 0 < y1 ∧ y1 < 1 := by
  -- Since $V_point 1 = \frac{\sqrt{6} - \sqrt{2}}{4}$ and $x1$ is between $0.95$ and $0.96$, we can show that $y1$ is positive and less than 1.
  have hy1_pos : 0 < y1 := by
    apply_rules [ mul_pos, div_pos ] <;> norm_num [ V_point_0_val, V_point ];
    · exact lt_of_lt_of_le ( Classical.choose_spec exists_root_x1 |>.2.1 ) ( by norm_num );
    · have := x1_prop;
      nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ]
  have hy1_lt_1 : y1 < 1 := by
    -- By definition of $y1$, we have $y1^2 = 1 - (1 - x1)^2$.
    have hy1_sq : y1^2 = 1 - (1 - x1)^2 := by
      have := dist_X_Y;
      norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at this;
      unfold X_point Y_point at this; norm_num at this; linarith;
    nlinarith [ show x1 < 1 by exact lt_of_lt_of_le ( Classical.choose_spec exists_root_x1 |>.2.1 ) ( by norm_num ) ]
  exact ⟨hy1_pos, hy1_lt_1⟩

/-
segment4 is contained in the open unit square.
-/
lemma segment4_in_square : segment4 ⊆ Region_Square := by
  -- By definition of open segment, any point p in segment4 can be written as p = (1-t)X_point + tY_point for some t in (0,1).
  intro p hp
  obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, p = (1 - t) • X_point + t • Y_point := by
    rcases hp with ⟨ a, b, ha, hb, hab, rfl ⟩ ; exact ⟨ b, ⟨ by linarith, by linarith ⟩, by simp +decide [ ← eq_sub_iff_add_eq' ] at *; aesop ⟩ ;
  -- Substitute the coordinates of X_point and Y_point into the expression for p.
  have hp_coords : p 0 = (1 - t) * x1 + t ∧ p 1 = t * y1 := by
    simp [ht, X_point, Y_point];
  -- Since $0 < x1 < 1$ and $0 < y1 < 1$, we have $0 < (1 - t) * x1 + t < 1$ and $0 < t * y1 < 1$.
  have hx1_bounds : 0 < x1 ∧ x1 < 1 := by
    exact ⟨ lt_trans ( by norm_num ) ( x1_prop.1 ), lt_trans ( x1_prop.2.1 ) ( by norm_num ) ⟩
  have hy1_bounds : 0 < y1 ∧ y1 < 1 := by
    exact y1_bounds;
  exact ⟨ by nlinarith [ ht.1.1, ht.1.2 ], by nlinarith [ ht.1.1, ht.1.2 ], by nlinarith [ ht.1.1, ht.1.2 ], by nlinarith [ ht.1.1, ht.1.2 ] ⟩

/-
segment5 is contained in the open unit square.
-/
lemma segment5_in_square : segment5 ⊆ Region_Square := by
  -- Since segment4 is contained in Region_Square, and sigma is an isometry, segment5 is also contained in Region_Square.
  have h_segment5_in_square : segment4 ⊆ Region_Square := by
    exact segment4_in_square;
  have h_segment5_in_square : segment5 = (fun p => sigma p) '' segment4 := by
    ext; simp [openSegment];
    constructor;
    · rintro ⟨ a, ha, b, hb, hab, rfl ⟩;
      refine' ⟨ _, ⟨ a, ha, b, hb, hab, rfl ⟩, _ ⟩;
      ext i; fin_cases i <;> norm_num [ sigma ] ;
    · rintro ⟨ x, ⟨ a, ha, b, hb, hab, rfl ⟩, rfl ⟩;
      exact ⟨ a, ha, b, hb, hab, by ext i; fin_cases i <;> norm_num [ sigma ] ⟩;
  simp_all +decide [ Set.subset_def ];
  intro p hp; specialize ‹∀ x ∈ segment4, x ∈ Region_Square› p hp; unfold Region_Square at *; aesop;

/-
All segments in S_finite are contained in the open unit square.
-/
theorem S_finite_in_region : IsInRegion S_finite Region_Square := by
  exact fun s hs => by rcases hs with ( rfl | rfl | rfl | rfl | rfl ) <;> [ exact segment_from_corner_in_square _ ( by exact
    V_in_Region_Square ) ; exact segment_from_corner_in_square _ ( by exact
    sigma_V_in_Region_Square ) ; exact segment_inside_square _ _ ( by exact
    V_in_Region_Square ) ( by exact
    sigma_V_in_Region_Square ) ; exact segment4_in_square ; exact segment5_in_square ] ;

/-
segment1 and segment5 are disjoint.
-/
lemma disjoint_1_5 : Disjoint segment1 segment5 := by
  refine' Set.disjoint_left.mpr _;
  intro p hp hp'; obtain ⟨ u, v, hu, hv, huv, rfl ⟩ := hp; obtain ⟨ w, z, hw, hz, hwz, hp' ⟩ := hp';
  unfold sigma at hp';
  unfold X_point Y_point at * ; norm_num at *;
  -- By comparing the y-coordinates from hp' and huv, we can derive a contradiction.
  have h_y : w * x1 + z = u * 0 + v * V_point 1 := by
    convert congr_fun hp' 1 using 1 ; norm_num [ hwz ];
  -- By comparing the y-coordinates from hp' and huv, we can derive a contradiction. Since $y1 < 0.26$ and $x1 > 0.95$, we have $w * x1 + z > w * 0.95 + z$.
  have h_y_contra : w * x1 + z > w * 0.95 + z := by
    exact add_lt_add_right ( mul_lt_mul_of_pos_left ( by have := x1_prop; norm_num at *; linarith ) hw ) _;
  nlinarith [ V_bounds ]

/-
segment2 and segment4 are disjoint.
-/
lemma disjoint_2_4 : Disjoint segment2 segment4 := by
  refine' Set.disjoint_left.mpr _;
  intro x hx hx'; rw [ segment2 ] at hx; rw [ segment4 ] at hx'; obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hx; obtain ⟨ c, d, hc, hd, hcd, hcd' ⟩ := hx';
  -- By comparing the x-coordinates of the points in segment2 and segment4, we can see that they are disjoint.
  have h_x_coord : c * x1 + d * 1 ≠ a * 0 + b * (V_point 1) := by
    have h_x_coord : x1 > 0.95 ∧ V_point 1 < 0.26 := by
      exact ⟨ x1_prop.1, V_bounds.2.2.2 ⟩;
    cases le_or_gt c 0 <;> cases le_or_gt d 0 <;> nlinarith;
  exact h_x_coord ( by have := congr_fun hcd' 0; have := congr_fun hcd' 1; norm_num [ X_point, Y_point, O_point, sigma, V_point ] at *; linarith )

/-
segment4 and segment5 are disjoint.
-/
lemma disjoint_4_5 : Disjoint segment4 segment5 := by
  refine' Set.disjoint_left.mpr _;
  intro p hp hp'; obtain ⟨ u, v, hu, hv, huv, rfl ⟩ := hp; obtain ⟨ w, z, hw, hz, hwz, hp' ⟩ := hp'; simp_all +decide [ openSegment_eq_image ] ;
  unfold sigma at hp';
  have := congr_fun hp' 0 ; have := congr_fun hp' 1 ; norm_num [ X_point, Y_point ] at *;
  -- By definition of $x1$ and $y1$, we know that $0.95 < x1 < 0.96$ and $0 < y1 < 1$.
  have hx1_bounds : 0.95 < x1 ∧ x1 < 0.96 := by
    exact ⟨ by have := x1_prop; norm_num at *; linarith, by have := x1_prop; norm_num at *; linarith ⟩
  have hy1_bounds : 0 < y1 ∧ y1 < 1 := by
    exact y1_bounds;
  nlinarith

/-
segment1 and segment4 are disjoint.
-/
lemma disjoint_1_4 : Disjoint segment1 segment4 := by
  refine' Set.disjoint_left.mpr _;
  intro x hx1 hx4;
  -- Since $x$ is in both $segment1$ and $segment4$, it must lie on the line segment $OV$ and also on the line segment $XY$.
  obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, x = t • O_point + (1 - t) • V_point := by
    rw [ segment1 ] at hx1;
    rw [ openSegment_eq_image ] at hx1;
    rcases hx1 with ⟨ t, ht, rfl ⟩ ; exact ⟨ 1 - t, ⟨ by linarith [ ht.1, ht.2 ], by linarith [ ht.1, ht.2 ] ⟩, by ext i; fin_cases i <;> norm_num ⟩ ;
  obtain ⟨s, hs⟩ : ∃ s ∈ Set.Ioo (0 : ℝ) 1, x = s • X_point + (1 - s) • Y_point := by
    rw [ segment4 ] at hx4;
    rw [ openSegment_eq_image ] at hx4;
    rcases hx4 with ⟨ s, hs, rfl ⟩ ; exact ⟨ 1 - s, ⟨ by linarith [ hs.1, hs.2 ], by linarith [ hs.1, hs.2 ] ⟩, by simp +decide [ add_comm ] ⟩ ;
  -- By equating the two expressions for $x$, we get $t • O_point + (1 - t) • V_point = s • X_point + (1 - s) • Y_point$.
  have h_eq : t • O_point + (1 - t) • V_point = s • X_point + (1 - s) • Y_point := by
    rw [ ← ht.2, ← hs.2 ];
  unfold O_point V_point X_point Y_point at h_eq;
  rw [ ← List.ofFn_inj ] at h_eq ; norm_num at h_eq;
  -- Substitute y1 from its definition into the second equation.
  have hy1 : y1 = (Real.sqrt 6 - Real.sqrt 2) / 4 * (1 - x1) / ((Real.sqrt 6 + Real.sqrt 2) / 4 - x1) := by
    exact rfl;
  rw [ eq_div_iff ] at hy1;
  · -- Substitute y1 from its definition into the second equation and simplify.
    have h_simplified : (1 - t) * ((Real.sqrt 6 - Real.sqrt 2) / 4) * ((Real.sqrt 6 + Real.sqrt 2) / 4 - x1) = (1 - s) * ((Real.sqrt 6 - Real.sqrt 2) / 4) * (1 - x1) := by
      linear_combination' h_eq.2 * ( ( Real.sqrt 6 + Real.sqrt 2 ) / 4 - x1 ) + hy1 * ( 1 - s );
    -- Cancel out the common terms $(Real.sqrt 6 - Real.sqrt 2) / 4$ from both sides.
    have h_cancelled : (1 - t) * ((Real.sqrt 6 + Real.sqrt 2) / 4 - x1) = (1 - s) * (1 - x1) := by
      exact mul_left_cancel₀ ( show ( Real.sqrt 6 - Real.sqrt 2 ) / 4 ≠ 0 by nlinarith only [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ] ) ( by linear_combination h_simplified );
    nlinarith [ ht.1.1, ht.1.2, hs.1.1, hs.1.2, x1_prop.1, x1_prop.2.1, Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ];
  · intro h; rw [ h ] at hy1; norm_num [ hy1 ] at *;
    exact absurd ( h_eq.2.resolve_left ( by linarith ) ) ( sub_ne_zero_of_ne ( by norm_num ) )

/-
segment2 and segment5 are disjoint.
-/
lemma disjoint_2_5 : Disjoint segment2 segment5 := by
  have := @unit_segment_endpoints_are_vertices;
  contrapose! this;
  refine' ⟨ 0, EuclideanSpace.single 1 1, EuclideanSpace.single 1 1, _, _, _, _ ⟩ <;> norm_num;
  refine' ⟨ EuclideanSpace.single 1 ( 1 / 2 ), _, EuclideanSpace.single 1 ( 1 / 2 + 1 / 2 ), _, _ ⟩ <;> norm_num [ segment_eq_image ];
  · exact ⟨ 1 / 2, by norm_num, by ext i; fin_cases i <;> norm_num ⟩;
  · exact ⟨ 1, by norm_num ⟩;
  · norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
    exact this ( Set.disjoint_left.mpr fun x hx1 hx2 => by
      obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hx1;
      obtain ⟨ c, d, hc, hd, hcd, h ⟩ := hx2;
      unfold sigma at h;
      rw [ ← List.ofFn_inj ] at h ; norm_num at h;
      unfold X_point Y_point O_point V_point at h ; norm_num at h;
      -- Substitute $d = 1 - c$ into the first equation.
      have h_sub : (1 - c) * ((Real.sqrt 6 - Real.sqrt 2) / 4) * (1 - x1) = b * (Real.sqrt 6 - Real.sqrt 2) * (Real.sqrt 6 + Real.sqrt 2) / 16 := by
        rw [ show y1 = ( ( Real.sqrt 6 - Real.sqrt 2 ) / 4 ) * ( 1 - x1 ) / ( ( Real.sqrt 6 + Real.sqrt 2 ) / 4 - x1 ) by
              rw [ eq_div_iff ];
              · rw [ show y1 = ( ( Real.sqrt 6 - Real.sqrt 2 ) / 4 ) * ( 1 - x1 ) / ( ( Real.sqrt 6 + Real.sqrt 2 ) / 4 - x1 ) by rfl ] ; rw [ div_mul_eq_mul_div, div_eq_iff ] ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop ];
              · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop ] ] at h;
        grind;
      have := x1_prop;
      nlinarith [ show 0 < Real.sqrt 6 * Real.sqrt 2 by positivity, show 0 < Real.sqrt 6 by positivity, show 0 < Real.sqrt 2 by positivity, mul_pos hc ( sub_pos.mpr this.1 ), mul_pos hc ( sub_pos.mpr this.2.1 ), mul_pos ( sub_pos.mpr this.1 ) ( sub_pos.mpr this.2.1 ), Real.mul_self_sqrt ( show 6 ≥ 0 by norm_num ), Real.mul_self_sqrt ( show 2 ≥ 0 by norm_num ) ] )

/-
segment3 and segment4 are disjoint.
-/
lemma disjoint_3_4 : Disjoint segment3 segment4 := by
  -- Since segment3 is the open segment between V_point and sigma V_point, and segment4 is the open segment between X_point and Y_point, and V_point is not in segment3, they are disjoint.
  have h_disjoint : ∀ p ∈ segment3, p ≠ V_point := by
    intro p hp hp';
    obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hp;
    rw [ ← List.ofFn_inj ] at * ; norm_num at *;
    unfold sigma at * ; norm_num at * ; nlinarith [ V_bounds ];
  exact Set.disjoint_left.mpr fun p hp3 hp4 => h_disjoint p hp3 <| by
    have h_inter : segment3 ∩ segment4 ⊆ {V_point} := by
      have h_line3 : ∀ p ∈ segment3, p 0 + p 1 = (V_point 0) + (V_point 1) := by
        intro p hp; obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hp; norm_num [ Fin.sum_univ_two ] ; ring_nf;
        unfold sigma; norm_num; rw [ ← eq_sub_iff_add_eq' ] at hab; subst_vars; ring;
      have h_line4 : ∀ p ∈ segment4, p 1 = ((Y_point 1) - (X_point 1)) / ((Y_point 0) - (X_point 0)) * (p 0 - (X_point 0)) + (X_point 1) := by
        intros p hp4
        have h_line4_eq : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ p = (1 - t) • X_point + t • Y_point := by
          rw [ segment4 ] at hp4; rw [ openSegment_eq_image ] at hp4; aesop;
        rcases h_line4_eq with ⟨ t, ht₀, ht₁, rfl ⟩ ; norm_num [ X_point, Y_point ] ; ring_nf;
        nlinarith [ inv_mul_cancel_left₀ ( show ( 1 - x1 ) ≠ 0 by linarith [ show x1 < 1 by exact lt_of_lt_of_le ( Classical.choose_spec ( exists_root_x1 ) |>.2.1 ) ( by norm_num ) ] ) ( t * y1 ) ]
      -- Substitute h_line4 into h_line3 to get an equation in terms of p 0.
      have h_eq : ∀ p ∈ segment3 ∩ segment4, p 0 = V_point 0 := by
        intros p hp
        have h_eq : p 0 + ((Y_point 1 - X_point 1) / (Y_point 0 - X_point 0)) * (p 0 - X_point 0) + X_point 1 = V_point 0 + V_point 1 := by
          linarith [ h_line3 p hp.1, h_line4 p hp.2 ];
        unfold Y_point X_point at *;
        rw [ div_mul_eq_mul_div, add_div', div_add', div_eq_iff ] at h_eq <;> norm_num at *;
        · unfold y1 at h_eq;
          rw [ div_mul_eq_mul_div, add_div', div_eq_iff ] at h_eq <;> norm_num at *;
          · by_cases h : 1 - x1 = 0 <;> simp +decide [ h, mul_assoc, mul_comm, mul_left_comm ] at h_eq ⊢;
            · linarith [ x1_prop ];
            · exact mul_left_cancel₀ h <| by nlinarith [ x1_prop, V_bounds ] ;
          · intro h; norm_num [ h ] at h_eq;
            exact absurd ( h_eq.resolve_left ( by linarith [ show 0 < V_point 0 from by exact div_pos ( by positivity ) ( by positivity ), show 0 < V_point 1 from by exact div_pos ( by nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ] ) ( by positivity ) ] ) ) ( by linarith [ show x1 < 1 by exact lt_of_lt_of_le ( Classical.choose_spec exists_root_x1 |>.2.1 ) ( by norm_num ) ] );
          · exact sub_ne_zero_of_ne <| by linarith [ V_bounds, x1_prop ] ;
        · linarith [ x1_prop ];
        · linarith [ x1_prop ];
        · linarith [ x1_prop ];
      intros p hp
      have hp0 : p 0 = V_point 0 := h_eq p hp
      have hp1 : p 1 = V_point 1 := by
        linarith [ h_line3 p hp.1 ];
      exact funext fun i => by fin_cases i <;> assumption;
    exact h_inter ⟨ hp3, hp4 ⟩

/-
segment3 and segment5 are disjoint.
-/
lemma disjoint_3_5 : Disjoint segment3 segment5 := by
  convert Set.disjoint_left.mpr _;
  rintro p ⟨ a, b, ha, hb, hab, rfl ⟩ ⟨ c, d, hc, hd, hcd, h ⟩ ; simp_all +decide [ openSegment_eq_image ];
  unfold sigma at h;
  rw [ ← List.ofFn_inj ] at h ; norm_num at h;
  unfold X_point Y_point at h ; norm_num at h;
  unfold y1 at h ; norm_num [ show a = 1 - b by linarith, show c = 1 - d by linarith ] at h;
  unfold V_point at * ; norm_num at *;
  rw [ mul_div, div_eq_iff ] at h;
  · have := x1_prop;
    norm_num [ show b = 1 - a by linarith, show d = 1 - c by linarith ] at *;
    nlinarith [ show 0 < Real.sqrt 6 * Real.sqrt 2 by positivity, show 0 < Real.sqrt 6 by positivity, show 0 < Real.sqrt 2 by positivity, mul_pos ha hc, mul_pos ha ( sub_pos.mpr this.1 ), mul_pos ha ( sub_pos.mpr this.2.1 ), mul_pos hc ( sub_pos.mpr this.1 ), mul_pos hc ( sub_pos.mpr this.2.1 ), Real.mul_self_sqrt ( show 6 ≥ 0 by norm_num ), Real.mul_self_sqrt ( show 2 ≥ 0 by norm_num ) ];
  · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop ]

/-
segment1 and segment2 are disjoint.
-/
lemma disjoint_1_2 : Disjoint segment1 segment2 := by
  unfold segment1 segment2;
  norm_num [ openSegment_eq_image ];
  norm_num [ Set.disjoint_left ];
  rintro a x hx₁ hx₂ rfl y hy₁ hy₂ H; have := congr_fun H 0; have := congr_fun H 1; norm_num [ O_point, V_point, sigma ] at *;
  grind

/-
segment1 and segment3 are disjoint.
-/
lemma disjoint_1_3 : Disjoint segment1 segment3 := by
  unfold segment1 segment3;
  norm_num [ openSegment_eq_image ];
  norm_num [ Set.disjoint_left ];
  rintro a x hx₁ hx₂ rfl y hy₁ hy₂ H; have := congr_fun H 0; have := congr_fun H 1; norm_num [ O_point, V_point, sigma ] at *;
  nlinarith [ Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ), Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ), Real.mul_self_sqrt ( show 6 ≥ 0 by norm_num ), Real.mul_self_sqrt ( show 2 ≥ 0 by norm_num ) ]

/-
segment2 and segment3 are disjoint.
-/
lemma disjoint_2_3 : Disjoint segment2 segment3 := by
  rw [ Set.disjoint_left ];
  unfold segment2 segment3;
  norm_num [ openSegment_eq_image ];
  rintro a x hx₁ hx₂ rfl y hy₁ hy₂ H; have := congr_fun H 0; have := congr_fun H 1; norm_num [ O_point, V_point, sigma ] at *;
  nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ]

/-
The distance between sigma(V) and Y is less than 1.
-/
lemma dist_sigma_V_Y_lt_1 : dist (sigma V_point) Y_point < 1 := by
  -- By definition of $y1$, we know that $y1 = \frac{(Real.sqrt 6 - Real.sqrt 2)}{4} \cdot \frac{(1 - x1)}{\frac{(Real.sqrt 6 + Real.sqrt 2)}{4} - x1}$.
  have hy1 : y1 = (Real.sqrt 6 - Real.sqrt 2) / 4 * (1 - x1) / ((Real.sqrt 6 + Real.sqrt 2) / 4 - x1) := by
    unfold y1 V_point; ring_nf;
    repeat' erw [ Matrix.cons_val_succ' ] ; norm_num ; ring;
  -- By definition of $x1$, we know that $x1$ is in the interval $(0.95, 0.96)$.
  have hx1_bounds : 0.95 < x1 ∧ x1 < 0.96 := by
    exact ⟨ Classical.choose_spec exists_root_x1 |>.1, Classical.choose_spec exists_root_x1 |>.2.1 ⟩;
  -- By definition of $V_point$, we know that $V_point 0 = \frac{\sqrt{6} + \sqrt{2}}{4}$ and $V_point 1 = \frac{\sqrt{6} - \sqrt{2}}{4}$.
  have hV_bounds : 0.96 < V_point 0 ∧ V_point 0 < 0.97 ∧ 0.25 < V_point 1 ∧ V_point 1 < 0.26 := by
    exact V_bounds;
  -- By definition of $Y_point$, we know that $Y_point = ![1, y1]$.
  have hY_bounds : 0 < y1 ∧ y1 < 1 := by
    exact y1_bounds;
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
  rw [ Real.sqrt_lt' ] <;> norm_num [ sigma, V_point, Y_point ] at *;
  rw [ eq_div_iff ] at hy1 <;> try linarith [ hx1_bounds, hV_bounds, hY_bounds, hy1, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ] ;
  nlinarith only [ hy1, hx1_bounds, hV_bounds, hY_bounds, Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ]

/-
The distance between Y and sigma(Y) is less than 1.
-/
lemma dist_Y_sigma_Y_lt_1 : dist Y_point (sigma Y_point) < 1 := by
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
  rw [ Real.sqrt_lt' ] <;> norm_num [ Y_point, sigma ];
  -- By definition of $y1$, we know that $0 < y1 < 1$.
  have hy1_bounds : 0 < y1 ∧ y1 < 1 := by
    exact y1_bounds;
  nlinarith [ show y1 > 1 / 2 by { rw [ show y1 = ( V_point 1 ) * ( 1 - x1 ) / ( V_point 0 - x1 ) by rfl ] ; rw [ gt_iff_lt ] ; rw [ lt_div_iff₀ ] <;> nlinarith [ V_bounds, x1_prop ] } ]

/-
The distance between V and sigma(Y) is less than 1.
-/
lemma dist_V_sigma_Y_lt_1 : dist V_point (sigma Y_point) < 1 := by
  convert dist_sigma_V_Y_lt_1 using 1;
  convert sigma_isometry _ _ using 2 ; unfold sigma ; ext i ; fin_cases i <;> norm_num;
  · rfl;
  · rfl

/-
Region_Corner is the triangle with vertices Y, sigma Y, and (1,1).
-/
def Region_Corner : Set Point := convexHull ℝ {Y_point, sigma Y_point, ![1, 1]}

/-
The diameter of Region6b is less than 1.
-/
lemma Region6b_diameter_lt_1 : ∀ x y : Point, x ∈ Region6b → y ∈ Region6b → dist x y < 1 := by
  have h_sigma_V_sigma_Y_lt_1 : dist (sigma V_point) (sigma Y_point) < 1 := by
    rw [ sigma_isometry ];
    exact dist_V_Y_lt_1;
  intros x y hx hy;
  -- By the triangle diameter lemma, since the sides of Region6b are all less than 1, any two points in Region6b are also less than 1 apart.
  have h_triangle_diameter : ∀ x y : Point, x ∈ convexHull ℝ {sigma V_point, Y_point, sigma Y_point} → y ∈ convexHull ℝ {sigma V_point, Y_point, sigma Y_point} → dist x y ≤ max (dist (sigma V_point) Y_point) (max (dist Y_point (sigma Y_point)) (dist (sigma Y_point) (sigma V_point))) := by
    apply dist_le_max_vertices;
  refine' lt_of_le_of_lt ( h_triangle_diameter x y hx hy ) _;
  simp_all +decide [ dist_comm ];
  exact ⟨ by simpa only [ dist_comm ] using dist_sigma_V_Y_lt_1, by simpa only [ dist_comm ] using dist_Y_sigma_Y_lt_1 ⟩

/-
Distance from O to sigma(X) is less than 1.
-/
lemma dist_O_sigma_X_lt_1 : dist O_point (sigma X_point) < 1 := by
  convert dist_O_X_lt_1 using 1;
  unfold O_point sigma; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring_nf;

/-
Distance from sigma(V) to sigma(X) is less than 1.
-/
lemma dist_sigma_V_sigma_X_lt_1 : dist (sigma V_point) (sigma X_point) < 1 := by
  rw [ sigma_isometry ] ; exact dist_V_X_lt_1;

/-
Distance from sigma(X) to sigma(A0) is less than 1.
-/
lemma dist_sigma_X_sigma_A0_lt_1 : dist (sigma X_point) (sigma A_0) < 1 := by
  rw [ @dist_eq_norm ];
  norm_num [ EuclideanSpace.norm_eq ];
  rw [ Real.sqrt_lt' ] <;> norm_num [ sigma, X_point, A_0 ];
  exact abs_lt.mpr ⟨ by linarith [ x1_prop.1 ], by linarith [ x1_prop.2.1 ] ⟩

/-
Distance from sigma(A0) to sigma(Y) is less than 1.
-/
lemma dist_sigma_A0_sigma_Y_lt_1 : dist (sigma A_0) (sigma Y_point) < 1 := by
  rw [ sigma_isometry ] ; exact dist_A0_Y_lt_1

/-
S_finite blocks Region1.
-/
lemma Region1_blocking : IsBlocking S_finite Region1 := by
  intro L hL hL_sub
  obtain ⟨x, y, hxy⟩ : ∃ x y : Point, dist x y = 1 ∧ L = openSegment ℝ x y := by
    exact hL;
  -- By Lemma~\ref{lem:triangle_diameter_lemma}, any unit segment in Region 1 must be one of the sides.
  have h_triangle_diameter_lemma : x ∈ ({O_point, V_point, sigma V_point} : Set Point) ∧ y ∈ ({O_point, V_point, sigma V_point} : Set Point) := by
    have h_triangle_diameter_lemma : x ∈ convexHull ℝ {O_point, V_point, sigma V_point} ∧ y ∈ convexHull ℝ {O_point, V_point, sigma V_point} := by
      have hL_in_triangle : L ⊆ convexHull ℝ {O_point, V_point, sigma V_point} := by
        exact hL_sub;
      simp_all +decide [ Set.subset_def ];
      have hx : Filter.Tendsto (fun t : ℝ => (1 - t) • x + t • y) (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
        exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) );
      have hy : Filter.Tendsto (fun t : ℝ => (1 - t) • x + t • y) (nhdsWithin 1 (Set.Iio 1)) (nhds y) := by
        exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num );
      have hx_convex : x ∈ closure (convexHull ℝ {O_point, V_point, sigma V_point}) := by
        exact mem_closure_of_tendsto hx ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ) fun t ht => hL_in_triangle _ <| by exact ⟨ 1 - t, t, by linarith [ ht.1, ht.2 ], by linarith [ ht.1, ht.2 ], by simp +decide ⟩ )
      have hy_convex : y ∈ closure (convexHull ℝ {O_point, V_point, sigma V_point}) := by
        exact mem_closure_of_tendsto hy ( Filter.eventually_of_mem ( Ioo_mem_nhdsLT zero_lt_one ) fun t ht => hL_in_triangle _ <| by exact ⟨ 1 - t, t, by linarith [ ht.1, ht.2 ], by linarith [ ht.1, ht.2 ], by aesop ⟩ );
      have hx_convex : IsClosed (convexHull ℝ {O_point, V_point, sigma V_point}) := by
        have h_convex_closed : IsCompact (convexHull ℝ {O_point, V_point, sigma V_point}) := by
          have h_convex_closed : IsCompact (convexHull ℝ ({O_point, V_point, sigma V_point} : Set (EuclideanSpace ℝ (Fin 2)))) := by
            have h_finite : Set.Finite ({O_point, V_point, sigma V_point} : Set (EuclideanSpace ℝ (Fin 2))) := by
              exact Set.toFinite _
            exact h_finite.isCompact_convexHull;
          exact h_convex_closed;
        exact h_convex_closed.isClosed
      have hy_convex : IsClosed (convexHull ℝ {O_point, V_point, sigma V_point}) := by
        exact hx_convex;
      exact ⟨ hx_convex.closure_subset ‹_›, hy_convex.closure_subset ‹_› ⟩;
    apply unit_segment_endpoints_are_vertices;
    any_goals tauto;
    · exact dist_O_V.le;
    · exact dist_V_sigma_V.le;
    · rw [ dist_comm ] ; exact dist_O_sigma_V.le;
  rcases h_triangle_diameter_lemma with ⟨ rfl | rfl | rfl, rfl | rfl | rfl ⟩ <;> simp_all +decide [ IsUnitSegment ];
  all_goals simp_all +decide [ Set.disjoint_left, S_finite ];
  all_goals unfold segment1 segment2 segment3 segment4 segment5; simp +decide [ openSegment_symm ] ;
  all_goals norm_num [ openSegment_eq_image ] at *;
  exact Or.inl ⟨ _, 1 / 2, by norm_num, rfl ⟩;
  · exact Or.inr <| Or.inl ⟨ _, 1 / 2, by norm_num, rfl ⟩;
  · exact Or.inl ⟨ _, 1 / 2, by norm_num, rfl ⟩;
  · exact Or.inr <| Or.inr <| Or.inl ⟨ _, 1 / 2, by norm_num, rfl ⟩;
  · exact Or.inr <| Or.inl ⟨ _, 1 / 2, by norm_num, rfl ⟩;
  · exact Or.inr <| Or.inr <| Or.inl ⟨ _, 1 / 2, by norm_num, rfl ⟩

/-
If the distance between endpoints is less than 1, the open segment is not a unit segment.
-/
lemma not_isUnitSegment_of_dist_lt_1 {A B : Point} (h : dist A B < 1) : ¬ IsUnitSegment (openSegment ℝ A B) := by
  rintro ⟨ x, y, hxy, h ⟩;
  -- Since open segments determine their endpoints (up to order), we must have {A, B} = {x, y}.
  have h_eq_set : ({A, B} : Set Point) = ({x, y} : Set Point) := by
    -- Applying the lemma that states the closure of an open segment is the closed segment.
    have h_closure : closure (openSegment ℝ A B) = segment ℝ A B ∧ closure (openSegment ℝ x y) = segment ℝ x y := by
      bound;
    simp_all +decide [ segment_eq_image ];
    have h_eq_set : ∀ t : ℝ, t ∈ Set.Icc 0 1 → ∃ s : ℝ, s ∈ Set.Icc 0 1 ∧ (1 - t) • x + t • y = (1 - s) • A + s • B := by
      exact fun t ht => h_closure.subset ⟨ t, ht, rfl ⟩ |> fun ⟨ s, hs, hs' ⟩ => ⟨ s, hs, hs'.symm ⟩;
    have h_eq_set : ∃ s₁ s₂ : ℝ, s₁ ∈ Set.Icc 0 1 ∧ s₂ ∈ Set.Icc 0 1 ∧ x = (1 - s₁) • A + s₁ • B ∧ y = (1 - s₂) • A + s₂ • B := by
      exact Exists.elim ( h_eq_set 0 ( by norm_num ) ) fun s₁ hs₁ => Exists.elim ( h_eq_set 1 ( by norm_num ) ) fun s₂ hs₂ => ⟨ s₁, s₂, hs₁.1, hs₂.1, by simpa using hs₁.2, by simpa using hs₂.2 ⟩;
    obtain ⟨ s₁, s₂, hs₁, hs₂, rfl, rfl ⟩ := h_eq_set;
    have h_eq_set : s₁ = 0 ∧ s₂ = 1 ∨ s₁ = 1 ∧ s₂ = 0 := by
      have h_eq_set : dist ((1 - s₁) • A + s₁ • B) ((1 - s₂) • A + s₂ • B) = |s₂ - s₁| * dist A B := by
        norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
        rw [ show ( ( 1 - s₁ ) * A 0 + s₁ * B 0 - ( ( 1 - s₂ ) * A 0 + s₂ * B 0 ) ) ^ 2 + ( ( 1 - s₁ ) * A 1 + s₁ * B 1 - ( ( 1 - s₂ ) * A 1 + s₂ * B 1 ) ) ^ 2 = ( s₂ - s₁ ) ^ 2 * ( ( A 0 - B 0 ) ^ 2 + ( A 1 - B 1 ) ^ 2 ) by ring, Real.sqrt_mul ( sq_nonneg _ ), Real.sqrt_sq_eq_abs ];
      cases abs_cases ( s₂ - s₁ ) <;> first | left; constructor <;> nlinarith [ hs₁.1, hs₁.2, hs₂.1, hs₂.2 ] | right; constructor <;> nlinarith [ hs₁.1, hs₁.2, hs₂.1, hs₂.2 ] ;
    rcases h_eq_set with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num;
    exact Set.pair_comm _ _;
  -- Since {A, B} = {x, y}, we have A = x and B = y or A = y and B = x.
  have h_cases : (A = x ∧ B = y) ∨ (A = y ∧ B = x) := by
    simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ];
    grind;
  cases h_cases <;> simp_all +decide [ dist_comm ]

/-
S_finite blocks Region2.
-/
lemma Region2_blocking : IsBlocking S_finite Region2 := by
  intro L hLL_sub;
  -- By the triangle diameter lemma, L must be one of the open segments OV, VX, or XO.
  intros hL_sub
  have hL_segment : L = openSegment ℝ O_point V_point ∨ L = openSegment ℝ V_point X_point ∨ L = openSegment ℝ X_point O_point := by
    apply triangle_diameter_lemma O_point V_point X_point;
    · exact dist_O_V.le;
    · exact le_of_lt ( dist_V_X_lt_1 );
    · exact le_of_lt ( by simpa only [ dist_comm ] using dist_O_X_lt_1 );
    · assumption;
    · exact hL_sub;
  rcases hL_segment with ( rfl | rfl | rfl );
  · use openSegment ℝ O_point V_point;
    refine' ⟨ _, _ ⟩;
    · exact Set.mem_insert _ _;
    · norm_num [ openSegment_eq_image ];
      exact Set.Nonempty.ne_empty ⟨ 1 / 2, by norm_num ⟩;
  · exact absurd hLL_sub ( not_isUnitSegment_of_dist_lt_1 ( dist_V_X_lt_1 ) );
  · exact absurd hLL_sub ( not_isUnitSegment_of_dist_lt_1 ( by linarith [ dist_comm O_point X_point, dist_O_X_lt_1 ] ) )

/-
S_finite blocks Region3.
-/
lemma Region3_blocking : IsBlocking S_finite Region3 := by
  intro L hL hL_subset
  have hL_segment : L = openSegment ℝ O_point (sigma V_point) ∨ L = openSegment ℝ (sigma V_point) (sigma X_point) ∨ L = openSegment ℝ (sigma X_point) O_point := by
    apply_rules [ triangle_diameter_lemma ];
    · exact dist_O_sigma_V.le.trans ( by norm_num );
    · exact le_of_lt ( dist_sigma_V_sigma_X_lt_1 );
    · exact le_of_lt ( by simpa [ dist_comm ] using dist_O_sigma_X_lt_1 );
  rcases hL_segment with ( rfl | rfl | rfl ) <;> simp_all +decide [ S_finite ];
  · unfold segment1 segment2 segment3 segment4 segment5; norm_num [ Set.disjoint_left ] ;
    exact Or.inr <| Or.inl <| Set.Nonempty.ne_empty <| by exact ⟨ ( 1 / 2 : ℝ ) • O_point + ( 1 / 2 : ℝ ) • sigma V_point, by exact ⟨ 1 / 2, 1 / 2, by norm_num ⟩ ⟩ ;
  · exact absurd hL ( not_isUnitSegment_of_dist_lt_1 ( by linarith [ dist_sigma_V_sigma_X_lt_1 ] ) );
  · contrapose! hL; simp_all +decide [ Set.disjoint_left ] ;
    exact not_isUnitSegment_of_dist_lt_1 ( by simpa [ dist_comm ] using dist_O_sigma_X_lt_1 )

/-
S_finite blocks Region5.
-/
lemma Region5_blocking : IsBlocking S_finite Region5 := by
  -- Apply the triangle diameter lemma to the triangle sigma(X), sigma(A0), sigma(Y).
  have h_triangle : ∀ L : Set Point, IsUnitSegment L → L ⊆ Region5 → L = openSegment ℝ (sigma X_point) (sigma A_0) ∨ L = openSegment ℝ (sigma A_0) (sigma Y_point) ∨ L = openSegment ℝ (sigma Y_point) (sigma X_point) := by
    intros L hL hL_sub
    apply triangle_diameter_lemma;
    · exact le_of_lt ( dist_sigma_X_sigma_A0_lt_1 );
    · exact le_of_lt ( by simpa [ dist_comm ] using dist_sigma_A0_sigma_Y_lt_1 );
    · convert dist_sigma_X_sigma_Y.le using 1;
      exact dist_comm _ _;
    · assumption;
    · grind;
  intro L hL hL_sub
  obtain hL_cases | hL_cases | hL_cases := h_triangle L hL hL_sub
  all_goals generalize_proofs at *;
  · -- Since $L$ is a unit segment and its endpoints are inside the square, its length must be strictly less than 1.
    have hL_length_lt_1 : dist (sigma X_point) (sigma A_0) < 1 := by
      exact dist_sigma_X_sigma_A0_lt_1;
    exact False.elim <| not_isUnitSegment_of_dist_lt_1 hL_length_lt_1 <| hL_cases ▸ hL;
  · have h_dist_lt_1 : dist (sigma A_0) (sigma Y_point) < 1 := by
      convert dist_sigma_A0_sigma_Y_lt_1 using 1
    generalize_proofs at *; (
    exact False.elim <| not_isUnitSegment_of_dist_lt_1 h_dist_lt_1 <| hL_cases ▸ hL);
  · use segment5; simp [hL_cases, S_finite];
    unfold segment5; simp +decide [ Set.disjoint_left ] ;
    refine' ⟨ ( 1 / 2 : ℝ ) • sigma X_point + ( 1 / 2 : ℝ ) • sigma Y_point, _, _ ⟩ <;> norm_num [ openSegment_eq_image ];
    · exact ⟨ 1 / 2, by norm_num ⟩;
    · exact ⟨ 1 / 2, by norm_num, by ext i; fin_cases i <;> norm_num <;> ring ⟩

/-
If an open segment is contained in a closed region, its endpoints are also in the region (assuming distinct endpoints).
-/
lemma endpoints_in_closed_region {R : Set Point} (hR : IsClosed R) {x y : Point} (h_subset : openSegment ℝ x y ⊆ R) (h_nonempty : (openSegment ℝ x y).Nonempty) : x ∈ R ∧ y ∈ R := by
  have h_closure : closure (openSegment ℝ x y) ⊆ R := by
    exact hR.closure_subset_iff.mpr h_subset;
  have h_closure_eq : closure (openSegment ℝ x y) = segment ℝ x y := by
    exact closure_openSegment x y;
  exact ⟨ h_closure <| h_closure_eq.symm ▸ left_mem_segment _ _ _, h_closure <| h_closure_eq.symm ▸ right_mem_segment _ _ _ ⟩

/-
Region6_Total is the convex hull of {V, sigma V, Y, sigma Y, (1,1)}.
-/
def Region6_Total : Set Point := convexHull ℝ {V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]}

/-
The distance from V to (1,1) is less than 1.
-/
def Corner_point : Point := ![1, 1]

lemma dist_V_Corner_lt_1 : dist V_point Corner_point < 1 := by
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
  rw [ Real.sqrt_lt' ] <;> norm_num [ V_point, Corner_point ];
  nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ]

/-
Distance from Y to Corner is less than 1.
-/
lemma dist_Y_Corner_lt_1 : dist Y_point Corner_point < 1 := by
  unfold Y_point Corner_point;
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
  rw [ Real.sqrt_sq_eq_abs, abs_lt ];
  constructor <;> linarith [ y1_bounds ]

/-
Distance from sigma(V) to Corner is less than 1.
-/
lemma dist_sigma_V_Corner_lt_1 : dist (sigma V_point) Corner_point < 1 := by
  convert dist_V_Corner_lt_1 using 1;
  unfold sigma Corner_point; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ;
  ring_nf

/-
The distance between two convex combinations is bounded by the weighted sum of distances between the points.
-/
lemma dist_convex_combination_le {ι : Type*} {s : Finset ι} {v : ι → Point} {a b : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ j ∈ s, 0 ≤ b j)
    (ha_sum : ∑ i ∈ s, a i = 1) (hb_sum : ∑ j ∈ s, b j = 1) :
    dist (∑ i ∈ s, a i • v i) (∑ j ∈ s, b j • v j) ≤ ∑ i ∈ s, ∑ j ∈ s, a i * b j * dist (v i) (v j) := by
      simp +decide only [dist_eq_norm];
      -- By Fubini's theorem, we can interchange the order of summation.
      have h_fubini : ∑ x ∈ s, a x • v x - ∑ x ∈ s, b x • v x = ∑ i ∈ s, ∑ j ∈ s, a i • b j • (v i - v j) := by
        simp +decide only [smul_sub, Finset.sum_sub_distrib];
        simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, ← Finset.smul_sum, ← Finset.sum_smul, ha_sum, hb_sum ];
      rw [ h_fubini ];
      refine' le_trans ( norm_sum_le _ _ ) ( Finset.sum_le_sum fun i hi => norm_sum_le _ _ |> le_trans <| Finset.sum_le_sum fun j hj => _ );
      simp +decide [ norm_smul, mul_assoc, abs_of_nonneg ( ha i hi ), abs_of_nonneg ( hb j hj ) ]

/-
If the distance between two convex combinations is 1 and the diameter is 1, then any pair of points with positive weights must be at distance 1.
-/
lemma convex_combination_dist_eq_one_implies_support_dist_eq_one
  {ι : Type*} {s : Finset ι} {v : ι → Point} {a b : ι → ℝ}
  (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ j ∈ s, 0 ≤ b j)
  (ha_sum : ∑ i ∈ s, a i = 1) (hb_sum : ∑ j ∈ s, b j = 1)
  (h_diam : ∀ i ∈ s, ∀ j ∈ s, dist (v i) (v j) ≤ 1)
  (h_dist : dist (∑ i ∈ s, a i • v i) (∑ j ∈ s, b j • v j) = 1) :
  ∀ i ∈ s, ∀ j ∈ s, a i > 0 → b j > 0 → dist (v i) (v j) = 1 := by
    -- Applying the lemma about distance and convex combination.
    have h_dist_le : ∑ i ∈ s, ∑ j ∈ s, a i * b j * dist (v i) (v j) = 1 := by
      have h_dist_le : 1 ≤ ∑ i ∈ s, ∑ j ∈ s, a i * b j * dist (v i) (v j) := by
        convert dist_convex_combination_le ha hb ha_sum hb_sum |> le_trans h_dist.ge using 1;
      refine' le_antisymm _ h_dist_le;
      refine' le_trans ( Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ( h_diam i hi j hj ) ( mul_nonneg ( ha i hi ) ( hb j hj ) ) ) _;
      simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, ha_sum, hb_sum ];
    intro i hi j hj hi_pos hj_pos
    have h_eq : a i * b j * dist (v i) (v j) = a i * b j := by
      by_contra h_neq;
      have h_eq : ∑ i ∈ s, ∑ j ∈ s, a i * b j * dist (v i) (v j) < ∑ i ∈ s, ∑ j ∈ s, a i * b j := by
        apply Finset.sum_lt_sum;
        · exact fun i hi => Finset.sum_le_sum fun j hj => mul_le_of_le_one_right ( mul_nonneg ( ha i hi ) ( hb j hj ) ) ( h_diam i hi j hj );
        · refine' ⟨ i, hi, Finset.sum_lt_sum _ _ ⟩;
          · exact fun k hk => mul_le_of_le_one_right ( mul_nonneg hi_pos.le ( hb k hk ) ) ( h_diam i hi k hk );
          · exact ⟨ j, hj, lt_of_le_of_ne ( mul_le_of_le_one_right ( mul_nonneg hi_pos.le hj_pos.le ) ( h_diam i hi j hj ) ) h_neq ⟩;
      simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
    nlinarith only [ mul_pos hi_pos hj_pos, h_eq, h_diam i hi j hj ]

/-
If every pair of points with positive weights forms the set {A, B}, then the points are constant on the supports of the weights, taking distinct values A and B.
-/
lemma constant_on_support_of_pair_condition {ι : Type*} {s : Finset ι} {v : ι → Point} {a b : ι → ℝ} {A B : Point}
    (h_distinct : A ≠ B)
    (ha_exists : ∃ i ∈ s, a i > 0) (hb_exists : ∃ j ∈ s, b j > 0)
    (h_pair : ∀ i ∈ s, ∀ j ∈ s, a i > 0 → b j > 0 → ({v i, v j} : Set Point) = {A, B}) :
    ((∀ i ∈ s, a i > 0 → v i = A) ∧ (∀ j ∈ s, b j > 0 → v j = B)) ∨
    ((∀ i ∈ s, a i > 0 → v i = B) ∧ (∀ j ∈ s, b j > 0 → v j = A)) := by
      obtain ⟨ j, hj₁, hj₂ ⟩ := hb_exists;
      cases' eq_or_ne ( v j ) A with h h <;> simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ];
      · grind;
      · grind

/-
If all pairs of points with positive weights in two convex combinations form the set {A, B}, then the convex combinations themselves form the set {A, B}.
-/
lemma support_implies_endpoints {ι : Type*} {s : Finset ι} {v : ι → Point} {a b : ι → ℝ} {A B : Point}
    (h_distinct : A ≠ B)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ j ∈ s, 0 ≤ b j)
    (ha_sum : ∑ i ∈ s, a i = 1) (hb_sum : ∑ j ∈ s, b j = 1)
    (h_pair : ∀ i ∈ s, ∀ j ∈ s, a i > 0 → b j > 0 → ({v i, v j} : Set Point) = {A, B}) :
    ({∑ i ∈ s, a i • v i, ∑ j ∈ s, b j • v j} : Set Point) = {A, B} := by
      -- By `constant_on_support_of_pair_condition`, we know that either (all vi with ai > 0 equal A and all vj with bj > 0 equal B), or (all vi with ai > 0 equal B and all vj with bj > 0 equal A).
      have h_cases : ((∀ i ∈ s, a i > 0 → v i = v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ i ∈ s, a i) ≠ 0)))) ∧ (∀ j ∈ s, b j > 0 → v j = v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ j ∈ s, b j) ≠ 0))))) ∨ ((∀ i ∈ s, a i > 0 → v i = v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ j ∈ s, b j) ≠ 0)))) ∧ (∀ j ∈ s, b j > 0 → v j = v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ i ∈ s, a i) ≠ 0))))) := by
        have h_cases : (∀ i ∈ s, a i > 0 → v i = v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ i ∈ s, a i) ≠ 0)))) ∧ (∀ j ∈ s, b j > 0 → v j = v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ j ∈ s, b j) ≠ 0)))) ∨ (∀ i ∈ s, a i > 0 → v i = v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ j ∈ s, b j) ≠ 0)))) ∧ (∀ j ∈ s, b j > 0 → v j = v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ i ∈ s, a i) ≠ 0)))) := by
          have h_support : (∃ i ∈ s, a i > 0) ∧ (∃ j ∈ s, b j > 0) := by
            exact ⟨ by obtain ⟨ i, hi ⟩ := Finset.exists_ne_zero_of_sum_ne_zero ( by linarith : ( ∑ i ∈ s, a i ) ≠ 0 ) ; exact ⟨ i, hi.1, lt_of_le_of_ne ( ha i hi.1 ) ( Ne.symm hi.2 ) ⟩, by obtain ⟨ j, hj ⟩ := Finset.exists_ne_zero_of_sum_ne_zero ( by linarith : ( ∑ j ∈ s, b j ) ≠ 0 ) ; exact ⟨ j, hj.1, lt_of_le_of_ne ( hb j hj.1 ) ( Ne.symm hj.2 ) ⟩ ⟩
          have h_cases : ∀ i ∈ s, ∀ j ∈ s, a i > 0 → b j > 0 → ({v i, v j} : Set Point) = {v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ i ∈ s, a i) ≠ 0))), v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ j ∈ s, b j) ≠ 0)))} := by
            intros i hi j hj ha_pos hb_pos
            have h_eq : ({v i, v j} : Set Point) = {A, B} := by
              exact h_pair i hi j hj ha_pos hb_pos
            have h_eq' : ({v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ i ∈ s, a i) ≠ 0))), v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ j ∈ s, b j) ≠ 0)))} : Set Point) = {A, B} := by
              convert h_pair _ ( Classical.choose_spec h_support.1 |>.1 ) _ ( Classical.choose_spec h_support.2 |>.1 ) ( Classical.choose_spec h_support.1 |>.2 ) ( Classical.choose_spec h_support.2 |>.2 ) using 1;
              congr! 1;
              · grind;
              · congr! 1;
                grind
            rw [h_eq, h_eq'];
          have := constant_on_support_of_pair_condition ( show v ( Classical.choose ( Finset.exists_ne_zero_of_sum_ne_zero ( by linarith : ∑ i ∈ s, a i ≠ 0 ) ) ) ≠ v ( Classical.choose ( Finset.exists_ne_zero_of_sum_ne_zero ( by linarith : ∑ j ∈ s, b j ≠ 0 ) ) ) from ?_ ) h_support.1 h_support.2 h_cases ; aesop;
          intro h; have := Classical.choose_spec h_support.1; have := Classical.choose_spec h_support.2; simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ] ;
          have := h_pair _ ( Classical.choose_spec h_support.1 |>.1 ) _ ( Classical.choose_spec h_support.2 |>.1 ) ( Classical.choose_spec h_support.1 |>.2 ) ( Classical.choose_spec h_support.2 |>.2 ) ; aesop;
        exact h_cases;
      have h_sum_eq : ∑ i ∈ s, a i • v i = v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ i ∈ s, a i) ≠ 0))) ∧ ∑ j ∈ s, b j • v j = v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ j ∈ s, b j) ≠ 0))) ∨ ∑ i ∈ s, a i • v i = v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ j ∈ s, b j) ≠ 0))) ∧ ∑ j ∈ s, b j • v j = v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ i ∈ s, a i) ≠ 0))) := by
        have h_sum_eq : ∑ i ∈ s, a i • v i = ∑ i ∈ s, a i • v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ i ∈ s, a i) ≠ 0))) ∧ ∑ j ∈ s, b j • v j = ∑ j ∈ s, b j • v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ j ∈ s, b j) ≠ 0))) ∨ ∑ i ∈ s, a i • v i = ∑ i ∈ s, a i • v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ j ∈ s, b j) ≠ 0))) ∧ ∑ j ∈ s, b j • v j = ∑ j ∈ s, b j • v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ i ∈ s, a i) ≠ 0))) := by
          exact Or.imp ( fun h => ⟨ Finset.sum_congr rfl fun i hi => by by_cases hi' : a i = 0 <;> simpa [ hi' ] using h.1 i hi ( lt_of_le_of_ne ( ha i hi ) ( Ne.symm hi' ) ) ▸ rfl, Finset.sum_congr rfl fun j hj => by by_cases hj' : b j = 0 <;> simpa [ hj' ] using h.2 j hj ( lt_of_le_of_ne ( hb j hj ) ( Ne.symm hj' ) ) ▸ rfl ⟩ ) ( fun h => ⟨ Finset.sum_congr rfl fun i hi => by by_cases hi' : a i = 0 <;> simpa [ hi' ] using h.1 i hi ( lt_of_le_of_ne ( ha i hi ) ( Ne.symm hi' ) ) ▸ rfl, Finset.sum_congr rfl fun j hj => by by_cases hj' : b j = 0 <;> simpa [ hj' ] using h.2 j hj ( lt_of_le_of_ne ( hb j hj ) ( Ne.symm hj' ) ) ▸ rfl ⟩ ) h_cases;
        convert h_sum_eq using 2 <;> simp +decide [ ← Finset.sum_smul, ha_sum, hb_sum ];
      have h_pair_eq : ({v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ i ∈ s, a i) ≠ 0))), v (Classical.choose (Finset.exists_ne_zero_of_sum_ne_zero (by linarith : (∑ j ∈ s, b j) ≠ 0)))} : Set Point) = {A, B} := by
        convert h_pair _ ( Classical.choose_spec ( Finset.exists_ne_zero_of_sum_ne_zero ( by linarith : ( ∑ i ∈ s, a i ) ≠ 0 ) ) |>.1 ) _ ( Classical.choose_spec ( Finset.exists_ne_zero_of_sum_ne_zero ( by linarith : ( ∑ j ∈ s, b j ) ≠ 0 ) ) |>.1 ) _ _ using 1 <;> simp +decide [ Classical.choose_spec ( Finset.exists_ne_zero_of_sum_ne_zero ( by linarith : ( ∑ i ∈ s, a i ) ≠ 0 ) ), Classical.choose_spec ( Finset.exists_ne_zero_of_sum_ne_zero ( by linarith : ( ∑ j ∈ s, b j ) ≠ 0 ) ) ];
        · exact Classical.choose_spec ( Finset.exists_ne_zero_of_sum_ne_zero ( by linarith : ( ∑ i ∈ s, a i ) ≠ 0 ) ) |>.2 |> fun h => lt_of_le_of_ne ( ha _ ( Classical.choose_spec ( Finset.exists_ne_zero_of_sum_ne_zero ( by linarith : ( ∑ i ∈ s, a i ) ≠ 0 ) ) |>.1 ) ) ( Ne.symm h );
        · exact lt_of_le_of_ne ( hb _ ( Classical.choose_spec ( Finset.exists_ne_zero_of_sum_ne_zero ( by linarith : ( ∑ j ∈ s, b j ) ≠ 0 ) ) |>.1 ) ) ( Ne.symm ( Classical.choose_spec ( Finset.exists_ne_zero_of_sum_ne_zero ( by linarith : ( ∑ j ∈ s, b j ) ≠ 0 ) ) |>.2 ) );
      grind

/-
UnionRegions is the union of all 8 regions. S_total is the union of S_finite and S_sides.
-/
def UnionRegions : Set Point := Region1 ∪ Region2 ∪ Region3 ∪ Region4 ∪ Region5 ∪ Region6a ∪ Region6b ∪ Region_Corner

def S_total : Set (Set Point) := S_finite ∪ S_sides

/-
Applying sigma twice returns the original point.
-/
lemma sigma_sigma_eq_id (p : Point) : sigma (sigma p) = p := by
  exact funext fun i => by fin_cases i <;> rfl;

/-
If a point satisfies the linear inequalities for Region2, it is in Region2.
-/
open Set

/-
If a point satisfies the linear inequalities for Region4, it is in Region4.
-/
open Set

lemma in_Region4_of_coords (p : Point) (hp : p ∈ Region_Square)
    (h1 : x1 ≤ p 0) -- Right of X
    (h2 : p 1 ≤ y1) -- Below Y
    (h3 : p 1 * (1 - x1) ≤ y1 * (p 0 - x1)) -- Below XY
    : p ∈ Region4 := by
      -- By definition of $Region4$, we know that $p$ is a convex combination of the vertices $X_point$, $A_0$, and $Y_point$.
      have h_convex_comb : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • X_point + b • A_0 + c • Y_point := by
        use (1 - p 0) / (1 - x1), 1 - (1 - p 0) / (1 - x1) - p 1 / y1, p 1 / y1;
        refine' ⟨ div_nonneg ( by linarith [ hp.2.1 ] ) ( by linarith [ show x1 < 1 by exact lt_of_lt_of_le ( Classical.choose_spec exists_root_x1 |>.2.1 ) ( by norm_num ) ] ), _, _, _, _ ⟩ <;> norm_num [ X_point, A_0, Y_point ];
        · rw [ div_le_iff₀ ] <;> nlinarith [ show 0 < y1 by exact y1_bounds.1, show x1 < 1 by exact lt_of_lt_of_le ( Classical.choose_spec exists_root_x1 |>.2.1 ) ( by norm_num ), mul_div_cancel₀ ( 1 - p 0 ) ( by linarith [ show x1 < 1 by exact lt_of_lt_of_le ( Classical.choose_spec exists_root_x1 |>.2.1 ) ( by norm_num ) ] : ( 1 - x1 ) ≠ 0 ) ];
        · exact div_nonneg ( by linarith [ hp.2.2.1 ] ) ( by linarith [ y1_bounds.1 ] );
        · ring;
        · ext i ; fin_cases i <;> norm_num;
          · linarith! [ div_mul_cancel₀ ( 1 - p 0 ) ( show ( 1 - x1 ) ≠ 0 by linarith [ show x1 < 1 by exact lt_of_lt_of_le ( Classical.choose_spec exists_root_x1 |>.2.1 ) <| by norm_num ] ) ];
          · rw [ div_mul_cancel₀ _ ( ne_of_gt ( by linarith [ show 0 < y1 from by linarith [ show 0 < y1 from by linarith [ show 0 < y1 from by exact y1_bounds.1 ] ] ] ) ) ];
            rfl;
      obtain ⟨ a, b, c, ha, hb, hc, habc ⟩ := h_convex_comb; simp_all +decide [ Region4 ] ;
      rw [ convexHull_eq ];
      refine' ⟨ Fin 3, { 0, 1, 2 }, fun i => if i = 0 then a else if i = 1 then b else c, fun i => if i = 0 then X_point else if i = 1 then A_0 else Y_point, _, _, _, _ ⟩ <;> simp +decide [ Fin.sum_univ_three, Finset.centerMass ] ; aesop;
      · linarith;
      · norm_num [ ← add_assoc, habc.1 ]

/-
If a point satisfies the linear inequalities for Region1, it is in Region1.
-/
open Set

/-
If a point satisfies the linear inequalities for Region3, it is in Region3.
-/
open Set

/-
If a point satisfies the linear inequality for Region_Corner, it is in Region_Corner.
-/
open Set

lemma in_Region_Corner_of_coords (p : Point) (hp : p ∈ Region_Square)
    (h1 : 1 + y1 ≤ p 0 + p 1) -- Above Y-sigma Y
    : p ∈ Region_Corner := by
      unfold Region_Corner;
      -- We can express p as a convex combination of Y, sigma(Y), and (1,1).
      have h_comb : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • Y_point + b • sigma Y_point + c • ![1, 1] := by
        use (1 - p 1) / (1 - y1), (1 - p 0) / (1 - y1), 1 - (1 - p 1) / (1 - y1) - (1 - p 0) / (1 - y1);
        field_simp;
        refine' ⟨ div_nonneg ( sub_nonneg.2 <| hp.2.2.2.le ) ( sub_nonneg.2 <| _ ), div_nonneg ( sub_nonneg.2 <| hp.2.1.le ) ( sub_nonneg.2 <| _ ), _, _, _ ⟩;
        · linarith [ hp.1, hp.2.1, hp.2.2.1, hp.2.2.2 ];
        · exact le_of_lt ( y1_bounds.2 );
        · rw [ sub_sub, le_sub_iff_add_le ];
          rw [ zero_add, ← add_div, div_le_iff₀ ] <;> nlinarith [ hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, y1_bounds ];
        · ring;
        · ext i ; fin_cases i <;> norm_num [ Y_point, sigma ] <;> ring_nf!;
          · erw [ Pi.smul_apply ] ; norm_num ; ring_nf;
            linarith! [ inv_mul_cancel_left₀ ( show ( 1 - y1 ) ≠ 0 by linarith [ y1_bounds ] ) ( p 0 ), inv_mul_cancel₀ ( show ( 1 - y1 ) ≠ 0 by linarith [ y1_bounds ] ) ];
          · erw [ Pi.smul_apply ] ; norm_num ; ring_nf!;
            nlinarith! [ inv_mul_cancel_left₀ ( show ( 1 - y1 ) ≠ 0 by linarith [ y1_bounds.2 ] ) ( p 1 ), inv_mul_cancel_left₀ ( show ( 1 - y1 ) ≠ 0 by linarith [ y1_bounds.2 ] ) y1, y1_bounds.1, y1_bounds.2 ];
      rw [ convexHull_eq ];
      rcases h_comb with ⟨ a, b, c, ha, hb, hc, habc, rfl ⟩;
      refine' ⟨ Fin 3, { 0, 1, 2 }, fun i => if i = 0 then a else if i = 1 then b else c, fun i => if i = 0 then Y_point else if i = 1 then sigma Y_point else ![1, 1], _, _, _, _ ⟩ <;> simp +decide [ *, Fin.sum_univ_three, Finset.centerMass ];
      · linarith;
      · norm_num [ ← add_assoc, habc ]

/-
A point is in Region5 iff its reflection is in Region4.
-/
open Set

lemma mem_Region5_iff_sigma_mem_Region4 (p : Point) : p ∈ Region5 ↔ sigma p ∈ Region4 := by
  unfold Region4 Region5;
  norm_num [ convexHull_eq, sigma ];
  constructor <;> rintro ⟨ ι, t, w, hw₁, hw₂, x, hx₁, hx₂ ⟩;
  · refine' ⟨ ι, t, w, hw₁, hw₂, fun i => ![ ( x i ) 1, ( x i ) 0 ], _, _ ⟩ <;> simp_all +decide [ Finset.centerMass ];
    · intro i hi; specialize hx₁ i hi; aesop;
    · ext i ; fin_cases i <;> simp +decide [ ← hx₂, Finset.sum_apply, Algebra.smul_def ];
      · rw [ Finset.sum_apply, Finset.sum_apply ] ; aesop;
      · rw [ Finset.sum_apply, Finset.sum_apply ] ; aesop;
  · refine' ⟨ ι, t, w, hw₁, hw₂, fun i => ![x i 1, x i 0], _, _ ⟩ <;> simp_all +decide [ Finset.centerMass ];
    · intro i hi; specialize hx₁ i hi; aesop;
    · convert congr_arg ( fun q => ![q 1, q 0] ) hx₂ using 1;
      · ext i ; fin_cases i <;> simp +decide [ Finset.sum_apply, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, Finset.sum_add_distrib, add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.sum_smul ];
        · rw [ Finset.sum_apply, Finset.sum_apply ] ; aesop;
        · rw [ Finset.sum_apply, Finset.sum_apply ] ; aesop;
      · ext i; fin_cases i <;> rfl;

/-
A point is in Region3 iff its reflection is in Region2.
-/
open Set

lemma mem_Region3_iff_sigma_mem_Region2 (p : Point) : p ∈ Region3 ↔ sigma p ∈ Region2 := by
  -- By definition of sigma, we know that sigma(Region2) = Region3.
  have h_sigma_Region2 : sigma '' Region2 = Region3 := by
    apply Set.ext
    intro p
    simp [Region2, Region3];
    constructor <;> intro h;
    · obtain ⟨ x, hx, rfl ⟩ := h;
      rw [ convexHull_eq ] at hx ⊢;
      rcases hx with ⟨ ι, t, w, z, hw, hw', hz, rfl ⟩;
      refine' ⟨ ι, t, w, fun i => sigma ( z i ), hw, hw', _, _ ⟩ <;> simp_all +decide [ Finset.centerMass ];
      · intro i hi; specialize hz i hi; aesop;
      · ext i ; fin_cases i <;> simp +decide [ Finset.sum_apply, Finset.sum_smul, hw' ];
        · simp +decide [ sigma, Finset.sum_apply, Finset.sum_smul ];
          rw [ Finset.sum_apply, Finset.sum_apply ] ; aesop;
        · simp +decide [ sigma, Finset.sum_apply, Finset.sum_smul ];
          rw [ Finset.sum_apply, Finset.sum_apply ] ; aesop;
    · simp_all +decide [ segment_eq_image, convexHull_insert ];
      rcases h with ⟨ i, hi, x, hx, rfl ⟩ ; use i, hi, x, hx; ext j; fin_cases j <;> norm_num [ sigma ] ;
      · exact Or.inl rfl;
      · exact Or.inl rfl;
  rw [ ← h_sigma_Region2, mem_image ];
  constructor <;> intro h;
  · rcases h with ⟨ x, hx, rfl ⟩ ; exact sigma_sigma_eq_id x ▸ hx;
  · exact ⟨ _, h, by ext i; fin_cases i <;> rfl ⟩

/-
The collection S_finite is finite.
-/
lemma S_finite_finite : Set.Finite S_finite := by
  exact Set.toFinite { segment1, segment2, segment3, segment4, segment5 }

/-
The collection S_total is finite.
-/
lemma S_total_finite : Set.Finite S_total := by
  apply Set.Finite.union ?_ ?_;
  · exact S_finite_finite;
  · exact Set.toFinite { V_L, V_R, H_bot, H_top }

/-
S_total is a disjoint collection of unit segments.
-/
lemma S_total_is_disjoint_collection : IsDisjointCollection S_total := by
  -- Since S_finite and S_sides are disjoint and each consists of unit segments, their union S_total is also a disjoint collection of unit segments.
  apply And.intro;
  · intro s hs
    apply Or.elim hs;
    · exact fun a ↦ S_finite_consists_of_unit_segments s a;
    · rintro ( rfl | rfl | rfl | rfl ) <;> unfold IsUnitSegment;
      · unfold V_L; use ![0, 0], ![0, 1]; norm_num;
        norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
      · use ![1, 0], ![1, 1];
        unfold V_R; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ;
      · unfold H_bot; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ;
        exact ⟨ _, _, by norm_num, rfl ⟩;
      · exact ⟨ _, _, by norm_num [ EuclideanSpace.dist_eq ], rfl ⟩;
  · intro s t hs ht hst;
    cases' hs with hs hs <;> cases' ht with ht ht <;> simp_all +decide [ S_finite, S_sides ];
    · rcases hs with ( rfl | rfl | rfl | rfl | rfl ) <;> rcases ht with ( rfl | rfl | rfl | rfl | rfl ) <;> norm_num [ disjoint_1_2, disjoint_1_3, disjoint_1_4, disjoint_1_5, disjoint_2_3, disjoint_2_4, disjoint_2_5, disjoint_3_4, disjoint_3_5, disjoint_4_5 ];
      exact False.elim (hst rfl);
      exact Disjoint.symm disjoint_1_2;
      grind;
      exact Disjoint.symm disjoint_1_3;
      exact Disjoint.symm disjoint_2_3;
      exact False.elim (hst rfl);
      exact Disjoint.symm disjoint_1_4;
      exact Disjoint.symm disjoint_2_4;
      exact Disjoint.symm disjoint_3_4;
      exact False.elim (hst rfl);
      · exact Disjoint.symm disjoint_1_5;
      · exact Disjoint.symm disjoint_2_5;
      · exact Disjoint.symm disjoint_3_5;
      · exact Disjoint.symm disjoint_4_5;
      · grind;
    · rcases hs with ( rfl | rfl | rfl | rfl | rfl ) <;> rcases ht with ( rfl | rfl | rfl | rfl ) <;> norm_num [ segment1, segment2, segment3, segment4, segment5, V_L, V_R, H_bot, H_top ];
      all_goals norm_num [ openSegment_eq_image, segment1, segment2, segment3, segment4, segment5, V_L, V_R, H_bot, H_top, O_point, sigma ] at *;
      all_goals rw [ Set.disjoint_left ] ; norm_num [ Set.mem_image ];
      all_goals intro a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃; rw [ ← List.ofFn_inj ] at *; norm_num at *;
      all_goals norm_num [ X_point, Y_point, V_point ] at *;
      any_goals nlinarith [ show 0 < y1 by exact y1_bounds.1, show y1 < 1 by exact y1_bounds.2, show 0 < x1 by exact lt_trans ( by norm_num ) ( x1_prop.1 ), show x1 < 1 by exact lt_of_lt_of_le ( x1_prop.2.1 ) ( by norm_num ) ];
      all_goals nlinarith [ show Real.sqrt 6 > 2 by norm_num [ Real.lt_sqrt ], show Real.sqrt 2 > 1 by norm_num [ Real.lt_sqrt ], Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ];
    · -- By definition of $V_L$, $V_R$, $H_bot$, and $H_top$, they are all boundary segments of the unit square.
      have h_boundary_segments : ∀ s ∈ ({V_L, V_R, H_bot, H_top} : Set (Set Point)), ∀ t ∈ ({segment1, segment2, segment3, segment4, segment5} : Set (Set Point)), Disjoint s t := by
        intro s hs t ht
        have h_disjoint : s ⊆ SquareBoundary ∧ t ⊆ Region_Square := by
          -- Since $s$ is a boundary segment, it is contained within the boundary of the unit square.
          have h_boundary_s : s ⊆ SquareBoundary := by
            rcases hs with ( rfl | rfl | rfl | rfl ) <;> intro p hp <;> unfold SquareBoundary <;> simp_all +decide [ Set.subset_def ];
            · rcases hp with ⟨ a, b, ha, hb, hab, rfl ⟩ ; norm_num [ UnitSquare ] at *;
              exact Or.inl ⟨ by linarith, by linarith ⟩;
            · rcases hp with ⟨ a, b, ha, hb, hab, rfl ⟩ ; norm_num [ UnitSquare ];
              exact Or.inr <| Or.inl ⟨ ⟨ ⟨ by linarith, by linarith ⟩, ⟨ by linarith, by linarith ⟩ ⟩, hab ⟩;
            · rcases hp with ⟨ a, b, ha, hb, hab, rfl ⟩ ; norm_num [ UnitSquare ];
              exact Or.inr <| Or.inr ⟨ by linarith, by linarith ⟩;
            · rcases hp with ⟨ a, b, ha, hb, hab, rfl ⟩ ; norm_num [ UnitSquare ];
              exact Or.inr <| Or.inr <| Or.inr ⟨ ⟨ ⟨ by linarith, by linarith ⟩, by linarith, by linarith ⟩, by linarith ⟩;
          exact ⟨ h_boundary_s, by rcases ht with ( rfl | rfl | rfl | rfl | rfl ) <;> [ exact segment_from_corner_in_square _ ( V_in_Region_Square ) ; exact segment_from_corner_in_square _ ( sigma_V_in_Region_Square ) ; exact segment_inside_square _ _ ( V_in_Region_Square ) ( sigma_V_in_Region_Square ) ; exact segment4_in_square; exact segment5_in_square ] ⟩
        refine' Set.disjoint_left.mpr fun x hx hx' => _;
        have := h_disjoint.1 hx; have := h_disjoint.2 hx'; simp_all +decide [ SquareBoundary, Region_Square ] ;
        rcases ‹x ∈ UnitSquare ∧ x 0 = 0 ∨ x ∈ UnitSquare ∧ x 0 = 1 ∨ x ∈ UnitSquare ∧ x 1 = 0 ∨ x ∈ UnitSquare ∧ x 1 = 1› with ( ⟨ hx₁, hx₂ ⟩ | ⟨ hx₁, hx₂ ⟩ | ⟨ hx₁, hx₂ ⟩ | ⟨ hx₁, hx₂ ⟩ ) <;> linarith;
      grind;
    · rcases hs with ( rfl | rfl | rfl | rfl ) <;> rcases ht with ( rfl | rfl | rfl | rfl ) <;> norm_num [ V_L, V_R, H_bot, H_top, openSegment_eq_image ];
      all_goals norm_num [ Set.disjoint_left ] at *;
      all_goals rintro a x hx₁ hx₂ rfl y hy₁ hy₂; intro H; have := congr_fun H 0; have := congr_fun H 1; norm_num [ hx₁.ne', hx₂.ne', hy₁.ne', hy₂.ne' ] at *;
      · linarith;
      · linarith

/-
S_total is contained in the closed unit square.
-/
lemma S_total_in_UnitSquare : IsInRegion S_total UnitSquare := by
  intro s hs;
  cases' hs with hs hs;
  · -- Since $S_finite$ is a subset of the open unit square, every element of $S_finite$ is contained in the open unit square.
    have h_open_unit_square : ∀ s ∈ S_finite, s ⊆ Region_Square := by
      apply S_finite_in_region;
    exact Set.Subset.trans ( h_open_unit_square s hs ) ( fun x hx => by exact fun i => ⟨ hx.1 |> fun h => by fin_cases i <;> linarith! [ hx.2 ], hx.2 |> fun h => by fin_cases i <;> linarith! [ hx.1 ] ⟩ );
  · -- Each of the segments V_L, V_R, H_bot, and H_top is a subset of the unit square.
    have h_segments : V_L ⊆ UnitSquare ∧ V_R ⊆ UnitSquare ∧ H_bot ⊆ UnitSquare ∧ H_top ⊆ UnitSquare := by
      unfold V_L V_R H_bot H_top UnitSquare;
      norm_num [ Set.subset_def, openSegment_eq_image ];
      exact ⟨ by rintro x a ha₁ ha₂ rfl; exact ⟨ ⟨ by norm_num [ ha₁.le ], by norm_num [ ha₂.le ] ⟩, ⟨ by norm_num [ ha₁.le ], by norm_num [ ha₂.le ] ⟩ ⟩, by rintro x a ha₁ ha₂ rfl; exact ⟨ ⟨ by norm_num [ ha₁.le ], by norm_num [ ha₂.le ] ⟩, ⟨ by norm_num [ ha₁.le ], by norm_num [ ha₂.le ] ⟩ ⟩, by rintro x a ha₁ ha₂ rfl; exact ⟨ ⟨ by norm_num [ ha₁.le ], by norm_num [ ha₂.le ] ⟩, ⟨ by norm_num [ ha₁.le ], by norm_num [ ha₂.le ] ⟩ ⟩, by rintro x a ha₁ ha₂ rfl; exact ⟨ ⟨ by norm_num [ ha₁.le ], by norm_num [ ha₂.le ] ⟩, ⟨ by norm_num [ ha₁.le ], by norm_num [ ha₂.le ] ⟩ ⟩ ⟩;
    unfold S_sides at hs; aesop;

/-
The diameter of Region6_Total is at most 1.
-/
lemma Region6_Total_diameter_le_1 : ∀ x y : Point, x ∈ Region6_Total → y ∈ Region6_Total → dist x y ≤ 1 := by
  have h_convex_comb : ∀ x y : Point, x ∈ convexHull ℝ {V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} → y ∈ convexHull ℝ {V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} → dist x y ≤ max (max (max (max (dist V_point (sigma V_point)) (dist V_point Y_point)) (dist V_point (sigma Y_point))) (dist V_point ![1, 1])) (max (max (max (dist (sigma V_point) Y_point) (dist (sigma V_point) (sigma Y_point))) (dist (sigma V_point) ![1, 1])) (max (max (dist Y_point (sigma Y_point)) (dist Y_point ![1, 1])) (dist (sigma Y_point) ![1, 1]))) := by
    intros x y hx hy
    have h_convex_comb : ∃ a : Fin 5 → ℝ, (∀ i, 0 ≤ a i) ∧ (∑ i, a i = 1) ∧ x = ∑ i, a i • ![V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]] i := by
      simp_all +decide [ convexHull_insert ];
      rcases hx with ⟨ i, hi, j, hj, k, hk, hx ⟩;
      rcases hx with ⟨ a, b, ha, hb, hab, rfl ⟩ ; rcases hk with ⟨ c, d, hc, hd, hcd, rfl ⟩ ; rcases hj with ⟨ e, f, he, hf, hef, rfl ⟩ ; rcases hi with ⟨ g, h, hg, hh, hgh, rfl ⟩ ; norm_num [ Fin.sum_univ_succ ] at *;
      refine' ⟨ fun i => if i = 0 then a else if i = 1 then b * c else if i = 2 then b * d * e else if i = 3 then b * d * f * g else b * d * f * h, _, _, _ ⟩ <;> simp +decide [ Fin.forall_fin_succ, * ] ; ring_nf;
      · exact ⟨ mul_nonneg hb hc, mul_nonneg ( mul_nonneg hb hd ) he, mul_nonneg ( mul_nonneg ( mul_nonneg hb hd ) hf ) hg, mul_nonneg ( mul_nonneg ( mul_nonneg hb hd ) hf ) hh ⟩;
      · grind +ring;
      · ext i ; fin_cases i <;> norm_num [ Matrix.vecHead, Matrix.vecTail ] <;> ring!;
    have h_convex_comb_y : ∃ b : Fin 5 → ℝ, (∀ i, 0 ≤ b i) ∧ (∑ i, b i = 1) ∧ y = ∑ i, b i • ![V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]] i := by
      rw [ @convexHull_eq ] at hy;
      rcases hy with ⟨ ι, t, w, z, hw, hw', hz, rfl ⟩;
      -- By definition of $z$, we know that $z i$ is one of the vertices $V_point$, $sigma V_point$, $Y_point$, $sigma Y_point$, or $![1, 1]$.
      have hz_vertices : ∀ i ∈ t, ∃ j : Fin 5, z i = ![V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]] j := by
        intro i hi; specialize hz i hi; rcases hz with ( h | h | h | h | h ) <;> [ exact ⟨ 0, h ⟩ ; exact ⟨ 1, h ⟩ ; exact ⟨ 2, h ⟩ ; exact ⟨ 3, h ⟩ ; exact ⟨ 4, h ⟩ ] ;
      choose! j hj using hz_vertices;
      refine' ⟨ fun i => ∑ j ∈ t.filter ( fun k => j k = i ), w j, _, _, _ ⟩ <;> simp_all +decide [ Finset.centerMass ];
      · exact fun i => Finset.sum_nonneg fun j hj => hw j <| Finset.mem_filter.mp hj |>.1;
      · rw [ ← hw', Finset.sum_fiberwise ];
      · simp +decide [ Finset.sum_filter, Finset.sum_smul ];
        rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
    -- Apply the lemma dist_convex_combination_le with the given conditions.
    obtain ⟨a, ha_nonneg, ha_sum, hx⟩ := h_convex_comb
    obtain ⟨b, hb_nonneg, hb_sum, hy⟩ := h_convex_comb_y
    have h_dist_le : dist x y ≤ ∑ i, ∑ j, a i * b j * dist (![V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]] i) (![V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]] j) := by
      rw [ hx, hy ];
      convert dist_convex_combination_le ( fun i _ => ha_nonneg i ) ( fun i _ => hb_nonneg i ) ha_sum hb_sum using 1;
    refine le_trans h_dist_le ?_;
    have h_dist_le : ∀ i j, dist (![V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]] i) (![V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]] j) ≤ max (max (max (max (dist V_point (sigma V_point)) (dist V_point Y_point)) (dist V_point (sigma Y_point))) (dist V_point ![1, 1])) (max (max (max (dist (sigma V_point) Y_point) (dist (sigma V_point) (sigma Y_point))) (dist (sigma V_point) ![1, 1])) (max (max (dist Y_point (sigma Y_point)) (dist Y_point ![1, 1])) (dist (sigma Y_point) ![1, 1]))) := by
      simp +decide [ Fin.forall_fin_succ ];
      simp +decide [ dist_comm ];
    refine' le_trans ( Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ( h_dist_le i j ) ( mul_nonneg ( ha_nonneg i ) ( hb_nonneg j ) ) ) _;
    simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, ha_sum, hb_sum ];
  -- By calculating the distances between each pair of points, we can verify that they are all less than or equal to 1.
  have h_dist_V_sigma_V : dist V_point (sigma V_point) = 1 := by
    exact dist_V_sigma_V
  have h_dist_V_Y : dist V_point Y_point < 1 := by
    exact dist_V_Y_lt_1
  have h_dist_V_sigma_Y : dist V_point (sigma Y_point) < 1 := by
    exact dist_V_sigma_Y_lt_1
  have h_dist_V_Corner : dist V_point ![1, 1] < 1 := by
    convert dist_V_Corner_lt_1 using 1
  have h_dist_sigma_V_Y : dist (sigma V_point) Y_point < 1 := by
    exact dist_sigma_V_Y_lt_1
  have h_dist_sigma_V_sigma_Y : dist (sigma V_point) (sigma Y_point) < 1 := by
    convert Region6b_diameter_lt_1 _ _ _ _ using 1;
    · exact subset_convexHull ℝ _ ( by norm_num );
    · exact subset_convexHull ℝ _ <| by norm_num;
  have h_dist_sigma_V_Corner : dist (sigma V_point) ![1, 1] < 1 := by
    convert dist_sigma_V_Corner_lt_1 using 1
  have h_dist_Y_sigma_Y : dist Y_point (sigma Y_point) < 1 := by
    exact dist_Y_sigma_Y_lt_1
  have h_dist_Y_Corner : dist Y_point ![1, 1] < 1 := by
    convert dist_Y_Corner_lt_1 using 1
  have h_dist_sigma_Y_Corner : dist (sigma Y_point) ![1, 1] < 1 := by
    convert h_dist_Y_Corner using 1;
    convert sigma_isometry Y_point ![1, 1] using 1;
  exact fun x y hx hy => le_trans ( h_convex_comb x y hx hy ) ( by exact max_le ( max_le ( max_le ( max_le ( by linarith ) ( by linarith ) ) ( by linarith ) ) ( by linarith ) ) ( max_le ( max_le ( max_le ( by linarith ) ( by linarith ) ) ( by linarith ) ) ( max_le ( max_le ( by linarith ) ( by linarith ) ) ( by linarith ) ) ) )

/-
S_finite blocks Region6_Total.
-/
lemma Region6_Total_blocking : IsBlocking S_finite Region6_Total := by
  -- If L is a unit segment in Region6_Total, then L must be segment3.
  have h_segment3 : ∀ L : Set Point, IsUnitSegment L → L ⊆ Region6_Total → L = openSegment ℝ V_point (sigma V_point) := by
    intros L hL_unit hL_subset
    obtain ⟨x, y, hxy⟩ := hL_unit
    have hxy_dist : dist x y = 1 := by
      exact hxy.1
    have hxy_segment : x ∈ Region6_Total ∧ y ∈ Region6_Total := by
      have hL_subset_closed : IsClosed Region6_Total := by
        -- The convex hull of a finite set of points in Euclidean space is closed.
        have h_convex_hull_closed : ∀ (s : Finset Point), IsClosed (convexHull ℝ (s : Set Point)) := by
          intro s
          have h_convex_hull_closed : IsCompact (convexHull ℝ (s : Set Point)) := by
            exact s.finite_toSet.isCompact_convexHull
          generalize_proofs at *;
          exact h_convex_hull_closed.isClosed;
        convert h_convex_hull_closed { V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1] } using 1;
        unfold Region6_Total; aesop;
      have hxy_segment : openSegment ℝ x y ⊆ Region6_Total := by
        aesop
      have hxy_endpoints : x ∈ Region6_Total ∧ y ∈ Region6_Total := by
        apply endpoints_in_closed_region hL_subset_closed hxy_segment (by
        exact ⟨ ( 1 / 2 : ℝ ) • x + ( 1 / 2 : ℝ ) • y, by exact ⟨ 1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num ⟩ ⟩)
      exact hxy_endpoints
      skip
    have hxy_segment3 : x = V_point ∧ y = sigma V_point ∨ x = sigma V_point ∧ y = V_point := by
      have hxy_segment3 : ∀ x y : Point, x ∈ Region6_Total → y ∈ Region6_Total → dist x y = 1 → x = V_point ∧ y = sigma V_point ∨ x = sigma V_point ∧ y = V_point := by
        intros x y hx hy hxy_dist
        have hxy_segment3 : ∀ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), ∀ j ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), dist i j = 1 → i = V_point ∧ j = sigma V_point ∨ i = sigma V_point ∧ j = V_point := by
          simp +zetaDelta at *;
          refine' ⟨ _, _, _, _, _ ⟩;
          · exact ⟨ fun h => False.elim <| absurd h <| ne_of_lt <| dist_V_Y_lt_1, fun h => False.elim <| absurd h <| ne_of_lt <| dist_V_sigma_Y_lt_1, fun h => False.elim <| absurd h <| ne_of_lt <| dist_V_Corner_lt_1 ⟩;
          · refine' ⟨ _, _, _ ⟩;
            · intro h_dist
              have hxy_segment3 : dist (sigma V_point) Y_point < 1 := by
                exact dist_sigma_V_Y_lt_1
              exact absurd hxy_dist (by linarith [hxy_segment3]);
            · intro h_dist
              have hxy_segment3 : dist V_point Y_point = 1 := by
                rw [ ← h_dist, sigma_isometry ];
              exact absurd hxy_segment3 ( by exact ne_of_lt ( by exact dist_V_Y_lt_1 ) );
            · norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
              unfold sigma V_point; norm_num [ Fin.sum_univ_succ ] ; ring_nf ;
              exact fun h => absurd h ( by nlinarith only [ Real.sqrt_nonneg 6, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sqrt_nonneg 2, Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ] );
          · refine' ⟨ _, _, _, _ ⟩;
            · intro h;
              exact absurd h ( by rw [ dist_comm ] ; exact ne_of_lt ( dist_V_Y_lt_1 ) );
            · intro h;
              exact absurd h ( by rw [ dist_comm ] ; exact ne_of_lt ( dist_sigma_V_Y_lt_1 ) );
            · intro h_dist
              have hxy_segment3 : dist Y_point (sigma Y_point) < 1 := by
                exact dist_Y_sigma_Y_lt_1
              exact absurd hxy_dist (by linarith [hxy_segment3]);
            · intro h; have := dist_Y_Corner_lt_1; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
              rw [ Real.sqrt_lt' ] at this <;> norm_num [ Corner_point ] at * ; nlinarith [ this, h ];
          · refine' ⟨ _, _, _, _ ⟩;
            · intro hxy_dist
              have hxy_segment3 : dist (sigma Y_point) V_point < 1 := by
                convert dist_V_sigma_Y_lt_1 using 1;
                exact dist_comm _ _
              exact absurd hxy_dist (by linarith);
            · have := dist_sigma_V_Y_lt_1; ( have := dist_sigma_V_Corner_lt_1; ( have := dist_Y_Corner_lt_1; ( have := dist_V_Corner_lt_1; ( have := dist_V_Y_lt_1; ( have := dist_O_V; ( have := dist_O_sigma_V; ( have := dist_O_X_lt_1; ( have := dist_V_X_lt_1; ( have := dist_X_A0_lt_1; ( have := dist_A0_Y_lt_1; ( have := dist_sigma_X_sigma_Y; ( have := dist_sigma_V_sigma_X_lt_1; ( have := dist_sigma_A0_sigma_Y_lt_1; ( norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *; ) ) ) ) ) ) ) ) ) ) ) ) ) );
              norm_num [ Real.sqrt_lt', sigma, V_point, Y_point ] at *;
              grind;
            · intro hxy_dist
              have hxy_segment3 : dist Y_point (sigma Y_point) < 1 := by
                exact dist_Y_sigma_Y_lt_1
              exact absurd hxy_dist (by
              exact ne_of_lt ( by rwa [ dist_comm ] ));
            · intro h; have := dist_Y_Corner_lt_1; simp_all +decide [ dist_comm ] ;
              unfold Corner_point at this; simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ] ;
              rw [ Real.sqrt_lt' ] at this <;> norm_num [ sigma ] at *;
              linarith;
          · norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
            unfold V_point sigma Y_point; norm_num [ Fin.ext_iff ] ; ring_nf ;
            norm_num [ ← List.ofFn_inj ] ; ring_nf ; norm_num;
            exact ⟨ fun h => absurd h ( by nlinarith only [ Real.sq_sqrt ( show 6 ≥ 0 by norm_num ) ] ), fun h => absurd h ( by nlinarith only [ Real.sq_sqrt ( show 6 ≥ 0 by norm_num ) ] ), fun h => absurd h ( by rintro ( h | h ) <;> nlinarith only [ Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, y1_bounds, h ] ), fun h => absurd h ( by rintro ( h | h ) <;> nlinarith only [ Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, y1_bounds, h ] ) ⟩;
        have hxy_comb : ∃ (a : Point → ℝ) (b : Point → ℝ), (∀ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), 0 ≤ a i) ∧ (∀ j ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), 0 ≤ b j) ∧ (∑ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), a i = 1) ∧ (∑ j ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), b j = 1) ∧ x = ∑ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), a i • i ∧ y = ∑ j ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), b j • j := by
          have hxy_comb : ∀ x : Point, x ∈ convexHull ℝ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Set Point) → ∃ (a : Point → ℝ), (∀ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), 0 ≤ a i) ∧ (∑ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), a i = 1) ∧ x = ∑ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), a i • i := by
            intro x hx;
            rw [ convexHull_eq ] at hx;
            obtain ⟨ ι, t, w, z, hw, hw', hz, rfl ⟩ := hx;
            refine' ⟨ fun i => ∑ j ∈ t.filter ( fun j => z j = i ), w j, _, _, _ ⟩;
            · exact fun i hi => Finset.sum_nonneg fun j hj => hw j <| Finset.mem_filter.mp hj |>.1;
            · rw [ ← hw', Finset.sum_fiberwise_of_maps_to ];
              aesop;
            · simp +decide [ Finset.centerMass, hw' ];
              simp +decide [ Finset.sum_filter, Finset.sum_smul ];
              rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
          exact Exists.elim ( hxy_comb x hx ) fun a ha => Exists.elim ( hxy_comb y hy ) fun b hb => ⟨ a, b, ha.1, hb.1, ha.2.1, hb.2.1, ha.2.2, hb.2.2 ⟩;
        obtain ⟨ a, b, ha, hb, ha_sum, hb_sum, rfl, rfl ⟩ := hxy_comb;
        have hxy_comb : ∀ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), ∀ j ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), a i > 0 → b j > 0 → dist i j = 1 := by
          apply convex_combination_dist_eq_one_implies_support_dist_eq_one;
          all_goals try assumption;
          intros i hi j hj;
          have hxy_comb : ∀ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), ∀ j ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), dist i j ≤ 1 := by
            intros i hi j hj;
            have hxy_comb : ∀ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), ∀ j ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), dist i j ≤ 1 := by
              intro i hi j hj
              have hxy_comb : i ∈ Region6_Total ∧ j ∈ Region6_Total := by
                exact ⟨ subset_convexHull ℝ _ <| by simpa using hi, subset_convexHull ℝ _ <| by simpa using hj ⟩
              exact Region6_Total_diameter_le_1 i j hxy_comb.1 hxy_comb.2;
            exact hxy_comb i hi j hj;
          exact hxy_comb i hi j hj;
        have hxy_comb : ∀ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), ∀ j ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), a i > 0 → b j > 0 → ({i, j} : Set Point) = {V_point, sigma V_point} := by
          grind;
        have hxy_comb : ({∑ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), a i • i, ∑ j ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, ![1, 1]} : Finset Point), b j • j} : Set Point) = {V_point, sigma V_point} := by
          apply support_implies_endpoints;
          any_goals tauto;
          exact ne_of_apply_ne ( fun p => p 0 ) ( by norm_num [ V_point, sigma ] ; nlinarith [ Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), Real.sqrt_nonneg 6, Real.sqrt_nonneg 2 ] );
        exact pair_eq_pair_iff.mp hxy_comb;
      exact hxy_segment3 x y hxy_segment.1 hxy_segment.2 hxy_dist
    have hL_segment3 : L = openSegment ℝ V_point (sigma V_point) := by
      cases hxy_segment3 <;> simp_all +decide [ openSegment_symm ]
    exact hL_segment3;
  -- By h_segment3, any unit segment L in Region6_Total must be segment3.
  have h_L_is_segment3 : ∀ L : Set Point, IsUnitSegment L → L ⊆ Region6_Total → L = openSegment ℝ V_point (sigma V_point) := by
    assumption;
  -- By h_L_is_segment3, any unit segment L in Region6_Total must be segment3. Since segment3 is in S_finite, L must intersect with segment3.
  intros L hL hL_subset
  have hL_segment3 : L = openSegment ℝ V_point (sigma V_point) := h_L_is_segment3 L hL hL_subset
  exact ⟨openSegment ℝ V_point (sigma V_point), by
    exact Or.inr <| Or.inr <| Or.inl rfl, by
    rw [ hL_segment3, Set.not_disjoint_iff ] ; norm_num [ openSegment ];
    exact ⟨ _, 1 / 2, by norm_num, 1 / 2, by norm_num, by norm_num, rfl ⟩⟩

/-
Define the separator function sep.
-/
noncomputable def sep (p : Point) : ℝ := (1 - V_point 1) * (p 1 - V_point 0) - (y1 - V_point 0) * (p 0 - V_point 1)

/-
Define linear forms L1 and L2.
-/
noncomputable def L1 (p : Point) : ℝ := p 0 + p 1 - (V_point 0 + V_point 1)

noncomputable def L2 (p : Point) : ℝ := y1 * (p 0 - x1) - p 1 * (1 - x1)

/-
L1 is 0 at V and sigma V, and non-negative at Y.
-/
lemma L1_V : L1 V_point = 0 := by
  unfold L1; ring;

lemma L1_sigma_V : L1 (sigma V_point) = 0 := by
  unfold L1 sigma; norm_num;
  ring

lemma L1_Y_ge_0 : L1 Y_point ≥ 0 := by
  -- By definition of $y1$, we know that $y1 \geq V_point 0 + V_point 1 - 1$.
  have hy1_ge : y1 ≥ V_point 0 + V_point 1 - 1 := by
    unfold y1 V_point;
    simp +zetaDelta at *;
    rw [ div_add_one, le_div_iff₀ ];
    · have := x1_prop.2.1;
      nlinarith [ show Real.sqrt 6 > 2 by norm_num [ Real.lt_sqrt ], show Real.sqrt 2 > 1 by norm_num [ Real.lt_sqrt ], Real.mul_self_sqrt ( show 6 ≥ 0 by norm_num ), Real.mul_self_sqrt ( show 2 ≥ 0 by norm_num ), pow_two_nonneg ( Real.sqrt 6 - Real.sqrt 2 ), pow_two_nonneg ( Real.sqrt 6 - 2 ), pow_two_nonneg ( Real.sqrt 2 - 1 ) ];
    · have := x1_prop.2.1 ; norm_num at * ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
    · have := x1_prop.2.1 ; norm_num at * ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
  unfold L1; norm_num [ Y_point ] ; linarith;

/-
L2 is 0 at V and Y, and non-positive at sigma V.
-/
lemma L2_V : L2 V_point = 0 := by
  unfold L2;
  rw [ show y1 = V_point 1 * ( 1 - x1 ) / ( V_point 0 - x1 ) from rfl ];
  rw [ div_mul_cancel₀ _ ] <;> norm_num;
  nlinarith [ V_bounds, x1_prop ]

lemma L2_Y : L2 Y_point = 0 := by
  unfold L2 Y_point;
  -- Simplify the expression for L2 at Y.
  simp [y1]

lemma L2_sigma_V_le_0 : L2 (sigma V_point) ≤ 0 := by
  unfold L2 y1;
  erw [ div_mul_eq_mul_div, sub_le_iff_le_add ];
  rw [ div_le_iff₀ ] <;> norm_num [ V_point ] at *;
  · unfold sigma; norm_num; ring_nf; norm_num;
    have := x1_prop.1.le ; have := x1_prop.2.1.le ; norm_num at * ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_le_mul_of_nonneg_left this ( Real.sqrt_nonneg 6 ), mul_le_mul_of_nonneg_left this ( Real.sqrt_nonneg 2 ) ];
  · have := x1_prop;
    exact this.2.1.trans_le <| by nlinarith only [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt <| show 0 ≤ 6 by norm_num, Real.sq_sqrt <| show 0 ≤ 2 by norm_num, mul_pos ( Real.sqrt_pos.mpr <| show 0 < 6 by norm_num ) ( Real.sqrt_pos.mpr <| show 0 < 2 by norm_num ) ] ;

/-
The linear forms are strictly non-zero at the respective vertices.
-/
lemma L1_Y_pos : L1 Y_point > 0 := by
  -- Since $L1 Y_point$ is not zero and greater than or equal to zero, it must be strictly positive.
  apply lt_of_le_of_ne; exact L1_Y_ge_0; exact fun h => by
    unfold L1 at h; norm_num [ y1, V_point ] at h; ring_nf at h; norm_num at h;
    unfold Y_point at h ; norm_num at h;
    unfold y1 at h;
    unfold V_point at h ; norm_num at h;
    rw [ eq_comm, add_div', div_add', div_eq_iff ] at h <;> ring_nf at * <;> norm_num at *;
    · have := x1_prop.2.1;
      nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr this ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr this ) ];
    · have := x1_prop.1 ; have := x1_prop.2.1 ; norm_num at * ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
    · intro H; rw [ H ] at h; norm_num at h;
    · grind

lemma L2_sigma_V_neg : L2 (sigma V_point) < 0 := by
  unfold L2;
  unfold y1 sigma V_point;
  field_simp;
  refine' mul_neg_of_pos_of_neg _ _;
  · linarith [ x1_prop.2.1 ];
  · rw [ sub_neg, div_lt_iff₀ ] <;> ring_nf <;> norm_num;
    · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), x1_prop ];
    · have := x1_prop.2.1 ; norm_num at * ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ]

lemma sep_V_neg : sep V_point < 0 := by
  unfold sep; norm_num [ V_point_0_val ] ; ring_nf ; norm_num;
  rw [ show V_point = ![(Real.sqrt 6 + Real.sqrt 2) / 4, (Real.sqrt 6 - Real.sqrt 2) / 4] by rfl ] ; norm_num ; ring_nf ; norm_num;
  rw [ show y1 = ( V_point 1 ) * ( 1 - x1 ) / ( V_point 0 - x1 ) by rfl ] ; norm_num [ V_point ] ; ring_nf ; norm_num;
  have h_x1_bounds : 0.95 < x1 ∧ x1 < 0.96 := by
    exact ⟨ x1_prop.1, x1_prop.2.1 ⟩;
  have h_sqrt_bounds : Real.sqrt 6 > 2.449 ∧ Real.sqrt 6 < 2.45 ∧ Real.sqrt 2 > 1.414 ∧ Real.sqrt 2 < 1.415 := by
    norm_num [ Real.lt_sqrt, Real.sqrt_lt ];
  field_simp at *;
  rw [ add_div', div_lt_div_iff_of_pos_right ] <;> nlinarith [ mul_pos ( sub_pos.mpr h_sqrt_bounds.1 ) ( sub_pos.mpr h_sqrt_bounds.2.2.1 ), Real.mul_self_sqrt ( show 6 ≥ 0 by norm_num ), Real.mul_self_sqrt ( show 2 ≥ 0 by norm_num ) ]

/-
Define linear forms L3 and L4.
-/
noncomputable def L3 (p : Point) : ℝ := y1 * (p 1 - x1) - p 0 * (1 - x1)

noncomputable def L4 (p : Point) : ℝ := p 0 + p 1 - (1 + y1)

/-
L3 is 0 at sigma V and sigma Y, and negative at Y.
-/
lemma L3_sigma_V : L3 (sigma V_point) = 0 := by
  convert L2_V using 1

lemma L3_sigma_Y : L3 (sigma Y_point) = 0 := by
  unfold L3 sigma Y_point;
  simp +zetaDelta at *;

lemma L3_Y_neg : L3 Y_point < 0 := by
  -- Substitute the value of L3 Y and use the fact that y1 < 1 to conclude it's negative.
  have h_L3_Y_val : L3 Y_point = y1 * (y1 - x1) - 1 * (1 - x1) := by
    unfold L3 Y_point; norm_num;
  nlinarith [ y1_bounds, x1_prop.1, x1_prop.2.1 ]

/-
L4 is 0 at Y and sigma Y, and negative at sigma V.
-/
lemma L4_Y : L4 Y_point = 0 := by
  unfold L4 Y_point; norm_num;

lemma L4_sigma_Y : L4 (sigma Y_point) = 0 := by
  unfold L4 sigma Y_point;
  ring_nf!;
  erw [ Matrix.cons_val_succ' ] ; norm_num

lemma L4_sigma_V_neg : L4 (sigma V_point) < 0 := by
  convert neg_lt_zero.mpr L1_Y_pos using 1 ; ring_nf!;
  unfold L4 L1; norm_num [ sigma ] ; ring_nf;
  unfold Y_point; norm_num; ring;

/-
sep is 0 at sigma V and Y.
-/
lemma sep_sigma_V : sep (sigma V_point) = 0 := by
  unfold sep;
  unfold y1; ring_nf;
  unfold sigma; norm_num; ring;

lemma sep_Y : sep Y_point = 0 := by
  unfold sep Y_point;
  simp +zetaDelta at *;
  ring

/-
If a point in the square satisfies L2 >= 0, it is in Region4.
-/
lemma Region4_contains_L2_ge_0 : ∀ p ∈ Region_Square, L2 p ≥ 0 → p ∈ Region4 := by
  intro p hp hL2op;
  apply in_Region4_of_coords p hp;
  · unfold L2 at hL2op;
    -- Since $y1 > 0$ and $1 - x1 > 0$, we can divide both sides of the inequality by $y1$ to get $p 0 - x1 \geq \frac{p 1 (1 - x1)}{y1}$.
    have h_div : p 0 - x1 ≥ p 1 * (1 - x1) / y1 := by
      rw [ ge_iff_le, div_le_iff₀ ] <;> linarith [ y1_bounds.1 ];
    linarith [ show 0 ≤ p 1 * ( 1 - x1 ) / y1 by exact div_nonneg ( mul_nonneg ( le_of_lt ( hp.2.2.1 ) ) ( sub_nonneg.2 ( by linarith [ show x1 < 1 by linarith [ show x1 < 0.96 by linarith [ x1_prop ] ] ] ) ) ) ( le_of_lt ( by linarith [ y1_bounds ] ) ) ];
  · unfold L2 at hL2op;
    -- Since $p$ is in the square, we know that $p_0 < 1$.
    have h_p0_lt_1 : p 0 < 1 := by
      exact hp.2.1;
    nlinarith [ show x1 > 0.95 by exact Classical.choose_spec exists_root_x1 |>.1, show x1 < 0.96 by exact Classical.choose_spec exists_root_x1 |>.2.1, show y1 > 0 by exact y1_bounds.1, show y1 < 1 by exact y1_bounds.2 ];
  · exact sub_nonneg.mp hL2op

/-
If a point in the square satisfies L3 >= 0, it is in Region5.
-/
lemma Region5_contains_L3_ge_0 : ∀ p ∈ Region_Square, L3 p ≥ 0 → p ∈ Region5 := by
  intros p hp hL3
  have hq : sigma p ∈ Region4 := by
    apply Region4_contains_L2_ge_0;
    · exact ⟨ hp.2.2.1, hp.2.2.2, hp.1, hp.2.1 ⟩;
    · exact hL3
  exact mem_Region5_iff_sigma_mem_Region4 p |>.2 hq

/-
If a point in the square satisfies L4 >= 0, it is in Region_Corner.
-/
lemma Region_Corner_contains_L4_ge_0 : ∀ p ∈ Region_Square, L4 p ≥ 0 → p ∈ Region_Corner := by
  intro p hp hL4
  apply in_Region_Corner_of_coords p hp (by
  unfold L4 at hL4; linarith!;)

/-
Define lambda_V, lambda_sigma_V, lambda_Y.
-/
noncomputable def lambda_V (p : Point) : ℝ := sep p / sep V_point

noncomputable def lambda_sigma_V (p : Point) : ℝ := L2 p / L2 (sigma V_point)

noncomputable def lambda_Y (p : Point) : ℝ := L1 p / L1 Y_point

/-
y1 * (V_point 0 - x1) = V_point 1 * (1 - x1).
-/
lemma y1_relation : y1 * (V_point 0 - x1) = V_point 1 * (1 - x1) := by
  unfold y1;
  rw [ div_mul_cancel₀ ];
  -- Since $V_point 0 > 0.96$ and $x1 < 0.96$, we have $V_point 0 - x1 > 0$.
  have h_pos : V_point 0 > 0.96 ∧ x1 < 0.96 := by
    exact ⟨ by have := V_bounds; norm_num at *; linarith, by have := x1_prop; norm_num at *; linarith ⟩
  linarith [h_pos.left, h_pos.right]

/-
The sum of the coefficients of p0 in the barycentric coordinates is 0.
-/
lemma lambda_sum_p0_coeff_eq_zero :
  (-(y1 - V_point 0)) / sep V_point + y1 / L2 (sigma V_point) + 1 / L1 Y_point = 0 := by
    have h_num : y1 * (V_point 0 - x1) = V_point 1 * (1 - x1) := by
      exact y1_relation;
    rw [ div_add_div, div_add_div ] <;> norm_num;
    · unfold L1 L2 sep at *;
      unfold Y_point; norm_num [ sigma ] ; ring_nf;
      grind;
    · exact ⟨ by linarith [ sep_V_neg ], by linarith [ L2_sigma_V_neg ] ⟩;
    · exact ne_of_gt ( L1_Y_pos );
    · exact ne_of_lt ( by exact sep_V_neg );
    · exact ne_of_lt ( by exact L2_sigma_V_neg )

/-
The sum of the coefficients of p1 in the barycentric coordinates is 0.
-/
lemma lambda_sum_p1_coeff_eq_zero :
  (1 - V_point 1) / sep V_point - (1 - x1) / L2 (sigma V_point) + 1 / L1 Y_point = 0 := by
    rw [ div_sub_div, div_add_div ];
    · unfold sep L2 L1 at *;
      unfold Y_point at *; norm_num at *; ring_nf at *;
      unfold sigma at *; norm_num at *; ring_nf at *;
      unfold y1; ring_nf at *;
      by_cases h : -x1 + V_point 0 = 0 <;> simp_all +decide [ sq, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
      · exact absurd h ( by linarith [ x1_prop, V_bounds ] );
      · grind;
    · exact mul_ne_zero ( by nlinarith [ sep_V_neg ] ) ( by nlinarith [ L2_sigma_V_neg ] );
    · exact ne_of_gt ( L1_Y_pos );
    · exact ne_of_lt ( by exact sep_V_neg );
    · exact ne_of_lt ( L2_sigma_V_neg )

/-
The sum of the barycentric coordinates at the origin is 1.
-/
lemma lambda_sum_at_O_point_eq_one : lambda_V O_point + lambda_sigma_V O_point + lambda_Y O_point = 1 := by
  unfold lambda_V lambda_sigma_V lambda_Y O_point;
  unfold sep L2 L1;
  rw [ div_add_div, div_add_div, div_eq_iff ] <;> norm_num [ V_point, y1, X_point, Y_point, sigma ];
  any_goals rw [ div_mul_eq_mul_div, div_sub', div_eq_iff ] <;> ring_nf <;> norm_num;
  -- By simplifying, we can see that the denominator is non-zero.
  have h_denom_nonzero : (Real.sqrt 6 + Real.sqrt 2) / 4 - x1 ≠ 0 := by
    -- By definition of $x1$, we know that $0.95 < x1 < 0.96$.
    have hx1_bounds : 0.95 < x1 ∧ x1 < 0.96 := by
      -- By definition of $x1$, we know that $0.95 < x1 < 0.96$.
      apply x1_prop.left |> fun h => ⟨h, x1_prop.right.left⟩;
    nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
  any_goals nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), x1_prop ];
  grind;
  · constructor;
    · constructor;
      · rw [ div_sub', div_mul_eq_mul_div, sub_eq_zero ];
        · rw [ div_sub', div_mul_eq_mul_div, eq_div_iff ] <;> ring_nf <;> norm_num;
          · rw [ show ( 6 : ℝ ) = 3 * 2 by norm_num, Real.sqrt_mul ] <;> ring_nf <;> norm_num;
            nlinarith [ Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), Real.sq_sqrt ( show 0 ≤ 2 by norm_num ), x1_prop.1, x1_prop.2.1, mul_pos ( Real.sqrt_pos.mpr ( show 0 < 3 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 0 < 2 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 3 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 2 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
          · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
          · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
        · norm_num;
      · rw [ div_mul_eq_mul_div, div_sub', div_eq_iff ] <;> ring_nf <;> norm_num;
        · have := x1_prop.2.2;
          unfold poly_X at this;
          grind;
        · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
        · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
    · rw [ add_div', div_sub', div_eq_iff ] <;> ring_nf <;> norm_num;
      · have := x1_prop.2.1;
        nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr this ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr this ) ];
      · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
      · have := x1_prop.2.1 ; norm_num at this ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
      · have := x1_prop.2.1 ; norm_num at this ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
  · constructor;
    · rw [ div_sub', div_mul_eq_mul_div, sub_eq_zero ];
      · rw [ div_sub', div_mul_eq_mul_div, eq_div_iff ] <;> ring_nf <;> norm_num;
        · rw [ show ( 6 : ℝ ) = 3 * 2 by norm_num, Real.sqrt_mul ] <;> ring_nf <;> norm_num;
          nlinarith [ Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), Real.sq_sqrt ( show 0 ≤ 2 by norm_num ), x1_prop.1, x1_prop.2.1, mul_pos ( Real.sqrt_pos.mpr ( show 0 < 3 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 0 < 2 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 3 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 2 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
        · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
        · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
      · norm_num;
    · rw [ div_mul_eq_mul_div, div_sub', div_eq_iff ] <;> ring_nf <;> norm_num;
      · have := x1_prop.2.2;
        unfold poly_X at this;
        grind;
      · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
      · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
  · rw [ add_div', div_sub', div_eq_iff ] <;> ring_nf <;> norm_num;
    · have := x1_prop.2.1;
      nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr this ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr this ) ];
    · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
    · have := x1_prop.2.1 ; norm_num at this ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
    · have := x1_prop.2.1 ; norm_num at this ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
  · rw [ div_sub', div_mul_eq_mul_div, sub_eq_zero ];
    · rw [ div_sub', div_mul_eq_mul_div, eq_div_iff ] <;> ring_nf <;> norm_num;
      · rw [ show ( 6 : ℝ ) = 3 * 2 by norm_num, Real.sqrt_mul ] <;> ring_nf <;> norm_num;
        nlinarith [ Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), Real.sq_sqrt ( show 0 ≤ 2 by norm_num ), x1_prop.1, x1_prop.2.1, mul_pos ( Real.sqrt_pos.mpr ( show 0 < 3 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 0 < 2 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 3 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 2 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
      · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
      · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
    · norm_num;
  · have := x1_prop.2.2;
    unfold poly_X at this;
    grind

/-
The sum of the barycentric coordinates is 1 for any point p.
-/
lemma lambda_sum_eq_one (p : Point) : lambda_V p + lambda_sigma_V p + lambda_Y p = 1 := by
  have h_sum : ∀ p : Point, lambda_V p + lambda_sigma_V p + lambda_Y p = lambda_V O_point + lambda_sigma_V O_point + lambda_Y O_point + (p 0 - O_point 0) * ((-(y1 - V_point 0)) / sep V_point + y1 / L2 (sigma V_point) + 1 / L1 Y_point) + (p 1 - O_point 1) * ((1 - V_point 1) / sep V_point - (1 - x1) / L2 (sigma V_point) + 1 / L1 Y_point) := by
    intros p; unfold lambda_V; unfold lambda_sigma_V; unfold lambda_Y; unfold O_point; ring_nf;
    unfold sep L2 L1; ring;
  rw [ h_sum p, lambda_sum_at_O_point_eq_one, lambda_sum_p0_coeff_eq_zero, lambda_sum_p1_coeff_eq_zero ] ; ring

/-
The coefficient of p0 in the barycentric expansion of p0 is 1.
-/
lemma p0_coeff_p0 : (-(y1 - V_point 0)) / sep V_point * V_point 0 + y1 / L2 (sigma V_point) * (sigma V_point) 0 + 1 / L1 Y_point * Y_point 0 = 1 := by
  field_simp;
  rw [ neg_div', div_add_div, div_add_div ];
  · rw [ div_eq_iff ];
    · unfold L1 L2 sep Y_point sigma V_point x1;
      rw [ show y1 = ( ( Real.sqrt 6 - Real.sqrt 2 ) / 4 ) * ( 1 - Classical.choose exists_root_x1 ) / ( ( Real.sqrt 6 + Real.sqrt 2 ) / 4 - Classical.choose exists_root_x1 ) from rfl ];
      by_cases h : ( Real.sqrt 6 + Real.sqrt 2 ) / 4 - Classical.choose exists_root_x1 = 0 <;> simp_all +decide [ sub_eq_iff_eq_add ];
      · have := Classical.choose_spec exists_root_x1;
        nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
      · grind;
    · exact mul_ne_zero ( mul_ne_zero ( by linarith [ sep_V_neg ] ) ( by linarith [ L2_sigma_V_neg ] ) ) ( by linarith [ L1_Y_pos ] );
  · exact mul_ne_zero ( by linarith [ sep_V_neg ] ) ( by linarith [ L2_sigma_V_neg ] );
  · exact ne_of_gt ( L1_Y_pos );
  · exact ne_of_lt ( by exact sep_V_neg );
  · exact ne_of_lt ( L2_sigma_V_neg )

/-
sep V_point is equal to (V_point 1 - V_point 0) times L1 Y_point.
-/
lemma sep_eq_L1_mul_diff : sep V_point = (V_point 1 - V_point 0) * L1 Y_point := by
  unfold L1 sep; ring_nf;
  unfold Y_point; ring_nf;
  norm_num +zetaDelta at *;
  ring

/-
L2 (sigma V_point) can be factored into terms involving x1 and V_point coordinates.
-/
lemma L2_sigma_V_eq : L2 (sigma V_point) = (1 - x1) / (V_point 0 - x1) * (V_point 1 - V_point 0) * (V_point 1 + V_point 0 - x1) := by
  -- Substitute the values of sigma V_point into L2.
  have h_sub : L2 (sigma V_point) = y1 * (V_point 1 - x1) - V_point 0 * (1 - x1) := by
    exact rfl;
  -- Substitute the value of y1 into the expression for L2 at sigma V_point.
  have hy1 : y1 = V_point 1 * (1 - x1) / (V_point 0 - x1) := by
    exact rfl;
  by_cases hx : V_point 0 = x1 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, sub_eq_iff_eq_add ];
  · exact absurd hy1 ( by linarith [ y1_bounds ] );
  · grind

/-
L1 Y_point can be factored into terms involving x1 and V_point coordinates.
-/
lemma L1_Y_point_eq : L1 Y_point = (1 - V_point 0) * (V_point 1 + V_point 0 - x1) / (V_point 0 - x1) := by
  unfold L1 Y_point x1;
  rw [ eq_div_iff ];
  · -- Substitute y1 from the equation y1 = V_point 1 * (1 - x1) / (V_point 0 - x1) into the left-hand side.
    have hy1 : y1 = V_point 1 * (1 - Classical.choose exists_root_x1) / (V_point 0 - Classical.choose exists_root_x1) := by
      exact rfl;
    rw [ eq_div_iff ] at hy1 <;> norm_num at *;
    · linarith;
    · intro h; norm_num [ h ] at hy1;
      exact absurd hy1 ( ne_of_gt ( y1_bounds.1 ) );
  · have := Classical.choose_spec exists_root_x1;
    norm_num [ V_point ] at *;
    nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ]

/-
The coefficient of p1 in the barycentric expansion of p0 is 0.
-/
lemma p1_coeff_p0 : (1 - V_point 1) / sep V_point * V_point 0 + (-(1 - x1)) / L2 (sigma V_point) * (sigma V_point) 0 + 1 / L1 Y_point * Y_point 0 = 0 := by
  rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div ];
  rw [ div_add_div, div_add_div, div_eq_iff ] <;> ring_nf!;
  any_goals nlinarith [ sep_V_neg, L2_sigma_V_neg, L1_Y_pos ];
  · rw [ show L2 ( sigma V_point ) = ( 1 - x1 ) / ( V_point 0 - x1 ) * ( V_point 1 - V_point 0 ) * ( V_point 1 + V_point 0 - x1 ) by exact
    L2_sigma_V_eq ];
    rw [ show sep V_point = ( V_point 1 - V_point 0 ) * L1 Y_point by exact sep_eq_L1_mul_diff ] ; ring_nf;
    field_simp;
    norm_num [ show L1 Y_point = ( 1 - V_point 0 ) * ( V_point 1 + V_point 0 - x1 ) / ( V_point 0 - x1 ) by
                exact L1_Y_point_eq ] ; ring_nf;
    rw [ show Y_point 0 = 1 by rfl ] ; ring_nf;
    norm_num;
  · exact mul_ne_zero ( mul_ne_zero ( ne_of_lt ( sep_V_neg ) ) ( ne_of_lt ( L2_sigma_V_neg ) ) ) ( ne_of_gt ( L1_Y_pos ) )

/-
A lemma stating that if S blocks two closed regions R1 and R2, and the intersection R1 ∩ R2 is covered by S (except possibly at "corner" points where segments cannot cross), then S blocks R1 ∪ R2.
-/
lemma blocking_union_lemma {S : Set (Set Point)} {R1 R2 : Set Point}
    (hR1 : IsClosed R1) (hR2 : IsClosed R2)
    (h1 : IsBlocking S R1) (h2 : IsBlocking S R2)
    (h_cover : ∀ x ∈ R1 ∩ R2, (∃ s ∈ S, x ∈ s) ∨ (∀ L, IsUnitSegment L → L ⊆ R1 ∪ R2 → x ∈ L → L ⊆ R1 ∨ L ⊆ R2)) :
    IsBlocking S (R1 ∪ R2) := by
      intro L hLL_sub hL_inter
      by_cases hL_R1 : L ⊆ R1;
      · exact h1 _ hLL_sub hL_R1;
      · by_cases hL_R2 : L ⊆ R2;
        · exact h2 _ hLL_sub hL_R2;
        · -- Since L is not in R1 and not in R2, it must intersect R1 ∩ R2.
          obtain ⟨x, hx⟩ : ∃ x, x ∈ L ∧ x ∈ R1 ∩ R2 := by
            simp_all +decide [ Set.subset_def ];
            -- Since L is connected and R1 and R2 are closed, L must intersect R1 ∩ R2.
            have h_connected : IsConnected L := by
              obtain ⟨ A, B, hAB, hL ⟩ := hLL_sub;
              convert isConnected_Ioo ( show ( 0 : ℝ ) < 1 by norm_num ) using 1;
              constructor <;> intro h <;> have := h.isPreconnected <;> simp_all +decide [ openSegment_eq_image ];
              · exact isConnected_Ioo ( by norm_num );
              · exact h.image _ ( Continuous.continuousOn <| by continuity )
            have h_connected : IsConnected L := by
              exact h_connected
            have h_inter : ∃ z ∈ L, z ∈ R1 ∩ R2 := by
              have h_inter : IsPreconnected L := by
                exact h_connected.isPreconnected;
              contrapose! h_inter;
              simp_all +decide [ IsPreconnected ];
              use Set.univ \ R2, isOpen_univ.sdiff hR2, Set.univ \ R1, isOpen_univ.sdiff hR1;
              simp_all +decide [ Set.Nonempty ];
              exact ⟨ fun x hx => by cases hL_inter x hx <;> aesop, fun x hx hx' => by cases hL_inter x hx <;> aesop ⟩
            obtain ⟨ z, hz₁, hz₂ ⟩ := h_inter
            use z;
            exact ⟨ hz₁, hz₂.1, hz₂.2 ⟩;
          cases h_cover x hx.2 <;> simp_all +decide [ Set.disjoint_left ];
          · exact ⟨ _, ‹∃ s ∈ S, x ∈ s›.choose_spec.1, _, ‹∃ s ∈ S, x ∈ s›.choose_spec.2, hx.1 ⟩;
          · grind

/-
Define L_OV and prove it is positive at sigma V.
-/
noncomputable def L_OV (p : Point) : ℝ :=
  -(V_point 1) * p 0 + (V_point 0) * p 1

lemma L_OV_sigmaV_pos : L_OV (sigma V_point) > 0 := by
  unfold L_OV V_point;
  unfold sigma; norm_num; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ] ;

/-
The linear form L_OV is negative at X.
-/
lemma L_OV_X_neg : L_OV X_point < 0 := by
  unfold L_OV X_point;
  rw [ show V_point = ![ ( Real.sqrt 6 + Real.sqrt 2 ) / 4, ( Real.sqrt 6 - Real.sqrt 2 ) / 4 ] from rfl ] ; norm_num ; ring_nf;
  exact lt_trans ( by norm_num ) ( x1_prop.1 )

/-
Region2 lies in the non-positive half-plane of L_OV.
-/
lemma Region2_sub_H_neg : ∀ p ∈ Region2, L_OV p ≤ 0 := by
  intro p hp
  have h_convex : ∃ (a b c : ℝ), a + b + c = 1 ∧ 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ p = a • O_point + b • V_point + c • X_point := by
    rw [Region2] at hp
    generalize_proofs at *;
    rw [ convexHull_insert ] at hp;
    · norm_num [ segment_eq_image ] at hp;
      obtain ⟨ i, hi, x, hx, rfl ⟩ := hp; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by ring, by nlinarith, by nlinarith, by nlinarith, by ext ; simpa using by ring ⟩ ;
    · norm_num +zetaDelta at *
  generalize_proofs at *;
  -- Substitute p into L_OV and simplify using the convex combination.
  obtain ⟨a, b, c, habc, ha, hb, hc, hp_eq⟩ := h_convex
  have hL_OV : L_OV p = a * L_OV O_point + b * L_OV V_point + c * L_OV X_point := by
    unfold L_OV; norm_num [ hp_eq ] ; ring;
  -- Since $L_OV(O) = 0$ and $L_OV(V) = 0$, the expression simplifies to $c * L_OV(X)$.
  have hL_OV_simplified : L_OV p = c * L_OV X_point := by
    -- Substitute the values of L_OV at O and V into the equation.
    have hL_OV_values : L_OV O_point = 0 ∧ L_OV V_point = 0 := by
      unfold L_OV; norm_num [ O_point, V_point ] ; ring;
    generalize_proofs at *;
    rw [hL_OV, hL_OV_values.left, hL_OV_values.right]
    simp +decide [mul_zero, add_zero]
  generalize_proofs at *; (
  exact hL_OV_simplified.symm ▸ mul_nonpos_of_nonneg_of_nonpos hc ( le_of_lt ( L_OV_X_neg ) ) |> le_trans <| by norm_num;)

/-
Define weights and intersection point, and prove weights are positive.
-/
noncomputable def w_sigmaV : ℝ := L_OV (sigma V_point)

noncomputable def w_X : ℝ := -L_OV X_point

noncomputable def s_cross : ℝ := w_X / (w_sigmaV + w_X)

noncomputable def I_cross : Point := s_cross • (sigma V_point) + (1 - s_cross) • X_point

lemma w_pos : w_sigmaV > 0 ∧ w_X > 0 := by
  exact ⟨ L_OV_sigmaV_pos, neg_pos_of_neg L_OV_X_neg ⟩

/-
Prove that s_cross is strictly between 0 and 1.
-/
lemma s_cross_bounds : 0 < s_cross ∧ s_cross < 1 := by
  have h_s_cross_bounds : 0 < s_cross ∧ s_cross < 1 := by
    have h_w_sigmaV_pos : 0 < w_sigmaV := by
      apply (w_pos).left.trans_le' ( by norm_num )
    have h_w_X_pos : 0 < w_X := by
      exact neg_pos_of_neg ( L_OV_X_neg )
    unfold s_cross; exact ⟨ by positivity, by rw [ div_lt_iff₀ ( by positivity ) ] ; linarith ⟩ ;
  exact h_s_cross_bounds

/-
Prove that L_OV vanishes at I_cross.
-/
lemma L_OV_I_cross : L_OV I_cross = 0 := by
  unfold L_OV I_cross; norm_num [ sub_smul ] ; ring_nf;
  field_simp;
  unfold s_cross; rw [ div_mul_eq_mul_div, div_mul_eq_mul_div ] ; rw [ div_sub_one, div_mul_eq_mul_div ] ; ring_nf;
  · field_simp;
    rw [ div_add', div_eq_iff ] <;> ring_nf!;
    · unfold w_sigmaV w_X; ring_nf;
      unfold L_OV; ring_nf;
      unfold sigma; norm_num; ring;
    · exact ne_of_gt ( add_pos ( w_pos.2 ) ( w_pos.1 ) );
    · exact ne_of_gt ( add_pos ( w_pos.2 ) ( w_pos.1 ) );
  · exact ne_of_gt ( add_pos ( w_pos.1 ) ( w_pos.2 ) )

/-
The intersection point I_cross lies in the open segment between O and V.
-/
lemma I_cross_in_segment_OV : I_cross ∈ openSegment ℝ O_point V_point := by
  -- By definition of $I_cross$, we know that $I_cross = k • V$ for some $k \in (0, 1)$.
  obtain ⟨k, hk⟩ : ∃ k : ℝ, 0 < k ∧ k < 1 ∧ I_cross = k • V_point := by
    -- By definition of $I_cross$, we know that $I_cross = k • V$ for some $k \in (0, 1)$. We can solve for $k$ using the coordinates of $I_cross$ and $V$.
    obtain ⟨k, hk⟩ : ∃ k : ℝ, I_cross = k • V_point := by
      have hL_OV_I_cross : L_OV I_cross = 0 := by
        exact L_OV_I_cross;
      unfold L_OV at hL_OV_I_cross;
      use I_cross 0 / V_point 0;
      ext i; fin_cases i <;> norm_num <;> rw [ div_mul_eq_mul_div, eq_div_iff ] <;> linarith! [ V_bounds ] ;
    refine' ⟨ k, _, _, hk ⟩;
    · have := congr_fun hk 0; have := congr_fun hk 1; norm_num [ I_cross, s_cross ] at *;
      unfold sigma at *; unfold X_point at *; unfold V_point at *; norm_num at *;
      nlinarith [ show 0 < w_X / ( w_sigmaV + w_X ) by exact div_pos ( by exact neg_pos.mpr ( L_OV_X_neg ) ) ( by linarith [ w_pos ] ), show 0 < ( Real.sqrt 6 - Real.sqrt 2 ) / 4 by exact div_pos ( sub_pos.mpr ( Real.lt_sqrt_of_sq_lt ( by norm_num ) ) ) ( by norm_num ), show 0 < ( Real.sqrt 6 + Real.sqrt 2 ) / 4 by positivity ];
    · unfold I_cross at hk;
      rw [ ← List.ofFn_inj ] at hk ; norm_num at hk;
      nlinarith! [ s_cross_bounds, V_bounds, x1_prop ];
  -- Since $0 < k < 1$, we can write $I_cross$ as $(1 - k) • O_point + k • V_point$, which is in the open segment between $O_point$ and $V_point$.
  have h_open_segment : I_cross = (1 - k) • O_point + k • V_point := by
    rw [ hk.2.2, show O_point = 0 from by ext i; fin_cases i <;> rfl ] ; norm_num;
  exact ⟨ 1 - k, k, by norm_num; linarith, by linarith, by norm_num [ h_open_segment ] ⟩

/-
Express X as an affine combination of I_cross and sigma V.
-/
lemma X_eq_affine_I_sigmaV : X_point = (1 / (1 - s_cross)) • I_cross - (s_cross / (1 - s_cross)) • (sigma V_point) := by
  by_cases h : 1 - s_cross = 0 <;> simp_all +decide [ div_eq_inv_mul, smul_smul ];
  · exact absurd h ( by linarith [ s_cross_bounds.2 ] );
  · rw [ show I_cross = s_cross • sigma V_point + ( 1 - s_cross ) • X_point by ext i; fin_cases i <;> norm_num [ I_cross ] ] ; ext i ; fin_cases i <;> norm_num [ h ] <;> ring

/-
If a linear combination of weights is non-negative, then a related coefficient inequality holds.
-/
lemma coeff_ineq (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hL : c * w_sigmaV - d * w_X ≥ 0) :
  c - d * (s_cross / (1 - s_cross)) ≥ 0 := by
    field_simp;
    rw [ le_sub_comm, div_le_iff₀ ];
    · rw [ show s_cross = w_X / ( w_sigmaV + w_X ) by rfl ];
      rw [ mul_sub, mul_div, mul_one, div_le_iff₀ ] <;> nlinarith [ w_pos, mul_div_cancel₀ w_X ( by linarith [ w_pos ] : ( w_sigmaV + w_X ) ≠ 0 ) ];
    · linarith [ s_cross_bounds ]

/-
Any point in the convex hull of {O, V, sigma V, X} with non-negative L_OV value lies in Region1.
-/
lemma convexHull_sub_Region1_of_pos :
  ∀ p ∈ convexHull ℝ {O_point, V_point, sigma V_point, X_point}, L_OV p ≥ 0 → p ∈ Region1 := by
    intro p hp hp_nonneg_nonneg
    obtain ⟨a, b, c, d, ha, hb, hc, hd, habcd⟩ : ∃ a b c d : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ a + b + c + d = 1 ∧ p = a • O_point + b • V_point + c • sigma V_point + d • X_point := by
      norm_num [ convexHull_insert ] at hp;
      norm_num [ segment_eq_image ] at hp;
      rcases hp with ⟨ a, ⟨ ha₁, ha₂ ⟩, b, ⟨ hb₁, hb₂ ⟩, c, ⟨ hc₁, hc₂ ⟩, rfl ⟩ ; exact ⟨ 1 - c, c * ( 1 - b ), c * b * ( 1 - a ), c * b * a, by linarith, by nlinarith, by nlinarith [ mul_nonneg hc₁ hb₁ ], by nlinarith [ mul_nonneg hc₁ hb₁ ], by linarith, by ext i; fin_cases i <;> norm_num <;> ring ⟩ ;
    -- Substitute X using X_eq_affine_I_sigmaV:
    have hp_subst : p = a • O_point + b • V_point + (d / (1 - s_cross)) • I_cross + (c - d * (s_cross / (1 - s_cross))) • (sigma V_point) := by
      rw [ habcd.2, X_eq_affine_I_sigmaV ] ; ring_nf;
      ext ; norm_num ; ring;
    -- Since $I_cross$ is in the convex hull of $\{O, V\}$, we can write $I_cross$ as a convex combination of $O$ and $V$.
    obtain ⟨α, β, hα, hβ, hαβ⟩ : ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ α + β = 1 ∧ I_cross = α • O_point + β • V_point := by
      have hI_cross_convex : I_cross ∈ openSegment ℝ O_point V_point := by
        exact I_cross_in_segment_OV;
      rcases hI_cross_convex with ⟨ α, β, hα, hβ, hab, h ⟩ ; exact ⟨ α, β, hα.le, hβ.le, hab, h ▸ by ring_nf ⟩ ;
    -- Substitute $I_cross$ into the expression for $p$:
    have hp_final : p = (a + d / (1 - s_cross) * α) • O_point + (b + d / (1 - s_cross) * β) • V_point + (c - d * (s_cross / (1 - s_cross))) • (sigma V_point) := by
      convert hp_subst using 1 ; rw [ hαβ.2 ] ; ext ; norm_num ; ring;
    -- The coefficients of $O$, $V$, and $\sigma V$ in the expression for $p$ are non-negative and sum to 1.
    have h_coeff_nonneg : 0 ≤ a + d / (1 - s_cross) * α ∧ 0 ≤ b + d / (1 - s_cross) * β ∧ 0 ≤ c - d * (s_cross / (1 - s_cross)) ∧ (a + d / (1 - s_cross) * α) + (b + d / (1 - s_cross) * β) + (c - d * (s_cross / (1 - s_cross))) = 1 := by
      refine' ⟨ _, _, _, _ ⟩;
      · exact add_nonneg ha ( mul_nonneg ( div_nonneg hd ( sub_nonneg.mpr ( by linarith [ s_cross_bounds ] ) ) ) hα );
      · exact add_nonneg hb ( mul_nonneg ( div_nonneg hd ( sub_nonneg.mpr ( by linarith [ s_cross_bounds ] ) ) ) hβ );
      · have h_coeff_nonneg : c * w_sigmaV - d * w_X ≥ 0 := by
          convert hp_nonneg_nonneg using 1 ; norm_num [ habcd.2, L_OV ] ; ring_nf;
          unfold w_sigmaV w_X; ring_nf;
          unfold L_OV; ring_nf;
          unfold O_point; norm_num; ring;
        convert coeff_ineq c d hc hd h_coeff_nonneg using 1;
      · rw [ show α = 1 - β by linarith ] ; ring_nf;
        linarith [ inv_mul_cancel_left₀ ( show ( 1 - s_cross ) ≠ 0 by linarith [ s_cross_bounds ] ) d ];
    rw [hp_final];
    rw [Region1];
    rw [ convexHull_eq ];
    refine' ⟨ Fin 3, { 0, 1, 2 }, fun i => if i = 0 then a + d / ( 1 - s_cross ) * α else if i = 1 then b + d / ( 1 - s_cross ) * β else c - d * ( s_cross / ( 1 - s_cross ) ), fun i => if i = 0 then O_point else if i = 1 then V_point else sigma V_point, _, _, _, _ ⟩ <;> simp +decide [ *, Fin.sum_univ_three, Finset.centerMass ];
    · linarith;
    · norm_num [ ← add_assoc, h_coeff_nonneg.2.2.2 ];
      norm_num [ show a + d / ( 1 - s_cross ) * α + b + d / ( 1 - s_cross ) * β + ( c - d * ( s_cross / ( 1 - s_cross ) ) ) = 1 by linarith ]

/-
Express sigma V as an affine combination of I_cross and X.
-/
lemma sigmaV_eq_affine_I_X : sigma V_point = (1 / s_cross) • I_cross - ((1 - s_cross) / s_cross) • X_point := by
  field_simp;
  rw [ show I_cross = s_cross • sigma V_point + ( 1 - s_cross ) • X_point by rfl ];
  ext i ; ring_nf;
  by_cases h : s_cross = 0 <;> simp_all +decide [ sub_smul, smul_smul ];
  · exact absurd h ( ne_of_gt ( s_cross_bounds.1 ) );
  · grind

/-
Any point in the convex hull of {O, V, sigma V, X} with non-positive L_OV value lies in Region2.
-/
lemma convexHull_sub_Region2_of_neg :
  ∀ p ∈ convexHull ℝ {O_point, V_point, sigma V_point, X_point}, L_OV p ≤ 0 → p ∈ Region2 := by
    intro p hp hLull_subset_span;
    -- Since $p$ is in the convex hull of $\{O, V, \sigma V, X\}$, we can write it as a convex combination of these points.
    obtain ⟨a, b, c, d, ha, hb, hc, hd, habcd, hp_comb⟩ : ∃ a b c d : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ a + b + c + d = 1 ∧ p = a • O_point + b • V_point + c • sigma V_point + d • X_point := by
      rw [ convexHull_insert ] at hp;
      · norm_num [ segment_eq_image ] at hp;
        rcases hp with ⟨ q, hq, x, hx, rfl ⟩ ; rw [ convexHull_insert ] at hq <;> norm_num at hq ⊢;
        rcases hq with ⟨ y, hy, hq ⟩ ; rw [ segment_eq_image ] at hy hq; norm_num at hy hq ⊢;
        rcases hy with ⟨ y, ⟨ hy₀, hy₁ ⟩, rfl ⟩ ; rcases hq with ⟨ z, ⟨ hz₀, hz₁ ⟩, rfl ⟩ ; exact ⟨ 1 - x, by linarith, x * ( 1 - z ), by nlinarith, x * z * ( 1 - y ), by nlinarith [ mul_nonneg hx.1 hz₀ ], x * z * y, by nlinarith [ mul_nonneg hx.1 hz₀ ], by ring, by ext i; simpa using by ring ⟩ ;
      · norm_num +zetaDelta at *;
    -- Substitute sigma V using sigmaV_eq_affine_I_X:
    have hp_subst : p = a • O_point + b • V_point + (c / s_cross) • I_cross + (d - c * (1 - s_cross) / s_cross) • X_point := by
      convert hp_comb using 1;
      rw [ show sigma V_point = ( 1 / s_cross ) • I_cross - ( ( 1 - s_cross ) / s_cross ) • X_point from ?_ ] ; ext ; norm_num ; ring;
      convert sigmaV_eq_affine_I_X using 1;
    -- We need to show that the coefficients of $I_cross$ and $X$ are non-negative.
    have h_coeff_nonneg : 0 ≤ c / s_cross ∧ 0 ≤ d - c * (1 - s_cross) / s_cross := by
      have h_coeff_nonneg : d * w_X - c * w_sigmaV ≥ 0 := by
        have h_coeff_nonneg : L_OV p = c * w_sigmaV - d * w_X := by
          unfold L_OV w_sigmaV w_X; norm_num [ hp_comb ] ; ring_nf;
          unfold L_OV; norm_num [ O_point, V_point, sigma, X_point ] ; ring;
        linarith;
      have h_coeff_nonneg : d - c * (1 - s_cross) / s_cross ≥ 0 := by
        have h_coeff_nonneg : d * s_cross - c * (1 - s_cross) ≥ 0 := by
          have h_coeff_nonneg : d * (w_X / (w_sigmaV + w_X)) - c * (1 - w_X / (w_sigmaV + w_X)) ≥ 0 := by
            have h_pos : 0 < w_sigmaV + w_X := by
              exact add_pos ( w_pos.1 ) ( w_pos.2 )
            field_simp [h_pos] at *; linarith;
          exact h_coeff_nonneg;
        rw [ sub_div', ge_iff_le, le_div_iff₀ ] <;> linarith [ s_cross_bounds.1, s_cross_bounds.2 ]
      exact ⟨div_nonneg hc (by
      exact div_nonneg ( by linarith [ w_pos ] ) ( by linarith [ w_pos ] )), h_coeff_nonneg⟩;
    -- Since $I_cross$ is in the convex hull of $\{O, V\}$, we can write it as a convex combination of $O$ and $V$.
    obtain ⟨e, f, he, hf, hef, hI_cross⟩ : ∃ e f : ℝ, 0 ≤ e ∧ 0 ≤ f ∧ e + f = 1 ∧ I_cross = e • O_point + f • V_point := by
      obtain ⟨e, he⟩ : ∃ e : ℝ, 0 ≤ e ∧ e ≤ 1 ∧ I_cross = e • O_point + (1 - e) • V_point := by
        have := I_cross_in_segment_OV;
        obtain ⟨ e, he, he' ⟩ := this;
        exact ⟨ e, he'.1.le, by linarith, by simpa [ ← he'.2.2.1 ] using he'.2.2.2.symm ⟩;
      exact ⟨ e, 1 - e, he.1, sub_nonneg.2 he.2.1, by ring, he.2.2 ⟩;
    -- Substitute hI_cross into hp_subst and simplify.
    have hp_simplified : p = (a + (c / s_cross) * e) • O_point + (b + (c / s_cross) * f) • V_point + (d - c * (1 - s_cross) / s_cross) • X_point := by
      convert hp_subst using 1 ; rw [ hI_cross ] ; ext ; norm_num ; ring;
    -- Since the coefficients sum to 1 and are non-negative, p is a convex combination of O, V, and X.
    have h_convex_comb : ∃ a' b' c' : ℝ, 0 ≤ a' ∧ 0 ≤ b' ∧ 0 ≤ c' ∧ a' + b' + c' = 1 ∧ p = a' • O_point + b' • V_point + c' • X_point := by
      use a + c / s_cross * e, b + c / s_cross * f, d - c * (1 - s_cross) / s_cross;
      refine' ⟨ _, _, _, _, hp_simplified ⟩ <;> try nlinarith;
      rw [ ← eq_sub_iff_add_eq' ] at hef ; subst_vars ; ring_nf;
      rw [ mul_assoc, mul_inv_cancel₀ ( ne_of_gt ( show 0 < s_cross from by linarith [ s_cross_bounds ] ) ), mul_one ] ; linarith;
    obtain ⟨ a', b', c', ha', hb', hc', habcd', rfl ⟩ := h_convex_comb; exact (by
    rw [ show Region2 = convexHull ℝ { O_point, V_point, X_point } from rfl ];
    rw [ convexHull_eq ];
    refine' ⟨ Fin 3, { 0, 1, 2 }, fun i => if i = 0 then a' else if i = 1 then b' else c', fun i => if i = 0 then O_point else if i = 1 then V_point else X_point, _, _, _, _ ⟩ <;> simp +decide [ *, Fin.sum_univ_three, Finset.centerMass ];
    · linarith;
    · simp +decide [ ← add_assoc, habcd' ] at * ; aesop ( simp_config := { singlePass := true } ) ;);

/-
L2 is zero at X.
-/
lemma L2_X : L2 X_point = 0 := by
  unfold L2 X_point; norm_num;

/-
L2 is positive at A0.
-/
lemma L2_A0_pos : L2 A_0 > 0 := by
  unfold L2 A_0;
  -- Substitute the values of y1 and x1 from their definitions.
  simp [y1, x1];
  refine' mul_pos _ _;
  · refine' div_pos _ _;
    · refine' mul_pos _ _;
      · exact V_bounds.2.2.1.trans_le' <| by norm_num;
      · have := Classical.choose_spec exists_root_x1;
        norm_num at * ; linarith;
    · have := Classical.choose_spec exists_root_x1;
      exact sub_pos_of_lt ( by have := V_bounds; norm_num at *; linarith );
  · have := Classical.choose_spec exists_root_x1;
    norm_num at * ; linarith

/-
L2 is negative at O.
-/
lemma L2_O_neg : L2 O_point < 0 := by
  unfold L2; norm_num;
  unfold O_point x1 y1;
  have := Classical.choose_spec exists_root_x1; ( unfold V_point; norm_num; );
  rw [ div_mul_eq_mul_div, div_pos_iff ];
  refine' Or.inl ⟨ _, _ ⟩;
  · exact mul_pos ( mul_pos ( by nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ] ) ( by unfold x1; norm_num; linarith ) ) ( by linarith );
  · unfold x1; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ] ;

/-
L3 is zero at sigma X.
-/
lemma L3_sigma_X : L3 (sigma X_point) = 0 := by
  unfold L3 sigma X_point; norm_num;

/-
L3 is positive at sigma A0.
-/
lemma L3_sigma_A0_pos : L3 (sigma A_0) > 0 := by
  unfold L3 sigma A_0 ; norm_num;
  unfold y1 x1;
  refine' mul_pos _ _;
  · refine' div_pos _ _;
    · -- Since $V_point$ is in the open unit square, its coordinates are positive.
      have hV_pos : 0 < V_point 1 := by
        exact V_bounds.2.2.1.trans_le' <| by norm_num;
      exact mul_pos hV_pos ( sub_pos_of_lt ( by have := Classical.choose_spec exists_root_x1; nlinarith [ sq_nonneg ( ( Classical.choose exists_root_x1 ) ^ 2 - 1 ), sq_nonneg ( ( Classical.choose exists_root_x1 ) ^ 2 - 2 ), sq_nonneg ( ( Classical.choose exists_root_x1 ) ^ 2 - 3 ), sq_nonneg ( ( Classical.choose exists_root_x1 ) ^ 2 - 4 ) ] ) );
    · have := Classical.choose_spec exists_root_x1;
      exact sub_pos_of_lt ( by have := V_bounds; norm_num at *; linarith );
  · have := Classical.choose_spec exists_root_x1;
    norm_num at * ; linarith

/-
L3 is negative at O.
-/
lemma L3_O_neg : L3 O_point < 0 := by
  unfold L3;
  unfold y1 x1 O_point; norm_num;
  have hV_bounds : 0.96 < V_point 0 ∧ V_point 0 < 0.97 ∧ 0.25 < V_point 1 ∧ V_point 1 < 0.26 := by
    exact V_bounds
  generalize_proofs at *;
  have := Classical.choose_spec ‹∃ x : ℝ, 19 / 20 < x ∧ x < 24 / 25 ∧ poly_X x = 0›; norm_num [ poly_X ] at *; rw [ div_mul_eq_mul_div, lt_div_iff₀ ] <;> nlinarith;

/-
L2 is non-negative on Region4.
-/
lemma Region4_sub_L2_ge_0 : ∀ p ∈ Region4, L2 p ≥ 0 := by
  -- Since L2 is non-negative at all vertices of Region4, it is non-negative on the convex hull of these vertices.
  have h_L2_nonneg_vertices : ∀ p ∈ ({X_point, A_0, Y_point} : Set Point), L2 p ≥ 0 := by
    -- Since L2 is non-negative at X, A0, and Y, it is non-negative on the convex hull of these points.
    simp [L2_X, L2_A0_pos, L2_Y];
    exact le_of_lt ( L2_A0_pos );
  -- Since L2 is non-negative at all vertices of Region4, it is non-negative on the convex hull of these vertices by the properties of convex combinations.
  intros p hp
  have h_convex_comb : ∃ (a b c : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • X_point + b • A_0 + c • Y_point := by
    unfold Region4 at hp; simp_all +decide [ convexHull_insert ] ;
    rcases hp with ⟨ q, ⟨ a, b, ha, hb, hab, rfl ⟩, ⟨ c, d, hc, hd, hcd, rfl ⟩ ⟩ ; exact ⟨ c, hc, d * a, mul_nonneg hd ha, d * b, mul_nonneg hd hb, by nlinarith, by ext i; simpa using by ring ⟩ ;
  generalize_proofs at *; (
  obtain ⟨ a, b, c, ha, hb, hc, habc, rfl ⟩ := h_convex_comb; simp_all +decide [ L2 ] ;
  convert add_le_add_three ( mul_le_mul_of_nonneg_left h_L2_nonneg_vertices.1 ( by positivity : 0 ≤ a ) ) ( mul_le_mul_of_nonneg_left h_L2_nonneg_vertices.2.1 ( by positivity : 0 ≤ b ) ) ( mul_le_mul_of_nonneg_left h_L2_nonneg_vertices.2.2 ( by positivity : 0 ≤ c ) ) using 1 <;> ring_nf;
  linear_combination' y1 * x1 * habc)

/-
L3 is non-negative on Region5.
-/
lemma Region5_sub_L3_ge_0 : ∀ p ∈ Region5, L3 p ≥ 0 := by
  intro p hp;
  -- Since $p$ is in the convex hull of $\{ \sigma X, \sigma A0, \sigma Y \}$, we can write $p$ as a convex combination of these points.
  obtain ⟨a, b, c, ha, hb, hc, habc, hp_comb⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • sigma X_point + b • sigma A_0 + c • sigma Y_point := by
    rw [ Region5 ] at hp;
    rw [ convexHull_insert ] at hp;
    · norm_num [ segment_eq_image ] at hp;
      rcases hp with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext ; simpa using by ring ⟩ ;
    · norm_num +zetaDelta at *;
  -- Since $L3$ is affine, we have $L3(p) = a * L3(\sigma X) + b * L3(\sigma A0) + c * L3(\sigma Y)$.
  have hL3_affine : L3 p = a * L3 (sigma X_point) + b * L3 (sigma A_0) + c * L3 (sigma Y_point) := by
    unfold L3; norm_num [ hp_comb ] ; ring_nf;
    linear_combination' habc * y1 * x1;
  -- Since $L3(\sigma X) = 0$, $L3(\sigma A0) > 0$, and $L3(\sigma Y) = 0$, we have $L3(p) = b * L3(\sigma A0)$.
  have hL3_simplified : L3 p = b * L3 (sigma A_0) := by
    rw [ hL3_affine, show L3 ( sigma X_point ) = 0 from ?_, show L3 ( sigma Y_point ) = 0 from ?_ ] <;> ring_nf;
    · exact L3_sigma_Y;
    · exact L3_sigma_X;
  exact hL3_simplified.symm ▸ mul_nonneg hb ( le_of_lt ( L3_sigma_A0_pos ) )

/-
Region2 is in the half-plane L2 <= 0. Region3 is in the half-plane L3 <= 0.
-/
lemma Region2_sub_L2_le_0 : ∀ p ∈ Region2, L2 p ≤ 0 := by
  intro p hp
  obtain ⟨a, b, c, ha, hb, hc, habc, hp_eq⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • V_point + c • X_point := by
    rw [ show Region2 = convexHull ℝ { O_point, V_point, X_point } from rfl ] at hp;
    norm_num [ convexHull_insert ] at hp;
    rcases hp with ⟨ q, ⟨ a, b, ha, hb, hab, rfl ⟩, ⟨ c, d, hc, hd, hcd, rfl ⟩ ⟩ ; use c, d * a, d * b; simp_all +decide [ segment_eq_image ] ; ring_nf;
    exact ⟨ mul_nonneg hd ha, mul_nonneg hd hb, by nlinarith, by rw [ mul_smul, mul_smul ] ; abel1 ⟩;
  -- Since $L2$ is affine, we have $L2(p) = a * L2(O) + b * L2(V) + c * L2(X)$.
  have hL2_affine : L2 p = a * L2 O_point + b * L2 V_point + c * L2 X_point := by
    unfold L2; norm_num [ hp_eq ] ; ring_nf;
    rw [ ← eq_sub_iff_add_eq' ] at habc ; subst habc ; ring;
  nlinarith [ L2_O_neg, L2_V, L2_X ]

lemma Region3_sub_L3_le_0 : ∀ p ∈ Region3, L3 p ≤ 0 := by
  -- Using the fact that L3 is linear and that L3(O) < 0, L3(sigma V) = 0, and L3(sigma X) = 0, we can show that L3(p) ≤ 0 for any point p in Region3.
  intros p hp
  have h_comb : ∃ t u v : ℝ, 0 ≤ t ∧ 0 ≤ u ∧ 0 ≤ v ∧ t + u + v = 1 ∧ p = t • O_point + u • sigma V_point + v • sigma X_point := by
    have h_convex_comb : p ∈ convexHull ℝ {O_point, sigma V_point, sigma X_point} := by
      exact hp;
    rw [ convexHull_insert ] at h_convex_comb;
    · norm_num [ segment_eq_image ] at h_convex_comb;
      rcases h_convex_comb with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext ; simpa using by ring ⟩ ;
    · norm_num +zetaDelta at *;
  obtain ⟨t, u, v, ht, hu, hv, hsum, hp_eq⟩ := h_comb
  have hL3 : L3 p = t * L3 O_point + u * L3 (sigma V_point) + v * L3 (sigma X_point) := by
    unfold L3; simp +decide [ hp_eq, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm ] ;
    grind;
  rw [hL3];
  exact add_nonpos ( add_nonpos ( mul_nonpos_of_nonneg_of_nonpos ht ( by exact le_of_lt ( by exact
    L3_O_neg ) ) ) ( mul_nonpos_of_nonneg_of_nonpos hu ( by exact le_of_eq ( by exact L3_sigma_V ) ) ) ) ( mul_nonpos_of_nonneg_of_nonpos hv ( by exact le_of_eq ( by exact
    L3_sigma_X ) ) )

/-
L3 is negative at V.
-/
lemma L3_V_neg : L3 V_point < 0 := by
  unfold L3 y1 V_point x1;
  field_simp;
  refine' mul_neg_of_pos_of_neg _ _;
  · exact sub_pos_of_lt ( by have := Classical.choose_spec exists_root_x1; nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ] );
  · have := Classical.choose_spec exists_root_x1 ; norm_num;
    rw [ div_lt_iff₀ ] <;> norm_num at *;
    · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
    · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ]

/-
We define an auxiliary polynomial and identify its roots. The roots are 1 and `V_point 0 + V_point 1 - 1`.
-/
noncomputable def poly_sep_aux (y : ℝ) : ℝ :=
  (1 - V_point 1) * (1 - V_point 0) - (y - V_point 0) * (y - V_point 1)

/-
The value of the separator function at `sigma Y_point` is equal to the value of the auxiliary polynomial at `y1`.
-/
lemma sep_sigma_Y_eq_poly : sep (sigma Y_point) = poly_sep_aux y1 := by
  exact rfl

/-
We show that the auxiliary polynomial can be factored as `(y - root1) * (1 - y)`.
-/
lemma poly_sep_aux_eq_factored (y : ℝ) :
  poly_sep_aux y = (y - (V_point 0 + V_point 1 - 1)) * (1 - y) := by
    unfold poly_sep_aux; ring;

/-
We prove that `V_point 0 + V_point 1 - 1` is strictly less than `y1`.
-/
lemma root1_lt_y1 : V_point 0 + V_point 1 - 1 < y1 := by
  unfold y1 V_point;
  rw [ lt_div_iff₀ ] <;> norm_num;
  · unfold x1;
    have := Classical.choose_spec exists_root_x1;
    nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr this.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr this.1 ) ];
  · unfold x1;
    have := Classical.choose_spec exists_root_x1;
    nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ]

/-
The auxiliary polynomial is positive strictly between its roots.
-/
lemma poly_sep_aux_pos_of_between_roots (y : ℝ) (h1 : V_point 0 + V_point 1 - 1 < y) (h2 : y < 1) :
  poly_sep_aux y > 0 := by
    exact poly_sep_aux_eq_factored y ▸ mul_pos ( by linarith ) ( by linarith )

/-
The separator function is strictly positive at `sigma Y_point`.
-/
lemma sep_sigma_Y_pos : sep (sigma Y_point) > 0 := by
  rw [sep_sigma_Y_eq_poly]
  apply poly_sep_aux_pos_of_between_roots
  · exact root1_lt_y1
  · exact y1_bounds.2

/-
We define the barycentric coordinates for Region6b and verify their values at the vertices.
-/
noncomputable def mu_sigmaV (p : Point) : ℝ := L4 p / L4 (sigma V_point)

noncomputable def mu_Y (p : Point) : ℝ := L3 p / L3 Y_point

noncomputable def mu_sigmaY (p : Point) : ℝ := sep p / sep (sigma Y_point)

lemma mu_values :
  mu_sigmaV (sigma V_point) = 1 ∧ mu_sigmaV Y_point = 0 ∧ mu_sigmaV (sigma Y_point) = 0 ∧
  mu_Y (sigma V_point) = 0 ∧ mu_Y Y_point = 1 ∧ mu_Y (sigma Y_point) = 0 ∧
  mu_sigmaY (sigma V_point) = 0 ∧ mu_sigmaY Y_point = 0 ∧ mu_sigmaY (sigma Y_point) = 1 := by
    unfold mu_sigmaV mu_Y mu_sigmaY; norm_num [ L2_V, L2_Y, L3_sigma_V, L3_sigma_Y, L4_Y, L4_sigma_Y ] ;
    rw [ div_self, div_self, div_self ] <;> norm_num [ L3_Y_neg, L4_sigma_V_neg, sep_sigma_Y_pos, sep_Y, sep_sigma_V ];
    · exact ne_of_gt ( by exact sep_sigma_Y_pos );
    · exact ne_of_lt ( L3_Y_neg );
    · exact ne_of_lt ( L4_sigma_V_neg )

/-
We simplify the value of `L4` at `sigma V_point`.
-/
lemma val_L4_sigma_V : L4 (sigma V_point) = V_point 0 + V_point 1 - 1 - y1 := by
  unfold L4 sigma; ring!

/-
We simplify the value of `L3` at `Y_point`.
-/
lemma val_L3_Y : L3 Y_point = y1^2 - x1 * y1 + x1 - 1 := by
  unfold L3 Y_point; ring_nf;
  erw [ Matrix.cons_val_succ' ] ; norm_num ; ring

/-
We factor `L3 Y_point`.
-/
lemma L3_Y_factored : L3 Y_point = (y1 - 1) * (y1 + 1 - x1) := by
  rw [ val_L3_Y ] ; ring

/-
We prove an algebraic identity relating `x1`, `y1`, and `V_point` that is crucial for showing the coefficient of `p0` vanishes.
-/
lemma algebraic_identity_for_p0_coeff :
  (1 - V_point 0) * (y1 + 1 - x1) = (1 - x1) * (y1 - (V_point 0 + V_point 1 - 1)) := by
    -- By definition of y1, we have y1 * (V_point 0 - x1) = V_point 1 * (1 - x1).
    have h_y1_def : y1 * (V_point 0 - x1) = V_point 1 * (1 - x1) := by
      exact y1_relation
    generalize_proofs at *; (
    linarith! [ h_y1_def ] ;)

/-
We prove that the numerator of the coefficient of `p0` is zero, using the previously established algebraic identity.
-/
lemma numerator_p0_coeff_eq_zero :
  -(y1 - 1) * (y1 + 1 - x1) + (x1 - 1) * (y1 - (V_point 0 + V_point 1 - 1)) + (y1 - V_point 0) * (y1 + 1 - x1) = 0 := by
    have h_algebraic_identity : (1 - V_point 0) * (y1 + 1 - x1) = (1 - x1) * (y1 - (V_point 0 + V_point 1 - 1)) := by
      exact algebraic_identity_for_p0_coeff;
    grind

/-
The value of `L4` at `sigma V_point` is non-zero.
-/
lemma L4_sigma_V_ne_zero : L4 (sigma V_point) ≠ 0 := by
  rw [val_L4_sigma_V]
  have h : V_point 0 + V_point 1 - 1 < y1 := root1_lt_y1
  linarith

/-
We rewrite the values of `L4`, `L3`, and `sep` in forms convenient for finding a common denominator.
-/
lemma L4_sigma_V_eq_neg_root_diff : L4 (sigma V_point) = -(y1 - (V_point 0 + V_point 1 - 1)) := by
  rw [val_L4_sigma_V]
  ring

lemma L3_Y_eq_neg_factored : L3 Y_point = -(1 - y1) * (y1 + 1 - x1) := by
  rw [L3_Y_factored]
  ring

lemma sep_sigma_Y_eq_factored : sep (sigma Y_point) = (y1 - (V_point 0 + V_point 1 - 1)) * (1 - y1) := by
  rw [sep_sigma_Y_eq_poly, poly_sep_aux_eq_factored]

/-
The coefficient of `p0` in the sum of barycentric coordinates for Region6b is zero.
-/
lemma mu_sum_p0_coeff_eq_zero :
  1 / L4 (sigma V_point) + (x1 - 1) / L3 Y_point - (y1 - V_point 0) / sep (sigma Y_point) = 0 := by
    have h_common_denom : L4 (sigma V_point) ≠ 0 ∧ L3 Y_point ≠ 0 ∧ sep (sigma Y_point) ≠ 0 := by
      exact ⟨ by linarith [ show L4 ( sigma V_point ) < 0 from L4_sigma_V_neg ], by linarith [ show L3 Y_point < 0 from L3_Y_neg ], by linarith [ show sep ( sigma Y_point ) > 0 from sep_sigma_Y_pos ] ⟩;
    -- Substitute the factored forms of L4, L3, and sep into the coefficients.
    have h_coeff_p0 : (-(y1 - 1) * (y1 + 1 - x1) + (x1 - 1) * (y1 - (V_point 0 + V_point 1 - 1)) + (y1 - V_point 0) * (y1 + 1 - x1)) = 0 := by
      convert numerator_p0_coeff_eq_zero using 1;
    rw [ div_add_div, div_sub_div, div_eq_iff ] <;> simp_all +decide [ sub_eq_iff_eq_add ];
    -- Substitute the factored forms of L4, L3, and sep into the equation.
    have h_subst : (- (1 - y1) * (y1 + 1 - x1) + (-(y1 - (V_point 0 + V_point 1 - 1))) * (x1 - 1)) * ((y1 - (V_point 0 + V_point 1 - 1)) * (1 - y1)) = (-(y1 - (V_point 0 + V_point 1 - 1))) * (-(1 - y1) * (y1 + 1 - x1)) * (y1 - V_point 0) := by
      linear_combination -h_coeff_p0 * ( y1 - ( V_point 0 + V_point 1 - 1 ) ) * ( 1 - y1 );
    convert h_subst using 1 <;> push_cast [ L3_Y_eq_neg_factored, L4_sigma_V_eq_neg_root_diff, sep_sigma_Y_eq_factored ] <;> ring

/-
The coefficient of `p1` in the sum of barycentric coordinates for Region6b is zero.
-/
lemma mu_sum_p1_coeff_eq_zero :
  1 / L4 (sigma V_point) + y1 / L3 Y_point + (1 - V_point 1) / sep (sigma Y_point) = 0 := by
    rw [ L4_sigma_V_eq_neg_root_diff, L3_Y_eq_neg_factored, sep_sigma_Y_eq_factored ];
    rw [ div_add_div, div_add_div, div_eq_iff ] <;> norm_num [ sub_eq_zero, mul_eq_zero, ne_of_gt ] at *;
    any_goals constructor <;> try linarith [ y1_bounds ];
    grind +ring [ y1_bounds, V_bounds, algebraic_identity_for_p0_coeff ];
    any_goals nlinarith [ y1_bounds, V_bounds, algebraic_identity_for_p0_coeff, root1_lt_y1 ];
    · refine' ⟨ _, _, _ ⟩ <;> try linarith [ y1_bounds, V_bounds ];
      · exact ne_of_lt ( by have := root1_lt_y1; norm_num at *; linarith );
      · unfold y1 x1;
        have := Classical.choose_spec exists_root_x1;
        unfold V_point;
        rw [ div_add_one, div_eq_iff ] <;> norm_num;
        · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), pow_pos ( sub_pos.mpr this.1 ) 2, pow_pos ( sub_pos.mpr this.1 ) 3, pow_pos ( sub_pos.mpr this.1 ) 4, pow_pos ( sub_pos.mpr this.1 ) 5, pow_pos ( sub_pos.mpr this.1 ) 6 ];
        · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
        · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
    · constructor;
      · exact ne_of_gt ( by linarith [ root1_lt_y1 ] );
      · exact ne_of_gt ( by linarith [ y1_bounds ] );
    · constructor <;> nlinarith [ V_bounds, y1_bounds, root1_lt_y1, L2_sigma_V_neg, L4_sigma_V_neg, L3_Y_neg, L1_Y_pos, L2_V, L3_sigma_V, L4_Y, L2_A0_pos, L3_sigma_A0_pos, L2_O_neg, L3_O_neg, L2_X, L3_sigma_X, L4_sigma_V_eq_neg_root_diff, L3_Y_eq_neg_factored, sep_sigma_Y_eq_factored ]

/-
We prove an algebraic identity relating `y1`, `x1`, and `V_point` that is crucial for showing the constant term of the barycentric sum is 1.
-/
lemma algebraic_identity_for_const_coeff :
  (y1 + 1 - x1) * (V_point 1 - y1 * V_point 0) + y1 * x1 * (y1 - (V_point 0 + V_point 1 - 1)) = 0 := by
    unfold y1 V_point;
    unfold x1;
    by_cases h : ( Real.sqrt 6 + Real.sqrt 2 ) / 4 - Classical.choose exists_root_x1 = 0 <;> simp_all +decide [ sub_eq_iff_eq_add ];
    · have := Classical.choose_spec exists_root_x1;
      norm_num [ ← h, poly_X ] at this ⊢; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ] ;
    · grind

/-
Barycentric coordinates for Region2.
-/
noncomputable def Region2_gamma (p : Point) : ℝ := -L_OV p / (x1 * V_point 1)

noncomputable def Region2_beta (p : Point) : ℝ := p 1 / V_point 1

noncomputable def Region2_alpha (p : Point) : ℝ := 1 - Region2_beta p - Region2_gamma p

/-
Any point p can be decomposed into a linear combination of O, V, X using the defined barycentric coordinates.
-/
lemma Region2_decomp (p : Point) : p = Region2_alpha p • O_point + Region2_beta p • V_point + Region2_gamma p • X_point := by
  unfold Region2_alpha Region2_beta Region2_gamma;
  ext i ; norm_num [ L_OV ] ; ring_nf;
  fin_cases i <;> norm_num [ O_point, X_point, V_point ] <;> ring_nf;
  · unfold x1; norm_num; ring_nf;
    field_simp;
    rw [ eq_div_iff ] <;> norm_num ; ring_nf
    generalize_proofs at *;
    · by_cases h : Classical.choose ‹∃ x : ℝ, 19 < x * 20 ∧ x * 25 < 24 ∧ poly_X x = 0› = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ; ring_nf!;
      · linarith [ Classical.choose_spec ‹∃ x : ℝ, 19 < x * 20 ∧ x * 25 < 24 ∧ poly_X x = 0› ];
      · ring;
    · exact sub_ne_zero_of_ne <| by norm_num;
  · grind

/-
The beta coordinate for Region2 is non-negative for points in the square.
-/
lemma Region2_beta_nonneg (p : Point) (hp : p ∈ Region_Square) : 0 ≤ Region2_beta p := by
  -- Since $p \in \text{Region\_Square}$, we have $p 1 \geq 0$ by definition of $\text{Region\_Square}$.
  have hp1_nonneg : 0 ≤ p 1 := by
    have h_def : p ∈ {p : Point | ∀ i, 0 < p i ∧ p i < 1} := by
      convert hp using 1;
      unfold Region_Square; ext; simp +decide [ Set.pi ] ;
      tauto
    exact le_of_lt ( h_def 1 |>.1 );
  exact div_nonneg hp1_nonneg ( show 0 ≤ V_point 1 by exact div_nonneg ( by norm_num ) ( by norm_num ) )

/-
The gamma coordinate for Region2 is non-negative if L_OV <= 0.
-/
lemma Region2_gamma_nonneg (p : Point) (hOV : L_OV p ≤ 0) : 0 ≤ Region2_gamma p := by
  apply div_nonneg (by
  exact neg_nonneg_of_nonpos hOV) (by
  -- Since $V_point 1$ is positive and $x1$ is positive, their product is positive.
  have h_pos : 0 < V_point 1 ∧ 0 < x1 := by
    -- Since $V_point 1 = \frac{1}{4}$ and $x1 = \frac{9526}{10001}$, both are positive.
    simp [V_point, x1];
    exact ⟨ by norm_num, by have := Classical.choose_spec exists_root_x1; exact this.1 |> fun h => by linarith ⟩;
  exact mul_nonneg h_pos.2.le h_pos.1.le)

/-
Identity relating L2 and Region2_alpha.
-/
lemma L2_eq_neg_x1_y1_mul_alpha (p : Point) : L2 p = -x1 * y1 * Region2_alpha p := by
  unfold L2 Region2_alpha Region2_beta Region2_gamma L_OV; ring_nf;
  -- By definition of y1 and V_point, we know that y1 * (V_point 0 - x1) = V_point 1 * (1 - x1).
  have h_y1_V_point : y1 * (V_point 0 - x1) = V_point 1 * (1 - x1) := by
    exact y1_relation;
  by_cases h : V_point 1 = 0 <;> by_cases h' : x1 = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
  · exact absurd h' ( by linarith [ x1_prop.1 ] );
  · unfold V_point at * ; norm_num at *;
    exact absurd h ( sub_ne_zero_of_ne ( by norm_num ) );
  · exact absurd h' ( by exact ne_of_gt ( show 0 < x1 from by exact lt_of_le_of_lt ( by norm_num ) ( x1_prop.1 ) ) );
  · grind

/-
The alpha coordinate for Region2 is non-negative if L2 <= 0.
-/
lemma Region2_alpha_nonneg (p : Point) (hL2 : L2 p ≤ 0) : 0 ≤ Region2_alpha p := by
  -- Substitute L2 p from L2_eq_neg_x1_y1_mul_alpha into the inequality L2 p ≤ 0.
  have h_sub : -x1 * y1 * Region2_alpha p ≤ 0 := by
    exact hL2.trans' ( by rw [ show L2 p = -x1 * y1 * Region2_alpha p from L2_eq_neg_x1_y1_mul_alpha p ] );
  exact le_of_not_gt fun h => by nlinarith [ show 0 < x1 * y1 by exact mul_pos ( by have := x1_prop; norm_num at this; linarith ) ( by have := y1_bounds; norm_num at this; linarith ) ] ;

/-
If a point satisfies the inequalities for Region2, it is in Region2.
-/
lemma Region2_of_ineq (p : Point) (hp : p ∈ Region_Square) (hL2 : L2 p < 0) (hOV : L_OV p ≤ 0) : p ∈ Region2 := by
  -- By definition of Region2, we need to show that p is in the convex hull of {O, V, X}.
  have h_convex : p ∈ convexHull ℝ {O_point, V_point, X_point} := by
    -- By definition of Region2, we need to show that p is a convex combination of O, V, and X.
    have h_convex : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • V_point + c • X_point := by
      use Region2_alpha p, Region2_beta p, Region2_gamma p
      generalize_proofs at *; exact ⟨by
      exact Region2_alpha_nonneg p hL2.le
      skip, by
        exact Region2_beta_nonneg p hp |> le_trans <| by norm_num;, by
        exact Region2_gamma_nonneg p hOV, by
        unfold Region2_alpha Region2_beta Region2_gamma; ring;, by
        exact Region2_decomp p⟩
      skip
      skip
    generalize_proofs at *; exact (by
    rcases h_convex with ⟨ a, b, c, ha, hb, hc, habc, rfl ⟩ ; rw [ convexHull_eq ] ; norm_num [ ha, hb, hc, habc ] ;
    refine' ⟨ Fin 3, { 0, 1, 2 }, fun i => if i = 0 then a else if i = 1 then b else c, _, _, fun i => if i = 0 then O_point else if i = 1 then V_point else X_point, _, _ ⟩ <;> simp +decide [ *, Fin.sum_univ_three, Finset.centerMass ];
    · linarith;
    · norm_num [ ← add_assoc, habc ]);
  grind

/-
Symmetry of the unit square under sigma.
-/
lemma sigma_mem_Region_Square_iff (p : Point) : sigma p ∈ Region_Square ↔ p ∈ Region_Square := by
  constructor <;> intro hp <;> unfold Region_Square at * <;> aesop

/-
L3 is the reflection of L2.
-/
lemma L3_eq_L2_sigma (p : Point) : L3 p = L2 (sigma p) := by
  ring!

/-
If a point satisfies the inequalities for Region3, it is in Region3.
-/
lemma Region3_of_ineq (p : Point) (hp : p ∈ Region_Square) (hL3 : L3 p < 0) (hOV : L_OV (sigma p) ≤ 0) : p ∈ Region3 := by
  -- Apply `mem_Region3_iff_sigma_mem_Region2` to translate the question about p and Region3 into a question about sigma p and Region2.
  apply (mem_Region3_iff_sigma_mem_Region2 p).mpr;
  apply Region2_of_ineq;
  · exact (sigma_mem_Region_Square_iff p).mpr hp;
  · linarith [ L3_eq_L2_sigma p ];
  · assumption

/-
Barycentric coordinates for Region1.
-/
noncomputable def Region1_denom : ℝ := (V_point 0)^2 - (V_point 1)^2

noncomputable def Region1_beta (p : Point) : ℝ := L_OV (sigma p) / Region1_denom

noncomputable def Region1_gamma (p : Point) : ℝ := L_OV p / Region1_denom

noncomputable def Region1_alpha (p : Point) : ℝ := 1 - Region1_beta p - Region1_gamma p

/-
The denominator for Region1 barycentric coordinates is positive.
-/
lemma Region1_denom_pos : Region1_denom > 0 := by
  exact sub_pos.mpr ( by rw [ sq, sq ] ; exact ( by have := V_bounds; norm_num [ V_point ] at this ⊢; nlinarith ) )

/-
Decomposition of a point using Region1 barycentric coordinates.
-/
lemma Region1_decomp (p : Point) : p = Region1_alpha p • O_point + Region1_beta p • V_point + Region1_gamma p • (sigma V_point) := by
  unfold Region1_alpha Region1_beta Region1_gamma; ext i; fin_cases i <;> norm_num <;> ring_nf;
  · unfold L_OV Region1_denom O_point V_point sigma; norm_num; ring_nf;
    grind;
  · unfold L_OV Region1_denom O_point V_point sigma; norm_num ; ring_nf;
    norm_num [ mul_assoc, mul_comm, mul_left_comm ];
    rfl

/-
Non-negativity of beta coordinate for Region1.
-/
lemma Region1_beta_nonneg (p : Point) (h : L_OV (sigma p) ≥ 0) : Region1_beta p ≥ 0 := by
  unfold Region1_beta; exact div_nonneg h ( by linarith [ Region1_denom_pos ] ) ;

/-
Non-negativity of gamma coordinate for Region1.
-/
lemma Region1_gamma_nonneg (p : Point) (h : L_OV p ≥ 0) : Region1_gamma p ≥ 0 := by
  exact div_nonneg h ( le_of_lt ( by exact Region1_denom_pos ) )

/-
Sum of beta and gamma coordinates for Region1.
-/
lemma Region1_beta_add_gamma (p : Point) : Region1_beta p + Region1_gamma p = (p 0 + p 1) / (V_point 0 + V_point 1) := by
  convert congr_arg ( fun x : ℝ => x / Region1_denom ) ( show L_OV ( sigma p ) + L_OV p = ( p 0 + p 1 ) * ( V_point 0 - V_point 1 ) by
                                                          unfold L_OV sigma; ring_nf;
                                                          ring! ) using 1;
  · unfold Region1_beta Region1_gamma; ring;
  · rw [ show Region1_denom = ( V_point 0 - V_point 1 ) * ( V_point 0 + V_point 1 ) by unfold Region1_denom; ring ] ; rw [ div_eq_div_iff ] <;> ring_nf <;> norm_num [ V_point ];
    · ring_nf ; norm_num;
    · ring_nf; norm_num

/-
Non-negativity of alpha coordinate for Region1.
-/
lemma Region1_alpha_nonneg (p : Point) (hL1 : L1 p ≤ 0) : Region1_alpha p ≥ 0 := by
  -- Since $p 0 + p 1 \leq V_point 0 + V_point 1$ and $V_point 0 + V_point 1 > 0$, we have $(p 0 + p 1) / (V_point 0 + V_point 1) \leq 1$.
  have h_frac_le_one : (p 0 + p 1) / (V_point 0 + V_point 1) ≤ 1 := by
    unfold L1 at hL1; rw [ div_le_iff₀ ] <;> linarith [ V_bounds ] ;
  exact sub_nonneg_of_le ( by linarith [ show Region1_beta p + Region1_gamma p = ( p 0 + p 1 ) / ( V_point 0 + V_point 1 ) from by
                                          convert Region1_beta_add_gamma p using 1 ] )

/-
If a point satisfies the inequalities for Region1, it is in Region1.
-/
lemma Region1_of_ineq (p : Point) (hp : p ∈ Region_Square) (hL1 : L1 p ≤ 0) (hOV : L_OV p ≥ 0) (hOVsigma : L_OV (sigma p) ≥ 0) : p ∈ Region1 := by
  -- Let's choose any point $p$ in the region defined by $L1 p \leq 0$, $L_OV p \geq 0$, and $L_OV (sigma p) \geq 0$.
  apply convexHull_sub_Region1_of_pos;
  · -- By definition of Region1, we know that p is a convex combination of O, V, and sigma V.
    have h_convex : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • V_point + c • sigma V_point := by
      use Region1_alpha p, Region1_beta p, Region1_gamma p;
      exact ⟨ Region1_alpha_nonneg p hL1, Region1_beta_nonneg p hOVsigma, Region1_gamma_nonneg p hOV, by unfold Region1_alpha; ring, Region1_decomp p ⟩;
    rcases h_convex with ⟨ a, b, c, ha, hb, hc, habc, rfl ⟩ ; rw [ convexHull_eq ] ; norm_num [ ha, hb, hc, habc ] ;
    refine' ⟨ Fin 3, { 0, 1, 2 }, fun i => if i = 0 then a else if i = 1 then b else c, _, _, fun i => if i = 0 then O_point else if i = 1 then V_point else sigma V_point, _, _ ⟩ <;> simp +decide [ *, Finset.centerMass ];
    · linarith;
    · norm_num [ ← add_assoc, habc ];
  · assumption

/-
The y-coordinate of V is less than the x-coordinate of V.
-/
lemma V_point_1_lt_V_point_0 : V_point 1 < V_point 0 := by
  exact div_lt_div_iff_of_pos_right ( by norm_num ) |>.2 ( by nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ] )

/-
Point p can be decomposed into a convex combination of V, sigma V, and Y using the lambda coordinates.
-/
lemma Region6a_decomp (p : Point) : p = lambda_V p • V_point + lambda_sigma_V p • (sigma V_point) + lambda_Y p • Y_point := by
  -- We'll use the fact that if the denominator is non-zero, we can simplify the expression.
  have h_denom : sep V_point * L2 (sigma V_point) * L1 Y_point ≠ 0 := by
    exact mul_ne_zero ( mul_ne_zero ( by linarith [ sep_V_neg ] ) ( by linarith [ L2_sigma_V_neg ] ) ) ( by linarith [ L1_Y_pos ] );
  simp_all +decide [ funext_iff, Fin.forall_fin_two ];
  ext i; have := lambda_sum_eq_one p; have := lambda_sum_p0_coeff_eq_zero; have := lambda_sum_p1_coeff_eq_zero; have := p0_coeff_p0; have := p1_coeff_p0; norm_num [ lambda_V, lambda_sigma_V, lambda_Y ] at *; ring_nf at *;
  fin_cases i <;> ring_nf!;
  · unfold sep L2 L1 at *; ring_nf at *;
    grind;
  · unfold sep L2 L1 at *;
    unfold sigma V_point Y_point at * ; norm_num at * ; ring_nf at *;
    grind

/-
The coefficient of p0 in the sum of mu coordinates is 0.
-/
lemma mu_sum_p0_coeff_eq_zero_proof :
  1 / L4 (sigma V_point) + (x1 - 1) / L3 Y_point - (y1 - V_point 0) / sep (sigma Y_point) = 0 := by
    -- Apply the lemma that states the equation holds.
    apply mu_sum_p0_coeff_eq_zero

/-
The coefficient of p1 in the sum of mu coordinates is 0.
-/
lemma mu_sum_p1_coeff_eq_zero_proof :
  1 / L4 (sigma V_point) + y1 / L3 Y_point + (1 - V_point 1) / sep (sigma Y_point) = 0 := by
    convert mu_sum_p1_coeff_eq_zero using 1

/-
The sum of the barycentric coordinates for Region6b is 1 for any point p.
-/
lemma mu_sum_eq_one (p : Point) : mu_sigmaV p + mu_Y p + mu_sigmaY p = 1 := by
  have h_sum_const : ∀ p q : Point, (mu_sigmaV p + mu_Y p + mu_sigmaY p) - (mu_sigmaV q + mu_Y q + mu_sigmaY q) = (p 0 - q 0) * (1 / L4 (sigma V_point) + (x1 - 1) / L3 Y_point - (y1 - V_point 0) / sep (sigma Y_point)) + (p 1 - q 1) * (1 / L4 (sigma V_point) + y1 / L3 Y_point + (1 - V_point 1) / sep (sigma Y_point)) := by
    intros p q
    simp [mu_sigmaV, mu_Y, mu_sigmaY];
    unfold L4 L3 sep; ring;
  have h_sum_const : ∀ p q : Point, (mu_sigmaV p + mu_Y p + mu_sigmaY p) = (mu_sigmaV q + mu_Y q + mu_sigmaY q) := by
    intros p q; specialize h_sum_const p q; rw [ mu_sum_p0_coeff_eq_zero_proof, mu_sum_p1_coeff_eq_zero_proof ] at h_sum_const; linarith;
  convert h_sum_const p ( sigma V_point ) using 1 ; norm_num [ mu_values ]

/-
Algebraic identity for the coefficient of p0 in the x-coordinate of Region6b decomposition.
-/
lemma Region6b_coeff_p0_x_identity : (y1 + 1 - x1) * (V_point 0 - 1) + (1 - x1) * (y1 - V_point 0 - V_point 1 + 1) = 0 := by
  unfold V_point;
  unfold y1; ring_nf;
  field_simp;
  rw [ div_add', div_eq_iff ] <;> norm_num [ V_point ] ; ring_nf ;
  · unfold x1;
    have := Classical.choose_spec exists_root_x1;
    nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
  · unfold x1;
    have := Classical.choose_spec exists_root_x1;
    nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ]

/-
Algebraic identity for the coefficient of p1 in the x-coordinate of Region6b decomposition.
-/
lemma Region6b_coeff_p1_x_identity : (y1 + 1 - x1) * (V_point 1 - y1) + y1 * (y1 - V_point 0 - V_point 1 + 1) = 0 := by
  have := y1_relation;
  nlinarith

/-
The coefficient of p0 in the x-coordinate of the barycentric decomposition for Region6b is 1.
-/
lemma Region6b_coeff_p0_x : (1 / L4 (sigma V_point)) * (sigma V_point 0) + (-(1 - x1) / L3 Y_point) * Y_point 0 + (-(y1 - V_point 0) / sep (sigma Y_point)) * (sigma Y_point 0) = 1 := by
  field_simp;
  have hL4_sigma_V_eq_neg_root_diff : L4 (sigma V_point) = -(y1 - (V_point 0 + V_point 1 - 1)) := by
    unfold L4 sigma V_point; norm_num; ring;
  have hL3_Y_eq_neg_factored : L3 Y_point = -(1 - y1) * (y1 + 1 - x1) := by
    convert L3_Y_eq_neg_factored using 1
  have hsep_sigma_Y_eq_factored : sep (sigma Y_point) = (y1 - (V_point 0 + V_point 1 - 1)) * (1 - y1) := by
    convert sep_sigma_Y_eq_factored using 1;
  have hnum_eq_zero : (y1 + 1 - x1) * (V_point 0 - 1) + (1 - x1) * (y1 - V_point 0 - V_point 1 + 1) = 0 := by
    convert Region6b_coeff_p0_x_identity using 1;
  have hL4_sigma_V_ne_zero : L4 (sigma V_point) ≠ 0 := by
    apply L4_sigma_V_ne_zero
  have hL3_Y_ne_zero : L3 Y_point ≠ 0 := by
    have hL3_Y_pos : L3 Y_point < 0 := by
      exact L3_Y_neg;
    linarith
  have hsep_sigma_Y_ne_zero : sep (sigma Y_point) ≠ 0 := by
    grind;
  simp_all +decide [ sub_eq_iff_eq_add ];
  rw [ div_add', div_add', div_eq_iff ];
  · unfold sigma Y_point; norm_num; ring_nf;
    grind;
  · exact fun h => hL4_sigma_V_ne_zero <| by linarith;
  · exact fun h => hL4_sigma_V_ne_zero <| by linarith;
  · exact fun h => hL4_sigma_V_ne_zero <| by linarith;

/-
Points in the square with L2 >= 0 are in UnionRegions.
-/
lemma Cover_Part1 : ∀ p ∈ Region_Square, L2 p ≥ 0 → p ∈ UnionRegions := by
  intro p hp hL2
  have hRegion4 : p ∈ Region4 := by
    -- Apply the lemma that states if L2 p ≥ 0, then p is in Region4.
    apply Region4_contains_L2_ge_0 p hp hL2
  have hUnion : p ∈ UnionRegions := by
    simp [UnionRegions, hRegion4]
  exact hUnion

/-
Points in the square with L3 >= 0 are in UnionRegions.
-/
lemma Cover_Part2 : ∀ p ∈ Region_Square, L3 p ≥ 0 → p ∈ UnionRegions := by
  intros p hp hL3
  have hRegion5 : p ∈ Region5 := by
    apply Region5_contains_L3_ge_0 p hp hL3
    skip -- This should not be reachable, as the proof should be complete. p hp hL3
  exact (by
  unfold UnionRegions; aesop;)
  skip

/-
Points in the square with L4 >= 0 are in UnionRegions.
-/
lemma Cover_Part3 : ∀ p ∈ Region_Square, L4 p ≥ 0 → p ∈ UnionRegions := by
  intros p hp hL4;
  -- Apply the lemma that states if L4 p ≥ 0, then p is in Region_Corner.
  have h_region : p ∈ Region_Corner := by
    apply Region_Corner_contains_L4_ge_0 p hp hL4;
  exact Or.inr h_region

/-
Points in the square with L2 < 0, L3 < 0, L1 <= 0 are in UnionRegions.
-/
lemma Cover_Part4a : ∀ p ∈ Region_Square, L2 p < 0 → L3 p < 0 → L1 p ≤ 0 → p ∈ UnionRegions := by
  intros p hp hL2 hL3 hL1
  by_cases hL3 : L3 p < 0 ∧ L_OV p ≤ 0 ∨ L2 p < 0 ∧ L_OV (sigma p) ≤ 0 ∨ L1 p ≤ 0 ∧ L_OV p ≥ 0 ∧ L_OV (sigma p) ≥ 0
  generalize_proofs at *;
  · cases' hL3 with hL3 hL3 <;> simp_all +decide [ UnionRegions ];
    · exact Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inr <| Region2_of_ineq p hp hL2 hL3.2;
    · cases' hL3 with hL3 hL3 <;> simp_all +decide [ Region2_of_ineq, Region3_of_ineq, Region1_of_ineq ];
  · grind

/-
Points satisfying the inequalities for Region6a are in Region6a.
-/
lemma Cover_Part4b_Region6a : ∀ p ∈ Region_Square, L2 p < 0 → L3 p < 0 → L4 p < 0 → L1 p ≥ 0 → sep p ≤ 0 → p ∈ Region6a := by
  intros p hp_mem hpL2 hpL3 hpL4 hpL1 hpsep
  have hp_coeffs : 0 ≤ lambda_V p ∧ 0 ≤ lambda_sigma_V p ∧ 0 ≤ lambda_Y p ∧ lambda_V p + lambda_sigma_V p + lambda_Y p = 1 := by
    refine' ⟨ _, _, _, _ ⟩
    all_goals generalize_proofs at *;
    · exact div_nonneg_of_nonpos hpsep ( by linarith [ sep_V_neg ] );
    · exact div_nonneg_of_nonpos ( by linarith ) ( by linarith [ L2_sigma_V_neg ] );
    · exact div_nonneg hpL1 ( by linarith [ L1_Y_pos ] );
    · exact lambda_sum_eq_one p;
  rw [ show p = lambda_V p • V_point + lambda_sigma_V p • ( sigma V_point ) + lambda_Y p • Y_point from ?_ ];
  · rw [ show Region6a = convexHull ℝ { V_point, sigma V_point, Y_point } from ?_ ];
    · rw [ convexHull_eq ];
      refine' ⟨ Fin 3, { 0, 1, 2 }, fun i => if i = 0 then lambda_V p else if i = 1 then lambda_sigma_V p else lambda_Y p, fun i => if i = 0 then V_point else if i = 1 then sigma V_point else Y_point, _, _, _, _ ⟩ <;> simp +decide [ *, Fin.sum_univ_three, Finset.centerMass ];
      · linarith;
      · norm_num [ ← add_assoc, hp_coeffs.2.2.2 ];
    · exact rfl;
  · convert Region6a_decomp p using 1

/-
The value of sep at sigma Y is related to the value of L4 at sigma V by a factor of -(1-y1).
-/
lemma relation_sep_L4 : sep (sigma Y_point) = -L4 (sigma V_point) * (1 - y1) := by
  rw [ sep_sigma_Y_eq_factored, L4_sigma_V_eq_neg_root_diff ] ; ring

/-
The sum of the first and third terms in the p1 coefficient expression simplifies to a single fraction.
-/
lemma Region6b_p1_term13_simp : (1 / L4 (sigma V_point)) * (sigma V_point 0) + ((1 - V_point 1) / sep (sigma Y_point)) * (sigma Y_point 0) = (V_point 1 - y1) / (L4 (sigma V_point) * (1 - y1)) := by
  -- Substitute the known values of sigma V_point 0 and sigma Y_point 0 into the first two terms.
  have h_sub : 1 / L4 (sigma V_point) * sigma V_point 0 + (1 - V_point 1) / sep (sigma Y_point) * sigma Y_point 0 = 1 / L4 (sigma V_point) * V_point 1 + (1 - V_point 1) / sep (sigma Y_point) * y1 := by
    rfl;
  -- Substitute the known value of sep (sigma Y_point) into the expression.
  have h_sep : sep (sigma Y_point) = -L4 (sigma V_point) * (1 - y1) := by
    convert relation_sep_L4 using 1;
  by_cases h : L4 ( sigma V_point ) = 0 <;> by_cases h' : 1 - y1 = 0 <;> simp_all +decide [ division_def, mul_assoc, mul_comm, mul_left_comm ];
  · exact absurd h' ( by linarith [ show y1 < 1 from by linarith [ y1_bounds.1, y1_bounds.2 ] ] );
  · field_simp [h, h']
    ring

/-
A simplified algebraic identity involving V_point, y1, and x1 holds.
-/
lemma Region6b_coeff_p1_x_simplified : (V_point 1 - y1) / (y1 - (V_point 0 + V_point 1 - 1)) + y1 / (y1 + 1 - x1) = 0 := by
  convert congr_arg ( fun x : ℝ => x / ( ( y1 - ( V_point 0 + V_point 1 - 1 ) ) * ( y1 + 1 - x1 ) ) ) ( Region6b_coeff_p1_x_identity ) using 1;
  · rw [ div_add_div ] <;> ring_nf <;> nlinarith [ y1_bounds, root1_lt_y1, x1_prop ];
  · ring

/-
The core expression for the p1 coefficient is zero.
-/
lemma Region6b_coeff_p1_x_core : (V_point 1 - y1) / (L4 (sigma V_point) * (1 - y1)) + y1 / L3 Y_point = 0 := by
  -- Substitute the factored forms of L4 (sigma V_point) and L3 Y_point into the expression.
  have h_subst : (V_point 1 - y1) / (-(y1 - (V_point 0 + V_point 1 - 1)) * (1 - y1)) + y1 / (-(1 - y1) * (y1 + 1 - x1)) = 0 := by
    convert congr_arg ( fun x : ℝ => x * ( -1 / ( 1 - y1 ) ) ) ( Region6b_coeff_p1_x_simplified ) using 1 ; ring_nf;
    · grind;
    · ring;
  convert h_subst using 3 <;> norm_num [ L4_sigma_V_eq_neg_root_diff, L3_Y_eq_neg_factored ]

/-
The coefficient of p1 in the x-coordinate decomposition for Region6b is zero.
-/
lemma Region6b_coeff_p1_x : (1 / L4 (sigma V_point)) * (sigma V_point 0) + (y1 / L3 Y_point) * Y_point 0 + ((1 - V_point 1) / sep (sigma Y_point)) * (sigma Y_point 0) = 0 := by
  convert Region6b_coeff_p1_x_core using 1;
  rw [ ← Region6b_p1_term13_simp ] ; ring_nf;
  unfold Y_point; norm_num;

/-
The sum of the first and third terms in the constant coefficient expression simplifies to a single fraction.
-/
lemma Region6b_const_term13_simp : (-(1 + y1) / L4 (sigma V_point)) * (sigma V_point 0) + ((-(1 - V_point 1) * V_point 0 + (y1 - V_point 0) * V_point 1) / sep (sigma Y_point)) * (sigma Y_point 0) = (V_point 1 - y1 * V_point 0) / (-L4 (sigma V_point) * (1 - y1)) := by
  -- Substitute `sigma V_point 0 = V_point 1` and `sigma Y_point 0 = y1`.
  have h_subst : sigma V_point 0 = V_point 1 ∧ sigma Y_point 0 = y1 := by
    exact ⟨ rfl, rfl ⟩;
  rw [ show sep ( sigma Y_point ) = -L4 ( sigma V_point ) * ( 1 - y1 ) by
        exact relation_sep_L4 ] ; ring_nf;
  rw [ show L4 ( sigma V_point ) = - ( y1 - ( V_point 0 + V_point 1 - 1 ) ) by
        exact L4_sigma_V_eq_neg_root_diff ] ; ring_nf;
  rw [ show ( -1 - y1 + V_point 0 + V_point 1 ) = ( 1 + y1 * V_point 0 + ( y1 * V_point 1 - y1 ^ 2 ) + ( -V_point 0 - V_point 1 ) ) / ( - ( 1 - y1 ) ) by rw [ eq_div_iff ] <;> nlinarith [ y1_bounds, V_bounds ] ] ; norm_num ; ring_nf;
  rw [ h_subst.1, h_subst.2 ] ; ring;

/-
An algebraic identity involving V_point, y1, and x1 holds.
-/
lemma Region6b_coeff_const_x_identity : (y1 + 1 - x1) * (V_point 1 - y1 * V_point 0) + y1 * x1 * (y1 - (V_point 0 + V_point 1 - 1)) = 0 := by
  convert algebraic_identity_for_const_coeff using 1

/-
A simplified algebraic identity involving V_point, y1, and x1 holds.
-/
lemma Region6b_coeff_const_x_simplified : (V_point 1 - y1 * V_point 0) / (y1 - (V_point 0 + V_point 1 - 1)) + y1 * x1 / (y1 + 1 - x1) = 0 := by
  convert congr_arg ( fun x : ℝ => x / ( ( y1 - ( V_point 0 + V_point 1 - 1 ) ) * ( y1 + 1 - x1 ) ) ) ( Region6b_coeff_const_x_identity ) using 1;
  · rw [ div_add_div ];
    · ring;
    · exact sub_ne_zero_of_ne ( by linarith [ root1_lt_y1 ] );
    · linarith [ y1_bounds.1, y1_bounds.2, x1_prop.1, x1_prop.2.1 ];
  · ring

/-
The constant term in the x-coordinate decomposition for Region6b is zero.
-/
lemma Region6b_coeff_const_x : (-(1 + y1) / L4 (sigma V_point)) * (sigma V_point 0) + (-y1 * x1 / L3 Y_point) * Y_point 0 + ((-(1 - V_point 1) * V_point 0 + (y1 - V_point 0) * V_point 1) / sep (sigma Y_point)) * (sigma Y_point 0) = 0 := by
  -- Substitute the known values of the coefficients into the expression.
  have h_subst : (V_point 1 - y1 * V_point 0) / (-L4 (sigma V_point) * (1 - y1)) + (-y1 * x1) / (-(1 - y1) * (y1 + 1 - x1)) = 0 := by
    have h_subst : (V_point 1 - y1 * V_point 0) / (y1 - (V_point 0 + V_point 1 - 1)) + y1 * x1 / (y1 + 1 - x1) = 0 := by
      convert Region6b_coeff_const_x_simplified using 1;
    field_simp;
    convert congr_arg ( fun x : ℝ => x / ( 1 - y1 ) ) h_subst using 1 ; ring_nf;
    · rw [ show L4 ( sigma V_point ) = - ( y1 - ( V_point 0 + V_point 1 - 1 ) ) by exact
      L4_sigma_V_eq_neg_root_diff ] ; ring_nf;
      rw [ show ( -1 + ( V_point 1 - y1 ) + V_point 0 ) = - ( 1 - V_point 1 + ( y1 - V_point 0 ) ) by ring, inv_neg ] ; ring;
    · norm_num;
  rw [ ← h_subst, L3_Y_eq_neg_factored ];
  convert congr_arg ( fun x : ℝ => x + -y1 * x1 / ( - ( 1 - y1 ) * ( y1 + 1 - x1 ) ) ) ( Region6b_const_term13_simp ) using 1 ; ring_nf!;
  norm_num [ Y_point ]

/-
The x-coordinate of p can be decomposed into the weighted sum of the x-coordinates of the vertices sigma V, Y, sigma Y.
-/
lemma Region6b_decomp_x (p : Point) : p 0 = mu_sigmaV p * (sigma V_point) 0 + mu_Y p * Y_point 0 + mu_sigmaY p * (sigma Y_point) 0 := by
  have h_coeff_p0 : (1 / L4 (sigma V_point)) * (sigma V_point 0) + (-(1 - x1) / L3 Y_point) * Y_point 0 + (-(y1 - V_point 0) / sep (sigma Y_point)) * (sigma Y_point 0) = 1 := by
    convert Region6b_coeff_p0_x using 1;
  have h_coeff_p1 : (1 / L4 (sigma V_point)) * (sigma V_point 0) + (y1 / L3 Y_point) * Y_point 0 + ((1 - V_point 1) / sep (sigma Y_point)) * (sigma Y_point 0) = 0 := by
    convert Region6b_coeff_p1_x using 1;
  have h_coeff_const : (-(1 + y1) / L4 (sigma V_point)) * (sigma V_point 0) + (-y1 * x1 / L3 Y_point) * Y_point 0 + ((-(1 - V_point 1) * V_point 0 + (y1 - V_point 0) * V_point 1) / sep (sigma Y_point)) * (sigma Y_point 0) = 0 := by
    convert Region6b_coeff_const_x using 1;
  unfold mu_sigmaV mu_Y mu_sigmaY at *;
  unfold L4 L3 sep at *;
  linear_combination -h_coeff_const - h_coeff_p1 * p 1 - h_coeff_p0 * p 0

/-
The coefficient of p0 in the y-coordinate decomposition for Region6b is zero.
-/
lemma Region6b_coeff_p0_y : (1 / L4 (sigma V_point)) * (sigma V_point 1) + (-(1 - x1) / L3 Y_point) * Y_point 1 + (-(y1 - V_point 0) / sep (sigma Y_point)) * (sigma Y_point 1) = 0 := by
  -- Substitute the definitions of `L4`, `L3`, and `sep` into the coefficients.
  have h_sub : (1 / L4 (sigma V_point)) + (-(1 - x1) / L3 Y_point) + (-(y1 - V_point 0) / sep (sigma Y_point)) = 0 := by
    convert mu_sum_p0_coeff_eq_zero using 1;
    ring;
  convert congr_arg ( · * y1 ) h_sub using 1 <;> ring_nf;
  rw [ show sigma V_point 1 = V_point 0 from rfl, show Y_point 1 = y1 from rfl, show sigma Y_point 1 = 1 from rfl ] ; ring_nf;
  rw [ show sep ( sigma Y_point ) = -L4 ( sigma V_point ) * ( 1 - y1 ) from ?_ ] ; ring_nf;
  · rw [ show -L4 ( sigma V_point ) + L4 ( sigma V_point ) * y1 = L4 ( sigma V_point ) * ( -1 + y1 ) by ring ] ; norm_num ; ring_nf;
    nlinarith [ inv_mul_cancel_left₀ ( show -1 + y1 ≠ 0 by linarith [ y1_bounds ] ) ( ( L4 ( sigma V_point ) ) ⁻¹ * y1 ), inv_mul_cancel_left₀ ( show -1 + y1 ≠ 0 by linarith [ y1_bounds ] ) ( ( L4 ( sigma V_point ) ) ⁻¹ * V_point 0 ) ];
  · field_simp;
    rw [ relation_sep_L4 ] ; ring

/-
The sum of the first and third terms in the p1 coefficient expression for y simplifies to a single fraction.
-/
lemma Region6b_p1_y_term13_simp : (1 / L4 (sigma V_point)) * V_point 0 + ((1 - V_point 1) / sep (sigma Y_point)) * 1 = (V_point 0 * (1 - y1) - (1 - V_point 1)) / (L4 (sigma V_point) * (1 - y1)) := by
  field_simp;
  rw [ div_add_div ];
  · rw [ show sep ( sigma Y_point ) = -L4 ( sigma V_point ) * ( 1 - y1 ) by exact relation_sep_L4 ] ; ring_nf;
    rw [ show -L4 ( sigma V_point ) ^ 2 + L4 ( sigma V_point ) ^ 2 * y1 = L4 ( sigma V_point ) * ( L4 ( sigma V_point ) - L4 ( sigma V_point ) * y1 ) * -1 by ring ] ; norm_num ; ring_nf;
    by_cases h : L4 ( sigma V_point ) = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
  · exact L4_sigma_V_ne_zero;
  · linarith [ sep_sigma_Y_pos ]

/-
A simplified algebraic identity involving V_point, y1, and x1 holds.
-/
lemma Region6b_coeff_p1_y_simplified : (V_point 0 * (1 - y1) - (1 - V_point 1)) / (y1 - (V_point 0 + V_point 1 - 1)) + y1^2 / (y1 + 1 - x1) - (y1 - 1) = 0 := by
  rw [ div_add_div, div_sub', div_eq_iff ];
  · unfold V_point y1 x1; ring_nf;
    unfold V_point; norm_num; ring_nf;
    grind;
  · exact mul_ne_zero ( by linarith [ root1_lt_y1 ] ) ( by linarith [ x1_prop.1, x1_prop.2.1, y1_bounds ] );
  · exact mul_ne_zero ( by linarith [ root1_lt_y1 ] ) ( by linarith [ x1_prop.1, x1_prop.2.1, y1_bounds ] );
  · exact sub_ne_zero_of_ne ( by linarith [ root1_lt_y1 ] );
  · exact ne_of_gt ( by linarith [ x1_prop, y1_bounds ] )

/-
The core expression for the p1 coefficient in y is 1.
-/
lemma Region6b_coeff_p1_y_core : (V_point 0 * (1 - y1) - (1 - V_point 1)) / (L4 (sigma V_point) * (1 - y1)) + y1^2 / L3 Y_point = 1 := by
  have h_sub : (V_point 0 * (1 - y1) - (1 - V_point 1)) / (-(y1 - (V_point 0 + V_point 1 - 1)) * (1 - y1)) + y1^2 / (-(1 - y1) * (y1 + 1 - x1)) = 1 := by
    have h_simp : (V_point 0 * (1 - y1) - (1 - V_point 1)) / (y1 - (V_point 0 + V_point 1 - 1)) + y1^2 / (y1 + 1 - x1) = y1 - 1 := by
      have h_simp : (V_point 0 * (1 - y1) - (1 - V_point 1)) / (y1 - (V_point 0 + V_point 1 - 1)) + y1^2 / (y1 + 1 - x1) - (y1 - 1) = 0 := by
        convert Region6b_coeff_p1_y_simplified using 1;
      exact eq_of_sub_eq_zero h_simp ▸ rfl;
    convert congr_arg ( fun x : ℝ => x / ( - ( 1 - y1 ) ) ) h_simp using 1 <;> ring_nf;
    · rw [ show ( -1 + V_point 0 + ( - ( V_point 0 * y1 ) - y1 * V_point 1 ) + y1 ^ 2 + V_point 1 ) = ( 1 - V_point 0 + ( y1 - V_point 1 ) ) * ( -1 + y1 ) by ring, show ( -1 - y1 * x1 + y1 ^ 2 + x1 ) = ( 1 + ( y1 - x1 ) ) * ( -1 + y1 ) by ring ] ; norm_num ; ring;
    · linarith [ inv_mul_cancel₀ ( show -1 + y1 ≠ 0 by linarith [ y1_bounds ] ) ];
  convert h_sub using 2 <;> norm_num [ L4_sigma_V_eq_neg_root_diff, L3_Y_eq_neg_factored ]

/-
The coefficient of p1 in the y-coordinate decomposition for Region6b is 1.
-/
lemma Region6b_coeff_p1_y : (1 / L4 (sigma V_point)) * (sigma V_point 1) + (y1 / L3 Y_point) * Y_point 1 + ((1 - V_point 1) / sep (sigma Y_point)) * (sigma Y_point 1) = 1 := by
  -- Apply the lemma's result directly to conclude the proof.
  convert Region6b_coeff_p1_y_core using 1;
  rw [ ← Region6b_p1_y_term13_simp ];
  unfold sigma; norm_num; ring_nf;
  unfold Y_point; norm_num; ring;

/-
The sum of the first and third terms in the constant coefficient expression for y simplifies to a single fraction.
-/
lemma Region6b_const_y_term13_simp : (-(1 + y1) / L4 (sigma V_point)) * V_point 0 + ((-(1 - V_point 1) * V_point 0 + (y1 - V_point 0) * V_point 1) / sep (sigma Y_point)) * 1 = y1 * (V_point 1 - y1 * V_point 0) / (-L4 (sigma V_point) * (1 - y1)) := by
  rw [ show sep ( sigma Y_point ) = -L4 ( sigma V_point ) * ( 1 - y1 ) by exact relation_sep_L4 ] ; ring_nf;
  field_simp;
  rw [ ← mul_div_mul_left _ _ ( by nlinarith [ y1_bounds ] : ( -1 + y1 ) ≠ 0 ) ] ; ring_nf;
  grind

/-
The constant term in the y-coordinate decomposition for Region6b is zero.
-/
lemma Region6b_coeff_const_y : (-(1 + y1) / L4 (sigma V_point)) * (sigma V_point 1) + (-y1 * x1 / L3 Y_point) * Y_point 1 + ((-(1 - V_point 1) * V_point 0 + (y1 - V_point 0) * V_point 1) / sep (sigma Y_point)) * (sigma Y_point 1) = 0 := by
  have h_common_denom : y1 * (V_point 1 - y1 * V_point 0) / (-L4 (sigma V_point) * (1 - y1)) + (-y1 * x1 / L3 Y_point) * y1 = 0 := by
    convert congr_arg ( fun x : ℝ => x * y1 / ( 1 - y1 ) ) ( Region6b_coeff_const_x_simplified ) using 1 <;> ring_nf;
    rw [ show L4 ( sigma V_point ) = - ( y1 - ( V_point 0 + V_point 1 - 1 ) ) by exact
      L4_sigma_V_eq_neg_root_diff ] ; rw [ show L3 Y_point = - ( 1 - y1 ) * ( y1 + 1 - x1 ) by exact
      L3_Y_eq_neg_factored ] ; ring_nf;
    rw [ show ( 1 + y1 * V_point 1 + ( y1 * V_point 0 - y1 ^ 2 ) + ( -V_point 1 - V_point 0 ) ) = ( 1 + y1 + ( -V_point 1 - V_point 0 ) ) * ( 1 - y1 ) by ring ] ; norm_num ; ring_nf;
    grind;
  rw [ ← h_common_denom ];
  rw [ ← Region6b_const_y_term13_simp ] ; ring_nf!;
  erw [ show sigma Y_point 1 = 1 from rfl ] ; ring!;

/-
If a point in the square satisfies L2 < 0, L3 < 0, L4 < 0, and sep >= 0, it is in Region6b.
-/
lemma Cover_Part4b_Region6b : ∀ p ∈ Region_Square, L2 p < 0 → L3 p < 0 → L4 p < 0 → sep p ≥ 0 → p ∈ Region6b := by
  -- By definition of $p$ being in $Region6b$, we need to show that $p$ can be written as a convex combination of $\sigma V$, $Y$, and $\sigma Y$ with non-negative weights.
  intro p hp hL2 hL3 hL4 hsep
  have h_convex : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • sigma V_point + b • Y_point + c • sigma Y_point := by
    use mu_sigmaV p, mu_Y p, mu_sigmaY p;
    have h_mu_nonneg : 0 ≤ mu_sigmaV p ∧ 0 ≤ mu_Y p ∧ 0 ≤ mu_sigmaY p := by
      have h_L4_sigma_V_neg : L4 (sigma V_point) < 0 := by
        convert L4_sigma_V_neg
      have h_L3_Y_neg : L3 Y_point < 0 := by
        convert L3_Y_neg using 1
      have h_sep_sigma_Y_pos : sep (sigma Y_point) > 0 := by
        exact sep_sigma_Y_pos;
      exact ⟨ div_nonneg_of_nonpos hL4.le h_L4_sigma_V_neg.le, div_nonneg_of_nonpos hL3.le h_L3_Y_neg.le, div_nonneg hsep h_sep_sigma_Y_pos.le ⟩;
    have h_mu_sum : mu_sigmaV p + mu_Y p + mu_sigmaY p = 1 := by
      exact mu_sum_eq_one p;
    have h_mu_decomp : p 0 = mu_sigmaV p * (sigma V_point 0) + mu_Y p * Y_point 0 + mu_sigmaY p * (sigma Y_point 0) ∧ p 1 = mu_sigmaV p * (sigma V_point 1) + mu_Y p * Y_point 1 + mu_sigmaY p * (sigma Y_point 1) := by
      apply And.intro;
      · apply Region6b_decomp_x;
      · have h_mu_decomp_y : p 1 = mu_sigmaV p * (sigma V_point 1) + mu_Y p * Y_point 1 + mu_sigmaY p * (sigma Y_point 1) := by
          have := Region6b_coeff_p0_y
          have := Region6b_coeff_p1_y
          have := Region6b_coeff_const_y
          unfold mu_sigmaV mu_Y mu_sigmaY at *;
          unfold L4 L3 sep at *;
          grind;
        exact h_mu_decomp_y;
    exact ⟨ h_mu_nonneg.1, h_mu_nonneg.2.1, h_mu_nonneg.2.2, h_mu_sum, by ext i; fin_cases i <;> tauto ⟩;
  obtain ⟨ a, b, c, ha, hb, hc, habc, rfl ⟩ := h_convex; ( rw [ show Region6b = convexHull ℝ { sigma V_point, Y_point, sigma Y_point } from rfl ] ; );
  rw [ convexHull_eq ];
  refine' ⟨ _, { 0, 1, 2 }, fun i => if i = 0 then a else if i = 1 then b else c, fun i => if i = 0 then sigma V_point else if i = 1 then Y_point else sigma Y_point, _, _, _, _ ⟩ <;> simp +decide [ *, Finset.centerMass ];
  · linarith;
  · norm_num [ ← add_assoc, habc ]

/-
If a point in the square satisfies L2 < 0, L3 < 0, and L4 < 0, it is in UnionRegions.
-/
lemma Cover_Part4_Combined : ∀ p ∈ Region_Square, L2 p < 0 → L3 p < 0 → L4 p < 0 → p ∈ UnionRegions := by
  -- Let p be in Region_Square with L2 p < 0, L3 p < 0, L4 p < 0.
  intros p hp hL2 hL3 hL4
  by_cases hL1 : L1 p ≤ 0;
  · exact Cover_Part4a p hp hL2 hL3 hL1;
  · by_cases hsep : sep p ≤ 0 <;> simp_all +decide [ UnionRegions ];
    · exact Or.inl <| Or.inl <| Or.inr <| Cover_Part4b_Region6a p hp hL2 hL3 hL4 hL1.le hsep;
    · exact Or.inl <| Or.inr <| Cover_Part4b_Region6b p hp hL2 hL3 hL4 hsep.le

/-
The open unit square is contained in the union of the defined regions.
-/
lemma Region_Square_subset_UnionRegions : Region_Square ⊆ UnionRegions := by
  -- By definition of UnionRegions, we know that every point in the square is in one of the regions.
  intros p hp
  apply Classical.byContradiction
  intro h_not_in_union;
  -- By definition of UnionRegions, we know that every point in the square is in one of the regions. Hence, we can apply the disjunction elimination rule.
  apply Classical.byContradiction
  intro h_not_in_union;
  rename_i h_not_in_union'; exact h_not_in_union' <| if h : L2 p ≥ 0 then Cover_Part1 p hp h else if h' : L3 p ≥ 0 then Cover_Part2 p hp h' else if h'' : L4 p ≥ 0 then Cover_Part3 p hp h'' else Cover_Part4_Combined p hp ( lt_of_not_ge h ) ( lt_of_not_ge h' ) ( lt_of_not_ge h'' ) ;

/-
The intersection of Region1 and Region2 is the segment connecting O and V.
-/
lemma Region1_inter_Region2 : Region1 ∩ Region2 = segment ℝ O_point V_point := by
  -- To prove equality of sets �,� we show each � set� is a subset of the other.
  apply Set.ext
  intro p
  simp [Region1, Region2, segment];
  constructor <;> intro h;
  · -- By definition of convex hull, since $p$ is in the convex hull of $\{O, V, \sigma V\}$, there exist coefficients $a, b, c$ such that $a + b + c = 1$ and $p = aO + bV + c\sigma V$.
    obtain ⟨a, b, c, ha, hb, hc, habc⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • V_point + c • sigma V_point := by
      have h_convex_comb : p ∈ convexHull ℝ {O_point, V_point, sigma V_point} := by
        exact h.1;
      rw [ convexHull_insert ] at h_convex_comb;
      · norm_num [ segment_eq_image ] at h_convex_comb ⊢;
        rcases h_convex_comb with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, by linarith, x * ( 1 - i ), by nlinarith, x * i, by nlinarith, by ring, by ext ; simpa using by ring ⟩ ;
      · norm_num +zetaDelta at *;
    -- Since $p$ is in the convex hull of $\{O, V, X\}$, we have $L_OV p \leq 0$.
    have h_LOV_p_le_0 : L_OV p ≤ 0 := by
      have h_LOV_p_le_0 : ∀ p ∈ convexHull ℝ {O_point, V_point, X_point}, L_OV p ≤ 0 := by
        exact fun p a ↦ Region2_sub_H_neg p a
      generalize_proofs at *; exact h_LOV_p_le_0 p h.2;
    generalize_proofs at *; simp_all +decide [ L_OV ] ; (
    -- Since $c \geq 0$ and $L_OV(\sigma(V)) > 0$, we have $c = 0$.
    have hc_zero : c = 0 := by
      have h_LOV_sigma_V_pos : L_OV (sigma V_point) > 0 := by
        exact L_OV_sigmaV_pos
      generalize_proofs at *; simp_all +decide [ L_OV ] ; (
      unfold O_point V_point sigma at * ; norm_num at * ; nlinarith;)
    generalize_proofs at *; simp_all +decide [ L_OV ] ; (
    exact ⟨ a, ha, b, hb, habc.1, rfl ⟩));
  · rw [ @convexHull_insert ] <;> norm_num [ convexHull_insert ];
    rcases h with ⟨ a, ha, b, hb, hab, rfl ⟩ ; simp_all +decide [ segment_eq_image ] ;
    refine' ⟨ ⟨ 0, ⟨ by norm_num, by norm_num ⟩, b, ⟨ hb, by linarith ⟩, _ ⟩, ⟨ 0, ⟨ by norm_num, by norm_num ⟩, b, ⟨ hb, by linarith ⟩, _ ⟩ ⟩ <;> ext i <;> fin_cases i <;> norm_num [ O_point, V_point, X_point ]

/-
The union of Region1 and Region2 is the convex hull of {O, V, sigma V, X}.
-/
lemma Region12_eq_convexHull : Region1 ∪ Region2 = convexHull ℝ {O_point, V_point, sigma V_point, X_point} := by
  ext p
  constructor;
  · unfold Region1 Region2; intro hp; rcases hp with ( hp | hp ) <;> simp_all +decide [ convexHull_insert ] ;
    · obtain ⟨ q, hq, hpq ⟩ := hp; use sigma V_point; simp_all +decide [ segment_symm ] ;
      exact ⟨ right_mem_segment _ _ _, q, hq, hpq ⟩;
    · rcases hp with ⟨ q, hq, hp ⟩;
      exact ⟨ X_point, right_mem_segment _ _ _, q, hq, hp ⟩;
  · have h_convex_hull : convexHull ℝ {O_point, V_point, sigma V_point, X_point} ⊆ Region2 ∪ Region1 := by
      -- By definition of Region2 and Region1, we know that every point in the convex hull of {O, V, sigma V, X} is in either Region2 or Region1.
      have h_convex_hull : ∀ p ∈ convexHull ℝ {O_point, V_point, sigma V_point, X_point}, L_OV p ≥ 0 → p ∈ Region1 := by
        exact fun p a a_1 ↦ convexHull_sub_Region1_of_pos p a a_1;
      have h_convex_hull : ∀ p ∈ convexHull ℝ {O_point, V_point, sigma V_point, X_point}, L_OV p ≤ 0 → p ∈ Region2 := by
        exact fun p a a_1 ↦ convexHull_sub_Region2_of_neg p a a_1;
      exact fun p hp => if h : L_OV p ≤ 0 then Or.inl ( h_convex_hull p hp h ) else Or.inr ( by solve_by_elim [ le_of_not_ge h ] );
    exact fun h => by simpa only [ Set.union_comm ] using h_convex_hull h;

/-
The first quadrant is a convex set.
-/
def FirstQuadrant : Set Point := {p | 0 ≤ p 0 ∧ 0 ≤ p 1}

lemma FirstQuadrant_convex : Convex ℝ FirstQuadrant := by
  -- To prove convexity, take any two points $x, y \in \mathbb{R}^2_\geq$ and show that the line segment connecting them is also in $\mathbb{R}^2_\geq$.
  intro x hx y hy a b ha hb hab
  simp [FirstQuadrant] at hx hy ⊢;
  constructor <;> nlinarith

/-
The set of points {O, V, sigma V, X} is contained in the first quadrant.
-/
lemma Generators12_in_FirstQuadrant : {O_point, V_point, sigma V_point, X_point} ⊆ FirstQuadrant := by
  simp [FirstQuadrant, Set.subset_def];
  unfold O_point V_point sigma X_point; norm_num [ x1, y1 ] ;
  refine ⟨ ⟨ by positivity, by exact div_nonneg ( sub_nonneg.2 <| Real.sqrt_le_sqrt <| by norm_num ) <| by positivity ⟩, ⟨ by exact div_nonneg ( sub_nonneg.2 <| Real.sqrt_le_sqrt <| by norm_num ) <| by positivity, by positivity ⟩, ?_ ⟩
  generalize_proofs at *;
  linarith [ Classical.choose_spec ‹∃ x : ℝ, 19 / 20 < x ∧ x < 24 / 25 ∧ poly_X x = 0› ]

/-
All points in Region1 ∪ Region2 have non-negative coordinates.
-/
lemma Region12_subset_FirstQuadrant : ∀ p ∈ Region1 ∪ Region2, 0 ≤ p 0 ∧ 0 ≤ p 1 := by
  intro p hp
  have h_convex_hull : p ∈ convexHull ℝ {O_point, V_point, sigma V_point, X_point} := by
    exact Region12_eq_convexHull ▸ hp;
  have h_convex_hull_subset : convexHull ℝ {O_point, V_point, sigma V_point, X_point} ⊆ FirstQuadrant := by
    apply convexHull_min;
    · exact Generators12_in_FirstQuadrant;
    · exact FirstQuadrant_convex;
  exact h_convex_hull_subset h_convex_hull

/-
The point O is an extreme point of Region1 ∪ Region2 and cannot lie in the interior of any unit segment contained in the region.
-/
lemma O_extreme_Region12 : ∀ L, IsUnitSegment L → L ⊆ Region1 ∪ Region2 → O_point ∉ L := by
  intro L hL hL_sub hL_O
  obtain ⟨a, b, hab⟩ := hL;
  -- By Region12_subset_FirstQuadrant, a and b are in FirstQuadrant, so a.0 >= 0, a.1 >= 0, b.0 >= 0, b.1 >= 0.
  have h_a_b_nonneg : 0 ≤ a 0 ∧ 0 ≤ a 1 ∧ 0 ≤ b 0 ∧ 0 ≤ b 1 := by
    have h_a_b_nonneg : ∀ p ∈ openSegment ℝ a b, 0 ≤ p 0 ∧ 0 ≤ p 1 := by
      exact fun p hp => Region12_subset_FirstQuadrant p <| hL_sub <| hab.2 ▸ hp;
    have h_a_b_nonneg : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ (1 - t) * a 0 + t * b 0 ∧ 0 ≤ (1 - t) * a 1 + t * b 1 := by
      intro t ht; specialize h_a_b_nonneg ( ( 1 - t ) • a + t • b ) ; simp_all +decide [ openSegment_eq_image ] ;
      exact h_a_b_nonneg t ht.1 ht.2 rfl;
    have h_a_b_nonneg : Filter.Tendsto (fun t : ℝ => (1 - t) * a 0 + t * b 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds (a 0)) ∧ Filter.Tendsto (fun t : ℝ => (1 - t) * a 1 + t * b 1) (nhdsWithin 0 (Set.Ioi 0)) (nhds (a 1)) := by
      exact ⟨ tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ), tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ) ⟩;
    have h_a_b_nonneg : 0 ≤ a 0 ∧ 0 ≤ a 1 := by
      exact ⟨ le_of_tendsto_of_tendsto tendsto_const_nhds h_a_b_nonneg.1 ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun t ht => ‹∀ t ∈ Ioo 0 1, 0 ≤ ( 1 - t ) * a 0 + t * b 0 ∧ 0 ≤ ( 1 - t ) * a 1 + t * b 1› t ht |>.1 ), le_of_tendsto_of_tendsto tendsto_const_nhds h_a_b_nonneg.2 ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun t ht => ‹∀ t ∈ Ioo 0 1, 0 ≤ ( 1 - t ) * a 0 + t * b 0 ∧ 0 ≤ ( 1 - t ) * a 1 + t * b 1› t ht |>.2 ) ⟩;
    have h_a_b_nonneg : Filter.Tendsto (fun t : ℝ => (1 - t) * a 0 + t * b 0) (nhdsWithin 1 (Set.Iio 1)) (nhds (b 0)) ∧ Filter.Tendsto (fun t : ℝ => (1 - t) * a 1 + t * b 1) (nhdsWithin 1 (Set.Iio 1)) (nhds (b 1)) := by
      exact ⟨ tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ), tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ) ⟩;
    exact ⟨ by linarith, by linarith, by exact le_of_tendsto_of_tendsto tendsto_const_nhds h_a_b_nonneg.1 ( Filter.eventually_of_mem ( Ioo_mem_nhdsLT zero_lt_one ) fun t ht => by aesop ), by exact le_of_tendsto_of_tendsto tendsto_const_nhds h_a_b_nonneg.2 ( Filter.eventually_of_mem ( Ioo_mem_nhdsLT zero_lt_one ) fun t ht => by aesop ) ⟩;
  -- Since O = (0,0), we have (1-t)a.0 + tb.0 = 0. Since terms are non-negative and weights are positive, a.0 = 0 and b.0 = 0.
  have h_a_b_zero : a 0 = 0 ∧ b 0 = 0 ∧ a 1 = 0 ∧ b 1 = 0 := by
    -- Since O is in L, there exists a t in (0,1) such that O = (1-t)a + tb.
    obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, O_point = (1 - t) • a + t • b := by
      rw [ hab.2 ] at hL_O; rw [ openSegment_eq_image ] at hL_O; aesop;
    have h_a_b_zero : (1 - t) * a 0 + t * b 0 = 0 ∧ (1 - t) * a 1 + t * b 1 = 0 := by
      exact ⟨ by simpa using congr_fun ht.2.symm 0, by simpa using congr_fun ht.2.symm 1 ⟩;
    exact ⟨ by nlinarith [ ht.1.1, ht.1.2 ], by nlinarith [ ht.1.1, ht.1.2 ], by nlinarith [ ht.1.1, ht.1.2 ], by nlinarith [ ht.1.1, ht.1.2 ] ⟩;
  simp_all +decide [ show a = 0 from by ext i; fin_cases i <;> tauto, show b = 0 from by ext i; fin_cases i <;> tauto ]

/-
The sum of coordinates for any point in Region1 ∪ Region2 is at most the sum of coordinates of V.
-/
lemma Region12_sum_le_V_sum : ∀ p ∈ Region1 ∪ Region2, p 0 + p 1 ≤ V_point 0 + V_point 1 := by
  intro p hp
  have h_convex_hull : p ∈ convexHull ℝ {O_point, V_point, sigma V_point, X_point} := by
    exact Region12_eq_convexHull ▸ hp;
  -- By definition of convex hull, there exist weights $w_0, w_1, w_2, w_3$ such that $p = w_0 • O_point + w_1 • V_point + w_2 • sigma V_point + w_3 • X_point$ and $w_0 + w_1 + w_2 + w_3 = 1$.
  obtain ⟨w, hw⟩ : ∃ w : Fin 4 → ℝ, (∑ i, w i = 1) ∧ (0 ≤ w 0 ∧ 0 ≤ w 1 ∧ 0 ≤ w 2 ∧ 0 ≤ w 3) ∧ p = w 0 • O_point + w 1 • V_point + w 2 • sigma V_point + w 3 • X_point := by
    rw [ convexHull_insert ] at h_convex_hull;
    · norm_num [ segment_eq_image ] at h_convex_hull ⊢;
      rcases h_convex_hull with ⟨ i, hi, x, hx, rfl ⟩;
      rw [ convexHull_insert ] at hi <;> norm_num at *;
      rcases hi with ⟨ j, hj, hi ⟩ ; rw [ segment_eq_image ] at hj hi; norm_num at hj hi ⊢;
      rcases hj with ⟨ y, hy, rfl ⟩ ; rcases hi with ⟨ z, hz, rfl ⟩ ; use fun i => if i = 0 then 1 - x else if i = 1 then x * ( 1 - z ) else if i = 2 then x * z * ( 1 - y ) else x * z * y; simp +decide [ Fin.sum_univ_four ] ; ring_nf; norm_num [ hx, hy, hz ] ;
      exact ⟨ ⟨ by nlinarith, by nlinarith [ mul_nonneg hx.1 hz.1 ], by exact mul_nonneg ( mul_nonneg hx.1 hz.1 ) hy.1 ⟩, by ext i; fin_cases i <;> norm_num <;> ring ⟩;
    · norm_num;
  norm_num [ hw.2.2, Fin.sum_univ_four ] at *;
  norm_num [ O_point, V_point, sigma, X_point ] at *;
  unfold x1 at *;
  have := Classical.choose_spec exists_root_x1;
  nlinarith [ show 0 ≤ w 1 * Real.sqrt 6 by exact mul_nonneg hw.2.2.1 ( Real.sqrt_nonneg _ ), show 0 ≤ w 2 * Real.sqrt 6 by exact mul_nonneg hw.2.2.2.1 ( Real.sqrt_nonneg _ ), show 0 ≤ w 3 * Real.sqrt 6 by exact mul_nonneg hw.2.2.2.2 ( Real.sqrt_nonneg _ ), Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ]

/-
If the origin is in the open segment between two points in the first quadrant, then both points must be the origin.
-/
lemma origin_in_openSegment_FirstQuadrant_implies_endpoints_zero : ∀ a b : Point, a ∈ FirstQuadrant → b ∈ FirstQuadrant → O_point ∈ openSegment ℝ a b → a = O_point ∧ b = O_point := by
  -- By definition of open segment, there exists some $t \in (0, 1)$ such that $O_point = (1 - t) • a + t • b$.
  intro a b ha hb h_open_segment
  obtain ⟨t, ht₀, ht₁⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, O_point = (1 - t) • a + t • b := by
    rw [ openSegment_eq_image ] at h_open_segment ; aesop;
  -- By definition of open segment, we have $0 = (1 - t) * a 0 + t * b 0$ and $0 = (1 - t) * a 1 + t * b 1$.
  have h_eq0 : 0 = (1 - t) * a 0 + t * b 0 := by
    simpa using congr_fun ht₁ 0
  have h_eq1 : 0 = (1 - t) * a 1 + t * b 1 := by
    simpa using congr_fun ht₁ 1;
  -- Since $a$ and $b$ are in the first quadrant, their coordinates are non-negative. Therefore, the only way for the equations $0 = (1 - t) * a 0 + t * b 0$ and $0 = (1 - t) * a 1 + t * b 1$ to hold is if $a 0 = 0$ and $b 0 = 0$, and similarly for $a 1$ and $b 1$.
  have h_a0_b0 : a 0 = 0 ∧ b 0 = 0 := by
    constructor <;> nlinarith [ ha.1, ha.2, hb.1, hb.2, ht₀.1, ht₀.2 ]
  have h_a1_b1 : a 1 = 0 ∧ b 1 = 0 := by
    constructor <;> nlinarith [ ht₀.1, ht₀.2, ha.2, hb.2 ];
  exact ⟨ by ext i; fin_cases i <;> tauto, by ext i; fin_cases i <;> tauto ⟩

/-
The sum of the coordinates of V is positive.
-/
lemma sum_V_pos : V_point 0 + V_point 1 > 0 := by
  exact add_pos ( by rw [ show V_point 0 = ( Real.sqrt 6 + Real.sqrt 2 ) / 4 by rfl ] ; positivity ) ( by rw [ show V_point 1 = ( Real.sqrt 6 - Real.sqrt 2 ) / 4 by rfl ] ; exact div_pos ( sub_pos.mpr ( Real.lt_sqrt_of_sq_lt ( by norm_num ) ) ) ( by norm_num ) ) ;

/-
The sum of the coordinates of V is strictly greater than x1.
-/
lemma sum_V_gt_x1 : V_point 0 + V_point 1 > x1 := by
  unfold V_point x1;
  have := Classical.choose_spec exists_root_x1;
  norm_num [ poly_X ] at * ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ]

/-
If a point in Region1 ∪ Region2 has the maximum possible coordinate sum, it must lie on the segment connecting V and sigma V.
-/
lemma Region12_max_sum_implies_segment : ∀ p ∈ Region1 ∪ Region2, p 0 + p 1 = V_point 0 + V_point 1 → p ∈ segment ℝ V_point (sigma V_point) := by
  -- By definition of Region1 ∪ Region2, if p is in this union, then p can be written as a convex combination of O, V, sigma V, and X.
  intro p hp hsum
  obtain ⟨w_O, w_V, w_SV, w_X, hw_nonneg, hw_sum, hp_eq⟩ : ∃ w_O w_V w_SV w_X : ℝ, 0 ≤ w_O ∧ 0 ≤ w_V ∧ 0 ≤ w_SV ∧ 0 ≤ w_X ∧ w_O + w_V + w_SV + w_X = 1 ∧ p = w_O • O_point + w_V • V_point + w_SV • sigma V_point + w_X • X_point := by
    have h_convex : p ∈ convexHull ℝ {O_point, V_point, sigma V_point, X_point} := by
      exact Region12_eq_convexHull ▸ hp;
    rw [ convexHull_insert ] at h_convex;
    · norm_num [ segment_eq_image ] at h_convex;
      rcases h_convex with ⟨ q, hq, x, hx, rfl ⟩;
      rw [ convexHull_insert ] at hq;
      · norm_num [ segment_eq_image ] at hq;
        rcases hq with ⟨ i, hi, j, hj, rfl ⟩;
        exact ⟨ 1 - x, x * ( 1 - j ), x * j * ( 1 - i ), x * j * i, by linarith, by nlinarith, by nlinarith [ mul_nonneg hx.1 hj.1 ], by nlinarith [ mul_nonneg hx.1 hj.1 ], by linarith, by ext ; norm_num ; ring ⟩;
      · norm_num +zetaDelta at *;
    · norm_num +zetaDelta at *;
  -- Since S(V) > 0 and S(V) - x1 > 0, we have -w_O * S(V) - w_X * (S(V) - x1) = 0 implies w_O = 0 and w_X = 0.
  have h_weights_zero : w_O = 0 ∧ w_X = 0 := by
    have h_S_V_pos : V_point 0 + V_point 1 > 0 := by
      exact sum_V_pos
    have h_S_V_gt_x1 : V_point 0 + V_point 1 > x1 := by
      exact sum_V_gt_x1
    have h_S_V_gt_x1 : V_point 0 + V_point 1 - x1 > 0 := by
      linarith
    have h_eq : -w_O * (V_point 0 + V_point 1) - w_X * (V_point 0 + V_point 1 - x1) = 0 := by
      simp_all +decide [ show O_point = fun _ => 0 from funext fun i => by fin_cases i <;> rfl, show X_point = fun i => if i = 0 then x1 else 0 from funext fun i => by fin_cases i <;> rfl ];
      unfold sigma at *; norm_num [ Fin.sum_univ_succ ] at *; nlinarith;
    constructor <;> nlinarith only [ hw_nonneg, hw_sum, hp_eq, h_S_V_pos, h_S_V_gt_x1, h_eq ];
  simp_all +decide [ segment_eq_image ];
  exact ⟨ w_SV, ⟨ by linarith, by linarith ⟩, by rw [ ← eq_sub_iff_add_eq' ] at hp_eq; aesop ⟩

/-
The point V is an extreme point of Region1 ∪ Region2 and cannot lie in the interior of any unit segment contained in the region.
-/
lemma V_extreme_Region12 : ∀ L, IsUnitSegment L → L ⊆ Region1 ∪ Region2 → V_point ∉ L := by
  intro L hL hL'V;
  -- By Lemma 1, if L is a unit segment in Region1 ∪ Region2 and V ∈ L, then L must be the open segment between V and sigma V.
  obtain ⟨a, b, hab⟩ : ∃ a b : Point, a ∈ Region1 ∪ Region2 ∧ b ∈ Region1 ∪ Region2 ∧ L = openSegment ℝ a b ∧ dist a b = 1 := by
    obtain ⟨a, b, hab⟩ : ∃ a b : Point, L = openSegment ℝ a b ∧ dist a b = 1 := by
      cases hL ; tauto;
    use a, b;
    simp_all +decide [ Set.subset_def ];
    have h_a : a ∈ Region1 ∪ Region2 := by
      have h_a : Filter.Tendsto (fun t : ℝ => (1 - t) • a + t • b) (nhdsWithin 0 (Set.Ioi 0)) (nhds a) := by
        exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) );
      have h_a : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), (1 - t) • a + t • b ∈ Region1 ∪ Region2 := by
        filter_upwards [ Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ] with t ht using hL'V _ <| by rw [ openSegment_eq_image ] ; exact ⟨ t, ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩, by ext i; fin_cases i <;> norm_num ⟩ ;
      have h_a : IsClosed (Region1 ∪ Region2) := by
        have h_closed : IsClosed (convexHull ℝ {O_point, V_point, sigma V_point, X_point}) := by
          have h_closed : IsCompact (convexHull ℝ {O_point, V_point, sigma V_point, X_point}) := by
            have h_finite : Set.Finite {O_point, V_point, sigma V_point, X_point} := by
              exact Set.toFinite _
            exact h_finite.isCompact_convexHull;
          exact h_closed.isClosed;
        convert h_closed using 1;
        exact Region12_eq_convexHull;
      exact h_a.mem_of_tendsto ‹_› ‹_›
    have h_b : b ∈ Region1 ∪ Region2 := by
      have h_b : Filter.Tendsto (fun t : ℝ => (1 - t) • a + t • b) (nhdsWithin 1 (Set.Iio 1)) (nhds b) := by
        exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num );
      have h_b : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Iio 1), (1 - t) • a + t • b ∈ Region1 ∪ Region2 := by
        filter_upwards [ Ioo_mem_nhdsLT zero_lt_one ] with t ht using hL'V _ <| by rw [ openSegment_eq_image ] ; exact ⟨ t, ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩, by ext i; fin_cases i <;> simp +decide [ ht.1.le, ht.2.le ] ⟩ ;
      have h_b : IsClosed (Region1 ∪ Region2) := by
        have h_closed : IsClosed (convexHull ℝ {O_point, V_point, sigma V_point, X_point}) := by
          have h_closed : IsCompact (convexHull ℝ {O_point, V_point, sigma V_point, X_point}) := by
            have h_finite : Set.Finite {O_point, V_point, sigma V_point, X_point} := by
              exact Set.toFinite _;
            exact h_finite.isCompact_convexHull;
          exact h_closed.isClosed;
        convert h_closed using 1;
        exact Region12_eq_convexHull;
      exact h_b.mem_of_tendsto ‹_› ‹_›
    exact ⟨h_a, h_b⟩;
  -- By Lemma 2, if V ∈ L, then f(a) = f(V) and f(b) = f(V), where f(p) = p 0 + p 1.
  by_cases hV : V_point ∈ L
  have hfa : a 0 + a 1 = V_point 0 + V_point 1 := by
    have hfa : a 0 + a 1 ≤ V_point 0 + V_point 1 ∧ b 0 + b 1 ≤ V_point 0 + V_point 1 := by
      exact ⟨ Region12_sum_le_V_sum a hab.1, Region12_sum_le_V_sum b hab.2.1 ⟩;
    -- Since V is in L, we can write V as a convex combination of a and b. That is, there exists some t in (0,1) such that V = (1-t)a + tb.
    obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, V_point = (1 - t) • a + t • b := by
      rw [ hab.2.2.1 ] at hV;
      rw [ openSegment_eq_image ] at hV;
      simpa [ eq_comm ] using hV;
    norm_num [ ht.2 ] at *;
    nlinarith
  have hfb : b 0 + b 1 = V_point 0 + V_point 1 := by
    obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, V_point = (1 - t) • a + t • b := by
      rw [ hab.2.2.1, openSegment_eq_image ] at hV;
      simpa [ eq_comm ] using hV;
    have := congr_fun ht.2 0; have := congr_fun ht.2 1; norm_num at *; nlinarith [ ht.1.1, ht.1.2 ] ;
  · -- By Lemma 3, if f(a) = f(V) and f(b) = f(V), then a and b are in the segment between V and sigma V.
    have ha_sigmaV : a ∈ segment ℝ V_point (sigma V_point) := by
      apply Region12_max_sum_implies_segment a hab.left hfa
    have hb_sigmaV : b ∈ segment ℝ V_point (sigma V_point) := by
      exact Region12_max_sum_implies_segment b hab.2.1 hfb;
    -- Since dist a b = 1 and dist V (sigma V) = 1, {a, b} = {V, sigma V}.
    have h_eq : a = V_point ∧ b = sigma V_point ∨ a = sigma V_point ∧ b = V_point := by
      have h_eq : dist a b = dist V_point (sigma V_point) := by
        have h_eq : dist V_point (sigma V_point) = 1 := by
          exact dist_V_sigma_V;
        linarith;
      rw [ segment_eq_image ] at *;
      rcases ha_sigmaV with ⟨ θ₁, ⟨ hθ₁₀, hθ₁₁ ⟩, rfl ⟩ ; rcases hb_sigmaV with ⟨ θ₂, ⟨ hθ₂₀, hθ₂₁ ⟩, rfl ⟩ ; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
      -- Since the square roots are equal, the expressions inside must be equal. So, the sum of the squares of the differences must be equal to the sum of the squares of the differences between V_point and sigma V_point.
      have h_eq_squares : (θ₁ - θ₂)^2 * ((V_point 0 - sigma V_point 0)^2 + (V_point 1 - sigma V_point 1)^2) = (V_point 0 - sigma V_point 0)^2 + (V_point 1 - sigma V_point 1)^2 := by
        rw [ Real.sqrt_inj ( by positivity ) ( by positivity ) ] at h_eq ; linarith;
      -- Since the sum of squares is non-zero, we can divide both sides by it, leading to (θ₁ - θ₂)^2 = 1.
      have h_diff_squares : (θ₁ - θ₂)^2 = 1 := by
        have h_nonzero : (V_point 0 - sigma V_point 0)^2 + (V_point 1 - sigma V_point 1)^2 ≠ 0 := by
          unfold sigma; norm_num [ V_point ] ;
          ring_nf; norm_num;
        exact mul_left_cancel₀ h_nonzero <| by linear_combination' h_eq_squares;
      cases eq_or_eq_neg_of_sq_eq_sq ( θ₁ - θ₂ ) 1 ( by linarith ) <;> simp_all +decide [ sub_eq_iff_eq_add ];
      · norm_num [ show θ₂ = 0 by linarith ] at *;
        norm_num [ ← h_eq ] at *;
      · norm_num [ show θ₂ = 1 by linarith ] at *;
        norm_num [ ← h_eq ] at *;
    rcases h_eq with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> simp_all +decide [ openSegment ];
    · obtain ⟨ a, ha, b, hb, hab, h ⟩ := hV;
      rw [ ← List.ofFn_inj ] at * ; norm_num at *;
      norm_num [ show a = 1 - b by linarith ] at h;
      norm_num [ show b = 1 / 2 by nlinarith! [ show V_point 0 > V_point 1 from by
                                                  exact V_point_1_lt_V_point_0 ] ] at *;
      linarith! [ show V_point 0 > V_point 1 from by
                    exact V_point_1_lt_V_point_0 ];
    · obtain ⟨ a, ha, b, hb, hab, h ⟩ := hV;
      have := congr_fun h 0
      have := congr_fun h 1
      norm_num at *
      nlinarith [ show ( sigma V_point ) 0 = V_point 1 from rfl, show ( sigma V_point ) 1 = V_point 0 from rfl, show ( V_point ) 0 > ( V_point ) 1 from by exact V_point_1_lt_V_point_0 ]
  · exact hV

/-
The union of Region1 and Region2 is blocked by S_finite.
-/
lemma Region12_blocking : IsBlocking S_finite (Region1 ∪ Region2) := by
  -- Apply the blocking_union_lemma with the given conditions.
  have h_blocking_union : IsBlocking S_finite (Region1 ∪ Region2) := by
    have h_closed : IsClosed Region1 ∧ IsClosed Region2 := by
      -- The convex hull of a finite set of points in a finite-dimensional space is closed.
      have h_convex_hull_closed : ∀ (s : Set Point), s.Finite → IsClosed (convexHull ℝ s) := by
        intro s hs_finite
        have h_convex_hull_compact : IsCompact (convexHull ℝ s) := by
          exact hs_finite.isCompact_convexHull;
        exact h_convex_hull_compact.isClosed;
      exact ⟨ h_convex_hull_closed _ <| Set.toFinite _, h_convex_hull_closed _ <| Set.toFinite _ ⟩
    have h_blocked : IsBlocking S_finite Region1 ∧ IsBlocking S_finite Region2 := by
      exact ⟨ by exact Region1_blocking;, by exact Region2_blocking; ⟩
    have h_inter : Region1 ∩ Region2 = segment ℝ O_point V_point := by
      exact Region1_inter_Region2
    apply blocking_union_lemma;
    · exact h_closed.1;
    · exact h_closed.2;
    · exact h_blocked.1;
    · exact h_blocked.2;
    · intro x hx
      rw [h_inter] at hx
      obtain ⟨hx_segment, hx_extreme⟩ : x ∈ segment ℝ O_point V_point ∧ (x = O_point ∨ x = V_point ∨ x ∈ openSegment ℝ O_point V_point) := by
        rw [ segment_eq_image ] at hx ⊢;
        rcases hx with ⟨ θ, ⟨ hθ₀, hθ₁ ⟩, rfl ⟩ ; by_cases hθ : θ = 0 <;> by_cases hθ' : θ = 1 <;> simp_all +decide [ openSegment_eq_image ] ;
        · exact ⟨ 0, by norm_num ⟩;
        · exact ⟨ 1, by norm_num ⟩;
        · exact ⟨ ⟨ θ, ⟨ hθ₀, hθ₁ ⟩, rfl ⟩, Or.inr <| Or.inr <| ⟨ θ, ⟨ lt_of_le_of_ne hθ₀ <| Ne.symm hθ, lt_of_le_of_ne hθ₁ hθ' ⟩, rfl ⟩ ⟩;
      rcases hx_extreme with ( rfl | rfl | hx_extreme ) <;> norm_num [ segment_eq_image ] at hx_segment ⊢;
      · exact Or.inr fun L hL hL' hL'' => by have := O_extreme_Region12 L hL hL' hL''; contradiction;
      · exact Or.inr fun L hL hL' hL'' => by have := V_extreme_Region12 L hL hL' hL''; contradiction;
      · exact Or.inl ⟨ segment1, by unfold S_finite; norm_num, hx_extreme ⟩;
  grind

/-
Region12 is Region1 union Region2. Region123 is Region12 union Region3.
-/
def Region12 : Set Point := Region1 ∪ Region2

def Region123 : Set Point := Region12 ∪ Region3

/-
Define L_sep and prove its signs at the vertices O, V, sigma V, X, sigma X.
-/
noncomputable def L_sep (p : Point) : ℝ := V_point 0 * p 0 - V_point 1 * p 1

lemma L_sep_O : L_sep O_point = 0 := by
  exact show V_point 0 * 0 - V_point 1 * 0 = 0 by ring;

lemma L_sep_V_pos : L_sep V_point > 0 := by
  unfold L_sep V_point; ring_nf;
  simp +zetaDelta at *;
  nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ]

lemma L_sep_sigma_V : L_sep (sigma V_point) = 0 := by
  unfold L_sep sigma V_point
  skip;
  ring!

lemma L_sep_X_pos : L_sep X_point > 0 := by
  unfold L_sep;
  unfold V_point X_point;
  unfold x1;
  have := Classical.choose_spec exists_root_x1;
  norm_num [ poly_X ] at *;
  exact mul_pos ( by positivity ) ( by linarith )

lemma L_sep_sigma_X_neg : L_sep (sigma X_point) < 0 := by
  -- By definition of $L_{\text{sep}}$, we have $L_{\text{sep}}(\sigma X) = V_x \cdot 0 - V_y \cdot x_1$.
  have h_sep_sigma_X_def : L_sep (sigma X_point) = V_point 0 * 0 - V_point 1 * x1 := by
    exact rfl;
  -- Since $V_point 1$ and $x1$ are both positive, their product $V_point 1 * x1$ is also positive.
  have h_pos : 0 < V_point 1 * x1 := by
    have h_pos : 0 < V_point 1 ∧ 0 < x1 := by
      have h_V1_pos : 0 < V_point 1 := by
        exact div_pos ( sub_pos.mpr ( Real.lt_sqrt_of_sq_lt ( by norm_num ) ) ) ( by norm_num )
      have h_x1_pos : 0 < x1 := by
        exact mul_pos ( sub_pos.mpr x1_prop.1 ) ( sub_pos.mpr x1_prop.2.1 ) |> fun h => by nlinarith [ pow_pos ( sub_pos.mpr x1_prop.1 ) 3, pow_pos ( sub_pos.mpr x1_prop.2.1 ) 3 ] ;
      exact ⟨h_V1_pos, h_x1_pos⟩;
    exact mul_pos h_pos.left h_pos.right;
  linarith [ h_pos ]

/-
L_sep is non-negative on Region1.
-/
lemma Region1_sub_L_sep_ge_0 : ∀ p ∈ Region1, L_sep p ≥ 0 := by
  -- Since $L_{\text{sep}}$ is affine and its values at the vertices $O$, $V$, and $\sigma V$ are non-negative, it is non-negative on their convex hull.
  have h_affine : ∀ p ∈ convexHull ℝ {O_point, V_point, sigma V_point}, L_sep p ≥ 0 := by
    intro p hp
    have h_convex_comb : ∃ (a b c : ℝ), a + b + c = 1 ∧ 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ p = a • O_point + b • V_point + c • sigma V_point := by
      rw [ convexHull_insert ] at hp;
      · norm_num [ segment_eq_image ] at hp;
        rcases hp with ⟨ i, ⟨ hi₀, hi₁ ⟩, x, ⟨ hx₀, hx₁ ⟩, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by ring, by nlinarith, by nlinarith, by nlinarith, by ext ; simpa using by ring ⟩ ;
      · norm_num +zetaDelta at *
    obtain ⟨ a, b, c, h₁, h₂, h₃, h₄, rfl ⟩ := h_convex_comb; unfold L_sep; norm_num [ Fin.sum_univ_two ] ;
    unfold O_point V_point sigma; norm_num; ring_nf;
    norm_num [ ← Real.sqrt_mul ] ; nlinarith [ Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), Real.sq_sqrt ( show 0 ≤ 2 by norm_num ) ] ;
  grind

/-
L_sep is non-negative on Region2.
-/
lemma Region2_sub_L_sep_ge_0 : ∀ p ∈ Region2, L_sep p ≥ 0 := by
  intro p hp
  have h_convex : p ∈ convexHull ℝ {O_point, V_point, X_point} := by
    grind;
  rw [ mem_convexHull_iff ] at h_convex;
  specialize h_convex { q | 0 ≤ L_sep q } ?_ ?_ <;> norm_num at *;
  · norm_num [ Set.insert_subset_iff, L_sep_O, L_sep_V_pos, L_sep_X_pos ];
    exact ⟨ le_of_lt ( L_sep_V_pos ), le_of_lt ( L_sep_X_pos ) ⟩;
  · intro x hx y hy a b ha hb hab;
    unfold L_sep at *; simp_all +decide [ Fin.sum_univ_two ] ;
    nlinarith;
  · exact h_convex

/-
L_sep is non-positive on Region3.
-/
lemma Region3_sub_L_sep_le_0 : ∀ p ∈ Region3, L_sep p ≤ 0 := by
  intro p hp
  obtain ⟨a, b, c, ha, hb, hc, habc, hp_eq⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • sigma V_point + c • sigma X_point := by
    obtain ⟨a, b, c, ha, hb, hc, habc, hp_eq⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • sigma V_point + c • sigma X_point := by
      have h_convex : p ∈ convexHull ℝ {O_point, sigma V_point, sigma X_point} := hp
      rw [ convexHull_insert ] at h_convex
      generalize_proofs at *;
      · norm_num [ segment_eq_image ] at h_convex ⊢
        generalize_proofs at *;
        rcases h_convex with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, by linarith, x * ( 1 - i ), by nlinarith, x * i, by nlinarith, by ring, by ext ; simpa using by ring ⟩ ;
      · norm_num +zetaDelta at *
    generalize_proofs at *;
    use a, b, c;
  -- Substitute the expression for p into L_sep and use the known values of L_sep at the vertices.
  have hL_sep_p : L_sep p = a * L_sep O_point + b * L_sep (sigma V_point) + c * L_sep (sigma X_point) := by
    unfold L_sep; norm_num [ hp_eq ] ; ring;
  exact hL_sep_p.symm ▸ by nlinarith [ L_sep_O, L_sep_sigma_V, L_sep_sigma_X_neg ] ;

/-
L_sep is non-negative on Region12.
-/
lemma Region12_sub_L_sep_ge_0 : ∀ p ∈ Region12, L_sep p ≥ 0 := by
  have h_L_sep_nonneg : ∀ p ∈ Region1, L_sep p ≥ 0 := by
    apply Region1_sub_L_sep_ge_0
    skip
  have h_L_sep_nonneg2 : ∀ p ∈ Region2, L_sep p ≥ 0 := by
    exact fun p a ↦ Region2_sub_L_sep_ge_0 p a
  intro p hp
  obtain hp1 | hp2 := hp
  · exact h_L_sep_nonneg p hp1
  · exact h_L_sep_nonneg2 p hp2

/-
The intersection of Region3 and the line L_sep=0 is contained in the segment [O, sigma V].
-/
lemma Region3_inter_L_sep_zero : Region3 ∩ {p | L_sep p = 0} ⊆ segment ℝ O_point (sigma V_point) := by
  -- Let p be a point in the intersection. Then p can be written as a convex combination of O, sigma V, and sigma X.
  intro p hp
  obtain ⟨a, b, c, ha, hb, hc, habc, hp_eq⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • (sigma V_point) + c • (sigma X_point) := by
    -- By definition of convex hull, since p is in the convex hull of {O, sigma V, sigma X}, there exist non-negative weights a, b, c such that a + b + c = 1 and p = a • O + b • sigma V + c • sigma X.
    have h_convex : p ∈ convexHull ℝ ({O_point, sigma V_point, sigma X_point} : Set Point) := by
      exact mem_of_mem_inter_left hp;
    rw [ convexHull_insert ] at h_convex;
    · norm_num [ segment_eq_image ] at h_convex;
      rcases h_convex with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext ; simpa using by ring ⟩ ;
    · exact ⟨ _, Set.mem_insert _ _ ⟩;
  -- Since $L_{\text{sep}}(p) = 0$, we have $c * L_{\text{sep}}(\sigma X) = 0$. Given that $L_{\text{sep}}(\sigma X) < 0$, it follows that $c = 0$.
  have hc_zero : c = 0 := by
    have hc_zero : c * L_sep (sigma X_point) = 0 := by
      have hc_zero : L_sep p = a * L_sep O_point + b * L_sep (sigma V_point) + c * L_sep (sigma X_point) := by
        rw [hp_eq]; ring_nf;
        unfold L_sep; norm_num; ring;
      simp_all +decide [ L_sep_O, L_sep_sigma_V ];
    exact mul_left_cancel₀ ( show L_sep ( sigma X_point ) ≠ 0 from ne_of_lt ( by exact
      L_sep_sigma_X_neg ) ) ( by linarith );
  simp_all +decide [ segment_eq_image ];
  exact ⟨ b, ⟨ hb, by linarith ⟩, by rw [ ← eq_sub_iff_add_eq' ] at habc; aesop ⟩

/-
The intersection of Region12 and Region3 is contained in segment O (sigma V).
-/
lemma Region12_inter_Region3_subset_segment : Region12 ∩ Region3 ⊆ segment ℝ O_point (sigma V_point) := by
  -- By definition of Region12 and Region3, if p is in both, then L_sep p = 0.
  intros p hp
  have hL_sep : L_sep p = 0 := by
    exact le_antisymm ( le_of_not_gt fun h => by linarith [ hp.2, Region3_sub_L_sep_le_0 p hp.2 ] ) ( le_of_not_gt fun h => by linarith [ hp.1, Region12_sub_L_sep_ge_0 p hp.1 ] );
  exact Region3_inter_L_sep_zero ⟨ hp.2, hL_sep ⟩

/-
Region12 is blocked by S_finite.
-/
lemma Region12_blocking_thm : IsBlocking S_finite Region12 := by
  -- Apply the lemma that states the union of Region1 and Region2 is blocked by S_finite.
  apply Region12_blocking

/-
Region3 is contained in the first quadrant.
-/
lemma Region3_subset_FirstQuadrant : Region3 ⊆ FirstQuadrant := by
  refine' convexHull_min _ _;
  · rintro p ( rfl | rfl | rfl ) <;> unfold FirstQuadrant <;> norm_num [ O_point, sigma, V_point, X_point ];
    · constructor <;> nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ];
    · linarith [ x1_prop.1 ];
  · exact FirstQuadrant_convex

/-
Region123 is contained in the first quadrant.
-/
lemma Region123_subset_FirstQuadrant : Region123 ⊆ FirstQuadrant := by
  -- The union of two subsets is a subset.
  apply Set.union_subset; exact Region12_subset_FirstQuadrant; exact Region3_subset_FirstQuadrant

/-
L1 is non-positive on Region123.
-/
lemma Region123_sub_L1_le_0 : ∀ p ∈ Region123, L1 p ≤ 0 := by
  -- By definition of Region123, p is either in Region12 or in Region3.
  intro p hp
  cases' hp with hp12 hp3;
  · -- Since p is in Region12, we know that p's coordinates are non-negative and their sum is at most V_point 0 + V_point 1.
    have h_coords : 0 ≤ p 0 ∧ 0 ≤ p 1 ∧ p 0 + p 1 ≤ V_point 0 + V_point 1 := by
      exact ⟨ Region12_subset_FirstQuadrant _ hp12 |>.1, Region12_subset_FirstQuadrant _ hp12 |>.2, Region12_sum_le_V_sum _ hp12 ⟩;
    exact sub_nonpos_of_le ( by linarith [ show V_point 0 + V_point 1 > 0 from sum_V_pos ] );
  · -- By definition of Region3, we know that p can be written as a convex combination of O, sigma V, and sigma X.
    obtain ⟨a, b, c, ha, hb, hc, habc, hp⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • (sigma V_point) + c • (sigma X_point) := by
      obtain ⟨a, b, c, ha, hb, hc, habc, hp⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • sigma V_point + c • sigma X_point := by
        have h_convex : p ∈ convexHull ℝ {O_point, sigma V_point, sigma X_point} := by
          exact hp3
        rw [ convexHull_insert ] at h_convex;
        · norm_num [ segment_eq_image ] at h_convex;
          rcases h_convex with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext ; simpa using by ring ⟩ ;
        · exact ⟨ _, Set.mem_insert _ _ ⟩;
      use a, b, c;
    -- Substitute the values of L1 at O, sigma V, and sigma X into the equation.
    have hL1_values : L1 O_point = -(V_point 0 + V_point 1) ∧ L1 (sigma V_point) = 0 ∧ L1 (sigma X_point) = x1 - (V_point 0 + V_point 1) := by
      unfold L1; norm_num [ O_point, X_point, sigma ] ; ring;
    -- Substitute the values of L1 at O, sigma V, and sigma X into the equation and simplify.
    have hL1_simplified : L1 p = a * (-(V_point 0 + V_point 1)) + b * 0 + c * (x1 - (V_point 0 + V_point 1)) := by
      rw [ hp, ← hL1_values.1, ← hL1_values.2.1, ← hL1_values.2.2 ];
      unfold L1; norm_num [ add_assoc ] ; ring_nf;
      grind;
    nlinarith [ show V_point 0 + V_point 1 > 0 from sum_V_pos, show x1 < V_point 0 + V_point 1 from by linarith [ show V_point 0 + V_point 1 > x1 from sum_V_gt_x1 ] ]

/-
L1 is negative at O.
-/
lemma L1_O_neg : L1 O_point < 0 := by
  convert neg_lt_zero.mpr ( sum_V_pos ) using 1;
  unfold L1 O_point; ring_nf;
  erw [ Matrix.cons_val_succ' ] ; norm_num

/-
L1 is negative at X.
-/
lemma L1_X_neg : L1 X_point < 0 := by
  -- By definition of $L1$, we know that $L1 X_point = x1 - (V_point 0 + V_point 1)$.
  have hL1_X : L1 X_point = x1 - (V_point 0 + V_point 1) := by
    unfold L1
    simp [X_point];
  exact hL1_X ▸ sub_neg_of_lt ( by linarith [ sum_V_gt_x1 ] )

/-
L1 is negative at sigma X.
-/
lemma L1_sigma_X_neg : L1 (sigma X_point) < 0 := by
  -- Substitute the values of sigma X_point into L1 and simplify.
  have hL1_sigma_X : L1 (sigma X_point) = x1 - (V_point 0 + V_point 1) := by
    unfold sigma L1; norm_num;
    exact show 0 + x1 = x1 from by ring;
  exact hL1_sigma_X ▸ sub_neg_of_lt ( by linarith [ sum_V_gt_x1 ] )

/-
The intersection of Region12 and the line L1=0 is the segment V-sigma(V).
-/
lemma Region12_inter_L1_zero : Region12 ∩ {p | L1 p = 0} = segment ℝ V_point (sigma V_point) := by
  apply Set.eq_of_subset_of_subset;
  · intro p hp
    obtain ⟨hp12, hpL1⟩ := hp
    have hL1_zero : L1 p = 0 := hpL1
    have hL1_zero_segment : p ∈ segment ℝ V_point (sigma V_point) := by
      apply Region12_max_sum_implies_segment p hp12; exact (by
      unfold L1 at hL1_zero; linarith!;);
    exact hL1_zero_segment;
  · intro p hp;
    -- Since $p$ is in the segment between $V_point$ and $sigma V_point$, it is in $Region1$.
    have hp_region1 : p ∈ Region1 := by
      refine' convexHull_mono _ _;
      exact { V_point, sigma V_point };
      · norm_num [ Set.insert_subset_iff ];
      · exact convex_convexHull ℝ _ |> fun h => h.segment_subset ( subset_convexHull ℝ _ <| Set.mem_insert _ _ ) ( subset_convexHull ℝ _ <| Set.mem_insert_of_mem _ <| Set.mem_singleton _ ) hp;
    refine' ⟨ Or.inl hp_region1, _ ⟩;
    obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hp;
    unfold L1; norm_num [ ← eq_sub_iff_add_eq' ] at *; ring_nf;
    unfold V_point sigma; norm_num; ring_nf;
    rw [ hab ] ; ring

/-
The intersection of Region3 and the line L1=0 is the singleton {sigma V}.
-/
lemma Region3_inter_L1_zero : Region3 ∩ {p | L1 p = 0} = {sigma V_point} := by
  apply Set.eq_singleton_iff_unique_mem.mpr;
  refine' ⟨ ⟨ _, _ ⟩, _ ⟩;
  · refine' subset_convexHull ℝ _ _;
    exact Set.mem_insert_of_mem _ ( Set.mem_insert _ _ );
  · -- Since sigma V_point is (V_point 1, V_point 0), we can substitute these values into L1.
    simp [L1, sigma];
    ring;
  · intro p hp;
    -- Since $p \in \text{Region3}$ and $L1(p) = 0$, we can use the fact that $L1$ is affine to show that $p$ must be $\sigma(V)$.
    have h_affine : ∃ a b c : ℝ, a + b + c = 1 ∧ a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ p = a • O_point + b • sigma V_point + c • sigma X_point := by
      have h_convex : p ∈ convexHull ℝ {O_point, sigma V_point, sigma X_point} := by
        exact hp.1;
      rw [ convexHull_insert ] at h_convex;
      · norm_num [ segment_eq_image ] at h_convex;
        obtain ⟨ i, hi, x, hx, rfl ⟩ := h_convex; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by ring, by nlinarith, by nlinarith, by nlinarith, by ext; simpa using by ring ⟩ ;
      · exact ⟨ _, Set.mem_insert _ _ ⟩;
    obtain ⟨ a, b, c, h₁, h₂, h₃, h₄, rfl ⟩ := h_affine; simp_all +decide [ funext_iff, Fin.forall_fin_two ] ;
    -- Since $L1(O) < 0$, $L1(\sigma(X)) < 0$, and $L1(\sigma(V)) = 0$, the only way for $a * L1(O) + b * L1(\sigma(V)) + c * L1(\sigma(X)) = 0$ to hold is if $a = 0$ and $c = 0$.
    have h_ac_zero : a = 0 ∧ c = 0 := by
      have h_ac_zero : a * L1 O_point + c * L1 (sigma X_point) = 0 := by
        convert hp.2 using 1 ; norm_num [ L1 ] ; ring_nf;
        rw [ show b = 1 - a - c by linarith ] ; unfold sigma ; norm_num ; ring;
      constructor <;> nlinarith [ L1_O_neg, L1_sigma_X_neg ];
    aesop

/-
The intersection of Region123 and the line L1=0 is the segment V-sigma(V).
-/
lemma Region123_inter_L1_zero : Region123 ∩ {p | L1 p = 0} = segment ℝ V_point (sigma V_point) := by
  -- The intersection of Region12 with {L1=0} is the segment V-sigma V.
  have h_region12_inter_L1 : Region12 ∩ {p | L1 p = 0} = segment ℝ V_point (sigma V_point) := by
    -- Apply the lemma Region12_inter_L1_zero to conclude the proof.
    apply Region12_inter_L1_zero;
  -- The intersection of Region3 with {L1=0} is the singleton {sigma V}.
  have h_region3_inter_L1 : Region3 ∩ {p | L1 p = 0} = {sigma V_point} := by
    -- The intersection of Region3 and the line L1=0 is the singleton {sigma V} by definition.
    apply Region3_inter_L1_zero;
  -- The intersection of Region123 with {L1=0} is the union of the intersections of Region12 and Region3 with {L1=0}.
  have h_union_inter_L1 : (Region12 ∪ Region3) ∩ {p | L1 p = 0} = (Region12 ∩ {p | L1 p = 0}) ∪ (Region3 ∩ {p | L1 p = 0}) := by
    rw [ Set.union_inter_distrib_right ];
  convert h_union_inter_L1 using 1 ; rw [ h_region12_inter_L1, h_region3_inter_L1 ] ; ext ; simp +decide [ segment_eq_image ] ; ring_nf ; aesop;

/-
The origin cannot be in a unit segment contained in the first quadrant.
-/
lemma O_not_in_unit_segment_FirstQuadrant (L : Set Point) (hL : IsUnitSegment L) (hL_sub : L ⊆ FirstQuadrant) : O_point ∉ L := by
  -- Apply the lemma that states if the origin is in a unit segment in the first quadrant, then the endpoints must be the origin.
  have h_endpoints : ∀ a b : Point, a ∈ FirstQuadrant → b ∈ FirstQuadrant → O_point ∈ openSegment ℝ a b → a = O_point ∧ b = O_point := by
    intros a b ha hb hO
    apply origin_in_openSegment_FirstQuadrant_implies_endpoints_zero a b ha hb hO;
  obtain ⟨a, b, hab⟩ : ∃ a b : Point, L = openSegment ℝ a b ∧ dist a b = 1 := by
    cases hL ; tauto;
  contrapose! h_endpoints;
  use a, b;
  have h_closure : closure L ⊆ FirstQuadrant := by
    exact closure_minimal hL_sub ( isClosed_Ici.preimage ( continuous_apply 0 ) |> IsClosed.inter <| isClosed_Ici.preimage ( continuous_apply 1 ) );
  simp_all +decide [ Set.subset_def ];
  exact ⟨ h_closure a ( left_mem_segment _ _ _ ), h_closure b ( right_mem_segment _ _ _ ), by rintro rfl rfl; norm_num [ dist_eq_norm ] at hab ⟩

/-
L1 preserves affine combinations.
-/
lemma L1_convex_comb (x y : Point) (a b : ℝ) (h : a + b = 1) : L1 (a • x + b • y) = a * L1 x + b * L1 y := by
  -- Expand L1 (a • x + b • y) using the definition of L1.
  simp [L1];
  grind

/-
The intersection of Region12 and Region3 is covered by S_finite or satisfies the blocking condition.
-/
lemma Region12_inter_Region3_cover : ∀ x ∈ Region12 ∩ Region3, (∃ s ∈ S_finite, x ∈ s) ∨ (∀ L, IsUnitSegment L → L ⊆ Region12 ∪ Region3 → x ∈ L → L ⊆ Region12 ∨ L ⊆ Region3) := by
  intro x hx
  have h_cases : x ∈ segment ℝ O_point (sigma V_point) := by
    exact Region12_inter_Region3_subset_segment hx;
  by_cases hx_sigma_V : x = sigma V_point;
  · exact Or.inl ⟨ segment5, by unfold S_finite; tauto, hx_sigma_V ▸ sigma_V_on_segment5 ⟩;
  · by_cases hx_O : x = O_point;
    · right;
      intro L hL hL_sub hxL
      have hL_first_quadrant : L ⊆ FirstQuadrant := by
        exact fun p hp => Region123_subset_FirstQuadrant <| hL_sub hp;
      exact False.elim <| O_not_in_unit_segment_FirstQuadrant L hL hL_first_quadrant <| hx_O ▸ hxL;
    · -- Since x is in the open segment between O and sigma V, and x is not O or sigma V, it must be in segment2.
      have hx_segment2 : x ∈ openSegment ℝ O_point (sigma V_point) := by
        exact
          mem_openSegment_of_ne_left_right (fun a ↦ hx_O (id (Eq.symm a)))
            (fun a ↦ hx_sigma_V (id (Eq.symm a))) h_cases;
      exact Or.inl ⟨ segment2, by unfold S_finite; tauto, hx_segment2 ⟩

/-
Region123 is blocked by S_finite.
-/
def Region1234 : Set Point := Region123 ∪ Region4

def Region12345 : Set Point := Region1234 ∪ Region5

lemma Region123_blocking : IsBlocking S_finite Region123 := by
  convert blocking_union_lemma _ _ ( Region12_blocking_thm ) ( Region3_blocking ) _ using 1;
  · unfold Region12;
    convert Set.Finite.isClosed_convexHull ( show Set.Finite { O_point, V_point, sigma V_point, X_point } from ?_ ) using 1;
    · exact Region12_eq_convexHull;
    · exact Set.toFinite _;
  · convert Set.Finite.isClosed_convexHull ( show Set.Finite { O_point, sigma V_point, sigma X_point } from ?_ ) using 1;
    exact Set.toFinite _;
  · exact fun x a ↦ Region12_inter_Region3_cover x a

/-
If S blocks R1 and R2, and the intersection of R1 and R2 within U is covered by S, then S blocks the union of R1 and R2 within U.
-/
lemma blocking_union_restricted {S : Set (Set Point)} {R1 R2 U : Set Point}
    (h_closed1 : IsClosed R1) (h_closed2 : IsClosed R2)
    (h_open : IsOpen U)
    (h_block1 : IsBlocking S R1)
    (h_block2 : IsBlocking S R2)
    (h_cover : ∀ x ∈ R1 ∩ R2 ∩ U, ∃ s ∈ S, x ∈ s) :
    ∀ L, IsUnitSegment L → L ⊆ U → L ⊆ R1 ∪ R2 → ∃ s ∈ S, ¬Disjoint s L := by
      intro L hL hL' hL'';
      by_cases hL1 : L ⊆ R1 <;> by_cases hL2 : L ⊆ R2;
      · exact Exists.imp ( by simp +contextual [ Set.disjoint_left ] ) ( h_block1 L hL hL1 );
      · exact h_block1 L hL hL1;
      · exact h_block2 L hL hL2;
      · -- Since L is not contained in R1 and not contained in R2, it must intersect both R1 \ R2 and R2 \ R1.
        obtain ⟨x1, hx1⟩ : ∃ x1 ∈ L, x1 ∈ R1 \ R2 := by
          grind
        obtain ⟨x2, hx2⟩ : ∃ x2 ∈ L, x2 ∈ R2 \ R1 := by
          grind;
        -- Since L is connected and R1, R2 are closed, L must intersect R1 ∩ R2.
        obtain ⟨x, hx⟩ : ∃ x ∈ L, x ∈ R1 ∩ R2 := by
          have h_connected : IsConnected L := by
            rcases hL with ⟨ A, B, hAB, rfl ⟩;
            rw [ openSegment_eq_image ];
            exact ⟨ Set.Nonempty.image _ ⟨ 1 / 2, by norm_num ⟩, isPreconnected_Ioo.image _ <| Continuous.continuousOn <| by continuity ⟩;
          have h_inter : IsPreconnected L := by
            exact h_connected.isPreconnected;
          contrapose! h_inter;
          norm_num [ IsPreconnected ];
          refine' ⟨ Set.univ \ R2, isOpen_univ.sdiff h_closed2, Set.univ \ R1, isOpen_univ.sdiff h_closed1, _, _, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
          · grind +ring;
          · exact ⟨ x1, hx1.1, by aesop ⟩;
          · exact ⟨ x2, hx2.1, by aesop ⟩;
          · exact fun ⟨ x, hx ⟩ => h_inter x hx.1 ( by cases hL'' x hx.1 <;> aesop ) ( by cases hL'' x hx.1 <;> aesop );
        exact Exists.elim ( h_cover x ⟨ hx.2, hL' hx.1 ⟩ ) fun s hs => ⟨ s, hs.1, Set.not_disjoint_iff_nonempty_inter.mpr ⟨ x, hs.2, hx.1 ⟩ ⟩

/-
Region123 is a closed set.
-/
lemma Region123_isClosed : IsClosed Region123 := by
  apply_rules [ IsClosed.union, convexHull_eq_iInter ];
  · convert Set.Finite.isClosed_convexHull ( show Set.Finite { O_point, V_point, sigma V_point } by exact Set.toFinite _ ) using 1;
  · -- The convex hull of a finite set of points in a finite-dimensional space is closed.
    have h_finite : Set.Finite {O_point, V_point, X_point} := by
      exact Set.toFinite _;
    convert h_finite.isClosed_convexHull;
  · -- The convex hull of a finite set of points is closed.
    have h_convex_hull_closed : ∀ (s : Set Point), s.Finite → IsClosed (convexHull ℝ s) := by
      intro s hs;
      convert Set.Finite.isClosed_convexHull hs;
    exact h_convex_hull_closed _ <| Set.toFinite _

/-
Region4 is closed.
-/
lemma Region4_isClosed : IsClosed Region4 := by
  exact Set.Finite.isClosed_convexHull ( Set.toFinite _ )

/-
Region5 is closed.
-/
lemma Region5_isClosed : IsClosed Region5 := by
  exact Set.Finite.isClosed_convexHull <| Set.toFinite { sigma X_point, sigma A_0, sigma Y_point }

/-
Region6_Total is closed.
-/
lemma Region6_Total_isClosed : IsClosed Region6_Total := by
  apply Set.Finite.isClosed_convexHull;
  exact Set.toFinite _

/-
Region_Square is an open set.
-/
lemma Region_Square_isOpen : IsOpen Region_Square := by
  convert isOpen_Ioo.preimage ( show Continuous fun p : Fin 2 → ℝ => p 0 from continuous_apply _ ) |> IsOpen.inter <| isOpen_Ioo.preimage ( show Continuous fun p : Fin 2 → ℝ => p 1 from continuous_apply _ ) using 1 ; ext ; simp +decide [ Region_Square ] ; tauto;

/-
L2 is non-positive at sigma X.
-/
lemma L2_sigma_X_le_0 : L2 (sigma X_point) ≤ 0 := by
  unfold L2 sigma X_point ; norm_num [ y1_bounds ];
  -- Since $x1 > 0$, we can divide both sides of the inequality by $x1$.
  have h_div : -(y1) ≤ 1 - x1 := by
    linarith [ y1_bounds, show x1 < 1 by
                            exact x1_prop.2.1.trans_le ( by norm_num ) ];
  nlinarith [ show 0 < x1 from by exact ( show 0 < x1 from by exact ( by obtain ⟨ hx_pos, hx_lt_one, hx_poly ⟩ := x1_prop; linarith ) ) ]

/-
L2 is an affine function.
-/
lemma L2_affine : ∀ (x y : Point) (a b : ℝ), a + b = 1 → L2 (a • x + b • y) = a * L2 x + b * L2 y := by
  unfold L2
  intro x y a b hab
  simp [hab]
  ring_nf
  skip;
  rw [ ← eq_sub_iff_add_eq' ] at hab ; subst_vars ; ring

/-
If L2 is non-positive on a set s, it is non-positive on the convex hull of s.
-/
lemma L2_convex_hull_le_0 (s : Set Point) (hs : ∀ p ∈ s, L2 p ≤ 0) : ∀ p ∈ convexHull ℝ s, L2 p ≤ 0 := by
  have h_convex : Convex ℝ {p : Point | L2 p ≤ 0} := by
    intro p hp q hq a b ha hb hab;
    convert Set.mem_setOf.mpr ( show L2 ( a • p + b • q ) ≤ 0 from ?_ ) using 1;
    rw [ show L2 ( a • p + b • q ) = a * L2 p + b * L2 q from ?_ ];
    · nlinarith [ hp.out, hq.out ];
    · convert L2_affine p q a b hab using 1;
  exact fun p hp => h_convex.convexHull_subset_iff.mpr hs hp

/-
L2 is non-positive on Region1.
-/
lemma Region1_sub_L2_le_0 : ∀ p ∈ Region1, L2 p ≤ 0 := by
  apply L2_convex_hull_le_0;
  -- By definition of $L2$, we know that $L2(O_point) < 0$, $L2(V_point) = 0$, and $L2(sigma V_point) \leq 0$.
  simp [L2_O_neg, L2_V, L2_sigma_V_le_0];
  exact le_of_lt ( L2_O_neg )

/-
L2 is non-positive on Region3.
-/
lemma Region3_sub_L2_le_0 : ∀ p ∈ Region3, L2 p ≤ 0 := by
  apply L2_convex_hull_le_0;
  rintro p ( rfl | rfl | rfl ) <;> [ exact le_of_lt L2_O_neg; exact L2_sigma_V_le_0; exact L2_sigma_X_le_0 ]

/-
L2 is non-positive on Region123.
-/
lemma Region123_sub_L2_le_0 : ∀ p ∈ Region123, L2 p ≤ 0 := by
  -- By definition of Region123, we know that every point in Region123 is in either Region1, Region2, or Region3.
  intros p hp
  cases' hp with hp1 hp2 hp3
  all_goals generalize_proofs at *;
  · cases' hp1 with hp1 hp2 hp3
    all_goals generalize_proofs at *;
    · exact Region1_sub_L2_le_0 p hp1;
    · exact Region2_sub_L2_le_0 p hp2;
  · exact Region3_sub_L2_le_0 p hp2

/-
The intersection of Region2 and the line L2=0 is the segment VX.
-/
lemma Region2_inter_L2_zero : Region2 ∩ {p | L2 p = 0} = segment ℝ V_point X_point := by
  unfold Region2;
  -- Let's choose any point $p$ in the convex hull of $\{O, V, X\}$ and show that it lies on the segment $VX$ if and only if $L2(p) = 0$.
  ext p
  apply Iff.intro;
  · intro hp
    obtain ⟨a, b, c, ha, hb, hc, habc, hp_eq⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • V_point + c • X_point := by
      norm_num [ convexHull_insert ] at hp;
      rcases hp.1 with ⟨ q, ⟨ a, b, ha, hb, hab, rfl ⟩, ⟨ c, d, hc, hd, hcd, rfl ⟩ ⟩ ; exact ⟨ c, a * d, b * d, hc, mul_nonneg ha hd, mul_nonneg hb hd, by nlinarith, by ext i; fin_cases i <;> simpa using by ring ⟩ ;
    -- Since $L2 p = 0$, we have $a * L2 O + b * L2 V + c * L2 X = 0$.
    have hL2_zero : a * L2 O_point + b * L2 V_point + c * L2 X_point = 0 := by
      have hL2_zero : L2 p = a * L2 O_point + b * L2 V_point + c * L2 X_point := by
        unfold L2; norm_num [ hp_eq ] ; ring_nf;
        rw [ ← eq_sub_iff_add_eq' ] at habc ; subst habc ; ring;
      exact hL2_zero ▸ hp.2;
    -- Since $L2 O < 0$, we must have $a = 0$.
    have ha_zero : a = 0 := by
      nlinarith [ L2_O_neg, L2_V, L2_X ];
    simp_all +decide [ segment_eq_image ];
    exact ⟨ c, ⟨ hc, by linarith ⟩, by rw [ ← eq_sub_iff_add_eq' ] at habc; subst habc; ring_nf ⟩;
  · rintro ⟨ a, b, ha, hb, hab, rfl ⟩;
    -- Since $a + b = 1$, the point $a • V_point + b • X_point$ is a convex combination of $V_point$ and $X_point$, which are both in the set $\{O_point, V_point, X_point\}$. Therefore, it is in the convex hull.
    have h_convex : a • V_point + b • X_point ∈ convexHull ℝ {O_point, V_point, X_point} := by
      rw [ convexHull_eq ];
      refine' ⟨ Fin 2, { 0, 1 }, fun i => if i = 0 then a else b, fun i => if i = 0 then V_point else X_point, _, _, _, _ ⟩ <;> simp +decide [ *, Finset.centerMass ];
    refine' ⟨ h_convex, _ ⟩;
    convert L2_affine V_point X_point a b hab using 1 ; norm_num [ L2_V, L2_X ]

/-
The intersection of Region1 and the line L2=0 is the singleton {V}.
-/
lemma Region1_inter_L2_zero : Region1 ∩ {p | L2 p = 0} = {V_point} := by
  ext p;
  constructor;
  · intro hp
    obtain ⟨a, b, c, ha, hb, hc, habc, hp_eq⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • V_point + c • sigma V_point := by
      have h_convex_comb : p ∈ convexHull ℝ {O_point, V_point, sigma V_point} := by
        exact hp.1;
      rw [ convexHull_insert ] at h_convex_comb;
      · norm_num [ segment_eq_image ] at h_convex_comb;
        obtain ⟨ i, hi, x, hx, rfl ⟩ := h_convex_comb; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext ; simpa using by ring ⟩ ;
      · norm_num +zetaDelta at *;
    -- Since $L2 O < 0$ and $L2 sigma V < 0$, and $a, c \geq 0$, we have $a * L2 O + c * L2 sigma V = 0$ implies $a = 0$ and $c = 0$.
    have h_a_c_zero : a * L2 O_point + c * L2 (sigma V_point) = 0 → a = 0 ∧ c = 0 := by
      have h_a_c_zero : L2 O_point < 0 ∧ L2 (sigma V_point) < 0 := by
        exact ⟨ L2_O_neg, L2_sigma_V_neg ⟩;
      exact fun h => ⟨ by nlinarith, by nlinarith ⟩;
    have hL2_p : L2 p = a * L2 O_point + b * L2 V_point + c * L2 (sigma V_point) := by
      unfold L2; simp +decide [ hp_eq ] ; ring_nf;
      rw [ ← eq_sub_iff_add_eq' ] at habc ; subst habc ; ring;
    specialize h_a_c_zero ( by nlinarith [ hp.2.symm, show L2 V_point = 0 from L2_V ] ) ; aesop;
  · rintro rfl;
    exact ⟨ subset_convexHull ℝ _ <| Set.mem_insert_of_mem _ <| Set.mem_insert _ _, L2_V ⟩

/-
L2 is strictly negative at sigma X.
-/
lemma L2_sigma_X_neg : L2 (sigma X_point) < 0 := by
  unfold L2 sigma X_point; norm_num; nlinarith [ x1_prop.1, x1_prop.2.1, y1_bounds ] ;

/-
The intersection of Region3 and the line L2=0 is empty.
-/
lemma Region3_inter_L2_zero : Region3 ∩ {p | L2 p = 0} = ∅ := by
  -- By definition of $L2$, we know that $L2$ is strictly negative at $O$, $sigma V$, and $sigma X$.
  have hL2_neg : ∀ p ∈ ({O_point, sigma V_point, sigma X_point} : Set Point), L2 p < 0 := by
    exact fun p hp => by rcases hp with ( rfl | rfl | rfl ) <;> [ exact L2_O_neg; exact L2_sigma_V_neg; exact L2_sigma_X_neg ] ;
  -- By definition of $L2$, we know that $L2$ is strictly affine and negative at $O$, $sigma V$, and $sigma X$.
  have hL2_strict_neg : ∀ p ∈ convexHull ℝ {O_point, sigma V_point, sigma X_point}, L2 p < 0 := by
    intro p hp
    have h_convex_comb : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • sigma V_point + c • sigma X_point := by
      rw [ convexHull_insert ] at hp;
      · norm_num [ segment_eq_image ] at hp;
        rcases hp with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext ; simpa using by ring ⟩ ;
      · exact ⟨ _, Set.mem_insert _ _ ⟩;
    obtain ⟨ a, b, c, ha, hb, hc, habc, rfl ⟩ := h_convex_comb;
    have hL2_strict_neg : L2 (a • O_point + b • sigma V_point + c • sigma X_point) = a * L2 O_point + b * L2 (sigma V_point) + c * L2 (sigma X_point) := by
      unfold L2; norm_num; ring_nf;
      rw [ ← eq_sub_iff_add_eq' ] at habc ; subst habc ; ring;
    cases lt_or_eq_of_le ha <;> cases lt_or_eq_of_le hb <;> cases lt_or_eq_of_le hc <;> first | nlinarith [ hL2_neg O_point ( by norm_num ), hL2_neg ( sigma V_point ) ( by norm_num ), hL2_neg ( sigma X_point ) ( by norm_num ) ] | skip;
  exact Set.eq_empty_of_forall_notMem fun p hp => hp.2.not_lt <| hL2_strict_neg p hp.1

/-
The intersection of Region123 and the line L2=0 is the segment VX.
-/
lemma Region123_inter_L2_zero : Region123 ∩ {p | L2 p = 0} = segment ℝ V_point X_point := by
  -- The intersection of Region123 and the line L2=0 is the union of the intersections of each region with the line.
  have h_union_intersections : Region123 ∩ {p | L2 p = 0} = (Region1 ∩ {p | L2 p = 0}) ∪ (Region2 ∩ {p | L2 p = 0}) ∪ (Region3 ∩ {p | L2 p = 0}) := by
    unfold Region123 Region12; ext; aesop;
  rw [ h_union_intersections, Region1_inter_L2_zero, Region2_inter_L2_zero, Region3_inter_L2_zero ] ; norm_num [ segment_eq_image ];
  exact ⟨ 0, by norm_num ⟩

/-
The intersection of Region123 and Region4 is contained in the segment XV.
-/
lemma Region123_inter_Region4_subset_segment_XV : Region123 ∩ Region4 ⊆ segment ℝ X_point V_point := by
  -- If $p$ is in both $Region123$ and $Region4$, then $p$ is in the segment $VX$ because $L2 p = 0$.
  intro p hp
  have hL2_zero : L2 p = 0 := by
    exact le_antisymm ( Region123_sub_L2_le_0 p hp.1 ) ( Region4_sub_L2_ge_0 p hp.2 ) ▸ rfl;
  have h_segment_VX : p ∈ segment ℝ V_point X_point := by
    exact Region123_inter_L2_zero.subset ⟨ hp.1, hL2_zero ⟩;
  rw [ segment_symm ] at h_segment_VX ; tauto

/-
Region4 is blocked by S_finite.
-/
lemma Region4_blocking_thm : IsBlocking S_finite Region4 := by
  -- By definition of $Region4$, any unit segment in $Region4$ must be one of the open sides of the triangle $XAY$.
  intro L hL hL_sub
  have h_segment : L = openSegment ℝ X_point A_0 ∨ L = openSegment ℝ A_0 Y_point ∨ L = openSegment ℝ Y_point X_point := by
    apply_rules [ triangle_diameter_lemma ];
    · exact le_of_lt dist_X_A0_lt_1;
    · exact le_of_lt ( dist_A0_Y_lt_1 );
    · rw [ dist_comm ] ; exact dist_X_Y.le;
  rcases h_segment with ( rfl | rfl | rfl ) <;> simp_all +decide [ Set.disjoint_left ];
  · contrapose! hL;
    convert not_isUnitSegment_of_dist_lt_1 _ using 1_1;
    convert dist_X_A0_lt_1 using 1;
  · exact absurd hL ( not_isUnitSegment_of_dist_lt_1 dist_A0_Y_lt_1 );
  · use segment4;
    simp [S_finite, segment4];
    exists ( 1 / 2 : ℝ ) • X_point + ( 1 / 2 : ℝ ) • Y_point;
    constructor <;> norm_num [ openSegment_eq_image ];
    · exact ⟨ 1 / 2, by norm_num ⟩;
    · exact ⟨ 1 / 2, by norm_num, by ext i; fin_cases i <;> norm_num [ Y_point, X_point ] ; ring ⟩

/-
The intersection of segment XV and Region_Square is covered by S_finite.
-/
lemma segment_XV_covered_by_S_finite : ∀ x ∈ segment ℝ X_point V_point, x ∈ Region_Square → ∃ s ∈ S_finite, x ∈ s := by
  intro x hx hx'
  by_cases hxV : x = V_point;
  · exact ⟨ segment4, by simp +decide [ S_finite ], hxV.symm ▸ V_on_segment4 ⟩;
  · -- Since $x$ is in $(X, V)$, we have $x \in \text{openSegment} \, \mathbb{R} \, X \, V$.
    have hx_openSegment : x ∈ openSegment ℝ X_point V_point := by
      rw [ segment_eq_image ] at hx;
      rcases hx with ⟨ θ, ⟨ hθ₀, hθ₁ ⟩, rfl ⟩ ; cases lt_or_eq_of_le hθ₀ <;> cases lt_or_eq_of_le hθ₁ <;> simp_all +decide [ openSegment_eq_image ] ;
      · exact ⟨ θ, ⟨ by linarith, by linarith ⟩, rfl ⟩;
      · subst_vars; exact absurd hx' ( by unfold Region_Square; norm_num [ X_point, V_point ] ) ;
    -- Since $V$ is in $\text{openSegment} \, \mathbb{R} \, X \, Y$, we have $x \in \text{openSegment} \, \mathbb{R} \, X \, Y$.
    have hx_openSegment_Y : x ∈ openSegment ℝ X_point Y_point := by
      -- Since $V$ is in $(X, Y)$, we have $V \in \text{openSegment} \, \mathbb{R} \, X_point \, Y_point$.
      have hV_openSegment : V_point ∈ openSegment ℝ X_point Y_point := by
        convert V_on_segment4 using 1;
      obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hx_openSegment;
      obtain ⟨ c, d, hc, hd, hcd, h ⟩ := hV_openSegment;
      refine' ⟨ a + b * c, b * d, _, _, _, _ ⟩ <;> try nlinarith;
      rw [ ← h ] ; ext i ; norm_num ; ring;
    exact ⟨ _, Set.mem_insert_of_mem _ ( Set.mem_insert_of_mem _ ( Set.mem_insert_of_mem _ ( Set.mem_insert _ _ ) ) ), hx_openSegment_Y ⟩

/-
Region1234 is blocked by S_finite in Region_Square.
-/
lemma Region1234_blocking_in_Square : ∀ L, IsUnitSegment L → L ⊆ Region_Square → L ⊆ Region123 ∪ Region4 → ∃ s ∈ S_finite, ¬Disjoint s L := by
  apply blocking_union_restricted;
  · exact Region123_isClosed
  · exact Region4_isClosed
  · exact Region_Square_isOpen
  · exact Region123_blocking
  · exact Region4_blocking_thm
  · intros x hx
    obtain ⟨hx1, hx2⟩ := hx;
    have := segment_XV_covered_by_S_finite x (Region123_inter_Region4_subset_segment_XV hx1) hx2;
    exact this

/-
Region123 ∪ Region4 is blocked by S_finite in Region_Square.
-/
lemma Region1234_blocking_in_Square_v2 : ∀ L, IsUnitSegment L → L ⊆ Region_Square → L ⊆ Region123 ∪ Region4 → ∃ s ∈ S_finite, ¬Disjoint s L := by
  intros L hL hL_sub hL_union
  apply Region1234_blocking_in_Square L hL hL_sub hL_union
  skip

/-
L3 is negative at X.
-/
lemma L3_X_neg : L3 X_point < 0 := by
  exact show y1 * ( 0 - x1 ) - x1 * ( 1 - x1 ) < 0 from by nlinarith [ x1_prop.1, x1_prop.2.1, y1_bounds.1, y1_bounds.2 ] ;

/-
If L3 is non-positive on a set s, it is non-positive on the convex hull of s.
-/
lemma L3_convex_hull_le_0 (s : Set Point) (hs : ∀ p ∈ s, L3 p ≤ 0) : ∀ p ∈ convexHull ℝ s, L3 p ≤ 0 := by
  rw [ convexHull_eq ];
  simp +contextual [ L3, Set.mem_setOf_eq ];
  intro p x s w hw hs' f hf hp; rw [ ← hp ] ; simp +decide [ *, Finset.centerMass ] ;
  rw [ Finset.sum_apply, Finset.sum_apply ];
  have := Finset.sum_le_sum fun i ( hi : i ∈ s ) => mul_le_mul_of_nonneg_left ( hs ( f i ) ( hf i hi ) ) ( hw i hi ) ; simp_all +decide [ mul_sub, sub_mul, mul_comm, Finset.mul_sum _ _ _, Finset.sum_mul ] ;
  simp_all +decide [ L3, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, sub_mul, mul_sub, mul_assoc, mul_comm, mul_left_comm ];
  simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ]

/-
L3 is negative at A0.
-/
lemma L3_A0_neg : L3 A_0 < 0 := by
  unfold L3 A_0; norm_num [ x1_prop ] ; ring_nf ;
  nlinarith [ y1_bounds.1, y1_bounds.2, x1_prop.1, x1_prop.2.1 ]

/-
L3 is non-positive on Region1.
-/
lemma Region1_sub_L3_le_0 : ∀ p ∈ Region1, L3 p ≤ 0 := by
  apply L3_convex_hull_le_0;
  simp +zetaDelta at *;
  exact ⟨ by linarith [ L3_O_neg ], by linarith [ L3_V_neg ], by linarith [ L3_sigma_V ] ⟩

/-
L3 is non-positive on Region2.
-/
lemma Region2_sub_L3_le_0 : ∀ p ∈ Region2, L3 p ≤ 0 := by
  exact fun p hp => L3_convex_hull_le_0 { O_point, V_point, X_point } ( by rintro p ( rfl | rfl | rfl ) <;> [ exact L3_O_neg.le; exact L3_V_neg.le; exact L3_X_neg.le ] ) p hp

/-
L3 is non-positive on Region123.
-/
lemma Region123_sub_L3_le_0 : ∀ p ∈ Region123, L3 p ≤ 0 := by
  exact fun p hp => by rcases hp with ( hp | hp ) <;> [ exact ( by rcases hp with ( hp | hp ) <;> [ exact Region1_sub_L3_le_0 p hp; exact Region2_sub_L3_le_0 p hp ] ) ; exact Region3_sub_L3_le_0 p hp ] ;

/-
L3 is non-positive on Region4.
-/
lemma Region4_sub_L3_le_0 : ∀ p ∈ Region4, L3 p ≤ 0 := by
  apply L3_convex_hull_le_0;
  norm_num [ L3_X_neg, L3_A0_neg, L3_Y_neg ];
  exact ⟨ le_of_lt ( L3_X_neg ), le_of_lt ( L3_A0_neg ), le_of_lt ( L3_Y_neg ) ⟩

/-
L3 is non-positive on Region1234.
-/
lemma Region1234_sub_L3_le_0 : ∀ p ∈ Region1234, L3 p ≤ 0 := by
  exact fun p hp => by rcases hp with ( hp | hp ) <;> [ exact Region123_sub_L3_le_0 p hp; exact Region4_sub_L3_le_0 p hp ] ;

/-
The intersection of Region5 and the line L3=0 is the segment [sigma X, sigma Y].
-/
lemma Region5_inter_L3_zero : Region5 ∩ {p | L3 p = 0} = segment ℝ (sigma X_point) (sigma Y_point) := by
  apply Set.ext
  intro p
  simp [Region5, segment];
  constructor;
  · intro hp
    obtain ⟨hp_convex, hp_L3⟩ := hp
    have hp_comb : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • sigma X_point + b • sigma A_0 + c • sigma Y_point := by
      rw [ convexHull_insert ] at hp_convex;
      · norm_num [ segment_eq_image ] at hp_convex;
        rcases hp_convex with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext ; simpa using by ring ⟩ ;
      · exact ⟨ _, Set.mem_insert _ _ ⟩;
    obtain ⟨ a, b, c, ha, hb, hc, habc, rfl ⟩ := hp_comb;
    -- Since $L3(sigma A_0) > 0$, we have $b = 0$.
    have hb_zero : b = 0 := by
      have hb_zero : b * L3 (sigma A_0) = 0 := by
        have hb_zero : L3 (a • sigma X_point + b • sigma A_0 + c • sigma Y_point) = a * L3 (sigma X_point) + b * L3 (sigma A_0) + c * L3 (sigma Y_point) := by
          unfold L3; norm_num; ring_nf;
          rw [ ← eq_sub_iff_add_eq' ] at habc ; subst habc ; ring;
        rw [ show L3 ( sigma X_point ) = 0 by exact L3_sigma_X ] at hb_zero ; rw [ show L3 ( sigma Y_point ) = 0 by exact L3_sigma_Y ] at hb_zero ; linarith;
      exact Or.resolve_right ( mul_eq_zero.mp hb_zero ) ( ne_of_gt ( L3_sigma_A0_pos ) );
    exact ⟨ a, ha, c, hc, by linarith, by simpa [ hb_zero ] ⟩;
  · rintro ⟨ a, ha, b, hb, hab, rfl ⟩;
    refine' ⟨ _, _ ⟩;
    · rw [ convexHull_eq ];
      refine' ⟨ Fin 2, { 0, 1 }, fun i => if i = 0 then a else b, fun i => if i = 0 then sigma X_point else sigma Y_point, _, _, _, _ ⟩ <;> simp +decide [ *, Finset.centerMass ];
    · unfold L3; norm_num [ show a = 1 - b by linarith ] ; ring_nf;
      unfold sigma; norm_num [ X_point, Y_point ] ; ring;

/-
L2 is negative at sigma Y.
-/
lemma L2_sigma_Y_neg : L2 (sigma Y_point) < 0 := by
  unfold L2 sigma Y_point; norm_num;
  have hy1_bounds : 0 < y1 ∧ y1 < 1 := by
    exact ⟨ by have := y1_bounds; norm_num at this; linarith, by have := y1_bounds; norm_num at this; linarith ⟩
  have hx1_bounds : 0.95 < x1 ∧ x1 < 0.96 := by
    exact ⟨ by linear_combination x1_prop.1, by linear_combination x1_prop.2.1 ⟩
  norm_num at *;
  nlinarith

/-
The intersection of Region1234 and Region5 is contained in the segment [sigma X, sigma Y].
-/
lemma Region1234_inter_Region5_subset_segment_sigmaX_sigmaY : Region1234 ∩ Region5 ⊆ segment ℝ (sigma X_point) (sigma Y_point) := by
  intro p hp
  obtain ⟨hp1234, hp5⟩ := hp
  have hL3_zero : L3 p = 0 := by
    exact le_antisymm ( Region1234_sub_L3_le_0 p hp1234 ) ( Region5_sub_L3_ge_0 p hp5 ) |> Eq.trans <| by norm_num;
  exact (by
  exact Region5_inter_L3_zero.subset ⟨ hp5, hL3_zero ⟩)

/-
Region1234 is closed.
-/
lemma Region1234_isClosed : IsClosed Region1234 := by
  convert IsClosed.union ( Region123_isClosed ) ( Region4_isClosed ) using 1

/-
Region12345 is blocked by S_finite in Region_Square.
-/
lemma Region12345_blocking_in_Square : ∀ L, IsUnitSegment L → L ⊆ Region_Square → L ⊆ Region12345 → ∃ s ∈ S_finite, ¬Disjoint s L := by
  have h_union : ∀ L, IsUnitSegment L → L ⊆ Region_Square → L ⊆ Region1234 ∪ Region5 → ∃ s ∈ S_finite, ¬Disjoint s L := by
    intros L hL hL_sub hL_union
    by_cases hL_subset_Region1234 : L ⊆ Region1234
    · exact Region1234_blocking_in_Square_v2 L hL hL_sub hL_subset_Region1234
    · by_cases hL_subset_Region5 : L ⊆ Region5;
      · exact Region5_blocking L hL hL_subset_Region5 |> fun ⟨ s, hs₁, hs₂ ⟩ => ⟨ s, hs₁, hs₂ ⟩;
      · -- Let x be a point in L that is not in Region1234.
        obtain ⟨x, hxL, hx_not_in_Region1234⟩ : ∃ x ∈ L, x ∉ Region1234 := by
          exact Set.not_subset.mp hL_subset_Region1234 |> Exists.imp fun x hx => by tauto;
        -- Let y be a point in L that is not in Region5.
        obtain ⟨y, hyL, hy_not_in_Region5⟩ : ∃ y ∈ L, y ∉ Region5 := by
          exact Set.not_subset.mp hL_subset_Region5;
        -- Since L is a unit segment, it is connected. Therefore, there must be a point z in L that is in both Region1234 and Region5.
        obtain ⟨z, hzL, hz_both⟩ : ∃ z ∈ L, z ∈ Region1234 ∧ z ∈ Region5 := by
          have h_connected : IsConnected L := by
            obtain ⟨ A, B, hAB, rfl ⟩ := hL;
            rw [ openSegment_eq_image ];
            exact ⟨ Set.Nonempty.image _ ⟨ 1 / 2, by norm_num ⟩, isPreconnected_Ioo.image _ <| Continuous.continuousOn <| by continuity ⟩;
          have h_connected : IsPreconnected L := by
            exact h_connected.isPreconnected;
          contrapose! h_connected;
          norm_num [ IsPreconnected ];
          refine' ⟨ Region1234ᶜ, _, Region5ᶜ, _, _, _, _ ⟩;
          · exact isOpen_compl_iff.mpr ( show IsClosed Region1234 from by exact Region1234_isClosed );
          · exact isOpen_compl_iff.mpr ( show IsClosed Region5 from by exact Region5_isClosed );
          · exact fun z hz => by specialize hL_union hz; aesop;;
          · exact ⟨ x, hxL, hx_not_in_Region1234 ⟩;
          · exact ⟨ ⟨ y, hyL, hy_not_in_Region5 ⟩, fun ⟨ z, hzL, hz_not_in_Region1234, hz_not_in_Region5 ⟩ => by have := hL_union hzL; aesop ⟩;
        -- Since $z$ is in both $Region1234$ and $Region5$, and $Region1234 \cap Region5 \subseteq segment5$, we have $z \in segment5$.
        have hz_segment5 : z ∈ segment5 := by
          have hz_segment5 : z ∈ segment ℝ (sigma X_point) (sigma Y_point) := by
            exact Region1234_inter_Region5_subset_segment_sigmaX_sigmaY ⟨ hz_both.1, hz_both.2 ⟩;
          have hz_not_endpoints : z ≠ sigma X_point ∧ z ≠ sigma Y_point := by
            constructor <;> intro h <;> simp_all +decide [ Region_Square ];
            · exact absurd ( hL_sub hzL ) ( by norm_num [ sigma, X_point ] );
            · have := hL_sub hzL; norm_num [ sigma, Y_point ] at this;
          rw [ segment_eq_image ] at *;
          obtain ⟨ θ, hθ, rfl ⟩ := hz_segment5; simp_all +decide [ segment5 ] ;
          rw [ openSegment_eq_image ];
          exact ⟨ θ, ⟨ lt_of_le_of_ne hθ.1 ( Ne.symm <| by aesop ), lt_of_le_of_ne hθ.2 ( by aesop ) ⟩, rfl ⟩;
        exact ⟨ segment5, by unfold S_finite; aesop, Set.not_disjoint_iff_nonempty_inter.mpr ⟨ z, hz_segment5, hzL ⟩ ⟩;
  grind

/-
sigma Y is not in the open unit square.
-/
lemma sigma_Y_not_in_Region_Square : sigma Y_point ∉ Region_Square := by
  exact fun h => by have := h.2.2.2; norm_num [ sigma, Y_point ] at this;

/-
y1 is greater than 0.5.
-/
lemma y1_gt_half : y1 > 0.5 := by
  unfold y1;
  -- Substitute the approximate values of V_point 0 and V_point 1.
  have h_approx : V_point 0 > 0.96 ∧ V_point 0 < 0.97 ∧ V_point 1 > 0.25 ∧ V_point 1 < 0.26 := by
    exact V_bounds;
  -- Substitute the approximate values of x1.
  have h_x1_approx : 0.95 < x1 ∧ x1 < 0.96 := by
    exact ⟨ by exact x1_prop.1, by exact x1_prop.2.1 ⟩;
  norm_num at * ; nlinarith [ mul_div_cancel₀ ( V_point 1 * ( 1 - x1 ) ) ( by linarith : ( V_point 0 - x1 ) ≠ 0 ) ] ;

/-
L2 is non-positive on Region6_Total.
-/
lemma Region6_Total_sub_L2_le_0 : ∀ p ∈ Region6_Total, L2 p ≤ 0 := by
  apply L2_convex_hull_le_0;
  simp [L2_V, L2_sigma_V_neg, L2_Y, L2_sigma_Y_neg, y1_bounds];
  exact ⟨ le_of_lt L2_sigma_V_neg, le_of_lt L2_sigma_Y_neg, by unfold L2; norm_num; nlinarith [ x1_prop.1, x1_prop.2.1, y1_bounds.1, y1_bounds.2 ] ⟩

/-
L1 is an affine function.
-/
lemma L1_affine : ∀ (x y : Point) (a b : ℝ), a + b = 1 → L1 (a • x + b • y) = a * L1 x + b * L1 y := by
  -- By definition of L1, we have L1 (a • x + b • y) = (a • x + b • y) 0 + (a • x + b • y) 1 - (V_point 0 + V_point 1).
  intro x y a b hab
  simp [L1];
  linear_combination' hab * ( V_point 0 + V_point 1 )

/-
If L1 is non-negative on a set s, it is non-negative on the convex hull of s.
-/
lemma L1_convex_hull_ge_0 (s : Set Point) (hs : ∀ p ∈ s, L1 p ≥ 0) : ∀ p ∈ convexHull ℝ s, L1 p ≥ 0 := by
  -- Since L1 is affine, the set {p | L1 p ≥ 0} is convex.
  have h_convex : Convex ℝ {p | L1 p ≥ 0} := by
    intro x hx y hy a b ha hb hab; rw [ Set.mem_setOf_eq ] at *; rw [ show L1 ( a • x + b • y ) = a * L1 x + b * L1 y by exact L1_convex_comb x y a b hab ] ; nlinarith;
  exact fun p hp => h_convex.convexHull_subset_iff.mpr hs hp

/-
L1 is positive at sigma Y.
-/
lemma L1_sigma_Y_pos : L1 (sigma Y_point) > 0 := by
  unfold L1 sigma Y_point;
  have h_sum_V : V_point 0 + V_point 1 = Real.sqrt 6 / 2 := by
    unfold V_point; ring_nf; norm_num;
    ring;
  have h_y1_gt_half : y1 > 0.5 := by
    exact y1_gt_half
  norm_num [ y1 ] at *;
  nlinarith [ Real.sqrt_nonneg 6, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ) ]

/-
L1 is positive at (1,1).
-/
lemma L1_Corner_pos : L1 ![1, 1] > 0 := by
  -- Substitute the values of V_point 0 and V_point 1 into the expression for L1(1,1).
  have hL1_val : L1 ![1, 1] = 1 + 1 - ((Real.sqrt 6 + Real.sqrt 2) / 4 + (Real.sqrt 6 - Real.sqrt 2) / 4) := by
    exact rfl;
  nlinarith [ Real.sqrt_nonneg 6, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ]

/-
L1 is non-negative on Region6_Total.
-/
lemma Region6_Total_sub_L1_ge_0 : ∀ p ∈ Region6_Total, L1 p ≥ 0 := by
  apply L1_convex_hull_ge_0;
  simp +zetaDelta at *;
  exact ⟨ by rw [ show L1 V_point = 0 by exact L1_V ], by rw [ show L1 ( sigma V_point ) = 0 by exact L1_sigma_V ], by exact le_of_lt ( L1_Y_pos ), by exact le_of_lt ( L1_sigma_Y_pos ), by exact le_of_lt ( L1_Corner_pos ) ⟩

/-
If S blocks R1 within U and blocks R2 globally, and the intersection in U is covered, then S blocks R1 ∪ R2 within U.
-/
lemma blocking_union_restricted_v2 {S : Set (Set Point)} {R1 R2 U : Set Point}
    (h_closed1 : IsClosed R1) (h_closed2 : IsClosed R2)
    (h_open : IsOpen U)
    (h_block1 : ∀ L, IsUnitSegment L → L ⊆ U → L ⊆ R1 → ∃ s ∈ S, ¬Disjoint s L)
    (h_block2 : IsBlocking S R2)
    (h_cover : ∀ x ∈ R1 ∩ R2 ∩ U, ∃ s ∈ S, x ∈ s) :
    ∀ L, IsUnitSegment L → L ⊆ U → L ⊆ R1 ∪ R2 → ∃ s ∈ S, ¬Disjoint s L := by
      intros L hL hL_sub_U hL_sub_R1R2
      by_cases hL_sub_R1 : L ⊆ R1;
      · exact h_block1 L hL hL_sub_U hL_sub_R1;
      · by_cases hL_sub_R2 : L ⊆ R2;
        · exact h_block2 L hL hL_sub_R2;
        · -- Since L is not contained in R1 and not contained in R2, it must intersect both R1 \ R2 and R2 \ R1.
          obtain ⟨x, hx⟩ : ∃ x ∈ L, x ∈ R1 ∧ x ∉ R2 := by
            grind
          obtain ⟨y, hy⟩ : ∃ y ∈ L, y ∈ R2 ∧ y ∉ R1 := by
            grind;
          -- Since L is connected and R1, R2 are closed, L must intersect R1 ∩ R2.
          obtain ⟨z, hz⟩ : ∃ z ∈ L, z ∈ R1 ∩ R2 := by
            have h_connected : IsConnected L := by
              obtain ⟨ a, b, hab ⟩ := hL;
              rw [ hab.2 ];
              rw [ openSegment_eq_image ];
              exact ⟨ Set.Nonempty.image _ ⟨ 1 / 2, by norm_num ⟩, isPreconnected_Ioo.image _ <| Continuous.continuousOn <| by continuity ⟩;
            have h_inter : IsPreconnected L := by
              exact h_connected.isPreconnected;
            contrapose! h_inter;
            norm_num [ IsPreconnected ];
            use Set.univ \ R2, isOpen_univ.sdiff h_closed2, Set.univ \ R1, isOpen_univ.sdiff h_closed1;
            simp_all +decide [ Set.Nonempty ];
            exact ⟨ fun z hz => by cases hL_sub_R1R2 hz <;> aesop, ⟨ x, hx.1, hx.2.2 ⟩, ⟨ y, hy.1, hy.2.2 ⟩, fun z hz hz' => by cases hL_sub_R1R2 hz <;> aesop ⟩;
          exact Exists.elim ( h_cover z ⟨ hz.2, hL_sub_U hz.1 ⟩ ) fun s hs => ⟨ s, hs.1, Set.not_disjoint_iff_nonempty_inter.mpr ⟨ z, hs.2, hz.1 ⟩ ⟩

/-
The union of all defined regions is contained in the union of Region12345 and Region6_Total.
-/
lemma UnionRegions_subset_Region12345_union_Region6_Total : UnionRegions ⊆ Region12345 ∪ Region6_Total := by
  unfold UnionRegions Region12345 Region6_Total;
  unfold Region6a Region6b Region_Corner Region1234; norm_num [ Set.subset_def ] ;
  intro x hx; rcases hx with ( ( ( ( ( ( hx | hx ) | hx ) | hx ) | hx ) | hx ) | hx ) <;> simp_all +decide [ Region123 ] ;
  · unfold Region12; aesop;
  · exact Or.inr ( convexHull_mono ( by aesop_cat ) hx );
  · refine Or.inr <| convexHull_mono ?_ hx;
    grind;
  · exact Or.inr ( convexHull_mono ( by norm_num [ Set.insert_subset_iff ] ) hx )

/-
The intersection of Region1 and Region6_Total is contained in the segment connecting V and sigma V.
-/
lemma Region1_inter_Region6_Total_subset : Region1 ∩ Region6_Total ⊆ segment ℝ V_point (sigma V_point) := by
  -- By definition of $Region1 \cap Region6_Total$, we know that $Region1 \cap Region6_Total \subseteq Region123 \cap {p | L1 p = 0}$.
  have h1 : Region1 ∩ Region6_Total ⊆ Region123 ∩ {p | L1 p = 0} := by
    intro p hp_inter;
    have h1 : p ∈ Region123 ∩ {p | L1 p = 0} := by
      have h1 : p ∈ Region123 := by
        exact Or.inl <| Or.inl hp_inter.1
      have h2 : p ∈ {p | L1 p = 0} := by
        have h2 : L1 p ≤ 0 := by
          exact Region123_sub_L1_le_0 p h1
        have h3 : L1 p ≥ 0 := by
          exact Region6_Total_sub_L1_ge_0 p hp_inter.2 |> le_trans ( by norm_num ) |> le_trans <| le_rfl
        exact le_antisymm h2 h3
      exact ⟨h1, h2⟩;
    exact h1;
  exact h1.trans ( Region123_inter_L1_zero ▸ Set.Subset.refl _ )

/-
L1 is non-positive on Region2.
-/
lemma Region2_sub_L1_le_0 : ∀ p ∈ Region2, L1 p ≤ 0 := by
  have h_affine : ∀ (x y : Point) (a b : ℝ), a + b = 1 → L1 (a • x + b • y) = a * L1 x + b * L1 y := by
    -- Apply the lemma L1_affine with the given parameters.
    apply L1_affine;
  -- By definition of convex hull, any point in Region2 can be written as a convex combination of O, V, and X.
  intro p hp
  obtain ⟨a, b, c, ha, hb, hc, hsum, hp_eq⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • V_point + c • X_point := by
    -- By definition of convex hull, any point in the convex hull of {O, V, X} can be written as a convex combination of O, V, and X.
    have h_convex_comb : ∀ p ∈ convexHull ℝ {O_point, V_point, X_point}, ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • V_point + c • X_point := by
      intro p hp
      rw [convexHull_insert] at hp;
      · norm_num [ segment_eq_image ] at hp;
        rcases hp with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext j; fin_cases j <;> simpa using by ring ⟩ ;
      · norm_num +zetaDelta at *;
    exact h_convex_comb p hp;
  have hL1_O : L1 O_point < 0 := by
    exact L1_O_neg
  have hL1_V : L1 V_point = 0 := by
    unfold L1 V_point; norm_num;
  have hL1_X : L1 X_point < 0 := by
    exact L1_X_neg;
  have hL1_p : L1 p = a * L1 O_point + b * L1 V_point + c * L1 X_point := by
    have hL1_p : L1 (a • O_point + b • V_point + c • X_point) = a * L1 O_point + b * L1 V_point + c * L1 X_point := by
      have h_comb : a • O_point + b • V_point + c • X_point = (a + b) • ((a / (a + b)) • O_point + (b / (a + b)) • V_point) + c • X_point := by
        by_cases hab : a + b = 0 <;> simp_all +decide [ div_eq_inv_mul, MulAction.mul_smul ];
        norm_num [ show a = 0 by linarith, show b = 0 by linarith ]
      by_cases hab : a + b = 0 <;> simp_all +decide [ add_assoc ];
      · exact Or.inl ( by linarith );
      · convert h_affine ( ( a / ( a + b ) ) • O_point + ( b / ( a + b ) ) • V_point ) X_point ( a + b ) c ( by linarith ) using 1 ; ring_nf;
        · simp +decide only [smul_add];
          rw [ add_assoc ];
        · grind;
    rw [hp_eq, hL1_p];
  nlinarith

/-
The intersection of Region2 and the line L1=0 is the singleton {V}.
-/
lemma Region2_inter_L1_zero : Region2 ∩ {p | L1 p = 0} = {V_point} := by
  apply Set.eq_singleton_iff_unique_mem.mpr;
  apply And.intro (by
  exact ⟨ subset_convexHull ℝ _ ( by norm_num [ V_point ] ), by unfold L1; norm_num [ V_point ] ⟩) (by
  intro p hp
  obtain ⟨hp2, hp1⟩ := hp
  have h_convex : ∃ a b c : ℝ, a + b + c = 1 ∧ a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ p = a • O_point + b • V_point + c • X_point := by
    have h_convex : p ∈ convexHull ℝ {O_point, V_point, X_point} := by
      grind;
    rw [ convexHull_insert ] at h_convex;
    · norm_num [ segment_eq_image ] at h_convex;
      rcases h_convex with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by ring, by nlinarith, by nlinarith, by nlinarith, by ext j; fin_cases j <;> norm_num <;> ring ⟩ ;
    · norm_num +zetaDelta at *;
  obtain ⟨ a, b, c, h₁, h₂, h₃, h₄, rfl ⟩ := h_convex; simp_all +decide [ funext_iff, Fin.forall_fin_two ] ;
  -- Since $L1(O) < 0$, $L1(V) = 0$, and $L1(X) < 0$, and $a, c \geq 0$, the equation $a*L1(O) + c*L1(X) = 0$ implies $a = 0$ and $c = 0$.
  have h_ac_zero : a = 0 ∧ c = 0 := by
    have h_ac_zero : a * L1 O_point + c * L1 X_point = 0 := by
      unfold L1 at *; norm_num [ Fin.sum_univ_succ ] at *;
      rw [ ← eq_sub_iff_add_eq' ] at h₁ ; subst_vars ; linarith!;
    have h_ac_zero : L1 O_point < 0 ∧ L1 X_point < 0 := by
      exact ⟨ L1_O_neg, L1_X_neg ⟩;
    constructor <;> nlinarith;
  aesop)

/-
The intersection of Region2 and Region6_Total is contained in the singleton {V}.
-/
lemma Region2_inter_Region6_Total_subset : Region2 ∩ Region6_Total ⊆ {V_point} := by
  intro p hp
  have hL1 : L1 p = 0 := by
    exact le_antisymm ( le_of_not_gt fun h => by linarith [ hp.1, hp.2, Region2_sub_L1_le_0 p hp.1, Region6_Total_sub_L1_ge_0 p hp.2 ] ) ( le_of_not_gt fun h => by linarith [ hp.1, hp.2, Region2_sub_L1_le_0 p hp.1, Region6_Total_sub_L1_ge_0 p hp.2 ] );
  exact Region2_inter_L1_zero.subset ⟨ hp.1, hL1 ⟩

/-
The intersection of Region3 and Region6_Total is contained in the singleton {sigma V}.
-/
lemma Region3_inter_Region6_Total_subset : Region3 ∩ Region6_Total ⊆ {sigma V_point} := by
  intro p hp
  have h_inter : p ∈ Region3 ∩ {p | L1 p = 0} := by
    have h_inter : p ∈ Region3 ∧ p ∈ Region6_Total ∧ L1 p ≤ 0 ∧ L1 p ≥ 0 := by
      exact ⟨ hp.1, hp.2, by linarith [ Region123_sub_L1_le_0 p ( Or.inr hp.1 ) ], by linarith [ Region6_Total_sub_L1_ge_0 p hp.2 ] ⟩;
    exact ⟨ h_inter.1, le_antisymm h_inter.2.2.1 h_inter.2.2.2 ⟩
  have h_sigma_V : p = sigma V_point := by
    exact Region3_inter_L1_zero.subset h_inter ▸ rfl
  exact h_sigma_V.symm ▸ Set.mem_singleton p
  skip

/-
The intersection of Region4 and the line L2=0 is the segment connecting X and Y.
-/
lemma Region4_inter_L2_zero : Region4 ∩ {p | L2 p = 0} = segment ℝ X_point Y_point := by
  apply Set.eq_of_subset_of_subset;
  · -- Any point p in Region4 ∩ {p | L2 p = 0} can be written as a convex combination of X_point, A_0, and Y_point.
    intro p hp
    obtain ⟨a, b, c, ha, hb, hc, habc, hp_eq⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • X_point + b • A_0 + c • Y_point := by
      have h_convex : p ∈ convexHull ℝ {X_point, A_0, Y_point} := by
        exact hp.1;
      rw [ convexHull_insert ] at h_convex;
      · norm_num [ segment_eq_image ] at h_convex;
        obtain ⟨ i, hi, x, hx, rfl ⟩ := h_convex; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext ; simpa using by ring ⟩ ;
      · norm_num +zetaDelta at *;
    -- Since $L2(p) = 0$, we have $b * L2(A0) = 0$. Given that $L2(A0) > 0$, it follows that $b = 0$.
    have hb_zero : b = 0 := by
      have hb_zero : b * L2 A_0 = 0 := by
        have hb_zero : L2 p = a * L2 X_point + b * L2 A_0 + c * L2 Y_point := by
          unfold L2; norm_num [ hp_eq ] ; ring_nf;
          rw [ ← eq_sub_iff_add_eq' ] at habc ; subst habc ; ring;
        have hL2_X : L2 X_point = 0 := by
          unfold L2 X_point; norm_num [ x1, y1 ] ;
        have hL2_Y : L2 Y_point = 0 := by
          unfold L2; norm_num [ Y_point ] ;
        simp_all +decide [ add_eq_zero_iff_eq_neg ];
      exact Or.resolve_right ( mul_eq_zero.mp hb_zero ) ( by linarith [ L2_A0_pos ] );
    exact ⟨ a, c, ha, hc, by linarith, by simp [ hb_zero, hp_eq ] ⟩;
  · intro p hp;
    -- Since $p$ is in the segment $X_point Y_point$, it is also in the convex hull of $\{X_point, A_0, Y_point\}$, which is $Region4$.
    have hp_region4 : p ∈ convexHull ℝ {X_point, A_0, Y_point} := by
      exact convexHull_mono ( by aesop_cat ) ( segment_subset_convexHull ( by aesop_cat ) ( by aesop_cat ) hp );
    refine' ⟨ hp_region4, _ ⟩;
    rw [ segment_eq_image ] at hp;
    rcases hp with ⟨ θ, ⟨ hθ₀, hθ₁ ⟩, rfl ⟩ ; norm_num [ L2 ] ; ring_nf;
    unfold X_point Y_point; norm_num; ring;

/-
Define t_V as (1 - V_point 0) / (1 - x1).
-/
noncomputable def t_V : ℝ := (1 - V_point 0) / (1 - x1)

/-
t_V is between 0 and 1.
-/
lemma t_V_bounds : 0 ≤ t_V ∧ t_V ≤ 1 := by
  unfold t_V;
  unfold V_point x1; norm_num;
  constructor
  all_goals generalize_proofs at *;
  · exact div_nonneg ( sub_nonneg.2 <| by nlinarith [ sq_nonneg <| Real.sqrt 6 - Real.sqrt 2, Real.mul_self_sqrt ( show 6 ≥ 0 by norm_num ), Real.mul_self_sqrt ( show 2 ≥ 0 by norm_num ) ] ) ( sub_nonneg.2 <| by linarith [ Classical.choose_spec ‹∃ x : ℝ, 19 / 20 < x ∧ x < 24 / 25 ∧ poly_X x = 0› ] );
  · rw [ div_le_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), Classical.choose_spec ‹∃ x : ℝ, 19 / 20 < x ∧ x < 24 / 25 ∧ poly_X x = 0› ]

/-
1 - x1 is not zero.
-/
lemma one_sub_x1_ne_zero : 1 - x1 ≠ 0 := by
  -- Since $x1$ is between 0.95 and 0.96, we have $1 - x1 > 0$.
  have h_pos : 1 - x1 > 0 := by
    field_simp;
    rw [ sub_pos ];
    have := Classical.choose_spec exists_root_x1;
    exact this.2.1.trans_le <| by norm_num;
  exact ne_of_gt h_pos

/-
The x-coordinate of V satisfies the convex combination formula.
-/
lemma V_eq_convex_comb_x : V_point 0 = t_V * X_point 0 + (1 - t_V) * Y_point 0 := by
  unfold V_point t_V X_point Y_point;
  -- Substitute the values of V_point 0 and x1 into the equation.
  field_simp [V_point, x1]
  ring_nf;
  field_simp;
  rw [ eq_comm, div_add', div_eq_iff ] <;> ring_nf;
  · unfold V_point x1; norm_num ; ring;
  · exact one_sub_x1_ne_zero;
  · exact one_sub_x1_ne_zero

/-
The y-coordinate of V satisfies the convex combination formula.
-/
lemma V_eq_convex_comb_y : V_point 1 = t_V * X_point 1 + (1 - t_V) * Y_point 1 := by
  unfold t_V X_point Y_point; norm_num; ring_nf; (
  unfold V_point y1 x1; norm_num; ring_nf;
  field_simp
  ring_nf
  generalize_proofs at *;
  unfold V_point; norm_num ; ring_nf;
  field_simp;
  rw [ eq_div_iff ] <;> ring_nf ; norm_num;
  · rename_i h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
    generalize_proofs at *;
    have := Classical.choose_spec h₇; norm_num [ poly_X ] at this; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_inv_cancel₀ ( show ( 1 - Classical.choose h₇ ) ≠ 0 by nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ] ) ] ;
  · have := Classical.choose_spec ‹_› ; norm_num at this ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ])

/-
V is a convex combination of X and Y with coefficient t_V for X.
-/
lemma V_eq_convex_comb : V_point = t_V • X_point + (1 - t_V) • Y_point := by
  ext i;
  fin_cases i <;> [ exact V_eq_convex_comb_x; exact V_eq_convex_comb_y ]

/-
The part of the segment XY where L1 is non-negative is contained in the segment VY.
-/
lemma L1_segment_XY_nonneg : ∀ p ∈ segment ℝ X_point Y_point, L1 p ≥ 0 → p ∈ segment ℝ V_point Y_point := by
  -- By definition of segment, we can write p as a convex combination of X and Y.
  intro p hp hL1
  obtain ⟨t, ht⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p = t • X_point + (1 - t) • Y_point := by
    rw [ segment_eq_image ] at hp;
    rcases hp with ⟨ t, ⟨ ht₀, ht₁ ⟩, rfl ⟩ ; exact ⟨ 1 - t, by linarith, by linarith, by ext i; fin_cases i <;> norm_num ⟩ ;
  -- Since $L1 p \geq 0$, we have $t \leq t_V$.
  have ht_le_t_V : t ≤ t_V := by
    have ht_le_t_V : L1 p = t * L1 X_point + (1 - t) * L1 Y_point := by
      unfold L1; norm_num [ ht ] ; ring;
    have ht_le_t_V : L1 X_point < 0 ∧ L1 Y_point > 0 := by
      exact ⟨ L1_X_neg, L1_Y_pos ⟩;
    have ht_le_t_V : L1 V_point = 0 := by
      exact L1_V;
    have ht_le_t_V : L1 V_point = t_V * L1 X_point + (1 - t_V) * L1 Y_point := by
      have ht_le_t_V : V_point = t_V • X_point + (1 - t_V) • Y_point := by
        exact V_eq_convex_comb;
      rw [ht_le_t_V];
      convert L1_affine X_point Y_point t_V ( 1 - t_V ) ( by ring ) using 1;
    nlinarith;
  -- Since $t \leq t_V$, we can write $p$ as a convex combination of $V$ and $Y$.
  obtain ⟨s, hs⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ p = s • V_point + (1 - s) • Y_point := by
    -- Substitute V_point from V_eq_convex_comb into the expression for p.
    have hp_sub : p = (t / t_V) • (t_V • X_point + (1 - t_V) • Y_point) + (1 - t / t_V) • Y_point := by
      by_cases h : t_V = 0 <;> simp_all +decide [ div_eq_inv_mul, mul_assoc, mul_left_comm, smul_smul ] ; ring_nf;
      · norm_num [ show t = 0 by linarith ] at *;
      · ext i ; norm_num ; ring_nf;
        norm_num [ h ];
    exact ⟨ t / t_V, div_nonneg ht.1 ( t_V_bounds.1 ), div_le_one_of_le₀ ( by linarith ) ( t_V_bounds.1 ), hp_sub.trans ( by rw [ V_eq_convex_comb ] ) ⟩;
  exact hs.2.2 ▸ ⟨ s, 1 - s, by linarith, by linarith, by simp +decide [ hs.2.2 ] ⟩

/-
The intersection of Region4 and Region6_Total is contained in the segment connecting V and Y.
-/
lemma Region4_inter_Region6_Total_subset : Region4 ∩ Region6_Total ⊆ segment ℝ V_point Y_point := by
  intro p hp
  obtain ⟨hp4, hp6⟩ := hp
  have hL2 : L2 p = 0 := by
    -- Since $p$ is in both Region4 and Region6_Total, we have $L2 p \geq 0$ and $L2 p \leq 0$, which implies $L2 p = 0$.
    have hL2_nonneg : L2 p ≥ 0 := by
      exact Region4_sub_L2_ge_0 p hp4
    have hL2_nonpos : L2 p ≤ 0 := by
      exact Region6_Total_sub_L2_le_0 p hp6
    exact le_antisymm hL2_nonpos hL2_nonneg
  have hp_segment_XY : p ∈ segment ℝ X_point Y_point := by
    exact Region4_inter_L2_zero.subset ⟨ hp4, hL2 ⟩
  have hp_segment_VY : p ∈ segment ℝ V_point Y_point := by
    apply L1_segment_XY_nonneg p hp_segment_XY (Region6_Total_sub_L1_ge_0 p hp6)
  exact hp_segment_VY

/-
Define S_verts as the set {V, sigma V, Y, sigma Y, Corner}.
-/
def S_verts : Set Point := {V_point, sigma V_point, Y_point, sigma Y_point, Corner_point}

/-
Region6_Total is the convex hull of S_verts.
-/
lemma Region6_Total_eq_convexHull_S_verts : Region6_Total = convexHull ℝ S_verts := by
  exact rfl

/-
Region6_Total is symmetric under sigma.
-/
lemma Region6_Total_symmetric : ∀ p, p ∈ Region6_Total ↔ sigma p ∈ Region6_Total := by
  intro p;
  -- By definition of $Region6_Total$, we know that $p \in Region6_Total$ if and only if $p$ is in the convex hull of $S_verts$.
  simp [Region6_Total_eq_convexHull_S_verts];
  -- By definition of convex hull, we know that $p \in \text{conv}(S_verts)$ if and only if there exist points $x_1, x_2, \ldots, x_n \in S_verts$ and coefficients $a_1, a_2, \ldots, a_n \geq 0$ with $\sum_{i=1}^n a_i = 1$ such that $p = \sum_{i=1}^n a_i x_i$.
  simp [convexHull];
  constructor <;> intro h a ha ha' <;> have := h ( a.preimage ( fun x => sigma x ) ) ?_ ?_ <;> simp_all +decide [ Set.preimage ];
  · intro x hx; have := ha hx; simp_all +decide [ S_verts ] ;
    rcases hx with ( rfl | rfl | rfl | rfl | rfl ) <;> simp_all +decide [ Set.insert_subset_iff, sigma ];
    · exact ha.1;
    · convert ha.2.2.1 using 1;
    · convert this using 1;
  · intro x hx y hy a b ha hb hab; simp_all +decide [ sigma ] ;
    convert ha' hx hy ha hb hab using 1 ; ext i ; fin_cases i <;> norm_num;
  · convert this using 1 ; ext i ; fin_cases i <;> rfl;
  · -- Since $S_verts$ is closed under $\sigma$, for any $x \in S_verts$, $\sigma(x) \in S_verts$.
    have h_sigma_S_verts : ∀ x ∈ S_verts, sigma x ∈ S_verts := by
      unfold S_verts; aesop;
    exact fun x hx => ha ( h_sigma_S_verts x hx );
  · intro x hx y hy a b ha hb hab; simp_all +decide [ sigma ] ;
    convert ha' hx hy ha hb hab using 1 ; ext i ; fin_cases i <;> norm_num

/-
The intersection of Region5 and Region6_Total is contained in the segment connecting sigma V and sigma Y.
-/
lemma Region5_inter_Region6_Total_subset : Region5 ∩ Region6_Total ⊆ segment ℝ (sigma V_point) (sigma Y_point) := by
  intro x hx;
  -- Since sigma x is in Region4 Region6_Total, by Region4_inter_Region6_Total_subset, sigma x is in the segment between V_point and Y_point.
  have h_sigma_x_segment : sigma x ∈ segment ℝ V_point Y_point := by
    -- Since $x \in \text{Region5}$, we have $\sigma(x) \in \text{Region4}$.
    have h_sigma_x_region4 : sigma x ∈ Region4 := by
      exact ( mem_Region5_iff_sigma_mem_Region4 x ).mp hx.1;
    apply Region4_inter_Region6_Total_subset;
    -- Since $x \in \text{Region6_Total}$, we have $\sigma(x) \in \text �{�Region6_Total}$ by the symmetry of $\text{Region6_Total}$.
    have h_sigma_x_region6_total : sigma x ∈ Region6_Total := by
      exact Region6_Total_symmetric x |>.1 hx.2;
    grind;
  obtain ⟨ a, b, ha, hb, hab, h ⟩ := h_sigma_x_segment;
  use a, b;
  simp_all +decide [ ← eq_sub_iff_add_eq', funext_iff, Fin.forall_fin_two ];
  convert congr_arg sigma h using 1 ; norm_num [ sigma ] ; ring_nf;
  · ext i; fin_cases i <;> norm_num <;> ring;
  · ext i ; fin_cases i <;> norm_num [ sigma ] <;> ring!

/-
The segment connecting V and Y, excluding Y, is contained in segment4.
-/
lemma segment_V_Y_diff_Y_subset_segment4 : segment ℝ V_point Y_point \ {Y_point} ⊆ segment4 := by
  unfold segment4;
  -- Since $V$ is between $X$ and $Y$, any point on the segment from $V$ to $Y$ (excluding $Y$) is in the open segment from $X$ to $Y$.
  have hV_between_XY : V_point ∈ openSegment ℝ X_point Y_point := by
    convert V_on_segment4 using 1;
  obtain ⟨ a, b, ha, hb, hab, h ⟩ := hV_between_XY;
  intro x hx; obtain ⟨ u, v, hu, hv, huv, rfl ⟩ := hx.1; simp_all +decide [ ← eq_sub_iff_add_eq' ] ;
  refine' ⟨ u * a, 1 - u * a, _, _, _ ⟩ <;> try nlinarith;
  · cases lt_or_eq_of_le hu <;> aesop;
  · exact ⟨ by linarith, by rw [ show V_point = a • X_point + ( 1 - a ) • Y_point by ext i; have := congr_fun h i; norm_num at *; linarith ] ; ext i; norm_num; ring ⟩

/-
The segment connecting sigma V and sigma Y, excluding sigma Y, is contained in segment5.
-/
lemma segment_sigmaV_sigmaY_diff_sigmaY_subset_segment5 : segment ℝ (sigma V_point) (sigma Y_point) \ {sigma Y_point} ⊆ segment5 := by
  -- By definition of segment5, if x is in segment ℝ � (�sigma V_point) (sigma Y_point) and x ≠ sigma Y_point, then x must be in segment5.
  intros x hx
  obtain ⟨hx_segment, hx_ne⟩ := hx;
  -- By definition of segment, � there� exists t ∈ [0, 1] such that x = t • sigma V_point + (1 - t) • sigma Y_point.
  obtain ⟨t, ht₀, ht₁⟩ : ∃ t ∈ Set.Icc (0 : ℝ) 1, x = t • sigma V_point + (1 - t) • sigma Y_point := by
    rw [ segment_eq_image ] at hx_segment;
    rcases hx_segment with ⟨ t, ht, rfl ⟩ ; exact ⟨ 1 - t, ⟨ by linarith [ ht.1, ht.2 ], by linarith [ ht.1, ht.2 ] ⟩, by ring_nf ⟩ ;
  cases eq_or_lt_of_le ht₀.1 <;> cases eq_or_lt_of_le ht₀.2 <;> simp_all +decide [ segment_eq_image ];
  · aesop;
  · exact sigma_V_on_segment5;
  · have h_open_segment : sigma V_point ∈ openSegment ℝ (sigma X_point) (sigma Y_point) := by
      convert sigma_V_on_segment5 using 1;
    obtain ⟨ u, v, hu, hv, huv, h ⟩ := h_open_segment;
    exact ⟨ t * u, t * v + ( 1 - t ), by nlinarith, by nlinarith, by nlinarith, by ext i; have := congr_fun h i; norm_num at *; nlinarith ⟩

/-
Y is not in the open unit square.
-/
lemma Y_notin_Region_Square : Y_point ∉ Region_Square := by
  -- Since $Y_point 0 = 1$, it is not in the open unit square.
  simp [Region_Square, Y_point]

/-
sigma Y is not in the open unit square.
-/
lemma sigma_Y_notin_Region_Square : sigma Y_point ∉ Region_Square := by
  exact sigma_Y_not_in_Region_Square

/-
The intersection of Region4, Region6_Total, and Region_Square is covered by S_finite.
-/
lemma Region4_inter_Region6_Total_inter_Square_covered :
  ∀ x ∈ Region4 ∩ Region6_Total ∩ Region_Square, ∃ s ∈ S_finite, x ∈ s := by
    intros x hx; exact ⟨ segment4, by simp [ S_finite ], by
      apply segment_V_Y_diff_Y_subset_segment4;
      have hx_segment : x ∈ segment ℝ V_point Y_point := by
        exact Region4_inter_Region6_Total_subset ⟨ hx.1.1, hx.1.2 ⟩ |> fun h => h |> fun h => by
          exact h;
      have hx_ne_Y : x ≠ Y_point := by
        exact fun h => hx.2 |> fun h' => by rw [ h ] at h'; exact Y_notin_Region_Square h';
      exact ⟨hx_segment, hx_ne_Y⟩ ⟩

/-
The intersection of Region5, Region6_Total, and Region_Square is covered by S_finite.
-/
lemma Region5_inter_Region6_Total_inter_Square_covered :
  ∀ x ∈ Region5 ∩ Region6_Total ∩ Region_Square, ∃ s ∈ S_finite, x ∈ s := by
    intros x hx; exact ⟨ segment5, by
      exact Or.inr <| by tauto;, by
      apply segment_sigmaV_sigmaY_diff_sigmaY_subset_segment5;
      exact ⟨ by exact Region5_inter_Region6_Total_subset ⟨ hx.1.1, hx.1.2 ⟩, by rintro rfl; exact sigma_Y_notin_Region_Square hx.2 ⟩ ⟩ ;

/-
The intersection of Region1, Region6_Total, and Region_Square is covered by S_finite.
-/
lemma Region1_inter_Region6_Total_inter_Square_covered :
  ∀ x ∈ Region1 ∩ Region6_Total ∩ Region_Square, ∃ s ∈ S_finite, x ∈ s := by
    intro x hx;
    have := Region1_inter_Region6_Total_subset ⟨ hx.1.1, hx.1.2 ⟩;
    -- The segment [V, sigma V] � is� the union of openSegment V (sigma V) (which is segment3) and the endpoints {V, sigma V}.
    have h_segment : x ∈ openSegment ℝ V_point (sigma V_point) ∨ x = V_point ∨ x = sigma V_point := by
      rw [ segment_eq_image ] at this;
      rcases this with ⟨ θ, hθ, rfl ⟩ ; cases eq_or_lt_of_le hθ.1 <;> cases eq_or_lt_of_le hθ.2 <;> simp_all +decide [ openSegment_eq_image ] ;
      · aesop;
      · grind;
    rcases h_segment with ( h | rfl | rfl );
    · exact ⟨ segment3, by unfold S_finite; norm_num, h ⟩;
    · -- Since V_point is in segment4, we can conclude that there exists a segment in S_finite containing V_point.
      use segment4
      simp [S_finite];
      exact V_on_segment4;
    · exact ⟨ segment5, by
        exact Set.mem_insert_of_mem _ ( Set.mem_insert_of_mem _ ( Set.mem_insert_of_mem _ ( Set.mem_insert_of_mem _ ( Set.mem_singleton _ ) ) ) ), by
        exact sigma_V_on_segment5 ⟩

/-
The intersection of Region2, Region6_Total, and Region_Square is covered by S_finite.
-/
lemma Region2_inter_Region6_Total_inter_Square_covered :
  ∀ x ∈ Region2 ∩ Region6_Total ∩ Region_Square, ∃ s ∈ S_finite, x ∈ s := by
    simp +zetaDelta at *;
    intro x hx1 hx2 hx3
    have hx4 : x = V_point := by
      exact Region2_inter_Region6_Total_subset ⟨ hx1, hx2 ⟩ |> fun h => by aesop;
    generalize_proofs at *;
    exact ⟨ segment4, Or.inr <| Or.inr <| Or.inr <| Or.inl rfl, by simpa [ hx4 ] using V_on_segment4 ⟩

/-
The intersection of Region3, Region6_Total, and Region_Square is covered by S_finite.
-/
lemma Region3_inter_Region6_Total_inter_Square_covered :
  ∀ x ∈ Region3 ∩ Region6_Total ∩ Region_Square, ∃ s ∈ S_finite, x ∈ s := by
    intros x hx; exact ⟨ segment5, by simp [ S_finite ], by
      -- Since $x$ is in $Region3 \cap Region6_Total$, we have $x = \sigma(V)$.
      have hx_sigma_V : x = sigma V_point := by
        exact Set.eq_of_mem_singleton ( Region3_inter_Region6_Total_subset hx.1 )
      rw [hx_sigma_V]
      exact sigma_V_on_segment5 ⟩

/-
The intersection of Region12345, Region6_Total, and Region_Square is covered by S_finite.
-/
lemma IntersectionSet_covered : ∀ x ∈ Region12345 ∩ Region6_Total ∩ Region_Square, ∃ s ∈ S_finite, x ∈ s := by
  have h_cover;
  have h_cases : ∀ x ∈ Region12345 ∩ Region6_Total ∩ Region_Square, x ∈ Region1 ∪ Region2 ∪ Region3 ∪ Region4 ∪ Region5 := by
    unfold Region12345 at *; aesop;
  assumption;
  intro x hx;
  rcases h_cover x hx with ( ( ( ( h | h ) | h ) | h ) | h ) <;> [ exact Region1_inter_Region6_Total_inter_Square_covered x ⟨ ⟨ h, hx.1.2 ⟩, hx.2 ⟩ ; exact Region2_inter_Region6_Total_inter_Square_covered x ⟨ ⟨ h, hx.1.2 ⟩, hx.2 ⟩ ; exact Region3_inter_Region6_Total_inter_Square_covered x ⟨ ⟨ h, hx.1.2 ⟩, hx.2 ⟩ ; exact Region4_inter_Region6_Total_inter_Square_covered x ⟨ ⟨ h, hx.1.2 ⟩, hx.2 ⟩ ; exact Region5_inter_Region6_Total_inter_Square_covered x ⟨ ⟨ h, hx.1.2 ⟩, hx.2 ⟩ ]

/-
Region12345 is a closed set.
-/
lemma Region12345_isClosed : IsClosed Region12345 := by
  -- The union of two closed sets is closed.
  apply IsClosed.union; exact Region1234_isClosed; exact Region5_isClosed;

/-
S_finite blocks the open unit square.
-/
lemma S_finite_blocks_Region_Square : IsBlocking S_finite Region_Square := by
  -- Apply the blocking_union_restricted_v2 lemma with the conditions we have established.
  have h_apply : ∀ L, IsUnitSegment L → L ⊆ Region_Square → L ⊆ Region12345 ∪ Region6_Total → ∃ s ∈ S_finite, ¬Disjoint s L := by
    apply blocking_union_restricted_v2;
    · exact Region12345_isClosed
    · exact Region6_Total_isClosed
    · exact Region_Square_isOpen
    · exact fun L a a_1 a_2 ↦ Region12345_blocking_in_Square L a a_1 a_2
    · exact Region6_Total_blocking
    · exact fun x a ↦ IntersectionSet_covered x a
  -- Since `Region_Square UnionRegions` and `Union �Regions Region1234 �5 Region6_Total`, any unit segment in `Region_Square` is in `Region12345 ∪ Region6_Total`.
  have h_subset : Region_Square ⊆ Region12345 ∪ Region6_Total := by
    -- Since `Region_Square` is a subset of `UnionRegions`, and � `�UnionRegions` is a subset of `Region12345 ∪ Region6_Total`, we can conclude that `Region_Square` is a subset of `Region12345 ∪ Region6_Total`.
    have h_subset : Region_Square ⊆ UnionRegions := by
      exact Region_Square_subset_UnionRegions;
    exact h_subset.trans ( by exact UnionRegions_subset_Region12345_union_Region6_Total );
  exact fun L hL hL' => h_apply L hL hL' ( hL'.trans h_subset )

/-
The unit square is the union of the open square, the open sides, and the corners.
-/
def SquareCorners : Set Point := {![0, 0], ![0, 1], ![1, 0], ![1, 1]}

lemma UnitSquare_decomposition (p : Point) (hp : p ∈ UnitSquare) :
  p ∈ Region_Square ∨ (∃ s ∈ S_sides, p ∈ s) ∨ p ∈ SquareCorners := by
    unfold Region_Square S_sides SquareCorners UnitSquare at *;
    cases lt_or_eq_of_le ( hp 0 |>.2 ) <;> cases lt_or_eq_of_le ( hp 1 |>.2 ) <;> simp_all +decide [ Fin.forall_fin_two ];
    · by_cases h0 : p 0 = 0 <;> by_cases h1 : p 1 = 0 <;> simp_all +decide [ V_L, V_R, H_bot, H_top ];
      · exact Or.inr <| Or.inl <| by ext i; fin_cases i <;> aesop;
      · simp_all +decide [ openSegment, funext_iff, Fin.forall_fin_two ];
        exact Or.inl <| Or.inl ⟨ 1 - p 1, by linarith, p 1, by linarith [ show 0 < p 1 from lt_of_le_of_ne hp.1 ( Ne.symm h1 ) ], by linarith, by ext i; fin_cases i <;> simp +decide [ h0 ] ⟩;
      · refine Or.inl <| Or.inr <| Or.inr <| Or.inl <| ?_;
        rw [ openSegment_eq_image ];
        exact ⟨ p 0, ⟨ lt_of_le_of_ne hp.1 ( Ne.symm h0 ), by linarith ⟩, by ext i; fin_cases i <;> simp +decide [ * ] ⟩;
      · grind;
    · cases lt_or_eq_of_le hp.1 <;> simp_all +decide [ H_top ];
      · refine Or.inl <| Or.inr <| Or.inr <| Or.inr <| ?_;
        refine' ⟨ 1 - p 0, p 0, _, _, _ ⟩ <;> norm_num [ * ];
        ext i ; fin_cases i <;> norm_num ; linarith!;
        (expose_names; exact id (Eq.symm h_1));
      · exact Or.inr <| Or.inr <| Or.inl <| by ext i; fin_cases i <;> aesop;
    · by_cases h : p 1 = 0 <;> simp_all +decide [ V_L, V_R, H_bot, H_top ];
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <| by ext i; fin_cases i <;> aesop;
      · refine' Or.inl <| Or.inr <| Or.inl <| _;
        refine' ⟨ 1 - p 1, p 1, _, _, _ ⟩ <;> norm_num [ *, openSegment_eq_image ];
        · exact lt_of_le_of_ne hp.1 ( Ne.symm h );
        · ext i ; fin_cases i <;> norm_num ; linarith!;
          rfl;
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| by ext i; fin_cases i <;> assumption;

/-
The unit square is a closed set.
-/
lemma UnitSquare_isClosed : IsClosed UnitSquare := by
  unfold UnitSquare;
  simp +decide only [setOf_forall];
  refine' isClosed_iInter fun i => _;
  exact isClosed_Icc.preimage ( continuous_apply i )

/-
If a corner of the unit square lies in the open segment between two points in the square, then those two points must be equal to the corner.
-/
lemma SquareCorners_extreme_v2 (c : Point) (hc : c ∈ SquareCorners) (x y : Point) (hx : x ∈ UnitSquare) (hy : y ∈ UnitSquare) (h : c ∈ openSegment ℝ x y) : x = c ∧ y = c := by
  rcases hc with ( rfl | rfl | rfl | rfl ) <;> simp +decide [ *, openSegment ] at h ⊢;
  · obtain ⟨ a, ha, b, hb, hab, h ⟩ := h; have := congr_fun h 0; have := congr_fun h 1; simp_all +decide [ ← eq_sub_iff_add_eq' ] ;
    have := congr_fun h 0; have := congr_fun h 1; norm_num at *; exact ⟨ by ext i; fin_cases i <;> norm_num <;> nlinarith! [ hx 0, hx 1, hy 0, hy 1 ], by ext i; fin_cases i <;> norm_num <;> nlinarith! [ hx 0, hx 1, hy 0, hy 1 ] ⟩ ;
  · obtain ⟨ a, ha, b, hb, hab, h ⟩ := h;
    simp_all +decide [ ← List.ofFn_inj, UnitSquare ];
    have := congr_fun h 0; have := congr_fun h 1; norm_num at *; exact ⟨ by ext i; fin_cases i <;> norm_num <;> nlinarith !, by ext i; fin_cases i <;> norm_num <;> nlinarith ! ⟩ ;
  · rcases h with ⟨ a, ha, b, hb, hab, h ⟩ ; have := congr_fun h 0 ; have := congr_fun h 1 ; norm_num at *;
    -- Since $x$ and $y$ are in the unit square, we have $0 \leq x 0 \leq 1$ and $0 \leq y 0 \leq 1$, and similarly for $x 1$ and $y 1$.
    have hx0 : 0 ≤ x 0 ∧ x 0 ≤ 1 := by
      exact ⟨ hx 0 |>.1, hx 0 |>.2 ⟩
    have hy0 : 0 ≤ y 0 ∧ y 0 ≤ 1 := by
      exact ⟨ hy 0 |>.1, hy 0 |>.2 ⟩
    have hx1 : 0 ≤ x 1 ∧ x 1 ≤ 1 := by
      exact ⟨ hx 1 |>.1, hx 1 |>.2 ⟩
    have hy1 : 0 ≤ y 1 ∧ y 1 ≤ 1 := by
      exact ⟨ hy 1 |>.1, hy 1 |>.2 ⟩;
    -- Since $a$ and $b$ are positive and their sum is $1$, we can solve for $x_0$ and $y_0$.
    have hx0_eq : x 0 = 1 := by
      nlinarith
    have hy0_eq : y 0 = 1 := by
      nlinarith
    have hx1_eq : x 1 = 0 := by
      nlinarith [ ha, hb, hab, this, hx1, hy1 ]
    have hy1_eq : y 1 = 0 := by
      nlinarith;
    exact ⟨ by ext i; fin_cases i <;> assumption, by ext i; fin_cases i <;> assumption ⟩;
  · obtain ⟨ a, ha, b, hb, hab, h ⟩ := h; simp_all +decide [ ← List.ofFn_inj, Point ] ;
    simp_all +decide [ ← List.ofFn_inj, UnitSquare ];
    have := congr_fun h 0; have := congr_fun h 1; norm_num at *; exact ⟨ by ext i; fin_cases i <;> norm_num <;> nlinarith !, by ext i; fin_cases i <;> norm_num <;> nlinarith ! ⟩ ;

/-
If a unit segment in the closed unit square is disjoint from the sides, it is in the open unit square.
-/
lemma unit_segment_in_UnitSquare_disjoint_S_sides_implies_in_Region_Square (L : Set Point) (hL : IsUnitSegment L) (h_sub : L ⊆ UnitSquare) (h_disj : ∀ s ∈ S_sides, Disjoint s L) : L ⊆ Region_Square := by
  -- By `UnitSquare_decomposition`, `L ⊆ Region_Square ∪ SquareCorners`.
  have hL_decomp : L ⊆ Region_Square ∪ SquareCorners := by
    intro p hp
    have hp_unit : p ∈ UnitSquare := h_sub hp
    have hp_decomp : p ∈ Region_Square ∨ p ∈ SquareCorners ∨ ∃ s ∈ S_sides, p ∈ s := by
      have := UnitSquare_decomposition p hp_unit; aesop;
    exact hp_decomp.elim ( fun h => Or.inl h ) fun h => h.elim ( fun h => Or.inr h ) fun h => False.elim <| Set.disjoint_left.mp ( h_disj _ h.choose_spec.1 ) h.choose_spec.2 hp |> fun h => h.elim;
  -- Suppose for contradiction that $L$ contains a corner point $c$.
  by_contra h_contra;
  -- Then there exists a point $c \in L$ such that $c \in \text{SquareCorners}$.
  obtain ⟨c, hcL, hcC⟩ : ∃ c ∈ L, c ∈ SquareCorners := by
    grind;
  -- By `SquareCorners_extreme_v2`, $a = c$ and $b = c$, which contradicts `hL`.
  obtain ⟨a, b, ha, hb, hab⟩ := hL
  have h_eq : a = c ∧ b = c := by
    have h_eq : a ∈ UnitSquare ∧ b ∈ UnitSquare := by
      have h_closed : IsClosed UnitSquare := by
        exact UnitSquare_isClosed
      have h_closed_a : a ∈ UnitSquare := by
        have h_closed_a : a ∈ closure (openSegment ℝ a b) := by
          have h_closed_a : a ∈ segment ℝ a b := by
            exact left_mem_segment _ _ _
          have h_closed_a : segment ℝ a b ⊆ closure (openSegment ℝ a b) := by
            exact segment_subset_closure_openSegment;
          exact h_closed_a ‹_›;
        exact h_closed.closure_subset_iff.mpr h_sub h_closed_a |> fun h => by simpa using h;
      have h_closed_b : b ∈ UnitSquare := by
        have h_closed_b : Filter.Tendsto (fun t : ℝ => (1 - t) • a + t • b) (nhdsWithin 1 (Set.Iio 1)) (nhds b) := by
          exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num );
        exact h_closed.mem_of_tendsto h_closed_b ( Filter.eventually_of_mem ( Ioo_mem_nhdsLT zero_lt_one ) fun t ht => h_sub <| by exact ⟨ 1 - t, t, by linarith [ ht.1, ht.2 ], by linarith [ ht.1, ht.2 ], by simp +decide [ add_comm ] ⟩ ) |> fun h => by simpa using h;
      exact ⟨h_closed_a, h_closed_b⟩
    have h_eq : c ∈ openSegment ℝ a b := by
      exact hcL
    have h_eq : a = c ∧ b = c := by
      apply SquareCorners_extreme_v2 c hcC a b (by
      grind) (by
      grind) h_eq
    exact h_eq;
  aesop

/-
S_total blocks the closed unit square.
-/
lemma S_total_blocks_UnitSquare : IsBlocking S_total UnitSquare := by
  intro L hL hL_sub
  by_cases hL_disj_S_sides : ∀ s ∈ S_sides, Disjoint s L
  have hL_sub_Region_Square : L ⊆ Region_Square := by
    exact
      unit_segment_in_UnitSquare_disjoint_S_sides_implies_in_Region_Square L hL hL_sub
        hL_disj_S_sides
  have hL_block_S_finite : ∃ s ∈ S_finite, ¬Disjoint s L := by
    apply S_finite_blocks_Region_Square L hL hL_sub_Region_Square
  have hL_block_S_total : ∃ s ∈ S_total, ¬Disjoint s L := by
    exact ⟨ hL_block_S_finite.choose, hL_block_S_finite.choose_spec.1 |> fun h => Set.mem_union_left _ h, hL_block_S_finite.choose_spec.2 ⟩
  exact hL_block_S_total
  generalize_proofs at *; (
  unfold S_total; aesop;)

/-
A disjoint collection of unit segments in a region is maximal if and only if every unit segment in the region intersects at least one segment in the collection.
-/
def IsMaximalDisjointCollection (S : Set (Set Point)) (R : Set Point) : Prop :=
  IsDisjointCollection S ∧ IsInRegion S R ∧
  ∀ S', IsDisjointCollection S' → IsInRegion S' R → S ⊆ S' → S = S'

theorem maximal_iff_blocking (S : Set (Set Point)) (R : Set Point) (hS : IsDisjointCollection S) (hR : IsInRegion S R) :
  IsMaximalDisjointCollection S R ↔ IsBlocking S R := by
    unfold IsBlocking IsMaximalDisjointCollection;
    constructor;
    · intro hL L hL1 hL2
      by_contra h_contra
      push_neg at h_contra;
      -- Since $L$ is a unit segment in $R$ and is disjoint from all segments in $S$, the collection $S \cup \{L\}$ is a disjoint collection in $R$.
      have h_add_L : IsDisjointCollection (insert L S) := by
        refine' ⟨ _, _ ⟩;
        · exact fun s hs => hs.elim ( fun hs => hs.symm ▸ hL1 ) fun hs => hS.1 s hs;
        · rintro s t ( rfl | hs ) ( rfl | ht ) <;> simp_all +decide [ Set.disjoint_left ];
          · exact fun h x hx hx' => h_contra t ht hx' hx;
          · exact fun h => h_contra s hs;
          · exact fun hst x hx hx' => hL.1.2 s t hs ht hst |> fun h => h.le_bot ⟨ hx, hx' ⟩;
      -- Since $L$ is a unit segment in $R$ and is disjoint from all segments in $S$, the collection $S \cup \{L\}$ is a disjoint collection in $R$ and $S$ is a proper subset of $S \cup \{L\}$.
      have h_add_L_subset : S ⊂ insert L S := by
        simp_all +decide [ Set.ssubset_def, Set.subset_def ];
        intro hL3; specialize h_contra L hL3; rcases hL1 with ⟨ x, hx ⟩ ; simp_all +decide
        obtain ⟨ y, hy1, hy2 ⟩ := hx; rw [ eq_comm ] at hy2; simp_all +decide [ openSegment_eq_image ] ;
        exact Set.Nonempty.ne_empty ( Set.nonempty_Ioo.mpr zero_lt_one ) hy2;
      exact hL.2.2 ( Insert.insert L S ) h_add_L ( by exact fun s hs => by cases hs <;> aesop ) ( by exact fun s hs => by aesop ) |> fun h => h_add_L_subset.ne h;
    · intro h;
      refine' ⟨ hS, hR, fun S' hS' hR' hSS' => Set.Subset.antisymm hSS' _ ⟩;
      intro L hL;
      contrapose! h;
      cases hS' ; aesop

/-
S_total is a maximal disjoint collection in the closed unit square.
-/
theorem S_total_maximal : IsMaximalDisjointCollection S_total UnitSquare := by
  rw [maximal_iff_blocking];
  · convert S_total_blocks_UnitSquare using 1;
  · convert S_total_is_disjoint_collection using 1;
  · exact S_total_in_UnitSquare

/-
There exists a finite maximal disjoint collection in the closed unit square.
-/
theorem erdos_1071b : ∃ S, IsMaximalDisjointCollection S UnitSquare ∧ Set.Finite S := by
  -- Let's choose the set S to be the union of S_finite and S_sides.
  use S_total;
  -- By definition of $S_total$, we know that it is finite and maximal in the closed unit square.
  apply And.intro S_total_maximal S_total_finite

#print axioms erdos_1071b
-- 'Erdos1071b.erdos_1071b' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1071b
