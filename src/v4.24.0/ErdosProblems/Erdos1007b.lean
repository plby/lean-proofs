/-
We prove that the complete bipartite graph K_{3,3} cannot be embedded as a unit-distance graph in R^3.
We define `UnitDistanceEmbedding` as an injective map preserving unit distances for adjacent vertices.
We prove several helper lemmas:
1. `collinear_distinct_bisector_intersection_empty`: If three distinct points are collinear, the intersection of their bisector planes is empty.
2. `intersection_of_two_nonparallel_planes_is_line`: The intersection of two non-parallel planes is a line.
3. `line_sphere_intersection_subset_two_points`: The intersection of a line and a sphere contains at most 2 points.
4. `bisector_eq_plane`: The set of points equidistant from two points is a plane.
5. `linear_independent_of_not_collinear`: If three points are not collinear, the difference vectors are linearly independent.
Finally, `K33_no_unit_distance_embedding` combines these to show a contradiction: the 3 vertices on one side would have to lie in the intersection of bisector planes of the other 3 vertices (which is either empty or a line) and also on a unit sphere, limiting them to at most 2 points, contradicting that there are 3 distinct vertices.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Definition of a unit-distance embedding of a graph into a metric space.
-/
/-- An injective unit-distance embedding of a graph `G` into a metric space `M`. -/
structure UnitDistanceEmbedding {V : Type*} (G : SimpleGraph V) (M : Type*) [Dist M] where
  toFun : V → M
  inj' : Function.Injective toFun
  dist_eq_one : ∀ {u v}, G.Adj u v → dist (toFun u) (toFun v) = 1

/-
If three distinct points are collinear, the intersection of the bisector of the first two and the bisector of the last two is empty.
-/
open Set Real InnerProductSpace

lemma collinear_distinct_bisector_intersection_empty (x₁ x₂ x₃ : EuclideanSpace ℝ (Fin 3))
    (h_distinct : x₁ ≠ x₂ ∧ x₂ ≠ x₃ ∧ x₁ ≠ x₃)
    (h_collinear : Collinear ℝ {x₁, x₂, x₃}) :
    {z | dist z x₁ = dist z x₂} ∩ {z | dist z x₂ = dist z x₃} = ∅ := by
      -- If three distinct points are collinear, the set {z | dist z x₁ = dist z x₂} is a plane perpendicular to the line through x₁ and x₂.
      have h_perpendicular : ∀ z : EuclideanSpace ℝ (Fin 3), dist z x₁ = dist z x₂ ↔ 2 * inner ℝ (x₂ - x₁) z = (‖x₂‖ ^ 2 - ‖x₁‖ ^ 2) := by
        norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three ];
        norm_num [ Real.sq_sqrt ( add_nonneg ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ( sq_nonneg _ ) ) ];
        intro z; rw [ Real.sqrt_inj ( by positivity ) ( by positivity ) ] ; norm_num [ Fin.sum_univ_three, inner_sub_left, inner_sub_right ] ; ring;
        norm_num [ Fin.sum_univ_three, inner ] ; constructor <;> intro <;> linarith;
      -- Similarly, if three distinct points are collinear, the set {z | dist z x₂ = dist z x₃} is a plane perpendicular to the line through x₂ and x₃.
      have h_perpendicular2 : ∀ z : EuclideanSpace ℝ (Fin 3), dist z x₂ = dist z x₃ ↔ 2 * inner ℝ (x₃ - x₂) z = (‖x₃‖ ^ 2 - ‖x₂‖ ^ 2) := by
        norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three ];
        norm_num [ Real.sq_sqrt ( add_nonneg ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ( sq_nonneg _ ) ), Fin.sum_univ_three, inner ] ; ring;
        exact fun z => ⟨ fun h => by rw [ Real.sqrt_inj ] at h <;> nlinarith [ sq_nonneg ( z 0 - x₂ 0 ), sq_nonneg ( z 1 - x₂ 1 ), sq_nonneg ( z 2 - x₂ 2 ), sq_nonneg ( z 0 - x₃ 0 ), sq_nonneg ( z 1 - x₃ 1 ), sq_nonneg ( z 2 - x₃ 2 ) ], fun h => by rw [ Real.sqrt_inj ] <;> nlinarith [ sq_nonneg ( z 0 - x₂ 0 ), sq_nonneg ( z 1 - x₂ 1 ), sq_nonneg ( z 2 - x₂ 2 ), sq_nonneg ( z 0 - x₃ 0 ), sq_nonneg ( z 1 - x₃ 1 ), sq_nonneg ( z 2 - x₃ 2 ) ] ⟩;
      -- Since $x₁$, $x₂$, and $x₃$ are collinear, we have $x₃ - x₂ = k(x₂ - x₁)$ for some $k \in ℝ$.
      obtain ⟨k, hk⟩ : ∃ k : ℝ, x₃ - x₂ = k • (x₂ - x₁) := by
        rw [ collinear_iff_exists_forall_eq_smul_vadd ] at h_collinear;
        simp +zetaDelta at *;
        rcases h_collinear with ⟨ p₀, v, ⟨ r₁, hr₁ ⟩, ⟨ r₂, hr₂ ⟩, ⟨ r₃, hr₃ ⟩ ⟩ ; use ( r₃ - r₂ ) / ( r₂ - r₁ ) ; ext i ; by_cases hi : r₂ - r₁ = 0 <;> simp_all +decide [ sub_eq_iff_eq_add ] ; ring;
        grind;
      -- If there exists a point $z$ that satisfies both equations, then substituting $x₃ = x₂ + k(x₂ - x₁)$ into the second equation gives us $k(2⟨x₂ - x₁, z⟩) = k(‖x₂‖^2 - ‖x₁‖^2)$.
      by_contra h_contra
      obtain ⟨z, hz⟩ : ∃ z : EuclideanSpace ℝ (Fin 3), 2 * inner ℝ (x₂ - x₁) z = (‖x₂‖ ^ 2 - ‖x₁‖ ^ 2) ∧ 2 * inner ℝ (x₃ - x₂) z = (‖x₃‖ ^ 2 - ‖x₂‖ ^ 2) := by
        exact Exists.elim ( Set.nonempty_iff_ne_empty.mpr h_contra ) fun z hz => ⟨ z, h_perpendicular z |>.1 hz.1, h_perpendicular2 z |>.1 hz.2 ⟩;
      -- Substitute $x₃ = x₂ + k(x₂ - x₁)$ into the second equation and simplify.
      have h_subst : k * (‖x₂‖ ^ 2 - ‖x₁‖ ^ 2) = ‖x₂ + k • (x₂ - x₁)‖ ^ 2 - ‖x₂‖ ^ 2 := by
        rw [ ← hz.1, ← hk ];
        convert hz.2 using 1 <;> norm_num [ EuclideanSpace.norm_eq, Fin.sum_univ_three ] ; ring;
        rw [ hk, inner_smul_left ] ; ring;
        norm_num [ mul_assoc, mul_comm, mul_left_comm ];
      norm_num [ EuclideanSpace.norm_eq, Fin.sum_univ_three ] at *;
      rw [ Real.sq_sqrt ( by positivity ), Real.sq_sqrt ( by positivity ), Real.sq_sqrt ( by positivity ) ] at h_subst;
      -- Since $x₁$, $x₂$, and $x₃$ are distinct, we have $k \neq 0$ and $k \neq -1$.
      have h_k_ne_zero : k ≠ 0 := by
        intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
      have h_k_ne_neg_one : k ≠ -1 := by
        rintro rfl; simp_all +decide [ sub_eq_iff_eq_add ] ;
      -- Since $x₁$, $x₂$, and $x₃$ are distinct, we have $‖x₂ - x₁‖^2 > 0$.
      have h_norm_pos : ‖x₂ - x₁‖ ^ 2 > 0 := by
        exact sq_pos_of_pos ( norm_pos_iff.mpr ( sub_ne_zero.mpr ( Ne.symm h_distinct.1 ) ) );
      norm_num [ EuclideanSpace.norm_eq, Fin.sum_univ_three ] at h_norm_pos;
      grind

/-
The intersection of two planes in R^3 with linearly independent normal vectors is a line (affine subspace of dimension 1).
-/
open Set Real InnerProductSpace Module

lemma intersection_of_two_nonparallel_planes_is_line
    (n₁ n₂ : EuclideanSpace ℝ (Fin 3)) (c₁ c₂ : ℝ)
    (h_indep : LinearIndependent ℝ ![n₁, n₂]) :
    ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)),
      finrank ℝ L.direction = 1 ∧
      {x | inner ℝ x n₁ = c₁} ∩ {x | inner ℝ x n₂ = c₂} = (L : Set (EuclideanSpace ℝ (Fin 3))) := by
        -- The set `{x | inner ℝ x n₁ = c₁} ∩ {x | inner ℝ x n₂ = c₂}` is a line (affine subspace of dimension 1).
        have h_affine_subspace : ∃ (v : EuclideanSpace ℝ (Fin 3)) (w : EuclideanSpace ℝ (Fin 3)), w ≠ 0 ∧ {x | inner ℝ x n₁ = c₁} ∩ {x | inner ℝ x n₂ = c₂} = {x | ∃ t : ℝ, x = v + t • w} := by
          -- Let's choose any vector $w$ that is orthogonal to both $n₁$ and $n₂$.
          obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℝ (Fin 3), w ≠ 0 ∧ ⟪w, n₁⟫_ℝ = 0 ∧ ⟪w, n₂⟫_ℝ = 0 := by
            -- Since $n₁$ and $n₂$ are linearly independent, their cross product $n₁ \times n₂$ is non-zero.
            have h_cross_nonzero : n₁ 0 * n₂ 1 - n₁ 1 * n₂ 0 ≠ 0 ∨ n₁ 1 * n₂ 2 - n₁ 2 * n₂ 1 ≠ 0 ∨ n₁ 2 * n₂ 0 - n₁ 0 * n₂ 2 ≠ 0 := by
              contrapose! h_indep;
              rw [ Fintype.not_linearIndependent_iff ] ; by_cases h' : n₂ 0 = 0 <;> simp_all +decide [ linearIndependent_fin2 ];
              · by_cases h'' : n₂ 1 = 0 <;> by_cases h''' : n₂ 2 = 0 <;> simp_all +decide [ sub_eq_iff_eq_add ];
                · exact ⟨ fun i => if i = 0 then 0 else 1, by ext i; fin_cases i <;> simp +decide [ * ], by simp +decide ⟩;
                · exact ⟨ fun i => if i = 0 then n₂ 2 else -n₁ 2, by ext i; fin_cases i <;> simp +decide [ * ] ; ring, by aesop ⟩;
                · exact ⟨ fun i => if i = 0 then n₂ 1 else -n₁ 1, by ext i; fin_cases i <;> simp +decide [ * ] ; ring, by aesop ⟩;
                · exact ⟨ fun i => if i = 0 then n₂ 1 else -n₁ 1, by ext i; fin_cases i <;> simp +decide [ * ] <;> cases lt_or_gt_of_ne h'' <;> cases lt_or_gt_of_ne h''' <;> nlinarith, by aesop ⟩;
              · exact ⟨ fun i => if i = 0 then n₂ 0 else -n₁ 0, by ext i; fin_cases i <;> simp +decide <;> cases lt_or_gt_of_ne h' <;> cases lt_or_ge ( n₁ 0 ) 0 <;> cases lt_or_ge ( n₂ 0 ) 0 <;> nlinarith !, by aesop ⟩;
            refine' ⟨ fun i => if i = 0 then n₁ 1 * n₂ 2 - n₁ 2 * n₂ 1 else if i = 1 then n₁ 2 * n₂ 0 - n₁ 0 * n₂ 2 else n₁ 0 * n₂ 1 - n₁ 1 * n₂ 0, _, _, _ ⟩ <;> simp_all +decide [ Fin.sum_univ_three, inner_self_eq_norm_sq_to_K ];
            · exact fun h => by have := congr_fun h 0; have := congr_fun h 1; have := congr_fun h 2; simp_all +decide [ funext_iff, Fin.forall_fin_succ ] ;
            · simp +decide [ Fin.sum_univ_three, inner ] ; ring;
            · simp +decide [ Fin.sum_univ_three, inner ] ; ring;
          -- Let's choose any point $v$ in the intersection of the two planes.
          obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin 3), ⟪v, n₁⟫_ℝ = c₁ ∧ ⟪v, n₂⟫_ℝ = c₂ := by
            -- Since $n₁$ and $n₂$ are linearly independent, the system of equations $⟪v, n₁⟫_ℝ = c₁$ and $⟪v, n₂⟫_ℝ = c₂$ has a solution.
            have h_sol : ∃ v : EuclideanSpace ℝ (Fin 3), ⟪v, n₁⟫_ℝ = c₁ ∧ ⟪v, n₂⟫_ℝ = c₂ := by
              have h_rank : Matrix.rank (Matrix.of ![![n₁ 0, n₁ 1, n₁ 2], ![n₂ 0, n₂ 1, n₂ 2]]) = 2 := by
                have h_rank : LinearIndependent ℝ ![![n₁ 0, n₁ 1, n₁ 2], ![n₂ 0, n₂ 1, n₂ 2]] := by
                  rw [ Fintype.linearIndependent_iff ] at *;
                  intro g hg i; specialize h_indep g; simp_all +decide [ funext_iff, Fin.forall_fin_succ ] ;
                  exact h_indep ( by ext i; fin_cases i <;> aesop ) |> fun h => by fin_cases i <;> tauto;
                convert Matrix.rank_transpose _;
                rw [ Matrix.rank ];
                · rw [ @LinearMap.finrank_range_of_inj ];
                  · norm_num;
                  · intro x y hxy; simp_all +decide [ ← List.ofFn_inj, Matrix.mulVec ] ;
                    simp_all +decide [ Matrix.vecHead, Matrix.vecTail, dotProduct ];
                    rw [ Fintype.linearIndependent_iff ] at h_rank;
                    specialize h_rank ( fun i => if i = 0 then x 0 - y 0 else x 1 - y 1 ) ; simp_all +decide [ Fin.forall_fin_two, sub_eq_iff_eq_add ];
                    exact h_rank ( by linarith ) ( by linarith ) ( by linarith );
                · infer_instance
              -- Since the rank of the matrix is 2, the system of equations has a solution.
              have h_sol : ∃ v : Fin 3 → ℝ, Matrix.mulVec (Matrix.of ![![n₁ 0, n₁ 1, n₁ 2], ![n₂ 0, n₂ 1, n₂ 2]]) v = ![c₁, c₂] := by
                have h_sol : LinearMap.range (Matrix.mulVecLin (Matrix.of ![![n₁ 0, n₁ 1, n₁ 2], ![n₂ 0, n₂ 1, n₂ 2]])) = ⊤ := by
                  exact Submodule.eq_top_of_finrank_eq ( by aesop );
                exact LinearMap.range_eq_top.mp h_sol _;
              obtain ⟨ v, hv ⟩ := h_sol; use v; simp_all +decide [ ← List.ofFn_inj, Matrix.mulVec ] ;
              simp_all +decide [ Matrix.vecHead, Matrix.vecTail, inner ];
              simpa only [ Fin.sum_univ_three, add_assoc ] using hv;
            exact h_sol;
          refine' ⟨ v, w, hw.1, Set.Subset.antisymm _ _ ⟩;
          · intro x hx
            obtain ⟨hx₁, hx₂⟩ := hx
            have h_eq : ∃ t : ℝ, x - v = t • w := by
              -- Since $w$ is orthogonal to both $n₁$ and $n₂$, we have $⟪x - v, n₁⟫_ℝ = 0$ and $⟪x - v, n₂⟫_ℝ = 0$.
              have h_ortho : ⟪x - v, n₁⟫_ℝ = 0 ∧ ⟪x - v, n₂⟫_ℝ = 0 := by
                simp_all +decide [ inner_sub_left ];
              -- Since $w$ is orthogonal to both $n₁$ and $n₂$, we have $⟪x - v, n₁⟫_ℝ = 0$ and $⟪x - v, n₂⟫_ℝ = 0$, which implies that $x - v$ is in the span of $w$.
              have h_span : x - v ∈ Submodule.span ℝ {w} := by
                have h_span : Submodule.span ℝ {w} = (Submodule.span ℝ {n₁, n₂})ᗮ := by
                  have h_span : Submodule.span ℝ {w} ≤ (Submodule.span ℝ {n₁, n₂})ᗮ := by
                    simp_all +decide [ Submodule.mem_orthogonal, Submodule.mem_span_insert, Submodule.mem_span_singleton ];
                    simp_all +decide [ inner_add_left, inner_smul_left ];
                    simp_all +decide [ real_inner_comm ];
                  refine' Submodule.eq_of_le_of_finrank_eq h_span _;
                  have := Submodule.finrank_add_finrank_orthogonal ( Submodule.span ℝ { n₁, n₂ } ) ; simp_all +decide [ Submodule.finrank_eq_zero ] ;
                  rw [ finrank_span_singleton hw.1 ] ; rw [ show Module.finrank ℝ ( Submodule.span ℝ { n₁, n₂ } ) = 2 from ?_ ] at this ; linarith;
                  convert finrank_span_eq_card h_indep;
                  · aesop;
                  · exact?;
                  · aesop;
                simp_all +decide [ Submodule.mem_orthogonal ];
                intro u hu; rw [ Submodule.mem_span_pair ] at hu; obtain ⟨ a, b, rfl ⟩ := hu; simp_all +decide [ inner_add_left, inner_add_right, inner_smul_left, inner_smul_right ] ;
                simp_all +decide [ real_inner_comm ];
              rw [ Submodule.mem_span_singleton ] at h_span ; tauto;
            exact ⟨ h_eq.choose, eq_add_of_sub_eq' h_eq.choose_spec ⟩;
          · simp_all +decide [ inner_add_left, inner_smul_left ];
        obtain ⟨ v, w, hw, h ⟩ := h_affine_subspace;
        refine' ⟨ AffineSubspace.mk' v ( Submodule.span ℝ { w } ), _, _ ⟩;
        · rw [ AffineSubspace.direction_mk' ];
          rw [ finrank_span_singleton ] ; aesop;
        · simp_all +decide [ Set.ext_iff, AffineSubspace.mem_mk', Submodule.mem_span_singleton ];
          grind

/-
The intersection of a line and a sphere in R^3 contains at most 2 points.
-/
open Set Real InnerProductSpace Module

lemma line_sphere_intersection_subset_two_points
    (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ)
    (h_dim : finrank ℝ L.direction = 1) :
    ∃ p1 p2, (L : Set (EuclideanSpace ℝ (Fin 3))) ∩ Metric.sphere c r ⊆ {p1, p2} := by
      -- Since `finrank ℝ L.direction = 1`, `L` is a line.
      obtain ⟨p, v, hv⟩ : ∃ p : EuclideanSpace ℝ (Fin 3), ∃ v : EuclideanSpace ℝ (Fin 3), v ≠ 0 ∧ ∀ x ∈ L, ∃ t : ℝ, x = p + t • v := by
        -- Since `finrank ℝ L.direction = 1`, `L.direction` is generated by a single non-zero vector `v`.
        obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin 3), v ≠ 0 ∧ ∀ x ∈ L.direction, ∃ t : ℝ, x = t • v := by
          obtain ⟨ v, hv ⟩ := finrank_eq_one_iff'.mp h_dim;
          exact ⟨ v, by simpa using hv.1, fun x hx => by obtain ⟨ t, ht ⟩ := hv.2 ⟨ x, hx ⟩ ; exact ⟨ t, by simpa [ eq_comm ] using congr_arg Subtype.val ht ⟩ ⟩;
        by_cases h : ∃ p : EuclideanSpace ℝ ( Fin 3 ), p ∈ L;
        · obtain ⟨ p, hp ⟩ := h;
          refine' ⟨ p, v, hv.1, fun x hx => _ ⟩;
          obtain ⟨ t, ht ⟩ := hv.2 ( x - p ) ( by simpa [ hp, hx ] using AffineSubspace.vsub_mem_direction hx hp ) ; use t; simp_all +decide [ sub_eq_iff_eq_add' ] ;
        · exact ⟨ 0, v, hv.1, fun x hx => False.elim <| h ⟨ x, hx ⟩ ⟩;
      -- A point `x = p + t • v` is in the sphere iff `dist x c = r`, i.e., `‖x - c‖² = r²`.
      -- Substituting `x`, we get `‖(p - c) + t • v‖² = r²`.
      -- Expanding, `‖p - c‖² + 2t ⟪p - c, v⟫ + t² ‖v‖² = r²`.
      -- This is a quadratic equation in `t` of the form `A t² + B t + C = 0` with `A = ‖v‖² ≠ 0`.
      have h_quad : ∀ x ∈ L, x ∈ Metric.sphere c r → ∃ t : ℝ, x = p + t • v ∧ ‖p - c‖^2 + 2 * t * inner ℝ (p - c) v + t^2 * ‖v‖^2 = r^2 := by
        intro x hx hx'; obtain ⟨ t, rfl ⟩ := hv.2 x hx; use t; simp_all +decide [ EuclideanSpace.norm_eq, Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ] ; ring;
        rw [ ← hx', Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ] ; norm_num [ Fin.sum_univ_three, inner ] ; ring;
      -- A quadratic equation has at most 2 roots.
      have h_roots : ∀ t : ℝ, ‖p - c‖^2 + 2 * t * inner ℝ (p - c) v + t^2 * ‖v‖^2 = r^2 → t = (-2 * inner ℝ (p - c) v + Real.sqrt ((2 * inner ℝ (p - c) v)^2 - 4 * ‖v‖^2 * (‖p - c‖^2 - r^2))) / (2 * ‖v‖^2) ∨ t = (-2 * inner ℝ (p - c) v - Real.sqrt ((2 * inner ℝ (p - c) v)^2 - 4 * ‖v‖^2 * (‖p - c‖^2 - r^2))) / (2 * ‖v‖^2) := by
        intro t ht; rw [ eq_div_iff, eq_div_iff ] <;> norm_num [ hv.1 ];
        exact Classical.or_iff_not_imp_left.2 fun h => mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ ( 2 * ⟪p - c, v⟫_ℝ ) ^ 2 - 4 * ‖v‖ ^ 2 * ( ‖p - c‖ ^ 2 - r ^ 2 ) by nlinarith [ sq_nonneg ( 2 * ⟪p - c, v⟫_ℝ + 2 * t * ‖v‖ ^ 2 ) ] ) ] ;
      use p + ((-2 * inner ℝ (p - c) v + Real.sqrt ((2 * inner ℝ (p - c) v)^2 - 4 * ‖v‖^2 * (‖p - c‖^2 - r^2))) / (2 * ‖v‖^2)) • v, p + ((-2 * inner ℝ (p - c) v - Real.sqrt ((2 * inner ℝ (p - c) v)^2 - 4 * ‖v‖^2 * (‖p - c‖^2 - r^2))) / (2 * ‖v‖^2)) • v;
      intro x hx; rcases h_quad x hx.1 hx.2 with ⟨ t, rfl, ht ⟩ ; rcases h_roots t ht with ( rfl | rfl ) <;> norm_num;

/-
The set of points equidistant from x1 and x2 is a plane defined by a linear equation.
-/
open Set Real InnerProductSpace Module

lemma bisector_eq_plane (x₁ x₂ : EuclideanSpace ℝ (Fin 3)) :
    {z | dist z x₁ = dist z x₂} = {z | inner ℝ z (x₂ - x₁) = (‖x₂‖^2 - ‖x₁‖^2) / 2} := by
      ext; simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three];
      rw [ Real.sq_sqrt ( by positivity ), Real.sq_sqrt ( by positivity ) ] ; rw [ Real.sqrt_inj ( by positivity ) ( by positivity ) ] ; norm_num [ Fin.sum_univ_three, inner_sub_left, inner_sub_right ] ; ring;
      norm_num [ Fin.sum_univ_three, inner ] ; constructor <;> intro <;> linarith

/-
If three points are not collinear, the vectors formed by consecutive points are linearly independent.
-/
open Set Real InnerProductSpace Module

lemma linear_independent_of_not_collinear {x₁ x₂ x₃ : EuclideanSpace ℝ (Fin 3)}
  (h_distinct : x₁ ≠ x₂ ∧ x₂ ≠ x₃ ∧ x₁ ≠ x₃)
  (h_not_col : ¬ Collinear ℝ {x₁, x₂, x₃}) :
  LinearIndependent ℝ ![x₂ - x₁, x₃ - x₂] := by
    refine' linearIndependent_fin2.mpr _;
    simp_all +decide [ sub_eq_zero, collinear_pair ];
    refine' ⟨ by tauto, fun a ha => h_not_col _ ⟩;
    rw [ collinear_iff_exists_forall_eq_smul_vadd ];
    use x₂, x₃ - x₂;
    simp +zetaDelta at *;
    exact ⟨ ⟨ -a, by ext i; have := congr_fun ha i; norm_num at *; linarith ⟩, ⟨ 1, by ext i; norm_num ⟩ ⟩

/-
K_{3,3} does not embed as a unit-distance graph in R^3.
-/
open Set Real InnerProductSpace Module

theorem K33_no_unit_distance_embedding : ¬ Nonempty (UnitDistanceEmbedding (completeBipartiteGraph (Fin 3) (Fin 3)) (EuclideanSpace ℝ (Fin 3))) := by
  -- Assume for contradiction that such an embedding exists.
  by_contra h
  obtain ⟨f, hf⟩ := h

  -- Let the vertices of $K_{3,3}$ be $x_1, x_2, x_3$ and $y_1, y_2, y_3$.
  set x1 := f (Sum.inl 0)
  set x2 := f (Sum.inl 1)
  set x3 := f (Sum.inl 2)
  set y1 := f (Sum.inr 0)
  set y2 := f (Sum.inr 1)
  set y3 := f (Sum.inr 2);
  -- Since y1, y2, y3 are equidistant from x1, x2, and x3, they must lie on the intersection of the bisector planes of (x1, x2) and (x2, x3).
  have h_bisector_planes : ∀ y ∈ ({y1, y2, y3} : Set (EuclideanSpace ℝ (Fin 3))),
    inner ℝ y (x2 - x1) = (‖x2‖^2 - ‖x1‖^2) / 2 ∧
    inner ℝ y (x3 - x2) = (‖x3‖^2 - ‖x2‖^2) / 2 := by
      intro y hy
      have h_dist : dist y x1 = 1 ∧ dist y x2 = 1 ∧ dist y x3 = 1 := by
        aesop;
      norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three ] at h_dist ⊢;
      norm_num [ Real.sq_sqrt ( add_nonneg ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ( sq_nonneg _ ) ), Fin.sum_univ_three, inner ] at * ; constructor <;> linarith!;
  -- Consider two cases: $x_1, x_2, x_3$ are collinear or not.
  by_cases h_collinear : Collinear ℝ {x1, x2, x3};
  · -- Since $x_1, x_2, x_3$ are distinct and collinear, the bisector planes are parallel and distinct, so their intersection is empty.
    have h_parallel_distinct : {z | dist z x1 = dist z x2} ∩ {z | dist z x2 = dist z x3} = ∅ := by
      apply collinear_distinct_bisector_intersection_empty;
      · exact ⟨ hf.ne <| by decide, hf.ne <| by decide, hf.ne <| by decide ⟩;
      · exact h_collinear;
    simp_all +decide [ Set.ext_iff ];
    exact h_parallel_distinct y1 ( by aesop ) ( by aesop );
  · -- Since $x_1, x_2, x_3$ are not collinear, the bisector planes intersect in a line $L$.
    obtain ⟨L, hL⟩ : ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)),
      finrank ℝ L.direction = 1 ∧
      {z | inner ℝ z (x2 - x1) = (‖x2‖^2 - ‖x1‖^2) / 2} ∩ {z | inner ℝ z (x3 - x2) = (‖x3‖^2 - ‖x2‖^2) / 2} = (L : Set (EuclideanSpace ℝ (Fin 3))) := by
        convert intersection_of_two_nonparallel_planes_is_line ( x2 - x1 ) ( x3 - x2 ) ( ( ‖x2‖^2 - ‖x1‖^2 ) / 2 ) ( ( ‖x3‖^2 - ‖x2‖^2 ) / 2 ) _ using 1;
        apply_rules [ linear_independent_of_not_collinear ];
        exact ⟨ hf.ne <| by decide, hf.ne <| by decide, hf.ne <| by decide ⟩;
    -- Since $y1$, $y2$, and $y3$ lie on the line $L$, they must also lie on the unit sphere centered at $x1$.
    have h_sphere : ∀ y ∈ ({y1, y2, y3} : Set (EuclideanSpace ℝ (Fin 3))), dist y x1 = 1 := by
      aesop;
    -- The intersection of a line and a sphere has at most 2 points.
    have h_line_sphere : ∃ p1 p2 : EuclideanSpace ℝ (Fin 3), (L : Set (EuclideanSpace ℝ (Fin 3))) ∩ Metric.sphere x1 1 ⊆ {p1, p2} := by
      apply line_sphere_intersection_subset_two_points L x1 1 hL.left;
    obtain ⟨ p1, p2, h ⟩ := h_line_sphere;
    -- Since $y1$, $y2$, and $y3$ are distinct and lie on the line $L$, they must be among $p1$ and $p2$.
    have h_distinct : y1 ≠ y2 ∧ y2 ≠ y3 ∧ y1 ≠ y3 := by
      exact ⟨ hf.ne <| by decide, hf.ne <| by decide, hf.ne <| by decide ⟩;
    simp_all +decide [ Set.subset_def ];
    cases h y1 ( hL.2.subset ⟨ h_bisector_planes.1.1, h_bisector_planes.1.2 ⟩ ) ( by simpa [ dist_eq_norm ] using h_sphere.1 ) <;> cases h y2 ( hL.2.subset ⟨ h_bisector_planes.2.1.1, h_bisector_planes.2.1.2 ⟩ ) ( by simpa [ dist_eq_norm ] using h_sphere.2.1 ) <;> cases h y3 ( hL.2.subset ⟨ h_bisector_planes.2.2.1, h_bisector_planes.2.2.2 ⟩ ) ( by simpa [ dist_eq_norm ] using h_sphere.2.2 ) <;> aesop
