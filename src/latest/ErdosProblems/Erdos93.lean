import Mathlib

open Lean.Parser.Tactic in
macro "push_neg" cfg:optConfig loc:(location)? : tactic =>
  `(tactic| push $cfg:optConfig Not $[$loc]?)

set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.refine false
set_option linter.style.emptyLine false
set_option linter.style.multiGoal false
set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.cases false
set_option linter.style.induction false
set_option linter.flexible false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 2000000

open Real Metric Set InnerProductSpace Complex EuclideanGeometry
open scoped Classical InnerProductSpace Pointwise Complex EuclideanGeometry
namespace Erdos93
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V]
variable [Fact (Module.finrank ℝ V = 2)]

/--
The set of distinct distances determined by a finite set of points `s`.
It is the set { dist x y | x ∈ s, y ∈ s, x ≠ y }.
-/
def distinctDistances (s : Finset V) : Finset ℝ :=
  (s.product s).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2)

/--
An arbitrary linear equivalence from V to ℂ for angular sorting.
-/
noncomputable def to_complex_map {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [hdim : Fact (Module.finrank ℝ V = 2)] : V ≃ₗ[ℝ] ℂ :=
  LinearEquiv.ofFinrankEq V ℂ (by simp [hdim.out])

/--
The angular value of a point v relative to a center C.
-/
noncomputable def centroid_angle {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [hdim : Fact (Module.finrank ℝ V = 2)]
    (C : V) (v : V) : ℝ :=
  Complex.arg (to_complex_map (v - C))

/--
The centroid of a finite set of points.
-/
def finset_centroid (s : Finset V) : V :=
  (s.card : ℝ)⁻¹ • s.sum id

/--
A predicate stating that points `A 0, ..., A (n-1)` form a convex polygon in cyclic order.
Defined as:
1. The points are convex independent (no point is in the convex hull of others).
2. The points are distinct.
3. The segments connecting consecutive points lie on the frontier of the convex hull.
-/
def IsConvexPolygon (A : ℕ → V) (n : ℕ) : Prop :=
  let vertices : Set V := (Finset.range n).image A
  -- n ≥ 3 for a proper polygon
  3 ≤ n ∧
  -- Points are distinct
  (∀ i j, i < n → j < n → A i = A j → i = j) ∧
  -- Points are convex independent
  ConvexIndependent ℝ (fun i : Fin n => A i) ∧
  -- Cyclic order condition: edges are on the frontier
  ∀ i : Fin n, segment ℝ (A i) (A ((i + 1) % n)) ⊆ frontier (convexHull ℝ vertices)

/-
If a set of points affinely spans the whole space, there exists a continuous linear map that assigns to each vector a set of coefficients summing to zero such that the vector is the linear combination of the points with these coefficients.
(proven and stated by Aristotle)
-/
lemma exists_linear_map_coeff_sum_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι] [Nonempty ι] {pts : ι → V}
    (h_span : affineSpan ℝ (Set.range pts) = ⊤) :
    ∃ L : V →L[ℝ] (ι → ℝ), (∀ v, ∑ i, L v i = 0) ∧ (∀ v, ∑ i, (L v i) • pts i = v) := by
      -- Consider the linear map T from the subspace of coefficients summing to zero {c : ι → ℝ | sum c = 0} to V, defined by T(c) = sum c_i pts_i.
      set T : (ι → ℝ) →ₗ[ℝ] V := ∑ i, LinearMap.smulRight (LinearMap.proj i) (pts i) with hT_def
      have hT_surjective : Function.Surjective (T : (ι → ℝ) → V) := by
        -- Since affineSpan pts = ⊤, this vector span is V.
        have hT_span : Submodule.span ℝ (Set.range pts) = ⊤ := by
          simp_all +decide [ SetLike.ext_iff, affineSpan ];
          simp_all +decide [ spanPoints ];
          intro x
          obtain ⟨a, v, hv, hx⟩ := h_span x;
          simp_all +decide [ vectorSpan ];
          rw [ Submodule.mem_span ] at hv ⊢;
          intro p hp; specialize hv p; simp_all +decide [ Set.subset_def, Set.mem_vsub ] ;
          exact p.add_mem ( hv fun x i j hx => by simpa [ hx ] using p.sub_mem ( hp i ) ( hp j ) ) ( hp a );
        intro x; replace hT_span := Submodule.mem_span_range_iff_exists_fun ℝ |>.1 ( show x ∈ Submodule.span ℝ ( Set.range pts ) from hT_span.symm ▸ Submodule.mem_top ) ; aesop;
      -- Since T is surjective, there exists a right inverse R : V → (ι → ℝ) such that T(R(v)) = v for all v in V.
      obtain ⟨R, hR⟩ : ∃ R : V →ₗ[ℝ] (ι → ℝ), T.comp R = LinearMap.id := by
        exact Module.projective_lifting_property T LinearMap.id hT_surjective;
      -- Let L be the composition of R with the inclusion into ι → ℝ.
      obtain ⟨L, hL⟩ : ∃ L : V →ₗ[ℝ] (ι → ℝ), (∀ v, (∑ i, (L v i)) = 0) ∧ (∀ v, (∑ i, (L v i) • (pts i)) = v) := by
        -- Let $c$ be a vector in the kernel of $T$ such that $\sum_{i} c_i = 1$.
        obtain ⟨c, hc⟩ : ∃ c : ι → ℝ, (∑ i, c i) = 1 ∧ (∑ i, c i • pts i) = 0 := by
          -- Since the affine span of the points is the entire space, there exists a vector $c$ in the kernel of $T$ such that $\sum_{i} c_i = 1$.
          have h_kernel : ∃ c : ι → ℝ, (∑ i, c i) = 1 ∧ (∑ i, c i • pts i) = 0 := by
            have h_affine_span : ∃ c : ι → ℝ, (∑ i, c i) = 1 ∧ (∑ i, c i • pts i) = 0 := by
              have h_affine_span_def : affineSpan ℝ (Set.range pts) = ⊤ := h_span
              have h_affine_span_def : 0 ∈ affineSpan ℝ (Set.range pts) := by
                exact h_affine_span_def.symm ▸ Set.mem_univ _;
              rw [ mem_affineSpan_iff_eq_affineCombination ] at h_affine_span_def;
              obtain ⟨ s, w, hw₁, hw₂ ⟩ := h_affine_span_def; use fun i => if i ∈ s then w i else 0; simp_all +decide [ Finset.sum_ite ] ;
              simp +decide [ ← hw₂ ]
            exact h_affine_span;
          exact h_kernel;
        refine' ⟨ R - LinearMap.smulRight ( LinearMap.comp ( ∑ i, LinearMap.proj i ) R ) c, _, _ ⟩ <;> simp_all +decide [ LinearMap.ext_iff ];
        · simp +decide [ ← Finset.mul_sum _ _ _, hc ];
        · simp_all +decide [ sub_smul, Finset.sum_sub_distrib ];
          simp +decide [ SemigroupAction.mul_smul ];
          simp +decide [ ← Finset.smul_sum, hc.2 ];
      exact ⟨ L.toContinuousLinearMap, hL ⟩
/-
If w has positive entries and L is a continuous linear map, then for sufficiently small vectors v, w + L(v) has positive entries.
(proven and stated by Aristotle)
-/
lemma exists_ball_pos_of_pos_continuous_linear_map
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (L : V →L[ℝ] (ι → ℝ)) :
    ∃ δ > 0, ∀ v, ‖v‖ < δ → ∀ i, 0 < w i + L v i := by
      -- Let $m = \min_{i} w_i$. Since $w_i > 0$ for all $i$, $m > 0$.
      obtain ⟨m, hm⟩ : ∃ m > 0, ∀ i, w i ≥ m := by
        by_cases h_empty : Nonempty ι;
        · exact ⟨ Finset.min' ( Finset.univ.image w ) ⟨ w h_empty.some, Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) ⟩, by have := Finset.min'_mem ( Finset.univ.image w ) ⟨ w h_empty.some, Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) ⟩ ; aesop, fun i => Finset.min'_le _ _ ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) ) ⟩;
        · exact ⟨ 1, zero_lt_one, fun i => False.elim <| h_empty ⟨ i ⟩ ⟩;
      -- Since $L$ is continuous and $L(0) = 0$, there exists $\delta > 0$ such that $\|v\| < \delta$ implies $\|L(v)\| < m$.
      have h_cont : ∃ δ > 0, ∀ v, ‖v‖ < δ → ‖L v‖ < m := by
        simpa using Metric.continuous_iff.mp L.continuous 0 m hm.1;
      exact ⟨ h_cont.choose, h_cont.choose_spec.1, fun v hv i => by linarith [ hm.2 i, abs_le.mp ( show |(L v i)| ≤ ‖L v‖ by exact ( norm_le_pi_norm ( L v ) i ) ), h_cont.choose_spec.2 v hv ] ⟩

/-
If a point is a strictly positive convex combination of a set of points whose affine span is the whole space, then it lies in the interior of their convex hull.
(proven and stated by Aristotle)
-/
lemma mem_interior_convexHull_of_pos_comb {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι] {pts : ι → V}
    (h_span : affineSpan ℝ (Set.range pts) = ⊤)
    (w : ι → ℝ) (hw_pos : ∀ i, 0 < w i) (hw_sum : ∑ i, w i = 1) :
    (∑ i, w i • pts i) ∈ interior (convexHull ℝ (Set.range pts)) := by
      -- By `exists_linear_map_coeff_sum_zero`, there exists a continuous linear map L such that for any v, v = sum (L v)_i pts_i and sum (L v)_i = 0.
      obtain ⟨L, hL_sum, hL_coeff⟩ : ∃ L : V →L[ℝ] (ι → ℝ), (∀ v, ∑ i, L v i = 0) ∧ (∀ v, ∑ i, (L v i) • pts i = v) := by
        by_cases h : Nonempty ι <;> simp_all +decide [ affineSpan ];
        convert exists_linear_map_coeff_sum_zero h_span;
      -- By `exists_ball_pos_of_pos_continuous_linear_map`, there exists delta > 0 such that for ||v|| < delta, w_i + (L v)_i > 0 for all i.
      obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ v : V, ‖v‖ < δ → ∀ i, 0 < w i + L v i := by
        convert exists_ball_pos_of_pos_continuous_linear_map w hw_pos L using 1;
      -- For any v with ‖v‖ < δ, consider z + v.
      have hz_plus_v : ∀ v : V, ‖v‖ < δ → ∑ i, (w i + L v i) • pts i ∈ convexHull ℝ (Set.range pts) := by
        intro v hv
        have hz_plus_v : ∑ i, (w i + L v i) • pts i = ∑ i, (w i + L v i) • pts i ∧ ∑ i, (w i + L v i) = 1 := by
          simp +decide [ Finset.sum_add_distrib, hw_sum, hL_sum ];
        rw [ mem_convexHull_iff ];
        exact fun t ht ht' => ht'.sum_mem ( fun i _ => hδ v hv i |> le_of_lt ) hz_plus_v.2 ( fun i _ => ht <| Set.mem_range_self i );
      refine' mem_interior_iff_mem_nhds.mpr ( Filter.mem_of_superset ( Metric.ball_mem_nhds _ hδ_pos ) _ );
      intro v hv
      obtain ⟨v', hv'⟩ : ∃ v' : V, v = ∑ i, w i • pts i + v' ∧ ‖v'‖ < δ := by
        exact ⟨ v - ∑ i, w i • pts i, by simp +decide, by simpa [ dist_eq_norm ] using hv ⟩;
      convert hz_plus_v v' hv'.2 using 1 ; simp +decide [ hv'.1, add_smul, Finset.sum_add_distrib, hL_coeff ]

/-
If the affine span of 4 points has dimension less than 2, then the points are not convex independent.
(proven and stated by Aristotle)
-/
lemma not_convexIndependent_of_finrank_affineSpan_lt_two
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {pts : Fin 4 → V}
    (h_rank : Module.finrank ℝ (affineSpan ℝ (Set.range pts)).direction < 2) :
    ¬ ConvexIndependent ℝ pts := by
      -- If the rank of the affine span is less than 2, then the affine span is either a point (rank 0) or a line (rank 1).
      by_cases h_rank_zero : Module.finrank ℝ (affineSpan ℝ (Set.range pts)).direction = 0;
      · -- If the affine span is a point, then all points are equal, and thus they are not convex independent.
        have h_all_equal : ∀ i j : Fin 4, pts i = pts j := by
          simp_all +decide [ Submodule.eq_bot_iff ];
          intro i j; specialize h_rank_zero ( pts i - pts j ) ; simp_all +decide [ sub_eq_zero ] ;
          exact h_rank_zero ( AffineSubspace.vsub_mem_direction ( mem_affineSpan ℝ ( Set.mem_range_self i ) ) ( mem_affineSpan ℝ ( Set.mem_range_self j ) ) );
        simp +decide [ ConvexIndependent, h_all_equal _ 0 ];
        exact ⟨ { 0 }, by simp +decide [ convexHull_singleton ], 1, by simp +decide ⟩;
      · -- If the rank of the affine span is 1, then the points are collinear.
        have h_collinear : ∃ p q : V, q ≠ 0 ∧ ∀ i, ∃ t : ℝ, pts i = p + t • q := by
          -- Since the rank is 1, the direction of the affine span is a 1-dimensional subspace.
          obtain ⟨q, hq⟩ : ∃ q : V, q ≠ 0 ∧ ∀ v ∈ (affineSpan ℝ (Set.range pts)).direction, ∃ t : ℝ, v = t • q := by
            have h_collinear : ∃ q : V, q ≠ 0 ∧ ∀ v ∈ (affineSpan ℝ (Set.range pts)).direction, ∃ t : ℝ, v = t • q := by
              have h_subspace : ∃ W : Submodule ℝ V, W = (affineSpan ℝ (Set.range pts)).direction ∧ Module.finrank ℝ W = 1 := by
                grind
              obtain ⟨ W, hW₁, hW₂ ⟩ := h_subspace;
              obtain ⟨ q, hq ⟩ := ( finrank_eq_one_iff'.mp hW₂ );
              refine' ⟨ q, _, _ ⟩ <;> simp_all +decide [ Submodule.eq_bot_iff ];
              exact fun v hv => by obtain ⟨ t, ht ⟩ := hq.2 v hv; exact ⟨ t, by simpa [ Subtype.ext_iff ] using ht.symm ⟩ ;
            exact h_collinear;
          refine' ⟨ pts 0, q, hq.1, fun i => _ ⟩;
          obtain ⟨ t, ht ⟩ := hq.2 ( pts i - pts 0 ) ( by exact AffineSubspace.vsub_mem_direction ( show pts i ∈ affineSpan ℝ ( Set.range pts ) from mem_affineSpan ℝ ( Set.mem_range_self _ ) ) ( show pts 0 ∈ affineSpan ℝ ( Set.range pts ) from mem_affineSpan ℝ ( Set.mem_range_self _ ) ) );
          exact ⟨ t, eq_add_of_sub_eq' ht ⟩;
        obtain ⟨ p, q, hq, hpq ⟩ := h_collinear;
        -- Since the points are collinear, we can map them to ℝ via an isometry (or affine isomorphism).
        obtain ⟨t, ht⟩ : ∃ t : Fin 4 → ℝ, ∀ i, pts i = p + t i • q := by
          exact ⟨ fun i => Classical.choose ( hpq i ), fun i => Classical.choose_spec ( hpq i ) ⟩;
        -- Since the points are collinear, we can map them to ℝ via an isometry (or affine isomorphism). In ℝ, any set of 3 or more distinct points is not convex independent (one must be between the others).
        by_cases h_distinct : ∃ i j k : Fin 4, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ t i ≠ t j ∧ t i ≠ t k ∧ t j ≠ t k;
        · obtain ⟨ i, j, k, hij, hik, hjk, hti, htj, htk ⟩ := h_distinct;
          -- Without loss of generality, assume $t_i < t_j < t_k$.
          suffices h_wlog : ∀ {i j k : Fin 4}, i ≠ j → i ≠ k → j ≠ k → t i < t j → t j < t k → ¬ConvexIndependent ℝ pts by
            cases lt_or_gt_of_ne hti <;> cases lt_or_gt_of_ne htj <;> cases lt_or_gt_of_ne htk <;> first | exact h_wlog hij hik hjk ( by linarith ) ( by linarith ) | skip;
            · grind;
            · grind;
            · grind;
            · grind;
            · grind;
          intro i j k hij hik hjk hti htj
          have h_convex_comb : pts j = (1 - (t j - t i) / (t k - t i)) • pts i + ((t j - t i) / (t k - t i)) • pts k := by
            simp +decide [ ht, smul_add, sub_smul, div_eq_inv_mul];
            simp +decide [ ← smul_assoc, ← sub_smul ] ; abel_nf;
            simp +decide [ ← add_smul,] ; ring_nf;
            grind;
          rw [ convexIndependent_iff_notMem_convexHull_diff ];
          push_neg;
          refine' ⟨ j, { i, k }, _ ⟩;
          rw [ convexHull_eq ];
          refine' ⟨ Fin 2, { 0, 1 }, fun x => if x = 0 then 1 - ( t j - t i ) / ( t k - t i ) else ( t j - t i ) / ( t k - t i ), fun x => if x = 0 then pts i else pts k, _, _, _, _ ⟩ <;> simp +decide [ Finset.centerMass ];
          · exact ⟨ div_le_one_of_le₀ ( by linarith ) ( by linarith ), div_nonneg ( by linarith ) ( by linarith ) ⟩;
          · grind;
          · exact h_convex_comb.symm;
        · -- If there are no three distinct points, then there must be at least two points that are equal.
          obtain ⟨i, j, hij, h_eq⟩ : ∃ i j : Fin 4, i ≠ j ∧ t i = t j := by
            contrapose! h_distinct;
            exact ⟨ 0, 1, 2, by decide, by decide, by decide, h_distinct 0 1 ( by decide ), h_distinct 0 2 ( by decide ), h_distinct 1 2 ( by decide ) ⟩;
          intro h;
          have := h.injective;
          exact hij ( this ( by rw [ ht i, ht j, h_eq ] ) )

/-
4 convex independent points in a 2D space span the whole space.
(proven and stated by Aristotle)
-/
lemma affineSpan_eq_top_of_convexIndependent_fin_4
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Fact (Module.finrank ℝ V = 2)]
    {pts : Fin 4 → V} (h_indep : ConvexIndependent ℝ pts) :
    affineSpan ℝ (Set.range pts) = ⊤ := by
      -- If the affine span is not top, then its dimension is less than 2 (since dim V = 2).
      by_contra h_contra
      have h_dim : Module.finrank ℝ (affineSpan ℝ (Set.range pts)).direction < 2 := by
        have h_dim_lt_two : Module.finrank ℝ (affineSpan ℝ (Set.range pts)).direction < Module.finrank ℝ V := by
          have h_dim_lt_two : (affineSpan ℝ (Set.range pts)).direction ≠ ⊤ := by
            intro h
            have h_eq : affineSpan ℝ (Set.range pts) = ⊤ := by
              refine' AffineSubspace.ext_of_direction_eq _ _;
              · aesop;
              · exact ⟨ _, Set.mem_inter ( subset_affineSpan ℝ _ <| Set.mem_range_self 0 ) trivial ⟩
            contradiction
          exact Submodule.finrank_lt h_dim_lt_two;
        exact h_dim_lt_two.trans_le ( by rw [ Fact.out ( p := Module.finrank ℝ V = 2 ) ] );
      exact not_convexIndependent_of_finrank_affineSpan_lt_two h_dim h_indep

/-
If segments formed by disjoint pairs of convex independent points intersect, the intersection point is strictly inside both segments.
(proven and stated by Aristotle)
-/
lemma mem_openSegment_of_inter_segments_convexIndependent
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {pts : Fin 4 → V} (h_indep : ConvexIndependent ℝ pts)
    {i j k l : Fin 4}
    (h_disj_idx : ({i, j} : Set (Fin 4)) ∩ {k, l} = ∅)
    (z : V)
    (hz_ij : z ∈ segment ℝ (pts i) (pts j))
    (hz_kl : z ∈ segment ℝ (pts k) (pts l)) :
    z ∈ openSegment ℝ (pts i) (pts j) ∧ z ∈ openSegment ℝ (pts k) (pts l) := by
      -- By definition of open segment, we need to show that $z$ is not an endpoint of either segment.
      have h_not_endpoint_ij : z ≠ pts i ∧ z ≠ pts j := by
        have h_not_endpoint_ij : ∀ i j k l : Fin 4, i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l → ¬(pts i ∈ segment ℝ (pts k) (pts l)) := by
          intro i j k l h_disjoint h_mem
          have h_convex_hull : pts i ∈ convexHull ℝ ({pts k, pts l} : Set V) := by
            aesop;
          have := h_indep.mem_convexHull_iff;
          specialize this { k, l } i ; simp_all +decide [ Set.image_insert_eq, Set.image_singleton ];
        simp_all +decide [ Set.ext_iff ];
        exact ⟨ fun h => h_not_endpoint_ij i j k l h_disj_idx.1.1 h_disj_idx.1.2 h_disj_idx.2.1 h_disj_idx.2.2 <| h ▸ hz_kl, fun h => h_not_endpoint_ij j i k l h_disj_idx.2.1 h_disj_idx.2.2 h_disj_idx.1.1 h_disj_idx.1.2 <| h ▸ hz_kl ⟩
      have h_not_endpoint_kl : z ≠ pts k ∧ z ≠ pts l := by
        constructor <;> intro h <;> simp_all +decide ;
        · rw [ convexIndependent_iff_notMem_convexHull_diff ] at h_indep;
          refine' h_indep k { i, j } _;
          rw [ convexHull_eq ];
          rcases hz_ij with ⟨ a, b, ha, hb, hab, h ⟩;
          refine' ⟨ Fin 2, { 0, 1 }, fun x => if x = 0 then a else b, fun x => if x = 0 then pts i else pts j, _, _, _, _ ⟩ <;> simp +decide [ *, Finset.centerMass ];
          grind;
        · have := h_indep; simp_all +decide [ segment_eq_image ] ;
          rw [ convexIndependent_iff_notMem_convexHull_diff ] at this;
          contrapose! this;
          use l, { i, j } ; simp_all +decide [ convexHull_eq ] ;
          rcases hz_ij with ⟨ x, hx, hx' ⟩ ; use Fin 2, { 0, 1 }, fun i => if i = 0 then 1 - x else x ; simp_all +decide [ Finset.centerMass ] ;
          exact ⟨ fun b => if b = 0 then pts i else pts j, ⟨ ⟨ i, by aesop ⟩, ⟨ j, by aesop ⟩ ⟩, hx' ⟩;
      simp_all +decide [ segment_eq_image, openSegment_eq_image ];
      exact ⟨ by obtain ⟨ x, hx, rfl ⟩ := hz_ij; exact ⟨ x, ⟨ lt_of_le_of_ne hx.1 ( by aesop_cat ), lt_of_le_of_ne hx.2 ( by aesop_cat ) ⟩, rfl ⟩, by obtain ⟨ x, hx, rfl ⟩ := hz_kl; exact ⟨ x, ⟨ lt_of_le_of_ne hx.1 ( by aesop_cat ), lt_of_le_of_ne hx.2 ( by aesop_cat ) ⟩, rfl ⟩ ⟩

/-
If segments formed by disjoint pairs of convex independent points intersect, the intersection point is in the interior of the convex hull.
(proven and stated by Aristotle)
-/
lemma mem_interior_of_convexIndependent_inter_segments
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Fact (Module.finrank ℝ V = 2)]
    {pts : Fin 4 → V} (h_indep : ConvexIndependent ℝ pts)
    {i j k l : Fin 4}
    (h_disj_idx : ({i, j} : Set (Fin 4)) ∩ {k, l} = ∅)
    (z : V)
    (hz_ij : z ∈ segment ℝ (pts i) (pts j))
    (hz_kl : z ∈ segment ℝ (pts k) (pts l)) :
    z ∈ interior (convexHull ℝ (Set.range pts)) := by
      -- By Lemma `mem_openSegment_of_inter_segments_convexIndependent`, `z` is in the open segments `(pts i, pts j)` and `(pts k, pts l)`.
      obtain ⟨hz_ij_open, hz_kl_open⟩ : z ∈ openSegment ℝ (pts i) (pts j) ∧ z ∈ openSegment ℝ (pts k) (pts l) := by
        apply mem_openSegment_of_inter_segments_convexIndependent h_indep h_disj_idx z hz_ij hz_kl;
      -- This means `z = a • pts i + (1-a) • pts j` for some `0 < a < 1`, and `z = b • pts k + (1-b) • pts l` for some `0 < b < 1`.
      obtain ⟨a, ha⟩ : ∃ a : ℝ, 0 < a ∧ a < 1 ∧ z = a • pts i + (1 - a) • pts j := by
        rcases hz_ij_open with ⟨ a, b, ha, hb, hab, rfl ⟩ ; exact ⟨ a, ha, by linarith, by simp +decide [ ← eq_sub_iff_add_eq' ] at hab; simp +decide [ hab ] ⟩ ;
      obtain ⟨b, hb⟩ : ∃ b : ℝ, 0 < b ∧ b < 1 ∧ z = b • pts k + (1 - b) • pts l := by
        rcases hz_kl_open with ⟨ b, hb, hb' ⟩;
        exact ⟨ b, hb'.1, by linarith, by simpa [ ← hb'.2.2.1 ] using hb'.2.2.2.symm ⟩;
      -- Define weights `w : Fin 4 → ℝ` such that `w i = a/2`, `w j = (1-a)/2`, `w k = b/2`, `w l = (1-b)/2`.
      set w : Fin 4 → ℝ := fun x => if x = i then a / 2 else if x = j then (1 - a) / 2 else if x = k then b / 2 else (1 - b) / 2;
      -- Since `i, j, k, l` are distinct (implied by disjoint sets and size 4), this is well-defined.
      have h_distinct : i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l := by
        simp_all +decide [ Set.ext_iff ];
        constructor <;> intro h <;> simp_all +decide;
        · rw [ convexIndependent_iff_notMem_convexHull_diff ] at h_indep;
          contrapose! h_indep;
          use j, {k, l};
          rw [ convexHull_eq ];
          refine' ⟨ Fin 2, { 0, 1 }, fun i => if i = 0 then b else 1 - b, fun i => if i = 0 then pts k else pts l, _, _, _, _ ⟩ <;> simp +decide [ *, Finset.centerMass ];
          constructor <;> linarith;
        · rw [ convexIndependent_iff_notMem_convexHull_diff ] at h_indep;
          refine' h_indep l { i, j } _;
          rw [ convexHull_eq ];
          refine' ⟨ Fin 2, { 0, 1 }, fun x => if x = 0 then a else 1 - a, fun x => if x = 0 then pts i else pts j, _, _, _, _ ⟩ <;> simp +decide [ *, Finset.centerMass ];
          · constructor <;> linarith;
          · grind;
      -- The weighted sum is `(1/2)(a • pts i + (1-a) • pts j) + (1/2)(b • pts k + (1-b) • pts l) = (1/2)z + (1/2)z = z`.
      have h_weighted_sum : ∑ x, w x • pts x = z := by
        have h_weighted_sum : ∑ x, w x • pts x = (a / 2) • pts i + ((1 - a) / 2) • pts j + (b / 2) • pts k + ((1 - b) / 2) • pts l := by
          rw [ Finset.sum_eq_add_sum_diff_singleton i (fun x => w x • pts x) (by simp) ];
          rw [ show ( Finset.univ \ { i } : Finset ( Fin 4 ) ) = { j, k, l } by fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> trivial ] ; simp +decide [ *, add_assoc ] ;
          grind +ring;
        simp_all +decide [ div_eq_inv_mul ];
        rw [ show ( 2⁻¹ * a ) • pts i = ( 2⁻¹ : ℝ ) • ( a • pts i ) by rw [ smul_smul ], show ( 2⁻¹ * ( 1 - a ) ) • pts j = ( 2⁻¹ : ℝ ) • ( ( 1 - a ) • pts j ) by rw [ smul_smul ], show ( 2⁻¹ * b ) • pts k = ( 2⁻¹ : ℝ ) • ( b • pts k ) by rw [ smul_smul ], show ( 2⁻¹ * ( 1 - b ) ) • pts l = ( 2⁻¹ : ℝ ) • ( ( 1 - b ) • pts l ) by rw [ smul_smul ] ];
        field_simp;
        rw [ show ( 1 / 2 : ℝ ) • a • pts i + ( 1 / 2 : ℝ ) • ( 1 - a ) • pts j + ( 1 / 2 : ℝ ) • b • pts k + ( 1 / 2 : ℝ ) • ( 1 - b ) • pts l = ( 1 / 2 : ℝ ) • ( a • pts i + ( 1 - a ) • pts j + b • pts k + ( 1 - b ) • pts l ) by rw [ smul_add, smul_add, smul_add ] ] ; rw [ show a • pts i + ( 1 - a ) • pts j + b • pts k + ( 1 - b ) • pts l = ( a • pts i + ( 1 - a ) • pts j ) + ( b • pts k + ( 1 - b ) • pts l ) by abel1 ] ; rw [ ha.2.2 ] ; norm_num ; abel_nf;
        norm_num [ ← smul_assoc ];
        norm_num [ ← mul_assoc ];
      -- The affine span is top by `affineSpan_eq_top_of_convexIndependent_fin_4`.
      have h_affine_span : affineSpan ℝ (Set.range pts) = ⊤ := by
        exact affineSpan_eq_top_of_convexIndependent_fin_4 h_indep;
      -- Apply `mem_interior_convexHull_of_pos_comb` with the weights `w` and the fact that their sum is 1.
      apply mem_interior_convexHull_of_pos_comb h_affine_span w (by
      simp +zetaDelta at *;
      intro x; split_ifs <;> linarith;) (by
      simp +decide [ Fin.sum_univ_four ] ; ring_nf;
      grind) |> fun h => h_weighted_sum ▸ h

/-
The centroid of a set `s` can be decomposed into a convex combination of the centroid of a subset `t` and the centroid of the remainder `s \ t`. (aristotle)
-/
lemma centroid_decomposition
    {s t : Finset V} (h_sub : t ⊆ s) (h_t : t.Nonempty) (h_diff : (s \ t).Nonempty) :
    let n := (s.card : ℝ)
    let k := (t.card : ℝ)
    finset_centroid s = (k / n) • finset_centroid t + ((n - k) / n) • finset_centroid (s \ t) := by
      unfold finset_centroid;
      simp +decide [ ← smul_assoc, ← Finset.sum_sdiff h_sub, div_eq_inv_mul ];
      by_cases ht : t.card = 0 <;> by_cases hs : s.card = 0 <;> simp_all +decide [ Finset.card_sdiff ];
      simp +decide [ add_comm ];
      simp +decide [ ← Finset.inter_comm, Finset.inter_eq_right.mpr h_sub, Nat.cast_sub ( Finset.card_le_card h_sub ) ];
      by_cases h : ( s.card : ℝ ) - t.card = 0 <;> simp_all +decide [ sub_eq_iff_eq_add ];
      rw [ Finset.eq_of_subset_of_card_le h_sub ( by simp +decide [ h ] ) ]

/-
The centroid of a nonempty finite set of points lies within the convex hull of those points. (aristotle)
-/
lemma centroid_mem_convexHull {s : Finset V} (h : s.Nonempty) :
    finset_centroid s ∈ convexHull ℝ (s : Set V) := by
      rw [ mem_convexHull_iff ];
      intro t ht ht'
      have h_convex_comb : ∃ (w : V → ℝ), (∀ x ∈ s, 0 ≤ w x) ∧ (∑ x ∈ s, w x = 1) ∧ finset_centroid s = ∑ x ∈ s, w x • x := by
        refine' ⟨ fun x => 1 / s.card, _, _, _ ⟩ <;> simp +decide [ h.ne_empty ];
        unfold finset_centroid; simp +decide [ Finset.smul_sum ] ;
      obtain ⟨ w, hw₁, hw₂, hw₃ ⟩ := h_convex_comb;
      exact hw₃.symm ▸ ht'.sum_mem ( by aesop ) ( by aesop ) ( by aesop )

/-
The centroid of a set of 3 affinely independent points in a 2D space lies in the interior of their convex hull. (aristotle)
-/
lemma affine_independent_triangle_centroid_mem_interior {t : Finset V}
    (h_card : t.card = 3) (h_indep : AffineIndependent ℝ (Subtype.val : t → V)) :
    finset_centroid t ∈ interior (convexHull ℝ (t : Set V)) := by
  -- Construct an `AffineBasis` from `t`. Let `ι := t`. Define `b : AffineBasis ι ℝ V` by `b := AffineBasis.mk (Subtype.val) h_indep h_span`.
  obtain ⟨b, hb⟩ : ∃ b : AffineBasis t ℝ V, ∀ i : t, b i = i.val := by
    have h_span : affineSpan ℝ (Set.range (Subtype.val : t → V)) = ⊤ := by
      have h_span : Module.finrank ℝ (↥(affineSpan ℝ (Set.range (Subtype.val : t → V))).direction) = 2 := by
        have := h_indep;
        convert this.finrank_vectorSpan;
        any_goals exact t.card - 1;
        simp +decide [ h_card ];
        rw [ direction_affineSpan ];
      have h_span : (affineSpan ℝ (Set.range (Subtype.val : t → V))).direction = ⊤ := by
        exact Submodule.eq_top_of_finrank_eq ( by simp +decide [ h_span, Fact.out ( p := Module.finrank ℝ V = 2 ) ] );
      ext x; simp;
      have h_span : ∀ x : V, x ∈ affineSpan ℝ (Set.range (Subtype.val : t → V)) := by
        intro x; exact (by
        have h_span : ∀ x : V, x ∈ affineSpan ℝ (Set.range (Subtype.val : t → V)) := by
          intro x
          have h_span : x - (Classical.choose (Finset.card_pos.mp (by linarith : 0 < t.card))) ∈ (affineSpan ℝ (Set.range (Subtype.val : t → V))).direction := by
            aesop
          convert AffineSubspace.vadd_mem_of_mem_direction h_span ( Classical.choose_spec ( Finset.card_pos.mp ( by linarith : 0 < t.card ) ) |> fun h => subset_affineSpan ℝ _ <| Set.mem_range_self <| ⟨ _, h ⟩ ) using 1 ; simp +decide;
        exact h_span x);
      convert h_span x using 1;
      exact congr_arg _ ( by ext; simp +decide );
    refine' ⟨ _, _ ⟩;
    exact { toFun := Subtype.val, ind' := h_indep, tot' := h_span };
    aesop;
  convert b.centroid_mem_interior_convexHull using 1;
  · congr! 2;
    ext; aesop;
  · simp +decide [ Finset.centroid];
    simp +decide [ Finset.affineCombination, Finset.centroidWeights, hb, finset_centroid ];
    simp +decide [ ← Finset.smul_sum, h_card ];
    rw [ ← Finset.sum_attach ];
    module


/-
A set of 3 convex independent points is affinely independent (i.e., forms a non-degenerate triangle). (aristotle)
-/
lemma convex_independent_triangle_is_affine_independent {s : Finset V}
    (hs : ConvexIndependent ℝ (Subtype.val : s → V))
    (hc : s.card = 3) :
    AffineIndependent ℝ (Subtype.val : s → V) := by
    -- Suppose the points are not affinely independent. Since there are 3 points, they must be collinear.
    by_contra h_not_affine_indep
    have h_collinear : Collinear ℝ (s : Set V) := by
      rw [ collinear_iff_rank_le_one ];
      -- Since the points are not affinely independent, their vector span has a dimension less than the number of points minus one.
      have h_dim_lt : Module.finrank ℝ (vectorSpan ℝ (s : Set V)) < 3 - 1 := by
        contrapose! h_not_affine_indep;
        rw [ affineIndependent_iff_linearIndependent_vsub ];
        swap;
        exact ⟨ Classical.choose ( Finset.card_pos.mp ( by linarith ) ), Classical.choose_spec ( Finset.card_pos.mp ( by linarith ) ) ⟩;
        have h_lin_ind : Module.finrank ℝ (vectorSpan ℝ (s : Set V)) = Module.finrank ℝ (Submodule.span ℝ (Set.image (fun x : { x : V // x ∈ s } => (x : V) -ᵥ (Classical.choose (Finset.card_pos.mp (by linarith : 0 < s.card))) : { x : V // x ∈ s } → V) {x : { x : V // x ∈ s } | x ≠ ⟨Classical.choose (Finset.card_pos.mp (by linarith : 0 < s.card)), Classical.choose_spec (Finset.card_pos.mp (by linarith : 0 < s.card))⟩})) := by
          rw [ vectorSpan_eq_span_vsub_set_right ];
          rotate_left;
          exact Classical.choose ( Finset.card_pos.mp ( by linarith ) );
          · exact Classical.choose_spec ( Finset.card_pos.mp ( by linarith ) );
          · rw [ show ( fun x : V => x -ᵥ Classical.choose ( Finset.card_pos.mp ( by linarith ) ) ) '' ( s : Set V ) = ( fun x : { x : V // x ∈ s } => ( x : V ) -ᵥ Classical.choose ( Finset.card_pos.mp ( by linarith ) ) ) '' { x : { x : V // x ∈ s } | x ≠ ⟨ Classical.choose ( Finset.card_pos.mp ( by linarith ) ), Classical.choose_spec ( Finset.card_pos.mp ( by linarith ) ) ⟩ } ∪ { 0 } from ?_ ];
            · rw [ Submodule.span_union ];
              rw [ sup_eq_left.mpr ];
              simp +decide;
            · ext x; simp [Set.mem_image];
              constructor;
              · rintro ⟨ y, hy, rfl ⟩ ; by_cases hy' : y = Classical.choose ( Finset.card_pos.mp ( by linarith ) ) <;> aesop;
              · rintro ( rfl | ⟨ a, ha, ha', rfl ⟩ ) <;> [ exact ⟨ Classical.choose ( Finset.card_pos.mp ( by linarith ) ), Classical.choose_spec ( Finset.card_pos.mp ( by linarith ) ), by simp +decide ⟩ ; exact ⟨ a, ha', rfl ⟩ ];
        rw [ linearIndependent_iff_card_le_finrank_span ];
        convert h_not_affine_indep using 1;
        · simp +decide [ hc ];
        · convert h_lin_ind.symm using 1;
          rw [ Set.finrank ];
          congr! 2;
          · congr! 2;
            exact congr_arg _ ( by ext; aesop );
          · exact congr_arg _ ( by ext; simp +decide [ Set.mem_image ] );
          · exact congr_arg _ ( by ext; simp +decide [ Set.mem_image ] );
      rw [ ← Module.finrank_eq_rank ] ; interval_cases _ : Module.finrank ℝ ( vectorSpan ℝ ( s : Set V ) ) <;> simp_all +decide;
    -- If the points are collinear, then one of them must lie strictly between the other two (and thus in their convex hull).
    obtain ⟨a, b, c, ha, hb, hc, h_collinear⟩ : ∃ a b c : V, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ b ∈ segment ℝ a c := by
      have := Finset.card_eq_three.mp hc;
      obtain ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ := this;
      simp_all +decide [ collinear_iff_exists_forall_eq_smul_vadd ];
      rcases h_collinear with ⟨ p₀, v, ⟨ r₁, hr₁ ⟩, ⟨ r₂, hr₂ ⟩, ⟨ r₃, hr₃ ⟩ ⟩ ; simp_all +decide [ segment_eq_image ] ;
      -- Since $r₁$, $r₂$, and $r₃$ are distinct, we can order them. Without loss of generality, assume $r₁ < r₂ < r₃$.
      suffices h_order : ∀ {r₁ r₂ r₃ : ℝ}, r₁ ≠ r₂ → r₁ ≠ r₃ → r₂ ≠ r₃ → (∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ (1 - x) * r₁ + x * r₃ = r₂) ∨ (∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ (1 - x) * r₂ + x * r₃ = r₁) ∨ (∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ (1 - x) * r₂ + x * r₁ = r₃) by
        specialize @h_order r₁ r₂ r₃ ; simp_all +decide [ smul_smul, ← add_assoc ];
        rcases h_order ( by aesop ) ( by aesop ) ( by aesop ) with ( ⟨ x, hx₁, hx₂, hx₃ ⟩ | ⟨ x, hx₁, hx₂, hx₃ ⟩ | ⟨ x, hx₁, hx₂, hx₃ ⟩ ) <;> simp_all +decide [ mul_comm ];
        · exact Or.inl <| Or.inl ⟨ x, ⟨ hx₁, hx₂ ⟩, by rw [ ← hx₃ ] ; simp +decide [ add_smul, sub_smul ] ; abel1 ⟩;
        · exact Or.inr <| Or.inl <| Or.inl ⟨ by tauto, x, ⟨ hx₁, hx₂ ⟩, by rw [ ← hx₃ ] ; simp +decide [ add_smul, sub_smul ] ; abel1 ⟩;
        · refine' Or.inr ( Or.inl ( Or.inr ⟨ _, _, _ ⟩ ) );
          · exact fun a => hxz (id (Eq.symm a))
          · exact fun a => hxy (id (Eq.symm a));
          · exact ⟨ x, ⟨ hx₁, hx₂ ⟩, by rw [ ← hx₃ ] ; simp +decide [ add_smul, sub_smul ] ; abel1 ⟩;
      intro r₁ r₂ r₃ h₁₂ h₁₃ h₂₃; cases lt_or_gt_of_ne h₁₂ <;> cases lt_or_gt_of_ne h₁₃ <;> cases lt_or_gt_of_ne h₂₃ <;> first | exact Or.inl ⟨ ( r₂ - r₁ ) / ( r₃ - r₁ ), by nlinarith [ mul_div_cancel₀ ( r₂ - r₁ ) ( sub_ne_zero_of_ne <| by tauto : ( r₃ - r₁ ) ≠ 0 ) ], by nlinarith [ mul_div_cancel₀ ( r₂ - r₁ ) ( sub_ne_zero_of_ne <| by tauto : ( r₃ - r₁ ) ≠ 0 ) ], by nlinarith [ mul_div_cancel₀ ( r₂ - r₁ ) ( sub_ne_zero_of_ne <| by tauto : ( r₃ - r₁ ) ≠ 0 ) ] ⟩ | skip;
      · exact Or.inr <| Or.inr <| ⟨ ( r₂ - r₃ ) / ( r₂ - r₁ ), div_nonneg ( by linarith ) ( by linarith ), div_le_one_of_le₀ ( by linarith ) ( by linarith ), by linarith [ mul_div_cancel₀ ( r₂ - r₃ ) ( by linarith : ( r₂ - r₁ ) ≠ 0 ) ] ⟩;
      · exact Or.inr <| Or.inl ⟨ ( r₁ - r₂ ) / ( r₃ - r₂ ), div_nonneg_of_nonpos ( by linarith ) ( by linarith ), div_le_one_of_ge ( by linarith ) ( by linarith ), by linarith [ mul_div_cancel₀ ( r₁ - r₂ ) ( by linarith : ( r₃ - r₂ ) ≠ 0 ) ] ⟩;
      · exact Or.inr <| Or.inl ⟨ ( r₁ - r₂ ) / ( r₃ - r₂ ), div_nonneg ( by linarith ) ( by linarith ), div_le_one_of_le₀ ( by linarith ) ( by linarith ), by linarith [ mul_div_cancel₀ ( r₁ - r₂ ) ( by linarith : ( r₃ - r₂ ) ≠ 0 ) ] ⟩;
      · exact Or.inr <| Or.inr <| ⟨ ( r₃ - r₂ ) / ( r₁ - r₂ ), div_nonneg ( by linarith ) ( by linarith ), div_le_one_of_le₀ ( by linarith ) ( by linarith ), by linarith [ mul_div_cancel₀ ( r₃ - r₂ ) ( by linarith : ( r₁ - r₂ ) ≠ 0 ) ] ⟩;
    have := hs { ⟨ a, ha ⟩, ⟨ c, hc ⟩ } ; simp_all +decide [ segment_eq_image ] ;
    have := hs { ⟨ a, ha ⟩, ⟨ c, hc ⟩ } ; simp_all +decide [ convexIndependent_iff_notMem_convexHull_diff ] ;
    refine' hs b hb { ⟨ a, ha ⟩, ⟨ c, by assumption ⟩ } _;
    rcases h_collinear.2.2.2 with ⟨ x, hx, rfl ⟩ ; rw [ convexHull_eq ] ; simp +decide;
    refine' ⟨ Fin 2, { 0, 1 }, fun i => if i = 0 then 1 - x else x, _, _, fun i => if i = 0 then a else c, _, _ ⟩ <;> simp +decide [ *, Finset.centerMass ];
    exact Ne.symm h_collinear.2.1


/--
Helper: The centroid of a convexly independent set of at least 3 points in a 2D plane
lies in the interior of its convex hull. (aristotle)
-/
lemma centroid_in_interior {s : Finset V}
    (h_conv : ConvexIndependent ℝ (Subtype.val : s → V))
    (h_card : 3 ≤ s.card) :
    finset_centroid s ∈ interior (convexHull ℝ (s : Set V)) := by
  -- Choose a subset `t ⊆ s` with `t.card = 3`.
  obtain ⟨t, ht⟩ : ∃ t : Finset V, t ⊆ s ∧ t.card = 3 := by
    exact Finset.le_card_iff_exists_subset_card.mp h_card
  -- Since `t` is a subset of `s` with `t.card = 3`, `t` is convex independent (by `ConvexIndependent.mono` from `s`).
  have h_t_conv : ConvexIndependent ℝ (Subtype.val : t → V) := by
    exact h_conv.mono ht.1;
  -- By `convex_independent_triangle_is_affine_independent`, `t` is affinely independent.
  have h_t_aff : AffineIndependent ℝ (Subtype.val : t → V) := by
    convert convex_independent_triangle_is_affine_independent h_t_conv ht.2 using 1;
  -- By `affine_independent_triangle_centroid_mem_interior`, `c_t := finset_centroid t` is in `interior (convexHull t)`.
  have h_c_t_interior : finset_centroid t ∈ interior (convexHull ℝ (t : Set V)) := by
    exact affine_independent_triangle_centroid_mem_interior ht.2 h_t_aff;
  -- Since `convexHull t ⊆ convexHull s`, `interior (convexHull t) ⊆ interior (convexHull s)` (by `interior_mono`). Thus `c_t ∈ interior (convexHull s)`.
  have h_c_t_interior_s : finset_centroid t ∈ interior (convexHull ℝ (s : Set V)) := by
    exact interior_mono ( convexHull_mono ht.1 ) h_c_t_interior;
  -- If `s.card = 3`, then `s = t`, so `finset_centroid s = c_t ∈ interior (convexHull s)`.
  by_cases h_card_eq : s.card = 3;
  · have := Finset.eq_of_subset_of_card_le ht.1 ; aesop;
  · -- If `s.card > 3`, let `r = s \ t`. `r` is nonempty. Let `c_r := finset_centroid r`.
    set r := s \ t with hr_def
    have hr_nonempty : r.Nonempty := by
      exact Finset.nonempty_of_ne_empty ( by rw [ Ne.eq_def, Finset.sdiff_eq_empty_iff_subset ] ; exact fun h => h_card_eq <| by have := Finset.card_le_card h; linarith )
    set c_r := finset_centroid r with hc_r_def;
    -- By `centroid_decomposition`, `finset_centroid s` is a strict convex combination of `c_t` and `c_r`.
    have h_centroid_decomposition : finset_centroid s = (t.card / s.card : ℝ) • finset_centroid t + ((s.card - t.card) / s.card : ℝ) • c_r := by
      convert centroid_decomposition ht.1 _ hr_nonempty using 1;
      exact Finset.card_pos.mp ( by linarith );
    -- By `centroid_mem_convexHull`, `c_r ∈ convexHull r ⊆ convexHull s`.
    have h_c_r_convexHull : c_r ∈ convexHull ℝ (s : Set V) := by
      have h_c_r_convexHull : c_r ∈ convexHull ℝ (r : Set V) := by
        exact centroid_mem_convexHull hr_nonempty;
      exact convexHull_mono ( Finset.coe_subset.mpr ( Finset.sdiff_subset ) ) h_c_r_convexHull;
    -- By `Convex.combo_interior_self_mem_interior`, `finset_centroid s ∈ interior (convexHull s)`.
    have h_centroid_interior : ∀ {x y : V}, x ∈ interior (convexHull ℝ (s : Set V)) → y ∈ convexHull ℝ (s : Set V) → ∀ {a b : ℝ}, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ interior (convexHull ℝ (s : Set V)) := by
      intro x y hx hy a b ha hb hab;
      rw [ mem_interior_iff_mem_nhds, Metric.mem_nhds_iff ] at *;
      obtain ⟨ ε, ε_pos, hε ⟩ := hx;
      refine' ⟨ a * ε, mul_pos ha ε_pos, fun z hz => _ ⟩;
      -- Since $z$ is within $a \epsilon$ of $a x + b y$, we can write $z$ as $a x' + b y$ for some $x'$ within $\epsilon$ of $x$.
      obtain ⟨x', hx'⟩ : ∃ x', z = a • x' + b • y ∧ dist x' x < ε := by
        refine' ⟨ ( 1 / a ) • ( z - b • y ), _, _ ⟩ <;> simp_all +decide [ ne_of_gt, smul_smul ];
        rw [ dist_eq_norm ] at *;
        rw [ show a⁻¹ • ( z - b • y ) - x = a⁻¹ • ( z - ( a • x + b • y ) ) by simp +decide [ smul_add, smul_sub, ← smul_assoc, ha.ne' ] ; abel1 ] ; rw [ norm_smul, Real.norm_of_nonneg ( inv_nonneg.2 ha.le ) ] ; rw [ inv_mul_lt_iff₀ ha ] ; linarith;
      rw [ hx'.1 ];
      exact convex_convexHull ℝ _ ( hε ( Metric.mem_ball.mpr hx'.2 ) ) hy ( by positivity ) ( by positivity ) ( by linarith );
    convert h_centroid_interior h_c_t_interior_s h_c_r_convexHull _ _ _ using 1 <;> norm_num [ ht.2 ];
    · exact Finset.card_pos.mp ( pos_of_gt h_card );
    · exact div_pos ( sub_pos.mpr ( mod_cast lt_of_le_of_ne h_card ( Ne.symm h_card_eq ) ) ) ( Nat.cast_pos.mpr ( pos_of_gt h_card ) );
    · rw [ ← add_div, div_eq_iff ] <;> linarith [ show ( s.card : ℝ ) ≥ 3 by norm_cast ]


/-
A ray starting from an interior point of a closed convex set intersects the frontier at a unique point.
-/
lemma unique_ray_intersection_frontier {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K : Set V} (hK_conv : Convex ℝ K) (hK_closed : IsClosed K)
    {C : V} (hC : C ∈ interior K)
    {u v : V} (hu : u ∈ frontier K) (hv : v ∈ frontier K)
    (h_ray : SameRay ℝ (u - C) (v - C)) : u = v := by
      -- Since $u$ and $v$ are in the frontier of $K$ and $C$ is in the interior, the line segment $Cu$ and $Cv$ must both be in $K$ and intersect the frontier at $u$ and $v$ respectively. Therefore, $u$ and $v$ must be equal.
      have h_eq : ∀ t : ℝ, 0 < t → t < 1 → C + t • (u - C) ∈ interior K ∧ C + t • (v - C) ∈ interior K := by
        intro t ht ht'
        have h_interior : ∀ x y : V, x ∈ interior K → y ∈ K → ∀ t : ℝ, 0 < t → t < 1 → x + t • (y - x) ∈ interior K := by
          intro x y hx hy t ht ht'
          have h_interior : ∀ x y : V, x ∈ interior K → y ∈ K → ∀ t : ℝ, 0 < t → t < 1 → x + t • (y - x) ∈ interior K := by
            intro x y hx hy t ht ht'
            have h_convex : Convex ℝ K := hK_conv
            have h_interior : x ∈ interior K := hx
            have h_y : y ∈ K := hy
            rw [ mem_interior_iff_mem_nhds, Metric.mem_nhds_iff ] at *;
            obtain ⟨ ε, ε_pos, hε ⟩ := h_interior;
            refine' ⟨ ε * ( 1 - t ), mul_pos ε_pos ( sub_pos.mpr ht' ), fun z hz => _ ⟩;
            -- Since $z$ is in the ball around $x + t • (y - x)$ with radius $\epsilon * (1 - t)$, we can write $z$ as $x + t • (y - x) + w$ where $w$ is in the ball around $0$ with radius $\epsilon * (1 - t)$.
            obtain ⟨w, hw⟩ : ∃ w : V, z = x + t • (y - x) + w ∧ ‖w‖ < ε * (1 - t) := by
              exact ⟨ z - ( x + t • ( y - x ) ), by simp +decide, by simpa [ dist_eq_norm ] using hz ⟩;
            -- Since $w$ is in the ball around $0$ with radius $\epsilon * (1 - t)$, we can write $w$ as $(1 - t) • u$ for some $u$ in the ball around $0$ with radius $\epsilon$.
            obtain ⟨u, hu⟩ : ∃ u : V, w = (1 - t) • u ∧ ‖u‖ < ε := by
              refine' ⟨ ( 1 - t ) ⁻¹ • w, _, _ ⟩ <;> simp +decide [ norm_smul, abs_of_pos, ht', ne_of_gt ];
              rw [ inv_mul_lt_iff₀ ] <;> linarith;
            convert h_convex ( hε <| show x + u ∈ Metric.ball x ε from by simpa [ dist_eq_norm ] using hu.2 ) h_y ( show 0 ≤ 1 - t by linarith ) ( show 0 ≤ t by linarith ) ( by linarith ) using 1 ; simp +decide [ hw.1, hu.1 ] ; ring_nf;
            simp +decide [ smul_sub, sub_smul ] ; abel_nf;
          exact h_interior x y hx hy t ht ht';
        exact ⟨ h_interior C u hC ( frontier_subset_closure hu |> fun h => hK_closed.closure_subset h ) t ht ht', h_interior C v hC ( frontier_subset_closure hv |> fun h => hK_closed.closure_subset h ) t ht ht' ⟩;
      -- Since $u$ and $v$ are in the frontier of $K$ and $C$ is in the interior, the line segment $Cu$ and $Cv$ must both be in $K$ and intersect the frontier at $u$ and $v$ respectively. Therefore, $u$ and $v$ must be equal by the properties of the frontier.
      have h_eq_frontier : ∀ t : ℝ, 0 < t → t < 1 → C + t • (u - C) ∉ frontier K ∧ C + t • (v - C) ∉ frontier K := by
        simp_all +decide [ frontier_eq_closure_inter_closure, mem_interior_iff_mem_nhds ];
      cases' h_ray with h h
      · simp_all +decide [ sub_eq_zero ];
        exact absurd ( h_eq_frontier ( 1 / 2 ) ( by norm_num ) ) ( by norm_num );
      · rcases h with ( h | ⟨ r₁, r₂, hr₁, hr₂, h ⟩ )
        · simp_all +decide [ sub_eq_zero ];
          exact absurd ( h_eq_frontier ( 1 / 2 ) ( by norm_num ) ) ( by norm_num );
        · -- Since $r₁$ and $r₂$ are positive, we can divide both sides of the equation $r₁ • (u - C) = r₂ • (v - C)$ by $r₁$ and $r₂$ respectively.
          have h_div : (r₁ / r₂) • (u - C) = v - C := by
            calc
              (r₁ / r₂) • (u - C) = r₂⁻¹ • (r₁ • (u - C)) := by
                rw [div_eq_inv_mul, SemigroupAction.mul_smul]
              _ = r₂⁻¹ • (r₂ • (v - C)) := by rw [h]
              _ = v - C := by rw [inv_smul_smul₀ hr₂.ne']
          by_cases hr₁₂ : r₁ / r₂ ≤ 1;
          · by_cases hr₁₂' : r₁ / r₂ < 1;
            · have := h_eq_frontier ( r₁ / r₂ ) ( div_pos hr₁ hr₂ ) hr₁₂';
              simp_all +decide;
            · norm_num [ show r₁ / r₂ = 1 by linarith ] at *;
              exact h_div;
          · have h_div : (1 / (r₁ / r₂)) • (v - C) = u - C := by
              rw [ ← h_div, one_div, inv_smul_smul₀ ( by positivity ) ];
            specialize h_eq_frontier ( 1 / ( r₁ / r₂ ) ) ( by positivity ) ( by rw [ div_lt_iff₀ ( by positivity ) ] ; linarith ) ; simp_all +decide ;

/-
An extreme point of a convex set cannot lie in its interior.
-/
lemma extremePoint_not_in_interior {K : Set V} (hK : Convex ℝ K) {x : V} (hx : x ∈ K)
    (h_extreme : x ∈ Set.extremePoints ℝ K) : x ∉ interior K := by
      -- If x were in the interior, there would exist an open ball around x contained in K.
      by_contra h_interior
      obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, Metric.ball x ε ⊆ K := by
        exact Metric.mem_nhds_iff.1 ( mem_interior_iff_mem_nhds.1 h_interior );
      -- Since $V$ is a normed space and non-trivial (dimension 2), there exists a vector $v \neq 0$ with $\|v\| < \epsilon$.
      obtain ⟨v, hv_ne_zero, hv_norm⟩ : ∃ v : V, v ≠ 0 ∧ ‖v‖ < ε := by
        -- Since $V$ is a finite-dimensional inner product space, we can choose a nonzero vector $v$.
        obtain ⟨v, hv_ne_zero⟩ : ∃ v : V, v ≠ 0 := by
          by_cases h : ∃ v : V, v ≠ 0;
          · exact h;
          · have := Fact.out ( p := Module.finrank ℝ V = 2 ) ; simp_all +decide [ Module.finrank ] ;
            rw [ show Module.rank ℝ V = 0 by rw [ show Module.rank ℝ V = 0 by exact rank_zero_iff_forall_zero.mpr h ] ] at this ; norm_num at this;
        exact ⟨ ( ε / 2 / ‖v‖ ) • v, by simp [ hv_ne_zero, hε_pos.ne' ], by rw [ norm_smul, Real.norm_of_nonneg ( by positivity ), div_mul_cancel₀ _ ( norm_ne_zero_iff.mpr hv_ne_zero ) ] ; linarith ⟩;
      -- Then $x + v$ and $x - v$ are in $B(x, \epsilon)$, hence in $K$.
      have h_plus_minus : x + v ∈ K ∧ x - v ∈ K := by
        exact ⟨ hε ( mem_ball_iff_norm.mpr ( by simpa ) ), hε ( mem_ball_iff_norm.mpr ( by simpa ) ) ⟩;
      -- Note that $x = (1/2) • (x + v) + (1/2) • (x - v)$.
      have h_comb : x = (1 / 2 : ℝ) • (x + v) + (1 / 2 : ℝ) • (x - v) := by
        simp +decide [ ← two_smul ℝ, smul_add, smul_sub ];
      have := h_extreme.2 h_plus_minus.1 h_plus_minus.2;
      exact hv_ne_zero ( by simpa using this ⟨ 1 / 2, 1 / 2, by norm_num, by norm_num, by simpa [ ← two_smul ℝ ] using h_comb.symm ⟩ )

/-
If a point x in a convex independent set s is expressed as a convex combination of s, then the coefficient of x must be 1.
-/
lemma convex_combination_unique_at_vertex {s : Finset V}
    (hc : ConvexIndependent ℝ (Subtype.val : s → V))
    {x : V} (hx : x ∈ s)
    {w : V → ℝ} (hw_nonneg : ∀ v ∈ s, 0 ≤ w v)
    (hw_sum : ∑ v ∈ s, w v = 1)
    (hw_comb : ∑ v ∈ s, w v • v = x) : w x = 1 := by
  -- If $w x < 1$, then the sum of the coefficients excluding $x$ is $1 - w x$, which is positive.
  by_cases h_wx_lt_1 : w x < 1;
  · -- Since $w x < 1$, we have $x = \sum_{v \in s \setminus \{x\}} \frac{w v}{1 - w x} • v$.
    have hx_comb : x = ∑ v ∈ s.erase x, (w v / (1 - w x)) • v := by
      have hx_comb : (1 - w x) • x = ∑ v ∈ s.erase x, w v • v := by
        simp_all +decide [ sub_smul];
      convert congr_arg ( fun y => ( 1 - w x ) ⁻¹ • y ) hx_comb using 1 <;> norm_num [ div_eq_inv_mul, Finset.smul_sum, smul_smul ];
      rw [ inv_mul_cancel₀ ( by linarith ), one_smul ];
    -- Since $x$ is in the convex hull of $s \setminus \{x\}$, this contradicts the convex independence of $s$.
    have h_contradiction : x ∈ convexHull ℝ (s.erase x : Set V) := by
      rw [ mem_convexHull_iff ];
      intro t ht ht_convex
      have h_comb : x = ∑ v ∈ s.erase x, (w v / (1 - w x)) • v := by
        exact hx_comb;
      refine' h_comb ▸ ht_convex.sum_mem _ _ _;
      · exact fun v hv => div_nonneg ( hw_nonneg v ( Finset.mem_of_mem_erase hv ) ) ( sub_nonneg.2 h_wx_lt_1.le );
      · rw [ ← Finset.sum_div, ← Finset.sum_erase_add _ _ hx, add_comm ] at * ; nlinarith [ mul_div_cancel₀ ( ∑ v ∈ s.erase x, w v ) ( by linarith : ( 1 - w x ) ≠ 0 ) ];
      · exact fun v hv => ht hv;
    have h_contradiction : x ∈ insert x (s.erase x : Finset V) ∧ x ∈ convexHull ℝ (s.erase x : Set V) := by
      grind;
    convert hc _ _;
    rotate_left;
    exact Set.image ( fun v : s => v ) ( { y : s | y.val ≠ x } );
    exact ⟨ x, hx ⟩;
    simp +decide [ h_wx_lt_1.ne ];
    convert h_contradiction.2 using 1;
    congr with y ; simp +decide;
    tauto;
  · exact le_antisymm ( hw_sum ▸ Finset.single_le_sum ( fun v _ => hw_nonneg v ‹_› ) hx ) ( not_lt.mp h_wx_lt_1 )

/-
Points of a convex independent set are extreme points of their convex hull.
-/
lemma convexIndependent_implies_extremePoints {s : Finset V}
    (hc : ConvexIndependent ℝ (Subtype.val : s → V))
    {x : V} (hx : x ∈ s) :
    x ∈ Set.extremePoints ℝ (convexHull ℝ (s : Set V)) := by
      refine' ⟨ _, _ ⟩;
      · exact subset_convexHull ℝ _ ( Finset.mem_coe.2 hx );
      · intro y hy z hz hx
        obtain ⟨ a, ha_nonneg, ha_sum, ha_comb ⟩ : ∃ a : V → ℝ, (∀ v ∈ s, 0 ≤ a v) ∧ (∑ v ∈ s, a v = 1) ∧ (∑ v ∈ s, a v • v = y) := by
          exact Finset.mem_convexHull'.mp hy
        obtain ⟨ b, hb_nonneg, hb_sum, hb_comb ⟩ : ∃ b : V → ℝ, (∀ v ∈ s, 0 ≤ b v) ∧ (∑ v ∈ s, b v = 1) ∧ (∑ v ∈ s, b v • v = z) := by
          exact Finset.mem_convexHull'.mp hz
        obtain ⟨ c, hc_nonneg, hc_sum, hc_comb ⟩ : ∃ c : V → ℝ, (∀ v ∈ s, 0 ≤ c v) ∧ (∑ v ∈ s, c v = 1) ∧ (∑ v ∈ s, c v • v = x) := by
          rw [ openSegment_eq_image ] at hx;
          rcases hx with ⟨ θ, ⟨ hθ₀, hθ₁ ⟩, rfl ⟩;
          refine' ⟨ fun v => ( 1 - θ ) * a v + θ * b v, _, _, _ ⟩ <;> simp_all +decide [ Finset.sum_add_distrib, add_smul ];
          · exact fun v hv => add_nonneg ( mul_nonneg ( sub_nonneg.2 hθ₁.le ) ( ha_nonneg v hv ) ) ( mul_nonneg hθ₀.le ( hb_nonneg v hv ) );
          · simp +decide [ ← Finset.mul_sum _ _ _, ha_sum, hb_sum ];
          · simp +decide only [mul_smul, ← ha_comb, Finset.smul_sum, ← hb_comb];
        -- Since $x$ is a convex combination of $y$ and $z$, we have $x = t • y + (1 - t) • z$ for some $t \in (0, 1)$.
        obtain ⟨ t, ht₀, ht₁, ht₂ ⟩ : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ x = t • y + (1 - t) • z := by
          rcases hx with ⟨ u, v, hu, hv, huv, rfl ⟩;
          exact ⟨ u, hu, by linarith, by rw [ ← huv, add_sub_cancel_left ] ⟩;
        -- Substitute $y$ and $z$ into the equation $x = t • y + (1 - t) • z$ to get $x = t • (∑ v ∈ s, a v • v) + (1 - t) • (∑ v ∈ s, b v • v)$.
        have hx_sub : x = ∑ v ∈ s, (t * a v + (1 - t) * b v) • v := by
          simp +decide only [ht₂, ← ha_comb, Finset.smul_sum, smul_smul, ← hb_comb, add_smul,
                        Finset.sum_add_distrib];
        -- By `convex_combination_unique_at_vertex`, we have $t * a x + (1 - t) * b x = 1$.
        have h_coeff : t * a x + (1 - t) * b x = 1 := by
          have := convex_combination_unique_at_vertex hc ‹x ∈ s› ( fun v hv => add_nonneg ( mul_nonneg ht₀.le ( ha_nonneg v hv ) ) ( mul_nonneg ( sub_nonneg.2 ht₁.le ) ( hb_nonneg v hv ) ) ) ?_ hx_sub.symm;
          · exact this;
          · simp +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ha_sum, hb_sum ];
        -- Since $a x \leq 1$ and $b x \leq 1$, and $t * a x + (1 - t) * b x = 1$, we must have $a x = 1$ and $b x = 1$.
        have h_ax_bx : a x = 1 ∧ b x = 1 := by
          have h_ax_bx : a x ≤ 1 ∧ b x ≤ 1 := by
            exact ⟨ ha_sum ▸ Finset.single_le_sum ( fun v _ => ha_nonneg v ‹_› ) ‹_›, hb_sum ▸ Finset.single_le_sum ( fun v _ => hb_nonneg v ‹_› ) ‹_› ⟩;
          constructor <;> nlinarith only [ ht₀, ht₁, h_coeff, h_ax_bx ];
        -- Since $a x = 1$ and $b x = 1$, we have $a v = 0$ and $b v = 0$ for all $v \neq x$.
        have h_av_bv_zero : ∀ v ∈ s, v ≠ x → a v = 0 ∧ b v = 0 := by
          intro v hv hvx
          have h_av_zero : a v = 0 := by
            rw [ Finset.sum_eq_add_sum_diff_singleton x a (by intro hx; exact (hx ‹x ∈ s›).elim) ] at ha_sum;
            exact le_antisymm ( by linarith [ ha_nonneg v hv, Finset.single_le_sum ( fun v _ => ha_nonneg v ( Finset.mem_sdiff.mp ‹_› |>.1 ) ) ( Finset.mem_sdiff.mpr ⟨ hv, by simp [ hvx ] ⟩ : v ∈ s \ { x } ) ] ) ( ha_nonneg v hv )
          have h_bv_zero : b v = 0 := by
            rw [ Finset.sum_eq_add_sum_diff_singleton x b (by intro hx; exact (hx ‹x ∈ s›).elim) ] at hb_sum;
            exact le_antisymm ( by linarith [ hb_nonneg v hv, Finset.single_le_sum ( fun v _ => hb_nonneg v ( Finset.mem_sdiff.mp ‹_› |>.1 ) ) ( Finset.mem_sdiff.mpr ⟨ hv, by simpa using hvx ⟩ : v ∈ s \ { x } ) ] ) ( hb_nonneg v hv )
          exact ⟨h_av_zero, h_bv_zero⟩;
        rw [ ← ha_comb, Finset.sum_eq_single x ] <;> simp +contextual [ h_ax_bx, h_av_bv_zero ];
        tauto

/-
If a finite set of points is convex independent, then all points lie on the frontier of their convex hull.
-/
lemma convexIndependent_subset_frontier {s : Finset V}
    (hc : ConvexIndependent ℝ (Subtype.val : s → V)) :
    (s : Set V) ⊆ frontier (convexHull ℝ (s : Set V)) := by
      intro x hx;
      -- Since $x \in s$, we know that $x$ is an extreme point of the convex hull of $s$.
      have h_extreme : x ∈ Set.extremePoints ℝ (convexHull ℝ (s : Set V)) := by
        exact convexIndependent_implies_extremePoints hc hx
      -- Since $x$ is an extreme point of the convex hull of $s$, it cannot be in the interior of the convex hull of $s$.
      have h_not_interior : x ∉ interior (convexHull ℝ (s : Set V)) := by
        apply extremePoint_not_in_interior;
        · exact convex_convexHull ℝ _;
        · exact subset_convexHull ℝ _ hx;
        · exact h_extreme;
      exact ⟨ subset_closure ( subset_convexHull ℝ _ hx ), h_not_interior ⟩


lemma centroid_angle_injective_on_s {s : Finset V}
    (h_conv : ConvexIndependent ℝ (Subtype.val : s → V))
    (C : V) (hC_int : C ∈ interior (convexHull ℝ (s : Set V))) :
    Set.InjOn (centroid_angle C) s := by
  -- Let u, v ∈ s such that centroid_angle C u = centroid_angle C v.
  intro u hu v hv huv;
  -- Since to_complex is a linear equivalence, it preserves SameRay, so SameRay ℝ (u - C) (v - C).
  have h_same_ray : SameRay ℝ (u - C) (v - C) := by
    have h_same_ray : SameRay ℝ (to_complex_map (u - C)) (to_complex_map (v - C)) := by
       exact Complex.sameRay_of_arg_eq huv
    exact (SameRay.sameRay_map_iff to_complex_map).mp h_same_ray
  -- By convexIndependent_subset_frontier, s ⊆ frontier(convexHull s).
  have h_frontier : (s : Set V) ⊆ frontier (convexHull ℝ (s : Set V)) := by
    exact convexIndependent_subset_frontier h_conv
  apply_rules [ unique_ray_intersection_frontier ];
  · exact convex_convexHull ℝ _;
  · exact IsCompact.isClosed ( Set.Finite.isCompact_convexHull ℝ <| Finset.finite_toSet s )

lemma is_convex_polygon_rotate {A : ℕ → V} {n : ℕ} (h_convex : IsConvexPolygon A n) (k : ℕ) :
    IsConvexPolygon (fun i => A ((i + k) % n)) n := by
  let B := fun i => A ((i + k) % n)
  have hn3 := h_convex.1
  have hn_pos : 0 < n := by linarith
  have h_range : (Finset.range n).image B = (Finset.range n).image A := by
    ext x
    simp only [Finset.mem_image, Finset.mem_range, B]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨(j + k) % n, Nat.mod_lt _ hn_pos, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      let i_v := (j + (n - k % n)) % n
      use i_v
      constructor
      · exact Nat.mod_lt _ hn_pos
      · dsimp [i_v, B]
        apply congr_arg
        have h_m : j + (n - k % n) + k ≡ j [MOD n] := by
          have k_mod : k ≡ k % n [MOD n] := (Nat.mod_mod k n).symm
          have : j + (n - k % n) + k ≡ j + (n - k % n) + k % n [MOD n] := Nat.ModEq.add_left _ k_mod
          apply this.trans
          have : j + (n - k % n) + k % n = j + n := by
            rw [Nat.add_assoc, Nat.sub_add_cancel (Nat.le_of_lt (Nat.mod_lt k hn_pos))]
          rw [this, Nat.ModEq, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hj]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, h_m]
        exact Nat.mod_eq_of_lt hj
  constructor
  · exact hn3
  · constructor
    · intro i j hi hj hBij
      have h := h_convex.2.1 ((i + k) % n) ((j + k) % n) (Nat.mod_lt _ hn_pos) (Nat.mod_lt _ hn_pos) hBij
      -- Show i = j
      have : i = j := by
        have h_m : i + k ≡ j + k [MOD n] := h
        have : i ≡ j [MOD n] := Nat.ModEq.add_right_cancel' k h_m
        rw [Nat.ModEq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
        exact this
      exact this
    · constructor
      · -- Convex independent
        let f : Fin n ↪ Fin n := ⟨fun i => ⟨(i.val + k) % n, Nat.mod_lt _ hn_pos⟩, by
          intro i j h; simp [Fin.ext_iff] at h
          -- Show i = j
          have : i.val ≡ j.val [MOD n] := Nat.ModEq.add_right_cancel' k h
          rw [Nat.ModEq, Nat.mod_eq_of_lt i.is_lt, Nat.mod_eq_of_lt j.is_lt] at this
          exact Fin.ext this⟩
        have : (fun i : Fin n => B i) = (fun i : Fin n => A i) ∘ f := rfl
        rw [this]; apply ConvexIndependent.comp_embedding f h_convex.2.2.1
      · -- Cyclic frontier
        intro i
        let m : Fin n := i + ⟨k % n, Nat.mod_lt _ hn_pos⟩
        have h_Bi : B i = A m := by
          dsimp [B, m]; rw [Fin.val_add, Nat.add_mod_mod]
        have h_Bi1 : B (((i.val + 1) % n)) = A (((m.val + 1) % n)) := by
          dsimp [B, m]; rw [Fin.val_add, Nat.add_mod_mod]
          apply congr_arg; rw [Nat.add_mod, Nat.add_mod]; simp [Nat.add_assoc, Nat.add_comm]
        have h_range_v : (Finset.range n).image B = (Finset.range n).image A := h_range
        change segment ℝ (B i) (B ((i.val + 1) % n)) ⊆ frontier (convexHull ℝ (Finset.image B (Finset.range n) : Set V))
        rw [h_Bi, h_Bi1, h_range_v]
        exact h_convex.2.2.2 m

/--
Helper lemma: IsConvexPolygon only depends on the values of the vertices indices < n.
-/
lemma is_convex_polygon_congr {A B : ℕ → V} {n : ℕ}
    (h_eq : ∀ i < n, A i = B i) :
    IsConvexPolygon A n ↔ IsConvexPolygon B n := by
  have h_fin : (fun i : Fin n => A i) = (fun i : Fin n => B i) := by
    ext i; exact h_eq i i.2
  have h_img : (Finset.range n).image A = (Finset.range n).image B := by
    ext x; simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, (h_eq i hi).symm⟩
    · rintro ⟨i, hi, rfl⟩; use i, hi; rw [← h_eq i hi]
  unfold IsConvexPolygon
  apply and_congr_right -- Use the version that provides the hypothesis
  intro hn_ge_3 -- Now we have n >= 3
  apply and_congr
  · -- distinctness
    constructor
    · intro h i j hi hj heq
      rw [← h_eq i hi, ← h_eq j hj] at heq
      exact h i j hi hj heq
    · intro h i j hi hj heq
      rw [h_eq i hi, h_eq j hj] at heq
      exact h i j hi hj heq
  · apply and_congr
    · -- convex independence
      rw [h_fin]
    · -- frontier
      -- Rewrite the image set first
      rw [h_img]
      apply forall_congr'
      intro i
      -- Rewrite the segment endpoints
      -- We need n > 0 for mod_lt, which follows from n >= 3
      have n_pos : n > 0 := by omega
      have h1 : A i = B i := h_eq i i.2
      have h2 : A ((i + 1) % n) = B ((i + 1) % n) := h_eq _ (Nat.mod_lt _ n_pos)
      rw [h1, h2]

-- (proven by Aristotle)
lemma segment_frontier_transfer {s t : Finset V}
    (h_sub : s ⊆ t)
    {a b : V} (ha : a ∈ (s : Set V)) (hb : b ∈ (s : Set V))
    (h_seg_front_t : segment ℝ a b ⊆ frontier (convexHull ℝ (t : Set V))) :
    segment ℝ a b ⊆ frontier (convexHull ℝ (s : Set V)) := by
  simp_all +decide [ Set.subset_def, segment_eq_image ];
  intro x x_1 hx_nonneg hx_le_one hx_eq
  have hx_convex_s : x ∈ convexHull ℝ (s : Set V) := by
    rw [ convexHull_eq ];
    refine' ⟨ Fin 2, { 0, 1 }, fun i => if i = 0 then 1 - x_1 else x_1, fun i => if i = 0 then a else b, _, _, _, _ ⟩ <;> simp +decide [ *, Finset.centerMass ];
  refine' ⟨ subset_closure hx_convex_s, _ ⟩;
  intro hx_interior;
  have hx_interior_t : x ∈ interior (convexHull ℝ (t : Set V)) := by
    exact interior_mono ( convexHull_mono ( Finset.coe_subset.mpr h_sub ) ) hx_interior;
  exact h_seg_front_t x x_1 hx_nonneg hx_le_one hx_eq |>.2 hx_interior_t

/-
For any convex set s and a point x in its frontier, there exists a non-zero continuous linear functional f such that f(y) <= f(x) for all y in s.
(proven and stated by Aristotle)
-/
lemma exists_supporting_hyperplane_of_frontier {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {s : Set V} (hs : Convex ℝ s) {x : V} (hx : x ∈ frontier s) :
    ∃ f : V →L[ℝ] ℝ, f ≠ 0 ∧ ∀ y ∈ s, f y ≤ f x := by
      by_cases h_empty : interior s = ∅;
      · -- Since $s$ is convex and its interior is empty, $s$ must be contained in a proper affine subspace of $V$.
        obtain ⟨W, hW⟩ : ∃ W : Submodule ℝ V, W ≠ ⊤ ∧ s ⊆ W + {x} := by
          -- Since $s$ is convex and its interior is empty, $s$ must be contained in a proper affine subspace of $V$. Let $W$ be the affine hull of $s$.
          obtain ⟨W, hW⟩ : ∃ W : AffineSubspace ℝ V, W ≠ ⊤ ∧ s ⊆ W := by
            have h_affine_hull : affineSpan ℝ s ≠ ⊤ := by
              contrapose! h_empty;
              exact (Convex.interior_nonempty_iff_affineSpan_eq_top hs).mpr h_empty;
            exact ⟨ _, h_affine_hull, subset_spanPoints ℝ s ⟩;
          refine' ⟨ W.direction, _, _ ⟩;
          · cases W.eq_bot_or_nonempty <;> aesop;
          · intro y hy; have := hW.2 hy; simp_all +decide;
            convert AffineSubspace.vsub_mem_direction this ( show x ∈ W from _ ) using 1 ; simp +decide;
            · rw [ sub_eq_add_neg ];
            · exact closure_minimal hW.2 ( W.closed_of_finiteDimensional ) hx.1;
        -- Since $W$ is a proper subspace of $V$, there exists a non-zero continuous linear functional $f$ such that $f(y) = 0$ for all $y \in W$.
        obtain ⟨f, hf⟩ : ∃ f : V →L[ℝ] ℝ, f ≠ 0 ∧ ∀ y ∈ W, f y = 0 := by
          obtain ⟨y, hy⟩ : ∃ y : V, y ∉ W := by
            exact not_forall.mp fun h => hW.1 <| eq_top_iff.mpr fun y _ => h y;
          obtain ⟨f, hf⟩ : ∃ f : V →ₗ[ℝ] ℝ, f y ≠ 0 ∧ ∀ z ∈ W, f z = 0 := by
            exact Submodule.exists_le_ker_of_notMem hy;
          refine' ⟨ f.toContinuousLinearMap, _, _ ⟩ <;> aesop;
        refine' ⟨ f, hf.1, fun y hy => _ ⟩;
        have := hW.2 hy;
        rw [ Set.mem_add ] at this ; aesop;
      · -- By the geometric Hahn-Banach theorem, there exists a nonzero continuous linear functional $f$ such that $f(x) \geq f(y)$ for all $y \in \text{int}(s)$.
        obtain ⟨f, hf_ne_zero, hf⟩ : ∃ f : V →L[ℝ] ℝ, f ≠ 0 ∧ ∀ y ∈ interior s, f y ≤ f x := by
          have h_hahn_banach : ∃ f : V →L[ℝ] ℝ, f ≠ 0 ∧ (∀ y ∈ interior s, f y ≤ f x) := by
            have h_not_in_interior : x ∉ interior s := by
              exact fun h => hx.2 h
            have := @geometric_hahn_banach_open_point;
            obtain ⟨ f, hf ⟩ := this ( show Convex ℝ ( interior s ) from hs.interior ) ( isOpen_interior ) h_not_in_interior;
            refine' ⟨ f, _, fun y hy => le_of_lt ( hf y hy ) ⟩;
            exact fun h => h_not_in_interior <| by have := hf ( Classical.choose ( Set.nonempty_iff_ne_empty.2 h_empty ) ) ( Classical.choose_spec ( Set.nonempty_iff_ne_empty.2 h_empty ) ) ; simp_all +decide ;
          exact h_hahn_banach;
        -- Since $s$ is convex and $x \in \text{frontier}(s)$, for any $y \in s$, we have $y \in \overline{\text{int}(s)}$.
        have h_closure : ∀ y ∈ s, y ∈ closure (interior s) := by
          intro y hy
          have h_closure : ∀ z ∈ interior s, ∀ t ∈ Set.Ioo (0 : ℝ) 1, (1 - t) • y + t • z ∈ interior s := by
            intro z hz t ht;
            rw [ mem_interior_iff_mem_nhds, Metric.mem_nhds_iff ] at *;
            obtain ⟨ ε, ε_pos, hε ⟩ := hz;
            refine' ⟨ t * ε, mul_pos ht.1 ε_pos, fun w hw => _ ⟩;
            -- Since $w$ is in the ball around $(1 - t) • y + t • z$ with radius $t * ε$, we can write $w$ as $(1 - t) • y + t • z + v$ for some $v$ with $\|v\| < t * ε$.
            obtain ⟨ v, hv ⟩ : ∃ v : V, w = (1 - t) • y + t • z + v ∧ ‖v‖ < t * ε := by
              exact ⟨ w - ( ( 1 - t ) • y + t • z ), by simp +decide, by simpa [ dist_eq_norm ] using hw ⟩;
            -- Since $‖v‖ < t * ε$, we have $z + t⁻¹ • v ∈ Metric.ball z ε$.
            have h_ball : z + t⁻¹ • v ∈ Metric.ball z ε := by
              simp_all +decide [ norm_smul, abs_of_pos ht.1 ];
              rw [ inv_mul_lt_iff₀ ] <;> linarith;
            convert hs hy ( hε h_ball ) ( show 0 ≤ 1 - t by linarith [ ht.2 ] ) ( show 0 ≤ t by linarith [ ht.1 ] ) ( by linarith [ ht.1, ht.2 ] ) using 1 ; simp +decide [ hv.1, smul_smul, ht.1.ne'];
            rw [ add_assoc ];
          -- Since $y \in s$, we can find a sequence $\{z_n\}$ in $\text{int}(s)$ such that $z_n \to y$.
          obtain ⟨z, hz⟩ : ∃ z ∈ interior s, True := by
            exact Exists.elim ( Set.nonempty_iff_ne_empty.2 h_empty ) fun z hz => ⟨ z, hz, trivial ⟩;
          have h_seq : Filter.Tendsto (fun t : ℝ => (1 - t) • y + t • z) (nhdsWithin 0 (Set.Ioi 0)) (nhds y) := by
            exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by simp +decide ) );
          exact mem_closure_of_tendsto h_seq ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ) fun t ht => h_closure z hz.1 t ht );
        refine' ⟨ f, hf_ne_zero, fun y hy => _ ⟩;
        have := h_closure y hy;
        rw [ mem_closure_iff_seq_limit ] at this;
        exact le_of_tendsto_of_tendsto' ( f.continuous.continuousAt.tendsto.comp this.choose_spec.2 ) tendsto_const_nhds fun n => hf _ ( this.choose_spec.1 n )
-- (I have no idea what is happening here, but this fixes the error :-))  )
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V]
variable [Fact (Module.finrank ℝ V = 2)]
/--
If the segment [p, q] is on the frontier of the convex hull of S,
then there exists a supporting affine map f such that f vanishes on p and q,
and S lies in the non-positive half-space of f. (proven by Aristotle)
-/
lemma convex_chain_boundary_implies_support
    {S : Set V} {p q : V}
    (h_convex : Convex ℝ (convexHull ℝ S))
    (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q)
    (h_seg_frontier : segment ℝ p q ⊆ frontier (convexHull ℝ S)) :
    ∃ f : V →ᵃ[ℝ] ℝ, f.linear ≠ 0 ∧ f p = 0 ∧ f q = 0 ∧ ∀ x ∈ S, f x ≤ 0 := by
      obtain ⟨f, hf_linear, hf_pq⟩ : ∃ f : V →L[ℝ] ℝ, f ≠ 0 ∧ f p = f q ∧ f p ≥ f q ∧ ∀ x ∈ convexHull ℝ S, f x ≤ f p := by
        -- By `exists_supporting_hyperplane_of_frontier`, there exists a non-zero continuous linear functional $L$ such that $L(y) \le L(m)$ for all $y$ in the convex hull.
        obtain ⟨L, hL_ne_zero, hL_le⟩ : ∃ L : V →L[ℝ] ℝ, L ≠ 0 ∧ ∀ x ∈ convexHull ℝ S, L x ≤ L ((1 / 2 : ℝ) • (p + q)) := by
          have h_midpoint_frontier : (1 / 2 : ℝ) • (p + q) ∈ frontier (convexHull ℝ S) := by
            convert h_seg_frontier _;
            exact ⟨ 1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num ⟩;
          exact exists_supporting_hyperplane_of_frontier h_convex h_midpoint_frontier;
        refine' ⟨ L, hL_ne_zero, _, _, _ ⟩ <;> have := hL_le p ( subset_convexHull ℝ S hp ) <;> have := hL_le q ( subset_convexHull ℝ S hq ) <;> norm_num at *;
        · linarith;
        · linarith;
        · exact fun x hx => by linarith [ hL_le x hx ] ;
      refine' ⟨ AffineMap.mk ( fun x => f x - f p ) ( f.toAffineMap.linear ) _, _, _, _, _ ⟩ <;> simp_all +decide [ sub_eq_iff_eq_add ];
      · exact fun _ _ => by ring;
      · exact fun h => hf_linear <| ContinuousLinearMap.ext fun x => by simpa using congr_arg ( fun g => g x ) h;
      · exact fun x hx => hf_pq.1 ▸ hf_pq.2.2 x ( subset_convexHull ℝ S hx )

/-
If a segment [a, b] in the convex hull of S lies in a hyperplane {x | f x = 0} such that S lies in the half-space {x | f x ≤ 0} (where f is a non-zero affine map), then the segment is on the frontier of the convex hull.
(stated and proven by Aristotle)
-/
lemma segment_subset_frontier_of_supporting_hyperplane
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {S : Set V} {a b : V}
    (ha : a ∈ convexHull ℝ S) (hb : b ∈ convexHull ℝ S)
    (f : V →ᵃ[ℝ] ℝ) (hf_nonpos : ∀ x ∈ S, f x ≤ 0)
    (hfa : f a = 0) (hfb : f b = 0)
    (hf_ne_zero : f.linear ≠ 0) :
    segment ℝ a b ⊆ frontier (convexHull ℝ S) := by
      -- Since $f$ is affine and non-positive on $S$, the convex hull of $S$ is contained in the half-space $\{x \mid f(x) \leq 0\}$.
      have h_convex_hull_subset_halfspace : convexHull ℝ S ⊆ {x | f x ≤ 0} := by
        refine' convexHull_min _ _;
        · exact hf_nonpos;
        · intro x hx y hy a b ha hb hab;
          have := f.map_vadd ( a • x ) ( b • y ) ; simp_all +decide [ ← eq_sub_iff_add_eq' ] ;
          have := f.map_vadd 0 x; have := f.map_vadd 0 y; simp_all +decide [ add_comm ] ;
          have := f.map_vadd 0 ( a • x ) ; simp_all +decide [ add_comm ] ; nlinarith;
      -- Any point $x$ in the convex hull with $f(x) = 0$ lies on the boundary of the half-space.
      have h_boundary : ∀ x ∈ convexHull ℝ S, f x = 0 → x ∈ frontier (convexHull ℝ S) := by
        intro x hx hx'; rw [ frontier_eq_closure_inter_closure ] ; simp_all +decide [ Set.subset_def ] ;
        refine' ⟨ subset_closure hx, _ ⟩;
        intro hx''; obtain ⟨ ε, εpos, hε ⟩ := Metric.mem_nhds_iff.mp ( mem_interior_iff_mem_nhds.mp hx'' ) ; have := hε ( Metric.mem_ball_self εpos ) ; simp_all +decide;
        -- Since $f$ is non-zero, there exists a direction $v$ such that $f(x + tv) > 0$ for small $t > 0$.
        obtain ⟨v, hv⟩ : ∃ v : V, f.linear v > 0 := by
          contrapose! hf_ne_zero;
          exact LinearMap.ext fun x => le_antisymm ( hf_ne_zero x ) ( by simpa using hf_ne_zero ( -x ) );
        -- Choose $t > 0$ such that $t \|v\| < \epsilon$.
        obtain ⟨t, ht_pos, ht⟩ : ∃ t > 0, t * ‖v‖ < ε := by
          exact ⟨ ε / ( ‖v‖ + 1 ), div_pos εpos ( add_pos_of_nonneg_of_pos ( norm_nonneg v ) zero_lt_one ), by rw [ div_mul_eq_mul_div, div_lt_iff₀ ] <;> nlinarith [ norm_nonneg v ] ⟩;
        -- Since $f$ is affine, we have $f(x + tv) = f(x) + t f(v)$.
        have h_affine : f (x + t • v) = f x + t * f.linear v := by
          convert f.map_vadd x ( t • v ) using 1 ; simp +decide;
          · rw [ add_comm ];
          · simp +decide [ add_comm, map_smul ];
        exact absurd ( h_convex_hull_subset_halfspace ( x + t • v ) ( hε ( by simpa [ norm_smul, abs_of_pos ht_pos ] using ht ) ) ) ( by nlinarith );
      intro x hx;
      refine' h_boundary x _ _;
      · exact convex_convexHull ℝ S |> fun h => h.segment_subset ha hb hx;
      · rcases hx with ⟨ u, v, hu, hv, huv, rfl ⟩;
        convert f.map_vadd 0 ( u • a + v • b ) using 1 ; simp +decide
        have := f.map_vadd 0 a; have := f.map_vadd 0 b; simp_all +decide
        rw [ ← add_mul, huv, one_mul ]

-- proven by Aristotle
lemma affine_functional_through_two_points {p q : V} (hpq : p ≠ q)
    (hdim : ∃ (u v : V), LinearIndependent ℝ ![u, v]) :
    ∃ f : V →ᵃ[ℝ] ℝ, f.linear ≠ 0 ∧ f p = 0 ∧ f q = 0 := by
  revert hdim;
  intro h;
  -- Let $u$ be a vector such that $u$ is not in the span of $\{p-q\}$.
  obtain ⟨u, hu⟩ : ∃ u : V, u ∉ Submodule.span ℝ {p - q} := by
    contrapose! hpq;
    simp_all +decide [ Submodule.mem_span_singleton ];
    obtain ⟨ u, v, huv ⟩ := h;
    obtain ⟨ a, rfl ⟩ := hpq u; obtain ⟨ b, rfl ⟩ := hpq v; simp_all +decide [ linearIndependent_fin2 ] ;
    exact False.elim ( huv.2 ( a / b ) ( by rw [ smul_smul, div_mul_cancel₀ _ huv.1.1 ] ) );
  -- Let $f$ be a linear functional such that $f(u) \neq 0$ and $f(p - q) = 0$.
  obtain ⟨f, hf⟩ : ∃ f : V →ₗ[ℝ] ℝ, f u ≠ 0 ∧ f (p - q) = 0 := by
    have h_lin_ind : ∃ f : V →ₗ[ℝ] ℝ, f u ≠ 0 ∧ ∀ v ∈ Submodule.span ℝ {p - q}, f v = 0 := by
      exact Submodule.exists_le_ker_of_notMem hu;
    exact ⟨ h_lin_ind.choose, h_lin_ind.choose_spec.1, h_lin_ind.choose_spec.2 _ ( Submodule.mem_span_singleton_self _ ) ⟩;
  refine' ⟨ { toFun := fun x => f ( x - q ), linear := f, map_vadd' := _ }, _, _, _ ⟩ <;> simp_all +decide [ sub_eq_iff_eq_add ];
  · exact fun _ _ => by ring;
  · aesop;
  · simp_all +decide [ sub_eq_zero ]

-- Proven by Aristotle
lemma convex_independent_not_all_on_affine_line {n : ℕ} {A : Fin n → V}
    (hdim : Module.finrank ℝ V = 2)
    (hn : 3 ≤ n) (h_indep : ConvexIndependent ℝ A)
    (f : V →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) :
    ∃ i : Fin n, f (A i) ≠ 0 := by
  by_contra h_contra;
  -- Since $f(A_i) = 0$ for all $i$, all points $A_i$ lie on the affine hyperplane $H = \{x \mid f(x) = 0\}$.
  have h_hyperplane : ∀ i, A i ∈ {x | f x = 0} := by
    aesop;
  -- Since $V$ is 2-dimensional and $f$ is non-zero, $H$ is a 1-dimensional affine subspace (a line).
  have h_line : ∃ (p : V) (v : V), v ≠ 0 ∧ ∀ x, f x = 0 ↔ ∃ t : ℝ, x = p + t • v := by
    -- Since $f$ is non-zero, its kernel is a 1-dimensional subspace of $V$.
    have h_kernel_dim : Module.finrank ℝ (LinearMap.ker f.linear) = 1 := by
      have h_kernel_dim : Module.finrank ℝ (LinearMap.ker f.linear) + Module.finrank ℝ (LinearMap.range f.linear) = 2 := by
        rw [ ← hdim, add_comm ];
        convert LinearMap.finrank_range_add_finrank_ker f.linear;
      have h_range_dim : Module.finrank ℝ (LinearMap.range f.linear) = 1 := by
        exact le_antisymm ( le_trans ( Submodule.finrank_le _ ) ( by simp +decide ) ) ( Nat.pos_of_ne_zero fun h => hf <| LinearMap.range_eq_bot.mp <| Submodule.finrank_eq_zero.mp h );
      linarith;
    -- Since the kernel of $f$ is 1-dimensional, there exists a non-zero vector $v$ such that the kernel is spanned by $v$.
    obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 ∧ ∀ x, f.linear x = 0 ↔ ∃ t : ℝ, x = t • v := by
      obtain ⟨ v, hv ⟩ := finrank_eq_one_iff'.mp h_kernel_dim;
      refine' ⟨ v, _, _ ⟩ <;> simp_all +decide ;
      exact fun x => ⟨ fun hx => by obtain ⟨ t, ht ⟩ := hv.2 x hx; exact ⟨ t, by simpa [ Subtype.ext_iff ] using ht.symm ⟩, fun hx => by obtain ⟨ t, rfl ⟩ := hx; simp +decide ⟩;
    -- Since $f$ is non-zero, there exists a point $p$ such that $f(p) = 0$.
    obtain ⟨p, hp⟩ : ∃ p : V, f p = 0 := by
      exact ⟨ _, h_hyperplane ⟨ 0, by linarith ⟩ ⟩;
    use p, v;
    simp_all +decide;
    intro x; rw [ ← sub_eq_zero ] ; simp +decide;
    convert hv.2 ( x - p ) using 1 ; simp +decide ;
    · have := f.map_vadd p ( x - p ) ; aesop;
    · grind;
  obtain ⟨ p, v, hv, h ⟩ := h_line;
  -- Since $A$ is convexly independent, the points $A_i$ cannot all lie on a single line.
  have h_convex_indep : ¬∃ (t : Fin n → ℝ), (∀ i, A i = p + t i • v) ∧ (∃ i j k : Fin n, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ t i ≠ t j ∧ t i ≠ t k ∧ t j ≠ t k) := by
    rintro ⟨ t, ht, i, j, k, hij, hik, hjk, hti, htj, htk ⟩;
    -- Without loss of generality, assume $t_i < t_j < t_k$.
    wlog h_wlog : t i < t j ∧ t j < t k generalizing i j k;
    · cases lt_or_gt_of_ne hti <;> cases lt_or_gt_of_ne htj <;> cases lt_or_gt_of_ne htk <;> simp +decide [ * ] at h_wlog ⊢;
      grind;
      · grind;
      · exact this j i k ( by tauto ) ( by tauto ) ( by tauto ) ( by tauto ) ( by tauto ) ( by tauto ) ⟨ by linarith, by linarith ⟩;
      · linarith;
      · exact this j k i ( by tauto ) ( by tauto ) ( by tauto ) ( by tauto ) ( by tauto ) ( by tauto ) ⟨ by linarith, by linarith ⟩;
      · grind;
    · -- Since $t_i < t_j < t_k$, we have $A_j = \frac{t_k - t_j}{t_k - t_i} A_i + \frac{t_j - t_i}{t_k - t_i} A_k$.
      have h_comb : A j = ((t k - t j) / (t k - t i)) • A i + ((t j - t i) / (t k - t i)) • A k := by
        simp +decide [ ht, smul_add, smul_smul, div_eq_inv_mul ];
        rw [ show ( t k - t i ) ⁻¹ * ( t k - t j ) = 1 - ( t k - t i ) ⁻¹ * ( t j - t i ) by nlinarith [ inv_mul_cancel₀ ( by linarith : ( t k - t i ) ≠ 0 ) ] ] ; simp +decide [ sub_smul ] ; abel_nf;
        simp +decide [ ← add_smul ] ; ring_nf;
        exact congr_arg₂ _ ( by nlinarith [ inv_mul_cancel_left₀ ( by linarith : ( t k - t i ) ≠ 0 ) ( t i ), inv_mul_cancel_left₀ ( by linarith : ( t k - t i ) ≠ 0 ) ( t j ) ] ) rfl;
      have := h_indep;
      rw [ convexIndependent_iff_notMem_convexHull_diff ] at this;
      specialize this j { i, k };
      refine' this _;
      rw [ convexHull_eq ];
      refine' ⟨ _, { i, k }, fun x => if x = i then ( t k - t j ) / ( t k - t i ) else ( t j - t i ) / ( t k - t i ), fun x => if x = i then A i else A k, _, _, _, _ ⟩ <;> simp +decide [ *, Finset.centerMass ];
      · exact ⟨ div_nonneg ( by linarith ) ( by linarith ), by rw [ if_neg ( Ne.symm hik ) ] ; exact div_nonneg ( by linarith ) ( by linarith ) ⟩;
      · rw [ if_neg ( Ne.symm hik ), ← add_div, div_eq_iff ] <;> linarith;
      · grind;
      · split_ifs <;> simp_all +decide [← smul_assoc ];
        rw [ show ( t k - t j ) / ( t k - t i ) + ( t j - t i ) / ( t k - t i ) = 1 by rw [ ← add_div, div_eq_iff ] <;> linarith ] ; norm_num;
  -- Since $A$ is convexly independent, the points $A_i$ cannot all lie on a single line, contradicting our assumption.
  obtain ⟨t, ht⟩ : ∃ t : Fin n → ℝ, ∀ i, A i = p + t i • v := by
    exact ⟨ fun i => Classical.choose ( h _ |>.1 ( h_hyperplane i ) ), fun i => Classical.choose_spec ( h _ |>.1 ( h_hyperplane i ) ) ⟩;
  refine' h_convex_indep ⟨ t, ht, _ ⟩;
  -- Since $A$ is convexly independent, the points $A_i$ cannot all lie on a single line, contradicting our assumption that $t_i$ are distinct.
  have h_distinct : Function.Injective t := by
    intro i j hij;
    have := h_indep.injective;
          exact this ( by simp +decide [ ht, hij ] );
  exact ⟨ ⟨ 0, by linarith ⟩, ⟨ 1, by linarith ⟩, ⟨ 2, by linarith ⟩, by norm_num, by norm_num, by norm_num, h_distinct.ne ( by norm_num ), h_distinct.ne ( by norm_num ), h_distinct.ne ( by norm_num ) ⟩

lemma convex_hull_line_intersection_of_two_vertices {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Fact (Module.finrank ℝ V = 2)]
    {n : ℕ} [NeZero n] {A : Fin n → V}
    (hn : 3 ≤ n)
    (h_indep : ConvexIndependent ℝ A)
    (f : V →ᵃ[ℝ] ℝ)
    (h_f_zero : ∀ i : Fin n, f (A i) = 0 ↔ i = 0 ∨ i = ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩)
    (z : V)
    (hz_hull : z ∈ convexHull ℝ (range A))
    (hz_f : f z = 0) :
    z ∈ segment ℝ (A 0) (A ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩) := by
  let A0 := A 0
  let An := A ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩

  -- Step 1: f is not the zero map
  have hf_nz : f.linear ≠ 0 := by
    intro h_lin
    have h_const : ∀ x y, f x = f y := by
      intro x y; rw [← vsub_eq_zero_iff_eq, ← f.linearMap_vsub, h_lin, LinearMap.zero_apply]
    have hf1 : f (A ⟨1, by linarith⟩) = 0 := by
      rw [h_const (A ⟨1, by linarith⟩) (A 0), (h_f_zero 0).mpr (Or.inl rfl)]
    have h1 := (h_f_zero ⟨1, by linarith⟩).mp hf1
    rcases h1 with h1_zero | h1_last
    · simp at h1_zero
    · simp at h1_last; omega

  -- Step 2: z is collinear with A0 and An (lies on the kernel line)
  have h_collinear : z ∈ line[ℝ, A0, An] := by
    -- Define the indices once to avoid linarith issues in nested tactics
    let i0 : Fin n := 0
    let in1 : Fin n := ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩
    -- In 2D, the zero set of a non-trivial affine map is a line
    have h_dim : Module.finrank ℝ (LinearMap.ker f.linear) = 1 := by
      have h1 := LinearMap.finrank_range_add_finrank_ker f.linear
      rw [Fact.out (p := Module.finrank ℝ V = 2)] at h1
      have h_range_dim : Module.finrank ℝ (LinearMap.range f.linear) = 1 := by
        have h2 : Module.finrank ℝ (LinearMap.range f.linear) ≤ 1 := by
          have h_sub := Submodule.finrank_le (LinearMap.range f.linear)
          rw [Module.finrank_self ℝ] at h_sub
          exact h_sub
        refine (Nat.le_one_iff_eq_zero_or_eq_one.mp h2).resolve_left ?_
        intro h_zero; exact hf_nz (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h_zero))
      rw [h_range_dim] at h1; omega
    -- Point A0 and An are distinct
    have h_diff : A0 ≠ An := by
      intro h; have heq := h_indep.injective h
      simp at heq; omega
    -- The vectors spanning the zero set
    let v := An -ᵥ A0
    have hv_nz : v ≠ 0 := by rwa [vsub_ne_zero, ne_comm]
    have hv_ker : v ∈ LinearMap.ker f.linear := by
      rw [LinearMap.mem_ker, f.linearMap_vsub, vsub_eq_sub]
      simp [A0, An, i0, in1, (h_f_zero i0).mpr (Or.inl rfl), (h_f_zero in1).mpr (Or.inr rfl)]
    -- ker f is exactly Span {v}
    have h_ker_span : LinearMap.ker f.linear = Submodule.span ℝ {v} := by
      refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
      · rw [Submodule.span_le]; simp [hv_ker]
      · rw [h_dim, finrank_span_singleton hv_nz]
    -- z - A0 is in ker f
    have h_z_vsub : z -ᵥ A0 ∈ LinearMap.ker f.linear := by
      rw [LinearMap.mem_ker, f.linearMap_vsub, vsub_eq_sub]
      simp [A0, i0, hz_f, (h_f_zero i0).mpr (Or.inl rfl)]
    -- z is in affine span of {A0, An}
    rw [mem_affineSpan_iff_exists]
    use A0, Set.mem_insert _ _
    use z -ᵥ A0
    constructor
    -- (Project Numina's Lean Agent web demo fixed this itsy bitsy rw (when my Flash quota was gone))
    · rw [vectorSpan_pair, ← neg_vsub_eq_vsub_rev An A0, ← Set.neg_singleton, Submodule.span_neg, ← h_ker_span]
      exact h_z_vsub
    · simp

  -- Step 3: Any point in the hull that is collinear with two vertices must be in the segment between them
  -- This relies on A0 and An being extreme points of the convex hull.
  have h_z_mem_seg : z ∈ segment ℝ A0 An := by
    -- Vertices of a convex independent set are extreme points of their convex hull
    let s : Finset V := Finset.image A Finset.univ
    have h_range_eq : range A = (s : Set V) := by
      -- proven by Numina
      simp only [s, Fintype.coe_image_univ]
    have h_s_indep : ConvexIndependent ℝ (Subtype.val : s → V) := by
      -- proven by Numina
      have : ConvexIndependent ℝ (Subtype.val : range A → V) := h_indep.range
      rwa [h_range_eq] at this

    have h_extreme0 : A0 ∈ (convexHull ℝ (range A)).extremePoints ℝ := by
      rw [h_range_eq]
      apply convexIndependent_implies_extremePoints h_s_indep
      simp [s, A0]
    have h_extremeN : An ∈ (convexHull ℝ (range A)).extremePoints ℝ := by
      rw [h_range_eq]
      apply convexIndependent_implies_extremePoints h_s_indep
      simp [s, An]

    -- If z were outside the segment on the line, one of the extreme points would lie strictly between two hull points
    by_contra h_not_seg
    -- proven by Numina!
    have h_outside : A0 ∈ openSegment ℝ z An ∨ An ∈ openSegment ℝ A0 z := by
      have h_collinear_set : Collinear ℝ ({A0, z, An} : Set V) := by
        convert collinear_insert_of_mem_affineSpan_pair h_collinear using 1
        ext x
        simp [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      have h_wbtw := h_collinear_set.wbtw_or_wbtw_or_wbtw
      rw [mem_segment_iff_wbtw] at h_not_seg
      rcases h_wbtw with h1 | h2 | h3
      · -- A0 is weakly between z and An: Wbtw ℝ A0 z An
        exact absurd h1 h_not_seg
      · -- z is weakly between An and A0: Wbtw ℝ z An A0
        -- This is equivalent to: Wbtw ℝ A0 An z
        rw [wbtw_comm] at h2
        -- Now h2 : Wbtw ℝ A0 An z, meaning An is between A0 and z
        -- Need to show An is strictly between (i.e., An ≠ A0 and An ≠ z)
        right
        -- An is in the open segment between A0 and z
        apply mem_openSegment_of_ne_left_right
        · -- A0 ≠ An
          intro h; have heq := h_indep.injective h
          simp at heq; omega
        · -- z ≠ An
          intro h_eq
          rw [← h_eq] at h_not_seg
          simp at h_not_seg
        · -- An is in the closed segment [A0, z]
          rwa [mem_segment_iff_wbtw]
      · -- An is weakly between A0 and z: Wbtw ℝ An A0 z
        -- By commutativity: Wbtw ℝ z A0 An
        rw [wbtw_comm] at h3
        -- Now h3 : Wbtw ℝ z A0 An, meaning A0 is between z and An
        left
        -- A0 is in the open segment between z and An
        apply mem_openSegment_of_ne_left_right
        · -- z ≠ A0
          intro h_eq
          rw [h_eq] at h_not_seg
          simp at h_not_seg
        · -- An ≠ A0
          intro h; have heq := h_indep.injective h
          simp at heq; omega
        · -- A0 is in the closed segment [z, An]
          rwa [mem_segment_iff_wbtw]

    -- This contradicts the definition of extreme points
    rcases h_outside with h_case0 | h_caseN
    · -- A0 in openSegment z An contradicts A0 being an extreme point (Proven by Numina)
      have : z ∈ convexHull ℝ (range A) := hz_hull
      have : An ∈ convexHull ℝ (range A) := subset_convexHull ℝ (range A) (mem_range_self _)
      have h_contra := h_extreme0.2 ‹z ∈ convexHull ℝ (range A)› ‹An ∈ convexHull ℝ (range A)› h_case0
      have h_eq : z = A0 := h_contra
      rw [h_eq] at h_case0
      have h_eq_An : A0 = An := left_mem_openSegment_iff.mp h_case0
      have : (0 : Fin n) = (⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩ : Fin n) := by
        exact h_indep.injective h_eq_An
      simp at this
      omega
    · -- An in openSegment A0 z contradicts An being an extreme point (Proven by Numina)
      have : A0 ∈ convexHull ℝ (range A) := subset_convexHull ℝ (range A) (mem_range_self _)
      have : z ∈ convexHull ℝ (range A) := hz_hull
      have h_contra := h_extremeN.2 ‹A0 ∈ convexHull ℝ (range A)› this h_caseN
      have h_eq : A0 = An := h_contra
      have : (0 : Fin n) = (⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩ : Fin n) := by
        exact h_indep.injective h_eq
      simp at this
      omega

  exact h_z_mem_seg

lemma chain_vertices_independent_side_logic {n : ℕ} [NeZero n] {A : Fin n → V}
    (hn : 3 ≤ n) (h_indep : ConvexIndependent ℝ A)
    (h_chain : ∀ i : Fin n, i ≠ ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩ →
      segment ℝ (A i) (A (i + 1)) ⊆ frontier (convexHull ℝ (range A)))
    (f' g : V →ᵃ[ℝ] ℝ) (hf'_lin_nz : f'.linear ≠ 0)
    (hf'_zero : f' (A 0) = 0) (hf'_last : f' (A ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩) = 0)
    (hg_zero : g (A 0) = 0) (hg_le : ∀ x ∈ range A, g x ≤ 0)
    (h_ind_fg : LinearIndependent ℝ ![f'.linear, g.linear])
    {k : Fin n} (hf'_k_neg : f' (A k) < 0) :
    ∀ i : Fin n, f' (A i) ≤ 0 := by
  -- 1. Setup coordinate system (f', g).
  -- Since f'.linear and g.linear are independent in a 2D space, they form a basis of the dual space.
  -- We can transform our problem to R2: x -> (f' x, g x).
  -- ### Step 1: Setup Coordinate System
  let coord : V → ℝ × ℝ := fun v => (f' v, g v)
  have h_coord_inj : Function.Injective coord := by
    intro u v h
    simp only [coord, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h_diff : u -ᵥ v = 0 := by
      let Φ : Submodule ℝ (Module.Dual ℝ V) := Submodule.span ℝ (Set.range ![f'.linear, g.linear])
      have h_top : Φ = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [Subspace.dual_finrank_eq, (Fact.out : Module.finrank ℝ V = 2)]
        rw [finrank_span_eq_card h_ind_fg]
        simp
      have h_ker : Φ.dualCoannihilator = ⊥ := by
        rw [h_top, Submodule.dualCoannihilator_top]
      have h_mem : u -ᵥ v ∈ Φ.dualCoannihilator := by
        rw [Submodule.mem_dualCoannihilator]
        intro φ hφ
        induction hφ using Submodule.span_induction with
        | mem ψ hψ =>
          obtain ⟨i, rfl⟩ := hψ
          fin_cases i
          · change f'.linear (u -ᵥ v) = 0
            rw [f'.linearMap_vsub, h1, vsub_self]
          · change g.linear (u -ᵥ v) = 0
            rw [g.linearMap_vsub, h2, vsub_self]
        | zero => simp
        | add ψ₁ ψ₂ hψ₁ hψ₂ ih₁ ih₂ => rw [LinearMap.add_apply, ih₁, ih₂, add_zero]
        | smul r ψ hψ ih => rw [LinearMap.smul_apply, ih, smul_zero]
      rwa [h_ker, Submodule.mem_bot] at h_mem
    exact vsub_eq_zero_iff_eq.mp h_diff
  -- ### Step 2: Sign Permanence on the Frontier Chain (Part 1: Root Exclusion)
  have h_f_zero_idx : ∀ i : Fin n, f' (A i) = 0 ↔ i = 0 ∨ i = ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩ := by
    intro i
    constructor
    · intro hi
      by_contra! h_ne
      let sub_idx : Fin 3 → Fin n := ![0, i, ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩]
      have h_emb : Function.Injective sub_idx := by
        intro a b h_eq
        apply Fin.ext
        fin_cases a <;> fin_cases b
        · rfl
        · have : 0 = i.val := by simpa [sub_idx] using congr_arg Fin.val h_eq
          exact (h_ne.1 (Fin.ext this.symm)).elim
        · have : 0 = n - 1 := by simpa [sub_idx] using congr_arg Fin.val h_eq
          omega
        · have : i.val = 0 := by simpa [sub_idx] using congr_arg Fin.val h_eq
          exact (h_ne.1 (Fin.ext this)).elim
        · rfl
        · have : i.val = n - 1 := by simpa [sub_idx] using congr_arg Fin.val h_eq
          exact (h_ne.2 (Fin.ext this)).elim
        · have : n - 1 = 0 := by simpa [sub_idx] using congr_arg Fin.val h_eq
          omega
        · have : n - 1 = i.val := by simpa [sub_idx] using congr_arg Fin.val h_eq
          exact (h_ne.2 (Fin.ext this.symm)).elim
        · rfl
      let subA := A ∘ sub_idx
      have h_sub_indep : ConvexIndependent ℝ subA := h_indep.comp_embedding ⟨sub_idx, h_emb⟩
      obtain ⟨j, hj⟩ := convex_independent_not_all_on_affine_line (Fact.out : Module.finrank ℝ V = 2) (by norm_num) h_sub_indep f' hf'_lin_nz
      fin_cases j <;> simp [subA, sub_idx] at hj
      · exact hj hf'_zero
      · exact hj hi
      · exact hj hf'_last
    · rintro (rfl | rfl) <;> assumption
  -- ### Step 2: Sign Permanence on the Frontier Chain (Part 2: Contradiction via Separation)
  have h_f_val : ∀ i : Fin n, f' (A i) ≤ 0 := by
    intro i
    -- ### Step 3: Contradiction via Separation
    by_contra! h_pos_val
    have h_ik_cases : i.val < k.val ∨ k.val < i.val := by
      have : i ≠ k := by intro h; rw [h] at h_pos_val; linarith
      exact Nat.lt_or_gt.mp (Fin.val_ne_iff.mpr this)
    rcases h_ik_cases with h_ik | h_ki
    · -- Case i < k. Search for crossing in [i, k].
      let S : Finset (Fin n) := Finset.univ.filter (fun j => i.val ≤ j.val ∧ j.val < k.val ∧ f' (A j) > 0)
      have hS_nonempty : S.Nonempty := by
        use i; simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨le_refl _, h_ik, h_pos_val⟩
      let m := S.max' hS_nonempty
      rcases Finset.mem_filter.mp (S.max'_mem hS_nonempty) with ⟨_, h_im, h_mk, h_m_pos⟩
      have h_m_next_lt : m.val + 1 < n := by linarith [h_mk, k.is_lt]
      let m_next : Fin n := ⟨m.val + 1, h_m_next_lt⟩
      have hm_next_le : f' (A m_next) ≤ 0 := by
        by_contra! h_pos_next
        have h_in : m_next ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨by simp [m_next]; omega, ?_, h_pos_next⟩
          have : m_next ≠ k := by
            intro h0; rw [h0] at h_pos_next
            linarith [hf'_k_neg]
          exact (Fin.val_ne_iff.mpr this).lt_of_le (by simp [m_next]; omega)
        have h_lt : m.val < m_next.val := by simp [m_next]
        exact (Fin.le_def.mp (S.le_max' m_next h_in)).not_gt h_lt
      have h_next_idx_nz : m_next ≠ 0 ∧ m_next ≠ ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩ := by
        constructor
        · intro h; have := Fin.ext_iff.mp h; simp [m_next] at this
        · intro h; have := Fin.ext_iff.mp h; simp [m_next] at this
          have h_k_last : k ≠ ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩ := by
            intro h_last; rw [h_last] at hf'_k_neg; linarith [hf'_last]
          have : k.val < n - 1 := lt_of_le_of_ne (by omega) (Fin.ext_iff.mpr.mt h_k_last)
          omega
      have h_next_neg : f' (A m_next) < 0 := by
        have h_nz : f' (A m_next) ≠ 0 := by
          intro h0
          have h_m_next := (h_f_zero_idx m_next).mp h0
          exact (not_or.mpr h_next_idx_nz) h_m_next
        exact lt_of_le_of_ne hm_next_le h_nz
      let a := f' (A m)
      let b := f' (A m_next)
      let r := a / (a - b)
      have hab : a - b ≠ 0 := by linarith
      let z : V := (1 - r) • A m + r • A m_next
      have hz_f : f' z = 0 := by
        have : z = r • (A m_next -ᵥ A m) +ᵥ A m := by
          unfold z; simp [vadd_eq_add, vsub_eq_sub, smul_sub, sub_smul, one_smul]; abel
        rw [this, f'.map_vadd, f'.linear.map_smul, f'.linearMap_vsub]
        simp [vsub_eq_sub, vadd_eq_add, smul_eq_mul, r]
        field_simp [hab]
        simp [a, b]
        ring
      have hz_seg : z ∈ openSegment ℝ (A m) (A m_next) := by
        rw [openSegment_eq_image]
        refine ⟨r, ⟨?_, ?_⟩, ?_⟩
        · unfold r; apply div_pos h_m_pos; linarith
        · unfold r; apply (div_lt_one (by linarith)).mpr; linarith
        · unfold z; simp [sub_smul, one_smul]
      -- ### Step 4: Formalize Collinearity/Convexity Contradiction
      if hm0 : m = 0 then
        have h_z_val : f' z = r * f' (A m_next) := by
          have : z = r • (A m_next -ᵥ A 0) +ᵥ A 0 := by
            unfold z; rw [hm0]; simp [vadd_eq_add, vsub_eq_sub, smul_sub, sub_smul, one_smul]; abel
          rw [this, f'.map_vadd, f'.linear.map_smul, f'.linearMap_vsub, hf'_zero]
          simp [vadd_eq_add, vsub_eq_sub]
        have hr0 : 0 < r := by
          simp [r, a, b]
          apply div_pos h_m_pos
          linarith [h_m_pos, h_next_neg]
        have h_z_neg : f' z < 0 := by
          rw [h_z_val]
          exact mul_neg_of_pos_of_neg hr0 h_next_neg
        linarith [hz_f, h_z_neg]
      else
        let sub_idx : Fin 4 → Fin n := ![m, m_next, 0, ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩]
        have h_sub_inj : Function.Injective sub_idx := by
          intro a_idx b_idx h_eq
          have h_m_nz_both : m ≠ 0 ∧ m ≠ ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩ := by
            have h_fm_nz : f' (A m) ≠ 0 := h_m_pos.ne.symm
            simp [h_f_zero_idx] at h_fm_nz
            exact h_fm_nz
          fin_cases a_idx <;> fin_cases b_idx <;> try rfl
          · exfalso; have := Fin.ext_iff.mp h_eq; simp [sub_idx, m_next] at this
          · exfalso; simp [sub_idx] at h_eq; exact h_m_nz_both.left h_eq
          · exfalso; simp [sub_idx] at h_eq; exact h_m_nz_both.right h_eq
          · exfalso; have := Fin.ext_iff.mp h_eq; simp [sub_idx, m_next] at this
          · exfalso; simp [sub_idx] at h_eq; exact h_next_idx_nz.left h_eq
          · exfalso; simp [sub_idx] at h_eq; exact h_next_idx_nz.right h_eq
          · exfalso; simp [sub_idx] at h_eq; exact h_m_nz_both.left h_eq.symm
          · exfalso; simp [sub_idx] at h_eq; exact h_next_idx_nz.left h_eq.symm
          · exfalso; have := Fin.ext_iff.mp h_eq; dsimp [sub_idx] at this; omega
          · exfalso; simp [sub_idx] at h_eq; exact h_m_nz_both.right h_eq.symm
          · exfalso; simp [sub_idx] at h_eq; exact h_next_idx_nz.right h_eq.symm
          · exfalso; have := Fin.ext_iff.mp h_eq; dsimp [sub_idx] at this; omega
        let pts4 := A ∘ sub_idx
        have h_sub_indep : ConvexIndependent ℝ pts4 := h_indep.comp_embedding ⟨sub_idx, h_sub_inj⟩
        have hz_chord : z ∈ segment ℝ (A 0) (A ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩) := by
          apply convex_hull_line_intersection_of_two_vertices hn h_indep f' h_f_zero_idx z
          · have h_seg : z ∈ segment ℝ (A m) (A m_next) := openSegment_subset_segment ℝ (A m) (A m_next) hz_seg
            exact (convex_convexHull ℝ (range A)).segment_subset (subset_convexHull ℝ (range A) (mem_range_self m)) (subset_convexHull ℝ (range A) (mem_range_self m_next)) h_seg
          · exact hz_f
        have h_z_int : z ∈ interior (convexHull ℝ (range A)) := by
          have h_disj : ({0, 1} : Set (Fin 4)) ∩ {2, 3} = ∅ := by
            ext x; fin_cases x <;> simp
          have h_z_int_sub : z ∈ interior (convexHull ℝ (range pts4)) := by
            apply mem_interior_of_convexIndependent_inter_segments h_sub_indep h_disj z
            · exact openSegment_subset_segment ℝ (A m) (A m_next) hz_seg
            · exact hz_chord
          apply interior_mono (convexHull_mono (range_comp_subset_range sub_idx A)) h_z_int_sub
        have h_z_front : z ∈ frontier (convexHull ℝ (range A)) := by
          have h_m_nz : m ≠ ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩ := by
            intro h; simp [h, m] at h_m_pos; linarith [hf'_last]
          have : segment ℝ (A m) (A (m + 1 : Fin n)) ⊆ frontier (convexHull ℝ (range A)) := h_chain m h_m_nz
          have h_m_next : (m + 1 : Fin n) = m_next := by
             apply Fin.ext; simp [m_next, Fin.val_add]; rw [Nat.mod_eq_of_lt h_m_next_lt]
          rw [h_m_next] at this
          exact this (openSegment_subset_segment ℝ (A m) (A m_next) hz_seg)
        have h_disj : Disjoint (interior (convexHull ℝ (range A))) (frontier (convexHull ℝ (range A))) := disjoint_interior_frontier
        exact (Set.disjoint_left.mp h_disj h_z_int) h_z_front
    · -- Case k < i. Search for crossing in [k, i].
      let S : Finset (Fin n) := Finset.univ.filter (fun j => k.val ≤ j.val ∧ j.val < i.val ∧ f' (A j) < 0)
      have hS_nonempty : S.Nonempty := by
        use k; simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨le_refl _, h_ki, hf'_k_neg⟩
      let m := S.max' hS_nonempty
      rcases Finset.mem_filter.mp (S.max'_mem hS_nonempty) with ⟨_, h_km, h_mi, h_m_neg⟩
      have h_m_next_lt : m.val + 1 < n := by linarith [h_mi, i.is_lt]
      let m_next : Fin n := ⟨m.val + 1, h_m_next_lt⟩
      have hm_next_ge : f' (A m_next) ≥ 0 := by
        by_contra! h_neg_next
        have h_in : m_next ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨by simp [m_next]; omega, ?_, h_neg_next⟩
          have : m_next ≠ i := by
            intro h0; rw [h0] at h_neg_next
            linarith [h_pos_val]
          exact (Fin.val_ne_iff.mpr this).lt_of_le (by simp [m_next]; omega)
        have h_lt : m.val < m_next.val := by simp [m_next]
        exact (Fin.le_def.mp (S.le_max' m_next h_in)).not_gt h_lt
      have h_next_idx_nz : m_next ≠ 0 ∧ m_next ≠ ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩ := by
        constructor
        · intro h; have := Fin.ext_iff.mp h; simp [m_next] at this
        · intro h; have := Fin.ext_iff.mp h; simp [m_next] at this
          have h_i_last : i ≠ ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩ := by
            intro h_last; rw [h_last] at h_pos_val; linarith [hf'_last]
          have : i.val < n - 1 := lt_of_le_of_ne (by omega) (Fin.ext_iff.mpr.mt h_i_last)
          omega
      have h_next_pos : f' (A m_next) > 0 := by
        have h_nz : f' (A m_next) ≠ 0 := by
          intro h0
          have h_m_next := (h_f_zero_idx m_next).mp h0
          exact (not_or.mpr h_next_idx_nz) h_m_next
        exact lt_of_le_of_ne hm_next_ge h_nz.symm
      let a := f' (A m)
      let b := f' (A m_next)
      let r := a / (a - b)
      have hab : a - b ≠ 0 := by linarith
      let z : V := (1 - r) • A m + r • A m_next
      have hz_f : f' z = 0 := by
        have : z = r • (A m_next -ᵥ A m) +ᵥ A m := by
          unfold z; simp [vadd_eq_add, vsub_eq_sub, smul_sub, sub_smul, one_smul]; abel
        rw [this, f'.map_vadd, f'.linear.map_smul, f'.linearMap_vsub]
        simp [vsub_eq_sub, vadd_eq_add, smul_eq_mul, r]
        field_simp [hab]
        simp [a, b]
        ring
      have hz_seg : z ∈ openSegment ℝ (A m) (A m_next) := by
        rw [openSegment_eq_image]
        refine ⟨r, ⟨?_, ?_⟩, ?_⟩
        · unfold r; apply div_pos_of_neg_of_neg h_m_neg; linarith [h_m_neg, h_next_pos]
        · unfold r; rw [div_lt_one_of_neg (by linarith [h_m_neg, h_next_pos])]; linarith [h_m_neg, h_next_pos]
        · unfold z; simp [sub_smul, one_smul]
      let sub_idx : Fin 4 → Fin n := ![m, m_next, 0, ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩]
      have h_sub_inj : Function.Injective sub_idx := by
        intro a_idx b_idx h_eq
        have h_m_nz_both : m ≠ 0 ∧ m ≠ ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩ := by
          have h_fm_nz : f' (A m) ≠ 0 := h_m_neg.ne
          simp [h_f_zero_idx] at h_fm_nz
          exact h_fm_nz
        fin_cases a_idx <;> fin_cases b_idx <;> try rfl
        · exfalso; have := Fin.ext_iff.mp h_eq; simp [sub_idx, m_next] at this
        · exfalso; simp [sub_idx] at h_eq; exact h_m_nz_both.left h_eq
        · exfalso; simp [sub_idx] at h_eq; exact h_m_nz_both.right h_eq
        · exfalso; have := Fin.ext_iff.mp h_eq; simp [sub_idx, m_next] at this
        · exfalso; simp [sub_idx] at h_eq; exact h_next_idx_nz.left h_eq
        · exfalso; simp [sub_idx] at h_eq; exact h_next_idx_nz.right h_eq
        · exfalso; simp [sub_idx] at h_eq; exact h_m_nz_both.left h_eq.symm
        · exfalso; simp [sub_idx] at h_eq; exact h_next_idx_nz.left h_eq.symm
        · exfalso; have := Fin.ext_iff.mp h_eq; dsimp [sub_idx] at this; omega
        · exfalso; simp [sub_idx] at h_eq; exact h_m_nz_both.right h_eq.symm
        · exfalso; simp [sub_idx] at h_eq; exact h_next_idx_nz.right h_eq.symm
        · exfalso; have := Fin.ext_iff.mp h_eq; dsimp [sub_idx] at this; omega
      let pts4 := A ∘ sub_idx
      have h_sub_indep : ConvexIndependent ℝ pts4 := h_indep.comp_embedding ⟨sub_idx, h_sub_inj⟩
      have hz_chord : z ∈ segment ℝ (A 0) (A ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩) := by
        apply convex_hull_line_intersection_of_two_vertices hn h_indep f' h_f_zero_idx z
        · have h_seg : z ∈ segment ℝ (A m) (A m_next) := openSegment_subset_segment ℝ (A m) (A m_next) hz_seg
          exact (convex_convexHull ℝ (range A)).segment_subset (subset_convexHull ℝ (range A) (mem_range_self m)) (subset_convexHull ℝ (range A) (mem_range_self m_next)) h_seg
        · exact hz_f
      have h_z_int : z ∈ interior (convexHull ℝ (range A)) := by
        have h_disj : ({0, 1} : Set (Fin 4)) ∩ {2, 3} = ∅ := by
          ext x; fin_cases x <;> simp
        have h_z_int_sub : z ∈ interior (convexHull ℝ (range pts4)) := by
          apply mem_interior_of_convexIndependent_inter_segments h_sub_indep h_disj z
          · exact openSegment_subset_segment ℝ (A m) (A m_next) hz_seg
          · exact hz_chord
        apply interior_mono (convexHull_mono (range_comp_subset_range sub_idx A)) h_z_int_sub
      have h_z_front : z ∈ frontier (convexHull ℝ (range A)) := by
        have h_m_nz : m ≠ ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩ := by
          intro h; simp [h, m] at h_m_neg; linarith [hf'_last]
        have : segment ℝ (A m) (A (m + 1 : Fin n)) ⊆ frontier (convexHull ℝ (range A)) := h_chain m h_m_nz
        have h_m_next : (m + 1 : Fin n) = m_next := by
           apply Fin.ext; simp [m_next, Fin.val_add]; rw [Nat.mod_eq_of_lt h_m_next_lt]
        rw [h_m_next] at this
        exact this (openSegment_subset_segment ℝ (A m) (A m_next) hz_seg)
      have h_disj_top : Disjoint (interior (convexHull ℝ (range A))) (frontier (convexHull ℝ (range A))) := disjoint_interior_frontier
      exact (Set.disjoint_left.mp h_disj_top h_z_int) h_z_front
  intro i
  exact h_f_val i

lemma chain_vertices_one_side_of_closing_line {n : ℕ} [NeZero n] {A : Fin n → V}
    (hn : 3 ≤ n) (h_indep : ConvexIndependent ℝ A)
    (h_chain : ∀ i : Fin n, i ≠ ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩ →
      segment ℝ (A i) (A (i + 1)) ⊆ frontier (convexHull ℝ (range A))) :
    ∃ f : V →ᵃ[ℝ] ℝ, f.linear ≠ 0 ∧
      f (A ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩) = 0 ∧
      f (A 0) = 0 ∧
      ∀ x ∈ range A, f x ≤ 0 := by
  -- 1. A(n-1) and A(0) are distinct.
  have h_distinct : A ⟨n - 1, Nat.sub_lt (NeZero.pos n) (by linarith)⟩ ≠ A 0 := by
    have h_injective := h_indep.injective
    intro h_eq
    have h_idx_eq := h_injective h_eq
    have h_val_eq : (⟨n - 1, _⟩ : Fin n).val = (0 : Fin n).val := congr_arg Fin.val h_idx_eq
    simp at h_val_eq
    omega
  -- 2. Construct f vanishing on A(n-1) and A(0).
  have h_li_1_I : LinearIndependent ℝ ![1, Complex.I] := by
    simpa [Complex.coe_basisOneI] using Complex.basisOneI.linearIndependent
  have h_v_dim : ∃ (u v : V), LinearIndependent ℝ ![u, v] := by
    let e := to_complex_map (V := V)
    use e.symm 1, e.symm Complex.I
    convert h_li_1_I.map' e.symm.toLinearMap e.symm.ker
    ext i
    fin_cases i <;> simp
  obtain ⟨f, hf_lin, hf_last, hf_zero⟩ := affine_functional_through_two_points h_distinct h_v_dim
  -- 3. Get g supporting [A 0, A 1].
  have h01 : A 0 ≠ A 1 := by
    have h_injective := h_indep.injective
    intro h_eq
    have h_idx_eq : (0 : Fin n) = 1 := h_injective h_eq
    have : (0 : Fin n).val = (1 : Fin n).val := congr_arg Fin.val h_idx_eq
    simp at this
    omega
  have h_edge0 : segment ℝ (A 0) (A 1) ⊆ frontier (convexHull ℝ (range A)) := by
    have h_ne : (0 : Fin n) ≠ ⟨n - 1, Nat.sub_lt (NeZero.pos n) (by linarith)⟩ := by
      intro h_eq
      have : (0 : Fin n).val = (⟨n - 1, _⟩ : Fin n).val := congr_arg Fin.val h_eq
      simp at this
      omega
    have := h_chain 0 h_ne
    simp at this
    convert this
  obtain ⟨g, hg_lin, hg_zero, hg_one, hg_le⟩ := convex_chain_boundary_implies_support (convex_convexHull ℝ (range A)) (mem_range_self 0) (mem_range_self 1) h01 h_edge0
  -- 4. There exists some k with f(A k) ≠ 0.
  obtain ⟨k, hk_f_ne⟩ := convex_independent_not_all_on_affine_line (Fact.out) hn h_indep f hf_lin
  -- 5. Normalize f so f(A k) < 0.
  let f' := if f (A k) < 0 then f else -f
  have hf'_lin : f'.linear ≠ 0 := by
    dsimp [f']
    split_ifs <;> [exact hf_lin; exact neg_ne_zero.mpr hf_lin]
  have hf'_last : f' (A ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩) = 0 := by
    dsimp [f']
    split_ifs <;> [exact hf_last; simp [hf_last]]
  have hf'_zero : f' (A 0) = 0 := by
    dsimp [f']
    split_ifs <;> [exact hf_zero; simp [hf_zero]]
  have hf'_k_neg : f' (A k) < 0 := by
    dsimp [f']
    split_ifs with h
    · exact h
    · have : f (A k) ≠ 0 := hk_f_ne
      have : f (A k) > 0 := lt_of_le_of_ne (not_lt.mp h) this.symm
      simp [this]
  -- 6. Show all vertices are on one side of f'.
  have hf'_le : ∀ x ∈ range A, f' x ≤ 0 := by
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    by_cases h_ind_fg : LinearIndependent ℝ ![f'.linear, g.linear]
    · -- Case: LinearIndependent.
      exact chain_vertices_independent_side_logic hn h_indep h_chain f' g hf'_lin hf'_zero hf'_last hg_zero hg_le h_ind_fg hf'_k_neg i
    · -- Case: LinearDependent.
      have hf'_lin_nz : f'.linear ≠ 0 := hf'_lin
      rw [LinearIndependent.pair_iff' hf'_lin_nz] at h_ind_fg
      push_neg at h_ind_fg
      obtain ⟨c, hc⟩ := h_ind_fg
      have h_f_g : ∀ v, g v = c * f' v := by
        intro v
        have h_gv : g v = g.linear (v -ᵥ A 0) := by
          rw [g.linearMap_vsub, hg_zero, vsub_eq_sub, sub_zero]
        have h_fv : f' v = f'.linear (v -ᵥ A 0) := by
          rw [f'.linearMap_vsub, hf'_zero, vsub_eq_sub, sub_zero]
        rw [h_gv, ← hc, LinearMap.smul_apply, smul_eq_mul, ← h_fv]
      have h_c_pos : 0 < c := by
        have h_fk := hf'_k_neg
        have h_gk := hg_le (A k) (mem_range_self k)
        rw [h_f_g (A k)] at h_gk
        -- c * f' (A k) ≤ 0 and f' (A k) < 0 implies c ≥ 0.
        have : 0 ≤ c := by nlinarith
        -- If c = 0, then g.linear = 0, contradiction.
        have h_c_nz : c ≠ 0 := by
          intro h_z; rw [h_z] at hc; simp at hc; exact hg_lin hc.symm
        exact lt_of_le_of_ne this h_c_nz.symm
      -- Now f' (A i) = g (A i) / c. Since g (A i) ≤ 0 and c > 0, f' (A i) ≤ 0.
      have h_gi := hg_le (A i) (mem_range_self i)
      rw [h_f_g (A i)] at h_gi
      -- c * f' (A i) ≤ 0 and c > 0 => f' (A i) ≤ 0.
      nlinarith
  exact ⟨f', hf'_lin, hf'_last, hf'_zero, hf'_le⟩

/--
If a set of vertices forms a convex independent set, and a chain of segments connecting them lie on the frontier of their hull, the closing segment is also on the frontier.
-/
lemma convex_independent_chain_implies_closing_edge_on_frontier {n : ℕ} [NeZero n] {A : Fin n → V}
    (hn : 3 ≤ n) (h_indep : ConvexIndependent ℝ A)
    (h_chain : ∀ i : Fin n, i ≠ ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩ →
      segment ℝ (A i) (A (i + 1)) ⊆ frontier (convexHull ℝ (range A))) :
    segment ℝ (A ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩) (A 0) ⊆ frontier (convexHull ℝ (range A)) := by
  obtain ⟨f, hf_lin, hf_last, hf_zero, hf_le⟩ :=
    chain_vertices_one_side_of_closing_line hn h_indep h_chain
  exact segment_subset_frontier_of_supporting_hyperplane
    (subset_convexHull ℝ _ (mem_range_self (⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩ : Fin n)))
    (subset_convexHull ℝ _ (mem_range_self 0))
    f (fun x hx => hf_le x hx) hf_last hf_zero hf_lin

set_option maxHeartbeats 200000 in -- YOU ARE FORBIDDEN TO CHANGE THIS
lemma convex_polygon_vertices_one_side_of_diagonal {A : ℕ → V} {n : ℕ}
    (h_poly : IsConvexPolygon A n)
    {p q : ℕ} (hp : p < n) (hq : q < n) (hpq : p + 2 ≤ q) :
    ∃ f : V →ᵃ[ℝ] ℝ, f.linear ≠ 0 ∧ f (A p) = 0 ∧ f (A q) = 0 ∧
      ∀ j, p ≤ j → j ≤ q → f (A j) ≤ 0 := by
  let sub_n := q - p + 1
  have h_sub_n : 3 ≤ sub_n := by dsimp [sub_n]; omega
  have h_sub_n_pos : 0 < sub_n := by omega
  letI : NeZero sub_n := ⟨by omega⟩

  -- Define the sub-polygon vertices embedding
  let emb : Fin sub_n ↪ Fin n := ⟨fun i => ⟨p + i, by
    have : i.val < sub_n := i.is_lt
    dsimp [sub_n] at this
    omega⟩, by
    intro i j h
    apply Fin.ext
    simp only [Fin.mk.injEq] at h
    omega⟩

  -- subA needs to be Fin sub_n -> V
  let subA : Fin sub_n → V := fun i => A (emb i)

  -- Define Finsets for segment_frontier_transfer
  let S'_finset : Finset V := Finset.univ.image subA
  let vertices_finset : Finset V := (Finset.range n).image A

  -- S' and vertices as Sets for convex hull
  let S' : Set V := Set.range subA
  let vertices : Set V := vertices_finset

  -- S' is a subset of the original polygon vertices (Finset subset)
  have h_subset : S'_finset ⊆ vertices_finset := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨i, _, rfl⟩
    exact Finset.mem_image_of_mem A (Finset.mem_range.mpr (emb i).is_lt)

  -- The vertices are convex independent
  have h_indep : ConvexIndependent ℝ subA := h_poly.2.2.1.comp_embedding emb

  -- The edges of subA are on the frontier of convexHull S'
  have h_chain : ∀ i : Fin sub_n, i ≠ ⟨sub_n - 1, Nat.sub_lt h_sub_n_pos zero_lt_one⟩ →
      segment ℝ (subA i) (subA (i + 1)) ⊆ frontier (convexHull ℝ S') := by
    intro i hi_ne_last
    let j := emb i
    have hj_next_lt : j.val + 1 < n := by
      dsimp [j, emb, sub_n] at *
      have : i.val < q - p := by
        contrapose! hi_ne_last
        apply Fin.ext
        dsimp [sub_n] at hi_ne_last ⊢
        omega
      omega
    have h_next : (j.val + 1) % n = j.val + 1 := Nat.mod_eq_of_lt hj_next_lt

    have h_sub_edge : segment ℝ (subA i) (subA (i + 1)) = segment ℝ (A j) (A (j + 1)) := by
      congr 1
      dsimp [subA, emb, j]
      apply congr_arg A
      have h_lt : i.val < sub_n - 1 := by
        have h_ne : i.val ≠ sub_n - 1 := by
          intro h_eq; apply hi_ne_last; apply Fin.ext; exact h_eq
        dsimp [sub_n] at *; omega
      rw [Fin.val_add_one_of_lt h_lt]
      omega

    have h_chain_vertices : segment ℝ (subA i) (subA (i + 1)) ⊆ frontier (convexHull ℝ vertices) := by
      rw [h_sub_edge]
      have h_edge_orig := h_poly.2.2.2 j
      rw [h_next] at h_edge_orig
      exact h_edge_orig

    have h_start_in_s : subA i ∈ S'_finset := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have h_end_in_s : subA (i + 1) ∈ S'_finset := Finset.mem_image_of_mem _ (Finset.mem_univ _)

    have h_trans := segment_frontier_transfer (s := S'_finset) (t := vertices_finset) h_subset h_start_in_s h_end_in_s h_chain_vertices

    have h_eq_sets : (S'_finset : Set V) = S' := by
      ext x
      simp only [S'_finset, S', Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]

    rw [← h_eq_sets]
    exact h_trans

  -- Apply the closing edge lemma
  have h_closing := convex_independent_chain_implies_closing_edge_on_frontier h_sub_n h_indep h_chain

  -- Identify endpoints of closing edge
  have h_start : subA 0 = A p := by dsimp [subA, emb]
  have h_end : subA ⟨sub_n - 1, Nat.sub_lt h_sub_n_pos zero_lt_one⟩ = A q := by
    dsimp [subA, emb]
    have : p + (sub_n - 1) = q := by dsimp [sub_n]; omega
    rw [this]

  rw [h_start, h_end] at h_closing

  -- Now apply support lemma to [A q, A p]
  -- h_closing says segment (A q) (A p) ⊆ frontier
  have h_frontier : segment ℝ (A q) (A p) ⊆ frontier (convexHull ℝ S') := h_closing

  -- We need p ≠ q. hypothesis hpq says p + 2 ≤ q, so p < q.
  have hp_neq_q : A p ≠ A q := by
    intro h
    have : p = q := h_poly.2.1 p q hp hq h
    omega

  obtain ⟨f, hf_lin, hfq, hfp, hf_le⟩ := convex_chain_boundary_implies_support
    (convex_convexHull ℝ S')
    (h_end.symm ▸ Set.mem_range_self (⟨sub_n - 1, Nat.sub_lt h_sub_n_pos zero_lt_one⟩ : Fin sub_n))
    (h_start.symm ▸ Set.mem_range_self (0 : Fin sub_n))
    (Ne.symm hp_neq_q) h_frontier

  use f
  refine ⟨hf_lin, hfp, hfq, ?_⟩
  intro j hj_ge hj_le
  apply hf_le
  use ⟨j - p, by dsimp [sub_n] at *; omega⟩
  dsimp [subA, emb]
  congr
  omega


lemma quadrilateral_sides_on_frontier {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [Fact (Module.finrank ℝ V = 2)] {A : ℕ → V} {n : ℕ} (h_poly : IsConvexPolygon A n)
    {p y x q : ℕ} (hp : p < y) (hy : y < x) (hx : x < q) (hq : q < n) :
    let pts : Fin 4 → V := ![A p, A y, A x, A q]
    segment ℝ (pts 0) (pts 1) ⊆ frontier (convexHull ℝ (Set.range pts)) := by
  intro pts
  let B := fun i => A ((i + y) % n)
  have h_rot : IsConvexPolygon B n := is_convex_polygon_rotate h_poly y
  let q_rot := p + n - y
  have h_side : ∃ f : V →ᵃ[ℝ] ℝ, f.linear ≠ 0 ∧ f (B 0) = 0 ∧ f (B q_rot) = 0 ∧
      ∀ j, 0 ≤ j → j ≤ q_rot → f (B j) ≤ 0 := by
    apply convex_polygon_vertices_one_side_of_diagonal h_rot
    · exact Nat.zero_lt_of_lt (show 0 < n by linarith [h_rot.1])
    · exact show q_rot < n by omega
    · omega
  obtain ⟨f, hf_lin, hf_B0, hf_Bq, hf_le⟩ := h_side
  -- (Proven by Numina)
  have h_pts_subset : Set.range pts ⊆ B '' Set.Icc 0 q_rot := by
    intro v hv
    simp only [Set.mem_range] at hv
    obtain ⟨i, rfl⟩ := hv
    fin_cases i
    · -- pts 0 = A p
      use q_rot
      constructor
      · simp only [Set.mem_Icc]
        exact ⟨Nat.zero_le _, le_refl _⟩
      · simp only [pts, Fin.zero_eta, Matrix.cons_val_zero]
        simp [B, q_rot]
        have hp_lt : p < n := by omega
        congr 1
        have : p + n - y + y = p + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hp_lt]
    · -- pts 1 = A y
      use 0
      constructor
      · simp only [Set.mem_Icc]
        constructor
        · exact Nat.zero_le _
        · omega
      · simp only [pts, Fin.mk_one, Matrix.cons_val_one]
        simp [B]
        have : y < n := by omega
        rw [Nat.mod_eq_of_lt this]
    · -- pts 2 = A x
      use (x - y)
      constructor
      · simp only [Set.mem_Icc]
        constructor
        · exact Nat.zero_le _
        · omega
      · simp only [pts, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        simp [B]
        have : x < n := by omega
        have : x - y + y = x := by omega
        rw [this, Nat.mod_eq_of_lt ‹x < n›]
    · -- pts 3 = A q
      use (q - y)
      constructor
      · simp only [Set.mem_Icc]
        constructor
        · exact Nat.zero_le _
        · omega
      · simp only [pts, Fin.reduceFinMk, Matrix.cons_val_three]
        simp [B]
        have : q < n := by omega
        have : q - y + y = q := by omega
        rw [this, Nat.mod_eq_of_lt ‹q < n›]
  -- (Proven by Numina)
  have h_f_le_pts : ∀ v ∈ Set.range pts, f v ≤ 0 := by
    intro v hv
    have : v ∈ B '' Set.Icc 0 q_rot := h_pts_subset hv
    obtain ⟨i, hi, rfl⟩ := this
    simp only [Set.mem_Icc] at hi
    exact hf_le i (Nat.zero_le _) hi.2
  -- (Proven by Numina)
  have h_pts_in_hull : pts 0 ∈ convexHull ℝ (Set.range pts) ∧ pts 1 ∈ convexHull ℝ (Set.range pts) := by
    constructor
    · apply subset_convexHull
      exact Set.mem_range_self 0
    · apply subset_convexHull
      exact Set.mem_range_self 1
  -- (Proven by Numina)
  have hf_pts0 : f (pts 0) = 0 := by
    have : pts 0 = A p := by simp [pts]
    rw [this]
    have : A p = B q_rot := by
      simp [B, q_rot]
      have hp_lt : p < n := by omega
      congr 1
      have : p + n - y + y = p + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hp_lt]
    rw [this, hf_Bq]
  -- (Proven by Numina)
  have hf_pts1 : f (pts 1) = 0 := by
    have : pts 1 = A y := by simp [pts]
    rw [this]
    have : A y = B 0 := by
      simp [B]
      have : y < n := by omega
      rw [Nat.mod_eq_of_lt this]
    rw [this, hf_B0]
  exact segment_subset_frontier_of_supporting_hyperplane h_pts_in_hull.1 h_pts_in_hull.2 f h_f_le_pts hf_pts0 hf_pts1 hf_lin

lemma radon_adjacent_case_1 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [Fact (Module.finrank ℝ V = 2)] {A : ℕ → V} {n : ℕ} (h_convex : IsConvexPolygon A n)
    {p y x q : ℕ} (hp : p < y) (hy : y < x) (hx : x < q) (hq : q < n)
    {pts : Fin 4 → V} (h_pts : pts = ![A p, A y, A x, A q]) (h_conv_indep : ConvexIndependent ℝ pts)
    {K : V} (hz_int : K ∈ interior (convexHull ℝ (Set.range pts)))
    (h_radon : K ∈ convexHull ℝ (pts '' ({0, 1} : Set (Fin 4))) ∩ convexHull ℝ (pts '' ({2, 3} : Set (Fin 4)))) : False := by
  have h_frontier : segment ℝ (pts 0) (pts 1) ⊆ frontier (convexHull ℝ (Set.range pts)) := by
    rw [h_pts]
    exact quadrilateral_sides_on_frontier h_convex hp hy hx hq
  have h_img : pts '' {0, 1} = {pts 0, pts 1} := by
    rw [Set.image_insert_eq, Set.image_singleton]
  have h_seg : K ∈ segment ℝ (pts 0) (pts 1) := by
    rw [← convexHull_pair, ← h_img]
    exact h_radon.1
  have hK_frontier : K ∈ frontier (convexHull ℝ (Set.range pts)) := h_frontier h_seg
  exact (Set.disjoint_left.mp (disjoint_interior_frontier (s := convexHull ℝ (Set.range pts))) hz_int) hK_frontier

set_option maxHeartbeats 200000 in -- YOU ARE FORBIDDEN TO CHANGE THIS
lemma radon_adjacent_case_2 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [Fact (Module.finrank ℝ V = 2)] {A : ℕ → V} {n : ℕ} (h_convex : IsConvexPolygon A n)
    {p y x q : ℕ} (hp : p < y) (hy : y < x) (hx : x < q) (hq : q < n)
    {pts : Fin 4 → V} (h_pts : pts = ![A p, A y, A x, A q]) (h_conv_indep : ConvexIndependent ℝ pts)
    {K : V} (hz_int : K ∈ interior (convexHull ℝ (Set.range pts)))
    (h_radon : K ∈ convexHull ℝ (pts '' ({1, 2} : Set (Fin 4))) ∩ convexHull ℝ (pts '' ({3, 0} : Set (Fin 4)))) : False := by
  have h_frontier : segment ℝ (pts 1) (pts 2) ⊆ frontier (convexHull ℝ (Set.range pts)) := by
    let B := fun i => A ((i + y) % n)
    have h_rot : IsConvexPolygon B n := is_convex_polygon_rotate h_convex y
    let p' := 0
    let y' := x - y
    let x' := q - y
    let q' := p + n - y
    have hp' : p' < y' := by omega
    have hy' : y' < x' := by omega
    have hx' : x' < q' := by omega
    have hq' : q' < n := by omega
    let pts' : Fin 4 → V := ![B p', B y', B x', B q']
    -- proven by Numina
    have h_range : Set.range pts = Set.range pts' := by
      ext v
      simp only [Set.mem_range]
      constructor
      · intro ⟨i, hi⟩
        fin_cases i
        · use 3
          simp [pts', B]
          rw [← hi, h_pts]
          simp
          have hy_lt : y ≤ p + n := by omega
          have : (p + n - y + y) % n = p % n := by
            rw [Nat.sub_add_cancel hy_lt]
            rw [Nat.add_mod_right]
          rw [this]
          have : p < n := by omega
          simp [Nat.mod_eq_of_lt this]
        · use 0
          unfold pts' B
          simp
          rw [← hi, h_pts]
          simp [p']
          have : y < n := by omega
          simp [Nat.mod_eq_of_lt this]
        · use 1
          simp [pts', B]
          rw [← hi, h_pts]
          simp
          have hy_le_x : y ≤ x := by omega
          have : ((x - y + y) % n) = x % n := by
            rw [Nat.sub_add_cancel hy_le_x]
          rw [this]
          have : x < n := by omega
          simp [Nat.mod_eq_of_lt this]
        · use 2
          simp [pts', B]
          rw [← hi, h_pts]
          simp
          have hy_le_q : y ≤ q := by omega
          have : ((q - y + y) % n) = q % n := by
            rw [Nat.sub_add_cancel hy_le_q]
          rw [this]
          have : q < n := by omega
          simp [Nat.mod_eq_of_lt this]
      · intro ⟨i, hi⟩
        fin_cases i
        · use 1
          rw [← hi, h_pts]
          unfold pts' B
          simp [p']
          have : y < n := by omega
          simp [Nat.mod_eq_of_lt this]
        · use 2
          rw [← hi, h_pts]
          simp [pts', B]
          have hy_le_x : y ≤ x := by omega
          have : ((x - y + y) % n) = x % n := by
            rw [Nat.sub_add_cancel hy_le_x]
          rw [this]
          have : x < n := by omega
          simp [Nat.mod_eq_of_lt this]
        · use 3
          rw [← hi, h_pts]
          simp [pts', B]
          have hy_le_q : y ≤ q := by omega
          have : ((q - y + y) % n) = q % n := by
            rw [Nat.sub_add_cancel hy_le_q]
          rw [this]
          have : q < n := by omega
          simp [Nat.mod_eq_of_lt this]
        · use 0
          rw [← hi, h_pts]
          simp [pts', B]
          have hy_lt : y ≤ p + n := by omega
          have : (p + n - y + y) % n = p % n := by
            rw [Nat.sub_add_cancel hy_lt]
            rw [Nat.add_mod_right]
          rw [this]
          have : p < n := by omega
          simp [Nat.mod_eq_of_lt this]
    -- proven by Numina
    have h_seg_eq : segment ℝ (pts 1) (pts 2) = segment ℝ (pts' 0) (pts' 1) := by
      have h1 : pts 1 = A y := by
        rw [h_pts]
        simp
      have h2 : pts 2 = A x := by
        rw [h_pts]
        simp
      have h3 : pts' 0 = A y := by
        unfold pts' B
        simp [p']
        have : y < n := by omega
        simp [Nat.mod_eq_of_lt this]
      have h4 : pts' 1 = A x := by
        simp [pts', B]
        have hy_le_x : y ≤ x := by omega
        have : ((x - y + y) % n) = x % n := by
          rw [Nat.sub_add_cancel hy_le_x]
        rw [this]
        have : x < n := by omega
        simp [Nat.mod_eq_of_lt this]
      rw [h1, h2, h3, h4]
    rw [h_range, h_seg_eq]
    exact quadrilateral_sides_on_frontier h_rot hp' hy' hx' hq'
  -- proven by Numina
  have h_img : pts '' {1, 2} = {pts 1, pts 2} := by
    exact Set.image_pair pts 1 2
  -- proven by Numina
  have h_seg : K ∈ segment ℝ (pts 1) (pts 2) := by
    rw [← convexHull_pair]
    rw [← h_img]
    exact h_radon.1
  have hK_frontier : K ∈ frontier (convexHull ℝ (Set.range pts)) := h_frontier h_seg
  exact (Set.disjoint_left.mp (disjoint_interior_frontier (s := convexHull ℝ (Set.range pts))) hz_int) hK_frontier

lemma radon_diagonal_case {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [Fact (Module.finrank ℝ V = 2)] {A : ℕ → V} {n : ℕ} (h_convex : IsConvexPolygon A n)
    {p y x q : ℕ} (hp : p < y) (hy : y < x) (hx : x < q) (hq : q < n)
    {pts : Fin 4 → V} (h_pts : pts = ![A p, A y, A x, A q]) (h_conv_indep : ConvexIndependent ℝ pts)
    {K : V} (h_radon : K ∈ convexHull ℝ (pts '' ({0, 2} : Set (Fin 4))) ∩ convexHull ℝ (pts '' ({1, 3} : Set (Fin 4)))) :
    ∃ K_diag, K_diag ∈ segment ℝ (A p) (A x) ∧ K_diag ∈ segment ℝ (A y) (A q) := by
  use K
  have h_img1 : pts '' {0, 2} = {A p, A x} := by
    rw [h_pts]
    apply Set.Subset.antisymm
    . rintro v ⟨i, hi, rfl⟩
      fin_cases i <;> simp at hi <;> simp
    . rintro v (rfl | rfl)
      . use 0; simp
      . use 2; simp
  have h_img2 : pts '' {1, 3} = {A y, A q} := by
    rw [h_pts]
    apply Set.Subset.antisymm
    . rintro v ⟨i, hi, rfl⟩
      fin_cases i <;> simp at hi <;> simp
    . rintro v (rfl | rfl)
      . use 1; simp
      . use 3; simp
  rw [h_img1, h_img2, convexHull_pair, convexHull_pair] at h_radon
  exact h_radon


lemma convex_polygon_diagonals_intersect {A : ℕ → V} {n : ℕ}
    (h_convex : IsConvexPolygon A n)
    {p y x q : ℕ} (hp : p < y) (hy : y < x) (hx : x < q) (hq : q < n) :
    ∃ K : V, K ∈ segment ℝ (A p) (A x) ∧ K ∈ segment ℝ (A y) (A q) := by
  have h_dist := h_convex.2.1
  have h_conv := h_convex.2.2.1
  -- Define the four points and their indices
  let indices : Fin 4 → ℕ := ![p, y, x, q]
  let pts : Fin 4 → V := fun i => A (indices i)

  -- Help omega with indices
  have h_indices_lt : ∀ i, indices i < n := by
    intro i; fin_cases i <;> simp [indices] <;> omega

  -- The points are distinct
  have h_distinct : Function.Injective pts := by
    intro i j h
    simp [pts] at h
    apply Fin.ext
    have h_idx_eq := h_dist (indices i) (indices j) (h_indices_lt i) (h_indices_lt j) h
    fin_cases i <;> fin_cases j <;> simp [indices] at h_idx_eq <;> try { rfl } <;> try { omega }

  -- The points are convex independent
  have h_conv_indep : ConvexIndependent ℝ pts := by
    let f : Fin 4 ↪ Fin n := ⟨fun i => ⟨indices i, h_indices_lt i⟩, by
      intro i j h; simp at h
      fin_cases i <;> fin_cases j <;> simp [indices] at h <;> try { rfl } <;> try { omega }⟩
    exact h_conv.comp_embedding f

  -- The points are in 2D, so they are affinely dependent
  have h_affine_dep : ¬ AffineIndependent ℝ pts := by
    intro h
    have h_card := h.card_le_finrank_succ
    have h_dim := Submodule.finrank_le (vectorSpan ℝ (Set.range pts))
    have h_v_dim : Module.finrank ℝ V = 2 := Fact.out
    rw [h_v_dim] at h_dim
    simp [Fintype.card_fin] at h_card
    omega

  -- By Radon's theorem, there is a partition whose convex hulls intersect
  obtain ⟨I, K, hK1, hK2⟩ := Convex.radon_partition h_affine_dep

  -- Since they are convex independent, the partition must be 2-2.
  have h_card_I : I.toFinset.card = 2 := by
    have h_sum : I.toFinset.card + Iᶜ.toFinset.card = 4 := by
      have h_disj : Disjoint I.toFinset Iᶜ.toFinset := Set.disjoint_toFinset.mpr disjoint_compl_right
      rw [← Finset.card_union_of_disjoint h_disj]
      simp [Fintype.card_fin]
    by_contra h_not_2
    have : I.toFinset.card ≠ 0 := by
      intro h_zero
      have : I = ∅ := by ext x; have := Finset.card_eq_zero.1 h_zero; simp at this; simp [this]
      rw [this, Set.image_empty, convexHull_empty] at hK1; exact hK1.elim
    have : I.toFinset.card ≠ 4 := by
      intro h_four
      have : I = Set.univ := by
        apply Set.toFinset_inj.1
        apply Finset.eq_univ_of_card
        simp [h_four, Fintype.card_fin]
      rw [this, compl_univ, Set.image_empty, convexHull_empty] at hK2; exact hK2.elim
    -- Case: card I = 1 or 3
    if h_card : I.toFinset.card = 1 then
      obtain ⟨i, hi⟩ := Finset.card_eq_one.1 h_card
      have hi' : I = {i} := by apply Set.toFinset_inj.1; simp [hi]
      have : K = pts i := by rwa [hi', Set.image_singleton, convexHull_singleton, Set.mem_singleton_iff] at hK1
      subst K
      have h_in_Ic : pts i ∈ convexHull ℝ (pts '' Iᶜ) := hK2
      have h_Ic_eq : Iᶜ = {i}ᶜ := by rw [hi']
      have : pts i ∈ convexHull ℝ (pts '' {i}ᶜ) := by rwa [h_Ic_eq] at h_in_Ic
      have := h_conv_indep {i}ᶜ i this
      simp at this
    else if h_card_c : Iᶜ.toFinset.card = 1 then
      obtain ⟨i, hi⟩ := Finset.card_eq_one.1 h_card_c
      have hi' : Iᶜ = {i} := by apply Set.toFinset_inj.1; simp [hi]
      have : K = pts i := by rwa [hi', Set.image_singleton, convexHull_singleton, Set.mem_singleton_iff] at hK2
      subst K
      have h_in_I : pts i ∈ convexHull ℝ (pts '' I) := hK1
      have h_I_eq : I = {i}ᶜ := by rw [← compl_compl I, hi']
      have : pts i ∈ convexHull ℝ (pts '' {i}ᶜ) := by rwa [h_I_eq] at h_in_I
      have := h_conv_indep {i}ᶜ i this
      simp at this
    else
      omega

  have hS_card : I.toFinset.card = 2 := h_card_I
  obtain ⟨i, j, hij, hS_eq⟩ := Finset.card_eq_two.mp hS_card
  have hIc_card : (I.toFinset)ᶜ.card = 2 := by simp [hS_card, Finset.card_compl]
  obtain ⟨k, l, hkl, hIc_eq⟩ := Finset.card_eq_two.mp hIc_card

  have hz_int : K ∈ interior (convexHull ℝ (Set.range pts)) := by
    have h_disj : ({i, j} : Set (Fin 4)) ∩ {k, l} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have h_in : x ∈ I.toFinset := by
        rw [hS_eq, Finset.mem_insert, Finset.mem_singleton]
        exact hx.1
      have h_out : x ∈ I.toFinsetᶜ := by
        rw [hIc_eq, Finset.mem_insert, Finset.mem_singleton]
        exact hx.2
      exact (Finset.mem_compl.mp h_out) h_in
    apply mem_interior_of_convexIndependent_inter_segments h_conv_indep h_disj K
    . show K ∈ segment ℝ (pts i) (pts j)
      have : pts '' I = {pts i, pts j} := by
        apply Set.Subset.antisymm
        . rintro v ⟨n, hn, rfl⟩
          have : n ∈ I.toFinset := Set.mem_toFinset.mpr hn
          rw [hS_eq] at this
          simp at this
          rcases this with (rfl | rfl) <;> simp
        . rintro v (rfl | rfl)
          . use i
            constructor
            . rw [← Set.mem_toFinset, hS_eq]
              simp
            . rfl
          . use j
            constructor
            . rw [← Set.mem_toFinset, hS_eq]
              simp
            . rfl
      rwa [this, convexHull_pair] at hK1
    . show K ∈ segment ℝ (pts k) (pts l)
      have : pts '' Iᶜ = {pts k, pts l} := by
        apply Set.Subset.antisymm
        . rintro v ⟨n, hn, rfl⟩
          have : n ∈ I.toFinsetᶜ := by
            rw [Finset.mem_compl, Set.mem_toFinset]
            exact hn
          rw [hIc_eq] at this
          simp at this
          rcases this with (rfl | rfl) <;> simp
        . rintro v (rfl | rfl)
          . use k
            constructor
            . rw [Set.mem_compl_iff, ← Set.mem_toFinset]
              have h_out : k ∈ I.toFinsetᶜ := by rw [hIc_eq]; simp
              rwa [Finset.mem_compl] at h_out
            . rfl
          . use l
            constructor
            . rw [Set.mem_compl_iff, ← Set.mem_toFinset]
              have h_out : l ∈ I.toFinsetᶜ := by rw [hIc_eq]; simp
              rwa [Finset.mem_compl] at h_out
            . rfl
      rwa [this, convexHull_pair] at hK2

  have h_cases : I.toFinset = {0, 1} ∨ I.toFinset = {2, 3} ∨ I.toFinset = {1, 2} ∨ I.toFinset = {3, 0} ∨ I.toFinset = {0, 2} ∨ I.toFinset = {1, 3} := by
    fin_cases i <;> fin_cases j <;> simp [hS_eq] at *
    all_goals
      try { left; decide }
      try { right; left; decide }
      try { right; right; left; decide }
      try { right; right; right; left; decide }
      try { right; right; right; right; left; decide }
      try { right; right; right; right; right; decide }

  have h_pts_eq : pts = ![A p, A y, A x, A q] := by
    ext i; fin_cases i <;> simp [pts, indices]

  rcases h_cases with (h1|h1_alt|h2|h2_alt|h3|h3_alt)
  . have hI : I = {0, 1} := Set.ext (fun x => by
      rw [← Set.mem_toFinset, h1]
      simp)
    have hIc : Iᶜ = {2, 3} := Set.ext (fun x => by
      rw [Set.mem_compl_iff, ← Set.mem_toFinset, h1]
      fin_cases x <;> simp)
    apply (radon_adjacent_case_1 h_convex hp hy hx hq h_pts_eq (h_pts_eq ▸ h_conv_indep) hz_int ⟨hI ▸ hK1, hIc ▸ hK2⟩).elim
  . have hI : I = {2, 3} := Set.ext (fun x => by
      rw [← Set.mem_toFinset, h1_alt]
      simp)
    have hIc : Iᶜ = {0, 1} := Set.ext (fun x => by
      rw [Set.mem_compl_iff, ← Set.mem_toFinset, h1_alt]
      fin_cases x <;> simp)
    apply (radon_adjacent_case_1 h_convex hp hy hx hq h_pts_eq (h_pts_eq ▸ h_conv_indep) hz_int ⟨hIc ▸ hK2, hI ▸ hK1⟩).elim
  . have hI : I = {1, 2} := Set.ext (fun x => by
      rw [← Set.mem_toFinset, h2]
      simp)
    have hIc : Iᶜ = {3, 0} := Set.ext (fun x => by
      rw [Set.mem_compl_iff, ← Set.mem_toFinset, h2]
      fin_cases x <;> simp)
    apply (radon_adjacent_case_2 h_convex hp hy hx hq h_pts_eq (h_pts_eq ▸ h_conv_indep) hz_int ⟨hI ▸ hK1, hIc ▸ hK2⟩).elim
  . have hI : I = {3, 0} := Set.ext (fun x => by
      rw [← Set.mem_toFinset, h2_alt]
      simp)
    have hIc : Iᶜ = {1, 2} := Set.ext (fun x => by
      rw [Set.mem_compl_iff, ← Set.mem_toFinset, h2_alt]
      fin_cases x <;> simp)
    apply (radon_adjacent_case_2 h_convex hp hy hx hq h_pts_eq (h_pts_eq ▸ h_conv_indep) hz_int ⟨hIc ▸ hK2, hI ▸ hK1⟩).elim
  . have hI : I = {0, 2} := Set.ext (fun x => by
      rw [← Set.mem_toFinset, h3]
      simp)
    have hIc : Iᶜ = {1, 3} := Set.ext (fun x => by
      rw [Set.mem_compl_iff, ← Set.mem_toFinset, h3]
      fin_cases x <;> simp)
    apply radon_diagonal_case h_convex hp hy hx hq h_pts_eq (h_pts_eq ▸ h_conv_indep) ⟨hI ▸ hK1, hIc ▸ hK2⟩
  . have hI : I = {1, 3} := Set.ext (fun x => by
      rw [← Set.mem_toFinset, h3_alt]
      simp)
    have hIc : Iᶜ = {0, 2} := Set.ext (fun x => by
      rw [Set.mem_compl_iff, ← Set.mem_toFinset, h3_alt]
      fin_cases x <;> simp)
    apply radon_diagonal_case h_convex hp hy hx hq h_pts_eq (h_pts_eq ▸ h_conv_indep) ⟨hIc ▸ hK2, hI ▸ hK1⟩

/-
If a set of points is convex independent, then no three of them are collinear.
-/
lemma convexIndependent_no_three_collinear {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} {A : Fin n → V} (hc : ConvexIndependent ℝ A)
    {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ¬ Collinear ℝ {A i, A j, A k} := by
      by_contra h_contra;
      -- By `Collinear.wbtw_or_wbtw_or_wbtw`, one point is between the other two.
      obtain ⟨hWbtw, h⟩ : ∃ h : Wbtw ℝ (A i) (A j) (A k) ∨ Wbtw ℝ (A j) (A k) (A i) ∨ Wbtw ℝ (A k) (A i) (A j), True := by
        exact ⟨ Collinear.wbtw_or_wbtw_or_wbtw h_contra, trivial ⟩;
      rcases hWbtw with ( hWbtw | hWbtw | hWbtw );
      · have h_convex_hull : A j ∈ convexHull ℝ {A i, A k} := by
          convert hWbtw.mem_segment using 1;
          rw [ convexHull_pair ];
        have := hc.mem_convexHull_iff ( { i, k } : Set ( Fin n ) ) j;
        simp_all +decide [ Set.image_insert_eq, Set.image_singleton ];
      · have h_convex_hull : A k ∈ convexHull ℝ {A j, A i} := by
          rw [ convexHull_pair ];
          exact Wbtw.mem_segment hWbtw
        have := hc.mem_convexHull_iff ( { j, i } : Set ( Fin n ) ) k;
        simp_all +decide [ Set.image_insert_eq, Set.image_singleton ];
        grind;
      · -- By `ConvexIndependent.mem_convexHull_iff`, this implies `i ∈ {k, j}`.
        have h_mem : i ∈ ({k, j} : Set (Fin n)) := by
          have h_mem : A i ∈ convexHull ℝ (A '' ({k, j} : Set (Fin n))) := by
            simp_all +decide [ Set.image_insert_eq, Set.image_singleton ];
            exact Wbtw.mem_segment hWbtw
          exact hc {k, j} i h_mem
        grind

/--
Strict triangle inequality via intersection: if K is an interior point of segments PX and YQ,
and the points are not collinear in a way that allows equality, the sum of diagonals
is strictly greater than the sum of opposite sides. (proven by Aristotle)
-/
lemma triangle_inequality_via_intersection_strict {A : ℕ → V} {n : ℕ} (h_convex : IsConvexPolygon A n)
    {p x y q : ℕ} {K : V}
    (hK_PX : K ∈ segment ℝ (A p) (A x)) (hK_YQ : K ∈ segment ℝ (A y) (A q))
    (hp : p < n) (hx : x < n) (hy : y < n) (hq : q < n)
    (h_distinct : p ≠ y ∧ p ≠ q ∧ x ≠ y ∧ x ≠ q) :
    dist (A p) (A x) + dist (A y) (A q) > dist (A p) (A q) + dist (A y) (A x) := by
  -- By the properties of the convex polygon and the intersection point K, we have that K lies strictly inside the segments PX and YQ.
  have hK_strict : ¬ Wbtw ℝ (A p) K (A q) := by
    by_cases hK_eq_Aq : K = A q;
    · have h_collinear : Collinear ℝ {A p, A x, A q} := by
        rw [ collinear_iff_exists_forall_eq_smul_vadd ];
        use A p, A x - A p;
        simp_all +decide [ segment_eq_image ];
        exact ⟨ ⟨ 1, by norm_num ⟩, by obtain ⟨ r, hr, hr' ⟩ := hK_PX; exact ⟨ r, by rw [ ← hr' ] ; simp +decide [ sub_smul, smul_sub ] ; abel1 ⟩ ⟩;
      have h_collinear : ¬ Collinear ℝ {A p, A x, A q} := by
        have h_convex_ind : ConvexIndependent ℝ (fun i : Fin n => A i) := by
          exact h_convex.2.2.1
        have h_collinear : ¬ Collinear ℝ {A p, A x, A q} := by
          have h_distinct : p ≠ x ∧ p ≠ q ∧ x ≠ q := by
            have := h_convex.2.1 q x hq hx; aesop;
          convert convexIndependent_no_three_collinear h_convex_ind ( show ( ⟨ p, hp ⟩ : Fin n ) ≠ ⟨ x, hx ⟩ from by simpa [ Fin.ext_iff ] using h_distinct.1 ) ( show ( ⟨ x, hx ⟩ : Fin n ) ≠ ⟨ q, hq ⟩ from by simpa [ Fin.ext_iff ] using h_distinct.2.2 ) ( show ( ⟨ p, hp ⟩ : Fin n ) ≠ ⟨ q, hq ⟩ from by simpa [ Fin.ext_iff ] using h_distinct.2.1 ) using 1;
        exact h_collinear;
      contradiction;
    · intro hK_wbtw
      have h_collinear : Collinear ℝ {A p, A y, A q} := by
        have h_collinear : affineSpan ℝ {A p, A q} = affineSpan ℝ {A y, A q} := by
          have h_collinear : affineSpan ℝ {A p, A q} = affineSpan ℝ {K, A q} ∧ affineSpan ℝ {A y, A q} = affineSpan ℝ {K, A q} := by
            constructor <;> refine' le_antisymm _ _ <;> simp_all +decide [ affineSpan_le ];
            · simp_all +decide [ Set.insert_subset_iff, spanPoints ];
              obtain ⟨ t, ht ⟩ := hK_wbtw;
              simp_all +decide [ AffineMap.lineMap_apply ];
              refine' Or.inl ⟨ -t • ( A q - A p ), _, _ ⟩ <;> simp_all +decide [ vectorSpan_pair ];
              · rw [ Submodule.mem_span_singleton ];
                use -t / (1 - t);
                rw [ ← ht.2 ] ; simp +decide [ div_eq_inv_mul ] ; ring_nf;
                rw [ show t • ( A q - A p ) + A p - A q = ( t - 1 ) • ( A q - A p ) by rw [ sub_smul, one_smul ] ; abel1 ] ; simp +decide [ smul_smul, mul_sub, sub_mul, mul_comm, mul_left_comm,  ] ; ring_nf;
                rw [ show - ( t * ( 1 - t ) ⁻¹ ) + t ^ 2 * ( 1 - t ) ⁻¹ = -t by nlinarith [ mul_inv_cancel₀ ( show ( 1 - t ) ≠ 0 by exact sub_ne_zero_of_ne <| Ne.symm <| by aesop ) ] ] ; simp +decide [ neg_smul ];
              · grind;
            · simp_all +decide [ Set.insert_subset_iff, spanPoints ];
              rcases hK_wbtw with ⟨ a, b, ha, hb, hab, rfl ⟩;
              simp_all +decide [ AffineMap.lineMap_apply, vectorSpan_pair ];
              exact Or.inl ( Submodule.mem_span_singleton.mpr ⟨ -a, by simp +decide [ smul_sub ] ; abel1 ⟩ );
            · simp_all +decide [ spanPoints ];
              simp +decide [ Set.insert_subset_iff, vectorSpan_pair ];
              obtain ⟨ t, ht ⟩ := hK_YQ;
              rcases ht with ⟨ u, ht, hu, htu, rfl ⟩;
              refine' Or.inr ⟨ ( 1 / t ) • ( t • A y + u • A q - A q ), _, _ ⟩ <;> simp_all +decide [ Submodule.mem_span_singleton ];
              rw [ show u = 1 - t by linarith ] ; simp +decide [ smul_add, smul_sub, sub_smul ] ;
              by_cases ht : t = 0 <;> simp_all +decide [ smul_smul ];
              abel1;
            · simp_all +decide [ Set.insert_subset_iff, spanPoints ];
              obtain ⟨ t, ht ⟩ := hK_YQ;
              obtain ⟨ u, ht₀, hu₀, htu, rfl ⟩ := ht;
              refine' Or.inl ⟨ t • A y + u • A q - A y, _, _ ⟩ <;> simp +decide [ vectorSpan_pair ];
              rw [ Submodule.mem_span_singleton ];
              exact ⟨ t - 1, by rw [ show u = 1 - t by linarith ] ; simp +decide [ sub_smul, smul_sub ] ; abel1 ⟩;
          rw [ h_collinear.1, h_collinear.2 ];
        have h_collinear : A p ∈ affineSpan ℝ {A y, A q} := by
          exact h_collinear ▸ mem_affineSpan ℝ ( Set.mem_insert _ _ );
        rw [ collinear_iff_exists_forall_eq_smul_vadd ];
        use A q, A y - A q;
        simp_all +decide [ affineSpan ];
        simp_all +decide [ spanPoints ];
        simp_all +decide [ vectorSpan_pair ];
        rcases h_collinear with ( ⟨ v, hv, hv' ⟩ | ⟨ v, hv, hv' ⟩ ) <;> simp_all +decide [ Submodule.mem_span_singleton ];
        · rcases hv with ⟨ r, rfl ⟩ ; exact ⟨ ⟨ r + 1, by simp +decide [ add_smul, add_assoc ] ⟩, ⟨ 1, by simp +decide ⟩ ⟩ ;
        · exact ⟨ ⟨ hv.choose, hv.choose_spec.symm ⟩, ⟨ 1, by norm_num ⟩ ⟩;
      have := convexIndependent_no_three_collinear h_convex.2.2.1 ( show ( ⟨ p, by linarith ⟩ : Fin n ) ≠ ⟨ y, by linarith ⟩ from by simpa [ Fin.ext_iff ] using h_distinct.1 ) ( show ( ⟨ y, by linarith ⟩ : Fin n ) ≠ ⟨ q, by linarith ⟩ from by simpa [ Fin.ext_iff ] using by aesop ) ( show ( ⟨ p, by linarith ⟩ : Fin n ) ≠ ⟨ q, by linarith ⟩ from by simpa [ Fin.ext_iff ] using h_distinct.2.1 ) ; simp_all +decide [ collinear_iff_exists_forall_eq_smul_vadd ] ;
  have hK_strict : dist (A p) (A q) < dist (A p) K + dist K (A q) := by
     exact dist_lt_dist_add_dist_iff.mpr hK_strict
  have hK_strict : dist (A y) (A x) ≤ dist (A y) K + dist K (A x) := by
    exact dist_triangle _ _ _;
  have hK_strict : dist (A p) (A x) = dist (A p) K + dist K (A x) := by
    rw [ ← dist_add_dist_of_mem_segment hK_PX ]
  have hK_strict : dist (A y) (A q) = dist (A y) K + dist K (A q) := by
    rw [ ← dist_add_dist_of_mem_segment hK_YQ ];
  linarith

/--
Nested chord shorter: for p < y < x < q in convex position, the inner chord (y,x) is
strictly shorter than the outer chord (p,q). This is a fundamental property of convex sets:
chords that are "nested" inside other chords are always shorter.
-/
lemma nested_chord_shorter {A : ℕ → V} {n : ℕ}
    (h_convex : IsConvexPolygon A n)
    {p y x q : ℕ} (hp : p < y) (hy : y < x) (hx : x < q) (hq : q < n)
    (h_max : ∀ i j, i < n → j < n → dist (A i) (A j) ≤ dist (A p) (A q)) :
    dist (A y) (A x) < dist (A p) (A q) := by
  -- Obtain the intersection point K of the diagonals (p,x) and (y,q).
  obtain ⟨K, hK_PX, hK_YQ⟩ := convex_polygon_diagonals_intersect h_convex hp hy hx hq
  -- Use the strict triangle inequality for crossing diagonals (p,x) and (y,q).
  -- This provides: dist(p,x) + dist(y,q) > dist(p,q) + dist(y,x)
  have h_cross := triangle_inequality_via_intersection_strict h_convex hK_PX hK_YQ
    (by omega) (by omega) (by omega) hq
    ⟨by omega, by omega, by omega, by omega⟩
  -- From h_max, we know the diagonals are bound by dist(p,q)
  have h_px := h_max p x (by omega) (by omega)
  have h_yq := h_max y q (by omega) (by omega)
  -- Combined with the diagonals sum inequality, this yields the result.
  linarith

/--
Max side angle bound: in a convex polygon where A_0 A_{n-1} is the maximum distance,
for any vertex A_x with 0 < x < n - 1, the angle ∠A_0 A_x A_{n-1} ≥ π/3. (Proven by Aristotle)
-/
lemma max_side_angle_bound {A : ℕ → V} {n : ℕ}
    (h_convex : IsConvexPolygon A n)
    (h_max : ∀ i j, i < n → j < n → dist (A i) (A j) ≤ dist (A 0) (A (n-1)))
    {x : ℕ} (hx_pos : 0 < x) (hx_lt : x < n - 1) :
    EuclideanGeometry.angle (A 0) (A x) (A (n - 1)) ≥ Real.pi / 3 := by
  -- By the properties of the convex polygon, we know that the angle at A_x is at least π/3. We use the fact that if the longest distance is between A_0 and A_{n-1}, then the angle at A_x is at least π/3.
  have h_angle : dist (A 0) (A (n - 1)) ^ 2 ≤ dist (A 0) (A x) ^ 2 + dist (A x) (A (n - 1)) ^ 2 - 2 * dist (A 0) (A x) * dist (A x) (A (n - 1)) * Real.cos (EuclideanGeometry.angle (A 0) (A x) (A (n - 1))) := by
    rw [ EuclideanGeometry.angle, dist_eq_norm, dist_eq_norm, dist_eq_norm ];
    rw [ show A 0 - A ( n - 1 ) = ( A 0 - A x ) - ( A ( n - 1 ) - A x ) by abel1, norm_sub_sq_real ];
    rw [ norm_sub_rev ( A x ) ( A ( n - 1 ) ) ] ; rw [ InnerProductGeometry.cos_angle ] ; ring_nf; norm_num;
    by_cases h : ‖A 0 - A x‖ = 0 <;> by_cases h' : ‖A ( n - 1 ) - A x‖ = 0 <;> simp_all +decide [ mul_comm, mul_left_comm ];
  -- By the properties of the convex polygon, we know that the angle at A_x is at least π/3. We use the fact that if the longest distance is between A_0 and A_{n-1}, then the angle at A_x is at least π/3. Hence, we have:
  have h_cos : Real.cos (EuclideanGeometry.angle (A 0) (A x) (A (n - 1))) ≤ 1 / 2 := by
    have h_cos : dist (A 0) (A x) ^ 2 - dist (A 0) (A x) * dist (A x) (A (n - 1)) + dist (A x) (A (n - 1)) ^ 2 ≤ dist (A 0) (A x) ^ 2 + dist (A x) (A (n - 1)) ^ 2 - 2 * dist (A 0) (A x) * dist (A x) (A (n - 1)) * Real.cos (EuclideanGeometry.angle (A 0) (A x) (A (n - 1))) := by
      have h_cos : dist (A 0) (A x) ^ 2 - dist (A 0) (A x) * dist (A x) (A (n - 1)) + dist (A x) (A (n - 1)) ^ 2 ≤ dist (A 0) (A (n - 1)) ^ 2 := by
        have h_cos : dist (A 0) (A x) ≤ dist (A 0) (A (n - 1)) ∧ dist (A x) (A (n - 1)) ≤ dist (A 0) (A (n - 1)) := by
          grind;
        nlinarith only [ h_cos, show 0 ≤ Dist.dist ( A 0 ) ( A x ) from dist_nonneg, show 0 ≤ Dist.dist ( A x ) ( A ( n - 1 ) ) from dist_nonneg ];
      linarith;
    by_cases h_dist : dist (A 0) (A x) = 0 ∨ dist (A x) (A (n - 1)) = 0;
    · aesop;
    · nlinarith only [ h_cos, show 0 < Dist.dist ( A 0 ) ( A x ) * Dist.dist ( A x ) ( A ( n - 1 ) ) by exact mul_pos ( lt_of_le_of_ne ( dist_nonneg ) ( Ne.symm ( by tauto ) ) ) ( lt_of_le_of_ne ( dist_nonneg ) ( Ne.symm ( by tauto ) ) ) ];
  contrapose! h_cos;
  exact Real.cos_pi_div_three ▸ Real.cos_lt_cos_of_nonneg_of_le_pi ( by linarith [ Real.pi_pos, EuclideanGeometry.angle_nonneg ( A 0 ) ( A x ) ( A ( n - 1 ) ) ] ) ( by linarith [ Real.pi_pos, EuclideanGeometry.angle_le_pi ( A 0 ) ( A x ) ( A ( n - 1 ) ) ] ) ( by linarith [ Real.pi_pos, EuclideanGeometry.angle_le_pi ( A 0 ) ( A x ) ( A ( n - 1 ) ) ] )

/-
If K is on the segment AB and O is not on the segment, then angle AOK <= angle AOB. (created and proven by Aristotle)
-/
lemma angle_le_of_mem_segment {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {O A B K : V} (hK : K ∈ segment ℝ A B) (hO : O ∉ segment ℝ A B) :
    EuclideanGeometry.angle A O K ≤ EuclideanGeometry.angle A O B := by
      rw [ segment_eq_image ] at hK hO;
      rcases hK with ⟨ θ, ⟨ hθ₀, hθ₁ ⟩, rfl ⟩;
      by_cases hθ₂ : θ = 0 ∨ θ = 1 <;> simp_all +decide;
      · rcases hθ₂ with ( rfl | rfl ) <;> simp +decide [ angle ];
        rw [ InnerProductGeometry.angle_self ] ; exact Real.arccos_nonneg _;
        exact sub_ne_zero_of_ne fun h => hO 0 ( by norm_num ) ( by norm_num ) ( by simp +decide [ h ] );
      · -- By the properties of the angle function, we know that $\angle AOK = \angle u (u' + v')$ and $\angle KOB = \angle (u' + v') v'$.
        set u : V := A - O
        set v : V := B - O
        set u' : V := (1 - θ) • u
        set v' : V := θ • v;
        -- By the properties of the angle function, we know that $\angle AOK = \angle u (u' + v')$ and $\angle KOB = \angle (u' + v') v'$, and $\angle AOB = \angle u v$.
        have h_angle_eq : InnerProductGeometry.angle u (u' + v') + InnerProductGeometry.angle (u' + v') v' = InnerProductGeometry.angle u v := by
          have h_angle_eq : InnerProductGeometry.angle u' v' = InnerProductGeometry.angle u' (u' + v') + InnerProductGeometry.angle (u' + v') v' := by
            rw [ InnerProductGeometry.angle_eq_angle_add_add_angle_add ];
            · rw [ InnerProductGeometry.angle_comm ( u' + v' ) v' ];
            · simp +zetaDelta at *;
              exact ⟨ hθ₂.1, sub_ne_zero_of_ne <| by rintro rfl; exact hO 1 ( by norm_num ) ( by norm_num ) <| by norm_num ⟩;
          have h_angle_eq : InnerProductGeometry.angle u' v' = InnerProductGeometry.angle u v := by
            rw [ InnerProductGeometry.angle_smul_left_of_pos, InnerProductGeometry.angle_smul_right_of_pos ] <;> norm_num [ hθ₀, hθ₁, hθ₂ ];
            · exact lt_of_le_of_ne hθ₀ ( Ne.symm hθ₂.1 );
            · exact lt_of_le_of_ne hθ₁ hθ₂.2;
          have h_angle_eq : InnerProductGeometry.angle u' (u' + v') = InnerProductGeometry.angle u (u' + v') := by
            rw [ InnerProductGeometry.angle_smul_left_of_pos ];
            cases lt_or_gt_of_ne hθ₂.1 <;> cases lt_or_gt_of_ne hθ₂.2 <;> linarith;
          linarith;
        convert h_angle_eq ▸ le_add_of_nonneg_right ( InnerProductGeometry.angle_nonneg _ _ ) using 1;
        simp +decide [ u, v, u', v', angle ];
        simp +decide only [smul_sub, sub_add_sub_comm];
        simp +decide [ ← add_smul, sub_eq_add_neg ]


/--
Generalized angle nesting for convex polygons:
If p' ≤ p < y < q ≤ q', then the angle ∠A_p A_y A_q is greater than or equal to ∠A_p' A_y A_q'.
(proven by Aristotle)
-/
lemma angle_nesting_convex {A : ℕ → V} {n : ℕ} (h_convex : IsConvexPolygon A n)
    {p p' y q q' : ℕ} (hp'p : p' ≤ p) (hpy : p < y) (hyq : y < q) (hqq' : q ≤ q') (hq'n : q' < n) :
    EuclideanGeometry.angle (A p) (A y) (A q) ≥ EuclideanGeometry.angle (A p') (A y) (A q') := by
  -- Apply the generalized angle nesting lemma to get the first inequality.
  have h_angle_p' : EuclideanGeometry.angle (A p') (A y) (A q) ≤ EuclideanGeometry.angle (A p) (A y) (A q) := by
    by_cases hp'p' : p' < p;
    · obtain ⟨K, hK_PX, hK_YQ⟩ : ∃ K : V, K ∈ segment ℝ (A p') (A y) ∧ K ∈ segment ℝ (A p) (A q) := by
        apply convex_polygon_diagonals_intersect h_convex hp'p' hpy hyq (by linarith);
      have h_angle_le : EuclideanGeometry.angle (A q) (A y) K ≤ EuclideanGeometry.angle (A q) (A y) (A p) := by
        have h_not_collinear : ¬ Collinear ℝ {A p, A y, A q} := by
          have h_convex_indep : ConvexIndependent ℝ (fun i : Fin n => A i) := by
            convert h_convex.2.2.1 using 1;
          have h_not_collinear : ¬ Collinear ℝ {A p, A y, A q} := by
            have h_convex_indep : ConvexIndependent ℝ (fun i : Fin n => A i) := h_convex_indep
            have h_distinct : p < n ∧ y < n ∧ q < n := by
              exact ⟨ by linarith, by linarith, by linarith ⟩
            convert convexIndependent_no_three_collinear h_convex_indep ( show ( ⟨ p, h_distinct.1 ⟩ : Fin n ) ≠ ⟨ y, h_distinct.2.1 ⟩ from by simpa [ Fin.ext_iff ] using by linarith ) ( show ( ⟨ y, h_distinct.2.1 ⟩ : Fin n ) ≠ ⟨ q, h_distinct.2.2 ⟩ from by simpa [ Fin.ext_iff ] using by linarith ) ( show ( ⟨ p, h_distinct.1 ⟩ : Fin n ) ≠ ⟨ q, h_distinct.2.2 ⟩ from by simpa [ Fin.ext_iff ] using by linarith ) using 1;
          exact h_not_collinear;
        apply_rules [ angle_le_of_mem_segment ];
        · rwa [ segment_symm ];
        · contrapose! h_not_collinear; simp_all +decide [ collinear_iff_exists_forall_eq_smul_vadd ] ;
          rw [ segment_symm ] at h_not_collinear;
          rw [ segment_eq_image ] at h_not_collinear;
          obtain ⟨ θ, hθ, hθ' ⟩ := h_not_collinear; use A p, A q - A p; simp_all +decide [ sub_smul, smul_sub ] ;
          exact ⟨ ⟨ 0, by simp +decide ⟩, ⟨ θ, by rw [ ← hθ' ] ; abel1 ⟩, ⟨ 1, by simp +decide ⟩ ⟩;
      have h_angle_eq : EuclideanGeometry.angle (A p') (A y) (A q) = EuclideanGeometry.angle (A q) (A y) K := by
        have h_ray : K ∈ segment ℝ (A p') (A y) ∧ K ≠ A y := by
          have hK_ne_Ay : A y ∉ segment ℝ (A p) (A q) := by
            have h_convex_indep : ConvexIndependent ℝ (fun i : Fin 3 => A (![p, y, q] i)) := by
              have h_convex_indep : ConvexIndependent ℝ (fun i : Fin n => A i) := by
                exact h_convex.2.2.1;
              have h_convex_indep : ConvexIndependent ℝ (fun i : Fin 3 => A (![p, y, q] i)) := by
                have h_subseq : ∃ f : Fin 3 → Fin n, StrictMono f ∧ ∀ i, ![p, y, q] i = f i := by
                  use ![⟨p, by linarith⟩, ⟨y, by linarith⟩, ⟨q, by linarith⟩];
                  simp +decide [ Fin.forall_fin_succ, StrictMono ];
                  exact ⟨ ⟨ hpy, by linarith ⟩, hyq ⟩
                obtain ⟨ f, hf_mono, hf_eq ⟩ := h_subseq; specialize h_convex_indep; simp_all +decide [ ConvexIndependent ] ;
                intro s x hx; specialize h_convex_indep ( f '' s ) ( f x ) ; simp_all +decide [ Set.image_image ] ;
                exact hf_mono.injective h_convex_indep.choose_spec.2 ▸ h_convex_indep.choose_spec.1;
              exact h_convex_indep;
            have h_convex_indep : ¬ Collinear ℝ {A p, A y, A q} := by
              have := convexIndependent_no_three_collinear h_convex_indep ( show ( 0 : Fin 3 ) ≠ 1 from by decide ) ( show ( 1 : Fin 3 ) ≠ 2 from by decide ) ( show ( 0 : Fin 3 ) ≠ 2 from by decide ) ; simp_all +decide ;
            contrapose! h_convex_indep;
            rw [ collinear_iff_exists_forall_eq_smul_vadd ];
            rw [ segment_eq_image ] at h_convex_indep;
            obtain ⟨ θ, hθ, hθ' ⟩ := h_convex_indep;
            use A p, A q - A p;
            simp_all +decide [ sub_smul, smul_sub ];
            exact ⟨ ⟨ 0, by simp +decide ⟩, ⟨ θ, by rw [ ← hθ' ] ; abel1 ⟩, ⟨ 1, by simp +decide ⟩ ⟩
          exact ⟨hK_PX, fun hK_eq_Ay => hK_ne_Ay <| hK_eq_Ay ▸ hK_YQ⟩
        rw [ EuclideanGeometry.angle_comm ];
        rw [ EuclideanGeometry.angle, EuclideanGeometry.angle ];
        rw [ segment_eq_image ] at h_ray;
        obtain ⟨ ⟨ θ, hθ, rfl ⟩, hK_ne ⟩ := h_ray;
        rw [ show ( 1 - θ ) • A p' + θ • A y -ᵥ A y = ( 1 - θ ) • ( A p' -ᵥ A y ) by simp +decide [ sub_smul, smul_sub ] ; abel1 ];
        rw [ InnerProductGeometry.angle_smul_right_of_pos ];
        exact sub_pos_of_lt ( lt_of_le_of_ne hθ.2 ( by aesop_cat ) );
      rw [ h_angle_eq, EuclideanGeometry.angle_comm ];
      rw [ EuclideanGeometry.angle_comm K ( A y ) ( A q ), EuclideanGeometry.angle_comm ( A p ) ( A y ) ( A q ) ] ; exact h_angle_le;
    · grind;
  -- Apply the generalized angle nesting lemma to get the second inequality.
  have h_angle_q' : EuclideanGeometry.angle (A p') (A y) (A q') ≤ EuclideanGeometry.angle (A p') (A y) (A q) := by
    by_cases h_cases : p' < y ∧ y < q ∧ q < q' ∧ q' < n;
    · -- By the properties of the convex polygon, the diagonals $A_{p'} A_q$ and $A_y A_{q'}$ intersect at some point $L$.
      obtain ⟨L, hL⟩ : ∃ L, L ∈ segment ℝ (A p') (A q) ∧ L ∈ segment ℝ (A y) (A q') := by
        apply convex_polygon_diagonals_intersect h_convex h_cases.left h_cases.right.left h_cases.right.right.left h_cases.right.right.right;
      have h_angle_L : EuclideanGeometry.angle (A p') (A y) L ≤ EuclideanGeometry.angle (A p') (A y) (A q) := by
        apply angle_le_of_mem_segment hL.left;
        have h_not_collinear : ¬ Collinear ℝ {A p', A y, A q} := by
          have h_not_collinear : ConvexIndependent ℝ (fun i : Fin n => A i) := by
            exact h_convex.2.2.1;
          have h_not_collinear : ¬ Collinear ℝ {A p', A y, A q} := by
            have h_convex_indep : ConvexIndependent ℝ (fun i : Fin n => A i) := h_not_collinear
            have h_distinct : p' < n ∧ y < n ∧ q < n := by
              grind
            convert convexIndependent_no_three_collinear h_convex_indep ( show ( ⟨ p', h_distinct.1 ⟩ : Fin n ) ≠ ⟨ y, h_distinct.2.1 ⟩ from by simpa [ Fin.ext_iff ] using by linarith ) ( show ( ⟨ y, h_distinct.2.1 ⟩ : Fin n ) ≠ ⟨ q, h_distinct.2.2 ⟩ from by simpa [ Fin.ext_iff ] using by linarith ) ( show ( ⟨ p', h_distinct.1 ⟩ : Fin n ) ≠ ⟨ q, h_distinct.2.2 ⟩ from by simpa [ Fin.ext_iff ] using by linarith ) using 1;
          exact h_not_collinear;
        contrapose! h_not_collinear;
        rw [ collinear_iff_exists_forall_eq_smul_vadd ];
        obtain ⟨ a, b, ha, hb, hab, h ⟩ := h_not_collinear;
        use A p', A q - A p';
        simp +decide [ ← h];
        exact ⟨ ⟨ b, by rw [ show a = 1 - b by linarith ] ; simp +decide [ sub_smul, smul_sub ] ; abel1 ⟩, ⟨ 1, by simp +decide ⟩ ⟩;
      have h_angle_L_eq : EuclideanGeometry.angle (A p') (A y) L = EuclideanGeometry.angle (A p') (A y) (A q') := by
        rw [ EuclideanGeometry.angle, EuclideanGeometry.angle ];
        obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hL.2;
        rw [ show a • A y + b • A q' -ᵥ A y = b • ( A q' -ᵥ A y ) by
              simp +decide [ sub_eq_add_neg, smul_add, smul_neg, ← eq_sub_iff_add_eq' ];
              rw [ show a = 1 - b by linarith ] ; simp +decide [ sub_smul ] ; abel1 ];
        by_cases hb : b = 0 <;> simp_all +decide [ InnerProductGeometry.angle ];
        · have h_collinear : Collinear ℝ {A p', A y, A q} := by
            rw [ collinear_iff_exists_forall_eq_smul_vadd ];
            use A p', A q - A p';
            simp +decide [ segment_eq_image ] at hL ⊢;
            exact ⟨ by obtain ⟨ x, hx, hx' ⟩ := hL.1; exact ⟨ x, by rw [ ← hx' ] ; simp +decide [ sub_smul, smul_sub ] ; abel1 ⟩, ⟨ 1, by simp +decide ⟩ ⟩;
          have h_convex_indep : ConvexIndependent ℝ (fun i : Fin n => A i) := by
            exact h_convex.2.2.1;
          have := convexIndependent_no_three_collinear h_convex_indep ( show ( ⟨ p', by linarith ⟩ : Fin n ) ≠ ⟨ y, by linarith ⟩ from by simpa [ Fin.ext_iff ] using by linarith ) ( show ( ⟨ y, by linarith ⟩ : Fin n ) ≠ ⟨ q, by linarith ⟩ from by simpa [ Fin.ext_iff ] using by linarith ) ( show ( ⟨ p', by linarith ⟩ : Fin n ) ≠ ⟨ q, by linarith ⟩ from by simpa [ Fin.ext_iff ] using by linarith ) ; simp_all +decide [ collinear_iff_exists_forall_eq_smul_vadd ] ;
        · simp +decide [ inner_smul_right, norm_smul];
          rw [ abs_of_nonneg ‹0 ≤ b› ] ; rw [ mul_div_mul_comm ] ; ring_nf;
          simp +decide [ mul_assoc, mul_comm b, hb ];
      exact h_angle_L_eq ▸ h_angle_L;
    · cases eq_or_lt_of_le hqq' <;> simp_all +decide [ EuclideanGeometry.angle ];
      linarith
  exact h_angle_q'.trans h_angle_p'

/--
Strict version of angle nesting for convex polygons:
If p' ≤ p < y < q ≤ q' and at least one endpoint is strictly nested, then the angle is strictly larger.
Proven by Aristotle (kinda impressed by this one, Gemini was trying to make a super
long and convoluted proof work, and Aristotle just made this one)
-/
lemma angle_eq_of_mem_segment
    {O A B K : V} (hK : K ∈ segment ℝ A B) (hO : O ∉ segment ℝ A B) :
    EuclideanGeometry.angle A O B = EuclideanGeometry.angle A O K + EuclideanGeometry.angle K O B := by
  convert ( EuclideanGeometry.angle_add_of_ne_of_ne _ _ _ ) |> Eq.symm;
  · exact fun h => hO ( h.symm ▸ left_mem_segment _ _ _ );
  · exact fun h => hO <| h.symm ▸ right_mem_segment _ _ _;
  · -- By definition of segment, we know that K lies on the line segment AB.
    apply (mem_segment_iff_wbtw).mp hK

/--
Strict version of angle nesting for convex polygons:
If p' ≤ p < y < q ≤ q' and at least one endpoint is strictly nested, then the angle is strictly larger.
-/
lemma angle_nesting_convex_strict {A : ℕ → V} {n : ℕ} (h_convex : IsConvexPolygon A n)
    {p p' y q q' : ℕ} (hp'p : p' ≤ p) (hpy : p < y) (hyq : y < q) (hqq' : q ≤ q') (hq'n : q' < n)
    (h_not_eq : p' < p ∨ q < q') :
    ∠ (A p) (A y) (A q) > ∠ (A p') (A y) (A q') := by
  -- Define Fin n elements at the top level
  let ip' : Fin n := ⟨p', by linarith [hqq', hq'n, hp'p, hpy, hyq]⟩
  let ip  : Fin n := ⟨p, by linarith [hqq', hq'n, hpy, hyq]⟩
  let iy  : Fin n := ⟨y, by linarith [hqq', hq'n, hyq]⟩
  let iq  : Fin n := ⟨q, by linarith [hqq', hq'n]⟩
  let iq' : Fin n := ⟨q', hq'n⟩

  -- Common distinctness proofs from hypothesis
  have h_ip_ne_iy : ip ≠ iy := by simp [ip, iy]; linarith
  have h_iy_ne_iq : iy ≠ iq := by simp [iy, iq]; linarith
  have h_ip_ne_iq : ip ≠ iq := by simp [ip, iq]; linarith
  have h_ip'_ne_iy : ip' ≠ iy := by simp [ip', iy]; linarith
  have h_iy_ne_iq' : iy ≠ iq' := by simp [iy, iq']; linarith

  -- First, we know the weak inequality holds
  have h_le : ∠ (A p') (A y) (A q') ≤ ∠ (A p) (A y) (A q) :=
    angle_nesting_convex h_convex hp'p hpy hyq hqq' hq'n

  -- We need to show they are not equal
  by_contra h_not_gt
  have h_eq : ∠ (A p') (A y) (A q') = ∠ (A p) (A y) (A q) := by
    linarith [h_le, le_of_not_gt h_not_gt]

  -- Split into two cases: strict nesting on left (p' < p) or right (q < q')
  cases h_not_eq with
  | inl h_p_strict =>
    have h_col : Collinear ℝ {A p', A p, A y} := by
      -- p' < p < y < q < n
      obtain ⟨K, hK_P'Y, hK_PQ⟩ : ∃ K : V, K ∈ segment ℝ (A p') (A y) ∧ K ∈ segment ℝ (A p) (A q) := by
        have hqn : q < n := lt_of_le_of_lt hqq' hq'n
        apply convex_polygon_diagonals_intersect h_convex h_p_strict hpy hyq hqn

      have h_not_col_y_pq : ¬Collinear ℝ {A y, A p, A q} := by
        have h_ip_ne_iy : ip ≠ iy := by simp [ip, iy]; linarith
        have h_ip_ne_iq : ip ≠ iq := by simp [ip, iq]; linarith
        have h_iy_ne_iq : iy ≠ iq := by simp [iy, iq]; linarith
        have := convexIndependent_no_three_collinear h_convex.2.2.1 h_ip_ne_iy.symm h_ip_ne_iq h_iy_ne_iq
        simp [ip, iy, iq] at this; exact this

      have hK_ne_y : K ≠ A y := by
        intro h; rw [h] at hK_PQ
        have h_col_y_pq : Collinear ℝ {A y, A p, A q} :=
          collinear_insert_of_mem_affineSpan_pair (convexHull_min (subset_affineSpan ℝ {A p, A q}) (affineSpan ℝ {A p, A q}).convex (by simpa [convexHull_pair] using hK_PQ))
        exact h_not_col_y_pq (h_col_y_pq.subset (by simp))

      have h_ray_eq : ∠ K (A y) (A q) = ∠ (A p') (A y) (A q) := by
        rw [segment_eq_image] at hK_P'Y
        rcases hK_P'Y with ⟨t, ⟨ht0, ht1⟩, h_eq_K⟩
        have ht_ne_1 : t ≠ 1 := by
          intro h; rw [h] at h_eq_K; dsimp at h_eq_K; simp at h_eq_K; exact hK_ne_y h_eq_K.symm
        have h_1_minus_t_pos : 0 < 1 - t := sub_pos_of_lt (lt_of_le_of_ne ht1 ht_ne_1)
        have h_K_vsub : K -ᵥ A y = (1 - t) • (A p' -ᵥ A y) := by
          dsimp at h_eq_K; rw [← h_eq_K]; dsimp; simp [sub_smul, smul_sub]; abel1
        rw [EuclideanGeometry.angle, EuclideanGeometry.angle, h_K_vsub]
        rw [InnerProductGeometry.angle_smul_left_of_pos _ _ h_1_minus_t_pos]

      have h_angle_split : ∠ (A p) (A y) (A q) = ∠ (A p) (A y) K + ∠ K (A y) (A q) := by
        apply angle_eq_of_mem_segment hK_PQ
        intro h; rw [segment_symm] at h
        have h_col_y_pq : Collinear ℝ {A y, A p, A q} :=
          collinear_insert_of_mem_affineSpan_pair (convexHull_min (subset_affineSpan ℝ {A p, A q}) (affineSpan ℝ {A p, A q}).convex (by rw [segment_symm] at h; simpa [convexHull_pair] using h))
        exact h_not_col_y_pq (h_col_y_pq.subset (by simp))

      have h_intermediate_eq : ∠ (A p) (A y) (A q) = ∠ (A p') (A y) (A q) := by
        have h1 : ∠ (A p') (A y) (A q) ≤ ∠ (A p) (A y) (A q) :=
          angle_nesting_convex h_convex hp'p hpy hyq (le_refl q) (lt_of_le_of_lt hqq' hq'n)
        have h2 : ∠ (A p') (A y) (A q') ≤ ∠ (A p') (A y) (A q) :=
          angle_nesting_convex h_convex (le_refl p') (hp'p.trans_lt hpy) hyq hqq' hq'n
        linarith [h_eq, h1, h2]

      have h_zero : ∠ (A p) (A y) K = 0 := by linarith [h_angle_split, h_ray_eq, h_intermediate_eq]

      have h_p_mem : A p ∈ affineSpan ℝ {A p', A y} := by
        have hyn : y < n := hyq.trans (hqq'.trans_lt hq'n)
        have h_Ap_ne_Ay : A p ≠ A y := mt (h_convex.2.1 p y (hpy.trans hyn) hyn) (by simp [ip, iy] at h_ip_ne_iy; exact h_ip_ne_iy)
        have h_col_pyk : Collinear ℝ {A p, A y, K} := by
          rw [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi]
          simp [h_zero]
        have h_p_in_yk : A p ∈ affineSpan ℝ {A y, K} :=
          h_col_pyk.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hK_ne_y.symm
        have hK_in_py : K ∈ affineSpan ℝ {A p', A y} :=
           convexHull_min (subset_affineSpan ℝ {A p', A y}) (affineSpan ℝ {A p', A y}).convex (by simpa [convexHull_pair] using hK_P'Y)
        have h_sub : affineSpan ℝ {A y, K} ≤ affineSpan ℝ {A p', A y} := by
          apply affineSpan_le.mpr; intro x hx; simp at hx; rcases hx with rfl | rfl
          · exact subset_affineSpan ℝ _ (by simp)
          · exact hK_in_py
        exact h_sub h_p_in_yk

      have h_subset : ({A p', A p, A y} : Set V) ⊆ insert (A p) {A p', A y} := by
        intro z hz; simp at hz ⊢; tauto
      exact (collinear_insert_of_mem_affineSpan_pair h_p_mem).subset h_subset

    have h_ip'_ne_ip : ip ≠ ip' := by simp [ip, ip']; linarith
    have h_not_col_p'_p_y : ¬Collinear ℝ {A p', A p, A y} := by
      have := convexIndependent_no_three_collinear h_convex.2.2.1 h_ip'_ne_ip.symm h_ip_ne_iy h_ip'_ne_iy
      simp [ip', ip, iy] at this; exact this
    exact h_not_col_p'_p_y h_col

  | inr h_strict =>
    have h_col : Collinear ℝ {A q, A q', A y} := by
      obtain ⟨L, hL_PQ, hL_YQ'⟩ : ∃ L : V, L ∈ segment ℝ (A p) (A q) ∧ L ∈ segment ℝ (A y) (A q') := by
        apply convex_polygon_diagonals_intersect h_convex hpy hyq h_strict hq'n

      have h_not_col_y_pq : ¬Collinear ℝ {A y, A p, A q} := by
        have h_ip_ne_iy : ip ≠ iy := by simp [ip, iy]; linarith
        have h_ip_ne_iq : ip ≠ iq := by simp [ip, iq]; linarith
        have h_iy_ne_iq : iy ≠ iq := by simp [iy, iq]; linarith
        have := convexIndependent_no_three_collinear h_convex.2.2.1 h_ip_ne_iy.symm h_ip_ne_iq h_iy_ne_iq
        simp [ip, iy, iq] at this; exact this

      have hL_ne_y : L ≠ A y := by
        intro h; rw [h] at hL_PQ
        have h_col_y_pq : Collinear ℝ {A y, A p, A q} :=
          collinear_insert_of_mem_affineSpan_pair (convexHull_min (subset_affineSpan ℝ {A p, A q}) (affineSpan ℝ {A p, A q}).convex (by simpa [convexHull_pair] using hL_PQ))
        exact h_not_col_y_pq (h_col_y_pq.subset (by simp))

      have h_ray_eq_L_q_q' : ∠ L (A y) (A q) = ∠ (A q') (A y) (A q) := by
        rw [segment_eq_image] at hL_YQ'
        rcases hL_YQ' with ⟨t, ⟨ht0, ht1⟩, h_eq_L⟩
        have ht_ne_0 : t ≠ 0 := by intro h; rw [h] at h_eq_L; dsimp at h_eq_L; simp at h_eq_L; exact hL_ne_y h_eq_L.symm
        have h_t_pos : 0 < t := lt_of_le_of_ne ht0 ht_ne_0.symm
        have h_L_vsub : L -ᵥ A y = t • (A q' -ᵥ A y) := by
          dsimp at h_eq_L; rw [← h_eq_L]; dsimp; simp [sub_smul, smul_sub]; abel1
        rw [EuclideanGeometry.angle, EuclideanGeometry.angle, h_L_vsub]
        rw [InnerProductGeometry.angle_smul_left_of_pos _ _ h_t_pos]

      have h_p_y_q_eq_q_prime : ∠ (A p) (A y) L = ∠ (A p) (A y) (A q') := by
        rw [segment_eq_image] at hL_YQ'
        rcases hL_YQ' with ⟨t, ⟨ht0, ht1⟩, h_eq_L⟩
        have ht_ne_0 : t ≠ 0 := by intro h; rw [h] at h_eq_L; dsimp at h_eq_L; simp at h_eq_L; exact hL_ne_y h_eq_L.symm
        have h_t_pos : 0 < t := lt_of_le_of_ne ht0 ht_ne_0.symm
        have h_L_vsub : L -ᵥ A y = t • (A q' -ᵥ A y) := by
          dsimp at h_eq_L; rw [← h_eq_L]; dsimp; simp [sub_smul, smul_sub]; abel1
        rw [EuclideanGeometry.angle, EuclideanGeometry.angle, h_L_vsub]
        rw [InnerProductGeometry.angle_smul_right_of_pos _ _ h_t_pos]

      have h_angle_split : ∠ (A p) (A y) (A q) = ∠ (A p) (A y) L + ∠ L (A y) (A q) := by
        apply angle_eq_of_mem_segment hL_PQ
        intro h; rw [segment_symm] at h
        have h_col_y_pq : Collinear ℝ {A y, A p, A q} :=
          collinear_insert_of_mem_affineSpan_pair (convexHull_min (subset_affineSpan ℝ {A p, A q}) (affineSpan ℝ {A p, A q}).convex (by rw [segment_symm] at h; simpa [convexHull_pair] using h))
        exact h_not_col_y_pq (h_col_y_pq.subset (by simp))

      have h_eq_nest : ∠ (A p) (A y) (A q) = ∠ (A p) (A y) (A q') := by
        have hyn : y < n := hyq.trans (hqq'.trans_lt hq'n)
        have h1 : ∠ (A p') (A y) (A q') ≤ ∠ (A p) (A y) (A q') :=
          angle_nesting_convex h_convex hp'p hpy (hyq.trans_le hqq') (le_refl q') hq'n
        have h2 : ∠ (A p) (A y) (A q') ≤ ∠ (A p) (A y) (A q) :=
          angle_nesting_convex h_convex (le_refl p) hpy hyq hqq' hq'n
        linarith [h_eq, h1, h2]

      have h_zero : ∠ (A q') (A y) (A q) = 0 := by linarith [h_angle_split, h_ray_eq_L_q_q', h_p_y_q_eq_q_prime, h_eq_nest]

      have h_q_mem : A q ∈ affineSpan ℝ {A y, A q'} := by
        have hyn : y < n := hyq.trans (hqq'.trans_lt hq'n)
        have hqn : q < n := hqq'.trans_lt hq'n
        have h_Aq'_ne_Ay : A q' ≠ A y := mt (h_convex.2.1 q' y hq'n hyn) (by linarith)
        have h_Aq_ne_Ay : A q ≠ A y := mt (h_convex.2.1 q y hqn hyn) (by linarith)
        have h_col_qyq' : Collinear ℝ {A q, A y, A q'} := by
          rw [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi]
          right; right; left
          rw [EuclideanGeometry.angle_comm]
          exact h_zero
        exact h_col_qyq'.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) h_Aq'_ne_Ay.symm

      have h_subset : ({A q, A q', A y} : Set V) ⊆ insert (A q) {A y, A q'} := by
        intro z hz; simp at hz ⊢; tauto
      exact (collinear_insert_of_mem_affineSpan_pair h_q_mem).subset h_subset

    have h_iq_ne_iq' : (⟨q, hqq'.trans_lt hq'n⟩ : Fin n) ≠ ⟨q', hq'n⟩ := by intro h; simp at h; linarith
    have h_not_col_q_q'_y : ¬Collinear ℝ {A q, A q', A y} := by
      have hyn : y < n := hyq.trans (hqq'.trans_lt hq'n)
      have h_iq_ne_iy : (⟨q, hqq'.trans_lt hq'n⟩ : Fin n) ≠ ⟨y, hyn⟩ := by intro h; simp at h; linarith
      have h_iq'_ne_iy : (⟨q', hq'n⟩ : Fin n) ≠ ⟨y, hyn⟩ := by intro h; simp at h; linarith
      have := convexIndependent_no_three_collinear h_convex.2.2.1 h_iq_ne_iq' h_iq'_ne_iy h_iq_ne_iy
      simp at this; exact this
    exact h_not_col_q_q'_y h_col


/-
If A, B, C are not collinear and the angle at B is greater than π/3, then AC is strictly greater than AB or AC is strictly greater than BC.
stated and proven by Aristotle
-/
lemma dist_lt_of_angle_gt_pi_div_three_of_not_collinear {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Fact (Module.finrank ℝ V = 2)]
    {A B C : V}
    (h_nc : ¬Collinear ℝ {A, B, C})
    (h_angle : EuclideanGeometry.angle A B C > Real.pi / 3) :
    dist A B < dist A C ∨ dist C B < dist A C := by
      -- By the Law of Cosines, we have $AC^2 = AB^2 + BC^2 - 2 \cdot AB \cdot BC \cdot \cos(\angle ABC)$.
      have h_cos : dist A C ^ 2 = dist A B ^ 2 + dist C B ^ 2 - 2 * dist A B * dist C B * Real.cos (EuclideanGeometry.angle A B C) := by
        rw [ EuclideanGeometry.angle, dist_eq_norm, dist_eq_norm, dist_eq_norm ];
        rw [ show A - C = ( A - B ) - ( C - B ) by abel1, norm_sub_sq_real ];
        rw [ InnerProductGeometry.cos_angle ] ; ring_nf;
        by_cases h : ‖A - B‖ = 0 <;> by_cases h' : ‖C - B‖ = 0 <;> simp_all +decide [ mul_comm, mul_left_comm ] ; ring!;
      -- Since $\cos(\angle ABC) < \cos(\pi/3) = 1/2$, we have $AC^2 > AB^2 + BC^2 - AB \cdot BC$.
      have h_cos_lt : Real.cos (EuclideanGeometry.angle A B C) < 1 / 2 := by
        rw [ ← Real.cos_pi_div_three ] ; exact Real.cos_lt_cos_of_nonneg_of_le_pi ( by linarith [ Real.pi_pos, EuclideanGeometry.angle_nonneg A B C ] ) ( by linarith [ Real.pi_pos, EuclideanGeometry.angle_le_pi A B C ] ) h_angle;
      contrapose! h_cos_lt;
      nlinarith [ show 0 < Dist.dist A B * Dist.dist C B by exact mul_pos ( dist_pos.mpr ( show A ≠ B by rintro rfl; exact h_nc <| by simp +decide [ collinear_pair ] ) ) ( dist_pos.mpr ( show C ≠ B by rintro rfl; exact h_nc <| by simp +decide [ collinear_pair ] ) ), sq_nonneg ( Dist.dist A B - Dist.dist C B ), dist_pos.mpr ( show A ≠ C by rintro rfl; exact h_nc <| by simp +decide [ collinear_pair ] ) ]

/-
If A, B, C are collinear and A ≠ C, and the angle at B is > π/3, then AC is strictly greater than AB or BC.
stated and proven by Aristotle
-/
lemma dist_lt_of_angle_gt_pi_div_three_of_collinear {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Fact (Module.finrank ℝ V = 2)]
    {A B C : V}
    (h_col : Collinear ℝ {A, B, C})
    (h_ne : A ≠ C)
    (h_angle : EuclideanGeometry.angle A B C > Real.pi / 3) :
    dist A B < dist A C ∨ dist C B < dist A C := by
      -- Since A, B, C are collinear and A ≠ C, B must be either strictly between A and C or distinct from A and C.
      by_cases hStrBet : B ∈ segment ℝ A C;
      · -- Since $B$ is strictly between $A$ and $C$, the line segment $AB$ is a proper subset of $AC$, and thus $dist A B < dist A C$.
        have h_dist_strict : dist A C = dist A B + dist B C := by
          exact Eq.symm (dist_add_dist_of_mem_segment hStrBet);
        contrapose! h_angle; simp_all +decide [ EuclideanGeometry.angle ] ;
        simp_all +decide [ dist_comm ];
      · -- Since B is not strictly between A and C, there exists a t ∈ ℝ such that B = (1-t)A + tC and either t < 0 or t > 1.
        obtain ⟨t, ht⟩ : ∃ t : ℝ, B = (1 - t) • A + t • C ∧ (t < 0 ∨ t > 1) := by
          -- Since B is collinear with A and C, there exists a scalar t such that B = A + t(C - A).
          obtain ⟨t, ht⟩ : ∃ t : ℝ, B = A + t • (C - A) := by
            rw [ collinear_iff_exists_forall_eq_smul_vadd ] at h_col;
            obtain ⟨ p₀, v, h ⟩ := h_col;
            obtain ⟨ r₁, hr₁ ⟩ := h A ( by simp +decide ) ; obtain ⟨ r₂, hr₂ ⟩ := h B ( by simp +decide ) ; obtain ⟨ r₃, hr₃ ⟩ := h C ( by simp +decide ) ; simp_all +decide [ add_comm, add_assoc ];
            refine' ⟨ ( r₂ - r₁ ) / ( r₃ - r₁ ), _ ⟩;
            simp +decide [ ← smul_assoc, ← sub_smul, div_eq_inv_mul ];
            rw [ inv_mul_eq_div, div_mul_cancel₀ _ ( sub_ne_zero_of_ne <| by aesop ) ] ; simp +decide [ sub_smul ];
          refine' ⟨ t, _, _ ⟩ <;> simp_all +decide [ segment_eq_image ];
          · simp +decide [ sub_smul, smul_sub ] ; abel1;
          · exact Classical.or_iff_not_imp_left.2 fun h => not_le.1 fun h' => hStrBet t ( by linarith ) ( by linarith ) ( by simp +decide [ sub_smul, smul_sub ] ; abel1 );
        -- Since $B$ is not strictly between $A$ and $C$, we have $\angle ABC = 0$.
        have h_angle_zero : EuclideanGeometry.angle A B C = 0 := by
          simp_all +decide [ EuclideanGeometry.angle ];
          rw [ InnerProductGeometry.angle_eq_zero_iff ];
          refine' ⟨ _, _ ⟩;
          · intro h;
            rw [ sub_eq_zero ] at h;
            rw [ eq_comm ] at h;
            simp_all +decide [ sub_smul ];
            exact hStrBet ( left_mem_segment _ _ _ );
          · cases' ht.2 with ht₂ ht₂ <;> [ refine' ⟨ - ( 1 - t ) / t, _, _ ⟩ ; refine' ⟨ ( t - 1 ) / t, _, _ ⟩ ] <;> simp_all +decide [ div_eq_inv_mul, sub_smul, smul_sub ];
            · nlinarith [ inv_mul_cancel₀ ( ne_of_lt ht₂ ) ];
            · simp +decide [ sub_mul, mul_sub, ht₂.ne, smul_smul ];
              simp +decide [ sub_smul ] ; abel_nf;
            · linarith;
            · simp +decide [ sub_smul, mul_sub, ne_of_gt ( zero_lt_one.trans ht₂ ) ] ; abel_nf;
        linarith [ Real.pi_pos ]

/-
If A ≠ C and the angle at B is greater than π/3, then AC is strictly greater than AB or BC.
stated and proven by Aristotle (originally had false version and it stated
this true version instead)
-/
lemma dist_lt_of_angle_gt_pi_div_three_of_ne {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Fact (Module.finrank ℝ V = 2)]
    {A B C : V}
    (h_angle : EuclideanGeometry.angle A B C > Real.pi / 3)
    (h_ne : A ≠ C) :
    dist A B < dist A C ∨ dist C B < dist A C := by
      by_cases h_collinear : Collinear ℝ { A, B, C };
      · apply dist_lt_of_angle_gt_pi_div_three_of_collinear h_collinear h_ne h_angle;
      · convert dist_lt_of_angle_gt_pi_div_three_of_not_collinear h_collinear h_angle using 1


/--
In a triangle ABC, if side AC > side BC, then angle ABC > angle BAC.
(Strict inequality version) (proven by Aristotle)
-/
lemma angle_gt_of_dist_gt {A B C : V} (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C)
    (h_not_col : ¬Collinear ℝ {A, B, C}) (h : dist A C > dist B C) :
    EuclideanGeometry.angle A B C > EuclideanGeometry.angle B A C := by
  -- By the Law of Cosines, since $AC > BC$, we have $\cos(\angle ABC) < \cos(\angle BAC)$.
  have h_cos : Real.cos (EuclideanGeometry.angle A B C) < Real.cos (EuclideanGeometry.angle B A C) := by
    simp_all +decide [ EuclideanGeometry.angle, dist_eq_norm ];
    simp_all +decide [ InnerProductGeometry.cos_angle, norm_sub_rev ];
    -- By simplifying the inner products and using the fact that ‖B - C‖ < ‖A - C‖, we can show that the left-hand side is less than the right-hand side.
    have h_inner : ⟪A - B, C - B⟫_ℝ = (‖A - B‖^2 + ‖C - B‖^2 - ‖A - C‖^2) / 2 ∧ ⟪B - A, C - A⟫_ℝ = (‖B - A‖^2 + ‖C - A‖^2 - ‖B - C‖^2) / 2 := by
      norm_num [ @norm_sub_sq ℝ, inner_sub_left, inner_sub_right ] ; ring_nf;
      simp +decide [ real_inner_comm, real_inner_self_eq_norm_sq ] ; ring_nf ; norm_num;
    rw [ h_inner.1, h_inner.2, div_lt_div_iff₀ ];
    · simp_all +decide [ norm_sub_rev ];
      -- By simplifying, we can see that the inequality holds because ‖B - C‖ < ‖A - C‖.
      have h_simplified : (‖A - B‖^2 + ‖B - C‖^2 - ‖A - C‖^2) * ‖A - C‖ < (‖A - B‖^2 + ‖A - C‖^2 - ‖B - C‖^2) * ‖B - C‖ := by
        have h_simplified : ‖A - B‖^2 < (‖A - C‖ + ‖B - C‖)^2 := by
          have h_simplified : ‖A - B‖ < ‖A - C‖ + ‖B - C‖ := by
            rw [ show A - B = ( A - C ) - ( B - C ) by abel1, norm_sub_rev ];
            rw [ norm_sub_rev ];
            refine' lt_of_le_of_ne ( norm_sub_le _ _ ) _;
            intro h;
            have h_collinear : ∃ t : ℝ, A - C = t • (B - C) := by
              have h_collinear : ‖A - C - (B - C)‖^2 = ‖A - C‖^2 + ‖B - C‖^2 + 2 * ‖A - C‖ * ‖B - C‖ := by
                rw [ h, add_sq ] ; ring;
              have h_collinear : ‖A - C - (B - C)‖^2 = ‖A - C‖^2 + ‖B - C‖^2 - 2 * inner ℝ (A - C) (B - C) := by
                rw [ @norm_sub_sq ℝ ];
                norm_num ; ring;
              have h_collinear : inner ℝ (A - C) (B - C) = -‖A - C‖ * ‖B - C‖ := by
                linarith;
              have h_collinear : ‖A - C + (‖A - C‖ / ‖B - C‖) • (B - C)‖^2 = 0 := by
                rw [ @norm_add_sq ℝ ];
                simp_all +decide [ norm_smul, inner_smul_right ];
                -- Combine like terms and simplify the expression.
                field_simp
                ring_nf;
                rw [ mul_assoc, mul_inv_cancel₀ ( norm_ne_zero_iff.mpr ( sub_ne_zero.mpr hBC ) ), mul_one, sub_self ];
              exact ⟨ - ( ‖A - C‖ / ‖B - C‖ ), by simpa [ neg_smul ] using eq_neg_of_add_eq_zero_left ( norm_eq_zero.mp ( sq_eq_zero_iff.mp h_collinear ) ) ⟩;
            obtain ⟨ t, ht ⟩ := h_collinear;
            refine' h_not_col _;
            rw [ collinear_iff_exists_forall_eq_smul_vadd ];
            exact ⟨ C, B - C, fun p hp => by rcases hp with ( rfl | rfl | rfl ) <;> [ exact ⟨ t, by simpa [ sub_eq_iff_eq_add ] using ht ⟩ ; exact ⟨ 1, by simp +decide ⟩ ; exact ⟨ 0, by simp +decide ⟩ ] ⟩;
          gcongr;
        nlinarith [ mul_pos ( sub_pos.mpr h ) ( norm_pos_iff.mpr ( sub_ne_zero.mpr hBC ) ), mul_pos ( sub_pos.mpr h ) ( norm_pos_iff.mpr ( sub_ne_zero.mpr hAC ) ), mul_pos ( norm_pos_iff.mpr ( sub_ne_zero.mpr hBC ) ) ( norm_pos_iff.mpr ( sub_ne_zero.mpr hAC ) ) ];
      nlinarith [ norm_pos_iff.mpr ( sub_ne_zero.mpr hAB ) ];
    · exact mul_pos ( norm_pos_iff.mpr ( sub_ne_zero.mpr hAB ) ) ( norm_pos_iff.mpr ( sub_ne_zero.mpr hBC ) );
    · exact mul_pos ( norm_pos_iff.mpr ( sub_ne_zero.mpr hAB ) ) ( norm_pos_iff.mpr ( sub_ne_zero.mpr hAC ) );
  exact not_le.mp fun h_le => h_cos.not_ge <| Real.cos_le_cos_of_nonneg_of_le_pi ( by linarith [ Real.pi_pos, EuclideanGeometry.angle_nonneg A B C, EuclideanGeometry.angle_nonneg B A C ] ) ( by linarith [ Real.pi_pos, EuclideanGeometry.angle_le_pi A B C, EuclideanGeometry.angle_le_pi B A C ] ) h_le

/--
In a triangle ABC, if side AC ≥ side BC, then angle ABC ≥ angle BAC.
(Strict inequality version) (proven by Aristotle)
-/
lemma angle_ge_of_dist_ge {A B C : V} (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C)
    (h_not_col : ¬Collinear ℝ {A, B, C}) (h : dist A C ≥ dist B C) :
    EuclideanGeometry.angle A B C ≥ EuclideanGeometry.angle B A C := by
  have h_not_col' : ¬Collinear ℝ ({C, B, A} : Set V) := by
    have hset : ({C, B, A} : Set V) = {A, B, C} := by
      ext x
      simp
      tauto
    intro hc
    exact h_not_col (hset ▸ hc)
  have hdist : dist C B ≤ dist C A := by
    simpa [dist_comm] using h
  have hangle :=
    (EuclideanGeometry.angle_le_iff_dist_le (a := C) (b := B) (c := A) h_not_col').2 hdist
  simpa [EuclideanGeometry.angle_comm] using hangle

/--
The sum of angles in a non-degenerate triangle is π.
This is a specialization of `EuclideanGeometry.angle_add_angle_add_angle_eq_pi`
to avoid timeouts during elaboration in complex contexts.
-/
lemma triangle_angle_sum_eq_pi (a b c : V) (h : b ≠ a) :
    EuclideanGeometry.angle a b c +
      EuclideanGeometry.angle b c a +
      EuclideanGeometry.angle c a b = Real.pi := by
  exact angle_add_angle_add_angle_eq_pi c h

/-- Helper: If B lies strictly between A and C, then angle D A B = angle D A C. (proven by Aristotle) -/
lemma angle_eq_of_between {a b c d : V} (h : Sbtw ℝ a b c) :
    ∠ d a b = ∠ d a c := by
  obtain ⟨ s, hs ⟩ := h;
  obtain ⟨ u, v, hv ⟩ := s; simp_all +decide [ EuclideanGeometry.angle ] ;
  simp +decide [ ← hv, AffineMap.lineMap_apply ];
  rw [ InnerProductGeometry.angle_smul_right_of_pos ] ; cases lt_or_eq_of_le v.1 <;> aesop

/-- Helper: If D lies strictly between A and B, then angle C D A + angle C D B = π. (proven by Aristotle) -/
lemma angle_add_eq_pi_of_between {a b c d : V} (h : Sbtw ℝ a d b) (hc : d ≠ c) :
    EuclideanGeometry.angle c d a + EuclideanGeometry.angle c d b = Real.pi := by
  -- Since $d$ is strictly between $a$ and $b$, the line through $a$ and $b$ is the same as the line through $d$ and $b$.
  have h_line : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ d = (1 - t) • a + t • b := by
    obtain ⟨ t, ht ⟩ := h;
    obtain ⟨ t, ht ⟩ := t;
    cases lt_or_eq_of_le ht.1.1 <;> cases lt_or_eq_of_le ht.1.2 <;> simp_all +decide [ AffineMap.lineMap_apply ];
    · exact ⟨ t, by linarith, by linarith, by rw [ ← ht.2 ] ; simp +decide [ sub_smul, smul_sub ] ; abel1 ⟩;
    · aesop;
  obtain ⟨ t, ht₀, ht₁, rfl ⟩ := h_line; simp +decide [ EuclideanGeometry.angle, * ] ;
  rw [ show a - ( ( 1 - t ) • a + t • b ) = -t • ( b - a ) by simp +decide [ sub_smul, smul_sub ] ; abel_nf, show b - ( ( 1 - t ) • a + t • b ) = ( 1 - t ) • ( b - a ) by simp +decide [ sub_smul, smul_sub ] ; abel_nf ];
  rw [ InnerProductGeometry.angle_smul_right_of_neg, InnerProductGeometry.angle_smul_right_of_pos ] <;> norm_num [ ht₀, ht₁ ];
  rw [ show b - a = - ( a - b ) by abel1, InnerProductGeometry.angle_neg_right ] ; ring


lemma altman_crossing_angle_logic_case_q_lt_n1 {A : ℕ → V} {n : ℕ}
    (h_convex : IsConvexPolygon A n)
    {p y x q : ℕ}
    (hp_pos : 0 < p) (hp_y : p < y) (hy_x : y < x) (hx_q : x < q) (hq_n : q < n)
    (hq_lt_n1 : q < n - 1)
    (K L : V)
    (hK_Ay : K ∈ segment ℝ (A 0) (A y))
    (hK_pq : K ∈ segment ℝ (A p) (A q))
    (hL_Ax : L ∈ segment ℝ (A (n - 1)) (A x))
    (hL_pq : L ∈ segment ℝ (A p) (A q))
    (phi_bar psi_bar phi_double_bar psi_double_bar : ℝ)
    (h_phi_def : phi_bar = EuclideanGeometry.angle (A y) K (A q))
    (h_psi_def : psi_bar = EuclideanGeometry.angle (A x) L (A p))
    (h_phi_db_def : phi_double_bar = EuclideanGeometry.angle (A y) (A 0) (A (n - 1)))
    (h_psi_db_def : psi_double_bar = EuclideanGeometry.angle (A x) (A (n - 1)) (A 0)) :
    phi_bar + psi_bar = phi_double_bar + psi_double_bar := by
  have hn3 : 3 ≤ n := h_convex.1
  have h_ci := h_convex.2.2.1
  let n1 := n - 1
  -- Fin definitions optimized to avoid omega
  have h_n_pos : 0 < n := by omega
  have h_n1_lt_n : n1 < n := by omega
  let i0 : Fin n := ⟨0, h_n_pos⟩
  let ip : Fin n := ⟨p, hp_y.trans (hy_x.trans (hx_q.trans hq_n))⟩
  let iy : Fin n := ⟨y, hy_x.trans (hx_q.trans hq_n)⟩
  let ix : Fin n := ⟨x, hx_q.trans hq_n⟩
  let iq : Fin n := ⟨q, hq_n⟩
  let in1 : Fin n := ⟨n1, h_n1_lt_n⟩

  -- Shared inequalities optimized
  have h_p_ne_0 : ip ≠ i0 := by apply Fin.ne_of_val_ne; exact ne_of_gt hp_pos
  have h_y_ne_0 : iy ≠ i0 := by apply Fin.ne_of_val_ne; exact ne_of_gt (Nat.lt_trans hp_pos hp_y)
  have h_x_ne_0 : ix ≠ i0 := by apply Fin.ne_of_val_ne; exact ne_of_gt (Nat.lt_trans hp_pos (Nat.lt_trans hp_y hy_x))
  have h_q_ne_0 : iq ≠ i0 := by apply Fin.ne_of_val_ne; exact ne_of_gt (Nat.lt_trans hp_pos (Nat.lt_trans hp_y (Nat.lt_trans hy_x hx_q)))
  have h_n1_ne_0 : in1 ≠ i0 := by apply Fin.ne_of_val_ne; exact ne_of_gt (Nat.lt_trans hp_pos (Nat.lt_trans hp_y (Nat.lt_trans hy_x (Nat.lt_trans hx_q hq_lt_n1))))

  have h_y_ne_p : iy ≠ ip := by apply Fin.ne_of_val_ne; exact ne_of_gt hp_y
  have h_x_ne_p : ix ≠ ip := by apply Fin.ne_of_val_ne; exact ne_of_gt (Nat.lt_trans hp_y hy_x)
  have h_q_ne_p : iq ≠ ip := by apply Fin.ne_of_val_ne; exact ne_of_gt (Nat.lt_trans hp_y (Nat.lt_trans hy_x hx_q))
  have h_n1_ne_p : in1 ≠ ip := by apply Fin.ne_of_val_ne; exact ne_of_gt (Nat.lt_trans hp_y (Nat.lt_trans hy_x (Nat.lt_trans hx_q hq_lt_n1)))

  have h_x_ne_y : ix ≠ iy := by apply Fin.ne_of_val_ne; exact ne_of_gt hy_x
  have h_q_ne_y : iq ≠ iy := by apply Fin.ne_of_val_ne; exact ne_of_gt (Nat.lt_trans hy_x hx_q)
  have h_n1_ne_y : in1 ≠ iy := by apply Fin.ne_of_val_ne; exact ne_of_gt (Nat.lt_trans hy_x (Nat.lt_trans hx_q hq_lt_n1))

  have h_q_ne_x : iq ≠ ix := by apply Fin.ne_of_val_ne; exact ne_of_gt hx_q
  have h_n1_ne_x : in1 ≠ ix := by apply Fin.ne_of_val_ne; exact ne_of_gt (Nat.lt_trans hx_q hq_lt_n1)

  have h_n1_ne_q : in1 ≠ iq := by apply Fin.ne_of_val_ne; exact ne_of_gt hq_lt_n1

  -- Symmetric versions for convenience
  have h_0_ne_p := h_p_ne_0.symm
  have h_0_ne_y := h_y_ne_0.symm
  have h_0_ne_x := h_x_ne_0.symm
  have h_0_ne_q := h_q_ne_0.symm
  have h_0_ne_n1 := h_n1_ne_0.symm
  have h_p_ne_y := h_y_ne_p.symm
  have h_p_ne_x := h_x_ne_p.symm
  have h_p_ne_q := h_q_ne_p.symm
  have h_p_ne_n1 := h_n1_ne_p.symm
  have h_y_ne_x := h_x_ne_y.symm
  have h_y_ne_q := h_q_ne_y.symm
  have h_y_ne_n1 := h_n1_ne_y.symm
  have h_x_ne_q := h_q_ne_x.symm
  have h_x_ne_n1 := h_n1_ne_x.symm
  have h_q_ne_n1 := h_n1_ne_q.symm

  -- 2. Define intersection I of diagonals 0-q and p-n1
  obtain ⟨I, hI_0q, hI_pn1⟩ := convex_polygon_diagonals_intersect h_convex hp_pos (hp_y.trans (hy_x.trans hx_q)) hq_lt_n1 h_n1_lt_n

  have h_col_K_0y : Collinear ℝ {A i0, K, A iy} := (mem_segment_iff_wbtw.mp hK_Ay).collinear
  have h_col_K_pq : Collinear ℝ {A ip, K, A iq} := (mem_segment_iff_wbtw.mp hK_pq).collinear

  -- 3. Decompose phi_bar = angle(y, K, q)
  have h_phi_decomp : phi_bar = ∠ (A y) (A 0) (A q) + ∠ (A p) (A q) (A 0) := by
    have h_sum_0Kq : ∠ (A 0) K (A q) + ∠ K (A q) (A 0) + ∠ (A q) (A 0) K = Real.pi := by
      apply triangle_angle_sum_eq_pi;
      intro h_col; subst h_col;
      -- K=0. K on p-q. ip, i0, iq.
      have := h_col_K_pq;
      exact (convexIndependent_no_three_collinear h_ci h_p_ne_0 h_0_ne_q h_p_ne_q) (by simpa [ip, i0, iq] using this)

    have h_K_lin : ∠ (A y) K (A q) + ∠ (A 0) K (A q) = Real.pi := by
      have h_K_sbtw : Sbtw ℝ (A 0) K (A y) := by
        refine ⟨mem_segment_iff_wbtw.mp hK_Ay, ?_, ?_⟩
        · intro h; subst h; -- K=0
          exact (convexIndependent_no_three_collinear h_ci h_p_ne_0 h_0_ne_q h_p_ne_q) (by simpa using h_col_K_pq)
        · intro h; subst h; -- K=y
          exact (convexIndependent_no_three_collinear h_ci h_p_ne_y h_y_ne_q h_p_ne_q) (by simpa using h_col_K_pq)

      rw [angle_comm (A y) K (A q), angle_comm (A 0) K (A q)]
      apply angle_add_eq_pi_of_between h_K_sbtw.symm
      intro h_eq; subst h_eq; -- K=q
      have h_col : Collinear ℝ {A i0, A iq, A iy} := by simpa [i0, iq, iy] using h_col_K_0y
      exact convexIndependent_no_three_collinear h_ci h_0_ne_q h_q_ne_y h_0_ne_y h_col

    have h_ray_Kq0 : ∠ K (A q) (A 0) = ∠ (A p) (A q) (A 0) := by
      rw [EuclideanGeometry.angle_comm K (A q) (A 0), EuclideanGeometry.angle_comm (A p) (A q) (A 0)]
      have h_sbtw : Sbtw ℝ (A q) K (A p) := by
        refine ⟨(mem_segment_iff_wbtw.mp hK_pq).symm, ?_, ?_⟩
        · intro h_eq; subst h_eq; -- K=q
          have := h_col_K_0y;
          exact (convexIndependent_no_three_collinear h_ci h_0_ne_q h_q_ne_y h_0_ne_y) (by simpa [i0, iq, iy] using this)
        · intro h_eq; subst h_eq; -- K=p
          have := h_col_K_0y;
          exact (convexIndependent_no_three_collinear h_ci h_0_ne_p h_p_ne_y h_0_ne_y) (by simpa [i0, ip, iy] using this)
      apply angle_eq_of_between h_sbtw

    have h_ray_q0K : ∠ (A q) (A 0) K = ∠ (A q) (A 0) (A y) := by
      have h_sbtw : Sbtw ℝ (A 0) K (A y) := by
        refine ⟨mem_segment_iff_wbtw.mp hK_Ay, ?_, ?_⟩
        · intro h_eq; subst h_eq; -- K=0
          have := h_col_K_pq;
          exact (convexIndependent_no_three_collinear h_ci h_p_ne_0 h_0_ne_q h_p_ne_q) (by simpa [ip, i0, iq] using this)
        · intro h_eq; subst h_eq; -- K=y
          have := h_col_K_pq;
          exact (convexIndependent_no_three_collinear h_ci h_p_ne_y h_y_ne_q h_p_ne_q) (by simpa [ip, iy, iq] using this)
      apply angle_eq_of_between h_sbtw

    rw [h_phi_def]
    linarith [h_sum_0Kq, h_K_lin, h_ray_Kq0, h_ray_q0K, angle_comm (A q) (A 0) (A y)]

  have h_col_L_n1x : Collinear ℝ {A in1, L, A ix} := (mem_segment_iff_wbtw.mp hL_Ax).collinear
  have h_col_L_pq : Collinear ℝ {A ip, L, A iq} := (mem_segment_iff_wbtw.mp hL_pq).collinear

  -- 4. Decompose psi_bar = angle(x, L, p)
  have h_psi_decomp : psi_bar = ∠ (A x) (A n1) (A p) + ∠ (A q) (A p) (A n1) := by
    have hL_on_xn1 : L ∈ segment ℝ (A x) (A n1) := by rw [segment_symm]; exact hL_Ax
    have h_sum_n1Lp : ∠ (A n1) L (A p) + ∠ L (A p) (A n1) + ∠ (A p) (A n1) L = Real.pi := by
      apply triangle_angle_sum_eq_pi;
      intro h_col; subst h_col;
      -- L=n1. L on p-q. ip, in1, iq.
      have := h_col_L_pq;
      exact (convexIndependent_no_three_collinear h_ci h_p_ne_n1 h_n1_ne_q h_p_ne_q) (by simpa [ip, in1, iq] using this)

    have h_L_lin : ∠ (A x) L (A p) + ∠ (A n1) L (A p) = Real.pi := by
      rw [angle_comm (A x) L (A p), angle_comm (A n1) L (A p), add_comm]
      have h_sbtw_xn1 : Sbtw ℝ (A x) L (A n1) := by
        refine ⟨mem_segment_iff_wbtw.mp hL_on_xn1, ?_, ?_⟩
        · intro h; subst h; -- L=x
          have := h_col_L_pq;
          exact (convexIndependent_no_three_collinear h_ci h_p_ne_x h_x_ne_q h_p_ne_q) (by simpa [ip, ix, iq] using this)
        · intro h; subst h; -- L=n1
          have := h_col_L_pq;
          exact (convexIndependent_no_three_collinear h_ci h_p_ne_n1 h_n1_ne_q h_p_ne_q) (by simpa [ip, in1, iq] using this)
      have h_p_ne_L : L ≠ A p := by
        intro h; subst h; -- L=p
        have := h_col_L_n1x
        exact (convexIndependent_no_three_collinear h_ci h_n1_ne_p h_p_ne_x h_n1_ne_x) (by simpa [in1, ip, ix] using this)
      rw [add_comm]
      apply angle_add_eq_pi_of_between h_sbtw_xn1 h_p_ne_L

    have h_ray_Lpn1 : ∠ L (A p) (A n1) = ∠ (A q) (A p) (A n1) := by
      have h_sbtw : Sbtw ℝ (A q) L (A p) := by
        refine ⟨(mem_segment_iff_wbtw.mp hL_pq).symm, ?_, ?_⟩
        · intro h_eq; subst h_eq; -- L=q
          have := h_col_L_n1x;
          exact (convexIndependent_no_three_collinear h_ci h_n1_ne_q h_q_ne_x h_n1_ne_x) (by simpa [in1, iq, ix] using this)
        · intro h_eq; subst h_eq; -- L=p
          have := h_col_L_n1x;
          exact (convexIndependent_no_three_collinear h_ci h_n1_ne_p h_p_ne_x h_n1_ne_x) (by simpa [in1, ip, ix] using this)
      rw [angle_comm L (A p) (A n1), angle_comm (A q) (A p) (A n1)]
      apply angle_eq_of_between h_sbtw.symm

    have h_ray_pn1L : ∠ (A p) (A n1) L = ∠ (A p) (A n1) (A x) := by
      have h_sbtw : Sbtw ℝ (A x) L (A n1) := by
        refine ⟨mem_segment_iff_wbtw.mp hL_on_xn1, ?_, ?_⟩
        · intro h_eq; subst h_eq; -- L=x
          have := h_col_L_pq;
          exact (convexIndependent_no_three_collinear h_ci h_p_ne_x h_x_ne_q h_p_ne_q) (by simpa [ip, ix, iq] using this)
        · intro h_eq; subst h_eq; -- L=n1
          have := h_col_L_pq;
          exact (convexIndependent_no_three_collinear h_ci h_p_ne_n1 h_n1_ne_q h_p_ne_q) (by simpa [ip, in1, iq] using this)
      apply angle_eq_of_between h_sbtw.symm

    rw [h_psi_def]
    linarith [h_sum_n1Lp, h_L_lin, h_ray_Lpn1, h_ray_pn1L, angle_comm (A p) (A n1) (A x)]

  have h_col_I_0q : Collinear ℝ {A i0, I, A iq} := by simpa [i0, iq] using (mem_segment_iff_wbtw.mp hI_0q).collinear
  have h_col_I_pn1 : Collinear ℝ {A ip, I, A in1} := by simpa [ip, in1] using (mem_segment_iff_wbtw.mp hI_pn1).collinear

  -- 5. Decompose base angles using I (0-q and p-n1)
  have h_base_decomp_1 : ∠ (A y) (A 0) (A n1) = ∠ (A y) (A 0) (A q) + ∠ (A q) (A 0) (A n1) := by
    -- 0-I-q betweenness
    have h_sbtw_0q_I : Sbtw ℝ (A q) I (A 0) := by
      refine ⟨(mem_segment_iff_wbtw.mp hI_0q).symm, ?_, ?_⟩
      · intro h_eq; subst h_eq; -- I=q
        have h_col : Collinear ℝ {A ip, A iq, A in1} := by
          have := h_col_I_pn1
          rwa [Set.insert_comm] at this
        exact (convexIndependent_no_three_collinear h_ci h_p_ne_q h_q_ne_n1 h_p_ne_n1) h_col
      · intro h_eq; subst h_eq; -- I=0
        have h_col : Collinear ℝ {A ip, A i0, A in1} := h_col_I_pn1
        exact (convexIndependent_no_three_collinear h_ci h_p_ne_0 h_0_ne_n1 h_p_ne_n1) h_col

    have h_ray_0I_q : ∠ I (A 0) (A n1) = ∠ (A q) (A 0) (A n1) := by
      rw [angle_comm, angle_comm (A q)]
      apply angle_eq_of_between h_sbtw_0q_I.symm

    have h_ray_0I_y : ∠ (A y) (A 0) I = ∠ (A y) (A 0) (A q) := by
      apply angle_eq_of_between h_sbtw_0q_I.symm

    have h_sum : ∠ (A y) (A 0) I + ∠ I (A 0) (A n1) = ∠ (A y) (A 0) (A n1) := by
      obtain ⟨J, hJ_0q, hJ_y_n1⟩ := convex_polygon_diagonals_intersect h_convex (show 0 < y by omega) (show y < q by omega) hq_lt_n1 (show n1 < n by omega)
      have h_col_J_0q : Collinear ℝ {A 0, J, A q} := (mem_segment_iff_wbtw.mp hJ_0q).collinear
      have h_col_J_yn1 : Collinear ℝ {A y, J, A n1} := (mem_segment_iff_wbtw.mp hJ_y_n1).collinear

      have h_sbtw_0q_J : Sbtw ℝ (A q) J (A 0) := by
        refine ⟨(mem_segment_iff_wbtw.mp hJ_0q).symm, ?_, ?_⟩
        · intro h; subst h; -- J=q
          have h_col : Collinear ℝ {A iy, A iq, A in1} := h_col_J_yn1
          exact (convexIndependent_no_three_collinear h_ci h_y_ne_q h_q_ne_n1 h_y_ne_n1) h_col
        · intro h; subst h; -- J=0
          have h_col : Collinear ℝ {A iy, A i0, A in1} := h_col_J_yn1
          exact (convexIndependent_no_three_collinear h_ci h_y_ne_0 h_0_ne_n1 h_y_ne_n1) h_col

      have h_sbtw_yn1_J : Sbtw ℝ (A y) J (A n1) := by
        refine ⟨mem_segment_iff_wbtw.mp hJ_y_n1, ?_, ?_⟩
        · intro h; subst h; -- J=y
          have h_col : Collinear ℝ {A i0, A iy, A iq} := h_col_J_0q
          exact (convexIndependent_no_three_collinear h_ci h_0_ne_y h_y_ne_q h_0_ne_q) h_col
        · intro h; subst h; -- J=n1
          have h_col : Collinear ℝ {A i0, A in1, A iq} := h_col_J_0q
          exact (convexIndependent_no_three_collinear h_ci h_0_ne_n1 h_n1_ne_q h_0_ne_q) h_col

      have h_ray_I_J_y : ∠ (A y) (A 0) I = ∠ (A y) (A 0) J := by
        rw [angle_eq_of_between h_sbtw_0q_I.symm, angle_eq_of_between h_sbtw_0q_J.symm]

      have h_ray_I_J_n1 : ∠ (A n1) (A 0) I = ∠ (A n1) (A 0) J := by
        rw [angle_eq_of_between h_sbtw_0q_I.symm, angle_eq_of_between h_sbtw_0q_J.symm]

      rw [h_ray_I_J_y, angle_comm I (A 0) (A n1), h_ray_I_J_n1]
      have h_ne0y : A 0 ≠ A y := by
        intro h; exact h_0_ne_y (Fin.ext (h_convex.2.1 _ _ i0.isLt iy.isLt h))
      have h_ne0n1 : A 0 ≠ A n1 := by
        intro h; exact h_0_ne_n1 (Fin.ext (h_convex.2.1 _ _ i0.isLt in1.isLt h))
      rw [angle_comm (A n1) (A 0) J]
      exact angle_add_of_ne_of_ne h_ne0y h_ne0n1 h_sbtw_yn1_J.wbtw

    linarith [h_sum, h_ray_0I_q, h_ray_0I_y]

  have h_base_decomp_2 : ∠ (A x) (A n1) (A 0) = ∠ (A x) (A n1) (A p) + ∠ (A p) (A n1) (A 0) := by
    obtain ⟨K', hK'_0x, hK'_pn1⟩ := convex_polygon_diagonals_intersect h_convex hp_pos (hp_y.trans hy_x) (hx_q.trans hq_lt_n1) h_n1_lt_n
    have h_col_K'_0x : Collinear ℝ {A 0, K', A x} := (mem_segment_iff_wbtw.mp hK'_0x).collinear
    have h_col_K'_pn1 : Collinear ℝ {A p, K', A n1} := (mem_segment_iff_wbtw.mp hK'_pn1).collinear

    have h_sbtw_0x_K' : Sbtw ℝ (A 0) K' (A x) := by
      refine ⟨mem_segment_iff_wbtw.mp hK'_0x, ?_, ?_⟩
      · intro h; subst h; -- K'=0
        exact (convexIndependent_no_three_collinear h_ci h_p_ne_0 h_0_ne_n1 h_p_ne_n1) (by simpa [ip, i0, in1] using h_col_K'_pn1)
      · intro h; subst h; -- K'=x
        exact (convexIndependent_no_three_collinear h_ci h_p_ne_x h_x_ne_n1 h_p_ne_n1) (by simpa [ip, ix, in1] using h_col_K'_pn1)

    have h_sbtw_pn1_K' : Sbtw ℝ (A p) K' (A n1) := by
      refine ⟨mem_segment_iff_wbtw.mp hK'_pn1, ?_, ?_⟩
      · intro h; subst h; -- K'=p
        exact (convexIndependent_no_three_collinear h_ci h_0_ne_p h_p_ne_x h_0_ne_x) (by simpa [i0, ip, ix] using h_col_K'_0x)
      · intro h; subst h; -- K'=n1
        exact (convexIndependent_no_three_collinear h_ci h_0_ne_n1 h_n1_ne_x h_0_ne_x) (by simpa [i0, in1, ix] using h_col_K'_0x)

    have h_ray_n1_0p : ∠ K' (A n1) (A 0) = ∠ (A p) (A n1) (A 0) := by
      rw [angle_comm K' (A n1) (A 0), angle_comm (A p) (A n1) (A 0)]
      apply angle_eq_of_between h_sbtw_pn1_K'.symm

    have h_ray_n1_xp : ∠ (A x) (A n1) K' = ∠ (A x) (A n1) (A p) := by
      apply angle_eq_of_between h_sbtw_pn1_K'.symm

    rw [← h_ray_n1_xp, ← h_ray_n1_0p, angle_comm (A x) (A n1) K', add_comm]
    have h_nen10 : A n1 ≠ A 0 := by intro h; exact h_n1_ne_0 (Fin.ext (h_convex.2.1 _ _ in1.isLt i0.isLt h))
    have h_nen1x : A n1 ≠ A x := by intro h; exact h_n1_ne_x (Fin.ext (h_convex.2.1 _ _ in1.isLt ix.isLt h))
    rw [angle_comm K' (A n1) (A 0), angle_comm (A x)]
    exact (angle_add_of_ne_of_ne h_nen10 h_nen1x h_sbtw_0x_K'.wbtw).symm

  -- 6. Quadrilateral Identity
  have h_ne_n1_0 : A n1 ≠ A 0 := by intro h; exact h_n1_ne_0 (Fin.ext (h_convex.2.1 _ _ in1.isLt i0.isLt h))
  have h_ne_q_p : A q ≠ A p := by intro h; exact h_q_ne_p (Fin.ext (h_convex.2.1 _ _ iq.isLt ip.isLt h))
  have h_ne_p_0 : A p ≠ A 0 := by intro h; exact h_p_ne_0 (Fin.ext (h_convex.2.1 _ _ ip.isLt i0.isLt h))
  have h_ne_n1_q : A n1 ≠ A q := by intro h; exact h_n1_ne_q (Fin.ext (h_convex.2.1 _ _ in1.isLt iq.isLt h))

  have h_quad_id : ∠ (A p) (A q) (A 0) + ∠ (A q) (A p) (A n1) = ∠ (A q) (A 0) (A n1) + ∠ (A p) (A n1) (A 0) := by
    have h_s_0q : Sbtw ℝ (A 0) I (A q) := by
      refine ⟨mem_segment_iff_wbtw.mp hI_0q, ?_, ?_⟩
      · intro h; subst h; -- I=0. But I on p-n1.
        exact (convexIndependent_no_three_collinear h_ci h_p_ne_0 h_0_ne_n1 h_p_ne_n1) (by simpa [ip, i0, in1] using h_col_I_pn1)
      · intro h; subst h; -- I=q. But I on p-n1.
        exact (convexIndependent_no_three_collinear h_ci h_p_ne_q h_q_ne_n1 h_p_ne_n1) (by simpa [ip, iq, in1] using h_col_I_pn1)

    have h_s_pn1 : Sbtw ℝ (A p) I (A n1) := by
      refine ⟨mem_segment_iff_wbtw.mp hI_pn1, ?_, ?_⟩
      · intro h; subst h; -- I=p. But I on 0-q.
        exact (convexIndependent_no_three_collinear h_ci h_0_ne_p h_p_ne_q h_0_ne_q) (by simpa [i0, ip, iq] using h_col_I_0q)
      · intro h; subst h; -- I=n1. But I on 0-q.
        exact (convexIndependent_no_three_collinear h_ci h_0_ne_n1 h_n1_ne_q h_0_ne_q) (by simpa [i0, in1, iq] using h_col_I_0q)

    have h_neI0 : I ≠ A 0 := h_s_0q.ne_left
    have h_neIp : I ≠ A p := h_s_pn1.ne_left

    have h_tri_0In1 : ∠ (A n1) (A 0) I + ∠ (A 0) I (A n1) + ∠ I (A n1) (A 0) = Real.pi :=
      triangle_angle_sum_eq_pi (A n1) (A 0) I h_ne_n1_0.symm

    have h_tri_qIp : ∠ (A p) (A q) I + ∠ (A q) I (A p) + ∠ I (A p) (A q) = Real.pi :=
      triangle_angle_sum_eq_pi (A p) (A q) I h_ne_q_p

    have h_vert : ∠ (A 0) I (A n1) = ∠ (A q) I (A p) := by
      have h1 : ∠ (A p) I (A 0) + ∠ (A p) I (A q) = Real.pi := angle_add_eq_pi_of_between h_s_0q h_neIp
      have h2 : ∠ (A 0) I (A p) + ∠ (A 0) I (A n1) = Real.pi := angle_add_eq_pi_of_between h_s_pn1 h_neI0
      linarith [h1, h2, angle_comm (A 0) I (A p), angle_comm (A p) I (A 0), angle_comm (A q) I (A p)]

    have h_r0 : ∠ (A n1) (A 0) I = ∠ (A n1) (A 0) (A q) := angle_eq_of_between h_s_0q
    have h_rn1 : ∠ I (A n1) (A 0) = ∠ (A p) (A n1) (A 0) := by
      rw [angle_comm, angle_comm (A p)]
      apply angle_eq_of_between h_s_pn1.symm
    have h_rq : ∠ (A p) (A q) I = ∠ (A p) (A q) (A 0) := angle_eq_of_between h_s_0q.symm
    have h_rp : ∠ (A q) (A p) I = ∠ (A q) (A p) (A n1) := angle_eq_of_between h_s_pn1

    linarith [h_tri_0In1, h_tri_qIp, h_vert, h_r0, h_rn1, h_rq, h_rp, angle_comm (A q) (A 0) (A n1), angle_comm (A p) (A q) (A 0), angle_comm (A n1) (A p) (A 0), angle_comm (A q) (A p) I, angle_comm I (A p) (A q)]

  linarith [h_phi_decomp, h_psi_decomp, h_base_decomp_1, h_base_decomp_2, h_quad_id, h_phi_db_def, h_psi_db_def]

/--
Variant of `altman_crossing_angle_logic` with ≥ hypotheses instead of >.
If p < y < x < q and BOTH dist(A p, A x) ≥ dist(A p, A q) and dist(A q, A y) ≥ dist(A p, A q),
we still derive a contradiction via the crossing-angle argument.
-/
lemma altman_crossing_angle_logic_ge {A : ℕ → V} {n : ℕ}
    (h_convex : IsConvexPolygon A n)
    (h_max : ∀ i j, i < n → j < n → dist (A i) (A j) ≤ dist (A 0) (A (n - 1)))
    {p q x y : ℕ} (hp : 0 ≤ p) (hp_y : p < y) (hy_x : y < x) (hx_q : x < q) (hq_n1 : q < n - 1)
    (h_px : dist (A p) (A x) ≥ dist (A p) (A q))
    (h_qy : dist (A q) (A y) ≥ dist (A p) (A q)) :
    False := by
  have hy_n : y < n := by omega
  have hx_n : x < n := by omega
  have hp_n : p < n := by omega
  have hq_n : q < n := by omega
  have hq_n0 : 0 < n := by omega
  have hy_n1 : y < n - 1 := by omega
  have hx_n1 : x < n - 1 := by omega
  have hq_lt_n1 : q < n - 1 := hq_n1
  have hn_n1 : n - 1 < n := by omega

  -- Same general setup as strict version
  let n1 := n - 1
  -- Define angles
  let alpha := ∠ (A p) (A y) (A q)
  let beta := ∠ (A q) (A x) (A p)
  let alpha_bar := ∠ (A 0) (A y) (A n1)
  let beta_bar := ∠ (A n1) (A x) (A 0)
  let phi_double_bar := ∠ (A y) (A 0) (A n1)
  let psi_double_bar := ∠ (A x) (A n1) (A 0)

  -- Fin indices
  have h_ci := h_convex.2.2.1
  let ip : Fin n := ⟨p, hp_n⟩
  let iy : Fin n := ⟨y, hy_n⟩
  let ix : Fin n := ⟨x, hx_n⟩
  let iq : Fin n := ⟨q, hq_n⟩
  let in1 : Fin n := ⟨n1, by omega⟩
  let i0 : Fin n := ⟨0, hq_n0⟩

  -- Fin inequalities
  have hiy_ix : iy ≠ ix := by simp [iy, ix]; omega
  have hix_iq : ix ≠ iq := by simp [ix, iq]; omega
  have hi0_ix : i0 ≠ ix := by simp [i0, ix]; omega
  have hin1_iy : in1 ≠ iy := by simp [in1, iy]; omega
  have hip_iy : ip ≠ iy := by simp [ip, iy]; omega
  have hiy_iq : iy ≠ iq := by simp [iy, iq]; omega
  have hip_iq : ip ≠ iq := by simp [ip, iq]; omega
  have hip_ix : ip ≠ ix := by simp [ip, ix]; omega
  have hi0_iy : i0 ≠ iy := by simp [i0, iy]; omega
  have hiy_in1 : iy ≠ in1 := by simp [iy, in1]; omega
  have hi0_in1 : i0 ≠ in1 := by simp [i0, in1]; omega
  have hin1_ix : in1 ≠ ix := by simp [in1, ix]; omega
  have hix_i0 : ix ≠ i0 := by simp [ix, i0]; omega
  have hin1_i0 : in1 ≠ i0 := by simp [in1, i0]; omega
  have hi0_iq : i0 ≠ iq := by simp [i0, iq]; omega
  have hin1_ip : in1 ≠ ip := by simp [in1, ip]; omega
  have hin1_iq : in1 ≠ iq := by simp [in1, iq]; omega



  -- Point distinctness proofs
  have h_Ay_ne_Ap : A y ≠ A p := fun h => by have := h_convex.2.1 y p hy_n hp_n h; omega
  have h_Ap_ne_Ay : A p ≠ A y := h_Ay_ne_Ap.symm
  have h_Ay_ne_Aq : A y ≠ A q := fun h => by have := h_convex.2.1 y q hy_n hq_n h; omega
  have h_Aq_ne_Ay : A q ≠ A y := h_Ay_ne_Aq.symm
  have h_Ap_ne_Aq : A p ≠ A q := fun h => by have := h_convex.2.1 p q hp_n hq_n h; omega
  have h_Aq_ne_Ap : A q ≠ A p := h_Ap_ne_Aq.symm
  have h_Ax_ne_Aq : A x ≠ A q := fun h => by have := h_convex.2.1 x q hx_n hq_n h; omega
  have h_Aq_ne_Ax : A q ≠ A x := h_Ax_ne_Aq.symm
  have h_Ap_ne_Ax : A p ≠ A x := fun h => by have := h_convex.2.1 p x hp_n hx_n h; omega
  have h_Ax_ne_Ap : A x ≠ A p := h_Ap_ne_Ax.symm

  -- Step 1: Angle inequalities from distances (h_px, h_qy)

  have h_ci := h_convex.2.2.1  -- ConvexIndependent part of IsConvexPolygon

  -- Define points on a Fin-indexed function for convexIndependent_no_three_collinear
  -- For now, we use the non-collinearity directly
  have h_not_col_pyx : ¬ Collinear ℝ ({A p, A y, A x} : Set V) := by
    have := convexIndependent_no_three_collinear h_ci hip_iy hiy_ix hip_ix
    -- Clean up the set representation to match {!A ip, !A iy, !A ix}
    simp [ip, iy, ix] at this
    exact this

  have h_not_col_yxq : ¬ Collinear ℝ ({A y, A x, A q} : Set V) := by
    have := convexIndependent_no_three_collinear h_ci hiy_ix hix_iq hiy_iq
    simp [iy, ix, iq] at this
    exact this

  have h_not_col_ypq : ¬ Collinear ℝ ({A y, A p, A q} : Set V) := by
    have := convexIndependent_no_three_collinear h_ci hip_iy.symm hip_iq hiy_iq
    simp [ip, iy, iq] at this
    exact this

  have h_not_col_xqp : ¬ Collinear ℝ ({A x, A q, A p} : Set V) := by
    have := convexIndependent_no_three_collinear h_ci hix_iq hip_iq.symm hip_ix.symm
    simp [ip, ix, iq] at this
    exact this

  -- Uses `angle_ge_of_dist_ge` to get non-strict bounds
  have h_phi_ge_alpha : ∠ (A y) (A p) (A q) ≥ alpha := by
    apply angle_ge_of_dist_ge h_Ay_ne_Ap h_Ap_ne_Aq h_Ay_ne_Aq h_not_col_ypq
    rw [dist_comm] at h_qy
    exact h_qy

  have h_psi_ge_beta : ∠ (A x) (A q) (A p) ≥ beta := by
    apply angle_ge_of_dist_ge h_Ax_ne_Aq h_Aq_ne_Ap h_Ax_ne_Ap h_not_col_xqp
    -- We need dist (A x) (A p) ≥ dist (A q) (A p).
    -- h_px is dist (A p) (A x) ≥ dist (A p) (A q).
    rw [dist_comm (A p), dist_comm (A p)] at h_px
    exact h_px

  -- Step 2: STRICT Angle nesting using hq_n1
  -- Uses `angle_nesting_convex_strict`
  have h_alpha_gt_alpha_bar : alpha > alpha_bar := by
    apply angle_nesting_convex_strict (p':=0) (q':=n-1) h_convex hp hp_y (Nat.lt_trans hy_x hx_q) (le_of_lt hq_n1) (Nat.sub_lt hq_n0 Nat.one_pos) (Or.inr hq_n1)

  have h_beta_gt_beta_bar : beta > beta_bar := by
    unfold beta beta_bar
    rw [angle_comm (A q) (A x) (A p), angle_comm (A n1) (A x) (A 0)]
    apply angle_nesting_convex_strict (p':=0) (q':=n-1) h_convex hp (Nat.lt_trans hp_y hy_x) hx_q (le_of_lt hq_n1) (Nat.sub_lt hq_n0 Nat.one_pos) (Or.inr hq_n1)

  -- Step 3: Base triangle angle bounds
  have h0_y : 0 < y := by omega

  have h_alpha_bar_ge_phi_double : alpha_bar ≥ phi_double_bar := by
    have h_side : dist (A 0) (A n1) ≥ dist (A y) (A n1) := h_max y n1 hy_n hn_n1
    apply angle_ge_of_dist_ge
    · intro h; have := h_convex.2.1 0 y hq_n0 hy_n h; omega
    · intro h; have := h_convex.2.1 y n1 hy_n hn_n1 h; omega
    · intro h; have := h_convex.2.1 0 n1 hq_n0 hn_n1 h; omega
    · -- Non-collinearity of {0, y, n-1}
      have := convexIndependent_no_three_collinear h_convex.2.2.1 hi0_iy hin1_iy.symm hi0_in1
      simp [i0, iy, in1] at this
      exact this
    · exact h_side

  have h_beta_bar_ge_psi_double : beta_bar ≥ psi_double_bar := by
    -- In triangle A_n1 A_x A_0, side A_0 A_n1 is maximal.
    have h_side : dist (A 0) (A n1) ≥ dist (A x) (A 0) := h_max x 0 hx_n hq_n0
    apply angle_ge_of_dist_ge
    · intro h; have := h_convex.2.1 n1 x hn_n1 hx_n h; omega
    · intro h; have := h_convex.2.1 x 0 hx_n hq_n0 h; omega
    · intro h; have := h_convex.2.1 n1 0 hn_n1 hq_n0 h; omega
    · -- Non-collinearity of {n-1, x, 0}
      have := convexIndependent_no_three_collinear h_convex.2.2.1 hin1_ix hi0_ix.symm hi0_in1.symm
      simp [in1, ix, i0] at this
      exact this
    · rw [dist_comm]; exact h_side

  -- Step 4: Intersection Points K and L
  -- K = intersection (A p, A q) with (A 0, A y)
  -- L = intersection (A p, A q) with (A n1, A x)
  obtain ⟨K, hK_Ay, hK_pq⟩ : ∃ K : V, (K ∈ segment ℝ (A 0) (A y)) ∧ (K ∈ segment ℝ (A p) (A q)) := by
    by_cases hp0 : p = 0
    · subst hp0; use A 0; exact ⟨left_mem_segment ℝ (A 0) (A y), left_mem_segment ℝ (A 0) (A q)⟩
    · have h0_p : 0 < p := Nat.pos_of_ne_zero hp0
      have hy_q : y < q := Nat.lt_trans hy_x hx_q
      obtain ⟨Ki, hKi_0y, hKi_pq⟩ := convex_polygon_diagonals_intersect h_convex h0_p hp_y hy_q hq_n
      use Ki;

  obtain ⟨L, hL_Ax, hL_pq⟩ : ∃ L : V, (L ∈ segment ℝ (A n1) (A x)) ∧ (L ∈ segment ℝ (A p) (A q)) := by
    -- Since q < n - 1, we have q < n1.
    -- Diagonals are (A p, A q) and (A x, A n1).
    -- Order for intersection lemma: p < x < q < n1.
    have hq_lt_n1 : q < n1 := by omega
    have hp_x : p < x := Nat.lt_trans hp_y hy_x
    have hn1_n : n1 < n := by omega
    -- intersection of (A p, A q) and (A x, A n1)
    obtain ⟨Li, hLi_pq, hLi_xn1⟩ := convex_polygon_diagonals_intersect h_convex hp_x hx_q hq_lt_n1 hn1_n
    use Li; exact ⟨segment_symm ℝ (A x) (A n1) ▸ hLi_xn1, hLi_pq⟩

  let phi_bar := ∠ (A y) K (A q)
  let psi_bar := ∠ (A x) L (A p)

  -- Step 5: Exterior Angle Properties (K and L on p-q)
  have h_phi_bar_ge : phi_bar ≥ ∠ (A y) (A p) (A q) := by
    by_cases hp0 : p = 0
    · subst hp0; have : K = A 0 := by
        by_contra hne
        have hK_0y : K ∈ segment ℝ (A 0) (A y) := hK_Ay
        have hK_0q : K ∈ segment ℝ (A 0) (A q) := hK_pq
        have h_col1 : Collinear ℝ ({A 0, K, A y} : Set V) := (mem_segment_iff_wbtw.mp hK_0y).collinear
        have h_col2 : Collinear ℝ ({A 0, K, A q} : Set V) := (mem_segment_iff_wbtw.mp hK_0q).collinear
        have h_col_all : Collinear ℝ ({A 0, A y, A q} : Set V) := by
          refine collinear_triple_of_mem_affineSpan_pair (left_mem_affineSpan_pair ℝ (A 0) K) ?_ ?_
          · exact h_col1.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) (Ne.symm hne)
          · exact h_col2.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) (Ne.symm hne)
        exact convexIndependent_no_three_collinear h_ci hi0_iy hiy_iq hi0_iq h_col_all
      subst this; exact le_refl _
    · have h_p_pos : 0 < p := Nat.pos_of_ne_zero hp0
      have hi0_ip : i0 ≠ ip := by simp [i0, ip]; omega
      have h_K_btwn : Sbtw ℝ (A p) K (A q) := by
        refine ⟨mem_segment_iff_wbtw.mp hK_pq, ?_, ?_⟩
        · intro hKp
          have hK_0y : K ∈ segment ℝ (A 0) (A y) := hK_Ay
          rw [hKp] at hK_0y
          have h_col : Collinear ℝ ({A 0, A p, A y} : Set V) := (mem_segment_iff_wbtw.mp hK_0y).collinear
          have h_col' : Collinear ℝ ({A i0, A ip, A iy} : Set V) := by
             convert h_col using 2;
          exact convexIndependent_no_three_collinear h_ci hi0_ip hip_iy hi0_iy h_col'
        · intro hKq
          have hK_0y : K ∈ segment ℝ (A 0) (A y) := hK_Ay
          rw [hKq] at hK_0y
          have h_col : Collinear ℝ ({A 0, A q, A y} : Set V) := (mem_segment_iff_wbtw.mp hK_0y).collinear
          have h_col' : Collinear ℝ ({A i0, A iq, A iy} : Set V) := by
             convert h_col using 2;
          exact convexIndependent_no_three_collinear h_ci hi0_iq hiy_iq.symm hi0_iy h_col'
      have h_Ay_ne_K : (A y) ≠ K := by
        intro h_eq; subst h_eq
        have h_col : Collinear ℝ ({A p, A y, A q} : Set V) := h_K_btwn.wbtw.collinear
        exact convexIndependent_no_three_collinear h_ci hip_iy hiy_iq hip_iq h_col
      have h1 : ∠ (A y) K (A p) + ∠ (A y) K (A q) = Real.pi := by
        apply angle_add_eq_pi_of_between h_K_btwn h_Ay_ne_K.symm
      have h2 : ∠ (A y) (A p) K + ∠ (A p) (A y) K + ∠ (A y) K (A p) = Real.pi := by
        have h_sum := triangle_angle_sum_eq_pi (A y) (A p) K h_Ap_ne_Ay
        linarith [EuclideanGeometry.angle_comm (A y) (A p) K,
                  EuclideanGeometry.angle_comm (A p) K (A y),
                  EuclideanGeometry.angle_comm K (A y) (A p)]
      have : phi_bar = ∠ (A y) (A p) K + ∠ (A p) (A y) K := by
        unfold phi_bar; linarith
      have h_ray : ∠ (A y) (A p) K = ∠ (A y) (A p) (A q) := by
        apply angle_eq_of_between h_K_btwn
      rw [this, h_ray]
      linarith [EuclideanGeometry.angle_nonneg (A p) (A y) K]

  have h_psi_bar_ge_psi : psi_bar ≥ ∠ (A x) (A q) (A p) := by
    -- Symmetric to h_phi_bar_ge_phi
    have h_L_btwn : Sbtw ℝ (A q) L (A p) := by
      apply sbtw_comm.mp
      refine ⟨mem_segment_iff_wbtw.mp (segment_symm ℝ (A p) (A q) ▸ hL_pq), ?_, ?_⟩
      · intro hLp
        have hL_xn1 : L ∈ segment ℝ (A n1) (A x) := hL_Ax
        rw [hLp] at hL_xn1
        have h_col : Collinear ℝ ({A n1, A p, A x} : Set V) := (mem_segment_iff_wbtw.mp hL_xn1).collinear
        -- Set {n1, p, x}. i=n1, j=p, k=x.
        -- Need: n1!=p, p!=x, n1!=x.
        exact convexIndependent_no_three_collinear h_ci hin1_ip hip_ix hin1_ix h_col
      · intro hLq
        have hL_xn1 : L ∈ segment ℝ (A n1) (A x) := hL_Ax
        rw [hLq] at hL_xn1
        have h_col : Collinear ℝ ({A n1, A q, A x} : Set V) := (mem_segment_iff_wbtw.mp hL_xn1).collinear
        -- Set {n1, q, x}. i=n1, j=q, k=x.
        -- Need: n1!=q, q!=x, n1!=x.
        exact convexIndependent_no_three_collinear h_ci hin1_iq hix_iq.symm hin1_ix h_col
    have h_Ax_ne_L : (A x) ≠ L := by
      intro h_eq; subst h_eq
      have h_col : Collinear ℝ ({A p, A x, A q} : Set V) := by
          have h_col_L := h_L_btwn.wbtw.collinear
          rw [show ({A q, A x, A p} : Set V) = {A p, A x, A q} by ext; simp [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h_col_L
          exact h_col_L
      -- Set {p, x, q}. i=p, j=x, k=q.
      -- Need: p!=x, x!=q, p!=q.
      exact convexIndependent_no_three_collinear h_ci hip_ix hix_iq hip_iq h_col
    have h1 : ∠ (A x) L (A q) + ∠ (A x) L (A p) = Real.pi := by
      apply angle_add_eq_pi_of_between h_L_btwn h_Ax_ne_L.symm
    have h2 : ∠ (A x) (A q) L + ∠ (A q) (A x) L + ∠ (A x) L (A q) = Real.pi := by
      have h_sum := triangle_angle_sum_eq_pi (A x) (A q) L h_Aq_ne_Ax
      linarith [EuclideanGeometry.angle_comm (A x) (A q) L,
                EuclideanGeometry.angle_comm (A q) L (A x),
                EuclideanGeometry.angle_comm L (A x) (A q)]
    have : psi_bar = ∠ (A x) (A q) L + ∠ (A q) (A x) L := by
      unfold psi_bar; linarith
    have h_ray : ∠ (A x) (A q) L = ∠ (A x) (A q) (A p) := by
      apply angle_eq_of_between h_L_btwn
    rw [this, h_ray]
    linarith [EuclideanGeometry.angle_nonneg (A q) (A x) L]

  -- Step 6: Sum Equality (G)
  -- Uses `altman_crossing_angle_logic_case_q_lt_n1`
  have h_KL_pq : K ∈ segment ℝ (A p) (A q) ∧ L ∈ segment ℝ (A p) (A q) := ⟨hK_pq, hL_pq⟩
  have h_G : phi_bar + psi_bar = phi_double_bar + psi_double_bar := by
    have h_n1_0 : A n1 ≠ A 0 := by intro h; exact hi0_in1.symm (Fin.ext (h_convex.2.1 _ _ in1.isLt i0.isLt h))
    -- have h_n1_0 : A n1 ≠ A 0 := by intro h; have := Fin.ext (h_convex.2.1 n1 0 hq_n1 hq_n0); omega
    have h_y_0 : A y ≠ A 0 := by
      intro h; exact hi0_iy.symm (Fin.ext (h_convex.2.1 _ _ iy.isLt i0.isLt h))
    -- have h_x_n1 : A x ≠ A n1 := by intro h; have := Fin.ext (h_convex.2.1 x n1 hx_n hq_n1); omega
    have h_x_n1 : A x ≠ A n1 := by
      intro h; exact hin1_ix.symm (Fin.ext (h_convex.2.1 _ _ ix.isLt in1.isLt h))
    by_cases hp0 : p = 0
    · subst hp0; have hK0 : K = A 0 := by
        by_contra h_ne
        have h_col1 : Collinear ℝ {A 0, K, A y} := (mem_segment_iff_wbtw.mp hK_Ay).collinear
        have h_col2 : Collinear ℝ {A 0, K, A q} := (mem_segment_iff_wbtw.mp hK_pq).collinear
        have h_col_all : Collinear ℝ {A 0, A y, A q} := by
          refine collinear_triple_of_mem_affineSpan_pair (left_mem_affineSpan_pair ℝ (A 0) K) ?_ ?_
          · exact h_col1.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) (Ne.symm h_ne)
          · exact h_col2.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) (Ne.symm h_ne)
        exact convexIndependent_no_three_collinear h_ci hi0_iy hiy_iq hi0_iq h_col_all
      subst hK0; unfold phi_bar
      have hqn1_lt : q < n1 := by omega
      have hin1_iq : in1 ≠ iq := by simp [in1, iq]; omega
      have h_L_btwn_0q : Sbtw ℝ (A 0) L (A q) := by
        refine ⟨mem_segment_iff_wbtw.mp (segment_symm ℝ (A 0) (A q) ▸ hL_pq), ?_, ?_⟩
        · intro h; subst h; have h_col : Collinear ℝ {A n1, A 0, A x} := (mem_segment_iff_wbtw.mp hL_Ax).collinear
          have h_neq : in1 ≠ i0 ∧ i0 ≠ ix ∧ in1 ≠ ix := by simp [in1, i0, ix]; omega
          exact convexIndependent_no_three_collinear h_ci h_neq.1 h_neq.2.1 h_neq.2.2 h_col
        · intro h; subst h; have h_col : Collinear ℝ {A n1, A q, A x} := (mem_segment_iff_wbtw.mp hL_Ax).collinear
          have h_neq : in1 ≠ iq ∧ iq ≠ ix ∧ in1 ≠ ix := by simp [in1, iq, ix]; omega
          exact convexIndependent_no_three_collinear h_ci h_neq.1 h_neq.2.1 h_neq.2.2 h_col
      have h_An1_L_Ax : Sbtw ℝ (A n1) L (A x) := by
        refine ⟨mem_segment_iff_wbtw.mp hL_Ax, ?_, ?_⟩
        · intro h; subst h; have h_col : Collinear ℝ {A 0, A n1, A q} := (mem_segment_iff_wbtw.mp hL_pq).collinear
          have h_neq : i0 ≠ in1 ∧ in1 ≠ iq ∧ i0 ≠ iq := by simp [i0, in1, iq]; omega
          exact convexIndependent_no_three_collinear h_ci h_neq.1 h_neq.2.1 h_neq.2.2 h_col
        · intro h; subst h; have h_col : Collinear ℝ {A 0, A x, A q} := (mem_segment_iff_wbtw.mp hL_pq).collinear
          have h_neq : i0 ≠ ix ∧ ix ≠ iq ∧ i0 ≠ iq := by simp [i0, ix, iq]; omega
          exact convexIndependent_no_three_collinear h_ci h_neq.1 h_neq.2.1 h_neq.2.2 h_col
      have h_sum_tri : ∠ (A n1) (A 0) L + ∠ (A 0) L (A n1) + ∠ L (A n1) (A 0) = Real.pi := by
        apply triangle_angle_sum_eq_pi
        exact h_n1_0.symm
      have h_L_supp : ∠ (A n1) L (A 0) + ∠ (A x) L (A 0) = Real.pi := by
        rw [angle_comm (A n1) L (A 0), angle_comm (A x) L (A 0)]
        apply angle_add_eq_pi_of_between h_An1_L_Ax h_L_btwn_0q.ne_left
        -- exact h_L_btwn_0q.ne_left.symm
      have h_ray_0L : ∠ (A n1) (A 0) L = ∠ (A n1) (A 0) (A q) := by
        apply angle_eq_of_between h_L_btwn_0q
      have h_ray_n1L : ∠ (A 0) (A n1) L = ∠ (A 0) (A n1) (A x) := by
        apply angle_eq_of_between h_An1_L_Ax

      have h_A0_add : ∠ (A y) (A 0) (A n1) = ∠ (A y) (A 0) (A q) + ∠ (A q) (A 0) (A n1) := by
        obtain ⟨M, hM_0q_seg, hM_yn1_seg⟩ := convex_polygon_diagonals_intersect h_convex (by omega : 0 < y) (by omega : y < q) (by omega : q < n1) (by omega : n1 < n)
        have h_M_sbtw_yn1 : Sbtw ℝ (A y) M (A n1) := by
          refine ⟨mem_segment_iff_wbtw.mp hM_yn1_seg, ?_, ?_⟩
          · intro h; subst h; have h_col : Collinear ℝ {A 0, A y, A q} := (mem_segment_iff_wbtw.mp hM_0q_seg).collinear
            have h_neq : i0 ≠ iy ∧ iy ≠ iq ∧ i0 ≠ iq := by simp [i0, iy, iq]; omega
            exact convexIndependent_no_three_collinear h_ci h_neq.1 h_neq.2.1 h_neq.2.2 h_col
          · intro h; subst h; have h_col : Collinear ℝ {A 0, A n1, A q} := (mem_segment_iff_wbtw.mp hM_0q_seg).collinear
            have h_neq : i0 ≠ in1 ∧ in1 ≠ iq ∧ i0 ≠ iq := by simp [i0, in1, iq]; omega
            exact convexIndependent_no_three_collinear h_ci h_neq.1 h_neq.2.1 h_neq.2.2 h_col
        have h_M_sbtw_0q : Sbtw ℝ (A 0) M (A q) := by
          refine ⟨mem_segment_iff_wbtw.mp hM_0q_seg, ?_, ?_⟩
          · intro h; subst h; have h_col : Collinear ℝ {A y, A 0, A n1} := h_M_sbtw_yn1.wbtw.collinear
            have h_neq : iy ≠ i0 ∧ i0 ≠ in1 ∧ iy ≠ in1 := by simp [iy, i0, in1]; omega
            exact convexIndependent_no_three_collinear h_ci h_neq.1 h_neq.2.1 h_neq.2.2 h_col
          · intro h; subst h; have h_col : Collinear ℝ {A y, A q, A n1} := h_M_sbtw_yn1.wbtw.collinear
            have h_neq : iy ≠ iq ∧ iq ≠ in1 ∧ iy ≠ in1 := by simp [iy, iq, in1]; omega
            exact convexIndependent_no_three_collinear h_ci h_neq.1 h_neq.2.1 h_neq.2.2 h_col

        -- Use manual logic since the dedicated lemma is missing/renamed
        -- We want: angle y 0 n1 = angle y 0 M + angle n1 0 M
        -- M is strictly between y and n1? No, M is intersection of diagonals.
        -- M is strictly between 0 and q? Yes, h_M_sbtw_0q.
        -- Rays 0-M and 0-q are the same.
        -- We need angle additivity at vertex 0? No, vertex is 0?
        -- Wait, M is on 0-q.
        -- The target is angle y 0 n1 = angle y 0 q + angle q 0 n1.
        -- This requires ray 0-q to be between rays 0-y and 0-n1.
        -- This follows from convexity and index ordering 0 < y < q < n1 < n.
        -- But to avoid full Convexity proof, we use the fact M is inside triangle 0 y n1?
        -- h_M_sbtw_yn1 says M is between y and n1.
        -- Thus ray 0-M is between ray 0-y and ray 0-n1.
        -- Since M is on 0-q, ray 0-q is same as ray 0-M.

        have h_ray_0M_eq_0q : ∠ (A y) (A 0) M = ∠ (A y) (A 0) (A q) := by
          apply angle_eq_of_between h_M_sbtw_0q
        have h_ray_0M_eq_0q_2 : ∠ (A n1) (A 0) M = ∠ (A n1) (A 0) (A q) := by
          apply angle_eq_of_between h_M_sbtw_0q


        have h_sum_tri_large : ∠ (A y) (A 0) (A n1) + ∠ (A 0) (A n1) (A y) + ∠ (A n1) (A y) (A 0) = Real.pi := by
          apply triangle_angle_sum_eq_pi; exact h_y_0.symm

        have h_sum_tri_1 : ∠ (A y) (A 0) M + ∠ (A 0) M (A y) + ∠ M (A y) (A 0) = Real.pi := by
          apply triangle_angle_sum_eq_pi; exact h_y_0.symm

        have h_sum_tri_2 : ∠ (A n1) (A 0) M + ∠ (A 0) M (A n1) + ∠ M (A n1) (A 0) = Real.pi := by
          apply triangle_angle_sum_eq_pi; exact h_n1_0.symm

        have h_M_linear : ∠ (A y) M (A 0) + ∠ (A n1) M (A 0) = Real.pi := by
          rw [angle_comm (A y) M (A 0), angle_comm (A n1) M (A 0)]
          apply angle_add_eq_pi_of_between h_M_sbtw_yn1
          exact h_M_sbtw_0q.ne_left

        -- M is on y-n1, so angle M y 0 = angle n1 y 0?
        -- Yes, ray y-M is ray y-n1.
        have h_ray_y : ∠ M (A y) (A 0) = ∠ (A n1) (A y) (A 0) := by
          rw [angle_comm M (A y) (A 0), angle_comm (A n1) (A y) (A 0)]
          apply angle_eq_of_between h_M_sbtw_yn1

        -- And angle M n1 0 = angle y n1 0.
        have h_ray_n1 : ∠ M (A n1) (A 0) = ∠ (A y) (A n1) (A 0) := by
          rw [angle_comm M (A n1) (A 0), angle_comm (A y) (A n1) (A 0)]
          apply angle_eq_of_between (sbtw_comm.mp h_M_sbtw_yn1)

        -- Now combine.
        -- h_sum_tri_1 + h_sum_tri_2:
        -- (ang y 0 M + ang n1 0 M) + (ang 0 M y + ang 0 M n1) + (ang M y 0 + ang M n1 0) = 2pi.
        -- (ang y 0 M + ang n1 0 M) + (pi) + (ang n1 y 0 + ang y n1 0) = 2pi.
        -- (ang y 0 M + ang n1 0 M) + (ang n1 y 0 + ang y n1 0) = pi.

        -- h_sum_tri_large:
        -- ang y 0 n1 + ang 0 n1 y + ang n1 y 0 = pi.

        -- Therefore ang y 0 n1 = ang y 0 M + ang n1 0 M.
        linarith [h_sum_tri_large, h_sum_tri_1, h_sum_tri_2, h_M_linear, h_ray_y, h_ray_n1,
                  h_ray_0M_eq_0q, h_ray_0M_eq_0q_2,
                  angle_comm (A 0) M (A y), angle_comm (A 0) M (A n1),
                  angle_comm (A n1) (A 0) (A q),
                  angle_comm (A 0) (A n1) (A y), angle_comm (A 0) (A y) (A n1)]
      unfold psi_bar; rw [show phi_double_bar = ∠ (A y) (A 0) (A n1) by rfl, show psi_double_bar = ∠ (A x) (A n1) (A 0) by rfl]
      linarith [h_sum_tri, h_ray_0L, h_ray_n1L, h_L_supp, h_A0_add,
                angle_comm (A n1) (A 0) (A q), angle_comm (A 0) L (A n1),
                angle_comm L (A n1) (A 0), angle_comm (A q) (A 0) (A n1),
                angle_comm (A 0) (A n1) (A x), angle_comm (A x) (A n1) (A 0),
                angle_comm (A n1) (A 0) L]
    · -- General Case: p > 0.
      -- 1. Establish index ordering 0 < p < q <= n1
      have hp_pos : 0 < p := Nat.pos_of_ne_zero hp0

      have h_sum_eq : phi_bar + psi_bar = phi_double_bar + psi_double_bar := by
        have hqn1_lt : q < n1 := by omega
        have hin1_iq : in1 ≠ iq := by simp [in1, iq]; omega
        apply altman_crossing_angle_logic_case_q_lt_n1 h_convex hp_pos hp_y hy_x hx_q hq_n hqn1_lt K L hK_Ay hK_pq hL_Ax hL_pq phi_bar psi_bar phi_double_bar psi_double_bar rfl rfl rfl rfl
      exact h_sum_eq

  -- Step 7: Contradiction
  -- Chain: φ̄ ≥ φ ≥ α > ᾱ ≥ φ̿ AND ψ̄ ≥ ψ ≥ β > β̄ ≥ ψ̿
  -- Sum: φ̄ + ψ̄ > φ̿ + ψ̿, but eq holds.
  have h_contra : phi_bar + psi_bar > phi_double_bar + psi_double_bar := by
    calc phi_bar + psi_bar
      _ ≥ ∠ (A y) (A p) (A q) + ∠ (A x) (A q) (A p) := add_le_add h_phi_bar_ge h_psi_bar_ge_psi
      _ ≥ alpha + beta := add_le_add h_phi_ge_alpha h_psi_ge_beta
      _ > alpha_bar + beta_bar := add_lt_add h_alpha_gt_alpha_bar h_beta_gt_beta_bar
      _ ≥ phi_double_bar + psi_double_bar := add_le_add h_alpha_bar_ge_phi_double h_beta_bar_ge_psi_double

  linarith

/--
Strict version of `altman_lemma_1_strict_triangle`:
For strictly inner triangle (q < n-1), at least one leg is strictly smaller than the base.
-/
lemma altman_lemma_1_strict_triangle {A : ℕ → V} {n : ℕ}
    (h_convex : IsConvexPolygon A n)
    (h_max : ∀ i j, i < n → j < n → dist (A i) (A j) ≤ dist (A 0) (A (n - 1)))
    {p q y : ℕ} (hp : 0 ≤ p) (hp_y : p < y) (hy_q : y < q) (hq_n1 : q < n - 1) :
    dist (A p) (A y) < dist (A p) (A q) ∨ dist (A q) (A y) < dist (A p) (A q) := by
  have h_n_ge_3 : 3 ≤ n := h_convex.1
  have h0_y : 0 < y := by omega
  have hy_n1 : y < n - 1 := by omega
  have h_base_angle := max_side_angle_bound h_convex h_max h0_y hy_n1
  have hq_le_n1 : q ≤ n - 1 := by linarith
  have hn1_lt_n : n - 1 < n := by omega
  have h_strict_nest : EuclideanGeometry.angle (A p) (A y) (A q) > EuclideanGeometry.angle (A 0) (A y) (A (n - 1)) := by
    apply angle_nesting_convex_strict h_convex (Nat.zero_le p) hp_y hy_q hq_le_n1 hn1_lt_n
    right; exact hq_n1
  have h_angle_gt : EuclideanGeometry.angle (A p) (A y) (A q) > Real.pi / 3 := by
    linarith
  apply dist_lt_of_angle_gt_pi_div_three_of_ne h_angle_gt
  have h_p_ne_q : A p ≠ A q := by
    intro heq
    have := h_convex.2.1 p q (by omega) (by omega) heq
    omega
  exact h_p_ne_q

/--
Strict version of `altman_lemma_1`: at least one of the two "inner" diagonals
is STRICTLY shorter than the base diagonal A_p A_q.
Requires q < n-1 to avoid degenerate equilateral case.

This is the actual content of Altman's Lemma 1 (the paper proves strict <).
Derived by contradiction using `altman_crossing_angle_logic_ge` for crossing case,
and `altman_lemma_1_strict_triangle` for non-crossing.
-/
lemma altman_lemma_1_strict {A : ℕ → V} {n : ℕ}
    (h_convex : IsConvexPolygon A n)
    (h_max : ∀ i j, i < n → j < n → dist (A i) (A j) ≤ dist (A 0) (A (n - 1)))
    {p q x y : ℕ} (hp : 0 ≤ p) (hp_y : p < y) (hy_x : y ≤ x) (hx_q : x < q) (hq_n1 : q < n - 1) :
    dist (A p) (A x) < dist (A p) (A q) ∨ dist (A q) (A y) < dist (A p) (A q) := by
  by_cases h_xy : x = y
  · subst h_xy
    exact altman_lemma_1_strict_triangle h_convex h_max hp hp_y hx_q hq_n1
  · have hy_lt_x : y < x := lt_of_le_of_ne hy_x (Ne.symm h_xy)
    -- Assuming negation leads to contradiction via crossing angle logic
    by_contra h_contra
    push_neg at h_contra
    obtain ⟨h_px, h_qy⟩ := h_contra
    exact altman_crossing_angle_logic_ge h_convex h_max hp hp_y hy_lt_x hx_q hq_n1 h_px h_qy


-- proven by Aristotle
lemma exists_smaller_diagonal_in_quadrilateral {A : ℕ → V} {n : ℕ}
    (h_convex : IsConvexPolygon A n)
    (h_max : ∀ i j, i < n → j < n → dist (A i) (A j) ≤ dist (A 0) (A (n - 1)))
    {i j k l : ℕ} (hi_j : i < j) (hj_k : j < k) (hk_l : k < l) (hl_n : l < n)
    (hi0 : i = 0) (hln1 : l = n - 1) :
    dist (A j) (A k) < dist (A i) (A l) := by
    -- By the nested chord shorter lemma, since j < k < l, we have dist(A j, A k) < dist(A 0, A (n - 1)).
    have h_nested_chord : dist (A j) (A k) < dist (A 0) (A (n - 1)) := by
      -- Apply the nested chord shorter lemma with p=0, y=j, x=k, q=l, and using the fact that l = n-1.
      apply nested_chord_shorter h_convex (by linarith) (by linarith) (by linarith) (by linarith) (by
      exact fun i j a a_1 => h_max i j a a_1);
    -- Substitute the equalities i = 0 and l = n - 1 into the goal.
    rw [hi0, hln1] at *; exact h_nested_chord

-- (proven by Aristotle)
lemma dist_set_cardinality_from_chain {m : ℕ} (d : ℕ → ℝ) (h_strict : ∀ i < m, d (i + 1) < d i) :
    (Finset.image d (Finset.range (m + 1))).card = m + 1 := by
  -- Since $d$ is strictly decreasing, it is injective on the range up to $m$.
  have h_inj : ∀ i j : ℕ, i < m + 1 → j < m + 1 → i ≠ j → d i ≠ d j := by
    -- By induction on $j - i$, we can show that $d_i > d_j$ for any $i < j$.
    have h_ind : ∀ i j, i < j → i < m + 1 → j < m + 1 → d i > d j := by
      -- By induction on $j - i$, we can show that $d_i > d_j$ for any $i < j$.
      intros i j hij hi hj
      induction' hij with k hk ih;
      · exact h_strict i ( Nat.lt_of_succ_lt_succ hj );
      · grind;
    exact fun i j hi hj hij => fun h => hij <| le_antisymm ( le_of_not_gt fun hi' => by linarith [ h_ind _ _ hi' hj hi ] ) ( le_of_not_gt fun hj' => by linarith [ h_ind _ _ hj' hi hj ] );
  rw [ Finset.card_image_of_injOn fun i hi j hj hij => by contrapose hij; exact h_inj i j ( Finset.mem_range.mp hi ) ( Finset.mem_range.mp hj ) hij, Finset.card_range ]


-- (proven by Aristotle)
lemma exists_intermediate_transversal {A : ℕ → V} {n : ℕ}
    (h_convex : IsConvexPolygon A n)
    (h_max_unique : ∀ i j, i < n → j < n → (i ≠ 0 ∨ j ≠ n-1) → (i ≠ n-1 ∨ j ≠ 0) →
      dist (A i) (A j) < dist (A 0) (A (n-1))) :
    ∃ d, d ∈ distinctDistances (Finset.image A (Finset.range n)) ∧
      dist (A 1) (A (n-2)) < d ∧ d < dist (A 0) (A (n-1)) := by
  rcases n with ( _ | _ | _ | _ | n ) <;> simp_all +decide [ Finset.image ];
  · have := h_convex.1;
    contradiction;
  · cases h_convex.1;
    contradiction;
  · have := h_convex.1; simp_all +decide ;
  · refine' ⟨ Dist.dist ( A 0 ) ( A 1 ), _, _, _ ⟩;
    · simp +decide [ distinctDistances, Finset.mem_insert, Finset.mem_singleton ];
      exact ⟨ A 0, A 1, ⟨ ⟨ by tauto, by tauto ⟩, by have := h_convex.2.2.1 0 1; aesop ⟩, rfl ⟩;
    · have := h_convex.2.1 0 1 ( by decide ) ( by decide ) ; simp_all +decide ;
    · exact h_max_unique 0 1 ( by decide ) ( by decide ) ( by decide ) ( by decide );
  · -- By `convex_polygon_diagonals_intersect`, diagonals A_0 A_{n-2} and A_1 A_{n-1} intersect at K.
    obtain ⟨K, hK_Ay, hK_pq⟩ : ∃ K : V, K ∈ segment ℝ (A 0) (A (n + 2)) ∧ K ∈ segment ℝ (A 1) (A (n + 3)) := by
      convert convex_polygon_diagonals_intersect h_convex ( show 0 < 1 by norm_num ) ( show 1 < n + 2 by linarith ) ( show n + 2 < n + 3 by linarith ) ( show n + 3 < n + 1 + 1 + 1 + 1 by linarith ) using 1;
    -- By `triangle_inequality_via_intersection_strict`, dist(A_0, A_{n-2}) + dist(A_1, A_{n-1}) > dist(A_0, A_{n-1}) + dist(A_1, A_{n-2}).
    have h_triangle : dist (A 0) (A (n + 2)) + dist (A 1) (A (n + 3)) > dist (A 0) (A (n + 3)) + dist (A 1) (A (n + 2)) := by
      apply triangle_inequality_via_intersection_strict h_convex hK_Ay hK_pq (by linarith) (by linarith) (by linarith) (by linarith) ⟨by linarith, by linarith, by linarith, by linarith⟩;
    cases le_or_gt ( Dist.dist ( A 0 ) ( A ( n + 2 ) ) ) ( Dist.dist ( A 1 ) ( A ( n + 3 ) ) ) <;> [ refine' ⟨ Dist.dist ( A 1 ) ( A ( n + 3 ) ), _, _, _ ⟩ ; refine' ⟨ Dist.dist ( A 0 ) ( A ( n + 2 ) ), _, _, _ ⟩ ] <;> simp_all +decide [ distinctDistances ];
    · refine' ⟨ A 1, A ( n + 3 ), _, _ ⟩ <;> simp +decide [ *];
      refine' ⟨ _, _ ⟩;
      · rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.lt_succ_iff ];
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| ⟨ 1, by linarith, rfl ⟩;
      · intro h; specialize h_max_unique 1 ( n + 3 ) ; simp_all +decide ;
    · linarith [ h_max_unique 0 ( n + 2 ) ( by linarith ) ( by linarith ) ( by norm_num ) ( by norm_num ) ];
    · grind;
    · grind

lemma altman_descent_chain {A : ℕ → V} {n : ℕ}
    (h_convex : IsConvexPolygon A n) (hn : n ≥ 4)
    (h_max : ∀ i j, i < n → j < n → dist (A i) (A j) ≤ dist (A 0) (A (n-1))) :
    ∃ (d : ℕ → ℝ),
      d 0 = dist (A 0) (A (n - 1)) ∧
      d 1 = dist (A 1) (A (n - 2)) ∧
      (∀ k ≤ n - 3, ∃ p q, p < n ∧ q < n ∧ p ≠ q ∧ d k = dist (A p) (A q)) ∧
      (∀ k < n - 3, d (k + 1) < d k) := by
  -- Define "step" function
  let step (pq : ℕ × ℕ) : ℕ × ℕ :=
    let p := pq.1
    let q := pq.2
    if h_gap : p + 2 ≤ q then
      if dist (A (p + 1)) (A q) < dist (A p) (A q) then (p + 1, q)
      else (p, q - 1)
    else pq

  -- Recursive definition using iterate notation
  let indices (k : ℕ) : ℕ × ℕ :=
    match k with
    | 0 => (0, n - 1)
    | k + 1 => step^[k] (1, n - 2)

  let p (k : ℕ) := (indices k).1
  let q (k : ℕ) := (indices k).2
  let d (k : ℕ) := dist (A (p k)) (A (q k))

  have h_ind_0 : indices 0 = (0, n - 1) := rfl
  have h_ind_1 : indices 1 = (1, n - 2) := rfl
  have h_ind_succ : ∀ k, 1 ≤ k → indices (k + 1) = step (indices k) := by
    intro k hk
    cases k with
    | zero => contradiction
    | succ k =>
      cases k with
      | zero => rfl
      | succ k => simp [indices]; apply Function.Commute.iterate_self step

  let gap (k : ℕ) := q k - p k

  -- Base cases
  have h_base_0 : p 0 = 0 ∧ q 0 = n - 1 ∧ gap 0 = n - 1 := by simp [p, q, gap, indices]
  have h_base_1 : p 1 = 1 ∧ q 1 = n - 2 ∧ gap 1 = n - 3 := by simp [p, q, gap, indices, h_ind_1]; omega

  -- Invariants for k >= 1
  have h_inv : ∀ k, 1 ≤ k → k ≤ n - 3 →
      (1 ≤ p k ∧ q k ≤ n - 2 ∧ p k < q k ∧ gap k = n - k - 2) := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base =>
      intro _
      simp [h_base_1, gap]; omega
    | succ k hk h_ind =>
      intro h_kn
      have h_k_lt : k < n - 3 := by omega
      specialize h_ind h_k_lt.le
      obtain ⟨hp, hq, hpq, hgap⟩ := h_ind

      have h_cond : p k + 2 ≤ q k := by
        simp [gap] at hgap
        omega

      have h_indices_kp1 : indices (k + 1) = step (indices k) := h_ind_succ k hk
      match h_pq : indices k with
      | (p_val, q_val) =>
        simp [p, q, gap, h_pq] at *
        simp only [h_indices_kp1, step, h_cond]
        split_ifs with h_chord
        · simp only at * ; omega
        · simp only at * ; omega

  -- Prove strict decrease d(k+1) < d(k)
  have h_decr : ∀ k < n - 3, d (k + 1) < d k := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      simp [d, p, q, h_ind_0, h_ind_1]
      apply exists_smaller_diagonal_in_quadrilateral h_convex h_max (i:=0) (j:=1) (k:=n-2) (l:=n-1)
      · norm_num
      · show 1 < n - 2; omega
      · show n - 2 < n - 1; omega
      · show n - 1 < n; omega
      · rfl
      · rfl
    · -- Inductive descent
      have h_k_ge_1 : 1 ≤ k := by omega
      have h_kn : k ≤ n - 3 := by omega
      obtain ⟨hp, hq, hpq, hgap⟩ := h_inv k h_k_ge_1 h_kn

      have h_indices_kp1 : indices (k + 1) = step (indices k) := h_ind_succ k h_k_ge_1

      have h_cond : p k + 2 ≤ q k := by
        simp [gap] at hgap
        omega

      -- Apply strict lemma to current chord
      have h_strict := altman_lemma_1_strict h_convex h_max (p:=p k) (q:=q k) (x:=q k - 1) (y:=p k + 1)
        (by omega) (by omega) (by omega) (by omega) (by omega)

      simp at h_strict

      have h_indices_kp1 : indices (k + 1) = step (indices k) := h_ind_succ k h_k_ge_1
      match h_pq : indices k with
      | (p_val, q_val) =>
        simp [d, p, q, gap, h_pq] at *
        simp only [h_indices_kp1, step, h_cond]
        split_ifs with h_chord
        · exact h_chord
        · simp only at *
          cases h_strict with
          | inl h => exact h
          | inr h => rw [dist_comm] at h ; contradiction

  -- Final logic
  refine ⟨d, rfl, ?_, ?_, h_decr⟩
  · simp [d, p, q, indices, h_ind_1]
  · intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      refine ⟨0, n - 1, by omega, by omega, by omega, rfl⟩
    · have h_k_ge_1 : 1 ≤ k := by omega
      obtain ⟨hp, hq, hpq, _⟩ := h_inv k h_k_ge_1 hk
      refine ⟨p k, q k, by omega, by omega, by omega, rfl⟩

lemma altman_lemma_2 {A : ℕ → V} {n : ℕ}
    (h_convex : IsConvexPolygon A n)
    (h_max : ∀ i j, i < n → j < n → dist (A i) (A j) ≤ dist (A 0) (A (n-1))) :
    (distinctDistances (Finset.image A (Finset.range n))).card ≥ n - 2 := by
  have hn3 : 3 ≤ n := h_convex.1
  by_cases hn : n ≥ 4
  · obtain ⟨d, h_d0, _, h_dim, h_decr⟩ := altman_descent_chain h_convex hn h_max
    let m := n - 3
    let S := (Finset.range (m + 1)).image d
    have h_card : S.card = n - 2 := by
      have h_m_val : m + 1 = n - 2 := by omega
      rw [← h_m_val]
      apply dist_set_cardinality_from_chain d
      intro i hi
      apply h_decr
      omega
    have h_subset : S ⊆ distinctDistances (Finset.image A (Finset.range n)) := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      simp [m] at hk
      obtain ⟨p, q, hp, hq, hpq, hdk⟩ := h_dim k (by omega)
      rw [hdk, distinctDistances, Finset.mem_image]
      apply Exists.intro (A p, A q)
      constructor
      · simp only [Finset.mem_filter, ne_eq]
        constructor
        · apply Finset.mem_product.mpr
          simp only [Finset.mem_image, Finset.mem_range]
          exact ⟨⟨p, hp, rfl⟩, q, hq, rfl⟩
        · exact mt (h_convex.2.1 p q hp hq) hpq
      · rfl
    exact h_card ▸ Finset.card_le_card h_subset
  · -- Case n = 3
    have : n = 3 := by omega
    subst this
    simp only [Nat.reduceSub]
    apply Finset.card_pos.mpr
    use dist (A 0) (A 1)
    rw [distinctDistances, Finset.mem_image]
    apply Exists.intro (A 0, A 1)
    constructor
    · simp only [Finset.mem_filter, ne_eq]
      constructor
      · apply Finset.mem_product.mpr
        simp only [Finset.mem_image, Finset.mem_range]
        exact ⟨⟨0, by omega, rfl⟩, 1, by omega, rfl⟩
      · exact mt (h_convex.2.1 0 1 (by omega) (by omega)) (by omega)
    · rfl

lemma altman_lemma_2_strong {A : ℕ → V} {n : ℕ}
    (h_convex : IsConvexPolygon A n)
    (h_max_strict : ∀ i j, i < n → j < n → (i ≠ 0 ∨ j ≠ n-1) → (i ≠ n-1 ∨ j ≠ 0) →
       dist (A i) (A j) < dist (A 0) (A (n-1))) :
    (distinctDistances (Finset.image A (Finset.range n))).card ≥ n - 1 := by
  have hn3 : 3 ≤ n := h_convex.1

  -- Derive weak maximality from strict
  have h_max : ∀ i j, i < n → j < n → dist (A i) (A j) ≤ dist (A 0) (A (n-1)) := by
    intro i j hi hj
    by_cases h_end : (i = 0 ∧ j = n - 1) ∨ (i = n - 1 ∧ j = 0)
    · rcases h_end with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · rw [dist_comm]
    · push_neg at h_end
      replace h_end : (i ≠ 0 ∨ j ≠ n - 1) ∧ (i ≠ n - 1 ∨ j ≠ 0) := by tauto
      exact le_of_lt (h_max_strict i j hi hj h_end.1 h_end.2)

  by_cases hn : n ≥ 4
  · -- Main case n ≥ 4
    -- 1. Get the chain of n-2 distances
    obtain ⟨d, h_d0, h_d1, h_dim, h_decr⟩ := altman_descent_chain h_convex hn h_max

    -- 2. get the intermediate transversal
    obtain ⟨d_bar, h_d_bar_mem, h_d_bar_gt, h_d_bar_lt⟩ := exists_intermediate_transversal h_convex h_max_strict

    -- 3. Construct the set of distances
    let m := n - 3
    let S := (Finset.range (m + 1)).image d

    -- S has cardinality n - 2
    have h_card_S : S.card = n - 2 := by
      have h_m_val : m + 1 = n - 2 := by omega
      rw [← h_m_val]
      apply dist_set_cardinality_from_chain d
      intro i hi
      apply h_decr
      omega

    have h_subset_S : S ⊆ distinctDistances (Finset.image A (Finset.range n)) := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      simp [m] at hk
      obtain ⟨p, q, hp, hq, hpq, hdk⟩ := h_dim k (by omega)
      rw [hdk, distinctDistances, Finset.mem_image]
      apply Exists.intro (A p, A q)
      constructor
      · simp only [Finset.mem_filter, ne_eq]
        constructor
        · apply Finset.mem_product.mpr
          simp only [Finset.mem_image, Finset.mem_range]
          exact ⟨⟨p, hp, rfl⟩, q, hq, rfl⟩
        · exact mt (h_convex.2.1 p q hp hq) hpq
      · rfl

    -- S is strictly descending
    have h_chain_strict : ∀ k, k < m → d (k + 1) < d k := by
      intro k hk
      apply h_decr
      omega

    -- d_bar is not in S
    have h_d_bar_not_mem_S : d_bar ∉ S := by
      simp only [S, Finset.mem_image, Finset.mem_range]
      rintro ⟨k, hk_range, rfl⟩
      -- Split into k=0 and k>0
      cases k with
      | zero =>
        -- d 0 = max dist > d_bar
        rw [h_d0] at h_d_bar_lt
        linarith
      | succ k =>
        -- For k >= 1, we want to show d (k+1) <= d 1 < d_bar.
        -- We know d is strictly decreasing.
        have h_chain_le : d (k + 1) ≤ d 1 := by
           -- Use Nat.le_induction to show d j <= d 1 for all 1 <= j <= k+1
           have h_le_ind : ∀ j, 1 ≤ j → j ≤ k + 1 → d j ≤ d 1 := by
             intro j hj hjk
             induction j, hj using Nat.le_induction with
             | base => exact le_refl _
             | succ x hx ih =>
               have h_valid : x < m := by omega
               have h_lt : d (x + 1) < d x := h_chain_strict x h_valid
               exact le_trans (le_of_lt h_lt) (ih (by omega))
           apply h_le_ind (k + 1) (by omega) (by omega)

        rw [h_d1] at h_chain_le
        linarith

    have h_final : (insert d_bar S).card = n - 1 := by
      rw [Finset.card_insert_of_notMem h_d_bar_not_mem_S, h_card_S]
      omega

    have h_final_subset : insert d_bar S ⊆ distinctDistances (Finset.image A (Finset.range n)) := by
      rw [Finset.insert_subset_iff]
      exact ⟨h_d_bar_mem, h_subset_S⟩

    exact h_final ▸ Finset.card_le_card h_final_subset

  · -- Case n = 3
    have : n = 3 := by omega
    subst this
    simp only [Nat.reduceSub]

    let t : Finset ℝ := {dist (A 0) (A 2), dist (A 0) (A 1)}
    have h_neq : dist (A 0) (A 2) ≠ dist (A 0) (A 1) := by
      intro h_eq
      have h0 := h_max_strict 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rw [← h_eq] at h0
      linarith
    have h_card_t : t.card = 2 := by
      simp [t, Finset.card_insert_of_notMem, Finset.mem_singleton, h_neq]

    have h_subset : t ⊆ distinctDistances (Finset.image A (Finset.range 3)) := by
      intro x hx
      simp [t] at hx
      rcases hx with rfl | rfl
      · -- dist(A0, A2)
        rw [distinctDistances, Finset.mem_image]
        apply Exists.intro (A 0, A 2)
        constructor
        · rw [Finset.mem_filter]
          constructor
          · apply Finset.mem_product.mpr
            constructor
            · simp [Finset.mem_image, Finset.mem_range]; use 0; simp
            · simp [Finset.mem_image, Finset.mem_range]; use 2; simp
          · exact mt (h_convex.2.1 0 2 (by norm_num) (by norm_num)) (by norm_num)
        · rfl
      · -- dist(A0, A1)
        rw [distinctDistances, Finset.mem_image]
        apply Exists.intro (A 0, A 1)
        constructor
        · rw [Finset.mem_filter]
          constructor
          · apply Finset.mem_product.mpr
            constructor
            · simp [Finset.mem_image, Finset.mem_range]; use 0; simp
            · simp [Finset.mem_image, Finset.mem_range]; use 1; simp
          · exact mt (h_convex.2.1 0 1 (by norm_num) (by norm_num)) (by norm_num)
        · rfl
    rw [← h_card_t]
    exact Finset.card_le_card h_subset

/--
A convex polygon in 2D has at least 3 vertices.
-/
lemma is_convex_polygon_implies_n_ge_3 {A : ℕ → V} {n : ℕ}
    (h : IsConvexPolygon A n) : n ≥ 3 := h.1

/--
If the global max distance is strictly greater than all side lengths,
then the global max is achieved by a diagonal (not a side).
This means the index difference satisfies 2 ≤ q - p ≤ n - 2.
-/
lemma maximal_diagonal_not_side {A : ℕ → V} {n : ℕ} {p q : ℕ}
    (hp : p < n) (hq : q < n) (h_pq : p ≤ q)
    (h_strict : ∀ i, i < n → dist (A i) (A ((i + 1) % n)) < dist (A p) (A q)) :
    2 ≤ q - p ∧ q - p ≤ n - 2 := by
  -- If q - p ∈ {0, 1} or q - p ≥ n - 1, then (p, q) would be a side (or degenerate)
  -- which contradicts h_strict
  have h_diff := Nat.sub_le q p
  constructor
  · -- Show 2 ≤ q - p
    by_contra h_lt
    push_neg at h_lt
    -- q - p ∈ {0, 1}
    rcases Nat.eq_zero_or_pos (q - p) with h0 | hpos
    · -- q - p = 0 means p = q (since p ≤ q), so dist(A p, A q) = 0
      have heq : p = q := by omega
      have h_side := h_strict p hp
      rw [heq, dist_self] at h_side
      exact not_lt.mpr (dist_nonneg) h_side
    · -- q - p ≥ 1, so q - p = 1
      have h1 : q - p = 1 := by omega
      have heq : q = p + 1 := by omega
      have h_side := h_strict p hp
      have h2 : (p + 1) % n = p + 1 := Nat.mod_eq_of_lt (by omega)
      rw [h2, heq] at h_side
      exact lt_irrefl _ h_side
  · -- Show q - p ≤ n - 2
    by_contra h_gt
    push_neg at h_gt
    -- q - p ≥ n - 1, but q - p ≤ q < n, so q - p ≤ n - 1, meaning q - p = n - 1
    have h_eq : q - p = n - 1 := by omega
    have hp_eq : p = 0 := by omega
    have hq_eq : q = n - 1 := by omega
    -- The side at index n-1 is A_{n-1} to A_0
    have h_side := h_strict (n - 1) (by omega : n - 1 < n)
    have h_mod : (n - 1 + 1) % n = 0 := by simp [Nat.sub_add_cancel (by omega : 1 ≤ n)]
    rw [h_mod, hp_eq, hq_eq, dist_comm] at h_side
    exact lt_irrefl _ h_side



-- (proven by Aristotle)
lemma is_convex_polygon_consecutive_zero {A : ℕ → V} {n : ℕ} {len : ℕ}
    (h_poly : IsConvexPolygon A n)
    (h_len_ge_3 : 3 ≤ len)
    (h_len_le_n : len ≤ n) :
    IsConvexPolygon A len := by
  constructor <;> try linarith;
  refine' ⟨ _, _, _ ⟩;
  · have := h_poly.2.1;
    exact fun i j hi hj hij => this i j ( lt_of_lt_of_le hi h_len_le_n ) ( lt_of_lt_of_le hj h_len_le_n ) hij;
  · have h_convex_indep : ConvexIndependent ℝ (fun i : Fin n => A i) := by
      have := h_poly.2.2;
      exact this.1;
    convert h_convex_indep.comp_embedding ( Fin.castLEEmb h_len_le_n ) using 1;
  · intro i
    by_cases hi : i.val < len - 1;
    · have h_segment_frontier : segment ℝ (A i) (A (i + 1)) ⊆ frontier (convexHull ℝ (Finset.image A (Finset.range n))) := by
        have := h_poly.2.2.2;
        convert this ⟨ i, by linarith [ Fin.is_lt i, Nat.sub_add_cancel ( by linarith : 1 ≤ len ) ] ⟩ using 1;
        rw [ Nat.mod_eq_of_lt ( by linarith [ Fin.is_lt i, Nat.sub_add_cancel ( by linarith : 1 ≤ len ) ] ) ];
      convert segment_frontier_transfer _ _ _ h_segment_frontier using 1;
      · rw [ Nat.mod_eq_of_lt ( by linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ len ) ] ) ];
      · exact Finset.image_subset_image ( Finset.range_mono h_len_le_n );
      · exact Finset.mem_coe.2 ( Finset.mem_image.2 ⟨ i, Finset.mem_range.2 i.2, rfl ⟩ );
      · grind;
    · -- Apply the lemma convex_polygon_vertices_one_side_of_diagonal to get the affine map f.
      obtain ⟨f, hf_nonzero, hf_zero, hf_le⟩ : ∃ f : V →ᵃ[ℝ] ℝ, f.linear ≠ 0 ∧ f (A 0) = 0 ∧ f (A (len - 1)) = 0 ∧ ∀ j, 0 ≤ j → j ≤ len - 1 → f (A j) ≤ 0 := by
        apply convex_polygon_vertices_one_side_of_diagonal h_poly (by linarith) (by omega) (by omega);
      convert segment_subset_frontier_of_supporting_hyperplane _ _ f _ _ _ hf_nonzero using 1;
      · exact subset_convexHull ℝ _ ( Finset.mem_image_of_mem _ ( Finset.mem_range.mpr ( by linarith [ Fin.is_lt i ] ) ) );
      · exact subset_convexHull ℝ _ ( Finset.mem_coe.mpr ( Finset.mem_image.mpr ⟨ ( i + 1 ) % len, Finset.mem_range.mpr ( Nat.mod_lt _ ( by linarith ) ), rfl ⟩ ) );
      · simp +zetaDelta at *;
        exact fun j hj => hf_le.2 j ( Nat.le_pred_of_lt hj );
      · grind;
      · rcases len with ( _ | _ | len ) <;> simp_all +decide
        norm_num [ show ( i : ℕ ) = len + 1 by linarith [ Fin.is_lt i ] ] at * ; aesop


lemma is_convex_polygon_consecutive {A : ℕ → V} {n : ℕ} {start : ℕ} {len : ℕ}
    (h_poly : IsConvexPolygon A n)
    (h_len_ge_3 : 3 ≤ len)
    (h_len_le_n : len ≤ n) :
    IsConvexPolygon (fun i => A ((start + i) % n)) len := by
  -- 1. Rotate
  let B := fun i => A ((i + start) % n)
  have h_rot : IsConvexPolygon B n := is_convex_polygon_rotate h_poly start
  -- 2. Take first len elements
  have h_consecutive : IsConvexPolygon B len := is_convex_polygon_consecutive_zero h_rot h_len_ge_3 h_len_le_n
  -- 3. Match types
  have h_eq : (fun i => A ((start + i) % n)) = B := by
    funext i
    simp only [B, Nat.add_comm]
  rw [h_eq]
  exact h_consecutive

/--
Slicing a convex polygon from index p to q gives a convex sub-polygon.
AP i = A (p + i) for i ∈ {0, ..., q - p}.
-/
lemma is_convex_polygon_slice {A : ℕ → V} {n : ℕ} {p q : ℕ}
    (h_poly : IsConvexPolygon A n)
    (_hp : p < n) (_hq : q < n) (h_pq_min : p + 2 ≤ q) :
    IsConvexPolygon (fun i => A (p + i)) (q - p + 1) := by
  have h_len_ge_3 : 3 ≤ q - p + 1 := by omega
  have h_len_le_n : q - p + 1 ≤ n := by omega
  -- Call the general lemma
  let poly_consecutive := is_convex_polygon_consecutive h_poly h_len_ge_3 h_len_le_n (start := p)
  -- Use congruence to show it matches our desired form
  -- We have IsConvexPolygon (fun i => A ((p + i) % n)) (q - p + 1)
  -- We want IsConvexPolygon (fun i => A (p + i)) (q - p + 1)
  rw [← is_convex_polygon_congr (n := q - p + 1)]
  · exact poly_consecutive
  · intro i hi
    -- Proof that (p + i) % n = p + i because p + i < n
    rw [Nat.mod_eq_of_lt]
    omega -- p + i < n follows from i < q - p + 1 and p + (q-p) = q < n

lemma is_convex_polygon_wrap {A : ℕ → V} {n : ℕ} {p q : ℕ}
    (h_poly : IsConvexPolygon A n)
    (hp : p < n) (hq : q < n) (h_pq_lt : p + 2 ≤ q) (h_pq_up : q ≤ p + n - 2) :
    IsConvexPolygon (fun i => A ((q + i) % n)) (n - q + p + 1) := by
  have h_len_ge_3 : 3 ≤ n - q + p + 1 := by omega
  have h_len_le_n : n - q + p + 1 ≤ n := by omega
  -- Direct application of the general lemma
  exact is_convex_polygon_consecutive h_poly h_len_ge_3 h_len_le_n (start := q)

/--
Distances in a slice are a subset of distances in the original polygon.
-/
lemma distinct_distances_slice_subset {A : ℕ → V} {n : ℕ} {p q : ℕ}
    (_hp : p < n) (_hq : q < n) (_h_pq : p ≤ q) :
    let AP := fun i => A (p + i)
    let x := q - p
    distinctDistances (Finset.image AP (Finset.range (x + 1))) ⊆
    distinctDistances (Finset.image A (Finset.range n)) := by
  intro AP x d hd
  -- Unfold distinctDistances definition
  unfold distinctDistances at hd ⊢
  simp only [Finset.mem_image, Finset.mem_filter] at hd ⊢
  obtain ⟨⟨v1, v2⟩, hpair, hd_eq⟩ := hd
  obtain ⟨hprod, hne⟩ := hpair
  have ⟨hv1_mem, hv2_mem⟩ := Finset.mem_product.mp hprod
  simp only [Finset.mem_image, Finset.mem_range] at hv1_mem hv2_mem
  obtain ⟨i, hi, hv1⟩ := hv1_mem
  obtain ⟨j, hj, hv2⟩ := hv2_mem
  -- v1 = AP i = A (p + i), v2 = AP j = A (p + j)
  simp only [AP] at hv1 hv2
  -- Show (A(p+i), A(p+j)) is in original distances
  refine ⟨(A (p + i), A (p + j)), ?_, ?_⟩
  · constructor
    · apply Finset.mem_product.mpr
      simp only [Finset.mem_image, Finset.mem_range]
      refine ⟨⟨p + i, ?_, rfl⟩, ⟨p + j, ?_, rfl⟩⟩
      · omega  -- p + i < n since i < x + 1 = q - p + 1 and p + (q-p) = q < n
      · omega  -- p + j < n
    · -- A(p+i) ≠ A(p+j)
      simp only
      rw [hv1, hv2]
      exact hne
  · -- dist = d
    simp only
    rw [hv1, hv2]
    exact hd_eq

/--
Distances in a wrap are a subset of distances in the original polygon.
-/
lemma distinct_distances_wrap_subset {A : ℕ → V} {n : ℕ} {p q : ℕ}
    (_hp : p < n) (hq : q < n) (_h_pq : p ≤ q) :
    let AQ := fun i => A ((q + i) % n)
    let size := n - q + p + 1
    distinctDistances (Finset.image AQ (Finset.range size)) ⊆
    distinctDistances (Finset.image A (Finset.range n)) := by
  intro AQ size d hd
  -- Unfold distinctDistances definition
  unfold distinctDistances at hd ⊢
  simp only [Finset.mem_image, Finset.mem_filter] at hd ⊢
  obtain ⟨⟨v1, v2⟩, hpair, hd_eq⟩ := hd
  obtain ⟨hprod, hne⟩ := hpair
  have ⟨hv1_mem, hv2_mem⟩ := Finset.mem_product.mp hprod
  simp only [Finset.mem_image, Finset.mem_range] at hv1_mem hv2_mem
  obtain ⟨i, hi, hv1⟩ := hv1_mem
  obtain ⟨j, hj, hv2⟩ := hv2_mem
  -- v1 = AQ i = A ((q + i) % n), v2 = AQ j = A ((q + j) % n)
  simp only [AQ] at hv1 hv2
  -- Show (A((q+i)%n), A((q+j)%n)) is in original distances
  have hi_mod : (q + i) % n < n := Nat.mod_lt _ (by omega : n > 0)
  have hj_mod : (q + j) % n < n := Nat.mod_lt _ (by omega : n > 0)
  refine ⟨(A ((q + i) % n), A ((q + j) % n)), ?_, ?_⟩
  · constructor
    · apply Finset.mem_product.mpr
      simp only [Finset.mem_image, Finset.mem_range]
      refine ⟨⟨(q + i) % n, hi_mod, rfl⟩, ⟨(q + j) % n, hj_mod, rfl⟩⟩
    · -- A((q+i)%n) ≠ A((q+j)%n)
      simp only
      rw [hv1, hv2]
      exact hne
  · -- dist = d
    simp only
    rw [hv1, hv2]
    exact hd_eq

/--
Required sublemma 1 for strict_maximality_in_slice:
In a convex polygon where A_p A_q is maximal and no side is maximal,
any chord connecting p and an internal vertex i (p < i < q) is strictly shorter.
-/
lemma dist_endpoint_strictly_shorter_in_slice {A : ℕ → V} {n : ℕ} {p q : ℕ}
    (_h_poly : IsConvexPolygon A n)
    (_hp : p < n) (_hq : q < n) (_h_pq : p < q)
    (h_max : ∀ i j, i < n → j < n → dist (A i) (A j) ≤ dist (A p) (A q))
    (_h_strict : ∀ i, i < n → dist (A i) (A ((i + 1) % n)) < dist (A p) (A q))
    (h_strict_p : ∀ i, p < i → i < q → dist (A p) (A i) ≠ dist (A p) (A q))
    {i : ℕ} (hp_i : p < i) (hi_q : i < q) :
    dist (A p) (A i) < dist (A p) (A q) := by
  have h_le : dist (A p) (A i) ≤ dist (A p) (A q) := by
    apply h_max
    · omega
    · omega -- i < q < n implies i < n
  have h_ne : dist (A p) (A i) ≠ dist (A p) (A q) := by
    exact h_strict_p i hp_i hi_q
  exact lt_of_le_of_ne h_le h_ne

/--
Required sublemma 2 for strict_maximality_in_slice:
In a convex polygon where A_p A_q is maximal and no side is maximal,
any chord connecting q and an internal vertex i (p < i < q) is strictly shorter.
-/
lemma dist_rev_endpoint_strictly_shorter_in_slice {A : ℕ → V} {n : ℕ} {p q : ℕ}
    (_h_convex : IsConvexPolygon A n)
    (_hp : p < n) (hq : q < n) (_h_pq : p < q)
    (h_max : ∀ i j, i < n → j < n → dist (A i) (A j) ≤ dist (A p) (A q))
    (_h_strict : ∀ i, i < n → dist (A i) (A ((i + 1) % n)) < dist (A p) (A q))
    (h_strict_q : ∀ i, p < i → i < q → dist (A q) (A i) ≠ dist (A p) (A q))
    {i : ℕ} (hp_i : p < i) (hi_q : i < q) :
    dist (A q) (A i) < dist (A p) (A q) := by
  have h_le : dist (A q) (A i) ≤ dist (A p) (A q) := by
    rw [dist_comm]
    apply h_max
    · omega
    · exact hq
  have h_ne : dist (A q) (A i) ≠ dist (A p) (A q) := by
    exact h_strict_q i hp_i hi_q
  exact lt_of_le_of_ne h_le h_ne

/--
If (p, q) is the global max diagonal, then in the slice AP, the side AP_0 AP_x is strictly maximal.
-/
lemma strict_maximality_in_slice {A : ℕ → V} {n : ℕ} {p q : ℕ}
    (h_poly : IsConvexPolygon A n)
    (hp : p < n) (hq : q < n) (h_pq : p < q)
    (h_max : ∀ i j, i < n → j < n → dist (A i) (A j) ≤ dist (A p) (A q))
    (h_strict : ∀ i, i < n → dist (A i) (A ((i + 1) % n)) < dist (A p) (A q))
    (h_strict_p : ∀ i, p < i → i < q → dist (A p) (A i) ≠ dist (A p) (A q))
    (h_strict_q : ∀ i, p < i → i < q → dist (A q) (A i) ≠ dist (A p) (A q)) :
    let AP := fun i => A (p + i)
    let x := q - p
    ∀ i j, i < x + 1 → j < x + 1 → (i ≠ 0 ∨ j ≠ x) → (i ≠ x ∨ j ≠ 0) →
      dist (AP i) (AP j) < dist (AP 0) (AP x) := by
  intro AP x i j hi hj hne1 hne2
  -- Unfold the let-bindings
  simp only [AP, x] at *

  -- Use A p and A q as reference points
  have h_p0 : p + 0 = p := by simp
  have h_qx : p + (q - p) = q := by omega
  rw [h_p0, h_qx]

  rcases lt_trichotomy i j with hij | heq | hji
  · -- Case: i < j
    by_cases hi0 : i = 0
    · subst hi0
      -- We need p < p + j < q
      have hj_lt : p + j < q := by
        rcases hne1 with h | h
        · contradiction
        · omega
      apply dist_endpoint_strictly_shorter_in_slice h_poly hp hq h_pq h_max h_strict h_strict_p
      · omega
      · exact hj_lt
    · -- i > 0
      by_cases hjx : j = q - p
      · subst hjx
        have cancel : p + (q - p) = q := by omega
        rw [cancel]
        rw [dist_comm]
        apply dist_rev_endpoint_strictly_shorter_in_slice h_poly hp hq h_pq h_max h_strict h_strict_q
        · omega
        · omega
      · -- p < p + i < p + j < q
        apply nested_chord_shorter h_poly
        · omega
        · omega
        · omega
        · exact hq
        · exact h_max
  · -- Case: i = j. dist is 0.
    subst heq
    rw [dist_self]
    -- Distance p q is positive from polygon distinctness
    have h_pos : 0 < dist (A p) (A q) := by
      rw [dist_pos]
      intro h_eq
      have := h_poly.2.1 p q hp hq h_eq
      omega
    exact h_pos
  · -- Case: j < i. Symmetric.
    rw [dist_comm]
    by_cases hj0 : j = 0
    · subst hj0
      have hi_lt : p + i < q := by
        rcases hne2 with h | h
        · omega
        · contradiction
      apply dist_endpoint_strictly_shorter_in_slice h_poly hp hq h_pq h_max h_strict h_strict_p
      · omega
      · exact hi_lt
    · -- j > 0
      by_cases hix : i = q - p
      · subst hix
        have cancel : p + (q - p) = q := by omega
        rw [cancel]
        rw [dist_comm]
        apply dist_rev_endpoint_strictly_shorter_in_slice h_poly hp hq h_pq h_max h_strict h_strict_q
        · omega
        · omega
      · -- p < p + j < p + i < q
        apply nested_chord_shorter h_poly
        · omega
        · omega
        · omega
        · exact hq
        · exact h_max

/--
If (p, q) is the global max diagonal, then in the wrap AQ, the side AQ_0 AQ_(n-x) is weakly maximal.
-/
lemma weak_maximality_in_wrap {A : ℕ → V} {n : ℕ} {p q : ℕ}
    (hp : p < n) (hq : q < n) (_h_pq : p ≤ q)
    (h_max : ∀ i j, i < n → j < n → dist (A i) (A j) ≤ dist (A p) (A q)) :
    let AQ := fun i => A ((q + i) % n)
    let size := n - q + p + 1
    ∀ i j, i < size → j < size → dist (AQ i) (AQ j) ≤ dist (AQ 0) (AQ (size - 1)) := by
  intro AQ size i j hi hj
  -- AQ i = A ((q + i) % n), AQ j = A ((q + j) % n)
  -- AQ 0 = A (q % n) = A q (since q < n)
  -- AQ (size - 1) = A ((q + size - 1) % n) = A ((q + (n - q + p)) % n) = A (p % n) = A p
  -- So dist(AQ 0, AQ (size - 1)) = dist(A q, A p) = dist(A p, A q)
  -- And dist(AQ i, AQ j) = dist(A ((q+i)%n), A ((q+j)%n))
  -- Since (q + i) % n < n and (q + j) % n < n, by h_max we get ≤ dist(A p, A q)
  simp only [AQ]
  have hi_mod : (q + i) % n < n := Nat.mod_lt _ (by omega : n > 0)
  have hj_mod : (q + j) % n < n := Nat.mod_lt _ (by omega : n > 0)
  have h_ineq := h_max ((q + i) % n) ((q + j) % n) hi_mod hj_mod
  -- Need to show dist(AQ 0, AQ (size-1)) = dist(A p, A q)
  have h0 : (q + 0) % n = q := by simp; exact Nat.mod_eq_of_lt hq
  have hs : (q + (size - 1)) % n = p := by
    simp only [size]
    have h_eq : q + (n - q + p + 1 - 1) = n + p := by omega
    rw [h_eq]
    simp [Nat.mod_eq_of_lt hp]
  rw [h0, hs]
  calc dist (A ((q + i) % n)) (A ((q + j) % n))
      ≤ dist (A p) (A q) := h_ineq
    _ = dist (A q) (A p) := dist_comm _ _

-- ============================================================================
/--
Decomposition Lemma:
If no side is maximal (i.e., there exists a strictly longer diagonal), then there exists a diagonal
that splits the polygon into two sub-polygons P and Q such that:
1. P has size x+1 and strictly maximal side.
2. Q has size n-x+1 and maximal side.
3. Distances are subsets of original.
-/
lemma decomposition_lemma {A : ℕ → V} {n : ℕ}
    (h_convex : IsConvexPolygon A n)
    (h_not_side_max : ∃ p q, p < n ∧ q < n ∧
      ∀ i, i < n → dist (A i) (A ((i + 1) % n)) < dist (A p) (A q)) :
    ∃ (x : ℕ) (AP AQ : ℕ → V),
      -- Sizes
      2 ≤ x ∧ x ≤ n - 2 ∧
      -- Convexity
      IsConvexPolygon AP (x + 1) ∧
      IsConvexPolygon AQ (n - x + 1) ∧
      -- Distance containment
      distinctDistances (Finset.image AP (Finset.range (x + 1))) ⊆ distinctDistances (Finset.image A (Finset.range n)) ∧
      distinctDistances (Finset.image AQ (Finset.range (n - x + 1))) ⊆ distinctDistances (Finset.image A (Finset.range n)) ∧
      -- Maximality in AP (Strict)
      (∀ i j, i < x + 1 → j < x + 1 → (i ≠ 0 ∨ j ≠ x) → (i ≠ x ∨ j ≠ 0) →
         dist (AP i) (AP j) < dist (AP 0) (AP x)) ∧
      -- Maximality in AQ (Weak)
      (∀ i j, i < n - x + 1 → j < n - x + 1 → dist (AQ i) (AQ j) ≤ dist (AQ 0) (AQ (n - x))) := by
  -- Get n >= 3 from convexity
  have hn_ge_3 : n ≥ 3 := is_convex_polygon_implies_n_ge_3 h_convex

  -- Use compact space property to find global max
  -- 1. Find the maximum distance value
  let all_pairs := (Finset.range n).product (Finset.range n)
  have h_nonempty : all_pairs.Nonempty := by
    use (0, 1)
    dsimp [all_pairs]
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    omega

  let f_dist (p : ℕ × ℕ) := dist (A p.1) (A p.2)
  obtain ⟨max_pair, h_mem_max, h_global_max_pair⟩ := Finset.exists_max_image all_pairs f_dist h_nonempty
  let max_d := f_dist max_pair

  -- 2. Filter pairs that achieve this maximum distance
  let max_pairs := all_pairs.filter (fun p => f_dist p = max_d)
  have h_max_pairs_nonempty : max_pairs.Nonempty := by
    use max_pair
    simp only [max_pairs, Finset.mem_filter]
    constructor
    · exact h_mem_max
    · rfl

  -- 3. Select pair with MINIMAL span (index difference) among max_pairs
  -- Function to calculate span, handling wrap-around for proper diagonal length?
  -- Wait, index difference `abs (q - p)` or just `q - p`?
  -- All pairs are just (i, j). We want to canonicalize (min < max).
  -- Let's minimize q' - p' where p' = min, q' = max.
  let f_span (p : ℕ × ℕ) := (max p.1 p.2) - (min p.1 p.2)
  obtain ⟨best_pair, h_best_mem, h_min_span⟩ := Finset.exists_min_image max_pairs f_span h_max_pairs_nonempty

  -- Extract p' and q' from best_pair
  let p' := min best_pair.1 best_pair.2
  let q' := max best_pair.1 best_pair.2
  have hp'_lt : p' < n := by
    have h_mem := (Finset.mem_filter.mp h_best_mem).1
    dsimp [all_pairs] at h_mem
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at h_mem
    exact min_lt_of_left_lt h_mem.1
  have hq'_lt : q' < n := by
    have h_mem := (Finset.mem_filter.mp h_best_mem).1
    dsimp [all_pairs] at h_mem
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at h_mem
    exact max_lt h_mem.1 h_mem.2
  have h_pq_order : p' ≤ q' := min_le_max

  -- Properties of our selected p', q'
  have h_dist_eq_max : dist (A p') (A q') = max_d := by
    have h_eq := (Finset.mem_filter.mp h_best_mem).2
    dsimp [p', q', f_dist] at h_eq ⊢
    rcases le_total best_pair.1 best_pair.2 with h | h
    · rw [min_eq_left h, max_eq_right h]; exact h_eq
    · rw [min_eq_right h, max_eq_left h, dist_comm]; exact h_eq

  have h_max_all : ∀ i j, i < n → j < n → dist (A i) (A j) ≤ dist (A p') (A q') := by
    intro i j hi hj
    rw [h_dist_eq_max]
    apply h_global_max_pair (i, j)
    dsimp [all_pairs]
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨hi, hj⟩

  -- Minimal span property: For any OTHER maximal pair, the span is >= current span.
  have h_span_minimal : ∀ i j, i < n → j < n → dist (A i) (A j) = dist (A p') (A q') → (max i j) - (min i j) ≥ q' - p' := by
    intro i j hi hj h_eq
    have h_mem_pairs : (i, j) ∈ max_pairs := by
      rw [Finset.mem_filter]
      constructor
      · dsimp [all_pairs]
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]; exact ⟨hi, hj⟩
      · dsimp [f_dist]; rw [h_dist_eq_max] at h_eq; exact h_eq
    specialize h_min_span (i, j) h_mem_pairs
    dsimp [f_span, p', q' ] at h_min_span ⊢
    exact h_min_span

  -- The diagonal must be strictly larger than all sides (from h_not_side_max).
  have h_diag_strict : ∀ i, i < n → dist (A i) (A ((i + 1) % n)) < dist (A p') (A q') := by
    intro i hi
    obtain ⟨p0, q0, hp0, hq0, h_strict⟩ := h_not_side_max
    specialize h_strict i hi
    apply lt_of_lt_of_le h_strict
    exact h_max_all p0 q0 hp0 hq0

  let x := q' - p'

  -- Need p' < q' for the sub-lemmas
  have h_p'_lt_q' : p' < q' := by
    have h_bounds := maximal_diagonal_not_side hp'_lt hq'_lt h_pq_order h_diag_strict
    omega

  -- Verify x bounds using maximal_diagonal_not_side
  have h_x_bounds : 2 ≤ x ∧ x ≤ n - 2 :=
    maximal_diagonal_not_side hp'_lt hq'_lt h_pq_order h_diag_strict

  -- Define AP
  let AP (i : ℕ) := A (p' + i)
  -- Define AQ
  let AQ (i : ℕ) := A ((q' + i) % n)

  have h_conv_AP : IsConvexPolygon AP (x + 1) := by
    dsimp [AP, x]
    exact is_convex_polygon_slice h_convex hp'_lt hq'_lt (by dsimp [x] at h_x_bounds; omega)

  have h_conv_AQ : IsConvexPolygon AQ (n - x + 1) := by
    have h_len : n - q' + p' + 1 = n - x + 1 := by dsimp [x]; omega
    dsimp [AQ, x]
    rw [← h_len]
    exact is_convex_polygon_wrap h_convex hp'_lt hq'_lt (by dsimp [x] at h_x_bounds; omega) (by dsimp [x] at h_x_bounds; omega)

  have h_subset_AP : distinctDistances (Finset.image AP (Finset.range (x + 1))) ⊆
      distinctDistances (Finset.image A (Finset.range n)) :=
    distinct_distances_slice_subset hp'_lt hq'_lt h_pq_order

  have h_subset_AQ : distinctDistances (Finset.image AQ (Finset.range (n - x + 1))) ⊆
      distinctDistances (Finset.image A (Finset.range n)) := by
    have h_len : n - q' + p' + 1 = n - x + 1 := by dsimp [x]; omega
    rw [← h_len]
    exact distinct_distances_wrap_subset hp'_lt hq'_lt h_pq_order

  have h_strict_AP : ∀ i j, i < x + 1 → j < x + 1 → (i ≠ 0 ∨ j ≠ x) → (i ≠ x ∨ j ≠ 0) →
      dist (AP i) (AP j) < dist (AP 0) (AP x) := by
    apply strict_maximality_in_slice h_convex hp'_lt hq'_lt h_p'_lt_q' h_max_all h_diag_strict
    · -- h_strict_p
      intro i hi_p hi_q h_eq
      have h_span := h_span_minimal p' i hp'_lt (by omega) h_eq
      have h_max_p_i : max p' i = i := max_eq_right (le_of_lt hi_p)
      have h_min_p_i : min p' i = p' := min_eq_left (le_of_lt hi_p)
      rw [h_max_p_i, h_min_p_i] at h_span
      omega
    · -- h_strict_q
      intro i hi_p hi_q h_eq
      have h_span := h_span_minimal q' i hq'_lt (by omega) (by rw [h_eq])
      have h_max_q_i : max q' i = q' := max_eq_left (le_of_lt (by omega))
      have h_min_q_i : min q' i = i := min_eq_right (le_of_lt (by omega))
      rw [h_max_q_i, h_min_q_i] at h_span
      omega

  have h_weak_AQ : ∀ i j, i < n - x + 1 → j < n - x + 1 →
      dist (AQ i) (AQ j) ≤ dist (AQ 0) (AQ (n - x)) := by
    intro i j hi hj
    have h_size_eq : n - x + 1 = n - q' + p' + 1 := by dsimp only [x]; omega
    have hi' : i < n - q' + p' + 1 := by omega
    have hj' : j < n - q' + p' + 1 := by omega
    have h_weak := weak_maximality_in_wrap hp'_lt hq'_lt h_pq_order h_max_all
    have h_res := h_weak i j hi' hj'
    simp only [AQ] at h_res ⊢
    have h_idx_eq : n - q' + p' + 1 - 1 = n - x := by dsimp only [x]; omega
    rw [h_idx_eq] at h_res
    exact h_res

  exact ⟨x, AP, AQ, h_x_bounds.1, h_x_bounds.2, h_conv_AP, h_conv_AQ, h_subset_AP, h_subset_AQ, h_strict_AP, h_weak_AQ⟩



/--
If ConvexIndependent holds for a set s, and A maps bijections to s, then ConvexIndependent holds for A.
-/
lemma convexIndependent_of_eq_image {n : ℕ} {s : Finset V}
    (h_conv : ConvexIndependent ℝ (Subtype.val : s → V))
    (A : ℕ → V) (h_img : (Finset.range n).image A = s)
    (h_inj : Set.InjOn A (Finset.range n)) :
    ConvexIndependent ℝ (fun i : Fin n => A i) := by
  let f : Fin n ↪ s := ⟨fun i => ⟨A i, by rewrite [← h_img]; apply Finset.mem_image_of_mem; simp⟩, by
    intro i j h
    simp at h
    apply Fin.ext
    apply h_inj (Finset.mem_range.mpr i.isLt) (Finset.mem_range.mpr j.isLt) h⟩
  exact h_conv.comp_embedding f

/--
A sorted list without duplicates implies the index mapping is injective.
-/
lemma injective_of_nodup_sorted_get {n : ℕ} (hn : 0 < n) {l : List V} (hl_len : l.length = n) (hl_nodup : l.Nodup)
    (A : ℕ → V) (hA : ∀ i, A i = l.get ⟨i % n, by rw [hl_len]; exact Nat.mod_lt _ hn⟩) :
    Set.InjOn A (Finset.range n) := by
  intro i hi j hj hij;
  simp_all +decide [ Nat.mod_eq_of_lt ];
  exact (List.Nodup.getElem_inj_iff hl_nodup).mp hij

/--
If points are angularly sorted, the open sector between consecutive points contains no other points. (By Aristotle)
-/
lemma angular_sector_empty_of_sorted {n : ℕ} {s : Finset V} (h_n : 3 ≤ n)
    (h_conv : ConvexIndependent ℝ (Subtype.val : s → V))
    (C : V) (hC_int : C ∈ interior (convexHull ℝ (s : Set V)))
    (A : ℕ → V) (h_img : Finset.image A (Finset.range n) = s)
    (h_sorted : ∀ i j, i < n → j < n → i < j → centroid_angle C (A i) < centroid_angle C (A j))
    (i : Fin n) :
    let idx_next := (i.val + 1) % n;
    ∀ pt_x ∈ s, pt_x ≠ A i → pt_x ≠ A idx_next → ¬ (
      centroid_angle C (A i) < centroid_angle C pt_x ∧ centroid_angle C pt_x < centroid_angle C (A idx_next) ∨
      centroid_angle C (A idx_next) < centroid_angle C (A i) ∧ (centroid_angle C pt_x > centroid_angle C (A i) ∨ centroid_angle C pt_x < centroid_angle C (A idx_next))) := by
  intro idx_nxt v_p h_v_s h_v_ni h_v_nn h_dis
  have h_ne_C : C ≠ v_p := by
    intro h_eq_C
    have h_v_fr : v_p ∈ frontier (convexHull ℝ (s : Set V)) := convexIndependent_subset_frontier h_conv h_v_s
    have h_C_fr : C ∈ frontier (convexHull ℝ (s : Set V)) := h_eq_C ▸ h_v_fr
    exact (disjoint_interior_frontier (s := convexHull ℝ (s : Set V))).le_bot ⟨hC_int, h_C_fr⟩

  rw [← h_img] at h_v_s
  obtain ⟨k_val, hk_m, h_eq_vk⟩ := Finset.mem_image.mp h_v_s
  let k_fin : Fin n := ⟨k_val, Finset.mem_range.mp hk_m⟩
  let next_fin : Fin n := ⟨idx_nxt, Nat.mod_lt _ (by linarith [h_n])⟩

  have h_k_ne_i : k_fin ≠ i := by
    intro h; apply h_v_ni; rw [← h_eq_vk]; exact congr_arg A (Fin.ext_iff.mp h)
  have h_k_ne_next : k_fin ≠ next_fin := by
    intro h; apply h_v_nn; rw [← h_eq_vk]; exact congr_arg A (Fin.ext_iff.mp h)

  by_cases h_wrap : i.val + 1 < n
  · have hnext_val : next_fin.val = i.val + 1 := Nat.mod_eq_of_lt h_wrap
    rcases h_dis with h_std | h_wrp
    · by_cases h_ik : i.val < k_fin.val
      · by_cases h_kn : k_fin.val < next_fin.val
        · linarith [hnext_val] -- contradiction: i < k < i+1
        · have h_kne : next_fin.val < k_fin.val := by
            apply Nat.lt_iff_le_and_ne.mpr
            constructor
            · exact not_lt.mp h_kn
            · exact (Fin.ext_iff.not.mp h_k_ne_next.symm)
          have h_ang := h_sorted next_fin.val k_fin.val next_fin.is_lt k_fin.is_lt h_kne
          rw [h_eq_vk] at h_ang
          linarith [h_std.2, h_ang]
      · have h_klt : k_fin.val < i.val := by
          apply Nat.lt_iff_le_and_ne.mpr
          constructor
          · exact not_lt.mp h_ik
          · exact (Fin.ext_iff.not.mp h_k_ne_i)
        have h_ang := h_sorted k_fin.val i.val k_fin.is_lt i.is_lt h_klt
        rw [h_eq_vk] at h_ang
        linarith [h_std.1, h_ang]
    · have hi_idx : i.val < next_fin.val := by rw [hnext_val]; exact i.val.lt_succ_self
      have h_ang : centroid_angle C (A i.val) < centroid_angle C (A next_fin.val) :=
        h_sorted i.val next_fin.val i.is_lt next_fin.is_lt hi_idx
      linarith [h_wrp.1, h_ang]
  · have hi_val : i.val = n - 1 := by have := i.is_lt; omega
    have hnext_val : next_fin.val = 0 := by
      have h_idx : next_fin.val = idx_nxt := rfl
      have h1 : idx_nxt = (i.val + 1) % n := rfl
      rw [hi_val] at h1
      have h2 : (n - 1 + 1) = n := Nat.sub_add_cancel (by linarith [h_n])
      rw [h2, Nat.mod_self] at h1
      rw [h1] at h_idx
      exact h_idx
    rcases h_dis with h_std | h_wrp
    · have h0i : centroid_angle C (A 0) < centroid_angle C (A (n-1)) :=
        h_sorted 0 (n - 1) (by omega) (by omega) (by linarith [h_n])
      have h_ang1 := h_std.1
      have h_ang2 := h_std.2
      rw [hi_val] at h_ang1
      have h_idx0 : idx_nxt = 0 := hnext_val
      rw [h_idx0] at h_ang2
      linarith [h0i]
    · rcases h_wrp.2 with hv_gt | hv_lt
      · have h_klt : k_fin.val < i.val := by have := k_fin.is_lt; omega
        have h_ang := h_sorted k_fin.val i.val k_fin.is_lt i.is_lt h_klt
        rw [h_eq_vk] at h_ang
        linarith [hv_gt, h_ang]
      · have h_nlt : next_fin.val < k_fin.val := by have := k_fin.is_lt; omega
        have h_ang := h_sorted next_fin.val k_fin.val next_fin.is_lt k_fin.is_lt h_nlt
        rw [h_eq_vk] at h_ang
        linarith [hv_lt, h_ang]

lemma openSegment_subset_interior_convex_hull {s : Finset V} {C x : V}
    (hC : C ∈ interior (convexHull ℝ (s : Set V))) (hx : x ∈ convexHull ℝ (s : Set V)) :
    openSegment ℝ C x ⊆ interior (convexHull ℝ (s : Set V)) := by
  intro y hy
  simp [openSegment] at hy
  obtain ⟨a, ha, b, hb, hab, rfl⟩ := hy
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at *
  obtain ⟨ε, ε_pos, hε⟩ := hC
  refine' ⟨a * ε, mul_pos ha ε_pos, fun z hz => _⟩
  obtain ⟨C', hC'⟩ : ∃ C', z = a • C' + b • x ∧ dist C' C < ε := by
    refine' ⟨a⁻¹ • (z - b • x), _, _⟩
    · simp [smul_sub, smul_smul, ha.ne']
    · rw [dist_eq_norm, show a⁻¹ • (z - b • x) - C = a⁻¹ • (z - (a • C + b • x)) by
        simp [smul_sub, smul_add, ← smul_assoc, ha.ne']; abel]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha), inv_mul_lt_iff₀ ha]
      rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz
  rw [hC'.1]
  exact convex_convexHull ℝ (s : Set V) (hε (hC'.2)) hx (le_of_lt ha) (le_of_lt hb) hab

-- (By aristotle, created and proven)
lemma not_subset_halfplane_of_mem_interior_convexHull {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {s : Set V} {f : V →L[ℝ] ℝ} (h_int : 0 ∈ interior (convexHull ℝ s)) (hf : f ≠ 0) :
    ¬ (s ⊆ {x | f x ≤ 0}) := by
      contrapose! h_int;
      -- Since $f$ is continuous and $s \subseteq \{x \mid f x \le 0\}$, the convex hull of $s$ is also contained in $\{x \mid f x \le 0\}$.
      have h_convex_hull : convexHull ℝ s ⊆ {x | f x ≤ 0} := by
        refine' convexHull_min h_int _;
        exact ( convex_iff_forall_pos.mpr fun x hx y hy a b ha hb hab => by simpa [ map_add, map_smul, hab.symm ] using by nlinarith [ hx.out, hy.out ] );
      simp_all +decide [ Set.subset_def, mem_interior_iff_mem_nhds, Metric.mem_nhds_iff ];
      intro ε ε_pos;
      -- Since $f$ is non-zero, there exists some $x$ such that $f(x) > 0$.
      obtain ⟨x, hx⟩ : ∃ x : V, f x > 0 := by
        exact not_forall_not.mp fun h => hf <| ContinuousLinearMap.ext fun x => le_antisymm ( le_of_not_gt fun hx => h x hx ) ( le_of_not_gt fun hx => h ( -x ) <| by simpa using hx );
      -- Choose $t$ such that $0 < t < \min(1, \frac{\epsilon}{\|x\|})$.
      obtain ⟨t, ht_pos, ht_lt⟩ : ∃ t : ℝ, 0 < t ∧ t < min 1 (ε / ‖x‖) := by
        exact exists_between ( lt_min zero_lt_one ( div_pos ε_pos ( norm_pos_iff.mpr ( show x ≠ 0 from by rintro rfl; simp +decide at hx ) ) ) );
      refine' ⟨ t • x, _, _ ⟩ <;> simp_all +decide [ norm_smul, abs_of_pos ];
      · rw [ lt_div_iff₀ ] at ht_lt <;> nlinarith [ norm_pos_iff.2 ( show x ≠ 0 by rintro rfl; simp +decide at hx ) ];
      · intro H; have := h_convex_hull _ H; simp_all +decide ;
        exact this.not_gt ( mul_pos ht_pos hx )
-- (By aristotle, created and proven)
lemma exists_halfplane_functional_of_angle_span {s : Set ℂ} (a b : ℝ)
    (h_len : b - a ≤ Real.pi)
    (h_range : ∀ z ∈ s, z ≠ 0 → ∃ k : ℤ, Complex.arg z + k * 2 * Real.pi ∈ Set.Icc a b) :
    ∃ f : ℂ →L[ℝ] ℝ, f ≠ 0 ∧ ∀ z ∈ s, f z ≤ 0 := by
      by_contra h_contra;
      -- Let $\alpha = (a + b) / 2$ and consider the rotated points $w = z \cdot e^{-i\alpha}$.
      set α : ℝ := (a + b) / 2
      have hw : ∀ z ∈ s, z ≠ 0 → Complex.re (z * Complex.exp (-α * Complex.I)) ≥ 0 := by
        intro z hz hz'; obtain ⟨ k, hk ⟩ := h_range z hz hz'; simp_all +decide [ Complex.exp_re, Complex.exp_im ];
        -- Since $z.arg + k * 2 * π$ is in the interval $[a, b]$, we have $\cos(z.arg + k * 2 * π - α) \geq 0$.
        have h_cos_nonneg : Real.cos (z.arg + k * 2 * Real.pi - α) ≥ 0 := by
          rw [ ← Real.cos_abs ] ; exact Real.cos_nonneg_of_mem_Icc ⟨ by cases abs_cases ( z.arg + k * 2 * Real.pi - ( a + b ) / 2 ) <;> linarith, by cases abs_cases ( z.arg + k * 2 * Real.pi - ( a + b ) / 2 ) <;> linarith ⟩ ;
        convert mul_nonneg ( norm_nonneg z ) h_cos_nonneg using 1
        rw [← Complex.norm_mul_cos_arg z, ← Complex.norm_mul_sin_arg z]
        rw [show z.arg + (k : ℝ) * 2 * Real.pi - α =
            (z.arg - α) + (k : ℝ) * (2 * Real.pi) by ring]
        rw [Real.cos_add_int_mul_two_pi, Real.cos_sub]
        ring
      refine' h_contra ⟨ _, _, _ ⟩;
      exact - ( ContinuousLinearMap.smulRight ( Complex.reCLM ) 1 ) ∘L ( ContinuousLinearMap.mul ℝ ℂ ( Complex.exp ( -α * Complex.I ) ) );
      · intro h; have := congr_arg ( fun f => f ( Complex.exp ( α * Complex.I ) ) ) h; norm_num [ Complex.exp_re, Complex.exp_im ] at this;
        nlinarith [ Real.sin_sq_add_cos_sq α ];
      · intro z hz; specialize hw z hz; by_cases hz' : z = 0 <;> simp_all +decide [ Complex.exp_re, Complex.exp_im ] ;
        linarith
-- (By aristotle, created and proven)
lemma consecutive_angle_diff_lt_pi {n : ℕ} {z : Fin n → ℂ}
    (h_n : 3 ≤ n)
    (h_int : 0 ∈ interior (convexHull ℝ (Set.range z)))
    (h_sorted : ∀ i j : Fin n, i < j → Complex.arg (z i) < Complex.arg (z j))
    (i : Fin n) :
    let next : Fin n := ⟨(i + 1) % n, Nat.mod_lt _ (lt_of_lt_of_le (by norm_num) h_n)⟩
    let diff := if i.val < n - 1 then Complex.arg (z next) - Complex.arg (z i)
                else 2 * Real.pi + Complex.arg (z next) - Complex.arg (z i)
    diff < Real.pi := by
      rcases n with ( _ | _ | n ) <;> simp_all +decide ; aesop;
      split_ifs <;> simp_all +decide [Nat.mod_eq_of_lt ];
      · by_contra h_contra;
        -- By `exists_halfplane_functional_of_angle_span`, there exists `f ≠ 0` such that `f(z j) ≤ 0` for all `j`.
        obtain ⟨f, hf_ne_zero, hf_halfplane⟩ : ∃ f : ℂ →L[ℝ] ℝ, f ≠ 0 ∧ ∀ j : Fin (n + 1 + 1), f (z j) ≤ 0 := by
          have h_angle_span : ∀ j : Fin (n + 1 + 1), ∃ k : ℤ, Complex.arg (z j) + k * 2 * Real.pi ∈ Set.Icc (Complex.arg (z ⟨i.val + 1, by linarith⟩)) (Complex.arg (z i) + 2 * Real.pi) := by
            intro j
            by_cases hj : j ≤ i
            generalize_proofs at *;
            · use 1
              generalize_proofs at *;
              constructor <;> norm_num <;> linarith [ Complex.neg_pi_lt_arg ( z j ), Complex.arg_le_pi ( z j ), Complex.neg_pi_lt_arg ( z i ), Complex.arg_le_pi ( z i ), Complex.neg_pi_lt_arg ( z ⟨ i + 1, by linarith ⟩ ), Complex.arg_le_pi ( z ⟨ i + 1, by linarith ⟩ ), show ( z j |> Complex.arg ) ≤ ( z i |> Complex.arg ) from by exact le_of_not_gt fun h => by linarith [ h_sorted _ _ <| lt_of_le_of_ne hj <| Ne.symm <| by aesop ] ];
            · use 0
              simp;
              constructor;
              · exact monotone_iff_forall_lt.mpr ( fun i j hij => le_of_lt ( h_sorted i j hij ) ) ( show ⟨ i + 1, by linarith ⟩ ≤ j from Nat.succ_le_of_lt ( lt_of_not_ge hj ) );
              · linarith [ Complex.neg_pi_lt_arg ( z j ), Complex.arg_le_pi ( z j ), Complex.neg_pi_lt_arg ( z i ), Complex.arg_le_pi ( z i ) ];
          convert exists_halfplane_functional_of_angle_span ( Complex.arg ( z ⟨ i.val + 1, by linarith ⟩ ) ) ( Complex.arg ( z i ) + 2 * Real.pi ) _ _ using 1 <;> norm_num [ h_angle_span ];
          any_goals exact Set.range z;
          · ext; simp [Set.mem_range];
          · linarith [ Real.pi_pos, Complex.neg_pi_lt_arg ( z i ), Complex.arg_le_pi ( z i ), Complex.neg_pi_lt_arg ( z ⟨ i.val + 1, by linarith ⟩ ), Complex.arg_le_pi ( z ⟨ i.val + 1, by linarith ⟩ ) ];
          · rintro _ ⟨ j, rfl ⟩ hj; specialize h_angle_span j; aesop;
        exact not_subset_halfplane_of_mem_interior_convexHull h_int hf_ne_zero <| Set.range_subset_iff.mpr fun j => hf_halfplane j;
      · -- Since $i = n + 1$, we have $i + 1 = 0$.
        have h_i_plus_one : (↑i + 1 : ℕ) % (n + 1 + 1) = 0 := by
          rw [ Nat.mod_eq_zero_of_dvd ] ; exact ⟨ 1, by linarith [ Fin.is_lt i ] ⟩;
        -- By contradiction, assume that $2\pi + \arg(z_0) - \arg(z_{n+1}) \geq \pi$.
        by_contra h_contra
        have h_halfplane : ∃ f : ℂ →L[ℝ] ℝ, f ≠ 0 ∧ ∀ j : Fin (n + 1 + 1), f (z j) ≤ 0 := by
          have h_halfplane : ∃ f : ℂ →L[ℝ] ℝ, f ≠ 0 ∧ ∀ j : Fin (n + 1 + 1), f (z j) ≤ 0 := by
            have h_arg_range : ∀ j : Fin (n + 1 + 1), (z j).arg ∈ Set.Icc ((z ⟨0, by linarith⟩).arg) ((z i).arg) := by
              intro j; exact ⟨by
              exact if hj : j = ⟨ 0, by linarith ⟩ then hj.symm ▸ le_rfl else le_of_lt ( h_sorted _ _ ( lt_of_le_of_ne ( Nat.zero_le _ ) ( Ne.symm hj ) ) ), by
                exact le_of_not_gt fun h => by linarith [ h_sorted _ _ <| show j < i from lt_of_le_of_ne ( Nat.le_of_lt_succ <| by linarith [ Fin.is_lt j, Fin.is_lt i ] ) <| by aesop ] ;⟩
            convert exists_halfplane_functional_of_angle_span ( ( z ⟨ 0, by linarith ⟩ |> Complex.arg ) ) ( ( z i |> Complex.arg ) ) _ _ using 1 <;> norm_num [ h_arg_range ];
            any_goals exact Set.range z;
            · ext; simp [Set.mem_range];
            · grind;
            · rintro _ ⟨ j, rfl ⟩ hj; use 0; aesop;
          exact h_halfplane;
        obtain ⟨ f, hf_ne_zero, hf ⟩ := h_halfplane; exact not_subset_halfplane_of_mem_interior_convexHull h_int hf_ne_zero <| Set.range_subset_iff.mpr hf;
-- (By aristotle, created and proven)
lemma consecutive_angle_diff_pos {n : ℕ} {z : Fin n → ℂ}
    (h_n : 3 ≤ n)
    (h_sorted : ∀ i j : Fin n, i < j → Complex.arg (z i) < Complex.arg (z j))
    (i : Fin n) :
    let next : Fin n := ⟨(i + 1) % n, Nat.mod_lt _ (lt_of_lt_of_le (by norm_num) h_n)⟩
    let diff := if i.val < n - 1 then Complex.arg (z next) - Complex.arg (z i)
                else 2 * Real.pi + Complex.arg (z next) - Complex.arg (z i)
    0 < diff := by
      split_ifs;
      · convert sub_pos.mpr ( h_sorted i ⟨ ( i + 1 ) % n, Nat.mod_lt _ ( by linarith ) ⟩ _ ) using 1;
        norm_num [ Fin.lt_def ];
        rw [ Nat.mod_eq_of_lt ] <;> linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ n ) ];
      · linarith [ Real.pi_pos, Complex.neg_pi_lt_arg ( z i ), Complex.arg_le_pi ( z i ), Complex.neg_pi_lt_arg ( z ⟨ ( ( i + 1 ) % n ), Nat.mod_lt _ ( by linarith ) ⟩ ), Complex.arg_le_pi ( z ⟨ ( ( i + 1 ) % n ), Nat.mod_lt _ ( by linarith ) ⟩ ) ]
-- (By aristotle, proven)
lemma orientation_sweep_consecutive_pos {n : ℕ} {s : Finset V} {A : ℕ → V} {C : V}
    (h_conv : ConvexIndependent ℝ (Subtype.val : s → V))
    (h_n : 3 ≤ n) (h_img : Finset.image A (Finset.range n) = s)
    (h_sorted : ∀ i j, i < n → j < n → i < j → centroid_angle C (A i) < centroid_angle C (A j))
    (hC_int : C ∈ interior (convexHull ℝ (s : Set V)))
    (h_img_distinct : ∀ {i j}, i < n → j < n → A i = A j → i = j)
    (i : Fin n) :
    0 < (to_complex_map (A ((i.val + 1) % n) - C) / to_complex_map (A i.val - C)).im := by
  -- Let $z_k = to_complex_map (A k - C)$.
  set z : Fin n → ℂ := fun k => to_complex_map (A k - C);
  -- We need to show that $0 < \arg(z_{i+1}) - \arg(z_i) < \pi$.
  have h_arg_diff : 0 < (if i.val < n - 1 then Complex.arg (z (⟨(i + 1) % n, Nat.mod_lt _ (lt_of_lt_of_le (by norm_num) h_n)⟩)) - Complex.arg (z i) else 2 * Real.pi + Complex.arg (z (⟨(i + 1) % n, Nat.mod_lt _ (lt_of_lt_of_le (by norm_num) h_n)⟩)) - Complex.arg (z i)) ∧ (if i.val < n - 1 then Complex.arg (z (⟨(i + 1) % n, Nat.mod_lt _ (lt_of_lt_of_le (by norm_num) h_n)⟩)) - Complex.arg (z i) else 2 * Real.pi + Complex.arg (z (⟨(i + 1) % n, Nat.mod_lt _ (lt_of_lt_of_le (by norm_num) h_n)⟩)) - Complex.arg (z i)) < Real.pi := by
    have h_arg_diff : 0 < (if i.val < n - 1 then Complex.arg (z (⟨(i + 1) % n, Nat.mod_lt _ (lt_of_lt_of_le (by norm_num) h_n)⟩)) - Complex.arg (z i) else 2 * Real.pi + Complex.arg (z (⟨(i + 1) % n, Nat.mod_lt _ (lt_of_lt_of_le (by norm_num) h_n)⟩)) - Complex.arg (z i)) ∧ (if i.val < n - 1 then Complex.arg (z (⟨(i + 1) % n, Nat.mod_lt _ (lt_of_lt_of_le (by norm_num) h_n)⟩)) - Complex.arg (z i) else 2 * Real.pi + Complex.arg (z (⟨(i + 1) % n, Nat.mod_lt _ (lt_of_lt_of_le (by norm_num) h_n)⟩)) - Complex.arg (z i)) < Real.pi := by
      have h_int : 0 ∈ interior (convexHull ℝ (Set.range z)) := by
        have h_arg_diff : 0 ∈ interior (convexHull ℝ (Set.image (fun x => to_complex_map (x - C)) s)) := by
          have h_arg_diff : 0 ∈ interior (Set.image (fun x => to_complex_map (x - C)) (convexHull ℝ (s : Set V))) := by
            have h_arg_diff : IsOpen (Set.image (fun x => to_complex_map (x - C)) (interior (convexHull ℝ (s : Set V)))) := by
              have h_arg_diff : IsOpenMap (fun x => to_complex_map (x - C)) := by
                have h_arg_diff : IsOpenMap (fun x : V => to_complex_map x) := by
                  have h_arg_diff : IsOpenMap (fun x : V => to_complex_map x) := by
                    have h_linear : ∃ (f : V →ₗ[ℝ] ℂ), ∀ x, to_complex_map x = f x := by
                      exact ⟨ to_complex_map.toLinearMap, fun x => rfl ⟩
                    obtain ⟨ f, hf ⟩ := h_linear; simp +decide [ hf ] ;
                    have h_linear : Function.Surjective f := by
                      have h_linear : Function.Surjective (to_complex_map : V → ℂ) := by
                        exact LinearEquiv.surjective _;
                      exact fun x => by obtain ⟨ y, hy ⟩ := h_linear x; exact ⟨ y, by simpa [ hf ] using hy ⟩ ;
                    exact LinearMap.isOpenMap_of_finiteDimensional f h_linear
                  exact h_arg_diff;
                intro s hs; specialize h_arg_diff ( s - { C } ) ; simp_all +decide [ sub_eq_add_neg ] ;
                convert h_arg_diff ( hs.preimage ( continuous_id.add continuous_const ) ) using 1;
                ext; simp [Set.mem_image];
                exact ⟨ fun ⟨ x, hx, hx' ⟩ => ⟨ x - C, by simpa using hx, by simpa using hx' ⟩, fun ⟨ x, hx, hx' ⟩ => ⟨ x + C, by simpa using hx, by simpa using hx' ⟩ ⟩;
              exact h_arg_diff _ ( isOpen_interior );
            refine' mem_interior.mpr _;
            refine' ⟨ _, _, h_arg_diff, _ ⟩;
            · exact Set.image_mono interior_subset;
            · exact ⟨ C, hC_int, by simp +decide ⟩;
          refine' interior_mono _ h_arg_diff;
          intro x hx;
          obtain ⟨ y, hy, rfl ⟩ := hx;
          rw [ convexHull_eq ] at hy ⊢;
          rcases hy with ⟨ ι, t, w, z, hw, hw', hz, rfl ⟩;
          refine' ⟨ ι, t, w, fun i => to_complex_map ( z i - C ), hw, hw', _, _ ⟩
          · intro i hi
            exact ⟨z i, hz i hi, rfl⟩
          · simp_all +decide [ Finset.centerMass ]
            calc
              (∑ x ∈ t, w x • (to_complex_map (z x) - to_complex_map C))
                  = ∑ x ∈ t,
                      ((w x : ℂ) * to_complex_map (z x) - (w x : ℂ) * to_complex_map C) := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    simp
                    ring
              _ = (∑ x ∈ t, (w x : ℂ) * to_complex_map (z x)) -
                    (∑ x ∈ t, (w x : ℂ) * to_complex_map C) := by
                    rw [Finset.sum_sub_distrib]
              _ = (∑ x ∈ t, (w x : ℂ) * to_complex_map (z x)) - to_complex_map C := by
                    congr 1
                    rw [← Finset.sum_mul]
                    norm_cast
                    rw [hw']
                    simp
        convert h_arg_diff using 3;
        ext; simp [z];
        constructor <;> intro h;
        · rcases h with ⟨ y, rfl ⟩ ; exact ⟨ A y, h_img ▸ Finset.mem_image_of_mem _ ( Finset.mem_range.mpr y.2 ), rfl ⟩ ;
        · rcases h with ⟨ x, hx, rfl ⟩ ; rw [ ← h_img ] at hx; obtain ⟨ y, hy, rfl ⟩ := Finset.mem_image.mp hx; exact ⟨ ⟨ y, by linarith [ Finset.mem_range.mp hy ] ⟩, rfl ⟩ ;
      have h_sorted : ∀ i j : Fin n, i < j → Complex.arg (z i) < Complex.arg (z j) := by
        exact fun i j hij => h_sorted i j ( Fin.is_lt i ) ( Fin.is_lt j ) hij
      have := consecutive_angle_diff_lt_pi h_n h_int h_sorted i; have := consecutive_angle_diff_pos h_n h_sorted i; split_ifs at * <;> constructor <;> linarith;
    exact h_arg_diff;
  -- Since $z_k = to_complex_map (A k - C)$, we have $z_k \neq 0$ for all $k$.
  have h_z_ne_zero : ∀ k : Fin n, z k ≠ 0 := by
    intro k hk_zero
    have h_contra : A k = C := by
      exact sub_eq_zero.mp ( to_complex_map.injective <| by aesop );
    have h_contra : C ∈ frontier (convexHull ℝ (s : Set V)) := by
      have h_contra : C ∈ s := by
        exact h_img ▸ Finset.mem_image_of_mem _ ( Finset.mem_range.mpr k.2 ) |> fun h => h_contra ▸ h;
      exact convexIndependent_subset_frontier h_conv ( by simpa );
    exact h_contra.2 hC_int;
  -- Since $z_k = to_complex_map (A k - C)$, we have $z_k \neq 0$ for all $k$, and thus the imaginary part of $z_{i+1} / z_i$ is positive.
  have h_im_pos : 0 < Complex.im (z (⟨(i + 1) % n, Nat.mod_lt _ (lt_of_lt_of_le (by norm_num) h_n)⟩) / z i) := by
    rw [ Complex.div_im ];
    rw [ ← sub_div, lt_div_iff₀ ];
    · have h_sin_pos : 0 < Real.sin ((if i.val < n - 1 then Complex.arg (z (⟨(i + 1) % n, Nat.mod_lt _ (lt_of_lt_of_le (by norm_num) h_n)⟩)) - Complex.arg (z i) else 2 * Real.pi + Complex.arg (z (⟨(i + 1) % n, Nat.mod_lt _ (lt_of_lt_of_le (by norm_num) h_n)⟩)) - Complex.arg (z i))) := by
        exact Real.sin_pos_of_pos_of_lt_pi h_arg_diff.1 h_arg_diff.2;
      convert mul_pos h_sin_pos ( mul_pos ( norm_pos_iff.mpr ( h_z_ne_zero i ) ) ( norm_pos_iff.mpr ( h_z_ne_zero ⟨ ( i + 1 ) % n, Nat.mod_lt _ ( by linarith ) ⟩ ) ) ) using 1 ; simp +decide [ Complex.normSq ] ; ring_nf;
      split_ifs <;> simp +decide [ *, mul_two, Real.sin_add, Real.sin_sub ] <;> ring_nf;
      · rw [ ← Complex.norm_mul_cos_arg, ← Complex.norm_mul_sin_arg, ← Complex.norm_mul_cos_arg, ← Complex.norm_mul_sin_arg ] ; ring_nf;
      · rw [ ← Complex.norm_mul_cos_arg, ← Complex.norm_mul_sin_arg, ← Complex.norm_mul_cos_arg, ← Complex.norm_mul_sin_arg ] ; ring_nf;
    · exact Complex.normSq_pos.mpr ( h_z_ne_zero i );
  convert h_im_pos using 1

-- (proven by Aristotle)
lemma arg_convex_comb_lt {w : ℂ} (hw_im : 0 < w.im)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ((1 - c : ℝ) + c * w : ℂ).arg < w.arg := by
  rw [ Complex.arg, Complex.arg ];
  split_ifs <;> norm_num [ Complex.normSq, Complex.norm_def ] at *;
  any_goals nlinarith [ mul_pos hc0 hw_im ];
  · rw [ Real.arcsin_lt_iff_lt_sin, Real.sin_arcsin ];
    · field_simp;
      refine' Real.lt_sqrt_of_sq_lt _;
      rw [ mul_pow, Real.sq_sqrt ] <;> nlinarith [ mul_pos hc0 hw_im, mul_pos hc0 ( sub_pos.mpr hc1 ) ];
    · exact le_trans ( by norm_num ) ( div_nonneg hw_im.le ( Real.sqrt_nonneg _ ) );
    · exact div_le_one_of_le₀ ( Real.le_sqrt_of_sq_le ( by nlinarith ) ) ( Real.sqrt_nonneg _ );
    · exact ⟨ by rw [ le_div_iff₀ ( Real.sqrt_pos.mpr <| by nlinarith [ mul_pos hc0 hw_im ] ) ] ; nlinarith [ Real.sqrt_nonneg ( ( 1 - c + c * w.re ) * ( 1 - c + c * w.re ) + c * w.im * ( c * w.im ) ), Real.mul_self_sqrt ( by nlinarith [ mul_pos hc0 hw_im ] : 0 ≤ ( 1 - c + c * w.re ) * ( 1 - c + c * w.re ) + c * w.im * ( c * w.im ) ) ], by rw [ div_le_one₀ ( Real.sqrt_pos.mpr <| by nlinarith [ mul_pos hc0 hw_im ] ) ] ; nlinarith [ Real.sqrt_nonneg ( ( 1 - c + c * w.re ) * ( 1 - c + c * w.re ) + c * w.im * ( c * w.im ) ), Real.mul_self_sqrt ( by nlinarith [ mul_pos hc0 hw_im ] : 0 ≤ ( 1 - c + c * w.re ) * ( 1 - c + c * w.re ) + c * w.im * ( c * w.im ) ) ] ⟩;
    · exact ⟨ Real.neg_pi_div_two_le_arcsin _, Real.arcsin_le_pi_div_two _ ⟩;
  · rw [ Real.arcsin_eq_pi_div_two_sub_arccos, Real.arccos_eq_arcsin ];
    · norm_num [ neg_div ];
      linarith [ Real.pi_pos, Real.arcsin_lt_pi_div_two.2 ( show w.im / Real.sqrt ( w.re * w.re + w.im * w.im ) < 1 by rw [ div_lt_one ( Real.sqrt_pos.mpr ( by nlinarith ) ) ] ; exact Real.lt_sqrt_of_sq_lt ( by nlinarith ) ), Real.arcsin_nonneg.2 ( show 0 ≤ Real.sqrt ( 1 - ( c * w.im / Real.sqrt ( ( 1 - c + c * w.re ) * ( 1 - c + c * w.re ) + c * w.im * ( c * w.im ) ) ) ^ 2 ) by positivity ) ];
    · positivity;
  · rw [ Real.arcsin_lt_iff_lt_sin, Real.sin_arcsin ];
    · field_simp;
      rw [ neg_lt_neg_iff ];
      rw [ Real.sqrt_lt' ] <;> ring_nf <;> try positivity;
      rw [ Real.sq_sqrt ] <;> nlinarith [ mul_pos hc0 hw_im, mul_pos hc0 ( sub_pos.mpr hc1 ) ];
    · rw [ le_div_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg ( w.re * w.re + w.im * w.im ), Real.mul_self_sqrt ( add_nonneg ( mul_self_nonneg w.re ) ( mul_self_nonneg w.im ) ) ];
    · exact le_trans ( div_nonpos_of_nonpos_of_nonneg ( neg_nonpos_of_nonneg hw_im.le ) ( Real.sqrt_nonneg _ ) ) ( by norm_num );
    · exact ⟨ by rw [ le_div_iff₀ ( Real.sqrt_pos.mpr <| by nlinarith ) ] ; nlinarith [ Real.sqrt_nonneg ( ( 1 - c + c * w.re ) * ( 1 - c + c * w.re ) + c * w.im * ( c * w.im ) ), Real.mul_self_sqrt ( by nlinarith : 0 ≤ ( 1 - c + c * w.re ) * ( 1 - c + c * w.re ) + c * w.im * ( c * w.im ) ) ], by rw [ div_le_iff₀ ( Real.sqrt_pos.mpr <| by nlinarith ) ] ; nlinarith [ Real.sqrt_nonneg ( ( 1 - c + c * w.re ) * ( 1 - c + c * w.re ) + c * w.im * ( c * w.im ) ), Real.mul_self_sqrt ( by nlinarith : 0 ≤ ( 1 - c + c * w.re ) * ( 1 - c + c * w.re ) + c * w.im * ( c * w.im ) ) ] ⟩;
    · exact ⟨ Real.neg_pi_div_two_le_arcsin _, Real.arcsin_le_pi_div_two _ ⟩


lemma convex_polygon_supporting_line_property {n : ℕ} {s : Finset V} {A : ℕ → V} {C : V}
    (h_conv : ConvexIndependent ℝ (Subtype.val : s → V))
    (h_n : 3 ≤ n) (h_img : Finset.image A (Finset.range n) = s)
    (h_sorted : ∀ i j, i < n → j < n → i < j → centroid_angle C (A i) < centroid_angle C (A j))
    (hC_int : C ∈ interior (convexHull ℝ (s : Set V)))
    (i : Fin n) (f : V →ᵃ[ℝ] ℝ)
    (hf_vi : f (A i) = 0) (hf_vj : f (A ((i + 1) % n)) = 0) (hfC : f C < 0) : ∀ x ∈ s, f x ≤ 0 := by
  intro x hx
  rw [← h_img] at hx; obtain ⟨k_val, hk_mem, rfl⟩ := Finset.mem_image.mp hx
  let k : Fin n := ⟨k_val, Finset.mem_range.mp hk_mem⟩
  let j : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ (by linarith [h_n])⟩
  by_contra h_pos
  rw [not_le] at h_pos

  -- A k cannot be A i or A j because f (A i) = 0 and f (A j) = 0
  have h_k_ne_i : k.val ≠ i.val := by
    intro h_eq; have h_zero : f (A k.val) = 0 := h_eq.symm ▸ hf_vi; linarith [h_pos, h_zero]
  have h_k_ne_j : k.val ≠ j.val := by
    intro h_eq; have h_zero : f (A k.val) = 0 := h_eq.symm ▸ hf_vj; linarith [h_pos, h_zero]

  let t := -f C / (f (A k) - f C)
  have h_denom : f (A k) - f C > 0 := by linarith
  have ht0 : 0 < t := div_pos (neg_pos.mpr hfC) h_denom
  have ht1 : t < 1 := (div_lt_one h_denom).mpr (by linarith)
  let P := (1 - t) • C + t • (A k)

  have hP_f_zero : f P = 0 := by
    rw [show P = t • (A k - C) +ᵥ C by dsimp [P]; module]
    rw [f.map_vadd, f.linear.map_smul]
    have h_lin : f.linear (A k - C) = f (A k) - f C := by
      conv_rhs => rw [← vsub_vadd (A k) C, f.map_vadd]
      simp
    rw [h_lin]
    dsimp [t]
    field_simp [h_denom]
    ring

  have hP_seg : P ∈ openSegment ℝ C (A k) := by
    rw [openSegment_eq_image]; use t; simp [ht0, ht1, P]

  have hP_int : P ∈ interior (convexHull ℝ (s : Set V)) :=
    openSegment_subset_interior_convex_hull hC_int (subset_convexHull _ _ (by rw [← h_img]; apply Finset.mem_image_of_mem; apply Finset.mem_range.mpr; exact k.2)) hP_seg

  have h_inj : ∀ {m1 m2}, m1 < n → m2 < n → A m1 = A m2 → m1 = m2 := by
    intro m1 m2 hm1 hm2 h_eq
    by_cases h12 : m1 < m2
    · have := h_sorted m1 m2 hm1 hm2 h12; rw [h_eq] at this; linarith
    · by_cases h21 : m2 < m1
      · have := h_sorted m2 m1 hm2 hm1 h21; rw [h_eq] at this; linarith
      · linarith

  have hx_ne_Ai : A k ≠ A i := by
    intro h; apply h_k_ne_i; exact h_inj k.2 i.2 h
  have hx_ne_Aj : A k ≠ A j := by
    intro h; apply h_k_ne_j; exact h_inj k.2 j.2 h

  have h_C_ne_Ak : C ≠ A k := by
    intro h_eq; have hf_Ak : f (A k) = f C := h_eq ▸ rfl; linarith [h_pos, hfC, hf_Ak]

  have hP_angle : (centroid_angle C P) = (centroid_angle C (A k)) := by
    dsimp [centroid_angle, P]
    rw [show (1 - t) • C + t • A k - C = t • (A k - C) by
        rw [sub_smul, one_smul, smul_sub]; abel]
    rw [to_complex_map.map_smul]
    exact Complex.arg_real_mul (to_complex_map (A k - C)) ht0

  -- Formulate the angular sector contradiction.
  -- P is in the interior of the hull and lies on the segment (Ai, Aj).
  have hf_lin_ne_zero : f.linear ≠ 0 := by
    intro h
    have h_eval : f (A k) = f.linear (A k - C) + f C := by
      nth_rw 1 [← vsub_vadd (A k) C]
      rw [f.map_vadd]; simp
    rw [h] at h_eval
    simp at h_eval
    linarith [h_denom]

  have h_ij_ne : A i ≠ A j := by
    intro h; have h_val := h_inj i.2 j.2 h; dsimp [j] at h_val
    if h_case : i.val + 1 < n then
      have := Nat.mod_eq_of_lt h_case
      omega
    else
      have h_eq : i.val = n - 1 := by omega
      rw [h_eq] at h_val
      have : (n - 1 + 1) % n = 0 := by
        have : n - 1 + 1 = n := Nat.sub_add_cancel (by linarith [h_n])
        rw [this, Nat.mod_self]
      rw [this] at h_val
      omega

  have hP_AiAj : P ∈ openSegment ℝ (A i) (A j) := by
    have h_prop : ∃ c : ℝ, P -ᵥ A i = c • (A j -ᵥ A i) := by
       have h_ker : Module.finrank ℝ (LinearMap.ker f.linear) = 1 := by
         have := LinearMap.finrank_range_add_finrank_ker f.linear
         rw [(inferInstance : Fact (Module.finrank ℝ V = 2)).out] at this
         have h_range_pos : 0 < Module.finrank ℝ (LinearMap.range f.linear) := by
           rw [Module.finrank_pos_iff_exists_ne_zero]
           use ⟨f.linear (A k - C), LinearMap.mem_range_self _ _⟩
           intro h_zero
           have h_val : f.linear (A k - C) = 0 := Subtype.ext_iff.mp h_zero
           have h_lin : f.linear (A k - C) = f (A k) - f C := by
             rw [← vsub_eq_sub, f.linearMap_vsub, vsub_eq_sub]
           rw [h_lin] at h_val
           linarith [h_denom]
         have : Module.finrank ℝ (LinearMap.range f.linear) = 1 := by
           refine le_antisymm ?_ h_range_pos
           have h_dim : Module.finrank ℝ (LinearMap.range f.linear) ≤ Module.finrank ℝ ℝ :=
             Submodule.finrank_le _
           rw [Module.finrank_self ℝ] at h_dim
           exact h_dim
         linarith
       have h_Pi : P -ᵥ A i ∈ LinearMap.ker f.linear := by
         rw [LinearMap.mem_ker, f.linearMap_vsub, vsub_eq_sub, hP_f_zero, hf_vi, sub_self]
       have h_ji : A j -ᵥ A i ∈ LinearMap.ker f.linear := by
         rw [LinearMap.mem_ker, f.linearMap_vsub, vsub_eq_sub, hf_vj, hf_vi, sub_self]
       have h_ji_ne : A j -ᵥ A i ≠ 0 := by
         intro h; rw [vsub_eq_zero_iff_eq] at h; exact h_ij_ne h.symm
       let K := LinearMap.ker f.linear
       let v : K := ⟨A j -ᵥ A i, h_ji⟩
       let w : K := ⟨P -ᵥ A i, h_Pi⟩
       have hv_ne : v ≠ 0 := by intro h; apply h_ji_ne; exact Subtype.ext_iff.mp h
       obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one h_ker hv_ne w
       use c; have := Subtype.ext_iff.mp hc; dsimp [v, w] at this; exact this.symm
    obtain ⟨c, hc_eq⟩ := h_prop
    have hP_comb : P = (1 - c) • (A i) + c • (A j) := by
      rw [← eq_vadd_iff_vsub_eq] at hc_eq
      rw [hc_eq]; simp [vadd_eq_add, sub_smul, smul_sub]; abel
    rw [openSegment_eq_image]; use c
    refine ⟨⟨?_ , ?_⟩, hP_comb.symm⟩
    · by_contra hc0; push_neg at hc0 -- c <= 0
      if h0 : c = 0 then
        have h_eq : P = A i := by rw [h0] at hP_comb; simp at hP_comb; exact hP_comb
        have hAi_fr := convexIndependent_subset_frontier h_conv (by rw [← h_img]; apply Finset.mem_image_of_mem; exact Finset.mem_range.mpr i.is_lt)
        exact hAi_fr.2 (h_eq ▸ hP_int)
      else
        have : c < 0 := lt_of_le_of_ne hc0 h0
        have hw_seg : A i ∈ openSegment ℝ P (A j) := by
          rw [openSegment_eq_image]; use -c / (1 - c)
          have h_den : 1 - c > 0 := by linarith
          refine' ⟨⟨div_pos (neg_pos.mpr (lt_of_le_of_ne hc0 h0)) h_den, (div_lt_one h_den).mpr (by linarith)⟩, _⟩
          dsimp
          rw [hP_comb, smul_add, smul_smul, smul_smul]
          field_simp [h_den]; simp
        have hAi_int : A i ∈ interior (convexHull ℝ (s : Set V)) :=
          openSegment_subset_interior_convex_hull hP_int (subset_convexHull ℝ (s : Set V) (by rw [← h_img]; apply Finset.mem_image_of_mem; exact Finset.mem_range.mpr j.is_lt)) hw_seg
        have hAi_front := convexIndependent_subset_frontier h_conv (by rw [← h_img]; apply Finset.mem_image_of_mem; exact Finset.mem_range.mpr i.is_lt)
        exact hAi_front.2 hAi_int
    · by_contra hc1; push_neg at hc1 -- c >= 1
      if h1 : c = 1 then
        have h_eq : P = A j := by rw [h1] at hP_comb; simp at hP_comb; exact hP_comb
        have hAj_fr := convexIndependent_subset_frontier h_conv (by rw [← h_img]; apply Finset.mem_image_of_mem; exact Finset.mem_range.mpr j.is_lt)
        exact hAj_fr.2 (h_eq ▸ hP_int)
      else
        have : c > 1 := lt_of_le_of_ne hc1 (by rw [← ne_eq] at h1; exact h1.symm)
        have hw_seg : A j ∈ openSegment ℝ P (A i) := by
          rw [openSegment_eq_image]; use (c - 1) / c
          have h_den : c > 0 := by linarith
          refine' ⟨⟨div_pos (sub_pos.mpr (by linarith)) h_den, (div_lt_one h_den).mpr (by linarith)⟩, _⟩
          dsimp
          rw [hP_comb, smul_add, smul_smul, smul_smul]
          field_simp [h_den]
          have : (1 + -c) / c + (c + -1) / c = 0 := by field_simp [h_den]; ring
          simp [sub_eq_add_neg]
          rw [add_assoc, add_comm (A j), ← add_assoc, ← add_smul, this]
          simp
        have hAj_int : A j ∈ interior (convexHull ℝ (s : Set V)) :=
          openSegment_subset_interior_convex_hull hP_int (subset_convexHull ℝ (s : Set V) (by rw [← h_img]; apply Finset.mem_image_of_mem; exact Finset.mem_range.mpr i.is_lt)) hw_seg
        have hAj_front := convexIndependent_subset_frontier h_conv (by rw [← h_img]; apply Finset.mem_image_of_mem; exact Finset.mem_range.mpr j.is_lt)
        exact hAj_front.2 hAj_int

  have h_sector : centroid_angle C (A i) < centroid_angle C (A k) ∧ centroid_angle C (A k) < centroid_angle C (A j) ∨
                  centroid_angle C (A j) < centroid_angle C (A i) ∧ (centroid_angle C (A k) > centroid_angle C (A i) ∨ centroid_angle C (A k) < centroid_angle C (A j)) := by
    rw [← hP_angle]
    dsimp [centroid_angle]
    rw [openSegment_eq_image] at hP_AiAj
    obtain ⟨c, ⟨hc_pos, hc_lt1⟩, hP_comb⟩ := hP_AiAj
    dsimp at hP_comb
    let z1 := to_complex_map (A i - C)
    let z2 := to_complex_map (A j - C)
    have z1_ne : z1 ≠ 0 := by
      intro h_z
      have h_eq : A i = C := by
        rw [← vsub_eq_zero_iff_eq, ← to_complex_map.map_eq_zero_iff]
        exact h_z
      have hAi_fr := convexIndependent_subset_frontier h_conv (by rw [← h_img]; apply Finset.mem_image_of_mem; exact Finset.mem_range.mpr i.is_lt)
      exact hAi_fr.2 (h_eq ▸ hC_int)
    have z2_ne : z2 ≠ 0 := by
      intro h_z
      have h_eq : A j = C := by
        rw [← vsub_eq_zero_iff_eq, ← to_complex_map.map_eq_zero_iff]
        exact h_z
      have hAj_fr := convexIndependent_subset_frontier h_conv (by rw [← h_img]; apply Finset.mem_image_of_mem; exact Finset.mem_range.mpr j.is_lt)
      exact hAj_fr.2 (h_eq ▸ hC_int)
    -- Since C is in the interior and the segment [Ai, Aj] is on the frontier,
    -- the open segment (Ai, Aj) does not contain C.
    -- Furthermore, no point of the segment can be C.
    have h_complex_arg_between : 0 < c → c < 1 → (1 - c) • z1 + c • z2 ≠ 0 →
        arg ((1 - c) • z1 + c • z2) ∈ (if arg z1 < arg z2 then Ioo (arg z1) (arg z2) else (Ioi (arg z1) ∪ Iio (arg z2))) := by
      intro hc0_lt hc1_lt h_nz
      -- Since z1 ≠ 0 and z2 ≠ 0 are already established as z1_ne, z2_ne,
      -- we can proceed with the argument analysis.
      set z := (1 - c) • z1 + c • z2
      have h_ratio : z / z1 = (1 - c) + c * (z2 / z1) := by
        field_simp [z1_ne]; simp [z]; ring
      have h_im_eq : (z / z1).im = c * (z2 / z1).im := by
        rw [h_ratio]; simp
      have h_det_pos : 0 < (z2 / z1).im := orientation_sweep_consecutive_pos h_conv h_n h_img h_sorted hC_int h_inj i
      have h_arg_pos : 0 < (z2 / z1).arg ∧ (z2 / z1).arg < π := by
        constructor
        · rw [lt_iff_le_and_ne, arg_nonneg_iff]
          refine ⟨h_det_pos.le, fun h => ?_⟩
          have h0 := arg_eq_zero_iff.mp h.symm
          have : (z2 / z1).im = 0 := h0.2
          linarith
        · rw [arg_lt_pi_iff]; exact Or.inr h_det_pos.ne.symm
      have h_ratio_arg : (z / z1).arg ∈ Ioo 0 (z2 / z1).arg := by
        constructor
        · rw [lt_iff_le_and_ne, arg_nonneg_iff]
          refine ⟨(by rw [h_im_eq]; apply mul_nonneg hc0_lt.le h_det_pos.le), fun h_zarg => ?_⟩
          have h0 := arg_eq_zero_iff.mp h_zarg.symm
          have : (z / z1).im = 0 := h0.2
          rw [h_im_eq] at this
          have h_mul_pos : 0 < c * (z2 / z1).im := mul_pos hc0_lt h_det_pos
          linarith
        · -- Monotonicity of arg on the segment [1, z2/z1]
          -- We want to show arg((1-c) + c*(z2/z1)) < arg(z2/z1).
          -- This follows from the fact that (1-c) + c*w lies on the open segment (1, w),
          -- and since 1 has arg 0 and w has arg ∈ (0, π), the argument strictly increases.
          -- We can use the cotangent formula: cot(arg z) = re z / im z.
          -- For z = (1-c) + c*w, im z = c * im w, re z = (1-c) + c * re w.
          -- cot(arg z) = ((1-c) + c * re w) / (c * im w) = (1-c)/(c * im w) + re w / im w.
          -- Since (1-c) > 0, c > 0, and im w > 0, cot(arg z) > cot(arg w).
          -- Since cot is strictly decreasing on (0, π), arg z < arg w.
          rw [h_ratio, ← Complex.ofReal_one, ← Complex.ofReal_sub]
          apply arg_convex_comb_lt h_det_pos hc0_lt hc1_lt
      by_cases h_ord : arg z1 < arg z2
      · -- Non-crossing case: arg z1 < arg z2
        rw [if_pos h_ord]
        have h_z2_sum : arg z2 = arg z1 + arg (z2 / z1) := by
          have h_mul : z2 = z1 * (z2 / z1) := by field_simp [z1_ne]
          have h_mem : arg z1 + arg (z2 / z1) ∈ Set.Ioc (-π) π := by
            constructor
            · linarith [neg_pi_lt_arg z1, h_arg_pos.1]
            · by_contra h_gt'
              rw [not_le] at h_gt'
              have h_wrap : arg z2 = arg z1 + arg (z2 / z1) - 2 * π := by
                rw [← Complex.arg_coe_angle_toReal_eq_arg z2]
                have h_angle : (arg z2 : Real.Angle) = (arg z1 : Real.Angle) + (arg (z2 / z1) : Real.Angle) := by
                  rw [← Complex.arg_mul_coe_angle z1_ne (div_ne_zero z2_ne z1_ne), h_mul]
                  field_simp
                rw [h_angle, ← Real.Angle.coe_add, Real.Angle.toReal_coe_eq_self_sub_two_pi_iff]
                rw [Set.mem_Ioc]
                constructor
                · linarith [h_gt']
                · linarith [arg_le_pi z1, h_arg_pos.2]
              linarith [h_ord, h_wrap]
          rw [h_mul, Complex.arg_mul z1_ne (div_ne_zero z2_ne z1_ne) h_mem]
          simp [z1_ne]
        have h_sum : arg z = arg z1 + arg (z / z1) := by
          have h_mul_z : z = z1 * (z / z1) := by field_simp [z1_ne]
          have h_mem_z : arg z1 + arg (z / z1) ∈ Set.Ioc (-π) π := by
            constructor
            · linarith [neg_pi_lt_arg z1, h_ratio_arg.1]
            · linarith [h_z2_sum, h_ratio_arg.2, arg_le_pi z2]
          rw [h_mul_z, Complex.arg_mul z1_ne (div_ne_zero h_nz z1_ne) h_mem_z]
          simp [z1_ne]
        rw [Set.mem_Ioo, h_sum, h_z2_sum]
        constructor <;> linarith [h_ratio_arg.1, h_ratio_arg.2]
      · -- Crossing case: arg z1 >= arg z2
        rw [if_neg h_ord]
        -- θ2 = θ1 + α2 - 2π
        have h_z2_sum : arg z2 = arg z1 + arg (z2 / z1) - 2 * π := by
          rw [← Complex.arg_coe_angle_toReal_eq_arg z2]
          have h_mul : z2 = z1 * (z2 / z1) := by field_simp [z1_ne]
          have h_angle : (arg z2 : Real.Angle) = (arg z1 : Real.Angle) + (arg (z2 / z1) : Real.Angle) := by
            nth_rw 1 [h_mul]
            rw [Complex.arg_mul_coe_angle z1_ne (div_ne_zero z2_ne z1_ne)]
          rw [h_angle, ← Real.Angle.coe_add, Real.Angle.toReal_coe_eq_self_sub_two_pi_iff]
          rw [Set.mem_Ioc]
          constructor
          · -- Prove π < arg z1 + arg (z2 / z1)
            by_contra h_le_pi
            push_neg at h_le_pi
            have h_mem' : arg z1 + arg (z2 / z1) ∈ Set.Ioc (-π) π := by
              constructor
              · linarith [neg_pi_lt_arg z1, h_arg_pos.1]
              · exact h_le_pi
            have h_eq_arg := Complex.arg_mul z1_ne (div_ne_zero z2_ne z1_ne) h_mem'
            have h_mul_z2 : z2 = z1 * (z2 / z1) := by field_simp [z1_ne]
            rw [← h_mul_z2] at h_eq_arg
            linarith [h_ord, h_arg_pos.1, h_eq_arg]
          · linarith [arg_le_pi z1, h_arg_pos.2]
        by_cases h_wrap : arg z1 + arg (z / z1) ≤ π
        · left; rw [Set.mem_Ioi]
          have h_eq : arg z = arg z1 + arg (z / z1) := by
            have h_mul_z : z = z1 * (z / z1) := by field_simp [z1_ne]
            have h_mem_z : arg z1 + arg (z / z1) ∈ Set.Ioc (-π) π := by
              constructor
              · linarith [neg_pi_lt_arg z1, h_ratio_arg.1]
              · exact h_wrap
            rw [h_mul_z, Complex.arg_mul z1_ne (div_ne_zero h_nz z1_ne) h_mem_z]
            field_simp
          rw [h_eq]; linarith [h_ratio_arg.1]
        · right; rw [Set.mem_Iio]
          have h_eq : arg z = arg z1 + arg (z / z1) - 2 * π := by
            rw [← Complex.arg_coe_angle_toReal_eq_arg z]
            have h_mul_z : z = z1 * (z / z1) := by field_simp [z1_ne]
            have h_angle : (arg z : Real.Angle) = (arg z1 : Real.Angle) + (arg (z / z1) : Real.Angle) := by
              rw [h_mul_z, Complex.arg_mul_coe_angle z1_ne (div_ne_zero h_nz z1_ne)]
              field_simp
            rw [h_angle, ← Real.Angle.coe_add, Real.Angle.toReal_coe_eq_self_sub_two_pi_iff]
            rw [Set.mem_Ioc]
            constructor
            · push_neg at h_wrap; exact h_wrap
            · linarith [arg_le_pi z1, h_ratio_arg.2]
          rw [h_eq]
          have h1 : arg (z / z1) < arg (z2 / z1) := h_ratio_arg.2
          linarith [h_z2_sum, h1]
    have hz_mid : ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → (1 - t) • (A i) + t • (A j) ≠ C := by
      intro t ht0 ht1 h_eq
      -- We show that f is 0 on the segment [Ai, Aj], which contradicts f C < 0.
      have hf_seg : f ((1 - t) • (A i) + t • (A j)) = 0 := by
        have h_affine : (1 - t) • (A i) + t • (A j) = t • (A j -ᵥ A i) +ᵥ A i := by
          simp [vadd_eq_add, vsub_eq_sub, sub_smul, smul_sub]; abel
        rw [h_affine, f.map_vadd, f.linear.map_smul, f.linearMap_vsub, hf_vi, hf_vj]
        simp
      rw [h_eq] at hf_seg
      linarith [hfC, hf_seg]

    have h_between : arg (to_complex_map (P - C)) ∈ (if arg z1 < arg z2 then Ioo (arg z1) (arg z2) else (Ioi (arg z1) ∪ Iio (arg z2))) := by
      have h_eq_vec : P - C = (1 - c) • (A i - C) + c • (A j - C) := by
        rw [← hP_comb]; simp [sub_smul, smul_sub]; abel
      have hzP : to_complex_map (P - C) = (1 - c) • z1 + c • z2 := by
        rw [h_eq_vec, to_complex_map.map_add, to_complex_map.map_smul, to_complex_map.map_smul]
        rfl
      rw [hzP]
      apply h_complex_arg_between
      · exact hc_pos
      · exact hc_lt1
      · intro h_zero
        have : (1 - c) • (A i) + c • (A j) = C := by
          rw [← vsub_eq_zero_iff_eq, show (1-c)•A i + c•A j -ᵥ C = (1-c)•(A i - C) + c•(A j - C) by
            simp [sub_smul, smul_sub]; abel]
          rw [← h_eq_vec, ← to_complex_map.map_eq_zero_iff, hzP, h_zero]
        exact hz_mid c (by linarith [hc_pos]) (by linarith [hc_lt1]) this

    -- Now split into cases based on arg z1 < arg z2
    by_cases h_ordered : arg z1 < arg z2
    · left; constructor
      · rw [if_pos h_ordered] at h_between; exact h_between.1
      · rw [if_pos h_ordered] at h_between; exact h_between.2
    · right; constructor
      · push_neg at h_ordered; refine' lt_of_le_of_ne h_ordered (by
          intro h_eq
          -- This means arg z1 = arg z2.
          -- Since z1, z2 ≠ 0, this implies z1 and z2 are on the same ray from the origin.
          have h_ray : ∃ (r : ℝ), r > 0 ∧ z2 = (r : ℂ) * z1 := by
            let r_val := ‖z2‖ / ‖z1‖
            use r_val
            constructor
            · apply div_pos (norm_pos_iff.mpr z2_ne) (norm_pos_iff.mpr z1_ne)
            · apply Complex.ext
              · simp
                rw [← Complex.norm_mul_cos_arg z2, ← Complex.norm_mul_cos_arg z1]
                rw [h_eq]
                let r := ‖z2‖ / ‖z1‖
                have h_abs : ‖z2‖ = r * ‖z1‖ := by
                  dsimp [r]; field_simp [norm_ne_zero_iff.mpr z1_ne]
                rw [h_abs]; ring
              · simp
                rw [← Complex.norm_mul_sin_arg z2, ← Complex.norm_mul_sin_arg z1]
                rw [h_eq]
                let r := ‖z2‖ / ‖z1‖
                have h_abs : ‖z2‖ = r * ‖z1‖ := by
                  dsimp [r]; field_simp [norm_ne_zero_iff.mpr z1_ne]
                rw [h_abs]; ring
          obtain ⟨r, hr0, hr_eq⟩ := h_ray
          have h_coll : A j = r • (A i -ᵥ C) +ᵥ C := by
            apply to_complex_map.injective
            rw [vadd_eq_add, vsub_eq_sub]
            -- Use the properties of to_complex_map as a linear map
            have h_z1 : z1 = to_complex_map (A i) - to_complex_map C := by simp [z1]
            have h_z2 : z2 = to_complex_map (A j) - to_complex_map C := by simp [z2]
            have h1 : to_complex_map (A j) - to_complex_map C = (r : ℂ) * (to_complex_map (A i) - to_complex_map C) := by
               rw [← h_z2, ← h_z1, hr_eq]
            have h2 : to_complex_map (A j) = (r : ℂ) * to_complex_map (A i) + (1 - r : ℂ) * to_complex_map C := by
               rw [eq_add_of_sub_eq h1]; ring_nf
            have h3 : to_complex_map (r • (A i - C) + C) = (r : ℂ) * to_complex_map (A i) + (1 - r : ℂ) * to_complex_map C := by
               simp only [map_add, map_smul, map_sub, Complex.real_smul]
               ring_nf
            rw [h2, h3]
          -- This implies one of A i, A j is in the interior
          if hr1 : r = 1 then
            have : A j = A i := by
              rw [hr1] at h_coll; simp only [one_smul, vsub_vadd] at h_coll; exact h_coll
            exact h_ij_ne this.symm
          else
            if hr_lt : r < 1 then
              -- A j is in (C, A i)
              have h_seg : A j ∈ openSegment ℝ C (A i) := by
                rw [openSegment_eq_image]; use r
                refine ⟨⟨hr0, hr_lt⟩, ?_⟩
                rw [h_coll]
                simp [vadd_eq_add, vsub_eq_sub, sub_smul, smul_sub]
                abel
              have h_int : A j ∈ interior (convexHull ℝ (s : Set V)) :=
                openSegment_subset_interior_convex_hull hC_int (subset_convexHull ℝ (s : Set V) (by rw [← h_img]; apply Finset.mem_image_of_mem; exact Finset.mem_range.mpr i.is_lt)) h_seg
              have h_fr := convexIndependent_subset_frontier h_conv (by rw [← h_img]; apply Finset.mem_image_of_mem; exact Finset.mem_range.mpr j.is_lt)
              exact h_fr.2 h_int
            else
              -- A i is in (C, A j)
              have h_seg : A i ∈ openSegment ℝ C (A j) := by
                rw [openSegment_eq_image]; use 1/r;
                have hr_gt_one : 1 < r := lt_of_le_of_ne (not_lt.mp hr_lt) (Ne.symm hr1)
                have h1r : 1/r < 1 := (div_lt_one hr0).mpr hr_gt_one
                have h1r0 : 0 < 1/r := div_pos zero_lt_one hr0
                refine ⟨⟨h1r0, h1r⟩, ?_⟩
                have : A i = (r⁻¹) • (A j -ᵥ C) +ᵥ C := by
                  rw [h_coll]
                  simp only [vadd_eq_add, vsub_eq_sub, smul_sub, smul_add, smul_smul]
                  field_simp [ne_of_gt hr0]
                  simp [one_smul]
                rw [this]
                simp only [one_div, vadd_eq_add, vsub_eq_sub, sub_smul, smul_sub, one_smul]
                abel_nf
              have h_int : A i ∈ interior (convexHull ℝ (s : Set V)) :=
                openSegment_subset_interior_convex_hull hC_int (subset_convexHull ℝ (s : Set V) (by rw [← h_img]; apply Finset.mem_image_of_mem; exact Finset.mem_range.mpr j.is_lt)) h_seg
              have h_fr := convexIndependent_subset_frontier h_conv (by rw [← h_img]; apply Finset.mem_image_of_mem; exact Finset.mem_range.mpr i.is_lt)
              exact h_fr.2 h_int)
      · rw [if_neg h_ordered] at h_between; exact h_between

  -- We also need proofs that A k is not A i or A j.
  have hx_ne_next : A k ≠ A j := hx_ne_Aj

  exact angular_sector_empty_of_sorted h_n h_conv C hC_int A h_img h_sorted i (A k) (by rw [← h_img]; apply Finset.mem_image_of_mem; apply Finset.mem_range.mpr; exact k.2) hx_ne_Ai hx_ne_next h_sector

/--
The line through consecutive angular vertices supports the convex hull.
-/
lemma exists_supporting_line_of_angular_sorted {n : ℕ} {s : Finset V} (h_n : 3 ≤ n)
    (h_conv : ConvexIndependent ℝ (Subtype.val : s → V))
    (C : V) (hC_int : C ∈ interior (convexHull ℝ (s : Set V)))
    (A : ℕ → V) (h_img : Finset.image A (Finset.range n) = s)
    (h_sorted : ∀ i j, i < n → j < n → i < j → centroid_angle C (A i) < centroid_angle C (A j))
    (i : Fin n) :
    ∃ f : V →ᵃ[ℝ] ℝ, f.linear ≠ 0 ∧ f (A i) = 0 ∧ f (A ((i + 1) % n)) = 0 ∧ ∀ x ∈ s, f x ≤ 0 := by
  let j : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ (by linarith [h_n])⟩
  let vi := A i; let vj := A j
  let zi := to_complex_map (vi - C); let zj := to_complex_map (vj - C)
  let L_raw : V →ₗ[ℝ] ℝ :=
    { toFun := fun v => (to_complex_map (vj - vi)).re * (to_complex_map v).im -
                       (to_complex_map (vj - vi)).im * (to_complex_map v).re,
      map_add' := by intro u v; simp; ring,
      map_smul' := by intro c v; simp; ring }
  let f_pre : V →ᵃ[ℝ] ℝ := { toFun := fun x => L_raw (x - vi), linear := L_raw, map_vadd' := by intro x v; simp [vadd_eq_add]; ring }

  let det_zj_zi := (zj.re * zi.im - zj.im * zi.re)
  have h_det_zj_zi_ne_zero : det_zj_zi ≠ 0 := by
    intro h_zero
    -- Case vi = vj: angular sorting contradiction
    by_cases h_eq : vi = vj
    · have h_ang_eq : centroid_angle C vi = centroid_angle C vj := by rw [h_eq]
      by_cases h_cs : i.val < j.val
      · have h_lt := h_sorted i.val j.val i.is_lt j.is_lt h_cs
        exact lt_irrefl _ (h_ang_eq ▸ h_lt)
      · have h_jv_val : j.val = (i.val+1)%n := rfl
        rcases i with ⟨iv, hi⟩; rcases j with ⟨jv, hj_lt⟩; dsimp at *
        have h_wrap : iv = n - 1 ∧ jv = 0 := by
          by_cases h_next : iv + 1 < n
          · have h_jv_eq : jv = iv + 1 := by rw [h_jv_val, Nat.mod_eq_of_lt h_next]
            omega
          · have h_iv_eq : iv = n - 1 := by omega
            have h_jv_eq : jv = 0 := by
              rw [h_jv_val, h_iv_eq, Nat.sub_add_cancel (by linarith [h_n])]
              exact Nat.mod_self n
            exact ⟨h_iv_eq, h_jv_eq⟩
        have h_sorted_0_n : centroid_angle C (A 0) < centroid_angle C (A (n-1)) :=
          h_sorted 0 (n-1) (by omega) (by omega) (by omega)
        have h_vi_idx : vi = A (n - 1) := by dsimp [vi]; rw [h_wrap.1]
        have h_vj_idx : vj = A 0 := by dsimp [vj]; rw [h_wrap.2]
        rw [h_vi_idx, h_vj_idx] at h_ang_eq
        exact lt_irrefl _ (h_ang_eq ▸ h_sorted_0_n)

    · -- Case vi != vj: collinearity contradiction
      have h_zi_nz : zi ≠ 0 := by
        intro h_z
        have h_vi_C' : vi - C = 0 := to_complex_map.map_eq_zero_iff.mp h_z
        have h_vi_C : vi = C := eq_of_sub_eq_zero h_vi_C'
        have h_vi_s : vi ∈ s := by
          rw [← h_img]; exact Finset.mem_image_of_mem A (Finset.mem_range.mpr i.is_lt)
        have h_vi_fr : vi ∈ frontier (convexHull ℝ (s : Set V)) :=
          convexIndependent_subset_frontier h_conv h_vi_s
        rw [h_vi_C] at h_vi_fr
        have h_abs : C ∈ interior (convexHull ℝ (s : Set V)) ∩ frontier (convexHull ℝ (s : Set V)) := ⟨hC_int, h_vi_fr⟩
        rw [disjoint_interior_frontier.inter_eq] at h_abs
        exact Set.notMem_empty C h_abs
      have h_zj_nz : zj ≠ 0 := by
        intro h_z
        have h_vj_C' : vj - C = 0 := to_complex_map.map_eq_zero_iff.mp h_z
        have h_vj_C : vj = C := eq_of_sub_eq_zero h_vj_C'
        have h_vj_s : vj ∈ s := by
          rw [← h_img]; exact Finset.mem_image_of_mem A (Finset.mem_range.mpr j.is_lt)
        have h_vj_fr : vj ∈ frontier (convexHull ℝ (s : Set V)) :=
          convexIndependent_subset_frontier h_conv h_vj_s
        rw [h_vj_C] at h_vj_fr
        have h_abs : C ∈ interior (convexHull ℝ (s : Set V)) ∩ frontier (convexHull ℝ (s : Set V)) := ⟨hC_int, h_vj_fr⟩
        rw [disjoint_interior_frontier.inter_eq] at h_abs
        exact Set.notMem_empty C h_abs

      have h_collinear : ∃ k : ℝ, k ≠ 0 ∧ zj = k • zi := by
        -- Algebra: zi.re * zj.im - zi.im * zj.re = 0
        let zi_v := ![zi.re, zi.im]
        let zj_v := ![zj.re, zj.im]
        have h_det_nz : (!![zi.re, zi.im; zj.re, zj.im] : Matrix (Fin 2) (Fin 2) ℝ).det = 0 := by
          rw [Matrix.det_fin_two]; dsimp [det_zj_zi] at h_zero ⊢
          linarith [h_zero]
        have h_dep : ¬ LinearIndependent ℝ ![zi_v, zj_v] := by
          intro h_indep
          have h_unit := (Matrix.linearIndependent_rows_iff_isUnit (K := ℝ) (A := !![zi.re, zi.im; zj.re, zj.im])).1 h_indep
          have h_det_nz_fact := (Matrix.isUnit_iff_isUnit_det !![zi.re, zi.im; zj.re, zj.im]).1 h_unit |>.ne_zero
          rw [h_det_nz] at h_det_nz_fact
          exact h_det_nz_fact rfl
        have h_zi_v_nz : zi_v ≠ 0 := by
          intro h_z; exact h_zi_nz (Complex.ext (congr_fun h_z 0) (congr_fun h_z 1))
        rw [LinearIndependent.pair_iff' h_zi_v_nz] at h_dep
        push_neg at h_dep
        obtain ⟨k, hk⟩ := h_dep
        use k
        have h_k_nz : k ≠ 0 := by
          intro h_k_zero; rw [h_k_zero, zero_smul] at hk
          have h0 := congr_fun hk 0; dsimp [zj_v] at h0
          have h1 := congr_fun hk 1; dsimp [zj_v] at h1
          exact h_zj_nz (Complex.ext h0.symm h1.symm)
        refine ⟨h_k_nz, ?_⟩
        apply Complex.ext
        · have h0 := congr_fun hk 0; dsimp [zj_v, zi_v] at h0
          simp [h0]
        · have h1 := congr_fun hk 1; dsimp [zj_v, zi_v] at h1
          simp [h1]

      obtain ⟨k, hk_nz, hk_eq⟩ := h_collinear
      by_cases hk_pos : 0 < k
      · -- Case k > 0: Same ray
        have h_ray : SameRay ℝ (vi - C) (vj - C) := by
          apply (SameRay.sameRay_map_iff to_complex_map).mp
          simp only [zi, zj, hk_eq]
          exact SameRay.sameRay_pos_smul_right zi hk_pos
        have h_eq_pts : vi = vj := unique_ray_intersection_frontier (convex_convexHull ℝ _)
          (IsCompact.isClosed (Set.Finite.isCompact_convexHull ℝ <| Finset.finite_toSet s)) hC_int
          (convexIndependent_subset_frontier h_conv (by rw [← h_img]; exact Finset.mem_image_of_mem A (Finset.mem_range.mpr i.is_lt)))
          (convexIndependent_subset_frontier h_conv (by rw [← h_img]; exact Finset.mem_image_of_mem A (Finset.mem_range.mpr j.is_lt))) h_ray
        exact h_eq h_eq_pts
      · -- Case k < 0: Opposite rays
        have hk_neg : k < 0 := lt_of_le_of_ne (le_of_not_gt hk_pos) hk_nz
        have h_opp : SameRay ℝ (vi - C) (-(vj - C)) := by
          apply (SameRay.sameRay_map_iff to_complex_map).mp
          rw [map_neg]
          change SameRay ℝ zi (-zj)
          rw [hk_eq]
          simpa [neg_smul] using
            (SameRay.sameRay_pos_smul_right (R := ℝ) (S := ℝ) zi (show 0 < -k by linarith))
        -- This implies C is in the open segment between vi and vj
        have h_C_seg : C ∈ openSegment ℝ vi vj := by
          rw [openSegment_eq_image, Set.mem_image]
          let t := 1 / (1 - k)
          use t
          have h_t_pos : 0 < t := by
            have : 1 - k > 0 := by linarith
            positivity
          have h_t_lt : t < 1 := by
            have : 1 - k > 1 := by linarith
            exact (div_lt_one (by linarith)).mpr this
          refine ⟨⟨h_t_pos, h_t_lt⟩, ?_⟩
          have h_vj_vec : vj - C = k • (vi - C) := by
            apply to_complex_map.injective
            rw [to_complex_map.map_smul]
            simpa [zi, zj] using hk_eq
          have h_vi_decomp : vi = C + (vi - C) := by abel
          have h_vj_decomp : vj = C + (vj - C) := by abel
          rw [h_vi_decomp, h_vj_decomp, h_vj_vec]
          dsimp [t]
          have hden : 1 - k ≠ 0 := by linarith
          have hcoefC : (1 - 1 / (1 - k)) + 1 / (1 - k) = 1 := by ring
          have hcoefd : (1 - 1 / (1 - k)) + (1 / (1 - k)) * k = 0 := by
            field_simp [hden]
            ring
          calc
            (1 - 1 / (1 - k)) • (C + (vi - C)) +
                (1 / (1 - k)) • (C + k • (vi - C))
                = ((1 - 1 / (1 - k)) + 1 / (1 - k)) • C +
                  ((1 - 1 / (1 - k)) + (1 / (1 - k)) * k) • (vi - C) := by
                    rw [smul_add, smul_add, smul_smul]
                    module
            _ = C := by
              rw [hcoefC, hcoefd]
              simp
        -- Contradiction with angular sorted property
        -- Since C is in the interior, all angle differences between consecutive points must be < π.
        -- If zj = k • zi with k < 0, then the angle difference is exactly π.
        have h_ang_diff : (to_complex_map (vj - C)).arg = (to_complex_map (vi - C)).arg + Real.pi ∨
                         (to_complex_map (vj - C)).arg = (to_complex_map (vi - C)).arg - Real.pi := by
          let zi_val := to_complex_map (vi - C)
          let zj_val := to_complex_map (vj - C)
          have h_zj_zi : zj_val = k • zi_val := by
            dsimp [zj_val, zi_val, zi, zj] at *; exact hk_eq
          change zj_val.arg = zi_val.arg + Real.pi ∨ zj_val.arg = zi_val.arg - Real.pi
          rw [h_zj_zi]
          -- arg(k • zi) = arg((-k) • (-zi)) = arg(-zi) since -k > 0
          have h_k_neg : 0 < -k := neg_pos.mpr hk_neg
          have h_mul : k • zi_val = ((-k : ℝ) : ℂ) * (-zi_val) := by simp
          rw [h_mul, Complex.arg_real_mul (-zi_val) h_k_neg]
          by_cases h_pos : 0 < zi_val.im
          · right; rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos h_pos]
          · by_cases h_neg : zi_val.im < 0
            · left; rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg h_neg]
            · -- Case zi.im = 0: since zi != 0, zi.re != 0.
              have h_im_zero : zi_val.im = 0 := by linarith
              have h_re_nz : zi_val.re ≠ 0 := by
                intro h_re; exact h_zi_nz (Complex.ext h_re h_im_zero)
              by_cases h_re_neg : zi_val.re < 0
              · -- arg zi = pi, arg(-zi) = 0
                right
                have h_arg_zi : zi_val.arg = Real.pi := by
                  have : zi_val = (zi_val.re : ℂ) := by
                    apply Complex.ext; simp; simp [h_im_zero]
                  rw [this, Complex.arg_ofReal_of_neg h_re_neg]
                have h_arg_neg_zi : (-zi_val).arg = 0 := by
                  have : -zi_val = ((-zi_val.re : ℝ) : ℂ) := by
                    apply Complex.ext; simp; simp [h_im_zero]
                  rw [this, Complex.arg_ofReal_of_nonneg (by linarith)]
                rw [h_arg_zi, h_arg_neg_zi]; ring
              · -- arg zi = 0, arg(-zi) = pi
                left
                have h_re_pos : 0 < zi_val.re := lt_of_le_of_ne (le_of_not_gt h_re_neg) h_re_nz.symm
                have h_arg_zi : zi_val.arg = 0 := by
                  have : zi_val = (zi_val.re : ℂ) := by
                    apply Complex.ext; simp; simp [h_im_zero]
                  rw [this, Complex.arg_ofReal_of_nonneg h_re_pos.le]
                have h_arg_neg_zi : (-zi_val).arg = Real.pi := by
                  have : -zi_val = ((-zi_val.re : ℝ) : ℂ) := by
                    apply Complex.ext; simp; simp [h_im_zero]
                  rw [this, Complex.arg_ofReal_of_neg (by linarith)]
                rw [h_arg_zi, h_arg_neg_zi]; ring

        -- Let f_line be the functional defining the line through C, vi, vj.
        let f_line : V →ₗ[ℝ] ℝ := {
          toFun := fun v => zi.re * (to_complex_map v).im - zi.im * (to_complex_map v).re,
          map_add' := by intro u v; simp; ring,
          map_smul' := by intro c v; simp; ring }
        have hf_vi : f_line (vi - C) = 0 := by dsimp [f_line, zi]; ring
        have hf_vj : f_line (vj - C) = 0 := by
          change zi.re * zj.im - zi.im * zj.re = 0
          rw [hk_eq]
          simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
          ring

        have h_one_side : (∀ k < n, 0 ≤ f_line (A k - C)) ∨ (∀ k < n, f_line (A k - C) ≤ 0) := by
          let θ := fun k => centroid_angle C (A k)
          have h_θ_sorted : ∀ k1 k2, k1 < n → k2 < n → k1 < k2 → θ k1 < θ k2 := h_sorted

          right; intro k hk
          by_cases h_ki : k = i.val
          · rw [h_ki]; exact hf_vi.le
          by_cases h_kj : k = j.val
          · rw [h_kj]; exact hf_vj.le

          let zk := to_complex_map (A k - C)
          have h_det : f_line (A k - C) = zi.re * zk.im - zi.im * zk.re := rfl

          -- Sign justification via sin
          have h_sin_nonpos : Real.sin (θ k - θ i) ≤ 0 := by
            let iv := i.1; let jv := j.1
            have hi_lt := i.2; have hj_lt := j.2
            have hj_val : jv = (iv + 1) % n := rfl

            have h_total : θ (n-1) - θ 0 < 2 * Real.pi := by
              have h0_mem := Complex.arg_mem_Ioc (to_complex_map (A 0 - C))
              have hn_mem := Complex.arg_mem_Ioc (to_complex_map (A (n-1) - C))
              dsimp [θ, centroid_angle] at *
              linarith [h0_mem.1, hn_mem.2]

            change Real.sin (θ k - θ iv) ≤ 0
            by_cases hij : iv < jv
            · -- j = i + 1
              have h_diff : θ jv = θ iv + Real.pi := by
                rcases h_ang_diff with h_plus | h_minus
                · exact h_plus
                · dsimp [θ, centroid_angle, vi, vj, iv, jv] at *
                  have h_lt := h_θ_sorted iv jv hi_lt hj_lt hij
                  linarith [Real.pi_pos, h_lt, h_minus]

              by_cases h_k_lt : k < iv
              · have h_range : θ k - θ iv ∈ Set.Ioo (-Real.pi) 0 := by
                  constructor
                  · have h_iv0 : θ iv - θ 0 < Real.pi := by
                      have h_total' : θ (n-1) - θ 0 < 2 * Real.pi := h_total
                      have h_nm1_jv : θ jv ≤ θ (n-1) := by
                        by_cases h_eq_nm1 : jv = n-1
                        · rw [h_eq_nm1]
                        · apply (h_θ_sorted jv (n-1) hj_lt (by omega) (by omega)).le
                      linarith [h_total', h_diff, h_nm1_jv]
                    have h_k0 : θ 0 ≤ θ k := by
                      by_cases h_k0 : k = 0
                      · rw [h_k0]
                      · apply (h_θ_sorted 0 k (by omega) hk (by omega)).le
                    linarith [h_iv0, h_k0]
                  · exact sub_neg.mpr (h_θ_sorted k iv hk hi_lt h_k_lt)
                exact Real.sin_nonpos_of_nonpos_of_neg_pi_le h_range.2.le h_range.1.le
              · have h_range : θ k - θ iv ∈ Set.Ioo Real.pi (2 * Real.pi) := by
                  constructor
                  · have : θ jv < θ k := h_θ_sorted jv k hj_lt hk (by
                      have : jv = iv + 1 := by
                        have : iv + 1 < n := by
                          have : jv < n := hj_lt
                          omega
                        rw [hj_val, Nat.mod_eq_of_lt this]
                      omega)
                    linarith [h_diff]
                  · have h_iv0 : θ 0 ≤ θ iv := by
                      by_cases h_iv_zero : iv = 0
                      · rw [h_iv_zero];
                      · apply (h_θ_sorted 0 iv (by omega) hi_lt (by omega)).le
                    have h_kn : θ k ≤ θ (n-1) := by
                      by_cases h_kn : k = n-1
                      · rw [h_kn]
                      · apply (h_θ_sorted k (n-1) hk (by omega) (by omega)).le
                    linarith [h_total, h_iv0, h_kn]
                have h_sin_eq : Real.sin (θ k - θ iv) = -Real.sin (θ k - θ iv - Real.pi) := by
                  rw [← Real.sin_add_pi (θ k - θ iv - Real.pi)]
                  simp
                rw [h_sin_eq]
                apply neg_nonpos.mpr
                apply Real.sin_nonneg_of_nonneg_of_le_pi
                · linarith [h_range.1]
                · linarith [h_range.2]
            · -- Wrap-around Case (jv ≤ iv)
              have hi_eq : iv = n-1 := by
                by_contra h_lt
                have h_iv_lt : iv < n - 1 := by omega
                have h_lt_n : iv + 1 < n := by omega
                have : jv = iv + 1 := by
                  rw [hj_val, Nat.mod_eq_of_lt h_lt_n]
                omega
              have hj_eq : jv = 0 := by
                rw [hi_eq] at hj_val
                have : n - 1 + 1 = n := by omega
                rw [this, Nat.mod_self] at hj_val
                exact hj_val
              have h_sorting : θ 0 < θ (n-1) := h_θ_sorted 0 (n-1) (by omega) (by omega) (by omega)
              have h_diff : θ (n-1) = θ 0 + Real.pi := by
                rcases h_ang_diff with h_plus | h_minus
                · -- θ jv = θ iv + π => θ 0 = θ (n-1) + π
                  dsimp [θ, centroid_angle, vi, vj, iv, jv] at *
                  rw [hi_eq, hj_eq] at h_plus
                  linarith [Real.pi_pos, h_sorting, h_plus]
                · -- θ jv = θ iv - π => θ 0 = θ (n-1) - π
                  dsimp [θ, centroid_angle, vi, vj, iv, jv] at *
                  rw [hi_eq, hj_eq] at h_minus
                  linarith [h_minus]
              have h_range : θ k - θ (n-1) ∈ Set.Ioc (-Real.pi) 0 := by
                constructor
                · have h_k_pos : θ 0 < θ k := by
                    have : k ≠ 0 := by
                      intro h_zero; rw [h_zero] at h_kj
                      have : jv = 0 := hj_eq
                      omega
                    apply h_θ_sorted 0 k (by omega) hk (by omega)
                  linarith [h_diff, h_k_pos]
                · have h_k_lt_nm1 : θ k < θ (n-1) := by
                    have : k ≠ n-1 := by
                      intro h_nm1; rw [h_nm1] at h_ki
                      have : iv = n-1 := hi_eq
                      omega
                    apply h_θ_sorted k (n-1) hk (by omega) (by omega)
                  linarith [h_k_lt_nm1]
              rw [hi_eq]
              exact Real.sin_nonpos_of_nonpos_of_neg_pi_le h_range.2 h_range.1.le

          -- Final link det -> sin
          have h_f_sin : (f_line (A k - C)) = ‖zi‖ * ‖zk‖ * Real.sin (θ k - θ i) := by
            dsimp [f_line, θ, centroid_angle, zi, zk]
            rw [Real.sin_sub]
            have h_re {v : ℂ} (hv : v ≠ 0) : v.re = ‖v‖ * Real.cos v.arg := by
              rw [cos_arg hv, mul_div_cancel₀ v.re (norm_ne_zero_iff.mpr hv)]
            have h_im {v : ℂ} (hv : v ≠ 0) : v.im = ‖v‖ * Real.sin v.arg := by
              rw [sin_arg v, mul_div_cancel₀ v.im (norm_ne_zero_iff.mpr hv)]
            have hzk_nz : zk ≠ 0 := by
              rw [to_complex_map.map_ne_zero_iff, sub_ne_zero]
              intro h_eq
              have hC_fr : C ∈ frontier (convexHull ℝ (s : Set V)) := by
                rw [← h_eq]
                apply convexIndependent_subset_frontier h_conv
                rw [← h_img]; exact Finset.mem_image_of_mem A (Finset.mem_range.mpr hk)
              exact disjoint_interior_frontier.le_bot ⟨hC_int, hC_fr⟩
            rw [h_re h_zi_nz, h_im hzk_nz, h_im h_zi_nz, h_re hzk_nz]
            ring

          rw [h_f_sin]
          have hzi_pos : 0 < ‖zi‖ := norm_pos_iff.mpr h_zi_nz
          have hzk_pos : 0 < ‖zk‖ := by
            have hzk_nz : zk ≠ 0 := by
              rw [to_complex_map.map_ne_zero_iff, sub_ne_zero]
              intro h_eq
              have hC_fr : C ∈ frontier (convexHull ℝ (s : Set V)) := by
                rw [← h_eq]
                apply convexIndependent_subset_frontier h_conv
                rw [← h_img]; exact Finset.mem_image_of_mem A (Finset.mem_range.mpr hk)
              exact disjoint_interior_frontier.le_bot ⟨hC_int, hC_fr⟩
            exact norm_pos_iff.mpr hzk_nz

          apply mul_nonpos_of_nonneg_of_nonpos
          · apply mul_nonneg (le_of_lt hzi_pos) (le_of_lt hzk_pos)
          · exact h_sin_nonpos

        -- A point in the interior of the hull cannot lie on a supporting line.
        rcases h_one_side with h_all | h_all
        · have h_hull : ∀ x ∈ convexHull ℝ (s : Set V), 0 ≤ f_line (x - C) := by
            intro x hx; apply convexHull_min _ _ hx
            · intro p hp; rw [← h_img] at hp; obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hp; exact h_all k' (Finset.mem_range.mp hk')
            · let f_aff : V →ᵃ[ℝ] ℝ := { toFun := fun x => f_line (x - C), linear := f_line, map_vadd' := by intro p v; simp; ring }
              exact (convex_Ici 0).affine_preimage f_aff
          have h_nhds : (convexHull ℝ (s : Set V)) ∈ nhds C := mem_interior_iff_mem_nhds.mp hC_int
          obtain ⟨ε, hε_pos, h_ball_sub⟩ := Metric.nhds_basis_ball.mem_iff.mp h_nhds
          -- f_line is non-zero, so it must take negative values in the ball.
          have hf_nz : f_line ≠ 0 := by
            intro h_f_zero; dsimp [zi] at h_zi_nz
            have h_re : zi.re = f_line ((to_complex_map (V := V)).symm Complex.I) := by
              simp [f_line, to_complex_map.apply_symm_apply]
            have h_im : zi.im = -f_line ((to_complex_map (V := V)).symm 1) := by
              simp [f_line, to_complex_map.apply_symm_apply];
            rw [h_f_zero] at h_re h_im; simp at h_re h_im
            exact h_zi_nz (Complex.ext h_re h_im)
          obtain ⟨u, hu_neg⟩ : ∃ u, f_line u < 0 := by
            have ⟨u_raw, hu_raw⟩ : ∃ u_raw, f_line u_raw ≠ 0 := by
              contrapose! hf_nz; ext v; simp [hf_nz]
            by_cases h : f_line u_raw < 0
            · use u_raw
            · use -u_raw; simp; linarith [lt_of_le_of_ne (le_of_not_gt h) hu_raw.symm]
          -- Scale u to be inside the ball
          let δ := ε / 2 / ‖u‖
          have hδ_pos : 0 < δ := div_pos (half_pos hε_pos) (norm_pos_iff.mpr (fun h => by rw [h] at hu_neg; simp at hu_neg))
          let v := C + δ • u
          have hv_ball : v ∈ Metric.ball C ε := by
            simp [v, Metric.ball, dist_eq_norm]
            have h_nz : u ≠ 0 := by intro h; rw [h] at hu_neg; simp at hu_neg
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ_pos]
            dsimp [δ]; field_simp [norm_pos_iff.mpr h_nz]; linarith
          have hv_neg : f_line (v - C) < 0 := by
            simp [v]; apply mul_neg_of_pos_of_neg hδ_pos hu_neg
          linarith [h_hull v (h_ball_sub hv_ball)]
        · -- Symmetric case k ≥ 0 similarly leads to contradiction
          have h_hull : ∀ x ∈ convexHull ℝ (s : Set V), f_line (x - C) ≤ 0 := by
            intro x hx; apply convexHull_min _ _ hx
            · intro p hp; rw [← h_img] at hp; obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hp; exact h_all k' (Finset.mem_range.mp hk')
            · let f_aff : V →ᵃ[ℝ] ℝ := { toFun := fun x => f_line (x - C), linear := f_line, map_vadd' := by intro p v; simp; ring }
              exact (convex_Iic 0).affine_preimage f_aff
          rw [mem_interior_iff_mem_nhds] at hC_int
          obtain ⟨ε, hε_pos, h_ball_sub⟩ := Metric.nhds_basis_ball.mem_iff.mp hC_int
          have hf_nz : f_line ≠ 0 := by
            intro h_f_zero; dsimp [zi] at h_zi_nz
            have h_re : zi.re = f_line ((to_complex_map.symm Complex.I)) := by
              simp [f_line, to_complex_map.apply_symm_apply]
            have h_im : zi.im = -f_line ((to_complex_map.symm 1)) := by
              simp [f_line, to_complex_map.apply_symm_apply];
            rw [h_f_zero] at h_re h_im; simp at h_re h_im
            exact h_zi_nz (Complex.ext h_re h_im)
          obtain ⟨u, hu_pos⟩ : ∃ u, 0 < f_line u := by
            have ⟨u_raw, hu_raw⟩ : ∃ u_raw, f_line u_raw ≠ 0 := by
              contrapose! hf_nz; ext v; simp [hf_nz]
            by_cases h : 0 < f_line u_raw
            · use u_raw
            · use -u_raw; simp; linarith [lt_of_le_of_ne (le_of_not_gt h) hu_raw]
          let δ := ε / 2 / ‖u‖
          have hδ_pos : 0 < δ := div_pos (half_pos hε_pos) (norm_pos_iff.mpr (fun h => by rw [h] at hu_pos; simp at hu_pos))
          let v := C + δ • u
          have hv_ball : v ∈ Metric.ball C ε := by
            simp [v, Metric.ball, dist_eq_norm]
            have h_nz : u ≠ 0 := by intro h; rw [h] at hu_pos; simp at hu_pos
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ_pos]
            dsimp [δ]; field_simp [norm_pos_iff.mpr h_nz]; linarith
          have hv_pos : 0 < f_line (v - C) := by
            simp [v]; apply mul_pos hδ_pos hu_pos
          linarith [h_hull v (h_ball_sub hv_ball)]


  let s_sign := if 0 < det_zj_zi then (1 : ℝ) else (-1 : ℝ)
  let f : V →ᵃ[ℝ] ℝ := {
    toFun := fun x => s_sign * f_pre x,
    linear := s_sign • L_raw,
    map_vadd' := by
      intro u v; simp [f_pre, L_raw]; ring }
  use f
  refine ⟨?h_linear, ?h_f_vi, ?h_f_vj, ?h_f_Ak⟩
  case h_linear =>
    have h_linear_map : f.linear = s_sign • L_raw := rfl
    rw [h_linear_map, smul_ne_zero_iff]
    refine ⟨by simp [s_sign]; split_ifs <;> norm_num, ?_⟩
    intro h_L_zero
    have h_vi_vj : vi = vj := by
      apply to_complex_map.injective
      apply Complex.ext
      · have h := LinearMap.congr_fun h_L_zero ((to_complex_map (V := V)).symm Complex.I)
        dsimp [L_raw] at h; simp [to_complex_map.apply_symm_apply] at h; exact (sub_eq_zero.mp h).symm
      · have h := LinearMap.congr_fun h_L_zero ((to_complex_map (V := V)).symm 1)
        dsimp [L_raw] at h; simp [to_complex_map.apply_symm_apply] at h; exact sub_eq_zero.mp h
    exact h_det_zj_zi_ne_zero (by dsimp [det_zj_zi, zj, zi]; rw [h_vi_vj]; simp; ring)
  case h_f_vi =>
    simp [f, f_pre, L_raw, vi]
  case h_f_vj =>
    simp [f, s_sign, f_pre, L_raw, vj, vi, j]; ring_nf; simp
  case h_f_Ak =>
    have h_det_zi' : L_raw (C-vi) = -det_zj_zi := by
      dsimp [L_raw, det_zj_zi, vi]
      have h1 : to_complex_map (vj - vi) = zj - zi := by simp [zj, zi, map_sub]
      have h2 : to_complex_map (C - vi) = -zi := by simp [zi, map_sub]
      rw [h1, h2]; dsimp [det_zj_zi]; ring
    have hfC : f C < 0 := by
      dsimp [f, s_sign, f_pre, vi]
      rw [h_det_zi']
      simp; split_ifs with h_pos
      · nlinarith
      · have h_neg : det_zj_zi < 0 := lt_of_le_of_ne (le_of_not_gt h_pos) h_det_zj_zi_ne_zero
        nlinarith
    have hf_vi : f (A i) = 0 := by simp [f, f_pre, L_raw, vi]
    have hf_vj : f (A ((i + 1) % n)) = 0 := by
      simp [f, s_sign, f_pre, L_raw, vj, vi, j]; ring_nf; simp
    exact convex_polygon_supporting_line_property h_conv h_n h_img h_sorted hC_int i f hf_vi hf_vj hfC


/--
Key geometric lemma: if points are sorted angularly around an interior centroid,
the segments connecting consecutive points lie on the frontier of the convex hull.
-/
lemma segment_subset_frontier_of_angular_order {n : ℕ} {s : Finset V}
    (h_n : 3 ≤ n) (h_conv : ConvexIndependent ℝ (Subtype.val : s → V))
    (C : V) (hC_int : C ∈ interior (convexHull ℝ (s : Set V)))
    (A : ℕ → V) (h_img : (Finset.range n).image A = s)
    (h_sorted : ∀ i j, i < n → j < n → i < j →
      centroid_angle C (A i) < centroid_angle C (A j)) :
    ∀ i : Fin n, segment ℝ (A i) (A ((i + 1) % n)) ⊆ frontier (convexHull ℝ (s : Set V)) := by
  intro i
  -- Use the supporting line lemma
  obtain ⟨f, hf_non_trivial, hf_Ai, hf_Anext, hf_s⟩ := exists_supporting_line_of_angular_sorted h_n h_conv C hC_int A h_img h_sorted i

  -- The convex hull is contained in the halfspace {x | f x ≤ 0}
  have h_hull_subset : convexHull ℝ (s : Set V) ⊆ {x | f x ≤ 0} := by
    apply convexHull_min
    · intro x hx; exact hf_s x hx
    · exact (convex_Iic 0).affine_preimage f

  -- The segment is contained in the convex hull
  have h_seg_subset_hull : segment ℝ (A i) (A ((i + 1) % n)) ⊆ convexHull ℝ (s : Set V) := by
    apply segment_subset_convexHull
    · rw [← h_img]; apply Finset.mem_image_of_mem; rw [Finset.mem_range]; exact i.is_lt
    · rw [← h_img]; apply Finset.mem_image_of_mem; rw [Finset.mem_range]; apply Nat.mod_lt; linarith

  -- The segment lies in the hyperplane
  have h_seg_subset_hyperplane : segment ℝ (A i) (A ((i + 1) % n)) ⊆ {x | f x = 0} :=
    ((convex_singleton 0).affine_preimage f).segment_subset hf_Ai hf_Anext

  -- A non-trivial supporting hyperplane intersects the convex hull only at the frontier
  intro x hx
  constructor
  · apply subset_closure; exact h_seg_subset_hull hx
  · intro h_int
    obtain ⟨U, hU_sub, hU_open, hx_U⟩ := mem_interior.mp h_int
    -- exists v s.t. f.linear v > 0
    have : ∃ v, f.linear v > 0 := by
      by_contra h_all_le
      push_neg at h_all_le
      apply hf_non_trivial
      ext v
      exact le_antisymm (h_all_le v) (by simpa using h_all_le (-v))
    obtain ⟨v, hv⟩ := this

    -- Construct point y = x + ε v in U with f y > 0
    obtain ⟨ε, hε_pos, h_ball⟩ := Metric.isOpen_iff.mp hU_open x hx_U
    let t := ε / (2 * ‖v‖)
    have ht_pos : 0 < t := div_pos hε_pos (mul_pos two_pos (norm_pos_iff.mpr (by intro h; rw [h] at hv; simp at hv)))
    let y := x + t • v

    have hy_U : y ∈ U := by
      apply h_ball
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [y]
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (le_of_lt ht_pos)]
      calc
        t * ‖v‖ = (ε / (2 * ‖v‖)) * ‖v‖ := rfl
        _ = ε / 2 := by
          have hv_ne_zero : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr (by intro h; rw [h] at hv; simp at hv)
          field_simp [hv_ne_zero]
        _ < ε := by linarith

    have hfy : f y > 0 := by
      have hfx : f x = 0 := h_seg_subset_hyperplane hx
      simp only [y]
      rw [add_comm, ← vadd_eq_add, f.map_vadd, hfx, vadd_eq_add, add_zero, f.linear.map_smul, smul_eq_mul]
      apply mul_pos ht_pos hv

    have hy_hull : y ∈ convexHull ℝ (s : Set V) := hU_sub hy_U
    have := h_hull_subset hy_hull
    rw [Set.mem_setOf_eq] at this
    linarith

lemma is_convex_polygon_angular_order {n : ℕ} {s : Finset V}
    (h_n : 3 ≤ n)
    (h_card : s.card = n)
    (h_conv : ConvexIndependent ℝ (Subtype.val : s → V))
    (C : V) (hC_int : C ∈ interior (convexHull ℝ (s : Set V)))
    (A : ℕ → V) (h_img : (Finset.range n).image A = s)
    (h_nodup : (s.toList.insertionSort (fun v1 v2 => centroid_angle C v1 < centroid_angle C v2)).Nodup)
    (h_A : ∀ i, A i = (s.toList.insertionSort (fun v1 v2 => centroid_angle C v1 < centroid_angle C v2)).get ⟨i % n, by
      have hl_len : (s.toList.insertionSort (fun v1 v2 => centroid_angle C v1 < centroid_angle C v2)).length = n := by
        rw [List.length_insertionSort, Finset.length_toList, h_card]
      rw [hl_len]; exact Nat.mod_lt _ (by omega)⟩) :
    IsConvexPolygon A n := by
  -- Define the angle function and relations
  let angle := centroid_angle C
  let R_lt := fun v1 v2 => angle v1 < angle v2
  let R_le := fun v1 v2 => angle v1 ≤ angle v2
  let l := s.toList.insertionSort R_lt

  -- Basic properties of l
  have hl_len : l.length = n := by
    rw [List.length_insertionSort, Finset.length_toList, h_card]
  have hn_pos : 0 < n := by omega

  -- 1. Injectivity (using helper lemma)
  have h_inj : Set.InjOn A (Finset.range n) :=
    injective_of_nodup_sorted_get hn_pos hl_len h_nodup A h_A

  -- 2. Convex Independence (using helper lemma)
  have h_conv_A : ConvexIndependent ℝ (fun i : Fin n => A i) :=
    convexIndependent_of_eq_image h_conv A h_img h_inj

  -- 3. Frontier Condition via Angular Order
  -- Prove that the list sorted by '<' is also sorted by '≤'
  have h_total : Std.Total R_le := ⟨fun x y => le_total (angle x) (angle y)⟩
  have h_trans : IsTrans V R_le := ⟨fun x y z hxy hyz => le_trans hxy hyz⟩

  have h_sort_eq : l = s.toList.insertionSort R_le := by
    -- Manual induction to prove insertionSort equality
    let rec aux_insert (x : V) (L : List V) (hx : x ∈ s) (hL_subset : ∀ y ∈ L, y ∈ s) (h_x_not_in_L : x ∉ L) :
        List.orderedInsert R_lt x L = List.orderedInsert R_le x L := by
      induction L with
      | nil => simp [List.orderedInsert]
      | cons y ys ih =>
        have hy : y ∈ s := hL_subset y (List.mem_cons_self)
        have h_ne : x ≠ y := by intro h; rw [h] at h_x_not_in_L; exact h_x_not_in_L (List.mem_cons_self)
        have h_iff : R_lt x y ↔ R_le x y := by
          simp [R_lt, R_le]
          have h_inj := centroid_angle_injective_on_s h_conv C hC_int hx hy
          constructor
          · intro h; exact le_of_lt h
          · intro h; exact lt_of_le_of_ne h (mt h_inj h_ne)
        simp [List.orderedInsert, h_iff]
        by_cases h_cond : R_le x y
        · simp [h_cond]
        · simp [h_cond]
          apply ih
          · intro z hz; apply hL_subset; exact List.mem_cons_of_mem _ hz
          · intro h; apply h_x_not_in_L; exact List.mem_cons_of_mem _ h

    let rec aux_sort (L : List V) (hL_subset : ∀ x ∈ L, x ∈ s) (hL_nodup : L.Nodup) :
        L.insertionSort R_lt = L.insertionSort R_le := by
      induction L with
      | nil => simp [List.insertionSort]
      | cons x xs ih =>
        change List.orderedInsert R_lt x (xs.insertionSort R_lt) =
          List.orderedInsert R_le x (xs.insertionSort R_le)
        have hxs_subset : ∀ z ∈ xs, z ∈ s := fun z hz => hL_subset z (List.mem_cons_of_mem _ hz)
        have hxs_nodup : xs.Nodup := (List.nodup_cons.mp hL_nodup).2
        rw [ih hxs_subset hxs_nodup]
        apply aux_insert
        · exact hL_subset x (List.mem_cons_self)
        · intro z hz
          rw [List.mem_insertionSort] at hz
          exact hxs_subset z hz
        · intro h
          rw [List.mem_insertionSort] at h
          exact (List.nodup_cons.mp hL_nodup).1 h

    exact aux_sort s.toList (fun x hx => Finset.mem_toList.mp hx) (Finset.nodup_toList s)

  -- Use the property that insertionSort with a total relation creates a Sorted list
  have h_sorted_le : l.Pairwise R_le := by
    rw [h_sort_eq]
    exact @List.pairwise_insertionSort V R_le (by infer_instance) h_total h_trans s.toList

  -- Transfer sorted property to A indices
  have h_angle_sorted : ∀ i j, i < n → j < n → i < j → angle (A i) < angle (A j) := by
    intro i j hi hj hij
    rw [h_A i, h_A j]
    let i_fin : Fin l.length := ⟨i % n, by rw [hl_len]; exact Nat.mod_lt _ hn_pos⟩
    let j_fin : Fin l.length := ⟨j % n, by rw [hl_len]; exact Nat.mod_lt _ hn_pos⟩
    have hij_fin : i_fin < j_fin := by
      simp [i_fin, j_fin]
      rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
    -- Direct proof from sorted_le and uniqueness
    have h_le : R_le (l.get i_fin) (l.get j_fin) := by
      exact (List.pairwise_iff_get.mp h_sorted_le) i_fin j_fin hij_fin
    have h_ne_idx : i_fin ≠ j_fin := ne_of_lt hij_fin
    have h_ne : l.get i_fin ≠ l.get j_fin := by
      -- Use pairwise inequality from Nodup
      have h_pw_ne : l.Pairwise (· ≠ ·) := List.nodup_iff_pairwise_ne.mp h_nodup
      exact (List.pairwise_iff_get.mp h_pw_ne) i_fin j_fin hij_fin
    simp [R_le] at h_le
    simp [angle] at *
    exact lt_of_le_of_ne h_le (fun h => h_ne (centroid_angle_injective_on_s h_conv C hC_int
      (Finset.mem_toList.1 ((List.mem_insertionSort (r := R_lt)).mp (List.get_mem l i_fin)))
      (Finset.mem_toList.1 ((List.mem_insertionSort (r := R_lt)).mp (List.get_mem l j_fin)))
      h))

  -- Apply the geometric helper lemma
  have h_frontier : ∀ i : Fin n, segment ℝ (A i) (A ((i + 1) % n)) ⊆ frontier (convexHull ℝ (s : Set V)) :=
    segment_subset_frontier_of_angular_order h_n h_conv C hC_int A h_img h_angle_sorted

  -- 4. Conclusion
  unfold IsConvexPolygon
  refine ⟨h_n, ?_, h_conv_A, ?_⟩
  · intro i j hi hj heq
    apply h_inj (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) heq
  · simp [h_img] at h_frontier ⊢
    exact h_frontier

/--
The function A defined from the angularly sorted list l maps the range 0..n-1 exactly to the set s.
(proven by Aristotle)
-/
lemma angular_order_image_eq_set {n : ℕ} {s : Finset V} (h_n : 0 < n) (h_card : s.card = n)
    (l : List V) (hl_len : l.length = n) (hl_perm : l.Perm s.toList)
    (A : ℕ → V) (hA : ∀ i, A i = l.get ⟨i % n, by rw [hl_len]; exact Nat.mod_lt _ h_n⟩) :
    (Finset.range n).image A = s := by
  have h_image_A : (Finset.image A (Finset.range n)) = l.toFinset := by
    ext x
    simp [hA];
    constructor;
    · rintro ⟨ i, hi, rfl ⟩ ; exact List.getElem_mem _;
    · intro hx;
      obtain ⟨ i, hi ⟩ := List.mem_iff_get.1 hx;
      exact ⟨ i, by simpa [ hl_len ] using i.2, by simpa [ Nat.mod_eq_of_lt ( show i < n from by simpa [ hl_len ] using i.2 ) ] using hi ⟩;
  simp_all +decide [ Finset.ext_iff, List.mem_toFinset ];
  exact fun a => ⟨ fun ha => by simpa using hl_perm.subset ha, fun ha => hl_perm.symm.subset <| by simpa using ha ⟩


lemma exists_convex_polygon_of_convex_independent {n : ℕ} {s : Finset V}
    (h_n : 3 ≤ n)
    (h_card : s.card = n)
    (h_conv : ConvexIndependent ℝ (Subtype.val : s → V)) :
    ∃ A : ℕ → V, IsConvexPolygon A n ∧ (Finset.range n).image A = s := by
  -- 1. Get the centroid as an interior point
  let C := finset_centroid s
  have hC_int : C ∈ interior (convexHull ℝ (s : Set V)) :=
    centroid_in_interior h_conv (by rw [h_card]; exact h_n)

  -- 2. Sort s by angle
  let l := s.toList.insertionSort (fun v1 v2 => centroid_angle C v1 < centroid_angle C v2)
  have hl_len : l.length = n := by rw [List.length_insertionSort, ← h_card, Finset.length_toList]
  have hl_nodup : l.Nodup := by
    have h_perm : List.Perm l s.toList := List.perm_insertionSort _ _
    rw [List.Perm.nodup_iff h_perm]
    apply Finset.nodup_toList

  -- Define A i as the i-th element of l (cyclic)
  let A (i : ℕ) := l.get ⟨i % n, by rw [hl_len]; exact Nat.mod_lt _ (by omega)⟩
  have h_perm : l.Perm s.toList := List.perm_insertionSort _ _

  have h_img : (Finset.range n).image A = s :=
    angular_order_image_eq_set (by omega) h_card l hl_len h_perm A (fun i => rfl)

  use A
  constructor
  · apply is_convex_polygon_angular_order h_n h_card h_conv C hC_int A h_img hl_nodup
    intro i; rfl
  · exact h_img


/--
Helper: Reversing and rotating a convex polygon preserves convexity.
-/
lemma is_convex_polygon_reverse_rotate {A : ℕ → V} {n : ℕ} {k : ℕ}
    (h_poly : IsConvexPolygon A n) :
    IsConvexPolygon (fun i => A ((k + n - i) % n)) n := by
  let f : ℕ → ℕ := fun i => (k + n - i) % n
  let A' := fun i => A (f i)
  unfold IsConvexPolygon
  obtain ⟨hn3, h_dist, h_conv, h_front⟩ := h_poly
  have hn_pos : 0 < n := by omega
  constructor; · exact hn3
  constructor
  · -- Points are distinct
    intro i j hi hj heq
    apply h_dist (f i) (f j) (Nat.mod_lt _ hn_pos) (Nat.mod_lt _ hn_pos) at heq
    dsimp [f] at heq
    have : (i : ℤ) ≡ j [ZMOD n] := by
      have h1 : ((k + n - i : ℕ) : ℤ) ≡ ((k + n - j : ℕ) : ℤ) [ZMOD n] := by
        rw [Int.natCast_modEq_iff]; exact heq
      have hi_le : i ≤ k + n := by omega
      have hj_le : j ≤ k + n := by omega
      rw [Int.ofNat_sub hi_le, Int.ofNat_sub hj_le] at h1
      have h2 : -(i : ℤ) ≡ -(j : ℤ) [ZMOD n] := Int.ModEq.add_left_cancel (Int.ModEq.refl (↑(k + n))) h1
      have hnm := Int.ModEq.neg h2
      simp only [neg_neg] at hnm; exact hnm
    have h_eq : (i : ℤ) % n = (j : ℤ) % n := this
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at h_eq
    exact Int.ofNat_inj.mp h_eq
  constructor
  · -- Convex independent
    let g : Fin n → Fin n := fun i => ⟨f i.1, Nat.mod_lt _ hn_pos⟩
    have h_inv : ∀ i : Fin n, g (g i) = i := by
      intro i; apply Fin.ext; dsimp [g, f]
      refine Nat.ModEq.eq_of_lt_of_lt ?_ (Nat.mod_lt _ hn_pos) i.2
      rw [← Int.natCast_modEq_iff]
      calc
        (↑(f (f i.1)) : ℤ)
        ≡ ↑(k + n - f i.1) [ZMOD n] := by rw [Int.natCast_modEq_iff]; exact Nat.mod_modEq _ _
        _ = ↑(k + n) - ↑(f i.1) := by rw [Int.ofNat_sub (show f i.1 ≤ k+n by dsimp [f]; have := Nat.mod_lt (k+n-i.1) hn_pos; omega)]
        _ ≡ ↑(k + n) - (↑(k + n) - ↑i.1) [ZMOD n] := by
             apply Int.ModEq.sub_left (↑(k + n))
             dsimp [f]
             rw [Int.ofNat_sub (show i.1 ≤ k+n by omega)]
             exact Int.mod_modEq _ _
        _ = ↑i.1 := by have := i.2; omega
    let fe : Fin n ≃ Fin n := ⟨g, g, h_inv, h_inv⟩
    have : (fun i : Fin n => A' i.1) = (fun i : Fin n => A i.1) ∘ fe := by
      ext i; rfl
    rw [this]
    apply h_conv.comp_embedding fe.toEmbedding
  · -- Frontier condition
    intro i
    have h_image_eq : (Finset.range n).image (fun i => A ((k + n - i) % n)) = (Finset.range n).image A := by
      ext v
      simp only [Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨j, hj, hv⟩; exact ⟨(k + n - j) % n, Nat.mod_lt _ hn_pos, hv⟩
      · rintro ⟨j, hj, hv⟩
        let i' := (k + n - j) % n
        use i', Nat.mod_lt _ hn_pos
        rw [← hv]; apply congr_arg A
        refine Nat.ModEq.eq_of_lt_of_lt ?_ (Nat.mod_lt _ hn_pos) hj
        rw [← Int.natCast_modEq_iff]
        calc
          (↑(f i') : ℤ)
          ≡ ↑(k + n - i') [ZMOD n] := by rw [Int.natCast_modEq_iff]; exact Nat.mod_modEq _ _
          _ = ↑(k + n) - ↑i' := by rw [Int.ofNat_sub (show i' ≤ k+n by dsimp [f, i']; have := Nat.mod_lt (k+n-j) hn_pos; omega)]
          _ ≡ ↑(k + n) - (↑(k + n) - ↑j) [ZMOD n] := by
             apply Int.ModEq.sub_left (↑(k + n))
             dsimp [i']
             rw [Int.ofNat_sub (show j ≤ k+n by omega)]
             exact Int.mod_modEq _ _
          _ = ↑j := by have := hj; omega
    rw [h_image_eq]
    let j := f ((i.1 + 1) % n)
    have hj_lt : j < n := Nat.mod_lt _ hn_pos
    have h_fi : f i.1 = (j + 1) % n := by
      dsimp [f, j]
      refine Nat.ModEq.eq_of_lt_of_lt ?_ (Nat.mod_lt _ hn_pos) (Nat.mod_lt _ hn_pos)
      rw [← Int.natCast_modEq_iff]
      calc
        (↑(f i.1) : ℤ)
        ≡ ↑(k + n - i.1) [ZMOD n] := by rw [Int.natCast_modEq_iff]; exact Nat.mod_modEq _ _
        _ = ↑(k + n) - ↑i.1 := by rw [Int.ofNat_sub (show i.1 ≤ k+n by omega)]
        _ = (↑(k + n) - (↑i.1 + 1)) + 1 := by have := i.2; omega
        _ ≡ (↑(k + n) - ↑((i.1 + 1) % n)) + 1 [ZMOD n] := by
           apply Int.ModEq.add_right 1; apply Int.ModEq.sub_left (↑(k + n))
           rw [← Nat.cast_add_one]; exact Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _).symm
        _ = ↑(k + n - (i.1 + 1) % n) + 1 :=
           by have := Nat.mod_lt (i.1+1) hn_pos; rw [Int.ofNat_sub (show (i.1+1)%n ≤ k+n by omega)]
        _ ≡ ↑(f ((i.1 + 1) % n)) + 1 [ZMOD n] := by
           apply Int.ModEq.add_right 1; dsimp [f]; exact Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _).symm
        _ = ↑j + 1 := rfl
        _ ≡ ↑((j + 1) % n) [ZMOD n] := by
           rw [← Nat.cast_add_one]; exact Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _).symm
    have h_seg : segment ℝ (A (f i)) (A (f ((i.1 + 1) % n))) = segment ℝ (A j) (A ((j + 1) % n)) := by
      simp only [j]; rw [h_fi, segment_symm]
    rw [h_seg]
    exact h_front ⟨j, hj_lt⟩

/--
Helper: Distinct distances are invariant under permutation (rotation/reversal) of vertices.
-/
lemma distinct_distances_reverse_rotate {A : ℕ → V} {n : ℕ} {k : ℕ} :
    distinctDistances (Finset.image (fun i => A ((k + n - i) % n)) (Finset.range n)) =
    distinctDistances (Finset.image A (Finset.range n)) := by
  -- The key is that the image of A under the map i ↦ (k + n - i) % n is the same set
  -- because this map is a bijection on {0, ..., n-1}.
  -- Using (k + n - i) instead of (k - i + n) ensures k + n >= i when i < n.
  congr 1
  ext v
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · intro ⟨i, hi, hv⟩
    refine ⟨(k + n - i) % n, Nat.mod_lt _ (by omega : n > 0), hv⟩
  · intro ⟨j, hj, hv⟩
    -- The inverse: given j < n, find i < n such that (k + n - i) % n = j
    -- Use i = (k + n - j) % n. Then (k + n - ((k + n - j) % n)) % n = j when j < n.
    by_cases hn : n = 0
    · omega
    · use (k + n - j) % n
      constructor
      · exact Nat.mod_lt _ (Nat.pos_of_ne_zero hn)
      · -- Show A ((k + n - ((k + n - j) % n)) % n) = A j
        have h_pos : 0 < n := Nat.pos_of_ne_zero hn
        have h_j_lt : j < n := hj
        -- When i < n and k + n >= i (always true since k >= 0 and i < n <= n):
        --   (k + n - i) is in range [k, k + n].
        -- For the inverse, (k + n - j) % n gives a value m in [0, n-1].
        -- Then (k + n - m) % n should equal j.
        have h_idx_eq : (k + n - ((k + n - j) % n)) % n = j := by
          -- Since j < n, we have k + n - j >= k >= 0.
          -- Let m = (k + n - j) % n, so m < n and k + n - j = n * q + m for some q.
          -- Then k + n - m = k + n - (k + n - j - n * q) = j + n * q.
          -- So (k + n - m) % n = (j + n * q) % n = j (since j < n).
          have h1 : j < n := hj
          -- The key calculation
          have h_geq : k + n - j >= (k + n - j) % n := Nat.mod_le _ _
          have h_eq : k + n - ((k + n - j) % n) = j + n * ((k + n - j) / n) := by
            have := Nat.div_add_mod (k + n - j) n
            omega
          rw [h_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
        rw [h_idx_eq, hv]

/--
Helper: If A k A (k+1) is maximal in A, then A' 0 A' (n-1) is maximal in A' (reversed rotated).
-/
lemma max_dist_reverse_rotate {A : ℕ → V} {n : ℕ} {k : ℕ}
    (hk_lt_n : k < n)
    (h_max_side : ∀ i j, i < n → j < n → dist (A i) (A j) ≤ dist (A k) (A ((k + 1) % n))) :
    let A' := fun i => A ((k + n - i) % n)
    ∀ i j, i < n → j < n → dist (A' i) (A' j) ≤ dist (A' 0) (A' (n - 1)) := by
  intro A' i j hi hj
  simp only [A']
  have hi_mod : (k + n - i) % n < n := Nat.mod_lt _ (by omega : n > 0)
  have hj_mod : (k + n - j) % n < n := Nat.mod_lt _ (by omega : n > 0)
  have h_ineq := h_max_side _ _ hi_mod hj_mod
  -- A' 0 = A ((k + n - 0) % n) = A ((k + n) % n) = A k (since k < n, k + n >= n, so mod gives k)
  have h0 : (k + n - 0) % n = k := by
    simp only [Nat.sub_zero]
    rw [Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hk_lt_n]
  -- A' (n-1) = A ((k + n - (n-1)) % n) = A ((k + 1) % n)
  have hn1 : (k + n - (n - 1)) % n = (k + 1) % n := by
    have h1 : k + n - (n - 1) = k + 1 := by omega
    rw [h1]
  rw [h0, hn1]
  exact h_ineq

/--
Helper: If n >= 2, distinct distances is nonempty.
-/
lemma distinct_distances_nonempty_of_ge_2 {s : Finset V} (h : 2 ≤ s.card) :
    (distinctDistances s).Nonempty := by
  have h_ne : ∃ x ∈ s, ∃ y ∈ s, x ≠ y := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
    obtain ⟨y, hy, hxy⟩ := Finset.exists_mem_ne (by omega : 1 < s.card) x
    exact ⟨x, hx, y, hy, hxy.symm⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := h_ne
  use dist x y
  simp [distinctDistances]
  use x, y

/--
Altman-Erdos Theorem (1963):
If n distinct points in R^2 form a convex polygon, then they determine at least floor(n/2) distinct distances.
-/
theorem altman_erdos (s : Finset V) (n : ℕ)
    (h_n : 3 ≤ n)
    (h_card : s.card = n)
    (h_conv : ConvexIndependent ℝ (Subtype.val : s → V)) :
    (distinctDistances s).card ≥ n / 2 := by
  -- Bridge to ordered polygon
  have h_poly_exists : ∃ A : ℕ → V, IsConvexPolygon A n ∧ (Finset.range n).image A = s :=
    exists_convex_polygon_of_convex_independent h_n h_card h_conv
  obtain ⟨A, h_poly, h_range⟩ := h_poly_exists

  -- Define D_A as the set of distinct distances of the polygon A
  let D_A := distinctDistances (Finset.image A (Finset.range n))
  have h_D_eq : D_A = distinctDistances s := by
    dsimp [D_A]
    rw [h_range]

  by_contra h_contra
  rw [← h_D_eq] at h_contra
  have h_len : D_A.card < n / 2 := lt_of_not_ge h_contra

  -- Check if some side is maximal among all distances
  by_cases h_side_max : ∃ k, k < n ∧ ∀ i j, i < n → j < n → dist (A i) (A j) ≤ dist (A k) (A ((k + 1) % n))
  · -- Case 1: Max distance is achieved by a side
    obtain ⟨k, hk_lt_n, hk_max⟩ := h_side_max

    let A' (i : ℕ) := A ((k + n - i) % n)
    have h_poly' : IsConvexPolygon A' n := is_convex_polygon_reverse_rotate h_poly

    have h_max' : ∀ i j, i < n → j < n → dist (A' i) (A' j) ≤ dist (A' 0) (A' (n - 1)) :=
      max_dist_reverse_rotate hk_lt_n hk_max

    have h_D_A' : distinctDistances (Finset.image A' (Finset.range n)) = D_A :=
      distinct_distances_reverse_rotate

    have h_lemma2 := altman_lemma_2 h_poly' h_max'
    rw [h_D_A'] at h_lemma2

    -- Contradiction derivations
    have h_n_ge_4 : n - 2 < n / 2 := lt_of_le_of_lt h_lemma2 h_len

    by_cases hn_small : n < 4
    · -- Handle small n
      rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 by omega) with rfl | rfl | rfl | rfl
      · omega
      · omega
      · have : D_A.Nonempty := by
           rw [h_D_eq]
           refine distinct_distances_nonempty_of_ge_2 ?_
           rw [h_card]
        have : 1 ≤ D_A.card := Finset.card_pos.mpr this
        omega
      · have : D_A.Nonempty := by
           rw [h_D_eq]
           refine distinct_distances_nonempty_of_ge_2 ?_
           rw [h_card]; norm_num
        have : 1 ≤ D_A.card := Finset.card_pos.mpr this
        omega
    · -- n >= 4
      omega

  · -- Case 2: No side is maximal.
    push_neg at h_side_max

    have h_strict : ∃ p q, p < n ∧ q < n ∧ ∀ i, i < n → dist (A i) (A ((i + 1) % n)) < dist (A p) (A q) := by
      let all_pairs := (Finset.range n).product (Finset.range n)
      have h_nonempty : all_pairs.Nonempty := by
        by_cases hn : 2 ≤ n
        · use (0, 1)
          dsimp [all_pairs]
          rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
          constructor <;> apply lt_of_lt_of_le (by norm_num) hn
        · have : n < 2 := by omega
          simp at h_len
          have : n / 2 = 0 := by omega
          rw [this] at h_len
          omega

      let f (p : ℕ × ℕ) := dist (A p.1) (A p.2)
      obtain ⟨⟨p_idx, q_idx⟩, h_mem, h_max⟩ := Finset.exists_max_image all_pairs f h_nonempty

      dsimp [all_pairs] at h_mem
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at h_mem
      use p_idx, q_idx
      refine ⟨h_mem.1, h_mem.2, fun i hi => ?_⟩
      specialize h_side_max i hi
      obtain ⟨ip, iq, hip, hiq, h_gt⟩ := h_side_max
      have h_le : dist (A ip) (A iq) ≤ dist (A p_idx) (A q_idx) := by
        specialize h_max (ip, iq)
        dsimp [all_pairs] at h_max
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at h_max
        exact h_max ⟨hip, hiq⟩
      exact lt_of_lt_of_le h_gt h_le

    obtain ⟨x, AP, AQ, h_decomp_props⟩ := decomposition_lemma h_poly h_strict
    rcases h_decomp_props with ⟨h_ge_2, h_le_n2, h_poly_P, h_poly_Q, h_dist_P, h_dist_Q, h_strict_P, h_weak_Q⟩


    have h_strong := altman_lemma_2_strong h_poly_P h_strict_P
    let DP := distinctDistances (Finset.image AP (Finset.range (x + 1)))

    have h_weak := altman_lemma_2 h_poly_Q h_weak_Q
    let DQ := distinctDistances (Finset.image AQ (Finset.range (n - x + 1)))

    have h_card_P : DP.card ≥ x := by
      have := h_strong
      simp at this ⊢
      exact this

    have h_card_Q : DQ.card ≥ n - x - 1 := by
      have := h_weak
      simp at this ⊢
      exact this

    have h1 : x < n / 2 := lt_of_le_of_lt (le_trans h_card_P (Finset.card_le_card h_dist_P)) h_len
    have h2 : n - x - 1 < n / 2 := lt_of_le_of_lt (le_trans h_card_Q (Finset.card_le_card h_dist_Q)) h_len

    have h_contradiction_final : False := by
      omega

    exact h_contradiction_final
#print axioms altman_erdos
-- 'Erdos93.altman_erdos' depends on axioms: [propext, Classical.choice, Quot.sound]

end
end Erdos93
