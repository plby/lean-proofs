/-

This is a Lean formalization of a solution to Erdős Problem 1007.
https://www.erdosproblems.com/forum/thread/1007

The original proof was found by: Roger House

[Ho13] House, Roger F., A 4-dimensional graph has at least 9
edges. Discrete Math. (2013), 1783--1789.

[ChNo16] Chaffee, Joe and Noble, Matt, Dimension 4 and dimension 5
graphs with minimum edge set. Australas. J. Combin. (2016), 327--333.


The proof was auto-formalized by Aristotle (from Harmonic).  Aristotle
was supplied with a proof that K_{3,3} does not embed into R^3.
Aristotle was not supplied with a proof that smaller graphs do.

The final theorem statement was written by Aristotle.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We proved that the complete bipartite graph K_{3,3} has 9 edges.
We proved that any graph with fewer than 9 edges has a unit-distance embedding in R^3.
We concluded that the smallest number of edges in a graph with dimension 4 is 9.
-/

/-
This module defines unit-distance embeddings and graph dimension, and proves that the dimension of K_{3,3} is 4.
It includes the following results:
- `exists_embedding`: Every finite graph has a unit-distance embedding in some dimension.
- `sphere_intersection_infinite`: The intersection of two unit spheres in R^3 is infinite.
- `line_inter_sphere_at_most_two`: A line intersects a sphere in at most two points.
- `planes_inter_is_line`: The intersection of two non-parallel planes in R^3 is a line.
- `three_spheres_intersection`: The intersection of three unit spheres centered at distinct points in R^3 has at most two points.
- `three_spheres_intersection_finite`: The intersection of three unit spheres centered at distinct points in R^3 is finite.
- `dim_K33_le_4`: K_{3,3} has dimension at most 4.
- `dim_K33_eq_4`: The dimension of K_{3,3} is exactly 4.
-/

/-
The following results were available but removed during simplification:
- `embedding_of_subgraph`: Subgraphs inherit unit-distance embeddings.
- `embedding_monotone`: If a graph embeds in dimension n, it embeds in dimension m >= n.
- `dim_monotone`: Graph dimension is monotonic under subgraphs.
- `dim_isolated`: Graph dimension is invariant under adding/removing isolated vertices.
- `sphere_inter_sphere_subset_hyperplane`: The intersection of two unit spheres is contained in a hyperplane.
- `K33_not_embeddable_in_R3`: K_{3,3} does not embed in R^3.
-/

import Mathlib

namespace Erdos1007

set_option linter.mathlibStandardSet false

open scoped Classical

set_option maxHeartbeats 0

open SimpleGraph

--noncomputable section

/-
Definitions of unit-distance embedding and graph dimension.
-/
def IsUnitDistanceEmbedding {V : Type*} (G : SimpleGraph V) (d : ℕ) (f : V → EuclideanSpace ℝ (Fin d)) : Prop :=
  Function.Injective f ∧ ∀ {u v}, G.Adj u v → dist (f u) (f v) = 1

def HasUnitDistanceEmbedding {V : Type*} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ f : V → EuclideanSpace ℝ (Fin d), IsUnitDistanceEmbedding G d f

noncomputable def GraphDimension {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf { d | HasUnitDistanceEmbedding G d }

/-
Every finite graph has a unit-distance embedding in some dimension.
-/
lemma exists_embedding {V : Type*} [Fintype V] (G : SimpleGraph V) : ∃ d, HasUnitDistanceEmbedding G d := by
  use Fintype.card V;
  -- Embed $V$ as a regular simplex in $\mathbb{R}^{|V|}$.
  have h_regular_simplex : ∃ f : V → EuclideanSpace ℝ (Fin (Fintype.card V)), Function.Injective f ∧ ∀ u v : V, u ≠ v → dist (f u) (f v) = 1 := by
    -- Let's choose any basis for the Euclidean space of dimension $|V|$.
    obtain ⟨basis, hbasis⟩ : ∃ basis : V → EuclideanSpace ℝ (Fin (Fintype.card V)), Function.Injective basis ∧ ∀ u v, u ≠ v → dist (basis u) (basis v) = Real.sqrt 2 := by
      -- We can construct such a basis using the standard basis vectors in Euclidean space.
      obtain ⟨basis, hbasis⟩ : ∃ basis : Fin (Fintype.card V) → EuclideanSpace ℝ (Fin (Fintype.card V)), Function.Injective basis ∧ ∀ i j, i ≠ j → dist (basis i) (basis j) = Real.sqrt 2 := by
        refine' ⟨ fun i => fun j => if i = j then 1 else 0, _, _ ⟩ <;> simp +decide [ Function.Injective, dist_eq_norm, EuclideanSpace.norm_eq ];
        · intro i j h; replace h := congr_fun h j; aesop;
        · intro i j hij; rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ i ) ] ; simp +decide [ Finset.sum_add_distrib, sub_sq, hij ] ;
          grind;
      have := Fintype.truncEquivFin V;
      obtain ⟨ e ⟩ := Trunc.exists_rep this; exact ⟨ fun u => basis ( e u ), fun u v huv => by simpa [ e.injective.eq_iff ] using hbasis.1 huv, fun u v huv => hbasis.2 _ _ ( by simpa [ e.injective.eq_iff ] using huv ) ⟩ ;
    refine' ⟨ fun u => ( 1 / Real.sqrt 2 ) • basis u, _, _ ⟩ <;> simp_all +decide [ Function.Injective, dist_eq_norm ];
    · exact fun u v h => hbasis.1 <| smul_right_injective _ ( by positivity ) h;
    · intro u v huv; rw [ ← smul_sub, norm_smul, Real.norm_of_nonneg ( by positivity ) ] ; simp +decide [ hbasis.2 u v huv ] ;
  exact ⟨ h_regular_simplex.choose, h_regular_simplex.choose_spec.1, fun { u v } huv => h_regular_simplex.choose_spec.2 u v huv.ne ⟩

/-
Let a,b in R^3 with dist(a,b)=1. Then the intersection of the unit spheres centered at a and b is an infinite set.
-/
lemma sphere_intersection_infinite {a b : EuclideanSpace ℝ (Fin 3)} (h : dist a b = 1) :
    (Metric.sphere a 1 ∩ Metric.sphere b 1).Infinite := by
      norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three ] at *;
      -- Let $c = \frac{a + b}{2}$ be the midpoint of $a$ and $b$.
      set c : EuclideanSpace ℝ (Fin 3) := fun i => (a i + b i) / 2;
      -- Consider the circle $S$ in the plane perpendicular to $ab$ through $c$ with radius $\sqrt{3}/2$.
      have h_circle : Set.Infinite {x : EuclideanSpace ℝ (Fin 3) | (x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2 + (x 2 - c 2) ^ 2 = 3 / 4 ∧ (x 0 - c 0) * (a 0 - b 0) + (x 1 - c 1) * (a 1 - b 1) + (x 2 - c 2) * (a 2 - b 2) = 0} := by
        -- Consider the circle $S$ in the plane perpendicular to $ab$ through $c$ with radius $\sqrt{3}/2$. We can parameterize this circle.
        have h_circle_param : ∃ (u v : EuclideanSpace ℝ (Fin 3)), u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧ (u 0 * (a 0 - b 0) + u 1 * (a 1 - b 1) + u 2 * (a 2 - b 2) = 0) ∧ (v 0 * (a 0 - b 0) + v 1 * (a 1 - b 1) + v 2 * (a 2 - b 2) = 0) ∧ (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1) ∧ (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) ∧ (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 = 0) := by
          -- Let $u$ be a vector perpendicular to $ab$ with length 1.
          obtain ⟨u, hu⟩ : ∃ u : EuclideanSpace ℝ (Fin 3), u ≠ 0 ∧ (u 0 * (a 0 - b 0) + u 1 * (a 1 - b 1) + u 2 * (a 2 - b 2) = 0) ∧ (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1) := by
            by_cases h_cases : a 0 = b 0;
            · exact ⟨ fun i => if i = 0 then 1 else if i = 1 then 0 else 0, by intros h; simpa using congr_fun h 0, by simp +decide [ h_cases ], by simp +decide ⟩;
            · refine' ⟨ fun i => if i = 0 then ( a 1 - b 1 ) / Real.sqrt ( ( a 1 - b 1 ) ^ 2 + ( a 0 - b 0 ) ^ 2 ) else if i = 1 then - ( a 0 - b 0 ) / Real.sqrt ( ( a 1 - b 1 ) ^ 2 + ( a 0 - b 0 ) ^ 2 ) else 0, _, _, _ ⟩ <;> simp +decide
              · intro H; have := congr_fun H 0; have := congr_fun H 1; simp_all +decide [ sub_eq_iff_eq_add ] ;
                exact absurd ( this.resolve_left ( Ne.symm h_cases ) ) ( by exact ne_of_gt ( Real.sqrt_pos.mpr ( by nlinarith only [ mul_self_pos.mpr ( sub_ne_zero.mpr h_cases ) ] ) ) );
              · ring;
              · rw [ div_pow, div_pow, Real.sq_sqrt <| by positivity, ← add_div, div_eq_iff ] <;> nlinarith [ mul_self_pos.2 ( sub_ne_zero.2 h_cases ) ];
          -- Let $v$ be a vector perpendicular to both $u$ and $ab$ with length 1.
          obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin 3), v ≠ 0 ∧ (v 0 * (a 0 - b 0) + v 1 * (a 1 - b 1) + v 2 * (a 2 - b 2) = 0) ∧ (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) ∧ (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 = 0) := by
            -- Let $v$ be a vector perpendicular to both $u$ and $ab$ with length 1. We can construct such a vector using the cross product.
            use ![u 1 * (a 2 - b 2) - u 2 * (a 1 - b 1), u 2 * (a 0 - b 0) - u 0 * (a 2 - b 2), u 0 * (a 1 - b 1) - u 1 * (a 0 - b 0)];
            simp_all +decide
            refine' ⟨ _, _, _, _ ⟩ <;> ring_nf;
            · intro H; have := congr_fun H 0; have := congr_fun H 1; have := congr_fun H 2; simp_all +decide
              exact hu.1 ( by ext i; fin_cases i <;> norm_num <;> nlinarith! only [ hu.2, this, ‹u 1 * a 2 + ( - ( u 1 * b 2 ) - u 2 * a 1 ) + u 2 * b 1 = 0›, ‹- ( a 2 * u 0 ) + b 2 * u 0 + ( u 2 * a 0 - u 2 * b 0 ) = 0›, ‹- ( u 1 * a 0 ) + u 1 * b 0 + ( a 1 * u 0 - b 1 * u 0 ) = 0›, h ] );
            · grind +ring;
          bound;
        obtain ⟨ u, v, hu, hv, huv, hu', hv', hu'', hv'', huv' ⟩ := h_circle_param;
        -- Consider the circle $S$ in the plane perpendicular to $ab$ through $c$ with radius $\sqrt{3}/2$. We can parameterize this circle using $u$ and $v$.
        have h_circle_param : ∀ θ : ℝ, (fun i => c i + (Real.sqrt 3 / 2) * (Real.cos θ * u i + Real.sin θ * v i)) ∈ {x : EuclideanSpace ℝ (Fin 3) | (x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2 + (x 2 - c 2) ^ 2 = 3 / 4 ∧ (x 0 - c 0) * (a 0 - b 0) + (x 1 - c 1) * (a 1 - b 1) + (x 2 - c 2) * (a 2 - b 2) = 0} := by
          intro θ; ring_nf; norm_num [ hu'', hv'', huv', hu', hv' ] ; ring_nf;
          constructor <;> ring_nf <;> norm_num [ hu'', hv'', huv', hu', hv' ] <;> ring_nf;
          · rw [ Real.sin_sq, Real.cos_sq ] ; ring_nf;
            grind;
          · linear_combination' hu' * Real.sqrt 3 * Real.cos θ / 2 + hv' * Real.sqrt 3 * Real.sin θ / 2;
        -- Since these points are parameterized by $\theta$, and $\theta$ can take infinitely many values, the set is infinite.
        have h_infinite : Set.Infinite (Set.image (fun θ : ℝ => (fun i => c i + (Real.sqrt 3 / 2) * (Real.cos θ * u i + Real.sin θ * v i))) (Set.Ioo 0 (Real.pi / 2))) := by
          refine' Set.Infinite.image _ ( Set.Ioo_infinite ( by positivity ) );
          intros θ₁ hθ₁ θ₂ hθ₂ h_eq; simp_all +decide [ funext_iff, Fin.forall_fin_succ ] ;
          -- Since $u$ and $v$ are linearly independent, the only solution to the system of equations is $\cos \theta_1 = \cos \theta_2$ and $\sin \theta_1 = \sin \theta_2$.
          have h_cos_sin : Real.cos θ₁ = Real.cos θ₂ ∧ Real.sin θ₁ = Real.sin θ₂ := by
            have h_cos_sin : (Real.cos θ₁ - Real.cos θ₂) ^ 2 + (Real.sin θ₁ - Real.sin θ₂) ^ 2 = 0 := by
              grind;
            exact ⟨ by nlinarith only [ h_cos_sin ], by nlinarith only [ h_cos_sin ] ⟩;
          exact Real.injOn_cos ⟨ by linarith, by linarith ⟩ ⟨ by linarith, by linarith ⟩ h_cos_sin.1;
        field_simp;
        exact h_infinite.mono fun x hx => by obtain ⟨ θ, hθ, rfl ⟩ := hx; specialize h_circle_param θ; exact ⟨ by linear_combination h_circle_param.1 * 4, h_circle_param.2 ⟩ ;
      refine' h_circle.mono _;
      norm_num [ Set.subset_def, Metric.mem_sphere ];
      norm_num [ EuclideanSpace.norm_eq, Fin.sum_univ_three ];
      grind

/-
The intersection of two planes with linearly independent normal vectors in R^3 is a line.
-/
lemma planes_inter_is_line {n1 n2 : EuclideanSpace ℝ (Fin 3)} (h : LinearIndependent ℝ ![n1, n2]) (c1 c2 : ℝ) :
    ∃ p v, v ≠ 0 ∧ {x | inner ℝ n1 x = c1} ∩ {x | inner ℝ n2 x = c2} = {p + t • v | t : ℝ} := by
      -- The intersection of two non-parallel planes in R^3 is a line. Since n1 and n2 are linearly independent, their cross product v = n1 x n2 is non-zero and orthogonal to both.
      obtain ⟨v, hv⟩ : ∃ (v : EuclideanSpace ℝ (Fin 3)), v ≠ 0 ∧ inner ℝ v n1 = 0 ∧ inner ℝ v n2 = 0 := by
        -- Since n1 and n2 are linearly independent, their cross product v = n1 x n2 is non-zero and orthogonal to both.
        obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin 3), v ≠ 0 ∧ inner ℝ v n1 = 0 ∧ inner ℝ v n2 = 0 := by
          have h_cross : ∃ v : EuclideanSpace ℝ (Fin 3), v ≠ 0 ∧ v ∈ (Submodule.span ℝ {n1, n2})ᗮ := by
            have h_cross : Module.finrank ℝ (Submodule.span ℝ {n1, n2})ᗮ = 1 := by
              have h_cross : Module.finrank ℝ (Submodule.span ℝ {n1, n2}) = 2 := by
                convert finrank_span_eq_card h;
                · aesop;
                · aesop;
                · aesop;
              have := Submodule.finrank_add_finrank_orthogonal ( Submodule.span ℝ { n1, n2 } );
              norm_num at * ; linarith;
            obtain ⟨ v, hv ⟩ := ( finrank_eq_one_iff'.mp h_cross );
            exact ⟨ v, by simpa using hv.1, v.2 ⟩
          simp_all +decide [ Submodule.mem_orthogonal' ];
          exact ⟨ h_cross.choose, h_cross.choose_spec.1, h_cross.choose_spec.2 n1 ( Submodule.subset_span ( Set.mem_insert _ _ ) ), h_cross.choose_spec.2 n2 ( Submodule.subset_span ( Set.mem_insert_of_mem _ ( Set.mem_singleton _ ) ) ) ⟩;
        use v;
      -- We can find a particular solution p to the system <n1, p> = c1, <n2, p> = c2.
      obtain ⟨p, hp⟩ : ∃ (p : EuclideanSpace ℝ (Fin 3)), inner ℝ n1 p = c1 ∧ inner ℝ n2 p = c2 := by
        -- We can solve the system of linear equations given by the inner products.
        have h_sol : ∃ p : ℝ × ℝ × ℝ, (n1 0 * p.1 + n1 1 * p.2.1 + n1 2 * p.2.2 = c1) ∧ (n2 0 * p.1 + n2 1 * p.2.1 + n2 2 * p.2.2 = c2) := by
          -- Since $n1$ and $n2$ are linearly independent, the determinant of the matrix formed by their coordinates is non-zero.
          have h_det : (n1 0 * n2 1 - n1 1 * n2 0) ≠ 0 ∨ (n1 0 * n2 2 - n1 2 * n2 0) ≠ 0 ∨ (n1 1 * n2 2 - n1 2 * n2 1) ≠ 0 := by
            contrapose! h; simp_all +decide [ Fintype.linearIndependent_iff ] ;
            by_cases h1 : n1 0 = 0 <;> by_cases h2 : n2 0 = 0 <;> simp_all +decide [ sub_eq_iff_eq_add ];
            · by_cases h3 : n1 1 = 0 <;> by_cases h4 : n2 1 = 0 <;> simp_all +decide [ mul_comm ];
              · by_cases h5 : n1 2 = 0 <;> by_cases h6 : n2 2 = 0 <;> simp_all +decide
                · exact ⟨ fun i => if i = 0 then 1 else 0, by ext i; fin_cases i <;> simp +decide [ * ], by simp +decide ⟩;
                · exact ⟨ fun i => if i = 0 then 1 else 0, by ext i; fin_cases i <;> simp +decide [ * ], by simp +decide ⟩;
                · exact ⟨ fun i => if i = 0 then 0 else 1, by ext i; fin_cases i <;> simp +decide [ * ], by simp +decide ⟩;
                · exact ⟨ fun i => if i = 0 then n2 2 else -n1 2, by ext i; fin_cases i <;> simp +decide [ *, mul_comm ], by simp +decide [ * ] ⟩;
              · exact ⟨ fun i => if i = 0 then 1 else 0, by ext i; fin_cases i <;> simp +decide [ * ], by simp +decide ⟩;
              · exact ⟨ fun i => if i = 0 then 0 else 1, by ext i; fin_cases i <;> aesop, by aesop ⟩;
              · exact ⟨ fun i => if i = 0 then -n2 1 else n1 1, by ext i; fin_cases i <;> simp +decide [ * ] ; linarith !, by simp +decide [ * ] ⟩;
            · exact ⟨ fun i => if i = 0 then 1 else 0, by ext i; fin_cases i <;> simp +decide [ * ], by simp +decide ⟩;
            · exact ⟨ fun i => if i = 0 then 0 else 1, by ext i; fin_cases i <;> simp +decide [ * ], by simp +decide ⟩;
            · exact ⟨ fun i => if i = 0 then -n2 0 else n1 0, by ext i; fin_cases i <;> simp +decide <;> linarith !, by simp +decide [ h1, h2 ] ⟩;
          rcases h_det with h | h | h;
          · use ( ( c1 * n2 1 - c2 * n1 1 ) / ( n1 0 * n2 1 - n1 1 * n2 0 ), ( c2 * n1 0 - c1 * n2 0 ) / ( n1 0 * n2 1 - n1 1 * n2 0 ), 0 );
            grind;
          · use ( ( c1 * n2 2 - c2 * n1 2 ) / ( n1 0 * n2 2 - n1 2 * n2 0 ), 0, ( c2 * n1 0 - c1 * n2 0 ) / ( n1 0 * n2 2 - n1 2 * n2 0 ) );
            grind;
          · use (0, (c1 * n2 2 - c2 * n1 2) / (n1 1 * n2 2 - n1 2 * n2 1), (c2 * n1 1 - c1 * n2 1) / (n1 1 * n2 2 - n1 2 * n2 1));
            grind;
        simp_all +decide [ Fin.sum_univ_three, inner ];
        obtain ⟨ a, b, c, h1, h2 ⟩ := h_sol; exact ⟨ fun i => if i = 0 then a else if i = 1 then b else c, by simpa [ mul_comm ] using h1, by simpa [ mul_comm ] using h2 ⟩ ;
      refine' ⟨ p, v, hv.1, Set.Subset.antisymm _ _ ⟩ <;> intro x hx <;> simp_all +decide
      · -- Since $n1$ and $n2$ are linearly independent, the vector $x - p$ is orthogonal to both $n1$ and $n2$, and hence lies in the span of $v$.
        have h_orthogonal : ∃ t : ℝ, x - p = t • v := by
          have h_orthogonal : ∀ w : EuclideanSpace ℝ (Fin 3), inner ℝ n1 w = 0 ∧ inner ℝ n2 w = 0 → ∃ t : ℝ, w = t • v := by
            -- Since $n1$ and $n2$ are linearly independent, the vector $w$ is orthogonal to both $n1$ and $n2$, and hence lies in the span of $v$.
            intros w hw
            have h_orthogonal : w ∈ (Submodule.span ℝ {n1, n2})ᗮ := by
              intro u hu; rw [ Submodule.mem_span_pair ] at hu; obtain ⟨ a, b, rfl ⟩ := hu; simp_all +decide [ inner_add_left, inner_smul_left ] ;
            -- Since $n1$ and $n2$ are linearly independent, the orthogonal complement of their span is one-dimensional.
            have h_orthogonal_complement : Module.finrank ℝ (↥((Submodule.span ℝ {n1, n2})ᗮ)) = 1 := by
              have h_orthogonal_complement : Module.finrank ℝ (↥((Submodule.span ℝ {n1, n2})ᗮ)) = 3 - Module.finrank ℝ (↥(Submodule.span ℝ {n1, n2})) := by
                have := Submodule.finrank_add_finrank_orthogonal ( Submodule.span ℝ { n1, n2 } );
                exact eq_tsub_of_add_eq <| by norm_num at this; linarith;
              rw [ h_orthogonal_complement, show Module.finrank ℝ ( Submodule.span ℝ { n1, n2 } ) = 2 from ?_ ];
              convert finrank_span_eq_card h;
              · aesop;
              · exact Eq.symm (Matrix.range_cons_cons_empty n1 n2 ![]);
              · aesop;
            have h_orthogonal_complement : Submodule.span ℝ {v} = (Submodule.span ℝ {n1, n2})ᗮ := by
              refine' Submodule.eq_of_le_of_finrank_eq _ _ <;> norm_num [ h_orthogonal_complement ];
              · simp_all +decide [ Submodule.mem_orthogonal' ];
                intro u hu
                rw [ Submodule.mem_span_pair ] at hu
                obtain ⟨ a, b, rfl ⟩ := hu
                simp_all +decide [ inner_add_right, inner_smul_right ]
              · rw [ finrank_span_singleton ] ; aesop;
            exact Submodule.mem_span_singleton.mp ( h_orthogonal_complement.symm ▸ h_orthogonal ) |> fun ⟨ t, ht ⟩ => ⟨ t, ht.symm ⟩;
          simp_all +decide [ inner_sub_right ];
        exact ⟨ h_orthogonal.choose, by rw [ ← h_orthogonal.choose_spec, add_sub_cancel ] ⟩;
      · rcases hx with ⟨ t, rfl ⟩ ; simp_all +decide [ inner_add_right, inner_smul_right ] ;
        exact ⟨ Or.inr ( by simpa [ real_inner_comm ] using hv.2.1 ), Or.inr ( by simpa [ real_inner_comm ] using hv.2.2 ) ⟩

/-
The intersection of three unit spheres centered at distinct points a, b, c in R^3 has at most two points.
-/
lemma three_spheres_intersection {a b c : EuclideanSpace ℝ (Fin 3)}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (Metric.sphere a 1 ∩ Metric.sphere b 1 ∩ Metric.sphere c 1).ncard ≤ 2 := by
      -- The intersection of three unit spheres centered at distinct points a, b, c in R^3 has at most two points.
      by_cases h_collinear : ∃ t : ℝ, b = a + t • (c - a);
      · by_contra h_contra;
        -- If a, b, c are collinear, then Pab and Pac are parallel and distinct (since b!=c), so their intersection is empty.
        obtain ⟨t, ht⟩ : ∃ t : ℝ, b = a + t • (c - a) := h_collinear
        have h_parallel : ∀ x, x ∈ Metric.sphere a 1 ∩ Metric.sphere b 1 → x ∈ Metric.sphere c 1 → False := by
          intro x hx hx'; simp_all +decide [ EuclideanSpace.norm_eq, Fin.sum_univ_three ] ;
          -- Expanding and simplifying the equations from hx and hx', we get:
          have h_expand : t * (t - 1) * ((c 0 - a 0) ^ 2 + (c 1 - a 1) ^ 2 + (c 2 - a 2) ^ 2) = 0 := by
            grind;
          simp_all +decide [ sub_eq_iff_eq_add ];
          exact hbc ( by rw [ h_expand.resolve_right ( by intro H; exact hab.2 <| by ext i; fin_cases i <;> nlinarith! only [ H ] ) ] ; ext i; fin_cases i <;> norm_num );
        exact h_contra <| by rw [ show Metric.sphere a 1 ∩ Metric.sphere b 1 ∩ Metric.sphere c 1 = ∅ by ext x; aesop ] ; norm_num;
      · -- Since $a$, $b$, and $c$ are not collinear, the planes $P_{ab}$ and $P_{ac}$ intersect in a line $L$.
        obtain ⟨p, v, hv_ne_zero, hL⟩ : ∃ p v : EuclideanSpace ℝ (Fin 3), v ≠ 0 ∧ {x | inner ℝ (b - a) x = inner ℝ (b - a) a + (1 / 2) * (‖b - a‖ ^ 2)} ∩ {x | inner ℝ (c - a) x = inner ℝ (c - a) a + (1 / 2) * (‖c - a‖ ^ 2)} = {p + t • v | t : ℝ} := by
          have h_planes_inter : LinearIndependent ℝ ![b - a, c - a] := by
            refine' linearIndependent_fin2.mpr _;
            simp_all +decide [ sub_eq_iff_eq_add ];
            exact ⟨ Ne.symm hac, fun x hx => h_collinear x <| by ext i; have := congr_fun hx i; norm_num at *; linarith ⟩;
          have := planes_inter_is_line h_planes_inter ( inner ℝ ( b - a ) a + 2⁻¹ * ‖b - a‖ ^ 2 ) ( inner ℝ ( c - a ) a + 2⁻¹ * ‖c - a‖ ^ 2 ) ; aesop;
        -- The intersection of the three spheres is thus contained in $L \cap S(a,1)$, which has at most 2 points.
        have h_inter_L_sphere : (Metric.sphere a 1 ∩ Metric.sphere b 1 ∩ Metric.sphere c 1) ⊆ {x | ∃ t : ℝ, p + t • v = x ∧ dist (p + t • v) a = 1} := by
          intro x hx;
          simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three ];
          replace hL := Set.ext_iff.mp hL x; simp_all +decide [ Real.sq_sqrt <| add_nonneg ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ( sq_nonneg _ ) ] ;
          simp_all +decide [ Fin.sum_univ_three, inner ];
          exact hL.mp ⟨ by linarith, by linarith ⟩ |> fun ⟨ t, ht ⟩ => ⟨ t, ht, by simpa [ ← ht ] using hx.1.1 ⟩;
        -- The equation $dist (p + t • v) a = 1$ is a quadratic equation in $t$, which has at most two solutions.
        have h_quad_eq : ∀ t : ℝ, dist (p + t • v) a = 1 → t = (-inner ℝ v (p - a) + Real.sqrt ((inner ℝ v (p - a))^2 - (‖v‖^2) * (‖p - a‖^2 - 1))) / ‖v‖^2 ∨ t = (-inner ℝ v (p - a) - Real.sqrt ((inner ℝ v (p - a))^2 - (‖v‖^2) * (‖p - a‖^2 - 1))) / ‖v‖^2 := by
          intro t ht
          have h_quad_eq : ‖v‖^2 * t^2 + 2 * inner ℝ v (p - a) * t + (‖p - a‖^2 - 1) = 0 := by
            norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three ] at *;
            norm_num [ Real.sq_sqrt ( add_nonneg ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ( sq_nonneg _ ) ), inner ] ; ring_nf;
            norm_num [ Fin.sum_univ_three ] ; linarith;
          field_simp;
          exact Classical.or_iff_not_imp_left.2 fun h => mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ Inner.inner ℝ v ( p - a ) ^ 2 - ‖v‖ ^ 2 * ( ‖p - a‖ ^ 2 - 1 ) by nlinarith [ sq_nonneg ( ‖v‖ ^ 2 * t + Inner.inner ℝ v ( p - a ) ) ] ) ] ;
        -- Therefore, the intersection of the three spheres has at most two points.
        have h_inter_L_sphere_card : (Metric.sphere a 1 ∩ Metric.sphere b 1 ∩ Metric.sphere c 1).ncard ≤ 2 := by
          have : Metric.sphere a 1 ∩ Metric.sphere b 1 ∩ Metric.sphere c 1 ⊆ {p + ((-inner ℝ v (p - a) + Real.sqrt ((inner ℝ v (p - a))^2 - (‖v‖^2) * (‖p - a‖^2 - 1))) / ‖v‖^2) • v, p + ((-inner ℝ v (p - a) - Real.sqrt ((inner ℝ v (p - a))^2 - (‖v‖^2) * (‖p - a‖^2 - 1))) / ‖v‖^2) • v} := by
            intro x hx; obtain ⟨ t, rfl, ht ⟩ := h_inter_L_sphere hx; specialize h_quad_eq t ht; aesop;
          exact le_trans ( Set.ncard_le_ncard this ) ( Set.ncard_insert_le _ _ ) |> le_trans <| by norm_num;
        exact h_inter_L_sphere_card

/-
The dimension of K_{3,3} is at most 4.
-/
lemma dim_K33_le_4 : GraphDimension (completeBipartiteGraph (Fin 3) (Fin 3)) ≤ 4 := by
  refine' Nat.sInf_le _;
  -- Define the function f that maps the vertices of K_{3,3} to points in R^4.
  use fun v => if v = (Sum.inl 0) then ![1 / Real.sqrt 2, 0, 0, 0] else if v = (Sum.inl 1) then ![0, 1 / Real.sqrt 2, 0, 0] else if v = (Sum.inl 2) then ![-1 / Real.sqrt 2, 0, 0, 0] else if v = (Sum.inr 0) then ![0, 0, 1 / Real.sqrt 2, 0] else if v = (Sum.inr 1) then ![0, 0, 0, 1 / Real.sqrt 2] else ![0, 0, -1 / Real.sqrt 2, 0];
  constructor <;> simp +decide [ Function.Injective, Fin.forall_fin_succ ];
  · ring_nf ;
    repeat erw [ ← List.ofFn_inj ] ; norm_num;
    constructor <;> linarith [ inv_pos.mpr ( Real.sqrt_pos.mpr zero_lt_two ) ];
  · norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_succ ] ; ring_nf ; norm_num;

/-
If a graph has a unit-distance embedding in dimension n, it has one in any dimension m >= n.
-/
lemma embedding_dim_mono {V : Type*} (G : SimpleGraph V) {n m : ℕ} (h : n ≤ m)
    (h_emb : HasUnitDistanceEmbedding G n) : HasUnitDistanceEmbedding G m := by
      obtain ⟨ f, hf ⟩ := h_emb;
      refine' ⟨ _, _, _ ⟩;
      exact fun v => ( f v ) |> fun x => fun i => if hi : i.val < n then x ⟨ i.val, hi ⟩ else 0;
      · intro v w h_eq;
        exact hf.1 ( by ext i; simpa using congr_fun h_eq ⟨ i, by linarith [ Fin.is_lt i ] ⟩ );
      · intro u v huv; have := hf.2 huv; simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ] ;
        rw [ ← this, Finset.sum_fin_eq_sum_range ];
        rw [ ← Finset.sum_range_add_sum_Ico _ h ];
        simp +decide [ Finset.sum_range, Finset.sum_Ico_eq_sum_range ];
        exact Finset.sum_congr rfl fun x hx => if_pos ( by linarith [ Fin.is_lt x ] )

/-
The set of parameters t for which a line p + t*v intersects a sphere is finite.
-/
lemma line_inter_sphere_finite {p v : EuclideanSpace ℝ (Fin 3)} (hv : v ≠ 0)
    {c : EuclideanSpace ℝ (Fin 3)} {r : ℝ} :
    ({t : ℝ | dist (p + t • v) c = r}).Finite := by
      -- The set of t such that dist(p + t • v, c) = r is finite because a line intersects a sphere in at most two points.
      have h_finite : ∀ t1 t2 t3 : ℝ, t1 ≠ t2 → t2 ≠ t3 → t1 ≠ t3 → dist (p + t1 • v) c = r → dist (p + t2 • v) c = r → dist (p + t3 • v) c = r → False := by
        intros t1 t2 t3 h1 h2 h3 ht1 ht2 ht3
        have h_quad : (t2 - t1) * (t3 - t1) * (t3 - t2) ≠ 0 := by
          exact mul_ne_zero ( mul_ne_zero ( sub_ne_zero_of_ne <| by tauto ) ( sub_ne_zero_of_ne <| by tauto ) ) ( sub_ne_zero_of_ne <| by tauto );
        norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three ] at *;
        have h_quad_eq : (p 0 + t1 * v 0 - c 0) ^ 2 + (p 1 + t1 * v 1 - c 1) ^ 2 + (p 2 + t1 * v 2 - c 2) ^ 2 = (p 0 + t2 * v 0 - c 0) ^ 2 + (p 1 + t2 * v 1 - c 1) ^ 2 + (p 2 + t2 * v 2 - c 2) ^ 2 ∧ (p 0 + t2 * v 0 - c 0) ^ 2 + (p 1 + t2 * v 1 - c 1) ^ 2 + (p 2 + t2 * v 2 - c 2) ^ 2 = (p 0 + t3 * v 0 - c 0) ^ 2 + (p 1 + t3 * v 1 - c 1) ^ 2 + (p 2 + t3 * v 2 - c 2) ^ 2 := by
          exact ⟨ by rw [ ← Real.sqrt_inj ( by positivity ) ( by positivity ), ht1, ht2 ], by rw [ ← Real.sqrt_inj ( by positivity ) ( by positivity ), ht2, ht3 ] ⟩;
        -- By expanding and simplifying, we can derive that the coefficients of $t^2$, $t$, and the constant term must all be zero.
        have h_coeff : (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) * (t2 - t1) * (t3 - t1) * (t3 - t2) = 0 := by
          grind;
        simp_all +decide [ sub_eq_iff_eq_add ];
        exact hv ( by ext i; fin_cases i <;> norm_num <;> nlinarith! only [ h_coeff ] );
      contrapose! h_finite;
      obtain ⟨ s, hs ⟩ := Set.Infinite.nonempty h_finite;
      obtain ⟨ t1, ht1 ⟩ := Set.Infinite.nonempty ( Set.Infinite.diff h_finite ( Set.finite_singleton s ) ) ; obtain ⟨ t2, ht2 ⟩ := Set.Infinite.nonempty ( Set.Infinite.diff ( Set.Infinite.diff h_finite ( Set.finite_singleton s ) ) ( Set.finite_singleton t1 ) ) ; use s, t1, t2; aesop;

/-
The intersection of three unit spheres centered at distinct points a, b, c in R^3 is finite.
-/
lemma three_spheres_intersection_finite {a b c : EuclideanSpace ℝ (Fin 3)}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (Metric.sphere a 1 ∩ Metric.sphere b 1 ∩ Metric.sphere c 1).Finite := by
      -- If a, b, c are collinear, the intersection of the radical planes of (a,b) and (b,c) is empty because they are distinct parallel planes (since b != c). Thus the intersection of spheres is empty, hence finite.
      by_cases h_collinear : ∃ (t : ℝ), b = a + t • (c - a);
      · -- If a, b, c are collinear, then the intersection of the radical planes of (a,b) and (b,c) is empty because they are distinct parallel planes (since b != c). Thus the intersection of spheres is empty, hence finite.
        obtain ⟨t, ht⟩ := h_collinear
        have h_radical_planes : Metric.sphere a 1 ∩ Metric.sphere b 1 ∩ Metric.sphere c 1 = ∅ := by
          norm_num [ Set.ext_iff, ht ];
          intros x hx1 hx2 hx3;
          norm_num [ EuclideanSpace.norm_eq, Fin.sum_univ_three ] at *;
          -- Since $a$, $b$, and $c$ are collinear, we have $t = 0$ or $t = 1$.
          by_cases ht_zero : t = 0 ∨ t = 1;
          · aesop;
          · exact ht_zero <| Classical.or_iff_not_imp_left.2 fun h => mul_left_cancel₀ h <| by nlinarith [ sq_nonneg ( t - 1 ), sq_nonneg ( t + 1 ), show ( c 0 - a 0 ) ^ 2 + ( c 1 - a 1 ) ^ 2 + ( c 2 - a 2 ) ^ 2 > 0 from not_le.mp fun h' => hac <| by ext i; fin_cases i <;> nlinarith! only [ h' ] ] ;
        exact h_radical_planes ▸ Set.finite_empty;
      · -- If a, b, c are not collinear, the intersection of the radical planes is a line L. The intersection of the three spheres is contained in L ∩ S(a,1), which is finite.
        obtain ⟨p, v, hv_ne_zero, hv_line⟩ : ∃ (p : EuclideanSpace ℝ (Fin 3)) (v : EuclideanSpace ℝ (Fin 3)), v ≠ 0 ∧ {x | inner ℝ (b - a) x = (‖b‖^2 - ‖a‖^2) / 2} ∩ {x | inner ℝ (c - a) x = (‖c‖^2 - ‖a‖^2) / 2} = {p + t • v | t : ℝ} := by
          have hplanes_inter_is_line : LinearIndependent ℝ ![b - a, c - a] := by
            norm_num [ linearIndependent_fin2 ];
            exact ⟨ sub_ne_zero_of_ne <| by tauto, fun t ht => h_collinear ⟨ t, by ext i; have := congr_fun ht i; norm_num at *; linarith ⟩ ⟩;
          have := planes_inter_is_line hplanes_inter_is_line ( ( ‖b‖ ^ 2 - ‖a‖ ^ 2 ) / 2 ) ( ( ‖c‖ ^ 2 - ‖a‖ ^ 2 ) / 2 ) ; aesop;
        -- The intersection of the three spheres is contained in L ∩ S(a,1), which is finite.
        have h_inter_subset : Metric.sphere a 1 ∩ Metric.sphere b 1 ∩ Metric.sphere c 1 ⊆ {p + t • v | t : ℝ} ∩ Metric.sphere a 1 := by
          intro x hx;
          simp_all +decide [ EuclideanSpace.norm_eq, Fin.sum_univ_three ];
          replace hv_line := Set.ext_iff.mp hv_line x ; simp_all +decide [ Real.sq_sqrt ( add_nonneg ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ( sq_nonneg _ ) ) ];
          exact hv_line.mp ⟨ by norm_num [ Fin.sum_univ_three, inner ] ; linarith, by norm_num [ Fin.sum_univ_three, inner ] ; linarith ⟩;
        have h_inter_finite : ({t : ℝ | dist (p + t • v) a = 1}).Finite := by
          exact line_inter_sphere_finite hv_ne_zero;
        exact Set.Finite.subset ( h_inter_finite.image fun t => p + t • v ) fun x hx => by rcases h_inter_subset hx with ⟨ ⟨ t, rfl ⟩, hx ⟩ ; aesop;

/-
K_{3,3} does not have a unit-distance embedding in R^3.
-/
lemma K33_no_embedding_R3 : ¬ HasUnitDistanceEmbedding (completeBipartiteGraph (Fin 3) (Fin 3)) 3 := by
  rintro ⟨ f, hf_inj, hf_dist ⟩;
  -- Each b_j must lie on the intersection of the three unit spheres centered at a_0, a_1, a_2.
  have h_b_sphere : ∀ j : Fin 3, f (Sum.inr j) ∈ Metric.sphere (f (Sum.inl 0)) 1 ∧ f (Sum.inr j) ∈ Metric.sphere (f (Sum.inl 1)) 1 ∧ f (Sum.inr j) ∈ Metric.sphere (f (Sum.inl 2)) 1 := by
    exact fun j => ⟨ hf_dist ( by simp +decide [ completeBipartiteGraph ] ), hf_dist ( by simp +decide [ completeBipartiteGraph ] ), hf_dist ( by simp +decide [ completeBipartiteGraph ] ) ⟩;
  have h_three_spheres : Set.ncard (Metric.sphere (f (Sum.inl 0)) 1 ∩ Metric.sphere (f (Sum.inl 1)) 1 ∩ Metric.sphere (f (Sum.inl 2)) 1) ≤ 2 := by
    apply_rules [ three_spheres_intersection ];
    · exact hf_inj.ne ( by decide );
    · exact hf_inj.ne ( by decide );
    · exact hf_inj.ne ( by decide );
  have h_three_points : Set.ncard (Set.image f {Sum.inr 0, Sum.inr 1, Sum.inr 2}) ≤ 2 := by
    refine le_trans ?_ h_three_spheres;
    apply_rules [ Set.ncard_le_ncard ] ; aesop_cat;
    exact Set.Finite.subset ( three_spheres_intersection_finite ( show f ( Sum.inl 0 ) ≠ f ( Sum.inl 1 ) from hf_inj.ne <| by decide ) ( show f ( Sum.inl 1 ) ≠ f ( Sum.inl 2 ) from hf_inj.ne <| by decide ) ( show f ( Sum.inl 0 ) ≠ f ( Sum.inl 2 ) from hf_inj.ne <| by decide ) ) fun x hx => by aesop;
  simp_all +decide [ Set.ncard_image_of_injective ]

/-
The dimension of K_{3,3} is 4.
-/
lemma dim_K33_eq_4 : GraphDimension (completeBipartiteGraph (Fin 3) (Fin 3)) = 4 := by
  apply le_antisymm
  · exact dim_K33_le_4
  · by_contra! h
    have h_emb : HasUnitDistanceEmbedding (completeBipartiteGraph (Fin 3) (Fin 3)) 3 := by
      -- If dim < 4, then dim <= 3.
      have h_le_3 : GraphDimension (completeBipartiteGraph (Fin 3) (Fin 3)) ≤ 3 := Nat.le_of_lt_succ h
      -- There exists some d such that HasUnitDistanceEmbedding G d.
      -- GraphDimension G is the infimum.
      -- If inf <= 3, does it mean there exists d <= 3?
      -- Yes, because the set of dimensions is upward closed (embedding_dim_mono).
      -- So if inf <= 3, then 3 is in the set.
      obtain ⟨d, hd⟩ := exists_embedding (completeBipartiteGraph (Fin 3) (Fin 3))
      have h_nonempty : {d | HasUnitDistanceEmbedding (completeBipartiteGraph (Fin 3) (Fin 3)) d}.Nonempty := ⟨d, hd⟩
      have h_inf_mem : GraphDimension (completeBipartiteGraph (Fin 3) (Fin 3)) ∈ {d | HasUnitDistanceEmbedding (completeBipartiteGraph (Fin 3) (Fin 3)) d} := Nat.sInf_mem h_nonempty
      apply embedding_dim_mono (completeBipartiteGraph (Fin 3) (Fin 3)) h_le_3 h_inf_mem
    exact K33_no_embedding_R3 h_emb


/-
The complete bipartite graph K_{3,3} has 9 edges.
-/
theorem K33_edges : (completeBipartiteGraph (Fin 3) (Fin 3)).edgeFinset.card = 9 := by
  norm_num [ completeBipartiteGraph ];
  simp +decide [ Finset.card ];
  erw [ Multiset.filter_coe ] ; simp +decide [ SimpleGraph.edgeSet ] ;
  simp +decide [ List.finRange, List.map, List.sym2 ]

/-
Defining deleteVertex and addEdge for SimpleGraphs.
-/
def deleteVertex {V : Type*} (G : SimpleGraph V) (v : V) : SimpleGraph {u // u ≠ v} :=
  G.induce {u | u ≠ v}

def addEdge {V : Type*} (G : SimpleGraph V) (u v : V) : SimpleGraph V :=
  G ⊔ SimpleGraph.fromEdgeSet {s(u,v)}

/-
If a graph G has a vertex of degree 1, and G without that vertex embeds in R^3, then G embeds in R^3.
-/
lemma embed_extend_deg_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V)
    (h : G.degree v = 1) (h_emb : HasUnitDistanceEmbedding (deleteVertex G v) 3) :
    HasUnitDistanceEmbedding G 3 := by
      by_contra h_contra;
      -- Let f' be the embedding of G - v. Let u be the unique neighbor of v.
      obtain ⟨f', hf'⟩ : ∃ f' : { u : V // u ≠ v } → EuclideanSpace ℝ (Fin 3), IsUnitDistanceEmbedding (deleteVertex G v) 3 f' := by
        exact h_emb;
      -- Let u be the unique neighbor of v.
      obtain ⟨u, hu⟩ : ∃ u : V, u ≠ v ∧ G.Adj v u := by
        obtain ⟨ u, hu ⟩ := G.degree_pos_iff_exists_adj v |>.1 ( by linarith ) ; use u; aesop;
      -- The set of points at distance 1 from f'(u) is a sphere in R^3.
      -- This sphere is infinite.
      have h_sphere_infinite : (Metric.sphere (f' ⟨u, hu.1⟩) 1).Infinite := by
        intro H;
        have h_sphere_infinite : Set.Infinite (Metric.sphere (f' ⟨u, hu.1⟩) 1) := by
          have h_sphere_infinite : Set.Infinite (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
            intro h;
            have := h.image ( fun x => x 0 );
            refine' this.not_infinite _;
            refine' Set.Infinite.mono _ ( Set.Ioo_infinite ( show -1 < 1 by norm_num ) );
            intro x hx;
            refine' ⟨ fun i => if i = 0 then x else if i = 1 then Real.sqrt ( 1 - x ^ 2 ) else 0, _, _ ⟩ <;> simp +decide [ EuclideanSpace.norm_eq, Fin.sum_univ_three ];
            rw [ Real.sq_sqrt ] <;> nlinarith [ hx.1, hx.2 ]
          convert h_sphere_infinite.image _ using 1;
          rotate_left;
          use fun x => f' ⟨ u, hu.1 ⟩ + x;
          · exact fun x hx y hy hxy => by simpa using hxy;
          · simp +decide
        exact h_sphere_infinite H;
      -- The set of images of other vertices is finite.
      have h_finite : Set.Finite (Set.image f' Set.univ) := by
        exact Set.toFinite _;
      -- Thus there exists a point p on the sphere not in the image of other vertices.
      obtain ⟨p, hp_sphere, hp_not_in_image⟩ : ∃ p : EuclideanSpace ℝ (Fin 3), p ∈ Metric.sphere (f' ⟨u, hu.1⟩) 1 ∧ p ∉ Set.image f' Set.univ := by
        exact Set.Infinite.nonempty ( h_sphere_infinite.diff h_finite );
      refine' h_contra ⟨ fun w => if hw : w = v then p else f' ⟨ w, hw ⟩, _, _ ⟩ <;> simp_all +decide [ IsUnitDistanceEmbedding ];
      · intro w w' h_eq; by_cases hw : w = v <;> by_cases hw' : w' = v <;> simp_all +decide [ Function.Injective.eq_iff hf'.1 ] ;
        (expose_names; exact False.elim (hp_not_in_image w' hw'_1 rfl));
      · intro a b hab; split_ifs <;> simp_all +decide [ dist_eq_norm ] ;
        · have := Finset.card_eq_one.mp h;
          obtain ⟨ w, hw ⟩ := this; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
        · -- Since $G$ is a simple graph, if $a$ is adjacent to $v$, then $a$ must be $u$.
          have ha_eq_u : a = u := by
            have := Finset.card_eq_one.mp h;
            obtain ⟨ w, hw ⟩ := this; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
            exact hw.2 a ( by simpa [ SimpleGraph.adj_comm ] using hab );
          simp_all +decide [ norm_sub_rev ];
        · exact hf'.2 a ‹_› b ‹_› ( by exact hab )

/-
If a graph G has a vertex v of degree 2 with neighbors u and w, and u and w are adjacent, and G - v embeds in R^3, then G embeds in R^3.
-/
lemma embed_extend_deg_2_adj {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V)
    (u w : V) (hu : G.Adj v u) (hw : G.Adj v w) (huw : u ≠ w) (hdeg : G.degree v = 2)
    (hu_adj_w : G.Adj u w)
    (h_emb : HasUnitDistanceEmbedding (deleteVertex G v) 3) :
    HasUnitDistanceEmbedding G 3 := by
      obtain ⟨ f', hf' ⟩ := h_emb;
      -- Since u and w are adjacent in G, they are adjacent in G - v. Therefore, we can extend the embedding f' of G - v to an embedding of G by mapping v to a point in the intersection of the unit spheres around f(u) and f(w) that is not in the image of f'.
      obtain ⟨p, hp⟩ : ∃ p : EuclideanSpace ℝ (Fin 3), dist (f' ⟨u, by aesop⟩) p = 1 ∧ dist (f' ⟨w, by aesop⟩) p = 1 ∧ p ∉ Set.range f' := by
        have h_inter_infinite : Set.Infinite {p : EuclideanSpace ℝ (Fin 3) | dist (f' ⟨u, by aesop⟩) p = 1 ∧ dist (f' ⟨w, by aesop⟩) p = 1} := by
          have h_dist : dist (f' ⟨u, by aesop⟩) (f' ⟨w, by aesop⟩) = 1 := by
            exact hf'.2 ( show ( deleteVertex G v ).Adj ⟨ u, by aesop ⟩ ⟨ w, by aesop ⟩ from by aesop )
          convert sphere_intersection_infinite h_dist using 1;
          ext; simp +decide
          simp +decide only [dist_eq_norm'];
        exact Exists.imp ( by aesop ) ( h_inter_infinite.exists_notMem_finset ( Set.toFinset ( Set.range f' ) ) );
      refine' ⟨ fun x => if hx : x = v then p else f' ⟨ x, hx ⟩, _, _ ⟩ <;> simp_all +decide
      · intro x y hxy; by_cases hx : x = v <;> by_cases hy : y = v <;> simp_all +decide [ hf'.1.eq_iff ] ;
        grind;
      · intro x y hxy; cases eq_or_ne x v <;> cases eq_or_ne y v <;> simp_all +decide
        · have h_neighbors : Finset.image (fun x => x) (G.neighborFinset v) = {u, w} := by
            rw [ Finset.eq_of_subset_of_card_le ( show { u, w } ⊆ Finset.image ( fun x => x ) ( G.neighborFinset v ) from by aesop_cat ) ] ; aesop;
          simp_all +decide [ Finset.ext_iff ];
          rcases hxy with ( rfl | rfl ) <;> [ exact hp.1 ▸ dist_comm _ _; exact hp.2.1 ▸ dist_comm _ _ ];
        · have := Finset.card_eq_two.mp hdeg;
          simp_all +decide [ Finset.ext_iff, SimpleGraph.neighborFinset ];
          obtain ⟨ x, y, hxy, h ⟩ := this; have := h u; have := h w; simp_all +decide [ SimpleGraph.adj_comm ] ;
          grind;
        · have := hf' |>.2 ( show ( deleteVertex G v ).Adj ⟨ x, by assumption ⟩ ⟨ y, by assumption ⟩ from ?_ ) ; aesop;
          exact hxy

/-
If a graph G has a vertex v of degree 2 with neighbors u and w, and u and w are not adjacent, and the graph obtained by removing v and adding edge (u,w) embeds in R^3, then G embeds in R^3.
-/
lemma embed_extend_deg_2_not_adj {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V)
    (u w : V) (hu : G.Adj v u) (hw : G.Adj v w) (huw : u ≠ w) (hdeg : G.degree v = 2)
    (hu_not_adj_w : ¬ G.Adj u w)
    (h_emb : HasUnitDistanceEmbedding (addEdge (deleteVertex G v) ⟨u, (G.ne_of_adj hu).symm⟩ ⟨w, (G.ne_of_adj hw).symm⟩) 3) :
    HasUnitDistanceEmbedding G 3 := by
      -- Since the intersection of the two spheres is infinite, we can pick any point in that intersection that's not in the image of f'.
      obtain ⟨p, hp⟩ : ∃ p : EuclideanSpace ℝ (Fin 3), p ∈ Metric.sphere (h_emb.choose ⟨u, by
        exact hu.symm.ne⟩) 1 ∩ Metric.sphere (h_emb.choose ⟨w, by
        exact hw.symm.ne⟩) 1 ∧ p ∉ Set.range (h_emb.choose) := by
        have h_infinite : Set.Infinite (Metric.sphere (h_emb.choose ⟨u, by
          exact hu.ne.symm⟩) 1 ∩ Metric.sphere (h_emb.choose ⟨w, by
          exact Adj.ne' hw⟩) 1) := by
          have := h_emb.choose_spec;
          apply sphere_intersection_infinite;
          exact this.2 ( by simp +decide [ addEdge, huw ] );
        exact h_infinite.exists_notMem_finset ( Set.toFinset ( Set.range h_emb.choose ) ) |> fun ⟨ p, hp₁, hp₂ ⟩ => ⟨ p, hp₁, by simpa using hp₂ ⟩;
      refine' ⟨ fun x => if hx : x = v then p else h_emb.choose ⟨ x, _ ⟩, _, _ ⟩;
      exact hx;
      · intro x y hxy;
        by_cases hx : x = v <;> by_cases hy : y = v <;> simp_all +decide;
        · exact False.elim ( hp.2 _ hy rfl );
        · have := h_emb.choose_spec.1 hxy; aesop;
      · intro x y hxy; by_cases hx : x = v <;> by_cases hy : y = v <;> simp_all +decide
        · have := Finset.eq_of_subset_of_card_le ( show { u, w } ⊆ G.neighborFinset v from ?_ ) ; simp_all +decide
          · replace this := Finset.ext_iff.mp this y; aesop;
          · simp_all +decide [ Finset.insert_subset_iff ];
        · -- Since $x$ is adjacent to $v$ and $v$ is adjacent to $u$ and $w$, $x$ must be either $u$ or $w$.
          have hx_u_or_w : x = u ∨ x = w := by
            have := Finset.card_eq_two.mp hdeg;
            simp_all +decide [ Finset.ext_iff, SimpleGraph.neighborFinset ];
            obtain ⟨ x, y, hxy, h ⟩ := this; have := h u; have := h w; simp_all +decide [ SimpleGraph.adj_comm ] ;
            grind;
          cases hx_u_or_w <;> simp_all +decide [ dist_eq_norm' ];
        · convert h_emb.choose_spec.2 _;
          unfold addEdge; aesop;

/-
Any graph with at most 4 vertices has dimension at most 3.
-/
lemma dim_le_3_of_card_le_4 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (h : Fintype.card V ≤ 4) : GraphDimension G ≤ 3 := by
      -- Any graph with at most 4 vertices is a subgraph of $K_4$, which can be embedded in $\mathbb{R}^3$.
      have h_subgraph : ∃ (f : V → EuclideanSpace ℝ (Fin 3)), IsUnitDistanceEmbedding G 3 f := by
        have h_subgraph : ∃ (f : V → EuclideanSpace ℝ (Fin 3)), ∀ v w : V, v ≠ w → dist (f v) (f w) = 1 := by
          -- Let's choose any four points in $\mathbb{R}^3$ that are pairwise at a distance of 1.
          obtain ⟨f, hf⟩ : ∃ (f : Fin (Fintype.card V) → EuclideanSpace ℝ (Fin 3)), ∀ i j : Fin (Fintype.card V), i ≠ j → dist (f i) (f j) = 1 := by
            interval_cases _ : Fintype.card V <;> simp_all +decide;
            · refine' ⟨ fun i => if i = 0 then 0 else EuclideanSpace.single 0 1, _, _ ⟩ <;> norm_num;
            · -- For the case when $n = 3$, we can construct the embedding explicitly.
              use ![ ![0, 0, 0], ![1, 0, 0], ![1/2, Real.sqrt 3 / 2, 0] ];
              norm_num [ Fin.forall_fin_succ, dist_eq_norm, EuclideanSpace.norm_eq ];
              norm_num [ Fin.sum_univ_succ ] ; ring_nf ; norm_num;
            · -- For the case when $|V| = 4$, we can construct the embedding explicitly.
              use ![![0, 0, 0], ![1, 0, 0], ![1/2, Real.sqrt 3 / 2, 0], ![1/2, Real.sqrt 3 / 6, Real.sqrt 6 / 3]];
              norm_num [ Fin.forall_fin_succ, dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_succ ];
              repeat erw [ Matrix.cons_val_succ' ] ; norm_num ; ring_nf ; norm_num;
          exact ⟨ fun v => f ( Fintype.equivFin V v ), fun v w hvw => hf _ _ ( by simpa [ Fintype.equivFin ] using hvw ) ⟩;
        obtain ⟨ f, hf ⟩ := h_subgraph;
        refine' ⟨ f, _, _ ⟩;
        · intro v w h; specialize hf v w; aesop;
        · exact fun { u v } huv => hf u v huv.ne;
      exact csInf_le ⟨ 0, fun d hd => Nat.zero_le _ ⟩ ⟨ h_subgraph.choose, h_subgraph.choose_spec ⟩

/-
Given three points x, y, z in R^3 forming a regular triangle of side 1, there exists a point p at distance 1 from all of them, distinct from a fourth point u.
-/
lemma regular_triangle_sphere_intersection_avoid {x y z u : EuclideanSpace ℝ (Fin 3)}
    (hxy : Dist.dist x y = 1) (hyz : Dist.dist y z = 1) (hzx : Dist.dist z x = 1) :
    ∃ p, Dist.dist p x = 1 ∧ Dist.dist p y = 1 ∧ Dist.dist p z = 1 ∧ p ≠ u := by
      by_contra! h;
      -- Since there are two such points, and u is just one point, at least one of them is distinct from u.
      obtain ⟨p₁, hp₁⟩ : ∃ p₁ : EuclideanSpace ℝ (Fin 3), dist p₁ x = 1 ∧ dist p₁ y = 1 ∧ dist p₁ z = 1 := by
        norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three ] at *;
        -- Let $p₁$ be the point $(x + y + z)/3 + t \cdot (x \times y + y \times z + z \times x)$ for some $t$.
        obtain ⟨t, ht⟩ : ∃ t : ℝ, ((x 0 + y 0 + z 0) / 3 + t * ((y 1 - x 1) * (z 2 - x 2) - (y 2 - x 2) * (z 1 - x 1)) - x 0) ^ 2 + ((x 1 + y 1 + z 1) / 3 + t * ((y 2 - x 2) * (z 0 - x 0) - (y 0 - x 0) * (z 2 - x 2)) - x 1) ^ 2 + ((x 2 + y 2 + z 2) / 3 + t * ((y 0 - x 0) * (z 1 - x 1) - (y 1 - x 1) * (z 0 - x 0)) - x 2) ^ 2 = 1 := by
          -- We can solve this quadratic equation for $t$.
          have h_quad : ∃ t : ℝ, t^2 * (( (y 1 - x 1) * (z 2 - x 2) - (y 2 - x 2) * (z 1 - x 1) )^2 + ( (y 2 - x 2) * (z 0 - x 0) - (y 0 - x 0) * (z 2 - x 2) )^2 + ( (y 0 - x 0) * (z 1 - x 1) - (y 1 - x 1) * (z 0 - x 0) )^2 ) = 1 - ((x 0 + y 0 + z 0) / 3 - x 0)^2 - ((x 1 + y 1 + z 1) / 3 - x 1)^2 - ((x 2 + y 2 + z 2) / 3 - x 2)^2 := by
            by_cases h₂ : ((y 1 - x 1) * (z 2 - x 2) - (y 2 - x 2) * (z 1 - x 1)) ^ 2 + ((y 2 - x 2) * (z 0 - x 0) - (y 0 - x 0) * (z 2 - x 2)) ^ 2 + ((y 0 - x 0) * (z 1 - x 1) - (y 1 - x 1) * (z 0 - x 0)) ^ 2 = 0;
            · grind;
            · exact ⟨ Real.sqrt ( ( 1 - ( ( x 0 + y 0 + z 0 ) / 3 - x 0 ) ^ 2 - ( ( x 1 + y 1 + z 1 ) / 3 - x 1 ) ^ 2 - ( ( x 2 + y 2 + z 2 ) / 3 - x 2 ) ^ 2 ) / ( ( ( y 1 - x 1 ) * ( z 2 - x 2 ) - ( y 2 - x 2 ) * ( z 1 - x 1 ) ) ^ 2 + ( ( y 2 - x 2 ) * ( z 0 - x 0 ) - ( y 0 - x 0 ) * ( z 2 - x 2 ) ) ^ 2 + ( ( y 0 - x 0 ) * ( z 1 - x 1 ) - ( y 1 - x 1 ) * ( z 0 - x 0 ) ) ^ 2 ) ), by rw [ Real.sq_sqrt ( div_nonneg ( by linarith [ sq_nonneg ( x 0 - y 0 ), sq_nonneg ( x 1 - y 1 ), sq_nonneg ( x 2 - y 2 ), sq_nonneg ( y 0 - z 0 ), sq_nonneg ( y 1 - z 1 ), sq_nonneg ( y 2 - z 2 ), sq_nonneg ( z 0 - x 0 ), sq_nonneg ( z 1 - x 1 ), sq_nonneg ( z 2 - x 2 ) ] ) ( by positivity ) ) ] ; rw [ div_mul_cancel₀ _ h₂ ] ⟩;
          exact h_quad.imp fun t ht => by linarith;
        use fun i => if i = 0 then ( x 0 + y 0 + z 0 ) / 3 + t * ( ( y 1 - x 1 ) * ( z 2 - x 2 ) - ( y 2 - x 2 ) * ( z 1 - x 1 ) ) else if i = 1 then ( x 1 + y 1 + z 1 ) / 3 + t * ( ( y 2 - x 2 ) * ( z 0 - x 0 ) - ( y 0 - x 0 ) * ( z 2 - x 2 ) ) else ( x 2 + y 2 + z 2 ) / 3 + t * ( ( y 0 - x 0 ) * ( z 1 - x 1 ) - ( y 1 - x 1 ) * ( z 0 - x 0 ) );
        grind;
      obtain ⟨p₂, hp₂⟩ : ∃ p₂ : EuclideanSpace ℝ (Fin 3), dist p₂ x = 1 ∧ dist p₂ y = 1 ∧ dist p₂ z = 1 ∧ p₂ ≠ p₁ := by
        -- Let $p₂$ be the reflection of $p₁$ over the plane containing $x$, $y$, and $z$.
        use 2 • (1 / 3 : ℝ) • (x + y + z) - p₁;
        norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three ] at *;
        refine' ⟨ _, _, _, _ ⟩ <;> ring_nf at * <;> norm_num at *;
        · linarith;
        · linarith;
        · linarith;
        · intro H; have := congr_fun H 0; have := congr_fun H 1; have := congr_fun H 2; norm_num at * ; nlinarith;
      exact hp₂.2.2.2 ( h p₂ hp₂.1 hp₂.2.1 hp₂.2.2.1 ▸ h p₁ hp₁.1 hp₁.2.1 hp₁.2.2 ▸ rfl )

/-
If a graph has 5 vertices, fewer than 9 edges, and minimum degree at least 3, then it has a vertex of degree 3.
-/
lemma exists_deg_3_of_card_5_edges_lt_9 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hV : Fintype.card V = 5) (hE : G.edgeFinset.card < 9) (hmin : ∀ v, 3 ≤ G.degree v) :
    ∃ v, G.degree v = 3 := by
      by_contra h_contra;
      -- If all vertices have degree at least 4, then the sum of degrees is at least 4*5 = 20.
      have h_sum_deg : ∑ v : V, G.degree v ≥ 4 * 5 := by
        exact le_trans ( by norm_num [ hV ] ) ( Finset.sum_le_sum fun v _ => Nat.succ_le_of_lt ( lt_of_le_of_ne ( hmin v ) ( Ne.symm fun h => h_contra ⟨ v, h ⟩ ) ) );
      have := G.sum_degrees_eq_twice_card_edges; simp_all +decide ; linarith;

/-
If G has 5 vertices and v has degree 3, there exists an embedding of G - v such that the neighbors of v form a regular triangle (pairwise distance 1).
-/
lemma exists_embedding_with_regular_neighbors {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V)
    (hV : Fintype.card V = 5) (hdeg : G.degree v = 3) :
    ∃ f : {u // u ≠ v} → EuclideanSpace ℝ (Fin 3),
      IsUnitDistanceEmbedding (deleteVertex G v) 3 f ∧
      ∀ x y (hx : G.Adj v x) (hy : G.Adj v y), x ≠ y →
        dist (f ⟨x, (G.ne_of_adj hx).symm⟩)
             (f ⟨y, (G.ne_of_adj hy).symm⟩) = 1 := by
               simp +zetaDelta at *;
               -- Let $N = G.neighborFinset v$. Define $H$ as $G \setminus \{v\}$ with all edges between distinct pairs in $N$ added.
               set N := G.neighborFinset v
               set H : SimpleGraph {u // u ≠ v} := (deleteVertex G v) ⊔ (SimpleGraph.fromEdgeSet {s(u, w) | (u : {u // u ≠ v}) (w : {u // u ≠ v}) (hu : u.val ∈ N) (hw : w.val ∈ N) (huw : u.val ≠ w.val)});
               have h_H_embedding : HasUnitDistanceEmbedding H 3 := by
                 have h_H_embedding : Fintype.card {u : V | u ≠ v} ≤ 4 := by
                   simp +decide [ hV ];
                 convert dim_le_3_of_card_le_4 H h_H_embedding |> fun h => _;
                 have h_embedding : ∃ d, HasUnitDistanceEmbedding H d ∧ d ≤ 3 := by
                   exact ⟨ _, Nat.sInf_mem ( show ∃ d, HasUnitDistanceEmbedding H d from exists_embedding H ), h ⟩;
                 exact embedding_dim_mono H ( by linarith [ h_embedding.choose_spec ] ) h_embedding.choose_spec.1;
               obtain ⟨ f, hf ⟩ := h_H_embedding;
               refine' ⟨ f, ⟨ hf.1, fun { u v } huv => _ ⟩, _ ⟩;
               · exact hf.2 ( by aesop );
               · field_simp;
                 intro x y hx hy hxy;
                 convert hf.2 _;
                 simp +zetaDelta at *;
                 exact Or.inr ⟨ ⟨ x, by aesop_cat, y, by aesop_cat, hy, hx, by aesop_cat, by aesop_cat ⟩, hxy ⟩

/-
If a graph has 5 vertices and a vertex v has degree 3, there is exactly one vertex u distinct from v that is not adjacent to v.
-/
lemma exists_unique_non_neighbor {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V)
    (hV : Fintype.card V = 5) (hdeg : G.degree v = 3) :
    ∃! u, u ≠ v ∧ ¬ G.Adj v u := by
      simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ];
      have h_unique : Finset.card (Finset.filter (fun u => ¬u = v ∧ ¬G.Adj v u) Finset.univ) = 1 := by
        rw [ show ( Finset.univ.filter fun u => ¬u = v ∧ ¬G.Adj v u ) = Finset.univ \ ( { v } ∪ Finset.filter ( fun u => G.Adj v u ) Finset.univ ) by ext; aesop, Finset.card_sdiff ] ; simp +decide [ * ];
      exact (Fintype.existsUnique_iff_card_one fun a => ¬a = v ∧ ¬G.Adj v a).mpr h_unique

/-
Given a unit distance embedding of G - v and a point p that is at distance 1 from neighbors of v and distinct from non-neighbors of v, we can extend the embedding to G.
-/
lemma embedding_extension {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V)
    (f' : {u // u ≠ v} → EuclideanSpace ℝ (Fin 3))
    (hf' : IsUnitDistanceEmbedding (deleteVertex G v) 3 f')
    (p : EuclideanSpace ℝ (Fin 3))
    (hp_adj : ∀ u (h : G.Adj v u), dist p (f' ⟨u, G.ne_of_adj (G.adj_symm h)⟩) = 1)
    (hp_not_adj : ∀ u (h : u ≠ v), ¬ G.Adj v u → p ≠ f' ⟨u, h⟩) :
    HasUnitDistanceEmbedding G 3 := by
      refine' ⟨ fun u => if hu : u = v then p else f' ⟨ u, hu ⟩, _, _ ⟩ <;> simp_all +decide [ IsUnitDistanceEmbedding ];
      · intro u w h_eq; by_cases hu : u = v <;> by_cases hw : w = v <;> simp_all +decide [ Function.Injective.eq_iff hf'.1 ] ;
        · contrapose! hp_not_adj;
          exact ⟨ w, hw, by rintro H; specialize hp_adj _ H; aesop, rfl ⟩;
        · by_cases h : G.Adj v u <;> simp_all +decide [ eq_comm ];
          exact absurd ( hp_adj u h ) ( by norm_num [ h.symm ] );
      · intro u w h;
        by_cases hu : u = v <;> by_cases hw : w = v <;> simp +decide [ * ];
        · aesop;
        · grind;
        · rw [ ← hp_adj u ( by simpa [ hw ] using h.symm ) ];
          exact dist_comm _ _;
        · exact hf'.2 u hu w hw ( by simpa [ hu, hw ] using h )

/-
If a graph has fewer than 9 edges and minimum degree at least 3, it can be embedded in dimension 3.
-/
lemma min_degree_ge_3_edges_lt_9_embeds {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hE : G.edgeFinset.card < 9) (hmin : ∀ v, 3 ≤ G.degree v) :
    HasUnitDistanceEmbedding G 3 := by
      -- By `degree_le_2_or_small` and `hmin`, we have `Fintype.card V ≤ 5`.
      have h_card : Fintype.card V ≤ 5 := by
        have := SimpleGraph.sum_degrees_eq_twice_card_edges G;
        have := Finset.sum_le_sum fun v ( hv : v ∈ Finset.univ ) => hmin v; norm_num at this; linarith;
      by_cases h_card : Fintype.card V ≤ 4;
      · have := dim_le_3_of_card_le_4 G h_card;
        exact embedding_dim_mono G this ( by exact Nat.sInf_mem ( show { d | HasUnitDistanceEmbedding G d }.Nonempty from ⟨ _, exists_embedding G |> Classical.choose_spec ⟩ ) );
      · -- Since Fintype.card V = 5, we can apply the lemma to find a vertex v with degree 3.
        obtain ⟨v, hv⟩ : ∃ v : V, G.degree v = 3 := by
          apply exists_deg_3_of_card_5_edges_lt_9 G (by linarith) hE hmin;
        obtain ⟨f', hf', hp⟩ : ∃ f' : {u // u ≠ v} → EuclideanSpace ℝ (Fin 3), IsUnitDistanceEmbedding (deleteVertex G v) 3 f' ∧ ∀ x y (hx : G.Adj v x) (hy : G.Adj v y), x ≠ y → dist (f' ⟨x, (G.ne_of_adj hx).symm⟩) (f' ⟨y, (G.ne_of_adj hy).symm⟩) = 1 := by
          apply exists_embedding_with_regular_neighbors G v (by
          linarith) hv
        -- By `exists_unique_non_neighbor`, there is a unique vertex `u` distinct from `v` that is not adjacent to `v`.
        obtain ⟨u, hu⟩ : ∃! u : V, u ≠ v ∧ ¬ G.Adj v u := by
          convert exists_unique_non_neighbor G v ( by linarith ) hv;
        -- Let `x, y, z` be the images of the three neighbors of `v` under `f`. They form a regular triangle.
        obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ : ∃ x y z : {u // u ≠ v}, G.Adj v x.val ∧ G.Adj v y.val ∧ G.Adj v z.val ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ dist (f' x) (f' y) = 1 ∧ dist (f' x) (f' z) = 1 ∧ dist (f' y) (f' z) = 1 := by
          have h_neighbors : Finset.card (Finset.filter (fun u => G.Adj v u) (Finset.univ.erase v)) = 3 := by
            simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ];
            convert hv using 2 ; ext ; aesop;
          obtain ⟨ x, y, z, h ⟩ := Finset.card_eq_three.mp h_neighbors;
          simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
          exact ⟨ x, h.2.2.2.2.1.2, h.2.2.2.2.1.1, y, h.2.2.2.2.2.1.2, h.2.2.2.2.2.1.1, z, h.2.2.2.2.2.2.2, by tauto, by tauto, by tauto, hp x y h.2.2.2.2.1.2 h.2.2.2.2.2.1.2 h.1, by tauto, hp x z h.2.2.2.2.1.2 h.2.2.2.2.2.2.2 h.2.1, hp y z h.2.2.2.2.2.1.2 h.2.2.2.2.2.2.2 h.2.2.1 ⟩;
        -- By `regular_triangle_sphere_intersection_avoid`, there exists a point `p` at distance 1 from `x, y, z` and distinct from `u'`.
        obtain ⟨p, hp_dist, hp_ne⟩ : ∃ p : EuclideanSpace ℝ (Fin 3), dist p (f' x) = 1 ∧ dist p (f' y) = 1 ∧ dist p (f' z) = 1 ∧ p ≠ f' ⟨u, hu.left.left⟩ := by
          apply regular_triangle_sphere_intersection_avoid;
          · exact hxyz.2.2.2.1;
          · exact hxyz.2.2.2.2.2;
          · grind;
        apply embedding_extension G v f' hf' p;
        · intro u hu;
          have := Finset.eq_of_subset_of_card_le ( show { x.val, y.val, z.val } ⊆ G.neighborFinset v from by aesop_cat ) ; simp_all +decide ;
          rw [ Finset.ext_iff ] at this ; specialize this ( by rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> aesop ) u ; aesop;
        · grind

/-
The number of edges in G is the number of edges in G-v plus the degree of v.
-/
lemma card_edges_deleteVertex {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V) :
    G.edgeFinset.card = (deleteVertex G v).edgeFinset.card + G.degree v := by
      unfold deleteVertex;
      -- The edges of G are partitioned into those incident to v and those not incident to v. The edges not incident to v are exactly the edges of the induced subgraph, which has cardinality (G.edgeFinset.filter (fun e => v ∉ e)).card. The edges incident to v are exactly G.degree v.
      have h_partition : G.edgeFinset = (G.edgeFinset.filter (fun e => v ∉ e)) ∪ (G.incidenceFinset v) := by
        ext e;
        simp +decide [ SimpleGraph.incidenceSet, SimpleGraph.incidenceSet ];
        tauto;
      have h_partition_card : G.edgeFinset.card = (G.edgeFinset.filter (fun e => v ∉ e)).card + (G.incidenceFinset v).card := by
        rw [ ← Finset.card_union_of_disjoint, ← h_partition ];
        simp +contextual [ Finset.disjoint_left, SimpleGraph.incidenceSet ];
      convert h_partition_card;
      · refine' Finset.card_bij ( fun e he => Sym2.map ( fun u => u.val ) e ) _ _ _;
        · simp +decide [ Sym2.forall ];
        · rintro ⟨ u, hu ⟩ hu' ⟨ w, hw ⟩ hw' h; rcases u with ⟨ u, hu ⟩ ; rcases w with ⟨ w, hw ⟩ ; simp +decide at h ⊢;
          grind;
        · simp +decide [ SimpleGraph.edgeSet, Sym2.forall ];
          intro x y hxy hx hy; use s(⟨x, by tauto⟩, ⟨y, by tauto⟩); simp +decide [ hxy ] ;
      · exact Eq.symm (card_incidenceFinset_eq_degree G v)

/-
Adding a non-existing edge increases the edge count by 1.
-/
lemma card_edges_addEdge {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (u v : V)
    (h : ¬ G.Adj u v) (h_ne : u ≠ v) :
    (addEdge G u v).edgeFinset.card = G.edgeFinset.card + 1 := by
      unfold addEdge;
      simp +decide [ *, SimpleGraph.edgeFinset ];
      rw [ Finset.card_union_of_disjoint ];
      · simp +decide [ Finset.card_sdiff, * ];
      · rw [ Finset.disjoint_left ] ; aesop

/-
If a vertex v has degree 2 and its neighbors u, w are not adjacent, then removing v and adding edge (u,w) results in a graph with strictly fewer edges.
-/
lemma card_edges_step_deg_2_not_adj {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V)
    (u w : V) (hu : G.Adj v u) (hw : G.Adj v w) (huw : u ≠ w) (hdeg : G.degree v = 2)
    (h_not_adj : ¬ G.Adj u w) :
    (addEdge (deleteVertex G v) ⟨u, (G.ne_of_adj hu).symm⟩ ⟨w, (G.ne_of_adj hw).symm⟩).edgeFinset.card < G.edgeFinset.card := by
      -- By Lemma~\ref{lem:card_edges_deleteVertex}, $G.edgeFinset.card = (deleteVertex G v).edgeFinset.card + G.degree v$.
      have h_card : G.edgeFinset.card = (deleteVertex G v).edgeFinset.card + G.degree v := by
        exact card_edges_deleteVertex G v;
      -- By Lemma~\ref{lem:card_edges_addEdge}, $G'.edgeFinset.card = (deleteVertex G v).edgeFinset.card + 1$.
      have h_card_add : (addEdge (deleteVertex G v) ⟨u, (G.ne_of_adj hu).symm⟩ ⟨w, (G.ne_of_adj hw).symm⟩).edgeFinset.card = (deleteVertex G v).edgeFinset.card + 1 := by
        apply card_edges_addEdge;
        · exact fun h => h_not_adj <| by simpa using h;
        · grind +ring;
      linarith

/-
The complete bipartite graph K_{3,3} has 9 edges.
-/
theorem K33_edges_final : (completeBipartiteGraph (Fin 3) (Fin 3)).edgeFinset.card = 9 := by
  convert K33_edges

/-
If a graph G has an isolated vertex v, and G - v embeds in R^3, then G embeds in R^3.
-/
lemma embed_isolated {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V)
    (h : G.degree v = 0) (h_emb : HasUnitDistanceEmbedding (deleteVertex G v) 3) :
    HasUnitDistanceEmbedding G 3 := by
      obtain ⟨ f', hf' ⟩ := h_emb;
      -- Since V is finite, the image of f' is finite. R^3 is infinite, so there exists a point p in R^3 not in the image of f'.
      obtain ⟨ p, hp ⟩ : ∃ p : EuclideanSpace ℝ (Fin 3), p ∉ Set.range f' := by
        by_contra h_contra;
        have h_finite_image : Set.Finite (Set.range f') := by
          exact Set.toFinite _;
        have h_infinite_space : Set.Infinite (Set.univ : Set (EuclideanSpace ℝ (Fin 3))) := by
          exact Set.infinite_univ_iff.mpr ( by exact Infinite.of_injective ( fun n => EuclideanSpace.single 0 n ) fun a b hab => by simpa using congr_fun hab 0 );
        exact h_infinite_space ( h_finite_image.subset fun x _ => by aesop );
      refine' ⟨ _, _ ⟩;
      exact fun u => if hu : u = v then p else f' ⟨ u, hu ⟩;
      constructor;
      · intro u u' h; by_cases hu : u = v <;> by_cases hu' : u' = v <;> simp_all +decide ;
        · specialize hp u' hu'; aesop;
        · have := hf'.1 h; aesop;
      · intro u w huw; by_cases hu : u = v <;> by_cases hv : w = v <;> simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ] ;
        · exact False.elim ( h huw.symm );
        · exact hf'.2 ( by aesop )

/-
Every graph with fewer than 9 edges has a unit-distance embedding in R^3.
-/
lemma edges_lt_9_embeds_in_3_measure (n : ℕ) :
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    3 * G.edgeFinset.card + Fintype.card V = n → G.edgeFinset.card < 9 → HasUnitDistanceEmbedding G 3 := by
      intro V _ _ G hn hE;
      -- We prove this by strong induction on `n`.
      induction' n using Nat.strong_induction_on with n ih generalizing V G;
      -- If `∀ v, G.degree v ≥ 3`, then `min_degree_ge_3_edges_lt_9_embeds` applies.
      by_cases h_min_deg : ∀ v, G.degree v ≥ 3;
      · exact min_degree_ge_3_edges_lt_9_embeds G hE h_min_deg;
      · -- Otherwise, there exists `v` with `G.degree v ≤ 2`.
        obtain ⟨v, hv⟩ : ∃ v, G.degree v ≤ 2 := by
          grind;
        interval_cases _ : G.degree v <;> simp_all +decide only;
        · -- If `G.degree v = 0`, then `v` is an isolated vertex. Let `G' = deleteVertex G v`.
          set G' := deleteVertex G v
          have hG' : 3 * G'.edgeFinset.card + Fintype.card {u : V // u ≠ v} < n := by
            have hG'_edges : G'.edgeFinset.card = G.edgeFinset.card := by
              refine' Finset.card_bij ( fun e he => Sym2.map ( Subtype.val ) e ) _ _ _ <;> simp +decide [ *, Sym2.map ];
              · rintro ⟨ a, b ⟩ hab ; aesop;
              · rintro ⟨ a, b ⟩ hab ⟨ c, d ⟩ hcd h; simp_all +decide [ Quot.map ] ;
                exact Or.imp ( fun h => ⟨ Subtype.ext h.1, Subtype.ext h.2 ⟩ ) ( fun h => ⟨ Subtype.ext h.1, Subtype.ext h.2 ⟩ ) h;
              · rintro ⟨ u, w ⟩ huv; use Sym2.mk ( ⟨ u, by
                  rintro rfl; simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ] ⟩, ⟨ w, by
                  intro h; simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ] ;
                  exact ‹∀ x, ¬G.Adj v x› u huv.symm ⟩ ) ; aesop;
            simp_all +decide
            linarith [ Nat.sub_add_cancel ( show 1 ≤ Fintype.card V from Fintype.card_pos_iff.mpr ⟨ v ⟩ ) ];
          by_cases hG'_edges : G'.edgeFinset.card < 9;
          · have hdv : G.degree v = 0 := by
              subst hn
              simp_all only [Set.toFinset_card, Fintype.card_ofFinset, ge_iff_le, not_forall, not_le, ne_eq,
                forall_const, Fintype.card_subtype_compl, Fintype.card_unique, G']
            exact
              embed_isolated G v hdv
                (ih (3 * G'.edgeFinset.card + Fintype.card { u // u ≠ v }) hG' (deleteVertex G v)
                  rfl hG'_edges)
          · linarith [ card_edges_deleteVertex G v ];
        · -- Let `G' = deleteVertex G v`.
          set G' : SimpleGraph {u : V // u ≠ v} := deleteVertex G v;
          -- By the induction hypothesis, `G'` embeds in R^3.
          have hG'_embed : HasUnitDistanceEmbedding G' 3 := by
            apply ih (3 * G'.edgeFinset.card + Fintype.card {u : V // u ≠ v});
            · have h_card_edges : G.edgeFinset.card = G'.edgeFinset.card + G.degree v := by
                exact card_edges_deleteVertex G v;
              simp_all +decide
              omega;
            · rfl;
            · have h_card_edges : G'.edgeFinset.card + G.degree v = G.edgeFinset.card := by
                exact Eq.symm (card_edges_deleteVertex G v);
              linarith;
          have hdv : G.degree v = 1 := by
            subst hn
            simp_all only [Set.toFinset_card, Fintype.card_ofFinset, ge_iff_le, not_forall, not_le, ne_eq,
              forall_const, G']
          exact embed_extend_deg_1 G v hdv hG'_embed
        · -- Let `u, w` be neighbors.
          obtain ⟨u, w, hu, hw, huw⟩ : ∃ u w : V, G.Adj v u ∧ G.Adj v w ∧ u ≠ w := by
            obtain ⟨ u, hu ⟩ := G.degree_pos_iff_exists_adj v |>.1 ( by linarith );
            obtain ⟨ w, hw ⟩ := Finset.exists_mem_ne ( show 1 < Finset.card ( G.neighborFinset v ) from by simp +decide [ * ] ) u; use u, w; aesop;
          by_cases h_adj : G.Adj u w;
          · -- Let `G' = deleteVertex G v`.
            set G' : SimpleGraph {u : V // u ≠ v} := deleteVertex G v;
            -- By the induction hypothesis, `G'` embeds in R^3.
            have hG'_embed : HasUnitDistanceEmbedding G' 3 := by
              apply ih (3 * G'.edgeFinset.card + Fintype.card {u : V // u ≠ v});
              · have h_card_edges : G.edgeFinset.card = G'.edgeFinset.card + 2 := by
                  convert card_edges_deleteVertex G v using 1;
                  grind;
                simp_all +decide [ Fintype.card_subtype ];
                grind;
              · rfl;
              · have h_card_edges_deleteVertex : G.edgeFinset.card = G'.edgeFinset.card + G.degree v := by
                  exact card_edges_deleteVertex G v;
                linarith;
            convert embed_extend_deg_2_adj G v u w hu hw huw ‹_› h_adj hG'_embed using 1;
          · -- Let `G' = addEdge (deleteVertex G v) u w`.
            set G' : SimpleGraph {u : V // u ≠ v} := addEdge (deleteVertex G v) ⟨u, (G.ne_of_adj hu).symm⟩ ⟨w, (G.ne_of_adj hw).symm⟩;
            -- By the induction hypothesis, `G'` embeds in R^3.
            have hG'_embed : HasUnitDistanceEmbedding G' 3 := by
              apply ih (3 * G'.edgeFinset.card + Fintype.card {u : V // u ≠ v});
              · have hG'_edges : G'.edgeFinset.card < G.edgeFinset.card := by
                  apply card_edges_step_deg_2_not_adj G v u w hu hw huw ‹_› h_adj;
                simp_all +decide [ Fintype.card_subtype ];
                grind;
              · rfl;
              · have h_card_edges_G' : G'.edgeFinset.card ≤ G.edgeFinset.card - 2 + 1 := by
                  have hn'_lt_n : G'.edgeFinset.card ≤ (deleteVertex G v).edgeFinset.card + 1 := by
                    -- The edge set of G' is the union of the edge set of deleteVertex G v and the new edge between u and w.
                    have h_edge_union : G'.edgeFinset = (deleteVertex G v).edgeFinset ∪ {s(⟨u, (G.ne_of_adj hu).symm⟩, ⟨w, (G.ne_of_adj hw).symm⟩)} := by
                      ext ⟨x, y⟩; simp [G'];
                      simp [addEdge, deleteVertex];
                      grind;
                    exact h_edge_union ▸ Finset.card_union_le _ _;
                  have := card_edges_deleteVertex G v; aesop;
                omega;
            apply embed_extend_deg_2_not_adj G v u w hu hw huw ‹_› h_adj hG'_embed

/-
Every graph with fewer than 9 edges has a unit-distance embedding in R^3.
-/
theorem edges_lt_9_embeds_in_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (h : G.edgeFinset.card < 9) : HasUnitDistanceEmbedding G 3 := by
      apply edges_lt_9_embeds_in_3_measure;
      exacts [ rfl, h ]

/-
The smallest number of edges in a graph with dimension 4 is 9.
-/
theorem erdos_1007 : IsLeast {n : ℕ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V), GraphDimension G = 4 ∧ G.edgeFinset.card = n} 9 := by
  constructor;
  · use ( Sum ( Fin 3 ) ( Fin 3 ) );
    use inferInstance, inferInstance, completeBipartiteGraph ( Fin 3 ) ( Fin 3 );
    exact ⟨ dim_K33_eq_4, K33_edges_final ⟩;
  · intros n hn
    obtain ⟨V, hV, hD, G, hG, hn_eq⟩ := hn;
    contrapose! hG;
    -- By `edges_lt_9_embeds_in_3`, G embeds in R^3.
    have h_embedding : HasUnitDistanceEmbedding G 3 := by
      exact edges_lt_9_embeds_in_3 G ( by linarith );
    exact ne_of_lt ( lt_of_le_of_lt ( Nat.sInf_le h_embedding ) ( Nat.lt_succ_self _ ) )

#print axioms erdos_1007
-- 'erdos_1007' depends on axioms: [propext, Classical.choice, Quot.sound]
