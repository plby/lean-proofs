/-

This is a Lean formalization of

61: Theorem of Ceva


This was proven formally by Aristotle (from Harmonic), given an
informal proof by ChatGPT-5.2 Pro (from OpenAI).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

-/

/-
This module contains a formal statement and proof of Ceva's Theorem in the Euclidean plane.
It defines the necessary geometric conditions using affine spaces and barycentric coordinates.
The main result, `ceva_theorem`, proves that for a triangle ABC and points A₁, B₁, C₁ on its sides,
the lines AA₁, BB₁, and CC₁ are concurrent if and only if the product of the ratios of the segments
(BA₁/A₁C * CB₁/B₁A * AC₁/C₁B) equals 1.
The proof is decomposed into forward and reverse directions (`ceva_forward` and `ceva_reverse`),
utilizing helper lemmas to translate between geometric incidence and algebraic conditions on barycentric coordinates.
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

open EuclideanGeometry Affine AffineSubspace Set

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

#check AffineIndependent
#check ![ (1 : ℕ), 2, 3 ]

#check AffineSpace

#check segment
#check Wbtw

#print AffineBasis

/-
A point `p` lies on the affine segment between the second and third points of an affine basis `b` (indexed by `Fin 3`) if and only if its first barycentric coordinate is 0 and the other two are non-negative.
-/
open EuclideanGeometry Affine AffineSubspace Set

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

lemma mem_affineSegment_iff_barycentric_coords_zero
    (b : AffineBasis (Fin 3) ℝ P) (p : P) :
    p ∈ affineSegment ℝ (b 1) (b 2) ↔
    b.coord 0 p = 0 ∧ 0 ≤ b.coord 1 p ∧ 0 ≤ b.coord 2 p := by
  constructor <;> intro hp;
  · obtain ⟨ t, ht, rfl ⟩ := hp;
    aesop;
    · simp +decide [ AffineMap.lineMap_apply ] ; linarith;
    · exact left.trans ( by simp +decide [ AffineMap.lineMap_apply ] );
  · have := b.sum_coord_apply_eq_one p;
    rw [ Fin.sum_univ_three ] at this;
    refine' ⟨ ( b.coord 2 ) p, _, _ ⟩ <;> aesop;
    · linarith;
    · convert b.affineCombination_coord_eq_self p using 1;
      rw [ Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one ] <;> norm_num [ Fin.sum_univ_three, this ];
      swap;
      exact b 1;
      simp +decide [ left, left_1, right, AffineMap.lineMap_apply ]

/-
A point `O` lies on the line connecting the first basis point `b 0` and a point `A₁` (which lies on the opposite side, i.e., its first coordinate is 0) if and only if the second and third barycentric coordinates of `O` are proportional to those of `A₁`.
-/
open EuclideanGeometry Affine AffineSubspace Set

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

lemma mem_line_iff_barycentric_proportional
    (b : AffineBasis (Fin 3) ℝ P) (O : P) (A₁ : P)
    (hA₁_on_BC : b.coord 0 A₁ = 0) :
    O ∈ line[ℝ, b 0, A₁] ↔
    b.coord 1 O * b.coord 2 A₁ = b.coord 2 O * b.coord 1 A₁ := by
  constructor;
  · rw [ affineSpan ];
    aesop;
    simp_all +decide [ spanPoints ];
    cases' a with a a;
    · rw [ vectorSpan_pair ] at a;
      simp_all +decide [ Submodule.mem_span_singleton ];
      -- By definition of barycentric coordinates, we know that
      have h_barycentric : ∀ p q : P, ∀ a : ℝ, (b.coord 1) (a • (p -ᵥ q) +ᵥ q) = a * ((b.coord 1) p - (b.coord 1) q) + (b.coord 1) q ∧ (b.coord 2) (a • (p -ᵥ q) +ᵥ q) = a * ((b.coord 2) p - (b.coord 2) q) + (b.coord 2) q := by
        intro p q a;
        have h_barycentric : ∀ p q : P, ∀ a : ℝ, (b.coord 1) (a • (p -ᵥ q) +ᵥ q) = a * ((b.coord 1) p - (b.coord 1) q) + (b.coord 1) q ∧ (b.coord 2) (a • (p -ᵥ q) +ᵥ q) = a * ((b.coord 2) p - (b.coord 2) q) + (b.coord 2) q := by
          intro p q a
          have h_barycentric : ∀ i : Fin 3, (b.coord i) (a • (p -ᵥ q) +ᵥ q) = a * ((b.coord i) p - (b.coord i) q) + (b.coord i) q := by
            intro i;
            have h_barycentric : ∀ p q : P, ∀ a : ℝ, (b.coord i) (a • (p -ᵥ q) +ᵥ q) = a * ((b.coord i) p - (b.coord i) q) + (b.coord i) q := by
              intro p q a
              have h_barycentric : ∀ (f : P →ᵃ[ℝ] ℝ), f (a • (p -ᵥ q) +ᵥ q) = a * (f p - f q) + f q := by
                intro f;
                have := f.map_vadd q ( a • ( p -ᵥ q ) ) ; aesop
              convert h_barycentric ( b.coord i ) using 1;
            exact h_barycentric p q a
          exact ⟨h_barycentric 1, h_barycentric 2⟩;
        exact h_barycentric p q a;
      have := h_barycentric A₁ ( b 0 ) 1; aesop;
      ring;
    · rcases a with ⟨ v, hv, rfl ⟩;
      -- Since $v \in \text{vectorSpan} \{b 0, A₁\}$, we can write $v = t \cdot (A₁ - b 0)$ for some scalar $t$.
      obtain ⟨t, ht⟩ : ∃ t : ℝ, v = t • (A₁ -ᵥ b 0) := by
        rw [ vectorSpan_pair ] at hv;
        rw [ Submodule.mem_span_singleton ] at hv;
        bound;
        exact ⟨ -w, by rw [ neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev ] ⟩;
      -- Substitute $v = t \cdot (A₁ - b 0)$ into the coordinates.
      have h_coords : b.coord 1 (v +ᵥ A₁) = b.coord 1 A₁ + t * (b.coord 1 A₁ - b.coord 1 (b 0)) ∧ b.coord 2 (v +ᵥ A₁) = b.coord 2 A₁ + t * (b.coord 2 A₁ - b.coord 2 (b 0)) := by
        have h_coords : ∀ (p q : P) (t : ℝ), b.coord 1 (t • (p -ᵥ q) +ᵥ p) = b.coord 1 p + t * (b.coord 1 p - b.coord 1 q) ∧ b.coord 2 (t • (p -ᵥ q) +ᵥ p) = b.coord 2 p + t * (b.coord 2 p - b.coord 2 q) := by
          intro p q t;
          have h_coords : ∀ (p q : P) (t : ℝ), b.coord 1 (t • (p -ᵥ q) +ᵥ p) = b.coord 1 p + t * (b.coord 1 p - b.coord 1 q) ∧ b.coord 2 (t • (p -ᵥ q) +ᵥ p) = b.coord 2 p + t * (b.coord 2 p - b.coord 2 q) := by
            intro p q t
            have h_linear : ∀ (f : P →ᵃ[ℝ] ℝ), f (t • (p -ᵥ q) +ᵥ p) = f p + t * (f p - f q) := by
              intro f; have := f.map_vadd; aesop;
              ring
            exact ⟨ h_linear _, h_linear _ ⟩;
          exact h_coords p q t;
        simpa only [ ht, add_comm ] using h_coords A₁ ( b 0 ) t;
      aesop ; ring;
  · intro h;
    rw [ affineSpan, ];
    simp +decide [ spanPoints ];
    -- Let's express O as a linear combination of b 0 and A₁.
    obtain ⟨c, hc⟩ : ∃ c : ℝ, O = c • (b 0 -ᵥ A₁) +ᵥ A₁ := by
      have h_comb : ∃ c : ℝ, (b.coord 1 O) = c * (b.coord 1 (b 0) - b.coord 1 A₁) + b.coord 1 A₁ ∧ (b.coord 2 O) = c * (b.coord 2 (b 0) - b.coord 2 A₁) + b.coord 2 A₁ := by
        by_cases h₁ : b.coord 1 (b 0) - b.coord 1 A₁ = 0 <;> by_cases h₂ : b.coord 2 (b 0) - b.coord 2 A₁ = 0 <;> simp_all +decide [ sub_eq_iff_eq_add ];
        · have h_comb : ∑ i : Fin 3, b.coord i A₁ = 1 := by
            exact?;
          rw [ Fin.sum_univ_three ] at h_comb ; aesop;
        · exact ⟨ ( b.coord 2 A₁ - b.coord 2 O ) / b.coord 2 A₁, by rw [ div_mul_cancel₀ _ h₂ ] ; ring ⟩;
        · exact ⟨ ( b.coord 1 A₁ - b.coord 1 O ) / b.coord 1 A₁, by rw [ div_mul_cancel₀ _ h₁ ] ; ring ⟩;
        · use ( ( b.coord 1 A₁ - b.coord 1 O ) / b.coord 1 A₁ );
          field_simp [h₁, h₂];
          constructor <;> linarith;
      obtain ⟨ c, hc₁, hc₂ ⟩ := h_comb;
      have h_comb : ∀ i : Fin 3, (b.coord i O) = c * (b.coord i (b 0) - b.coord i A₁) + b.coord i A₁ := by
        intro i
        by_cases hi : i = 0 ∨ i = 1 ∨ i = 2;
        · aesop;
          have h_sum : (b.coord 0 O) + (b.coord 1 O) + (b.coord 2 O) = 1 := by
            have := b.sum_coord_apply_eq_one O;
            rwa [ Fin.sum_univ_three ] at this;
          have h_sum_A₁ : (b.coord 0 A₁) + (b.coord 1 A₁) + (b.coord 2 A₁) = 1 := by
            have := b.sum_coord_apply_eq_one A₁;
            rwa [ Fin.sum_univ_three ] at this;
          grind +ring;
        · fin_cases i <;> contradiction;
      use c;
      convert b.ext_elem fun i => ?_;
      convert h_comb i using 1;
      simp +decide [ AffineBasis.coord ];
      rw [ show ( b 0 -ᵥ A₁ : V ) = ( b 0 -ᵥ b i ) + ( b i -ᵥ A₁ ) by rw [ vsub_add_vsub_cancel ] ] ; simp +decide [ Finset.sum_add_distrib, mul_add, add_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm ] ;
      rw [ show ( A₁ -ᵥ b i : V ) = - ( b i -ᵥ A₁ ) by rw [ neg_vsub_eq_vsub_rev ], map_neg ] ; simp +decide [ Finset.sum_neg_distrib, mul_neg ];
    simp_all +decide [ vectorSpan_pair ];
    exact Or.inr ⟨ c • ( b 0 -ᵥ A₁ ), Submodule.smul_mem _ _ ( Submodule.subset_span ( Set.mem_singleton _ ) ), by simp +decide ⟩

/-
If a point `p` lies on the segment between two basis points `b i` and `b j`, then `dist (b i) p * b.coord i p = dist p (b j) * b.coord j p`.
-/
open EuclideanGeometry Affine AffineSubspace Set

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

lemma dist_mul_coord_eq_dist_mul_coord
    (b : AffineBasis (Fin 3) ℝ P) (i j : Fin 3) (p : P)
    (hp : p ∈ affineSegment ℝ (b i) (b j)) (hij : i ≠ j) :
    dist (b i) p * b.coord i p = dist p (b j) * b.coord j p := by
  rcases hp with ⟨ a, ha, b, hb, hab, rfl ⟩;
  -- By definition of barycentric coordinates, we know that
  have h_bcoord : (b.coord i) ((AffineMap.lineMap ((b : Fin 3 → P) i) ((b : Fin 3 → P) j) : ℝ → P) a) = 1 - a ∧ (b.coord j) ((AffineMap.lineMap ((b : Fin 3 → P) i) ((b : Fin 3 → P) j) : ℝ → P) a) = a := by
    aesop;
    · simp +decide [ AffineMap.lineMap_apply ];
      ring;
    · simp +decide [ AffineMap.lineMap_apply, hij ];
      -- By definition of barycentric coordinates, we know that $(b.coord j) (b i) = 0$ since $i \neq j$.
      have h_bcoord_j_i : (b.coord j) (b i) = 0 := by
        exact?;
      rw [ h_bcoord_j_i ] ; ring;
  simp +decide [ *, dist_eq_norm_vsub ];
  rw [ norm_smul, norm_smul, Real.norm_of_nonneg ha.1, Real.norm_of_nonneg ( sub_nonneg.2 ha.2 ) ] ; ring

/-
Given three affine independent points A, B, C, they form an affine basis for the affine subspace they span.
-/
open EuclideanGeometry Affine AffineSubspace Set

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

noncomputable def triangleBasis
    (A B C : P) (h : AffineIndependent ℝ ![A, B, C]) :
    AffineBasis (Fin 3) ℝ (affineSpan ℝ (Set.range ![A, B, C])) :=
  AffineBasis.mk (fun i => ⟨![A, B, C] i, subset_affineSpan ℝ (Set.range ![A, B, C]) (mem_range_self i)⟩)
    (by
    convert h
    generalize_proofs at *;
    rw [ affineIndependent_iff_linearIndependent_vsub, affineIndependent_iff_linearIndependent_vsub ];
    rotate_left;
    exact?;
    exact 2;
    simp +decide [ linearIndependent_iff', Subtype.ext_iff ])
    (by
    refine' AffineSubspace.ext_of_direction_eq _ _;
    · ext x
      generalize_proofs at *;
      simp +decide [ direction_affineSpan ];
      rcases x with ⟨ x, hx ⟩;
      rw [ direction_affineSpan ] at hx;
      rw [ vectorSpan_eq_span_vsub_set_right ] at hx ⊢;
      rotate_left;
      exact ⟨ A, subset_affineSpan ℝ _ ( Set.mem_range_self 0 ) ⟩;
      exact ⟨ 0, rfl ⟩;
      exact A;
      · exact ⟨ 0, rfl ⟩;
      · rw [ Submodule.mem_span ] at hx ⊢;
        intro p hp;
        convert hx ( Submodule.map ( Submodule.subtype ( affineSpan ℝ ( Set.range ![A, B, C] ) |> AffineSubspace.direction ) ) p ) _;
        · simp +decide [ Submodule.mem_map ];
          exact ⟨ fun hx => ⟨ by simpa [ Set.insert_comm ] using ‹x ∈ ( affineSpan ℝ ( Set.range ![A, B, C] ) ).direction›, hx ⟩, fun ⟨ _, hx ⟩ => hx ⟩;
        · norm_num +zetaDelta at *;
          rintro x ( rfl | rfl | rfl ) <;> [ exact ⟨ _, hp ( Set.mem_range_self 2 ) |> fun h => by aesop ⟩ ; exact ⟨ _, hp ( Set.mem_range_self 1 ) |> fun h => by aesop ⟩ ; exact ⟨ _, hp ( Set.mem_range_self 0 ) |> fun h => by aesop ⟩ ];
    · exact ⟨ ⟨ A, mem_affineSpan ℝ ( Set.mem_range_self 0 ) ⟩, Set.mem_inter ( mem_affineSpan ℝ ( Set.mem_range_self 0 ) ) ( Set.mem_univ _ ) ⟩)

open EuclideanGeometry Affine AffineSubspace Set

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

lemma subtype_dist_eq (s : Set P) (x y : s) : dist x y = dist (x : P) (y : P) := rfl

/-
The product of distances condition in Ceva's theorem is equivalent to the product of barycentric coordinates condition.
-/
open EuclideanGeometry Affine AffineSubspace Set

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

lemma ceva_dist_eq_iff_coord_eq
    (b : AffineBasis (Fin 3) ℝ P)
    (A₁ B₁ C₁ : P)
    (hA₁ : A₁ ∈ affineSegment ℝ (b 1) (b 2))
    (hB₁ : B₁ ∈ affineSegment ℝ (b 2) (b 0))
    (hC₁ : C₁ ∈ affineSegment ℝ (b 0) (b 1)) :
    dist (b 1) A₁ * dist (b 2) B₁ * dist (b 0) C₁ = dist A₁ (b 2) * dist B₁ (b 0) * dist C₁ (b 1) ↔
    b.coord 2 A₁ * b.coord 0 B₁ * b.coord 1 C₁ = b.coord 1 A₁ * b.coord 2 B₁ * b.coord 0 C₁ := by
  bound;
  · have h_prod_eq : dist (b 1) A₁ * b.coord 1 A₁ = dist A₁ (b 2) * b.coord 2 A₁ := by
      apply dist_mul_coord_eq_dist_mul_coord;
      · exact hA₁;
      · decide
    have h_prod_eq' : dist (b 2) B₁ * b.coord 2 B₁ = dist B₁ (b 0) * b.coord 0 B₁ := by
      apply dist_mul_coord_eq_dist_mul_coord b 2 0 B₁ hB₁ (by decide)
    have h_prod_eq'' : dist (b 0) C₁ * b.coord 0 C₁ = dist C₁ (b 1) * b.coord 1 C₁ := by
      convert dist_mul_coord_eq_dist_mul_coord b 0 1 C₁ hC₁ ( by decide ) using 1;
    by_cases h : Dist.dist A₁ ( b 2 ) * Dist.dist B₁ ( b 0 ) * Dist.dist C₁ ( b 1 ) = 0;
    · simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
      rcases h with ( rfl | rfl | rfl ) <;> simp_all +decide [ dist_comm ];
      · rcases a with ( rfl | h | rfl ) <;> simp_all +decide [ affineSegment ];
        have := b.2;
        have := this.injective;
        exact absurd ( this h ) ( by decide );
      · rcases a with ( rfl | rfl | h ) <;> simp_all +decide [ affineSegment ];
        have := b.2;
        have := this.injective;
        exact absurd ( this h ) ( by decide );
      · rcases a with ( h | rfl | rfl );
        · have := b.2;
          have := this.injective;
          exact absurd ( this h ) ( by decide );
        · simp_all +decide [ dist_comm ];
        · simp_all +decide [ AffineBasis.coord_apply ];
    · exact mul_left_cancel₀ h <| by linear_combination' a * ( b.coord 1 A₁ * b.coord 2 B₁ * b.coord 0 C₁ ) - h_prod_eq * h_prod_eq' * h_prod_eq'';
  · -- Multiply the three equations from `dist_mul_coord_eq_dist_mul_coord` for `A₁`, `B₁`, and `C₁`.
    have h_mul : (dist (b 1) A₁ * b.coord 1 A₁) * (dist (b 2) B₁ * b.coord 2 B₁) * (dist (b 0) C₁ * b.coord 0 C₁) = (dist A₁ (b 2) * b.coord 2 A₁) * (dist B₁ (b 0) * b.coord 0 B₁) * (dist C₁ (b 1) * b.coord 1 C₁) := by
      rw [ dist_mul_coord_eq_dist_mul_coord b 1 2 A₁ hA₁ ( by decide ), dist_mul_coord_eq_dist_mul_coord b 2 0 B₁ hB₁ ( by decide ), dist_mul_coord_eq_dist_mul_coord b 0 1 C₁ hC₁ ( by decide ) ];
    by_cases h : b.coord 2 A₁ * b.coord 0 B₁ * b.coord 1 C₁ = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
    · simp_all +decide [ affineSegment ];
      aesop;
    · grind

/-
Algebraic version of Ceva's theorem: A system of proportionality equations has a solution summing to 1 if and only if the cyclic product of coefficients equals the other cyclic product.
-/
lemma ceva_algebraic_iff (y_A z_A x_B z_B x_C y_C : ℝ)
    (hy_A : 0 ≤ y_A) (hz_A : 0 ≤ z_A) (hA : y_A + z_A = 1)
    (hx_B : 0 ≤ x_B) (hz_B : 0 ≤ z_B) (hB : x_B + z_B = 1)
    (hx_C : 0 ≤ x_C) (hy_C : 0 ≤ y_C) (hC : x_C + y_C = 1) :
    (∃ x y z : ℝ, x + y + z = 1 ∧
      y * z_A = z * y_A ∧
      z * x_B = x * z_B ∧
      x * y_C = y * x_C) ↔
    z_A * x_B * y_C = y_A * z_B * x_C := by
  constructor;
  · grind;
  · by_cases h : z_A = 0 <;> by_cases h' : z_B = 0 <;> by_cases h'' : z_A * x_B = 0 <;> aesop;
    · exact ⟨ x_C, y_C, hC, by ring ⟩;
    · -- Let's choose $y = \frac{y_A}{y_A + z_A}$ and $z = \frac{z_A}{y_A + z_A}$.
      use 0, y_A / (y_A + z_A), z_A / (y_A + z_A);
      grind;
    · use z_A * x_B / (z_A * x_B + z_A * z_B + z_B * y_A), z_B * y_A / (z_A * x_B + z_A * z_B + z_B * y_A), z_A * z_B / (z_A * x_B + z_A * z_B + z_B * y_A);
      field_simp;
      exact ⟨ by ring, trivial, trivial, by linarith ⟩

/-
A point O lies on the line connecting vertex B (b 1) and a point B₁ on the opposite side AC iff the barycentric coordinates of O corresponding to A and C are proportional to those of B₁.
-/
open EuclideanGeometry Affine AffineSubspace Set

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

lemma mem_line_iff_barycentric_proportional_B
    (b : AffineBasis (Fin 3) ℝ P) (O : P) (B₁ : P)
    (hB₁_on_AC : b.coord 1 B₁ = 0) :
    O ∈ line[ℝ, b 1, B₁] ↔
    b.coord 0 O * b.coord 2 B₁ = b.coord 2 O * b.coord 0 B₁ := by
      have := @mem_line_iff_barycentric_proportional;
      convert @this V P _ _ _ _ ( b.reindex ( Equiv.swap 0 1 ) ) O B₁ _ using 1;
      · simp +decide [ AffineBasis.coord, Equiv.swap_apply_def ];
      · simp +decide [ *, AffineBasis.coord_reindex ]

/-
A point O lies on the line connecting vertex C (b 2) and a point C₁ on the opposite side AB iff the barycentric coordinates of O corresponding to A and B are proportional to those of C₁.
-/
open EuclideanGeometry Affine AffineSubspace Set

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

lemma mem_line_iff_barycentric_proportional_C
    (b : AffineBasis (Fin 3) ℝ P) (O : P) (C₁ : P)
    (hC₁_on_AB : b.coord 2 C₁ = 0) :
    O ∈ line[ℝ, b 2, C₁] ↔
    b.coord 0 O * b.coord 1 C₁ = b.coord 1 O * b.coord 0 C₁ := by
      constructor;
      · intro hO
        obtain ⟨t, ht⟩ : ∃ t : ℝ, O = AffineMap.lineMap (b 2) C₁ t := by
          obtain ⟨ t, ht ⟩ := hO;
          rcases ht with ⟨ rfl | rfl, v, hv, rfl ⟩;
          · rw [ vectorSpan_pair ] at hv;
            rw [ Submodule.mem_span_singleton ] at hv;
            aesop;
            simp +decide [ AffineMap.lineMap_apply ];
            exact ⟨ -w, by rw [ neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev ] ⟩;
          · rw [ vectorSpan_pair ] at hv;
            rw [ Submodule.mem_span_singleton ] at hv ; aesop;
            use 1 - w;
            norm_num +zetaDelta at *;
            rw [ AffineMap.lineMap_apply ];
        have h_barycentric : (b.coord 0) (AffineMap.lineMap (b 2) C₁ t) = (1 - t) * (b.coord 0) (b 2) + t * (b.coord 0) C₁ ∧ (b.coord 1) (AffineMap.lineMap (b 2) C₁ t) = (1 - t) * (b.coord 1) (b 2) + t * (b.coord 1) C₁ ∧ (b.coord 2) (AffineMap.lineMap (b 2) C₁ t) = (1 - t) * (b.coord 2) (b 2) + t * (b.coord 2) C₁ := by
          have h_barycentric : ∀ (p q : P) (t : ℝ), (b.coord 0) (AffineMap.lineMap p q t) = (1 - t) * (b.coord 0) p + t * (b.coord 0) q ∧ (b.coord 1) (AffineMap.lineMap p q t) = (1 - t) * (b.coord 1) p + t * (b.coord 1) q ∧ (b.coord 2) (AffineMap.lineMap p q t) = (1 - t) * (b.coord 2) p + t * (b.coord 2) q := by
            norm_num +zetaDelta at *;
            simp +decide [ AffineMap.lineMap_apply ];
            exact fun p q t => ⟨ by ring, by ring, by ring ⟩;
          exact h_barycentric _ _ _;
        have := b.coord_apply 0 2; have := b.coord_apply 1 2; have := b.coord_apply 2 2; aesop;
        ring;
      · simp +decide [ affineSpan, collinear_pair ];
        simp +decide [ spanPoints ];
        rintro h;
        -- Since $O$ lies on the line connecting $b 2$ and $C₁$, we can write $O$ as a linear combination of $b 2$ and $C₁$.
        obtain ⟨t, ht⟩ : ∃ t : ℝ, O = t • (C₁ -ᵥ b 2) +ᵥ b 2 := by
          have h_collinear : ∃ t : ℝ, b.coord 0 O = t * b.coord 0 C₁ ∧ b.coord 1 O = t * b.coord 1 C₁ := by
            by_cases hC₁ : b.coord 0 C₁ = 0 <;> by_cases hC₁' : b.coord 1 C₁ = 0 <;> simp_all +decide [ mul_comm ];
            · have h_sum : b.coord 0 C₁ + b.coord 1 C₁ + b.coord 2 C₁ = 1 := by
                have := b.sum_coord_apply_eq_one C₁;
                rwa [ Fin.sum_univ_three ] at this;
              aesop;
            · exact ⟨ ( b.coord 1 ) O / ( b.coord 1 ) C₁, by rw [ div_mul_cancel₀ _ hC₁' ] ⟩;
            · exact ⟨ ( b.coord 0 O ) / ( b.coord 0 C₁ ), by rw [ div_mul_cancel₀ _ hC₁ ] ⟩;
            · exact ⟨ ( b.coord 0 ) O / ( b.coord 0 ) C₁, by rw [ div_mul_cancel₀ _ hC₁ ], by rw [ div_mul_eq_mul_div, eq_div_iff hC₁ ] ; linarith ⟩;
          obtain ⟨ t, ht₀, ht₁ ⟩ := h_collinear;
          use t;
          have h_coords : ∀ i : Fin 3, b.coord i O = t * b.coord i C₁ + (1 - t) * b.coord i (b 2) := by
            intro i; fin_cases i <;> simp_all +decide [ Fin.sum_univ_three ] ;
            have h_sum : ∑ i, b.coord i O = 1 ∧ ∑ i, b.coord i C₁ = 1 := by
              exact ⟨ b.sum_coord_apply_eq_one O, b.sum_coord_apply_eq_one C₁ ⟩;
            rw [ Fin.sum_univ_three, Fin.sum_univ_three ] at h_sum ; aesop;
            linear_combination' left - right * t;
          refine' b.ext_elem _;
          intro i; rw [ h_coords i ] ; simp +decide [ hC₁_on_AB ] ;
          simp +decide [ Fin.sum_univ_three, AffineBasis.coord ];
          rw [ show ( C₁ -ᵥ b i ) = ( C₁ -ᵥ b 2 ) + ( b 2 -ᵥ b i ) by rw [ vsub_add_vsub_cancel ], show ( b 2 -ᵥ b i ) = ( b 2 -ᵥ b i ) by rfl, map_add ] ; simp +decide [ Finset.sum_add_distrib, mul_add, add_mul, sub_eq_add_neg ] ; ring;
        refine' Or.inl ⟨ t • ( C₁ -ᵥ b 2 ), _, _ ⟩;
        · exact Submodule.smul_mem _ _ ( Submodule.subset_span ⟨ C₁, by simp +decide, b 2, by simp +decide, rfl ⟩ );
        · exact ht

/-
Forward direction of Ceva's Theorem: If the cevians are concurrent, the product of ratios is 1.
-/
open EuclideanGeometry Affine AffineSubspace Set

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

lemma ceva_forward
    (b : AffineBasis (Fin 3) ℝ P)
    (A₁ B₁ C₁ : P)
    (hA₁ : A₁ ∈ affineSegment ℝ (b 1) (b 2))
    (hB₁ : B₁ ∈ affineSegment ℝ (b 2) (b 0))
    (hC₁ : C₁ ∈ affineSegment ℝ (b 0) (b 1))
    (hA₁_ne_B : A₁ ≠ b 1) (hA₁_ne_C : A₁ ≠ b 2)
    (hB₁_ne_C : B₁ ≠ b 2) (hB₁_ne_A : B₁ ≠ b 0)
    (hC₁_ne_A : C₁ ≠ b 0) (hC₁_ne_B : C₁ ≠ b 1)
    (h_concurrent : ∃ O : P, O ∈ line[ℝ, b 0, A₁] ∧ O ∈ line[ℝ, b 1, B₁] ∧ O ∈ line[ℝ, b 2, C₁]) :
    dist (b 1) A₁ * dist (b 2) B₁ * dist (b 0) C₁ = dist A₁ (b 2) * dist B₁ (b 0) * dist C₁ (b 1) := by
      -- Apply the distance product equivalence given by the hypothesis h_dist_ratio_equiv.
      apply (ceva_dist_eq_iff_coord_eq b A₁ B₁ C₁ hA₁ hB₁ hC₁).mpr;
      obtain ⟨ O, hO₁, hO₂, hO₃ ⟩ := h_concurrent;
      -- By the properties of the barycentric coordinates, since O is on the line segments, we have:
      have hO₁_coord : b.coord 1 O * b.coord 2 A₁ = b.coord 2 O * b.coord 1 A₁ := by
        have h_O_A : O ∈ line[ℝ, b 0, A₁] := by
          exact hO₁;
        apply mem_line_iff_barycentric_proportional b O A₁ _ |>.1 h_O_A;
        exact mem_affineSegment_iff_barycentric_coords_zero b A₁ |>.1 hA₁ |>.1
      have hO₂_coord : b.coord 0 O * b.coord 2 B₁ = b.coord 2 O * b.coord 0 B₁ := by
        apply (mem_line_iff_barycentric_proportional_B b O B₁ (by
        cases hB₁ ; aesop)).mp hO₂
      have hO₃_coord : b.coord 0 O * b.coord 1 C₁ = b.coord 1 O * b.coord 0 C₁ := by
        have hO₃_coord : O ∈ line[ℝ, b 2, C₁] := by
          exact hO₃;
        apply (mem_line_iff_barycentric_proportional_C b O C₁ _).mp hO₃_coord;
        obtain ⟨ t, ht ⟩ := hC₁;
        aesop;
      by_cases hO : b.coord 0 O = 0 <;> by_cases hO' : b.coord 1 O = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
      · have h_sum : b.coord 0 O + b.coord 1 O + b.coord 2 O = 1 := by
          have := b.sum_coord_apply_eq_one O;
          rwa [ Fin.sum_univ_three ] at this;
        cases hO₁_coord <;> aesop;
      · cases hO₂_coord <;> simp_all +decide [ AffineBasis.coord_apply ];
      · grind;
      · grind +ring

/-
If a point O has barycentric coordinates (x, y, z) that satisfy the proportionality conditions with respect to points A₁, B₁, C₁ on the sides of a triangle, then O lies on the lines AA₁, BB₁, and CC₁.
-/
open EuclideanGeometry Affine AffineSubspace Set

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

lemma ceva_point_on_lines
    (b : AffineBasis (Fin 3) ℝ P)
    (A₁ B₁ C₁ : P)
    (hA₁ : A₁ ∈ affineSegment ℝ (b 1) (b 2))
    (hB₁ : B₁ ∈ affineSegment ℝ (b 2) (b 0))
    (hC₁ : C₁ ∈ affineSegment ℝ (b 0) (b 1))
    (O : P)
    (x y z : ℝ)
    (h_coords : b.coord 0 O = x ∧ b.coord 1 O = y ∧ b.coord 2 O = z)
    (h_propA : y * b.coord 2 A₁ = z * b.coord 1 A₁)
    (h_propB : z * b.coord 0 B₁ = x * b.coord 2 B₁)
    (h_propC : x * b.coord 1 C₁ = y * b.coord 0 C₁) :
    O ∈ line[ℝ, b 0, A₁] ∧ O ∈ line[ℝ, b 1, B₁] ∧ O ∈ line[ℝ, b 2, C₁] := by
      have h_on_AA₁ : O ∈ line[ℝ, b 0, A₁] := by
        apply mem_line_iff_barycentric_proportional b O A₁ _ |>.2;
        · aesop;
        · exact mem_affineSegment_iff_barycentric_coords_zero b A₁ |>.1 hA₁ |>.1
      have h_on_BB₁ : O ∈ line[ℝ, b 1, B₁] := by
        rw [ mem_line_iff_barycentric_proportional_B ];
        · grind;
        · unfold affineSegment at hB₁;
          aesop
      have h_on_CC₁ : O ∈ line[ℝ, b 2, C₁] := by
        have h_on_CC₁ : O ∈ line[ℝ, b 2, C₁] := by
          have := mem_line_iff_barycentric_proportional_C b O C₁
          unfold affineSegment at *;
          aesop;
        exact h_on_CC₁;
      exact ⟨ h_on_AA₁, h_on_BB₁, h_on_CC₁ ⟩

/-
Reverse direction of Ceva's Theorem: If the product of ratios is 1, the cevians are concurrent.
-/
open EuclideanGeometry Affine AffineSubspace Set

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

lemma ceva_reverse
    (b : AffineBasis (Fin 3) ℝ P)
    (A₁ B₁ C₁ : P)
    (hA₁ : A₁ ∈ affineSegment ℝ (b 1) (b 2))
    (hB₁ : B₁ ∈ affineSegment ℝ (b 2) (b 0))
    (hC₁ : C₁ ∈ affineSegment ℝ (b 0) (b 1))
    (hA₁_ne_B : A₁ ≠ b 1) (hA₁_ne_C : A₁ ≠ b 2)
    (hB₁_ne_C : B₁ ≠ b 2) (hB₁_ne_A : B₁ ≠ b 0)
    (hC₁_ne_A : C₁ ≠ b 0) (hC₁_ne_B : C₁ ≠ b 1)
    (h_dist_prod : dist (b 1) A₁ * dist (b 2) B₁ * dist (b 0) C₁ = dist A₁ (b 2) * dist B₁ (b 0) * dist C₁ (b 1)) :
    ∃ O : P, O ∈ line[ℝ, b 0, A₁] ∧ O ∈ line[ℝ, b 1, B₁] ∧ O ∈ line[ℝ, b 2, C₁] := by
      have h_concurrent : ∃ x y z : ℝ, x + y + z = 1 ∧ y * b.coord 2 A₁ = z * b.coord 1 A₁ ∧ z * b.coord 0 B₁ = x * b.coord 2 B₁ ∧ x * b.coord 1 C₁ = y * b.coord 0 C₁ := by
        -- Let's express the coordinates of $A₁$, $B₁$, and $C₁$ in terms of their barycentric coordinates with respect to $b$.
        obtain ⟨y_A, z_A, hyA, hzA, hA⟩ : ∃ y_A z_A : ℝ, 0 ≤ y_A ∧ 0 ≤ z_A ∧ y_A + z_A = 1 ∧ b.coord 0 A₁ = 0 ∧ b.coord 1 A₁ = y_A ∧ b.coord 2 A₁ = z_A := by
          have := mem_affineSegment_iff_barycentric_coords_zero b A₁;
          have := b.sum_coord_apply_eq_one A₁;
          rw [ Fin.sum_univ_three ] at this; use b.coord 1 A₁, b.coord 2 A₁; aesop;
        obtain ⟨x_B, z_B, hx_B, hz_B, hB⟩ : ∃ x_B z_B : ℝ, 0 ≤ x_B ∧ 0 ≤ z_B ∧ x_B + z_B = 1 ∧ b.coord 0 B₁ = x_B ∧ b.coord 1 B₁ = 0 ∧ b.coord 2 B₁ = z_B := by
          have hB₁_coords : b.coord 1 B₁ = 0 ∧ 0 ≤ b.coord 0 B₁ ∧ 0 ≤ b.coord 2 B₁ := by
            rw [affineSegment_comm] at hB₁;
            have := mem_affineSegment_iff_barycentric_coords_zero b B₁;
            have := mem_affineSegment_iff_barycentric_coords_zero ( b.reindex ( Equiv.swap 0 1 ) ) B₁; simp_all +decide [ affineSegment_eq_segment ] ;
            exact this.mp ( by simpa [ Equiv.swap_apply_def ] using hB₁ ) |> fun h => ⟨ h.1, h.2.1, h.2.2 ⟩;
          have := b.sum_coord_apply_eq_one B₁;
          exact ⟨ b.coord 0 B₁, b.coord 2 B₁, hB₁_coords.2.1, hB₁_coords.2.2, by rw [ Fin.sum_univ_three ] at this; linarith, rfl, hB₁_coords.1, rfl ⟩
        obtain ⟨x_C, y_C, hx_C, hy_C, hC⟩ : ∃ x_C y_C : ℝ, 0 ≤ x_C ∧ 0 ≤ y_C ∧ x_C + y_C = 1 ∧ b.coord 0 C₁ = x_C ∧ b.coord 1 C₁ = y_C ∧ b.coord 2 C₁ = 0 := by
          have h_coords_C₁ : b.coord 2 C₁ = 0 := by
            bound;
            have := mem_affineSegment_iff_barycentric_coords_zero b C₁;
            have := mem_affineSegment_iff_barycentric_coords_zero ( b.reindex ( Equiv.swap 0 2 ) ) C₁; simp_all +decide [ affineSegment_comm ] ;
            exact this.mp ( by simpa using hC₁ ) |>.1;
          have h_coords_C₁_sum : b.coord 0 C₁ + b.coord 1 C₁ + b.coord 2 C₁ = 1 := by
            have := b.sum_coord_apply_eq_one C₁;
            rwa [ Fin.sum_univ_three ] at this;
          aesop;
          · rw [ affineSegment ] at hC₁;
            aesop;
            norm_num [ AffineMap.lineMap_apply ];
            linarith;
          · have h_coords_C₁_nonneg : ∀ i, 0 ≤ b.coord i C₁ := by
              intro i;
              have h_coords_C₁_nonneg : ∀ p ∈ affineSegment ℝ (b 0) (b 1), ∀ i, 0 ≤ b.coord i p := by
                intro p hp i;
                obtain ⟨ t, ht, rfl ⟩ := hp;
                have h_coords_C₁_nonneg : ∀ p ∈ affineSegment ℝ (b 0) (b 1), ∀ i, 0 ≤ b.coord i p := by
                  intro p hp i
                  obtain ⟨ t, ht, rfl ⟩ := hp
                  have h_coords_C₁_nonneg : b.coord i ((AffineMap.lineMap (b 0) (b 1)) t) = (1 - t) * b.coord i (b 0) + t * b.coord i (b 1) := by
                    simp +zetaDelta at *;
                    simp +decide [ AffineMap.lineMap_apply ];
                    ring
                  simp_all +decide [ Fin.forall_fin_succ ];
                  fin_cases i <;> simp +decide [ *, AffineBasis.coord_apply ];
                exact h_coords_C₁_nonneg _ ( by exact ⟨ t, ht, rfl ⟩ ) _;
              exact h_coords_C₁_nonneg C₁ hC₁ i;
            exact h_coords_C₁_nonneg 1;
        simp_all +decide [ dist_comm ];
        -- Apply the algebraic lemma to conclude the existence of x, y, z.
        apply (ceva_algebraic_iff y_A z_A x_B z_B x_C y_C hyA hzA hA.left hx_B hz_B hB.left hx_C hy_C hC.left).mpr;
        have := ceva_dist_eq_iff_coord_eq b A₁ B₁ C₁ hA₁ hB₁ hC₁;
        simp_all +decide [ dist_comm ];
      aesop;
      -- Let $O$ be the point with barycentric coordinates $(x, y, z)$ with respect to the basis $b$.
      obtain ⟨O, hO⟩ : ∃ O : P, b.coord 0 O = w ∧ b.coord 1 O = w_1 ∧ b.coord 2 O = w_2 := by
        have h_affine_comb : ∀ (x : Fin 3 → ℝ), (∑ i, x i = 1) → ∃ O : P, ∀ i, b.coord i O = x i := by
          intro x hx
          use Finset.univ.affineCombination ℝ b x;
          simp +decide [ hx, Finset.affineCombination_eq_linear_combination ];
        exact Exists.elim ( h_affine_comb ( fun i => if i = 0 then w else if i = 1 then w_1 else w_2 ) ( by simp +decide [ Fin.sum_univ_three, * ] ) ) fun O hO => ⟨ O, hO 0, hO 1, hO 2 ⟩;
      use O;
      apply ceva_point_on_lines;
      any_goals assumption

/-
Ceva's Theorem: The lines AA₁, BB₁, CC₁ are concurrent iff the product of the ratios of the segments is 1.
-/
open EuclideanGeometry Affine AffineSubspace Set

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

theorem ceva_theorem
    (b : AffineBasis (Fin 3) ℝ P)
    (A₁ B₁ C₁ : P)
    (hA₁ : A₁ ∈ affineSegment ℝ (b 1) (b 2))
    (hB₁ : B₁ ∈ affineSegment ℝ (b 2) (b 0))
    (hC₁ : C₁ ∈ affineSegment ℝ (b 0) (b 1))
    (hA₁_ne_B : A₁ ≠ b 1) (hA₁_ne_C : A₁ ≠ b 2)
    (hB₁_ne_C : B₁ ≠ b 2) (hB₁_ne_A : B₁ ≠ b 0)
    (hC₁_ne_A : C₁ ≠ b 0) (hC₁_ne_B : C₁ ≠ b 1) :
    (∃ O : P, O ∈ line[ℝ, b 0, A₁] ∧ O ∈ line[ℝ, b 1, B₁] ∧ O ∈ line[ℝ, b 2, C₁]) ↔
    dist (b 1) A₁ * dist (b 2) B₁ * dist (b 0) C₁ = dist A₁ (b 2) * dist B₁ (b 0) * dist C₁ (b 1) := by
      constructor;
      · apply_rules [ ceva_forward ];
      · exact?
