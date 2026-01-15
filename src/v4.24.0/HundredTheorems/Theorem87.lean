/-

This is a Lean formalization of

87: Desargues’s Theorem


This was proven formally by Aristotle (from Harmonic), given an
informal proof by ChatGPT-5.2 Pro (from OpenAI).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

-/

import Mathlib


open scoped EuclideanGeometry

/-- The (standard) Euclidean plane as a real inner product space. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- `P` is a common point of the lines determined by `(A,B)` and `(A',B')`. -/
def IntersectsIn (A B A' B' P : Plane) : Prop :=
  Collinear ℝ ({A, B, P} : Set Plane) ∧
  Collinear ℝ ({A', B', P} : Set Plane)

/-- `P` is the **unique** intersection point of the lines through `A,B` and `A',B'`. -/
def UniqueIntersection (A B A' B' P : Plane) : Prop :=
  IntersectsIn A B A' B' P ∧
  ∀ Q : Plane,
    IntersectsIn A B A' B' Q → Q = P

/-
**Desargues's theorem in the Euclidean plane (nondegenerate version).**

Let `ABC` and `A'B'C'` be two (not necessarily disjoint) triangles in the Euclidean plane.
Assume the joining lines `AA'`, `BB'`, `CC'` are concurrent at a point `O`. Suppose that

* `Pab` is the unique intersection of the lines `AB` and `A'B'`,
* `Pbc` is the unique intersection of the lines `BC` and `B'C'`,
* `Pca` is the unique intersection of the lines `CA` and `C'A'`.

Then the three points `Pab`, `Pbc`, `Pca` are collinear.

The "unique intersection" hypotheses rule out the degenerate configurations
where the corresponding sides coincide (or a triangle collapses to a point or a segment),
which is exactly what breaks the earlier naive formulation.
-/
noncomputable section AristotleLemmas

/-
The sum of the coefficients used in the Desargues algebraic identity is zero.
-/
lemma desargues_coeffs_sum (α β γ : ℝ) :
  (1 - γ) * (β - α) + (1 - α) * (γ - β) + (1 - β) * (α - γ) = 0 := by
  ring

/-
The weighted sum of the numerators of the Desargues points is zero.
-/
lemma desargues_vector_sum_zero (A B C : Plane) (α β γ : ℝ) :
  (1 - γ) • ((β * (1 - α)) • B - (α * (1 - β)) • A) +
  (1 - α) • ((γ * (1 - β)) • C - (β * (1 - γ)) • B) +
  (1 - β) • ((α * (1 - γ)) • A - (γ * (1 - α)) • C) = 0 := by
  ext ; norm_num ; ring

/-
If three points satisfy a non-trivial linear combination with coefficients summing to zero, they are collinear.
-/
lemma collinear_of_lin_comb_zero {A B C : Plane} {a b c : ℝ}
  (h_sum : a + b + c = 0)
  (h_comb : a • A + b • B + c • C = 0)
  (h_nontriv : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
  Collinear ℝ ({A, B, C} : Set Plane) := by
  rcases eq_or_ne c 0 <;> simp_all +decide [ collinear_pair ];
  · simp_all +decide [ add_eq_zero_iff_eq_neg ];
    rw [ collinear_iff_exists_forall_eq_smul_vadd ] ; aesop;
    exact ⟨ A, C - A, ⟨ 0, by norm_num ⟩, ⟨ 0, by simp_all +decide [ smul_right_inj ] ⟩, ⟨ 1, by norm_num ⟩ ⟩;
  · rw [ collinear_iff_exists_forall_eq_smul_vadd ] ; use B; aesop;
    refine' ⟨ A - B, ⟨ 1, by norm_num ⟩, ⟨ ( a : ℝ ) / ( a + b ), _ ⟩ ⟩;
    ext x ; have := congr_fun h_comb x ; norm_num at *;
    grind +ring

/-
The algebraic identity for Desargues's theorem holds.
-/
lemma desargues_algebraic_identity
  (A B C : Plane) (α β γ : ℝ)
  (hαβ : α ≠ β) (hβγ : β ≠ γ) (hγα : γ ≠ α) :
  let Pab := (β - α)⁻¹ • ((β * (1 - α)) • B - (α * (1 - β)) • A)
  let Pbc := (γ - β)⁻¹ • ((γ * (1 - β)) • C - (β * (1 - γ)) • B)
  let Pca := (α - γ)⁻¹ • ((α * (1 - γ)) • A - (γ * (1 - α)) • C)
  Collinear ℝ ({Pab, Pbc, Pca} : Set Plane) := by
  -- By definition of collinearity, we need to show that there exists a line such that all three points lie on it.
  set a : ℝ := (1 - γ) * (β - α)
  set b : ℝ := (1 - α) * (γ - β)
  set c : ℝ := (1 - β) * (α - γ);
  -- We have `a • Pab + b • Pbc + c • Pca = 0` by `desargues_vector_sum_zero`.
  have h_comb : a • ((β - α)⁻¹ • ((β * (1 - α)) • B - (α * (1 - β)) • A)) +
                b • ((γ - β)⁻¹ • ((γ * (1 - β)) • C - (β * (1 - γ)) • B)) +
                c • ((α - γ)⁻¹ • ((α * (1 - γ)) • A - (γ * (1 - α)) • C)) = 0 := by
                  convert desargues_vector_sum_zero A B C α β γ using 1;
                  simp +zetaDelta at *;
                  simp +decide [ ← smul_assoc, mul_assoc, mul_comm ( β - α ), mul_comm ( γ - β ), mul_comm ( α - γ ), sub_ne_zero.mpr ( Ne.symm hαβ ), sub_ne_zero.mpr ( Ne.symm hβγ ), sub_ne_zero.mpr ( Ne.symm hγα ) ];
  -- To prove collinearity, we use that if a linear combination of three points with sum of coefficients zero equals zero, then the points are collinear.
  apply collinear_of_lin_comb_zero;
  any_goals tauto;
  · linear_combination' desargues_coeffs_sum α β γ;
  · grind

/-
If A, A', and O are collinear and A is not O, then A' - O is a scalar multiple of A - O.
-/
lemma exists_scalar_of_collinear {A A' O : Plane}
  (h : Collinear ℝ ({A, A', O} : Set Plane))
  (hA : A ≠ O) :
  ∃ α : ℝ, A' - O = α • (A - O) := by
  rw [ collinear_iff_exists_forall_eq_smul_vadd ] at h ; aesop;
  -- Since $w_3 • w_1 - w_4 • w_1$ and $w_2 • w_1 - w_4 • w_1$ are parallel, there exists a scalar $\alpha$ such that $w_3 • w_1 - w_4 • w_1 = \alpha • (w_2 • w_1 - w_4 • w_1)$.
  use (w_3 - w_4) / (w_2 - w_4);
  ext ; norm_num ; ring;
  grind

/-
If A' = αA and B' = βB with α ≠ β, the intersection of AB and A'B' is given by a specific formula.
-/
lemma desargues_intersection_formula
  {A B A' B' P : Plane} {α β : ℝ}
  (hA : A' = α • A) (hB : B' = β • B)
  (hαβ : α ≠ β)
  (h_unique : UniqueIntersection A B A' B' P) :
  P = (β - α)⁻¹ • ((β * (1 - α)) • B - (α * (1 - β)) • A) := by
  obtain ⟨hP₁, hP₂⟩ := h_unique;
  contrapose! hP₂; simp_all +decide [ collinear_pair, hP₁, IntersectsIn ] ; ring_nf at * ; norm_num at *;
  -- Let's choose any point $Q$ that lies on both lines $AB$ and $A'B'$.
  obtain ⟨Q, hQ⟩ : ∃ Q : Plane, Collinear ℝ ({A, B, Q} : Set Plane) ∧ Collinear ℝ ({α • A, β • B, Q} : Set Plane) ∧ Q ≠ P := by
    refine' ⟨ ( β - α ) ⁻¹ • ( ( β - β * α ) • B - ( - ( β * α ) + α ) • A ), _, _, _ ⟩ <;> simp_all +decide [ collinear_pair ];
    · rw [ collinear_iff_exists_forall_eq_smul_vadd ] ; use A ; aesop;
      refine' ⟨ B - A, ⟨ 1, by norm_num ⟩, ( β - α ) ⁻¹ * ( β - β * α ), _ ⟩ ; ext ; norm_num ; ring;
      linarith [ inv_mul_cancel_left₀ ( sub_ne_zero_of_ne ( Ne.symm hαβ ) ) ( A ‹_› ) ];
    · rw [ collinear_iff_exists_forall_eq_smul_vadd ] ; use α • A ; aesop;
      refine' ⟨ β • B - α • A, _, _ ⟩ <;> norm_num [ sub_smul ];
      · exact ⟨ 1, by norm_num ⟩;
      · use ( β - α ) ⁻¹ * ( 1 - α ) ; ext ; norm_num ; ring;
        grind;
    · exact Ne.symm hP₂;
  exact ⟨ Q, ⟨ hQ.1, hQ.2.1 ⟩, hQ.2.2 ⟩

/-
If two lines defined by pairs of points have a unique intersection, then the defining points of each line must be distinct.
-/
lemma unique_intersection_implies_distinct_points {A B A' B' P : Plane}
  (h : UniqueIntersection A B A' B' P) :
  A ≠ B ∧ A' ≠ B' := by
  -- Suppose A = B. Then Collinear {A, B, Q} is true for all Q.
  by_cases hAB : A = B;
  · -- If A = B, then any point Q on the line through A and B would also be on the line through A' and B', contradicting the uniqueness of P.
    have h_contradiction : ∀ Q : Plane, Collinear ℝ ({A', B', Q} : Set Plane) → Q = P := by
      -- By definition of UniqueIntersection, if Q is on the line through A' and B', then Q must be equal to P.
      intros Q hQ
      apply h.right Q
      aesop;
      constructor <;> simp_all ( config := { decide := Bool.true } ) [ collinear_pair ];
    rcases eq_or_ne A' B' <;> simp_all +decide [ collinear_pair ];
    exact absurd ( h_contradiction ( P + EuclideanSpace.single 0 1 ) ) ( ne_of_apply_ne ( fun x => x 0 ) ( by norm_num ) );
  · cases h ; aesop;
    unfold IntersectsIn at *;
    have := right ( A + ( B - A ) ) ; simp_all +decide [ collinear_pair ] ;

set_option maxHeartbeats 0 in
/-
If two lines have a unique intersection, their direction vectors cannot be parallel.
-/
lemma not_parallel_of_unique_intersection {A B A' B' P : Plane}
  (h : UniqueIntersection A B A' B' P) (k : ℝ) :
  B' - A' ≠ k • (B - A) := by
  have h_distinct : A ≠ B ∧ A' ≠ B' := by
    exact unique_intersection_implies_distinct_points h |> fun h' => ⟨ h'.1, h'.2 ⟩;
  -- If $B' - A'$ were parallel to $B - A$, then the lines $AB$ and $A'B'$ would be parallel.
  by_contra h_parallel
  have h_parallel_lines : ∀ t : ℝ, ∃ s : ℝ, A' + t • (B' - A') = A + s • (B - A) := by
    -- Since P lies on both lines AB and A'B', we can express P as P = A + s • (B - A) and P = A' + t • (B' - A').
    obtain ⟨s, hs⟩ : ∃ s : ℝ, P = A + s • (B - A) := by
      have := h.1.1;
      rw [ collinear_iff_exists_forall_eq_smul_vadd ] at this;
      bound;
      obtain ⟨ r, hr ⟩ := h_1 A ( by norm_num ) ; obtain ⟨ s, hs ⟩ := h_1 B ( by norm_num ) ; obtain ⟨ t, ht ⟩ := h_1 P ( by norm_num ) ; use ( t - r ) / ( s - r ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
      ext ; norm_num ; ring;
      grind +ring
    obtain ⟨t, ht⟩ : ∃ t : ℝ, P = A' + t • (B' - A') := by
      have := h.1.2;
      bound;
      rw [ collinear_iff_exists_forall_eq_smul_vadd ] at this;
      simp +zetaDelta at *;
      obtain ⟨ p₀, v, ⟨ r₁, hr₁ ⟩, ⟨ r₂, hr₂ ⟩, ⟨ r₃, hr₃ ⟩ ⟩ := this;
      aesop;
      use ( r₃ - r₁ ) / ( r₂ - r₁ );
      rw [ ← h_parallel ] ; ext ; norm_num ; ring;
      grind;
    aesop;
    exact ⟨ s + ( t_1 - t ) * k, by ext ; have := congr_fun hs ‹_› ; norm_num at * ; linarith ⟩;
  have h_parallel_lines : ∀ t : ℝ, A' + t • (B' - A') ∈ {x : Plane | Collinear ℝ ({A, B, x} : Set Plane)} := by
    intro t; obtain ⟨ s, hs ⟩ := h_parallel_lines t; simp +decide [ hs, collinear_pair ] ;
    rw [ collinear_iff_exists_forall_eq_smul_vadd ];
    exact ⟨ A, B - A, by rintro x ( rfl | rfl | rfl ) <;> [ exact ⟨ 0, by norm_num ⟩ ; exact ⟨ 1, by norm_num ⟩ ; exact ⟨ s, by norm_num [ add_comm ] ⟩ ] ⟩;
  have h_parallel_lines : ∀ t : ℝ, A' + t • (B' - A') ∈ {x : Plane | Collinear ℝ ({A', B', x} : Set Plane)} := by
    intro t; simp [collinear_iff_exists_forall_eq_smul_vadd];
    exact ⟨ A', B' - A', ⟨ 0, by norm_num ⟩, ⟨ 1, by norm_num ⟩, ⟨ t, by abel1 ⟩ ⟩;
  have h_parallel_lines : ∀ t : ℝ, A' + t • (B' - A') = P := by
    intros t
    apply h.right;
    unfold IntersectsIn; aesop;
  have := h_parallel_lines 0; have := h_parallel_lines 1; simp_all +decide [ sub_eq_iff_eq_add ] ;

/-
If A' = αA and B' = βB and the lines AB and A'B' have a unique intersection, then α ≠ β.
-/
lemma desargues_scalars_ne {A B A' B' P : Plane} {α β : ℝ}
  (hA : A' = α • A) (hB : B' = β • B)
  (h_unique : UniqueIntersection A B A' B' P) :
  α ≠ β := by
    intro h; have := not_parallel_of_unique_intersection h_unique; simp_all +decide [ sub_eq_iff_eq_add ] ;
    exact this β ( by ext x; simpa using by ring )

set_option maxHeartbeats 0 in
/-
The property of being a unique intersection point is invariant under translation.
-/
lemma unique_intersection_translation_invariance (v : Plane) (A B A' B' P : Plane) :
  UniqueIntersection (A - v) (B - v) (A' - v) (B' - v) (P - v) ↔ UniqueIntersection A B A' B' P := by
  constructor <;> intro h;
  · unfold UniqueIntersection at * ; aesop;
    · unfold IntersectsIn at *;
      norm_num [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
      bound;
      · exact ⟨ v + w, w_2, ⟨ w_4, by ext i; have := congr_fun h i; norm_num at *; linarith ⟩, ⟨ w_6, by ext i; have := congr_fun h_2 i; norm_num at *; linarith ⟩, ⟨ w_7, by ext i; have := congr_fun h_3 i; norm_num at *; linarith ⟩ ⟩;
      · exact ⟨ w_1 + v, w_3, ⟨ w_5, by ext ; have := congr_fun h_1 ‹_› ; norm_num at * ; linarith ⟩, ⟨ w_8, by ext ; have := congr_fun h_4 ‹_› ; norm_num at * ; linarith ⟩, ⟨ w_9, by ext ; have := congr_fun h_5 ‹_› ; norm_num at * ; linarith ⟩ ⟩;
    · -- By definition of IsLine, we know that Q - v satisfies the collinearity conditions for A - v, B - v, A' - v, and B' - v.
      have h_collinear : Collinear ℝ ({A - v, B - v, Q - v} : Set Plane) ∧ Collinear ℝ ({A' - v, B' - v, Q - v} : Set Plane) := by
        bound;
        · unfold IntersectsIn at a;
          rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
          norm_num +zetaDelta at *;
          bound;
          exact ⟨ w - v, w_1, ⟨ w_2, by abel1 ⟩, ⟨ w_3, by abel1 ⟩, ⟨ w_4, by abel1 ⟩ ⟩;
        · unfold IntersectsIn at a; aesop;
          rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
          obtain ⟨ p₀, v, hv ⟩ := right_1;
          norm_num +zetaDelta at *;
          exact ⟨ p₀ - _, v, by obtain ⟨ r, hr ⟩ := hv.1; exact ⟨ r, by ext i; simpa using by have := congr_fun hr i; norm_num at *; linarith ⟩, by obtain ⟨ r, hr ⟩ := hv.2.1; exact ⟨ r, by ext i; simpa using by have := congr_fun hr i; norm_num at *; linarith ⟩, by obtain ⟨ r, hr ⟩ := hv.2.2; exact ⟨ r, by ext i; simpa using by have := congr_fun hr i; norm_num at *; linarith ⟩ ⟩;
      have := right ( Q - v ) ⟨ h_collinear.1, h_collinear.2 ⟩ ; aesop;
  · constructor;
    · unfold IntersectsIn; aesop;
      · have h_collinear : Collinear ℝ ({A, B, P} : Set Plane) := by
          exact h.1.1;
        rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
        aesop;
        exact ⟨ w - v, w_1, ⟨ w_2, by abel1 ⟩, ⟨ w_3, by abel1 ⟩, ⟨ w_4, by abel1 ⟩ ⟩;
      · rw [ collinear_iff_exists_forall_eq_smul_vadd ] ; use A' - v; aesop;
        have := h.1.2;
        rw [ collinear_iff_exists_forall_eq_smul_vadd ] at this ; aesop;
        exact ⟨ w_1, ⟨ w_3 - w_2, by ext ; simpa using by ring ⟩, ⟨ w_4 - w_2, by ext ; simpa using by ring ⟩ ⟩;
    · rintro Q ⟨ hcollinear_left, hcollinear_right ⟩;
      -- By definition of collinearity, if Q is collinear with A - v, B - v, and A' - v, B' - v, then Q - v is collinear with A, B, and A', B'.
      have h_collinear_Qv : Collinear ℝ ({A, B, Q + v} : Set Plane) ∧ Collinear ℝ ({A', B', Q + v} : Set Plane) := by
        simp_all +decide [ collinear_iff_exists_forall_eq_smul_vadd ];
        exact ⟨ by obtain ⟨ p₀, v_1, ⟨ r₁, hr₁ ⟩, ⟨ r₂, hr₂ ⟩, ⟨ r₃, hr₃ ⟩ ⟩ := hcollinear_left; exact ⟨ p₀ + v, v_1, ⟨ r₁, by ext i; have := congr_fun hr₁ i; have := congr_fun hr₂ i; have := congr_fun hr₃ i; norm_num at *; linarith ⟩, ⟨ r₂, by ext i; have := congr_fun hr₁ i; have := congr_fun hr₂ i; have := congr_fun hr₃ i; norm_num at *; linarith ⟩, ⟨ r₃, by ext i; have := congr_fun hr₁ i; have := congr_fun hr₂ i; have := congr_fun hr₃ i; norm_num at *; linarith ⟩ ⟩, by obtain ⟨ p₀, v_1, ⟨ r₁, hr₁ ⟩, ⟨ r₂, hr₂ ⟩, ⟨ r₃, hr₃ ⟩ ⟩ := hcollinear_right; exact ⟨ p₀ + v, v_1, ⟨ r₁, by ext i; have := congr_fun hr₁ i; have := congr_fun hr₂ i; have := congr_fun hr₃ i; norm_num at *; linarith ⟩, ⟨ r₂, by ext i; have := congr_fun hr₁ i; have := congr_fun hr₂ i; have := congr_fun hr₃ i; norm_num at *; linarith ⟩, ⟨ r₃, by ext i; have := congr_fun hr₁ i; have := congr_fun hr₂ i; have := congr_fun hr₃ i; norm_num at *; linarith ⟩ ⟩ ⟩;
      have := h.2 ( Q + v ) ⟨ h_collinear_Qv.1, h_collinear_Qv.2 ⟩ ; aesop;

/-
The affine version of the Desargues intersection formula, derived by translating the origin to O.
-/
lemma desargues_intersection_formula_affine
  {A B A' B' O P : Plane} {α β : ℝ}
  (hA : A' - O = α • (A - O)) (hB : B' - O = β • (B - O))
  (hαβ : α ≠ β)
  (h_unique : UniqueIntersection A B A' B' P) :
  P - O = (β - α)⁻¹ • ((β * (1 - α)) • (B - O) - (α * (1 - β)) • (A - O)) := by
  have h_translation : UniqueIntersection (A - O) (B - O) (A' - O) (B' - O) (P - O) := by
    exact?;
  apply desargues_intersection_formula;
  exacts [ hA, hB, hαβ, h_translation ]

/-
Desargues's theorem holds in the degenerate case where A = O.
-/
lemma desargues_plane_A_eq_O
  {A B C A' B' C' O Pab Pbc Pca : Plane}
  (hA : A = O)
  (hO_BB' : Collinear ℝ ({B, B', O} : Set Plane))
  (hO_CC' : Collinear ℝ ({C, C', O} : Set Plane))
  (hPab : UniqueIntersection A B A' B' Pab)
  (hPbc : UniqueIntersection B C B' C' Pbc)
  (hPca : UniqueIntersection C A C' A' Pca) :
  Collinear ℝ ({Pab, Pbc, Pca} : Set Plane) := by
  -- Since $A = O$, the line $AB$ passes through $O$ and $B$, and the line $A'B'$ passes through $O$ and $B'$.
  -- Thus, $B'$ is an intersection point of $AB$ and $A'B'$.
  -- By uniqueness, $Pab = B'$.
  have hPabB' : Pab = B' := by
    -- Since $B'$ is on both lines $AB$ and $A'B'$, and $Pab$ is the unique intersection, $B'$ must equal $Pab$.
    have hB'_intersection : IntersectsIn A B A' B' B' := by
      constructor;
      · simp_all +decide [ collinear_iff_exists_forall_eq_smul_vadd ];
        grind;
      · simp [collinear_pair];
    exact hPab.2 B' hB'_intersection ▸ rfl;
  -- Similarly, $C'$ is an intersection point of $CA$ and $C'A'$.
  -- By uniqueness, $Pca = C'$.
  have hPcaC' : Pca = C' := by
    unfold UniqueIntersection at *; aesop;
    rw [ ← right C' ];
    unfold IntersectsIn; simp [hO_CC'];
    exact ⟨ by simpa only [ Set.insert_comm, Set.pair_comm ] using hO_CC', collinear_pair ℝ _ _ ⟩
  aesop;
  have := hPbc.1.2;
  simp_all ( config := { decide := Bool.true } ) [ collinear_iff_exists_forall_eq_smul_vadd ];
  exact ⟨ this.choose, this.choose_spec.choose, ⟨ this.choose_spec.choose_spec.1.choose, this.choose_spec.choose_spec.1.choose_spec ⟩, ⟨ this.choose_spec.choose_spec.2.2.choose, this.choose_spec.choose_spec.2.2.choose_spec ⟩, ⟨ this.choose_spec.choose_spec.2.1.choose, this.choose_spec.choose_spec.2.1.choose_spec ⟩ ⟩

end AristotleLemmas

set_option maxHeartbeats 0 in
theorem desargues_plane
  {A B C A' B' C' O Pab Pbc Pca : Plane}
  -- concurrency at O
  (hO_AA' : Collinear ℝ ({A, A', O} : Set Plane))
  (hO_BB' : Collinear ℝ ({B, B', O} : Set Plane))
  (hO_CC' : Collinear ℝ ({C, C', O} : Set Plane))
  -- unique intersections of corresponding sides
  (hPab : UniqueIntersection A B A' B' Pab)
  (hPbc : UniqueIntersection B C B' C' Pbc)
  (hPca : UniqueIntersection C A C' A' Pca) :
  -- conclusion: these three intersection points are collinear
  Collinear ℝ ({Pab, Pbc, Pca} : Set Plane) :=
by
  -- Consider two cases: $A \neq O$, $B \neq O$, and $C \neq O$.
  by_cases hAO : A ≠ O
  by_cases hBO : B ≠ O
  by_cases hCO : C ≠ O;
  · -- Since A, B, C are distinct from O, we can apply the affine Desargues theorem.
    obtain ⟨α, β, γ, hα, hβ, hγ⟩ : ∃ α β γ : ℝ, A' - O = α • (A - O) ∧ B' - O = β • (B - O) ∧ C' - O = γ • (C - O) ∧ α ≠ β ∧ β ≠ γ ∧ γ ≠ α := by
      -- By definition of collinearity, since $A$, $A'$, and $O$ are collinear, there exists a scalar $\alpha$ such that $A' - O = \alpha • (A - O)$.
      obtain ⟨α, hα⟩ : ∃ α : ℝ, A' - O = α • (A - O) := by
        exact exists_scalar_of_collinear hO_AA' hAO
      obtain ⟨β, hβ⟩ : ∃ β : ℝ, B' - O = β • (B - O) := by
        apply exists_scalar_of_collinear hO_BB' hBO
      obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, C' - O = γ • (C - O) := by
        exact exists_scalar_of_collinear ( by simpa [ collinear_pair ] using hO_CC' ) ( by simpa [ collinear_pair ] using hCO );
      refine' ⟨ α, β, γ, hα, hβ, hγ, _, _, _ ⟩ <;> intro h <;> simp_all +decide [ sub_eq_iff_eq_add ];
      · have := not_parallel_of_unique_intersection hPab β; simp_all ( config := { decide := Bool.true } ) [ sub_eq_iff_eq_add ] ;
        exact this ( by ext ; norm_num ; ring );
      · have := not_parallel_of_unique_intersection hPbc ( γ : ℝ ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
        exact this ( by rw [ ← smul_add, show C - B + ( B - O ) = C - O by abel1 ] );
      · have := not_parallel_of_unique_intersection hPca;
        exact this α ( by ext ; norm_num ; ring );
    -- Using the affine intersection formula, we can express Pab - O, Pbc - O, Pca - O in terms of A-O, B-O, C-O and α, β, γ.
    have hPab_expr : Pab - O = (β - α)⁻¹ • ((β * (1 - α)) • (B - O) - (α * (1 - β)) • (A - O)) := by
      exact desargues_intersection_formula_affine hα hβ hγ.2.1 hPab
    have hPbc_expr : Pbc - O = (γ - β)⁻¹ • ((γ * (1 - β)) • (C - O) - (β * (1 - γ)) • (B - O)) := by
      convert desargues_intersection_formula_affine _ _ _ using 1 <;> aesop
    have hPca_expr : Pca - O = (α - γ)⁻¹ • ((α * (1 - γ)) • (A - O) - (γ * (1 - α)) • (C - O)) := by
      exact desargues_intersection_formula_affine ( by simpa using hγ.1 ) ( by simpa using hα ) ( by tauto ) ( by simpa [ UniqueIntersection ] using hPca ) ▸ by ring;
    -- By the algebraic identity proven in `desargues_algebraic_identity`, the points `Pab - O`, `Pbc - O`, `Pca - O` are collinear.
    have h_collinear : Collinear ℝ ({Pab - O, Pbc - O, Pca - O} : Set Plane) := by
      rw [ hPab_expr, hPbc_expr, hPca_expr ];
      convert desargues_algebraic_identity ( A - O ) ( B - O ) ( C - O ) α β γ ( Ne.symm <| by tauto ) ( Ne.symm <| by tauto ) ( Ne.symm <| by tauto ) using 1;
    rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
    obtain ⟨ p₀, v, hv ⟩ := h_collinear;
    use p₀ + O, v;
    simp +zetaDelta at *;
    exact ⟨ by obtain ⟨ r, hr ⟩ := hv.1; exact ⟨ r, by ext i; have := congr_fun hr i; norm_num at *; linarith ⟩, by obtain ⟨ r, hr ⟩ := hv.2.1; exact ⟨ r, by ext i; have := congr_fun hr i; norm_num at *; linarith ⟩, by obtain ⟨ r, hr ⟩ := hv.2.2; exact ⟨ r, by ext i; have := congr_fun hr i; norm_num at *; linarith ⟩ ⟩;
  · have hPbcB' : Pbc = B' := by
      have hB'_intersection : IntersectsIn B C B' C' B' := by
        unfold IntersectsIn; aesop;
        · rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
          exact ⟨ hO_BB'.choose, hO_BB'.choose_spec.choose, fun p hp => by simpa using hO_BB'.choose_spec.choose_spec p <| by aesop ⟩;
        · exact collinear_pair _ _ _;
      exact hPbc.2 B' hB'_intersection ▸ rfl
    have hPcaA' : Pca = A' := by
      have hPcaA' : IntersectsIn C A C' A' A' := by
        constructor <;> simp_all +decide [ collinear_pair ];
        rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
        obtain ⟨ p₀, v, hp₀ ⟩ := hO_AA'; use p₀, v; intro p hp; specialize hp₀ p; aesop;
      exact hPca.2 A' hPcaA' ▸ rfl
    aesop;
    have := hPab.1.1; have := hPab.1.2; simp_all +decide [ collinear_pair ] ;
    rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
    exact ⟨ this.choose, this.choose_spec.choose, fun p hp => this.choose_spec.choose_spec p ( by aesop ) ⟩;
  · have hPabA' : Pab = A' := by
      have := hPab.2 A' ?_ <;> aesop ( simp_config := { singlePass := true } );
      unfold IntersectsIn; aesop;
      · rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
        obtain ⟨ p₀, v, hv ⟩ := hO_AA'; use p₀, v; intro p hp; specialize hv p; aesop;
      · exact collinear_pair _ _ _
    have hPbcC' : Pbc = C' := by
      -- Since $C' = B$, the line $BC$ passes through $B$ and $C$, and the line $B'C'$ passes through $B'$ and $C'$. Thus, $C'$ is an intersection of $BC$ and $B'C'$.
      have hC'_intersection : Collinear ℝ ({B, C, C'} : Set Plane) ∧ Collinear ℝ ({B', C', C'} : Set Plane) := by
        simp_all +decide [ collinear_pair ];
        rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
        exact ⟨ hO_CC'.choose, hO_CC'.choose_spec.choose, fun p hp => by obtain ⟨ r, hr ⟩ := hO_CC'.choose_spec.choose_spec p ( by aesop ) ; exact ⟨ r, hr ⟩ ⟩;
      exact hPbc.2 C' hC'_intersection ▸ rfl
    aesop;
    have := hPca.1.2; simp_all +decide [ collinear_iff_exists_forall_eq_smul_vadd ] ;
    exact ⟨ this.choose, this.choose_spec.choose, this.choose_spec.choose_spec.2.1, this.choose_spec.choose_spec.1, this.choose_spec.choose_spec.2.2 ⟩;
  · convert desargues_plane_A_eq_O ( Classical.not_not.mp hAO ) hO_BB' hO_CC' hPab hPbc hPca using 1
