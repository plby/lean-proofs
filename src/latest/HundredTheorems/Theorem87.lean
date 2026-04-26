/-

This is a Lean formalization of

87: Desargues’s Theorem


This was proven formally by Aristotle (from Harmonic), given an
informal proof by ChatGPT-5.2 Pro (from OpenAI).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

-/

import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.longLine false
set_option linter.style.maxHeartbeats false
set_option linter.style.multiGoal false
set_option linter.style.refine false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Theorem87

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

lemma exists_eq_left_add_smul_sub_of_collinear {A B P : Plane}
    (hcol : Collinear ℝ ({A, B, P} : Set Plane)) (hAB : A ≠ B) :
    ∃ s : ℝ, P = A + s • (B - A) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hcol
  rcases hcol with ⟨p₀, v, hv⟩
  rcases hv A (by simp) with ⟨rA, hA⟩
  rcases hv B (by simp) with ⟨rB, hB⟩
  rcases hv P (by simp) with ⟨rP, hP⟩
  have hr : rB - rA ≠ 0 := by
    intro hr
    apply hAB
    ext i
    have hAi := congrArg (fun Q : Plane => Q i) hA
    have hBi := congrArg (fun Q : Plane => Q i) hB
    simp [PiLp.add_apply, PiLp.smul_apply] at hAi hBi
    have : rB = rA := sub_eq_zero.mp hr
    rw [this] at hBi
    linarith
  refine ⟨(rP - rA) / (rB - rA), ?_⟩
  ext i
  have hAi := congrArg (fun Q : Plane => Q i) hA
  have hBi := congrArg (fun Q : Plane => Q i) hB
  have hPi := congrArg (fun Q : Plane => Q i) hP
  simp [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply] at hAi hBi hPi ⊢
  rw [hAi, hBi, hPi]
  field_simp [hr]
  ring

lemma collinear_sub_right_iff (v A B C : Plane) :
    Collinear ℝ ({A - v, B - v, C - v} : Set Plane) ↔
      Collinear ℝ ({A, B, C} : Set Plane) := by
  constructor
  · intro h
    rw [collinear_iff_exists_forall_eq_smul_vadd] at h ⊢
    rcases h with ⟨p₀, d, hd⟩
    refine ⟨p₀ + v, d, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hp | hp | hp
    · rcases hd (A - v) (by simp) with ⟨r, hr⟩
      exact ⟨r, by rw [hp]; ext i; have hri := congrArg (fun Q : Plane => Q i) hr; simp [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply] at hri ⊢; linarith⟩
    · rcases hd (B - v) (by simp) with ⟨r, hr⟩
      exact ⟨r, by rw [hp]; ext i; have hri := congrArg (fun Q : Plane => Q i) hr; simp [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply] at hri ⊢; linarith⟩
    · rcases hd (C - v) (by simp) with ⟨r, hr⟩
      exact ⟨r, by rw [hp]; ext i; have hri := congrArg (fun Q : Plane => Q i) hr; simp [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply] at hri ⊢; linarith⟩
  · intro h
    rw [collinear_iff_exists_forall_eq_smul_vadd] at h ⊢
    rcases h with ⟨p₀, d, hd⟩
    refine ⟨p₀ - v, d, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hp | hp | hp
    · rcases hd A (by simp) with ⟨r, hr⟩
      exact ⟨r, by rw [hp]; ext i; have hri := congrArg (fun Q : Plane => Q i) hr; simp [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply] at hri ⊢; linarith⟩
    · rcases hd B (by simp) with ⟨r, hr⟩
      exact ⟨r, by rw [hp]; ext i; have hri := congrArg (fun Q : Plane => Q i) hr; simp [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply] at hri ⊢; linarith⟩
    · rcases hd C (by simp) with ⟨r, hr⟩
      exact ⟨r, by rw [hp]; ext i; have hri := congrArg (fun Q : Plane => Q i) hr; simp [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply] at hri ⊢; linarith⟩

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
  by_cases hc : c = 0
  · have hab_sum : a + b = 0 := by linarith
    have ha_or_hb : a ≠ 0 ∨ b ≠ 0 := by
      rcases h_nontriv with ha | hb | hc'
      · exact Or.inl ha
      · exact Or.inr hb
      · exact False.elim (hc' hc)
    have hAB : A = B := by
      rcases ha_or_hb with ha | hb
      · ext i
        have hi := congrArg (fun P : Plane => P i) h_comb
        simp [hc, PiLp.add_apply, PiLp.smul_apply] at hi
        have hb_eq : b = -a := by linarith
        rw [hb_eq] at hi
        have hmul : a * (A i - B i) = 0 := by linarith
        exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left ha)
      · ext i
        have hi := congrArg (fun P : Plane => P i) h_comb
        simp [hc, PiLp.add_apply, PiLp.smul_apply] at hi
        have ha_eq : a = -b := by linarith
        rw [ha_eq] at hi
        have hmul : b * (B i - A i) = 0 := by linarith
        exact Eq.symm (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hb))
    simpa [hAB, Set.insert_eq_of_mem] using collinear_pair ℝ B C
  · rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨A, B - A, ?_⟩
    intro P hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rcases hP with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · refine ⟨-b / c, ?_⟩
      ext i
      have hi := congrArg (fun P : Plane => P i) h_comb
      simp [PiLp.add_apply, PiLp.smul_apply] at hi ⊢
      field_simp [hc]
      ring_nf at hi h_sum ⊢
      have haeq : a = -b - c := by linarith
      rw [haeq] at hi
      nlinarith

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
  rw [ collinear_iff_exists_forall_eq_smul_vadd ] at h ; aesop (config := {warnOnNonterminal := false});
  -- Since $w_3 • w_1 - w_4 • w_1$ and $w_2 • w_1 - w_4 • w_1$ are parallel, there exists a scalar $\alpha$ such that $w_3 • w_1 - w_4 • w_1 = \alpha • (w_2 • w_1 - w_4 • w_1)$.
  use (w_3 - w_4) / (w_2 - w_4);
  ext ; norm_num ; ring_nf;
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
  let Q : Plane := (β - α)⁻¹ • ((β * (1 - α)) • B - (α * (1 - β)) • A)
  have hQ₁ : Collinear ℝ ({A, B, Q} : Set Plane) := by
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    use A, B - A
    intro X hX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · refine ⟨(β - α)⁻¹ * (β * (1 - α)), ?_⟩
      ext i
      simp [Q, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply]
      field_simp [sub_ne_zero.mpr (Ne.symm hαβ)]
      ring
  have hQ₂ : Collinear ℝ ({A', B', Q} : Set Plane) := by
    rw [hA, hB]
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    use α • A, β • B - α • A
    intro X hX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · refine ⟨(β - α)⁻¹ * (1 - α), ?_⟩
      ext i
      simp [Q, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply]
      field_simp [sub_ne_zero.mpr (Ne.symm hαβ)]
      ring
  exact (h_unique.2 Q ⟨hQ₁, hQ₂⟩).symm

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
      aesop (config := {warnOnNonterminal := false});
      constructor <;> simp_all ( config := { decide := Bool.true } ) [ collinear_pair ];
    rcases eq_or_ne A' B' <;> simp_all +decide [ collinear_pair ];
    exact absurd ( h_contradiction ( P + EuclideanSpace.single 0 1 ) ) ( ne_of_apply_ne ( fun x => x 0 ) ( by norm_num ) );
  · cases h ; aesop (config := {warnOnNonterminal := false});
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
      exact exists_eq_left_add_smul_sub_of_collinear h.1.1 h_distinct.1
    obtain ⟨t, ht⟩ : ∃ t : ℝ, P = A' + t • (B' - A') := by
      exact exists_eq_left_add_smul_sub_of_collinear h.1.2 h_distinct.2
    intro t_1
    simp_all only [ne_eq]
    obtain ⟨left, right⟩ := h_distinct
    exact ⟨ s + ( t_1 - t ) * k, by
      ext i
      have hsi := congrArg (fun P : Plane => P i) hs
      have hti := congrArg (fun P : Plane => P i) ht
      have hpi := congrArg (fun P : Plane => P i) h_parallel
      simp [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply] at hsi hti hpi ⊢
      nlinarith ⟩;
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
    unfold IntersectsIn; aesop (config := {warnOnNonterminal := false});
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
  constructor
  · intro h
    refine ⟨⟨(collinear_sub_right_iff v A B P).mp h.1.1,
      (collinear_sub_right_iff v A' B' P).mp h.1.2⟩, ?_⟩
    intro Q hQ
    have hQ' : IntersectsIn (A - v) (B - v) (A' - v) (B' - v) (Q - v) :=
      ⟨(collinear_sub_right_iff v A B Q).mpr hQ.1,
        (collinear_sub_right_iff v A' B' Q).mpr hQ.2⟩
    have hsub := h.2 (Q - v) hQ'
    ext i
    have hi := congrArg (fun R : Plane => R i) hsub
    simp [PiLp.sub_apply] at hi
    linarith
  · intro h
    refine ⟨⟨(collinear_sub_right_iff v A B P).mpr h.1.1,
      (collinear_sub_right_iff v A' B' P).mpr h.1.2⟩, ?_⟩
    intro Q hQ
    have hQ' : IntersectsIn A B A' B' (Q + v) := by
      constructor
      · have hQleft : Collinear ℝ ({A - v, B - v, (Q + v) - v} : Set Plane) := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hQ.1
        exact (collinear_sub_right_iff v A B (Q + v)).mp hQleft
      · have hQright : Collinear ℝ ({A' - v, B' - v, (Q + v) - v} : Set Plane) := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hQ.2
        exact (collinear_sub_right_iff v A' B' (Q + v)).mp hQright
    have hmain := h.2 (Q + v) hQ'
    ext i
    have hi := congrArg (fun R : Plane => R i) hmain
    simp [PiLp.add_apply] at hi ⊢
    linarith

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
    exact (unique_intersection_translation_invariance O A B A' B' P).mpr h_unique
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
    unfold UniqueIntersection at *; aesop (config := {warnOnNonterminal := false});
    rw [ ← right C' ];
    unfold IntersectsIn; simp [hO_CC'];
    exact ⟨ by simpa only [ Set.insert_comm, Set.pair_comm ] using hO_CC', collinear_pair ℝ _ _ ⟩
  aesop (config := {warnOnNonterminal := false});
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
      convert desargues_intersection_formula_affine _ _ _ using 1 <;> aesop (config := {warnOnNonterminal := false})
    have hPca_expr : Pca - O = (α - γ)⁻¹ • ((α * (1 - γ)) • (A - O) - (γ * (1 - α)) • (C - O)) := by
      exact desargues_intersection_formula_affine ( by simpa using hγ.1 ) ( by simpa using hα ) ( by tauto ) ( by simpa [ UniqueIntersection ] using hPca ) ▸ by ring_nf;
    -- By the algebraic identity proven in `desargues_algebraic_identity`, the points `Pab - O`, `Pbc - O`, `Pca - O` are collinear.
    have h_collinear : Collinear ℝ ({Pab - O, Pbc - O, Pca - O} : Set Plane) := by
      rw [ hPab_expr, hPbc_expr, hPca_expr ];
      convert desargues_algebraic_identity ( A - O ) ( B - O ) ( C - O ) α β γ ( Ne.symm <| by tauto ) ( Ne.symm <| by tauto ) ( Ne.symm <| by tauto ) using 1;
    rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
    obtain ⟨ p₀, v, hv ⟩ := h_collinear;
    use p₀ + O, v;
    simp +zetaDelta at *;
    exact ⟨ by obtain ⟨ r, hr ⟩ := hv.1; exact ⟨ r, by ext i; have := congrArg (fun P : Plane => P i) hr; norm_num at *; linarith ⟩, by obtain ⟨ r, hr ⟩ := hv.2.1; exact ⟨ r, by ext i; have := congrArg (fun P : Plane => P i) hr; norm_num at *; linarith ⟩, by obtain ⟨ r, hr ⟩ := hv.2.2; exact ⟨ r, by ext i; have := congrArg (fun P : Plane => P i) hr; norm_num at *; linarith ⟩ ⟩;
  · have hPbcB' : Pbc = B' := by
      have hB'_intersection : IntersectsIn B C B' C' B' := by
        unfold IntersectsIn; aesop (config := {warnOnNonterminal := false});
        · rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
          exact ⟨ hO_BB'.choose, hO_BB'.choose_spec.choose, fun p hp => by simpa using hO_BB'.choose_spec.choose_spec p <| by aesop ⟩;
        · exact collinear_pair _ _ _;
      exact hPbc.2 B' hB'_intersection ▸ rfl
    have hPcaA' : Pca = A' := by
      have hPcaA' : IntersectsIn C A C' A' A' := by
        constructor <;> simp_all +decide [ collinear_pair ];
        rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
        obtain ⟨ p₀, v, hp₀ ⟩ := hO_AA'; use p₀, v; intro p hp; specialize hp₀ p; aesop (config := {warnOnNonterminal := false});
      exact hPca.2 A' hPcaA' ▸ rfl
    aesop (config := {warnOnNonterminal := false});
    have := hPab.1.1; have := hPab.1.2; simp_all +decide [ collinear_pair ] ;
    rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
    exact ⟨ this.choose, this.choose_spec.choose, fun p hp => this.choose_spec.choose_spec p ( by aesop ) ⟩;
  · have hPabA' : Pab = A' := by
      have := hPab.2 A' ?_ <;> aesop (config := {warnOnNonterminal := false}) (simp_config := { singlePass := true } );
      unfold IntersectsIn; aesop (config := {warnOnNonterminal := false});
      · rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
        obtain ⟨ p₀, v, hv ⟩ := hO_AA'; use p₀, v; intro p hp; specialize hv p; aesop (config := {warnOnNonterminal := false});
      · exact collinear_pair _ _ _
    have hPbcC' : Pbc = C' := by
      -- Since $C' = B$, the line $BC$ passes through $B$ and $C$, and the line $B'C'$ passes through $B'$ and $C'$. Thus, $C'$ is an intersection of $BC$ and $B'C'$.
      have hC'_intersection : Collinear ℝ ({B, C, C'} : Set Plane) ∧ Collinear ℝ ({B', C', C'} : Set Plane) := by
        simp_all +decide [ collinear_pair ];
        rw [ collinear_iff_exists_forall_eq_smul_vadd ] at *;
        exact ⟨ hO_CC'.choose, hO_CC'.choose_spec.choose, fun p hp => by obtain ⟨ r, hr ⟩ := hO_CC'.choose_spec.choose_spec p ( by aesop ) ; exact ⟨ r, hr ⟩ ⟩;
      exact hPbc.2 C' hC'_intersection ▸ rfl
    aesop (config := {warnOnNonterminal := false});
    have := hPca.1.2; simp_all +decide [ collinear_iff_exists_forall_eq_smul_vadd ] ;
    exact ⟨ this.choose, this.choose_spec.choose, this.choose_spec.choose_spec.2.1, this.choose_spec.choose_spec.1, this.choose_spec.choose_spec.2.2 ⟩;
  · convert desargues_plane_A_eq_O ( Classical.not_not.mp hAO ) hO_BB' hO_CC' hPab hPbc hPca using 1

#print axioms desargues_plane
-- 'Theorem87.desargues_plane' depends on axioms: [propext, Classical.choice, Quot.sound]

end Theorem87
