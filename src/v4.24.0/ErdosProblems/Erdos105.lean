/-

The original human proof was found by Wu Xichuan and posted at
https://www.erdosproblems.com/forum/thread/105#post-1430

The configuration included points at infinity, so a projective transformation
was applied that brought all points into the finite (affine) plane, with
integer coordinates for extra convenience.

ChatGPT Pro (Thinking) from OpenAI generated the lemma statements.

Aristotle from Harmonic generated the proofs.

The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/

import Mathlib

/-- The ambient plane. -/
abbrev R2 : Type := EuclideanSpace ℝ (Fin 2)

/-- The affine line through two points `p q` as an `AffineSubspace`. -/
@[simp] noncomputable def lineThrough (p q : R2) : AffineSubspace ℝ R2 :=
  affineSpan ℝ ({p, q} : Set R2)

/-- Predicate: an affine subspace of `R2` is (an affine) line. -/
def IsLine (ℓ : AffineSubspace ℝ R2) : Prop :=
  ∃ p q : R2, p ≠ q ∧ ℓ = lineThrough p q

/-- Map an integer pair to a point in `R2`. -/
def toR2 (p : ℤ × ℤ) : R2 := ![(p.1 : ℝ), (p.2 : ℝ)]

lemma toR2_injective : Function.Injective toR2 := by
  -- To prove injectivity, assume toR2 (a, b) = toR2 (c, d). This means the points (a, b) and (c, d) are equal in R2.
  intro p q h_eq
  simp [toR2] at h_eq
  aesop;
  · simpa using congr_fun h_eq 0;
  · -- Since the vectors are equal, their second components must be equal.
    have h_snd : (snd : ℝ) = snd_1 := by
      -- Since the vectors are equal, their corresponding components must be equal. Therefore, snd must equal snd_1.
      apply congr_fun h_eq 1;
    exact_mod_cast h_snd

/-- The 12-point set as integer pairs. -/
def Aℤ : Finset (ℤ × ℤ) :=
  ({ (0,    6930), (0,    7920), (13860, 0),    (5544, 5544),
     (3465, 6930), (2520, 7560), (18480, 0),    (9240, 4620),
     (6160, 6160), (4620, 6930), (11880, 3960), (8316, 5544) } :
    Finset (ℤ × ℤ))

/-- The 9-point set as integer pairs. -/
def Bℤ : Finset (ℤ × ℤ) :=
  ({ (0,    9240), (-13860, 13860), (27720, 0),   (6930, 6930),
     (3960, 7920), (-55440, 27720), (11088, 5544), (5940, 5940),
     (-5544, 11088) } :
    Finset (ℤ × ℤ))

/-- The corresponding `R2` finsets (`A0`, `B0`). -/
noncomputable def A0 : Finset R2 := Aℤ.image toR2

noncomputable def B0 : Finset R2 := Bℤ.image toR2

lemma disjoint_A0_B0 : Disjoint A0 B0 := by
  rw [ Finset.disjoint_left ];
  -- Since toR2 is injective, if a point is in both A0 and B0, then there must be a point in Aℤ that maps to it and a point in Bℤ that maps to it. But since toR2 is injective, these two points must be the same, which contradicts the fact that Aℤ and Bℤ are disjoint.
  have h_inj : Function.Injective toR2 := by
    -- To prove injectivity, we show that if toR2 p = toR2 q, then p = q.
    intro p q hpq
    simp [toR2] at hpq
    aesop;
    · -- Since the vectors are equal, their corresponding components must be equal. Therefore, we have fst = fst_1.
      have h_comp : fst = fst_1 := by
        have := congr_fun hpq 0
        simp at this
        exact_mod_cast this;
      -- Since the vectors are equal, their corresponding components must be equal. Therefore, we have fst = fst_1 by h_comp.
      exact h_comp;
    · simpa using congr_fun hpq 1;
  -- Since toR2 is injective, if a point is in both A0 and B0, then there must be a point in Aℤ that maps to it and a point in Bℤ that maps to it. But since Aℤ and Bℤ are disjoint, this can't happen.
  intros a ha hb
  obtain ⟨p, hpA, hp⟩ := Finset.mem_image.mp ha
  obtain ⟨q, hqB, hq⟩ := Finset.mem_image.mp hb
  have h_eq : p = q := by
    exact h_inj <| hp.trans hq.symm;
  subst h_eq;
  exact absurd hqB ( by rw [ show Bℤ = { ( 0, 9240 ), ( -13860, 13860 ), ( 27720, 0 ), ( 6930, 6930 ), ( 3960, 7920 ), ( -55440, 27720 ), ( 11088, 5544 ), ( 5940, 5940 ), ( -5544, 11088 ) } by rfl ] ; fin_cases hpA <;> trivial )

lemma A0_card : A0.card = 12 := by
  -- Since toR2 is injective, the cardinality of the image A0 is equal to the cardinality of Aℤ.
  apply Finset.card_image_of_injective;
  -- To prove injectivity, we show that if `toR2 a = toR2 b`, then `a = b`.
  intro a b hab
  simp [toR2] at hab;
  exact Prod.ext ( by simpa using congr_fun hab 0 ) ( by simpa using congr_fun hab 1 )

lemma B0_card : B0.card = 9 := by
  -- Since toR2 is injective, the cardinality of B0 is equal to the cardinality of Bℤ by the lemma `Finset.card_image_of_injective`.
  apply Finset.card_image_of_injective; exact toR2_injective

/-- The 12-point set `A0` is not contained in a line. -/
lemma A0_not_on_a_line :
  ¬ ∃ ℓ : AffineSubspace ℝ R2, IsLine ℓ ∧ (A0 : Set R2) ⊆ (ℓ : Set R2) := by
  -- Assume for contradiction that there exists a line ℓ such that A0 is a subset of ℓ.
  by_contra h_contra
  obtain ⟨ℓ, hℓ_line, hℓ_subset⟩ := h_contra;
  obtain ⟨ p, q, hpq, rfl ⟩ := hℓ_line;
  -- Since $A0$ is a subset of the line through $p$ and $q$, all points in $A0$ must satisfy the equation of the line.
  have h_eq : ∀ x ∈ Aℤ, ∃ t : ℝ, toR2 x = p + t • (q - p) := by
    intro x hx; specialize hℓ_subset ( Finset.mem_image_of_mem _ hx ) ; unfold lineThrough at hℓ_subset; aesop;
    rw [ spanPoints ] at hℓ_subset;
    norm_num [ vectorSpan_pair ] at hℓ_subset;
    rcases hℓ_subset with ( ⟨ v, hv, hv' ⟩ | ⟨ v, hv, hv' ⟩ ) <;> rw [ Submodule.mem_span_singleton ] at hv <;> aesop;
    · exact ⟨ -w, by ext ; norm_num ; ring ⟩;
    · exact ⟨ 1 - w, by ext i; have := congr_fun hv' i; norm_num at *; linarith ⟩;
  -- Let's choose any three points from $A0$ that are not collinear.
  obtain ⟨ x1, x2, x3, hx1, hx2, hx3, hx_not_collinear ⟩ : ∃ x1 x2 x3 : ℤ × ℤ, x1 ∈ Aℤ ∧ x2 ∈ Aℤ ∧ x3 ∈ Aℤ ∧ ¬(Collinear ℝ ({toR2 x1, toR2 x2, toR2 x3} : Set R2)) := by
    use (0, 6930), (0, 7920), (13860, 0);
    simp +decide [ collinear_pair ];
    norm_num [ collinear_iff_exists_forall_eq_smul_vadd ];
    intros x y a ha b hb c hc; have := congr_fun ha 0; have := congr_fun hb 0; have := congr_fun hc 0; have := congr_fun ha 1; have := congr_fun hb 1; have := congr_fun hc 1; norm_num [ toR2 ] at * ; nlinarith;
  obtain ⟨ t1, ht1 ⟩ := h_eq x1 hx1
  obtain ⟨ t2, ht2 ⟩ := h_eq x2 hx2
  obtain ⟨ t3, ht3 ⟩ := h_eq x3 hx3;
  refine' hx_not_collinear _;
  rw [ collinear_iff_exists_forall_eq_smul_vadd ] ; use p ; aesop;
  exact ⟨ q - p, ⟨ t1, by abel1 ⟩, ⟨ t2, by abel1 ⟩, ⟨ t3, by abel1 ⟩ ⟩

lemma neg_last_condition_sets :
    ∀ (p q : R2),
      p ∈ A0 → q ∈ A0 → p ≠ q →
      ∃ b ∈ B0, b ∈ (lineThrough p q : Set R2) := by
  -- By definition of $A0$ and $B0$, for any $p, q \in A0$, there exist integer pairs $(a, b)$ and $(c, d)$ in $Aℤ$ such that $p = toR2 (a, b)$ and $q = toR2 (c, d)$. Similarly, for any $b \in B0$, there exists an integer pair $(e, f)$ in $Bℤ$ such that $b = toR2 (e, f)$.
  intro p q hp hq hpq
  obtain ⟨a, b, ha, hb⟩ : ∃ a b : ℤ, (a, b) ∈ Aℤ ∧ p = toR2 (a, b) := by
    unfold A0 at hp; aesop;
  obtain ⟨c, d, hc, hd⟩ : ∃ c d : ℤ, (c, d) ∈ Aℤ ∧ q = toR2 (c, d) := by
    unfold A0 at hq; aesop;
  obtain ⟨e, f, he, hf⟩ : ∃ e f : ℤ, (e, f) ∈ Bℤ ∧ toR2 (e, f) ∈ lineThrough (toR2 (a, b)) (toR2 (c, d)) := by
    -- By definition of $Bℤ$, we can check each point in $Bℤ$ to see if it lies on the line defined by $(a, b)$ and $(c, d)$.
    have h_check : ∃ e f : ℤ, (e, f) ∈ Bℤ ∧ (f - b) * (c - a) = (e - a) * (d - b) := by
      -- By checking each pair of points in Aℤ, we can verify that there exists a point in Bℤ that lies on the line defined by them.
      have h_check : ∀ p ∈ Aℤ, ∀ q ∈ Aℤ, p ≠ q → ∃ r ∈ Bℤ, (r.2 - p.2) * (q.1 - p.1) = (r.1 - p.1) * (q.2 - p.2) := by
        native_decide +revert;
      aesop;
    -- By definition of $lineThrough$, if $(f - b) * (c - a) = (e - a) * (d - b)$, then $(e, f)$ lies on the line through $(a, b)$ and $(c, d)$.
    obtain ⟨e, f, he, hf⟩ := h_check;
    use e, f;
    aesop;
    -- By definition of affine span, we need to show that there exists a scalar $t$ such that $(e, f) = (a, b) + t \cdot ((c, d) - (a, b))$.
    obtain ⟨t, ht⟩ : ∃ t : ℝ, (e : ℝ) = a + t * (c - a) ∧ (f : ℝ) = b + t * (d - b) := by
      by_cases hac : ( c : ℝ ) - a = 0 <;> by_cases hbd : ( d : ℝ ) - b = 0 <;> simp_all +decide [ sub_eq_iff_eq_add ];
      · exact ⟨ ( f - b ) / ( d - b ), by rw [ div_mul_cancel₀ _ ( sub_ne_zero_of_ne <| by aesop ) ] ; ring ⟩;
      · exact ⟨ ( e - a ) / ( c - a ), by rw [ div_mul_cancel₀ _ ( sub_ne_zero_of_ne <| mod_cast hac ) ] ; ring ⟩;
      ·
        -- By dividing both sides of the equation $(e - a) * (d - b) = (f - b) * (c - a)$ by $(c - a) * (d - b)$, we can solve for $t$.
        use (e - a) / (c - a);
        -- By dividing both sides of the equation $(f - b) * (c - a) = (e - a) * (d - b)$ by $(c - a) * (d - b)$, we can solve for $t$ and show that it satisfies both equations.
        field_simp [hac, hbd];
        -- By combining terms, we can factor out $(c - a)$ and simplify the expression.
        have h_simp : (f - b : ℝ) * (c - a) = (e - a) * (d - b) := by
          exact mod_cast hf;
        exact ⟨ by rw [ mul_div_cancel_right₀ _ ( sub_ne_zero_of_ne <| mod_cast hac ) ] ; ring, by rw [ ← h_simp, mul_div_cancel_right₀ _ ( sub_ne_zero_of_ne <| mod_cast hac ) ] ; ring ⟩
    -- By definition of affine span, if $(e, f)$ can be written as $(a, b) + t \cdot ((c, d) - (a, b))$, then it lies in the affine span of $\{(a, b), (c, d)\}$.
    have h_affine_span : ∀ (p q : R2), ∀ (t : ℝ), p + t • (q - p) ∈ affineSpan ℝ {p, q} := by
      intro p q t; rw [ affineSpan ] ; simp +decide [ Set.mem_setOf_eq, AffineSubspace.mem_mk', smul_sub ] ;
      simp +decide [ spanPoints ];
      -- Since $t • (q - p)$ is in the vector span of $\{p, q\}$, we can write $p + t • (q - p)$ as $t • (q - p) + p$, which is of the form $v + p$ where $v = t • (q - p)$.
      left
      use t • (q - p)
      simp [vectorSpan];
      exact ⟨ Submodule.smul_mem _ _ <| Submodule.subset_span <| by simp +decide [ Set.mem_vsub ], by ext; simp +decide ; ring ⟩;
    convert h_affine_span ( toR2 ( a, b ) ) ( toR2 ( c, d ) ) t using 1 ; ext i ; fin_cases i <;> aesop;
  -- Since $e$ and $f$ are in $Bℤ$, $toR2 (e, f)$ is in $B0$.
  use toR2 (e, f)
  aesop;
  exact Finset.mem_image_of_mem _ he

/--
**Erdős–Purdy (Erdős Problem 105).**

Given finite point sets `A, B ⊆ R2` and a natural number `n`, if:
* `A` and `B` are disjoint,
* `|A| = n` and `|B| = n - 3`,
* `A` is not contained in any affine line,

then there exist two distinct points `p, q ∈ A` such that the line through them
avoids all points of `B`.
-/
def erdos_105 : Prop :=
  ∀ (A B : Finset R2) (n : ℕ),
  Disjoint A B →
  A.card = n →
  B.card = n - 3 →
  (¬ ∃ ℓ : AffineSubspace ℝ R2, IsLine ℓ ∧ (A : Set R2) ⊆ (ℓ : Set R2)) →
  ∃ (p q : R2),
    p ∈ A ∧ q ∈ A ∧ p ≠ q ∧
    (∀ b ∈ B, b ∉ (lineThrough p q : Set R2))

theorem not_erdos_105 : ¬erdos_105 := by
  -- By definition of `erdos_105`, if `erdos_105` holds, then for any sets `A` and `B` satisfying the conditions, there exist two distinct points `p` and `q` in `A` such that the line through them avoids all points of `B`.
  by_contra h_contra;
  -- Apply the Erdős problem 105 to the sets A0 and B0 with n=12.
  have h_apply : ∃ p q : R2, p ∈ A0 ∧ q ∈ A0 ∧ p ≠ q ∧ (∀ b ∈ B0, b ∉ (lineThrough p q : Set R2)) := by
    -- Apply the Erdős problem 105 to the sets A0 and B0 with n=12, which satisfy the conditions.
    apply h_contra A0 B0 12 disjoint_A0_B0 A0_card B0_card A0_not_on_a_line;
  -- Apply the neg_last_condition_sets hypothesis to the points p and q from h_apply.
  obtain ⟨p, q, hpA, hqA, hpq, hline⟩ := h_apply;
  obtain ⟨b, hbB, hbline⟩ := neg_last_condition_sets p q hpA hqA hpq;
  aesop
