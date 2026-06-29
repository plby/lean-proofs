/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 105.
https://www.erdosproblems.com/forum/thread/105

Informal authors:
- Wu Xichuan

Formal authors:
- ChatGPT Pro (Thinking)
- Aristotle
- Boris Alexeev

URLs:
- https://www.erdosproblems.com/forum/thread/105#post-1430
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos105.md
-/
import Mathlib

namespace Erdos105

/-- The ambient plane. -/
abbrev R2 : Type := EuclideanSpace ℝ (Fin 2)

/-- The affine line through two points `p q` as an `AffineSubspace`. -/
@[simp] noncomputable def lineThrough (p q : R2) : AffineSubspace ℝ R2 :=
  affineSpan ℝ ({p, q} : Set R2)

/-- Predicate: an affine subspace of `R2` is (an affine) line. -/
def IsLine (ℓ : AffineSubspace ℝ R2) : Prop :=
  ∃ p q : R2, p ≠ q ∧ ℓ = lineThrough p q

/-- Map an integer pair to a point in `R2`. -/
def toR2 (p : ℤ × ℤ) : R2 := WithLp.toLp 2 ![(p.1 : ℝ), (p.2 : ℝ)]

lemma toR2_injective : Function.Injective toR2 := by
  intro p q h_eq
  apply Prod.ext
  · have h0 := congr_arg (fun x : R2 => x 0) h_eq
    have h0 : (p.1 : ℝ) = q.1 := by
      simpa [toR2] using h0
    exact_mod_cast h0
  · have h1 := congr_arg (fun x : R2 => x 1) h_eq
    have h1 : (p.2 : ℝ) = q.2 := by
      simpa [toR2] using h1
    exact_mod_cast h1

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
  rw [Finset.disjoint_left]
  -- Use injectivity to move membership in the images back to the integer sets.
  have h_inj : Function.Injective toR2 := by
    exact toR2_injective
  -- The two integer preimages must coincide, contradicting the enumerated disjointness.
  intros a ha hb
  obtain ⟨p, hpA, hp⟩ := Finset.mem_image.mp ha
  obtain ⟨q, hqB, hq⟩ := Finset.mem_image.mp hb
  have h_eq : p = q := by
    exact h_inj <| hp.trans hq.symm
  subst h_eq
  exact absurd hqB (by
    rw [show Bℤ =
      { ( 0, 9240 ), ( -13860, 13860 ), ( 27720, 0 ), ( 6930, 6930 ),
        ( 3960, 7920 ), ( -55440, 27720 ), ( 11088, 5544 ), ( 5940, 5940 ),
        ( -5544, 11088 ) } by rfl]
    fin_cases hpA
    all_goals trivial)

lemma A0_card : A0.card = 12 := by
  -- Since toR2 is injective, the cardinality of the image A0 is equal to the cardinality of Aℤ.
  apply Finset.card_image_of_injective
  -- To prove injectivity, we show that if `toR2 a = toR2 b`, then `a = b`.
  exact toR2_injective

lemma B0_card : B0.card = 9 := by
  -- Since `toR2` is injective, image cardinality is preserved.
  apply Finset.card_image_of_injective
  exact toR2_injective

/-- The 12-point set `A0` is not contained in a line. -/
lemma A0_not_on_a_line :
  ¬ ∃ ℓ : AffineSubspace ℝ R2, IsLine ℓ ∧ (A0 : Set R2) ⊆ (ℓ : Set R2) := by
  -- Assume for contradiction that there exists a line ℓ such that A0 is a subset of ℓ.
  by_contra h_contra
  obtain ⟨ℓ, hℓ_line, hℓ_subset⟩ := h_contra
  obtain ⟨ p, q, hpq, rfl ⟩ := hℓ_line
  -- All points in `A0` satisfy the equation of the line.
  have h_eq : ∀ x ∈ Aℤ, ∃ t : ℝ, toR2 x = p + t • (q - p) := by
    intro x hx
    specialize hℓ_subset ( Finset.mem_image_of_mem _ hx )
    unfold lineThrough at hℓ_subset
    rw [ coe_affineSpan ] at hℓ_subset
    rw [ spanPoints ] at hℓ_subset
    norm_num [ vectorSpan_pair ] at hℓ_subset
    rcases hℓ_subset with (⟨v, hv, hv'⟩ | ⟨v, hv, hv'⟩)
    · rw [Submodule.mem_span_singleton] at hv
      obtain ⟨w, hv⟩ := hv
      rw [← hv] at hv'
      exact
        ⟨-w, by
          rw [hv']
          ext
          norm_num
          ring⟩
    · rw [Submodule.mem_span_singleton] at hv
      obtain ⟨w, hv⟩ := hv
      rw [← hv] at hv'
      exact
        ⟨1 - w, by
          ext i
          have := congr_arg (fun x : R2 => x i) hv'
          norm_num at *
          linarith⟩
  -- Let's choose any three points from $A0$ that are not collinear.
  obtain ⟨ x1, x2, x3, hx1, hx2, hx3, hx_not_collinear ⟩ :
      ∃ x1 x2 x3 : ℤ × ℤ,
        x1 ∈ Aℤ ∧ x2 ∈ Aℤ ∧ x3 ∈ Aℤ ∧
          ¬(Collinear ℝ ({toR2 x1, toR2 x2, toR2 x3} : Set R2)) := by
    use (0, 6930), (0, 7920), (13860, 0)
    simp +decide only [true_and]
    norm_num [ collinear_iff_exists_forall_eq_smul_vadd ]
    intros x y a ha b hb c hc
    have := congr_arg (fun z : R2 => z 0) ha
    have := congr_arg (fun z : R2 => z 0) hb
    have := congr_arg (fun z : R2 => z 0) hc
    have := congr_arg (fun z : R2 => z 1) ha
    have := congr_arg (fun z : R2 => z 1) hb
    have := congr_arg (fun z : R2 => z 1) hc
    norm_num [ toR2 ] at *
    nlinarith
  obtain ⟨ t1, ht1 ⟩ := h_eq x1 hx1
  obtain ⟨ t2, ht2 ⟩ := h_eq x2 hx2
  obtain ⟨ t3, ht3 ⟩ := h_eq x3 hx3
  refine hx_not_collinear ?_
  rw [ collinear_iff_exists_forall_eq_smul_vadd ]
  use p
  use q - p
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl
  · exact ⟨t1, by simpa [vadd_eq_add, add_comm] using ht1⟩
  · exact ⟨t2, by simpa [vadd_eq_add, add_comm] using ht2⟩
  · exact ⟨t3, by simpa [vadd_eq_add, add_comm] using ht3⟩

lemma neg_last_condition_sets :
    ∀ (p q : R2),
      p ∈ A0 → q ∈ A0 → p ≠ q →
  ∃ b ∈ B0, b ∈ (lineThrough p q : Set R2) := by
  -- Pass from the real points back to their integer coordinates.
  intro p q hp hq hpq
  obtain ⟨a, b, ha, hb⟩ : ∃ a b : ℤ, (a, b) ∈ Aℤ ∧ p = toR2 (a, b) := by
    obtain ⟨r, hrA, hrp⟩ := Finset.mem_image.mp hp
    refine ⟨r.1, r.2, ?_, ?_⟩
    · simpa using hrA
    · simpa [Prod.eta] using hrp.symm
  obtain ⟨c, d, hc, hd⟩ : ∃ c d : ℤ, (c, d) ∈ Aℤ ∧ q = toR2 (c, d) := by
    obtain ⟨r, hrA, hrq⟩ := Finset.mem_image.mp hq
    refine ⟨r.1, r.2, ?_, ?_⟩
    · simpa using hrA
    · simpa [Prod.eta] using hrq.symm
  obtain ⟨e, f, he, hf⟩ :
      ∃ e f : ℤ,
        (e, f) ∈ Bℤ ∧ toR2 (e, f) ∈ lineThrough (toR2 (a, b)) (toR2 (c, d)) := by
    -- Check the finite set `Bℤ` directly.
    have h_check : ∃ e f : ℤ, (e, f) ∈ Bℤ ∧ (f - b) * (c - a) = (e - a) * (d - b) := by
      -- Check each pair of points in `Aℤ`.
      have h_check :
          ∀ p ∈ Aℤ, ∀ q ∈ Aℤ, p ≠ q →
            ∃ r ∈ Bℤ, (r.2 - p.2) * (q.1 - p.1) = (r.1 - p.1) * (q.2 - p.2) := by
        decide
      have habcd : (a, b) ≠ (c, d) := by
        intro h
        apply hpq
        rw [hb, hd, h]
      obtain ⟨r, hrB, hr⟩ := h_check (a, b) ha (c, d) hc habcd
      exact ⟨r.1, r.2, by simpa using hrB, by simpa using hr⟩
    -- Translate the determinant equation into membership in the affine span.
    obtain ⟨e, f, he, hf⟩ := h_check
    use e, f
    constructor
    · exact he
    obtain ⟨t, ht⟩ :
        ∃ t : ℝ, (e : ℝ) = a + t * (c - a) ∧ (f : ℝ) = b + t * (d - b) := by
      by_cases hac : ( c : ℝ ) - a = 0
      · by_cases hbd : ( d : ℝ ) - b = 0
        · simp_all +decide only [ne_eq, sub_eq_iff_eq_add, zero_add, Int.cast_inj, sub_self,
            mul_zero, add_zero, exists_const]
        · simp_all +decide only [ne_eq, sub_eq_iff_eq_add, zero_add, Int.cast_inj, sub_self,
            mul_zero, add_zero, exists_and_left, zero_eq_mul, or_false, true_and]
          have hbd' : (d : ℝ) - b ≠ 0 := sub_ne_zero_of_ne (by exact_mod_cast hbd)
          exact
            ⟨( f - b ) / ( d - b ),
              by
                rw [div_mul_cancel₀ _ hbd']
                ring⟩
      · by_cases hbd : ( d : ℝ ) - b = 0
        · simp_all +decide only [ne_eq, sub_eq_iff_eq_add, zero_add, Int.cast_inj, sub_self,
            mul_zero, add_zero, or_false, exists_and_right, mul_eq_zero, and_true]
          have hac' : (c : ℝ) - a ≠ 0 := sub_ne_zero_of_ne (by exact_mod_cast hac)
          exact
            ⟨( e - a ) / ( c - a ),
              by
                rw [div_mul_cancel₀ _ hac']
                ring⟩
        · simp_all +decide only [ne_eq, sub_eq_iff_eq_add, zero_add, Int.cast_inj]
          have hac' : (c : ℝ) - a ≠ 0 := sub_ne_zero_of_ne (by exact_mod_cast hac)
          have hbd' : (d : ℝ) - b ≠ 0 := sub_ne_zero_of_ne (by exact_mod_cast hbd)
          -- Divide the determinant equation to solve for `t`.
          use (e - a) / (c - a)
          field_simp [hac', hbd']
          -- By combining terms, we can factor out $(c - a)$ and simplify the expression.
          have h_simp : (f - b : ℝ) * (c - a) = (e - a) * (d - b) := by
            exact mod_cast hf
          refine ⟨?_, ?_⟩
          · ring
          · rw [← h_simp]
            ring
    -- Convert the parametric representation into affine-span membership.
    have h_affine_span : ∀ (p q : R2), ∀ (t : ℝ), p + t • (q - p) ∈ affineSpan ℝ {p, q} := by
      intro p q t
      rw [ affineSpan ]
      simp +decide only [smul_sub]
      simp +decide only [spanPoints, Set.mem_insert_iff, Set.mem_singleton_iff, vadd_eq_add,
        exists_eq_or_imp, ↓existsAndEq, true_and]
      -- Write the point as `v + p` with `v` in the vector span.
      left
      use t • (q - p)
      simp only [vectorSpan]
      exact
        ⟨Submodule.smul_mem _ _ <| Submodule.subset_span <| by
            simp +decide [ Set.mem_vsub ],
          by
            ext
            simp +decide
            ring⟩
    have hpoint :
        toR2 (e, f) = toR2 (a, b) + t • (toR2 (c, d) - toR2 (a, b)) := by
      ext i
      fin_cases i
      · simpa [toR2] using ht.1
      · simpa [toR2] using ht.2
    simpa [lineThrough, hpoint] using
      h_affine_span (toR2 (a, b)) (toR2 (c, d)) t
  -- Since $e$ and $f$ are in $Bℤ$, $toR2 (e, f)$ is in $B0$.
  use toR2 (e, f)
  constructor
  · exact Finset.mem_image_of_mem _ he
  · rw [hb, hd]
    exact hf

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
  -- Apply the statement to the counterexample sets.
  by_contra h_contra
  -- Apply the Erdős problem 105 to the sets A0 and B0 with n=12.
  have h_apply :
      ∃ p q : R2,
        p ∈ A0 ∧ q ∈ A0 ∧ p ≠ q ∧
          (∀ b ∈ B0, b ∉ (lineThrough p q : Set R2)) := by
    -- Apply the Erdős problem 105 to the sets A0 and B0 with n=12, which satisfy the conditions.
    apply h_contra A0 B0 12 disjoint_A0_B0 A0_card B0_card A0_not_on_a_line
  -- Apply the neg_last_condition_sets hypothesis to the points p and q from h_apply.
  obtain ⟨p, q, hpA, hqA, hpq, hline⟩ := h_apply
  obtain ⟨b, hbB, hbline⟩ := neg_last_condition_sets p q hpA hqA hpq
  exact hline b hbB hbline

#print axioms not_erdos_105
-- 'Erdos105.not_erdos_105' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos105
