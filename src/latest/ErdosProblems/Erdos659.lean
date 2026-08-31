/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 659.
https://www.erdosproblems.com/forum/thread/659

Formalization status:
- Unconditional

Informal authors:
- Benjamin Grayzel
- Adam Sheffer
- Pieter Moree
- Robert Osburn
- Desmond Weisenberg
- Gemini

Statement authors:
- Formal Conjectures authors

Formal authors:
- Aristotle
- Boris Alexeev
- Codex (unconditional Bernays proof and integration)

URLs:
- https://adamsheffer.wordpress.com/2014/07/16/point-sets-with-few-distinct-distances/
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos659.md
-/
/-
We formalized the solution to the Erdős problem concerning distances and points.
We defined the lattice `L` and the point sets `P_m`.
We proved that `P_m` satisfies the local constraint (every 4 points determine at least 3 distances)
by reducing it to the absence of squares, equilateral triangles, and golden ratio distances in `L`,
which we verified.
We proved that the number of distinct distances in `P_m` is bounded by `B_Q(3m^2)`, where `Q` is the
quadratic form `x^2 + 2y^2`.
Using the proved Bernays theorem, we established the asymptotic bound `O(n /
sqrt(log n))` for the number of distinct distances in a subset of size `n`.
--
I have proved Perucca's classification theorem (`PeruccaClassificationStatement_proof`) using some
helper lemmas I established.
-/

import ErdosProblems.Erdos659.Geometry
import ErdosProblems.Axioms

open Filter Asymptotics EuclideanGeometry Finset Real
open scoped Real

namespace Erdos659

/-
Define the quadratic form Q(u,v) = u^2 + 2v^2 and prove it is primitive and positive definite with
discriminant -8.
-/
def Q_form : BinQuadForm := ⟨1, 0, 2⟩

lemma Q_form_primitive : Q_form.Primitive := by
  unfold BinQuadForm.Primitive Q_form
  decide

lemma Q_form_posDef : Q_form.PosDef := by
  unfold BinQuadForm.PosDef BinQuadForm.discr Q_form
  decide

lemma Q_form_discr : Q_form.discr = -8 := by
  unfold BinQuadForm.discr Q_form
  rfl

/-
The number of distinct Euclidean distances in P_m is bounded by B_Q(3m^2).
-/
theorem distinctDistances'_euc_bound (m : ℕ) (_hm : m ≥ 1) :
    (distinctDistances'_euc (P m)).card ≤ BinQuadForm.B Q_form (3 * m ^ 2) := by
      -- The number of distinct squared distances in P_m is at most the number of integers ≤ 3m^2
      -- represented by the quadratic form Q(u,v) = u^2 + 2v^2.
      have h_card_dist_sq : (distinctDistances'_euc (P m)).card ≤
          (Nat.card {n : ℕ | (n : ℝ) ≤ 3 * m ^ 2 ∧
            ∃ u v : ℤ, (Q_form.eval u v : ℤ) = n}) := by
        -- By definition of $distinctDistances'_euc$, every element in $distinctDistances'_euc (P
        -- m)$ is a square root of an integer in the set $\{n \mid (n : ℝ) \leq 3 *
        -- m ^ 2 ∧ \exists
        -- u v : ℤ, (Q_form.eval u v : ℤ) = n\}$.
        have h_subset : ∀ d ∈ distinctDistances'_euc (P m),
          ∃ n ∈ {n : ℕ | (n : ℝ) ≤ 3 * m ^ 2 ∧
            ∃ u v : ℤ, (Q_form.eval u v : ℤ) = n},
          d = Real.sqrt n := by
          intro d hd
          obtain ⟨p, q, hp, hq, hd_eq⟩ : ∃ p q : ℝ × ℝ,
            p ∈ P m ∧ q ∈ P m ∧ dist_euc p q = d := by
            unfold distinctDistances'_euc at hd;
            simp +zetaDelta at *;
            tauto;
          obtain ⟨ u, v, hu, hv, h ⟩ := P_dist_sq_form m p q hp hq;
          use Int.natAbs (u^2 + 2 * v^2);
          field_simp;
          constructor;
          · constructor;
            · norm_cast;
              nlinarith only [ abs_lt.mp hu, abs_lt.mp hv,
                abs_of_nonneg ( by positivity : 0 ≤ u ^ 2 + 2 * v ^ 2 ) ];
            · use u, v;
              unfold Q_form
              norm_num [ abs_of_nonneg ( by positivity : 0 ≤ u ^ 2 + 2 * v ^ 2 ) ] ;
              unfold BinQuadForm.eval; norm_num; ring;
          · norm_num [ ← hd_eq, ← h ];
            rw [ Real.sqrt_sq ( by exact Real.sqrt_nonneg _ ) ];
        have h_finite : Set.Finite {n : ℕ | (n : ℝ) ≤ 3 * m ^ 2 ∧
            ∃ u v : ℤ, (Q_form.eval u v : ℤ) = n} := by
          exact Set.finite_iff_bddAbove.mpr
            ⟨ ⌊ ( 3 * m ^ 2 : ℝ ) ⌋₊, fun n hn => Nat.le_floor hn.1 ⟩
        have h_card : (distinctDistances'_euc (P m)).card ≤
            (Finset.image (fun n : ℕ => Real.sqrt n) (Set.Finite.toFinset h_finite)).card := by
          exact Finset.card_le_card fun x hx => by
            obtain ⟨ n, hn, rfl ⟩ := h_subset x hx
            exact Finset.mem_image.mpr ⟨ n, by aesop ⟩ ;
        generalize_proofs at *;
        exact h_card.trans ( Finset.card_image_le.trans ( by
          rw [ ← Nat.card_eq_finsetCard ]
          aesop ) );
      simpa [BinQuadForm.B] using h_card_dist_sq

/-
The quadratic form Q satisfies the conditions of Bernays' theorem.
-/
lemma Q_satisfies_bernays :
    let Δ := Q_form.discr
    (¬ ∃ z : ℤ, z * z = Δ) ∧ Q_form.Primitive ∧ Q_form.PosDef := by
      unfold Q_form;
      constructor;
      · unfold BinQuadForm.discr;
        exact fun ⟨ z, hz ⟩ => by
          norm_num [ BinQuadForm.b, BinQuadForm.a, BinQuadForm.c ] at hz
          nlinarith
      · exact ⟨ by trivial, by trivial ⟩

/-
Main theorem: Existence of sets P_n satisfying the local constraint and the distinct distance bound.
-/
theorem main_theorem (h_perucca : PeruccaClassificationStatement)
    (h_bernays : ∀ (Δ : ℤ) (_hΔnonsq : ¬ ∃ z : ℤ, z * z = Δ),
    ∃ CΔ : ℝ, 0 < CΔ ∧
      ∀ f : BinQuadForm,
        f.Primitive →
        f.PosDef →
        f.discr = Δ →
        (fun x : ℝ => (f.B x : ℝ))
          ~[Filter.atTop]
          (fun x : ℝ => CΔ * x / Real.sqrt (Real.log x))) :
    ∃ (P : ℕ → Finset (ℝ × ℝ)),
      (∀ n, (P n).card = n) ∧
      (∀ n, n ≥ 4 → ∀ S, S ⊆ P n → S.card = 4 →
        (distinctDistances'_euc S).card ≥ 3) ∧
      (Asymptotics.IsBigO Filter.atTop (fun n => ((distinctDistances'_euc (P n)).card : ℝ))
        (fun n => (n : ℝ) / Real.sqrt (Real.log n))) := by
          -- Apply Bernays' theorem to the quadratic form Q.
          obtain ⟨CΔ, hCΔ_pos, hCΔ⟩ : ∃ CΔ : ℝ,
            0 < CΔ ∧ (fun x => (Q_form.B x : ℝ)) ~[Filter.atTop]
              (fun x => CΔ * x / Real.sqrt (Real.log x)) := by
            exact h_bernays _
              (by
                rintro ⟨ z, hz ⟩
                nlinarith [ show z ≤ 2 by nlinarith, show z ≥ -2 by nlinarith ])
              |> fun ⟨ CΔ, hCΔ₁, hCΔ₂ ⟩ =>
                ⟨ CΔ, hCΔ₁, hCΔ₂ _ Q_form_primitive Q_form_posDef Q_form_discr ⟩;
          refine ⟨ fun n => P_seq n, ?_, ?_, ?_ ⟩;
          · exact fun n => P_seq_spec n |>.1;
          · intro n hn S hS hS_card
            have h_subset : S ⊆ P (m_of_n n) := by
              exact hS.trans ( P_seq_spec n |>.2 );
            exact P_local_constraint (m_of_n n) h_perucca S h_subset hS_card;
          · -- Since $B_Q(3 * (m_of_n n)^2) \leq B_Q(3n + 6\sqrt{n} + 3)$, we can
            -- use the bound from
            -- Bernays' theorem.
            have h_bound : ∀ n : ℕ,
              n ≥ 1 →
                (distinctDistances'_euc (P_seq n)).card ≤
                  (Q_form.B (3 * n + 6 * Real.sqrt n + 3) : ℝ) := by
              intros n hn
              have h_bound : (distinctDistances'_euc (P_seq n)).card ≤
                  (Q_form.B (3 * (m_of_n n) ^ 2) : ℝ) := by
                have h_bound : (distinctDistances'_euc (P_seq n)).card ≤
                    (distinctDistances'_euc (P (m_of_n n))).card := by
                  have h_subset : P_seq n ⊆ P (m_of_n n) := by
                    exact P_seq_spec n |>.2;
                  apply_rules [ Finset.card_le_card ];
                  simp_all +decide only [not_exists, ge_iff_le, subset_iff, Prod.forall]
                  unfold distinctDistances'_euc; aesop;
                exact_mod_cast h_bound.trans ( distinctDistances'_euc_bound _ <| Nat.succ_pos _ );
              refine le_trans h_bound ?_;
              refine Nat.cast_le.mpr ?_;
              refine Nat.card_mono ?_ ?_;
              · refine Set.finite_iff_bddAbove.mpr ⟨ ⌊3 * n + 6 * Real.sqrt n + 3⌋₊,
                fun x hx => Nat.le_floor <| hx.1 ⟩;
              · refine fun x hx => ⟨ ?_, hx.2 ⟩;
                refine le_trans hx.1 ?_;
                norm_num [ m_of_n ];
                nlinarith only [ show ( n.sqrt : ℝ ) ^ 2 ≤ n by exact_mod_cast Nat.sqrt_le' n,
                  Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n,
                  show ( n.sqrt : ℝ ) ≥ 0 by positivity ];
            -- Using the bound from Bernays' theorem, we get $B_Q(3n + 6\sqrt{n} + 3) \leq CΔ * (3n
            -- + 6\sqrt{n} + 3) / \sqrt{\log(3n + 6\sqrt{n} + 3)}$.
            have h_bernays_bound : ∀ᶠ n in Filter.atTop,
              (Q_form.B (3 * n + 6 * Real.sqrt n + 3) : ℝ) ≤
                CΔ * (3 * n + 6 * Real.sqrt n + 3) /
                  Real.sqrt (Real.log (3 * n + 6 * Real.sqrt n + 3)) * 2 := by
              have h_bernays_bound : ∀ᶠ x in Filter.atTop,
                (Q_form.B x : ℝ) ≤ CΔ * x / Real.sqrt (Real.log x) * 2 := by
                have := hCΔ.def ( show 0 < 1 by norm_num );
                filter_upwards [ this, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂;
                norm_num [ abs_of_nonneg, div_nonneg, Real.sqrt_nonneg, hCΔ_pos.le,
                  hx₂.le ] at hx₁ ⊢;
                rw [ abs_of_nonneg ( by positivity : 0 ≤ x ) ] at hx₁
                linarith [ abs_le.mp hx₁ ];
              rw [ Filter.eventually_atTop ] at *;
              obtain ⟨ a, ha ⟩ := h_bernays_bound
              use Max.max a 1
              intro b hb
              specialize ha ( 3 * b + 6 * Real.sqrt b + 3 )
                ( by linarith [ le_max_left a 1, le_max_right a 1, Real.sqrt_nonneg b ] )
              aesop;
            -- Using the bound from Bernays' theorem, we get $B_Q(3n + 6\sqrt{n} + 3) \leq CΔ * (3n
            -- + 6\sqrt{n} + 3) / \sqrt{\log(3n + 6\sqrt{n} + 3)}$ for sufficiently large $n$.
            have h_bernays_bound_simplified : ∀ᶠ n in Filter.atTop,
              (Q_form.B (3 * n + 6 * Real.sqrt n + 3) : ℝ) ≤
                CΔ * (3 * n + 6 * Real.sqrt n + 3) / Real.sqrt (Real.log n) * 2 := by
              filter_upwards [ h_bernays_bound,
                Filter.eventually_gt_atTop 1 ] with n hn hn' using
                le_trans hn ( mul_le_mul_of_nonneg_right
                  ( div_le_div_of_nonneg_left ( by positivity )
                    ( Real.sqrt_pos.mpr <| Real.log_pos <| by linarith ) <|
                      Real.sqrt_le_sqrt <| Real.log_le_log ( by positivity ) <|
                        by linarith [ Real.sqrt_nonneg n ] )
                  zero_le_two );
            -- Using the bound from Bernays' theorem, we get $B_Q(3n + 6\sqrt{n} + 3) \leq CΔ * (3n
            -- + 6\sqrt{n} + 3) / \sqrt{\log n}$ for sufficiently large $n$.
            have h_bernays_bound_final : ∀ᶠ n in Filter.atTop,
              (Q_form.B (3 * n + 6 * Real.sqrt n + 3) : ℝ) ≤
                12 * CΔ * n / Real.sqrt (Real.log n) := by
              filter_upwards [ h_bernays_bound_simplified,
                Filter.eventually_gt_atTop 16 ] with n hn hn';
              refine le_trans hn ?_;
              rw [ div_mul_eq_mul_div,
                div_le_div_iff_of_pos_right ( Real.sqrt_pos.mpr <| Real.log_pos <| by linarith ) ];
              nlinarith [ sq_nonneg ( Real.sqrt n - 4 ),
                Real.mul_self_sqrt ( show 0 ≤ n by linarith ), Real.sqrt_nonneg n,
                mul_le_mul_of_nonneg_left
                  ( show Real.sqrt n ≤ n / 2 by
                    nlinarith [ sq_nonneg ( Real.sqrt n - 4 ),
                      Real.mul_self_sqrt ( show 0 ≤ n by linarith ), Real.sqrt_nonneg n ] )
                  hCΔ_pos.le ];
            rw [ Asymptotics.isBigO_iff ];
            exact ⟨ 12 * CΔ, by
              filter_upwards [ Filter.eventually_ge_atTop 1,
                h_bernays_bound_final.natCast_atTop ] with n hn hn'
              rw [ Real.norm_of_nonneg ( Nat.cast_nonneg _ ),
                Real.norm_of_nonneg ( by positivity ) ]
              exact le_trans ( h_bound n hn ) ( by simpa [ mul_div_assoc ] using hn' ) ⟩

/--
Is there a set of $n$ points in $\mathbb{R}^2$ such that every subset of $4$ points determines at
least $3$ distances, yet the total number of distinct distances is $\ll \frac{n}{\sqrt{\log n}}$?
-/
theorem erdos_659 : ∃ A : ℕ → Finset ℝ²,
   (∀ n, #(A n) = n ∧ ∀ S ⊆ A n, #S = 4 → 3 ≤ distinctDistances S) ∧
    (fun n ↦ distinctDistances (A n)) ≪ fun n ↦ n / sqrt (log n) := by
  obtain ⟨P, hP_card, hP_local, hP_bigO⟩ :=
    main_theorem PeruccaClassificationStatement_proof
      (by intro Δ hΔ; exact _root_.bernays Δ hΔ)
  refine ⟨fun n => (P n).image toEuclideanPoint, ?_, ?_⟩
  · intro n
    constructor
    · rw [Finset.card_image_of_injective _ toEuclideanPoint_injective, hP_card n]
    · intro S hS hS_card
      have hA_card : ((P n).image toEuclideanPoint).card = n := by
        rw [Finset.card_image_of_injective _ toEuclideanPoint_injective, hP_card n]
      have hn : n ≥ 4 := by
        have hle := Finset.card_le_card hS
        rw [hA_card, hS_card] at hle
        omega
      let S' : Finset (ℝ × ℝ) := (P n).filter (fun p => toEuclideanPoint p ∈ S)
      have hS'_subset : S' ⊆ P n := by
        intro p hp
        exact (Finset.mem_filter.mp hp).1
      have hS_image : S'.image toEuclideanPoint = S := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
          exact (Finset.mem_filter.mp hp).2
        · intro hx
          have hxA : x ∈ (P n).image toEuclideanPoint := hS hx
          rcases Finset.mem_image.mp hxA with ⟨p, hp, rfl⟩
          exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hx⟩, rfl⟩
      have hS'_card : S'.card = 4 := by
        rw [← hS_card, ← hS_image,
          Finset.card_image_of_injective _ toEuclideanPoint_injective]
      have hdist := hP_local n hn S' hS'_subset hS'_card
      rw [← hS_image, distinctDistances_image_toEuclideanPoint]
      exact hdist
  · simpa [distinctDistances_image_toEuclideanPoint] using hP_bigO


#print axioms erdos_659
-- 'Erdos659.erdos_659' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos659
