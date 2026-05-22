/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 818.
https://www.erdosproblems.com/forum/thread/818

Informal authors:
- József Solymosi

Formal authors:
- Aristotle
- Tomaz Mascarenhas

URLs:
- https://www.erdosproblems.com/forum/thread/818#post-5890
- https://gist.githubusercontent.com/tomaz1502/d8f3632157bae289e5d0ed68ccdc9433/raw/fa7570f83d63ead268ebe5478670f6c06142edcd/Erdos_818.lean
-/
import Mathlib

namespace Erdos818

open Finset
open scoped Pointwise BigOperators

/-! ## Geometric helpers -/

noncomputable def slopeSet (A : Finset ℝ) (s : ℝ) : Finset ℝ :=
  A.filter (fun a => s * a ∈ A)

noncomputable def sumImage
    (A : Finset ℝ) (s t : ℝ) : Finset (ℝ × ℝ) :=
  (slopeSet A s ×ˢ slopeSet A t).image
    (fun p => (p.1 + p.2, s * p.1 + t * p.2))

lemma slopeSet_subset
    (A : Finset ℝ) (s : ℝ) : slopeSet A s ⊆ A :=
  filter_subset _ _

lemma mul_mem_of_slopeSet
    {A : Finset ℝ} {s a : ℝ}
    (ha : a ∈ slopeSet A s) : s * a ∈ A := by
  exact (mem_filter.mp ha).2

lemma sumImage_subset_sumset_sq
    (A : Finset ℝ) (s t : ℝ) :
    sumImage A s t ⊆ (A + A) ×ˢ (A + A) := by
  intro x
  unfold sumImage
  unfold slopeSet
  simp +contextual [Finset.mem_add]
  grind

lemma sumMap_injOn
    (A : Finset ℝ) {s t : ℝ} (hst : s ≠ t) :
    Set.InjOn
      (fun p : ℝ × ℝ =>
        (p.1 + p.2, s * p.1 + t * p.2))
      ↑(slopeSet A s ×ˢ slopeSet A t) := by
  intros p hp q hq h_eq
  have h1 : p.1 + p.2 = q.1 + q.2 :=
    congr_arg Prod.fst h_eq
  have h2 :
      s * p.1 + t * p.2 = s * q.1 + t * q.2 := by
    grind
  have : p.1 = q.1 := by grind
  have : p.2 = q.2 := by grobner
  aesop

lemma sumImage_card
    (A : Finset ℝ) {s t : ℝ} (hst : s ≠ t) :
    (sumImage A s t).card =
      (slopeSet A s).card *
        (slopeSet A t).card := by
  convert Finset.card_image_of_injOn _
  · rw [Finset.card_product]
  · exact sumMap_injOn A hst

lemma sumImage_slope_range
    (A : Finset ℝ) (hpos : ∀ a ∈ A, (0 : ℝ) < a)
    {s t : ℝ} (hst : s < t)
    {p : ℝ × ℝ} (hp : p ∈ sumImage A s t) :
    0 < p.1 ∧ s < p.2 / p.1 ∧
      p.2 / p.1 < t := by
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    Finset.mem_image.mp hp
  unfold slopeSet at ha; norm_num at ha
  exact
    ⟨add_pos (hpos _ ha.1.1) (hpos _ ha.2.1),
     by rw [lt_div_iff₀] <;>
       nlinarith [hpos _ ha.1.1, hpos _ ha.2.1],
     by rw [div_lt_iff₀] <;>
       nlinarith [hpos _ ha.1.1, hpos _ ha.2.1]⟩

lemma sumImage_disjoint
    (A : Finset ℝ) (hpos : ∀ a ∈ A, (0 : ℝ) < a)
    {s₁ s₂ s₃ s₄ : ℝ}
    (h12 : s₁ < s₂) (h23 : s₂ ≤ s₃)
    (h34 : s₃ < s₄) :
    Disjoint (sumImage A s₁ s₂)
      (sumImage A s₃ s₄) := by
  rw [Finset.disjoint_left]
  intros a ha hb
  have := sumImage_slope_range A hpos h12 ha
  have := sumImage_slope_range A hpos h34 hb
  linarith

noncomputable def extraImage
    (A : Finset ℝ) (hA : A.Nonempty) (sm : ℝ) :
    Finset (ℝ × ℝ) :=
  (slopeSet A sm ×ˢ slopeSet A sm).image
    (fun p =>
      (p.1 + A.min' hA, sm * p.1 + sm * p.2))

-- The generated subset proof relies on contextual simplification over products.
set_option linter.flexible false in
lemma extraImage_subset
    (A : Finset ℝ) (hA : A.Nonempty) (sm : ℝ) :
    extraImage A hA sm ⊆
      (A + A) ×ˢ (A + A) := by
  unfold extraImage
  simp +contextual [Finset.subset_iff, slopeSet]
  rintro a b x y hx hy hx' hy' rfl rfl
  exact
    ⟨Finset.add_mem_add hx
       (Finset.min'_mem _ hA),
     Finset.add_mem_add hy hy'⟩

lemma extraImage_card
    (A : Finset ℝ) (hA : A.Nonempty)
    (_hpos : ∀ a ∈ A, (0 : ℝ) < a)
    {sm : ℝ} (_hsm : 0 < sm) :
    (extraImage A hA sm).card =
      (slopeSet A sm).card ^ 2 := by
  convert Finset.card_image_of_injOn _
  · norm_num [sq]
  · intro p hp q hq; aesop

-- The generated slope proof relies on broad simplification after unpacking the image.
set_option linter.flexible false in
lemma extraImage_slope_ge
    (A : Finset ℝ) (hA : A.Nonempty)
    (hpos : ∀ a ∈ A, (0 : ℝ) < a)
    {sm : ℝ} (hsm : 0 < sm)
    {p : ℝ × ℝ} (hp : p ∈ extraImage A hA sm) :
    0 < p.1 ∧ sm ≤ p.2 / p.1 := by
  obtain ⟨q, hq⟩ : ∃ q : ℝ × ℝ,
      q ∈ slopeSet A sm ×ˢ slopeSet A sm ∧
      p = (q.1 + A.min' hA,
           sm * q.1 + sm * q.2) := by
    unfold extraImage at hp; aesop
  simp_all +decide [slopeSet]
  exact
    ⟨add_pos (hpos _ hq.1.1.1)
       (hpos _ (Finset.min'_mem _ hA)),
     by rw [le_div_iff₀ (add_pos
          (hpos _ hq.1.1.1)
          (hpos _ (Finset.min'_mem _ hA)))]
        nlinarith [hpos _ hq.1.1.1,
          hpos _ hq.1.2.1,
          Finset.min'_le _ _ hq.1.2.1]⟩

lemma extraImage_disjoint_sumImage
    (A : Finset ℝ) (hA : A.Nonempty)
    (hpos : ∀ a ∈ A, (0 : ℝ) < a)
    {s t sm : ℝ} (hst : s < t)
    (_htsm : t ≤ sm) (hsm : 0 < sm) :
    Disjoint (sumImage A s t)
      (extraImage A hA sm) := by
  by_contra h_contra
  rw [Finset.not_disjoint_iff] at h_contra
  obtain ⟨p, hp₁, hp₂⟩ := h_contra
  have := sumImage_slope_range A hpos hst hp₁
  have := extraImage_slope_ge A hA hpos hsm hp₂
  linarith

/-!
# Solymosi's Sum-Product Bound (2009)

**Theorem 2.1**: For any finite set `A` of positive
reals,
  `|A|⁴ ≤ 4⌈log₂|A|⌉ · |A·A| · |A+A|²`
-/

open Finset
open scoped Pointwise BigOperators

/-! ## Definitions -/

noncomputable def mulRep (A : Finset ℝ) (p : ℝ) : ℕ :=
  ((A ×ˢ A).filter
    (fun ab => ab.1 * ab.2 = p)).card

noncomputable def ratioRep (A : Finset ℝ) (s : ℝ) : ℕ :=
  (A.filter (fun a => s * a ∈ A)).card

/-! ## Part 1: Cauchy-Schwarz bound -/

lemma sum_mulRep_eq (A : Finset ℝ) :
    ∑ p ∈ A * A, mulRep A p = A.card ^ 2 := by
  unfold mulRep
  rw [← Finset.card_eq_sum_card_fiberwise]
  · rw [sq, Finset.card_product]
  · exact fun x hx =>
      Finset.mem_mul.mpr <| by aesop

lemma cauchy_schwarz_energy (A : Finset ℝ) :
    A.card ^ 4 ≤
      (∑ p ∈ A * A, mulRep A p ^ 2) *
        (A * A).card := by
  convert sq_sum_le_card_mul_sum_sq
    (s := A * A)
    (f := fun p => mulRep A p) using 1 <;> ring_nf
  · rw [sum_mulRep_eq]; ring
  · norm_num [mul_comm]

/-! ## Part 2: Geometric sub-lemmas -/

lemma weighted_avg_between
    {s t a b : ℝ} (hst : s < t)
    (ha : 0 < a) (hb : 0 < b) :
    s < (s * a + t * b) / (a + b) ∧
      (s * a + t * b) / (a + b) < t :=
  ⟨by rw [lt_div_iff₀] <;> nlinarith,
   by rw [div_lt_iff₀] <;> nlinarith⟩

lemma sum_pair_injective
    {s t : ℝ} (hst : s ≠ t)
    {a₁ b₁ a₂ b₂ : ℝ}
    (h1 : a₁ + b₁ = a₂ + b₂)
    (h2 : s * a₁ + t * b₁ =
      s * a₂ + t * b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  grind +qlia

/-! ## Part 3: Sub-lemmas for Lemma 2.3 -/

-- The generated energy bijection proof uses broad simplification and `refine'`.
set_option linter.flexible false in
set_option linter.style.refine false in
lemma energy_equiv
    (A : Finset ℝ)
    (hpos : ∀ a ∈ A, (0 : ℝ) < a) :
    ∑ p ∈ A * A, mulRep A p ^ 2 =
      ∑ s ∈ A / A, ratioRep A s ^ 2 := by
  suffices h_bij :
      ∑ p ∈ A * A, mulRep A p ^ 2 =
        ∑ s ∈ A / A, ratioRep A s ^ 2 from h_bij
  have : Finset.card (Finset.filter
      (fun ((a, b), (c, d)) => a * d = b * c)
      (Finset.product (A ×ˢ A) (A ×ˢ A))) =
      ∑ p ∈ A * A, mulRep A p ^ 2 := by
    have h_bij : Finset.card (Finset.filter
        (fun ((a, b), (c, d)) => a * b = c * d)
        (Finset.product (A ×ˢ A) (A ×ˢ A))) =
        ∑ p ∈ A * A, mulRep A p ^ 2 := by
      have h_bij : Finset.card (Finset.filter
          (fun ((a, b), (c, d)) => a * b = c * d)
          (Finset.product (A ×ˢ A) (A ×ˢ A))) =
          ∑ p ∈ A * A,
            Finset.card (Finset.filter
              (fun (a, b) => a * b = p)
              (A ×ˢ A)) ^ 2 := by
        have h_bij : Finset.filter
            (fun ((a, b), (c, d)) =>
              a * b = c * d)
            (Finset.product
              (A ×ˢ A) (A ×ˢ A)) =
            Finset.biUnion (A * A) (fun p =>
              Finset.product
                (Finset.filter
                  (fun (a, b) => a * b = p)
                  (A ×ˢ A))
                (Finset.filter
                  (fun (a, b) => a * b = p)
                  (A ×ˢ A))) := by
          ext ⟨⟨a, b⟩, ⟨c, d⟩⟩
          simp [Finset.mem_biUnion,
            Finset.mem_filter]
          rw [Finset.mem_mul]; aesop
        rw [h_bij, Finset.card_biUnion]
        · exact Finset.sum_congr rfl
            fun x hx => by
              erw [Finset.card_product]; ring
        · intros p hp q hq hpq;
          simp_all +decide [Finset.disjoint_left]
      convert h_bij using 1
    convert h_bij using 1
    refine' Finset.card_bij
      (fun x hx =>
        ((x.1.1, x.2.2), x.2.1, x.1.2))
      _ _ _ <;> simp +contextual
    · exact fun _ _ _ _ _ _ _ _ _ =>
        mul_comm _ _
    · exact fun _ _ _ _ _ _ _ _ _ =>
        mul_comm _ _
  have : Finset.card (Finset.filter
      (fun ((a, b), (c, d)) => a * d = b * c)
      (Finset.product (A ×ˢ A) (A ×ˢ A))) =
      ∑ s ∈ A / A, ratioRep A s ^ 2 := by
    have : Finset.card (Finset.filter
        (fun ((a, b), (c, d)) => a * d = b * c)
        (Finset.product (A ×ˢ A) (A ×ˢ A))) =
        ∑ s ∈ A / A,
          Finset.card (Finset.filter
            (fun (a, c) => a / c = s)
            (A ×ˢ A)) ^ 2 := by
      have : Finset.filter
          (fun ((a, b), (c, d)) => a * d = b * c)
          (Finset.product
            (A ×ˢ A) (A ×ˢ A)) =
          Finset.biUnion (A / A) (fun s =>
            Finset.product
              (Finset.filter
                (fun (a, c) => a / c = s)
                (A ×ˢ A))
              (Finset.filter
                (fun (b, d) => b / d = s)
                (A ×ˢ A))) := by
        ext ⟨⟨a, b⟩, ⟨c, d⟩⟩
        simp [Finset.mem_biUnion,
          Finset.mem_filter]
        constructor <;> intro h <;>
          simp_all +decide [Finset.mem_div]
        · exact
            ⟨⟨a, h.1.1.1, b, h.1.1.2, rfl⟩,
             by rw [div_eq_div_iff] <;>
               nlinarith [hpos a h.1.1.1,
                 hpos b h.1.1.2,
                 hpos c h.1.2.1,
                 hpos d h.1.2.2]⟩
        · rw [div_eq_div_iff] at h <;>
            nlinarith [hpos a h.2.1.1,
              hpos b h.2.1.2,
              hpos c h.2.2.1.1,
              hpos d h.2.2.1.2]
      rw [this, Finset.card_biUnion]
      · exact Finset.sum_congr rfl
          fun x hx => by
            erw [Finset.card_product]; ring
      · intros s hs t ht hst;
        simp_all +decide [Finset.disjoint_left]
    have h_ratioRep :
        ∀ s ∈ A / A, ratioRep A s =
          Finset.card (Finset.filter
            (fun (a, c) => a / c = s)
            (A ×ˢ A)) := by
      intros s hs
      simp [ratioRep]
      refine' Finset.card_bij
        (fun x hx => (s * x, x)) _ _ _ <;>
        simp +contextual
          [div_eq_iff, ne_of_gt (hpos _ _)]
      exact fun a b ha hb hab => hab ▸ ha
    exact this.trans
      (Finset.sum_congr rfl fun x hx => by
        rw [h_ratioRep x hx])
  linarith

lemma ratioRep_le_card
    (A : Finset ℝ) (s : ℝ) :
    ratioRep A s ≤ A.card :=
  Finset.card_filter_le _ _

lemma slopes_contribution_bound
    (A : Finset ℝ)
    (hpos : ∀ a ∈ A, (0 : ℝ) < a)
    (hA : A.Nonempty) (D : Finset ℝ)
    (_hD : ↑D ⊆ ↑(A / A))
    (hDpos : ∀ s ∈ D, (0 : ℝ) < s) (n : ℕ)
    (hn : ∀ s ∈ D, n ≤ ratioRep A s) :
    D.card * n ^ 2 ≤ (A + A).card ^ 2 := by
  by_cases hD_nonempty : D.Nonempty
  · obtain ⟨L, hL⟩ :
        ∃ L : Fin (D.card) → ℝ,
          StrictMono L ∧ ∀ i, L i ∈ D :=
      ⟨fun i => D.orderEmbOfFin rfl i,
       by simp +decide [StrictMono],
       fun i => D.orderEmbOfFin_mem rfl _⟩
    have h_sumImages :
        ∀ i : Fin (D.card - 1),
          (sumImage A
            (L ⟨i, by omega⟩)
            (L ⟨i + 1, by omega⟩)).card ≥
              n ^ 2 := by
      intro i
      have h_slopeSet :
          (slopeSet A
            (L ⟨i, by omega⟩)).card ≥ n ∧
          (slopeSet A
            (L ⟨i + 1, by omega⟩)).card ≥
              n :=
        ⟨hn _ (hL.2 _), hn _ (hL.2 _)⟩
      generalize_proofs at *
      rw [sumImage_card]
      · nlinarith
      · exact hL.1.injective.ne
          (ne_of_lt (Nat.lt_succ_self _))
    generalize_proofs at *
    have hDcard_pos := hD_nonempty.card_pos
    have h_extraImage :
        (extraImage A hA
          (L ⟨D.card - 1, by omega⟩)).card ≥
            n ^ 2 := by
      rw [extraImage_card]
      · exact Nat.pow_le_pow_left
          (hn _ (hL.2 _)) 2
      · assumption
      · exact hDpos _ (hL.2 _)
    generalize_proofs at *
    have h_disjoint :
        ∀ i j : Fin (D.card - 1), i < j →
          Disjoint
            (sumImage A (L ⟨i, by omega⟩)
              (L ⟨i + 1, by omega⟩))
            (sumImage A (L ⟨j, by omega⟩)
              (L ⟨j + 1, by omega⟩)) := by
      intros i j hij
      apply sumImage_disjoint A hpos
      all_goals generalize_proofs at *
      · exact hL.1 (Nat.lt_succ_self _)
      · exact hL.1.monotone
          (Nat.succ_le_of_lt hij)
      · exact hL.1 (Nat.lt_succ_self _)
    generalize_proofs at *
    have h_disjoint_extra :
        ∀ i : Fin (D.card - 1), Disjoint
          (sumImage A (L ⟨i, by omega⟩)
            (L ⟨i + 1, by omega⟩))
          (extraImage A hA
            (L ⟨D.card - 1, by omega⟩)) := by
      intro i
      apply extraImage_disjoint_sumImage
      · assumption
      · exact hL.1 (Nat.lt_succ_self _)
      · exact hL.1.monotone
          (Nat.le_pred_of_lt
            (by solve_by_elim))
      · exact hDpos _ (hL.2 _)
    generalize_proofs at *
    set Sunion :=
      Finset.biUnion
        (Finset.univ :
          Finset (Fin (D.card - 1)))
        (fun i => sumImage A
          (L ⟨i, by omega⟩)
          (L ⟨i + 1, by omega⟩)) ∪
      extraImage A hA
        (L ⟨D.card - 1, by omega⟩)
    have h_union_size :
        Sunion.card ≥
          (D.card - 1) * n ^ 2 + n ^ 2 := by
      rw [Finset.card_union_of_disjoint]
      · rw [Finset.card_biUnion]
        · exact add_le_add
            (le_trans (by norm_num)
              (Finset.sum_le_sum
                fun _ _ => h_sumImages _))
            h_extraImage
        · exact fun i _ j _ hij =>
            if hij' : i < j then
              h_disjoint i j hij'
            else Disjoint.symm
              (h_disjoint j i
                (lt_of_le_of_ne
                  (le_of_not_gt hij')
                  (Ne.symm hij)))
      · exact Finset.disjoint_left.mpr
          fun x hx₁ hx₂ => by
            obtain ⟨i, _, hi⟩ :=
              Finset.mem_biUnion.mp hx₁
            exact Finset.disjoint_left.mp
              (h_disjoint_extra i) hi hx₂
    have h_union_subset :
        Sunion ⊆ (A + A) ×ˢ (A + A) :=
      Finset.union_subset
        (Finset.biUnion_subset.mpr fun i _ =>
          sumImage_subset_sumset_sq _ _ _)
        (extraImage_subset _ _ _)
    have := Finset.card_mono h_union_subset
    simp_all +decide [sq]
    nlinarith [Nat.sub_add_cancel
      hD_nonempty.card_pos]
  · aesop

-- The dyadic decomposition proof uses generated broad simplifications and `refine'`.
set_option linter.flexible false in
set_option linter.style.refine false in
lemma ratio_energy_bound
    (A : Finset ℝ)
    (hpos : ∀ a ∈ A, (0 : ℝ) < a)
    (hcard : 2 ≤ A.card) :
    ∑ s ∈ A / A, ratioRep A s ^ 2 ≤
      4 * Nat.clog 2 A.card *
        (A + A).card ^ 2 := by
  set k := Nat.clog 2 A.card with hk
  have hk_pos : 1 ≤ k :=
    Nat.le_trans (by decide)
      (Nat.clog_mono_right 2 hcard)
  have h_class_bound :
      ∀ i < k,
        ∑ s ∈ (A / A).filter (fun s =>
            2 ^ i ≤ ratioRep A s ∧
            ratioRep A s < 2 ^ (i + 1)),
          ratioRep A s ^ 2 ≤
            4 * (A + A).card ^ 2 := by
    intro i hi
    have h_cb_i :
        (Finset.filter (fun s =>
            2 ^ i ≤ ratioRep A s ∧
            ratioRep A s < 2 ^ (i + 1))
          (A / A)).card *
          (2 ^ i) ^ 2 ≤
          (A + A).card ^ 2 := by
      convert slopes_contribution_bound A
        hpos
        (Finset.card_pos.mp
          (pos_of_gt hcard))
        (Finset.filter (fun s =>
            2 ^ i ≤ ratioRep A s ∧
            ratioRep A s < 2 ^ (i + 1))
          (A / A)) _ _ (2 ^ i) _
        using 1 <;> norm_num
      · intro s hs h₁ h₂
        rw [Finset.mem_div] at hs
        obtain ⟨a, ha, b, hb, rfl⟩ := hs
        exact div_pos (hpos _ ha) (hpos _ hb)
      · bound
    refine' le_trans
      (Finset.sum_le_sum fun x hx =>
        show ratioRep A x ^ 2 ≤
            4 * (2 ^ i) ^ 2 by
          nlinarith only [
            show ratioRep A x < 2 ^ (i + 1)
              from
              Finset.mem_filter.mp hx |>.2.2,
            show ratioRep A x ≥ 2 ^ i from
              Finset.mem_filter.mp hx |>.2.1,
            pow_succ' (2 : ℕ) i]) _;
    norm_num [Finset.sum_add_distrib,
      mul_assoc] at *;
    nlinarith [pow_pos (zero_lt_two' ℕ) i]
  have h_last_class_bound :
      ∑ s ∈ (A / A).filter
          (fun s =>
            2 ^ (k - 1) ≤ ratioRep A s),
        ratioRep A s ^ 2 ≤
          4 * (A + A).card ^ 2 := by
    have := slopes_contribution_bound A hpos
      (Finset.card_pos.mp (pos_of_gt hcard))
      (Finset.filter
        (fun s =>
          2 ^ (k - 1) ≤ ratioRep A s)
        (A / A)) ?_ ?_ (2 ^ (k - 1)) ?_ <;>
      norm_num at *
    · refine le_trans ?_
        (mul_le_mul_of_nonneg_left
          this zero_le_four)
      refine' le_trans
        (Finset.sum_le_sum fun x hx =>
          Nat.pow_le_pow_left
            (show ratioRep A x ≤ 2 ^ k
              from _) 2) _
      · exact le_trans
          (ratioRep_le_card A x)
          (Nat.le_pow_clog (by norm_num) _)
      · rcases k with (_ | k) <;>
          simp_all +decide [pow_succ'];
        ring_nf;
        rw [show Nat.clog 2 #A * 2 =
            (Nat.clog 2 #A - 1) * 2 + 2 by
          linarith [Nat.sub_add_cancel
            hk_pos]];
        ring_nf; norm_num
    · intro s hs h
      rw [Finset.mem_div] at hs
      obtain ⟨a, ha, b, hb, rfl⟩ := hs
      exact div_pos (hpos _ ha) (hpos _ hb)
  have h_sum_bound :
      ∑ s ∈ A / A, ratioRep A s ^ 2 ≤
        ∑ i ∈ Finset.range (k - 1),
          ∑ s ∈ (A / A).filter (fun s =>
              2 ^ i ≤ ratioRep A s ∧
              ratioRep A s < 2 ^ (i + 1)),
            ratioRep A s ^ 2 +
        ∑ s ∈ (A / A).filter
            (fun s =>
              2 ^ (k - 1) ≤ ratioRep A s),
          ratioRep A s ^ 2 := by
    rw [← Finset.sum_biUnion,
      ← Finset.sum_union]
    · refine Finset.sum_le_sum_of_subset ?_;
      intro s hs;
      by_cases h :
          2 ^ (k - 1) ≤ ratioRep A s <;>
        simp_all +decide;
      by_cases h₂ : ratioRep A s = 0;
      · simp_all +decide [ratioRep];
        contrapose! h₂;
        simp_all +decide [Finset.mem_div];
        rcases hs with ⟨b, hb, c, hc, rfl⟩;
        exact ⟨c, hc, by simpa [div_mul_cancel₀ _ (ne_of_gt (hpos _ hc))] using hb⟩
      · exact Or.inl
          ⟨Nat.log 2 (ratioRep A s),
           Nat.log_lt_of_lt_pow
             (by positivity) h,
           Nat.pow_le_of_le_log
             (by positivity) (by linarith),
           Nat.lt_pow_of_log_lt
             (by linarith) (by linarith)⟩
    · norm_num [Finset.disjoint_left];
      exact fun s i hi₁ hi₂ hi₃ hi₄ hi₅ =>
        lt_of_lt_of_le hi₄
          (pow_le_pow_right₀ (by norm_num)
            (Nat.succ_le_of_lt hi₁))
    · intros i hi j hj hij;
      simp_all +decide [Finset.disjoint_left];
      contrapose! hij;
      obtain ⟨a, ha₁, ha₂, ha₃, ha₄, ha₅⟩ :=
        hij;
      exact le_antisymm
        (Nat.le_of_not_lt fun hi' => by
          linarith [pow_le_pow_right₀
            (by norm_num : (1 : ℕ) ≤ 2)
            (by linarith : i ≥ j + 1)])
        (Nat.le_of_not_lt fun hj' => by
          linarith [pow_le_pow_right₀
            (by norm_num : (1 : ℕ) ≤ 2)
            (by linarith : j ≥ i + 1)])
  refine le_trans h_sum_bound ?_;
  refine' le_trans (add_le_add
    (Finset.sum_le_sum fun i hi =>
      h_class_bound i <|
        Nat.lt_of_lt_of_le
          (Finset.mem_range.mp hi)
          (Nat.pred_le _))
    h_last_class_bound) _;
  norm_num; ring_nf;
  nlinarith only [Nat.sub_add_cancel hk_pos]

lemma energy_le_sumset_sq
    (A : Finset ℝ)
    (hpos : ∀ a ∈ A, (0 : ℝ) < a)
    (hcard : 2 ≤ A.card) :
    ∑ p ∈ A * A, mulRep A p ^ 2 ≤
      4 * Nat.clog 2 A.card *
        (A + A).card ^ 2 := by
  rw [energy_equiv A hpos]
  exact ratio_energy_bound A hpos hcard

/-! ## Main Theorem -/

theorem solymosi_bound
    (A : Finset ℝ)
    (hpos : ∀ a ∈ A, (0 : ℝ) < a)
    (hcard : 2 ≤ A.card) :
    A.card ^ 4 ≤
      4 * Nat.clog 2 A.card *
        (A * A).card *
        (A + A).card ^ 2 := by
  calc A.card ^ 4
      ≤ (∑ p ∈ A * A, mulRep A p ^ 2) *
          (A * A).card :=
        cauchy_schwarz_energy A
    _ ≤ (4 * Nat.clog 2 A.card *
          (A + A).card ^ 2) *
          (A * A).card := by
        apply Nat.mul_le_mul_right
        exact energy_le_sumset_sq A hpos hcard
    _ = 4 * Nat.clog 2 A.card *
          (A * A).card *
          (A + A).card ^ 2 := by ring

-- The final case split uses broad simplification over the selected maximum.
set_option linter.flexible false in
theorem solymosi_corollary
    (A : Finset ℝ)
    (hpos : ∀ a ∈ A, (0 : ℝ) < a)
    (hcard : 2 ≤ A.card) :
    A.card ^ 4 ≤
      4 * Nat.clog 2 A.card *
        (max (A + A).card
          (A * A).card) ^ 3 := by
  have := solymosi_bound A hpos hcard
  refine le_trans this ?_
  cases max_cases (#(A + A)) (#(A * A)) <;>
    simp +decide [*, mul_assoc, pow_succ]
  · exact Nat.mul_le_mul_left _ (by
      nlinarith [mul_le_mul_right
        (by tauto : #(A * A) ≤ #(A + A))
        (#(A + A))])
  · exact Nat.mul_le_mul_left _
      (Nat.mul_le_mul_left _
        (by nlinarith))

/-!
# Erdős Problem 818 (with C = 1)

**Problem 818**: Let A be a finite set of integers
such that |A+A| ≪ |A|.
Is it true that |A·A| ≫ |A|² / (log |A|)^C
for some constant C > 0?

**Answer** (Solymosi, 2009): Yes, with C = 1.
-/

open Finset
open scoped Pointwise BigOperators

theorem erdos_problem_818
    (A : Finset ℝ)
    (hpos : ∀ a ∈ A, (0 : ℝ) < a)
    (hcard : 2 ≤ A.card)
    (c : ℕ) (hc : (A + A).card ≤ c * A.card) :
    A.card ^ 2 ≤
      4 * c ^ 2 * Nat.clog 2 A.card *
        (A * A).card := by
  have h_sol :
      A.card ^ 4 ≤
        4 * Nat.clog 2 A.card *
          (A * A).card *
          (A + A).card ^ 2 := by
    convert solymosi_bound A hpos hcard using 1
  have h_subst :
      A.card ^ 4 ≤
        4 * Nat.clog 2 A.card *
          (A * A).card *
          (c * A.card) ^ 2 :=
    h_sol.trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left hc 2))
  nlinarith

/-! ## General version -/

private noncomputable def posFilter (A : Finset ℝ) :
    Finset ℝ :=
  A.filter (fun a => 0 < a)

private noncomputable def negFilter (A : Finset ℝ) :
    Finset ℝ :=
  A.filter (fun a => a < 0)

private lemma posFilter_pos (A : Finset ℝ) :
    ∀ a ∈ posFilter A, (0 : ℝ) < a := by
  intro a ha
  exact (mem_filter.mp ha).2

private lemma neg_negFilter_pos
    (A : Finset ℝ) :
    ∀ a ∈ -(negFilter A), (0 : ℝ) < a := by
  simp +contextual [negFilter]

-- The generated cardinality comparison uses `refine'` to preserve its proof shape.
set_option linter.style.refine false in
private lemma card_le_pos_neg_plus_one
    (A : Finset ℝ) :
    A.card ≤
      (posFilter A).card +
        (negFilter A).card + 1 := by
  have h_inter :
      A = posFilter A ∪ negFilter A ∪
        ({0} ∩ A) := by
    unfold posFilter negFilter
    ext x; by_cases hx : x = 0 <;> aesop
  rw [h_inter]
  refine' le_trans
    (Finset.card_union_le _ _) _
  grind

private lemma posFilter_subset
    (A : Finset ℝ) : posFilter A ⊆ A :=
  filter_subset _ _

private lemma negFilter_subset
    (A : Finset ℝ) : negFilter A ⊆ A :=
  filter_subset _ _

private lemma neg_mul_neg_eq
    (S : Finset ℝ) : (-S) * (-S) = S * S :=
  neg_mul_neg S S

private lemma neg_add_eq
    (S : Finset ℝ) :
    (-S) + (-S) = -(S + S) := by
  rw [← neg_add]

private lemma neg_add_card_eq
    (S : Finset ℝ) :
    ((-S) + (-S)).card = (S + S).card := by
  rw [neg_add_eq, card_neg]

private lemma sumset_card_mono
    {A B : Finset ℝ} (h : B ⊆ A) :
    (B + B).card ≤ (A + A).card :=
  card_le_card (add_subset_add h h)

private lemma prodset_card_mono
    {A B : Finset ℝ} (h : B ⊆ A) :
    (B * B).card ≤ (A * A).card :=
  card_le_card (mul_subset_mul h h)

-- The generated case proof uses `refine'` to construct the subset witnesses.
set_option linter.style.refine false in
private lemma exists_pos_large_subset
    (A : Finset ℝ) (hcard : 5 ≤ A.card) :
    ∃ B : Finset ℝ,
      (∀ b ∈ B, (0 : ℝ) < b) ∧
      2 ≤ B.card ∧
      A.card ≤ 3 * B.card ∧
      (B + B).card ≤ (A + A).card ∧
      (B * B).card ≤ (A * A).card := by
  by_cases hP :
      (posFilter A).card ≥
        (negFilter A).card
  · refine' ⟨posFilter A, _, _, _, _, _⟩
    · exact fun x hx =>
        Finset.mem_filter.mp hx |>.2
    · linarith [card_le_pos_neg_plus_one A]
    · linarith [card_le_pos_neg_plus_one A]
    · exact sumset_card_mono
        (Finset.filter_subset _ _)
    · exact prodset_card_mono
        (posFilter_subset A)
  · refine' ⟨-negFilter A, _, _, _, _, _⟩ <;>
      norm_num
    · exact fun x hx =>
        neg_neg_iff_pos.mp
          (Finset.mem_filter.mp hx |>.2)
    · linarith [show
        Finset.card (posFilter A) +
          Finset.card (negFilter A) ≥ 4 by
        linarith
          [card_le_pos_neg_plus_one A]]
    · linarith
        [card_le_pos_neg_plus_one A]
    · convert sumset_card_mono
        (negFilter_subset A) using 1
      convert neg_add_card_eq
        (negFilter A) using 1
    · exact prodset_card_mono
        (negFilter_subset A)

-- The subset extraction branch uses broad simplification to assemble hypotheses.
set_option linter.flexible false in
theorem erdos_problem_818_general
    (A : Finset ℝ) (hcard : 5 ≤ A.card)
    (c : ℕ)
    (hc : (A + A).card ≤ c * A.card) :
    A.card ^ 2 ≤
      324 * c ^ 2 * Nat.clog 2 A.card *
        (A * A).card := by
  obtain ⟨B, hBpos, hB2, hB3, hBsum,
      hBprod, hBcard⟩ :
      ∃ B : Finset ℝ,
        (∀ b ∈ B, (0 : ℝ) < b) ∧
        2 ≤ B.card ∧
        A.card ≤ 3 * B.card ∧
        (B + B).card ≤ (A + A).card ∧
        (B * B).card ≤ (A * A).card ∧
        B.card ≤ A.card := by
    obtain ⟨B, hB₁, hB₂, hB₃, hB₄, hB₅⟩ :=
      exists_pos_large_subset A hcard
    by_cases hB_card : B.card ≤ A.card
    · exact ⟨B, hB₁, hB₂, hB₃,
        hB₄, hB₅, hB_card⟩
    · have := Finset.exists_subset_card_eq
        (show #A ≤ #B from by linarith)
      obtain ⟨t, ht₁, ht₂⟩ := this
      use t;
      simp_all +decide [Finset.subset_iff];
      exact ⟨by linarith, by linarith,
        le_trans
          (Finset.card_le_card <|
            Finset.add_subset_add
              (Finset.subset_iff.mpr ht₁)
              (Finset.subset_iff.mpr ht₁))
          hB₄,
        le_trans
          (Finset.card_le_card <|
            Finset.mul_subset_mul
              (Finset.subset_iff.mpr ht₁)
              (Finset.subset_iff.mpr ht₁))
          hB₅⟩
  have := erdos_problem_818 B hBpos hB2
    (3 * c) ?_
  · have h_clog :
        Nat.clog 2 B.card ≤
          Nat.clog 2 A.card := by
      apply_rules [Nat.clog_mono_right]
    nlinarith [Nat.zero_le (Nat.clog 2 #A),
      mul_le_mul_right h_clog (4 * c ^ 2),
      mul_le_mul_right hBprod
        (4 * c ^ 2 * Nat.clog 2 #A)]
  · nlinarith

#print axioms erdos_problem_818_general
-- 'Erdos818.erdos_problem_818_general' depends on axioms: [propext, choice, Quot.sound]

end Erdos818
