/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib
import Submission.IsAffineLine

/-!
# Erdős Problem 607

For a finite set `P` of points in the real affine plane, `multiplicitySpectrum P`
is the set of cardinalities of the intersections of `P` with the affine lines
determined by pairs of distinct points of `P`.  The finite set
`possibleSpectra n` consists exactly of the spectra realized by `n`-point
sets, and `F n` is its cardinality.

We prove the affirmative resolution

`F n ≤ exp (C * sqrt n)` eventually.

This is the faithful interpretation of `F(n) ≤ exp(O(sqrt n))`: the constant
belongs inside the exponential.  The proof is the set-valued specialization
of the Szemerédi--Trotter resolution.  It uses an elementary very-rich-line
bound and a dyadic finite counting argument.  The detailed mathematical
reconstruction is in `tex/607.tex`.
-/

open Filter
open scoped BigOperators Real

noncomputable section

namespace Erdos607

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The real Euclidean plane. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- Affine lines in the real Euclidean plane. -/
abbrev Line := {ℓ : AffineSubspace ℝ Point // IsAffineLine ℓ}

local instance : DecidableEq Line := Classical.decEq Line

/-- The line determined by an off-diagonal ordered pair of points of `P`. -/
noncomputable def pairLine (P : Finset Point) (pq : P.offDiag) : Line :=
  ⟨affineSpan ℝ ({pq.1.1, pq.1.2} : Set Point),
    ⟨⟨pq.1.1, subset_affineSpan ℝ _ (by simp)⟩, by
      rw [direction_affineSpan, vectorSpan_pair]
      exact finrank_span_singleton
        (vsub_ne_zero.2 (Finset.mem_offDiag.mp pq.2).2.2)⟩⟩

/-- The finite set of distinct affine lines determined by two points of `P`. -/
noncomputable def determinedLines (P : Finset Point) : Finset Line :=
  P.offDiag.attach.image (pairLine P)

/-- The points of `P` lying on `ℓ`. -/
noncomputable def pointsOn (P : Finset Point) (ℓ : Line) : Finset Point :=
  P.filter fun p ↦ p ∈ (ℓ.1 : Set Point)

/-- The number of points of `P` lying on `ℓ`. -/
noncomputable def richness (P : Finset Point) (ℓ : Line) : ℕ :=
  (pointsOn P ℓ).card

@[simp] lemma mem_pointsOn {P : Finset Point} {ℓ : Line} {p : Point} :
    p ∈ pointsOn P ℓ ↔ p ∈ P ∧ p ∈ (ℓ.1 : Set Point) := by
  simp [pointsOn]

lemma richness_le_card (P : Finset Point) (ℓ : Line) :
    richness P ℓ ≤ P.card := by
  exact Finset.card_filter_le _ _

/-- Two distinct points on an affine line span the whole line. -/
lemma affineSpan_pair_eq_line {p q : Point} (hpq : p ≠ q) (ℓ : Line)
    (hp : p ∈ (ℓ.1 : Set Point)) (hq : q ∈ (ℓ.1 : Set Point)) :
    affineSpan ℝ ({p, q} : Set Point) = ℓ.1 := by
  have line_le : affineSpan ℝ ({p, q} : Set Point) ≤ ℓ.1 :=
    affineSpan_le.2 (by
      intro z hz
      rcases hz with (rfl | hz)
      · exact hp
      · simpa only [Set.mem_singleton_iff] using hz ▸ hq)
  have line_rank : Module.finrank ℝ
      (affineSpan ℝ ({p, q} : Set Point)).direction = 1 := by
    rw [direction_affineSpan, vectorSpan_pair]
    exact finrank_span_singleton (vsub_ne_zero.2 hpq)
  have dir_eq :
      (affineSpan ℝ ({p, q} : Set Point)).direction = ℓ.1.direction :=
    Submodule.eq_of_le_of_finrank_eq
      (AffineSubspace.direction_le line_le)
      (line_rank.trans ℓ.2.2.symm)
  exact AffineSubspace.ext_of_direction_eq dir_eq
    ⟨p, subset_affineSpan ℝ _ (by simp), hp⟩

/-- A line is determined by `P` exactly when it contains at least two points
of `P`. -/
lemma mem_determinedLines_iff_two_points {P : Finset Point} {ℓ : Line} :
    ℓ ∈ determinedLines P ↔ 2 ≤ richness P ℓ := by
  constructor
  · intro hℓ
    obtain ⟨pq, hpq, hpqℓ⟩ := Finset.mem_image.mp hℓ
    have hpqmem : pq.1 ∈ P.offDiag := pq.2
    have hp := (Finset.mem_offDiag.mp hpqmem).1
    have hq := (Finset.mem_offDiag.mp hpqmem).2.1
    have hpqne := (Finset.mem_offDiag.mp hpqmem).2.2
    have hline : (pairLine P pq).1 = ℓ.1 := congrArg Subtype.val hpqℓ
    apply Finset.one_lt_card.mpr
    refine ⟨pq.1.1, ?_, pq.1.2, ?_, hpqne⟩
    · exact Finset.mem_filter.mpr ⟨hp, by
        rw [← hline]
        exact subset_affineSpan ℝ _ (by simp)⟩
    · exact Finset.mem_filter.mpr ⟨hq, by
        rw [← hline]
        exact subset_affineSpan ℝ _ (by simp)⟩
  · intro hcard
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hcard
    have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
    have hpℓ : p ∈ (ℓ.1 : Set Point) := (Finset.mem_filter.mp hp).2
    have hqP : q ∈ P := (Finset.mem_filter.mp hq).1
    have hqℓ : q ∈ (ℓ.1 : Set Point) := (Finset.mem_filter.mp hq).2
    let pq : P.offDiag :=
      ⟨(p, q), Finset.mem_offDiag.mpr ⟨hpP, hqP, hpq⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨pq, Finset.mem_attach _ pq, ?_⟩
    apply Subtype.ext
    exact affineSpan_pair_eq_line hpq ℓ hpℓ hqℓ

/-- The set of distinct line multiplicities determined by `P`. -/
noncomputable def multiplicitySpectrum (P : Finset Point) : Finset ℕ :=
  (determinedLines P).image (richness P)

/-- A canonical (classically chosen) determined line witnessing a value in
the multiplicity spectrum. -/
noncomputable def representativeLine (P : Finset Point)
    (k : multiplicitySpectrum P) : Line :=
  Classical.choose (Finset.mem_image.mp k.2)

lemma representativeLine_mem (P : Finset Point) (k : multiplicitySpectrum P) :
    representativeLine P k ∈ determinedLines P :=
  (Classical.choose_spec (Finset.mem_image.mp k.2)).1

@[simp] lemma richness_representativeLine (P : Finset Point)
    (k : multiplicitySpectrum P) :
    richness P (representativeLine P k) = k :=
  (Classical.choose_spec (Finset.mem_image.mp k.2)).2

/-- Distinct spectrum values have distinct representative lines. -/
noncomputable def representativeEmbedding (P : Finset Point)
    (S : Finset ℕ) (hS : S ⊆ multiplicitySpectrum P) : S ↪ Line where
  toFun k := representativeLine P ⟨k.1, hS k.2⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    have := congrArg (richness P) hab
    simpa using this

lemma multiplicitySpectrum_subset_Icc (P : Finset Point) :
    multiplicitySpectrum P ⊆ Finset.Icc 2 P.card := by
  intro k hk
  obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.mp hk
  exact Finset.mem_Icc.mpr
    ⟨mem_determinedLines_iff_two_points.mp hℓ, richness_le_card P ℓ⟩

/-- `A` is realized as the exact line-multiplicity spectrum of an `n`-point
set in the real plane. -/
def IsRealizableSpectrum (n : ℕ) (A : Finset ℕ) : Prop :=
  ∃ P : Finset Point, P.card = n ∧ multiplicitySpectrum P = A

/-- The finite set of all spectra realized by `n`-point configurations. -/
noncomputable def possibleSpectra (n : ℕ) : Finset (Finset ℕ) :=
  ((Finset.Icc 2 n).powerset).filter (IsRealizableSpectrum n)

/-- The function `F(n)` in Erdős Problem 607. -/
noncomputable def F (n : ℕ) : ℕ :=
  (possibleSpectra n).card

@[simp] theorem mem_possibleSpectra {n : ℕ} {A : Finset ℕ} :
    A ∈ possibleSpectra n ↔ IsRealizableSpectrum n A := by
  constructor
  · exact fun h ↦ (Finset.mem_filter.mp h).2
  · rintro ⟨P, hPcard, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, ⟨P, hPcard, rfl⟩⟩
    simpa [hPcard] using multiplicitySpectrum_subset_Icc P

/-! ## An elementary very-rich-line bound -/

lemma card_inter_pointsOn_le_one (P : Finset Point) {ℓ m : Line}
    (hℓm : ℓ ≠ m) :
    ((pointsOn P ℓ) ∩ pointsOn P m).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  have hpℓ : p ∈ (ℓ.1 : Set Point) := (mem_pointsOn.mp (Finset.mem_inter.mp hp).1).2
  have hpm : p ∈ (m.1 : Set Point) := (mem_pointsOn.mp (Finset.mem_inter.mp hp).2).2
  have hqℓ : q ∈ (ℓ.1 : Set Point) := (mem_pointsOn.mp (Finset.mem_inter.mp hq).1).2
  have hqm : q ∈ (m.1 : Set Point) := (mem_pointsOn.mp (Finset.mem_inter.mp hq).2).2
  by_contra hpq
  apply hℓm
  apply Subtype.ext
  exact (affineSpan_pair_eq_line hpq ℓ hpℓ hqℓ).symm.trans
    (affineSpan_pair_eq_line hpq m hpm hqm)

/-- The first two terms of inclusion--exclusion for a family whose pairwise
intersections have cardinality at most one. -/
lemma sum_card_le_card_biUnion_add_choose {α β : Type*}
    [DecidableEq β] (f : α → Finset β) (s : Finset α)
    (hpair : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (f a ∩ f b).card ≤ 1) :
    ∑ a ∈ s, (f a).card ≤ (s.biUnion f).card + s.card.choose 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a L ha ih =>
      have hpairL : ∀ b ∈ L, ∀ c ∈ L, b ≠ c → (f b ∩ f c).card ≤ 1 := by
        intro b hb c hc hbc
        exact hpair b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc) hbc
      have hih := ih hpairL
      let U : Finset β := L.biUnion f
      have hihU : (∑ b ∈ L, (f b).card) ≤ U.card + Nat.choose L.card 2 := by
        simpa [U] using hih
      have hover_sub : f a ∩ U ⊆ L.biUnion (fun b ↦ f a ∩ f b) := by
        intro x hx
        obtain ⟨hxa, hxU⟩ := Finset.mem_inter.mp hx
        obtain ⟨b, hbL, hxb⟩ := Finset.mem_biUnion.mp hxU
        exact Finset.mem_biUnion.mpr
          ⟨b, hbL, Finset.mem_inter.mpr ⟨hxa, hxb⟩⟩
      have hover : (f a ∩ U).card ≤ L.card := by
        calc
          (f a ∩ U).card ≤ (L.biUnion (fun b ↦ f a ∩ f b)).card :=
            Finset.card_le_card hover_sub
          _ ≤ ∑ b ∈ L, (f a ∩ f b).card := Finset.card_biUnion_le
          _ ≤ ∑ _b ∈ L, 1 := by
            gcongr with b hb
            exact hpair a (by simp) b (by simp [hb]) (by
              intro hab
              apply ha
              simpa [hab] using hb)
          _ = L.card := by simp
      have hunion : (f a).card + U.card = (f a ∪ U).card + (f a ∩ U).card :=
        (Finset.card_union_add_card_inter (f a) U).symm
      have hbiUnion : (insert a L).biUnion f = f a ∪ U := by
        ext x
        simp [U]
      have hchoose : Nat.choose (L.card + 1) 2 =
          Nat.choose L.card 2 + L.card := by
        rw [Nat.choose_succ_succ]
        simp [Nat.add_comm]
      simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      rw [hbiUnion, hchoose]
      omega

/-- Incidence inequality for a finite family of distinct affine lines. -/
lemma sum_richness_le_card_add_choose (P : Finset Point) (L : Finset Line) :
    ∑ ℓ ∈ L, richness P ℓ ≤ P.card + Nat.choose L.card 2 := by
  have hlinear : ∀ ℓ₁ ∈ L, ∀ ℓ₂ ∈ L, ℓ₁ ≠ ℓ₂ →
      (pointsOn P ℓ₁ ∩ pointsOn P ℓ₂).card ≤ 1 := by
    intro ℓ₁ _ ℓ₂ _ hne
    exact card_inter_pointsOn_le_one P hne
  have hfamily := sum_card_le_card_biUnion_add_choose (pointsOn P) L hlinear
  have hunion_sub : L.biUnion (pointsOn P) ⊆ P := by
    intro p hp
    obtain ⟨ℓ, _hℓ, hpℓ⟩ := Finset.mem_biUnion.mp hp
    exact (mem_pointsOn.mp hpℓ).1
  calc
    (∑ ℓ ∈ L, richness P ℓ) = ∑ ℓ ∈ L, (pointsOn P ℓ).card := by rfl
    _ ≤ (L.biUnion (pointsOn P)).card + Nat.choose L.card 2 := hfamily
    _ ≤ P.card + Nat.choose L.card 2 :=
      Nat.add_le_add_right (Finset.card_le_card hunion_sub) _

/-- If every line in `L` contains more than `sqrt (2 * |P|)` points, then
the total lower-bound incidence `|L| * k` is at most `2 * |P|`. -/
lemma very_rich_lines (P : Finset Point) (L : Finset Line) (k : ℕ)
    (hk : 2 * P.card < k ^ 2)
    (hrich : ∀ ℓ ∈ L, k ≤ richness P ℓ) :
    L.card * k ≤ 2 * P.card := by
  have hlower (S : Finset Line) (hSL : S ⊆ L) :
      S.card * k ≤ ∑ ℓ ∈ S, richness P ℓ := by
    calc
      S.card * k = ∑ _ℓ ∈ S, k := by simp
      _ ≤ ∑ ℓ ∈ S, richness P ℓ := by
        gcongr with ℓ hℓ
        exact hrich ℓ (hSL hℓ)
  have hLk : L.card ≤ k := by
    by_contra hnot
    have hk1L : k + 1 ≤ L.card := by omega
    obtain ⟨S, hSL, hScard⟩ := Finset.exists_subset_card_eq hk1L
    have hlowS := hlower S hSL
    have huppS := sum_richness_le_card_add_choose P S
    rw [hScard] at hlowS huppS
    have hchooseS : 2 * Nat.choose (k + 1) 2 = (k + 1) * k := by
      rw [Nat.choose_two_right,
        Nat.mul_div_cancel' (Nat.two_dvd_mul_sub_one (k + 1))]
      simp
    have htwice := Nat.mul_le_mul_left 2 (hlowS.trans huppS)
    nlinarith
  have hlowL := hlower L (by simp)
  have huppL := sum_richness_le_card_add_choose P L
  have hchoose_bound : 2 * Nat.choose L.card 2 ≤ L.card * k := by
    rw [Nat.choose_two_right,
      Nat.mul_div_cancel' (Nat.two_dvd_mul_sub_one L.card)]
    exact Nat.mul_le_mul_left _ ((Nat.sub_le _ _).trans hLk)
  have htwice := Nat.mul_le_mul_left 2 (hlowL.trans huppL)
  omega

/-! ## A finite entropy bound -/

lemma card_powerset_filter_card_le_eq_sum
    {α : Type*} (U : Finset α) (b : ℕ) :
    (U.powerset.filter fun S => S.card ≤ b).card =
      ∑ k ∈ Finset.range (b + 1), U.card.choose k := by
  classical
  have h_union :
      U.powerset.filter (fun S => S.card ≤ b) =
        (Finset.range (b + 1)).biUnion (fun k => U.powersetCard k) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard]
    constructor
    · rintro ⟨hSU, hSb⟩
      exact ⟨S.card, Nat.lt_succ_of_le hSb, hSU, rfl⟩
    · rintro ⟨k, hkb, hSU, hSk⟩
      exact ⟨hSU, by omega⟩
  rw [h_union, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.card_powersetCard]
  · intro i hi j hj hij
    rw [Function.onFun, Finset.disjoint_iff_ne]
    intro S hSi T hTj hST
    rw [Finset.mem_powersetCard] at hSi hTj
    subst T
    exfalso
    apply hij
    omega

lemma choose_mono_right_of_le_half {n i b : ℕ}
    (hib : i ≤ b) (hbn : b ≤ n / 2) : n.choose i ≤ n.choose b := by
  induction b, hib using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih =>
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

lemma pow_div_three_le_factorial (k : ℕ) :
    ((k : ℝ) / 3) ^ k ≤ (k.factorial : ℝ) := by
  by_cases hk : k = 0
  · simp [hk]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * k) := by
    rw [Real.one_le_sqrt]
    have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    nlinarith
  have hbase : (k : ℝ) / 3 ≤ (k : ℝ) / Real.exp 1 := by
    exact div_le_div_of_nonneg_left (by positivity) (Real.exp_pos 1)
      Real.exp_one_lt_three.le
  calc
    ((k : ℝ) / 3) ^ k ≤ ((k : ℝ) / Real.exp 1) ^ k :=
      pow_le_pow_left₀ (by positivity) hbase k
    _ ≤ Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ k := by
      exact le_mul_of_one_le_left (by positivity) hsqrt
    _ ≤ (k.factorial : ℝ) := Stirling.le_factorial_stirling k

lemma choose_le_three_mul_div_pow (n k : ℕ) :
    (n.choose k : ℝ) ≤ ((3 : ℝ) * n / k) ^ k := by
  by_cases hk : k = 0
  · simp [hk]
  have hkpos : (0 : ℝ) < k := by positivity
  have hfacpos : (0 : ℝ) < k.factorial := by positivity
  calc
    (n.choose k : ℝ) ≤ (n : ℝ) ^ k / k.factorial := Nat.choose_le_pow_div k n
    _ ≤ (n : ℝ) ^ k / (((k : ℝ) / 3) ^ k) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_div_three_le_factorial k)
    _ = ((3 : ℝ) * n / k) ^ k := by
      rw [← div_pow]
      congr 1
      field_simp

lemma succ_le_two_pow (b : ℕ) : b + 1 ≤ 2 ^ b := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [pow_succ]
      omega

/-- A dyadic block of `R * 2^j` possible values with cap `R / 2^j`
has at most the displayed number of subsets. -/
lemma card_powerset_filter_card_le_dyadic
    {α : Type*} (U : Finset α) (R j : ℕ)
    (hU : U.card = R * 2 ^ j) :
    (U.powerset.filter fun S => S.card ≤ R / 2 ^ j).card ≤
      2 ^ ((2 * j + 4) * (R / 2 ^ j)) := by
  classical
  let q := 2 ^ j
  let b := R / q
  let N := U.card
  have hqpos : 0 < q := by simp [q]
  have hN : N = R * q := by simpa [N, q] using hU
  have hcardeq :
      (U.powerset.filter fun S => S.card ≤ b).card =
        ∑ k ∈ Finset.range (b + 1), N.choose k := by
    simpa [N] using card_powerset_filter_card_le_eq_sum U b
  by_cases hb0 : b = 0
  · have hcardle := Nat.le_of_eq hcardeq
    simpa [b, q, hb0] using hcardle
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
  by_cases hj0 : j = 0
  · subst j
    simp only [pow_zero, Nat.div_one] at *
    calc
      (U.powerset.filter fun S => S.card ≤ R).card ≤ U.powerset.card :=
        Finset.card_filter_le _ _
      _ = 2 ^ U.card := Finset.card_powerset U
      _ = 2 ^ R := by simp [hU]
      _ ≤ 2 ^ (4 * R) := Nat.pow_le_pow_right (by omega) (by omega)
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
  have hq2 : 2 ≤ q := by
    simp only [q]
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hjpos
  have hbR : b ≤ R := Nat.div_le_self R q
  have hbhalf : b ≤ N / 2 := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    calc
      b * 2 = 2 * b := by omega
      _ ≤ q * b := Nat.mul_le_mul_right b hq2
      _ ≤ q * R := Nat.mul_le_mul_left q hbR
      _ = N := by rw [hN]; ring
  have hsum_le :
      (∑ k ∈ Finset.range (b + 1), N.choose k) ≤
        (b + 1) * N.choose b := by
    calc
      (∑ k ∈ Finset.range (b + 1), N.choose k) ≤
          ∑ _k ∈ Finset.range (b + 1), N.choose b := by
        apply Finset.sum_le_sum
        intro k hk
        exact choose_mono_right_of_le_half
          (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hbhalf
      _ = (b + 1) * N.choose b := by simp
  have hRlt : R < (b + 1) * q := by
    rw [← Nat.div_lt_iff_lt_mul hqpos]
    simp [b]
  have hRle : R ≤ 2 * b * q := by
    calc
      R ≤ (b + 1) * q := Nat.le_of_lt hRlt
      _ ≤ (2 * b) * q := Nat.mul_le_mul_right q (by omega)
      _ = 2 * b * q := by ring
  have hratio : ((3 : ℝ) * N / b) ≤ (2 : ℝ) ^ (2 * j + 3) := by
    have hqreal : (q : ℝ) = (2 : ℝ) ^ j := by simp [q]
    rw [div_le_iff₀ (by positivity)]
    rw [show (2 : ℝ) ^ (2 * j + 3) = 8 * ((2 : ℝ) ^ j) ^ 2 by
      rw [show 2 * j + 3 = j + j + 3 by omega, pow_add, pow_add]
      norm_num
      ring]
    rw [hN, Nat.cast_mul, hqreal]
    have hRle' : (R : ℝ) ≤ 2 * b * q := by exact_mod_cast hRle
    rw [hqreal] at hRle'
    calc
      3 * ((R : ℝ) * (2 : ℝ) ^ j) ≤
          3 * (2 * (b : ℝ) * (2 : ℝ) ^ j) * (2 : ℝ) ^ j := by
        have := mul_le_mul_of_nonneg_right hRle'
          (show (0 : ℝ) ≤ 3 * 2 ^ j by positivity)
        nlinarith
      _ ≤ 8 * ((2 : ℝ) ^ j) ^ 2 * b := by
        ring_nf
        have hz : (0 : ℝ) ≤ (b : ℝ) * 2 ^ (j * 2) := by positivity
        nlinarith
  have hbpow : (b + 1 : ℝ) ≤ 2 ^ b := by
    exact_mod_cast succ_le_two_pow b
  have hreal :
      ((U.powerset.filter fun S => S.card ≤ b).card : ℝ) ≤
        (2 : ℝ) ^ ((2 * j + 4) * b) := by
    calc
      ((U.powerset.filter fun S => S.card ≤ b).card : ℝ) =
          (∑ k ∈ Finset.range (b + 1), N.choose k : ℕ) := by rw [hcardeq]
      _ ≤ ((b + 1) * N.choose b : ℕ) := by exact_mod_cast hsum_le
      _ = (b + 1 : ℝ) * (N.choose b : ℝ) := by norm_num
      _ ≤ (b + 1 : ℝ) * (((3 : ℝ) * N / b) ^ b) := by
        gcongr
        exact choose_le_three_mul_div_pow N b
      _ ≤ (b + 1 : ℝ) * (((2 : ℝ) ^ (2 * j + 3)) ^ b) := by
        gcongr
      _ ≤ (2 : ℝ) ^ b * (((2 : ℝ) ^ (2 * j + 3)) ^ b) := by
        gcongr
      _ = (2 : ℝ) ^ ((2 * j + 4) * b) := by
        rw [← pow_mul]
        rw [show (2 * j + 4) * b = b + (2 * j + 3) * b by ring, pow_add]
  exact_mod_cast hreal

/-! ## The dyadic decomposition -/

/-- A convenient integer strictly larger than `2 * sqrt n`. -/
def cutoff (n : ℕ) : ℕ :=
  2 * (Nat.sqrt n + 1)

lemma cutoff_pos (n : ℕ) : 0 < cutoff n := by
  simp [cutoff]

lemma two_mul_lt_cutoff_sq (n : ℕ) :
    2 * n < cutoff n ^ 2 := by
  have hn : n < (Nat.sqrt n + 1) ^ 2 := Nat.lt_succ_sqrt' n
  simp only [cutoff]
  nlinarith [sq_nonneg (Nat.sqrt n + 1)]

/-- The half-open dyadic interval `[R * 2^j, R * 2^(j+1))`. -/
def block (R j : ℕ) : Finset ℕ :=
  Finset.Ico (R * 2 ^ j) (R * 2 ^ (j + 1))

/-- The maximum number of spectrum values allowed in the `j`th block. -/
def blockCap (R j : ℕ) : ℕ :=
  R / 2 ^ j

/-- All subsets of the `j`th block satisfying its cardinality cap. -/
def blockFamily (R j : ℕ) : Finset (Finset ℕ) :=
  (block R j).powerset.filter fun S ↦ S.card ≤ blockCap R j

@[simp] lemma card_block (R j : ℕ) :
    (block R j).card = R * 2 ^ j := by
  rw [block, Nat.card_Ico, pow_succ]
  have h : R * (2 ^ j * 2) = R * 2 ^ j + R * 2 ^ j := by ring
  rw [h]
  omega

@[simp] lemma mem_block {R j k : ℕ} :
    k ∈ block R j ↔ R * 2 ^ j ≤ k ∧ k < R * 2 ^ (j + 1) := by
  simp [block]

@[simp] lemma mem_blockFamily {R j : ℕ} {S : Finset ℕ} :
    S ∈ blockFamily R j ↔ S ⊆ block R j ∧ S.card ≤ blockCap R j := by
  simp [blockFamily]

lemma card_blockFamily_le (R j : ℕ) :
    (blockFamily R j).card ≤
      2 ^ ((2 * j + 4) * blockCap R j) := by
  unfold blockFamily blockCap
  exact card_powerset_filter_card_le_dyadic (block R j) R j (card_block R j)

lemma exists_mem_block {R k : ℕ} (hR : 0 < R) (hk : R ≤ k) :
    ∃ j ≤ k, k ∈ block R j := by
  let Q : ℕ → Prop := fun q ↦ k < R * 2 ^ q
  have hQ : ∃ q, Q q := by
    refine ⟨k, (Nat.lt_pow_self (n := k) (a := 2) (by omega)).trans_le ?_⟩
    simpa using Nat.mul_le_mul_right (2 ^ k) hR
  let q := Nat.find hQ
  have hqQ : Q q := Nat.find_spec hQ
  have hqpos : 0 < q := by
    by_contra h
    have hq0 : q = 0 := by omega
    have : k < R := by simpa [Q, hq0] using hqQ
    omega
  refine ⟨q - 1, ?_, ?_⟩
  · have hqk : q ≤ k := Nat.find_min' hQ (show Q k from by
      exact (Nat.lt_pow_self (n := k) (a := 2) (by omega)).trans_le (by
        simpa using Nat.mul_le_mul_right (2 ^ k) hR))
    omega
  · rw [mem_block]
    have hnot : ¬ Q (q - 1) := Nat.find_min hQ (by omega)
    have hqeq : q - 1 + 1 = q := by omega
    exact ⟨by simpa [Q] using Nat.le_of_not_gt hnot, by simpa [hqeq] using hqQ⟩

lemma exists_mem_block_range {R n k : ℕ} (hR : 0 < R)
    (hkR : R ≤ k) (hkn : k ≤ n) :
    ∃ j ∈ Finset.range (n + 1), k ∈ block R j := by
  obtain ⟨j, hjk, hjmem⟩ := exists_mem_block hR hkR
  exact ⟨j, Finset.mem_range.mpr (by omega), hjmem⟩

/-- The intersections of `A` with all high dyadic blocks. -/
def blockCode (R n : ℕ) (A : Finset ℕ) :
    (j : ℕ) → j ∈ Finset.range (n + 1) → Finset ℕ :=
  fun j _ ↦ A ∩ block R j

/-- The low part of a spectrum together with all its high dyadic parts. -/
def spectrumCode (R n : ℕ) (A : Finset ℕ) :
    Finset ℕ × ((j : ℕ) → j ∈ Finset.range (n + 1) → Finset ℕ) :=
  (A ∩ Finset.range R, blockCode R n A)

/-- The finite product containing every code that satisfies the dyadic caps. -/
def spectrumTarget (R n : ℕ) :
    Finset (Finset ℕ × ((j : ℕ) → j ∈ Finset.range (n + 1) → Finset ℕ)) :=
  (Finset.range R).powerset ×ˢ
    Finset.pi (Finset.range (n + 1)) (blockFamily R)

lemma spectrumCode_injOn {R n : ℕ} (hR : 0 < R)
    (family : Finset (Finset ℕ))
    (hsub : ∀ A ∈ family, A ⊆ Finset.Icc 2 n) :
    Set.InjOn (spectrumCode R n) family := by
  intro A hA B hB hencode
  have hlow : A ∩ Finset.range R = B ∩ Finset.range R :=
    congrArg Prod.fst hencode
  have hblocks : blockCode R n A = blockCode R n B :=
    congrArg Prod.snd hencode
  apply Finset.ext
  intro k
  by_cases hkR : k < R
  · have hmem : k ∈ Finset.range R := Finset.mem_range.mpr hkR
    have := congrArg (fun S : Finset ℕ ↦ k ∈ S) hlow
    simpa [hmem] using this
  · have hRk : R ≤ k := by omega
    by_cases hkn : k ≤ n
    · obtain ⟨j, hjrange, hjblock⟩ := exists_mem_block_range hR hRk hkn
      have hblockEq : A ∩ block R j = B ∩ block R j := by
        exact congrFun (congrFun hblocks j) hjrange
      have := congrArg (fun S : Finset ℕ ↦ k ∈ S) hblockEq
      simpa [hjblock] using this
    · have hkA : k ∉ A := by
        intro hk
        exact hkn (Finset.mem_Icc.mp (hsub A hA hk)).2
      have hkB : k ∉ B := by
        intro hk
        exact hkn (Finset.mem_Icc.mp (hsub B hB hk)).2
      simp [hkA, hkB]

lemma spectrumCode_mem_target {R n : ℕ} {family : Finset (Finset ℕ)}
    (hcap : ∀ A ∈ family, ∀ j ∈ Finset.range (n + 1),
      (A ∩ block R j).card ≤ blockCap R j) :
    Set.MapsTo (spectrumCode R n) family (spectrumTarget R n) := by
  intro A hA
  change spectrumCode R n A ∈ spectrumTarget R n
  rw [spectrumTarget]
  refine Finset.mem_product.mpr ⟨?_, ?_⟩
  · exact Finset.mem_powerset.mpr Finset.inter_subset_right
  · rw [Finset.mem_pi]
    intro j hj
    exact mem_blockFamily.mpr
      ⟨Finset.inter_subset_right, hcap A hA j hj⟩

/-- Abstract cardinal bound for a family satisfying all dyadic caps. -/
theorem card_family_le_two_pow {R n : ℕ} (hR : 0 < R)
    (family : Finset (Finset ℕ))
    (hsub : ∀ A ∈ family, A ⊆ Finset.Icc 2 n)
    (hcap : ∀ A ∈ family, ∀ j ∈ Finset.range (n + 1),
      (A ∩ block R j).card ≤ blockCap R j) :
    family.card ≤
      2 ^ (R + ∑ j ∈ Finset.range (n + 1), (2 * j + 4) * blockCap R j) := by
  calc
    family.card ≤ (spectrumTarget R n).card :=
      Finset.card_le_card_of_injOn (spectrumCode R n)
        (spectrumCode_mem_target hcap) (spectrumCode_injOn hR family hsub)
    _ = 2 ^ R * ∏ j ∈ Finset.range (n + 1), (blockFamily R j).card := by
      rw [spectrumTarget, Finset.card_product, Finset.card_powerset,
        Finset.card_range, Finset.card_pi]
    _ ≤ 2 ^ R * ∏ j ∈ Finset.range (n + 1),
        2 ^ ((2 * j + 4) * blockCap R j) := by
      exact Nat.mul_le_mul_left _ (Finset.prod_le_prod' fun j _ ↦ card_blockFamily_le R j)
    _ = 2 ^ (R + ∑ j ∈ Finset.range (n + 1),
        (2 * j + 4) * blockCap R j) := by
      rw [pow_add, Finset.prod_pow_eq_pow_sum]

/-- Every realizable spectrum obeys the dyadic block cap above `cutoff n`. -/
lemma spectrum_inter_block_card_le (P : Finset Point) (n j : ℕ)
    (hPcard : P.card = n) :
    (multiplicitySpectrum P ∩ block (cutoff n) j).card ≤
      blockCap (cutoff n) j := by
  let S := multiplicitySpectrum P ∩ block (cutoff n) j
  have hSspec : S ⊆ multiplicitySpectrum P := Finset.inter_subset_left
  let e : S ↪ Line := representativeEmbedding P S hSspec
  let L : Finset Line := S.attach.map e
  have hLcard : L.card = S.card := by simp [L]
  have hrich : ∀ ℓ ∈ L, cutoff n * 2 ^ j ≤ richness P ℓ := by
    intro ℓ hℓ
    obtain ⟨k, _hkattach, hkℓ⟩ := Finset.mem_map.mp hℓ
    subst ℓ
    have hkblock : k.1 ∈ block (cutoff n) j :=
      (Finset.mem_inter.mp k.2).2
    have hrepr : richness P (e k) = k.1 := by
      change richness P (representativeLine P ⟨k.1, hSspec k.2⟩) = k.1
      exact richness_representativeLine P ⟨k.1, hSspec k.2⟩
    rw [hrepr]
    exact (mem_block.mp hkblock).1
  have hk : 2 * P.card < (cutoff n * 2 ^ j) ^ 2 := by
    rw [hPcard]
    have hcut := two_mul_lt_cutoff_sq n
    have hpow : cutoff n ^ 2 ≤ (cutoff n * 2 ^ j) ^ 2 := by
      gcongr
      exact Nat.le_mul_of_pos_right _ (pow_pos (by omega : 0 < 2) _)
    exact hcut.trans_le hpow
  have hrichBound := very_rich_lines P L (cutoff n * 2 ^ j) hk hrich
  rw [hLcard, hPcard] at hrichBound
  have hstrict : S.card * (cutoff n * 2 ^ j) < cutoff n ^ 2 :=
    hrichBound.trans_lt (two_mul_lt_cutoff_sq n)
  have hstrict' : (S.card * 2 ^ j) * cutoff n < cutoff n * cutoff n := by
    simpa [pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hstrict
  have hcancel : S.card * 2 ^ j < cutoff n :=
    (Nat.mul_lt_mul_right (cutoff_pos n)).mp hstrict'
  apply (Nat.le_div_iff_mul_le (pow_pos (by omega : 0 < 2) j)).2
  exact hcancel.le

/-! ## Counting all realizable spectra -/

/-- The exact family of realizable spectra satisfies the abstract dyadic
counting estimate. -/
lemma F_le_two_pow (n : ℕ) :
    F n ≤ 2 ^ (cutoff n + ∑ j ∈ Finset.range (n + 1),
      (2 * j + 4) * blockCap (cutoff n) j) := by
  unfold F
  apply card_family_le_two_pow (cutoff_pos n)
  · intro A hA
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
  · intro A hA j hj
    obtain ⟨P, hPcard, hPA⟩ := mem_possibleSpectra.mp hA
    rw [← hPA]
    exact spectrum_inter_block_card_le P n j hPcard

lemma cast_blockCap_le (R j : ℕ) :
    ((blockCap R j : ℕ) : ℝ) ≤ (R : ℝ) / (2 : ℝ) ^ j := by
  have hqpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  rw [le_div_iff₀ hqpos]
  have hnat : (R / 2 ^ j) * 2 ^ j ≤ R := Nat.div_mul_le_self R (2 ^ j)
  have hreal : (((R / 2 ^ j) * 2 ^ j : ℕ) : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast hnat
  simpa [blockCap] using hreal

lemma weightedGeometricSum_le_four (m : ℕ) :
    (∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ j) ≤ 4 := by
  have hmoment : HasSum (fun j : ℕ =>
      (j : ℝ) * ((1 : ℝ) / 2) ^ j) 2 := by
    have h := hasSum_coe_mul_geometric_of_norm_lt_one
      (𝕜 := ℝ) (r := (1 : ℝ) / 2) (by norm_num)
    norm_num at h
    exact h
  have htotal : HasSum (fun j : ℕ =>
      (j : ℝ) * ((1 : ℝ) / 2) ^ j + ((1 : ℝ) / 2) ^ j) 4 := by
    convert hmoment.add hasSum_geometric_two using 1
    all_goals norm_num
  have hnonneg : ∀ j : ℕ,
      0 ≤ (j : ℝ) * ((1 : ℝ) / 2) ^ j + ((1 : ℝ) / 2) ^ j := by
    intro j
    positivity
  calc
    (∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ j) =
        ∑ j ∈ Finset.range m,
          ((j : ℝ) * ((1 : ℝ) / 2) ^ j + ((1 : ℝ) / 2) ^ j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      norm_num [div_pow]
      ring
    _ ≤ ∑' j : ℕ,
          ((j : ℝ) * ((1 : ℝ) / 2) ^ j + ((1 : ℝ) / 2) ^ j) :=
      htotal.summable.sum_le_tsum (Finset.range m) (fun j _hj => hnonneg j)
    _ = 4 := htotal.tsum_eq

lemma weightedGeometricSum_mul_le (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    (∑ j ∈ Finset.range m,
      (2 * (j : ℝ) + 4) * (R / (2 : ℝ) ^ j)) ≤ 16 * R := by
  have hsum := weightedGeometricSum_le_four m
  calc
    (∑ j ∈ Finset.range m,
      (2 * (j : ℝ) + 4) * (R / (2 : ℝ) ^ j)) ≤
        ∑ j ∈ Finset.range m,
          4 * (((j + 1 : ℕ) : ℝ)) * (R / (2 : ℝ) ^ j) := by
      apply Finset.sum_le_sum
      intro j _hj
      have hden : 0 ≤ R / (2 : ℝ) ^ j := by positivity
      push_cast
      exact mul_le_mul_of_nonneg_right
        (show 2 * (j : ℝ) + 4 ≤ 4 * ((j : ℝ) + 1) by
          have hj : (0 : ℝ) ≤ j := by positivity
          linarith) hden
    _ = 4 * R * (∑ j ∈ Finset.range m,
          ((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ ≤ 4 * R * 4 := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 16 * R := by ring

lemma cast_dyadicExponentSum_le (R m : ℕ) :
    ((∑ j ∈ Finset.range m, (2 * j + 4) * blockCap R j : ℕ) : ℝ) ≤
      16 * R := by
  calc
    ((∑ j ∈ Finset.range m, (2 * j + 4) * blockCap R j : ℕ) : ℝ) =
        ∑ j ∈ Finset.range m,
          (2 * (j : ℝ) + 4) * ((blockCap R j : ℕ) : ℝ) := by
      push_cast
      rfl
    _ ≤ ∑ j ∈ Finset.range m,
          (2 * (j : ℝ) + 4) * ((R : ℝ) / (2 : ℝ) ^ j) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact mul_le_mul_of_nonneg_left (cast_blockCap_le R j) (by positivity)
    _ ≤ 16 * R := weightedGeometricSum_mul_le m R (by positivity)

lemma cutoff_le_four_sqrt (n : ℕ) (hn : 1 ≤ n) :
    (cutoff n : ℝ) ≤ 4 * Real.sqrt n := by
  have hsqrt_one : (1 : ℝ) ≤ Real.sqrt n := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hnat : (Nat.sqrt n : ℝ) ≤ Real.sqrt n :=
    Real.nat_sqrt_le_real_sqrt
  simp only [cutoff, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  linarith

lemma pow_two_le_exp (M : ℕ) : (2 : ℝ) ^ M ≤ Real.exp M := by
  have hbase : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1
  calc
    (2 : ℝ) ^ M ≤ (Real.exp 1) ^ M := by gcongr
    _ = Real.exp M := by
      rw [← Real.exp_nat_mul]
      norm_num

/-- Affirmative resolution of Erdős Problem 607.  This is the literal
eventual-bound meaning of `F(n) ≤ exp(O(sqrt n))`, with the absolute constant
made explicit. -/
theorem erdos_607 :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (F n : ℝ) ≤ Real.exp (C * Real.sqrt n) := by
  refine ⟨68, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  let E : ℕ := cutoff n + ∑ j ∈ Finset.range (n + 1),
    (2 * j + 4) * blockCap (cutoff n) j
  have hcardNat : F n ≤ 2 ^ E := by
    simpa [E] using F_le_two_pow n
  have hcardReal : (F n : ℝ) ≤ (2 : ℝ) ^ E := by
    exact_mod_cast hcardNat
  have hsum := cast_dyadicExponentSum_le (cutoff n) (n + 1)
  have hcut := cutoff_le_four_sqrt n hn
  have hE : (E : ℝ) ≤ 68 * Real.sqrt n := by
    dsimp [E]
    rw [Nat.cast_add]
    linarith
  calc
    (F n : ℝ) ≤ (2 : ℝ) ^ E := hcardReal
    _ ≤ Real.exp E := pow_two_le_exp E
    _ ≤ Real.exp (68 * Real.sqrt n) := Real.exp_le_exp.mpr hE

end Erdos607

#print axioms Erdos607.erdos_607
