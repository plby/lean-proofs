import Mathlib

open scoped BigOperators Topology
open Filter Finset

namespace Erdos440Liminf

/-! A generic finite nested-selection device. -/

lemma exists_finset_extension {α : Type*} [DecidableEq α]
    {u s : Finset α} {m : ℕ} (hus : u ⊆ s) (hu : u.card ≤ m) (hm : m ≤ s.card) :
    ∃ v : Finset α, u ⊆ v ∧ v ⊆ s ∧ v.card = m := by
  obtain ⟨w, hwsu, hwcard⟩ :=
    Finset.exists_subset_card_eq (s := s \ u) (n := m - u.card) (by
      rw [Finset.card_sdiff, Finset.inter_eq_left.2 hus]
      omega)
  refine ⟨u ∪ w, Finset.subset_union_left, ?_, ?_⟩
  · exact Finset.union_subset hus (hwsu.trans (Finset.sdiff_subset))
  · rw [Finset.card_union_of_disjoint]
    · omega
    · exact Finset.disjoint_left.2 fun x hxu hxw ↦ (Finset.mem_sdiff.1 (hwsu hxw)).2 hxu

section Selection

variable {α : Type*} [DecidableEq α]

structure SelectionSystem (α : Type*) [DecidableEq α] where
  sets : ℕ → Finset α
  sizes : ℕ → ℕ
  sets_mono : ∀ n, sets n ⊆ sets (n + 1)
  sizes_mono : Monotone sizes
  enough : ∀ n, sizes n ≤ (sets n).card

noncomputable def nestedSelection (D : SelectionSystem α) :
    ∀ n, {u : Finset α // u ⊆ D.sets n ∧ u.card = D.sizes n}
  | 0 => by
      classical
      let h := Finset.exists_subset_card_eq (D.enough 0)
      exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2⟩
  | n + 1 => by
      classical
      let u := nestedSelection D n
      let h := exists_finset_extension
        (u.property.1.trans (D.sets_mono n))
        (by simpa [u.property.2] using D.sizes_mono (Nat.le_succ n)) (D.enough (n + 1))
      exact ⟨h.choose, h.choose_spec.2.1, h.choose_spec.2.2⟩

lemma nestedSelection_subset_succ (D : SelectionSystem α) (n : ℕ) :
    (nestedSelection D n : Finset α) ⊆ nestedSelection D (n + 1) := by
  classical
  simp only [nestedSelection]
  let h := exists_finset_extension
    ((nestedSelection D n).property.1.trans (D.sets_mono n))
    (by simpa [(nestedSelection D n).property.2] using D.sizes_mono (Nat.le_succ n))
    (D.enough (n + 1))
  exact h.choose_spec.1

lemma nestedSelection_card (D : SelectionSystem α) (n : ℕ) :
    (nestedSelection D n : Finset α).card = D.sizes n :=
  (nestedSelection D n).property.2

lemma nestedSelection_subset (D : SelectionSystem α) (n : ℕ) :
    (nestedSelection D n : Finset α) ⊆ D.sets n :=
  (nestedSelection D n).property.1

lemma sum_nestedSelection_lower (D : SelectionSystem α) (p : ℕ)
    (weight : α → ℚ) (lower : ℕ → ℚ)
    (hsizes : ∀ n, D.sizes n = p * n)
    (hpoint : ∀ n i, i ∈ D.sets (n + 1) → lower (n + 1) ≤ weight i)
    (R : ℕ) :
    ∑ n ∈ Finset.range R, (p : ℚ) * lower (n + 1) ≤
      ∑ i ∈ (nestedSelection D R : Finset α), weight i := by
  induction R with
  | zero =>
      have hcard : (nestedSelection D 0 : Finset α).card = 0 := by
        rw [nestedSelection_card, hsizes]
        simp
      rw [Finset.card_eq_zero.mp hcard]
      simp
  | succ R ih =>
      let u := (nestedSelection D R : Finset α)
      let v := (nestedSelection D (R + 1) : Finset α)
      have huv : u ⊆ v := nestedSelection_subset_succ D R
      have hdiff_card : (v \ u).card = p := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.2 huv,
          show v.card = D.sizes (R + 1) from nestedSelection_card D (R + 1),
          show u.card = D.sizes R from nestedSelection_card D R, hsizes, hsizes]
        simp [Nat.mul_succ]
      have hdiff_sets : v \ u ⊆ D.sets (R + 1) := by
        exact (Finset.sdiff_subset.trans (nestedSelection_subset D (R + 1)))
      have hnew : (p : ℚ) * lower (R + 1) ≤ ∑ i ∈ v \ u, weight i := by
        have h := Finset.card_nsmul_le_sum (v \ u) weight (lower (R + 1))
          (fun i hi ↦ hpoint R i (hdiff_sets hi))
        simpa [hdiff_card, nsmul_eq_mul] using h
      have hsplit :
          (∑ i ∈ v \ u, weight i) + ∑ i ∈ u, weight i = ∑ i ∈ v, weight i :=
        Finset.sum_sdiff huv
      rw [Finset.sum_range_succ]
      linarith

end Selection

section Lcm

structure IncreasingPositiveSequence where
  val : ℕ → ℕ
  pos : ∀ i, 0 < val i
  strictMono : StrictMono val

def edgeLcm (A : IncreasingPositiveSequence) (i : ℕ) : ℕ :=
  Nat.lcm (A.val i) (A.val (i + 1))

lemma gcd_le_gap (A : IncreasingPositiveSequence) (i : ℕ) :
    Nat.gcd (A.val i) (A.val (i + 1)) ≤ A.val (i + 1) - A.val i := by
  have hai : A.val i ≤ A.val (i + 1) := (A.strictMono (Nat.lt_succ_self i)).le
  apply Nat.le_of_dvd (Nat.sub_pos_of_lt (A.strictMono (Nat.lt_succ_self i)))
  exact (Nat.dvd_sub_iff_left hai (Nat.gcd_dvd_left _ _)).2 (Nat.gcd_dvd_right _ _)

lemma edgeLcm_pos (A : IncreasingPositiveSequence) (i : ℕ) : 0 < edgeLcm A i := by
  exact Nat.lcm_pos (A.pos i) (A.pos (i + 1))

lemma reciprocal_edge_le_drop (A : IncreasingPositiveSequence) (i : ℕ) :
    (1 : ℚ) / edgeLcm A i ≤ 1 / A.val i - 1 / A.val (i + 1) := by
  have hai : (0 : ℚ) < A.val i := by exact_mod_cast A.pos i
  have hais : (0 : ℚ) < A.val (i + 1) := by exact_mod_cast A.pos (i + 1)
  have hl : (0 : ℚ) < edgeLcm A i := by exact_mod_cast edgeLcm_pos A i
  have hg : (Nat.gcd (A.val i) (A.val (i + 1)) : ℚ) ≤
      ((A.val (i + 1) - A.val i : ℕ) : ℚ) := by
    exact_mod_cast gcd_le_gap A i
  have hprod :
      (edgeLcm A i : ℚ) * Nat.gcd (A.val i) (A.val (i + 1)) =
        A.val i * A.val (i + 1) := by
    exact_mod_cast Nat.lcm_mul_gcd (A.val i) (A.val (i + 1))
  calc
    (1 : ℚ) / edgeLcm A i =
        Nat.gcd (A.val i) (A.val (i + 1)) / (A.val i * A.val (i + 1)) := by
      field_simp
      nlinarith
    _ ≤ ((A.val (i + 1) - A.val i : ℕ) : ℚ) /
        (A.val i * A.val (i + 1)) := by
      exact div_le_div_of_nonneg_right hg (by positivity)
    _ = 1 / A.val i - 1 / A.val (i + 1) := by
      rw [Nat.cast_sub (A.strictMono (Nat.lt_succ_self i)).le]
      field_simp

lemma sum_range_drop (u : ℕ → ℚ) (N : ℕ) :
    ∑ i ∈ Finset.range N, (u i - u (i + 1)) = u 0 - u N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

lemma inv_sq_ge_inv_mul_succ (n : ℕ) (hn : 0 < n) :
    (1 : ℚ) / (n * (n + 1)) ≤ 1 / n ^ 2 := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  field_simp
  nlinarith

lemma sum_shifted_inv_sq_lower (m R : ℕ) :
    (1 : ℚ) / (m + 1) - 1 / (m + R + 1) ≤
      ∑ j ∈ Finset.range R, (1 : ℚ) / (m + j + 1) ^ 2 := by
  calc
    (1 : ℚ) / (m + 1) - 1 / (m + R + 1) =
        ∑ j ∈ Finset.range R,
          ((1 : ℚ) / (m + j + 1) - 1 / (m + j + 2)) := by
      induction R with
      | zero => simp
      | succ R ih =>
          rw [Finset.sum_range_succ, ← ih]
          push_cast
          ring
    _ ≤ ∑ j ∈ Finset.range R, (1 : ℚ) / (m + j + 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have h₁ : (0 : ℚ) < m + j + 1 := by positivity
      have h₂ : (0 : ℚ) < m + j + 2 := by positivity
      field_simp
      nlinarith

lemma square_layer_sum_lower (p q m R : ℕ) (hp : 0 < p) (hq : 0 < q) :
    (p : ℚ) / q ^ 2 * ((1 : ℚ) / (m + 1) - 1 / (m + R + 1)) ≤
      ∑ j ∈ Finset.range R, (p : ℚ) / (q * (m + j + 1)) ^ 2 := by
  have hbase := sum_shifted_inv_sq_lower m R
  calc
    (p : ℚ) / q ^ 2 * ((1 : ℚ) / (m + 1) - 1 / (m + R + 1)) ≤
        (p : ℚ) / q ^ 2 *
          (∑ j ∈ Finset.range R, (1 : ℚ) / (m + j + 1) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = ∑ j ∈ Finset.range R, (p : ℚ) / (q * (m + j + 1)) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      field_simp

lemma sum_Ico_drop (u : ℕ → ℚ) {k N : ℕ} (hkn : k ≤ N) :
    ∑ i ∈ Finset.Ico k N, (u i - u (i + 1)) = u k - u N := by
  rw [Finset.sum_Ico_eq_sub _ hkn, sum_range_drop, sum_range_drop]
  ring

lemma sum_Ico_reciprocal_edge_le (A : IncreasingPositiveSequence) {k N : ℕ} (hkn : k ≤ N) :
    ∑ i ∈ Finset.Ico k N, (1 : ℚ) / edgeLcm A i ≤ 1 / A.val k - 1 / A.val N := by
  calc
    ∑ i ∈ Finset.Ico k N, (1 : ℚ) / edgeLcm A i
        ≤ ∑ i ∈ Finset.Ico k N, ((1 : ℚ) / A.val i - 1 / A.val (i + 1)) := by
          exact Finset.sum_le_sum fun i hi ↦ reciprocal_edge_le_drop A i
    _ = 1 / A.val k - 1 / A.val N := sum_Ico_drop (fun i ↦ (1 : ℚ) / A.val i) hkn

lemma sum_Ico_reciprocal_edge_le_inv (A : IncreasingPositiveSequence) {k N : ℕ} (hkn : k ≤ N) :
    ∑ i ∈ Finset.Ico k N, (1 : ℚ) / edgeLcm A i ≤ 1 / A.val k := by
  exact (sum_Ico_reciprocal_edge_le A hkn).trans (by
    have : (0 : ℚ) ≤ 1 / A.val N := by positivity
    linarith)

def goodEdges (A : IncreasingPositiveSequence) (x : ℕ) : Finset ℕ :=
  (Finset.range x).filter fun i ↦ edgeLcm A i ≤ x

def count (A : IncreasingPositiveSequence) (x : ℕ) : ℕ := (goodEdges A x).card

lemma index_succ_le (A : IncreasingPositiveSequence) (i : ℕ) : i + 1 ≤ A.val i := by
  induction i with
  | zero => have := A.pos 0; omega
  | succ i ih =>
      have hstep : A.val i < A.val (i + 1) := A.strictMono (Nat.lt_succ_self i)
      change i + 2 ≤ A.val (i + 1)
      omega

lemma edgeLcm_ge_right (A : IncreasingPositiveSequence) (i : ℕ) :
    A.val (i + 1) ≤ edgeLcm A i := by
  exact Nat.le_of_dvd (edgeLcm_pos A i) (Nat.dvd_lcm_right _ _)

lemma index_lt_of_edgeLcm_le (A : IncreasingPositiveSequence) {i x : ℕ}
    (hix : edgeLcm A i ≤ x) : i < x := by
  have := index_succ_le A (i + 1)
  have := edgeLcm_ge_right A i
  omega

lemma mem_goodEdges_iff (A : IncreasingPositiveSequence) {i x : ℕ} :
    i ∈ goodEdges A x ↔ edgeLcm A i ≤ x := by
  simp only [goodEdges, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨index_lt_of_edgeLcm_le A h, h⟩⟩

lemma goodEdges_mono (A : IncreasingPositiveSequence) {x y : ℕ} (hxy : x ≤ y) :
    goodEdges A x ⊆ goodEdges A y := by
  intro i hi
  rw [mem_goodEdges_iff] at hi ⊢
  exact hi.trans hxy

def tailGoodEdges (A : IncreasingPositiveSequence) (k x : ℕ) : Finset ℕ :=
  goodEdges A x \ Finset.range k

lemma tailGoodEdges_mono (A : IncreasingPositiveSequence) (k : ℕ) {x y : ℕ} (hxy : x ≤ y) :
    tailGoodEdges A k x ⊆ tailGoodEdges A k y :=
  Finset.sdiff_subset_sdiff (goodEdges_mono A hxy) (Subset.rfl)

lemma card_tailGoodEdges_lower (A : IncreasingPositiveSequence) (k x : ℕ) :
    count A x - k ≤ (tailGoodEdges A k x).card := by
  rw [tailGoodEdges, Finset.card_sdiff]
  have hinter : (Finset.range k ∩ goodEdges A x).card ≤ k := by
    simpa using Finset.card_le_card (Finset.inter_subset_left :
      Finset.range k ∩ goodEdges A x ⊆ Finset.range k)
  simp only [count]
  omega

lemma tailGoodEdges_subset_Ico (A : IncreasingPositiveSequence) {k x : ℕ} :
    tailGoodEdges A k x ⊆ Finset.Ico k x := by
  intro i hi
  have hgood := (Finset.mem_sdiff.1 hi).1
  have hk : k ≤ i := by simpa using (Finset.mem_sdiff.1 hi).2
  have hx : i < x := (Finset.mem_range.1 (Finset.mem_filter.1 hgood).1)
  simpa using And.intro hk hx

theorem not_all_square_counts_large (A : IncreasingPositiveSequence)
    {p q n₀ : ℕ} (hq : 0 < q) (hpq : q < p) :
    ¬ ∀ n ≥ n₀, p * n ≤ count A ((q * n) ^ 2) := by
  intro hlarge
  let m := n₀ + q ^ 2 + 1
  let k := p * m
  let threshold : ℕ → ℕ := fun j ↦ (q * (m + j)) ^ 2
  let S : ℕ → Finset ℕ := fun j ↦ tailGoodEdges A k (threshold j)
  have hm₀ : n₀ ≤ m := by dsimp [m]; omega
  have hmpos : 0 < m := by simp [m]
  have hSmono : ∀ j, S j ⊆ S (j + 1) := by
    intro j
    apply tailGoodEdges_mono
    dsimp [threshold]
    apply Nat.pow_le_pow_left
    exact Nat.mul_le_mul_left q (by omega)
  have hScard : ∀ j, p * j ≤ (S j).card := by
    intro j
    have hc := hlarge (m + j) (hm₀.trans (Nat.le_add_right m j))
    have ht := card_tailGoodEdges_lower A k (threshold j)
    calc
      p * j ≤ count A (threshold j) - k := by
        dsimp [threshold, k] at hc ⊢
        rw [Nat.mul_add] at hc
        omega
      _ ≤ (S j).card := ht
  let D : SelectionSystem ℕ := {
    sets := S
    sizes := fun j ↦ p * j
    sets_mono := hSmono
    sizes_mono := fun i j hij ↦ Nat.mul_le_mul_left p hij
    enough := hScard
  }
  let weight : ℕ → ℚ := fun i ↦ 1 / edgeLcm A i
  let lower : ℕ → ℚ := fun j ↦ 1 / (threshold j : ℚ)
  have hp : 0 < p := lt_of_lt_of_le hq hpq.le
  have hpoint : ∀ j i, i ∈ D.sets (j + 1) → lower (j + 1) ≤ weight i := by
    intro j i hi
    have hiS : i ∈ S (j + 1) := hi
    have hLnat : edgeLcm A i ≤ threshold (j + 1) := by
      exact (mem_goodEdges_iff A).1 (Finset.mem_sdiff.1 hiS).1
    have hL : (edgeLcm A i : ℚ) ≤ threshold (j + 1) := by exact_mod_cast hLnat
    dsimp [lower, weight]
    exact one_div_le_one_div_of_le (by exact_mod_cast edgeLcm_pos A i) hL
  let R := p * (m + 1) * (p * m + 1)
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hlayers :
      ∑ j ∈ Finset.range R, (p : ℚ) / (q * (m + j + 1)) ^ 2 ≤
        ∑ i ∈ (nestedSelection D R : Finset ℕ), weight i := by
    have hsel := sum_nestedSelection_lower D p weight lower (fun n ↦ rfl) hpoint R
    calc
      ∑ j ∈ Finset.range R, (p : ℚ) / (q * (m + j + 1)) ^ 2 =
          ∑ j ∈ Finset.range R, (p : ℚ) * lower (j + 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [lower, threshold]
        norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
        field_simp
        ring
      _ ≤ ∑ i ∈ (nestedSelection D R : Finset ℕ), weight i := hsel
  have hselected_subset :
      (nestedSelection D R : Finset ℕ) ⊆ Finset.Ico k (threshold R) := by
    exact (nestedSelection_subset D R).trans (tailGoodEdges_subset_Ico A)
  have hkR : k ≤ threshold R := by
    have hRk : k ≤ R := by
      dsimp [R, k]
      have hm1 : 1 ≤ m + 1 := by omega
      have hpm1 : 1 ≤ p * m + 1 := by omega
      nlinarith
    have hq1 : 1 ≤ q := hq
    have hbase : R ≤ q * (m + R) := by nlinarith
    have hbase1 : 1 ≤ q * (m + R) := by nlinarith
    dsimp [threshold]
    nlinarith
  have hselected_upper :
      ∑ i ∈ (nestedSelection D R : Finset ℕ), weight i ≤ 1 / A.val k := by
    calc
      ∑ i ∈ (nestedSelection D R : Finset ℕ), weight i ≤
          ∑ i ∈ Finset.Ico k (threshold R), (1 : ℚ) / edgeLcm A i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hselected_subset
        intro i hiI hiU
        positivity
      _ ≤ 1 / A.val k := sum_Ico_reciprocal_edge_le_inv A hkR
  have hAk : (1 : ℚ) / A.val k ≤ 1 / (k + 1) := by
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast index_succ_le A k)
  have hsum_lower := square_layer_sum_lower p q m R hp hq
  have hfinite :
      (1 : ℚ) / (k + 1) <
        (p : ℚ) / q ^ 2 * ((1 : ℚ) / (m + 1) - 1 / (m + R + 1)) := by
    have hpq_succ : q + 1 ≤ p := by omega
    have hp2 : q ^ 2 + 1 ≤ p ^ 2 := by
      have hsquare := Nat.pow_le_pow_left hpq_succ 2
      nlinarith
    have hqm : q ^ 2 + 1 ≤ m := by simp [m]
    have hnum : q ^ 2 * (m + 1) + 1 ≤ p * (p * m + 1) := by
      have hmul := Nat.mul_le_mul_right m hp2
      nlinarith
    have hasymp :
        (1 : ℚ) / (k + 1) +
            1 / (q ^ 2 * (m + 1) * (p * m + 1)) ≤
          (p : ℚ) / q ^ 2 * (1 / (m + 1)) := by
      have hnumq :
          (q : ℚ) ^ 2 * (m + 1) + 1 ≤ p * (p * m + 1) := by exact_mod_cast hnum
      dsimp [k]
      norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at hnumq ⊢
      field_simp
      nlinarith
    have herror :
        (p : ℚ) / q ^ 2 * (1 / (m + R + 1)) <
          1 / (q ^ 2 * (m + 1) * (p * m + 1)) := by
      have hRlarge : p * (m + 1) * (p * m + 1) < m + R + 1 := by
        dsimp [R]
        omega
      have hRlargeq :
          (p : ℚ) * (m + 1) * (p * m + 1) < m + R + 1 := by exact_mod_cast hRlarge
      field_simp
      nlinarith
    linarith
  have :
      (p : ℚ) / q ^ 2 * ((1 : ℚ) / (m + 1) - 1 / (m + R + 1)) ≤
        1 / (k + 1) :=
    hsum_lower.trans (hlayers.trans (hselected_upper.trans hAk))
  linarith

theorem frequently_square_count_lt (A : IncreasingPositiveSequence)
    {p q : ℕ} (hq : 0 < q) (hpq : q < p) :
    ∀ n₀, ∃ n ≥ n₀, count A ((q * n) ^ 2) < p * n := by
  intro n₀
  by_contra h
  push Not at h
  exact not_all_square_counts_large A hq hpq h

noncomputable def normalizedCount (A : IncreasingPositiveSequence) (x : ℕ) : ℝ :=
  (count A x : ℝ) / Real.sqrt x

lemma normalizedCount_nonneg (A : IncreasingPositiveSequence) (x : ℕ) :
    0 ≤ normalizedCount A x := by
  exact div_nonneg (by positivity) (Real.sqrt_nonneg _)

theorem frequently_normalizedCount_le_rat (A : IncreasingPositiveSequence)
    (q : ℕ) (hq : 0 < q) :
    ∃ᶠ x in Filter.atTop,
      normalizedCount A x ≤ ((q + 1 : ℕ) : ℝ) / q := by
  rw [Filter.frequently_atTop]
  intro X
  obtain ⟨n, hn, hcount⟩ :=
    frequently_square_count_lt A hq (Nat.lt_succ_self q) (max X 1)
  let x := (q * n) ^ 2
  have hnX : X ≤ n := (le_max_left X 1).trans hn
  have hnpos : 0 < n := lt_of_lt_of_le (by omega : 0 < max X 1) hn
  have hqn : 0 < q * n := Nat.mul_pos hq hnpos
  have hXx : X ≤ x := by
    dsimp [x]
    have hnqn : n ≤ q * n := by nlinarith
    have hqnpow : q * n ≤ (q * n) ^ 2 := by nlinarith
    omega
  refine ⟨x, hXx, ?_⟩
  have hxcast : (x : ℝ) = ((q * n : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast rfl
  have hsqrt : Real.sqrt x = (q * n : ℕ) := by
    rw [hxcast, Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity
  have hcount_real : (count A x : ℝ) ≤ ((q + 1) * n : ℕ) := by
    exact_mod_cast (Nat.le_of_lt hcount)
  rw [normalizedCount, hsqrt]
  calc
    (count A x : ℝ) / (q * n : ℕ) ≤ (((q + 1) * n : ℕ) : ℝ) / (q * n : ℕ) := by
      exact div_le_div_of_nonneg_right hcount_real (by positivity)
    _ = ((q + 1 : ℕ) : ℝ) / q := by
      push_cast
      field_simp

theorem liminf_normalizedCount_le_one (A : IncreasingPositiveSequence) :
    Filter.atTop.liminf (normalizedCount A) ≤ 1 := by
  by_contra hle
  have hlt : (1 : ℝ) < Filter.atTop.liminf (normalizedCount A) := lt_of_not_ge hle
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
  let q := n + 1
  have hq : 0 < q := by simp [q]
  have hfreq := frequently_normalizedCount_le_rat A q hq
  have hbounded :
      IsBoundedUnder (fun x y : ℝ ↦ x ≥ y) Filter.atTop (normalizedCount A) := by
    refine ⟨0, ?_⟩
    simpa only [Filter.eventually_map] using
      (Filter.Eventually.of_forall (normalizedCount_nonneg A))
  have hlim :
      Filter.atTop.liminf (normalizedCount A) ≤ ((q + 1 : ℕ) : ℝ) / q :=
    Filter.liminf_le_of_frequently_le hfreq hbounded
  have hrat : ((q + 1 : ℕ) : ℝ) / q < Filter.atTop.liminf (normalizedCount A) := by
    have hqreal : (0 : ℝ) < q := by positivity
    have hrewrite : ((q + 1 : ℕ) : ℝ) / q = 1 + 1 / (n + 1 : ℝ) := by
      dsimp [q]
      push_cast
      field_simp
    rw [hrewrite]
    linarith
  exact (not_lt_of_ge hlim) hrat

end Lcm

end Erdos440Liminf
