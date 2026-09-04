/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field

/-!
# Uniform density and sections of finite cubes

This file contains the elementary finite-probability layer used by the
density-increment proof of density Hales--Jewett for three letters.  It is
deliberately independent of the unfinished Erdős 171 density framework.
All densities and averages take values in `ℝ`, and every identity below is
an exact identity between finite sums.
-/

open scoped BigOperators

namespace Erdos185.DHJ

section FiniteProbability

variable {X Y : Type*}

/-- Uniform average of a real-valued function on a finite type. -/
noncomputable def average [Fintype X] (f : X → ℝ) : ℝ :=
  𝔼 x, f x

/-- Uniform density of a finset in its ambient finite type. -/
noncomputable def density [Fintype X] (A : Finset X) : ℝ :=
  (A.card : ℝ) / Fintype.card X

@[simp] theorem average_eq_sum_div_card [Fintype X] (f : X → ℝ) :
    average f = (∑ x, f x) / Fintype.card X := by
  simp [average, Fintype.expect_eq_sum_div_card]

@[simp] theorem density_eq_card_div_card [Fintype X] (A : Finset X) :
    density A = (A.card : ℝ) / Fintype.card X :=
  rfl

@[simp] theorem density_empty [Fintype X] : density (∅ : Finset X) = 0 := by
  simp [density]

@[simp] theorem density_univ [Fintype X] [Nonempty X] :
    density (Finset.univ : Finset X) = 1 := by
  simp [density]

theorem density_nonneg [Fintype X] (A : Finset X) : 0 ≤ density A := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem density_le_one [Fintype X] (A : Finset X) : density A ≤ 1 := by
  cases isEmpty_or_nonempty X with
  | inl hX =>
      let := hX
      have hA : A = ∅ := by
        ext x
        exact isEmptyElim x
      simp [hA]
  | inr hX =>
      let := hX
      rw [density, div_le_one (by positivity)]
      exact_mod_cast Finset.card_le_univ A

theorem density_mono [Fintype X] {A B : Finset X} (hAB : A ⊆ B) :
    density A ≤ density B := by
  unfold density
  gcongr

/-- Density is preserved by an equivalence of finite ambient types. -/
theorem density_map_equiv [Fintype X] [Fintype Y]
    (e : X ≃ Y) (A : Finset X) :
    density (A.map e.toEmbedding) = density A := by
  simp [density, Fintype.card_congr e]

theorem average_const [Fintype X] [Nonempty X] (c : ℝ) :
    average (fun _ : X ↦ c) = c := by
  simp [average, Fintype.expect_const]

theorem average_add [Fintype X] (f g : X → ℝ) :
    average (fun x ↦ f x + g x) = average f + average g := by
  simp [average, Finset.expect_add_distrib]

theorem average_sub [Fintype X] (f g : X → ℝ) :
    average (fun x ↦ f x - g x) = average f - average g := by
  simp [average, Finset.expect_sub_distrib]

theorem average_mul_const [Fintype X] (f : X → ℝ) (c : ℝ) :
    average (fun x ↦ f x * c) = average f * c := by
  simp [average, Finset.expect_mul]

theorem average_const_mul [Fintype X] (c : ℝ) (f : X → ℝ) :
    average (fun x ↦ c * f x) = c * average f := by
  simp [average, Finset.mul_expect]

theorem average_mono [Fintype X] {f g : X → ℝ}
    (hfg : ∀ x, f x ≤ g x) : average f ≤ average g := by
  simp only [average_eq_sum_div_card]
  gcongr with x
  exact hfg x

theorem average_nonneg [Fintype X] {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ average f := by
  simpa only [average, Finset.expect_const_zero] using
    average_mono (f := fun _ : X ↦ 0) (g := f) hf

theorem average_le_const [Fintype X] [Nonempty X] {f : X → ℝ} {c : ℝ}
    (hf : ∀ x, f x ≤ c) : average f ≤ c := by
  simpa [average_const] using
    average_mono (f := f) (g := fun _ ↦ c) hf

theorem const_le_average [Fintype X] [Nonempty X] {f : X → ℝ} {c : ℝ}
    (hf : ∀ x, c ≤ f x) : c ≤ average f := by
  simpa [average_const] using
    average_mono (f := fun _ ↦ c) (g := f) hf

/-- Some value of a function is at least its uniform average. -/
theorem exists_average_le [Fintype X] [Nonempty X] (f : X → ℝ) :
    ∃ x, average f ≤ f x := by
  by_contra! h
  have hsum : (∑ x, f x) < ∑ _x : X, average f :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun x _ ↦ h x)
  have hcard : (Fintype.card X : ℝ) ≠ 0 := by positivity
  rw [average_eq_sum_div_card, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  have hcancel : (Fintype.card X : ℝ) *
      ((∑ x, f x) / Fintype.card X) = ∑ x, f x := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hcard
  rw [hcancel] at hsum
  exact hsum.false

/-- Some value of a function is at most its uniform average. -/
theorem exists_le_average [Fintype X] [Nonempty X] (f : X → ℝ) :
    ∃ x, f x ≤ average f := by
  obtain ⟨x, hx⟩ := exists_average_le (fun x ↦ -f x)
  have hneg : average (fun x ↦ -f x) = -average f := by
    simp [average_eq_sum_div_card]
    ring
  exact ⟨x, by rw [hneg] at hx; linarith⟩

theorem exists_ge_of_le_average [Fintype X] [Nonempty X]
    {f : X → ℝ} {c : ℝ} (hc : c ≤ average f) :
    ∃ x, c ≤ f x := by
  obtain ⟨x, hx⟩ := exists_average_le f
  exact ⟨x, hc.trans hx⟩

theorem exists_gt_of_lt_average [Fintype X] [Nonempty X]
    {f : X → ℝ} {c : ℝ} (hc : c < average f) :
    ∃ x, c < f x := by
  obtain ⟨x, hx⟩ := exists_average_le f
  exact ⟨x, hc.trans_le hx⟩

/-- The fibre of a finset in a product after fixing its first coordinate. -/
noncomputable def fiber [Fintype Y] (A : Finset (X × Y)) (x : X) : Finset Y := by
  classical
  exact Finset.univ.filter fun y ↦ (x, y) ∈ A

@[simp] theorem mem_fiber [Fintype Y] (A : Finset (X × Y)) (x : X) (y : Y) :
    y ∈ fiber A x ↔ (x, y) ∈ A := by
  classical
  simp [fiber]

/-- Exact fibrewise counting for a subset of a finite product. -/
theorem card_eq_sum_card_fiber [Fintype X] [Fintype Y]
    (A : Finset (X × Y)) : A.card = ∑ x, (fiber A x).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (s := A) (t := Finset.univ) (f := Prod.fst) (by simp)]
  apply Finset.sum_congr rfl
  intro x _
  refine Finset.card_bij (fun p _ ↦ p.2) ?_ ?_ ?_
  · intro p hp
    have hp' := Finset.mem_filter.1 hp
    apply (mem_fiber A x p.2).2
    rw [← hp'.2]
    simpa using hp'.1
  · intro p hp q hq hpq
    apply Prod.ext
    · have hp' := (Finset.mem_filter.1 hp).2
      have hq' := (Finset.mem_filter.1 hq).2
      simpa [hp', hq']
    · exact hpq
  · intro y hy
    refine ⟨(x, y), ?_, rfl⟩
    have hy' : (x, y) ∈ A := (mem_fiber A x y).1 hy
    simp [hy']

/-- Density in a product is the average of the densities of its fibres. -/
theorem density_eq_average_fiber [Fintype X] [Fintype Y]
    (A : Finset (X × Y)) :
    density A = average fun x ↦ density (fiber A x) := by
  cases isEmpty_or_nonempty X with
  | inl hX =>
      let := hX
      simp [density_eq_card_div_card, average_eq_sum_div_card]
  | inr hX =>
      let := hX
      cases isEmpty_or_nonempty Y with
      | inl hY =>
          let := hY
          simp [density_eq_card_div_card, average_eq_sum_div_card]
      | inr hY =>
          let := hY
          rw [density_eq_card_div_card, average_eq_sum_div_card]
          rw [card_eq_sum_card_fiber]
          simp only [density_eq_card_div_card]
          rw [Fintype.card_prod]
          push_cast
          rw [← Finset.sum_div]
          have hXcard : (Fintype.card X : ℝ) ≠ 0 := by positivity
          have hYcard : (Fintype.card Y : ℝ) ≠ 0 := by positivity
          field_simp

/-- A product set has a fibre at least as dense as the whole set. -/
theorem exists_fiber_density_ge [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (A : Finset (X × Y)) :
    ∃ x, density A ≤ density (fiber A x) := by
  rw [density_eq_average_fiber]
  exact exists_average_le _

/-- The indicator of a finset has average equal to its density. -/
theorem average_indicator [Fintype X] [DecidableEq X] (A : Finset X) :
    average (fun x ↦ if x ∈ A then (1 : ℝ) else 0) = density A := by
  classical
  simp [average_eq_sum_div_card, density_eq_card_div_card, Finset.sum_boole]

/-- The exact average of a function which is constant on a finset and its complement. -/
theorem average_piecewise_const [Fintype X] [Nonempty X] [DecidableEq X]
    (A : Finset X) (a b : ℝ) :
    average (fun x ↦ if x ∈ A then a else b) =
      density A * a + (1 - density A) * b := by
  let ι : X → ℝ := fun x ↦ if x ∈ A then 1 else 0
  have hpoint : (fun x ↦ if x ∈ A then a else b) =
      fun x ↦ ι x * a + (1 - ι x) * b := by
    funext x
    simp only [ι]
    split <;> ring
  rw [hpoint, average_add, average_mul_const, average_mul_const,
    average_sub, average_const, average_indicator]

/-- The set where a real-valued function is at least a prescribed threshold. -/
noncomputable def superlevel [Fintype X] (f : X → ℝ) (c : ℝ) : Finset X := by
  classical
  exact Finset.univ.filter fun x ↦ c ≤ f x

@[simp] theorem mem_superlevel [Fintype X] (f : X → ℝ) (c : ℝ) (x : X) :
    x ∈ superlevel f c ↔ c ≤ f x := by
  classical
  simp [superlevel]

/-- Quantitative averaging.  If `f ≤ B` and `μ ≤ average f`, the set on
which `f ≥ c` has density at least `(μ-c)/(B-c)`. -/
theorem density_superlevel_ge [Fintype X] [Nonempty X] [DecidableEq X]
    (f : X → ℝ) {mu c B : ℝ} (havg : mu ≤ average f)
    (hub : ∀ x, f x ≤ B) (hcB : c < B) :
    (mu - c) / (B - c) ≤ density (superlevel f c) := by
  have hpoint : ∀ x, f x ≤
      (if x ∈ superlevel f c then B else c) := by
    intro x
    by_cases hx : x ∈ superlevel f c
    · simpa [hx] using hub x
    · simp only [hx, if_false]
      exact le_of_lt (not_le.1 (by simpa using hx))
  have havg' : average f ≤ density (superlevel f c) * B +
      (1 - density (superlevel f c)) * c := by
    calc
      average f ≤ average (fun x ↦ if x ∈ superlevel f c then B else c) :=
        average_mono hpoint
      _ = density (superlevel f c) * B +
          (1 - density (superlevel f c)) * c :=
        average_piecewise_const (superlevel f c) B c
  rw [div_le_iff₀ (sub_pos.2 hcB)]
  nlinarith

/-- Prefixes whose corresponding fibre has density at least `c`. -/
noncomputable def largeFibers [Fintype X] [Fintype Y]
    (A : Finset (X × Y)) (c : ℝ) : Finset X :=
  superlevel (fun x ↦ density (fiber A x)) c

@[simp] theorem mem_largeFibers [Fintype X] [Fintype Y]
    (A : Finset (X × Y)) (c : ℝ) (x : X) :
    x ∈ largeFibers A c ↔ c ≤ density (fiber A x) := by
  simp [largeFibers]

/-- Quantitative large-fibre principle. -/
theorem density_largeFibers_ge [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] [DecidableEq X]
    (A : Finset (X × Y)) {mu c : ℝ} (hA : mu ≤ density A) (hc : c < 1) :
    (mu - c) / (1 - c) ≤ density (largeFibers A c) := by
  rw [density_eq_average_fiber] at hA
  simpa only [largeFibers] using
    density_superlevel_ge (fun x ↦ density (fiber A x)) hA
      (fun x ↦ density_le_one _) hc

/-- Half-threshold version: a `[0,1]`-valued function of average at least
`δ` is at least `δ/2` on a set of density at least `δ/2`. -/
theorem half_le_density_superlevel [Fintype X] [Nonempty X] [DecidableEq X]
    (f : X → ℝ) {delta : ℝ} (hdelta : 0 ≤ delta)
    (havg : delta ≤ average f) (hub : ∀ x, f x ≤ 1) :
    delta / 2 ≤ density (superlevel f (delta / 2)) := by
  have hmain := density_superlevel_ge f havg hub
    (show delta / 2 < 1 by
      have hdelta1 : delta ≤ 1 := havg.trans (average_le_const hub)
      linarith)
  have hdens0 := density_nonneg (superlevel f (delta / 2))
  have hdens1 := density_le_one (superlevel f (delta / 2))
  rw [div_le_iff₀ (show 0 < (1 : ℝ) - delta / 2 by
    have hdelta1 : delta ≤ 1 := havg.trans (average_le_const hub)
    linarith)] at hmain
  nlinarith

/-- Half-threshold form specialized to product fibres. -/
theorem half_le_density_largeFibers [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] [DecidableEq X]
    (A : Finset (X × Y)) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hA : delta ≤ density A) :
    delta / 2 ≤ density (largeFibers A (delta / 2)) := by
  rw [density_eq_average_fiber] at hA
  simpa only [largeFibers] using
    half_le_density_superlevel (fun x ↦ density (fiber A x)) hdelta hA
      (fun x ↦ density_le_one _)

end FiniteProbability

section CubeSections

/-- A generic finite word, kept separate from the ternary `Erdos185.Word`. -/
abbrev Cube (k n : ℕ) := Erdos171.Word k n

/-- Split a word into an initial block and a final block. -/
def wordSplitEquiv (k m r : ℕ) : Cube k (m + r) ≃ Cube k m × Cube k r :=
  (Equiv.piCongrLeft (fun _ : Fin (m + r) ↦ Fin k) finSumFinEquiv).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin r) (Fin k))

@[simp] theorem wordSplitEquiv_apply_fst (k m r : ℕ) (w : Cube k (m + r))
    (i : Fin m) : (wordSplitEquiv k m r w).1 i = w (Fin.castAdd r i) := by
  simp [wordSplitEquiv]

@[simp] theorem wordSplitEquiv_apply_snd (k m r : ℕ) (w : Cube k (m + r))
    (i : Fin r) : (wordSplitEquiv k m r w).2 i = w (Fin.natAdd m i) := by
  simp [wordSplitEquiv]

/-- The product-coordinate form of a set in a cube split after `m` coordinates. -/
noncomputable def splitFinset {k m r : ℕ} (A : Finset (Cube k (m + r))) :
    Finset (Cube k m × Cube k r) :=
  A.map (wordSplitEquiv k m r).toEmbedding

@[simp] theorem mem_splitFinset {k m r : ℕ} (A : Finset (Cube k (m + r)))
    (x : Cube k m) (y : Cube k r) :
    (x, y) ∈ splitFinset A ↔ (wordSplitEquiv k m r).symm (x, y) ∈ A := by
  classical
  simp [splitFinset]

/-- The section `A_x` obtained by fixing the first `m` coordinates to `x`. -/
noncomputable def prefixSection {k m r : ℕ} (A : Finset (Cube k (m + r)))
    (x : Cube k m) : Finset (Cube k r) :=
  fiber (splitFinset A) x

@[simp] theorem mem_prefixSection {k m r : ℕ}
    (A : Finset (Cube k (m + r))) (x : Cube k m) (y : Cube k r) :
    y ∈ prefixSection A x ↔ (wordSplitEquiv k m r).symm (x, y) ∈ A := by
  simp [prefixSection]

@[simp] theorem card_splitFinset {k m r : ℕ} (A : Finset (Cube k (m + r))) :
    (splitFinset A).card = A.card := by
  simp [splitFinset]

/-- Exact counting by prefix sections. -/
theorem card_eq_sum_card_prefixSection {k m r : ℕ}
    (A : Finset (Cube k (m + r))) :
    A.card = ∑ x : Cube k m, (prefixSection A x).card := by
  rw [← card_splitFinset A, card_eq_sum_card_fiber]
  rfl

/-- Density of a cube set is the average of the densities of all its prefix sections. -/
theorem density_eq_average_prefixSection {k m r : ℕ}
    (A : Finset (Cube k (m + r))) :
    density A = average fun x : Cube k m ↦ density (prefixSection A x) := by
  have hmap : density (splitFinset A) = density A :=
    density_map_equiv (wordSplitEquiv k m r) A
  rw [← hmap, density_eq_average_fiber]
  rfl

/-- A nonempty-alphabet cube has a prefix section at least as dense as the set. -/
theorem exists_prefixSection_density_ge {k m r : ℕ} (hk : 0 < k)
    (A : Finset (Cube k (m + r))) :
    ∃ x : Cube k m, density A ≤ density (prefixSection A x) := by
  let : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  rw [density_eq_average_prefixSection]
  exact exists_average_le _

/-- Prefixes supporting a section of density at least `c`. -/
noncomputable def largePrefixSections {k m r : ℕ}
    (A : Finset (Cube k (m + r))) (c : ℝ) : Finset (Cube k m) :=
  superlevel (fun x ↦ density (prefixSection A x)) c

@[simp] theorem mem_largePrefixSections {k m r : ℕ}
    (A : Finset (Cube k (m + r))) (c : ℝ) (x : Cube k m) :
    x ∈ largePrefixSections A c ↔ c ≤ density (prefixSection A x) := by
  simp [largePrefixSections]

/-- Quantitative density of the collection of large prefix sections. -/
theorem density_largePrefixSections_ge {k m r : ℕ} (hk : 0 < k)
    (A : Finset (Cube k (m + r))) {mu c : ℝ}
    (hA : mu ≤ density A) (hc : c < 1) :
    (mu - c) / (1 - c) ≤ density (largePrefixSections A c) := by
  let : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  rw [density_eq_average_prefixSection] at hA
  simpa only [largePrefixSections] using
    density_superlevel_ge (fun x ↦ density (prefixSection A x)) hA
      (fun x ↦ density_le_one _) hc

/-- Half-threshold form for prefix sections. -/
theorem half_le_density_largePrefixSections {k m r : ℕ} (hk : 0 < k)
    (A : Finset (Cube k (m + r))) {delta : ℝ}
    (hdelta : 0 ≤ delta) (hA : delta ≤ density A) :
    delta / 2 ≤ density (largePrefixSections A (delta / 2)) := by
  let : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  rw [density_eq_average_prefixSection] at hA
  simpa only [largePrefixSections] using
    half_le_density_superlevel (fun x ↦ density (prefixSection A x)) hdelta hA
      (fun x ↦ density_le_one _)

end CubeSections

end Erdos185.DHJ
