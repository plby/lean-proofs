/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos255.Baire
import ErdosProblems.Erdos255.NoUniform

/-!
# Erdős Problem 255

For every sequence in `[0,1]`, some interval has unbounded discrepancy.  We
prove the stronger form established by Schmidt: the interval may be chosen to
be an anchored half-open interval `[0,x)`.

The proof has three parts.  `FiniteRoth.lean` proves a finite two-dimensional
Roth inequality by exact sums of dyadic Haar functions.  `NoUniform.lean`
deduces that no sequence in `[0,1)` has uniformly bounded anchored
discrepancy.  `Baire.lean` localizes a hypothetical pointwise bound by the
Baire category theorem, extends it one-sidedly across the countable set of
sequence values, and rescales the resulting local subsequence.  The detailed
mathematical proof and Leanization map are in `tex/255.tex`.

The interval convention is half open.  This is harmless for the problem and,
more importantly, the theorem below explicitly counts membership in `[0,x)`;
there is no endpoint-convention abstraction hidden in the statement.
-/

open Filter Finset Set
open scoped BigOperators Topology

namespace Erdos255

/-- Discrepancy of the first `N` terms in the actual interval `[0,x)`. -/
noncomputable def anchoredDiscrepancy (z : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  (((range N).filter fun n ↦ z n ∈ Ico (0 : ℝ) x).card : ℝ) - N * x

lemma baire_prefixCount_eq (z : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    Erdos255Baire.prefixCount z N x = prefixCount z N x := by
  rw [Erdos255Baire.prefixCount, Nat.count_eq_card_filter_range, prefixCount]

lemma baire_discrepancy_eq (z : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    Erdos255Baire.discrepancy z N x = starDisc z N x := by
  unfold Erdos255Baire.discrepancy starDisc
  rw [baire_prefixCount_eq]

lemma anchoredDiscrepancy_eq_starDisc (z : ℕ → ℝ)
    (hz : ∀ n, z n ∈ Icc (0 : ℝ) 1) (N : ℕ) (x : ℝ) :
    anchoredDiscrepancy z N x = starDisc z N x := by
  unfold anchoredDiscrepancy starDisc prefixCount
  congr 2
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ico]
  constructor
  · rintro ⟨hn, hzero, hx⟩
    exact ⟨hn, hx⟩
  · rintro ⟨hn, hx⟩
    exact ⟨hn, (hz n).1, hx⟩

/-- The Baire theorem applies because the finite Roth argument rules out a
uniformly bounded star discrepancy after every local rescaling. -/
lemma noUniformStarDiscrepancy : Erdos255Baire.NoUniformStarDiscrepancy := by
  intro w hw C
  obtain ⟨N, x, hx, hlarge⟩ := no_uniform_star_discrepancy w hw C
  refine ⟨N, x, hx, ?_⟩
  rwa [baire_discrepancy_eq]

/-- Quantitative form used to obtain the limsup statement: an anchored
interval `[0,x)` has discrepancy exceeding every prescribed real bound. -/
theorem erdos_255_unbounded (z : ℕ → ℝ) (hz : ∀ n, z n ∈ Icc (0 : ℝ) 1) :
    ∃ x ∈ Icc (0 : ℝ) 1, ∀ C : ℝ, ∃ N : ℕ,
      C < |anchoredDiscrepancy z N x| := by
  obtain ⟨x, hx, hub⟩ :=
    Erdos255Baire.unbounded_endpoint_of_no_uniform noUniformStarDiscrepancy z
  refine ⟨x, hx, ?_⟩
  intro C
  obtain ⟨N, hN⟩ := hub C
  refine ⟨N, ?_⟩
  rwa [anchoredDiscrepancy_eq_starDisc z hz,
    ← baire_discrepancy_eq]

private lemma frequently_gt_of_unbounded (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (h : ∀ C : ℝ, ∃ n, C < f n) (C : ℝ) : ∃ᶠ n in atTop, C < f n := by
  rw [frequently_atTop]
  intro a
  obtain ⟨n, hn⟩ := h (max C (∑ i ∈ range a, f i))
  refine ⟨n, ?_, lt_of_le_of_lt (le_max_left _ _) hn⟩
  by_contra hna
  have hnmem : n ∈ range a := by simp_all
  have hnle : f n ≤ ∑ i ∈ range a, f i :=
    single_le_sum (fun i _ ↦ hf i) hnmem
  exact (not_lt_of_ge hnle) (lt_of_le_of_lt (le_max_right _ _) hn)

/-- An unbounded nonnegative real sequence has extended-real limsup `⊤`. -/
private lemma limsup_coe_eq_top_of_unbounded (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (h : ∀ C : ℝ, ∃ n, C < f n) :
    atTop.limsup (fun n ↦ (f n : EReal)) = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro C
  have hfreq : ∃ᶠ n in atTop, (C + 1 : EReal) ≤ (f n : EReal) := by
    rw [frequently_atTop]
    intro a
    obtain ⟨n, han, hn⟩ := (frequently_atTop.mp
      (frequently_gt_of_unbounded f hf h (C + 1))) a
    refine ⟨n, han, ?_⟩
    norm_cast
    linarith
  refine lt_of_lt_of_le ?_ (le_limsup_of_frequently_le' hfreq)
  norm_cast
  linarith

/-- **Erdős Problem 255 (Schmidt).**  For every sequence in `[0,1]`, there
is an interval `[0,x) ⊆ [0,1]` for which the limsup of the absolute
discrepancy is infinite. -/
theorem erdos_255 (z : ℕ → ℝ) (hz : ∀ n, z n ∈ Icc (0 : ℝ) 1) :
    ∃ x ∈ Icc (0 : ℝ) 1,
      Ico (0 : ℝ) x ⊆ Icc (0 : ℝ) 1 ∧
      atTop.limsup (fun N ↦ ((|anchoredDiscrepancy z N x| : ℝ) : EReal)) = ⊤ := by
  obtain ⟨x, hx, hub⟩ := erdos_255_unbounded z hz
  refine ⟨x, hx, ?_, limsup_coe_eq_top_of_unbounded
    (fun N ↦ |anchoredDiscrepancy z N x|) (fun _ ↦ abs_nonneg _) hub⟩
  intro y hy
  exact ⟨hy.1, hy.2.le.trans hx.2⟩

#print axioms Erdos255.erdos_255

end Erdos255
