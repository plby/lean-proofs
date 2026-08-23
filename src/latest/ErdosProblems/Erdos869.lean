/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 869.
https://www.erdosproblems.com/forum/thread/869

Informal authors:
- Daniel Larsen

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos869.md
-/
/-
This file formalizes Daniel Larsen's negative resolution of Erdős Problem 869.

Mathematical proof and Leanization notes: ../../../tex/869.tex
Primary source: D. Larsen, "Three Questions of Erdős--Nathanson on
Asymptotic Bases of Order 2", arXiv:2603.03472v1 (2026), Sections 2 and 4.
-/

import ErdosProblems.Erdos868
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Probability.Distributions.Uniform

open Filter
open scoped Pointwise

namespace Erdos869

/-- An asymptotic additive basis of order two. -/
abbrev IsBasis2 (A : Set ℕ) : Prop := A.IsAsymptoticAddBasisOfOrder 2

/-- Minimality in the one-element deletion form used in Problem 869. -/
def IsMinimalBasis2 (A : Set ℕ) : Prop :=
  IsBasis2 A ∧ ∀ a ∈ A, ¬ IsBasis2 (A \ {a})

/-- The exact deterministic output required from Larsen's construction. -/
structure CounterexampleCertificate where
  left : Set ℕ
  right : Set ℕ
  disjoint : Disjoint left right
  left_basis : IsBasis2 left
  right_basis : IsBasis2 right
  every_subbasis_erasable :
    ∀ D ⊆ left ∪ right, IsBasis2 D → ∀ d ∈ D, IsBasis2 (D \ {d})

lemma basis2_nonempty {A : Set ℕ} (hA : IsBasis2 A) : A.Nonempty := by
  change A.IsAsymptoticAddBasisOfOrder 2 at hA
  rw [Set.isAsymptoticAddBasisOfOrder_iff_atTop] at hA
  obtain ⟨n, hn⟩ := hA.exists
  have hn' : n ∈ A + A := by simpa [two_nsmul] using hn
  rcases hn' with ⟨a, ha, _b, _hb, _⟩
  exact ⟨a, ha⟩

lemma CounterexampleCertificate.no_minimal_subbasis
    (c : CounterexampleCertificate) :
    ¬ ∃ D ⊆ c.left ∪ c.right, IsMinimalBasis2 D := by
  rintro ⟨D, hDsub, hDbasis, hDmin⟩
  obtain ⟨d, hd⟩ := basis2_nonempty hDbasis
  exact hDmin d hd (c.every_subbasis_erasable D hDsub hDbasis d hd)

lemma CounterexampleCertificate.refutes_problem
    (c : CounterexampleCertificate) :
    ¬ (∀ (A₁ A₂ : Set ℕ), Disjoint A₁ A₂ → IsBasis2 A₁ → IsBasis2 A₂ →
      ∃ D ⊆ A₁ ∪ A₂, IsMinimalBasis2 D) := by
  intro h
  exact c.no_minimal_subbasis
    (h c.left c.right c.disjoint c.left_basis c.right_basis)

/-! ## A deterministic interface for the block construction -/

/-- The exceptional sums in Larsen's construction. -/
def scale (k : ℕ) : ℕ := 4 ^ (k + 1)

def exceptional : Set ℕ := {n | ∃ k, n = scale (k + 1)}

lemma scale_pos (k : ℕ) : 0 < scale k := pow_pos (by decide) _

lemma scale_ne_zero (k : ℕ) : scale k ≠ 0 := (scale_pos k).ne'

lemma scale_succ (k : ℕ) : scale (k + 1) = 4 * scale k := by
  simp [scale, pow_succ, mul_comm]

lemma scale_strictMono : StrictMono scale := by
  intro i j hij
  exact pow_lt_pow_right₀ (by decide) (Nat.add_lt_add_right hij 1)

/-- A certificate split into ordinary sums and finitely many fragile exceptional sums.

The ordinary field says that every element of every subbasis can be erased away from
the scale points.  The exceptional field says that a fixed element is a summand of only
finitely many scale points. -/
structure BlockCertificate where
  left : Set ℕ
  right : Set ℕ
  disjoint : Disjoint left right
  left_basis : IsBasis2 left
  right_basis : IsBasis2 right
  ordinary_survives :
    ∀ D ⊆ left ∪ right, IsBasis2 D → ∀ d ∈ D,
      ∀ᶠ n : ℕ in atTop, n ∉ exceptional → n ∈ 2 • (D \ {d})
  exceptional_summands_finite :
    ∀ d ∈ left ∪ right,
      {n : ℕ | n ∈ exceptional ∧ ∃ a ∈ left ∪ right, d + a = n}.Finite

lemma BlockCertificate.every_subbasis_erasable (c : BlockCertificate)
    (D : Set ℕ) (hDsub : D ⊆ c.left ∪ c.right) (hD : IsBasis2 D)
    (d : ℕ) (hd : d ∈ D) : IsBasis2 (D \ {d}) := by
  change D.IsAsymptoticAddBasisOfOrder 2 at hD
  change (D \ {d}).IsAsymptoticAddBasisOfOrder 2
  rw [Set.isAsymptoticAddBasisOfOrder_iff_atTop] at hD ⊢
  have hescape : ∀ᶠ n : ℕ in atTop,
      n ∉ {n : ℕ | n ∈ exceptional ∧
        ∃ a ∈ c.left ∪ c.right, d + a = n} := by
    rw [← Nat.cofinite_eq_atTop]
    exact (c.exceptional_summands_finite d (hDsub hd)).compl_mem_cofinite
  filter_upwards [hD, c.ordinary_survives D hDsub
    (Set.isAsymptoticAddBasisOfOrder_iff_atTop.2 hD) d hd, hescape]
      with n hnD hnordinary hnescape
  by_cases hnexc : n ∈ exceptional
  · have hnDD : n ∈ D + D := by simpa [two_nsmul] using hnD
    rcases hnDD with ⟨a, haD, b, hbD, hab⟩
    have haA := hDsub haD
    have hbA := hDsub hbD
    have had : a ≠ d := by
      intro had
      subst a
      exact hnescape ⟨hnexc, b, hbA, hab⟩
    have hbd : b ≠ d := by
      intro hbd
      subst b
      exact hnescape ⟨hnexc, a, haA, by simpa [add_comm] using hab⟩
    have hn' : n ∈ (D \ {d}) + (D \ {d}) :=
      ⟨a, ⟨haD, by simpa using had⟩,
       b, ⟨hbD, by simpa using hbd⟩, hab⟩
    simpa [two_nsmul] using hn'
  · exact hnordinary hnexc

def BlockCertificate.toCounterexampleCertificate
    (c : BlockCertificate) : CounterexampleCertificate where
  left := c.left
  right := c.right
  disjoint := c.disjoint
  left_basis := c.left_basis
  right_basis := c.right_basis
  every_subbasis_erasable := c.every_subbasis_erasable

/-! ## The deterministic ordinary-target deletion argument -/

/-- The window in which the final deletion argument finds its two summands. -/
def window (X : Set ℕ) (M : ℕ) : Set ℕ :=
  X ∩ Set.Icc M (100 * M)

/-- Points of a color in the current window which the candidate subbasis omitted. -/
noncomputable def missingWindow (X D : Set ℕ) (M : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc M (100 * M)).filter fun x ↦ x ∈ X ∧ x ∉ D

lemma mem_missingWindow {X D : Set ℕ} {M x : ℕ} :
    x ∈ missingWindow X D M ↔ x ∈ X ∧ x ∉ D ∧ M ≤ x ∧ x ≤ 100 * M := by
  simp [missingWindow, and_assoc, and_left_comm, and_comm]

/-- Unordered representations whose two summands lie in the current window. -/
noncomputable def localRepr (X : Set ℕ) (M n : ℕ) : Finset (ℕ × ℕ) :=
  Erdos868.unordRepr (window X M) n

lemma mem_localRepr {X : Set ℕ} {M n : ℕ} {p : ℕ × ℕ} :
    p ∈ localRepr X M n ↔
      p.1 ≤ p.2 ∧ p.1 ∈ X ∧ M ≤ p.1 ∧ p.1 ≤ 100 * M ∧
        p.2 ∈ X ∧ M ≤ p.2 ∧ p.2 ≤ 100 * M ∧ p.1 + p.2 = n := by
  rw [localRepr, Erdos868.mem_unordRepr]
  simp only [window, Set.mem_inter_iff, Set.mem_Icc]
  aesop

/-- Larsen's restricted representation count: ordered increasingly, with ratio at most 100. -/
noncomputable def balancedRepr (X : Set ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (Erdos868.unordRepr X n).filter fun p ↦ p.2 ≤ 100 * p.1

lemma mem_balancedRepr {X : Set ℕ} {n : ℕ} {p : ℕ × ℕ} :
    p ∈ balancedRepr X n ↔
      p.1 ≤ p.2 ∧ p.1 ∈ X ∧ p.2 ∈ X ∧ p.1 + p.2 = n ∧
        p.2 ≤ 100 * p.1 := by
  rw [balancedRepr, Finset.mem_filter, Erdos868.mem_unordRepr]
  aesop

/-- The short block `[101 M - 100, 101 M]`, written without truncated subtraction. -/
def InShortBlock (M n : ℕ) : Prop :=
  101 * M ≤ n + 100 ∧ n ≤ 101 * M

lemma balancedRepr_mem_localRepr {X : Set ℕ} {M n : ℕ} {p : ℕ × ℕ}
    (_hM : 0 < M) (hn : InShortBlock M n) (hp : p ∈ balancedRepr X n) :
    p ∈ localRepr X M n := by
  rcases hn with ⟨hnlo, hnhi⟩
  rw [mem_balancedRepr] at hp
  rw [mem_localRepr]
  rcases hp with ⟨hp12, hpX, hp2X, hsum, hratio⟩
  have hp1lo : M ≤ p.1 := by omega
  have hp2lo : M ≤ p.2 := hp1lo.trans hp12
  have hp1hi : p.1 ≤ 100 * M := by omega
  have hp2hi : p.2 ≤ 100 * M := by omega
  exact ⟨hp12, hpX, hp1lo, hp1hi, hp2X, hp2lo, hp2hi, hsum⟩

lemma balancedRepr_card_le_localRepr_card {X : Set ℕ} {M n : ℕ}
    (hM : 0 < M) (hn : InShortBlock M n) :
    (balancedRepr X n).card ≤ (localRepr X M n).card := by
  exact Finset.card_le_card fun _ hp ↦ balancedRepr_mem_localRepr hM hn hp

lemma unordRepr_eq_of_common_summand {A : Set ℕ} {n d : ℕ}
    {p q : ℕ × ℕ} (hp : p ∈ Erdos868.unordRepr A n)
    (hq : q ∈ Erdos868.unordRepr A n)
    (hpd : p.1 = d ∨ p.2 = d) (hqd : q.1 = d ∨ q.2 = d) : p = q := by
  have hp' := Erdos868.mem_unordRepr.1 hp
  have hq' := Erdos868.mem_unordRepr.1 hq
  apply Prod.ext <;> grind

/-- If at most one point of `X` is absent from `D` in the window, two local
representations force one representation all of whose summands belong to `D`. -/
lemma exists_localRepr_in_D {X D : Set ℕ} {M n : ℕ}
    (hmany : 2 ≤ (localRepr X M n).card)
    (hsparse : (missingWindow X D M).card < 2) :
    ∃ p ∈ localRepr X M n, p.1 ∈ D ∧ p.2 ∈ D := by
  have htwo : 1 < (localRepr X M n).card := by omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 htwo
  by_contra hnone
  push Not at hnone
  have hp' := mem_localRepr.1 hp
  have hq' := mem_localRepr.1 hq
  have hpMissing : p.1 ∈ missingWindow X D M ∨ p.2 ∈ missingWindow X D M := by
    by_cases hp1D : p.1 ∈ D
    · right
      exact mem_missingWindow.2 ⟨hp'.2.2.2.2.1, hnone p hp hp1D,
        hp'.2.2.2.2.2.1, hp'.2.2.2.2.2.2.1⟩
    · left
      exact mem_missingWindow.2 ⟨hp'.2.1, hp1D, hp'.2.2.1, hp'.2.2.2.1⟩
  have hqMissing : q.1 ∈ missingWindow X D M ∨ q.2 ∈ missingWindow X D M := by
    by_cases hq1D : q.1 ∈ D
    · right
      exact mem_missingWindow.2 ⟨hq'.2.2.2.2.1, hnone q hq hq1D,
        hq'.2.2.2.2.2.1, hq'.2.2.2.2.2.2.1⟩
    · left
      exact mem_missingWindow.2 ⟨hq'.2.1, hq1D, hq'.2.2.1, hq'.2.2.2.1⟩
  have hle : (missingWindow X D M).card ≤ 1 := by omega
  have heq := Finset.card_le_one.1 hle
  rcases hpMissing with hp1 | hp2 <;> rcases hqMissing with hq1 | hq2
  · exact hpq (unordRepr_eq_of_common_summand hp hq (Or.inl rfl)
      (Or.inl (heq _ hq1 _ hp1)))
  · exact hpq (unordRepr_eq_of_common_summand hp hq (Or.inl rfl)
      (Or.inr (heq _ hq2 _ hp1)))
  · exact hpq (unordRepr_eq_of_common_summand hp hq (Or.inr rfl)
      (Or.inl (heq _ hq1 _ hp2)))
  · exact hpq (unordRepr_eq_of_common_summand hp hq (Or.inr rfl)
      (Or.inr (heq _ hq2 _ hp2)))

/-- The representation supplied by the preceding lemma avoids every fixed `d < M`. -/
lemma localRepr_survives_erase {X D : Set ℕ} {M n d : ℕ}
    (hdM : d < M) (hmany : 2 ≤ (localRepr X M n).card)
    (hsparse : (missingWindow X D M).card < 2) :
    n ∈ 2 • (D \ {d}) := by
  obtain ⟨p, hp, hp1D, hp2D⟩ := exists_localRepr_in_D hmany hsparse
  have hp' := mem_localRepr.1 hp
  have hp1d : p.1 ≠ d := by omega
  have hp2d : p.2 ≠ d := by omega
  have : n ∈ (D \ {d}) + (D \ {d}) :=
    ⟨p.1, ⟨hp1D, by simpa using hp1d⟩,
      p.2, ⟨hp2D, by simpa using hp2d⟩, hp'.2.2.2.2.2.2.2⟩
  simpa [two_nsmul] using this

/-- Absence of a cross-color missing pair implies the sparse-side alternative used by
Larsen: one color omits fewer than two points in the window. -/
lemma sparse_side_of_no_cross_pair {B C D : Set ℕ} {M : ℕ}
    (hno : ¬ ∃ b ∈ missingWindow B D M, ∃ c ∈ missingWindow C D M, True) :
    (missingWindow B D M).card < 2 ∨ (missingWindow C D M).card < 2 := by
  by_contra h
  push Not at h
  have hBpos : 0 < (missingWindow B D M).card := by omega
  have hCpos : 0 < (missingWindow C D M).card := by omega
  obtain ⟨b, hb⟩ := Finset.card_pos.1 hBpos
  obtain ⟨c, hc⟩ := Finset.card_pos.1 hCpos
  exact hno ⟨b, hb, c, hc, trivial⟩

/-- The complete deterministic argument for a single ordinary target in a short block. -/
lemma shortBlock_survives_erase {B C D : Set ℕ} {M n d : ℕ}
    (hM : 0 < M) (hdM : d < M) (hn : InShortBlock M n)
    (hsparse : (missingWindow B D M).card < 2 ∨
      (missingWindow C D M).card < 2)
    (hBmany : 2 ≤ (balancedRepr B n).card)
    (hCmany : 2 ≤ (balancedRepr C n).card) :
    n ∈ 2 • (D \ {d}) := by
  rcases hsparse with hB | hC
  · apply localRepr_survives_erase hdM
    · exact hBmany.trans (balancedRepr_card_le_localRepr_card hM hn)
    · exact hB
  · apply localRepr_survives_erase hdM
    · exact hCmany.trans (balancedRepr_card_le_localRepr_card hM hn)
    · exact hC

/-- The canonical short-block index, namely `ceil (n / 101)`. -/
def shortIndex (n : ℕ) : ℕ := n ⌈/⌉ 101

lemma shortIndex_mem_shortBlock (n : ℕ) : InShortBlock (shortIndex n) n := by
  constructor
  · change 101 * (n ⌈/⌉ 101) ≤ n + 100
    rw [Nat.ceilDiv_eq_add_pred_div]
    norm_num
    exact Nat.mul_div_le (n + 100) 101
  · exact (ceilDiv_le_iff_le_mul (a := 101) (b := n)
      (c := n ⌈/⌉ 101) (by decide)).1 le_rfl

lemma shortIndex_ge {N n : ℕ} (hn : 101 * N ≤ n) : N ≤ shortIndex n := by
  by_contra h
  have hlt : shortIndex n < N := Nat.lt_of_not_ge h
  have hn' : n ≤ 101 * shortIndex n := (shortIndex_mem_shortBlock n).2
  omega

/-- Cofinality of the short blocks turns the pointwise deletion lemma into precisely the
`ordinary_survives` field required by the block certificate. -/
lemma ordinary_survives_eventually {B C D E : Set ℕ} (d : ℕ)
    (hsparse : ∀ᶠ M : ℕ in atTop,
      (missingWindow B D M).card < 2 ∨ (missingWindow C D M).card < 2)
    (hBmany : ∀ᶠ M : ℕ in atTop, ∀ n, InShortBlock M n → n ∉ E →
      2 ≤ (balancedRepr B n).card)
    (hCmany : ∀ᶠ M : ℕ in atTop, ∀ n, InShortBlock M n → n ∉ E →
      2 ≤ (balancedRepr C n).card) :
    ∀ᶠ n : ℕ in atTop, n ∉ E → n ∈ 2 • (D \ {d}) := by
  have hM : ∀ᶠ M : ℕ in atTop,
      ((missingWindow B D M).card < 2 ∨ (missingWindow C D M).card < 2) ∧
      (∀ n, InShortBlock M n → n ∉ E → 2 ≤ (balancedRepr B n).card) ∧
      (∀ n, InShortBlock M n → n ∉ E → 2 ≤ (balancedRepr C n).card) ∧
      d < M := by
    filter_upwards [hsparse, hBmany, hCmany, eventually_gt_atTop d] with M hsp hB hC hd
    exact ⟨hsp, hB, hC, hd⟩
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hM
  filter_upwards [eventually_ge_atTop (101 * M₀)] with n hn
  intro hnE
  have hindex : M₀ ≤ shortIndex n := shortIndex_ge hn
  have hdata := hM₀ (shortIndex n) hindex
  have hindex_pos : 0 < shortIndex n := by omega
  exact shortBlock_survives_erase hindex_pos
    hdata.2.2.2 (shortIndex_mem_shortBlock n) hdata.1
    (hdata.2.1 n (shortIndex_mem_shortBlock n) hnE)
    (hdata.2.2.1 n (shortIndex_mem_shortBlock n) hnE)

/-! ## The independent random four-label reservoir -/

open MeasureTheory ProbabilityTheory

/- Larsen's three-colour construction admits a convenient four-label refinement.
Labels `0,1` are the two bases and labels `2,3` are their respective hole
reservoirs.  A reflected representation consequently uses two raw coordinates
instead of three. -/
abbrev Color := Fin 4
abbrev ColorSample := ℕ → Color

noncomputable def colorCoordinateMeasure : Measure Color :=
  (PMF.uniformOfFintype Color).toMeasure

noncomputable instance : IsProbabilityMeasure colorCoordinateMeasure := by
  unfold colorCoordinateMeasure
  infer_instance

noncomputable def colorMeasure : Measure ColorSample :=
  Measure.infinitePi (fun _ : ℕ ↦ colorCoordinateMeasure)

noncomputable local instance : IsProbabilityMeasure colorMeasure := by
  unfold colorMeasure
  infer_instance

def colorAt (n : ℕ) (ω : ColorSample) : Color := ω n

lemma colorAt_measurable (n : ℕ) : Measurable (colorAt n) := by
  exact measurable_pi_apply n

lemma colorAt_iIndep : iIndepFun colorAt colorMeasure := by
  change iIndepFun (fun i (ω : ℕ → Color) ↦ ω i)
    (Measure.infinitePi fun _ : ℕ ↦ colorCoordinateMeasure)
  exact iIndepFun_infinitePi (P := fun _ : ℕ ↦ colorCoordinateMeasure)
    (X := fun _ ↦ id) (fun _ ↦ measurable_id)

lemma colorAt_probability (n : ℕ) (i : Color) :
    colorMeasure.real {ω | colorAt n ω = i} = 1 / 4 := by
  change colorMeasure.real ((colorAt n) ⁻¹' {i}) = _
  rw [← map_measureReal_apply (colorAt_measurable n) (MeasurableSet.singleton i)]
  change ((Measure.infinitePi fun _ : ℕ ↦ colorCoordinateMeasure).map
    (fun ω : ℕ → Color ↦ ω n)).real {i} = _
  rw [Measure.infinitePi_map_eval]
  rw [colorCoordinateMeasure, measureReal_def,
    PMF.toMeasure_uniformOfFintype_apply (s := ({i} : Set Color))
      (MeasurableSet.singleton i)]
  norm_num

/-! A reusable family of mutually coordinate-disjoint finite color patterns. -/

structure PatternFamily (arity : ℕ) where
  count : ℕ
  endpoint : Fin count × Fin arity → ℕ
  endpoint_injective : Function.Injective endpoint
  desired : Fin arity → Color

def patternPresent {r : ℕ} (f : PatternFamily r) (i : Fin f.count)
    (ω : ColorSample) : Bool :=
  decide (∀ j : Fin r, colorAt (f.endpoint ⟨i, j⟩) ω = f.desired j)

lemma patternPresent_iff {r : ℕ} (f : PatternFamily r) (i : Fin f.count)
    (ω : ColorSample) :
    patternPresent f i ω = true ↔
      ∀ j : Fin r, colorAt (f.endpoint ⟨i, j⟩) ω = f.desired j := by
  simp [patternPresent]

lemma patternPresent_measurable {r : ℕ} (f : PatternFamily r)
    (i : Fin f.count) : Measurable (patternPresent f i) := by
  let Y : ColorSample → (Fin r → Color) :=
    fun ω j ↦ colorAt (f.endpoint ⟨i, j⟩) ω
  have hY : Measurable Y := measurable_pi_lambda _ fun j ↦
    colorAt_measurable (f.endpoint ⟨i, j⟩)
  let g : (Fin r → Color) → Bool :=
    fun x ↦ decide (∀ j, x j = f.desired j)
  have hg : Measurable g := measurable_of_finite g
  exact hg.comp hY

lemma patternPresent_iIndep {r : ℕ} (f : PatternFamily r) :
    iIndepFun (patternPresent f) colorMeasure := by
  let Y : (i : Fin f.count) → (j : Fin r) → ColorSample → Color :=
    fun i j ω ↦ colorAt (f.endpoint ⟨i, j⟩) ω
  have hflat : iIndepFun
      (fun (p : (i : Fin f.count) × Fin r) ω ↦ Y p.1 p.2 ω)
      colorMeasure := by
    have he : Function.Injective
        (fun p : (i : Fin f.count) × Fin r ↦ f.endpoint (p.1, p.2)) := by
      intro p q hpq
      have hpq' : (p.1, p.2) = (q.1, q.2) := f.endpoint_injective hpq
      rcases p with ⟨i, j⟩
      rcases q with ⟨i', j'⟩
      simpa using hpq'
    simpa only [Y] using iIndepFun.precomp he colorAt_iIndep
  have hgroup : iIndepFun (fun i ω ↦ (Y i · ω)) colorMeasure :=
    Erdos868.iIndepFun_curry_of_uncurry
      (fun i j ↦ colorAt_measurable (f.endpoint ⟨i, j⟩)) hflat
  let g : Fin f.count → (Fin r → Color) → Bool :=
    fun _ x ↦ decide (∀ j, x j = f.desired j)
  have hcomp := hgroup.comp g (fun _ ↦ measurable_of_finite _)
  convert hcomp using 1
  funext i ω
  simp [patternPresent, g, Y]

lemma patternEndpoint_fixed_injective {r : ℕ} (f : PatternFamily r)
    (i : Fin f.count) : Function.Injective (fun j ↦ f.endpoint ⟨i, j⟩) := by
  intro j k hjk
  have : (⟨i, j⟩ : (a : Fin f.count) × Fin r) = ⟨i, k⟩ :=
    by simpa using f.endpoint_injective hjk
  exact congrArg Sigma.snd this

lemma patternPresent_probability {r : ℕ} (f : PatternFamily r)
    (i : Fin f.count) :
    colorMeasure.real {ω | patternPresent f i ω = true} = (1 / 4 : ℝ) ^ r := by
  have hind : iIndepFun
      (fun j : Fin r ↦ colorAt (f.endpoint ⟨i, j⟩)) colorMeasure :=
    iIndepFun.precomp (patternEndpoint_fixed_injective f i) colorAt_iIndep
  have hprod := hind.measure_inter_preimage_eq_mul
    (Finset.univ : Finset (Fin r))
    (sets := fun j ↦ ({f.desired j} : Set Color))
    (fun j _ ↦ MeasurableSet.singleton _)
  have hevent : (⋂ j ∈ (Finset.univ : Finset (Fin r)),
      colorAt (f.endpoint ⟨i, j⟩) ⁻¹' ({f.desired j} : Set Color)) =
      {ω | patternPresent f i ω = true} := by
    ext ω
    simp [patternPresent_iff]
  rw [hevent] at hprod
  have hprod' := congrArg ENNReal.toReal hprod
  simp only [ENNReal.toReal_prod] at hprod'
  rw [← measureReal_def] at hprod'
  have hcoord (j : Fin r) :
      (colorMeasure (colorAt (f.endpoint ⟨i, j⟩) ⁻¹' {f.desired j})).toReal =
        (1 / 4 : ℝ) := by
    change colorMeasure.real
      {ω | colorAt (f.endpoint ⟨i, j⟩) ω = f.desired j} = 1 / 4
    exact colorAt_probability _ _
  simp_rw [hcoord] at hprod'
  simpa using hprod'

/-- Failure of every member of a coordinate-disjoint pattern family. -/
def patternNone {r : ℕ} (f : PatternFamily r) : Set ColorSample :=
  {ω | ∀ i, patternPresent f i ω = false}

lemma patternPresent_false_probability {r : ℕ} (f : PatternFamily r)
    (i : Fin f.count) :
    colorMeasure.real {ω | patternPresent f i ω = false} =
      1 - (1 / 4 : ℝ) ^ r := by
  have hmeas : MeasurableSet {ω | patternPresent f i ω = true} :=
    (patternPresent_measurable f i) (MeasurableSet.singleton true)
  rw [show {ω | patternPresent f i ω = false} =
      ({ω | patternPresent f i ω = true} : Set ColorSample)ᶜ by
    ext ω
    simp]
  rw [measureReal_compl hmeas, patternPresent_probability]
  simp

lemma patternNone_probability {r : ℕ} (f : PatternFamily r) :
    colorMeasure.real (patternNone f) =
      (1 - (1 / 4 : ℝ) ^ r) ^ f.count := by
  have hind := patternPresent_iIndep f
  have hprod := hind.measure_inter_preimage_eq_mul
    (Finset.univ : Finset (Fin f.count))
    (sets := fun _ ↦ ({false} : Set Bool))
    (fun _ _ ↦ MeasurableSet.singleton false)
  have hset : (⋂ i ∈ (Finset.univ : Finset (Fin f.count)),
      patternPresent f i ⁻¹' ({false} : Set Bool)) = patternNone f := by
    ext ω
    simp [patternNone]
  rw [hset] at hprod
  have hprod' := congrArg ENNReal.toReal hprod
  simp only [ENNReal.toReal_prod] at hprod'
  rw [← measureReal_def] at hprod'
  have hcoord (i : Fin f.count) :
      (colorMeasure (patternPresent f i ⁻¹' ({false} : Set Bool))).toReal =
        1 - (1 / 4 : ℝ) ^ r := by
    change colorMeasure.real {ω | patternPresent f i ω = false} = _
    exact patternPresent_false_probability f i
  simp_rw [hcoord] at hprod'
  rw [Finset.prod_const] at hprod'
  simpa using hprod'

lemma patternNone_probability_four (f : PatternFamily 4) :
    colorMeasure.real (patternNone f) = (255 / 256 : ℝ) ^ f.count := by
  rw [patternNone_probability]
  norm_num

lemma patternNone_probability_four_le_exp (f : PatternFamily 4) :
    colorMeasure.real (patternNone f) ≤
      Real.exp (-(f.count : ℝ) / 256) := by
  rw [patternNone_probability_four]
  have hbase : (255 / 256 : ℝ) ≤ Real.exp (-(1 / 256 : ℝ)) := by
    convert Real.one_sub_le_exp_neg (1 / 256 : ℝ) using 1 <;> norm_num
  calc
    (255 / 256 : ℝ) ^ f.count ≤
        (Real.exp (-(1 / 256 : ℝ))) ^ f.count :=
      pow_le_pow_left₀ (by norm_num) hbase _
    _ = Real.exp ((f.count : ℝ) * (-(1 / 256 : ℝ))) := by
      rw [Real.exp_nat_mul]
    _ = Real.exp (-(f.count : ℝ) / 256) := by
      congr 1
      ring

/-! ## One coloring that eventually realizes every scheduled pattern -/

def patternTrialCount (k : ℕ) : ℕ := 8192 * (k + 1)

structure PatternSchedule where
  requirementCount : ℕ → ℕ
  family : (k : ℕ) → Fin (requirementCount k) → PatternFamily 4
  family_count : ∀ k i, (family k i).count = patternTrialCount k
  requirement_bound : ∀ k, requirementCount k ≤ 100 * (scale k) ^ 2

def patternStageBad (s : PatternSchedule) (k : ℕ) : Set ColorSample :=
  ⋃ i : Fin (s.requirementCount k), patternNone (s.family k i)

lemma patternStageBad_measureReal_le_sum (s : PatternSchedule) (k : ℕ) :
    colorMeasure.real (patternStageBad s k) ≤
      ∑ i : Fin (s.requirementCount k),
        colorMeasure.real (patternNone (s.family k i)) := by
  exact measureReal_iUnion_fintype_le _

lemma sixteen_le_exp_three : (16 : ℝ) ≤ Real.exp 3 := by
  have he : (27 / 10 : ℝ) < Real.exp 1 := by
    exact (by norm_num : (27 / 10 : ℝ) < 2.7182818283).trans Real.exp_one_gt_d9
  have hp : (16 : ℝ) < Real.exp 1 ^ (3 : ℕ) := by
    calc
      (16 : ℝ) < (27 / 10 : ℝ) ^ (3 : ℕ) := by norm_num
      _ < Real.exp 1 ^ (3 : ℕ) := by gcongr
  have hexp : Real.exp 3 = Real.exp 1 ^ (3 : ℕ) := by
    simpa using Real.exp_nat_mul (1 : ℝ) 3
  rw [hexp]
  exact hp.le

lemma hundred_le_exp_five : (100 : ℝ) ≤ Real.exp 5 := by
  have he : (27 / 10 : ℝ) < Real.exp 1 := by
    exact (by norm_num : (27 / 10 : ℝ) < 2.7182818283).trans Real.exp_one_gt_d9
  have hp : (100 : ℝ) < Real.exp 1 ^ (5 : ℕ) := by
    calc
      (100 : ℝ) < (27 / 10 : ℝ) ^ (5 : ℕ) := by norm_num
      _ < Real.exp 1 ^ (5 : ℕ) := by gcongr
  have hexp : Real.exp 5 = Real.exp 1 ^ (5 : ℕ) := by
    simpa using Real.exp_nat_mul (1 : ℝ) 5
  rw [hexp]
  exact hp.le

lemma requirement_times_pattern_failure_le (s : PatternSchedule) (k : ℕ) :
    (s.requirementCount k : ℝ) *
        Real.exp (-(patternTrialCount k : ℝ) / 256) ≤
      Real.exp (-(k : ℝ)) := by
  let u := k + 1
  have hreq : (s.requirementCount k : ℝ) ≤ 100 * (16 : ℝ) ^ u := by
    have h := s.requirement_bound k
    have hscale : (scale k) ^ 2 = 16 ^ u := by
      change (4 ^ (k + 1)) ^ 2 = 16 ^ (k + 1)
      calc
        (4 ^ (k + 1)) ^ 2 = 4 ^ ((k + 1) * 2) := by rw [pow_mul]
        _ = 4 ^ (2 * (k + 1)) := by rw [Nat.mul_comm]
        _ = (4 ^ 2) ^ (k + 1) := by rw [pow_mul]
        _ = 16 ^ (k + 1) := by norm_num
    rw [hscale] at h
    have hc : (s.requirementCount k : ℝ) ≤
        ((100 * 16 ^ u : ℕ) : ℝ) := by exact_mod_cast h
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at hc
    exact hc
  have h16pow : (16 : ℝ) ^ u ≤ Real.exp ((u : ℝ) * 3) := by
    calc
      (16 : ℝ) ^ u ≤ (Real.exp 3) ^ u :=
        pow_le_pow_left₀ (by norm_num) sixteen_le_exp_three _
      _ = Real.exp ((u : ℝ) * 3) := by
        simpa [mul_comm] using (Real.exp_nat_mul (3 : ℝ) u).symm
  have h100 : (100 : ℝ) ≤ Real.exp ((u : ℝ) * 5) := by
    calc
      (100 : ℝ) ≤ Real.exp 5 := hundred_le_exp_five
      _ ≤ Real.exp ((u : ℝ) * 5) := by
        apply Real.exp_le_exp.mpr
        exact_mod_cast (show 1 * 5 ≤ u * 5 by omega)
  have hreqexp : (s.requirementCount k : ℝ) ≤
      Real.exp ((u : ℝ) * 8) := by
    calc
      (s.requirementCount k : ℝ) ≤ 100 * (16 : ℝ) ^ u := hreq
      _ ≤ Real.exp ((u : ℝ) * 5) * Real.exp ((u : ℝ) * 3) :=
        mul_le_mul h100 h16pow (by positivity) (by positivity)
      _ = Real.exp ((u : ℝ) * 8) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have htrial : Real.exp (-(patternTrialCount k : ℝ) / 256) =
      Real.exp (-(u : ℝ) * 32) := by
    congr 1
    simp [patternTrialCount, u]
    ring
  rw [htrial]
  calc
    (s.requirementCount k : ℝ) * Real.exp (-(u : ℝ) * 32) ≤
        Real.exp ((u : ℝ) * 8) * Real.exp (-(u : ℝ) * 32) :=
      mul_le_mul_of_nonneg_right hreqexp (by positivity)
    _ = Real.exp (-(u : ℝ) * 24) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(k : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hku : (k : ℝ) ≤ 24 * (u : ℝ) := by
        exact_mod_cast (show k ≤ 24 * u by omega)
      linarith

lemma patternStageBad_measureReal_le_exp (s : PatternSchedule) (k : ℕ) :
    colorMeasure.real (patternStageBad s k) ≤ Real.exp (-(k : ℝ)) := by
  calc
    colorMeasure.real (patternStageBad s k) ≤
        ∑ i : Fin (s.requirementCount k),
          colorMeasure.real (patternNone (s.family k i)) :=
      patternStageBad_measureReal_le_sum s k
    _ ≤ ∑ _i : Fin (s.requirementCount k),
          Real.exp (-(patternTrialCount k : ℝ) / 256) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [s.family_count k i] using
        patternNone_probability_four_le_exp (s.family k i)
    _ = (s.requirementCount k : ℝ) *
        Real.exp (-(patternTrialCount k : ℝ) / 256) := by simp
    _ ≤ Real.exp (-(k : ℝ)) := requirement_times_pattern_failure_le s k

lemma summable_patternStageBad_measureReal (s : PatternSchedule) :
    Summable (fun k : ℕ ↦ colorMeasure.real (patternStageBad s k)) := by
  apply Real.summable_exp_neg_nat.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact patternStageBad_measureReal_le_exp s k

lemma tsum_patternStageBad_ne_top (s : PatternSchedule) :
    (∑' k : ℕ, colorMeasure (patternStageBad s k)) ≠ ⊤ := by
  rw [show (fun k : ℕ ↦ colorMeasure (patternStageBad s k)) =
      (fun k ↦ ((colorMeasure (patternStageBad s k)).toNNReal : ENNReal)) by
    funext k
    exact (ENNReal.coe_toNNReal (measure_ne_top _ _)).symm]
  apply ENNReal.tsum_coe_ne_top_iff_summable_coe.2
  simpa only [Measure.real, ENNReal.coe_toNNReal_eq_toReal] using
    summable_patternStageBad_measureReal s

lemma PatternSchedule.exists_eventually_good (s : PatternSchedule) :
    ∃ ω : ColorSample, ∀ᶠ k : ℕ in atTop,
      ∀ i : Fin (s.requirementCount k),
        ∃ j : Fin (s.family k i).count,
          patternPresent (s.family k i) j ω = true := by
  have hae : ∀ᵐ ω ∂colorMeasure, ∀ᶠ k : ℕ in atTop,
      ω ∉ patternStageBad s k :=
    MeasureTheory.ae_eventually_notMem (tsum_patternStageBad_ne_top s)
  obtain ⟨ω, hω⟩ := hae.exists
  refine ⟨ω, ?_⟩
  filter_upwards [hω] with k hk i
  by_contra h
  push Not at h
  apply hk
  exact Set.mem_iUnion.2 ⟨i, fun j ↦ by
    cases hp : patternPresent (s.family k i) j ω with
    | false => rfl
    | true => exact (h j hp).elim⟩


/-! This file isolates the deterministic consequence of a completed four-label
block construction.  All probabilistic and interval work is hidden in the fields
of `RecursiveCertificate`; no field asserts either final basis or the desired
non-minimality conclusion. -/

/-- The increasing union of the finite pre-states of one reservoir. -/
def stageLimit (S : ℕ → Finset ℕ) : Set ℕ :=
  {x | ∃ k, x ∈ S k}

lemma mem_stageLimit {S : ℕ → Finset ℕ} {x : ℕ} :
    x ∈ stageLimit S ↔ ∃ k, x ∈ S k := Iff.rfl

/-- The abstract output of the finite recursive four-label construction.

`scheduled k = some (b,c)` means that the cross-colour pair `(b,c)` is the
trap used at scale `k`.  The complement points forced into the two reservoirs
give representations of the exceptional target, while `trap_fragile` says
that every representation of that target by the union hits the scheduled pair.
-/
structure RecursiveCertificate where
  Bk : ℕ → Finset ℕ
  Ck : ℕ → Finset ℕ
  Bk_mono : Monotone Bk
  Ck_mono : Monotone Ck
  stage_disjoint : ∀ k, Disjoint (Bk k) (Ck k)
  stage_bounded : ∀ k x, x ∈ Bk k ∨ x ∈ Ck k → x ≤ scale (k + 1)
  scheduled : ℕ → Option (ℕ × ℕ)
  scheduled_left : ∀ {k b c}, scheduled k = some (b, c) → b ∈ Bk k
  scheduled_right : ∀ {k b c}, scheduled k = some (b, c) → c ∈ Ck k
  scheduled_bounded : ∀ {k b c}, scheduled k = some (b, c) →
    b ≤ scale k ∧ c ≤ scale k
  reflected_left : ∀ {k b c}, scheduled k = some (b, c) →
    scale (k + 1) - b ∈ Bk (k + 1)
  reflected_right : ∀ {k b c}, scheduled k = some (b, c) →
    scale (k + 1) - c ∈ Ck (k + 1)
  inactive_finite : {k | scheduled k = none}.Finite
  sparse_window : ∀ (D : Set ℕ), D ⊆ stageLimit Bk ∪ stageLimit Ck → IsBasis2 D →
    ∀ᶠ M : ℕ in atTop,
      (missingWindow (stageLimit Bk) D M).card < 2 ∨
        (missingWindow (stageLimit Ck) D M).card < 2
  trap_fragile : ∀ {k b c}, scheduled k = some (b, c) →
    ∀ {x y}, x ∈ stageLimit Bk ∪ stageLimit Ck →
      y ∈ stageLimit Bk ∪ stageLimit Ck →
      x + y = scale (k + 1) → x = b ∨ x = c ∨ y = b ∨ y = c
  fixed_trap_incidence : ∀ d,
    {k | ∃ b c, scheduled k = some (b, c) ∧ (d = b ∨ d = c)}.Finite
  ordinary_many_left : ∀ᶠ M : ℕ in atTop, ∀ n, InShortBlock M n →
    n ∉ exceptional → 2 ≤ (balancedRepr (stageLimit Bk) n).card
  ordinary_many_right : ∀ᶠ M : ℕ in atTop, ∀ n, InShortBlock M n →
    n ∉ exceptional → 2 ≤ (balancedRepr (stageLimit Ck) n).card

namespace FourBuild

abbrev Trap := ℕ × ℕ

def leftColor : Color := 0
def rightColor : Color := 1
def leftHole : Color := 2
def rightHole : Color := 3

def flipColor : Color → Color
  | 0 => leftHole
  | 1 => rightHole
  | 2 => leftColor
  | 3 => rightColor

@[simp] lemma flip_leftColor : flipColor leftColor = leftHole := rfl
@[simp] lemma flip_rightColor : flipColor rightColor = rightHole := rfl
@[simp] lemma flip_leftHole : flipColor leftHole = leftColor := rfl
@[simp] lemma flip_rightHole : flipColor rightHole = rightColor := rfl

structure StageState where
  left : Finset ℕ
  right : Finset ℕ
  label : ℕ → Color
  known : Finset Trap
  used : Finset Trap

def trapMax (p : Trap) : ℕ := max p.1 p.2

noncomputable def leastByMax (s : Finset Trap) (hs : s.Nonempty) : Trap :=
  let maxima := s.image trapMax
  let m := maxima.min' (hs.image trapMax)
  let shell := s.filter fun p ↦ trapMax p = m
  Classical.choose (show shell.Nonempty by
    obtain ⟨p, hp⟩ := hs
    have hm : m ∈ maxima := Finset.min'_mem _ _
    rcases Finset.mem_image.1 hm with ⟨q, hq, hqm⟩
    exact ⟨q, Finset.mem_filter.2 ⟨hq, hqm⟩⟩)

lemma leastByMax_mem (s : Finset Trap) (hs : s.Nonempty) :
    leastByMax s hs ∈ s := by
  rw [leastByMax]
  exact (Finset.mem_filter.1 (Classical.choose_spec _)).1

lemma leastByMax_max_le (s : Finset Trap) (hs : s.Nonempty) {p : Trap}
    (hp : p ∈ s) : trapMax (leastByMax s hs) ≤ trapMax p := by
  rw [leastByMax]
  have hshell := Finset.mem_filter.1 (Classical.choose_spec (show
    (s.filter fun q ↦
      trapMax q = (s.image trapMax).min' (hs.image trapMax)).Nonempty by
      have hm := Finset.min'_mem (s.image trapMax) (hs.image trapMax)
      rcases Finset.mem_image.1 hm with ⟨q, hq, hqm⟩
      exact ⟨q, Finset.mem_filter.2 ⟨hq, hqm⟩⟩))
  rw [hshell.2]
  exact Finset.min'_le _ _ (Finset.mem_image.2 ⟨p, hp, rfl⟩)

def eligible (s : StageState) (k : ℕ) : Finset Trap :=
  (s.left.product s.right).filter fun p ↦
    k ≤ p.1 ∧ p.1 ≤ scale k ∧ k ≤ p.2 ∧ p.2 ≤ scale k

def available (s : StageState) (k : ℕ) : Finset Trap :=
  s.known ∪ eligible s k

def candidates (s : StageState) (k : ℕ) : Finset Trap :=
  available s k \ s.used

def active (s : StageState) (k : ℕ) : Prop :=
  0 < k ∧ k ≤ (eligible s k).card

noncomputable def scheduled (s : StageState) (k : ℕ) : Option Trap := by
  classical
  if ha : active s k then
    if hc : (candidates s k).Nonempty then
      exact some (leastByMax (candidates s k) hc)
    else exact none
  else exact none

lemma scheduled_mem_candidates {s : StageState} {k : ℕ} {p : Trap}
    (hp : scheduled s k = some p) : p ∈ candidates s k := by
  classical
  unfold scheduled at hp
  split at hp <;> rename_i ha
  · split at hp <;> rename_i hc
    · simp only [Option.some.injEq] at hp
      rw [← hp]
      exact leastByMax_mem _ hc
    · simp at hp
  · simp at hp

lemma scheduled_mem_available {s : StageState} {k : ℕ} {p : Trap}
    (hp : scheduled s k = some p) : p ∈ available s k :=
  (Finset.mem_sdiff.1 (scheduled_mem_candidates hp)).1

lemma scheduled_not_used {s : StageState} {k : ℕ} {p : Trap}
    (hp : scheduled s k = some p) : p ∉ s.used :=
  (Finset.mem_sdiff.1 (scheduled_mem_candidates hp)).2

lemma scheduled_max_le {s : StageState} {k : ℕ} {p q : Trap}
    (hp : scheduled s k = some p) (hq : q ∈ candidates s k) :
    trapMax p ≤ trapMax q := by
  classical
  unfold scheduled at hp
  split at hp <;> rename_i ha
  · split at hp <;> rename_i hc
    · simp only [Option.some.injEq] at hp
      rw [← hp]
      exact leastByMax_max_le _ hc hq
    · simp at hp
  · simp at hp

lemma scheduled_some_of_active_of_card_used_lt {s : StageState} {k : ℕ}
    (ha : active s k) (hu : s.used.card < k) :
    ∃ p, scheduled s k = some p := by
  classical
  have hnot : ¬ available s k ⊆ s.used := by
    intro hsub
    have he : eligible s k ⊆ available s k := Finset.subset_union_right
    have hc := Finset.card_le_card (he.trans hsub)
    exact (Nat.not_le_of_lt hu) (ha.2.trans hc)
  have hc : (candidates s k).Nonempty := Finset.sdiff_nonempty.2 hnot
  exact ⟨leastByMax _ hc, by simp [scheduled, ha, hc]⟩

def directLeft (ω : ColorSample) (k : ℕ) : Finset ℕ :=
  (Finset.range (scale (k + 1))).filter fun x ↦
    ((4 * scale k < 3 * x ∧ x < 2 * scale k) ∨
      (8 * scale k < 3 * x ∧ x < 3 * scale k)) ∧ ω x = leftColor

def directRight (ω : ColorSample) (k : ℕ) : Finset ℕ :=
  (Finset.range (scale (k + 1))).filter fun x ↦
    ((4 * scale k < 3 * x ∧ x < 2 * scale k) ∨
      (8 * scale k < 3 * x ∧ x < 3 * scale k)) ∧ ω x = rightColor

def reflectedLeftHoles (s : StageState) (k : ℕ) : Finset ℕ :=
  ((Finset.range (scale k)).filter fun y ↦ 0 < y ∧ s.label y = leftHole).image
    fun y ↦ scale (k + 1) - y

def reflectedRightHoles (s : StageState) (k : ℕ) : Finset ℕ :=
  ((Finset.range (scale k)).filter fun y ↦ 0 < y ∧ s.label y = rightHole).image
    fun y ↦ scale (k + 1) - y

noncomputable def trapLeftReflection (s : StageState) (k : ℕ) : Finset ℕ :=
  match scheduled s k with
  | none => ∅
  | some p => {scale (k + 1) - p.1}

noncomputable def trapRightReflection (s : StageState) (k : ℕ) : Finset ℕ :=
  match scheduled s k with
  | none => ∅
  | some p => {scale (k + 1) - p.2}

noncomputable def nextLabel (ω : ColorSample) (s : StageState) (k x : ℕ) : Color :=
  if x < scale k then s.label x
  else if scale k < x ∧ x < 3 * scale k then ω x
  else if 3 * scale k < x ∧ x < scale (k + 1) then
    let y := scale (k + 1) - x
    match scheduled s k with
    | some p =>
        if y = p.1 then leftColor
        else if y = p.2 then rightColor
        else flipColor (s.label y)
    | none => flipColor (s.label y)
  else leftHole

noncomputable def advance (ω : ColorSample) (k : ℕ) (s : StageState) : StageState where
  left := s.left ∪ directLeft ω k ∪ reflectedLeftHoles s k ∪ trapLeftReflection s k
  right := s.right ∪ directRight ω k ∪ reflectedRightHoles s k ∪ trapRightReflection s k
  label := nextLabel ω s k
  known := available s k
  used := match scheduled s k with
    | none => s.used
    | some p => insert p s.used

noncomputable def build (ω : ColorSample) : ℕ → StageState
  | 0 => { left := ∅, right := ∅, label := ω, known := ∅, used := ∅ }
  | k + 1 => advance ω k (build ω k)

@[simp] lemma build_zero_left (ω : ColorSample) : (build ω 0).left = ∅ := rfl
@[simp] lemma build_zero_right (ω : ColorSample) : (build ω 0).right = ∅ := rfl
@[simp] lemma build_zero_known (ω : ColorSample) : (build ω 0).known = ∅ := rfl
@[simp] lemma build_zero_used (ω : ColorSample) : (build ω 0).used = ∅ := rfl
@[simp] lemma build_succ (ω : ColorSample) (k : ℕ) :
    build ω (k + 1) = advance ω k (build ω k) := rfl

lemma left_mono_step (ω : ColorSample) (s : StageState) (k : ℕ) :
    s.left ⊆ (advance ω k s).left := by
  intro x hx
  simp only [advance, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl hx))

lemma right_mono_step (ω : ColorSample) (s : StageState) (k : ℕ) :
    s.right ⊆ (advance ω k s).right := by
  intro x hx
  simp only [advance, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl hx))

lemma known_mono_step (ω : ColorSample) (s : StageState) (k : ℕ) :
    s.known ⊆ (advance ω k s).known := Finset.subset_union_left

lemma used_mono_step (ω : ColorSample) (s : StageState) (k : ℕ) :
    s.used ⊆ (advance ω k s).used := by
  simp only [advance]
  split <;> simp

lemma left_mono {ω : ColorSample} {i j : ℕ} (hij : i ≤ j) :
    (build ω i).left ⊆ (build ω j).left := by
  induction j, hij using Nat.le_induction with
  | base => exact fun _ ↦ id
  | succ j hij ih => exact ih.trans (left_mono_step ω (build ω j) j)

lemma right_mono {ω : ColorSample} {i j : ℕ} (hij : i ≤ j) :
    (build ω i).right ⊆ (build ω j).right := by
  induction j, hij using Nat.le_induction with
  | base => exact fun _ ↦ id
  | succ j hij ih => exact ih.trans (right_mono_step ω (build ω j) j)

lemma known_mono {ω : ColorSample} {i j : ℕ} (hij : i ≤ j) :
    (build ω i).known ⊆ (build ω j).known := by
  induction j, hij using Nat.le_induction with
  | base => exact fun _ ↦ id
  | succ j hij ih => exact ih.trans (known_mono_step ω (build ω j) j)

lemma used_mono {ω : ColorSample} {i j : ℕ} (hij : i ≤ j) :
    (build ω i).used ⊆ (build ω j).used := by
  induction j, hij using Nat.le_induction with
  | base => exact fun _ ↦ id
  | succ j hij ih => exact ih.trans (used_mono_step ω (build ω j) j)

structure GoodState (k : ℕ) (s : StageState) : Prop where
  left_bound : ∀ x ∈ s.left, 0 < x ∧ x < scale k
  right_bound : ∀ x ∈ s.right, 0 < x ∧ x < scale k
  left_label : ∀ x ∈ s.left, s.label x = leftColor
  right_label : ∀ x ∈ s.right, s.label x = rightColor
  disjoint : Disjoint s.left s.right
  known_colors : ∀ p ∈ s.known, p.1 ∈ s.left ∧ p.2 ∈ s.right
  used_known : s.used ⊆ s.known
  used_zero : k = 0 → s.used = ∅
  used_card_lt : 0 < k → s.used.card < k

lemma mem_available_colors {s : StageState} {k : ℕ} (hs : GoodState k s)
    {p : Trap} (hp : p ∈ available s k) : p.1 ∈ s.left ∧ p.2 ∈ s.right := by
  rcases Finset.mem_union.1 hp with hp | hp
  · exact hs.known_colors p hp
  · exact (Finset.mem_product.1 (Finset.mem_filter.1 hp).1)

lemma scheduled_colors {s : StageState} {k : ℕ} (hs : GoodState k s)
    {p : Trap} (hp : scheduled s k = some p) :
    p.1 ∈ s.left ∧ p.2 ∈ s.right :=
  mem_available_colors hs (scheduled_mem_available hp)

lemma scheduled_bounds {s : StageState} {k : ℕ} (hs : GoodState k s)
    {p : Trap} (hp : scheduled s k = some p) :
    0 < p.1 ∧ p.1 < scale k ∧ 0 < p.2 ∧ p.2 < scale k := by
  obtain ⟨hp1, hp2⟩ := scheduled_colors hs hp
  exact ⟨(hs.left_bound _ hp1).1, (hs.left_bound _ hp1).2,
    (hs.right_bound _ hp2).1, (hs.right_bound _ hp2).2⟩

lemma scheduled_ne {s : StageState} {k : ℕ} (hs : GoodState k s)
    {p : Trap} (hp : scheduled s k = some p) : p.1 ≠ p.2 := by
  obtain ⟨hp1, hp2⟩ := scheduled_colors hs hp
  exact fun h ↦ Finset.disjoint_left.1 hs.disjoint hp1 (h ▸ hp2)

lemma mem_directLeft {ω : ColorSample} {k x : ℕ} :
    x ∈ directLeft ω k ↔ x < scale (k + 1) ∧
      (((4 * scale k < 3 * x ∧ x < 2 * scale k) ∨
        (8 * scale k < 3 * x ∧ x < 3 * scale k)) ∧ ω x = leftColor) := by
  simp [directLeft]

lemma mem_directRight {ω : ColorSample} {k x : ℕ} :
    x ∈ directRight ω k ↔ x < scale (k + 1) ∧
      (((4 * scale k < 3 * x ∧ x < 2 * scale k) ∨
        (8 * scale k < 3 * x ∧ x < 3 * scale k)) ∧ ω x = rightColor) := by
  simp [directRight]

lemma directLeft_bounds {ω : ColorSample} {k x : ℕ} (hx : x ∈ directLeft ω k) :
    scale k < x ∧ x < 3 * scale k := by
  rw [mem_directLeft] at hx
  rcases hx.2.1 with h | h <;> omega

lemma directRight_bounds {ω : ColorSample} {k x : ℕ} (hx : x ∈ directRight ω k) :
    scale k < x ∧ x < 3 * scale k := by
  rw [mem_directRight] at hx
  rcases hx.2.1 with h | h <;> omega

lemma mem_reflectedLeftHoles {s : StageState} {k x : ℕ} :
    x ∈ reflectedLeftHoles s k ↔
      ∃ y < scale k, 0 < y ∧ s.label y = leftHole ∧ scale (k + 1) - y = x := by
  simp [reflectedLeftHoles, and_assoc]

lemma mem_reflectedRightHoles {s : StageState} {k x : ℕ} :
    x ∈ reflectedRightHoles s k ↔
      ∃ y < scale k, 0 < y ∧ s.label y = rightHole ∧ scale (k + 1) - y = x := by
  simp [reflectedRightHoles, and_assoc]

lemma reflected_bounds {k x y : ℕ} (hy0 : 0 < y) (hy : y < scale k)
    (hx : scale (k + 1) - y = x) :
    scale k < x ∧ x < scale (k + 1) := by
  rw [scale_succ] at hx ⊢
  have hN := scale_pos k
  omega

lemma reflected_gt_three {k x y : ℕ} (hy : y < scale k)
    (hx : scale (k + 1) - y = x) : 3 * scale k < x := by
  rw [scale_succ] at hx
  omega

lemma mem_trapLeftReflection {s : StageState} {k x : ℕ} :
    x ∈ trapLeftReflection s k ↔
      ∃ p, scheduled s k = some p ∧ x = scale (k + 1) - p.1 := by
  classical
  unfold trapLeftReflection
  split <;> simp_all

lemma mem_trapRightReflection {s : StageState} {k x : ℕ} :
    x ∈ trapRightReflection s k ↔
      ∃ p, scheduled s k = some p ∧ x = scale (k + 1) - p.2 := by
  classical
  unfold trapRightReflection
  split <;> simp_all

lemma nextLabel_old {ω : ColorSample} {s : StageState} {k x : ℕ}
    (hx : x < scale k) : nextLabel ω s k x = s.label x := by
  simp [nextLabel, hx]

lemma nextLabel_fresh {ω : ColorSample} {s : StageState} {k x : ℕ}
    (hx0 : scale k < x) (hx1 : x < 3 * scale k) :
    nextLabel ω s k x = ω x := by
  have hn : ¬x < scale k := by omega
  simp [nextLabel, hn, hx0, hx1]

lemma nextLabel_reflected_leftHole {ω : ColorSample} {s : StageState} {k y : ℕ}
    (hs : GoodState k s) (hy0 : 0 < y) (hy : y < scale k)
    (hlabel : s.label y = leftHole) :
    nextLabel ω s k (scale (k + 1) - y) = leftColor := by
  have hbounds := reflected_bounds hy0 hy rfl
  rw [scale_succ] at hbounds ⊢
  have hsub : 4 * scale k - (4 * scale k - y) = y := by omega
  have hnold : ¬4 * scale k - y < scale k := by omega
  have href : 3 * scale k < 4 * scale k - y ∧ 4 * scale k - y < 4 * scale k := by
    omega
  unfold nextLabel
  rw [scale_succ]
  simp only [hnold, if_false]
  rw [if_neg (by omega : ¬(scale k < 4 * scale k - y ∧
    4 * scale k - y < 3 * scale k)), if_pos href]
  simp only [hsub]
  cases hopt : scheduled s k with
  | none => simp [hopt, hlabel]
  | some p =>
      have hp1 := (hs.left_label _ (scheduled_colors hs hopt).1)
      have hp2 := (hs.right_label _ (scheduled_colors hs hopt).2)
      have hy1 : y ≠ p.1 := by intro h; rw [h, hp1] at hlabel; contradiction
      have hy2 : y ≠ p.2 := by intro h; rw [h, hp2] at hlabel; contradiction
      simp [hopt, hy1, hy2, hlabel]

lemma nextLabel_reflected_rightHole {ω : ColorSample} {s : StageState} {k y : ℕ}
    (hs : GoodState k s) (hy0 : 0 < y) (hy : y < scale k)
    (hlabel : s.label y = rightHole) :
    nextLabel ω s k (scale (k + 1) - y) = rightColor := by
  have hbounds := reflected_bounds hy0 hy rfl
  rw [scale_succ] at hbounds ⊢
  have hsub : 4 * scale k - (4 * scale k - y) = y := by omega
  have hnold : ¬4 * scale k - y < scale k := by omega
  have href : 3 * scale k < 4 * scale k - y ∧ 4 * scale k - y < 4 * scale k := by
    omega
  unfold nextLabel
  rw [scale_succ]
  simp only [hnold, if_false]
  rw [if_neg (by omega : ¬(scale k < 4 * scale k - y ∧
    4 * scale k - y < 3 * scale k)), if_pos href]
  simp only [hsub]
  cases hopt : scheduled s k with
  | none => simp [hopt, hlabel]
  | some p =>
      have hp1 := (hs.left_label _ (scheduled_colors hs hopt).1)
      have hp2 := (hs.right_label _ (scheduled_colors hs hopt).2)
      have hy1 : y ≠ p.1 := by intro h; rw [h, hp1] at hlabel; contradiction
      have hy2 : y ≠ p.2 := by intro h; rw [h, hp2] at hlabel; contradiction
      simp [hopt, hy1, hy2, hlabel]

lemma nextLabel_trap_left {ω : ColorSample} {s : StageState} {k : ℕ} {p : Trap}
    (hs : GoodState k s) (hp : scheduled s k = some p) :
    nextLabel ω s k (scale (k + 1) - p.1) = leftColor := by
  have hb := scheduled_bounds hs hp
  have hr := reflected_bounds hb.1 hb.2.1 rfl
  rw [scale_succ] at hr ⊢
  have hsub : 4 * scale k - (4 * scale k - p.1) = p.1 := by omega
  have hnold : ¬4 * scale k - p.1 < scale k := by omega
  have href : 3 * scale k < 4 * scale k - p.1 ∧
      4 * scale k - p.1 < 4 * scale k := by omega
  have hnfresh : ¬(scale k < 4 * scale k - p.1 ∧
      4 * scale k - p.1 < 3 * scale k) := by omega
  unfold nextLabel
  rw [scale_succ]
  simp [hnold, hnfresh, href, hp, hsub]

lemma nextLabel_trap_right {ω : ColorSample} {s : StageState} {k : ℕ} {p : Trap}
    (hs : GoodState k s) (hp : scheduled s k = some p) :
    nextLabel ω s k (scale (k + 1) - p.2) = rightColor := by
  have hb := scheduled_bounds hs hp
  have hr := reflected_bounds hb.2.2.1 hb.2.2.2 rfl
  have hne := scheduled_ne hs hp
  rw [scale_succ] at hr ⊢
  have hsub : 4 * scale k - (4 * scale k - p.2) = p.2 := by omega
  have hnold : ¬4 * scale k - p.2 < scale k := by omega
  have href : 3 * scale k < 4 * scale k - p.2 ∧
      4 * scale k - p.2 < 4 * scale k := by omega
  have hnfresh : ¬(scale k < 4 * scale k - p.2 ∧
      4 * scale k - p.2 < 3 * scale k) := by omega
  have hne' : p.2 ≠ p.1 := Ne.symm hne
  unfold nextLabel
  rw [scale_succ]
  simp [hnold, hnfresh, href, hp, hsub, hne']

lemma advance_left_bound {ω : ColorSample} {s : StageState} {k : ℕ}
    (hs : GoodState k s) :
    ∀ x ∈ (advance ω k s).left, 0 < x ∧ x < scale (k + 1) := by
  intro x hx
  simp only [advance, Finset.mem_union] at hx
  rcases hx with hx | hx
  · rcases hx with hx | hx
    · rcases hx with hx | hx
      · exact ⟨(hs.left_bound _ hx).1,
          (hs.left_bound _ hx).2.trans (scale_strictMono (Nat.lt_succ_self k))⟩
      · exact ⟨(scale_pos k).trans (directLeft_bounds hx).1,
          (mem_directLeft.1 hx).1⟩
    · obtain ⟨y, hy, hy0, _hlabel, rfl⟩ := mem_reflectedLeftHoles.1 hx
      exact ⟨(reflected_bounds hy0 hy rfl).1.trans' (scale_pos k),
        (reflected_bounds hy0 hy rfl).2⟩
  · obtain ⟨p, hp, rfl⟩ := mem_trapLeftReflection.1 hx
    have hb := scheduled_bounds hs hp
    exact ⟨(reflected_bounds hb.1 hb.2.1 rfl).1.trans' (scale_pos k),
      (reflected_bounds hb.1 hb.2.1 rfl).2⟩

lemma advance_right_bound {ω : ColorSample} {s : StageState} {k : ℕ}
    (hs : GoodState k s) :
    ∀ x ∈ (advance ω k s).right, 0 < x ∧ x < scale (k + 1) := by
  intro x hx
  simp only [advance, Finset.mem_union] at hx
  rcases hx with hx | hx
  · rcases hx with hx | hx
    · rcases hx with hx | hx
      · exact ⟨(hs.right_bound _ hx).1,
          (hs.right_bound _ hx).2.trans (scale_strictMono (Nat.lt_succ_self k))⟩
      · exact ⟨(scale_pos k).trans (directRight_bounds hx).1,
          (mem_directRight.1 hx).1⟩
    · obtain ⟨y, hy, hy0, _hlabel, rfl⟩ := mem_reflectedRightHoles.1 hx
      exact ⟨(reflected_bounds hy0 hy rfl).1.trans' (scale_pos k),
        (reflected_bounds hy0 hy rfl).2⟩
  · obtain ⟨p, hp, rfl⟩ := mem_trapRightReflection.1 hx
    have hb := scheduled_bounds hs hp
    exact ⟨(reflected_bounds hb.2.2.1 hb.2.2.2 rfl).1.trans' (scale_pos k),
      (reflected_bounds hb.2.2.1 hb.2.2.2 rfl).2⟩

lemma advance_left_label {ω : ColorSample} {s : StageState} {k : ℕ}
    (hs : GoodState k s) :
    ∀ x ∈ (advance ω k s).left, (advance ω k s).label x = leftColor := by
  intro x hx
  simp only [advance, Finset.mem_union] at hx
  change nextLabel ω s k x = leftColor
  rcases hx with hx | hx
  · rcases hx with hx | hx
    · rcases hx with hx | hx
      · rw [nextLabel_old (hs.left_bound _ hx).2, hs.left_label _ hx]
      · rw [nextLabel_fresh (directLeft_bounds hx).1 (directLeft_bounds hx).2]
        exact (mem_directLeft.1 hx).2.2
    · obtain ⟨y, hy, hy0, hlabel, rfl⟩ := mem_reflectedLeftHoles.1 hx
      exact nextLabel_reflected_leftHole hs hy0 hy hlabel
  · obtain ⟨p, hp, rfl⟩ := mem_trapLeftReflection.1 hx
    exact nextLabel_trap_left hs hp

lemma advance_right_label {ω : ColorSample} {s : StageState} {k : ℕ}
    (hs : GoodState k s) :
    ∀ x ∈ (advance ω k s).right, (advance ω k s).label x = rightColor := by
  intro x hx
  simp only [advance, Finset.mem_union] at hx
  change nextLabel ω s k x = rightColor
  rcases hx with hx | hx
  · rcases hx with hx | hx
    · rcases hx with hx | hx
      · rw [nextLabel_old (hs.right_bound _ hx).2, hs.right_label _ hx]
      · rw [nextLabel_fresh (directRight_bounds hx).1 (directRight_bounds hx).2]
        exact (mem_directRight.1 hx).2.2
    · obtain ⟨y, hy, hy0, hlabel, rfl⟩ := mem_reflectedRightHoles.1 hx
      exact nextLabel_reflected_rightHole hs hy0 hy hlabel
  · obtain ⟨p, hp, rfl⟩ := mem_trapRightReflection.1 hx
    exact nextLabel_trap_right hs hp

lemma advance_disjoint {ω : ColorSample} {s : StageState} {k : ℕ}
    (hs : GoodState k s) : Disjoint (advance ω k s).left (advance ω k s).right := by
  rw [Finset.disjoint_left]
  intro x hxL hxR
  have hL := advance_left_label hs x hxL
  have hR := advance_right_label hs x hxR
  rw [hL] at hR
  norm_num [leftColor, rightColor] at hR

lemma advance_known_colors {ω : ColorSample} {s : StageState} {k : ℕ}
    (hs : GoodState k s) :
    ∀ p ∈ (advance ω k s).known,
      p.1 ∈ (advance ω k s).left ∧ p.2 ∈ (advance ω k s).right := by
  intro p hp
  change p ∈ available s k at hp
  obtain ⟨hp1, hp2⟩ := mem_available_colors hs hp
  exact ⟨left_mono_step ω s k hp1, right_mono_step ω s k hp2⟩

lemma advance_used_known {ω : ColorSample} {s : StageState} {k : ℕ}
    (hs : GoodState k s) : (advance ω k s).used ⊆ (advance ω k s).known := by
  intro p hp
  change p ∈ available s k
  simp only [advance] at hp
  cases hopt : scheduled s k with
  | none =>
      simp only [hopt] at hp
      exact Finset.mem_union_left _ (hs.used_known hp)
  | some q =>
      simp only [hopt] at hp
      rcases Finset.mem_insert.1 hp with rfl | hp
      · exact scheduled_mem_available hopt
      · exact Finset.mem_union_left _ (hs.used_known hp)

lemma advance_used_card_lt {ω : ColorSample} {s : StageState} {k : ℕ}
    (hs : GoodState k s) : (advance ω k s).used.card < k + 1 := by
  by_cases hk : k = 0
  · subst k
    have hnone : scheduled s 0 = none := by simp [scheduled, active]
    simp [advance, hnone, hs.used_zero rfl]
  · have hkpos : 0 < k := by omega
    have hu := hs.used_card_lt hkpos
    cases hopt : scheduled s k with
    | none => simpa [advance, hopt] using hu.trans (Nat.lt_succ_self k)
    | some p =>
        have hc : (insert p s.used).card ≤ s.used.card + 1 := Finset.card_insert_le _ _
        change (match scheduled s k with
          | none => s.used
          | some q => insert q s.used).card < k + 1
        rw [hopt]
        exact hc.trans_lt (by omega)

lemma good_advance {ω : ColorSample} {s : StageState} {k : ℕ}
    (hs : GoodState k s) : GoodState (k + 1) (advance ω k s) where
  left_bound := advance_left_bound hs
  right_bound := advance_right_bound hs
  left_label := advance_left_label hs
  right_label := advance_right_label hs
  disjoint := advance_disjoint hs
  known_colors := advance_known_colors hs
  used_known := advance_used_known hs
  used_zero := by omega
  used_card_lt := fun _ ↦ advance_used_card_lt hs

lemma good_build (ω : ColorSample) (k : ℕ) : GoodState k (build ω k) := by
  induction k with
  | zero =>
      exact {
        left_bound := by simp
        right_bound := by simp
        left_label := by simp
        right_label := by simp
        disjoint := by simp
        known_colors := by simp
        used_known := by simp
        used_zero := by simp
        used_card_lt := by omega }
  | succ k ih => exact good_advance ih

lemma scheduled_exists_of_active {ω : ColorSample} {k : ℕ}
    (ha : active (build ω k) k) :
    ∃ p, scheduled (build ω k) k = some p := by
  exact scheduled_some_of_active_of_card_used_lt ha ((good_build ω k).used_card_lt ha.1)

def WasEligible (ω : ColorSample) (k : ℕ) (p : Trap) : Prop :=
  ∃ i < k, p ∈ eligible (build ω i) i

lemma mem_build_known_iff {ω : ColorSample} {k : ℕ} {p : Trap} :
    p ∈ (build ω k).known ↔ WasEligible ω k p := by
  induction k with
  | zero => simp [WasEligible]
  | succ k ih =>
      rw [build_succ]
      change p ∈ available (build ω k) k ↔ _
      simp only [available, Finset.mem_union, ih]
      constructor
      · rintro (⟨i, hi, hp⟩ | hp)
        · exact ⟨i, by omega, hp⟩
        · exact ⟨k, by omega, hp⟩
      · rintro ⟨i, hi, hp⟩
        by_cases hik : i = k
        · right
          simpa [hik] using hp
        · left
          exact ⟨i, by omega, hp⟩

def ScheduledAt (ω : ColorSample) (k : ℕ) (p : Trap) : Prop :=
  scheduled (build ω k) k = some p

lemma scheduledAt_wasEligible {ω : ColorSample} {k : ℕ} {p : Trap}
    (hp : ScheduledAt ω k p) : ∃ i ≤ k, p ∈ eligible (build ω i) i := by
  have hm := scheduled_mem_available hp
  rcases Finset.mem_union.1 hm with hm | hm
  · obtain ⟨i, hi, hip⟩ := mem_build_known_iff.1 hm
    exact ⟨i, Nat.le_of_lt hi, hip⟩
  · exact ⟨k, le_rfl, hm⟩

lemma scheduledAt_mem_used_succ {ω : ColorSample} {k : ℕ} {p : Trap}
    (hp : ScheduledAt ω k p) : p ∈ (build ω (k + 1)).used := by
  rw [build_succ]
  change p ∈ (match scheduled (build ω k) k with
    | none => (build ω k).used
    | some q => insert q (build ω k).used)
  rw [hp]
  simp

lemma scheduledAt_ne_of_lt {ω : ColorSample} {i j : ℕ} {p q : Trap}
    (hij : i < j) (hi : ScheduledAt ω i p) (hj : ScheduledAt ω j q) : p ≠ q := by
  intro hpq
  subst q
  have hused0 := scheduledAt_mem_used_succ hi
  have hused : p ∈ (build ω j).used := used_mono (Nat.succ_le_iff.2 hij) hused0
  exact scheduled_not_used hj hused

lemma scheduledAt_stage_injective {ω : ColorSample} {i j : ℕ} {p : Trap}
    (hi : ScheduledAt ω i p) (hj : ScheduledAt ω j p) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact (scheduledAt_ne_of_lt h hi hj rfl).elim
  · exact h
  · exact (scheduledAt_ne_of_lt h hj hi rfl).elim

lemma scheduledAt_colors {ω : ColorSample} {k : ℕ} {p : Trap}
    (hp : ScheduledAt ω k p) :
    p.1 ∈ (build ω k).left ∧ p.2 ∈ (build ω k).right :=
  scheduled_colors (good_build ω k) hp

lemma scheduledAt_bounds {ω : ColorSample} {k : ℕ} {p : Trap}
    (hp : ScheduledAt ω k p) :
    0 < p.1 ∧ p.1 < scale k ∧ 0 < p.2 ∧ p.2 < scale k :=
  scheduled_bounds (good_build ω k) hp

lemma scheduledAt_own_representations {ω : ColorSample} {k : ℕ} {p : Trap}
    (hp : ScheduledAt ω k p) :
    scale (k + 1) ∈
        (↑(build ω (k + 1)).left : Set ℕ) + (↑(build ω (k + 1)).left : Set ℕ) ∧
      scale (k + 1) ∈
        (↑(build ω (k + 1)).right : Set ℕ) + (↑(build ω (k + 1)).right : Set ℕ) := by
  have hc := scheduledAt_colors hp
  have hb := scheduledAt_bounds hp
  constructor
  · refine ⟨p.1, left_mono_step ω (build ω k) k hc.1,
      scale (k + 1) - p.1, ?_, ?_⟩
    · rw [build_succ]
      change scale (k + 1) - p.1 ∈
        (build ω k).left ∪ directLeft ω k ∪ reflectedLeftHoles (build ω k) k ∪
          trapLeftReflection (build ω k) k
      exact Finset.mem_union_right _ (mem_trapLeftReflection.2 ⟨p, hp, rfl⟩)
    · have hle : p.1 ≤ scale (k + 1) :=
        (Nat.le_of_lt hb.2.1).trans (scale_strictMono.monotone (by omega))
      exact Nat.add_sub_of_le hle
  · refine ⟨p.2, right_mono_step ω (build ω k) k hc.2,
      scale (k + 1) - p.2, ?_, ?_⟩
    · rw [build_succ]
      change scale (k + 1) - p.2 ∈
        (build ω k).right ∪ directRight ω k ∪ reflectedRightHoles (build ω k) k ∪
          trapRightReflection (build ω k) k
      exact Finset.mem_union_right _ (mem_trapRightReflection.2 ⟨p, hp, rfl⟩)
    · have hle : p.2 ≤ scale (k + 1) :=
        (Nat.le_of_lt hb.2.2.2).trans (scale_strictMono.monotone (by omega))
      exact Nat.add_sub_of_le hle

lemma mem_build_used_imp_scheduled {ω : ColorSample} {k : ℕ} {p : Trap}
    (hp : p ∈ (build ω k).used) : ∃ i < k, ScheduledAt ω i p := by
  induction k with
  | zero => simp at hp
  | succ k ih =>
      rw [build_succ] at hp
      simp only [advance] at hp
      cases hopt : scheduled (build ω k) k with
      | none =>
          simp only [hopt] at hp
          obtain ⟨i, hi, hip⟩ := ih hp
          exact ⟨i, by omega, hip⟩
      | some q =>
          simp only [hopt] at hp
          rcases Finset.mem_insert.1 hp with rfl | hp
          · exact ⟨k, by omega, hopt⟩
          · obtain ⟨i, hi, hip⟩ := ih hp
            exact ⟨i, by omega, hip⟩

noncomputable def stageTrap (ω : ColorSample) (k : ℕ) : Trap :=
  (scheduled (build ω k) k).getD (0, 0)

lemma stageTrap_eq_of_scheduledAt {ω : ColorSample} {k : ℕ} {p : Trap}
    (hp : ScheduledAt ω k p) : stageTrap ω k = p := by
  unfold ScheduledAt at hp
  unfold stageTrap
  rw [hp]
  rfl

lemma stageTrap_scheduledAt_of_active {ω : ColorSample} {k : ℕ}
    (ha : active (build ω k) k) : ScheduledAt ω k (stageTrap ω k) := by
  obtain ⟨p, hp⟩ := scheduled_exists_of_active ha
  rw [stageTrap_eq_of_scheduledAt hp]
  exact hp

lemma scheduledAt_containing_bound {ω : ColorSample} {k d : ℕ} {p : Trap}
    (hp : ScheduledAt ω k p) (hd : p.1 = d ∨ p.2 = d) :
    p.1 ≤ scale d ∧ p.2 ≤ scale d := by
  obtain ⟨i, hik, hi⟩ := scheduledAt_wasEligible hp
  have hei := Finset.mem_filter.1 hi
  have hbounds := hei.2
  have hid : i ≤ d := by rcases hd with rfl | rfl <;> omega
  have hscale : scale i ≤ scale d := scale_strictMono.monotone hid
  exact ⟨hbounds.2.1.trans hscale, hbounds.2.2.2.trans hscale⟩

def incidenceStages (ω : ColorSample) (d : ℕ) : Set ℕ :=
  {k | ∃ p, ScheduledAt ω k p ∧ (p.1 = d ∨ p.2 = d)}

lemma incidenceStages_finite (ω : ColorSample) (d : ℕ) :
    (incidenceStages ω d).Finite := by
  let pool : Finset Trap :=
    (Finset.range (scale d + 1)).product (Finset.range (scale d + 1))
  have himage : stageTrap ω '' incidenceStages ω d ⊆ (↑pool : Set Trap) := by
    rintro q ⟨k, ⟨p, hp, hd⟩, rfl⟩
    rw [stageTrap_eq_of_scheduledAt hp]
    have hb := scheduledAt_containing_bound hp hd
    simp [pool, hb]
  have hfinite : (stageTrap ω '' incidenceStages ω d).Finite :=
    (pool.finite_toSet.subset himage)
  apply hfinite.of_finite_image
  intro i hi j hj hij
  obtain ⟨p, hip, _⟩ := hi
  obtain ⟨q, hjp, _⟩ := hj
  have his : ScheduledAt ω i (stageTrap ω i) := by
    rw [stageTrap_eq_of_scheduledAt hip]
    exact hip
  have hjs : ScheduledAt ω j (stageTrap ω j) := by
    rw [stageTrap_eq_of_scheduledAt hjp]
    exact hjp
  rw [hij] at his
  exact scheduledAt_stage_injective his hjs

theorem scheduler_fair {ω : ColorSample} {k₀ : ℕ} {p : Trap}
    (hp : WasEligible ω k₀ p)
    (hactive : ∃ K, ∀ k, K ≤ k → active (build ω k) k) :
    ∃ k, ScheduledAt ω k p := by
  by_contra hnever
  push_neg at hnever
  obtain ⟨K, hK⟩ := hactive
  let L := max k₀ K
  let pool : Finset Trap :=
    (Finset.range (trapMax p + 1)).product (Finset.range (trapMax p + 1))
  have hpknown : ∀ k, L ≤ k → p ∈ (build ω k).known := by
    intro k hk
    have hp0 : p ∈ (build ω k₀).known := mem_build_known_iff.2 hp
    exact known_mono (le_trans (Nat.le_max_left _ _) hk) hp0
  have hpcandidate : ∀ k, L ≤ k → p ∈ candidates (build ω k) k := by
    intro k hk
    apply Finset.mem_sdiff.2
    constructor
    · exact Finset.mem_union_left _ (hpknown k hk)
    · intro hpused
      obtain ⟨i, _hi, hip⟩ := mem_build_used_imp_scheduled hpused
      exact hnever i hip
  have hstage : ∀ k, L ≤ k → ScheduledAt ω k (stageTrap ω k) := by
    intro k hk
    apply stageTrap_scheduledAt_of_active
    exact hK k (le_trans (Nat.le_max_right _ _) hk)
  have himage : stageTrap ω '' Set.Ici L ⊆ (↑pool : Set Trap) := by
    rintro q ⟨k, hk, rfl⟩
    have hs := hstage k hk
    have hm := scheduled_max_le hs (hpcandidate k hk)
    have h1 : (stageTrap ω k).1 ≤ trapMax p :=
      le_trans (Nat.le_max_left _ _) hm
    have h2 : (stageTrap ω k).2 ≤ trapMax p :=
      le_trans (Nat.le_max_right _ _) hm
    simp [pool, h1, h2]
  have hfiniteImage : (stageTrap ω '' Set.Ici L).Finite :=
    pool.finite_toSet.subset himage
  have hinj : Set.InjOn (stageTrap ω) (Set.Ici L) := by
    intro i hi j hj hij
    have his := hstage i hi
    rw [hij] at his
    exact scheduledAt_stage_injective his (hstage j hj)
  have hfinite : (Set.Ici L).Finite := hfiniteImage.of_finite_image hinj
  exact (Set.Ici_infinite L).not_finite hfinite

def finalLeft (ω : ColorSample) : Set ℕ :=
  stageLimit fun k ↦ (build ω k).left

def finalRight (ω : ColorSample) : Set ℕ :=
  stageLimit fun k ↦ (build ω k).right

lemma mem_finalLeft_of_stage {ω : ColorSample} {k x : ℕ}
    (hx : x ∈ (build ω k).left) : x ∈ finalLeft ω := ⟨k, hx⟩

lemma mem_finalRight_of_stage {ω : ColorSample} {k x : ℕ}
    (hx : x ∈ (build ω k).right) : x ∈ finalRight ω := ⟨k, hx⟩

lemma finalLeft_disjoint_finalRight (ω : ColorSample) :
    Disjoint (finalLeft ω) (finalRight ω) := by
  rw [Set.disjoint_left]
  rintro x ⟨i, hi⟩ ⟨j, hj⟩
  have hi' := left_mono (le_max_left i j) hi
  have hj' := right_mono (le_max_right i j) hj
  exact Finset.disjoint_left.1 (good_build ω (max i j)).disjoint hi' hj'

lemma directLeft_mem_final {ω : ColorSample} {k x : ℕ}
    (hx : x ∈ directLeft ω k) : x ∈ finalLeft ω := by
  apply mem_finalLeft_of_stage (k := k + 1)
  rw [build_succ]
  change x ∈ (build ω k).left ∪ directLeft ω k ∪ reflectedLeftHoles (build ω k) k ∪
    trapLeftReflection (build ω k) k
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hx))

lemma directRight_mem_final {ω : ColorSample} {k x : ℕ}
    (hx : x ∈ directRight ω k) : x ∈ finalRight ω := by
  apply mem_finalRight_of_stage (k := k + 1)
  rw [build_succ]
  change x ∈ (build ω k).right ∪ directRight ω k ∪ reflectedRightHoles (build ω k) k ∪
    trapRightReflection (build ω k) k
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hx))

lemma directLeft_mem_final_of_raw {ω : ColorSample} {k x : ℕ}
    (hx : (4 * scale k < 3 * x ∧ x < 2 * scale k) ∨
      (8 * scale k < 3 * x ∧ x < 3 * scale k))
    (hcolor : ω x = leftColor) : x ∈ finalLeft ω := by
  apply directLeft_mem_final (k := k)
  rw [mem_directLeft]
  rw [scale_succ]
  constructor
  · rcases hx with hx | hx <;> omega
  · exact ⟨hx, hcolor⟩

lemma directRight_mem_final_of_raw {ω : ColorSample} {k x : ℕ}
    (hx : (4 * scale k < 3 * x ∧ x < 2 * scale k) ∨
      (8 * scale k < 3 * x ∧ x < 3 * scale k))
    (hcolor : ω x = rightColor) : x ∈ finalRight ω := by
  apply directRight_mem_final (k := k)
  rw [mem_directRight]
  rw [scale_succ]
  constructor
  · rcases hx with hx | hx <;> omega
  · exact ⟨hx, hcolor⟩

lemma rawFreshLabel {ω : ColorSample} {k y : ℕ}
    (hy0 : scale k < y) (hy1 : y < 3 * scale k) :
    (build ω (k + 1)).label y = ω y := by
  rw [build_succ]
  exact nextLabel_fresh hy0 hy1

lemma rawHole_reflection_mem_finalLeft {ω : ColorSample} {k y : ℕ}
    (hy0 : scale k < y) (hy1 : y < 3 * scale k)
    (hcolor : ω y = leftHole) :
    scale (k + 2) - y ∈ finalLeft ω := by
  apply mem_finalLeft_of_stage (k := k + 2)
  rw [show k + 2 = (k + 1) + 1 by omega, build_succ]
  change scale (k + 2) - y ∈
    (build ω (k + 1)).left ∪ directLeft ω (k + 1) ∪
      reflectedLeftHoles (build ω (k + 1)) (k + 1) ∪
        trapLeftReflection (build ω (k + 1)) (k + 1)
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  apply mem_reflectedLeftHoles.2
  refine ⟨y, ?_, (scale_pos k).trans hy0, ?_, rfl⟩
  · rw [scale_succ]
    omega
  · rw [rawFreshLabel hy0 hy1, hcolor]

lemma rawHole_reflection_mem_finalRight {ω : ColorSample} {k y : ℕ}
    (hy0 : scale k < y) (hy1 : y < 3 * scale k)
    (hcolor : ω y = rightHole) :
    scale (k + 2) - y ∈ finalRight ω := by
  apply mem_finalRight_of_stage (k := k + 2)
  rw [show k + 2 = (k + 1) + 1 by omega, build_succ]
  change scale (k + 2) - y ∈
    (build ω (k + 1)).right ∪ directRight ω (k + 1) ∪
      reflectedRightHoles (build ω (k + 1)) (k + 1) ∪
        trapRightReflection (build ω (k + 1)) (k + 1)
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  apply mem_reflectedRightHoles.2
  refine ⟨y, ?_, (scale_pos k).trans hy0, ?_, rfl⟩
  · rw [scale_succ]
    omega
  · rw [rawFreshLabel hy0 hy1, hcolor]

lemma advance_left_old_of_le {ω : ColorSample} {s : StageState} {k x : ℕ}
    (hs : GoodState k s) (hx : x ∈ (advance ω k s).left) (hxN : x ≤ scale k) :
    x ∈ s.left := by
  simp only [advance, Finset.mem_union] at hx
  rcases hx with hx | hx
  · rcases hx with hx | hx
    · rcases hx with hx | hx
      · exact hx
      · have := (directLeft_bounds hx).1
        omega
    · obtain ⟨y, hy, hy0, _, rfl⟩ := mem_reflectedLeftHoles.1 hx
      have := (reflected_bounds hy0 hy rfl).1
      omega
  · obtain ⟨p, hp, rfl⟩ := mem_trapLeftReflection.1 hx
    have hb := scheduled_bounds hs hp
    have := (reflected_bounds hb.1 hb.2.1 rfl).1
    omega

lemma advance_right_old_of_le {ω : ColorSample} {s : StageState} {k x : ℕ}
    (hs : GoodState k s) (hx : x ∈ (advance ω k s).right) (hxN : x ≤ scale k) :
    x ∈ s.right := by
  simp only [advance, Finset.mem_union] at hx
  rcases hx with hx | hx
  · rcases hx with hx | hx
    · rcases hx with hx | hx
      · exact hx
      · have := (directRight_bounds hx).1
        omega
    · obtain ⟨y, hy, hy0, _, rfl⟩ := mem_reflectedRightHoles.1 hx
      have := (reflected_bounds hy0 hy rfl).1
      omega
  · obtain ⟨p, hp, rfl⟩ := mem_trapRightReflection.1 hx
    have hb := scheduled_bounds hs hp
    have := (reflected_bounds hb.2.2.1 hb.2.2.2 rfl).1
    omega

lemma build_left_stable_below (ω : ColorSample) {i k x : ℕ} (hik : i ≤ k)
    (hx : x ∈ (build ω k).left) (hxi : x ≤ scale i) : x ∈ (build ω i).left := by
  induction k with
  | zero =>
      have : i = 0 := by omega
      subst i
      exact hx
  | succ k ih =>
      rcases Nat.eq_or_lt_of_le hik with rfl | hik'
      · exact hx
      · apply ih (Nat.le_of_lt_succ hik')
        apply advance_left_old_of_le (good_build ω k) (by simpa [build] using hx)
        exact hxi.trans (scale_strictMono.monotone (Nat.le_of_lt_succ hik'))

lemma build_right_stable_below (ω : ColorSample) {i k x : ℕ} (hik : i ≤ k)
    (hx : x ∈ (build ω k).right) (hxi : x ≤ scale i) : x ∈ (build ω i).right := by
  induction k with
  | zero =>
      have : i = 0 := by omega
      subst i
      exact hx
  | succ k ih =>
      rcases Nat.eq_or_lt_of_le hik with rfl | hik'
      · exact hx
      · apply ih (Nat.le_of_lt_succ hik')
        apply advance_right_old_of_le (good_build ω k) (by simpa [build] using hx)
        exact hxi.trans (scale_strictMono.monotone (Nat.le_of_lt_succ hik'))

lemma finalLeft_mem_build_of_le {ω : ColorSample} {i x : ℕ} (hx : x ∈ finalLeft ω)
    (hxi : x ≤ scale i) : x ∈ (build ω i).left := by
  obtain ⟨j, hj⟩ := hx
  rcases le_total j i with hji | hij
  · exact left_mono hji hj
  · exact build_left_stable_below ω hij hj hxi

lemma finalRight_mem_build_of_le {ω : ColorSample} {i x : ℕ} (hx : x ∈ finalRight ω)
    (hxi : x ≤ scale i) : x ∈ (build ω i).right := by
  obtain ⟨j, hj⟩ := hx
  rcases le_total j i with hji | hij
  · exact right_mono hji hj
  · exact build_right_stable_below ω hij hj hxi

lemma finalUnion_mem_build_of_le {ω : ColorSample} {i x : ℕ}
    (hx : x ∈ finalLeft ω ∪ finalRight ω) (hxi : x ≤ scale i) :
    x ∈ (build ω i).left ∪ (build ω i).right := by
  rcases hx with hx | hx
  · exact Finset.mem_union_left _ (finalLeft_mem_build_of_le hx hxi)
  · exact Finset.mem_union_right _ (finalRight_mem_build_of_le hx hxi)

lemma advance_union_cases {ω : ColorSample} {s : StageState} {k x : ℕ} :
    x ∈ (advance ω k s).left ∪ (advance ω k s).right ↔
      x ∈ s.left ∪ s.right ∨ x ∈ directLeft ω k ∨ x ∈ directRight ω k ∨
        x ∈ reflectedLeftHoles s k ∨ x ∈ reflectedRightHoles s k ∨
          x ∈ trapLeftReflection s k ∨ x ∈ trapRightReflection s k := by
  simp only [advance, Finset.mem_union]
  tauto

lemma not_mem_advance_gap {ω : ColorSample} {s : StageState} {k z : ℕ}
    (hs : GoodState k s) (hlo : 2 * scale k < z) (hhi : 3 * z ≤ 8 * scale k) :
    z ∉ (advance ω k s).left ∪ (advance ω k s).right := by
  intro hz
  rw [advance_union_cases] at hz
  rcases hz with hz | hz | hz | hz | hz | hz | hz
  · rcases Finset.mem_union.1 hz with hz | hz
    · have := (hs.left_bound z hz).2
      omega
    · have := (hs.right_bound z hz).2
      omega
  · rcases (mem_directLeft.1 hz).2.1 with hm | hm <;> omega
  · rcases (mem_directRight.1 hz).2.1 with hm | hm <;> omega
  · obtain ⟨y, hy, hy0, _, rfl⟩ := mem_reflectedLeftHoles.1 hz
    have := reflected_gt_three hy rfl
    omega
  · obtain ⟨y, hy, hy0, _, rfl⟩ := mem_reflectedRightHoles.1 hz
    have := reflected_gt_three hy rfl
    omega
  · obtain ⟨p, hp, rfl⟩ := mem_trapLeftReflection.1 hz
    have hb := scheduled_bounds hs hp
    have := reflected_gt_three hb.2.1 rfl
    omega
  · obtain ⟨p, hp, rfl⟩ := mem_trapRightReflection.1 hz
    have hb := scheduled_bounds hs hp
    have := reflected_gt_three hb.2.2.2 rfl
    omega

lemma small_endpoint_old {ω : ColorSample} {s : StageState} {k a : ℕ}
    (hs : GoodState k s)
    (ha : a ∈ (advance ω k s).left ∪ (advance ω k s).right)
    (ha2 : a ≤ 2 * scale k)
    (href : scale (k + 1) - a ∈
      (advance ω k s).left ∪ (advance ω k s).right) :
    a ∈ s.left ∪ s.right := by
  rw [advance_union_cases] at ha
  rcases ha with ha | ha | ha | ha | ha | ha | ha
  · exact ha
  · rcases (mem_directLeft.1 ha).2.1 with hm | hm
    · exfalso
      apply not_mem_advance_gap hs (z := scale (k + 1) - a) (by
        rw [scale_succ]
        omega) (by rw [scale_succ]; omega) href
    · omega
  · rcases (mem_directRight.1 ha).2.1 with hm | hm
    · exfalso
      apply not_mem_advance_gap hs (z := scale (k + 1) - a) (by
        rw [scale_succ]
        omega) (by rw [scale_succ]; omega) href
    · omega
  · obtain ⟨y, hy, hy0, _, rfl⟩ := mem_reflectedLeftHoles.1 ha
    have := reflected_gt_three hy rfl
    omega
  · obtain ⟨y, hy, hy0, _, rfl⟩ := mem_reflectedRightHoles.1 ha
    have := reflected_gt_three hy rfl
    omega
  · obtain ⟨p, hp, rfl⟩ := mem_trapLeftReflection.1 ha
    have hb := scheduled_bounds hs hp
    have := reflected_gt_three hb.2.1 rfl
    omega
  · obtain ⟨p, hp, rfl⟩ := mem_trapRightReflection.1 ha
    have hb := scheduled_bounds hs hp
    have := reflected_gt_three hb.2.2.2 rfl
    omega

noncomputable def scheduledSet (s : StageState) (k : ℕ) : Finset ℕ :=
  match scheduled s k with
  | none => ∅
  | some p => {p.1, p.2}

lemma mem_scheduledSet_iff {s : StageState} {k a : ℕ} :
    a ∈ scheduledSet s k ↔
      ∃ p, scheduled s k = some p ∧ (a = p.1 ∨ a = p.2) := by
  unfold scheduledSet
  split <;> simp_all

lemma old_complement_forces_trap {ω : ColorSample} {s : StageState} {k a : ℕ}
    (hs : GoodState k s) (ha : a ∈ s.left ∪ s.right)
    (href : scale (k + 1) - a ∈
      (advance ω k s).left ∪ (advance ω k s).right) :
    a ∈ scheduledSet s k := by
  have ha0 : 0 < a := by
    rcases Finset.mem_union.1 ha with ha | ha
    · exact (hs.left_bound _ ha).1
    · exact (hs.right_bound _ ha).1
  have haN : a < scale k := by
    rcases Finset.mem_union.1 ha with ha | ha
    · exact (hs.left_bound _ ha).2
    · exact (hs.right_bound _ ha).2
  have halabel : s.label a = leftColor ∨ s.label a = rightColor := by
    rcases Finset.mem_union.1 ha with ha | ha
    · exact Or.inl (hs.left_label _ ha)
    · exact Or.inr (hs.right_label _ ha)
  rw [advance_union_cases] at href
  rcases href with href | href | href | href | href | href | href
  · rcases Finset.mem_union.1 href with href | href
    · have := (hs.left_bound _ href).2
      rw [scale_succ] at *
      omega
    · have := (hs.right_bound _ href).2
      rw [scale_succ] at *
      omega
  · have hb := (directLeft_bounds href).2
    rw [scale_succ] at *
    omega
  · have hb := (directRight_bounds href).2
    rw [scale_succ] at *
    omega
  · obtain ⟨y, hy, hy0, hylabel, heq⟩ := mem_reflectedLeftHoles.1 href
    rw [scale_succ] at heq
    have hay : a = y := by omega
    subst y
    rcases halabel with halabel | halabel
    · have hbad := halabel.symm.trans hylabel
      exact False.elim ((by decide : leftColor ≠ leftHole) hbad)
    · have hbad := halabel.symm.trans hylabel
      exact False.elim ((by decide : rightColor ≠ leftHole) hbad)
  · obtain ⟨y, hy, hy0, hylabel, heq⟩ := mem_reflectedRightHoles.1 href
    rw [scale_succ] at heq
    have hay : a = y := by omega
    subst y
    rcases halabel with halabel | halabel
    · have hbad := halabel.symm.trans hylabel
      exact False.elim ((by decide : leftColor ≠ rightHole) hbad)
    · have hbad := halabel.symm.trans hylabel
      exact False.elim ((by decide : rightColor ≠ rightHole) hbad)
  · obtain ⟨p, hp, heq⟩ := mem_trapLeftReflection.1 href
    have hpN := (scheduled_bounds hs hp).2.1
    rw [mem_scheduledSet_iff]
    refine ⟨p, hp, Or.inl ?_⟩
    rw [scale_succ] at heq
    omega
  · obtain ⟨p, hp, heq⟩ := mem_trapRightReflection.1 href
    have hpN := (scheduled_bounds hs hp).2.2.2
    rw [mem_scheduledSet_iff]
    refine ⟨p, hp, Or.inr ?_⟩
    rw [scale_succ] at heq
    omega

lemma advance_exceptional_meets_trap {ω : ColorSample} {s : StageState} {k x y : ℕ}
    (hs : GoodState k s)
    (hx : x ∈ (advance ω k s).left ∪ (advance ω k s).right)
    (hy : y ∈ (advance ω k s).left ∪ (advance ω k s).right)
    (hsum : x + y = scale (k + 1)) :
    x ∈ scheduledSet s k ∨ y ∈ scheduledSet s k := by
  by_cases hxy : x ≤ y
  · have hx2 : x ≤ 2 * scale k := by rw [scale_succ] at hsum; omega
    have hyref : y = scale (k + 1) - x := by omega
    left
    apply old_complement_forces_trap hs
    · apply small_endpoint_old hs hx hx2
      simpa [← hyref] using hy
    · simpa [← hyref] using hy
  · have hyx : y ≤ x := by omega
    have hy2 : y ≤ 2 * scale k := by rw [scale_succ] at hsum; omega
    have hxref : x = scale (k + 1) - y := by omega
    right
    apply old_complement_forces_trap hs
    · apply small_endpoint_old hs hy hy2
      simpa [← hxref] using hx
    · simpa [← hxref] using hx

lemma final_exceptional_meets_trap {ω : ColorSample} {k x y : ℕ}
    (hx : x ∈ finalLeft ω ∪ finalRight ω)
    (hy : y ∈ finalLeft ω ∪ finalRight ω)
    (hsum : x + y = scale (k + 1)) :
    x ∈ scheduledSet (build ω k) k ∨ y ∈ scheduledSet (build ω k) k := by
  have hxle : x ≤ scale (k + 1) := by omega
  have hyle : y ≤ scale (k + 1) := by omega
  have hx' := finalUnion_mem_build_of_le hx hxle
  have hy' := finalUnion_mem_build_of_le hy hyle
  simpa [build] using advance_exceptional_meets_trap (good_build ω k) hx' hy' hsum

lemma hundred_mul_le_scale {M : ℕ} (hM : 4 ≤ M) : 100 * M ≤ scale M := by
  induction M, hM using Nat.le_induction with
  | base => norm_num [scale]
  | succ M hM ih =>
      rw [scale_succ]
      omega

lemma sparse_window_of_eventual_active (ω : ColorSample)
    (hactive : ∀ᶠ k : ℕ in atTop, active (build ω k) k)
    (D : Set ℕ) (hDsub : D ⊆ finalLeft ω ∪ finalRight ω) (hD : IsBasis2 D) :
    ∀ᶠ M : ℕ in atTop,
      (missingWindow (finalLeft ω) D M).card < 2 ∨
        (missingWindow (finalRight ω) D M).card < 2 := by
  change D.IsAsymptoticAddBasisOfOrder 2 at hD
  rw [Set.isAsymptoticAddBasisOfOrder_iff_atTop] at hD
  obtain ⟨K, hK⟩ := eventually_atTop.1 hactive
  obtain ⟨N, hN⟩ := eventually_atTop.1 hD
  filter_upwards [eventually_ge_atTop (max (max K N) 4)] with M hM
  have hKM : K ≤ M := le_trans (le_max_left K N) (le_trans (le_max_left _ 4) hM)
  have hNM : N ≤ M := le_trans (le_max_right K N) (le_trans (le_max_left _ 4) hM)
  have h4M : 4 ≤ M := le_trans (le_max_right (max K N) 4) hM
  by_contra hsparse
  push Not at hsparse
  have hBL : 0 < (missingWindow (finalLeft ω) D M).card := by omega
  have hBR : 0 < (missingWindow (finalRight ω) D M).card := by omega
  obtain ⟨b, hb⟩ := Finset.card_pos.1 hBL
  obtain ⟨c, hc⟩ := Finset.card_pos.1 hBR
  have hb' := mem_missingWindow.1 hb
  have hc' := mem_missingWindow.1 hc
  have h100 : 100 * M ≤ scale M := hundred_mul_le_scale h4M
  have hbBuild : b ∈ (build ω M).left :=
    finalLeft_mem_build_of_le hb'.1 (hb'.2.2.2.trans h100)
  have hcBuild : c ∈ (build ω M).right :=
    finalRight_mem_build_of_le hc'.1 (hc'.2.2.2.trans h100)
  have hpair : ((b, c) : Trap) ∈ eligible (build ω M) M := by
    simp [eligible, hbBuild, hcBuild, hb'.2.2.1,
      hb'.2.2.2.trans h100, hc'.2.2.1, hc'.2.2.2.trans h100]
  have hwas : WasEligible ω (M + 1) (b, c) := ⟨M, by omega, hpair⟩
  obtain ⟨j, hj⟩ := scheduler_fair hwas ⟨M, fun k hk ↦ hK k (hKM.trans hk)⟩
  have hjbound := scheduledAt_bounds hj
  have hNj : N ≤ scale (j + 1) := by
    have : N ≤ scale j := hNM.trans (hb'.2.2.1.trans (Nat.le_of_lt hjbound.2.1))
    exact this.trans (scale_strictMono.monotone (Nat.le_succ j))
  have hrepr : scale (j + 1) ∈ D + D := by
    simpa [two_nsmul] using hN _ hNj
  rcases hrepr with ⟨x, hx, y, hy, hxy⟩
  have hmeet := final_exceptional_meets_trap (hDsub hx) (hDsub hy) hxy
  rcases hmeet with hmeet | hmeet
  · rw [mem_scheduledSet_iff] at hmeet
    obtain ⟨q, hq, hqend⟩ := hmeet
    have hqeq : q = (b, c) := Option.some.inj (hq.symm.trans hj)
    subst q
    rcases hqend with rfl | rfl
    · exact hb'.2.1 hx
    · exact hc'.2.1 hx
  · rw [mem_scheduledSet_iff] at hmeet
    obtain ⟨q, hq, hqend⟩ := hmeet
    have hqeq : q = (b, c) := Option.some.inj (hq.symm.trans hj)
    subst q
    rcases hqend with rfl | rfl
    · exact hb'.2.1 hy
    · exact hc'.2.1 hy

lemma inactive_finite_of_eventual_active (ω : ColorSample)
    (hactive : ∀ᶠ k : ℕ in atTop, active (build ω k) k) :
    {k | scheduled (build ω k) k = none}.Finite := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 hactive
  apply (Set.finite_Iio K).subset
  intro k hk
  change k < K
  by_contra hnot
  have hKk : K ≤ k := by omega
  obtain ⟨p, hp⟩ := scheduled_exists_of_active (hK k hKk)
  rw [hk] at hp
  contradiction

noncomputable def recursiveCertificate (ω : ColorSample)
    (hactive : ∀ᶠ k : ℕ in atTop, active (build ω k) k)
    (hmanyL : ∀ᶠ M : ℕ in atTop, ∀ n, InShortBlock M n →
      n ∉ exceptional → 2 ≤ (balancedRepr (finalLeft ω) n).card)
    (hmanyR : ∀ᶠ M : ℕ in atTop, ∀ n, InShortBlock M n →
      n ∉ exceptional → 2 ≤ (balancedRepr (finalRight ω) n).card) :
    RecursiveCertificate where
  Bk := fun k ↦ (build ω k).left
  Ck := fun k ↦ (build ω k).right
  Bk_mono := fun _ _ h ↦ left_mono h
  Ck_mono := fun _ _ h ↦ right_mono h
  stage_disjoint := fun k ↦ (good_build ω k).disjoint
  stage_bounded := by
    intro k x hx
    rcases hx with hx | hx
    · exact (Nat.le_of_lt ((good_build ω k).left_bound x hx).2).trans
        (scale_strictMono.monotone (Nat.le_succ k))
    · exact (Nat.le_of_lt ((good_build ω k).right_bound x hx).2).trans
        (scale_strictMono.monotone (Nat.le_succ k))
  scheduled := fun k ↦ scheduled (build ω k) k
  scheduled_left := fun h ↦ (scheduledAt_colors h).1
  scheduled_right := fun h ↦ (scheduledAt_colors h).2
  scheduled_bounded := fun h ↦
    ⟨Nat.le_of_lt (scheduledAt_bounds h).2.1,
      Nat.le_of_lt (scheduledAt_bounds h).2.2.2⟩
  reflected_left := by
    intro k b c h
    rw [build_succ]
    change scale (k + 1) - b ∈
      (build ω k).left ∪ directLeft ω k ∪ reflectedLeftHoles (build ω k) k ∪
        trapLeftReflection (build ω k) k
    exact Finset.mem_union_right _ (mem_trapLeftReflection.2 ⟨(b, c), h, rfl⟩)
  reflected_right := by
    intro k b c h
    rw [build_succ]
    change scale (k + 1) - c ∈
      (build ω k).right ∪ directRight ω k ∪ reflectedRightHoles (build ω k) k ∪
        trapRightReflection (build ω k) k
    exact Finset.mem_union_right _ (mem_trapRightReflection.2 ⟨(b, c), h, rfl⟩)
  inactive_finite := inactive_finite_of_eventual_active ω hactive
  sparse_window := fun D hDsub hD ↦
    sparse_window_of_eventual_active ω hactive D hDsub hD
  trap_fragile := by
    intro k b c h x y hx hy hsum
    have hm := final_exceptional_meets_trap hx hy hsum
    rcases hm with hm | hm
    · rw [mem_scheduledSet_iff] at hm
      obtain ⟨q, hq, hqend⟩ := hm
      have hqeq : q = (b, c) := Option.some.inj (hq.symm.trans h)
      subst q
      exact hqend.elim (fun hx ↦ Or.inl hx) (fun hx ↦ Or.inr (Or.inl hx))
    · rw [mem_scheduledSet_iff] at hm
      obtain ⟨q, hq, hqend⟩ := hm
      have hqeq : q = (b, c) := Option.some.inj (hq.symm.trans h)
      subst q
      exact hqend.elim (fun hy ↦ Or.inr (Or.inr (Or.inl hy)))
        (fun hy ↦ Or.inr (Or.inr (Or.inr hy)))
  fixed_trap_incidence := by
    intro d
    apply (incidenceStages_finite ω d).subset
    rintro k ⟨b, c, h, hd⟩
    exact ⟨(b, c), h, hd.elim (fun h ↦ Or.inl h.symm) (fun h ↦ Or.inr h.symm)⟩
  ordinary_many_left := hmanyL
  ordinary_many_right := hmanyR

end FourBuild

namespace RecursiveCertificate

def left (c : RecursiveCertificate) : Set ℕ := stageLimit c.Bk

def right (c : RecursiveCertificate) : Set ℕ := stageLimit c.Ck

lemma left_disjoint_right (c : RecursiveCertificate) : Disjoint c.left c.right := by
  rw [Set.disjoint_left]
  intro x hxB hxC
  rcases hxB with ⟨i, hi⟩
  rcases hxC with ⟨j, hj⟩
  have hi' : x ∈ c.Bk (max i j) := c.Bk_mono (le_max_left i j) hi
  have hj' : x ∈ c.Ck (max i j) := c.Ck_mono (le_max_right i j) hj
  exact Finset.disjoint_left.1 (c.stage_disjoint (max i j)) hi' hj'

lemma index_le_scale (k : ℕ) : k ≤ scale k := by
  induction k with
  | zero => simp [scale]
  | succ k ih =>
      rw [scale_succ]
      have hs := scale_pos k
      omega

lemma balancedRepr_mem_two_smul {X : Set ℕ} {n : ℕ}
    (h : 0 < (balancedRepr X n).card) : n ∈ 2 • X := by
  obtain ⟨p, hp⟩ := Finset.card_pos.1 h
  have hp' := mem_balancedRepr.1 hp
  have : n ∈ X + X := ⟨p.1, hp'.2.1, p.2, hp'.2.2.1, hp'.2.2.2.1⟩
  simpa [two_nsmul] using this

lemma ordinary_mem_eventually (X E : Set ℕ)
    (hmany : ∀ᶠ M : ℕ in atTop, ∀ n, InShortBlock M n → n ∉ E →
      2 ≤ (balancedRepr X n).card) :
    ∀ᶠ n : ℕ in atTop, n ∉ E → n ∈ 2 • X := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hmany
  filter_upwards [eventually_ge_atTop (101 * M₀)] with n hn hnE
  have hi : M₀ ≤ shortIndex n := shortIndex_ge hn
  have hcard := hM₀ (shortIndex n) hi n (shortIndex_mem_shortBlock n) hnE
  exact balancedRepr_mem_two_smul (by omega)

lemma traps_eventually (c : RecursiveCertificate) :
    ∀ᶠ k : ℕ in atTop, ∃ b c', c.scheduled k = some (b, c') := by
  rw [← Nat.cofinite_eq_atTop]
  have hmem : {k | c.scheduled k = none}ᶜ ∈ cofinite :=
    c.inactive_finite.compl_mem_cofinite
  filter_upwards [hmem] with k hk
  cases h : c.scheduled k with
  | none => exact (hk h).elim
  | some p =>
      rcases p with ⟨b, c'⟩
      exact ⟨b, c', rfl⟩

lemma exceptional_mem_left_eventually (c : RecursiveCertificate) :
    ∀ᶠ n : ℕ in atTop, n ∈ exceptional → n ∈ 2 • c.left := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 c.traps_eventually
  filter_upwards [eventually_ge_atTop (scale (K + 1))] with n hn
  rintro ⟨k, rfl⟩
  have hKk : K ≤ k := by
    have : K + 1 ≤ k + 1 := scale_strictMono.le_iff_le.1 hn
    omega
  obtain ⟨b, c', htrap⟩ := hK k hKk
  have hbsmall : b ≤ scale (k + 1) :=
    (c.scheduled_bounded htrap).1.trans (scale_strictMono.monotone (Nat.le_succ k))
  have hsum : b + (scale (k + 1) - b) = scale (k + 1) :=
    Nat.add_sub_of_le hbsmall
  have hmem : scale (k + 1) ∈ c.left + c.left :=
    ⟨b, ⟨k, c.scheduled_left htrap⟩,
      scale (k + 1) - b, ⟨k + 1, c.reflected_left htrap⟩, hsum⟩
  simpa [two_nsmul] using hmem

lemma exceptional_mem_right_eventually (c : RecursiveCertificate) :
    ∀ᶠ n : ℕ in atTop, n ∈ exceptional → n ∈ 2 • c.right := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 c.traps_eventually
  filter_upwards [eventually_ge_atTop (scale (K + 1))] with n hn
  rintro ⟨k, rfl⟩
  have hKk : K ≤ k := by
    have : K + 1 ≤ k + 1 := scale_strictMono.le_iff_le.1 hn
    omega
  obtain ⟨b, c', htrap⟩ := hK k hKk
  have hcsmall : c' ≤ scale (k + 1) :=
    (c.scheduled_bounded htrap).2.trans (scale_strictMono.monotone (Nat.le_succ k))
  have hsum : c' + (scale (k + 1) - c') = scale (k + 1) :=
    Nat.add_sub_of_le hcsmall
  have hmem : scale (k + 1) ∈ c.right + c.right :=
    ⟨c', ⟨k, c.scheduled_right htrap⟩,
      scale (k + 1) - c', ⟨k + 1, c.reflected_right htrap⟩, hsum⟩
  simpa [two_nsmul] using hmem

lemma left_isBasis2 (c : RecursiveCertificate) : IsBasis2 c.left := by
  change c.left.IsAsymptoticAddBasisOfOrder 2
  rw [Set.isAsymptoticAddBasisOfOrder_iff_atTop]
  have hord := ordinary_mem_eventually c.left exceptional c.ordinary_many_left
  filter_upwards [hord, c.exceptional_mem_left_eventually] with n hnord hnexc
  by_cases hn : n ∈ exceptional
  · exact hnexc hn
  · exact hnord hn

lemma right_isBasis2 (c : RecursiveCertificate) : IsBasis2 c.right := by
  change c.right.IsAsymptoticAddBasisOfOrder 2
  rw [Set.isAsymptoticAddBasisOfOrder_iff_atTop]
  have hord := ordinary_mem_eventually c.right exceptional c.ordinary_many_right
  filter_upwards [hord, c.exceptional_mem_right_eventually] with n hnord hnexc
  by_cases hn : n ∈ exceptional
  · exact hnexc hn
  · exact hnord hn

lemma sparse_side_eventually (c : RecursiveCertificate) (D : Set ℕ)
    (hDsub : D ⊆ c.left ∪ c.right) (hD : IsBasis2 D) :
    ∀ᶠ M : ℕ in atTop,
      (missingWindow c.left D M).card < 2 ∨
        (missingWindow c.right D M).card < 2 :=
  c.sparse_window D hDsub hD

lemma ordinary_survives (c : RecursiveCertificate) (D : Set ℕ)
    (hDsub : D ⊆ c.left ∪ c.right) (hD : IsBasis2 D) (d : ℕ) :
    ∀ᶠ n : ℕ in atTop, n ∉ exceptional → n ∈ 2 • (D \ {d}) := by
  exact ordinary_survives_eventually d
    (c.sparse_side_eventually D hDsub hD)
    c.ordinary_many_left c.ordinary_many_right

def trapIncidence (c : RecursiveCertificate) (d : ℕ) : Set ℕ :=
  {k | ∃ b c', c.scheduled k = some (b, c') ∧ (d = b ∨ d = c')}

def exceptionalIndexWithSummand (c : RecursiveCertificate) (d : ℕ) : Set ℕ :=
  {k | ∃ a ∈ c.left ∪ c.right, d + a = scale (k + 1)}

lemma exceptionalIndexWithSummand_finite (c : RecursiveCertificate) (d : ℕ)
    (hd : d ∈ c.left ∪ c.right) :
    (c.exceptionalIndexWithSummand d).Finite := by
  have hsub : c.exceptionalIndexWithSummand d ⊆
      {k | c.scheduled k = none} ∪ c.trapIncidence d ∪ Set.Iic d := by
    intro k hk
    rcases hk with ⟨a, ha, hsum⟩
    cases htrap : c.scheduled k with
    | none => exact Or.inl (Or.inl htrap)
    | some p =>
        rcases p with ⟨b, c'⟩
        have hhit := c.trap_fragile htrap hd ha hsum
        rcases hhit with hdb | hdc | hab | hac
        · exact Or.inl (Or.inr ⟨b, c', htrap, Or.inl hdb⟩)
        · exact Or.inl (Or.inr ⟨b, c', htrap, Or.inr hdc⟩)
        · right
          have habound : a ≤ scale k := by simpa [hab] using (c.scheduled_bounded htrap).1
          have htarget : d + a = 4 * scale k := by simpa [scale_succ] using hsum
          exact index_le_scale k |>.trans (by omega)
        · right
          have habound : a ≤ scale k := by simpa [hac] using (c.scheduled_bounded htrap).2
          have htarget : d + a = 4 * scale k := by simpa [scale_succ] using hsum
          exact index_le_scale k |>.trans (by omega)
  exact (c.inactive_finite.union (c.fixed_trap_incidence d) |>.union
    (Set.finite_Iic d)).subset hsub

lemma exceptional_summands_finite (c : RecursiveCertificate) (d : ℕ)
    (hd : d ∈ c.left ∪ c.right) :
    {n : ℕ | n ∈ exceptional ∧
      ∃ a ∈ c.left ∪ c.right, d + a = n}.Finite := by
  have hidx : (c.exceptionalIndexWithSummand d).Finite := by
    exact c.exceptionalIndexWithSummand_finite d hd
  apply (hidx.image fun k ↦ scale (k + 1)).subset
  rintro n ⟨⟨k, rfl⟩, a, ha, hsum⟩
  exact ⟨k, ⟨a, ha, hsum⟩, rfl⟩

/-- The deterministic recursive hypotheses imply the compact block certificate
used by the final deletion argument. -/
def toBlockCertificate (c : RecursiveCertificate) : BlockCertificate where
  left := c.left
  right := c.right
  disjoint := c.left_disjoint_right
  left_basis := c.left_isBasis2
  right_basis := c.right_isBasis2
  ordinary_survives := fun D hDsub hD d _hd ↦ c.ordinary_survives D hDsub hD d
  exceptional_summands_finite := fun d hd ↦ c.exceptional_summands_finite d hd

def toCounterexampleCertificate (c : RecursiveCertificate) : CounterexampleCertificate :=
  c.toBlockCertificate.toCounterexampleCertificate

/-- Once the finite recursive construction has supplied the fields above, its
logical consequence is exactly the negative answer to Erdős Problem 869. -/
theorem erdos_869_of_recursiveCertificate (c : RecursiveCertificate) :
    ¬ ∀ (A₁ A₂ : Set ℕ), Disjoint A₁ A₂ →
      IsBasis2 A₁ → IsBasis2 A₂ →
      ∃ D ⊆ A₁ ∪ A₂, IsBasis2 D ∧
        ∀ d ∈ D, ¬ IsBasis2 (D \ {d}) := by
  intro h
  ·
    apply c.toCounterexampleCertificate.refutes_problem
    simpa only [IsMinimalBasis2] using h

end RecursiveCertificate


/-! ## Strict interval pattern families and their simultaneous realization -/

/-! Integrated from /tmp/FourIntervals.lean -/

open MeasureTheory ProbabilityTheory

def P (N : ℕ) : Set ℕ := {x | N < 24 * x ∧ 64 * x < 3 * N}
def Q (N : ℕ) : Set ℕ := {x | 2 * N < 3 * x ∧ 4 * x < 3 * N}
def R (N : ℕ) : Set ℕ := {x | 4 * N < 3 * x ∧ x < 2 * N}
def S (N : ℕ) : Set ℕ := {x | 8 * N < 3 * x ∧ x < 3 * N}
def J (N : ℕ) : Set ℕ := {x | N < 4 * x ∧ 4 * x < 3 * N}

def baseLabel (c : Fin 2) : Color := ⟨c, by omega⟩
def holeLabel (c : Fin 2) : Color := ⟨c + 2, by omega⟩

def directReservoir (N : ℕ) : Set ℕ := P N ∪ Q N ∪ R N ∪ S N

def realizedReservoir (N : ℕ) (c : Fin 2) (ω : ColorSample) : Set ℕ :=
  {x | x ∈ directReservoir N ∧ colorAt x ω = baseLabel c} ∪
  {x | ∃ y ∈ J N, colorAt y ω = holeLabel c ∧ x = 4 * N - y}

def directDesired (c : Fin 2) (_ : Fin 4) : Color := baseLabel c

def directEndpoint (M n L : ℕ) (p : Fin M × Fin 4) : ℕ :=
  match p.2.1 with
  | 0 => L + 2 * p.1.1
  | 1 => n - (L + 2 * p.1.1)
  | 2 => L + 2 * p.1.1 + 1
  | _ => n - (L + 2 * p.1.1 + 1)

lemma directEndpoint_injective (M n L : ℕ) (hsep : 2 * (L + 2 * M) ≤ n) :
    Function.Injective (directEndpoint M n L) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  apply Prod.ext
  · apply Fin.ext
    fin_cases j <;> fin_cases j' <;>
      simp [directEndpoint] at h ⊢ <;> omega
  · apply Fin.ext
    fin_cases j <;> fin_cases j' <;>
      simp [directEndpoint] at h ⊢ <;> omega

def directFamily (M n L : ℕ) (c : Fin 2)
    (hsep : 2 * (L + 2 * M) ≤ n) : PatternFamily 4 where
  count := M
  endpoint := directEndpoint M n L
  endpoint_injective := directEndpoint_injective M n L hsep
  desired := directDesired c

def smallReflectedEndpoint (below : Bool) (M d L : ℕ)
    (p : Fin M × Fin 4) : ℕ :=
  let a := 4 * p.1.1
  match below, p.2.1 with
  | false, 0 => L + d * a
  | false, 1 => L + d * (a + 1)
  | false, 2 => L + d * (a + 2)
  | false, _ => L + d * (a + 3)
  | true, 0 => L + d * (a + 1)
  | true, 1 => L + d * a
  | true, 2 => L + d * (a + 3)
  | true, _ => L + d * (a + 2)

lemma smallReflectedEndpoint_injective (below : Bool) (M d L : ℕ) (hd : 0 < d) :
    Function.Injective (smallReflectedEndpoint below M d L) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  apply Prod.ext
  · apply Fin.ext
    cases below <;> fin_cases j <;> fin_cases j' <;>
      simp [smallReflectedEndpoint] at h ⊢ <;> omega
  · apply Fin.ext
    cases below <;> fin_cases j <;> fin_cases j' <;>
      simp [smallReflectedEndpoint] at h ⊢ <;> omega

def largeReflectedEndpoint (below : Bool) (M d L : ℕ)
    (p : Fin M × Fin 4) : ℕ :=
  let a := L + 2 * p.1.1
  match below, p.2.1 with
  | false, 0 => a
  | false, 1 => a + d
  | false, 2 => a + 1
  | false, _ => a + d + 1
  | true, 0 => a + d
  | true, 1 => a
  | true, 2 => a + d + 1
  | true, _ => a + 1

lemma largeReflectedEndpoint_injective (below : Bool) (M d L : ℕ) (hd : 2 * M ≤ d) :
    Function.Injective (largeReflectedEndpoint below M d L) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  apply Prod.ext
  · apply Fin.ext
    cases below <;> fin_cases j <;> fin_cases j' <;>
      simp [largeReflectedEndpoint] at h ⊢ <;> omega
  · apply Fin.ext
    cases below <;> fin_cases j <;> fin_cases j' <;>
      simp [largeReflectedEndpoint] at h ⊢ <;> omega

def reflectedDesired (c : Fin 2) : Fin 4 → Color
  | ⟨0, _⟩ => holeLabel c
  | ⟨1, _⟩ => baseLabel c
  | ⟨2, _⟩ => holeLabel c
  | _ => baseLabel c

def smallReflectedFamily (below : Bool) (M d L : ℕ) (c : Fin 2) (hd : 0 < d) :
    PatternFamily 4 where
  count := M
  endpoint := smallReflectedEndpoint below M d L
  endpoint_injective := smallReflectedEndpoint_injective below M d L hd
  desired := reflectedDesired c

def largeReflectedFamily (below : Bool) (M d L : ℕ) (c : Fin 2)
    (hd : 2 * M ≤ d) : PatternFamily 4 where
  count := M
  endpoint := largeReflectedEndpoint below M d L
  endpoint_injective := largeReflectedEndpoint_injective below M d L hd
  desired := reflectedDesired c

def FamilyProduces (N n : ℕ) (c : Fin 2) (f : PatternFamily 4) : Prop :=
  ∀ (ω : ColorSample) (i : Fin f.count), patternPresent f i ω = true →
    2 ≤ (balancedRepr (realizedReservoir N c ω) n).card

lemma balancedRepr_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    balancedRepr A n ⊆ balancedRepr B n := by
  intro p hp
  rw [mem_balancedRepr] at hp ⊢
  exact ⟨hp.1, hAB hp.2.1, hAB hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2⟩

lemma FamilyProduces.mono {N n : ℕ} {c : Fin 2} {f : PatternFamily 4}
    (hf : FamilyProduces N n c f) (A : ColorSample → Set ℕ)
    (hsub : ∀ ω, realizedReservoir N c ω ⊆ A ω) :
    ∀ (ω : ColorSample) (i : Fin f.count), patternPresent f i ω = true →
      2 ≤ (balancedRepr (A ω) n).card := by
  intro ω i hi
  exact (hf ω i hi).trans
    (Finset.card_le_card (balancedRepr_mono (hsub ω) n))

/-- Abstract adapter from the five reservoir predicates to a recursively built final
set.  This is the only interface the block recursion has to discharge. -/
lemma realizedReservoir_subset (N : ℕ) (c : Fin 2) (ω : ColorSample) (A : Set ℕ)
    (hdirect : ∀ x, x ∈ directReservoir N → colorAt x ω = baseLabel c → x ∈ A)
    (hreflect : ∀ y, y ∈ J N → colorAt y ω = holeLabel c → 4 * N - y ∈ A) :
    realizedReservoir N c ω ⊆ A := by
  rintro x (hx | ⟨y, hyJ, hyc, rfl⟩)
  · exact hdirect x hx.1 hx.2
  · exact hreflect y hyJ hyc

lemma directPatterns_produce (N n : ℕ) (c : Fin 2) (f : PatternFamily 4)
    (hdesired : f.desired = directDesired c)
    (hdata : ∀ i : Fin f.count,
      let x₀ := f.endpoint ⟨i, 0⟩
      let y₀ := f.endpoint ⟨i, 1⟩
      let x₁ := f.endpoint ⟨i, 2⟩
      let y₁ := f.endpoint ⟨i, 3⟩
      x₀ ∈ directReservoir N ∧ y₀ ∈ directReservoir N ∧
      x₁ ∈ directReservoir N ∧ y₁ ∈ directReservoir N ∧
      x₀ ≤ y₀ ∧ x₀ + y₀ = n ∧ y₀ ≤ 100 * x₀ ∧
      x₁ ≤ y₁ ∧ x₁ + y₁ = n ∧ y₁ ≤ 100 * x₁) :
    FamilyProduces N n c f := by
  intro ω i hi
  have hp := (patternPresent_iff f i ω).1 hi
  have hc₀ := hp (0 : Fin 4)
  have hc₁ := hp (1 : Fin 4)
  have hc₂ := hp (2 : Fin 4)
  have hc₃ := hp (3 : Fin 4)
  rw [hdesired] at hc₀ hc₁ hc₂ hc₃
  simp [directDesired] at hc₀ hc₁ hc₂ hc₃
  specialize hdata i
  dsimp only at hdata
  rcases hdata with
    ⟨hx₀, hy₀, hx₁, hy₁, hxy₀, hsum₀, hrat₀, hxy₁, hsum₁, hrat₁⟩
  have hx₀' : f.endpoint ⟨i, 0⟩ ∈ realizedReservoir N c ω :=
    Or.inl ⟨hx₀, hc₀⟩
  have hy₀' : f.endpoint ⟨i, 1⟩ ∈ realizedReservoir N c ω :=
    Or.inl ⟨hy₀, hc₁⟩
  have hx₁' : f.endpoint ⟨i, 2⟩ ∈ realizedReservoir N c ω :=
    Or.inl ⟨hx₁, hc₂⟩
  have hy₁' : f.endpoint ⟨i, 3⟩ ∈ realizedReservoir N c ω :=
    Or.inl ⟨hy₁, hc₃⟩
  have hp₀ : (f.endpoint ⟨i, 0⟩, f.endpoint ⟨i, 1⟩) ∈
      balancedRepr (realizedReservoir N c ω) n :=
    mem_balancedRepr.2 ⟨hxy₀, hx₀', hy₀', hsum₀, hrat₀⟩
  have hp₁ : (f.endpoint ⟨i, 2⟩, f.endpoint ⟨i, 3⟩) ∈
      balancedRepr (realizedReservoir N c ω) n :=
    mem_balancedRepr.2 ⟨hxy₁, hx₁', hy₁', hsum₁, hrat₁⟩
  have hne : (f.endpoint ⟨i, 0⟩, f.endpoint ⟨i, 1⟩) ≠
      (f.endpoint ⟨i, 2⟩, f.endpoint ⟨i, 3⟩) := by
    intro h
    have := congrArg Prod.fst h
    have he := congrArg Prod.snd (f.endpoint_injective this)
    have he' : (0 : Fin 4) = 2 := by simpa using he
    exact (by decide : (0 : Fin 4) ≠ 2) he'
  have : 1 < (balancedRepr (realizedReservoir N c ω) n).card :=
    Finset.one_lt_card.2 ⟨_, hp₀, _, hp₁, hne⟩
  omega

lemma directFamily_produces_of_block (N n M L : ℕ) (c : Fin 2)
    (hsep : 2 * (L + 2 * M) ≤ n)
    (hmem : ∀ x, L ≤ x → x < L + 2 * M →
      x ∈ directReservoir N ∧ n - x ∈ directReservoir N)
    (hratio : ∀ x, L ≤ x → x < L + 2 * M → n - x ≤ 100 * x) :
    FamilyProduces N n c (directFamily M n L c hsep) := by
  apply directPatterns_produce N n c _ rfl
  intro i
  have hi : i.1 < M := i.2
  have hx₀lo : L ≤ L + 2 * i.1 := by omega
  have hx₀hi : L + 2 * i.1 < L + 2 * M := by omega
  have hx₁lo : L ≤ L + 2 * i.1 + 1 := by omega
  have hx₁hi : L + 2 * i.1 + 1 < L + 2 * M := by omega
  have hm₀ := hmem _ hx₀lo hx₀hi
  have hm₁ := hmem _ hx₁lo hx₁hi
  have hr₀ := hratio _ hx₀lo hx₀hi
  have hr₁ := hratio _ hx₁lo hx₁hi
  have hx₀n : L + 2 * i.1 ≤ n := by omega
  have hx₁n : L + 2 * i.1 + 1 ≤ n := by omega
  change
    (L + 2 * i.1 ∈ directReservoir N) ∧
    (n - (L + 2 * i.1) ∈ directReservoir N) ∧
    (L + 2 * i.1 + 1 ∈ directReservoir N) ∧
    (n - (L + 2 * i.1 + 1) ∈ directReservoir N) ∧
    L + 2 * i.1 ≤ n - (L + 2 * i.1) ∧
    (L + 2 * i.1) + (n - (L + 2 * i.1)) = n ∧
    n - (L + 2 * i.1) ≤ 100 * (L + 2 * i.1) ∧
    L + 2 * i.1 + 1 ≤ n - (L + 2 * i.1 + 1) ∧
    (L + 2 * i.1 + 1) + (n - (L + 2 * i.1 + 1)) = n ∧
    n - (L + 2 * i.1 + 1) ≤ 100 * (L + 2 * i.1 + 1)
  exact ⟨hm₀.1, hm₀.2, hm₁.1, hm₁.2, by omega, by omega,
    hr₀, by omega, by omega, hr₁⟩

lemma reflectedPatterns_produce (N n : ℕ) (c : Fin 2) (f : PatternFamily 4)
    (hdesired : f.desired = reflectedDesired c)
    (hdata : ∀ i : Fin f.count,
      let y₀ := f.endpoint ⟨i, 0⟩
      let x₀ := f.endpoint ⟨i, 1⟩
      let y₁ := f.endpoint ⟨i, 2⟩
      let x₁ := f.endpoint ⟨i, 3⟩
      y₀ ∈ J N ∧ x₀ ∈ directReservoir N ∧
      y₁ ∈ J N ∧ x₁ ∈ directReservoir N ∧
      x₀ ≤ 4 * N - y₀ ∧ x₀ + (4 * N - y₀) = n ∧
      4 * N - y₀ ≤ 100 * x₀ ∧
      x₁ ≤ 4 * N - y₁ ∧ x₁ + (4 * N - y₁) = n ∧
      4 * N - y₁ ≤ 100 * x₁) :
    FamilyProduces N n c f := by
  intro ω i hi
  have hp := (patternPresent_iff f i ω).1 hi
  have hc₀ := hp (0 : Fin 4)
  have hc₁ := hp (1 : Fin 4)
  have hc₂ := hp (2 : Fin 4)
  have hc₃ := hp (3 : Fin 4)
  rw [hdesired] at hc₀ hc₁ hc₂ hc₃
  simp [reflectedDesired] at hc₀ hc₁ hc₂ hc₃
  specialize hdata i
  dsimp only at hdata
  rcases hdata with
    ⟨hy₀, hx₀, hy₁, hx₁, hxy₀, hsum₀, hrat₀, hxy₁, hsum₁, hrat₁⟩
  have hx₀' : f.endpoint ⟨i, 1⟩ ∈ realizedReservoir N c ω :=
    Or.inl ⟨hx₀, hc₁⟩
  have hy₀' : 4 * N - f.endpoint ⟨i, 0⟩ ∈ realizedReservoir N c ω :=
    Or.inr ⟨_, hy₀, hc₀, rfl⟩
  have hx₁' : f.endpoint ⟨i, 3⟩ ∈ realizedReservoir N c ω :=
    Or.inl ⟨hx₁, hc₃⟩
  have hy₁' : 4 * N - f.endpoint ⟨i, 2⟩ ∈ realizedReservoir N c ω :=
    Or.inr ⟨_, hy₁, hc₂, rfl⟩
  have hp₀ : (f.endpoint ⟨i, 1⟩, 4 * N - f.endpoint ⟨i, 0⟩) ∈
      balancedRepr (realizedReservoir N c ω) n :=
    mem_balancedRepr.2 ⟨hxy₀, hx₀', hy₀', hsum₀, hrat₀⟩
  have hp₁ : (f.endpoint ⟨i, 3⟩, 4 * N - f.endpoint ⟨i, 2⟩) ∈
      balancedRepr (realizedReservoir N c ω) n :=
    mem_balancedRepr.2 ⟨hxy₁, hx₁', hy₁', hsum₁, hrat₁⟩
  have hne : (f.endpoint ⟨i, 1⟩, 4 * N - f.endpoint ⟨i, 0⟩) ≠
      (f.endpoint ⟨i, 3⟩, 4 * N - f.endpoint ⟨i, 2⟩) := by
    intro h
    have := congrArg Prod.fst h
    have he := congrArg Prod.snd (f.endpoint_injective this)
    have he' : (1 : Fin 4) = 3 := by simpa using he
    exact (by decide : (1 : Fin 4) ≠ 3) he'
  have : 1 < (balancedRepr (realizedReservoir N c ω) n).card :=
    Finset.one_lt_card.2 ⟨_, hp₀, _, hp₁, hne⟩
  omega

/-! Integrated from /tmp/ArithRows.lean -/

open MeasureTheory ProbabilityTheory

lemma mem_directReservoir_of_mem_P {N x : ℕ} (h : x ∈ P N) :
    x ∈ directReservoir N := by
  exact Or.inl (Or.inl (Or.inl h))

lemma mem_directReservoir_of_mem_Q {N x : ℕ} (h : x ∈ Q N) :
    x ∈ directReservoir N := by
  exact Or.inl (Or.inl (Or.inr h))

lemma mem_directReservoir_of_mem_R {N x : ℕ} (h : x ∈ R N) :
    x ∈ directReservoir N := by
  exact Or.inl (Or.inr h)

lemma mem_directReservoir_of_mem_S {N x : ℕ} (h : x ∈ S N) :
    x ∈ directReservoir N := by
  exact Or.inr h

/-- The purely linear-arithmetic part of the seven direct rows in Larsen's
four-interval construction.  The remainder `r` lets callers instantiate this
with `u = N / 24000` without any rational arithmetic. -/
theorem exists_direct_family_on_grid_rows
    (N n M u r : ℕ) (c : Fin 2)
    (hN : N = 192 * u + r) (hr : r < 192)
    (hu : 1000 + 16 * M ≤ u)
    (hlo : 3 * N ≤ 2 * n) (hhi : n < 6 * N)
    (hrows : n ≤ 765 * u ∨
      (803 * u < n ∧ n ≤ 903 * u) ∨
      (1027 * u < n ∧ n ≤ 1149 * u)) :
    ∃ f : PatternFamily 4, f.count = M ∧ FamilyProduces N n c f := by
  have hu0 : 0 < u := by omega
  have hM : 16 * M ≤ u := by omega
  rcases hrows with hlow | hrest
  · by_cases h1 : n ≤ 392 * u
    · have hsep : 2 * (8 * u + 8 + 2 * M) ≤ n := by omega
      refine ⟨directFamily M n (8 * u + 8) c hsep, rfl, ?_⟩
      apply directFamily_produces_of_block
      · intro x hx0 hx1
        constructor
        · apply mem_directReservoir_of_mem_P
          simp only [P, Set.mem_setOf_eq]
          omega
        · apply mem_directReservoir_of_mem_R
          simp only [R, Set.mem_setOf_eq]
          omega
      · intro x hx0 hx1
        omega
    · by_cases h2 : n ≤ 512 * u
      · have hsep : 2 * (129 * u + 2 * M) ≤ n := by omega
        refine ⟨directFamily M n (129 * u) c hsep, rfl, ?_⟩
        apply directFamily_produces_of_block
        · intro x hx0 hx1
          constructor
          · apply mem_directReservoir_of_mem_Q
            simp only [Q, Set.mem_setOf_eq]
            omega
          · apply mem_directReservoir_of_mem_R
            simp only [R, Set.mem_setOf_eq]
            omega
        · intro x hx0 hx1
          omega
      · by_cases h3 : n ≤ 526 * u
        · let L := n - 383 * u
          have hLu : L + 383 * u = n := by
            dsimp [L]
            omega
          have hLlo : 129 * u ≤ L := by omega
          have hLhi : L + 2 * M ≤ 144 * u := by omega
          have hsep : 2 * (L + 2 * M) ≤ n := by omega
          refine ⟨directFamily M n L c hsep, rfl, ?_⟩
          apply directFamily_produces_of_block
          · intro x hx0 hx1
            have hxn : x ≤ n := by omega
            constructor
            · apply mem_directReservoir_of_mem_Q
              simp only [Q, Set.mem_setOf_eq]
              omega
            · apply mem_directReservoir_of_mem_R
              simp only [R, Set.mem_setOf_eq]
              omega
          · intro x hx0 hx1
            omega
        · by_cases h4 : n ≤ 641 * u
          · have hsep : 2 * (258 * u + 2 * M) ≤ n := by omega
            refine ⟨directFamily M n (258 * u) c hsep, rfl, ?_⟩
            apply directFamily_produces_of_block
            · intro x hx0 hx1
              constructor
              · apply mem_directReservoir_of_mem_R
                simp only [R, Set.mem_setOf_eq]
                omega
              · apply mem_directReservoir_of_mem_R
                simp only [R, Set.mem_setOf_eq]
                omega
            · intro x hx0 hx1
              omega
          · let L := n - 383 * u
            have hLu : L + 383 * u = n := by
              dsimp [L]
              omega
            have hLlo : 257 * u ≤ L := by omega
            have hLhi : L + 2 * M ≤ 383 * u := by omega
            have hsep : 2 * (L + 2 * M) ≤ n := by omega
            refine ⟨directFamily M n L c hsep, rfl, ?_⟩
            apply directFamily_produces_of_block
            · intro x hx0 hx1
              have hxn : x ≤ n := by omega
              constructor
              · apply mem_directReservoir_of_mem_R
                simp only [R, Set.mem_setOf_eq]
                omega
              · apply mem_directReservoir_of_mem_R
                simp only [R, Set.mem_setOf_eq]
                omega
            · intro x hx0 hx1
              omega
  · rcases hrest with hmid | htop
    · rcases hmid with ⟨hmid0, hmid1⟩
      by_cases h6 : n ≤ 865 * u
      · have hsep : 2 * (290 * u + 2 * M) ≤ n := by omega
        refine ⟨directFamily M n (290 * u) c hsep, rfl, ?_⟩
        apply directFamily_produces_of_block
        · intro x hx0 hx1
          have hxn : x ≤ n := by omega
          have hsum : x + (n - x) = n := Nat.add_sub_of_le hxn
          constructor
          · apply mem_directReservoir_of_mem_R
            simp only [R, Set.mem_setOf_eq]
            omega
          · apply mem_directReservoir_of_mem_S
            simp only [S, Set.mem_setOf_eq]
            omega
        · intro x hx0 hx1
          omega
      · let L := n - 575 * u
        have hLu : L + 575 * u = n := by
          dsimp [L]
          omega
        have hLlo : 289 * u ≤ L := by omega
        have hLhi : L + 2 * M ≤ 329 * u := by omega
        have hsep : 2 * (L + 2 * M) ≤ n := by omega
        refine ⟨directFamily M n L c hsep, rfl, ?_⟩
        apply directFamily_produces_of_block
        · intro x hx0 hx1
          have hxn : x ≤ n := by omega
          constructor
          · apply mem_directReservoir_of_mem_R
            simp only [R, Set.mem_setOf_eq]
            omega
          · apply mem_directReservoir_of_mem_S
            simp only [S, Set.mem_setOf_eq]
            omega
        · intro x hx0 hx1
          omega
    · rcases htop with ⟨htop0, htop1⟩
      by_cases h7 : n ≤ 1088 * u
      · have hsep : 2 * (512 * u + 512 + 2 * M) ≤ n := by omega
        refine ⟨directFamily M n (512 * u + 512) c hsep, rfl, ?_⟩
        apply directFamily_produces_of_block
        · intro x hx0 hx1
          have hxn : x ≤ n := by omega
          have hsum : x + (n - x) = n := Nat.add_sub_of_le hxn
          constructor
          · apply mem_directReservoir_of_mem_S
            simp only [S, Set.mem_setOf_eq]
            omega
          · apply mem_directReservoir_of_mem_S
            simp only [S, Set.mem_setOf_eq]
            omega
        · intro x hx0 hx1
          omega
      · let L := n - 575 * u
        have hLu : L + 575 * u = n := by
          dsimp [L]
          omega
        have hLlo : 513 * u ≤ L := by omega
        have hLhi : L + 2 * M ≤ 575 * u := by omega
        have hsep : 2 * (L + 2 * M) ≤ n := by omega
        refine ⟨directFamily M n L c hsep, rfl, ?_⟩
        apply directFamily_produces_of_block
        · intro x hx0 hx1
          have hxn : x ≤ n := by omega
          constructor
          · apply mem_directReservoir_of_mem_S
            simp only [S, Set.mem_setOf_eq]
            omega
          · apply mem_directReservoir_of_mem_S
            simp only [S, Set.mem_setOf_eq]
            omega
        · intro x hx0 hx1
          omega

/-! Integrated from /tmp/ReflectedRows.lean -/

lemma small_reflected_offset_lt {M d : ℕ} (hd0 : 0 < d) (hd : d < 2 * M)
    (i : Fin M) (a : ℕ)
    (ha : a ≤ 3) : d * (4 * i.1 + a) < 8 * M ^ 2 := by
  have hi : 4 * i.1 + a < 4 * M := by omega
  have h₁ : d * (4 * i.1 + a) < d * (4 * M) :=
    Nat.mul_lt_mul_of_pos_left hi hd0
  have h₂ : d * (4 * M) ≤ (2 * M) * (4 * M) :=
    Nat.mul_le_mul_right (4 * M) (by omega)
  nlinarith

lemma smallReflectedFamily_produces_above
    (N n M d L : ℕ) (c : Fin 2) (hd0 : 0 < d) (hd : d < 2 * M)
    (hsum : 4 * N + d = n)
    (hblock : ∀ z, L ≤ z → z < L + 8 * M ^ 2 →
      z ∈ J N ∧ z + d ∈ directReservoir N ∧
      z + d ≤ 4 * N - z ∧ 4 * N - z ≤ 100 * (z + d)) :
    FamilyProduces N n c (smallReflectedFamily false M d L c hd0) := by
  apply reflectedPatterns_produce N n c _ rfl
  intro i
  have h₀ := small_reflected_offset_lt hd0 hd i 0 (by omega)
  have h₂ := small_reflected_offset_lt hd0 hd i 2 (by omega)
  norm_num at h₀
  have hb₀ := hblock (L + d * (4 * i.1)) (by omega) (by omega)
  have hb₂ := hblock (L + d * (4 * i.1 + 2)) (by omega) (by omega)
  change
    (L + d * (4 * i.1) ∈ J N) ∧
    (L + d * (4 * i.1 + 1) ∈ directReservoir N) ∧
    (L + d * (4 * i.1 + 2) ∈ J N) ∧
    (L + d * (4 * i.1 + 3) ∈ directReservoir N) ∧
    L + d * (4 * i.1 + 1) ≤ 4 * N - (L + d * (4 * i.1)) ∧
    (L + d * (4 * i.1 + 1)) + (4 * N - (L + d * (4 * i.1))) = n ∧
    4 * N - (L + d * (4 * i.1)) ≤ 100 * (L + d * (4 * i.1 + 1)) ∧
    L + d * (4 * i.1 + 3) ≤ 4 * N - (L + d * (4 * i.1 + 2)) ∧
    (L + d * (4 * i.1 + 3)) + (4 * N - (L + d * (4 * i.1 + 2))) = n ∧
    4 * N - (L + d * (4 * i.1 + 2)) ≤ 100 * (L + d * (4 * i.1 + 3))
  rcases hb₀ with ⟨hy₀, hx₀, hord₀, hrat₀⟩
  rcases hb₂ with ⟨hy₁, hx₁, hord₁, hrat₁⟩
  refine ⟨hy₀, ?_, hy₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert hx₀ using 1 <;> ring
  · convert hx₁ using 1 <;> ring
  · convert hord₀ using 1 <;> ring
  · rw [show L + d * (4 * i.1 + 1) = (L + d * (4 * i.1)) + d by ring]
    have hy : L + d * (4 * i.1) ≤ 4 * N := by omega
    omega
  · convert hrat₀ using 1 <;> ring
  · convert hord₁ using 1 <;> ring
  · rw [show L + d * (4 * i.1 + 3) = (L + d * (4 * i.1 + 2)) + d by ring]
    have hy : L + d * (4 * i.1 + 2) ≤ 4 * N := by omega
    omega
  · convert hrat₁ using 1 <;> ring

lemma smallReflectedFamily_produces_below
    (N n M d L : ℕ) (c : Fin 2) (hd0 : 0 < d) (hd : d < 2 * M)
    (hsum : n + d = 4 * N)
    (hblock : ∀ z, L ≤ z → z < L + 8 * M ^ 2 →
      z ∈ directReservoir N ∧ z + d ∈ J N ∧
      z ≤ 4 * N - (z + d) ∧ 4 * N - (z + d) ≤ 100 * z) :
    FamilyProduces N n c (smallReflectedFamily true M d L c hd0) := by
  apply reflectedPatterns_produce N n c _ rfl
  intro i
  have h₀ := small_reflected_offset_lt hd0 hd i 0 (by omega)
  have h₂ := small_reflected_offset_lt hd0 hd i 2 (by omega)
  norm_num at h₀
  have hb₀ := hblock (L + d * (4 * i.1)) (by omega) (by omega)
  have hb₂ := hblock (L + d * (4 * i.1 + 2)) (by omega) (by omega)
  change
    (L + d * (4 * i.1 + 1) ∈ J N) ∧
    (L + d * (4 * i.1) ∈ directReservoir N) ∧
    (L + d * (4 * i.1 + 3) ∈ J N) ∧
    (L + d * (4 * i.1 + 2) ∈ directReservoir N) ∧
    L + d * (4 * i.1) ≤ 4 * N - (L + d * (4 * i.1 + 1)) ∧
    (L + d * (4 * i.1)) + (4 * N - (L + d * (4 * i.1 + 1))) = n ∧
    4 * N - (L + d * (4 * i.1 + 1)) ≤ 100 * (L + d * (4 * i.1)) ∧
    L + d * (4 * i.1 + 2) ≤ 4 * N - (L + d * (4 * i.1 + 3)) ∧
    (L + d * (4 * i.1 + 2)) + (4 * N - (L + d * (4 * i.1 + 3))) = n ∧
    4 * N - (L + d * (4 * i.1 + 3)) ≤ 100 * (L + d * (4 * i.1 + 2))
  rcases hb₀ with ⟨hx₀, hy₀, hord₀, hrat₀⟩
  rcases hb₂ with ⟨hx₁, hy₁, hord₁, hrat₁⟩
  refine ⟨?_, hx₀, ?_, hx₁, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert hy₀ using 1 <;> ring
  · convert hy₁ using 1 <;> ring
  · convert hord₀ using 1 <;> ring
  · rw [show L + d * (4 * i.1 + 1) = (L + d * (4 * i.1)) + d by ring]
    have hy : L + d * (4 * i.1) + d ≤ 4 * N := by omega
    omega
  · convert hrat₀ using 1 <;> ring
  · convert hord₁ using 1 <;> ring
  · rw [show L + d * (4 * i.1 + 3) = (L + d * (4 * i.1 + 2)) + d by ring]
    have hy : L + d * (4 * i.1 + 2) + d ≤ 4 * N := by omega
    omega
  · convert hrat₁ using 1 <;> ring

lemma largeReflectedFamily_produces_above
    (N n M d L : ℕ) (c : Fin 2) (hd : 2 * M ≤ d)
    (hsum : 4 * N + d = n)
    (hblock : ∀ z, L ≤ z → z < L + 2 * M →
      z ∈ J N ∧ z + d ∈ directReservoir N ∧
      z + d ≤ 4 * N - z ∧ 4 * N - z ≤ 100 * (z + d)) :
    FamilyProduces N n c (largeReflectedFamily false M d L c hd) := by
  apply reflectedPatterns_produce N n c _ rfl
  intro i
  have hi : i.1 < M := by simpa [largeReflectedFamily] using i.2
  have hb₀ := hblock (L + 2 * i.1) (by omega) (by omega)
  have hb₁ := hblock (L + 2 * i.1 + 1) (by omega) (by omega)
  change
    (L + 2 * i.1 ∈ J N) ∧ (L + 2 * i.1 + d ∈ directReservoir N) ∧
    (L + 2 * i.1 + 1 ∈ J N) ∧
    (L + 2 * i.1 + d + 1 ∈ directReservoir N) ∧
    L + 2 * i.1 + d ≤ 4 * N - (L + 2 * i.1) ∧
    (L + 2 * i.1 + d) + (4 * N - (L + 2 * i.1)) = n ∧
    4 * N - (L + 2 * i.1) ≤ 100 * (L + 2 * i.1 + d) ∧
    L + 2 * i.1 + d + 1 ≤ 4 * N - (L + 2 * i.1 + 1) ∧
    (L + 2 * i.1 + d + 1) + (4 * N - (L + 2 * i.1 + 1)) = n ∧
    4 * N - (L + 2 * i.1 + 1) ≤ 100 * (L + 2 * i.1 + d + 1)
  rcases hb₀ with ⟨hy₀, hx₀, hord₀, hrat₀⟩
  rcases hb₁ with ⟨hy₁, hx₁, hord₁, hrat₁⟩
  refine ⟨hy₀, hx₀, hy₁, ?_, hord₀, ?_, hrat₀, ?_, ?_, ?_⟩
  · convert hx₁ using 1 <;> ring
  · have hy : L + 2 * i.1 ≤ 4 * N := by omega
    omega
  · convert hord₁ using 1 <;> ring
  · have hy : L + 2 * i.1 + 1 ≤ 4 * N := by omega
    omega
  · convert hrat₁ using 1 <;> ring

lemma largeReflectedFamily_produces_below
    (N n M d L : ℕ) (c : Fin 2) (hd : 2 * M ≤ d)
    (hsum : n + d = 4 * N)
    (hblock : ∀ z, L ≤ z → z < L + 2 * M →
      z ∈ directReservoir N ∧ z + d ∈ J N ∧
      z ≤ 4 * N - (z + d) ∧ 4 * N - (z + d) ≤ 100 * z) :
    FamilyProduces N n c (largeReflectedFamily true M d L c hd) := by
  apply reflectedPatterns_produce N n c _ rfl
  intro i
  have hi : i.1 < M := by simpa [largeReflectedFamily] using i.2
  have hb₀ := hblock (L + 2 * i.1) (by omega) (by omega)
  have hb₁ := hblock (L + 2 * i.1 + 1) (by omega) (by omega)
  change
    (L + 2 * i.1 + d ∈ J N) ∧ (L + 2 * i.1 ∈ directReservoir N) ∧
    (L + 2 * i.1 + d + 1 ∈ J N) ∧
    (L + 2 * i.1 + 1 ∈ directReservoir N) ∧
    L + 2 * i.1 ≤ 4 * N - (L + 2 * i.1 + d) ∧
    (L + 2 * i.1) + (4 * N - (L + 2 * i.1 + d)) = n ∧
    4 * N - (L + 2 * i.1 + d) ≤ 100 * (L + 2 * i.1) ∧
    L + 2 * i.1 + 1 ≤ 4 * N - (L + 2 * i.1 + d + 1) ∧
    (L + 2 * i.1 + 1) + (4 * N - (L + 2 * i.1 + d + 1)) = n ∧
    4 * N - (L + 2 * i.1 + d + 1) ≤ 100 * (L + 2 * i.1 + 1)
  rcases hb₀ with ⟨hx₀, hy₀, hord₀, hrat₀⟩
  rcases hb₁ with ⟨hx₁, hy₁, hord₁, hrat₁⟩
  refine ⟨hy₀, hx₀, ?_, hx₁, hord₀, ?_, hrat₀, ?_, ?_, ?_⟩
  · convert hy₁ using 1 <;> ring
  · have hy : L + 2 * i.1 + d ≤ 4 * N := by omega
    omega
  · convert hord₁ using 1 <;> ring
  · have hy : L + 2 * i.1 + d + 1 ≤ 4 * N := by omega
    omega
  · convert hrat₁ using 1 <;> ring

lemma direct_of_Q {N x : ℕ} (h : x ∈ Q N) : x ∈ directReservoir N :=
  Or.inl (Or.inl (Or.inr h))

lemma direct_of_R {N x : ℕ} (h : x ∈ R N) : x ∈ directReservoir N :=
  Or.inl (Or.inr h)

lemma direct_of_S {N x : ℕ} (h : x ∈ S N) : x ∈ directReservoir N :=
  Or.inr h

theorem exists_reflected_family_on_grid_gaps
    (N n M u r : ℕ) (c : Fin 2)
    (hN : N = 192 * u + r) (hr : r < 192)
    (hu : 1000 + 8 * M ^ 2 ≤ u)
    (hlo : 3 * N ≤ 2 * n) (hhi : n < 6 * N) (hne : n ≠ 4 * N)
    (hgaps : (765 * u < n ∧ n ≤ 803 * u) ∨
      (903 * u < n ∧ n ≤ 1027 * u) ∨ 1149 * u < n) :
    ∃ f : PatternFamily 4, f.count = M ∧ FamilyProduces N n c f := by
  have hu0 : 0 < u := by omega
  have hsmall : 8 * M ^ 2 ≤ u := by omega
  have hlarge : 2 * M ≤ u := by
    have hM : M ≤ M ^ 2 + 1 := by nlinarith
    nlinarith
  rcases hgaps with hQ | hrest
  · by_cases hbelow : n < 4 * N
    · let d := 4 * N - n
      have hd0 : 0 < d := by dsimp [d]; omega
      have hsum : n + d = 4 * N := by dsimp [d]; omega
      by_cases hd : d < 2 * M
      · refine ⟨smallReflectedFamily true M d (135 * u) c hd0, rfl, ?_⟩
        apply smallReflectedFamily_produces_below N n M d (135 * u) c hd0 hd hsum
        intro z hz0 hz1
        have hzQ : z ∈ Q N := by
          simp only [Q, Set.mem_setOf_eq]
          omega
        have hydJ : z + d ∈ J N := by
          simp only [J, Set.mem_setOf_eq]
          omega
        refine ⟨direct_of_Q hzQ, hydJ, ?_, ?_⟩ <;> omega
      · have hd' : 2 * M ≤ d := by omega
        refine ⟨largeReflectedFamily true M d (135 * u) c hd', rfl, ?_⟩
        apply largeReflectedFamily_produces_below N n M d (135 * u) c hd' hsum
        intro z hz0 hz1
        have hzQ : z ∈ Q N := by
          simp only [Q, Set.mem_setOf_eq]
          omega
        have hydJ : z + d ∈ J N := by
          simp only [J, Set.mem_setOf_eq]
          omega
        refine ⟨direct_of_Q hzQ, hydJ, ?_, ?_⟩ <;> omega
    · have habove : 4 * N < n := by omega
      let d := n - 4 * N
      have hd0 : 0 < d := by dsimp [d]; omega
      have hsum : 4 * N + d = n := by dsimp [d]; omega
      let L := 135 * u - d
      have hLd : L + d = 135 * u := by dsimp [L]; omega
      by_cases hd : d < 2 * M
      · refine ⟨smallReflectedFamily false M d L c hd0, rfl, ?_⟩
        apply smallReflectedFamily_produces_above N n M d L c hd0 hd hsum
        intro z hz0 hz1
        have hzJ : z ∈ J N := by
          simp only [J, Set.mem_setOf_eq]
          omega
        have hzdQ : z + d ∈ Q N := by
          simp only [Q, Set.mem_setOf_eq]
          omega
        refine ⟨hzJ, direct_of_Q hzdQ, ?_, ?_⟩ <;> omega
      · have hd' : 2 * M ≤ d := by omega
        refine ⟨largeReflectedFamily false M d L c hd', rfl, ?_⟩
        apply largeReflectedFamily_produces_above N n M d L c hd' hsum
        intro z hz0 hz1
        have hzJ : z ∈ J N := by
          simp only [J, Set.mem_setOf_eq]
          omega
        have hzdQ : z + d ∈ Q N := by
          simp only [Q, Set.mem_setOf_eq]
          omega
        refine ⟨hzJ, direct_of_Q hzdQ, ?_, ?_⟩ <;> omega
  · have habove : 4 * N < n := by omega
    let d := n - 4 * N
    have hd0 : 0 < d := by dsimp [d]; omega
    have hsum : 4 * N + d = n := by dsimp [d]; omega
    rcases hrest with hR | hS
    · by_cases hd : d < 2 * M
      · refine ⟨smallReflectedFamily false M d (123 * u) c hd0, rfl, ?_⟩
        apply smallReflectedFamily_produces_above N n M d (123 * u) c hd0 hd hsum
        intro z hz0 hz1
        have hzJ : z ∈ J N := by simp only [J, Set.mem_setOf_eq]; omega
        have hzdR : z + d ∈ R N := by simp only [R, Set.mem_setOf_eq]; omega
        refine ⟨hzJ, direct_of_R hzdR, ?_, ?_⟩ <;> omega
      · have hd' : 2 * M ≤ d := by omega
        refine ⟨largeReflectedFamily false M d (123 * u) c hd', rfl, ?_⟩
        apply largeReflectedFamily_produces_above N n M d (123 * u) c hd' hsum
        intro z hz0 hz1
        have hzJ : z ∈ J N := by simp only [J, Set.mem_setOf_eq]; omega
        have hzdR : z + d ∈ R N := by simp only [R, Set.mem_setOf_eq]; omega
        refine ⟨hzJ, direct_of_R hzdR, ?_, ?_⟩ <;> omega
    · by_cases hd : d < 2 * M
      · refine ⟨smallReflectedFamily false M d (138 * u) c hd0, rfl, ?_⟩
        apply smallReflectedFamily_produces_above N n M d (138 * u) c hd0 hd hsum
        intro z hz0 hz1
        have hzJ : z ∈ J N := by simp only [J, Set.mem_setOf_eq]; omega
        have hzdS : z + d ∈ S N := by simp only [S, Set.mem_setOf_eq]; omega
        refine ⟨hzJ, direct_of_S hzdS, ?_, ?_⟩ <;> omega
      · have hd' : 2 * M ≤ d := by omega
        refine ⟨largeReflectedFamily false M d (138 * u) c hd', rfl, ?_⟩
        apply largeReflectedFamily_produces_above N n M d (138 * u) c hd' hsum
        intro z hz0 hz1
        have hzJ : z ∈ J N := by simp only [J, Set.mem_setOf_eq]; omega
        have hzdS : z + d ∈ S N := by simp only [S, Set.mem_setOf_eq]; omega
        refine ⟨hzJ, direct_of_S hzdS, ?_, ?_⟩ <;> omega

/-! Integrated from /tmp/ReflectedRowsFinished.lean -/

/-- Checked packaging of the three reflected rows used to fill the gaps left by
the direct interval families.  The exceptional integer `4 * N` is deliberately
excluded: it is handled by the deterministic trap scheduler. -/
theorem exists_reflected_family_on_grid_gaps_finished
    (N n M u r : ℕ) (c : Fin 2)
    (hN : N = 192 * u + r) (hr : r < 192)
    (hu : 1000 + 8 * M ^ 2 ≤ u)
    (hlo : 3 * N ≤ 2 * n) (hhi : n < 6 * N) (hne : n ≠ 4 * N)
    (hgaps : (765 * u < n ∧ n ≤ 803 * u) ∨
      (903 * u < n ∧ n ≤ 1027 * u) ∨ 1149 * u < n) :
    ∃ f : PatternFamily 4, f.count = M ∧ FamilyProduces N n c f := by
  exact exists_reflected_family_on_grid_gaps N n M u r c hN hr hu hlo hhi hne hgaps

/-! Integrated from /tmp/CoverageSchedule.lean -/

theorem exists_family_on_all_grid_targets
    (N n M u r : ℕ) (c : Fin 2)
    (hN : N = 192 * u + r) (hr : r < 192)
    (hu : 1000 + 16 * M + 8 * M ^ 2 ≤ u)
    (hlo : 3 * N ≤ 2 * n) (hhi : n < 6 * N) (hne : n ≠ 4 * N) :
    ∃ f : PatternFamily 4, f.count = M ∧ FamilyProduces N n c f := by
  by_cases hdirect : n ≤ 765 * u ∨
      (803 * u < n ∧ n ≤ 903 * u) ∨
      (1027 * u < n ∧ n ≤ 1149 * u)
  · exact exists_direct_family_on_grid_rows N n M u r c hN hr (by omega)
      hlo hhi hdirect
  · apply exists_reflected_family_on_grid_gaps_finished N n M u r c hN hr (by omega)
      hlo hhi hne
    omega

def coverageQuota (k : ℕ) : ℕ :=
  1000 + 16 * patternTrialCount k + 8 * patternTrialCount k ^ 2

def coverageU (k : ℕ) : ℕ := scale k / 192

def coverageR (k : ℕ) : ℕ := scale k % 192

def CoverageAmple (k : ℕ) : Prop := coverageQuota k ≤ coverageU k

lemma scale_grid_decomposition (k : ℕ) :
    scale k = 192 * coverageU k + coverageR k := by
  have h := Nat.div_add_mod (scale k) 192
  simp only [coverageU, coverageR]
  omega

lemma coverageR_lt (k : ℕ) : coverageR k < 192 := by
  exact Nat.mod_lt _ (by omega)

lemma coverageQuota_step (k : ℕ) (hk : 24 ≤ k) :
    coverageQuota (k + 1) ≤ 4 * coverageQuota k := by
  simp only [coverageQuota, patternTrialCount]
  nlinarith [sq_nonneg (k : ℤ)]

lemma coverageQuota_mul_le_scale {k : ℕ} (hk : 24 ≤ k) :
    192 * coverageQuota k ≤ scale k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [coverageQuota, patternTrialCount, scale]
  | succ k hk ih =>
      rw [scale_succ]
      have hq := coverageQuota_step k hk
      omega

lemma coverageAmple_of_ge {k : ℕ} (hk : 24 ≤ k) : CoverageAmple k := by
  unfold CoverageAmple coverageU
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 192)).2
  simpa [mul_comm] using coverageQuota_mul_le_scale hk

lemma eventually_coverageAmple : ∀ᶠ k : ℕ in atTop, CoverageAmple k := by
  filter_upwards [eventually_ge_atTop 24] with k hk
  exact coverageAmple_of_ge hk

def coverageRequirementCount (k : ℕ) : ℕ := 2 * (6 * scale k + 1)

def coverageTarget (k : ℕ) (i : Fin (coverageRequirementCount k)) : ℕ := i.1 / 2

def coverageColor {k : ℕ} (i : Fin (coverageRequirementCount k)) : Fin 2 :=
  ⟨i.1 % 2, Nat.mod_lt _ (by omega)⟩

def CoverageValid (k : ℕ) (i : Fin (coverageRequirementCount k)) : Prop :=
  CoverageAmple k ∧
  3 * scale k ≤ 2 * coverageTarget k i ∧
  coverageTarget k i < 6 * scale k ∧
  coverageTarget k i ≠ 4 * scale k

lemma exists_coverage_family (k : ℕ) (i : Fin (coverageRequirementCount k))
    (h : CoverageValid k i) :
    ∃ f : PatternFamily 4,
      f.count = patternTrialCount k ∧
      FamilyProduces (scale k) (coverageTarget k i) (coverageColor i) f := by
  apply exists_family_on_all_grid_targets
      (scale k) (coverageTarget k i) (patternTrialCount k)
      (coverageU k) (coverageR k) (coverageColor i)
  · exact scale_grid_decomposition k
  · exact coverageR_lt k
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

def dummyCoverageFamily (M : ℕ) : PatternFamily 4 :=
  directFamily M (4 * M) 0 0 (by omega)

@[simp] lemma dummyCoverageFamily_count (M : ℕ) :
    (dummyCoverageFamily M).count = M := rfl

noncomputable def coverageFamily (k : ℕ)
    (i : Fin (coverageRequirementCount k)) : PatternFamily 4 := by
  classical
  exact if h : CoverageValid k i then Classical.choose (exists_coverage_family k i h)
    else dummyCoverageFamily (patternTrialCount k)

lemma coverageFamily_count (k : ℕ) (i : Fin (coverageRequirementCount k)) :
    (coverageFamily k i).count = patternTrialCount k := by
  classical
  simp only [coverageFamily]
  split
  · exact (Classical.choose_spec (exists_coverage_family k i ‹CoverageValid k i›)).1
  · rfl

lemma coverageFamily_produces (k : ℕ) (i : Fin (coverageRequirementCount k))
    (h : CoverageValid k i) :
    FamilyProduces (scale k) (coverageTarget k i) (coverageColor i)
      (coverageFamily k i) := by
  classical
  simp only [coverageFamily, dif_pos h]
  exact (Classical.choose_spec (exists_coverage_family k i h)).2

lemma coverageRequirementCount_bound (k : ℕ) :
    coverageRequirementCount k ≤ 100 * scale k ^ 2 := by
  have hN := scale_pos k
  simp only [coverageRequirementCount]
  nlinarith [sq_nonneg (scale k : ℤ)]

noncomputable def coverageSchedule : PatternSchedule where
  requirementCount := coverageRequirementCount
  family := coverageFamily
  family_count := coverageFamily_count
  requirement_bound := coverageRequirementCount_bound

def coverageIndex (k : ℕ) (c : Fin 2) (n : ℕ) (hn : n < 6 * scale k) :
    Fin (coverageRequirementCount k) :=
  ⟨2 * n + c.1, by
    have hc : c.1 < 2 := c.2
    simp only [coverageRequirementCount]
    omega⟩

@[simp] lemma coverageTarget_coverageIndex (k : ℕ) (c : Fin 2) (n : ℕ)
    (hn : n < 6 * scale k) :
    coverageTarget k (coverageIndex k c n hn) = n := by
  change (2 * n + c.1) / 2 = n
  omega

@[simp] lemma coverageColor_coverageIndex (k : ℕ) (c : Fin 2) (n : ℕ)
    (hn : n < 6 * scale k) :
    coverageColor (coverageIndex k c n hn) = c := by
  apply Fin.ext
  change (2 * n + c.1) % 2 = c.1
  omega

theorem exists_coloring_eventually_covers :
    ∃ ω : ColorSample, ∀ᶠ k : ℕ in atTop,
      ∀ (c : Fin 2) (n : ℕ),
        3 * scale k ≤ 2 * n → n < 6 * scale k → n ≠ 4 * scale k →
        2 ≤ (balancedRepr (realizedReservoir (scale k) c ω) n).card := by
  obtain ⟨ω, hω⟩ := coverageSchedule.exists_eventually_good
  refine ⟨ω, ?_⟩
  filter_upwards [hω, eventually_coverageAmple] with k hgood hample
  intro c n hlo hhi hne
  let i := coverageIndex k c n hhi
  have hvalid : CoverageValid k i := by
    refine ⟨hample, ?_, ?_, ?_⟩
    · simpa [i] using hlo
    · simpa [i] using hhi
    · simpa [i] using hne
  obtain ⟨j, hj⟩ := hgood i
  have hp := coverageFamily_produces k i hvalid ω j hj
  simpa [i] using hp

lemma scale_add_two (k : ℕ) : scale (k + 2) = 16 * scale k := by
  rw [show k + 2 = (k + 1) + 1 by omega, scale_succ, scale_succ]
  ring

lemma scale_add_three (k : ℕ) : scale (k + 3) = 64 * scale k := by
  rw [show k + 3 = (k + 2) + 1 by omega, scale_succ, scale_add_two]
  ring

lemma realizedReservoir_subset_finalLeft {ω : ColorSample} {k : ℕ} (hk : 3 ≤ k) :
    realizedReservoir (scale k) 0 ω ⊆ FourBuild.finalLeft ω := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 3 := ⟨k - 3, by omega⟩
  apply realizedReservoir_subset
  · intro x hx hcolor
    rcases hx with ((hP | hQ) | hR) | hS
    · apply FourBuild.directLeft_mem_final_of_raw (k := t)
      · right
        simp only [P, Set.mem_ofPred_eq] at hP
        rw [scale_add_three] at hP
        exact ⟨by omega, by omega⟩
      · exact hcolor
    · apply FourBuild.directLeft_mem_final_of_raw (k := t + 2)
      · right
        simp only [Q, Set.mem_ofPred_eq] at hQ
        rw [show t + 3 = (t + 2) + 1 by omega, scale_succ] at hQ
        exact ⟨by omega, by omega⟩
      · exact hcolor
    · apply FourBuild.directLeft_mem_final_of_raw (k := t + 3)
      · left
        exact hR
      · exact hcolor
    · apply FourBuild.directLeft_mem_final_of_raw (k := t + 3)
      · right
        exact hS
      · exact hcolor
  · intro y hy hcolor
    simp only [J, Set.mem_ofPred_eq] at hy
    have hy' : scale (t + 2) < y ∧ y < 3 * scale (t + 2) := by
      rw [show t + 3 = (t + 2) + 1 by omega, scale_succ] at hy
      exact ⟨by omega, by omega⟩
    have h := FourBuild.rawHole_reflection_mem_finalLeft
      (k := t + 2) hy'.1 hy'.2 hcolor
    rw [show t + 2 + 2 = (t + 3) + 1 by omega, scale_succ] at h
    exact h

lemma realizedReservoir_subset_finalRight {ω : ColorSample} {k : ℕ} (hk : 3 ≤ k) :
    realizedReservoir (scale k) 1 ω ⊆ FourBuild.finalRight ω := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 3 := ⟨k - 3, by omega⟩
  apply realizedReservoir_subset
  · intro x hx hcolor
    rcases hx with ((hP | hQ) | hR) | hS
    · apply FourBuild.directRight_mem_final_of_raw (k := t)
      · right
        simp only [P, Set.mem_ofPred_eq] at hP
        rw [scale_add_three] at hP
        exact ⟨by omega, by omega⟩
      · exact hcolor
    · apply FourBuild.directRight_mem_final_of_raw (k := t + 2)
      · right
        simp only [Q, Set.mem_ofPred_eq] at hQ
        rw [show t + 3 = (t + 2) + 1 by omega, scale_succ] at hQ
        exact ⟨by omega, by omega⟩
      · exact hcolor
    · apply FourBuild.directRight_mem_final_of_raw (k := t + 3)
      · left
        exact hR
      · exact hcolor
    · apply FourBuild.directRight_mem_final_of_raw (k := t + 3)
      · right
        exact hS
      · exact hcolor
  · intro y hy hcolor
    simp only [J, Set.mem_ofPred_eq] at hy
    have hy' : scale (t + 2) < y ∧ y < 3 * scale (t + 2) := by
      rw [show t + 3 = (t + 2) + 1 by omega, scale_succ] at hy
      exact ⟨by omega, by omega⟩
    have h := FourBuild.rawHole_reflection_mem_finalRight
      (k := t + 2) hy'.1 hy'.2 hcolor
    rw [show t + 2 + 2 = (t + 3) + 1 by omega, scale_succ] at h
    exact h

lemma exists_larsen_scale (K n : ℕ) (hn : 6 * scale K ≤ n) :
    ∃ j, K ≤ j ∧ 3 * scale j ≤ 2 * n ∧ n < 6 * scale j := by
  have hex : ∃ j, n < 6 * scale j := by
    refine ⟨n + 1, ?_⟩
    have hs : n + 1 ≤ scale (n + 1) :=
      RecursiveCertificate.index_le_scale (n + 1)
    have hp := scale_pos (n + 1)
    omega
  let j := Nat.find hex
  have hj : n < 6 * scale j := Nat.find_spec hex
  have hKj : K < j := by
    by_contra h
    have hjK : j ≤ K := Nat.le_of_not_gt h
    have hs : scale j ≤ scale K := scale_strictMono.monotone hjK
    omega
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hiFind : i < Nat.find hex := by
    dsimp [j] at hi
    omega
  rw [hi] at hj hKj
  have hprev : 6 * scale i ≤ n := by
    by_contra h
    have hlt : n < 6 * scale i := Nat.lt_of_not_ge h
    exact (Nat.find_min hex hiFind) hlt
  refine ⟨i + 1, by omega, ?_, hj⟩
  rw [scale_succ]
  omega

lemma ordinary_many_finalLeft (ω : ColorSample)
    (hcoverage : ∀ᶠ k : ℕ in atTop, ∀ (c : Fin 2) (n : ℕ),
      3 * scale k ≤ 2 * n → n < 6 * scale k → n ≠ 4 * scale k →
      2 ≤ (balancedRepr (realizedReservoir (scale k) c ω) n).card) :
    ∀ᶠ n : ℕ in atTop, n ∉ exceptional →
      2 ≤ (balancedRepr (FourBuild.finalLeft ω) n).card := by
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 hcoverage
  let K := max K₀ 3
  filter_upwards [eventually_ge_atTop (6 * scale K)] with n hn hnexc
  obtain ⟨j, hKj, hjlo, hjhi⟩ := exists_larsen_scale K n hn
  have hj3 : 3 ≤ j := (le_max_right K₀ 3).trans hKj
  have hne : n ≠ 4 * scale j := by
    intro heq
    apply hnexc
    refine ⟨j, ?_⟩
    rw [scale_succ]
    exact heq
  have hcard := hK₀ j ((le_max_left K₀ 3).trans hKj) (0 : Fin 2) n hjlo hjhi hne
  exact hcard.trans (Finset.card_le_card
    (balancedRepr_mono (realizedReservoir_subset_finalLeft hj3) n))

lemma ordinary_many_finalRight (ω : ColorSample)
    (hcoverage : ∀ᶠ k : ℕ in atTop, ∀ (c : Fin 2) (n : ℕ),
      3 * scale k ≤ 2 * n → n < 6 * scale k → n ≠ 4 * scale k →
      2 ≤ (balancedRepr (realizedReservoir (scale k) c ω) n).card) :
    ∀ᶠ n : ℕ in atTop, n ∉ exceptional →
      2 ≤ (balancedRepr (FourBuild.finalRight ω) n).card := by
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 hcoverage
  let K := max K₀ 3
  filter_upwards [eventually_ge_atTop (6 * scale K)] with n hn hnexc
  obtain ⟨j, hKj, hjlo, hjhi⟩ := exists_larsen_scale K n hn
  have hj3 : 3 ≤ j := (le_max_right K₀ 3).trans hKj
  have hne : n ≠ 4 * scale j := by
    intro heq
    apply hnexc
    refine ⟨j, ?_⟩
    rw [scale_succ]
    exact heq
  have hcard := hK₀ j ((le_max_left K₀ 3).trans hKj) (1 : Fin 2) n hjlo hjhi hne
  exact hcard.trans (Finset.card_le_card
    (balancedRepr_mono (realizedReservoir_subset_finalRight hj3) n))

lemma eventually_shortBlocks_of_eventually_targets (X : Set ℕ)
    (h : ∀ᶠ n : ℕ in atTop, n ∉ exceptional →
      2 ≤ (balancedRepr X n).card) :
    ∀ᶠ M : ℕ in atTop, ∀ n, InShortBlock M n → n ∉ exceptional →
      2 ≤ (balancedRepr X n).card := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  filter_upwards [eventually_ge_atTop (N + 1)] with M hM n hn hnexc
  apply hN n (by rcases hn with ⟨hn, _⟩; omega) hnexc

lemma card_le_sq_of_all_represented (I B : Finset ℕ)
    (hrep : ∀ n ∈ I, ∃ b ∈ B, ∃ c ∈ B, b + c = n) :
    I.card ≤ B.card ^ 2 := by
  classical
  have hrep' : ∀ n : I, ∃ b ∈ B, ∃ c ∈ B, b + c = (n : ℕ) := by
    intro n
    exact hrep n n.property
  choose b hb c hc hsum using hrep'
  let f : I → B × B := fun n => (⟨b n, hb n⟩, ⟨c n, hc n⟩)
  have hf_sum (n : I) : (f n).1.1 + (f n).2.1 = (n : ℕ) := hsum n
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    rw [← hf_sum x, ← hf_sum y, hxy]
  have hcard := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_coe, pow_two] using hcard

lemma card_ge_of_Ico_represented (B : Finset ℕ) {lo hi k : ℕ}
    (hlen : lo + k ^ 2 ≤ hi)
    (hrep : ∀ n ∈ Finset.Ico lo hi, ∃ b ∈ B, ∃ c ∈ B, b + c = n) :
    k ≤ B.card := by
  have hI := card_le_sq_of_all_represented (Finset.Ico lo hi) B hrep
  rw [Nat.card_Ico] at hI
  have hkSq : k ^ 2 ≤ hi - lo := by omega
  have hsquares : k ^ 2 ≤ B.card ^ 2 := hkSq.trans hI
  nlinarith

lemma card_filter_ge_of_add_le_card (B : Finset ℕ) (stage k : ℕ)
    (hcard : stage + k ≤ B.card) :
    k ≤ (B.filter fun b => stage ≤ b).card := by
  classical
  let H := B.filter fun b => stage ≤ b
  have hsub : B ⊆ H ∪ Finset.range stage := by
    intro b hb
    by_cases h : stage ≤ b
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hb, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_range.2 (Nat.lt_of_not_ge h))
  have hupper : B.card ≤ H.card + stage := by
    calc
      B.card ≤ (H ∪ Finset.range stage).card := Finset.card_le_card hsub
      _ ≤ H.card + (Finset.range stage).card := Finset.card_union_le _ _
      _ = H.card + stage := by simp
  dsimp [H] at hupper ⊢
  omega

lemma eligible_card_ge_of_Ico_represented (B : Finset ℕ)
    {lo hi stage k : ℕ}
    (hlen : lo + (stage + k) ^ 2 ≤ hi)
    (hrep : ∀ n ∈ Finset.Ico lo hi, ∃ b ∈ B, ∃ c ∈ B, b + c = n) :
    k ≤ (B.filter fun b => stage ≤ b).card := by
  exact card_filter_ge_of_add_le_card B stage k
    (card_ge_of_Ico_represented B hlen hrep)

lemma exists_buildLeft_repr_of_coverage {ω : ColorSample} {k n : ℕ}
    (hk : 3 ≤ k) (hnlo : 2 * scale k ≤ n) (hnhi : n < 3 * scale k)
    (hcard : 2 ≤ (balancedRepr (realizedReservoir (scale k) 0 ω) n).card) :
    ∃ b ∈ (FourBuild.build ω (k + 1)).left,
      ∃ c ∈ (FourBuild.build ω (k + 1)).left, b + c = n := by
  obtain ⟨p, hp⟩ := Finset.card_pos.1 (by omega : 0 <
    (balancedRepr (realizedReservoir (scale k) 0 ω) n).card)
  have hp' := mem_balancedRepr.1 hp
  have hsub := realizedReservoir_subset_finalLeft (ω := ω) hk
  have hbfinal := hsub hp'.2.1
  have hcfinal := hsub hp'.2.2.1
  have hbscale : p.1 ≤ scale (k + 1) := by rw [scale_succ]; omega
  have hcscale : p.2 ≤ scale (k + 1) := by rw [scale_succ]; omega
  exact ⟨p.1, FourBuild.finalLeft_mem_build_of_le hbfinal hbscale,
    p.2, FourBuild.finalLeft_mem_build_of_le hcfinal hcscale, hp'.2.2.2.1⟩

lemma exists_buildRight_repr_of_coverage {ω : ColorSample} {k n : ℕ}
    (hk : 3 ≤ k) (hnlo : 2 * scale k ≤ n) (hnhi : n < 3 * scale k)
    (hcard : 2 ≤ (balancedRepr (realizedReservoir (scale k) 1 ω) n).card) :
    ∃ b ∈ (FourBuild.build ω (k + 1)).right,
      ∃ c ∈ (FourBuild.build ω (k + 1)).right, b + c = n := by
  obtain ⟨p, hp⟩ := Finset.card_pos.1 (by omega : 0 <
    (balancedRepr (realizedReservoir (scale k) 1 ω) n).card)
  have hp' := mem_balancedRepr.1 hp
  have hsub := realizedReservoir_subset_finalRight (ω := ω) hk
  have hbfinal := hsub hp'.2.1
  have hcfinal := hsub hp'.2.2.1
  have hbscale : p.1 ≤ scale (k + 1) := by rw [scale_succ]; omega
  have hcscale : p.2 ≤ scale (k + 1) := by rw [scale_succ]; omega
  exact ⟨p.1, FourBuild.finalRight_mem_build_of_le hbfinal hbscale,
    p.2, FourBuild.finalRight_mem_build_of_le hcfinal hcscale, hp'.2.2.2.1⟩

lemma eventual_active_of_coverage (ω : ColorSample)
    (hcoverage : ∀ᶠ k : ℕ in atTop, ∀ (c : Fin 2) (n : ℕ),
      3 * scale k ≤ 2 * n → n < 6 * scale k → n ≠ 4 * scale k →
      2 ≤ (balancedRepr (realizedReservoir (scale k) c ω) n).card) :
    ∀ᶠ s : ℕ in atTop, FourBuild.active (FourBuild.build ω s) s := by
  have hstages : ∀ᶠ k : ℕ in atTop,
      FourBuild.active (FourBuild.build ω (k + 1)) (k + 1) := by
    filter_upwards [hcoverage, eventually_coverageAmple, eventually_ge_atTop 3]
      with k hcov hample hk
    have hqscale : coverageQuota k ≤ scale k :=
      hample.trans (Nat.div_le_self _ _)
    have hsquare : (2 * (k + 1)) ^ 2 ≤ scale k := by
      simp only [coverageQuota, patternTrialCount] at hqscale
      nlinarith
    have hlen : 2 * scale k + ((k + 1) + (k + 1)) ^ 2 ≤ 3 * scale k := by
      nlinarith
    have hrepL : ∀ n ∈ Finset.Ico (2 * scale k) (3 * scale k),
        ∃ b ∈ (FourBuild.build ω (k + 1)).left,
          ∃ c ∈ (FourBuild.build ω (k + 1)).left, b + c = n := by
      intro n hn
      have hn' := Finset.mem_Ico.1 hn
      apply exists_buildLeft_repr_of_coverage hk hn'.1 hn'.2
      apply hcov (0 : Fin 2) n <;> omega
    have hrepR : ∀ n ∈ Finset.Ico (2 * scale k) (3 * scale k),
        ∃ b ∈ (FourBuild.build ω (k + 1)).right,
          ∃ c ∈ (FourBuild.build ω (k + 1)).right, b + c = n := by
      intro n hn
      have hn' := Finset.mem_Ico.1 hn
      apply exists_buildRight_repr_of_coverage hk hn'.1 hn'.2
      apply hcov (1 : Fin 2) n <;> omega
    have hleft := eligible_card_ge_of_Ico_represented
      (FourBuild.build ω (k + 1)).left hlen hrepL
    have hright := eligible_card_ge_of_Ico_represented
      (FourBuild.build ω (k + 1)).right hlen hrepR
    have hprod : (k + 1) ^ 2 ≤
        (((FourBuild.build ω (k + 1)).left.filter fun b => k + 1 ≤ b).product
          ((FourBuild.build ω (k + 1)).right.filter fun c => k + 1 ≤ c)).card := by
      simpa [pow_two] using Nat.mul_le_mul hleft hright
    have hsub :
        ((FourBuild.build ω (k + 1)).left.filter fun b => k + 1 ≤ b).product
          ((FourBuild.build ω (k + 1)).right.filter fun c => k + 1 ≤ c) ⊆
            FourBuild.eligible (FourBuild.build ω (k + 1)) (k + 1) := by
      intro p hp
      have hp' := Finset.mem_product.1 hp
      have hb := Finset.mem_filter.1 hp'.1
      have hc := Finset.mem_filter.1 hp'.2
      rw [FourBuild.eligible, Finset.mem_filter]
      refine ⟨Finset.mem_product.2 ⟨hb.1, hc.1⟩, hb.2, ?_, hc.2, ?_⟩
      · exact Nat.le_of_lt ((FourBuild.good_build ω (k + 1)).left_bound p.1 hb.1).2
      · exact Nat.le_of_lt ((FourBuild.good_build ω (k + 1)).right_bound p.2 hc.1).2
    refine ⟨by omega, ?_⟩
    have hcard := Finset.card_le_card hsub
    exact (show k + 1 ≤ (k + 1) ^ 2 by nlinarith).trans (hprod.trans hcard)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hstages
  apply eventually_atTop.2
  refine ⟨K + 1, ?_⟩
  intro s hs
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  exact hK k (by omega)

theorem exists_recursiveCertificate : Nonempty RecursiveCertificate := by
  obtain ⟨ω, hcoverage⟩ := exists_coloring_eventually_covers
  have hactive := eventual_active_of_coverage ω hcoverage
  have hmanyL := eventually_shortBlocks_of_eventually_targets
    (FourBuild.finalLeft ω) (ordinary_many_finalLeft ω hcoverage)
  have hmanyR := eventually_shortBlocks_of_eventually_targets
    (FourBuild.finalRight ω) (ordinary_many_finalRight ω hcoverage)
  exact ⟨FourBuild.recursiveCertificate ω hactive hmanyL hmanyR⟩

theorem erdos_869 :
    ¬ ∀ (A₁ A₂ : Set ℕ), Disjoint A₁ A₂ →
      IsBasis2 A₁ → IsBasis2 A₂ →
      ∃ D ⊆ A₁ ∪ A₂, IsBasis2 D ∧
        ∀ d ∈ D, ¬ IsBasis2 (D \ {d}) := by
  obtain ⟨c⟩ := exists_recursiveCertificate
  exact RecursiveCertificate.erdos_869_of_recursiveCertificate c


end Erdos869

#print axioms Erdos869.erdos_869
