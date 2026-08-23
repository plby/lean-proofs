/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 190.
https://www.erdosproblems.com/forum/thread/190

Informal authors:
- J. H. Bae

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos190.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Combinatorics.HalesJewett
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Order
import PrimeNumberTheoremAnd.Consequences

/-!
# Erdős Problem 190

For a positive integer N, let [N] be represented by Fin N.  This file
defines the least N for which every coloring of [N] by an arbitrary finite
type has a monochromatic or rainbow k-term arithmetic progression, and
proves that its real k-th root divided by k tends to infinity.

The mathematical proof and Leanization map are in tex/190.tex.
-/

namespace Erdos190

open scoped BigOperators Finset Topology
open Filter Function Finset Fintype

/-- A positive-step k-term arithmetic progression contained in Fin N. -/
structure AP (N k : ℕ) where
  start : ℕ
  step : ℕ
  step_pos : 0 < step
  isLt : ∀ i : Fin k, start + i.1 * step < N

namespace AP

/-- The term of an arithmetic progression at an index. -/
def term (P : AP N k) (i : Fin k) : Fin N :=
  ⟨P.start + i.1 * P.step, P.isLt i⟩

@[simp] lemma term_val (P : AP N k) (i : Fin k) :
    (P.term i).1 = P.start + i.1 * P.step := rfl

lemma term_injective (P : AP N k) : Injective P.term := by
  intro i j hij
  apply Fin.ext
  have h :
      P.start + i.1 * P.step = P.start + j.1 * P.step :=
    congrArg Fin.val hij
  have hm : i.1 * P.step = j.1 * P.step := Nat.add_left_cancel h
  exact Nat.eq_of_mul_eq_mul_right P.step_pos hm

end AP

/-- A coloring is constant on the progression P. -/
def Monochromatic (c : Fin N → C) (P : AP N k) : Prop :=
  ∀ i j : Fin k, c (P.term i) = c (P.term j)

/-- A coloring takes pairwise distinct values on the progression P. -/
def Rainbow (c : Fin N → C) (P : AP N k) : Prop :=
  Injective (c ∘ P.term)

/-- The exact universal canonical-Ramsey property from Problem 190. -/
def Good (k N : ℕ) : Prop :=
  ∀ (C : Type) (_ : Fintype C) (c : Fin N → C),
    ∃ P : AP N k, Monochromatic c P ∨ Rainbow c P

/-- There is an r-coloring of Fin N with no monochromatic k-AP. -/
def Avoidable (r k N : ℕ) : Prop :=
  ∃ c : Fin N → Fin r, ∀ P : AP N k, ¬Monochromatic c P

/-- Equality patterns of (k+1)-tuples.  We use all Boolean matrices;
being an equivalence relation is irrelevant to the finite-color argument. -/
abbrev Pattern (k : ℕ) := Fin (k + 1) → Fin (k + 1) → Bool

/-- Wildcard coordinates of a combinatorial line. -/
def wildcards {α ι : Type*} [Fintype ι] (l : Combinatorics.Line α ι) :
    Finset ι :=
  {i | l.idxFun i = none}

lemma wildcards_nonempty {α ι : Type*} [Fintype ι]
    (l : Combinatorics.Line α ι) : (wildcards l).Nonempty := by
  obtain ⟨i, hi⟩ := l.proper
  exact ⟨i, by simp [wildcards, hi]⟩

/-- The fixed-coordinate contribution to the sum along a line. -/
noncomputable def fixedSum {M ι : Type*} [AddCommMonoid M] [Fintype ι]
    (l : Combinatorics.Line M ι) : M := by
  classical
  exact ∑ i ∈ (wildcards l)ᶜ, (l.idxFun i).getD 0

/-- Summing the words on a combinatorial line gives a homothetic copy:
the dilation is the nonzero number of wildcard coordinates. -/
lemma line_sum_eq {M ι : Type*} [AddCommMonoid M] [Fintype ι]
    (l : Combinatorics.Line M ι) (x : M) :
    ∑ i, l x i = (wildcards l).card • x + fixedSum l := by
  classical
  rw [← Finset.sum_add_sum_compl (wildcards l)]
  congr 1
  · rw [← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro i hi
    rw [wildcards, Finset.mem_filter] at hi
    simpa [Combinatorics.Line.coe_apply, hi.2]
  · unfold fixedSum
    apply Finset.sum_congr rfl
    intro i hi
    rw [wildcards, Finset.compl_filter, Finset.mem_filter] at hi
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hi.2
    simp [Combinatorics.Line.coe_apply, ← hy]

/-- Fixed-coordinate contribution after mapping the alphabet into an
additive commutative monoid. -/
noncomputable def fixedMapSum {α M ι : Type*} [AddCommMonoid M] [Fintype ι]
    (f : α → M) (l : Combinatorics.Line α ι) : M := by
  classical
  exact ∑ i ∈ (wildcards l)ᶜ, ((l.idxFun i).map f).getD 0

/-- Mapped line-sum formula.  This lets us sum the natural values of a
finite alphabet without using its modular additive structure. -/
lemma line_map_sum_eq {α M ι : Type*} [AddCommMonoid M] [Fintype ι]
    (f : α → M) (l : Combinatorics.Line α ι) (x : α) :
    ∑ i, f (l x i) = (wildcards l).card • f x + fixedMapSum f l := by
  classical
  rw [← Finset.sum_add_sum_compl (wildcards l)]
  congr 1
  · rw [← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro i hi
    rw [wildcards, Finset.mem_filter] at hi
    simp [Combinatorics.Line.coe_apply, hi.2]
  · unfold fixedMapSum
    apply Finset.sum_congr rfl
    intro i hi
    rw [wildcards, Finset.compl_filter, Finset.mem_filter] at hi
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hi.2
    simp [Combinatorics.Line.coe_apply, ← hy]

/-- Sum the first coordinates of a word over a product alphabet. -/
def sum₁ {ι : Type*} [Fintype ι] {A B : ℕ}
    (w : ι → Fin A × Fin B) : ℕ :=
  ∑ i, (w i).1.1

/-- Sum the second coordinates of a word over a product alphabet. -/
def sum₂ {ι : Type*} [Fintype ι] {A B : ℕ}
    (w : ι → Fin A × Fin B) : ℕ :=
  ∑ i, (w i).2.1

lemma sum₁_le {ι : Type*} [Fintype ι] {A B : ℕ}
    (w : ι → Fin A × Fin B) :
    sum₁ w ≤ Fintype.card ι * (A - 1) := by
  unfold sum₁
  calc
    ∑ i, (w i).1.1 ≤ ∑ _i : ι, (A - 1) := by
      apply Finset.sum_le_sum
      intro i _
      omega
    _ = Fintype.card ι * (A - 1) := by simp

lemma sum₂_le {ι : Type*} [Fintype ι] {A B : ℕ}
    (w : ι → Fin A × Fin B) :
    sum₂ w ≤ Fintype.card ι * (B - 1) := by
  unfold sum₂
  calc
    ∑ i, (w i).2.1 ≤ ∑ _i : ι, (B - 1) := by
      apply Finset.sum_le_sum
      intro i _
      omega
    _ = Fintype.card ι * (B - 1) := by simp

/-- The finite canonical van der Waerden theorem, obtained directly from
the finite Hales--Jewett theorem.  The bound is uniform in the finite color
type because the Hales--Jewett coloring records only equality patterns. -/
theorem good_exists_ge_two (k : ℕ) (hk : 2 ≤ k) :
    ∃ N, 0 < N ∧ Good k N := by
  classical
  let M := k * (k - 1)
  let α := Fin (2 * M + 1) × Fin (2 * M + 1)
  obtain ⟨ι, instι, hι⟩ :=
    Combinatorics.Line.exists_mono_in_high_dimension α (Pattern k)
  let B := Fintype.card ι * (2 * M) + 1
  let N := (k + 1) * B
  have hB : 0 < B := by simp [B]
  have hN : 0 < N := Nat.mul_pos (by omega) hB
  refine ⟨N, hN, ?_⟩
  intro C instC c
  let pt (w : ι → α) (i : Fin (k + 1)) : Fin N :=
    ⟨sum₁ w + i.1 * sum₂ w, by
      have h₁ := sum₁_le w
      have h₂ := sum₂_le w
      have h₁' : sum₁ w ≤ B - 1 := by
        simpa [α, B] using h₁
      have h₂' : sum₂ w ≤ B - 1 := by
        simpa [α, B] using h₂
      have hi : i.1 ≤ k := by omega
      calc
        sum₁ w + i.1 * sum₂ w
            ≤ (B - 1) + k * (B - 1) :=
          Nat.add_le_add h₁' (Nat.mul_le_mul hi h₂')
        _ = (k + 1) * (B - 1) := by ring
        _ < (k + 1) * B :=
          Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hB (by omega)) (by omega)
        _ = N := rfl⟩
  let pat : (ι → α) → Pattern k :=
    fun w i j => decide (c (pt w i) = c (pt w j))
  obtain ⟨l, q, hl⟩ := hι pat
  let D := (wildcards l).card
  let A := fixedMapSum (fun x : α => x.1.1) l
  let E := fixedMapSum (fun x : α => x.2.1) l
  have hD : 0 < D := by
    simpa [D] using (wildcards_nonempty l).card_pos
  have hsum₁ (x : α) : sum₁ (l x) = D * x.1.1 + A := by
    simpa [sum₁, D, A, nsmul_eq_mul] using
      (line_map_sum_eq (fun x : α => x.1.1) l x)
  have hsum₂ (x : α) : sum₂ (l x) = D * x.2.1 + E := by
    simpa [sum₂, D, E, nsmul_eq_mul] using
      (line_map_sum_eq (fun x : α => x.2.1) l x)
  have hMpos : 0 < M := by
    exact Nat.mul_pos (by omega) (Nat.sub_pos_of_lt (by omega))
  let z₀ : α :=
    (⟨M, by omega⟩, ⟨M, by omega⟩)
  let a := sum₁ (l z₀)
  let d := sum₂ (l z₀)
  have hd : 0 < d := by
    dsimp [d]
    rw [hsum₂]
    dsimp [z₀]
    nlinarith
  let P₀ : AP N k :=
    { start := a + d
      step := d
      step_pos := hd
      isLt := fun i => by
        have hp := (pt (l z₀) (Fin.succ i)).isLt
        change sum₁ (l z₀) + (i.1 + 1) * sum₂ (l z₀) < N at hp
        dsimp [a, d]
        calc
          sum₁ (l z₀) + sum₂ (l z₀) + i.1 * sum₂ (l z₀) =
              sum₁ (l z₀) + (i.1 + 1) * sum₂ (l z₀) := by ring
          _ < N := hp }
  by_cases hr : Rainbow c P₀
  · exact ⟨P₀, Or.inr hr⟩
  · obtain ⟨i, j, hijc, hij⟩ :=
      Function.not_injective_iff.mp hr
    have collision {i j : Fin k} (hijlt : i < j)
        (hijc : (c ∘ P₀.term) i = (c ∘ P₀.term) j) :
        ∃ P : AP N k, Monochromatic c P := by
      let x := i.1 + 1
      let y := j.1 + 1
      have hxk : x ≤ k := by dsimp [x]; omega
      have hyk : y ≤ k := by dsimp [y]; omega
      have hxy : x < y := by dsimp [x, y]; omega
      have hkm : k - 1 ≤ M := by
        dsimp [M]
        nlinarith
      let z (t : Fin k) : α :=
        (⟨M - x * t.1, by
            have ht : t.1 ≤ k - 1 := by omega
            have hxt : x * t.1 ≤ M := by
              dsimp [M]
              exact Nat.mul_le_mul hxk ht
            omega⟩,
         ⟨M + t.1, by
            have ht : t.1 ≤ k - 1 := by omega
            omega⟩)
      have hxt (t : Fin k) : x * t.1 ≤ M := by
        have ht : t.1 ≤ k - 1 := by omega
        dsimp [M]
        exact Nat.mul_le_mul hxk ht
      have hpt₀ (u : Fin k) :
          pt (l z₀) (Fin.succ u) = P₀.term u := by
        apply Fin.ext
        simp only [pt, AP.term_val, P₀, Fin.succ_mk]
        dsimp [a, d]
        ring
      have hcenter :
          pat (l z₀) (Fin.succ i) (Fin.succ j) = true := by
        simp only [pat, decide_eq_true_eq]
        change c (P₀.term i) = c (P₀.term j) at hijc
        simpa only [hpt₀] using hijc
      have hshift (t : Fin k) :
          c (pt (l (z t)) (Fin.succ i)) =
            c (pt (l (z t)) (Fin.succ j)) := by
        have hm :
            pat (l (z t)) (Fin.succ i) (Fin.succ j) =
              pat (l z₀) (Fin.succ i) (Fin.succ j) := by
          rw [hl (z t), hl z₀]
        have : pat (l (z t)) (Fin.succ i) (Fin.succ j) = true :=
          hm.trans hcenter
        simpa only [pat, decide_eq_true_eq] using this
      have hleft (t : Fin k) :
          pt (l (z t)) (Fin.succ i) = pt (l z₀) (Fin.succ i) := by
        apply Fin.ext
        simp only [pt, Fin.succ_mk]
        rw [hsum₁, hsum₂, hsum₁, hsum₂]
        dsimp [z, z₀, x]
        have hcancel : M - (i.1 + 1) * t.1 + (i.1 + 1) * t.1 = M :=
          Nat.sub_add_cancel (hxt t)
        calc
          D * (M - (i.1 + 1) * t.1) + A +
                (i.1 + 1) * (D * (M + t.1) + E) =
              D * (M - (i.1 + 1) * t.1) + D * ((i.1 + 1) * t.1) + A +
                (i.1 + 1) * (D * M + E) := by ring
          _ = D * M + A + (i.1 + 1) * (D * M + E) := by
            rw [← Nat.mul_add, hcancel]
      have hright_val (t : Fin k) :
          a + y * d + t.1 * ((y - x) * D) =
            sum₁ (l (z t)) + y * sum₂ (l (z t)) := by
        dsimp [a, d]
        rw [hsum₁ z₀, hsum₂ z₀, hsum₁ (z t), hsum₂ (z t)]
        dsimp [z, z₀]
        apply Nat.cast_injective (R := ℤ)
        push_cast [Nat.cast_sub (hxt t), Nat.cast_sub hxy.le]
        ring
      let P : AP N k :=
        { start := a + y * d
          step := (y - x) * D
          step_pos := Nat.mul_pos (Nat.sub_pos_of_lt hxy) hD
          isLt := fun t => by
            have hp := (pt (l (z t)) (Fin.succ j)).isLt
            change sum₁ (l (z t)) + y * sum₂ (l (z t)) < N at hp
            rw [hright_val t]
            exact hp }
      refine ⟨P, ?_⟩
      intro t u
      have ht := hshift t
      have hu := hshift u
      rw [hleft t] at ht
      rw [hleft u] at hu
      have hright (v : Fin k) :
          P.term v = pt (l (z v)) (Fin.succ j) := by
        apply Fin.ext
        simp only [AP.term_val, P, pt, Fin.succ_mk]
        exact hright_val v
      rw [hright t, hright u]
      exact ht.symm.trans hu
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · obtain ⟨P, hP⟩ := collision hijlt hijc
      exact ⟨P, Or.inl hP⟩
    · obtain ⟨P, hP⟩ := collision hjilt hijc.symm
      exact ⟨P, Or.inl hP⟩

lemma good_zero : Good 0 1 := by
  intro C instC c
  let P : AP 1 0 :=
    { start := 0
      step := 1
      step_pos := by omega
      isLt := fun i => Fin.elim0 i }
  exact ⟨P, Or.inl fun i => Fin.elim0 i⟩

lemma good_one : Good 1 1 := by
  intro C instC c
  let P : AP 1 1 :=
    { start := 0
      step := 1
      step_pos := by omega
      isLt := fun i => by fin_cases i; simp }
  exact ⟨P, Or.inl fun i j => by fin_cases i; fin_cases j; rfl⟩

/-- Existence of the exact finite canonical Ramsey number for every k. -/
theorem good_nonempty (k : ℕ) : ∃ N, 0 < N ∧ Good k N := by
  obtain h | h := lt_or_ge k 2
  · interval_cases k
    · exact ⟨1, by omega, good_zero⟩
    · exact ⟨1, by omega, good_one⟩
  · exact good_exists_ge_two k h

/-- The canonical van der Waerden number H(k) from Problem 190. -/
noncomputable def H (k : ℕ) : ℕ :=
  sInf {N : ℕ | 0 < N ∧ Good k N}

lemma H_spec (k : ℕ) : 0 < H k ∧ Good k (H k) := by
  change sInf {N : ℕ | 0 < N ∧ Good k N} ∈
    {N : ℕ | 0 < N ∧ Good k N}
  exact csInf_mem (good_nonempty k)

lemma H_pos (k : ℕ) : 0 < H k := (H_spec k).1

lemma good_H (k : ℕ) : Good k (H k) := (H_spec k).2

lemma H_minimal {k N : ℕ} (hN : 0 < N) (hgood : Good k N) :
    H k ≤ N := by
  exact csInf_le' ⟨hN, hgood⟩

lemma Good.mono {k N M : ℕ} (h : Good k N) (hNM : N ≤ M) : Good k M := by
  intro C instC c
  obtain ⟨P, hP⟩ := h C instC (fun x => c (Fin.castLE hNM x))
  let Q : AP M k :=
    { start := P.start
      step := P.step
      step_pos := P.step_pos
      isLt := fun i => (P.isLt i).trans_le hNM }
  have hterm (i : Fin k) :
      Q.term i = Fin.castLE hNM (P.term i) := by
    rfl
  refine ⟨Q, ?_⟩
  rcases hP with hmono | hrain
  · left
    intro i j
    simpa only [hterm] using hmono i j
  · right
    intro i j hij
    apply hrain
    simpa only [Function.comp_apply, hterm] using hij

lemma not_good_of_avoidable {r k N : ℕ} (h : Avoidable r k N) (hrk : r < k) :
    ¬Good k N := by
  rintro hgood
  rcases h with ⟨c, hc⟩
  obtain ⟨P, hmono | hrain⟩ := hgood (Fin r) inferInstance c
  · exact hc P hmono
  · have hcard : k ≤ r := by
      simpa using Fintype.card_le_of_injective (c ∘ P.term) hrain
    omega

lemma lt_H_of_avoidable {r k N : ℕ} (h : Avoidable r k N) (hrk : r < k) :
    N < H k := by
  by_contra hnot
  have hHN : H k ≤ N := Nat.le_of_not_gt hnot
  exact not_good_of_avoidable h hrk (Good.mono (good_H k) hHN)

/-- For k at least two, a bounded arithmetic progression is encoded by
its start and positive step. -/
noncomputable def apEmbedding {N k : ℕ} (hk : 2 ≤ k) :
    AP N k ↪ Fin N × Fin N where
  toFun P :=
    (⟨P.start, by
        simpa using P.isLt ⟨0, by omega⟩⟩,
     ⟨P.step, by
        have h := P.isLt ⟨1, by omega⟩
        simp only [one_mul] at h
        omega⟩)
  inj' := by
    intro P Q h
    have hstart : P.start = Q.start :=
      congrArg (fun z : Fin N × Fin N => z.1.1) h
    have hstep : P.step = Q.step :=
      congrArg (fun z : Fin N × Fin N => z.2.1) h
    cases P
    cases Q
    simp_all

/-- Colorings monochromatic on one fixed progression. -/
abbrev MonoColorings (r : ℕ) (P : AP N k) :=
  {c : Fin N → Fin r // Monochromatic c P}

noncomputable instance monoColoringsFintype (r : ℕ) (P : AP N k) :
    Fintype (MonoColorings r P) :=
  Fintype.ofFinite (MonoColorings r P)

lemma card_monoColorings_le {r N k : ℕ} (hk : 1 ≤ k) (P : AP N k) :
    Fintype.card (MonoColorings r P) ≤ r ^ (N - k + 1) := by
  classical
  let i₀ : Fin k := ⟨0, hk⟩
  let Range := Set.range P.term
  letI : Fintype Range := Fintype.ofFinite Range
  let Off := {x : Fin N // x ∉ Range}
  letI : Fintype Off := Fintype.ofFinite Off
  let encode : MonoColorings r P → Fin r × (Off → Fin r) :=
    fun c => (c.1 (P.term i₀), fun x => c.1 x.1)
  have hencode : Injective encode := by
    intro c₁ c₂ h
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ Set.range P.term
    · obtain ⟨i, rfl⟩ := hx
      have hfirst := congrArg Prod.fst h
      exact (c₁.2 i i₀).trans (hfirst.trans (c₂.2 i i₀).symm)
    · have hsecond := congrArg Prod.snd h
      exact congrFun hsecond ⟨x, hx⟩
  have hrange :
      Fintype.card Range = k := by
    simpa [Range] using
      (Fintype.card_congr (Equiv.ofInjective P.term P.term_injective)).symm
  have hoff : Fintype.card Off = N - k := by
    simpa [Off, Fintype.card_fin, hrange] using
      (Fintype.card_subtype_compl (fun x : Fin N => x ∈ Range))
  calc
    Fintype.card (MonoColorings r P)
        ≤ Fintype.card (Fin r × (Off → Fin r)) :=
      Fintype.card_le_of_injective encode hencode
    _ = r * r ^ (N - k) := by simp [hoff]
    _ = r ^ (N - k + 1) := by rw [pow_succ']

/-- Elementary union-counting lower bound for multicolor van der Waerden
numbers. -/
theorem avoidable_of_sq_lt_pow {r k N : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hkN : k ≤ N) (hsize : N ^ 2 < r ^ (k - 1)) :
    Avoidable r k N := by
  classical
  let e := apEmbedding (N := N) hk
  letI : Finite (AP N k) := Finite.of_injective e e.injective
  letI : Fintype (AP N k) := Fintype.ofFinite (AP N k)
  let bad (P : AP N k) : Finset (Fin N → Fin r) :=
    Finset.univ.filter fun c => Monochromatic c P
  let allBad : Finset (Fin N → Fin r) :=
    Finset.univ.biUnion bad
  have hbad (P : AP N k) :
      #(bad P) ≤ r ^ (N - k + 1) := by
    change #(Finset.univ.filter fun c : Fin N → Fin r => Monochromatic c P) ≤ _
    rw [← Fintype.card_subtype]
    exact card_monoColorings_le (by omega) P
  have hapcard : Fintype.card (AP N k) ≤ N ^ 2 := by
    simpa [Nat.pow_two, Fintype.card_prod] using
      Fintype.card_le_of_embedding e
  have hallBad :
      #allBad ≤ N ^ 2 * r ^ (N - k + 1) := by
    calc
      #allBad ≤ ∑ P : AP N k, #(bad P) := by
        simpa [allBad] using (Finset.card_biUnion_le :
          #(Finset.univ.biUnion bad) ≤ ∑ P ∈ Finset.univ, #(bad P))
      _ ≤ ∑ _P : AP N k, r ^ (N - k + 1) :=
        Finset.sum_le_sum fun P _ => hbad P
      _ = Fintype.card (AP N k) * r ^ (N - k + 1) := by simp
      _ ≤ N ^ 2 * r ^ (N - k + 1) :=
        Nat.mul_le_mul_right _ hapcard
  have hpow :
      N ^ 2 * r ^ (N - k + 1) < r ^ N := by
    calc
      N ^ 2 * r ^ (N - k + 1)
          < r ^ (k - 1) * r ^ (N - k + 1) :=
        Nat.mul_lt_mul_of_pos_right hsize (pow_pos (by omega) _)
      _ = r ^ ((k - 1) + (N - k + 1)) := (pow_add r _ _).symm
      _ = r ^ N := by
        congr 1
        omega
  have hcardall :
      #allBad < Fintype.card (Fin N → Fin r) := by
    calc
      #allBad ≤ N ^ 2 * r ^ (N - k + 1) := hallBad
      _ < r ^ N := hpow
      _ = Fintype.card (Fin N → Fin r) := by simp
  by_contra h
  have h' : ∀ c : Fin N → Fin r, ∃ P : AP N k, Monochromatic c P := by
    intro c
    by_contra hc
    apply h
    exact ⟨c, fun P hP => hc ⟨P, hP⟩⟩
  have huniv : (Finset.univ : Finset (Fin N → Fin r)) ⊆ allBad := by
    intro c hc
    obtain ⟨P, hP⟩ := h' c
    exact Finset.mem_biUnion.mpr ⟨P, Finset.mem_univ _, by simp [bad, hP]⟩
  exact (Nat.not_le_of_lt hcardall) (Finset.card_le_card huniv)

/-! ## The Berlekamp--Chvátal--Tuza lifting recurrence -/

/-- The quotient block containing a point of `Fin (p * M)`. -/
def blockIndex {p M : ℕ} (x : Fin (p * M)) : Fin M :=
  ⟨x.1 / p, Nat.div_lt_of_lt_mul (by
    simpa only [Nat.mul_comm] using x.2)⟩

/-- Replace the base color by one new color precisely when it agrees with
the residue.  For a fixed residue this operation is injective in the base
color, which is the feature needed for progressions whose difference is a
multiple of `p`. -/
def recolor (r q : ℕ) (b : Fin r) : Fin (r + 1) :=
  if q = b.1 then Fin.last r else Fin.castSucc b

@[simp] lemma recolor_val (r q : ℕ) (b : Fin r) :
    (recolor r q b).1 = if q = b.1 then r else b.1 := by
  by_cases h : q = b.1 <;> simp [recolor, h]

lemma recolor_injective (r q : ℕ) : Injective (recolor r q) := by
  intro b₁ b₂ h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [recolor_val] at hv
  split at hv <;> rename_i h₁
  · split at hv <;> rename_i h₂
    · omega
    · have := b₂.2
      omega
  · split at hv <;> rename_i h₂
    · have := b₁.2
      omega
    · exact hv

/-- The explicit `(r+1)`-coloring used in the lifting recurrence. -/
def bctColor {p r M : ℕ} (c : Fin M → Fin r) (x : Fin (p * M)) : Fin (r + 1) :=
  recolor r (x.1 % p) (c (blockIndex x))

/-- If `p` is prime and does not divide `d`, the first `p` points of an
arithmetic progression run through every residue modulo `p`. -/
lemma residue_surjective {p a d : ℕ} (hp : p.Prime) (hpd : ¬p ∣ d) :
    Surjective (fun i : Fin p =>
      (⟨(a + i.1 * d) % p, Nat.mod_lt _ hp.pos⟩ : Fin p)) := by
  letI : Fact p.Prime := ⟨hp⟩
  apply Finite.surjective_of_injective
  intro i j hij
  apply Fin.ext
  have hmod : (a + i.1 * d) % p = (a + j.1 * d) % p :=
    congrArg Fin.val hij
  have hz : ((a + i.1 * d : ℕ) : ZMod p) = (a + j.1 * d : ℕ) :=
    (ZMod.natCast_eq_natCast_iff' _ _ p).2 hmod
  have hd0 : (d : ZMod p) ≠ 0 := by
    intro hd
    apply hpd
    exact (ZMod.natCast_eq_zero_iff d p).mp hd
  have hijz : (i.1 : ZMod p) = (j.1 : ZMod p) := by
    apply mul_right_cancel₀ hd0
    apply add_left_cancel
    simpa only [Nat.cast_add, Nat.cast_mul] using hz
  have hijmod : i.1 % p = j.1 % p :=
    (ZMod.natCast_eq_natCast_iff' _ _ p).1 hijz
  simpa only [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] using hijmod

lemma blockIndex_term_of_dvd {p M k : ℕ} (hp : 0 < p) (P : AP (p * M) k)
    {e : ℕ} (he : P.step = p * e) (i : Fin k) :
    (blockIndex (P.term i)).1 = P.start / p + i.1 * e := by
  simp only [blockIndex, AP.term_val]
  rw [he]
  have hdvd : p ∣ i.1 * (p * e) := by
    exact ⟨i.1 * e, by ring⟩
  rw [Nat.add_div_of_dvd_left hdvd]
  have hfactor : i.1 * (p * e) = p * (i.1 * e) := by ring
  rw [hfactor, Nat.mul_div_cancel_left]
  exact hp

lemma residue_term_of_dvd {p M k : ℕ} (P : AP (p * M) k)
    {e : ℕ} (he : P.step = p * e) (i : Fin k) :
    (P.term i).1 % p = P.start % p := by
  simp only [AP.term_val, he]
  have hdvd : p ∣ i.1 * (p * e) := by
    exact ⟨i.1 * e, by ring⟩
  simp only [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, add_zero, Nat.mod_mod]

/-- Berlekamp--Chvátal--Tuza recurrence in the exact form used here:
an `r`-coloring avoiding monochromatic `k`-APs on `M` points lifts to an
`(r+1)`-coloring on `p*M` points whenever `r < p < k` and `p` is prime. -/
theorem bct_step {r k M p : ℕ} (hbase : Avoidable r k M)
    (hp : p.Prime) (hrp : r < p) (hpk : p < k) :
    Avoidable (r + 1) k (p * M) := by
  rcases hbase with ⟨c, hc⟩
  refine ⟨bctColor c, ?_⟩
  intro P hmono
  by_cases hpd : p ∣ P.step
  · obtain ⟨e, he⟩ := hpd
    have hepos : 0 < e := by
      have hstep := P.step_pos
      rw [he] at hstep
      exact Nat.pos_of_ne_zero (fun hezero => by subst e; simp at hstep)
    let Q : AP M k :=
      { start := P.start / p
        step := e
        step_pos := hepos
        isLt := fun i => by
          have hblock := (blockIndex (P.term i)).2
          rwa [blockIndex_term_of_dvd hp.pos P he i] at hblock }
    apply hc Q
    intro i j
    have h := hmono i j
    change recolor r ((P.term i).1 % p) (c (blockIndex (P.term i))) =
      recolor r ((P.term j).1 % p) (c (blockIndex (P.term j))) at h
    rw [residue_term_of_dvd P he i, residue_term_of_dvd P he j] at h
    have hb : c (blockIndex (P.term i)) = c (blockIndex (P.term j)) :=
      recolor_injective r (P.start % p) h
    have hblock (u : Fin k) : blockIndex (P.term u) = Q.term u := by
      apply Fin.ext
      exact blockIndex_term_of_dvd hp.pos P he u
    simpa only [hblock] using hb
  · have hsurj := residue_surjective (a := P.start) hp hpd
    let i₀ : Fin k := ⟨0, by omega⟩
    let v := bctColor c (P.term i₀)
    have hvle : v.1 ≤ r := by
      exact Nat.le_of_lt_succ v.2
    rcases lt_or_eq_of_le hvle with hvold | hvnew
    · obtain ⟨u, hu⟩ := hsurj (⟨v.1, hvold.trans hrp⟩ : Fin p)
      let iu : Fin k := ⟨u.1, u.2.trans hpk⟩
      have hres : (P.term iu).1 % p = v.1 := by
        simpa only [AP.term_val, iu] using congrArg Fin.val hu
      have heq : bctColor c (P.term iu) = v := hmono iu i₀
      have hval := congrArg Fin.val heq
      simp only [bctColor, recolor_val, hres] at hval
      split at hval <;> omega
    · obtain ⟨u, hu⟩ := hsurj (⟨r, hrp⟩ : Fin p)
      let iu : Fin k := ⟨u.1, u.2.trans hpk⟩
      have hres : (P.term iu).1 % p = r := by
        simpa only [AP.term_val, iu] using congrArg Fin.val hu
      have heq : bctColor c (P.term iu) = v := hmono iu i₀
      have hval := congrArg Fin.val heq
      simp only [bctColor, recolor_val, hres, hvnew] at hval
      have hb := (c (blockIndex (P.term iu))).2
      split at hval <;> omega

private theorem bct_iterate_aux {r k M p : ℕ} (n : ℕ)
    (hbase : Avoidable r k M) (hp : p.Prime) (hrn : r + n = p)
    (hpk : p < k) : Avoidable p k (p ^ n * M) := by
  induction n generalizing r M with
  | zero =>
      have hr : r = p := by omega
      subst r
      simpa using hbase
  | succ n ih =>
      have hrp : r < p := by omega
      have hstep := bct_step hbase hp hrp hpk
      have hrest : r + 1 + n = p := by omega
      have hiter := ih hstep hrest
      simpa only [pow_succ, mul_assoc, mul_left_comm] using hiter

/-- Iterating the recurrence up to `p` colors. -/
theorem bct_iterate {r k M p : ℕ} (hbase : Avoidable r k M)
    (hp : p.Prime) (hrp : r ≤ p) (hpk : p < k) :
    Avoidable p k (p ^ (p - r) * M) := by
  apply bct_iterate_aux (p - r) hbase hp
  · omega
  · exact hpk

/-! ## A quantitative lower bound and the limit -/

/-- Number of colors in the elementary random-coloring seed. -/
def seedColors (k : ℕ) : ℕ := k / 16

/-- Length of the elementary random-coloring seed. -/
def seedLength (k : ℕ) : ℕ := seedColors k ^ (k / 3)

lemma seed_avoidable (k : ℕ) (hk : 512 ≤ k) :
    Avoidable (seedColors k) k (seedLength k) := by
  have hr : 2 ≤ seedColors k := by
    simp only [seedColors]
    omega
  have hm : 2 ≤ k / 3 := by omega
  have hklt : k < 16 * (seedColors k + 1) := by
    simp only [seedColors]
    omega
  have hrlarge : 32 ≤ seedColors k := by
    simp only [seedColors]
    omega
  have hk_sq : k ≤ seedColors k ^ 2 := by
    have hmul : 16 * (seedColors k + 1) ≤ seedColors k * seedColors k := by
      nlinarith
    simpa only [pow_two] using hklt.le.trans hmul
  have hkN : k ≤ seedLength k := by
    exact hk_sq.trans (Nat.pow_le_pow_right (by omega) hm)
  have hexp : 2 * (k / 3) < k - 1 := by omega
  have hsize : seedLength k ^ 2 < seedColors k ^ (k - 1) := by
    simpa only [seedLength, ← pow_mul, Nat.mul_comm] using
      Nat.pow_lt_pow_right (show 1 < seedColors k by omega) hexp
  exact avoidable_of_sq_lt_pow hr (by omega) hkN hsize

/-- A fixed prime window supplied by the prime number theorem.  Integer
inequalities are retained to make all subsequent exponent estimates exact. -/
lemma eventually_prime_window :
    ∀ᶠ k : ℕ in atTop,
      ∃ p : ℕ, p.Prime ∧ 19 * k < 20 * p ∧ p < k := by
  have hprime := prime_between (ε := (1 / 20 : ℝ)) (by norm_num)
  rw [Filter.eventually_atTop] at hprime ⊢
  obtain ⟨X, hX⟩ := hprime
  let K : ℕ := max 1 ⌈(20 / 19 : ℝ) * max X 0⌉₊
  refine ⟨K, ?_⟩
  intro k hk
  have hkpos : 0 < k := lt_of_lt_of_le (by simp [K]) hk
  have hceil :
      (20 / 19 : ℝ) * max X 0 ≤ (⌈(20 / 19 : ℝ) * max X 0⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hKk : (⌈(20 / 19 : ℝ) * max X 0⌉₊ : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (le_trans (Nat.le_max_right _ _) hk)
  have hxk : X ≤ (19 / 20 : ℝ) * (k : ℝ) := by
    have hXmax : X ≤ max X 0 := le_max_left _ _
    nlinarith
  obtain ⟨p, hp, hpLow, hpHigh⟩ := hX ((19 / 20 : ℝ) * (k : ℝ)) hxk
  refine ⟨p, hp, ?_, ?_⟩
  · have hreal : (19 * k : ℕ) < 20 * p := by
      exact_mod_cast (show (19 : ℝ) * k < 20 * p by nlinarith)
    exact hreal
  · have hreal : (p : ℝ) < k := by
      calc
        (p : ℝ) < (21 / 20 : ℝ) * ((19 / 20 : ℝ) * (k : ℝ)) := by
          convert hpHigh using 1 <;> norm_num
        _ = (399 / 400 : ℝ) * (k : ℝ) := by ring
        _ < (k : ℝ) := by nlinarith [show (0 : ℝ) < k by positivity]
    exact_mod_cast hreal

/-- The fully explicit lower-bound construction used in the asymptotic
argument. -/
def construction (k p : ℕ) : ℕ :=
  p ^ (p - seedColors k) * seedLength k

lemma construction_lt_H (k p : ℕ) (hk : 512 ≤ k) (hp : p.Prime)
    (hpLow : 19 * k < 20 * p) (hpk : p < k) :
    construction k p < H k := by
  have hrp : seedColors k ≤ p := by
    simp only [seedColors]
    omega
  have hav := bct_iterate (seed_avoidable k hk) hp hrp hpk
  exact lt_H_of_avoidable hav hpk

lemma construction_power_lower (k p : ℕ) (hk : 512 ≤ k)
    (hpLow : 19 * k < 20 * p) :
    seedColors k ^ (k + k / 8) ≤ construction k p := by
  have hrp : seedColors k ≤ p := by
    simp only [seedColors]
    omega
  have hexp : k + k / 8 ≤ p - seedColors k + k / 3 := by
    simp only [seedColors]
    omega
  calc
    seedColors k ^ (k + k / 8)
        ≤ seedColors k ^ (p - seedColors k + k / 3) :=
      Nat.pow_le_pow_right (by simp [seedColors]; omega) hexp
    _ = seedColors k ^ (p - seedColors k) * seedLength k := by
      simp only [seedLength, pow_add]
    _ ≤ p ^ (p - seedColors k) * seedLength k :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hrp _)
    _ = construction k p := rfl

lemma root_lower_bound (k p : ℕ) (hk : 512 ≤ k)
    (hpLow : 19 * k < 20 * p) (hH : construction k p < H k) :
    (seedColors k : ℝ) ^ (1 / 16 : ℝ) / 32 ≤
      (H k : ℝ) ^ (1 / (k : ℝ)) / (k : ℝ) := by
  let r := seedColors k
  let t := k / 8
  have hkpos : 0 < k := by omega
  have hrpos : 0 < r := by simp [r, seedColors]; omega
  have hNat : r ^ (k + t) ≤ H k := by
    exact (construction_power_lower k p hk hpLow).trans hH.le
  have hcast : (r ^ (k + t) : ℕ) ≤ (H k : ℝ) := by
    exact_mod_cast hNat
  have hroot₀ := Real.rpow_le_rpow
    (show (0 : ℝ) ≤ ((r ^ (k + t) : ℕ) : ℝ) by positivity)
    hcast (show 0 ≤ 1 / (k : ℝ) by positivity)
  have hrewrite :
      ((r ^ (k + t) : ℕ) : ℝ) ^ (1 / (k : ℝ)) =
        (r : ℝ) * (r : ℝ) ^ ((t : ℝ) / (k : ℝ)) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ r)]
    have he : ((k + t : ℕ) : ℝ) * (1 / (k : ℝ)) =
        1 + (t : ℝ) / (k : ℝ) := by
      push_cast
      field_simp
    rw [he, Real.rpow_add (by positivity), Real.rpow_one]
  have hkt : k ≤ 16 * t := by
    dsimp only [t]
    omega
  have hexp : (1 / 16 : ℝ) ≤ (t : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < k)]
    have hkt' : (k : ℝ) ≤ 16 * (t : ℝ) := by exact_mod_cast hkt
    nlinarith
  have hpow : (r : ℝ) ^ (1 / 16 : ℝ) ≤
      (r : ℝ) ^ ((t : ℝ) / (k : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ r by omega)) hexp
  have hroot : (r : ℝ) * (r : ℝ) ^ (1 / 16 : ℝ) ≤
      (H k : ℝ) ^ (1 / (k : ℝ)) := by
    calc
      (r : ℝ) * (r : ℝ) ^ (1 / 16 : ℝ)
          ≤ (r : ℝ) * (r : ℝ) ^ ((t : ℝ) / (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = ((r ^ (k + t) : ℕ) : ℝ) ^ (1 / (k : ℝ)) := hrewrite.symm
      _ ≤ (H k : ℝ) ^ (1 / (k : ℝ)) := hroot₀
  have hkr : k ≤ 32 * r := by
    dsimp only [r, seedColors]
    omega
  have hratio : (1 / 32 : ℝ) ≤ (r : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < k)]
    have hkr' : (k : ℝ) ≤ 32 * r := by exact_mod_cast hkr
    nlinarith
  change (r : ℝ) ^ (1 / 16 : ℝ) / 32 ≤ _
  calc
    (r : ℝ) ^ (1 / 16 : ℝ) / 32 =
        (1 / 32 : ℝ) * (r : ℝ) ^ (1 / 16 : ℝ) := by ring
    _ ≤ ((r : ℝ) / (k : ℝ)) * (r : ℝ) ^ (1 / 16 : ℝ) :=
      mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg (by positivity) _)
    _ = ((r : ℝ) * (r : ℝ) ^ (1 / 16 : ℝ)) / (k : ℝ) := by ring
    _ ≤ (H k : ℝ) ^ (1 / (k : ℝ)) / (k : ℝ) :=
      (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < k)).2 hroot

lemma eventually_root_lower_bound :
    ∀ᶠ k : ℕ in atTop,
      (seedColors k : ℝ) ^ (1 / 16 : ℝ) / 32 ≤
        (H k : ℝ) ^ (1 / (k : ℝ)) / (k : ℝ) := by
  filter_upwards [eventually_prime_window, Filter.eventually_ge_atTop 512]
    with k hprime hk
  obtain ⟨p, hp, hpLow, hpk⟩ := hprime
  exact root_lower_bound k p hk hpLow (construction_lt_H k p hk hp hpLow hpk)

/-- Resolution of Erdős Problem 190: the normalized k-th root of the exact
canonical van der Waerden number tends to infinity. -/
theorem erdos_190 :
    Tendsto (fun k : ℕ => (H k : ℝ) ^ (1 / (k : ℝ)) / (k : ℝ))
      atTop atTop := by
  have hrNat : Tendsto seedColors atTop atTop := by
    change Tendsto (fun k : ℕ => k / 16) atTop atTop
    exact Nat.tendsto_div_const_atTop (by norm_num : (16 : ℕ) ≠ 0)
  have hrReal : Tendsto (fun k : ℕ => (seedColors k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hrNat
  have hrpow : Tendsto (fun k : ℕ => (seedColors k : ℝ) ^ (1 / 16 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16)).comp hrReal
  have hlower : Tendsto
      (fun k : ℕ => (seedColors k : ℝ) ^ (1 / 16 : ℝ) / 32)
      atTop atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num) hrpow
  exact tendsto_atTop_mono' atTop eventually_root_lower_bound hlower

#print axioms erdos_190

end Erdos190
