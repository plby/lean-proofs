/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Licensed under the Apache License, Version 2.0; see LICENSE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 884.
Informal proof: Daniel Larsen, building on Terence Tao's construction.
Formal proof: Claude Fable 5, with minor guidance from R. J. Honicky.
Source: https://www.erdosproblems.com/884#post-7362
https://github.com/honicky/erdos884/tree/323e9a01306df1e094b434beaa48c018370fe258
Original Lean/Mathlib version: 4.31.0.
Original Mathlib commit: fabf563a7c95a166b8d7b6efca11c8b4dc9d911f.
The port reuses the repository's existing PNT+ Selberg sieve by Arend Mellendijk.
-/
import ErdosProblems.Erdos884.Definitions
import ErdosProblems.Erdos896.PNT.Mathlib.NumberTheory.Sieve.SelbergBounds

open Finset

set_option linter.mathlibStandardSet false

/-!
# Erdős Problem 884 — shared definitions and basic lemmas

For a finite set `A ⊆ ℕ` we study
* `pairSum A`  — the sum of `1/(b-a)` over all pairs `a < b` in `A`  (written `T(A)` in the papers)
* `gapSum A`   — the sum of `1/(b-a)` over *consecutive* pairs of `A` (written `S(A)`)

`pairSumOn A C` restricts the pair sum to pairs satisfying a predicate `C`; `gapSum` is by
definition the pair sum over consecutive pairs.  This makes "bound the consecutive sum class by
class, where each class is estimated by its full pair sum" a one-liner (`pairSumOn_mono_pred`).
-/

namespace Erdos884

/-- The reciprocal `1/(b - a)` of a gap, as a real number. -/
noncomputable abbrev invGap (a b : ℕ) : ℝ := ((b : ℝ) - (a : ℝ))⁻¹

/-- Sum of `1/(b-a)` over pairs `a < b` in `A` with `C a b`. -/
noncomputable def pairSumOn (A : Finset ℕ) (C : ℕ → ℕ → Prop) : ℝ :=
  letI : DecidablePred fun p : ℕ × ℕ => p.1 < p.2 ∧ C p.1 p.2 :=
    fun _ => Classical.propDecidable _
  ∑ p ∈ (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2 ∧ C p.1 p.2), invGap p.1 p.2

/-- `T(A)`: sum of reciprocals of all pairwise gaps of `A`. -/
noncomputable def pairSum (A : Finset ℕ) : ℝ := pairSumOn A fun _ _ => True

/-- `a` and `b` are consecutive elements of `A`: both belong to `A`, `a < b`, and no element
of `A` lies strictly between them. -/
def IsConsecutive (A : Finset ℕ) (a b : ℕ) : Prop :=
  a ∈ A ∧ b ∈ A ∧ a < b ∧ ∀ c ∈ A, ¬ (a < c ∧ c < b)

/-- `S(A)`: sum of reciprocals of consecutive gaps of `A`. -/
noncomputable def gapSum (A : Finset ℕ) : ℝ := pairSumOn A (IsConsecutive A)

/-! ## Basic properties (to be proved in `Basic884`) -/

lemma invGap_pos {a b : ℕ} (h : a < b) : 0 < invGap a b := by
  have : (1 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
    linarith
  positivity

lemma invGap_le_one {a b : ℕ} (h : a < b) : invGap a b ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
    linarith
  calc invGap a b ≤ (1 : ℝ)⁻¹ := by unfold invGap; gcongr
    _ = 1 := by norm_num

/-- If the (real) gap exceeds `N > 0` then the reciprocal gap is at most `1/N`. -/
lemma invGap_le {a b : ℕ} {N : ℝ} (hN : 0 < N) (h : N < (b : ℝ) - a) :
    invGap a b ≤ N⁻¹ := by
  unfold invGap
  gcongr

lemma pairSumOn_nonneg (A : Finset ℕ) (C : ℕ → ℕ → Prop) : 0 ≤ pairSumOn A C := by
  have memf : ∀ {q : ℕ × ℕ → Prop} {inst : DecidablePred q} {s : Finset (ℕ × ℕ)} {x : ℕ × ℕ},
      x ∈ @Finset.filter _ q inst s ↔ x ∈ s ∧ q x := by
    intro q inst s x
    let := inst
    exact Finset.mem_filter
  unfold pairSumOn
  refine Finset.sum_nonneg fun p hp => ?_
  exact (invGap_pos (memf.mp hp).2.1).le

lemma pairSum_nonneg (A : Finset ℕ) : 0 ≤ pairSum A := pairSumOn_nonneg A _

lemma gapSum_nonneg (A : Finset ℕ) : 0 ≤ gapSum A := pairSumOn_nonneg A _

/-- Enlarging the predicate (on pairs of elements of `A`) enlarges the sum. -/
lemma pairSumOn_mono_pred {A : Finset ℕ} {C C' : ℕ → ℕ → Prop}
    (h : ∀ a b, a ∈ A → b ∈ A → a < b → C a b → C' a b) :
    pairSumOn A C ≤ pairSumOn A C' := by
  have memf : ∀ {q : ℕ × ℕ → Prop} {inst : DecidablePred q} {s : Finset (ℕ × ℕ)} {x : ℕ × ℕ},
      x ∈ @Finset.filter _ q inst s ↔ x ∈ s ∧ q x := by
    intro q inst s x
    let := inst
    exact Finset.mem_filter
  unfold pairSumOn
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    have hp' := memf.mp hp
    have hpA := Finset.mem_product.mp hp'.1
    exact memf.mpr ⟨hp'.1, hp'.2.1, h p.1 p.2 hpA.1 hpA.2 hp'.2.1 hp'.2.2⟩
  · intro p hp _
    exact (invGap_pos (memf.mp hp).2.1).le

/-- A pair sum over a disjunction of predicates is at most the sum of the pair sums. -/
lemma pairSumOn_or_le (A : Finset ℕ) (C₁ C₂ : ℕ → ℕ → Prop) :
    pairSumOn A (fun a b => C₁ a b ∨ C₂ a b) ≤ pairSumOn A C₁ + pairSumOn A C₂ := by
  classical
  have memf : ∀ {q : ℕ × ℕ → Prop} {inst : DecidablePred q} {s : Finset (ℕ × ℕ)} {x : ℕ × ℕ},
      x ∈ @Finset.filter _ q inst s ↔ x ∈ s ∧ q x := by
    intro q inst s x
    let := inst
    exact Finset.mem_filter
  have key : ∀ (u s₁ s₂ : Finset (ℕ × ℕ)), u ⊆ s₁ ∪ s₂ →
      (∀ p ∈ s₁, (0:ℝ) ≤ invGap p.1 p.2) → (∀ p ∈ s₂, (0:ℝ) ≤ invGap p.1 p.2) →
      ∑ p ∈ u, invGap p.1 p.2 ≤ ∑ p ∈ s₁, invGap p.1 p.2 + ∑ p ∈ s₂, invGap p.1 p.2 := by
    intro u s₁ s₂ hu h1 h2
    calc ∑ p ∈ u, invGap p.1 p.2 ≤ ∑ p ∈ s₁ ∪ s₂, invGap p.1 p.2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hu fun p hp _ => ?_
          rcases Finset.mem_union.mp hp with hm | hm
          · exact h1 p hm
          · exact h2 p hm
      _ ≤ ∑ p ∈ s₁, invGap p.1 p.2 + ∑ p ∈ s₂, invGap p.1 p.2 := by
          have h0 : (0:ℝ) ≤ ∑ p ∈ s₁ ∩ s₂, invGap p.1 p.2 :=
            Finset.sum_nonneg fun p hp => h1 p (Finset.mem_inter.mp hp).1
          rw [← Finset.sum_union_inter]
          exact le_add_of_nonneg_right h0
  unfold pairSumOn
  refine key _ _ _ ?_ ?_ ?_
  · intro p hp
    have hp' := memf.mp hp
    rcases hp'.2.2 with hc | hc
    · exact Finset.mem_union_left _ (memf.mpr ⟨hp'.1, hp'.2.1, hc⟩)
    · exact Finset.mem_union_right _ (memf.mpr ⟨hp'.1, hp'.2.1, hc⟩)
  · intro p hp
    exact (invGap_pos (memf.mp hp).2.1).le
  · intro p hp
    exact (invGap_pos (memf.mp hp).2.1).le

lemma pairSumOn_le_pairSum (A : Finset ℕ) (C : ℕ → ℕ → Prop) :
    pairSumOn A C ≤ pairSum A :=
  pairSumOn_mono_pred fun _ _ _ _ _ _ => trivial

/-- Consecutive pairs of a subset: if `B ⊆ A` and `a, b ∈ B` are consecutive in `A`,
they are consecutive in `B`. -/
lemma IsConsecutive.of_subset {A B : Finset ℕ} {a b : ℕ} (hBA : B ⊆ A)
    (ha : a ∈ B) (hb : b ∈ B) (h : IsConsecutive A a b) : IsConsecutive B a b := by
  exact ⟨ha, hb, h.2.2.1, fun c hc => h.2.2.2 c (hBA hc)⟩

/-- Bounding the gap sum by classes: if every consecutive pair of `A` satisfies `C`,
then `gapSum A ≤ pairSumOn A C`. -/
lemma gapSum_le_pairSumOn {A : Finset ℕ} {C : ℕ → ℕ → Prop}
    (h : ∀ a b, IsConsecutive A a b → C a b) :
    gapSum A ≤ pairSumOn A C :=
  pairSumOn_mono_pred fun a b _ _ _ hc => h a b hc

/-- Superadditivity of the pair sum over disjoint subsets. -/
lemma sum_pairSum_le_pairSum {ι : Type*} {I : Finset ι} {B : ι → Finset ℕ} {A : Finset ℕ}
    (hBA : ∀ i ∈ I, B i ⊆ A)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B i) (B j)) :
    ∑ i ∈ I, pairSum (B i) ≤ pairSum A := by
  classical
  have memf : ∀ {q : ℕ × ℕ → Prop} {inst : DecidablePred q} {s : Finset (ℕ × ℕ)} {x : ℕ × ℕ},
      x ∈ @Finset.filter _ q inst s ↔ x ∈ s ∧ q x := by
    intro q inst s x
    let := inst
    exact Finset.mem_filter
  have key : ∀ (s : Finset (ℕ × ℕ)) (F : ι → Finset (ℕ × ℕ)),
      (∀ i ∈ I, F i ⊆ s) →
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (F i) (F j)) →
      (∀ p ∈ s, (0:ℝ) ≤ invGap p.1 p.2) →
      ∑ i ∈ I, ∑ p ∈ F i, invGap p.1 p.2 ≤ ∑ p ∈ s, invGap p.1 p.2 := by
    intro s F hFs hFd hnn
    have hpd : Set.PairwiseDisjoint (↑I : Set ι) F := by
      intro i hi j hj hij
      exact hFd i hi j hj hij
    calc ∑ i ∈ I, ∑ p ∈ F i, invGap p.1 p.2
        = ∑ p ∈ I.biUnion F, invGap p.1 p.2 := (Finset.sum_biUnion hpd).symm
      _ ≤ ∑ p ∈ s, invGap p.1 p.2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ => hnn p hp
          intro p hp
          obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
          exact hFs i hi hpi
  unfold pairSum pairSumOn
  refine key _ _ ?_ ?_ ?_
  · intro i hi p hp
    have hp' := memf.mp hp
    have hpq := Finset.mem_product.mp hp'.1
    exact memf.mpr
      ⟨Finset.mem_product.mpr ⟨hBA i hi hpq.1, hBA i hi hpq.2⟩, hp'.2⟩
  · intro i hi j hj hij
    rw [Finset.disjoint_left]
    intro p hpi hpj
    have h1 := Finset.mem_product.mp (memf.mp hpi).1
    have h2 := Finset.mem_product.mp (memf.mp hpj).1
    exact (Finset.disjoint_left.mp (hdisj i hi j hj hij)) h1.1 h2.1
  · intro p hp
    exact (invGap_pos (memf.mp hp).2.1).le

/-- The number of consecutive pairs is less than the cardinality: the map to the left
endpoint is injective. Combined with a uniform gap bound this bounds `gapSum`. -/
lemma gapSum_le_of_separated {A : Finset ℕ} {N : ℕ} (hN : 0 < N)
    (h : ∀ a ∈ A, ∀ b ∈ A, a < b → N < b - a) :
    gapSum A ≤ ((A.card - 1 : ℕ) : ℝ) / N := by
  classical
  have memf : ∀ {q : ℕ × ℕ → Prop} {inst : DecidablePred q} {s : Finset (ℕ × ℕ)} {x : ℕ × ℕ},
      x ∈ @Finset.filter _ q inst s ↔ x ∈ s ∧ q x := by
    intro q inst s x
    let := inst
    exact Finset.mem_filter
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∀ S : Finset (ℕ × ℕ),
      (∀ p ∈ S, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 < p.2 ∧ IsConsecutive A p.1 p.2) →
      ∑ p ∈ S, invGap p.1 p.2 ≤ ((A.card - 1 : ℕ) : ℝ) / N := by
    intro S hS
    rcases S.eq_empty_or_nonempty with rfl | hSne
    · have h0 : (0:ℝ) ≤ ((A.card - 1 : ℕ) : ℝ) / N := by positivity
      simpa using h0
    · have hAne : A.Nonempty := by
        obtain ⟨p, hp⟩ := hSne
        exact ⟨p.1, (hS p hp).1⟩
      have hterm : ∀ p ∈ S, invGap p.1 p.2 ≤ (N : ℝ)⁻¹ := by
        intro p hp
        obtain ⟨h1, h2, hlt, -⟩ := hS p hp
        refine invGap_le hN' ?_
        have hgap := h p.1 h1 p.2 h2 hlt
        have hgap' : N + p.1 < p.2 := by omega
        have hgapR : (N : ℝ) + p.1 < p.2 := by exact_mod_cast hgap'
        linarith
      have hcard : S.card ≤ A.card - 1 := by
        have hinj : S.card ≤ (A.erase (A.max' hAne)).card := by
          apply Finset.card_le_card_of_injOn (fun p => p.1)
          · intro p hp
            obtain ⟨h1, h2, hlt, -⟩ := hS p hp
            refine Finset.mem_erase.mpr ⟨?_, h1⟩
            intro hpM
            have hpM' : p.1 = A.max' hAne := hpM
            have hle : p.2 ≤ A.max' hAne := A.le_max' p.2 h2
            omega
          · intro p hp q hq hpq
            simp only [Finset.mem_coe] at hp hq
            have hpq' : p.1 = q.1 := hpq
            obtain ⟨hp1, hp2, hplt, hpc⟩ := hS p hp
            obtain ⟨hq1, hq2, hqlt, hqc⟩ := hS q hq
            have h2eq : p.2 = q.2 := by
              by_contra hne
              rcases Nat.lt_or_ge p.2 q.2 with hlt2 | hge2
              · exact hqc.2.2.2 p.2 hp2 ⟨by omega, hlt2⟩
              · have hlt2 : q.2 < p.2 := by omega
                exact hpc.2.2.2 q.2 hq2 ⟨by omega, hlt2⟩
            exact Prod.ext hpq' h2eq
        rwa [Finset.card_erase_of_mem (A.max'_mem hAne)] at hinj
      calc ∑ p ∈ S, invGap p.1 p.2
          ≤ ∑ _p ∈ S, (N : ℝ)⁻¹ := Finset.sum_le_sum hterm
        _ = (S.card : ℝ) * (N : ℝ)⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((A.card - 1 : ℕ) : ℝ) * (N : ℝ)⁻¹ := by
            have hc : (S.card : ℝ) ≤ ((A.card - 1 : ℕ) : ℝ) := by exact_mod_cast hcard
            gcongr
        _ = ((A.card - 1 : ℕ) : ℝ) / N := by rw [div_eq_mul_inv]
  unfold gapSum pairSumOn
  refine key _ fun p hp => ?_
  have hp' := memf.mp hp
  have hpq := Finset.mem_product.mp hp'.1
  exact ⟨hpq.1, hpq.2, hp'.2.1, hp'.2.2⟩

end Erdos884
