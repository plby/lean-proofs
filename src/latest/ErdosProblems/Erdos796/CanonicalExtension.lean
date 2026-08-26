import ErdosProblems.Erdos796.Core

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Canonical extension of a compatible prefix

This file develops the set- and cardinality-theoretic part of the canonical
extension.  The multiplicative compatibility proof is kept separate: it
requires a product classification by the number of primes larger than the
prefix cutoff.
-/

namespace Erdos796

open Filter Topology

/-- Primes in the half-open cutoff interval `J < p ≤ j`. -/
def newPrimes (J j : ℕ) : Finset ℕ :=
  (Finset.Ioc J j).filter Nat.Prime

/-- Extend a prefix through `J` by adjoining every new prime above `J`. -/
def canonicalExtension (J : ℕ) (U : ℕ → Finset ℕ) (j : ℕ) : Finset ℕ :=
  if j ≤ J then U j else U J ∪ newPrimes J j

@[simp] theorem canonicalExtension_of_le {J j : ℕ} {U : ℕ → Finset ℕ}
    (hj : j ≤ J) : canonicalExtension J U j = U j := by
  simp [canonicalExtension, hj]

@[simp] theorem canonicalExtension_of_lt {J j : ℕ} {U : ℕ → Finset ℕ}
    (hj : J < j) : canonicalExtension J U j = U J ∪ newPrimes J j := by
  have hnot : ¬j ≤ J := Nat.not_le_of_lt hj
  simp [canonicalExtension, hnot]

theorem mem_newPrimes {J j p : ℕ} :
    p ∈ newPrimes J j ↔ J < p ∧ p ≤ j ∧ p.Prime := by
  simp [newPrimes, and_assoc]

/-- The new-prime interval is the difference of two prime-counting finsets. -/
theorem newPrimes_eq_sdiff {J j : ℕ} :
    newPrimes J j = Nat.primesLE j \ Nat.primesLE J := by
  ext p
  simp only [mem_newPrimes, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨hJp, hpj, hp⟩
    exact ⟨⟨hpj, hp⟩, fun h => (Nat.not_le_of_lt hJp) h.1⟩
  · rintro ⟨⟨hpj, hp⟩, hnot⟩
    have hJp : J < p := by
      by_contra h
      exact hnot ⟨Nat.le_of_not_gt h, hp⟩
    exact ⟨hJp, hpj, hp⟩

theorem card_newPrimes {J j : ℕ} (hJj : J ≤ j) :
    (newPrimes J j).card = Nat.primeCounting j - Nat.primeCounting J := by
  rw [newPrimes_eq_sdiff]
  rw [Finset.card_sdiff_of_subset (Nat.primesLE_mono hJj)]
  simp

/-- Old cofactors and newly adjoined primes are disjoint. -/
theorem disjoint_old_new {J j : ℕ} {U : ℕ → Finset ℕ}
    (hU : U J ⊆ positiveIcc J) :
    Disjoint (U J) (newPrimes J j) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hxU hxP
  have hxle : x ≤ J := (mem_positiveIcc.mp (hU hxU)).2
  have hxgt : J < x := (mem_newPrimes.mp hxP).1
  omega

/-- The canonical extension remains fibrewise inside `[j]`. -/
theorem canonicalExtension_subset {J : ℕ} {U : ℕ → Finset ℕ}
    (hU : CompatiblePrefix J U) (j : ℕ) :
    canonicalExtension J U j ⊆ positiveIcc j := by
  by_cases hj : j ≤ J
  · simpa [canonicalExtension, hj] using! hU.1 j hj
  · rw [canonicalExtension_of_lt (Nat.lt_of_not_ge hj)]
    intro x hx
    rcases Finset.mem_union.mp hx with hxOld | hxNew
    · have hxIcc := mem_positiveIcc.mp (hU.1 J le_rfl hxOld)
      exact mem_positiveIcc.mpr ⟨hxIcc.1, hxIcc.2.trans (Nat.le_of_lt (Nat.lt_of_not_ge hj))⟩
    · have hp := mem_newPrimes.mp hxNew
      exact mem_positiveIcc.mpr ⟨hp.2.2.one_le, hp.2.1⟩

/-- Exact cardinality of every extended fibre past the cutoff. -/
theorem card_canonicalExtension {J j : ℕ} {U : ℕ → Finset ℕ}
    (hJj : J < j) (hU : U J ⊆ positiveIcc J) :
    (canonicalExtension J U j).card =
      (U J).card + (Nat.primeCounting j - Nat.primeCounting J) := by
  rw [canonicalExtension_of_lt hJj]
  rw [Finset.card_union_of_disjoint (disjoint_old_new hU)]
  rw [card_newPrimes hJj.le]

/-- The excess is constant along the canonical tail. -/
theorem excessInt_canonicalExtension {J j : ℕ} {U : ℕ → Finset ℕ}
    (hJj : J < j) (hU : U J ⊆ positiveIcc J) :
    excessInt (canonicalExtension J U) j = excessInt U J := by
  rw [excessInt, excessInt, card_canonicalExtension hJj hU]
  have hπ : Nat.primeCounting J ≤ Nat.primeCounting j :=
    Nat.monotone_primeCounting hJj.le
  push_cast [Nat.cast_sub hπ]
  ring

theorem excess_canonicalExtension {J j : ℕ} {U : ℕ → Finset ℕ}
    (hJj : J < j) (hU : U J ⊆ positiveIcc J) :
    excess (canonicalExtension J U) j = excess U J := by
  simp only [excess, excessInt_canonicalExtension hJj hU]

/-! ## Telescoping of the canonical tail -/

theorem cofactorWeight_eq_sub (j : ℕ) (hj : 0 < j) :
    cofactorWeight j =
      (1 : ℝ) / j - 1 / (j + 1 : ℕ) := by
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hj10 : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [cofactorWeight]
  field_simp
  push_cast
  ring

/-- The first `N` weights strictly after the cutoff `J`. -/
noncomputable def cofactorTailPartial (J N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, cofactorWeight (J + 1 + k)

theorem cofactorTailPartial_eq (J N : ℕ) :
    cofactorTailPartial J N =
      (1 : ℝ) / (J + 1 : ℕ) - 1 / (J + N + 1 : ℕ) := by
  induction N with
  | zero => simp [cofactorTailPartial]
  | succ N ih =>
      rw [cofactorTailPartial, Finset.sum_range_succ, ← cofactorTailPartial, ih]
      rw [cofactorWeight_eq_sub (J + 1 + N) (by omega)]
      push_cast
      ring

theorem cofactorWeight_nonneg (j : ℕ) : 0 ≤ cofactorWeight j := by
  rw [cofactorWeight]
  positivity

/-- The full canonical tail has the exact telescoping sum `1/(J+1)`. -/
theorem hasSum_cofactorTail (J : ℕ) :
    HasSum (fun k : ℕ => cofactorWeight (J + 1 + k))
      ((1 : ℝ) / (J + 1 : ℕ)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun k => cofactorWeight_nonneg (J + 1 + k))]
  change Tendsto (fun N : ℕ => cofactorTailPartial J N) atTop
    (𝓝 ((1 : ℝ) / (J + 1 : ℕ)))
  have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / (J + N + 1 : ℕ)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat (J + 1))
    exact h.congr' (Eventually.of_forall fun N => by
      norm_num [Nat.cast_add]
      ring)
  have hlim : Tendsto
      (fun N : ℕ => (1 : ℝ) / (J + 1 : ℕ) - 1 / (J + N + 1 : ℕ))
      atTop (𝓝 ((1 : ℝ) / (J + 1 : ℕ))) := by
    have hconst : Tendsto
        (fun _ : ℕ => (1 : ℝ) / (J + 1 : ℕ)) atTop
        (𝓝 ((1 : ℝ) / (J + 1 : ℕ))) := tendsto_const_nhds
    simpa using! hconst.sub hinv
  exact hlim.congr' (Eventually.of_forall fun N => (cofactorTailPartial_eq J N).symm)

end Erdos796
