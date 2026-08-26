import ErdosProblems.Erdos157.LogFibers
import ErdosProblems.Erdos157b.TagFields

/-! Trial tag triples with a fixed low prefix and disjoint high supports. -/

namespace Erdos157.Binary

open Erdos157.Elementary

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

structure MaskTarget (k : ℕ) where
  logarithm : LogVector K k
  firstMoment : ∀ i : Fin k, TagField i
  secondMoment : ∀ i : Fin k, TagField i

abbrev LevelMasks (k : ℕ) := ∀ i : Fin k, TagField i → LogDigit K i

structure MaskTrialFamily {k : ℕ} (z : MaskTarget K k) (h n : ℕ) where
  triple : ∀ i : Fin k, Fin n → TagField i × TagField i × TagField i
  moments : ∀ i j, Parabola.IsTriple (z.firstMoment i) (z.secondMoment i) (triple i j)
  nonconstant : ∀ i j, 2 ≤ (Parabola.support (triple i j)).card
  low_constant : ∀ i, i.1 < h → ∀ j l, triple i j = triple i l
  high_disjoint : ∀ i, ¬i.1 < h →
    Pairwise (fun j l => Disjoint (Parabola.support (triple i j)) (Parabola.support (triple i l)))

theorem exists_maskTrialFamily {k h n : ℕ} (z : MaskTarget K k)
    (hn : 1 ≤ n) (hsize : ∀ i, h ≤ i → 7 * n ≤ 7 ^ tagDimension i) : Nonempty (MaskTrialFamily K z h n) := by
  classical
  have hex (i : Fin k) : ∃ T : Fin n → TagField i × TagField i × TagField i,
      (∀ j, Parabola.IsTriple (z.firstMoment i) (z.secondMoment i) (T j)) ∧
      (∀ j, 2 ≤ (Parabola.support (T j)).card) ∧
      (i.1 < h → ∀ j l, T j = T l) ∧
      (¬i.1 < h → Pairwise (fun j l => Disjoint (Parabola.support (T j)) (Parabola.support (T l)))) := by
    by_cases hi : i.1 < h
    · obtain ⟨T, hm, hc, _⟩ := tagField_disjoint_trials i 1 (by decide)
        (by simpa using Nat.le_pow (a := 7) (tagDimension_pos i)) (z.firstMoment i) (z.secondMoment i)
      exact ⟨fun _ => T 0, fun _ => hm 0, fun _ => hc 0, fun _ _ _ => rfl,
        fun hnot => (hnot hi).elim⟩
    · obtain ⟨T, hm, hc, hd⟩ := tagField_disjoint_trials i n hn
        (hsize i (by omega))
        (z.firstMoment i) (z.secondMoment i)
      exact ⟨T, hm, hc, fun hyes => (hi hyes).elim, fun _ => hd⟩
  choose T hm hc hl hh using hex
  exact ⟨⟨T, hm, hc, hl, hh⟩⟩

noncomputable def trialLogVector {k h n : ℕ} {z : MaskTarget K k}
    (T : MaskTrialFamily K z h n) (τ : LevelMasks K k) (j : Fin n) : LogVector K k :=
  fun i => z.logarithm i - Masks.maskSum (T.triple i j) (τ i)

noncomputable def MaskTargetHit {k : ℕ} (τ : LevelMasks K k) (z : MaskTarget K k) : Prop :=
  ∃ t : ∀ i : Fin k, TagField i × TagField i × TagField i,
    (∀ i, Parabola.IsTriple (z.firstMoment i) (z.secondMoment i) (t i)) ∧
      GoodLogVector K k (fun i => z.logarithm i - Masks.maskSum (t i) (τ i))

theorem maskTargetHit_of_trial {k h n : ℕ} {z : MaskTarget K k}
    (T : MaskTrialFamily K z h n) (τ : LevelMasks K k) (j : Fin n)
    (hj : GoodLogVector K k (trialLogVector K T τ j)) : MaskTargetHit K τ z :=
  ⟨fun i => T.triple i j, fun i => T.moments i j, hj⟩

end Erdos157.Binary
