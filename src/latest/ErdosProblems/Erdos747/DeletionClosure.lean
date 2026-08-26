import ErdosProblems.Erdos747.ResidualPointwise

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Uniform layer bounds close the stopped deletion argument -/

/-- `SomeDeletionPrefix` is monotone in its prefix predicate. -/
lemma someDeletionPrefix_mono {n : ℕ} {H : Finset (Edge n)}
    {P Q : (t : ℕ) → DeletionHistory H t → Prop}
    (hPQ : ∀ t (e : DeletionHistory H t), P t e → Q t e) :
    ∀ T (e : DeletionHistory H T),
      SomeDeletionPrefix P T e → SomeDeletionPrefix Q T e := by
  intro T
  induction T with
  | zero =>
      intro e he
      exact hPQ 0 e he
  | succ T ih =>
      intro e he
      rw [someDeletionPrefix_succ] at he ⊢
      rcases he with he | he
      · exact Or.inl (ih _ he)
      · exact Or.inr (hPQ (T + 1) e he)

/-- Prefix occurrence distributes over a disjunction of prefix events. -/
lemma someDeletionPrefix_or {n : ℕ} {H : Finset (Edge n)}
    (P Q : (t : ℕ) → DeletionHistory H t → Prop) :
    ∀ T (e : DeletionHistory H T),
      SomeDeletionPrefix (fun t e ↦ P t e ∨ Q t e) T e ↔
        SomeDeletionPrefix P T e ∨ SomeDeletionPrefix Q T e := by
  intro T
  induction T with
  | zero =>
      intro e
      rfl
  | succ T ih =>
      intro e
      rw [someDeletionPrefix_succ, someDeletionPrefix_succ,
        someDeletionPrefix_succ, ih]
      tauto

/-- The finite form of Kahn's first-failure split.  A base regularity
failure along the entire deletion path is paid once.  Only the stopped
martingale tail and the structural failure conditional on base regularity
are union-bounded over all levels. -/
lemma finsetProbability_some_bootstrapBad_le_base_add_sum {n : ℕ}
    (H : Finset (Edge n)) (C u : ℝ)
    (Base Structural : (t : ℕ) → DeletionHistory H t → Prop)
    (T : ℕ) (hT : T ≤ H.card) :
    finsetProbability (Finset.univ : Finset (DeletionHistory H T))
        (SomeDeletionPrefix
          (DeletionBootstrapBad C u
            (fun t e ↦ Base t e ∧ Structural t e)) T) ≤
      finsetProbability (Finset.univ : Finset (DeletionHistory H T))
        (SomeDeletionPrefix (fun t e ↦ ¬ Base t e) T) +
      ∑ t ∈ Finset.range (T + 1),
        (finsetProbability (Finset.univ : Finset (DeletionHistory H t))
            (fun e ↦ u < stoppedCenteredSum C t e) +
          finsetProbability (Finset.univ : Finset (DeletionHistory H t))
            (fun e ↦ Base t e ∧ ¬ Structural t e)) := by
  let BaseBad : (t : ℕ) → DeletionHistory H t → Prop :=
    fun t e ↦ ¬ Base t e
  let LevelBad : (t : ℕ) → DeletionHistory H t → Prop :=
    fun t e ↦ u < stoppedCenteredSum C t e ∨
      (Base t e ∧ ¬ Structural t e)
  have hcontain : ∀ e : DeletionHistory H T,
      SomeDeletionPrefix
          (DeletionBootstrapBad C u
            (fun t e ↦ Base t e ∧ Structural t e)) T e →
        SomeDeletionPrefix BaseBad T e ∨
          SomeDeletionPrefix LevelBad T e := by
    intro e he
    rw [← someDeletionPrefix_or BaseBad LevelBad T e]
    apply someDeletionPrefix_mono (T := T) (e := e) (P :=
      DeletionBootstrapBad C u
        (fun t e ↦ Base t e ∧ Structural t e)) (Q :=
      fun t e ↦ BaseBad t e ∨ LevelBad t e) ?_ he
    intro t z hz
    change u < stoppedCenteredSum C t z ∨
      ¬ (Base t z ∧ Structural t z) at hz
    change (¬ Base t z) ∨
      (u < stoppedCenteredSum C t z ∨
        (Base t z ∧ ¬ Structural t z))
    tauto
  calc
    finsetProbability (Finset.univ : Finset (DeletionHistory H T))
        (SomeDeletionPrefix
          (DeletionBootstrapBad C u
            (fun t e ↦ Base t e ∧ Structural t e)) T) ≤
      finsetProbability (Finset.univ : Finset (DeletionHistory H T))
        (fun e ↦ SomeDeletionPrefix BaseBad T e ∨
          SomeDeletionPrefix LevelBad T e) := by
            apply finsetProbability_mono_event
            intro e _ he
            exact hcontain e he
    _ ≤ finsetProbability (Finset.univ : Finset (DeletionHistory H T))
          (SomeDeletionPrefix BaseBad T) +
        finsetProbability (Finset.univ : Finset (DeletionHistory H T))
          (SomeDeletionPrefix LevelBad T) :=
      finsetProbability_or_le_add _ _ _
    _ ≤ finsetProbability (Finset.univ : Finset (DeletionHistory H T))
          (SomeDeletionPrefix BaseBad T) +
        ∑ t ∈ Finset.range (T + 1),
          finsetProbability (Finset.univ : Finset (DeletionHistory H t))
            (LevelBad t) := by
      apply add_le_add le_rfl
      calc
        finsetProbability (Finset.univ : Finset (DeletionHistory H T))
            (SomeDeletionPrefix LevelBad T) =
          @finsetProbability _ Finset.univ
            (SomeDeletionPrefix LevelBad T) (Classical.decPred _) :=
              finsetProbability_decidable_irrel Finset.univ _ _ _
        _ ≤ ∑ t ∈ Finset.range (T + 1),
            @finsetProbability _ Finset.univ (LevelBad t)
              (Classical.decPred _) :=
          finsetProbability_someDeletionPrefix_le_sum H LevelBad T hT
        _ = ∑ t ∈ Finset.range (T + 1),
            finsetProbability
              (Finset.univ : Finset (DeletionHistory H t))
              (LevelBad t) := by
          apply Finset.sum_congr rfl
          intro t ht
          exact finsetProbability_decidable_irrel Finset.univ _ _ _
    _ ≤ finsetProbability (Finset.univ : Finset (DeletionHistory H T))
          (SomeDeletionPrefix (fun t e ↦ ¬ Base t e) T) +
        ∑ t ∈ Finset.range (T + 1),
          (finsetProbability (Finset.univ : Finset (DeletionHistory H t))
              (fun e ↦ u < stoppedCenteredSum C t e) +
            finsetProbability (Finset.univ : Finset (DeletionHistory H t))
              (fun e ↦ Base t e ∧ ¬ Structural t e)) := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro t ht
      exact finsetProbability_or_le_add
        (Finset.univ : Finset (DeletionHistory H t)) _ _

/-- A uniform bound for the stopped-martingale tail plus the structural
failure at every deletion prefix closes the first-failure argument.  The
factor `T + 1` is the exact number of exposed prefix levels. -/
lemma pmProbability_tendsto_one_of_uniform_bootstrap_level_bound
    (M : ℕ → ℕ) (C u B : ℕ → ℝ)
    (R : (n t : ℕ) → DeletionHistory (allEdges n) t → Prop)
    (hM : ∀ n, M n ≤ (allEdges n).card)
    (hpromote : ∀ n t (e : DeletionHistory (allEdges n) t),
      DeletionHistoryGood (C n) t e →
        stoppedCenteredSum (C n) t e ≤ u n →
          R n t e → DeletionStepGood (C n) e)
    (hB0 : ∀ n, 0 ≤ B n)
    (hlevel : ∀ n t,
      t ≤ (allEdges n).card - M n →
        finsetProbability
            (Finset.univ : Finset (DeletionHistory (allEdges n) t))
            (fun e ↦ u n < stoppedCenteredSum (C n) t e) +
          finsetProbability
            (Finset.univ : Finset (DeletionHistory (allEdges n) t))
            (fun e ↦ ¬ R n t e) ≤ B n)
    (hvanish : Tendsto
      (fun n ↦ ((((allEdges n).card - M n + 1 : ℕ) : ℝ) * B n))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ pmProbability n (M n)) atTop (𝓝 1) := by
  apply pmProbability_tendsto_one_of_bootstrapBad M C u R hM hpromote
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      finsetProbability_nonneg _ _
  · apply Eventually.of_forall
    intro n
    let T := (allEdges n).card - M n
    have hprefix := finsetProbability_some_bootstrapBad_le_sum
      (allEdges n) (C n) (u n) (R n) T (Nat.sub_le _ _)
    calc
      finsetProbability
          (Finset.univ : Finset (DeletionHistory (allEdges n) T))
          (SomeDeletionPrefix
            (DeletionBootstrapBad (C n) (u n) (R n)) T) ≤
        ∑ t ∈ Finset.range (T + 1),
          (finsetProbability
              (Finset.univ : Finset (DeletionHistory (allEdges n) t))
              (fun e ↦ u n < stoppedCenteredSum (C n) t e) +
            finsetProbability
              (Finset.univ : Finset (DeletionHistory (allEdges n) t))
              (fun e ↦ ¬ R n t e)) := hprefix
      _ ≤ ∑ _t ∈ Finset.range (T + 1), B n := by
        apply Finset.sum_le_sum
        intro t ht
        apply hlevel n t
        have ht' := Finset.mem_range.mp ht
        dsimp only [T] at ht' ⊢
        omega
      _ = (((T + 1 : ℕ) : ℝ) * B n) := by simp
      _ = ((((allEdges n).card - M n + 1 : ℕ) : ℝ) * B n) := by
        rfl
  · exact hvanish

/-- Eventual form of the uniform layer closure.  This is the version used
for asymptotic parameter choices, since the numerical Kahn inequalities are
only required once `n` is sufficiently large. -/
lemma pmProbability_tendsto_one_of_eventually_uniform_bootstrap_level_bound
    (M : ℕ → ℕ) (C u B : ℕ → ℝ)
    (R : (n t : ℕ) → DeletionHistory (allEdges n) t → Prop)
    (hvalid : ∀ᶠ n in atTop,
      M n ≤ (allEdges n).card ∧
      (∀ t (e : DeletionHistory (allEdges n) t),
        DeletionHistoryGood (C n) t e →
          stoppedCenteredSum (C n) t e ≤ u n →
            R n t e → DeletionStepGood (C n) e) ∧
      (∀ t, t ≤ (allEdges n).card - M n →
        finsetProbability
            (Finset.univ : Finset (DeletionHistory (allEdges n) t))
            (fun e ↦ u n < stoppedCenteredSum (C n) t e) +
          finsetProbability
            (Finset.univ : Finset (DeletionHistory (allEdges n) t))
            (fun e ↦ ¬ R n t e) ≤ B n))
    (hvanish : Tendsto
      (fun n ↦ ((((allEdges n).card - M n + 1 : ℕ) : ℝ) * B n))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ pmProbability n (M n)) atTop (𝓝 1) := by
  have hfail : Tendsto (fun n ↦ 1 - pmProbability n (M n))
      atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ sub_nonneg.mpr
        (pmProbability_le_one n (M n))
    · filter_upwards [hvalid] with n hn
      rcases hn with ⟨hM, hpromote, hlevel⟩
      let T := (allEdges n).card - M n
      have hone := one_sub_pmProbability_le_some_bootstrapBad
        hM (C n) (u n) (R n) hpromote
      have hprefix := finsetProbability_some_bootstrapBad_le_sum
        (allEdges n) (C n) (u n) (R n) T (Nat.sub_le _ _)
      calc
        1 - pmProbability n (M n) ≤
          finsetProbability
            (Finset.univ : Finset (DeletionHistory (allEdges n) T))
            (SomeDeletionPrefix
              (DeletionBootstrapBad (C n) (u n) (R n)) T) := hone
        _ ≤ ∑ t ∈ Finset.range (T + 1),
            (finsetProbability
                (Finset.univ : Finset (DeletionHistory (allEdges n) t))
                (fun e ↦ u n < stoppedCenteredSum (C n) t e) +
              finsetProbability
                (Finset.univ : Finset (DeletionHistory (allEdges n) t))
                (fun e ↦ ¬ R n t e)) := hprefix
        _ ≤ ∑ _t ∈ Finset.range (T + 1), B n := by
          apply Finset.sum_le_sum
          intro t ht
          apply hlevel t
          have ht' := Finset.mem_range.mp ht
          dsimp only [T] at ht' ⊢
          omega
        _ = ((((allEdges n).card - M n + 1 : ℕ) : ℝ) * B n) := by
          dsimp only [T]
          simp
    · exact hvanish
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hsub := hone.sub hfail
  simpa only [sub_sub_cancel, sub_zero] using hsub

/-- Eventual split closure matching Kahn's actual first-failure argument.
The pathwise base event has its own vanishing bound; only the martingale
tail and the structural failure conditional on that base are multiplied by
the number of deletion levels. -/
lemma pmProbability_tendsto_one_of_eventually_split_bootstrap_level_bound
    (M : ℕ → ℕ) (C u B : ℕ → ℝ)
    (Base Structural :
      (n t : ℕ) → DeletionHistory (allEdges n) t → Prop)
    (hvalid : ∀ᶠ n in atTop,
      M n ≤ (allEdges n).card ∧
      (∀ t (e : DeletionHistory (allEdges n) t),
        DeletionHistoryGood (C n) t e →
          stoppedCenteredSum (C n) t e ≤ u n →
            Base n t e → Structural n t e →
              DeletionStepGood (C n) e) ∧
      (∀ t, t ≤ (allEdges n).card - M n →
        finsetProbability
            (Finset.univ : Finset (DeletionHistory (allEdges n) t))
            (fun e ↦ u n < stoppedCenteredSum (C n) t e) +
          finsetProbability
            (Finset.univ : Finset (DeletionHistory (allEdges n) t))
            (fun e ↦ Base n t e ∧ ¬ Structural n t e) ≤ B n))
    (hbase : Tendsto
      (fun n ↦
        finsetProbability
          (Finset.univ : Finset (DeletionHistory (allEdges n)
            ((allEdges n).card - M n)))
          (SomeDeletionPrefix (fun t e ↦ ¬ Base n t e)
            ((allEdges n).card - M n))) atTop (𝓝 0))
    (hvanish : Tendsto
      (fun n ↦ ((((allEdges n).card - M n + 1 : ℕ) : ℝ) * B n))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ pmProbability n (M n)) atTop (𝓝 1) := by
  have hupper : Tendsto
      (fun n ↦
        finsetProbability
          (Finset.univ : Finset (DeletionHistory (allEdges n)
            ((allEdges n).card - M n)))
          (SomeDeletionPrefix (fun t e ↦ ¬ Base n t e)
            ((allEdges n).card - M n)) +
        ((((allEdges n).card - M n + 1 : ℕ) : ℝ) * B n))
      atTop (𝓝 0) := by
    simpa only [zero_add] using hbase.add hvanish
  have hfail : Tendsto (fun n ↦ 1 - pmProbability n (M n))
      atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ sub_nonneg.mpr
        (pmProbability_le_one n (M n))
    · filter_upwards [hvalid] with n hn
      rcases hn with ⟨hM, hpromote, hlevel⟩
      let T := (allEdges n).card - M n
      let R : (t : ℕ) → DeletionHistory (allEdges n) t → Prop :=
        fun t e ↦ Base n t e ∧ Structural n t e
      have hone := one_sub_pmProbability_le_some_bootstrapBad
        hM (C n) (u n) R (fun t e hgood hstop hR ↦
          hpromote t e hgood hstop hR.1 hR.2)
      have hsplit :=
        finsetProbability_some_bootstrapBad_le_base_add_sum
          (allEdges n) (C n) (u n) (Base n) (Structural n)
          T (Nat.sub_le _ _)
      calc
        1 - pmProbability n (M n) ≤
          finsetProbability
            (Finset.univ : Finset (DeletionHistory (allEdges n) T))
            (SomeDeletionPrefix (DeletionBootstrapBad (C n) (u n) R)
              T) := by simpa only [T, R] using hone
        _ ≤ finsetProbability
              (Finset.univ : Finset (DeletionHistory (allEdges n) T))
              (SomeDeletionPrefix (fun t e ↦ ¬ Base n t e) T) +
            ∑ t ∈ Finset.range (T + 1),
              (finsetProbability
                  (Finset.univ : Finset
                    (DeletionHistory (allEdges n) t))
                  (fun e ↦ u n < stoppedCenteredSum (C n) t e) +
                finsetProbability
                  (Finset.univ : Finset
                    (DeletionHistory (allEdges n) t))
                  (fun e ↦ Base n t e ∧ ¬ Structural n t e)) := hsplit
        _ ≤ finsetProbability
              (Finset.univ : Finset (DeletionHistory (allEdges n) T))
              (SomeDeletionPrefix (fun t e ↦ ¬ Base n t e) T) +
            ∑ _t ∈ Finset.range (T + 1), B n := by
          apply add_le_add le_rfl
          apply Finset.sum_le_sum
          intro t ht
          apply hlevel t
          have ht' := Finset.mem_range.mp ht
          dsimp only [T] at ht' ⊢
          omega
        _ = finsetProbability
              (Finset.univ : Finset (DeletionHistory (allEdges n)
                ((allEdges n).card - M n)))
              (SomeDeletionPrefix (fun t e ↦ ¬ Base n t e)
                ((allEdges n).card - M n)) +
            ((((allEdges n).card - M n + 1 : ℕ) : ℝ) * B n) := by
          dsimp only [T]
          simp
    · exact hupper
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hsub := hone.sub hfail
  simpa only [sub_sub_cancel, sub_zero] using hsub

end

end Erdos747
