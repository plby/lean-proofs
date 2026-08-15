/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
/-!
# Diagonal nested-box recursion for Erdős Problem 266

This file isolates the choice, diagonalization, convergence, and finite-block
reindexing steps of the Kovač--Tao construction.  The finite-dimensional block
lemma and scale estimates are supplied through `Scheme.refine`.
-/

namespace Erdos266Diagonal

noncomputable section

open Filter Finset Topology

/-- Abstract input to the diagonal nested-box construction.  The active
dimension may stay fixed for many stages, but grows by at most one per stage
and eventually activates every coordinate. -/
structure Scheme (β : Type*) where
  dim : ℕ → ℕ
  dim_zero : dim 0 = 0
  dim_mono : Monotone dim
  dim_step : ∀ k, dim (k + 1) ≤ dim k + 1
  dim_unbounded : ∀ i, ∃ k, i < dim k
  refBlock : ℕ → ℕ → ℝ
  actualBlock : ℕ → β → ℕ → ℝ
  admissible : ℕ → β → Prop
  radius : ℕ → ℕ → ℝ
  tail : ℕ → ℕ → ℝ
  radius_pos : ∀ i k, 0 < radius i k
  tail_succ : ∀ i k, tail i k = refBlock i k + tail i (k + 1)
  refine : ∀ k (error : Fin (dim k) → ℝ),
    (∀ i, |error i| ≤ radius i k) →
      ∃ b : β, admissible k b ∧ ∀ i,
        |error i + refBlock i k - actualBlock k b i| ≤ radius i (k + 1)

namespace Scheme

variable {β : Type*} (S : Scheme β)

/-- The first-`k` actual blocks plus the reference tail beginning at `k`. -/
def approximation (choice : ℕ → β) (i k : ℕ) : ℝ :=
  (∑ l ∈ range k, S.actualBlock l (choice l) i) + S.tail i k

/-- A finite-stage state.  Total functions are used for the data, while the
proof fields record only the already active/used parts. -/
structure State (k : ℕ) where
  target : ℕ → ℚ
  choice : ℕ → β
  invariant : ∀ i, i < S.dim k →
    |(target i : ℝ) - S.approximation choice i k| ≤ S.radius i k
  choice_admissible : ∀ l, l < k → S.admissible l (choice l)

/-- A successor preserves all targets already active and all block choices
already used. -/
def Extends {k : ℕ} (s : S.State k) (s' : S.State (k + 1)) : Prop :=
  (∀ i, i < S.dim k → s'.target i = s.target i) ∧
  (∀ l, l < k → s'.choice l = s.choice l)

private lemma exists_rat_abs_sub_lt (x ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℚ, |(q : ℝ) - x| < ε := by
  have hinterval : x - ε < x + ε := by linarith
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hinterval
  refine ⟨q, (abs_lt).2 ⟨?_, ?_⟩⟩ <;> linarith

/-- One successor step: refine every currently active coordinate with one
admissible block, then rationally initialize the at-most-one coordinate newly
visible in the output state. -/
theorem exists_next {k : ℕ} (s : S.State k) :
    ∃ s' : S.State (k + 1), S.Extends s s' := by
  let center : ℕ → ℝ := fun i ↦ S.approximation s.choice i k
  let error : Fin (S.dim k) → ℝ := fun i ↦ (s.target i : ℝ) - center i
  have herror : ∀ i, |error i| ≤ S.radius i k := by
    intro i
    simpa [error, center] using s.invariant i i.isLt
  obtain ⟨b, hbadm, hb⟩ := S.refine k error herror
  let choice' : ℕ → β := Function.update s.choice k b
  have hchoice_lt : ∀ l ∈ range k, choice' l = s.choice l := by
    intro l hl
    exact Function.update_of_ne (Nat.ne_of_lt (mem_range.1 hl)) b s.choice
  have hsum (i : ℕ) :
      (∑ l ∈ range k, S.actualBlock l (choice' l) i) =
        ∑ l ∈ range k, S.actualBlock l (s.choice l) i := by
    apply sum_congr rfl
    intro l hl
    rw [hchoice_lt l hl]
  have hchoice_k : choice' k = b := Function.update_self k b s.choice
  have hold : ∀ i, i < S.dim k →
      |(s.target i : ℝ) - S.approximation choice' i (k + 1)| ≤ S.radius i (k + 1) := by
    intro i hi
    have hblock := hb ⟨i, hi⟩
    rw [approximation, sum_range_succ, hsum, hchoice_k]
    change |((s.target i : ℝ) - center i) + S.refBlock i k - S.actualBlock k b i| ≤
      S.radius i (k + 1) at hblock
    dsimp [center] at hblock
    rw [approximation, S.tail_succ i k] at hblock
    convert hblock using 1
    abel_nf
  let newCenter : ℝ := S.approximation choice' (S.dim k) (k + 1)
  obtain ⟨q : ℚ, hq⟩ :=
    exists_rat_abs_sub_lt newCenter (S.radius (S.dim k) (k + 1))
      (S.radius_pos (S.dim k) (k + 1))
  let target' : ℕ → ℚ := Function.update s.target (S.dim k) q
  have hinvariant : ∀ i, i < S.dim (k + 1) →
      |(target' i : ℝ) - S.approximation choice' i (k + 1)| ≤ S.radius i (k + 1) := by
    intro i hi
    by_cases hiold : i < S.dim k
    · have hne : i ≠ S.dim k := Nat.ne_of_lt hiold
      simpa [target', Function.update_of_ne hne] using hold i hiold
    · have hieq : i = S.dim k := by
        have hstep := S.dim_step k
        omega
      subst i
      simpa [target', newCenter] using hq.le
  have hadmissible : ∀ l, l < k + 1 → S.admissible l (choice' l) := by
    intro l hl
    by_cases h : l = k
    · subst l
      simpa [choice'] using hbadm
    · have hlk : l < k := by omega
      simpa [choice', Function.update_of_ne h] using s.choice_admissible l hlk
  let s' : S.State (k + 1) := ⟨target', choice', hinvariant, hadmissible⟩
  refine ⟨s', ?_, ?_⟩
  · intro i hi
    exact Function.update_of_ne (Nat.ne_of_lt hi) q s.target
  · intro l hl
    exact Function.update_of_ne (Nat.ne_of_lt hl) b s.choice

/-- A default block choice, obtained from the stage-zero refinement theorem.
It is used only to fill as-yet unused entries of the total choice function. -/
def arbitraryChoice : β :=
  Classical.choose
    (S.refine 0
      (fun i ↦ Fin.elim0 (Fin.cast S.dim_zero i))
      (fun i ↦ Fin.elim0 (Fin.cast S.dim_zero i)))

/-- The stage-zero invariant and admissibility conditions are vacuous. -/
def initialState : S.State 0 where
  target := 0
  choice := fun _ ↦ S.arbitraryChoice
  invariant := by simp [S.dim_zero]
  choice_admissible := by simp

/-- A classically chosen successor state. -/
def nextState {k : ℕ} (s : S.State k) : S.State (k + 1) :=
  Classical.choose (S.exists_next s)

lemma nextState_extends {k : ℕ} (s : S.State k) : S.Extends s (S.nextState s) :=
  Classical.choose_spec (S.exists_next s)

/-- The recursively chosen finite-stage states. -/
def states : (k : ℕ) → S.State k
  | 0 => S.initialState
  | k + 1 => nextState S (states k)

lemma states_succ_extends (k : ℕ) :
    S.Extends (S.states k) (S.states (k + 1)) := by
  change S.Extends (S.states k) (S.nextState (S.states k))
  exact S.nextState_extends (S.states k)

/-- The first stage at which coordinate `i` is active. -/
def activationStage (i : ℕ) : ℕ := Nat.find (S.dim_unbounded i)

lemma lt_dim_activationStage (i : ℕ) : i < S.dim (S.activationStage i) :=
  Nat.find_spec (S.dim_unbounded i)

lemma activationStage_le_of_lt_dim {i k : ℕ} (hik : i < S.dim k) :
    S.activationStage i ≤ k :=
  Nat.find_min' (S.dim_unbounded i) hik

/-- The rational target permanently assigned to coordinate `i`. -/
def target (i : ℕ) : ℚ := (S.states (S.activationStage i)).target i

/-- The permanent actual-block choice at stage `k`. -/
def choice (k : ℕ) : β := (S.states (k + 1)).choice k

lemma states_target_eq_target {i k : ℕ} (hik : i < S.dim k) :
    (S.states k).target i = S.target i := by
  induction k with
  | zero => simp [S.dim_zero] at hik
  | succ k ih =>
      have ha : S.activationStage i ≤ k + 1 := S.activationStage_le_of_lt_dim hik
      by_cases heq : S.activationStage i = k + 1
      · unfold target
        rw [heq]
      · have ha' : S.activationStage i ≤ k := by omega
        have hia := S.lt_dim_activationStage i
        have hiprev : i < S.dim k := lt_of_lt_of_le hia (S.dim_mono ha')
        calc
          (S.states (k + 1)).target i = (S.states k).target i :=
            (S.states_succ_extends k).1 i hiprev
          _ = S.target i := ih hiprev

lemma states_choice_eq_choice {l k : ℕ} (hlk : l < k) :
    (S.states k).choice l = S.choice l := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases h : l = k
      · subst l
        rfl
      · have hlk' : l < k := by omega
        calc
          (S.states (k + 1)).choice l = (S.states k).choice l :=
            (S.states_succ_extends k).2 l hlk'
          _ = S.choice l := ih hlk'

/-- Every globally selected block satisfies the stage-specific admissibility
condition returned by the refinement theorem. -/
theorem choice_admissible (k : ℕ) : S.admissible k (S.choice k) := by
  exact (S.states (k + 1)).choice_admissible k (by omega)

/-- The global nested-box invariant. -/
theorem invariant (i k : ℕ) (hik : i < S.dim k) :
    |(S.target i : ℝ) - S.approximation S.choice i k| ≤ S.radius i k := by
  have h := (S.states k).invariant i hik
  rw [S.states_target_eq_target hik] at h
  have hsum :
      (∑ l ∈ range k, S.actualBlock l ((S.states k).choice l) i) =
        ∑ l ∈ range k, S.actualBlock l (S.choice l) i := by
    apply sum_congr rfl
    intro l hl
    rw [S.states_choice_eq_choice (mem_range.1 hl)]
  simpa only [approximation, hsum] using h

/-- Once actual block series are summable and tails and radii tend to zero,
each coordinate sum equals its rational target. -/
theorem target_eq_tsum
    (hsummable : ∀ i, Summable (fun k ↦ S.actualBlock k (S.choice k) i))
    (htail : ∀ i, Tendsto (S.tail i) atTop (𝓝 0))
    (hradius : ∀ i, Tendsto (S.radius i) atTop (𝓝 0))
    (i : ℕ) :
    (S.target i : ℝ) = ∑' k, S.actualBlock k (S.choice k) i := by
  let blocks : ℕ → ℝ := fun k ↦ S.actualBlock k (S.choice k) i
  let approx : ℕ → ℝ := fun k ↦ (∑ l ∈ range k, blocks l) + S.tail i k
  have hpartial : Tendsto (fun k ↦ ∑ l ∈ range k, blocks l) atTop
      (𝓝 (∑' k, blocks k)) := by
    exact (hsummable i).hasSum.tendsto_sum_nat
  have happ_tsum : Tendsto approx atTop (𝓝 (∑' k, blocks k)) := by
    simpa [approx] using hpartial.add (htail i)
  have hactive : ∀ᶠ k in atTop, i < S.dim k := by
    filter_upwards [eventually_ge_atTop (S.activationStage i)] with k hk
    exact lt_of_lt_of_le (S.lt_dim_activationStage i) (S.dim_mono hk)
  have hbound : ∀ᶠ k in atTop, |(S.target i : ℝ) - approx k| ≤ S.radius i k := by
    filter_upwards [hactive] with k hk
    simpa [approx, blocks, approximation] using S.invariant i k hk
  have habs : Tendsto (fun k ↦ |(S.target i : ℝ) - approx k|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) hbound (hradius i)
  have happ_target : Tendsto approx atTop (𝓝 (S.target i : ℝ)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [Real.dist_eq, abs_sub_comm] using habs
  exact tendsto_nhds_unique happ_target happ_tsum

/-- Packaged diagonal output for the main construction. -/
theorem exists_rational_coordinate_sums
    (hsummable : ∀ i, Summable (fun k ↦ S.actualBlock k (S.choice k) i))
    (htail : ∀ i, Tendsto (S.tail i) atTop (𝓝 0))
    (hradius : ∀ i, Tendsto (S.radius i) atTop (𝓝 0)) :
    ∃ q : ℕ → ℚ, ∃ b : ℕ → β,
      (∀ k, S.admissible k (b k)) ∧
      (∀ i k, i < S.dim k →
        |(q i : ℝ) - S.approximation b i k| ≤ S.radius i k) ∧
      ∀ i, (q i : ℝ) = ∑' k, S.actualBlock k (b k) i := by
  exact ⟨S.target, S.choice, S.choice_admissible, S.invariant,
    S.target_eq_tsum hsummable htail hradius⟩

/-! ### Reindexing finite blocks -/

/-- The sigma type of positions in finite blocks of prescribed sizes. -/
def BlockIndex (size : ℕ → ℕ) := Σ k, Fin (size k)

instance (size : ℕ → ℕ) : Countable (BlockIndex size) := by
  let encode : BlockIndex size → ℕ × ℕ := fun p ↦ (p.1, p.2.val)
  have hencode : Function.Injective encode := by
    intro a b hab
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    simp only [encode, Prod.mk.injEq] at hab
    obtain ⟨rfl, hval⟩ := hab
    congr
    exact Fin.ext hval
  exact hencode.countable

/-- Pulling a series back along an enumeration of all block positions preserves
summability.  The explicit equivalence is an input so the caller may choose any
convenient enumeration. -/
theorem summable_reindex_iff (size : ℕ → ℕ) (f : BlockIndex size → ℝ)
    (e : ℕ ≃ BlockIndex size) :
    Summable (fun n ↦ f (e n)) ↔ Summable f := by
  change Summable (f ∘ e) ↔ Summable f
  exact e.summable_iff

/-- Pulling a series back along an enumeration of all block positions preserves
its sum. -/
theorem tsum_reindex_eq (size : ℕ → ℕ) (f : BlockIndex size → ℝ)
    (e : ℕ ≃ BlockIndex size) :
    (∑' n, f (e n)) = ∑' p, f p := by
  simpa only [Function.comp_apply] using e.tsum_eq f

/-- A summable series over finite block positions is the iterated sum of its
finite blocks. -/
theorem tsum_blockIndex_eq_tsum_sum (size : ℕ → ℕ) (f : BlockIndex size → ℝ)
    (hf : Summable f) :
    (∑' p, f p) = ∑' k, ∑ j : Fin (size k), f ⟨k, j⟩ := by
  calc
    (∑' p, f p) = ∑' k, ∑' j : Fin (size k), f ⟨k, j⟩ := hf.tsum_sigma
    _ = ∑' k, ∑ j : Fin (size k), f ⟨k, j⟩ := by
      apply tsum_congr
      intro k
      exact tsum_fintype _

/-- Reindexing and splitting into finite blocks in one equality. -/
theorem tsum_reindex_eq_tsum_sum (size : ℕ → ℕ) (f : BlockIndex size → ℝ)
    (e : ℕ ≃ BlockIndex size) (hf : Summable f) :
    (∑' n, f (e n)) = ∑' k, ∑ j : Fin (size k), f ⟨k, j⟩ :=
  (tsum_reindex_eq size f e).trans (tsum_blockIndex_eq_tsum_sum size f hf)

end Scheme

end

end Erdos266Diagonal
