/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteKernelConcentration

/-!
# First-passage stopping for finite kernels

A time coordinate is adjoined to a finite state.  While the state is active,
the coordinate advances and the prescribed inhomogeneous kernel is applied;
otherwise the state is frozen.  This turns a stopped trajectory variable into
an ordinary homogeneous finite-kernel process to which the exponential bound
can be applied.
-/

namespace Erdos207

open scoped BigOperators NNReal

noncomputable section

namespace FiniteLaw

/-- A process state together with a time coordinate bounded by the horizon. -/
abbrev TimedState (Ω : Type*) (n : ℕ) := Fin (n + 1) × Ω

/-- Advance a bounded time coordinate which is strictly before the horizon. -/
def advanceTime {n : ℕ} (i : Fin (n + 1)) (hi : i.1 < n) : Fin (n + 1) :=
  ⟨i.1 + 1, by omega⟩

@[simp]
theorem advanceTime_val {n : ℕ} (i : Fin (n + 1)) (hi : i.1 < n) :
    (advanceTime i hi).1 = i.1 + 1 := rfl

/-- Homogeneous kernel on timed states obtained by freezing an
inhomogeneous process outside its active region. -/
def timedStoppedKernel
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (n : ℕ)
    (K : ℕ → Ω → FiniteLaw Ω) (active : ℕ → Ω → Prop)
    (z : TimedState Ω n) : FiniteLaw (TimedState Ω n) := by
  classical
  exact if h : z.1.1 < n ∧ active z.1.1 z.2 then
    map (fun y ↦ (advanceTime z.1 h.1, y)) (K z.1.1 z.2)
  else pure z

/-- Law of the timed stopped process after the full horizon. -/
def timedStoppedProcessLaw
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (n : ℕ)
    (K : ℕ → Ω → FiniteLaw Ω) (active : ℕ → Ω → Prop) (x₀ : Ω) :
    FiniteLaw (TimedState Ω n) :=
  evolveKernels (fun _ ↦ timedStoppedKernel n K active) n
    (pure (⟨0, by omega⟩, x₀))

/-- After the full horizon, a positive-mass stopped trajectory has either
reached the horizon or is frozen at a state where the active predicate
fails.  This is the first-passage progress certificate used to turn terminal
concentration into a full-length greedy run. -/
theorem timedStoppedProcessLaw_supported_terminal
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (n : ℕ) (K : ℕ → Ω → FiniteLaw Ω)
    (active : ℕ → Ω → Prop) (x₀ : Ω) :
    (timedStoppedProcessLaw n K active x₀).SupportedOn
      (fun z ↦ z.1.1 = n ∨ ¬ active z.1.1 z.2) := by
  classical
  let z₀ : TimedState Ω n := (⟨0, by omega⟩, x₀)
  let Kt : ℕ → TimedState Ω n → FiniteLaw (TimedState Ω n) :=
    fun _ ↦ timedStoppedKernel n K active
  let Progress : ℕ → TimedState Ω n → Prop := fun k z ↦
    z.1.1 ≤ k ∧ (z.1.1 = k ∨ ¬ active z.1.1 z.2)
  have hprogress : ∀ k, k ≤ n →
      (evolveKernels Kt k (pure z₀)).SupportedOn (Progress k) := by
    intro k hk
    induction k with
    | zero =>
        exact supportedOn_pure _ ⟨by simp [z₀], Or.inl (by simp [z₀])⟩
    | succ k ih =>
        rw [evolveKernels_succ]
        refine (ih (by omega)).bind (Kt k) ?_
        intro z hz
        have hklt : k < n := by omega
        dsimp [Kt]
        unfold timedStoppedKernel
        split_ifs with hrun
        · have hztime : z.1.1 = k :=
            hz.2.resolve_right (not_not_intro hrun.2)
          have hsupport : (K z.1.1 z.2).SupportedOn (fun _ ↦ True) :=
            fun _ _ ↦ trivial
          exact hsupport.map
            (fun y ↦ (advanceTime z.1 hrun.1, y)) fun y _hy ↦ by
              refine ⟨?_, Or.inl ?_⟩
              · simp [advanceTime, hztime]
              · simp [advanceTime, hztime]
        · apply supportedOn_pure
          refine ⟨hz.1.trans (Nat.le_succ k), ?_⟩
          rcases hz.2 with hztime | hinactive
          · right
            intro hactive
            exact hrun ⟨by simpa [hztime] using hklt, hactive⟩
          · exact Or.inr hinactive
  have hfinal := hprogress n le_rfl
  intro z hmass
  rcases hfinal z hmass with ⟨_hzle, hztime | hinactive⟩
  · exact Or.inl hztime
  · exact Or.inr hinactive

/-- The base-state invariant is retained by the timed stopped process. -/
theorem timedStoppedKernel_supported
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {n : ℕ} (K : ℕ → Ω → FiniteLaw Ω)
    (active : ℕ → Ω → Prop) {P : Ω → Prop}
    (hK : ∀ i, i < n → ∀ x, P x → (K i x).SupportedOn P)
    (z : TimedState Ω n) (hz : P z.2) :
    (timedStoppedKernel n K active z).SupportedOn (fun z' ↦ P z'.2) := by
  classical
  unfold timedStoppedKernel
  split_ifs with h
  · exact (hK z.1.1 h.1 z.2 hz).map
      (fun y ↦ (advanceTime z.1 h.1, y)) fun y hy ↦ hy
  · exact supportedOn_pure _ hz

/-- A base-state invariant preserved by every active transition is present on
the whole positive-mass support of the terminal stopped law. -/
theorem timedStoppedProcessLaw_supported
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P : Ω → Prop} (n : ℕ) (K : ℕ → Ω → FiniteLaw Ω)
    (active : ℕ → Ω → Prop) (x₀ : Ω)
    (hP₀ : P x₀)
    (hK : ∀ i, i < n → ∀ x, P x → (K i x).SupportedOn P) :
    (timedStoppedProcessLaw n K active x₀).SupportedOn
      (fun z ↦ P z.2) := by
  apply (supportedOn_pure (fun z : TimedState Ω n ↦ P z.2) hP₀).evolveKernels
  · intro i z hz
    exact timedStoppedKernel_supported K active hK z hz

/-- The stopped timed process satisfies the same exponential terminal bound
as a supermartingale with conditional second moment at most `v`. -/
theorem probability_timedStoppedProcess_deviation_ge_le_exp
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P : Ω → Prop} [DecidablePred P]
    (n : ℕ) (K : ℕ → Ω → FiniteLaw Ω)
    (active : ℕ → Ω → Prop) (F : ℕ → Ω → ℝ)
    (x₀ : Ω) (theta R a v : ℝ)
    (hP₀ : P x₀) (htheta : 0 < theta) (hR : 0 ≤ R)
    (hthetaR : theta * R ≤ 1) (hv : 0 ≤ v)
    (hK : ∀ i, i < n → ∀ x, P x → (K i x).SupportedOn P)
    (hjump : ∀ i, i < n → ∀ x, P x → active i x →
      ∀ y, 0 < (K i x).mass y → P y →
        F (i + 1) y - F i x ≤ R)
    (hdrift : ∀ i, i < n → ∀ x, P x → active i x →
      (K i x).expectationReal
        (fun y ↦ F (i + 1) y - F i x) ≤ 0)
    (hsecond : ∀ i, i < n → ∀ x, P x → active i x →
      (K i x).expectationReal
        (fun y ↦ (F (i + 1) y - F i x) ^ 2) ≤ v) :
    ((timedStoppedProcessLaw n K active x₀).probability
        (fun z ↦ a ≤ F z.1.1 z.2 - F 0 x₀) : ℝ) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v) := by
  let Ωt := TimedState Ω n
  let z₀ : Ωt := (⟨0, by omega⟩, x₀)
  let Kt : ℕ → Ωt → FiniteLaw Ωt :=
    fun _ ↦ timedStoppedKernel n K active
  let Ft : ℕ → Ωt → ℝ := fun _ z ↦ F z.1.1 z.2
  let Pt : Ωt → Prop := fun z ↦ P z.2
  have hKt : ∀ i z, Pt z → (Kt i z).SupportedOn Pt := by
    intro i z hz
    exact timedStoppedKernel_supported K active hK z hz
  have hjumpKt : ∀ i, i < n → ∀ z, Pt z → ∀ z',
      0 < (Kt i z).mass z' → Ft (i + 1) z' - Ft i z ≤ R := by
    intro i _hi z hz z' hz'mass
    classical
    dsimp [Kt] at hz'mass
    unfold timedStoppedKernel at hz'mass
    split at hz'mass <;> rename_i hactive
    · have hsupp : (map (fun y ↦ (advanceTime z.1 hactive.1, y))
          (K z.1.1 z.2)).SupportedOn
          (fun w ↦ w.1 = advanceTime z.1 hactive.1 ∧ P w.2) :=
        (hK z.1.1 hactive.1 z.2 hz).map
          (fun y ↦ (advanceTime z.1 hactive.1, y))
          (fun y hy ↦ ⟨rfl, hy⟩)
      have hz' := hsupp z' hz'mass
      have hz'baseMass : 0 < (K z.1.1 z.2).mass z'.2 := by
        change 0 < ∑ y, if
          (advanceTime z.1 hactive.1, y) = z' then
            (K z.1.1 z.2).mass y else 0 at hz'mass
        obtain ⟨y, _hyuniv, hy⟩ := Finset.sum_pos_iff.mp hz'mass
        by_cases heq : (advanceTime z.1 hactive.1, y) = z'
        · have hyval : y = z'.2 := congrArg Prod.snd heq
          subst y
          simpa [heq] using hy
        · simp [heq] at hy
      change F z'.1.1 z'.2 - F z.1.1 z.2 ≤ R
      rw [hz'.1]
      simp only [advanceTime_val]
      exact hjump z.1.1 hactive.1 z.2 hz hactive.2 z'.2
        hz'baseMass hz'.2
    · have hz'eq : z' = z := by
        have hs := supportedOn_pure (fun w : Ωt ↦ w = z) rfl
        exact hs z' hz'mass
      subst z'
      simp [Ft, hR]
  have hdriftKt : ∀ i, i < n → ∀ z, Pt z →
      (Kt i z).expectationReal (fun z' ↦ Ft (i + 1) z' - Ft i z) ≤ 0 := by
    intro i _hi z hz
    classical
    dsimp [Kt]
    unfold timedStoppedKernel
    split_ifs with hactive
    · rw [expectationReal_map]
      simpa [Ft] using hdrift z.1.1 hactive.1 z.2 hz hactive.2
    · simp [Ft]
  have hsecondKt : ∀ i, i < n → ∀ z, Pt z →
      (Kt i z).expectationReal
        (fun z' ↦ (Ft (i + 1) z' - Ft i z) ^ 2) ≤ v := by
    intro i _hi z hz
    classical
    dsimp [Kt]
    unfold timedStoppedKernel
    split_ifs with hactive
    · rw [expectationReal_map]
      simpa [Ft] using hsecond z.1.1 hactive.1 z.2 hz hactive.2
    · simpa [Ft] using hv
  have htail := probability_evolveKernels_deviation_ge_le_exp
    Kt Ft z₀ theta R a (fun _ ↦ v) n
    hP₀ htheta hR hthetaR hKt hjumpKt hdriftKt hsecondKt
  have hsum : ∑ _i ∈ Finset.range n, v = (n : ℝ) * v := by simp
  simpa [timedStoppedProcessLaw, Kt, Ft, Pt, z₀, hsum,
    mul_assoc] using htail

/-- Survival-weighted stopped-process bound.  The predicate `alive` is
monotone under the base kernels, and dead terminal states contribute no mass
to the deviation event. -/
theorem probability_timedStoppedProcess_alive_deviation_ge_le_exp
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P alive : Ω → Prop} [DecidablePred P] [DecidablePred alive]
    (n : ℕ) (K : ℕ → Ω → FiniteLaw Ω)
    (active : ℕ → Ω → Prop) (F : ℕ → Ω → ℝ)
    (x₀ : Ω) (theta R a v : ℝ)
    (hP₀ : P x₀) (halive₀ : alive x₀)
    (htheta : 0 < theta) (hR : 0 ≤ R)
    (hthetaR : theta * R ≤ 1) (hv : 0 ≤ v)
    (hK : ∀ i, i < n → ∀ x, P x → (K i x).SupportedOn P)
    (hdead : ∀ i, i < n → ∀ x, P x → ¬ alive x →
      (K i x).SupportedOn (fun y ↦ ¬ alive y))
    (hjump : ∀ i, i < n → ∀ x, P x → active i x → alive x →
      ∀ y, 0 < (K i x).mass y → P y → alive y →
        F (i + 1) y - F i x ≤ R)
    (hdrift : ∀ i, i < n → ∀ x, P x → active i x → alive x →
      (K i x).expectationReal (fun y ↦
        if alive y then F (i + 1) y - F i x else 0) ≤ 0)
    (hsecond : ∀ i, i < n → ∀ x, P x → active i x → alive x →
      (K i x).expectationReal (fun y ↦
        if alive y then (F (i + 1) y - F i x) ^ 2 else 0) ≤ v) :
    ((timedStoppedProcessLaw n K active x₀).probability
      (fun z ↦ alive z.2 ∧ a ≤ F z.1.1 z.2 - F 0 x₀) : ℝ) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v) := by
  classical
  let Ωt := TimedState Ω n
  let z₀ : Ωt := (⟨0, by omega⟩, x₀)
  let Kt : ℕ → Ωt → FiniteLaw Ωt :=
    fun _ ↦ timedStoppedKernel n K active
  let Ft : ℕ → Ωt → ℝ := fun _ z ↦ F z.1.1 z.2
  let Pt : Ωt → Prop := fun z ↦ P z.2
  let aliveT : Ωt → Prop := fun z ↦ alive z.2
  have hKt : ∀ i z, Pt z → (Kt i z).SupportedOn Pt := by
    intro i z hz
    exact timedStoppedKernel_supported K active hK z hz
  have hdeadKt : ∀ i z, Pt z → ¬ aliveT z →
      (Kt i z).SupportedOn (fun z' ↦ ¬ aliveT z') := by
    intro i z hz hzdead
    dsimp [Kt]
    unfold timedStoppedKernel
    split_ifs with hactive
    · exact (hdead z.1.1 hactive.1 z.2 hz hzdead).map
        (fun y ↦ (advanceTime z.1 hactive.1, y)) (fun _ hy ↦ hy)
    · exact supportedOn_pure _ hzdead
  have hjumpKt : ∀ i, i < n → ∀ z, Pt z → aliveT z → ∀ z',
      0 < (Kt i z).mass z' → aliveT z' →
        Ft (i + 1) z' - Ft i z ≤ R := by
    intro i _hi z hz hzAlive z' hz'mass hz'Alive
    dsimp [Kt] at hz'mass
    unfold timedStoppedKernel at hz'mass
    split at hz'mass <;> rename_i hactive
    · have hsupp : (map (fun y ↦ (advanceTime z.1 hactive.1, y))
          (K z.1.1 z.2)).SupportedOn
          (fun w ↦ w.1 = advanceTime z.1 hactive.1 ∧ P w.2) :=
        (hK z.1.1 hactive.1 z.2 hz).map
          (fun y ↦ (advanceTime z.1 hactive.1, y))
          (fun _ hy ↦ ⟨rfl, hy⟩)
      have hz' := hsupp z' hz'mass
      have hz'baseMass : 0 < (K z.1.1 z.2).mass z'.2 := by
        change 0 < ∑ y, if
          (advanceTime z.1 hactive.1, y) = z' then
            (K z.1.1 z.2).mass y else 0 at hz'mass
        obtain ⟨y, _hyuniv, hy⟩ := Finset.sum_pos_iff.mp hz'mass
        by_cases heq : (advanceTime z.1 hactive.1, y) = z'
        · have hyval : y = z'.2 := congrArg Prod.snd heq
          subst y
          simpa [heq] using hy
        · simp [heq] at hy
      change F z'.1.1 z'.2 - F z.1.1 z.2 ≤ R
      rw [hz'.1]
      simp only [advanceTime_val]
      exact hjump z.1.1 hactive.1 z.2 hz hactive.2 hzAlive z'.2
        hz'baseMass hz'.2 hz'Alive
    · have hz'eq : z' = z := by
        exact (supportedOn_pure (fun w : Ωt ↦ w = z) rfl) z' hz'mass
      subst z'
      simp [Ft, hR]
  have hdriftKt : ∀ i, i < n → ∀ z, Pt z → aliveT z →
      (Kt i z).expectationReal (fun z' ↦
        if aliveT z' then Ft (i + 1) z' - Ft i z else 0) ≤ 0 := by
    intro i _hi z hz hzAlive
    dsimp [Kt]
    unfold timedStoppedKernel
    split_ifs with hactive
    · rw [expectationReal_map]
      simpa [Ft, aliveT] using
        hdrift z.1.1 hactive.1 z.2 hz hactive.2 hzAlive
    · simp [Ft, aliveT, hzAlive]
  have hsecondKt : ∀ i, i < n → ∀ z, Pt z → aliveT z →
      (Kt i z).expectationReal (fun z' ↦
        if aliveT z' then (Ft (i + 1) z' - Ft i z) ^ 2 else 0) ≤ v := by
    intro i _hi z hz hzAlive
    dsimp [Kt]
    unfold timedStoppedKernel
    split_ifs with hactive
    · rw [expectationReal_map]
      simpa [Ft, aliveT] using
        hsecond z.1.1 hactive.1 z.2 hz hactive.2 hzAlive
    · simpa [Ft, aliveT, hzAlive] using hv
  have htail := probability_evolveKernels_alive_deviation_ge_le_exp
    aliveT (P := Pt) Kt Ft z₀ theta R a (fun _ ↦ v) n
    hP₀ halive₀ htheta hthetaR hKt hdeadKt hjumpKt hdriftKt hsecondKt
  have hsum : ∑ _i ∈ Finset.range n, v = (n : ℝ) * v := by simp
  simpa [timedStoppedProcessLaw, Kt, Ft, Pt, aliveT, z₀, hsum,
    mul_assoc] using htail

/-- Survival-weighted stopped-process bound in which the full increment is
used at an alive source state, including transitions that leave the alive
region.  The latter paths are discarded only in the terminal exponential
iteration. -/
theorem probability_timedStoppedProcess_alive_deviation_ge_le_exp_fullIncrement
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P alive : Ω → Prop} [DecidablePred P] [DecidablePred alive]
    (n : ℕ) (K : ℕ → Ω → FiniteLaw Ω)
    (active : ℕ → Ω → Prop) (F : ℕ → Ω → ℝ)
    (x₀ : Ω) (theta R a v : ℝ)
    (hP₀ : P x₀) (halive₀ : alive x₀)
    (htheta : 0 < theta) (hR : 0 ≤ R)
    (hthetaR : theta * R ≤ 1) (hv : 0 ≤ v)
    (hK : ∀ i, i < n → ∀ x, P x → active i x →
      (K i x).SupportedOn P)
    (hdead : ∀ i, i < n → ∀ x, P x → active i x → ¬ alive x →
      (K i x).SupportedOn (fun y ↦ ¬ alive y))
    (hjump : ∀ i, i < n → ∀ x, P x → active i x → alive x →
      ∀ y, 0 < (K i x).mass y → P y →
        F (i + 1) y - F i x ≤ R)
    (hdrift : ∀ i, i < n → ∀ x, P x → active i x → alive x →
      (K i x).expectationReal
        (fun y ↦ F (i + 1) y - F i x) ≤ 0)
    (hsecond : ∀ i, i < n → ∀ x, P x → active i x → alive x →
      (K i x).expectationReal
        (fun y ↦ (F (i + 1) y - F i x) ^ 2) ≤ v) :
    ((timedStoppedProcessLaw n K active x₀).probability
      (fun z ↦ alive z.2 ∧ a ≤ F z.1.1 z.2 - F 0 x₀) : ℝ) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v) := by
  classical
  let Ωt := TimedState Ω n
  let z₀ : Ωt := (⟨0, by omega⟩, x₀)
  let Kt : ℕ → Ωt → FiniteLaw Ωt :=
    fun _ ↦ timedStoppedKernel n K active
  let Ft : ℕ → Ωt → ℝ := fun _ z ↦ F z.1.1 z.2
  let Pt : Ωt → Prop := fun z ↦ P z.2
  let aliveT : Ωt → Prop := fun z ↦ alive z.2
  have hKt : ∀ i z, Pt z → (Kt i z).SupportedOn Pt := by
    intro i z hz
    dsimp [Kt]
    unfold timedStoppedKernel
    split_ifs with hactive
    · exact (hK z.1.1 hactive.1 z.2 hz hactive.2).map
        (fun y ↦ (advanceTime z.1 hactive.1, y)) (fun _ hy ↦ hy)
    · exact supportedOn_pure _ hz
  have hdeadKt : ∀ i z, Pt z → ¬ aliveT z →
      (Kt i z).SupportedOn (fun z' ↦ ¬ aliveT z') := by
    intro i z hz hzdead
    dsimp [Kt]
    unfold timedStoppedKernel
    split_ifs with hactive
    · exact (hdead z.1.1 hactive.1 z.2 hz hactive.2 hzdead).map
        (fun y ↦ (advanceTime z.1 hactive.1, y)) (fun _ hy ↦ hy)
    · exact supportedOn_pure _ hzdead
  have hjumpKt : ∀ i, i < n → ∀ z, Pt z → aliveT z → ∀ z',
      0 < (Kt i z).mass z' → Ft (i + 1) z' - Ft i z ≤ R := by
    intro i _hi z hz hzAlive z' hz'mass
    dsimp [Kt] at hz'mass
    unfold timedStoppedKernel at hz'mass
    split at hz'mass <;> rename_i hactive
    · have hsupp : (map (fun y ↦ (advanceTime z.1 hactive.1, y))
          (K z.1.1 z.2)).SupportedOn
          (fun w ↦ w.1 = advanceTime z.1 hactive.1 ∧ P w.2) :=
        (hK z.1.1 hactive.1 z.2 hz hactive.2).map
          (fun y ↦ (advanceTime z.1 hactive.1, y))
          (fun _ hy ↦ ⟨rfl, hy⟩)
      have hz' := hsupp z' hz'mass
      have hz'baseMass : 0 < (K z.1.1 z.2).mass z'.2 := by
        change 0 < ∑ y, if
          (advanceTime z.1 hactive.1, y) = z' then
            (K z.1.1 z.2).mass y else 0 at hz'mass
        obtain ⟨y, _hyuniv, hy⟩ := Finset.sum_pos_iff.mp hz'mass
        by_cases heq : (advanceTime z.1 hactive.1, y) = z'
        · have hyval : y = z'.2 := congrArg Prod.snd heq
          subst y
          simpa [heq] using hy
        · simp [heq] at hy
      change F z'.1.1 z'.2 - F z.1.1 z.2 ≤ R
      rw [hz'.1]
      simp only [advanceTime_val]
      exact hjump z.1.1 hactive.1 z.2 hz hactive.2 hzAlive z'.2
        hz'baseMass hz'.2
    · have hz'eq : z' = z := by
        exact (supportedOn_pure (fun w : Ωt ↦ w = z) rfl) z' hz'mass
      subst z'
      simp [Ft, hR]
  have hdriftKt : ∀ i, i < n → ∀ z, Pt z → aliveT z →
      (Kt i z).expectationReal
        (fun z' ↦ Ft (i + 1) z' - Ft i z) ≤ 0 := by
    intro i _hi z hz hzAlive
    dsimp [Kt]
    unfold timedStoppedKernel
    split_ifs with hactive
    · rw [expectationReal_map]
      simpa [Ft] using
        hdrift z.1.1 hactive.1 z.2 hz hactive.2 hzAlive
    · simp [Ft]
  have hsecondKt : ∀ i, i < n → ∀ z, Pt z → aliveT z →
      (Kt i z).expectationReal
        (fun z' ↦ (Ft (i + 1) z' - Ft i z) ^ 2) ≤ v := by
    intro i _hi z hz hzAlive
    dsimp [Kt]
    unfold timedStoppedKernel
    split_ifs with hactive
    · rw [expectationReal_map]
      simpa [Ft] using
        hsecond z.1.1 hactive.1 z.2 hz hactive.2 hzAlive
    · simpa [Ft] using hv
  have htail :=
    probability_evolveKernels_alive_deviation_ge_le_exp_fullIncrement
      aliveT (P := Pt) Kt Ft z₀ theta R a (fun _ ↦ v) n
      hP₀ halive₀ htheta hR hthetaR hKt hdeadKt hjumpKt hdriftKt hsecondKt
  have hsum : ∑ _i ∈ Finset.range n, v = (n : ℝ) * v := by simp
  simpa [timedStoppedProcessLaw, Kt, Ft, Pt, aliveT, z₀, hsum,
    mul_assoc] using htail

end FiniteLaw

end

end Erdos207
