/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 330, positive upper density formulation.
Informal authors: GPT-5.5 Pro, David Turturean.
Formal authors: Codex, GPT-5.5 Pro, Allen Graham Hart.
Source: https://www.erdosproblems.com/forum/thread/330#post-6271
https://github.com/AllenGrahamHart/FormalConjectures-Bench/tree/6160036caab0dcee80395ba3beb7b6ef2731604e/formalizations/erdos330
Original Lean/Mathlib version: 4.27.0.
-/
import ErdosProblems.Erdos330.Stage

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Abstract global construction for Erdős Problem 330

This file proves consequences of an infinite chain of finite stage states.
The concrete stage construction will later supply such a chain.
-/

namespace Erdos330

/-- The final set produced by an infinite sequence of finite stages. -/
def finalSet (st : ℕ → StageState) : Set ℕ :=
  {n | ∃ k : ℕ, n ∈ (st k).S}

/-- A sequence of stages where each stage extends the previous one. -/
structure StageChain (st : ℕ → StageState) where
  step : ∀ k : ℕ, StageExtension (st k) (st (k + 1))

namespace StageChain

theorem S_subset_of_le {st : ℕ → StageState} (chain : StageChain st)
    {i j : ℕ} (hij : i ≤ j) :
    (st i).S ⊆ (st j).S := by
  induction j with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst hi
      intro n hn
      exact hn
  | succ j ih =>
      by_cases hle : i ≤ j
      · intro n hn
        exact (chain.step j).S_subset ((ih hle) hn)
      · have hi : i = j + 1 := by omega
        subst hi
        intro n hn
        exact hn

theorem P_subset_of_le {st : ℕ → StageState} (chain : StageChain st)
    {i j : ℕ} (hij : i ≤ j) :
    (st i).P ⊆ (st j).P := by
  induction j with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst hi
      intro n hn
      exact hn
  | succ j ih =>
      by_cases hle : i ≤ j
      · intro n hn
        exact (chain.step j).P_subset ((ih hle) hn)
      · have hi : i = j + 1 := by omega
        subst hi
        intro n hn
        exact hn

theorem m_eq_of_le_of_mem_P {st : ℕ → StageState} (chain : StageChain st)
    {i j a : ℕ} (hij : i ≤ j) (ha : a ∈ (st i).P) :
    (st j).m a = (st i).m a := by
  induction j with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst hi
      rfl
  | succ j ih =>
      by_cases hle : i ≤ j
      · calc
          (st (j + 1)).m a = (st j).m a :=
            (chain.step j).m_eq_on_old a ((chain.P_subset_of_le hle) ha)
          _ = (st i).m a := ih hle
      · have hi : i = j + 1 := by omega
        subst hi
        rfl

theorem coverStart_eq_of_le {st : ℕ → StageState} (chain : StageChain st)
    {i j : ℕ} (hij : i ≤ j) :
    (st j).coverStart = (st i).coverStart := by
  induction j with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst hi
      rfl
  | succ j ih =>
      by_cases hle : i ≤ j
      · calc
          (st (j + 1)).coverStart = (st j).coverStart := (chain.step j).coverStart_eq
          _ = (st i).coverStart := ih hle
      · have hi : i = j + 1 := by omega
        subst hi
        rfl

theorem coverStart_eq_zero {st : ℕ → StageState} (chain : StageChain st) (j : ℕ) :
    (st j).coverStart = (st 0).coverStart :=
  chain.coverStart_eq_of_le (Nat.zero_le j)

theorem X_mono_of_le {st : ℕ → StageState} (chain : StageChain st)
    {i j : ℕ} (hij : i ≤ j) :
    (st i).X ≤ (st j).X := by
  induction j with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst hi
      rfl
  | succ j ih =>
      by_cases hle : i ≤ j
      · exact (ih hle).trans (chain.step j).X_mono
      · have hi : i = j + 1 := by omega
        subst hi
        rfl

theorem mem_of_mem_stage_of_le_X {st : ℕ → StageState} (chain : StageChain st)
    {i j n : ℕ} (hij : i ≤ j) (hnj : n ∈ (st j).S) (hnX : n ≤ (st i).X) :
    n ∈ (st i).S := by
  induction j with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst hi
      exact hnj
  | succ j ih =>
      by_cases hle : i ≤ j
      · have hnj_old : n ∈ (st j).S := by
          by_contra hnot
          have hnew := (chain.step j).new_elements_above_old_X n hnj hnot
          have hXiXj := chain.X_mono_of_le hle
          omega
        exact ih hle hnj_old
      · have hi : i = j + 1 := by omega
        subst hi
        exact hnj

theorem mem_stage_of_finalSet_of_le_X {st : ℕ → StageState} (chain : StageChain st)
    {k n : ℕ} (hn : n ∈ finalSet st) (hnX : n ≤ (st k).X) :
    n ∈ (st k).S := by
  rcases hn with ⟨j, hnj⟩
  cases le_total j k with
  | inl hjk => exact chain.S_subset_of_le hjk hnj
  | inr hkj => exact chain.mem_of_mem_stage_of_le_X hkj hnj hnX

end StageChain

theorem mem_finalSet_of_mem_stage {st : ℕ → StageState} {k n : ℕ}
    (hn : n ∈ (st k).S) :
    n ∈ finalSet st :=
  ⟨k, hn⟩

theorem stage_subset_finalSet {st : ℕ → StageState} (k : ℕ) :
    {n : ℕ | n ∈ (st k).S} ⊆ finalSet st := by
  intro n hn
  exact mem_finalSet_of_mem_stage hn

theorem twoFoldFinset_subset_finalSet {st : ℕ → StageState} (k : ℕ) :
    twoFoldFinset (st k).S ⊆ twoFold (finalSet st) := by
  intro n hn
  rcases hn with ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, mem_finalSet_of_mem_stage hx, y, mem_finalSet_of_mem_stage hy, hxy⟩

/--
If the finite-stage coverage endpoints are unbounded, the final union is an
asymptotic basis of order two.
-/
theorem finalSet_isAsymptoticBasisTwo {st : ℕ → StageState} (chain : StageChain st)
    (hR_unbounded : ∀ n : ℕ, ∃ k : ℕ, n ≤ (st k).R) :
    IsAsymptoticBasisTwo (finalSet st) := by
  refine ⟨(st 0).coverStart, ?_⟩
  intro n hn_start
  obtain ⟨k, hkR⟩ := hR_unbounded n
  have hstage_start : (st k).coverStart ≤ n := by
    rw [chain.coverStart_eq_zero k]
    exact hn_start
  exact twoFoldFinset_subset_finalSet k ((st k).coverage n hstage_start hkR)

theorem privateSet_final_of_private_stage {st : ℕ → StageState} (chain : StageChain st)
    {k a endpoint n : ℕ} (hendpoint : endpoint ≤ (st k).X)
    (cert : ProtectedBlockCertificate (st k).S a endpoint)
    (hn : n ∈ cert.block) :
    n ∈ privateSet (finalSet st) a := by
  have hstage := cert.block_subset_private n hn
  rcases hstage with ⟨hstage_two, hstage_not⟩
  refine ⟨?_, ?_⟩
  · rcases hstage_two with ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, mem_finalSet_of_mem_stage hx, y, mem_finalSet_of_mem_stage hy, hxy⟩
  · intro hfinal
    rcases hfinal with ⟨x, hx, y, hy, hxy⟩
    have hn_endpoint : n ≤ endpoint := cert.block_le_endpoint n hn
    have hx_stage : x ∈ (st k).S :=
      chain.mem_stage_of_finalSet_of_le_X hx.1 (by omega)
    have hy_stage : y ∈ (st k).S :=
      chain.mem_stage_of_finalSet_of_le_X hy.1 (by omega)
    apply hstage_not
    exact ⟨x, ⟨hx_stage, hx.2⟩, y, ⟨hy_stage, hy.2⟩, hxy⟩

theorem protectedBlock_subset_final_private {st : ℕ → StageState} (chain : StageChain st)
    {k a endpoint : ℕ} (hendpoint : endpoint ≤ (st k).X)
    (cert : ProtectedBlockCertificate (st k).S a endpoint) :
    ∀ n ∈ cert.block, n ∈ privateSet (finalSet st) a := by
  intro n hn
  exact privateSet_final_of_private_stage chain hendpoint cert hn

theorem mainTarget_of_finalSet_certificates {st : ℕ → StageState} (chain : StageChain st)
    (hR_unbounded : ∀ n : ℕ, ∃ k : ℕ, n ≤ (st k).R)
    (hA_density : HasPositiveUpperDensity (finalSet st))
    (hprivate_density :
      ∀ a ∈ finalSet st, HasPositiveUpperDensity (privateSet (finalSet st) a)) :
    MainTarget := by
  exact ⟨finalSet st, finalSet_isAsymptoticBasisTwo chain hR_unbounded, hA_density,
    hprivate_density⟩

end Erdos330
