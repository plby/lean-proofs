/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.AdaptiveProcess
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Lee's adaptive random-greedy schedule

The target colour classes are processed from the greatest class downwards.
Inside the current class, the next vertex is one of maximum realized defect.
This is the schedule used in Lee's Lemma 4.3.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace AdaptiveGreedy

universe u v w

variable {α : Type u} {β : Type v} {ι : Type w}
  [Fintype α] [DecidableEq α] [LinearOrder α]
  [Fintype β] [DecidableEq β]
  [DecidableEq ι] [LinearOrder ι]

/-! ## The numerical estimate in Lee's deterministic criterion -/

/-- If `j` positive target vertices all contribute at least the current
defect and their total contribution is at most `θ / 2`, then the current
common neighborhood has at least `2j` vertices.  The separate hypothesis
`2j ≤ θ` is exactly the zero-defect case. -/
theorem two_mul_le_commonNeighbors_card_of_mul_defect_le
    (G : SimpleGraph β) [DecidableRel G.Adj]
    {κ : Type*} [Fintype κ] (q : κ → β) (T : Finset β)
    {θ j : ℕ} (hθ : 0 < θ) (hj : 0 < j) (hθj : 2 * j ≤ θ)
    (hbound : (j : ℝ) * FiniteDefect.defect G θ q T ≤ (θ : ℝ) / 2) :
    2 * j ≤ (FiniteDefect.commonNeighbors G q T).card := by
  let m := (FiniteDefect.commonNeighbors G q T).card
  by_cases hlarge : θ ≤ m
  · exact hθj.trans hlarge
  have hsmall : m < θ := Nat.lt_of_not_ge hlarge
  by_cases hm : m = 0
  · have hempty : FiniteDefect.commonNeighbors G q T = ∅ :=
      Finset.card_eq_zero.mp hm
    rw [FiniteDefect.defect_eq_sentinel_of_empty G hθ hempty] at hbound
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hθR : (0 : ℝ) < θ := by exact_mod_cast hθ
    have hcardR : (1 : ℝ) ≤ Fintype.card β + 1 := by norm_num
    have hlower : (θ : ℝ) ≤
        (j : ℝ) * ((θ : ℝ) * (Fintype.card β + 1)) := by
      calc
        (θ : ℝ) = 1 * ((θ : ℝ) * 1) := by ring
        _ ≤ (j : ℝ) * ((θ : ℝ) * (Fintype.card β + 1)) := by
          gcongr
    linarith
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
    have hθR : (0 : ℝ) < θ := by exact_mod_cast hθ
    rw [FiniteDefect.defect_eq_div_of_pos_card_lt G (by simpa [m] using hmpos)
      (by simpa [m] using hsmall)] at hbound
    have hdiv : ((j : ℝ) * (θ : ℝ)) / (m : ℝ) ≤ (θ : ℝ) / 2 := by
      simpa [mul_div_assoc] using hbound
    have hmul : (j : ℝ) * (θ : ℝ) ≤ ((θ : ℝ) / 2) * m :=
      (div_le_iff₀ hmR).mp hdiv
    have hreal : (2 : ℝ) * j ≤ m := by
      nlinarith
    exact_mod_cast hreal

/-- The random-greedy data together with the vertices not yet exposed. -/
structure State (α : Type u) (β : Type v) where
  core : RandomGreedy.State α β
  remaining : Finset α

def initialState : State α β where
  core := RandomGreedy.initialState
  remaining := Finset.univ

noncomputable def currentDefect (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (default : β) (state : State α β) (x : α) : ℝ :=
  FiniteDefect.defect G (threshold (part x))
    (fun y : RandomGreedy.forwardNeighbors H x =>
      RandomGreedy.value default state.core y) (host (part x))

/-- The priority key first maximizes the target part, then the realized
defect, and finally uses the fixed target order only to break ties. -/
noncomputable def priorityKey (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (default : β) (state : State α β) (x : α) :
    Lex (ι × Lex (ℝ × α)) :=
  toLex (part x,
    toLex (currentDefect G H host part threshold default state x, x))

theorem priorityKey_injective (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (default : β) (state : State α β) :
    Function.Injective (priorityKey G H host part threshold default state) := by
  intro x y h
  exact congrArg (fun p : Lex (ι × Lex (ℝ × α)) => (ofLex (ofLex p).2).2) h

/-- The next target vertex.  The fallback is used only after `remaining` is
empty; all actual runs stop at that point. -/
noncomputable def next (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (defaultTarget : α) (default : β) (state : State α β) : α := by
  let key := priorityKey G H host part threshold default state
  let subkey : state.remaining → Lex (ι × Lex (ℝ × α)) := fun x => key x
  let ord : LinearOrder state.remaining := LinearOrder.lift' subkey
    ((priorityKey_injective G H host part threshold default state).comp
      Subtype.val_injective)
  exact if h : state.remaining.Nonempty then
    (@Finset.max' state.remaining ord state.remaining.attach (by simpa using h) :
      state.remaining)
  else defaultTarget

theorem next_mem (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (defaultTarget : α) (default : β) (state : State α β)
    (hne : state.remaining.Nonempty) :
    next G H host part threshold defaultTarget default state ∈ state.remaining := by
  let key := priorityKey G H host part threshold default state
  let subkey : state.remaining → Lex (ι × Lex (ℝ × α)) := fun x => key x
  let ord : LinearOrder state.remaining := LinearOrder.lift' subkey
    ((priorityKey_injective G H host part threshold default state).comp
      Subtype.val_injective)
  let m : state.remaining :=
    @Finset.max' state.remaining ord state.remaining.attach (by simpa using hne)
  have hm : (m : α) ∈ state.remaining := m.property
  simpa [next, hne, key, subkey, m] using hm

/-- The selected vertex lies in a greatest target part among those still
unexposed. -/
theorem part_le_part_next (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (defaultTarget : α) (default : β) (state : State α β)
    (hne : state.remaining.Nonempty) {y : α} (hy : y ∈ state.remaining) :
    part y ≤ part (next G H host part threshold defaultTarget default state) := by
  let key := priorityKey G H host part threshold default state
  let subkey : state.remaining → Lex (ι × Lex (ℝ × α)) := fun x => key x
  let ord : LinearOrder state.remaining := LinearOrder.lift' subkey
    ((priorityKey_injective G H host part threshold default state).comp
      Subtype.val_injective)
  let yy : state.remaining := ⟨y, hy⟩
  have hmax : @LE.le state.remaining ord.toLE yy
      (@Finset.max' state.remaining ord state.remaining.attach (by simpa using hne)) :=
    @Finset.le_max' state.remaining ord state.remaining.attach yy (by simp [yy])
  change key (yy : α) ≤ key
    (↑(@Finset.max' state.remaining ord state.remaining.attach (by simpa using hne)) : α)
      at hmax
  have hkey : key y ≤
      key (next G H host part threshold defaultTarget default state) := by
    simpa [next, hne, key, subkey, yy] using hmax
  by_contra hnot
  have hlt : part (next G H host part threshold defaultTarget default state) < part y :=
    lt_of_not_ge hnot
  have hkeylt :
      key (next G H host part threshold defaultTarget default state) < key y := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inl hlt
  exact (not_lt_of_ge hkey) hkeylt

/-- Within the greatest remaining target part, the selected vertex has
maximum realized defect. -/
theorem currentDefect_le_next (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (defaultTarget : α) (default : β) (state : State α β)
    (hne : state.remaining.Nonempty) {y : α} (hy : y ∈ state.remaining)
    (hpart : part y =
      part (next G H host part threshold defaultTarget default state)) :
    currentDefect G H host part threshold default state y ≤
      currentDefect G H host part threshold default state
        (next G H host part threshold defaultTarget default state) := by
  let key := priorityKey G H host part threshold default state
  let subkey : state.remaining → Lex (ι × Lex (ℝ × α)) := fun x => key x
  let ord : LinearOrder state.remaining := LinearOrder.lift' subkey
    ((priorityKey_injective G H host part threshold default state).comp
      Subtype.val_injective)
  let yy : state.remaining := ⟨y, hy⟩
  have hmax : @LE.le state.remaining ord.toLE yy
      (@Finset.max' state.remaining ord state.remaining.attach (by simpa using hne)) :=
    @Finset.le_max' state.remaining ord state.remaining.attach yy (by simp [yy])
  change key (yy : α) ≤ key
    (↑(@Finset.max' state.remaining ord state.remaining.attach (by simpa using hne)) : α)
      at hmax
  have hkey : key y ≤
      key (next G H host part threshold defaultTarget default state) := by
    simpa [next, hne, key, subkey, yy] using hmax
  by_contra hnot
  have hlt : currentDefect G H host part threshold default state
      (next G H host part threshold defaultTarget default state) <
      currentDefect G H host part threshold default state y := lt_of_not_ge hnot
  have hkeylt :
      key (next G H host part threshold defaultTarget default state) < key y := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    right
    refine ⟨hpart.symm, ?_⟩
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inl hlt
  exact (not_lt_of_ge hkey) hkeylt

/-! ## The injective branch -/

/-- If the full common neighborhood is nonempty and at least twice as large
as the already used set, Lee's three-branch rule is exactly the unused
common-neighborhood branch. -/
theorem choices_eq_unused_of_two_used_le
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (default : β)
    (state : RandomGreedy.State α β) (x : α)
    (hne : (RandomGreedy.fullCandidates G H host part default state x).Nonempty)
    (hused : 2 * (RandomGreedy.usedInPart part default state x).card ≤
      (RandomGreedy.fullCandidates G H host part default state x).card) :
    RandomGreedy.choices G H host part default state x =
      RandomGreedy.unusedCandidates G H host part default state x := by
  classical
  let N := RandomGreedy.fullCandidates G H host part default state x
  let U := RandomGreedy.usedInPart part default state x
  let L := RandomGreedy.unusedCandidates G H host part default state x
  have hNne : N ≠ ∅ := Finset.nonempty_iff_ne_empty.mp (by simpa [N] using hne)
  have hNLU : N.card ≤ L.card + U.card := by
    simpa [L, RandomGreedy.unusedCandidates, N, U] using
      (Finset.card_le_card_sdiff_add_card (s := N) (t := U))
  have hnotSmall : ¬2 * L.card < N.card := by
    intro hsmall
    have hused' : 2 * U.card ≤ N.card := by simpa [N, U] using hused
    omega
  unfold RandomGreedy.choices
  dsimp
  simpa [N, L, hNne, hnotSmall]

/-- Update at an explicitly specified target vertex. -/
noncomputable def stepAt (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (default : β) (x : α)
    (state : State α β) (z : β) : State α β :=
  { core := RandomGreedy.step G H host part (threshold ∘ part)
      momentExponent default x state.core z
    remaining := state.remaining.erase x }

/-- One adaptive transition: apply the old three-branch update at the
state-selected target and erase that target from the remaining set. -/
noncomputable def step (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    (state : State α β) (z : β) : State α β :=
  stepAt G H host part threshold momentExponent default
    (next G H host part threshold defaultTarget default state) state z

noncomputable def choices (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (defaultTarget : α) (default : β) (state : State α β) : Finset β :=
  RandomGreedy.choices G H host part default state.core
    (next G H host part threshold defaultTarget default state)

/-! ## Partial-embedding invariant -/

/-- Precisely the complement of `remaining` has been embedded, with all
already forced edges preserved. -/
structure GoodState (G : SimpleGraph β) (H : SimpleGraph α)
    (host : ι → Finset β) (part : α → ι) (default : β)
    (state : State α β) : Prop where
  assigned_iff : ∀ x, RandomGreedy.assigned state.core x ↔ x ∉ state.remaining
  in_host : ∀ x, RandomGreedy.assigned state.core x →
    RandomGreedy.value default state.core x ∈ host (part x)
  injective : ∀ ⦃x y⦄, RandomGreedy.assigned state.core x →
    RandomGreedy.assigned state.core y →
    RandomGreedy.value default state.core x =
      RandomGreedy.value default state.core y → x = y
  map_adj : ∀ ⦃x y⦄, RandomGreedy.assigned state.core x →
    RandomGreedy.assigned state.core y → H.Adj x y →
    G.Adj (RandomGreedy.value default state.core x)
      (RandomGreedy.value default state.core y)
  before_remaining : ∀ ⦃x y⦄, x ∈ state.remaining →
    RandomGreedy.assigned state.core y → H.Adj x y → x < y
  parts_ordered : ∀ ⦃x y⦄, x ∈ state.remaining →
    RandomGreedy.assigned state.core y → part x ≤ part y

theorem goodState_initial (G : SimpleGraph β) (H : SimpleGraph α)
    (host : ι → Finset β) (part : α → ι) (default : β) :
    GoodState G H host part default (initialState : State α β) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [RandomGreedy.assigned, initialState, RandomGreedy.initialState]
  · intro x hx
    simp [RandomGreedy.assigned, initialState, RandomGreedy.initialState] at hx
  · intro x y hx
    simp [RandomGreedy.assigned, initialState, RandomGreedy.initialState] at hx
  · intro x y hx
    simp [RandomGreedy.assigned, initialState, RandomGreedy.initialState] at hx
  · intro x y hx hy
    simp [RandomGreedy.assigned, initialState, RandomGreedy.initialState] at hy
  · intro x y hx hy
    simp [RandomGreedy.assigned, initialState, RandomGreedy.initialState] at hy

theorem goodState_stepAt
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (default : β)
    (hhost : ∀ ⦃i j⦄, i ≠ j → Disjoint (host i) (host j))
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    {state : State α β} {x : α} (hx : x ∈ state.remaining) {z : β}
    (hmaxpart : ∀ ⦃a⦄, a ∈ state.remaining → part a ≤ part x)
    (hbelow : ∀ ⦃a⦄, a ∈ state.remaining.erase x → H.Adj a x → a < x)
    (hgood : GoodState G H host part default state)
    (hz : z ∈ RandomGreedy.unusedCandidates G H host part default state.core x) :
    GoodState G H host part default
      (stepAt G H host part threshold momentExponent default x state z) := by
  let state' := stepAt G H host part threshold momentExponent default x state z
  have hzfull : z ∈ RandomGreedy.fullCandidates G H host part default state.core x :=
    (Finset.mem_sdiff.mp hz).1
  have hzhost : z ∈ host (part x) :=
    Defect.commonNeighbors_subset_target G _ _ hzfull
  have hnew_old_ne : ∀ ⦃y⦄, RandomGreedy.assigned state.core y →
      z ≠ RandomGreedy.value default state.core y := by
    intro y hy
    by_cases hpx : part y = part x
    · exact fun heq => (Finset.mem_sdiff.mp hz).2
        (heq ▸ RandomGreedy.mem_usedInPart_of_assigned part default state.core hy hpx)
    · have hyhost := hgood.in_host y hy
      intro heq
      rw [heq] at hzhost
      exact Finset.disjoint_left.mp (hhost hpx) hyhost hzhost
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    by_cases hyx : y = x
    · subst y
      simp [state', stepAt, RandomGreedy.assigned, RandomGreedy.step, hx]
    · change RandomGreedy.assigned
        (RandomGreedy.step G H host part (threshold ∘ part) momentExponent
          default x state.core z) y ↔ y ∉ state.remaining.erase x
      rw [RandomGreedy.assigned_step_of_ne G H host part (threshold ∘ part)
        momentExponent default state.core hyx z]
      rw [hgood.assigned_iff]
      simp [state', stepAt, hyx]
  · intro y hy
    by_cases hyx : y = x
    · subst y
      simpa [state', stepAt] using hzhost
    · change RandomGreedy.value default
        (RandomGreedy.step G H host part (threshold ∘ part) momentExponent
          default x state.core z) y ∈ host (part y)
      rw [RandomGreedy.value_step_of_ne G H host part (threshold ∘ part)
        momentExponent default state.core hyx z]
      exact hgood.in_host y
        ((RandomGreedy.assigned_step_of_ne G H host part (threshold ∘ part)
          momentExponent default state.core hyx z).mp hy)
  · intro a b ha hb hab
    by_cases hax : a = x
    · subst a
      by_cases hbx : b = x
      · exact hbx.symm
      · exfalso
        have hbOld := (RandomGreedy.assigned_step_of_ne G H host part
          (threshold ∘ part) momentExponent default state.core hbx z).mp hb
        have hvb := RandomGreedy.value_step_of_ne G H host part
          (threshold ∘ part) momentExponent default state.core hbx z
        exact hnew_old_ne hbOld (by simpa [state', stepAt, hvb] using hab)
    · by_cases hbx : b = x
      · subst b
        exfalso
        have haOld := (RandomGreedy.assigned_step_of_ne G H host part
          (threshold ∘ part) momentExponent default state.core hax z).mp ha
        have hva := RandomGreedy.value_step_of_ne G H host part
          (threshold ∘ part) momentExponent default state.core hax z
        exact hnew_old_ne haOld (by simpa [state', stepAt, hva] using hab.symm)
      · have haOld := (RandomGreedy.assigned_step_of_ne G H host part
          (threshold ∘ part) momentExponent default state.core hax z).mp ha
        have hbOld := (RandomGreedy.assigned_step_of_ne G H host part
          (threshold ∘ part) momentExponent default state.core hbx z).mp hb
        apply hgood.injective haOld hbOld
        simpa [state', stepAt,
          RandomGreedy.value_step_of_ne G H host part (threshold ∘ part)
            momentExponent default state.core hax z,
          RandomGreedy.value_step_of_ne G H host part (threshold ∘ part)
            momentExponent default state.core hbx z] using hab
  · intro a b ha hb hab
    by_cases hax : a = x
    · subst a
      have hbx : b ≠ x := fun h => H.irrefl (h ▸ hab)
      have hbOld := (RandomGreedy.assigned_step_of_ne G H host part
        (threshold ∘ part) momentExponent default state.core hbx z).mp hb
      have hxb : x < b := hgood.before_remaining hx hbOld hab
      have hbforward : b ∈ RandomGreedy.forwardNeighbors H x := by
        simp [RandomGreedy.forwardNeighbors, hab, hxb]
      have hadj : G.Adj z (RandomGreedy.value default state.core b) :=
        (((Defect.mem_commonNeighbors G _ _ z).mp hzfull).2
          ⟨b, hbforward⟩).symm
      simpa [state', stepAt,
        RandomGreedy.value_step_of_ne G H host part (threshold ∘ part)
          momentExponent default state.core hbx z] using hadj
    · by_cases hbx : b = x
      · subst b
        have haOld := (RandomGreedy.assigned_step_of_ne G H host part
          (threshold ∘ part) momentExponent default state.core hax z).mp ha
        have hxa : x < a := hgood.before_remaining hx haOld hab.symm
        have haforward : a ∈ RandomGreedy.forwardNeighbors H x := by
          simp [RandomGreedy.forwardNeighbors, hab.symm, hxa]
        have hadj : G.Adj z (RandomGreedy.value default state.core a) :=
          (((Defect.mem_commonNeighbors G _ _ z).mp hzfull).2
            ⟨a, haforward⟩).symm
        simpa [state', stepAt,
          RandomGreedy.value_step_of_ne G H host part (threshold ∘ part)
            momentExponent default state.core hax z] using hadj.symm
      · have haOld := (RandomGreedy.assigned_step_of_ne G H host part
          (threshold ∘ part) momentExponent default state.core hax z).mp ha
        have hbOld := (RandomGreedy.assigned_step_of_ne G H host part
          (threshold ∘ part) momentExponent default state.core hbx z).mp hb
        simpa [state', stepAt,
          RandomGreedy.value_step_of_ne G H host part (threshold ∘ part)
            momentExponent default state.core hax z,
          RandomGreedy.value_step_of_ne G H host part (threshold ∘ part)
            momentExponent default state.core hbx z] using
          hgood.map_adj haOld hbOld hab
  · intro a b ha hb hab
    by_cases hbx : b = x
    · subst b
      exact hbelow ha hab
    · exact hgood.before_remaining (Finset.mem_erase.mp ha).2
        ((RandomGreedy.assigned_step_of_ne G H host part (threshold ∘ part)
          momentExponent default state.core hbx z).mp hb) hab
  · intro a b ha hb
    by_cases hbx : b = x
    · subst b
      exact hmaxpart (Finset.mem_erase.mp ha).2
    · exact hgood.parts_ordered (Finset.mem_erase.mp ha).2
        ((RandomGreedy.assigned_step_of_ne G H host part (threshold ∘ part)
          momentExponent default state.core hbx z).mp hb)

theorem goodState_step
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    (hhost : ∀ ⦃i j⦄, i ≠ j → Disjoint (host i) (host j))
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    (horder : ∀ ⦃a b⦄, H.Adj a b → (a < b ↔ part a < part b))
    {state : State α β} (hne : state.remaining.Nonempty) {z : β}
    (hgood : GoodState G H host part default state)
    (hz : z ∈ RandomGreedy.unusedCandidates G H host part default state.core
      (next G H host part threshold defaultTarget default state)) :
    GoodState G H host part default
      (step G H host part threshold momentExponent defaultTarget default state z) := by
  let x := next G H host part threshold defaultTarget default state
  have hx : x ∈ state.remaining := by
    exact next_mem G H host part threshold defaultTarget default state hne
  have hbelow : ∀ ⦃a⦄, a ∈ state.remaining.erase x → H.Adj a x → a < x := by
    intro a ha hax
    have hle : part a ≤ part x := by
      exact part_le_part_next G H host part threshold defaultTarget default state
        hne (Finset.mem_erase.mp ha).2
    have hnepart : part a ≠ part x := hpart hax
    have hlt : part a < part x := lt_of_le_of_ne hle hnepart
    exact (horder hax).2 hlt
  have hmaxpart : ∀ ⦃a⦄, a ∈ state.remaining → part a ≤ part x := by
    intro a ha
    exact part_le_part_next G H host part threshold defaultTarget default state hne ha
  exact goodState_stepAt G H host part threshold momentExponent default hhost hpart
    hx hmaxpart hbelow hgood hz

/-! ## Maximum-defect order inside a target part -/

theorem currentDefect_stepAt_of_same_part
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (default : β)
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    (state : State α β) {x y : α} (hxy : part x = part y) (z : β) :
    currentDefect G H host part threshold default
        (stepAt G H host part threshold momentExponent default y state z) x =
      currentDefect G H host part threshold default state x := by
  unfold currentDefect
  apply congrArg (fun q =>
    FiniteDefect.defect G (threshold (part x)) q (host (part x)))
  funext a
  apply RandomGreedy.value_step_of_ne G H host part (threshold ∘ part)
    momentExponent default state.core
  intro ha
  have hadj : H.Adj x (a : α) :=
    (Finset.mem_filter.mp a.property).2.1
  have hnepart := hpart hadj
  apply hnepart
  simpa [ha] using hxy

structure DefectsOrdered (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (default : β) (state : State α β) : Prop where
  ordered : ∀ ⦃y x⦄, RandomGreedy.assigned state.core y →
    x ∈ state.remaining → part y = part x →
    currentDefect G H host part threshold default state x ≤ state.core.defectSeen y

theorem defectsOrdered_initial
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (default : β) :
    DefectsOrdered G H host part threshold default (initialState : State α β) := by
  constructor
  intro y x hy
  simp [RandomGreedy.assigned, initialState, RandomGreedy.initialState] at hy

theorem defectsOrdered_step
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    {state : State α β} (hne : state.remaining.Nonempty) (z : β)
    (hgood : GoodState G H host part default state)
    (hordered : DefectsOrdered G H host part threshold default state) :
    DefectsOrdered G H host part threshold default
      (step G H host part threshold momentExponent defaultTarget default state z) := by
  let x := next G H host part threshold defaultTarget default state
  have hx : x ∈ state.remaining :=
    next_mem G H host part threshold defaultTarget default state hne
  constructor
  intro y a hy ha hya
  have haOld : a ∈ state.remaining := (Finset.mem_erase.mp ha).2
  by_cases hyx : y = x
  · subst y
    have hax : part a = part x := hya.symm
    have hmax := currentDefect_le_next G H host part threshold defaultTarget default
      state hne haOld hax
    change currentDefect G H host part threshold default
        (stepAt G H host part threshold momentExponent default x state z) a ≤
      (RandomGreedy.step G H host part (threshold ∘ part) momentExponent
        default x state.core z).defectSeen x
    rw [currentDefect_stepAt_of_same_part G H host part threshold
      momentExponent default hpart state hax z]
    simpa [RandomGreedy.step, currentDefect] using hmax
  · have hyOld : RandomGreedy.assigned state.core y :=
      (RandomGreedy.assigned_step_of_ne G H host part (threshold ∘ part)
        momentExponent default state.core hyx z).mp hy
    have hxb : part x ≤ part y := hgood.parts_ordered hx hyOld
    have haxle : part a ≤ part x :=
      part_le_part_next G H host part threshold defaultTarget default state hne haOld
    have hsame : part a = part x := by
      apply le_antisymm haxle
      simpa [hya] using hxb
    have hold := hordered.ordered hyOld haOld hya
    change currentDefect G H host part threshold default
        (stepAt G H host part threshold momentExponent default x state z) a ≤
      (RandomGreedy.step G H host part (threshold ∘ part) momentExponent
        default x state.core z).defectSeen y
    rw [currentDefect_stepAt_of_same_part G H host part threshold
      momentExponent default hpart state hsame z]
    simpa [RandomGreedy.step, hyx] using hold

/-! ## Lee's `j · ω` estimate -/

noncomputable def assignedInPart (part : α → ι) (state : State α β)
    (x : α) : Finset α := by
  classical
  exact Finset.univ.filter fun y =>
    RandomGreedy.assigned state.core y ∧ part y = part x

@[simp] theorem mem_assignedInPart (part : α → ι) (state : State α β)
    (x y : α) :
    y ∈ assignedInPart part state x ↔
      RandomGreedy.assigned state.core y ∧ part y = part x := by
  classical
  simp [assignedInPart]

theorem usedInPart_card_le_assignedInPart_card
    (part : α → ι) (default : β) (state : State α β) (x : α) :
    (RandomGreedy.usedInPart part default state.core x).card ≤
      (assignedInPart part state x).card := by
  classical
  calc
    (RandomGreedy.usedInPart part default state.core x).card ≤
        (Finset.univ.filter fun y =>
          (state.core.image y).isSome ∧ part y = part x).card := by
      exact Finset.card_image_le
    _ = (assignedInPart part state x).card := by
      apply congrArg Finset.card
      ext y
      rw [mem_assignedInPart]
      simp [RandomGreedy.assigned]

theorem assignedInPart_card_add_one_le_partVertices_card
    (G : SimpleGraph β) (H : SimpleGraph α)
    (host : ι → Finset β) (part : α → ι) (default : β)
    {state : State α β} {x : α} (hx : x ∈ state.remaining)
    (hgood : GoodState G H host part default state) :
    (assignedInPart part state x).card + 1 ≤
      (RandomGreedy.partVertices part x).card := by
  classical
  have hxnot : x ∉ assignedInPart part state x := by
    intro hxin
    have hassigned : RandomGreedy.assigned state.core x :=
      (mem_assignedInPart part state x x).mp hxin |>.1
    exact (hgood.assigned_iff x).mp hassigned hx
  rw [← Finset.card_insert_of_notMem hxnot]
  apply Finset.card_le_card
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · simp [RandomGreedy.partVertices]
  · have hypart := (mem_assignedInPart part state x y).mp hy |>.2
    simp [RandomGreedy.partVertices, hypart]

noncomputable def realizedDefect
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (default : β) (state : State α β) (x : α) : ℝ :=
  @ite ℝ (RandomGreedy.assigned state.core x)
    (Classical.propDecidable (RandomGreedy.assigned state.core x))
    (state.core.defectSeen x)
    (currentDefect G H host part threshold default state x)

noncomputable def partDefectMass
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (default : β) (state : State α β) (i : ι) (s : ℕ) : ℝ :=
  ∑ x ∈ Finset.univ.filter fun x => part x = i,
    realizedDefect G H host part threshold default state x ^ s

theorem mul_currentDefect_le_partDefectMass
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (default : β) {state : State α β} {x : α} {s : ℕ}
    (hs : 0 < s) (hx : x ∈ state.remaining)
    (hgood : GoodState G H host part default state)
    (hordered : DefectsOrdered G H host part threshold default state) :
    ((assignedInPart part state x).card + 1 : ℕ) *
        currentDefect G H host part threshold default state x ≤
      partDefectMass G H host part threshold default state (part x) s := by
  classical
  let P := assignedInPart part state x
  let S := insert x P
  let w := currentDefect G H host part threshold default state x
  let f := fun y =>
    realizedDefect G H host part threshold default state y ^ s
  have hw0 : 0 ≤ w := by
    exact FiniteDefect.defect_nonneg G _ _ _
  have hxnotP : x ∉ P := by
    intro hxin
    have hassigned : RandomGreedy.assigned state.core x :=
      ((mem_assignedInPart part state x x).mp (by simpa [P] using hxin)).1
    exact (hgood.assigned_iff x).mp hassigned hx
  have hSsub : S ⊆ Finset.univ.filter fun y => part y = part x := by
    intro y hy
    simp only [S, Finset.mem_insert] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hy with hyx | hyP
    · subst y
      rfl
    · exact ((mem_assignedInPart part state x y).mp (by simpa [P] using hyP)).2
  have hterm : ∀ y ∈ S, w ≤ f y := by
    intro y hy
    simp only [S, Finset.mem_insert] at hy
    rcases hy with hyx | hyP
    · subst y
      have hxunassigned : ¬RandomGreedy.assigned state.core x := by
        intro hassigned
        exact (hgood.assigned_iff x).mp hassigned hx
      simp only [f, realizedDefect, if_neg hxunassigned, w]
      by_cases hw : currentDefect G H host part threshold default state x = 0
      · simp [hw]
      · have hw1 : 1 ≤ currentDefect G H host part threshold default state x := by
          exact FiniteDefect.one_le_defect_of_ne_zero G hw
        have hp := pow_le_pow_right₀ hw1
          (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hs))
        simpa using hp
    · have hyP' : y ∈ assignedInPart part state x := by
        simpa [P] using hyP
      have hyassigned : RandomGreedy.assigned state.core y :=
        ((mem_assignedInPart part state x y).mp hyP').1
      have hypart : part y = part x :=
        ((mem_assignedInPart part state x y).mp hyP').2
      have hle : w ≤ state.core.defectSeen y :=
        hordered.ordered hyassigned hx hypart
      have hy0 : 0 ≤ state.core.defectSeen y := hw0.trans hle
      simp only [f, realizedDefect, if_pos hyassigned]
      by_cases hw : w = 0
      · simpa [hw] using pow_nonneg hy0 s
      · have hw1 : 1 ≤ w := by
          exact FiniteDefect.one_le_defect_of_ne_zero G hw
        have hy1 : 1 ≤ state.core.defectSeen y := hw1.trans hle
        have hp := pow_le_pow_right₀ hy1
          (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hs))
        exact hle.trans (by simpa using hp)
  have hnonneg : ∀ y ∈ (Finset.univ.filter fun y => part y = part x),
      y ∉ S → 0 ≤ f y := by
    intro y hy hnot
    by_cases hyassigned : RandomGreedy.assigned state.core y
    · have hypart : part y = part x := (Finset.mem_filter.mp hy).2
      have hle : w ≤ state.core.defectSeen y :=
        hordered.ordered hyassigned hx hypart
      simpa [f, realizedDefect, hyassigned] using pow_nonneg (hw0.trans hle) s
    · simp only [f, realizedDefect, if_neg hyassigned]
      exact pow_nonneg (FiniteDefect.defect_nonneg G _ _ _) s
  calc
    ((P.card + 1 : ℕ) : ℝ) * w = ∑ _y ∈ S, w := by
      simp [S, hxnotP]
    _ ≤ ∑ y ∈ S, f y := Finset.sum_le_sum fun y hy => hterm y hy
    _ ≤ ∑ y ∈ (Finset.univ.filter fun y => part y = part x), f y :=
      Finset.sum_le_sum_of_subset_of_nonneg hSsub hnonneg
    _ = partDefectMass G H host part threshold default state (part x) s := by
      rfl

/-- Local form of Lee's deterministic success criterion. -/
theorem choices_eq_unused_of_partDefectMass_le
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    (hthreshold : ∀ i, 0 < threshold i)
    (hpartSize : ∀ x, 2 * (RandomGreedy.partVertices part x).card ≤
      threshold (part x))
    {state : State α β} (hne : state.remaining.Nonempty)
    (hgood : GoodState G H host part default state)
    (hordered : DefectsOrdered G H host part threshold default state)
    (hmass : partDefectMass G H host part threshold default state
      (part (next G H host part threshold defaultTarget default state)) momentExponent ≤
        (threshold (part (next G H host part threshold defaultTarget default state)) : ℝ) / 2)
    (hexponent : 0 < momentExponent) :
    choices G H host part threshold defaultTarget default state =
      RandomGreedy.unusedCandidates G H host part default state.core
        (next G H host part threshold defaultTarget default state) := by
  let x := next G H host part threshold defaultTarget default state
  let P := assignedInPart part state x
  let j := P.card + 1
  have hx : x ∈ state.remaining :=
    next_mem G H host part threshold defaultTarget default state hne
  have hj : 0 < j := by simp [j]
  have hjle : j ≤ (RandomGreedy.partVertices part x).card := by
    simpa [j, P] using
      assignedInPart_card_add_one_le_partVertices_card G H host part default hx hgood
  have hθj : 2 * j ≤ threshold (part x) := by
    exact (Nat.mul_le_mul_left 2 hjle).trans (hpartSize x)
  have hmul : (j : ℝ) *
      currentDefect G H host part threshold default state x ≤
        (threshold (part x) : ℝ) / 2 := by
    exact (mul_currentDefect_le_partDefectMass G H host part threshold default
      hexponent hx hgood hordered).trans (by simpa [x] using hmass)
  let q : RandomGreedy.forwardNeighbors H x → β := fun y =>
    RandomGreedy.value default state.core y
  have hcard : 2 * j ≤
      (RandomGreedy.fullCandidates G H host part default state.core x).card := by
    have h := two_mul_le_commonNeighbors_card_of_mul_defect_le G q (host (part x))
      (hthreshold (part x)) hj hθj
    apply h
    simpa [currentDefect, q] using hmul
  have hfullNonempty :
      (RandomGreedy.fullCandidates G H host part default state.core x).Nonempty := by
    apply Finset.card_pos.mp
    omega
  have husedCard :
      (RandomGreedy.usedInPart part default state.core x).card ≤ P.card := by
    simpa [P] using usedInPart_card_le_assignedInPart_card part default state x
  have htwiceUsed :
      2 * (RandomGreedy.usedInPart part default state.core x).card ≤
        (RandomGreedy.fullCandidates G H host part default state.core x).card := by
    omega
  exact choices_eq_unused_of_two_used_le G H host part default state.core x
    hfullNonempty htwiceUsed

end AdaptiveGreedy
end Erdos163
