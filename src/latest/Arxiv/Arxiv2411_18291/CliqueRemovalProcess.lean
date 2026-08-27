import Arxiv.Arxiv2411_18291.RemainingCliques
import Arxiv.Arxiv2411_18291.FiniteHistoryStep

/-!
# The actual random clique-removal process

At every step, choose uniformly among the remaining cliques. If there
are none, return an empty marker. The trajectory measure is constructed
from these finite transition laws, not postulated.
-/

open Finset MeasureTheory ProbabilityTheory Preorder

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

def State (V : Type*) (q : ℕ) := Option (Block V q)

def chosen {V : Type*} {q : ℕ} (Q : Block V q) : State V q := some Q

def aborted (V : Type*) (q : ℕ) : State V q := none

instance {V : Type*} [Fintype V] {q : ℕ} : Fintype (State V q) := by
  classical
  exact inferInstanceAs (Fintype (Option (Block V q)))

instance {V : Type*} {q : ℕ} : MeasurableSpace (State V q) := ⊤

instance {V : Type*} {q : ℕ} : MeasurableSingletonClass (State V q) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

variable {V : Type*} [Fintype V] [DecidableEq V] {q r n : ℕ}

def historyAt (h : FiniteHistoryProcess.History (State V q) n) (j : ℕ) : State V q :=
  if hj : j + 1 ≤ n then h ⟨j + 1, mem_Iic.mpr hj⟩ else none

def historyCliques (h : FiniteHistoryProcess.History (State V q) n) : Finset (Block V q) :=
  (range n).biUnion fun j => (historyAt h j).toFinset

def trajectoryCliques (ω : ℕ → State V q) (n : ℕ) : Finset (Block V q) :=
  (range n).biUnion fun j => (ω (j + 1)).toFinset

omit [Fintype V] [DecidableEq V] in
theorem historyAt_prefix (ω : ℕ → State V q) (n j : ℕ) (hj : j < n) :
    historyAt (frestrictLe n ω) j = ω (j + 1) := by
  simp [historyAt, show j + 1 ≤ n by omega, frestrictLe_apply]

omit [Fintype V] in
theorem historyCliques_prefix (ω : ℕ → State V q) (n : ℕ) :
    historyCliques (frestrictLe n ω) = trajectoryCliques ω n := by
  apply biUnion_congr rfl
  intro j hj
  rw [historyAt_prefix ω n j (mem_range.mp hj)]

omit [Fintype V] in
@[simp] theorem trajectoryCliques_zero (ω : ℕ → State V q) : trajectoryCliques ω 0 = ∅ := by
  simp [trajectoryCliques]

omit [Fintype V] in
theorem trajectoryCliques_succ (ω : ℕ → State V q) (n : ℕ) :
    trajectoryCliques ω (n + 1) = trajectoryCliques ω n ∪ (ω (n + 1)).toFinset := by
  simp [trajectoryCliques, range_add_one, union_comm]

def step (r : ℕ) (H : Finset (Block V q)) (n : ℕ)
    (h : FiniteHistoryProcess.History (State V q) n) : PMF (State V q) := by
  classical
  exact if hs : (remainingCliques r H (historyCliques h)).Nonempty then
    (PMF.uniformOfFinset (remainingCliques r H (historyCliques h)) hs).map
      chosen
  else PMF.pure (aborted V q)

def probability (r : ℕ) (H : Finset (Block V q)) : Measure (ℕ → State V q) :=
  FiniteHistoryProcess.probability (aborted V q) (step r H)

instance probability_isProbability (r : ℕ) (H : Finset (Block V q)) :
    IsProbabilityMeasure (probability r H) := by
  unfold probability
  exact FiniteHistoryProcess.probability_isProbability (aborted V q) (step r H)

theorem step_some_mem_support_iff (H : Finset (Block V q))
    (h : FiniteHistoryProcess.History (State V q) n) (Q : Block V q) :
    (some Q : State V q) ∈ (step r H n h).support ↔
      Q ∈ remainingCliques r H (historyCliques h) := by
  classical
  by_cases hs : (remainingCliques r H (historyCliques h)).Nonempty
  · rw [step, dif_pos hs]
    constructor
    · intro hQ
      obtain ⟨P, hP, hPQ⟩ := (PMF.mem_support_map_iff _ _ _).mp hQ
      have heq : P = Q := Option.some.inj hPQ
      subst P
      exact (PMF.mem_support_uniformOfFinset_iff hs Q).mp hP
    · intro hQ
      apply (PMF.mem_support_map_iff _ _ _).mpr
      exact ⟨Q, (PMF.mem_support_uniformOfFinset_iff hs Q).mpr hQ, rfl⟩
  · have heq := not_nonempty_iff_eq_empty.mp hs
    rw [step, dif_neg hs, heq]
    constructor
    · intro hQ
      have hnone := (PMF.mem_support_pure_iff (aborted V q) (some Q : State V q)).mp hQ
      exact (Option.some_ne_none Q hnone).elim
    · intro hQ
      exact (notMem_empty Q hQ).elim

theorem step_choose_of_nonempty (H : Finset (Block V q))
    (h : FiniteHistoryProcess.History (State V q) n)
    (hs : (remainingCliques r H (historyCliques h)).Nonempty)
    (a : State V q) (ha : a ∈ (step r H n h).support) :
    ∃ Q, a = some Q ∧ Q ∈ remainingCliques r H (historyCliques h) := by
  classical
  rw [step, dif_pos hs] at ha
  obtain ⟨Q, hQ, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
  exact ⟨Q, heq.symm, (PMF.mem_support_uniformOfFinset_iff hs Q).mp hQ⟩

end Arxiv2411_18291.CliqueRemovalProcess
