import ErdosProblems.Erdos941.Avoidance
import ErdosProblems.Erdos941.NonbacktrackingReach

/-! # Uniform avoidance bounds for forbidden turns -/

namespace Erdos941

section CanHit

variable {α : Type*} (step : α → Fin 3 → α) (target : α → Prop) [DecidablePred target]

theorem CanHit.succ {n : ℕ} {s : α} (h : CanHit step target n s) :
    CanHit step target (n + 1) s := by
  induction n generalizing s with
  | zero => exact Or.inl h
  | succ n ih =>
    rcases h with h | ⟨i, hi⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, ih hi⟩

theorem CanHit.mono {n m : ℕ} (hnm : n ≤ m) {s : α} (h : CanHit step target n s) :
    CanHit step target m s := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact ih.succ step target

theorem exists_uniform_canHit [Finite α] (h : ∀ s : α, ∃ n, CanHit step target n s) :
    ∃ K : ℕ, 0 < K ∧ ∀ s : α, CanHit step target K s := by
  classical
  letI := Fintype.ofFinite α
  choose k hk using h
  refine ⟨(∑ s : α, k s) + 1, by omega, ?_⟩
  intro s
  apply (hk s).mono step target
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)).trans (by omega)

end CanHit

section Edges

variable {X : Type*} (rot : Axis → X → X) (bad : (Axis × X) → Fin 3 → Prop)

noncomputable def hitFlagStep (s : (Axis × X) × Bool) (i : Fin 3) : (Axis × X) × Bool :=
  (turnStateStep rot s.1 i, s.2 || @decide (bad s.1 i) (Classical.propDecidable _))

def hitFlagTarget (s : (Axis × X) × Bool) : Prop := s.2 = true

instance : DecidablePred (@hitFlagTarget X) := fun s => inferInstanceAs (Decidable (s.2 = true))

theorem canHitFlag_of_bad (s : Axis × X) (b : Bool) {i : Fin 3} (hi : bad s i) :
    CanHit (hitFlagStep rot bad) hitFlagTarget 1 (s, b) := by
  classical
  apply Or.inr
  refine ⟨i, ?_⟩
  change (b || decide (bad s i)) = true
  simp only [decide_eq_true hi, Bool.or_true]

theorem exists_canHitFlag_of_reach {s t : Axis × X} (h : TurnReach rot s t)
    (ht : ∃ i : Fin 3, bad t i) :
    ∀ b : Bool, ∃ n, CanHit (hitFlagStep rot bad) hitFlagTarget n (s, b) := by
  classical
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro b
    obtain ⟨i, hi⟩ := ht
    exact ⟨1, canHitFlag_of_bad rot bad _ b hi⟩
  | @head s u hed hpath ih =>
    intro b
    obtain ⟨i, hi⟩ := hed
    obtain ⟨n, hn⟩ := ih (b || @decide (bad s i) (Classical.propDecidable _))
    refine ⟨n + 1, Or.inr ⟨i, ?_⟩⟩
    change CanHit (hitFlagStep rot bad) hitFlagTarget n
      (turnStateStep rot s i, b || decide (bad s i))
    rw [hi]
    exact hn

theorem exists_uniform_edge_avoidance [Finite X]
    (h : ∀ s : Axis × X, ∃ t : Axis × X, TurnReach rot s t ∧ ∃ i, bad t i) :
    ∃ K : ℕ, 0 < K ∧ ∀ (j : ℕ) (s : (Axis × X) × Bool),
      avoidanceCount (hitFlagStep rot bad) hitFlagTarget (K * j) s ≤ (3 ^ K - 1) ^ j := by
  obtain ⟨K, hK, hhit⟩ := exists_uniform_canHit (hitFlagStep rot bad) hitFlagTarget (by
    rintro ⟨s, b⟩
    obtain ⟨t, hst, hi⟩ := h s
    exact exists_canHitFlag_of_reach rot bad hst hi b)
  exact ⟨K, hK, avoidanceCount_block_bound (hitFlagStep rot bad) hitFlagTarget hhit⟩

end Edges

end Erdos941
