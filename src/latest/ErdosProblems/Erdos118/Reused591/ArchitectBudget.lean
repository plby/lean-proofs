import ErdosProblems.Erdos118.Reused591.ReplayBudget
import ErdosProblems.Erdos118.Reused591.ArchitectContinuation

namespace Erdos118.Reused591

/-!
# Finite next-request bounds for a fixed architect strategy

Nonpending histories on a finite numerical set form a finite set.
Their images under one fixed strategy therefore have bounded requested
sizes and conservative thresholds. No bound on arbitrary architect
requests is assumed; the fixed strategy is an explicit parameter.
-/

namespace Erdos591.Positive.Game.ArchitectBudget

variable {N : Set ℕ} {payoff : Bool → Board → Bool}

noncomputable def chosen (σ : (Concrete.game N payoff).ArchitectStrategy)
    (p : Concrete.Hist N) : Concrete.Hist N :=
  if hp : (Concrete.game N payoff).kind p = .architect then σ.move p hp else p

noncomputable def cost (σ : (Concrete.game N payoff).ArchitectStrategy)
    (b : Concrete.Hist N → ℕ) (p : Concrete.Hist N) : ℕ :=
  max (b p) (max (b (chosen σ p)) (chosen σ p).position.pendingSize)

noncomputable def bound (σ : (Concrete.game N payoff).ArchitectStrategy)
    (b : Concrete.Hist N → ℕ) (F : Finset ℕ) : ℕ :=
  max (F.sup id) ((ReplayBudget.finite_histories N F 0).toFinset.sup (cost σ b)) + 1

theorem cost_lt_bound (σ : (Concrete.game N payoff).ArchitectStrategy)
    (b : Concrete.Hist N → ℕ) (F : Finset ℕ) (p : Concrete.Hist N)
    (hF : ReplayBudget.used p ⊆ F) (hp : p.position.pending = none) :
    cost σ b p < bound σ b F := by
  have hsize : p.position.pendingSize ≤ 0 := by simp [Position.pendingSize, hp]
  have hmem : p ∈ (ReplayBudget.finite_histories N F 0).toFinset :=
    (ReplayBudget.finite_histories N F 0).mem_toFinset.mpr ⟨hF, hsize⟩
  exact (Finset.le_sup (f := cost σ b) hmem).trans_lt
    ((le_max_right _ _).trans_lt (Nat.lt_succ_self _))

theorem request_lt_bound (σ : (Concrete.game N payoff).ArchitectStrategy)
    (b : Concrete.Hist N → ℕ) (F : Finset ℕ) (p : Concrete.Hist N)
    (hF : ReplayBudget.used p ⊆ F) (hp : (Concrete.game N payoff).kind p = .architect) :
    b p < bound σ b F ∧ b (σ.move p hp) < bound σ b F ∧
      (σ.move p hp).position.pendingSize < bound σ b F := by
  have hnone := ((Concrete.kind_architect_iff payoff p).mp hp).1
  have hc := cost_lt_bound σ b F p hF hnone
  have hchosen : chosen σ p = σ.move p hp := by simp [chosen, hp]
  rw [cost, hchosen] at hc
  exact ⟨(le_max_left _ _).trans_lt hc,
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hc,
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hc⟩

theorem input_lt_bound (σ : (Concrete.game N payoff).ArchitectStrategy)
    (b : Concrete.Hist N → ℕ) (F : Finset ℕ) {x : ℕ} (hx : x ∈ F) : x < bound σ b F :=
  (Finset.le_sup (f := id) hx).trans_lt ((le_max_left _ _).trans_lt (Nat.lt_succ_self _))

theorem follow_request_lt_bound (σ : (Concrete.game N payoff).ArchitectStrategy)
    {H : Set ℕ} (b : Concrete.Hist N → ℕ) (F : Finset ℕ) {p q : Concrete.Hist N}
    (hF : ReplayBudget.used p ⊆ F) (hp : (Concrete.game N payoff).kind p = .architect)
    (hs : (Concrete.game N payoff).FollowStep σ H b p q) :
    b q < bound σ b F ∧ q.position.pendingSize < bound σ b F := by
  rw [hs.2 hp]
  exact (request_lt_bound σ b F p hF hp).2

theorem bound_mono (σ : (Concrete.game N payoff).ArchitectStrategy)
    (b : Concrete.Hist N → ℕ) {F E : Finset ℕ} (hFE : F ⊆ E) :
    bound σ b F ≤ bound σ b E := by
  have hh : (ReplayBudget.finite_histories N F 0).toFinset ⊆
      (ReplayBudget.finite_histories N E 0).toFinset := by
    intro p hp
    have h := (ReplayBudget.finite_histories N F 0).mem_toFinset.mp hp
    exact (ReplayBudget.finite_histories N E 0).mem_toFinset.mpr ⟨h.1.trans hFE, h.2⟩
  exact Nat.succ_le_succ (max_le_max (Finset.sup_mono hFE) (Finset.sup_mono hh))

#print axioms request_lt_bound
#print axioms bound_mono

end Erdos591.Positive.Game.ArchitectBudget

end Erdos118.Reused591
