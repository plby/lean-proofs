import ErdosProblems.Erdos117.BranchRestriction
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Selecting and composing branch stages

The stage cliques are chosen sequentially. Only the already-selected
anchors and interaction kernels enter the next restriction.
-/

namespace Erdos117

open scoped commutatorElement BigOperators

def selectedPrevious {M N : ℕ} (e : Fin M → Fin N) (k : Fin M) (i : Fin k.val) : Fin N :=
  e ⟨i, lt_trans i.2 k.2⟩

variable {G : Type*} [Group G] {p : ℕ} {D : CentralChain G p}

namespace CentralBranch

variable (B : CentralBranch D)

noncomputable def selectedInteractionSum {M : ℕ} (e : Fin M → Fin B.length) (k : Fin M) : ℕ :=
  ∑ i : Fin k.val, B.interactionRank (selectedPrevious e k i) (e k)

/-- The simultaneous family is constructed by induction on the number of
selected stages; the final stage centralizes exactly the previously chosen
anchors. -/
theorem exists_selected_stage_cliques [Finite G] [Fact p.Prime]
    {n : ℕ} (hn : NoncommutingBound G n) {M : ℕ}
    (e : Fin M → Fin B.length) (he : StrictMono e) :
    ∃ C : (k : Fin M) → B.StageClique (e k),
      (∀ i j, i < j → ∀ v, Commute ((C i).point 0) ((C j).point v)) ∧
      (∀ i j, i < j → ∀ u v,
        ⁅(C i).point u, (C j).point v⁆ ∈ D.term (e i + 1)) ∧
      ∀ k, scalarCreditRate p * B.halfRank (e k) ≤ (C k).credit + scalarDefect p +
        scalarCreditRate p * (B.selectedInteractionSum e k +
          k.val * Nat.clog p ((2 * n) ^ 2)) := by
  classical
  induction M with
  | zero =>
    refine ⟨fun i => Fin.elim0 i, ?_, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
  | succ M ih =>
    let e' : Fin M → Fin B.length := fun i => e i.castSucc
    have he' : StrictMono e' := fun i j hij => he hij
    obtain ⟨C, hanchor, hlayer, hcredit⟩ := ih e' he'
    have hr : ∀ i : Fin M, e' i ≤ e (Fin.last M) := fun i =>
      (he (Fin.castSucc_lt_last i)).le
    obtain ⟨C_last, hlast_anchor, hlast_layer, hlast_credit⟩ :=
      B.exists_stage_clique hn (e (Fin.last M)) e' hr (fun i => (C i).point 0)
    let C_all : (k : Fin (M + 1)) → B.StageClique (e k) := Fin.snoc C C_last
    have hinit (i : Fin M) : C_all i.castSucc = C i :=
      Fin.snoc_castSucc (α := fun k : Fin (M + 1) => B.StageClique (e k)) C_last C i
    have hlast : C_all (Fin.last M) = C_last :=
      Fin.snoc_last (α := fun k : Fin (M + 1) => B.StageClique (e k)) C_last C
    refine ⟨C_all, ?_, ?_, ?_⟩
    · intro i j
      cases j using Fin.lastCases with
      | last =>
        cases i using Fin.lastCases with
        | last => intro h; exact (lt_irrefl _ h).elim
        | cast i =>
          rw [hinit i, hlast]
          intro h v
          exact hlast_anchor i v
      | cast j =>
        cases i using Fin.lastCases with
        | last => intro h; exact (not_lt_of_ge (Fin.castSucc_lt_last j).le h).elim
        | cast i =>
          rw [hinit i, hinit j]
          exact hanchor i j
    · intro i j
      cases j using Fin.lastCases with
      | last =>
        cases i using Fin.lastCases with
        | last => intro h; exact (lt_irrefl _ h).elim
        | cast i =>
          rw [hinit i, hlast]
          intro h u v
          exact hlast_layer i ⟨(C i).point u, (C i).mem_group u⟩ v
      | cast j =>
        cases i using Fin.lastCases with
        | last => intro h; exact (not_lt_of_ge (Fin.castSucc_lt_last j).le h).elim
        | cast i =>
          rw [hinit i, hinit j]
          exact hlayer i j
    · intro k
      cases k using Fin.lastCases with
      | last =>
        rw [hlast]
        change scalarCreditRate p * B.halfRank (e (Fin.last M)) ≤
          C_last.credit + scalarDefect p + scalarCreditRate p *
            ((∑ i : Fin M, B.interactionRank (e' i) (e (Fin.last M))) +
              M * Nat.clog p ((2 * n) ^ 2))
        simpa only [Fintype.card_fin] using hlast_credit
      | cast k =>
        rw [hinit k]
        exact hcredit k

/-- Corollary 5.6, with an explicit integer error budget. The estimate is
valid for every increasing selection of stages, including the empty one. -/
theorem selected_stage_credit_bound [Finite G] [Fact p.Prime]
    (hG : commutator G ≤ Subgroup.center G) {n : ℕ} (hn : NoncommutingBound G n)
    {M : ℕ} (e : Fin M → Fin B.length) (he : StrictMono e) :
    scalarCreditRate p * (∑ k, B.halfRank (e k)) ≤
      n - 1 + M * scalarDefect p + scalarCreditRate p *
        ((∑ k, B.selectedInteractionSum e k) + M * M * Nat.clog p ((2 * n) ^ 2)) := by
  classical
  obtain ⟨C, hanchor, hlayer, hcredit⟩ := B.exists_selected_stage_cliques hn e he
  have htotal := layered_credit_le_of_fin hG hn (fun k => (C k).credit)
    (fun k => (C k).point) (fun k => D.term (e k + 1)) (fun k => (C k).leading)
    hanchor hlayer
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hcredit k)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hc : (∑ k, (C k).credit) ≤ n - 1 := by omega
  have hlevels : (∑ k : Fin M, k.val) ≤ M * M := by
    calc
      (∑ k : Fin M, k.val) ≤ ∑ _k : Fin M, M :=
        Finset.sum_le_sum (fun k _ => Nat.le_of_lt k.2)
      _ = M * M := by simp
  refine hsum.trans ?_
  exact Nat.add_le_add (Nat.add_le_add_right hc _)
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ hlevels) _))

end CentralBranch

end Erdos117
