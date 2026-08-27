/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.MasterTypicalityQuasiCaps
import ErdosProblems.Erdos207.BoundedPatternUnionTail

/-! # Finite common events for the local-degree and quasi-moment typicality tests -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def futureLevelPairs {ell : ℕ} (next : Fin (ell+1)) : Finset (Fin ell × Fin (ell+1)) :=
  univ.filter fun a ↦ next.val ≤ a.1.val ∧ (a.2 = a.1.castSucc ∨ a.2 = a.1.succ)

theorem mem_futureLevelPairs_iff {ell : ℕ} (next : Fin (ell+1)) (a : Fin ell × Fin (ell+1)) :
    a ∈ futureLevelPairs next ↔ next.val ≤ a.1.val ∧ (a.2 = a.1.castSucc ∨ a.2 = a.1.succ) := by
  simp only [futureLevelPairs, mem_filter, mem_univ, true_and]

theorem card_futureLevelPairs_le {ell : ℕ} (next : Fin (ell+1)) :
    (futureLevelPairs next).card ≤ ell * (ell+1) := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using card_le_univ (futureLevelPairs next)

def LocalFutureDegreeCaps
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (next : Fin (ell+1)) (G : SimpleGraph V) (M : TripleSystemOn V)
    (p eta epsilon : ℝ≥0) (h : ℕ) : Prop :=
  ∀ a ∈ futureLevelPairs next, ∀ v ∈ W.U a.1.castSucc,
    ((neighborsIn G (W.U a.2) v \
      neighborsIn (updatedStageGraph G (W.U next) M) (W.U a.2) v).card : ℝ≥0) ≤
      epsilon * p ^ h * eta ^ (h^2) * (W.U a.2).card

def FutureQuasiCaps
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (next : Fin (ell+1)) (F : ForbiddenFamilyOn V) (Γ : SimpleGraph V)
    (I D : TripleSystemOn V) (p eta epsilon : ℝ≥0) (h : ℕ) : Prop :=
  ∀ a ∈ futureLevelPairs next, ∀ Q : BoundedGraphPattern V h, ∀ e ∈ graphEdges Q.1,
    ((sourceQuasiObstructedVertices (W.prefix a.1.castSucc) F e (W.U a.2)
      (graphSupportFinset Q.1) Γ I D).card : ℝ≥0) ≤
      epsilon * p ^ (graphSupportFinset Q.1).card * eta ^ (graphEdges Q.1).card * (W.U a.2).card

theorem FiniteLaw.probability_not_localFutureDegreeCaps_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (next : Fin (ell+1))
    (G : Ω → SimpleGraph V) (M : Ω → TripleSystemOn V) (p eta epsilon error : ℝ≥0) (h : ℕ)
    (hpoint : ∀ a ∈ futureLevelPairs next, ∀ v ∈ W.U a.1.castSucc,
      L.probability (fun ω ↦ epsilon * p ^ h * eta ^ (h^2) * (W.U a.2).card <
        (neighborsIn (G ω) (W.U a.2) v \
          neighborsIn (updatedStageGraph (G ω) (W.U next) (M ω)) (W.U a.2) v).card) ≤ error) :
    L.probability (fun ω ↦ ¬ LocalFutureDegreeCaps W next (G ω) (M ω) p eta epsilon h) ≤
      (ell * (ell+1) : ℕ) * Fintype.card V * error := by
  let Bad := fun a : Fin ell × Fin (ell+1) ↦ fun ω ↦ ∃ v ∈ W.U a.1.castSucc,
    epsilon * p ^ h * eta ^ (h^2) * (W.U a.2).card <
      (neighborsIn (G ω) (W.U a.2) v \
        neighborsIn (updatedStageGraph (G ω) (W.U next) (M ω)) (W.U a.2) v).card
  have hpair : ∀ a ∈ futureLevelPairs next, L.probability (Bad a) ≤ Fintype.card V * error := by
    intro a ha
    calc
      _ ≤ ∑ v ∈ W.U a.1.castSucc, L.probability (fun ω ↦
          epsilon * p ^ h * eta ^ (h^2) * (W.U a.2).card <
            (neighborsIn (G ω) (W.U a.2) v \
              neighborsIn (updatedStageGraph (G ω) (W.U next) (M ω)) (W.U a.2) v).card) :=
        L.probability_exists_le _ _
      _ ≤ ∑ _v ∈ W.U a.1.castSucc, error := sum_le_sum (hpoint a ha)
      _ = (W.U a.1.castSucc).card * error := by simp
      _ ≤ _ := by gcongr; exact_mod_cast card_le_univ (W.U a.1.castSucc)
  have hb := (L.probability_exists_le (futureLevelPairs next) Bad).trans (sum_le_sum hpair)
  have hcover : L.probability (fun ω ↦ ¬ LocalFutureDegreeCaps W next (G ω) (M ω) p eta epsilon h) ≤
      L.probability (fun ω ↦ ∃ a ∈ futureLevelPairs next, Bad a ω) := by
    apply L.probability_mono
    intro ω hω
    simpa only [LocalFutureDegreeCaps, Bad, not_forall, not_le, exists_prop] using hω
  apply (hcover.trans hb).trans
  simp only [sum_const, nsmul_eq_mul]
  calc
    _ ≤ ((ell * (ell+1) : ℕ) : ℝ≥0) * (Fintype.card V * error) := by
      gcongr
      exact_mod_cast card_futureLevelPairs_le next
    _ = _ := (mul_assoc _ _ _).symm

theorem FiniteLaw.masterTypicalityLoss_probability_of_local_quasi
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (k next : Fin (ell+1)) (F : ForbiddenFamilyOn V)
    (Γ : SimpleGraph V) (G : Ω → SimpleGraph V) (A I D M : Ω → TripleSystemOn V)
    (p eta xi xi' epsilon errorDegree errorQuasi : ℝ≥0) (h : ℕ)
    (hold : L.SupportedOn fun ω ↦ IsMasterStagePointwiseGood W k F (G ω) (A ω) (I ω) (D ω) p eta xi h)
    (hstep : L.SupportedOn fun ω ↦ IsMasterCoverStep F (G ω) (W.U next) (A ω) (I ω) (D ω) (M ω))
    (hbase : ∀ ω, G ω ≤ Γ) (hp : p ≤ 1) (heta : eta ≤ 1) (hh : 1 ≤ h)
    (hepsilon : (1+h+h^2 : ℕ) * epsilon ≤ xi' - xi)
    (hsupport : ∀ a ∈ futureLevelPairs next,
      (h : ℝ≥0) ≤ epsilon * p ^ h * eta ^ (h^2) * (W.U a.2).card)
    (hdegree : L.probability (fun ω ↦ ¬ LocalFutureDegreeCaps W next (G ω) (M ω) p eta epsilon h) ≤ errorDegree)
    (hquasi : L.probability (fun ω ↦ ¬ FutureQuasiCaps W next F Γ (I ω) (D ω ∪ M ω) p eta epsilon h) ≤ errorQuasi) :
    1 - (errorDegree + errorQuasi) ≤ L.probability (fun ω ↦
      MasterTypicalityLossEvent W next F (G ω) (A ω) (I ω) (D ω) (M ω) p eta xi xi' h) := by
  let Good := fun ω ↦ LocalFutureDegreeCaps W next (G ω) (M ω) p eta epsilon h ∧
    FutureQuasiCaps W next F Γ (I ω) (D ω ∪ M ω) p eta epsilon h
  have hbad : L.probability (fun ω ↦ ¬ Good ω) ≤ errorDegree + errorQuasi := by
    have hb := L.probability_or_le
      (fun ω ↦ ¬ LocalFutureDegreeCaps W next (G ω) (M ω) p eta epsilon h)
      (fun ω ↦ ¬ FutureQuasiCaps W next F Γ (I ω) (D ω ∪ M ω) p eta epsilon h)
    have hevent : (fun ω ↦ ¬ Good ω) = (fun ω ↦
        ¬ LocalFutureDegreeCaps W next (G ω) (M ω) p eta epsilon h ∨
        ¬ FutureQuasiCaps W next F Γ (I ω) (D ω ∪ M ω) p eta epsilon h) := by
      funext ω
      exact propext not_and_or
    rw [hevent]
    exact hb.trans (add_le_add hdegree hquasi)
  have hgood : 1 - (errorDegree + errorQuasi) ≤ L.probability Good := by
    rw [L.probability_not Good] at hbad
    exact tsub_le_iff_tsub_le.mp hbad
  apply hgood.trans
  have hstruct : L.SupportedOn (fun ω ↦
    IsMasterStagePointwiseGood W k F (G ω) (A ω) (I ω) (D ω) p eta xi h ∧
      IsMasterCoverStep F (G ω) (W.U next) (A ω) (I ω) (D ω) (M ω)) :=
    fun ω hω ↦ ⟨hold ω hω, hstep ω hω⟩
  apply L.probability_mono_of_supported hstruct
  intro ω hb hg
  apply masterTypicalityLossEvent_of_local_quasi_caps hb.1 hb.2 (hbase ω) hp heta hh hepsilon
  · intro i hi iStar hStar
    exact hsupport (i, iStar) ((mem_futureLevelPairs_iff next _).mpr ⟨hi, hStar⟩)
  · intro i hi iStar hStar v hv
    exact hg.1 (i, iStar) ((mem_futureLevelPairs_iff next _).mpr ⟨hi, hStar⟩) v hv
  · intro i hi iStar hStar Q hQ e he
    exact hg.2 (i, iStar) ((mem_futureLevelPairs_iff next _).mpr ⟨hi, hStar⟩) ⟨Q, hQ⟩ e he

end

end Erdos207
