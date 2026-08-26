import ErdosProblems.Erdos1148.LiftForwardClose
import Mathlib.Data.Fintype.BigOperators

/-! # Multiplying coherent lift-cover bounds under finite refinement -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups BigOperators

def LiftCoverBound (η S : ℝ) (E : Set SL(2, ℝ)) (M : ℝ) : Prop :=
  ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
    (N : ℝ) ≤ M ∧ (⋃ i, B i) = E ∧ ∀ i, LiftForwardClose η S (B i)

theorem LiftCoverBound.mono_bound {η S M K : ℝ} {E : Set SL(2, ℝ)}
    (hE : LiftCoverBound η S E M) (hMK : M ≤ K) : LiftCoverBound η S E K := by
  obtain ⟨N, B, hN, hcov, hclose⟩ := hE
  exact ⟨N, B, hN.trans hMK, hcov, hclose⟩

theorem LiftForwardClose.coverBound {η S : ℝ} {E : Set SL(2, ℝ)}
    (hE : LiftForwardClose η S E) : LiftCoverBound η S E 1 := by
  refine ⟨1, fun _ => E, by norm_num, ?_, fun _ => hE⟩
  apply Set.Subset.antisymm
  · intro g hg
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    exact hi
  · intro g hg
    exact Set.mem_iUnion.mpr ⟨(0 : Fin 1), hg⟩

theorem LiftCoverBound.refine {η S T M K : ℝ} {E : Set SL(2, ℝ)}
    (hE : LiftCoverBound η S E M) (hK : 0 ≤ K)
    (hrefine : ∀ F ⊆ E, LiftForwardClose η S F → LiftCoverBound η T F K) :
    LiftCoverBound η T E (M * K) := by
  classical
  obtain ⟨N, B, hN, hcov, hB⟩ := hE
  have hsub (i : Fin N) : B i ⊆ E := by
    intro g hg
    rw [← hcov]
    exact Set.mem_iUnion.mpr ⟨i, hg⟩
  have hex (i : Fin N) := hrefine (B i) (hsub i) (hB i)
  choose n C hn hC hclose using hex
  let ι := (i : Fin N) × Fin (n i)
  let e := Fintype.equivFin ι
  let D : Fin (Fintype.card ι) → Set SL(2, ℝ) := fun i => C (e.symm i).1 (e.symm i).2
  refine ⟨Fintype.card ι, D, ?_, ?_, ?_⟩
  · change (Fintype.card ((i : Fin N) × Fin (n i)) : ℝ) ≤ M * K
    simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    calc
      ∑ i : Fin N, (n i : ℝ) ≤ ∑ _i : Fin N, K := Finset.sum_le_sum (fun i _ => hn i)
      _ = (N : ℝ) * K := by simp
      _ ≤ M * K := mul_le_mul_of_nonneg_right hN hK
  · apply Set.Subset.antisymm
    · intro g hg
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
      apply hsub (e.symm i).1
      rw [← hC (e.symm i).1]
      exact Set.mem_iUnion.mpr ⟨(e.symm i).2, hi⟩
    · intro g hg
      rw [← hcov] at hg
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
      rw [← hC i] at hi
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
      refine Set.mem_iUnion.mpr ⟨e ⟨i, j⟩, ?_⟩
      change g ∈ C (e.symm (e ⟨i, j⟩)).1 (e.symm (e ⟨i, j⟩)).2
      have he : e.symm (e ⟨i, j⟩) = ⟨i, j⟩ := e.symm_apply_apply _
      rw [he]
      exact hj
  · intro i
    exact hclose (e.symm i).1 (e.symm i).2

theorem LiftCoverBound.iterate {η M : ℝ} {E : Set SL(2, ℝ)}
    (time cost : ℕ → ℝ) (hcost : ∀ k, 0 ≤ cost k)
    (hstart : LiftCoverBound η (time 0) E M)
    (hstep : ∀ k, ∀ F ⊆ E, LiftForwardClose η (time k) F →
      LiftCoverBound η (time (k + 1)) F (cost k)) (n : ℕ) :
    LiftCoverBound η (time n) E (M * ∏ k ∈ Finset.range n, cost k) := by
  induction n with
  | zero => simpa only [Finset.range_zero, Finset.prod_empty, mul_one] using hstart
  | succ n ih =>
      have h := ih.refine (hcost n) (hstep n)
      simpa only [Finset.prod_range_succ, mul_assoc] using h

theorem LiftCoverBound.iterate_upto {η M : ℝ} {E : Set SL(2, ℝ)}
    (time cost : ℕ → ℝ) (hcost : ∀ k, 0 ≤ cost k)
    (hstart : LiftCoverBound η (time 0) E M) (n : ℕ) :
    (∀ k < n, ∀ F ⊆ E, LiftForwardClose η (time k) F →
      LiftCoverBound η (time (k + 1)) F (cost k)) →
    LiftCoverBound η (time n) E (M * ∏ k ∈ Finset.range n, cost k) := by
  induction n with
  | zero =>
      intro _
      simpa only [Finset.range_zero, Finset.prod_empty, mul_one] using hstart
  | succ n ih =>
      intro hstep
      have hprev := ih (fun k hk => hstep k (Nat.lt_trans hk (Nat.lt_succ_self n)))
      have h := hprev.refine (hcost n) (hstep n (Nat.lt_succ_self n))
      simpa only [Finset.prod_range_succ, mul_assoc] using h

end Erdos1148.DukeArithmetic
