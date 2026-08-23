import ErdosProblems.Erdos245.Conic

open scoped BigOperators

namespace Erdos245Scratch

def chainGen {V : Type*} [AddCommGroup V] [Module ℚ V]
    (u : ℕ → V) (n : ℕ) : Fin (n + 1) → V :=
  Fin.cases (u 0) fun j : Fin n ↦ u (j + 1) - (2 : ℚ) • u j

private lemma chainGen_castSucc {V : Type*} [AddCommGroup V] [Module ℚ V]
    (u : ℕ → V) (n : ℕ) (i : Fin (n + 1)) :
    chainGen u (n + 1) i.castSucc = chainGen u n i := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · rfl

private lemma chainGen_last {V : Type*} [AddCommGroup V] [Module ℚ V]
    (u : ℕ → V) (n : ℕ) :
    chainGen u (n + 1) (Fin.last (n + 1)) =
      u (n + 1) - (2 : ℚ) • u n := by
  rfl

lemma exists_nonnegative_chain_coefficients
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (u : ℕ → V) (n : ℕ) :
    ∃ a : Fin (n + 1) → ℚ, (∀ i, 0 ≤ a i) ∧
      u n = ∑ i, a i • chainGen u n i := by
  induction n with
  | zero =>
      refine ⟨fun _ ↦ 1, fun _ ↦ by positivity, ?_⟩
      simp [chainGen]
  | succ n ih =>
      obtain ⟨a, ha, hrepr⟩ := ih
      let a' : Fin (n + 2) → ℚ := Fin.lastCases 1 (fun i ↦ 2 * a i)
      refine ⟨a', ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simp [a']
        · simp [a', ha]
      · rw [Fin.sum_univ_castSucc]
        simp only [a', Fin.lastCases_castSucc, Fin.lastCases_last,
          chainGen_castSucc, chainGen_last]
        simp_rw [mul_smul]
        rw [← Finset.smul_sum, ← hrepr]
        module

def chainGenInt {d : ℕ} (u : ℕ → Fin d → ℤ) (n : ℕ) :
    Fin (n + 1) → Fin d → ℤ :=
  Fin.cases (u 0) fun j : Fin n ↦ u (j + 1) - 2 • u j

lemma castVec_chainGenInt {d : ℕ} (u : ℕ → Fin d → ℤ) (n : ℕ)
    (i : Fin (n + 1)) :
    castVec (chainGenInt u n i) =
      chainGen (fun k ↦ castVec (u k)) n i := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · ext q
    simp [chainGenInt, chainGen, castVec, sub_eq_add_neg]

/-- The doubling-chain representation, reduced to linearly independent
nonzero support and with its initial coefficient bounded by Cramer's rule. -/
lemma exists_bounded_reduced_chain_coefficients
    {d : ℕ} (u : ℕ → Fin d → ℤ) (n : ℕ) (q : Fin d)
    (hq : ∀ i, u i q = 1)
    (B : Fin d → ℕ) (hB : ∀ j, 1 ≤ B j)
    (hgen : ∀ i j, (chainGenInt u n i j).natAbs ≤ B j)
    (hv : ∀ j, (u n j).natAbs ≤ B j) :
    ∃ b : Fin (n + 1) → ℚ,
      (∀ i, 0 ≤ b i) ∧
      castVec (u n) = ∑ i, b i • castVec (chainGenInt u n i) ∧
      0 < b 0 ∧
      b 0 ≤ ((d.factorial * ∏ j, B j : ℕ) : ℚ) := by
  classical
  obtain ⟨a, ha, harepr⟩ :=
    exists_nonnegative_chain_coefficients (fun k ↦ castVec (u k)) n
  have harepr' :
      castVec (u n) = ∑ i, a i • castVec (chainGenInt u n i) := by
    rw [harepr]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [castVec_chainGenInt]
  obtain ⟨b, hb, hbsum, hbli⟩ :=
    exists_nonnegative_linearIndependent_support
      (fun i ↦ castVec (chainGenInt u n i)) a ha
  have hrel :
      castVec (u n) = ∑ i, b i • castVec (chainGenInt u n i) := by
    rw [harepr', ← hbsum]
  have hgenq (i : Fin (n + 1)) :
      chainGenInt u n i q = if i = 0 then 1 else -1 := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [chainGenInt, hq]
    · have hsucc : (Fin.succ j : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero j
      simp [chainGenInt, hq, hsucc]
  have hcoord :
      (1 : ℚ) = ∑ i, b i * (chainGenInt u n i q : ℚ) := by
    have h := congrFun hrel q
    simpa only [castVec_apply, hq, Int.cast_one, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using h
  have hbzero : 0 < b 0 := by
    by_contra hnpos
    have hb0 : b 0 = 0 := le_antisymm (le_of_not_gt hnpos) (hb 0)
    have hterm (i : Fin (n + 1)) :
        b i * (chainGenInt u n i q : ℚ) ≤ 0 := by
      by_cases hi : i = 0
      · subst i
        simp [hb0]
      · rw [hgenq, if_neg hi]
        simp [hb i]
    have hsum :
        (∑ i, b i * (chainGenInt u n i q : ℚ)) ≤ 0 :=
      Finset.sum_nonpos fun i _hi ↦ hterm i
    linarith
  let i0 : ↥(nzSupport b) := ⟨0, (mem_nzSupport b 0).2 hbzero.ne'⟩
  have hrel_support :
      castVec (u n) =
        ∑ i : ↥(nzSupport b),
          b i.1 • castVec (chainGenInt u n i.1) := by
    calc
      castVec (u n) =
          ∑ i, b i • castVec (chainGenInt u n i) := hrel
      _ = ∑ i ∈ nzSupport b,
          b i • castVec (chainGenInt u n i) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _hi hnot
        have hbi : b i = 0 :=
          not_ne_iff.mp (mt (mem_nzSupport b i).mpr hnot)
        simp [hbi]
      _ = ∑ i : ↥(nzSupport b),
          b i.1 • castVec (chainGenInt u n i.1) := by
        rw [← (nzSupport b).sum_attach]
        rfl
  have hcoeff := coefficient_le_of_integral_linearIndependent
    (fun i : ↥(nzSupport b) ↦ chainGenInt u n i.1) (u n)
    (fun i : ↥(nzSupport b) ↦ b i.1) i0 hbli hrel_support B hB
    (fun i j ↦ hgen i.1 j) hv
  refine ⟨b, hb, hrel, hbzero, ?_⟩
  simpa [i0] using hcoeff

end Erdos245Scratch

