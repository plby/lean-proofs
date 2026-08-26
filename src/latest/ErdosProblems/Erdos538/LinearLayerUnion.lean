import ErdosProblems.Erdos538.IntegerLinearLayer
import ErdosProblems.Erdos538.LayerUnionLower

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538

open ArithmeticFunction

/-- Combining the independently admissible exact layers loses only the worst
linear factor `128K`, not a sum of representation caps. -/
theorem exists_admissible_lowSquarefreeLayers_linear
    (N K : ℕ) :
    ∃ A : Finset ℕ,
      Admissible 2 N A ∧
      A ⊆ lowSquarefreeLayers N K ∧
      (∑ k ∈ Finset.Icc 1 K,
          reciprocalMassNN (squarefreePrimeLayer N k)) ≤
        (128 * K) • reciprocalMassNN A := by
  classical
  let ks := Finset.Icc 1 K
  have hex : ∀ k ∈ ks, ∃ A : Finset ℕ,
      Admissible 2 N A ∧ A ⊆ squarefreePrimeLayer N k ∧
      reciprocalMassNN (squarefreePrimeLayer N k) ≤
        (128 * k) • reciprocalMassNN A := by
    intro k hk
    by_cases hkone : k = 1
    · subst k
      obtain ⟨A, hAdm, hsub, hmass⟩ :=
        exists_admissible_squarefreeLayer_quarter_sq_with_subset N 1 (by omega)
      refine ⟨A, hAdm, hsub, hmass.trans ?_⟩
      simp only [nsmul_eq_mul]
      gcongr
      norm_num
    · exact exists_admissible_squarefreeLayer_linear_with_subset N k (by
        have hkpos := (Finset.mem_Icc.mp hk).1
        omega)
  let fam : ℕ → Finset ℕ := fun k =>
    if hk : k ∈ ks then Classical.choose (hex k hk) else ∅
  have hprops (k : ℕ) (hk : k ∈ ks) :
      Admissible 2 N (fam k) ∧ fam k ⊆ squarefreePrimeLayer N k ∧
      reciprocalMassNN (squarefreePrimeLayer N k) ≤
        (128 * k) • reciprocalMassNN (fam k) := by
    simp only [fam, dif_pos hk]
    exact Classical.choose_spec (hex k hk)
  have hAdm (k : ℕ) (hk : k ∈ ks) : Admissible 2 N (fam k) :=
    (hprops k hk).1
  have hsub (k : ℕ) (hk : k ∈ ks) :
      fam k ⊆ squarefreePrimeLayer N k := (hprops k hk).2.1
  have hmass (k : ℕ) (hk : k ∈ ks) :
      reciprocalMassNN (squarefreePrimeLayer N k) ≤
        (128 * k) • reciprocalMassNN (fam k) := (hprops k hk).2.2
  let A := ks.biUnion fam
  have hdisj : (ks : Set ℕ).PairwiseDisjoint fam := by
    intro i hi j hj hij
    change Disjoint (fam i) (fam j)
    rw [Finset.disjoint_left]
    intro a hai haj
    have hli := hsub i hi hai
    have hlj := hsub j hj haj
    have hci : a.primeFactors.card = i := (Finset.mem_filter.mp hli).2.2
    have hcj : a.primeFactors.card = j := (Finset.mem_filter.mp hlj).2.2
    exact hij (hci.symm.trans hcj)
  have hAsub : A ⊆ lowSquarefreeLayers N K := by
    intro a ha
    obtain ⟨k, hk, hak⟩ := Finset.mem_biUnion.mp ha
    apply Finset.mem_biUnion.mpr
    exact ⟨k, by simpa [ks] using hk, hsub k hk hak⟩
  have hrange : ∀ a ∈ A, 1 ≤ a ∧ a ≤ N := by
    intro a ha
    obtain ⟨k, hk, hak⟩ := Finset.mem_biUnion.mp ha
    have hla := hsub k hk hak
    exact Finset.mem_Icc.mp (Finset.mem_filter.mp hla).1
  have hslice (j : ℕ) :
      omegaSlice A j = if j ∈ ks then fam j else ∅ := by
    ext a
    by_cases hj : j ∈ ks
    · simp only [if_pos hj, omegaSlice, Finset.mem_filter]
      constructor
      · rintro ⟨haA, homega⟩
        obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp haA
        have hli := hsub i hi hai
        have hsquare : Squarefree a := (Finset.mem_filter.mp hli).2.1
        have hcard : a.primeFactors.card = i :=
          (Finset.mem_filter.mp hli).2.2
        have homega : cardFactors a = i :=
          (cardFactors_eq_primeFactors_card_of_squarefree hsquare).trans hcard
        have hij : i = j := by omega
        simpa [hij] using hai
      · intro haj
        refine ⟨Finset.mem_biUnion.mpr ⟨j, hj, haj⟩, ?_⟩
        have hlj := hsub j hj haj
        exact (cardFactors_eq_primeFactors_card_of_squarefree
          (Finset.mem_filter.mp hlj).2.1).trans
            (Finset.mem_filter.mp hlj).2.2
    · rw [if_neg hj]
      simp only [omegaSlice, Finset.mem_filter]
      constructor
      · rintro ⟨haA, homega⟩
        obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp haA
        have hli := hsub i hi hai
        have hsquare : Squarefree a := (Finset.mem_filter.mp hli).2.1
        have hcard : a.primeFactors.card = i := (Finset.mem_filter.mp hli).2.2
        have homega' : cardFactors a = i :=
          (cardFactors_eq_primeFactors_card_of_squarefree hsquare).trans hcard
        have : i = j := by omega
        exact (hj (this ▸ hi)).elim
      · intro ha
        simpa using ha
  have hAadm : Admissible 2 N A := by
    apply admissible_of_omegaSlices hrange
    intro j m
    rw [hslice j]
    by_cases hj : j ∈ ks
    · simp only [if_pos hj]
      exact (hAdm j hj).2 m
    · simp [hj, representations]
  have hmassA : reciprocalMassNN A =
      ∑ k ∈ ks, reciprocalMassNN (fam k) := by
    unfold reciprocalMassNN
    exact Finset.sum_biUnion hdisj
  refine ⟨A, hAadm, hAsub, ?_⟩
  calc
    (∑ k ∈ Finset.Icc 1 K,
        reciprocalMassNN (squarefreePrimeLayer N k)) =
      ∑ k ∈ ks, reciprocalMassNN (squarefreePrimeLayer N k) := by rfl
    _ ≤ ∑ k ∈ ks, (128 * K) • reciprocalMassNN (fam k) := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        reciprocalMassNN (squarefreePrimeLayer N k) ≤
            (128 * k) • reciprocalMassNN (fam k) := hmass k hk
        _ ≤ (128 * K) • reciprocalMassNN (fam k) := by
          simp only [nsmul_eq_mul]
          have hkK : (k : ℚ≥0) ≤ K := by
            exact_mod_cast (Finset.mem_Icc.mp (by simpa [ks] using hk)).2
          gcongr <;> exact_mod_cast hkK
    _ = (128 * K) • reciprocalMassNN A := by
      rw [hmassA, nsmul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp [nsmul_eq_mul]

end Erdos538
