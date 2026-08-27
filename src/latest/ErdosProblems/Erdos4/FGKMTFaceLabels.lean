import ErdosProblems.Erdos4.FGKMTFaceTuples
import ErdosProblems.Erdos4.CutoffSimplex

/-! Injecting the good mixed divisor tuples into compatible pairs of sieve labels. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open DivisorCoefficients IdealAction Classical

variable {P : Type*} [Fintype P] [DecidableEq P] {k R : ℕ}

noncomputable def faceLabel (ell : P → ℕ) (j : Fin k) (s : Fin 2)
    (a : (SieveCore j ⊕ Fin 2) → Fin (R + 1)) : P → Option (Fin k) :=
  labelOfTuple ell (faceTuple j s a)

theorem faceLabel_coordinate (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    {W T : ℕ} (L : ℝ)
    (hcover : ∀ u : ℕ, u ≤ R → Squarefree u → u.Coprime W →
      ∀ q ∈ u.primeFactors, ∃ p, ell p = q)
    (j : Fin k) (s : Fin 2) (a : (SieveCore j ⊕ Fin 2) → Fin (R + 1))
    (ha : MixedDivisorGood (SieveCore j) W T L a) (i : Fin k) :
    coordinateDivisor ell (faceLabel ell j s a) i = faceTuple j s a i := by
  apply coordinateDivisor_labelOfTuple ell hprime hinj (faceTuple j s a)
    (faceTuple_pairwise j s a ha.2.2.2)
  · intro l
    exact (ha.1 (faceIndex j s l)).1
  · intro l q hq
    exact hcover _ (Nat.le_of_lt_succ (a (faceIndex j s l)).isLt)
      (ha.1 (faceIndex j s l)).1 (ha.1 (faceIndex j s l)).2 q hq

theorem faceLabel_compatible (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    {W T : ℕ} (L : ℝ)
    (hcover : ∀ u : ℕ, u ≤ R → Squarefree u → u.Coprime W →
      ∀ q ∈ u.primeFactors, ∃ p, ell p = q)
    (j : Fin k) (a : (SieveCore j ⊕ Fin 2) → Fin (R + 1))
    (ha : MixedDivisorGood (SieveCore j) W T L a) :
    Compatible j (faceLabel ell j 0 a) (faceLabel ell j 1 a) := by
  intro p
  apply Option.ext
  intro i
  by_cases hij : i = j
  · subst i
    have hne (d : Option (Fin k)) : IdealProjection.freeze j d ≠ some j := by
      unfold IdealProjection.freeze
      split_ifs with h
      · simp
      · exact h
    simp only [hne, iff_self]
  · rw [IdealProjection.freeze_eq_some_iff j i hij,
      IdealProjection.freeze_eq_some_iff j i hij,
      ← prime_dvd_coordinateDivisor_iff ell hprime hinj _ p i,
      ← prime_dvd_coordinateDivisor_iff ell hprime hinj _ p i,
      faceLabel_coordinate ell hprime hinj L hcover j 0 a ha i,
      faceLabel_coordinate ell hprime hinj L hcover j 1 a ha i]
    simp [faceTuple, faceIndex, hij]

theorem faceLabel_cutoff (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    {W T : ℕ} (hR : 1 ≤ R) (hT : 1 ≤ T) (hTR : T ^ 2 ≤ R)
    (hcover : ∀ u : ℕ, u ≤ R → Squarefree u → u.Coprime W →
      ∀ q ∈ u.primeFactors, ∃ p, ell p = q)
    (j : Fin k) (s : Fin 2) (a : (SieveCore j ⊕ Fin 2) → Fin (R + 1))
    (ha : MixedDivisorGood (SieveCore j) W T (Real.log (R : ℝ) / 2) a) :
    totalDivisor ell (faceLabel ell j s a) ≤ R := by
  rw [CutoffSimplex.totalDivisor_eq_prod_coordinates]
  simp_rw [faceLabel_coordinate ell hprime hinj (Real.log (R : ℝ) / 2) hcover j s a ha]
  exact faceTuple_product_le j s hR hT hTR a ha

noncomputable def faceLabelPair (ell : P → ℕ) (j : Fin k)
    (a : (SieveCore j ⊕ Fin 2) → Fin (R + 1)) :
    (P → Option (Fin k)) × (P → Option (Fin k)) :=
  (faceLabel ell j 0 a, faceLabel ell j 1 a)

theorem faceLabelPair_injOn (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    {W T : ℕ} (L : ℝ)
    (hcover : ∀ u : ℕ, u ≤ R → Squarefree u → u.Coprime W →
      ∀ q ∈ u.primeFactors, ∃ p, ell p = q) (j : Fin k) :
    Set.InjOn (faceLabelPair (R := R) ell j)
      ((Finset.univ : Finset ((SieveCore j ⊕ Fin 2) → Fin (R + 1))).filter
        (MixedDivisorGood (SieveCore j) W T L)) := by
  intro a ha c hc hac
  have hga := (Finset.mem_filter.mp ha).2
  have hgc := (Finset.mem_filter.mp hc).2
  have heq0 : faceLabel ell j 0 a = faceLabel ell j 0 c := congrArg Prod.fst hac
  have heq1 : faceLabel ell j 1 a = faceLabel ell j 1 c := congrArg Prod.snd hac
  have htuple (s : Fin 2) : faceTuple j s a = faceTuple j s c := by
    have hlabel : faceLabel ell j s a = faceLabel ell j s c := by
      fin_cases s
      · exact heq0
      · exact heq1
    funext i
    rw [← faceLabel_coordinate ell hprime hinj L hcover j s a hga i,
      ← faceLabel_coordinate ell hprime hinj L hcover j s c hgc i, hlabel]
  funext i
  apply Fin.ext
  cases i with
  | inl i =>
    have hh := congrFun (htuple 0) i
    simpa only [faceTuple_core] using hh
  | inr s =>
    have hh := congrFun (htuple s) j
    simpa only [faceTuple_anchor] using hh

end Erdos4.FGKMT
