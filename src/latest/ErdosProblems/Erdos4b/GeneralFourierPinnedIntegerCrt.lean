/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedPrimeCrt

/-!
# The pinned CRT class for the literal integer affine forms

Squarefree coordinate divisibility is equivalent to the prime-local
equations. This connects the graph criterion to the original affine
forms, while avoiding any truncation of a negative shift difference.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem int_dvd_divisor_primeFinsetProduct_iff
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {D : ℕ}
    (hD : D ∣ ∏ p ∈ P, p) (n : ℤ) :
    (D : ℤ) ∣ n ↔ ∀ p ∈ P, p ∣ D → (p : ℤ) ∣ n := by
  simp only [Int.natCast_dvd]
  simpa only [Nat.modEq_zero_iff_dvd] using
    modEq_divisor_primeFinsetProduct_iff P hP hD n.natAbs 0

def pinnedFirstIntegerForm {K : ℕ} (h : Fin K) (w p₀ q : ℕ)
    (i : PinnedShiftIndex h) : ℤ :=
  (p₀ : ℤ) + (primorial w : ℤ) * ((i.val.val : ℤ) - h.val) * q

def PinnedIntegerDivisorCondition {K : ℕ} (h : Fin K) (w m p₀ q : ℕ)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ) : Prop :=
  ∀ i, ((Nat.lcm (d (.inl i) false) (d (.inl i) true) : ℕ) : ℤ) ∣
      pinnedFirstIntegerForm h w p₀ q i ∧
    ((Nat.lcm (d (.inr i) false) (d (.inr i) true) : ℕ) : ℤ) ∣
      (m : ℤ) * pinnedFirstIntegerForm h w p₀ q i - 1

theorem pinnedFirstIntegerForm_cast {K : ℕ} (h : Fin K) (w p₀ q p : ℕ)
    (i : PinnedShiftIndex h) :
    (pinnedFirstIntegerForm h w p₀ q i : ZMod p) =
      (p₀ : ZMod p) + pinnedIndexSlope h w p i * (q : ZMod p) := by
  simp only [pinnedFirstIntegerForm, pinnedIndexSlope, Int.cast_add, Int.cast_mul,
    Int.cast_sub, Int.cast_natCast]

theorem pinnedDivisorPrimeEquations_iff_integer_divisibility
    {K w m p₀ q : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)
    (hdiv : ∀ i b, d i b ∣ ∏ p ∈ P, p) :
    PinnedDivisorPrimeEquations h P w m p₀ q d ↔
      PinnedIntegerDivisorCondition h w m p₀ q d := by
  have hlcm (i : PinnedShiftIndex h ⊕ PinnedShiftIndex h) :
      Nat.lcm (d i false) (d i true) ∣ ∏ p ∈ P, p := Nat.lcm_dvd (hdiv i false) (hdiv i true)
  have hfirst (p : ℕ) (i : PinnedShiftIndex h) :
      (p : ℤ) ∣ pinnedFirstIntegerForm h w p₀ q i ↔
        (p₀ : ZMod p) + pinnedIndexSlope h w p i * (q : ZMod p) = 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, pinnedFirstIntegerForm_cast]
  have hcomp (p : ℕ) (i : PinnedShiftIndex h) :
      (p : ℤ) ∣ (m : ℤ) * pinnedFirstIntegerForm h w p₀ q i - 1 ↔
        (m : ZMod p) * ((p₀ : ZMod p) + pinnedIndexSlope h w p i * (q : ZMod p)) = 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one,
      pinnedFirstIntegerForm_cast, sub_eq_zero]
  constructor
  · intro hq i
    constructor
    · apply (int_dvd_divisor_primeFinsetProduct_iff P hP (hlcm (.inl i)) _).mpr
      intro p hp hpD
      exact (hfirst p i).mpr ((hq ⟨p, hp⟩).1 i hpD)
    · apply (int_dvd_divisor_primeFinsetProduct_iff P hP (hlcm (.inr i)) _).mpr
      intro p hp hpE
      exact (hcomp p i).mpr ((hq ⟨p, hp⟩).2 i hpE)
  · intro hq p
    constructor
    · intro i hi
      exact (hfirst p i).mp
        ((int_dvd_divisor_primeFinsetProduct_iff P hP (hlcm (.inl i)) _).mp
          (hq i).1 p p.property hi)
    · intro i hi
      exact (hcomp p i).mp
        ((int_dvd_divisor_primeFinsetProduct_iff P hP (hlcm (.inr i)) _).mp
          (hq i).2 p p.property hi)

theorem pinnedIntegerDivisorCondition_implies_localSolvable
    {K w m p₀ q Y : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hm : 0 < m) (hp₀ : p₀.Prime) (hcop : (m * p₀ - 1).Coprime (primorial Y))
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)
    (hdiv : ∀ i b, d i b ∣ ∏ p ∈ P, p)
    (hDsmall : ∀ i b, d (.inl i) b < p₀) (hEsmall : ∀ i b, d (.inr i) b ≤ Y)
    (hcond : PinnedIntegerDivisorCondition h w m p₀ q d) :
    ∀ p : P, PinnedLocalDivisorSolvable h w m p₀ p.val
      (fun i ↦ Nat.lcm (d (.inl i) false) (d (.inl i) true))
      (fun i ↦ Nat.lcm (d (.inr i) false) (d (.inr i) true)) := by
  classical
  have heq := (pinnedDivisorPrimeEquations_iff_integer_divisibility h P hP d hdiv).mpr hcond
  have hpos (i : PinnedShiftIndex h ⊕ PinnedShiftIndex h) (b : Bool) : 0 < d i b :=
    ((primeFinsetProduct_squarefree P hP).squarefree_of_dvd (hdiv i b)).ne_zero.bot_lt
  intro p
  let : Fact p.val.Prime := ⟨hP p p.property⟩
  by_cases hq : (q : ZMod p.val) ≠ 0
  · exact ⟨q, hq, heq p⟩
  · have hq0 := not_ne_iff.mp hq
    have hnoneD (i : PinnedShiftIndex h) :
        ¬p.val ∣ Nat.lcm (d (.inl i) false) (d (.inl i) true) := by
      intro hi
      have hn := prime_not_dvd_pinnedPrime_of_coordinate_lt (hP p p.property) hp₀
        (hpos _ _) (hpos _ _) (hDsmall i false) (hDsmall i true) hi
      have he := (heq p).1 i hi
      rw [hq0, mul_zero, add_zero] at he
      exact hn ((ZMod.natCast_eq_zero_iff p₀ p.val).mp he)
    have hnoneE (i : PinnedShiftIndex h) :
        ¬p.val ∣ Nat.lcm (d (.inr i) false) (d (.inr i) true) := by
      intro hi
      have hpY := prime_le_of_dvd_lcm_of_coordinate_le (hP p p.property)
        (hpos _ _) (hpos _ _) (hEsmall i false) (hEsmall i true) hi
      have hn := pinnedResidual_companion_numerator_ne_zero hm hp₀.pos hcop
        ⟨p.val, hP p p.property⟩ hpY
      have he := (heq p).2 i hi
      rw [hq0, mul_zero, add_zero] at he
      exact hn (sub_eq_zero.mpr he.symm)
    exact ⟨1, one_ne_zero, fun i hi ↦ (hnoneD i hi).elim, fun i hi ↦ (hnoneE i hi).elim⟩

theorem pinnedIntegerDivisorCondition_implies_cutoff_graph
    {K w m p₀ q Y : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hrough : ∀ p ∈ P, w < p) (hKw : K ≤ w) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hcop : (m * p₀ - 1).Coprime (primorial Y))
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)
    (hdiv : ∀ i b, d i b ∣ ∏ p ∈ P, p)
    (hDsmall : ∀ i b, d (.inl i) b < p₀) (hEsmall : ∀ i b, d (.inr i) b ≤ Y)
    (hcond : PinnedIntegerDivisorCondition h w m p₀ q d) :
    d ∈ doubledCutoffDivisorTuples (PinnedShiftIndex h) P ∧
      DoubledDivisorPrimeCompatible P (roughPinnedFourierEdges h w m p₀ Y)
        (truncatedPinnedFourierCompanion m Y) d := by
  have hsol := pinnedIntegerDivisorCondition_implies_localSolvable h P hP hm hp₀ hcop
    d hdiv hDsmall hEsmall hcond
  have hwithin := withinFamilyDivisorCoprime_of_pinnedLocalSolvable h P hP hrough hKw
    hm hp₀ hcop d hdiv hDsmall hEsmall hsol
  have hd := (mem_doubledCutoffDivisorTuples P hP d).mpr ⟨hdiv, hwithin⟩
  exact ⟨hd, (doubledDivisorPrimeCompatible_iff_pinnedLocalSolvable h P hP hrough hKw
    hm hp₀ hcop d hd hDsmall hEsmall).mpr hsol⟩

theorem exists_pinnedIntegerCrt_reduced_class_of_graph
    {K w m p₀ Y : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hrough : ∀ p ∈ P, w < p) (hKw : K ≤ w) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hcop : (m * p₀ - 1).Coprime (primorial Y))
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)
    (hd : d ∈ doubledCutoffDivisorTuples (PinnedShiftIndex h) P)
    (hDsmall : ∀ i b, d (.inl i) b < p₀) (hEsmall : ∀ i b, d (.inr i) b ≤ Y)
    (hgraph : DoubledDivisorPrimeCompatible P (roughPinnedFourierEdges h w m p₀ Y)
      (truncatedPinnedFourierCompanion m Y) d) :
    ∃ r : ℕ, r < pinnedFlatDivisorModulus h d ∧ r.Coprime (pinnedFlatDivisorModulus h d) ∧
      ∀ q : ℕ, PinnedIntegerDivisorCondition h w m p₀ q d ↔
        q ≡ r [MOD pinnedFlatDivisorModulus h d] := by
  have hdiv := ((mem_doubledCutoffDivisorTuples P hP d).mp hd).1
  have hsol := (doubledDivisorPrimeCompatible_iff_pinnedLocalSolvable h P hP hrough hKw
    hm hp₀ hcop d hd hDsmall hEsmall).mp hgraph
  obtain ⟨r, hrlt, hrcop, hr⟩ :=
    exists_pinnedPrimeCrt_bounded_reduced_class h P hP hrough hKw d hdiv hsol
  refine ⟨r, hrlt, hrcop, fun q ↦ ?_⟩
  rw [← pinnedDivisorPrimeEquations_iff_integer_divisibility h P hP d hdiv, hr q]

end

end Erdos4b
