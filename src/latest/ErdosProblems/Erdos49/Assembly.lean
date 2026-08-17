import ErdosProblems.Erdos49.PrimaryApplication
import ErdosProblems.Erdos49.SecondaryGlobal

/-!
# Finite assembly of Tao's argument

The theorem in this file contains no asymptotics.  It combines the anatomy
cover with the primary and secondary packing estimates and leaves only the
six exceptional-set cardinalities to be estimated.
-/

namespace Erdos49

noncomputable section

attribute [local instance] Classical.propDecidable

lemma primary_short_of_not_small
    {N L D W n : ℕ} (hD : 1 ≤ D) (hW : 0 < W)
    (hscale : (4 * D ^ 2 + 1) * W * L ≤ N)
    (hnI : n ∈ Finset.Icc 1 N) (hnsmall : n ∉ smallExceptional N L) :
    (W : ℝ) ≤ ((quotientBucket W n * W : ℕ) : ℝ) /
      (4 * (D : ℝ) ^ 2) := by
  have hnLarge : N < n * L := by
    by_contra h
    apply hnsmall
    exact Finset.mem_filter.mpr ⟨hnI, Nat.le_of_not_gt h⟩
  have hLpos : 0 < L := by
    by_contra h
    have : L = 0 := Nat.eq_zero_of_not_pos h
    subst L
    simp at hnLarge
  have hb := quotientBucket_bounds (W := W) (n := n) hW
  have hbucket : 4 * D ^ 2 * W ≤ quotientBucket W n * W := by
    by_contra h
    have hlt : quotientBucket W n * W < 4 * D ^ 2 * W :=
      Nat.lt_of_not_ge h
    have hnUpper : n < (4 * D ^ 2 + 1) * W := by
      calc
        n < quotientBucket W n * W + W := hb.2
        _ < 4 * D ^ 2 * W + W := Nat.add_lt_add_right hlt W
        _ = (4 * D ^ 2 + 1) * W := by ring
    have hnLUpper : n * L < (4 * D ^ 2 + 1) * W * L := by
      exact Nat.mul_lt_mul_of_pos_right hnUpper hLpos
    have : n * L < N + 1 := by
      calc
        n * L < (4 * D ^ 2 + 1) * W * L := hnLUpper
        _ ≤ N := hscale
        _ < N + 1 := Nat.lt_succ_self N
    omega
  have hden : (0 : ℝ) < 4 * (D : ℝ) ^ 2 := by positivity
  apply (le_div_iff₀ hden).2
  exact_mod_cast (by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
      mul_assoc, mul_comm, mul_left_comm] using hbucket)

def regularPart (A : Finset ℕ) (N L D R : ℕ) : Finset ℕ :=
  A \ exceptionalSet N L D R

def assembledPrimary (A : Finset ℕ) (N L D R : ℕ) : Finset ℕ :=
  (regularPart A N L D R).filter fun n ↦ n ∈ primarySet N L D

def assembledSecondary (A : Finset ℕ) (N L D R : ℕ) : Finset ℕ :=
  (regularPart A N L D R).filter fun n ↦ n ∈ secondarySet N L

lemma assembled_cover
    {N L D R : ℕ} {A : Finset ℕ}
    (hAI : A ⊆ Finset.Icc 1 N)
    (hL : 0 < L) (hLR : L < R) (hDR : D < R)
    (h8DR : 8 * D ^ 2 ≤ R) :
    A ⊆ assembledPrimary A N L D R ∪
      assembledSecondary A N L D R ∪ exceptionalSet N L D R := by
  have hcover := anatomy_cover (N := N) hL hLR hDR h8DR
  intro n hn
  by_cases hnE : n ∈ exceptionalSet N L D R
  · exact Finset.mem_union_right _ hnE
  have hnreg : n ∈ regularPart A N L D R := by
    exact Finset.mem_sdiff.mpr ⟨hn, hnE⟩
  have hPS := hcover (hAI hn)
  rcases Finset.mem_union.mp hPS with hPS | hnE'
  · rcases Finset.mem_union.mp hPS with hnP | hnS
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hnreg, hnP⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hnreg, hnS⟩))
  · exact (hnE hnE').elim

lemma exceptionalSet_card_le_sum (N L D R : ℕ) :
    (exceptionalSet N L D R).card ≤
      (smallExceptional N L).card + (smoothExceptional N R).card +
      (squareExceptional N L).card + (smoothTailExceptional N L D).card +
      (pairExceptional N L D R).card + (tripleExceptional N L R).card := by
  unfold exceptionalSet
  calc
    (((smallExceptional N L ∪ smoothExceptional N R) ∪
        squareExceptional N L ∪ smoothTailExceptional N L D ∪
        pairExceptional N L D R ∪ tripleExceptional N L R).card) ≤
      (((smallExceptional N L ∪ smoothExceptional N R) ∪
        squareExceptional N L ∪ smoothTailExceptional N L D ∪
        pairExceptional N L D R).card) +
          (tripleExceptional N L R).card := Finset.card_union_le _ _
    _ ≤ (((smallExceptional N L ∪ smoothExceptional N R) ∪
        squareExceptional N L ∪ smoothTailExceptional N L D).card) +
          (pairExceptional N L D R).card +
          (tripleExceptional N L R).card := by
      exact Nat.add_le_add_right
        (Finset.card_union_le _ _) (tripleExceptional N L R).card
    _ ≤ (((smallExceptional N L ∪ smoothExceptional N R) ∪
        squareExceptional N L).card) +
          (smoothTailExceptional N L D).card +
          (pairExceptional N L D R).card +
          (tripleExceptional N L R).card := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_right (Finset.card_union_le _ _)
          (pairExceptional N L D R).card)
        (tripleExceptional N L R).card
    _ ≤ ((smallExceptional N L ∪ smoothExceptional N R).card) +
          (squareExceptional N L).card +
          (smoothTailExceptional N L D).card +
          (pairExceptional N L D R).card +
          (tripleExceptional N L R).card := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_right
          (Nat.add_le_add_right (Finset.card_union_le _ _)
            (smoothTailExceptional N L D).card)
          (pairExceptional N L D R).card)
        (tripleExceptional N L R).card
    _ ≤ (smallExceptional N L).card + (smoothExceptional N R).card +
          (squareExceptional N L).card +
          (smoothTailExceptional N L D).card +
          (pairExceptional N L D R).card +
          (tripleExceptional N L R).card := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_right
          (Nat.add_le_add_right
            (Nat.add_le_add_right (Finset.card_union_le _ _)
              (squareExceptional N L).card)
            (smoothTailExceptional N L D).card)
          (pairExceptional N L D R).card)
        (tripleExceptional N L R).card

theorem assembled_finite_bound
    {N L D R W H : ℕ} {A : Finset ℕ} {Err : ℝ}
    (hAI : A ⊆ Finset.Icc 1 N) (hmono : TotientMonotoneOn A)
    (hL : 0 < L) (hLR : L < R) (hDR : D < R)
    (h8DR : 8 * D ^ 2 ≤ R)
    (hD : 1 ≤ D) (hW : 3 ≤ W)
    (hWscale : (4 * D ^ 2 + 1) * W * L ≤ N)
    (hErr : 0 ≤ Err)
    (htheta : ∀ x : ℕ, W - 1 ≤ x → x ≤ N →
      |Chebyshev.theta (x : ℝ) - x| ≤ Err)
    (hH : 2 ≤ H) (hLT : secondaryT H ^ 3 ≤ L) :
    (A.card : ℝ) ≤
      ((N : ℝ) / Real.log W +
        (((N / W + 1) * D : ℕ) : ℝ) * D *
          ((2 + 2 * Err) / Real.log W)) +
      (8000 * (N : ℝ) * (1 + Real.log N) *
        (N.log2 + 1 : ℕ) ^ 2 / secondaryT H) +
      (exceptionalSet N L D R).card := by
  let AP := assembledPrimary A N L D R
  let AS := assembledSecondary A N L D R
  have hcover := assembled_cover hAI hL hLR hDR h8DR
  have hcardNat := (Finset.card_le_card hcover).trans
    (Finset.card_union_le (AP ∪ AS) (exceptionalSet N L D R) |>.trans
      (Nat.add_le_add_right (Finset.card_union_le AP AS) _))
  have hAPprim : AP ⊆ primarySet N L D := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have hASsec : AS ⊆ secondarySet N L := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have hAPmono : TotientMonotoneOn AP := hmono.mono (by
    intro n hn
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hn).1).1)
  have hASmono : TotientMonotoneOn AS := hmono.mono (by
    intro n hn
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hn).1).1)
  have hAPshort : ∀ n ∈ AP,
      (W : ℝ) ≤ ((quotientBucket W n * W : ℕ) : ℝ) /
        (4 * (D : ℝ) ^ 2) := by
    intro n hn
    have hnreg := Finset.mem_sdiff.mp (Finset.mem_filter.mp hn).1
    have hnI := hAI hnreg.1
    have hnNotSmall : n ∉ smallExceptional N L := by
      intro hnSmall
      apply hnreg.2
      unfold exceptionalSet
      simp [hnSmall]
    exact primary_short_of_not_small hD (by omega) hWscale hnI hnNotSmall
  have hprimary := primary_global_bound_of_uniform_theta
    hAPprim hAPmono hD hW hAPshort hErr htheta
  have hNpos : 0 < N := by
    apply lt_of_lt_of_le (b := (4 * D ^ 2 + 1) * W * L)
    · positivity
    · exact hWscale
  have hsecondary := secondary_global_bound hASsec hASmono
    hNpos hH hLT
  have hcardReal : (A.card : ℝ) ≤
      (AP.card : ℝ) + AS.card + (exceptionalSet N L D R).card := by
    exact_mod_cast hcardNat
  exact hcardReal.trans (by linarith)

#print axioms assembled_finite_bound

end

end Erdos49
