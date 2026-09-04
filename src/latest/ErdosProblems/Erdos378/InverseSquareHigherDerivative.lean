/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.HigherDerivative

/-!
# Higher derivative bounds for an inverse-square phase

This is the `x / p^2` companion to `HigherDerivative`.  The abstract
van-der-Corput tree from that file is reused verbatim; only the explicit
derivative and terminal first-derivative estimate change.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos378
namespace InverseSquareHigherDerivative

open ReciprocalExponential
open HigherDerivative

noncomputable section

/-- The `k`th derivative of `t ↦ -X / t²` on the positive half-line. -/
noncomputable def inverseSquareDeriv (X : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  -X * ((-1 : ℝ) ^ k * ((k + 1).factorial : ℝ) *
    t ^ (-2 - (k : ℤ)))

@[simp] lemma inverseSquareDeriv_zero (X t : ℝ) :
    inverseSquareDeriv X 0 t = -X / t ^ 2 := by
  simp [inverseSquareDeriv, div_eq_mul_inv, zpow_neg]

lemma hasDerivAt_inverseSquareDeriv (X : ℝ) (k : ℕ) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (inverseSquareDeriv X k)
      (inverseSquareDeriv X (k + 1) t) t := by
  have hz := hasDerivAt_zpow (-2 - (k : ℤ)) t (Or.inl (ne_of_gt ht))
  have hmul := hz.const_mul
    (-X * ((-1 : ℝ) ^ k * ((k + 1).factorial : ℝ)))
  unfold inverseSquareDeriv
  have hfun :
      (fun y : ℝ ↦ -X *
        ((-1 : ℝ) ^ k * ((k + 1).factorial : ℝ) *
          y ^ (-2 - (k : ℤ)))) =
      (fun y : ℝ ↦
        (-X * ((-1 : ℝ) ^ k * ((k + 1).factorial : ℝ))) *
          y ^ (-2 - (k : ℤ))) := by
    funext y
    ring
  rw [hfun]
  have hder :
      -X * ((-1 : ℝ) ^ (k + 1) * ((k + 1 + 1).factorial : ℝ) *
          t ^ (-2 - ((k + 1 : ℕ) : ℤ))) =
        (-X * ((-1 : ℝ) ^ k * ((k + 1).factorial : ℝ))) *
          (((-2 - (k : ℤ) : ℤ) : ℝ) * t ^ (-2 - (k : ℤ) - 1)) := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      pow_succ]
    have hexp : -2 - ((k : ℤ) + 1) = -2 - (k : ℤ) - 1 := by ring
    rw [hexp]
    push_cast
    ring
  rw [hder]
  exact hmul

lemma exists_forwardDifferences_inverseSquare_eq (X : ℝ)
    (rs : List ℝ) (hrs : ∀ r ∈ rs, 0 < r) {t : ℝ} (ht : 0 < t) :
    ∃ y : ℝ, t ≤ y ∧ y ≤ t + rs.sum ∧
      forwardDifferences rs (fun x ↦ -X / x ^ 2) t =
        rs.prod * inverseSquareDeriv X rs.length y := by
  have hzero : inverseSquareDeriv X 0 = fun x ↦ -X / x ^ 2 := by
    funext x
    exact inverseSquareDeriv_zero X x
  rw [← hzero]
  exact exists_forwardDifferences_eq_prod_deriv (inverseSquareDeriv X)
    (fun k x hx ↦ hasDerivAt_inverseSquareDeriv X k hx) rs hrs ht

/-- The real phase represented by an iterated inverse-square correlation. -/
def signedInverseSquareDifference
    (X : ℝ) (A : ℕ) (rs : List ℕ) (i : ℕ) : ℝ :=
  ((-1 : ℝ) ^ rs.length) *
    forwardDifferences (rs.map (fun r : ℕ ↦ (r : ℝ)))
      (fun t ↦ -X / t ^ 2) (A + i : ℕ)

lemma iteratedCorrelation_inverseSquare_eq
    (X : ℝ) (A : ℕ) (rs : List ℕ) (n : ℕ) :
    iteratedCorrelation rs
        (fun m ↦ e (-X / ((A + m : ℕ) : ℝ) ^ 2)) n =
      e (signedInverseSquareDifference X A rs n) := by
  have h := iteratedCorrelation_e_eq
    (fun t : ℝ ↦ -X / ((A : ℝ) + t) ^ 2) rs n
  calc
    iteratedCorrelation rs
        (fun m ↦ e (-X / ((A + m : ℕ) : ℝ) ^ 2)) n =
      iteratedCorrelation rs
        (fun m ↦ e (-X / ((A : ℝ) + (m : ℝ)) ^ 2)) n := by
          congr 3
          funext m
          push_cast
          rfl
    _ = e (((-1 : ℝ) ^ rs.length) *
        forwardDifferences (rs.map (fun r : ℕ ↦ (r : ℝ)))
          (fun t : ℝ ↦ -X / ((A : ℝ) + t) ^ 2) n) := h
    _ = e (signedInverseSquareDifference X A rs n) := by
      unfold signedInverseSquareDifference
      congr 2
      rw [forwardDifferences_translate
        (fun t : ℝ ↦ -X / t ^ 2)
        (rs.map (fun r : ℕ ↦ (r : ℝ))) (A : ℝ) n]
      congr 2
      push_cast
      ring

private lemma neg_one_pow_mul_succ (k : ℕ) :
    ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ (k + 1)) = -1 := by
  rw [← pow_add]
  have hk : k + (k + 1) = 2 * k + 1 := by omega
  rw [hk, pow_succ, pow_mul]
  norm_num

private lemma neg_one_pow_mul_add_two (k : ℕ) :
    ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ (k + 2)) = 1 := by
  rw [← pow_add]
  have hk : k + (k + 2) = 2 * (k + 1) := by omega
  rw [hk, pow_mul]
  norm_num

lemma signedInverseSquareDifference_succ_sub (X : ℝ) (A : ℕ)
    (rs : List ℕ) (i : ℕ) :
    signedInverseSquareDifference X A rs (i + 1) -
        signedInverseSquareDifference X A rs i =
      ((-1 : ℝ) ^ rs.length) *
        forwardDifferences
          ((1 : ℝ) :: rs.map (fun r : ℕ ↦ (r : ℝ)))
          (fun t ↦ -X / t ^ 2) (A + i : ℕ) := by
  simp only [signedInverseSquareDifference, forwardDifferences_cons]
  push_cast
  ring_nf

lemma exists_signedInverseSquareDifference_gap
    (X : ℝ) (hX : 0 < X) {A : ℕ} (hA : 0 < A)
    (rs : List ℕ) (hrs : ∀ r ∈ rs, 0 < r) (i : ℕ) :
    ∃ y : ℝ, (A + i : ℕ) ≤ y ∧
      y ≤ (A + i : ℕ) + 1 + rs.sum ∧
      signedInverseSquareDifference X A rs (i + 1) -
          signedInverseSquareDifference X A rs i =
        X * ((rs.length + 2).factorial : ℝ) *
          (rs.prod : ℝ) / y ^ (rs.length + 3) := by
  let shifts : List ℝ :=
    (1 : ℝ) :: rs.map (fun r : ℕ ↦ (r : ℝ))
  have hshifts : ∀ r ∈ shifts, 0 < r := by
    intro r hr
    rw [show shifts = (1 : ℝ) ::
      rs.map (fun r : ℕ ↦ (r : ℝ)) by rfl] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · norm_num
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
      exact_mod_cast hrs s hs
  have ht : 0 < (((A + i : ℕ) : ℝ)) := by positivity
  obtain ⟨y, hty, hy, hfd⟩ :=
    exists_forwardDifferences_inverseSquare_eq X shifts hshifts ht
  refine ⟨y, hty, ?_, ?_⟩
  · have hsum : shifts.sum = 1 + (rs.sum : ℝ) := by simp [shifts]
    calc
      y ≤ ((A + i : ℕ) : ℝ) + shifts.sum := hy
      _ = ((A + i : ℕ) : ℝ) + 1 + (rs.sum : ℝ) := by rw [hsum]; ring
      _ = (((A + i : ℕ) : ℝ) + 1 + rs.sum) := by push_cast; ring
  · rw [signedInverseSquareDifference_succ_sub, hfd]
    have hypos : 0 < y := ht.trans_le hty
    have hsign := neg_one_pow_mul_succ rs.length
    have hlen : shifts.length = rs.length + 1 := by simp [shifts]
    have hprod : shifts.prod = (rs.prod : ℝ) := by simp [shifts]
    rw [hlen, hprod]
    unfold inverseSquareDeriv
    rw [show -2 - ((rs.length + 1 : ℕ) : ℤ) =
        -((rs.length + 3 : ℕ) : ℤ) by omega]
    rw [zpow_neg, zpow_natCast]
    change ((-1 : ℝ) ^ rs.length) *
        ((rs.prod : ℝ) *
          (-X * (((-1 : ℝ) ^ (rs.length + 1)) *
            ((rs.length + 2).factorial : ℝ) *
            (y ^ (rs.length + 3))⁻¹))) = _
    calc
      ((-1 : ℝ) ^ rs.length) *
          ((rs.prod : ℝ) *
            (-X * (((-1 : ℝ) ^ (rs.length + 1)) *
              ((rs.length + 2).factorial : ℝ) *
              (y ^ (rs.length + 3))⁻¹))) =
        -(((-1 : ℝ) ^ rs.length) *
            ((-1 : ℝ) ^ (rs.length + 1))) *
          X * ((rs.length + 2).factorial : ℝ) *
          (rs.prod : ℝ) * (y ^ (rs.length + 3))⁻¹ := by ring
      _ = X * ((rs.length + 2).factorial : ℝ) *
          (rs.prod : ℝ) / y ^ (rs.length + 3) := by
        rw [hsign]
        simp only [neg_neg, one_mul, div_eq_mul_inv]

lemma signedInverseSquareDifference_gap_lower
    (X : ℝ) (hX : 0 < X) {A N : ℕ} (hA : 0 < A)
    (rs : List ℕ) (hrs : ∀ r ∈ rs, 0 < r) {i : ℕ}
    (hi : i + 1 + rs.sum ≤ N) :
    X * ((rs.length + 2).factorial : ℝ) * (rs.prod : ℝ) /
        ((A + N : ℕ) : ℝ) ^ (rs.length + 3) ≤
      signedInverseSquareDifference X A rs (i + 1) -
        signedInverseSquareDifference X A rs i := by
  obtain ⟨y, hty, hy, hgap⟩ :=
    exists_signedInverseSquareDifference_gap X hX hA rs hrs i
  rw [hgap]
  have hypos : 0 < y := (by positivity : 0 < (((A + i : ℕ) : ℝ))).trans_le hty
  have hyAN : y ≤ ((A + N : ℕ) : ℝ) := by
    calc
      y ≤ ((A + i : ℕ) : ℝ) + 1 + rs.sum := hy
      _ ≤ ((A + N : ℕ) : ℝ) := by
        have hnat : A + i + 1 + rs.sum ≤ A + N := by omega
        exact_mod_cast hnat
  apply div_le_div_of_nonneg_left (by positivity)
  · positivity
  · gcongr

lemma signedInverseSquareDifference_gap_upper
    (X : ℝ) (hX : 0 < X) {A : ℕ} (hA : 0 < A)
    (rs : List ℕ) (hrs : ∀ r ∈ rs, 0 < r) (i : ℕ) :
    signedInverseSquareDifference X A rs (i + 1) -
        signedInverseSquareDifference X A rs i ≤
      X * ((rs.length + 2).factorial : ℝ) * (rs.prod : ℝ) /
        (A : ℝ) ^ (rs.length + 3) := by
  obtain ⟨y, hty, hy, hgap⟩ :=
    exists_signedInverseSquareDifference_gap X hX hA rs hrs i
  rw [hgap]
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hAy : (A : ℝ) ≤ y := by
    exact (by exact_mod_cast Nat.le_add_right A i :
      (A : ℝ) ≤ (A + i : ℕ)).trans hty
  apply div_le_div_of_nonneg_left (by positivity)
  · positivity
  · gcongr

lemma signedInverseSquareDifference_gap_succ_sub
    (X : ℝ) (A : ℕ) (rs : List ℕ) (i : ℕ) :
    (signedInverseSquareDifference X A rs (i + 2) -
        signedInverseSquareDifference X A rs (i + 1)) -
      (signedInverseSquareDifference X A rs (i + 1) -
        signedInverseSquareDifference X A rs i) =
      ((-1 : ℝ) ^ rs.length) *
        forwardDifferences
          ((1 : ℝ) :: (1 : ℝ) ::
            rs.map (fun r : ℕ ↦ (r : ℝ)))
          (fun t ↦ -X / t ^ 2) (A + i : ℕ) := by
  simp only [signedInverseSquareDifference, forwardDifferences_cons]
  push_cast
  ring_nf

lemma signedInverseSquareDifference_gap_antitone
    (X : ℝ) (hX : 0 ≤ X) {A : ℕ} (hA : 0 < A)
    (rs : List ℕ) (hrs : ∀ r ∈ rs, 0 < r) :
    Antitone (fun i ↦
      signedInverseSquareDifference X A rs (i + 1) -
        signedInverseSquareDifference X A rs i) := by
  apply antitone_nat_of_succ_le
  intro i
  by_cases hXzero : X = 0
  · subst X
    have hzero : forwardDifferences
        (rs.map (fun r : ℕ ↦ (r : ℝ))) (fun _ : ℝ ↦ 0) = fun _ ↦ 0 := by
      induction rs with
      | nil => rfl
      | cons r rs ih =>
          funext t
          simp only [List.map_cons, forwardDifferences_cons]
          rw [ih (fun s hs ↦ hrs s (by simp [hs]))]
          simp
    simp [signedInverseSquareDifference, hzero]
  · have hXpos : 0 < X := lt_of_le_of_ne hX (Ne.symm hXzero)
    let shifts : List ℝ :=
      (1 : ℝ) :: (1 : ℝ) :: rs.map (fun r : ℕ ↦ (r : ℝ))
    have hshifts : ∀ r ∈ shifts, 0 < r := by
      intro r hr
      rw [show shifts = (1 : ℝ) :: (1 : ℝ) ::
        rs.map (fun r : ℕ ↦ (r : ℝ)) by rfl] at hr
      rcases List.mem_cons.mp hr with rfl | hr
      · norm_num
      · rcases List.mem_cons.mp hr with rfl | hr
        · norm_num
        · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
          exact_mod_cast hrs s hs
    have ht : 0 < (((A + i : ℕ) : ℝ)) := by positivity
    obtain ⟨y, hty, hy, hfd⟩ :=
      exists_forwardDifferences_inverseSquare_eq X shifts hshifts ht
    have hlen : shifts.length = rs.length + 2 := by simp [shifts]
    have hprod : shifts.prod = (rs.prod : ℝ) := by simp [shifts]
    have hsign := neg_one_pow_mul_add_two rs.length
    have hypos : 0 < y := ht.trans_le hty
    have hnonpos :
        ((-1 : ℝ) ^ rs.length) *
          (shifts.prod * inverseSquareDeriv X shifts.length y) ≤ 0 := by
      rw [hlen, hprod]
      unfold inverseSquareDeriv
      rw [show -2 - ((rs.length + 2 : ℕ) : ℤ) =
          -((rs.length + 4 : ℕ) : ℤ) by omega]
      rw [zpow_neg, zpow_natCast]
      rw [show ((-1 : ℝ) ^ rs.length) *
            ((rs.prod : ℝ) *
              (-X * (((-1 : ℝ) ^ (rs.length + 2)) *
                ((rs.length + 3).factorial : ℝ) *
                (y ^ (rs.length + 4))⁻¹))) =
          -(((-1 : ℝ) ^ rs.length) *
              ((-1 : ℝ) ^ (rs.length + 2))) *
            X * ((rs.length + 3).factorial : ℝ) *
            (rs.prod : ℝ) * (y ^ (rs.length + 4))⁻¹ by ring]
      rw [hsign]
      have hpos : 0 ≤ X * ((rs.length + 3).factorial : ℝ) *
          (rs.prod : ℝ) * (y ^ (rs.length + 4))⁻¹ := by positivity
      nlinarith
    have hchange := signedInverseSquareDifference_gap_succ_sub X A rs i
    rw [← sub_nonpos]
    rw [show i + 1 + 1 = i + 2 by omega]
    rw [hchange, hfd]
    exact hnonpos

theorem norm_terminal_inverseSquare_correlation_le
    (X : ℝ) (hX : 0 < X) {A N : ℕ} (hA : 0 < A)
    (rs : List ℕ) (hrs : ∀ r ∈ rs, 0 < r)
    (hN : rs.sum + 2 ≤ N)
    (hsmall : X * ((rs.length + 2).factorial : ℝ) *
        (rs.prod : ℝ) / (A : ℝ) ^ (rs.length + 3) ≤ 1 / 2) :
    ‖∑ n ∈ Finset.Icc 1 (N - rs.sum),
        iteratedCorrelation rs
          (fun m ↦ e (-X / ((A + m : ℕ) : ℝ) ^ 2)) n‖ ≤
      1 + 3 / (2 *
        (X * ((rs.length + 2).factorial : ℝ) *
          (rs.prod : ℝ) /
            ((A + N : ℕ) : ℝ) ^ (rs.length + 3))) := by
  let M := N - rs.sum
  let m : ℝ := X * ((rs.length + 2).factorial : ℝ) *
    (rs.prod : ℝ) / ((A + N : ℕ) : ℝ) ^ (rs.length + 3)
  have hM : 2 ≤ M := by dsimp only [M]; omega
  have hm : 0 < m := by
    dsimp only [m]
    have hprod : 0 < rs.prod := List.prod_pos hrs
    positivity
  have hphase : ∀ i,
      iteratedCorrelation rs
          (fun q ↦ e (-X / ((A + q : ℕ) : ℝ) ^ 2)) (i + 1) =
        e (signedInverseSquareDifference X A rs (i + 1)) :=
    fun i ↦ iteratedCorrelation_inverseSquare_eq X A rs (i + 1)
  rw [sum_Icc_one_eq_sum_range]
  simp_rw [hphase]
  apply norm_sum_e_le_of_antitone_phaseDiff_sharp
    (fun i ↦ signedInverseSquareDifference X A rs (i + 1)) M hM m hm
  · intro i hi
    dsimp only [m]
    apply signedInverseSquareDifference_gap_lower X hX hA rs hrs
    dsimp only [M] at hi
    omega
  · intro i hi
    exact (signedInverseSquareDifference_gap_upper X hX hA rs hrs (i + 1)).trans hsmall
  · have hanti := signedInverseSquareDifference_gap_antitone X hX.le hA rs hrs
    intro i j hij
    exact hanti (by omega)

theorem terminalCorrelationMean_inverseSquare_le
    (X : ℝ) (hX : 0 < X) {A N : ℕ} (hA : 0 < A) (hN : 0 < N)
    (Ls : List ℕ) (hcut : ∀ L ∈ Ls, 1 ≤ L)
    (hfit : Ls.sum + 2 ≤ N)
    (hsmall : X * ((Ls.length + 2).factorial : ℝ) *
        (Ls.prod : ℝ) / (A : ℝ) ^ (Ls.length + 3) ≤ 1 / 2) :
    terminalCorrelationMean
        (fun m ↦ e (-X / ((A + m : ℕ) : ℝ) ^ 2)) N Ls [] ≤
      1 / (8 * (N : ℝ)) +
        (3 * ((A + N : ℕ) : ℝ) ^ (Ls.length + 3) /
          (16 * (N : ℝ) * X * ((Ls.length + 2).factorial : ℝ))) *
          reciprocalShiftFactor Ls := by
  let u : ℕ → ℂ := fun m ↦ e (-X / ((A + m : ℕ) : ℝ) ^ 2)
  let a : ℝ := 1 / (8 * (N : ℝ))
  let b : ℝ := 3 * ((A + N : ℕ) : ℝ) ^ (Ls.length + 3) /
    (16 * (N : ℝ) * X * ((Ls.length + 2).factorial : ℝ))
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hleaf : ∀ ss, IsShiftExtension Ls [] ss →
      correlationAverage u N ss ≤ a + b / (ss.prod : ℝ) := by
    intro ss hss
    have hlen : ss.length = Ls.length := by simpa using hss.length
    have hpos : ∀ r ∈ ss, 0 < r := hss.pos (by simp)
    have hsum : ss.sum + 2 ≤ N := by
      have := hss.sum_le
      simp only [List.sum_nil, add_zero] at this
      omega
    have hprod : ss.prod ≤ Ls.prod := by
      have := hss.prod_le
      simpa using this
    have hsmallss :
        X * ((ss.length + 2).factorial : ℝ) *
            (ss.prod : ℝ) / (A : ℝ) ^ (ss.length + 3) ≤ 1 / 2 := by
      rw [hlen]
      calc
        X * ((Ls.length + 2).factorial : ℝ) *
              (ss.prod : ℝ) / (A : ℝ) ^ (Ls.length + 3) ≤
            X * ((Ls.length + 2).factorial : ℝ) *
              (Ls.prod : ℝ) / (A : ℝ) ^ (Ls.length + 3) := by gcongr
        _ ≤ 1 / 2 := hsmall
    have hnorm := norm_terminal_inverseSquare_correlation_le
      X hX hA ss hpos hsum hsmallss
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hprodreal : (0 : ℝ) < ss.prod := by exact_mod_cast List.prod_pos hpos
    rw [correlationAverage]
    change
      ‖∑ n ∈ Finset.Icc 1 (N - ss.sum), iteratedCorrelation ss u n‖ /
          (8 * (N : ℝ)) ≤ a + b / (ss.prod : ℝ)
    calc
      _ ≤ (1 + 3 / (2 *
          (X * ((ss.length + 2).factorial : ℝ) *
            (ss.prod : ℝ) /
              ((A + N : ℕ) : ℝ) ^ (ss.length + 3)))) /
          (8 * (N : ℝ)) := by
            apply div_le_div_of_nonneg_right
            · simpa only [u] using hnorm
            · positivity
      _ = a + b / (ss.prod : ℝ) := by
        dsimp only [a, b]
        rw [hlen]
        field_simp [ne_of_gt hNreal, ne_of_gt hX, ne_of_gt hprodreal]
        <;> ring
  have havg := terminalCorrelationMean_le_of_leaf
    (u := u) (N := N) (a := a) (b := b) Ls [] ha hb (by simp) hcut hleaf
  simpa only [u, a, b, List.prod_nil, Nat.cast_one, div_one, one_mul] using havg

theorem inverseSquare_exponential_sum_high_derivative
    (X : ℝ) (hX : 0 < X) {A N : ℕ} (hA : 0 < A) (hN : 0 < N)
    (Ls : List ℕ) (hcut : ∀ L ∈ Ls, 1 ≤ L)
    (hfit : Ls.sum + 2 ≤ N)
    (hsmall : X * ((Ls.length + 2).factorial : ℝ) *
        (Ls.prod : ℝ) / (A : ℝ) ^ (Ls.length + 3) ≤ 1 / 2) :
    (‖∑ n ∈ Finset.Icc 1 N,
        e (-X / ((A + n : ℕ) : ℝ) ^ 2)‖ / (8 * (N : ℝ))) ^
        (2 ^ Ls.length) ≤
      vdcMomentConstant Ls.length *
        (differencingError Ls + 1 / (8 * (N : ℝ)) +
          (3 * ((A + N : ℕ) : ℝ) ^ (Ls.length + 3) /
            (16 * (N : ℝ) * X * ((Ls.length + 2).factorial : ℝ))) *
            reciprocalShiftFactor Ls) := by
  let u : ℕ → ℂ := fun m ↦ e (-X / ((A + m : ℕ) : ℝ) ^ 2)
  have hu : ∀ n, ‖u n‖ ≤ 1 := by intro n; simp [u]
  have hmoment := correlationAverage_pow_two_pow_le
    (u := u) (N := N) [] Ls hN (by simp; omega) hcut hu
  have hterm := terminalCorrelationMean_inverseSquare_le
    X hX hA hN Ls hcut hfit hsmall
  have hC : 0 ≤ vdcMomentConstant Ls.length :=
    (vdcMomentConstant_pos Ls.length).le
  rw [correlationAverage] at hmoment
  simp only [List.sum_nil, Nat.sub_zero, List.length_nil, u] at hmoment
  exact hmoment.trans <| by
    apply mul_le_mul_of_nonneg_left _ hC
    linarith

theorem inverseSquare_exponential_sum_high_derivative_pos
    (X : ℝ) (hX : 0 < X) {A N : ℕ} (hA : 0 < A) (hN : 0 < N)
    (Ls : List ℕ) (hcut : ∀ L ∈ Ls, 1 ≤ L)
    (hfit : Ls.sum + 2 ≤ N)
    (hsmall : X * ((Ls.length + 2).factorial : ℝ) *
        (Ls.prod : ℝ) / (A : ℝ) ^ (Ls.length + 3) ≤ 1 / 2) :
    (‖∑ n ∈ Finset.Icc 1 N,
        e (X / ((A + n : ℕ) : ℝ) ^ 2)‖ / (8 * (N : ℝ))) ^
        (2 ^ Ls.length) ≤
      vdcMomentConstant Ls.length *
        (differencingError Ls + 1 / (8 * (N : ℝ)) +
          (3 * ((A + N : ℕ) : ℝ) ^ (Ls.length + 3) /
            (16 * (N : ℝ) * X * ((Ls.length + 2).factorial : ℝ))) *
            reciprocalShiftFactor Ls) := by
  have hbase := inverseSquare_exponential_sum_high_derivative
    X hX hA hN Ls hcut hfit hsmall
  have hconj :
      conj (∑ n ∈ Finset.Icc 1 N,
        e (-X / ((A + n : ℕ) : ℝ) ^ 2)) =
      ∑ n ∈ Finset.Icc 1 N,
        e (X / ((A + n : ℕ) : ℝ) ^ 2) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [conj_e_eq_e_neg]
    congr 1
    ring
  rw [← hconj, Complex.norm_conj]
  exact hbase

end

end InverseSquareHigherDerivative
end Erdos378
