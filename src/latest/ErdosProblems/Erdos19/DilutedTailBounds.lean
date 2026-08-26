import ErdosProblems.Erdos19.DilutedMeanLocal
import Mathlib.Data.Nat.Choose.Bounds

/-! # Exponentially small tails for the diluted random coloring round -/

namespace Erdos19

attribute [local instance] Classical.propDecidable

theorem choose_certificate_ratio_le_half_pow (C T K s : ℕ)
    (hK : 0 < K) (hs : 0 < s) (hmargin : 8 * C * T ≤ s * K ^ 3) :
    ((C.choose s : ℝ) * (T : ℝ) ^ s) / (K : ℝ) ^ (3 * s) ≤ (1 / 2 : ℝ) ^ s := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hfactor : ((s : ℝ) / 3) ^ s ≤ (s.factorial : ℝ) := by
    apply le_trans _ (div_exp_pow_le_factorial s)
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_left hsR.le (Real.exp_pos 1) Real.exp_one_lt_three.le
  have hchoose : (C.choose s : ℝ) ≤ (3 * (C : ℝ) / s) ^ s := by
    calc
      (C.choose s : ℝ) ≤ (C : ℝ) ^ s / s.factorial := Nat.choose_le_pow_div s C
      _ ≤ (C : ℝ) ^ s / ((s : ℝ) / 3) ^ s :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hfactor
      _ = _ := by
        rw [← div_pow]
        congr 1
        field_simp
  have hmarginR : (8 : ℝ) * C * T ≤ s * (K : ℝ) ^ 3 := by exact_mod_cast hmargin
  have hbase : 3 * (C : ℝ) * T / ((s : ℝ) * K ^ 3) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hnonneg : (0 : ℝ) ≤ (C : ℝ) * T := by positivity
    nlinarith only [hmarginR, hnonneg]
  calc
    ((C.choose s : ℝ) * (T : ℝ) ^ s) / (K : ℝ) ^ (3 * s) ≤
        ((3 * (C : ℝ) / s) ^ s * (T : ℝ) ^ s) / (K : ℝ) ^ (3 * s) := by
      gcongr
    _ = (3 * (C : ℝ) * T / ((s : ℝ) * K ^ 3)) ^ s := by
      rw [pow_mul, ← mul_pow, ← div_pow]
      congr 1
      field_simp
    _ ≤ (1 / 2 : ℝ) ^ s := pow_le_pow_left₀ (by positivity) hbase s

theorem card_dilutedSpoiledExcess_ratio_le_half_pow {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) {A C Δ : ℕ} (active : Fin A) (v : V) (b : ℕ)
    (hC : 0 < C) (hdegree : ∀ x, (G.neighborSet x).ncard ≤ Δ)
    (hambient : 3 * (b + 1) ≤ Fintype.card V)
    (hmargin : 8 * C * (2 * (nonadjacentNeighborPairGraph G v).edgeSet.ncard * Δ) ≤
      (b + 1) * (A * C) ^ 3) :
    ((eventFinset {sample : V → Fin A × Fin C |
      b < (spoiledCollisionColors G (dilutedSample active sample) v).ncard}).card : ℝ) /
      Fintype.card (V → Fin A × Fin C) ≤ (1 / 2 : ℝ) ^ (b + 1) := by
  have hA : 0 < A := Nat.zero_lt_of_lt active.isLt
  have hK : (0 : ℝ) < A * C := by positivity
  have hcount := card_dilutedSpoiledExcess_le_of_degree G (C := C) active v b hdegree
  have hcountR : ((eventFinset {sample : V → Fin A × Fin C |
      b < (spoiledCollisionColors G (dilutedSample active sample) v).ncard}).card : ℝ) ≤
      ((C.choose (b + 1) : ℝ) *
        (2 * ((nonadjacentNeighborPairGraph G v).edgeSet.ncard : ℝ) * Δ) ^ (b + 1)) *
        ((A : ℝ) * C) ^ (Fintype.card V - 3 * (b + 1)) := by exact_mod_cast hcount
  have hden : (Fintype.card (V → Fin A × Fin C) : ℝ) = ((A : ℝ) * C) ^ Fintype.card V := by
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Nat.cast_pow, Nat.cast_mul]
  have hpow : ((A : ℝ) * C) ^ Fintype.card V = ((A : ℝ) * C) ^ (3 * (b + 1)) *
      ((A : ℝ) * C) ^ (Fintype.card V - 3 * (b + 1)) := by
    rw [← pow_add, Nat.add_sub_of_le hambient]
  rw [hden]
  apply le_trans (div_le_div_of_nonneg_right hcountR (by positivity))
  rw [hpow, mul_div_mul_right _ _ (pow_ne_zero _ hK.ne')]
  have hbound := choose_certificate_ratio_le_half_pow C
    (2 * (nonadjacentNeighborPairGraph G v).edgeSet.ncard * Δ)
    (A * C) (b + 1) (Nat.mul_pos hA hC) (by omega) hmargin
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbound

theorem card_dilutedTentativeShortfall_ratio_le_exp {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) {A C : ℕ} [Nonempty (Fin A × Fin C)]
    (active : Fin A) (v : V) [Fintype (G.neighborSet v)] (default : Fin A × Fin C)
    (a : ℕ) (hC : 0 < C) (hdegree : 2 ≤ (G.neighborSet v).ncard)
    (hpalette : 2 * (G.neighborSet v).ncard ≤ A * C) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hmargin : (a : ℝ) + epsilon ≤
      ((nonadjacentNeighborPairGraph G v).edgeSet.ncard : ℝ) / (2 * (A : ℝ) ^ 2 * C)) :
    ((eventFinset {sample : V → Fin A × Fin C |
      (tentativeCollisionColors G (dilutedSample active sample) v).ncard < a}).card : ℝ) /
        Fintype.card (V → Fin A × Fin C) ≤
      Real.exp (-epsilon ^ 2 / (2 * Fintype.card (G.neighborFinset v) * (2 : ℝ) ^ 2)) := by
  apply card_dilutedTentativeCollisionShortfallSet_le_exp G active v
    (by
      have hd : 0 < (G.neighborSet v).ncard := by omega
      simpa only [Fintype.card_coe, G.card_neighborFinset_eq_degree,
        ← G.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hd)
    default a hepsilon
  rw [dilutedTentativeFinStatistic_finiteAverage_eq]
  exact hmargin.trans (dilutedTentative_average_lower_bound G active v hC hdegree hpalette)

#print axioms card_dilutedSpoiledExcess_ratio_le_half_pow
#print axioms card_dilutedTentativeShortfall_ratio_le_exp

end Erdos19
