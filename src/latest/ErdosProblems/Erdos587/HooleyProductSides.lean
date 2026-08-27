import ErdosProblems.Erdos587.NVDevelopment

/-! # Individual side bounds from a product lower bound and coordinate upper bounds -/

open scoped BigOperators

namespace Erdos587.CFP

lemma delta_product_side_bound {d : ℕ} (a b : Fin d → ℕ) (F q : ℕ)
    (hside : ∀ i, b i ≤ q * a i)
    (hprod : (∏ i, (a i + 1)) ≤ F * ∏ i, (b i + 1)) (i : Fin d) :
    a i + 1 ≤ F * (q + 1) ^ d * (b i + 1) := by
  classical
  let A := ∏ j ∈ Finset.univ.erase i, (a j + 1)
  let B := ∏ j ∈ Finset.univ.erase i, (b j + 1)
  have hAsplit : (a i + 1) * A = ∏ j, (a j + 1) :=
    Finset.mul_prod_erase Finset.univ (fun j => a j + 1) (Finset.mem_univ i)
  have hBsplit : (b i + 1) * B = ∏ j, (b j + 1) :=
    Finset.mul_prod_erase Finset.univ (fun j => b j + 1) (Finset.mem_univ i)
  have hB : B ≤ (q + 1) ^ d * A := by
    calc
      _ ≤ ∏ j ∈ Finset.univ.erase i, (q + 1) * (a j + 1) :=
        Finset.prod_le_prod' (fun j _ => by have := hside j; nlinarith)
      _ = (q + 1) ^ (Finset.univ.erase i).card * A := by
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const, A]
      _ ≤ (q + 1) ^ d * A := by
        apply Nat.mul_le_mul_right
        apply Nat.pow_le_pow_right (by positivity)
        simp
  have hscaled : (a i + 1) * A ≤ (F * (q + 1) ^ d * (b i + 1)) * A := by
    calc
      _ = ∏ j, (a j + 1) := hAsplit
      _ ≤ F * ∏ j, (b j + 1) := hprod
      _ = F * ((b i + 1) * B) := by rw [hBsplit]
      _ ≤ F * ((b i + 1) * ((q + 1) ^ d * A)) :=
        Nat.mul_le_mul_left F (Nat.mul_le_mul_left (b i + 1) hB)
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hscaled (Finset.prod_pos (fun _ _ => Nat.succ_pos _))

lemma delta_coarse_coordinate_side_bound {d : ℕ} (P : NVFullGAP d)
    (hproper : P.Proper) (haxis : P.AxisAligned) (L : Fin d → ℕ) (F q : ℕ)
    (hcard : (nvCoordBox L).card ≤ F * P.carrier.card)
    (hexc : ∀ i, |(P.length i : ℤ) * P.step i i| ≤ (q : ℤ) * L i) :
    ∀ i, L i + 1 ≤ F * (q + 1) ^ d * (P.length i + 1) := by
  have hside (i : Fin d) : P.length i ≤ q * L i := by
    by_cases hi : P.length i = 0
    · simp [hi]
    · have ha := Int.one_le_abs (P.diagonal_ne_zero_of_axisAligned hproper haxis i (by omega))
      have he := hexc i
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ P.length i)] at he
      have hlen : (P.length i : ℤ) ≤ (q : ℤ) * L i := by nlinarith
      exact_mod_cast hlen
  rw [card_nvCoordBox, P.card_carrier_of_proper hproper] at hcard
  exact delta_product_side_bound L P.length F q hside hcard

lemma delta_coarse_step_bound {d : ℕ} (P : NVFullGAP d)
    (hproper : P.Proper) (haxis : P.AxisAligned) (L : Fin d → ℕ) (B q : ℕ) (hB : 0 < B)
    (hside : ∀ i, L i + 1 ≤ B * (P.length i + 1))
    (hexc : ∀ i, |(P.length i : ℤ) * P.step i i| ≤ (q : ℤ) * L i)
    (hlarge : ∀ i, 2 * B ≤ L i) :
    ∀ i, 0 < P.length i ∧ P.step i i ≠ 0 ∧ |P.step i i| ≤ (2 * q * B : ℕ) := by
  intro i
  have hLi : L i ≤ 2 * B * P.length i := by
    have := hside i
    have := hlarge i
    nlinarith
  have hpos : 0 < P.length i := by have := hlarge i; nlinarith
  refine ⟨hpos, P.diagonal_ne_zero_of_axisAligned hproper haxis i hpos, ?_⟩
  have hLiZ : (L i : ℤ) ≤ 2 * (B : ℤ) * P.length i := by exact_mod_cast hLi
  have he := hexc i
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ P.length i)] at he
  have hscaled : (P.length i : ℤ) * |P.step i i| ≤ (P.length i : ℤ) * (2 * q * B : ℕ) := by
    have hq : (0 : ℤ) ≤ q := by positivity
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hLiZ hq]
  exact le_of_mul_le_mul_left hscaled (by exact_mod_cast hpos)

lemma delta_coarse_radius_bound {L P B R : ℕ} (hB : 0 < B)
    (hside : L + 1 ≤ B * (P + 1)) (hlarge : 2 * B * (R + 1) ≤ L) : 2 * R ≤ P := by
  nlinarith

end Erdos587.CFP
