import ErdosProblems.Erdos587.HooleyIntervalMass
import ErdosProblems.Erdos587.HooleyExtractionConstants

/-! # Uniform full-width extraction on a fixed dyadic interval scale -/

open scoped BigOperators Pointwise
open Filter Erdos587.GeneralizedAP

namespace Erdos587.CFP

lemma delta_eventually_constant_mul_two_pow (a e : ℕ) :
    ∀ᶠ t : ℕ in atTop, a * 2 ^ (e * t) ≤ 2 ^ ((e + 1) * t) := by
  filter_upwards [delta_eventually_dyadic_polynomial_power a 1 0 e] with t ht
  simpa only [pow_zero, mul_one, one_mul, ← pow_mul, Nat.mul_comm t e] using ht

theorem exists_delta_dyadic_full_width :
    ∃ b R d₀ F C : ℕ, 0 < b ∧ 0 < R ∧ 0 < d₀ ∧ 0 < F ∧ 0 < C ∧
      ∀ᶠ t : ℕ in atTop, ∀ A : Finset ℤ,
        A ⊆ Finset.Icc 1 ((2 ^ (1000 * b * t) : ℕ) : ℤ) →
        2 ^ (20 * b * t) ≤ A.card →
        ∃ m : ℕ, 0 < m ∧ A.card ≤ R * m ∧ m ≤ A.card ∧
          ∃ Q : GeneralizedAP, 0 < Q.rank ∧ Q.rank ≤ d₀ ∧ Q.Proper ∧ Q.HasHomogeneousBase ∧
            (Q.carrier : Set ℤ) ⊆ (A.subsetSum : Set ℤ) ∧
            (∀ i, m ≤ F * Q.length i) ∧ m ^ (Q.rank + 1) ≤ 2 * F ^ Q.rank * Q.carrier.card ∧
            (Q.upperEndpoint : ℝ) ≤ (C : ℝ) * Q.coefficientSpan := by
  classical
  obtain ⟨C₀, K₀, hC₀, hK₀, hmodel⟩ := delta_exists_weak_highFold_model 1000
  let d₀ := freimanRank K₀
  let F₀ := freimanTSizeFactor K₀ 2
  let b := deltaSeedPower d₀ + 1
  let R := 3 ^ (2 * (1000 * b) + 2)
  let K := deltaExtractionScale d₀
  have hb : 0 < b := Nat.succ_pos _
  have hd₀ : 0 < d₀ := freimanRank_pos K₀
  have hF₀ : 0 < F₀ := by
    dsimp only [F₀, freimanTSizeFactor, freimanSizeFactor]
    positivity
  have hR : 0 < R := pow_pos (by omega) _
  have hK : 0 < K := deltaExtractionScale_pos d₀
  have hseedExponent : deltaSeedPower d₀ + 1 ≤ 3 * b := by dsimp only [b]; omega
  have hindexExponent : d₀ + 1 ≤ 3 * b := by
    dsimp only [b, deltaSeedPower]
    nlinarith
  refine ⟨b, 3 * R, d₀, deltaExtractionFactor d₀, 2 * K + 1,
    hb, Nat.mul_pos (by omega) hR, hd₀, deltaExtractionFactor_pos hd₀, Nat.succ_pos _, ?_⟩
  filter_upwards [eventually_ge_atTop 1,
    eventually_nat_polynomial_le_two_pow C₀ 0,
    delta_eventually_dyadic_index_bound d₀ (4 * F₀) (3 * b)
      (Nat.mul_pos (by omega) hF₀) hindexExponent,
    delta_eventually_preprocessing_linear_budget (1000 * b) (3 * b) (Nat.mul_pos (by omega) hb),
    delta_eventually_model_seed_power d₀ F₀ (1000 * b) (3 * b) hseedExponent,
    delta_eventually_constant_mul_two_pow (R * (16 + 2 * K)) (15 * b)]
      with t ht hCscale hindex hlinear hpower hcardScale
  let L := 1000 * b * t
  let k := 3 * b * t
  let h := 2 ^ k
  let M := 4 * F₀ * 2 ^ t
  have hkL : k ≤ L := Nat.mul_le_mul_right t (Nat.mul_le_mul_right b (by omega))
  have hpowt : 2 ^ t ≤ 2 ^ (b * t) :=
    Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hCsmall : C₀ ≤ 2 ^ (b * t) := by
    simp only [pow_zero, mul_one] at hCscale
    exact hCscale.trans hpowt
  have hCfold : C₀ * 2 ^ (b * t + b * t) ≤ h := by
    calc
      _ ≤ 2 ^ (b * t) * 2 ^ (b * t + b * t) := Nat.mul_le_mul_right _ hCsmall
      _ = h := by dsimp only [h, k]; rw [← pow_add]; congr 1; ring
  have hMle : M ≤ h := by
    have hh' := hindex 1 hd₀
    simpa only [M, h, k, pow_one] using hh'
  have hIle : ∀ d ≤ d₀, M ^ d ≤ h := by
    intro d hd
    exact hindex d hd
  have hh : 2 ≤ h := hlinear.1
  have hline : 8 * (L + 1) + 1 ≤ h := hlinear.2
  have hTbound : R * (6 * h ^ 5 + 6 + 2 * K + 4) ≤ 2 ^ (20 * b * t) := by
    have hhone : 1 ≤ h ^ 5 := one_le_pow₀ (by omega)
    have hrest : 10 + 2 * K ≤ (10 + 2 * K) * h ^ 5 :=
      Nat.le_mul_of_pos_right _ hhone
    have hinner : 6 * h ^ 5 + 6 + 2 * K + 4 ≤ (16 + 2 * K) * h ^ 5 := by
      nlinarith only [hrest]
    calc
      _ ≤ R * ((16 + 2 * K) * h ^ 5) := Nat.mul_le_mul_left _ hinner
      _ = (R * (16 + 2 * K)) * h ^ 5 := (Nat.mul_assoc _ _ _).symm
      _ = (R * (16 + 2 * K)) * 2 ^ ((15 * b) * t) := by
        dsimp only [h, k]
        rw [← pow_mul]
        congr 2
        ring
      _ ≤ 2 ^ ((15 * b + 1) * t) := hcardScale
      _ ≤ 2 ^ (20 * b * t) := Nat.pow_le_pow_right (by omega) (by nlinarith)
  intro A hA hAcard
  have hA₀ : A ⊆ Finset.Icc 0 ((2 ^ L : ℕ) : ℤ) := by
    intro a ha
    have hh' := Finset.mem_Icc.mp (hA ha)
    exact Finset.mem_Icc.mpr ⟨by omega, hh'.2⟩
  have hAweak : R * 4 ≤ A.card := (Nat.mul_le_mul_left _ (by omega : 4 ≤
    6 * h ^ 5 + 6 + 2 * K + 4)).trans (hTbound.trans hAcard)
  obtain ⟨B, hBA, hBretain, hBfour, P, hrank, hPpos, _hproper, hzero, hBP, hbox, hweak⟩ :=
    hmodel (1000 * b) A L k (b * t) t hA₀ hkL (Nat.mul_pos hb ht) ht
      (le_of_eq (by dsimp only [L]; ac_rfl)) (le_of_eq (by dsimp only [L]; ac_rfl))
      hCsmall hCfold hMle hAweak
  have hBbig : 6 * h ^ 5 + 6 + 2 * K + 4 ≤ B.card := by
    exact Nat.le_of_mul_le_mul_left ((hTbound.trans hAcard).trans hBretain) hR
  have hBcard : 6 * h ^ 5 + 6 ≤ B.card := by omega
  have hBm : K ≤ B.card / 2 := by omega
  have hB₀ : B ⊆ Finset.Icc 0 ((2 ^ L : ℕ) : ℤ) := hBA.trans hA₀
  have hBpos : ∀ a ∈ B, 0 < a := by
    intro a ha
    have hh' := (Finset.mem_Icc.mp (hA (hBA ha))).1
    omega
  have hseed := hpower P B L k hB₀ hkL hrank (by rfl) hbox
  have hDpos : 0 < (2 ^ P.rank * (4 * F₀ * 2 ^ t)) *
      (2 * (Nat.log 2 (nvCoordBox (fun i => 2 * (2 ^ k * P.length i))).card + 1)) ^ P.rank := by
    exact Nat.mul_pos
      (Nat.mul_pos (pow_pos (by omega) _)
        (Nat.mul_pos (Nat.mul_pos (by omega) hF₀) (pow_pos (by omega) _)))
      (pow_pos (Nat.mul_pos (by omega) (Nat.succ_pos _)) _)
  obtain ⟨hF, Q, hQpos, hQrank, hQproper, hQhom, hQsub, hside, hsize, hheight⟩ :=
    delta_full_width_GAP_of_robust_model P B hzero
      ((Finset.subset_insert 0 B).trans hBP) hPpos hBpos L h M hh (by
        have hMpos : 0 < M := Nat.mul_pos (Nat.mul_pos (by omega) hF₀) (pow_pos (by omega) _)
        omega) (delta_dyadic_interval_mass_le B L hB₀) hweak (hIle P.rank hrank) hline hBcard
      (delta_geometric_threshold_of_card hrank hBm) (hseed hDpos)
  rw [delta_extraction_ceil_eq] at hside hsize hheight
  obtain ⟨hside', hsize', hheight'⟩ := delta_uniform_full_width_bounds Q hrank hside hsize hheight
  refine ⟨B.card / 2, by omega, ?_, (Nat.div_le_self _ _).trans (Finset.card_le_card hBA),
    Q, hQpos, hQrank.trans hrank, hQproper, hQhom,
    hQsub.trans (Finset.subsetSum_mono hBA), hside', hsize', hheight'⟩
  calc
    A.card ≤ R * B.card := hBretain
    _ ≤ R * (3 * (B.card / 2)) := Nat.mul_le_mul_left _ (by omega)
    _ = (3 * R) * (B.card / 2) :=
      (Nat.mul_assoc R 3 _).symm.trans (congrArg (fun x : ℕ => x * (B.card / 2)) (Nat.mul_comm R 3))

end Erdos587.CFP
