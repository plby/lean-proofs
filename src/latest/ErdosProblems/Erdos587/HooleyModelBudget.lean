import ErdosProblems.Erdos587.HooleyWeakHighFoldModel
import ErdosProblems.Erdos587.HooleySeedDyadicBounds

/-! # Polynomial fiber costs in interval-set coordinate models -/

open scoped BigOperators
open Filter Erdos587.GeneralizedAP

namespace Erdos587.CFP

lemma delta_symmetric_model_box_card_le (P : GeneralizedAP) (h : ℕ) :
    (nvCoordBox (fun i => 2 * (h * P.length i))).card ≤ 2 ^ P.rank * (P.dilate h).boxCard := by
  rw [card_nvCoordBox]
  calc
    _ ≤ ∏ i : Fin P.rank, (2 * (h * P.length i + 1)) :=
      Finset.prod_le_prod' (fun i _ => by omega)
    _ = 2 ^ P.rank * (P.dilate h).boxCard := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rfl

def deltaModelFiberConstant (d₀ F B : ℕ) : ℕ := 2 * (d₀ + F + 2 * B + 2)

def deltaModelSeedCoefficient (d₀ F B : ℕ) : ℕ :=
  (2 ^ d₀ * (4 * F)) * deltaModelFiberConstant d₀ F B ^ d₀

lemma delta_model_fiber_cost_le (P : GeneralizedAP) (A : Finset ℤ)
    (L k F d₀ B t : ℕ) (hA : A ⊆ Finset.Icc 0 ((2 ^ L : ℕ) : ℤ))
    (hk : k ≤ L) (hd : P.rank ≤ d₀) (hL : L ≤ B * t)
    (hbox : (P.dilate (2 ^ k)).boxCard ≤ F * (dyadicSumsetWithZero A k).card) :
    2 * (Nat.log 2 (nvCoordBox (fun i => 2 * (2 ^ k * P.length i))).card + 1) ≤
      deltaModelFiberConstant d₀ F B * (t + 1) := by
  let T := (nvCoordBox (fun i => 2 * (2 ^ k * P.length i))).card
  have hT : T ≤ 2 ^ (d₀ + F + (2 * L + 1)) := by
    calc
      T ≤ 2 ^ P.rank * (P.dilate (2 ^ k)).boxCard := delta_symmetric_model_box_card_le P _
      _ ≤ 2 ^ d₀ * (F * 2 ^ (2 * L + 1)) := Nat.mul_le_mul
        (Nat.pow_le_pow_right (by omega) hd)
        (hbox.trans (Nat.mul_le_mul_left _ (dyadicSumsetWithZero_card_le A L k hA hk)))
      _ ≤ 2 ^ d₀ * (2 ^ F * 2 ^ (2 * L + 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ F.lt_two_pow_self.le)
      _ = 2 ^ (d₀ + F + (2 * L + 1)) := by rw [pow_add, pow_add]; ring
  have hlog : Nat.log 2 T ≤ d₀ + F + (2 * L + 1) :=
    (Nat.log_le_clog 2 T).trans (Nat.clog_le_of_le_pow hT)
  change 2 * (Nat.log 2 T + 1) ≤ _
  dsimp only [deltaModelFiberConstant]
  nlinarith

theorem delta_model_seed_parameter_bound (P : GeneralizedAP) (A : Finset ℤ)
    (L k F d₀ B t : ℕ) (hA : A ⊆ Finset.Icc 0 ((2 ^ L : ℕ) : ℤ))
    (hk : k ≤ L) (hd : P.rank ≤ d₀) (hL : L ≤ B * t)
    (hbox : (P.dilate (2 ^ k)).boxCard ≤ F * (dyadicSumsetWithZero A k).card) :
    let c := 2 * (Nat.log 2 (nvCoordBox (fun i => 2 * (2 ^ k * P.length i))).card + 1)
    let M := 2 ^ P.rank * (4 * F * 2 ^ t)
    M * c ^ P.rank ≤ deltaModelSeedCoefficient d₀ F B * 2 ^ t * (t + 1) ^ d₀ := by
  let c := 2 * (Nat.log 2 (nvCoordBox (fun i => 2 * (2 ^ k * P.length i))).card + 1)
  have hc : c ≤ deltaModelFiberConstant d₀ F B * (t + 1) :=
    delta_model_fiber_cost_le P A L k F d₀ B t hA hk hd hL hbox
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hcpow : c ^ P.rank ≤ (deltaModelFiberConstant d₀ F B * (t + 1)) ^ d₀ :=
    (Nat.pow_le_pow_right hcpos hd).trans (Nat.pow_le_pow_left hc d₀)
  calc
    _ ≤ (2 ^ d₀ * (4 * F * 2 ^ t)) *
        (deltaModelFiberConstant d₀ F B * (t + 1)) ^ d₀ := Nat.mul_le_mul
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hd)) hcpow
    _ = _ := by dsimp only [deltaModelSeedCoefficient]; rw [mul_pow]; ring

theorem delta_eventually_model_seed_power (d₀ F B b : ℕ)
    (hb : deltaSeedPower d₀ + 1 ≤ b) :
    ∀ᶠ t : ℕ in atTop, ∀ (P : GeneralizedAP) (A : Finset ℤ) (L k : ℕ),
      A ⊆ Finset.Icc 0 ((2 ^ L : ℕ) : ℤ) → k ≤ L → P.rank ≤ d₀ → L ≤ B * t →
      (P.dilate (2 ^ k)).boxCard ≤ F * (dyadicSumsetWithZero A k).card →
      let c := 2 * (Nat.log 2 (nvCoordBox (fun i => 2 * (2 ^ k * P.length i))).card + 1)
      let D := (2 ^ P.rank * (4 * F * 2 ^ t)) * c ^ P.rank
      0 < D → deltaSeedCostConstant P.rank * D ^ deltaSeedPower P.rank ≤ 2 ^ (b * t) := by
  filter_upwards [delta_eventually_uniform_seed_power d₀ (deltaModelSeedCoefficient d₀ F B)
    d₀ b hb] with t ht
  intro P A L k hA hk hd hL hbox
  dsimp only
  intro hD
  exact ht P.rank hd _ hD (delta_model_seed_parameter_bound P A L k F d₀ B t hA hk hd hL hbox)

end Erdos587.CFP
