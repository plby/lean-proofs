import ErdosProblems.Erdos157.PairDigits

/-! Carry-compatible target expansions for any finite list of paired data radices. -/

namespace Erdos157.Elementary.PairedTargets

open AuxiliaryDigits

structure Digit (b : ℕ) where
  data : Fin b
  auxiliary : Fin 103

def Digit.aux {b : ℕ} (d : Digit b) : ℕ := 39 + d.auxiliary.val
def Digit.value {b : ℕ} (d : Digit b) : ℕ := d.data.val + b * d.aux

theorem Digit.aux_bounds {b : ℕ} (d : Digit b) : 39 ≤ d.aux ∧ d.aux ≤ 141 := by
  have h := d.auxiliary.isLt
  dsimp only [Digit.aux]
  omega

theorem Digit.aux_carryCovered {b : ℕ} (d : Digit b) : CarryCovered auxiliaryDigitSet d.aux := by
  intro κ hκ
  have hb := d.aux_bounds
  obtain ⟨a, ha, c, hc, e, he, heq⟩ := explicitTripleCoverage
    (n := d.aux - κ) (by omega) (by omega)
  exact ⟨a, ha, c, hc, e, he, by omega⟩

theorem Digit.value_add_two_le {b : ℕ} (d : Digit b) : d.value + 2 ≤ 2 * (103 * b) := by
  have hx := d.data.isLt
  have hy := d.aux_bounds.2
  have hm := Nat.mul_le_mul_left b hy
  dsimp only [Digit.value]
  omega

def digitFrom (b m : ℕ) (hb : 0 < b) : Digit b :=
  ⟨⟨m % b, Nat.mod_lt _ hb⟩, ⟨(m / b + 64) % 103, Nat.mod_lt _ (by decide)⟩⟩

theorem digitFrom_congruent (b m : ℕ) (hb : 0 < b) :
    Nat.ModEq (103 * b) (digitFrom b m hb).value m := by
  have hy : Nat.ModEq 103 (digitFrom b m hb).aux (m / b) := compatibleTripleDigit_modEq _
  have hmul := hy.mul_left' b
  have hadd := hmul.add_left (m % b)
  rw [Nat.mod_add_div] at hadd
  simpa only [Digit.value, digitFrom, mul_comm 103 b] using hadd

theorem exists_step (b P m : ℕ) (hb : 0 < b) (hP : 0 < P)
    (hm : 6 * (103 * b * P) ≤ m + 2) :
    ∃ d : Digit b, ∃ t : ℕ, m = d.value + 103 * b * t ∧ 6 * P ≤ t + 2 := by
  let d := digitFrom b m hb
  have hd := d.value_add_two_le
  have hR : 0 < 103 * b := by omega
  have hRP : 103 * b ≤ 103 * b * P := Nat.le_mul_of_pos_right _ hP
  have hdm : d.value ≤ m := by omega
  have hc := digitFrom_congruent b m hb
  have hv : 103 * b ∣ m - d.value := (Nat.modEq_iff_dvd' hdm).mp hc
  obtain ⟨t, ht⟩ := hv
  have heq : m = d.value + 103 * b * t := by omega
  refine ⟨d, t, heq, ?_⟩
  have hmul : (103 * b) * (6 * P) ≤ (103 * b) * (t + 2) := by nlinarith
  nlinarith

/-- The product type follows the list, so splitting a target list never loses
the relation between a data digit and its radix. -/
def Digits : List ℕ → Type
  | [] => Unit
  | b :: bs => Digit b × Digits bs

def value : {bs : List ℕ} → Digits bs → ℕ
  | [], _ => 0
  | b :: _, d => d.1.value + 103 * b * value d.2

def place (bs : List ℕ) : ℕ := (bs.map (fun b => 103 * b)).prod

theorem place_pos {bs : List ℕ} (hbs : ∀ b ∈ bs, 0 < b) : 0 < place bs := by
  induction bs with
  | nil => exact Nat.zero_lt_one
  | cons b bs ih =>
    change 0 < 103 * b * place bs
    exact Nat.mul_pos (by have := hbs b (by simp); omega)
      (ih (fun c hc => hbs c (by simp [hc])))

theorem value_add_two_le {bs : List ℕ} (d : Digits bs) : value d + 2 ≤ 2 * place bs := by
  induction bs with
  | nil => exact le_refl _
  | cons b bs ih =>
    have hd := d.1.value_add_two_le
    have ht := ih d.2
    change d.1.value + 103 * b * value d.2 + 2 ≤ 2 * (103 * b * place bs)
    have hm := Nat.mul_le_mul_left (103 * b) ht
    nlinarith

theorem exists_expansion (bs : List ℕ) (hbs : ∀ b ∈ bs, 0 < b)
    (m : ℕ) (hm : 6 * place bs ≤ m + 2) :
    ∃ d : Digits bs, ∃ z : ℕ, m = value d + place bs * z ∧ 4 ≤ z := by
  induction bs generalizing m with
  | nil => exact ⟨(), m, by simp [value, place], by simpa [place] using hm⟩
  | cons b bs ih =>
    have hb := hbs b (by simp)
    have htail : ∀ c ∈ bs, 0 < c := fun c hc => hbs c (by simp [hc])
    obtain ⟨d, t, heq, ht⟩ := exists_step b (place bs) m hb (place_pos htail) hm
    obtain ⟨ds, z, hz, hz4⟩ := ih htail t ht
    refine ⟨(d, ds), z, ?_, hz4⟩
    change m = d.value + 103 * b * value ds + (103 * b * place bs) * z
    rw [heq, hz]
    ring

end Erdos157.Elementary.PairedTargets
