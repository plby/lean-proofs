import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open scoped BigOperators

/-- Ordered pairs of distinct elements of `S` which are not coprime. -/
def noncoprimeOrderedPairs (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  (S ×ˢ S).filter fun z => z.1 ≠ z.2 ∧ ¬Nat.Coprime z.1 z.2

/-- Elements of `S` divisible by `d`. -/
def multiplesIn (S : Finset ℕ) (d : ℕ) : Finset ℕ :=
  S.filter fun n => d ∣ n

/-- An interval of diameter `G` contains at most `G / p + 1` multiples of a
positive integer `p`. -/
theorem multiplesIn_interval_card_le
    (S : Finset ℕ) (L G p : ℕ) (hp : 0 < p)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G) :
    (multiplesIn S p).card ≤ G / p + 1 := by
  let M := multiplesIn S p
  let f : ℕ → ℕ := fun n => (n - L) / p
  have hinj : Set.InjOn f (M : Set ℕ) := by
    intro x hx y hy heq
    have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
    have hyS : y ∈ S := (Finset.mem_filter.mp hy).1
    have hpx : p ∣ x := (Finset.mem_filter.mp hx).2
    have hpy : p ∣ y := (Finset.mem_filter.mp hy).2
    have hxL := (hinterval x hxS).1
    have hyL := (hinterval y hyS).1
    rcases le_total x y with hxy | hyx
    · have hpdiv : p ∣ y - x := Nat.dvd_sub hpy hpx
      have hxlow : p * ((x - L) / p) ≤ x - L := Nat.mul_div_le _ _
      have hyup : y - L < p * ((y - L) / p + 1) := Nat.lt_mul_div_succ _ hp
      have hdiffshift : (y - L) - (x - L) = y - x := by omega
      have hdiff : y - x < p := by
        dsimp [f] at heq
        rw [← heq, Nat.mul_add] at hyup
        simp only [mul_one] at hyup
        rw [← hdiffshift]
        omega
      have hz : y - x = 0 := Nat.eq_zero_of_dvd_of_lt hpdiv hdiff
      omega
    · exact (by
        apply Eq.symm
        apply Nat.le_antisymm hyx
        have hpdiv : p ∣ x - y := Nat.dvd_sub hpx hpy
        have hylow : p * ((y - L) / p) ≤ y - L := Nat.mul_div_le _ _
        have hxup : x - L < p * ((x - L) / p + 1) := Nat.lt_mul_div_succ _ hp
        have hdiffshift : (x - L) - (y - L) = x - y := by omega
        have hdiff : x - y < p := by
          dsimp [f] at heq
          rw [heq, Nat.mul_add] at hxup
          simp only [mul_one] at hxup
          rw [← hdiffshift]
          omega
        have hz : x - y = 0 := Nat.eq_zero_of_dvd_of_lt hpdiv hdiff
        omega)
  have himage : M.image f ⊆ Finset.range (G / p + 1) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨n, hn, rfl⟩
    have hnS : n ∈ S := (Finset.mem_filter.mp hn).1
    have hnL := (hinterval n hnS).1
    have hnG := (hinterval n hnS).2
    apply Finset.mem_range.mpr
    dsimp [f]
    have hsub : n - L ≤ G := by omega
    have := (Nat.div_le_div_right hsub : (n - L) / p ≤ G / p)
    omega
  calc
    M.card = (M.image f).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.range (G / p + 1)).card := Finset.card_le_card himage
    _ = G / p + 1 := Finset.card_range _

/-- If all prime factors of elements of `S` exceed `Y` and `S` has diameter at
most `G`, every noncoprime distinct pair is covered by a prime `p` in `(Y,G]`.
Consequently any bounds on the number of multiples of each such prime give a
union-bound estimate for the number of bad ordered pairs. -/
theorem noncoprimeOrderedPairs_card_le_primeFiber_sum
    (S : Finset ℕ) (Y G : ℕ) (cap : ℕ → ℕ)
    (hrough : ∀ n ∈ S, ∀ p, Nat.Prime p → p ∣ n → Y < p)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, Nat.dist x y ≤ G)
    (hcap : ∀ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
      (multiplesIn S p).card ≤ cap p) :
    (noncoprimeOrderedPairs S).card ≤
      ∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow, (cap p) ^ 2 := by
  let P := (G + 1).primesBelow \ (Y + 1).primesBelow
  let U : Finset (ℕ × ℕ) := P.biUnion fun p => multiplesIn S p ×ˢ multiplesIn S p
  have hcover : noncoprimeOrderedPairs S ⊆ U := by
    intro z hz
    rcases z with ⟨x, y⟩
    have hz' := Finset.mem_filter.mp hz
    have hxS : x ∈ S := (Finset.mem_product.mp hz'.1).1
    have hyS : y ∈ S := (Finset.mem_product.mp hz'.1).2
    have hxy : x ≠ y := hz'.2.1
    have hgcd1 : Nat.gcd x y ≠ 1 := by
      exact fun h => hz'.2.2 (Nat.coprime_iff_gcd_eq_one.mpr h)
    let p := (Nat.gcd x y).minFac
    have hpprime : Nat.Prime p := Nat.minFac_prime hgcd1
    have hpdvdgcd : p ∣ Nat.gcd x y := Nat.minFac_dvd _
    have hpdx : p ∣ x := hpdvdgcd.trans (Nat.gcd_dvd_left x y)
    have hpdy : p ∣ y := hpdvdgcd.trans (Nat.gcd_dvd_right x y)
    have hpY : Y < p := hrough x hxS p hpprime hpdx
    have hpdist : p ∣ Nat.dist x y := by
      rcases le_total x y with hle | hle
      · rw [Nat.dist_eq_sub_of_le hle]
        exact Nat.dvd_sub hpdy hpdx
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hle]
        exact Nat.dvd_sub hpdx hpdy
    have hdistpos : 0 < Nat.dist x y := Nat.dist_pos_of_ne hxy
    have hpG : p ≤ G := (Nat.le_of_dvd hdistpos hpdist).trans (hdiam x hxS y hyS)
    have hpP : p ∈ P := by
      apply Finset.mem_sdiff.mpr
      constructor
      · exact Nat.mem_primesBelow.mpr ⟨by omega, hpprime⟩
      · intro hp
        have hplt := (Nat.mem_primesBelow.mp hp).1
        omega
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hpP, ?_⟩
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨hxS, hpdx⟩
    · exact Finset.mem_filter.mpr ⟨hyS, hpdy⟩
  calc
    (noncoprimeOrderedPairs S).card ≤ U.card := Finset.card_le_card hcover
    _ ≤ ∑ p ∈ P, (multiplesIn S p ×ˢ multiplesIn S p).card :=
      Finset.card_biUnion_le
    _ = ∑ p ∈ P, ((multiplesIn S p).card) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.card_product, pow_two]
    _ ≤ ∑ p ∈ P, (cap p) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact Nat.pow_le_pow_left (hcap p hp) 2

/-- Direct interval form of the rough-pair union bound. -/
theorem noncoprimeOrderedPairs_card_le_interval_prime_sum
    (S : Finset ℕ) (L G Y : ℕ)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hrough : ∀ n ∈ S, ∀ p, Nat.Prime p → p ∣ n → Y < p) :
    (noncoprimeOrderedPairs S).card ≤
      ∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow, (G / p + 1) ^ 2 := by
  apply noncoprimeOrderedPairs_card_le_primeFiber_sum S Y G
    (fun p => G / p + 1) hrough
  · intro x hx y hy
    have hxI := hinterval x hx
    have hyI := hinterval y hy
    rcases le_total x y with hxy | hyx
    · rw [Nat.dist_eq_sub_of_le hxy]
      omega
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hyx]
      omega
  · intro p hp
    have hpprime := (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).2
    exact multiplesIn_interval_card_le S L G p hpprime.pos hinterval

/-- A positive integral ray contains at most one primitive lattice point. -/
theorem nat_pair_eq_of_proportional_of_coprime
    (x₁ y₁ x₂ y₂ : ℕ)
    (hprop : x₁ * y₂ = y₁ * x₂)
    (hc₁ : Nat.Coprime x₁ y₁) (hc₂ : Nat.Coprime x₂ y₂) :
    x₁ = x₂ ∧ y₁ = y₂ := by
  have hx₁x₂ : x₁ ∣ x₂ := by
    apply hc₁.dvd_of_dvd_mul_left
    exact ⟨y₂, hprop.symm⟩
  have hx₂x₁ : x₂ ∣ x₁ := by
    apply hc₂.dvd_of_dvd_mul_left
    refine ⟨y₁, ?_⟩
    calc
      y₂ * x₁ = x₁ * y₂ := mul_comm _ _
      _ = y₁ * x₂ := hprop
      _ = x₂ * y₁ := mul_comm _ _
  have hy₁y₂ : y₁ ∣ y₂ := by
    apply hc₁.symm.dvd_of_dvd_mul_right
    refine ⟨x₂, ?_⟩
    calc
      y₂ * x₁ = x₁ * y₂ := mul_comm _ _
      _ = y₁ * x₂ := hprop
  have hy₂y₁ : y₂ ∣ y₁ := by
    apply hc₂.symm.dvd_of_dvd_mul_right
    refine ⟨x₁, ?_⟩
    calc
      y₁ * x₂ = x₁ * y₂ := hprop.symm
      _ = y₂ * x₁ := mul_comm _ _
  exact ⟨Nat.dvd_antisymm hx₁x₂ hx₂x₁, Nat.dvd_antisymm hy₁y₂ hy₂y₁⟩

end Erdos489
