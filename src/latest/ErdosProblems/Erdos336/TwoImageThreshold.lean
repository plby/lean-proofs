import ErdosProblems.Erdos336.TwoImagePartition

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

/-- Monotonicity of the normalized `3n-3` threshold, in a division-free form. -/
theorem three_minus_three_mono_support
    (s n d a : ℕ) (hs : 0 < s) (hsn : s ≤ n)
    (h : n * d ≥ 3 * (n - 1) * a) :
    s * d ≥ 3 * (s - 1) * a := by
  have hn : 0 < n := lt_of_lt_of_le hs hsn
  have hid0 : n * (s - 1) + (n - s) = s * (n - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
    simp only [mul_one]
    rw [mul_comm s n]
    have hnle : n ≤ n * s := by
      have hm := Nat.mul_le_mul_left n (by omega : 1 ≤ s)
      simpa using hm
    omega
  have hid :
      n * (3 * (s - 1) * a) + 3 * (n - s) * a =
        s * (3 * (n - 1) * a) := by
    calc
      n * (3 * (s - 1) * a) + 3 * (n - s) * a =
          3 * a * (n * (s - 1) + (n - s)) := by ring
      _ = 3 * a * (s * (n - 1)) := by rw [hid0]
      _ = s * (3 * (n - 1) * a) := by ring
  have hmult := Nat.mul_le_mul_left s h
  have hscaled : n * (3 * (s - 1) * a) ≤ n * (s * d) := by
    calc
      n * (3 * (s - 1) * a) ≤
          n * (3 * (s - 1) * a) + 3 * (n - s) * a := Nat.le_add_right _ _
      _ = s * (3 * (n - 1) * a) := hid
      _ ≤ s * (n * d) := hmult
      _ = n * (s * d) := by ring
  exact Nat.le_of_mul_le_mul_left hscaled hn

/-- A two-class / three-double-class quotient is incompatible with a strict
`3(1-1/s)` doubling inequality in `ℤ × H`. -/
theorem not_two_image_three_sum_of_strict_threshold
    {H Q : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    [AddCommGroup Q] [DecidableEq Q]
    (T : Finset (ℤ × H)) (ρ : (ℤ × H) →+ Q) (hzero : (0, 0) ∈ T)
    (hthreshold : (T.image Prod.fst).card * (T + T).card <
      3 * ((T.image Prod.fst).card - 1) * T.card)
    (himage : (T.image ρ).card = 2)
    (hdoubleImage : ((T + T).image ρ).card = 3) : False := by
  classical
  let A₀ := zeroImagePart T ρ
  let A₁ := nonzeroImagePart T ρ
  obtain ⟨hA₀ne, hA₁ne, hTunion, hD00_01, hD00_11, hD01_11, hsum⟩ :=
    two_image_three_sum_partition T ρ hzero himage hdoubleImage
  let n₀ := (A₀.image Prod.fst).card
  let n₁ := (A₁.image Prod.fst).card
  let n := n₀ + n₁
  let s := (T.image Prod.fst).card
  let d := (T + T).card
  let a := T.card
  have hn₀ : 0 < n₀ := (hA₀ne.image Prod.fst).card_pos
  have hn₁ : 0 < n₁ := (hA₁ne.image Prod.fst).card_pos
  have hpartsDisj : Disjoint A₀ A₁ := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    exact (mem_nonzeroImagePart.mp hx1).2 (mem_zeroImagePart.mp hx0).2
  have hacard : A₀.card + A₁.card = a := by
    change A₀.card + A₁.card = T.card
    rw [hTunion, Finset.card_union_of_disjoint hpartsDisj]
  have hsupportEq : T.image Prod.fst =
      A₀.image Prod.fst ∪ A₁.image Prod.fst := by
    rw [hTunion, Finset.image_union]
  have hsn : s ≤ n := by
    change (T.image Prod.fst).card ≤
      (A₀.image Prod.fst).card + (A₁.image Prod.fst).card
    rw [hsupportEq]
    exact Finset.card_union_le _ _
  have hs : 0 < s := by
    have hTne : T.Nonempty := ⟨(0, 0), hzero⟩
    exact (hTne.image Prod.fst).card_pos
  have hprop := projection_two_piece_bound A₀ A₁ hA₀ne hA₁ne
  change n * ((A₀ + A₀).card + (A₀ + A₁).card + (A₁ + A₁).card) ≥
    3 * (n - 1) * (A₀.card + A₁.card) at hprop
  have hsum' :
      (A₀ + A₀).card + (A₀ + A₁).card + (A₁ + A₁).card ≤ d := hsum
  have hbase : n * d ≥ 3 * (n - 1) * a := by
    rw [← hacard]
    exact le_trans hprop (Nat.mul_le_mul_left n hsum')
  have hcontra := three_minus_three_mono_support s n d a hs hsn hbase
  exact (Nat.not_lt_of_ge hcontra hthreshold)

end Erdos336
