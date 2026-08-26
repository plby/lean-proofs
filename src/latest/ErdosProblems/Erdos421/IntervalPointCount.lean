import ErdosProblems.Erdos421.PointSetCount
import ErdosProblems.Erdos421.ImplicitConvex
import ErdosProblems.Erdos421.Counting

/-!
# A uniform count for positive interval-product equations

The positive branch becomes strictly convex after `2r²`. This permits an
elementary lattice-chain argument in place of the general CCDN curve theorem.
-/

namespace Erdos421

def fallingNatProduct (x r : ℕ) : ℕ := ∏ i ∈ Finset.range r, (x - i)

def intervalSolutions (B r s : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc r B) ×ˢ (Finset.Icc 1 B)).filter
    (fun p ↦ fallingNatProduct p.1 r = intervalProduct p.2 s)

theorem mem_intervalSolutions {B r s : ℕ} {p : ℕ × ℕ} :
    p ∈ intervalSolutions B r s ↔
      r ≤ p.1 ∧ p.1 ≤ B ∧ 1 ≤ p.2 ∧ p.2 ≤ B ∧
        fallingNatProduct p.1 r = intervalProduct p.2 s := by
  simp only [intervalSolutions, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

theorem fallingNatProduct_cast {x r : ℕ} (hx : r ≤ x) :
    (fallingNatProduct x r : ℝ) = ∏ i : Fin r, ((x : ℝ) - i) := by
  simp only [fallingNatProduct, Nat.cast_prod]
  rw [← Fin.prod_univ_eq_prod_range (fun i ↦ ((x - i : ℕ) : ℝ))]
  apply Finset.prod_congr rfl
  intro i _
  exact Nat.cast_sub (i.is_lt.le.trans hx)

theorem intervalProduct_cast (y s : ℕ) :
    (intervalProduct y s : ℝ) = ∏ i : Fin s, ((y : ℝ) - -(i : ℝ)) := by
  simp only [intervalProduct, Nat.cast_prod, Nat.cast_add, sub_neg_eq_add]
  exact (Fin.prod_univ_eq_prod_range (fun i ↦ (y : ℝ) + (i : ℝ)) s).symm

theorem solution_root_eq {B r s : ℕ} {p : ℕ × ℕ} (hp : p ∈ intervalSolutions B r s) :
    productRoot s (fun i : Fin r ↦ (i : ℝ)) p.1 =
      productRoot s (fun i : Fin s ↦ -(i : ℝ)) p.2 := by
  obtain ⟨hpx, _, hpy, _, heq⟩ := mem_intervalSolutions.mp hp
  apply productRoot_eq_of_prod_eq
  · intro i
    have hi : (i : ℕ) < p.1 := i.is_lt.trans_le hpx
    exact sub_pos.mpr (by exact_mod_cast hi)
  · intro i
    have hy : (0 : ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
    have hi : (0 : ℝ) ≤ i := by positivity
    linarith
  · rw [← fallingNatProduct_cast hpx, ← intervalProduct_cast]
    exact_mod_cast heq

theorem intervalSolutions_fst_injOn {B r s : ℕ} (hs : 0 < s) :
    Set.InjOn Prod.fst (↑(intervalSolutions B r s) : Set (ℕ × ℕ)) := by
  intro p hp q hq hpq
  have hp' := mem_intervalSolutions.mp hp
  have hq' := mem_intervalSolutions.mp hq
  apply Prod.ext hpq
  exact (intervalProduct_injective hs)
    (hp'.2.2.2.2.symm.trans ((congrArg (fun x ↦ fallingNatProduct x r) hpq).trans hq'.2.2.2.2))

theorem intervalSolutions_snd_strictMono {B r s : ℕ} (hs : 0 < s) (hrs : s < r)
    {p q : ℕ × ℕ} (hp : p ∈ intervalSolutions B r s) (hq : q ∈ intervalSolutions B r s)
    (hpq : p.1 < q.1) : p.2 < q.2 := by
  have hp' := mem_intervalSolutions.mp hp
  have hq' := mem_intervalSolutions.mp hq
  have hshifts : ∀ i : Fin r, (i : ℝ) ≤ (r : ℝ) - 1 := by
    intro i
    have h : (i : ℝ) + 1 ≤ r := by exact_mod_cast i.is_lt
    linarith
  have hF := productRoot_strictMonoOn (hs.trans hrs) hs _ ((r : ℝ) - 1) hshifts
  have hpx : (r : ℝ) ≤ p.1 := by exact_mod_cast hp'.1
  have hqx : (r : ℝ) ≤ q.1 := by exact_mod_cast hq'.1
  have hloglt := hF (show (r : ℝ) - 1 < p.1 by linarith)
    (show (r : ℝ) - 1 < q.1 by linarith) (by exact_mod_cast hpq)
  rw [solution_root_eq hp, solution_root_eq hq] at hloglt
  have hshifts' : ∀ i : Fin s, -(i : ℝ) ≤ 0 := by intro i; exact neg_nonpos.mpr (by positivity)
  have hG := productRoot_strictMonoOn hs hs _ 0 hshifts'
  by_contra h
  have hyq : (0 : ℝ) < q.2 := by exact_mod_cast (show 0 < q.2 by omega)
  have hyp : (0 : ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
  have hle : (q.2 : ℝ) ≤ p.2 := by exact_mod_cast (show q.2 ≤ p.2 by omega)
  exact hloglt.not_ge (hG.monotoneOn hyq hyp hle)

theorem intervalSolutions_large_triple_slopes {B r s : ℕ} (hs : 0 < s) (hrs : s < r)
    {p q v : ℕ × ℕ} (hp : p ∈ intervalSolutions B r s) (hq : q ∈ intervalSolutions B r s)
    (hv : v ∈ intervalSolutions B r s) (hlarge : 2 * r ^ 2 ≤ p.1)
    (hpq : p.1 < q.1) (hqv : q.1 < v.1) :
    ((q.2 : ℝ) - p.2) / ((q.1 : ℝ) - p.1) <
      ((v.2 : ℝ) - q.2) / ((v.1 : ℝ) - q.1) := by
  have hp' := mem_intervalSolutions.mp hp
  have hq' := mem_intervalSolutions.mp hq
  have hv' := mem_intervalSolutions.mp hv
  apply falling_rising_root_slopes hs hrs
  · exact_mod_cast hlarge
  · exact_mod_cast hpq
  · exact_mod_cast hqv
  · exact_mod_cast (show 0 < p.2 by omega)
  · exact_mod_cast (show 0 < q.2 by omega)
  · exact_mod_cast (show 0 < v.2 by omega)
  · exact solution_root_eq hp
  · exact solution_root_eq hq
  · exact solution_root_eq hv

theorem intervalSolutions_large_bound (B r s T : ℕ) (hs : 0 < s) (hrs : s < r)
    (S : Finset (ℕ × ℕ)) (hS : S ⊆ intervalSolutions B r s)
    (hlarge : ∀ p ∈ S, 2 * r ^ 2 ≤ p.1) :
    T * S.card ≤ T ^ 3 + 2 * B + T := by
  apply finite_point_set_bound S T B
  · intro p hp
    have h := mem_intervalSolutions.mp (hS hp)
    exact ⟨h.2.1, h.2.2.2.1⟩
  · exact (intervalSolutions_fst_injOn hs).mono hS
  · intro p hp q hq hpq
    exact intervalSolutions_snd_strictMono hs hrs (hS hp) (hS hq) hpq
  · intro p hp q hq v hv hpq hqv
    exact intervalSolutions_large_triple_slopes hs hrs (hS hp) (hS hq) (hS hv)
      (hlarge p hp) hpq hqv

/-- Coefficient-free counting for the actual positive interval-product equations.
Choosing `T` near `B^(1/3)` gives `O(B^(2/3) + r²)` solutions. -/
theorem intervalSolutions_card_bound (B r s T : ℕ) (hs : 0 < s) (hrs : s < r) :
    T * (intervalSolutions B r s).card ≤ 2 * T * r ^ 2 + T + T ^ 3 + 2 * B := by
  let S := intervalSolutions B r s
  let small := S.filter (fun p ↦ p.1 < 2 * r ^ 2)
  have hsmall : small ⊆ S := Finset.filter_subset _ _
  have hsmallcard : small.card ≤ 2 * r ^ 2 := by
    have hxin : Set.InjOn Prod.fst (↑small : Set (ℕ × ℕ)) :=
      (intervalSolutions_fst_injOn hs).mono hsmall
    calc
      small.card = (small.image Prod.fst).card := (Finset.card_image_iff.mpr hxin).symm
      _ ≤ (Finset.range (2 * r ^ 2)).card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      _ = 2 * r ^ 2 := Finset.card_range _
  have hlarge : ∀ p ∈ S \ small, 2 * r ^ 2 ≤ p.1 := by
    intro p hp
    obtain ⟨hpS, hpnot⟩ := Finset.mem_sdiff.mp hp
    by_contra h
    exact hpnot (Finset.mem_filter.mpr ⟨hpS, by omega⟩)
  have hbig := intervalSolutions_large_bound B r s T hs hrs (S \ small)
    Finset.sdiff_subset hlarge
  have hcards := congrArg (fun n ↦ T * n) (Finset.card_sdiff_add_card_eq_card hsmall)
  rw [Nat.mul_add] at hcards
  have hscaled := Nat.mul_le_mul_left T hsmallcard
  change T * S.card ≤ _
  nlinarith

def lengthPairs (L : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 L) ×ˢ (Finset.Icc 1 L)).filter (fun p ↦ p.2 < p.1)

theorem lengthPairs_card_le (L : ℕ) : (lengthPairs L).card ≤ L ^ 2 := by
  have h := Finset.card_le_card (Finset.filter_subset (fun p : ℕ × ℕ ↦ p.2 < p.1)
    ((Finset.Icc 1 L) ×ˢ (Finset.Icc 1 L)))
  simpa only [lengthPairs, Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel, pow_two] using h

/-- A finite uniform bound summed over all possible pairs of block lengths. -/
theorem sum_intervalSolutions_card_bound (B L T : ℕ) :
    T * (∑ p ∈ lengthPairs L, (intervalSolutions B p.1 p.2).card) ≤
      L ^ 2 * (T ^ 3 + 2 * B + T + 2 * T * L ^ 2) := by
  rw [Finset.mul_sum]
  calc
    (∑ p ∈ lengthPairs L, T * (intervalSolutions B p.1 p.2).card) ≤
        ∑ _p ∈ lengthPairs L, (T ^ 3 + 2 * B + T + 2 * T * L ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp, hsr⟩ := Finset.mem_filter.mp hp
      obtain ⟨hr, hs⟩ := Finset.mem_product.mp hp
      obtain ⟨_, hrL⟩ := Finset.mem_Icc.mp hr
      obtain ⟨hs1, _⟩ := Finset.mem_Icc.mp hs
      have h := intervalSolutions_card_bound B p.1 p.2 T hs1 hsr
      have hpow := Nat.pow_le_pow_left hrL 2
      have hscaled := Nat.mul_le_mul_left (2 * T) hpow
      nlinarith
    _ = (lengthPairs L).card * (T ^ 3 + 2 * B + T + 2 * T * L ^ 2) := by simp
    _ ≤ L ^ 2 * (T ^ 3 + 2 * B + T + 2 * T * L ^ 2) :=
      Nat.mul_le_mul_right _ (lengthPairs_card_le L)

theorem sum_intervalSolutions_card_bound_cube (B L T : ℕ) (hT : 0 < T) (hB : B ≤ T ^ 3) :
    (∑ p ∈ lengthPairs L, (intervalSolutions B p.1 p.2).card) ≤
      L ^ 2 * (3 * T ^ 2 + 1 + 2 * L ^ 2) := by
  have h := sum_intervalSolutions_card_bound B L T
  have hscale : T ^ 3 + 2 * B + T + 2 * T * L ^ 2 ≤
      T * (3 * T ^ 2 + 1 + 2 * L ^ 2) := by nlinarith
  have hscaled := Nat.mul_le_mul_left (L ^ 2) hscale
  have hfinal := h.trans hscaled
  rw [← mul_assoc, mul_comm (L ^ 2) T, mul_assoc] at hfinal
  exact Nat.le_of_mul_le_mul_left hfinal hT

/-- A convenient integer-power scale for the `X^(4/5)` raw-gap bound. -/
theorem sum_intervalSolutions_card_bound_scale (n : ℕ) :
    (∑ p ∈ lengthPairs (2 ^ (4 * n)),
      (intervalSolutions (2 ^ (60 * n)) p.1 p.2).card) ≤ 6 * 2 ^ (48 * n) := by
  have hB : 2 ^ (60 * n) = (2 ^ (20 * n)) ^ 3 := by
    rw [← pow_mul]
    congr 1
    omega
  have h := sum_intervalSolutions_card_bound_cube (2 ^ (60 * n)) (2 ^ (4 * n))
    (2 ^ (20 * n)) (by positivity) hB.le
  have hL : (2 ^ (4 * n)) ^ 2 = 2 ^ (8 * n) := by rw [← pow_mul]; congr 1; omega
  have hT : (2 ^ (20 * n)) ^ 2 = 2 ^ (40 * n) := by rw [← pow_mul]; congr 1; omega
  rw [hL, hT] at h
  have hLT : (2 : ℕ) ^ (8 * n) ≤ 2 ^ (40 * n) := Nat.pow_le_pow_right (by decide) (by omega)
  have hOne : (1 : ℕ) ≤ 2 ^ (40 * n) := Nat.one_le_pow _ _ (by decide)
  have hinside : 3 * 2 ^ (40 * n) + 1 + 2 * 2 ^ (8 * n) ≤ 6 * 2 ^ (40 * n) := by omega
  have hmul := Nat.mul_le_mul_left (2 ^ (8 * n)) hinside
  have hprod : 2 ^ (8 * n) * (6 * 2 ^ (40 * n)) = 6 * 2 ^ (48 * n) := by
    rw [mul_left_comm, ← pow_add]
    congr 2
    omega
  exact h.trans (hmul.trans_eq hprod)

end Erdos421
