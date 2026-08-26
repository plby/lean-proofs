import ErdosProblems.Erdos421.Blocks

/-!
# Arithmetic of the rejected-gap forest

These lemmas prove the multiplier alternatives in Section 3 of the selected
Sneiderman note. No point-count or prime-gap estimate is assumed here.
-/

namespace Erdos421

/-- A prime dividing a product on a later numerical interval has a multiplier there. -/
theorem exists_multiplier_in_interval {p m n : ℕ} (hp : p.Prime) (hpm : p < m)
    (hdiv : p ∣ (Finset.Icc m n).prod id) :
    ∃ a : ℕ, 2 ≤ a ∧ m ≤ a * p ∧ a * p ≤ n := by
  obtain ⟨x, hx, hpx⟩ := (hp.prime.dvd_finsetProd_iff id).mp hdiv
  obtain ⟨a, rfl⟩ := hpx
  have hbounds := Finset.mem_Icc.mp hx
  refine ⟨a, ?_, ?_, ?_⟩
  · by_contra h
    have ha : a ≤ 1 := by omega
    have := Nat.mul_le_mul_left p ha
    simp only [mul_one] at this
    omega
  · simpa [mul_comm] using hbounds.1
  · simpa [mul_comm] using hbounds.2

/-- Distinct multipliers imply the scale-contraction inequality, without division. -/
theorem unequal_multiplier_bound {p q g m n s a b : ℕ}
    (hq : q = p + g) (hs : n + 1 = m + s)
    (ha : m ≤ a * p ∧ a * p ≤ n) (hb : m ≤ b * q ∧ b * q ≤ n)
    (hab : a ≠ b) : p ^ 2 ≤ n * g + p * s := by
  have hnear1 : a * p ≤ b * q + s := by omega
  have hnear2 : b * q ≤ a * p + s := by omega
  rcases lt_or_gt_of_ne hab with hab | hab
  · have hab' : (a + 1) * p ≤ b * p := Nat.mul_le_mul_right p hab
    have hps : p ≤ s := by nlinarith
    have := Nat.mul_le_mul_left p hps
    nlinarith
  · have hab' : (b + 1) * p ≤ a * p := Nat.mul_le_mul_right p hab
    have hpgs : p ≤ b * g + s := by nlinarith
    have hbp : b * p ≤ n := by nlinarith [hb.2]
    have h1 := Nat.mul_le_mul_left p hpgs
    have h2 := Nat.mul_le_mul_right g hbp
    nlinarith

/-- The exact parent-child alternatives, given the two prime divisibilities. -/
theorem parent_child_alternatives {p q m n : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hqm : q < m)
    (hpdvd : p ∣ (Finset.Icc m n).prod id)
    (hqdvd : q ∣ (Finset.Icc m n).prod id) :
    (∃ j : ℕ, 2 ≤ j ∧ m ≤ j * p ∧ j * q ≤ n) ∨
      p ^ 2 ≤ n * (q - p) + p * (n - m + 1) := by
  obtain ⟨a, ha2, ham, han⟩ := exists_multiplier_in_interval hp (hpq.trans hqm) hpdvd
  obtain ⟨b, hb2, hbm, hbn⟩ := exists_multiplier_in_interval hq hqm hqdvd
  by_cases hab : a = b
  · exact Or.inl ⟨a, ha2, ham, hab ▸ hbn⟩
  · right
    have hmn : m ≤ n := ham.trans han
    exact unequal_multiplier_bound (by omega) (by omega) ⟨ham, han⟩ ⟨hbm, hbn⟩ hab

/-- Equal multipliers force the child gap to be longer than the scaled parent gap. -/
theorem equal_edge_length {p q P Q j : ℕ} (hpq : p ≤ q)
    (hleft : P < j * p) (hright : j * q < Q) : j * (q - p) < Q - P := by
  have hid : j * q = j * p + j * (q - p) := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hpq]
  omega

/-- The endpoints propagated along a string of equal edges stay inside its terminal gap. -/
theorem equal_edge_composition {p q P Q R S J j : ℕ}
    (hJ : P < J * p ∧ J * q < Q)
    (hj : R < j * P ∧ j * Q < S) (hjpos : 0 < j) :
    R < (j * J) * p ∧ (j * J) * q < S := by
  constructor
  · have h := Nat.mul_lt_mul_of_pos_left hJ.1 hjpos
    simpa only [mul_assoc] using hj.1.trans h
  · have h := Nat.mul_lt_mul_of_pos_left hJ.2 hjpos
    simpa only [mul_assoc] using h.trans hj.2

end Erdos421
