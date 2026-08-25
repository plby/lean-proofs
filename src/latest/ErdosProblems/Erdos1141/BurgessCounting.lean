import ErdosProblems.Erdos1141.ElementaryBounds

/-!
# Counting equal ratios in Burgess's averaging argument

For prefix sums the congruence of two ratios becomes an equality of integer
products when `A*N < q`. Divisor counts then give a convenient upper bound.
-/

open scoped BigOperators

namespace Erdos1141

def ratioPairs (A N : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (((Finset.Icc 1 A).product (Finset.Icc 1 N)).product
    ((Finset.Icc 1 A).product (Finset.Icc 1 N))).filter
    fun z ↦ z.1.1 * z.2.2 = z.2.1 * z.1.2

lemma mem_ratioPairs {A N a n b m : ℕ} :
    ((a, n), (b, m)) ∈ ratioPairs A N ↔
      (1 ≤ a ∧ a ≤ A) ∧ (1 ≤ n ∧ n ≤ N) ∧
      (1 ≤ b ∧ b ≤ A) ∧ (1 ≤ m ∧ m ≤ N) ∧ a * m = b * n := by
  simp only [ratioPairs, Finset.mem_filter, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc]
  tauto

/-- Encode an equal-ratio pair by the common product and two of its divisors. -/
theorem card_ratioPairs_le (A N : ℕ) :
    (ratioPairs A N).card ≤ ∑ t ∈ Finset.Icc 1 (A * N), t.divisors.card ^ 2 := by
  classical
  let target : Finset (Σ _t : ℕ, ℕ × ℕ) :=
    (Finset.Icc 1 (A * N)).sigma fun t ↦ t.divisors.product t.divisors
  let encode : ((ℕ × ℕ) × (ℕ × ℕ)) → (Σ _t : ℕ, ℕ × ℕ) :=
    fun z ↦ ⟨z.1.1 * z.2.2, z.1.1, z.2.1⟩
  have hmaps : ∀ z ∈ ratioPairs A N, encode z ∈ target := by
    rintro ⟨⟨a, n⟩, ⟨b, m⟩⟩ hz
    obtain ⟨ha, hn, hb, hm, heq⟩ := mem_ratioPairs.mp hz
    have ht : 0 < a * m := Nat.mul_pos ha.1 hm.1
    simp only [target, encode, Finset.mem_sigma, Finset.mem_Icc, Finset.product_eq_sprod,
      Finset.mem_product, Nat.mem_divisors]
    exact ⟨⟨ht, Nat.mul_le_mul ha.2 hm.2⟩,
      ⟨dvd_mul_right a m, ht.ne'⟩, ⟨heq.symm ▸ dvd_mul_right b n, ht.ne'⟩⟩
  have hinj : Set.InjOn encode (ratioPairs A N) := by
    rintro ⟨⟨a, n⟩, ⟨b, m⟩⟩ hx ⟨⟨a', n'⟩, ⟨b', m'⟩⟩ hy he
    obtain ⟨ha, hn, hb, hm, hprod⟩ := mem_ratioPairs.mp hx
    obtain ⟨ha', hn', hb', hm', hprod'⟩ := mem_ratioPairs.mp hy
    have ht : a * m = a' * m' := congrArg Sigma.fst he
    have haeq : a = a' := congrArg (fun z : Σ _t : ℕ, ℕ × ℕ ↦ z.2.1) he
    have hbeq : b = b' := congrArg (fun z : Σ _t : ℕ, ℕ × ℕ ↦ z.2.2) he
    subst a'
    subst b'
    have hm_eq : m = m' := Nat.eq_of_mul_eq_mul_left ha.1 ht
    subst m'
    have hn_eq : n = n' := Nat.eq_of_mul_eq_mul_left hb.1 (hprod.symm.trans hprod')
    subst n'
    rfl
  have hcard : (ratioPairs A N).card ≤ target.card :=
    Finset.card_le_card_of_injOn encode hmaps hinj
  simpa [target, Finset.card_sigma, Finset.card_product, pow_two] using hcard

/-- Positive numerator/denominator pairs in one residue-class ratio. -/
def ratioFiber (q A N : ℕ) (x : ZMod q) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 A).product (Finset.Icc 1 N)).filter
    fun z ↦ z.1.Coprime q ∧ (z.2 : ZMod q) = x * (z.1 : ZMod q)

lemma mem_ratioFiber {q A N a n : ℕ} {x : ZMod q} :
    (a, n) ∈ ratioFiber q A N x ↔
      (1 ≤ a ∧ a ≤ A) ∧ (1 ≤ n ∧ n ≤ N) ∧
        a.Coprime q ∧ (n : ZMod q) = x * (a : ZMod q) := by
  simp only [ratioFiber, Finset.mem_filter, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc]
  tauto

/-- The short-box hypothesis rules out nonzero multiples of the modulus. -/
lemma ratioFiber_cross_product {q A N a n b m : ℕ} {x : ZMod q}
    (hbox : A * N < q) (h₁ : (a, n) ∈ ratioFiber q A N x)
    (h₂ : (b, m) ∈ ratioFiber q A N x) : a * m = b * n := by
  obtain ⟨ha, hn, _, he₁⟩ := mem_ratioFiber.mp h₁
  obtain ⟨hb, hm, _, he₂⟩ := mem_ratioFiber.mp h₂
  have heq : (a * m : ℕ) ≡ b * n [MOD q] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [he₁, he₂]
    ring
  exact heq.eq_of_lt_of_lt ((Nat.mul_le_mul ha.2 hm.2).trans_lt hbox)
    ((Nat.mul_le_mul hb.2 hn.2).trans_lt hbox)

/-- The second moment of ratio multiplicities is controlled by divisor counts. -/
theorem sum_ratioFiber_card_sq_le (q A N : ℕ) [NeZero q] (hbox : A * N < q) :
    (∑ x : ZMod q, (ratioFiber q A N x).card ^ 2) ≤
      ∑ t ∈ Finset.Icc 1 (A * N), t.divisors.card ^ 2 := by
  classical
  let source : Finset (Σ _x : ZMod q, (ℕ × ℕ) × (ℕ × ℕ)) :=
    Finset.univ.sigma fun x ↦ (ratioFiber q A N x).product (ratioFiber q A N x)
  let forget : (Σ _x : ZMod q, (ℕ × ℕ) × (ℕ × ℕ)) → ((ℕ × ℕ) × (ℕ × ℕ)) :=
    fun z ↦ z.2
  have hmaps : ∀ z ∈ source, forget z ∈ ratioPairs A N := by
    rintro ⟨x, ⟨⟨a, n⟩, ⟨b, m⟩⟩⟩ hz
    have hpair := Finset.mem_product.mp (Finset.mem_sigma.mp hz).2
    obtain ⟨ha, hn, _, _⟩ := mem_ratioFiber.mp hpair.1
    obtain ⟨hb, hm, _, _⟩ := mem_ratioFiber.mp hpair.2
    exact mem_ratioPairs.mpr ⟨ha, hn, hb, hm, ratioFiber_cross_product hbox hpair.1 hpair.2⟩
  have hinj : Set.InjOn forget source := by
    rintro ⟨x, ⟨⟨a, n⟩, ⟨b, m⟩⟩⟩ hx ⟨y, z⟩ hy he
    change ((a, n), (b, m)) = z at he
    subst z
    have hx₁ := (Finset.mem_product.mp (Finset.mem_sigma.mp hx).2).1
    have hy₁ := (Finset.mem_product.mp (Finset.mem_sigma.mp hy).2).1
    obtain ⟨_, _, hcop, hxEq⟩ := mem_ratioFiber.mp hx₁
    obtain ⟨_, _, _, hyEq⟩ := mem_ratioFiber.mp hy₁
    have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr hcop
    have hxy := congrArg (fun v : ZMod q ↦ v * (a : ZMod q)⁻¹) (hxEq.symm.trans hyEq)
    simp only [mul_assoc, ZMod.mul_inv_of_unit _ hu, mul_one] at hxy
    subst y
    rfl
  have hcard : source.card ≤ (ratioPairs A N).card :=
    Finset.card_le_card_of_injOn forget hmaps hinj
  have hcard' : (∑ x : ZMod q, (ratioFiber q A N x).card ^ 2) ≤ (ratioPairs A N).card := by
    simpa [source, Finset.card_sigma, Finset.card_product, pow_two] using hcard
  exact hcard'.trans (card_ratioPairs_le A N)

lemma sum_divisors_card_sq_le_rpow (r : ℕ) (hr : 0 < r) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / (r : ℝ)))
    (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (n.divisors.card : ℝ) ^ 2) ≤
      C ^ 2 * (X : ℝ) ^ (1 + 2 / (r : ℝ)) := by
  by_cases hX : X = 0
  · subst X
    simp [Real.zero_rpow (by positivity : 1 + 2 / (r : ℝ) ≠ 0)]
  have hXpos : (0 : ℝ) < X := by exact_mod_cast Nat.pos_of_ne_zero hX
  calc
    _ ≤ ∑ _n ∈ Finset.Icc 1 X, (C * (X : ℝ) ^ (1 / (r : ℝ))) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
      apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ 2
      exact (hbound n hnpos).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
          (by positivity)) hC.le)
    _ = (X : ℝ) * (C * (X : ℝ) ^ (1 / (r : ℝ))) ^ 2 := by simp
    _ = C ^ 2 * ((X : ℝ) ^ (1 : ℝ) * (X : ℝ) ^ ((1 / (r : ℝ)) * 2)) := by
      have hp : (X : ℝ) ^ ((1 / (r : ℝ)) * 2) = ((X : ℝ) ^ (1 / (r : ℝ))) ^ 2 := by
        simpa only [Nat.cast_ofNat] using Real.rpow_mul_natCast hXpos.le (1 / (r : ℝ)) 2
      rw [Real.rpow_one, hp]
      ring
    _ = _ := by
      rw [← Real.rpow_add hXpos]
      congr 2
      ring

/-- A subpower bound for the energy of the ratio weights, uniformly in the modulus. -/
theorem exists_sum_ratioFiber_sq_le_rpow (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q A N : ℕ) [NeZero q], A * N < q →
      (∑ x : ZMod q, ((ratioFiber q A N x).card : ℝ) ^ 2) ≤
        C * ((A * N : ℕ) : ℝ) ^ (1 + 2 / (r : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_divisors_card_le_rpow r hr
  refine ⟨C ^ 2, pow_pos hC _, ?_⟩
  intro q A N _ hbox
  have hcount : (∑ x : ZMod q, ((ratioFiber q A N x).card : ℝ) ^ 2) ≤
      ∑ t ∈ Finset.Icc 1 (A * N), (t.divisors.card : ℝ) ^ 2 := by
    exact_mod_cast sum_ratioFiber_card_sq_le q A N hbox
  exact hcount.trans (sum_divisors_card_sq_le_rpow r hr C hC hbound (A * N))

end Erdos1141
