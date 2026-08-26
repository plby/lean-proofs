import Mathlib

/-!
# An elementary lattice-chain bound

Distinct positive integer step vectors with bounded total length cannot be
too numerous. This is the counting input for a strictly convex increasing
solution branch.
-/

namespace Erdos421

/-- A finite form of the elementary convex-lattice-chain estimate. -/
theorem vector_card_bound (S : Finset (ℕ × ℕ)) (T B : ℕ)
    (hpos : ∀ v ∈ S, 0 < v.1 ∧ 0 < v.2)
    (hsum : (∑ v ∈ S, (v.1 + v.2)) ≤ B) :
    T * S.card ≤ T ^ 3 + B := by
  let small := S.filter (fun v ↦ v.1 ≤ T ∧ v.2 ≤ T)
  have hsmall : small ⊆ S := Finset.filter_subset _ _
  have hbox : small ⊆ (Finset.Icc 1 T) ×ˢ (Finset.Icc 1 T) := by
    intro v hv
    obtain ⟨hvS, hxT, hyT⟩ := Finset.mem_filter.mp hv
    have hp := hpos v hvS
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hp.1, hxT⟩, Finset.mem_Icc.mpr ⟨hp.2, hyT⟩⟩
  have hsmallcard : small.card ≤ T ^ 2 := by
    have h := Finset.card_le_card hbox
    simpa [Finset.card_product, Nat.card_Icc, pow_two] using h
  have hlarge : T * (S \ small).card ≤ B := by
    calc
      T * (S \ small).card = ∑ _v ∈ S \ small, T := by simp [mul_comm]
      _ ≤ ∑ v ∈ S \ small, (v.1 + v.2) := by
        apply Finset.sum_le_sum
        intro v hv
        obtain ⟨hvS, hvsmall⟩ := Finset.mem_sdiff.mp hv
        have hnot : ¬ (v.1 ≤ T ∧ v.2 ≤ T) := by
          intro h
          exact hvsmall (Finset.mem_filter.mpr ⟨hvS, h⟩)
        omega
      _ ≤ ∑ v ∈ S, (v.1 + v.2) :=
        Finset.sum_le_sum_of_subset Finset.sdiff_subset
      _ ≤ B := hsum
  have hcards := Finset.card_sdiff_add_card_eq_card hsmall
  have hscaled := Nat.mul_le_mul_left T hsmallcard
  nlinarith [show T ^ 3 = T * T ^ 2 by ring]

theorem sum_nat_steps (x : ℕ → ℕ) (n : ℕ)
    (hx : ∀ i < n, x i ≤ x (i + 1)) :
    (∑ i ∈ Finset.range n, (x (i + 1) - x i)) + x 0 = x n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hprev := ih (fun i hi ↦ hx i (by omega))
    have hlast := hx n (by omega)
    omega

/-- A chain with strictly increasing slopes has at most this many edges. -/
theorem increasing_slope_chain_bound (x y : ℕ → ℕ) (n T B : ℕ)
    (hx : ∀ i < n, x i < x (i + 1))
    (hy : ∀ i < n, y i < y (i + 1)) (hxB : x n ≤ B) (hyB : y n ≤ B)
    (hslopes : StrictMono (fun i : Fin n ↦
      ((y (i + 1) - y i : ℕ) : ℝ) / ((x (i + 1) - x i : ℕ) : ℝ))) :
    T * n ≤ T ^ 3 + 2 * B := by
  let v : Fin n → ℕ × ℕ := fun i ↦ (x (i + 1) - x i, y (i + 1) - y i)
  let S := Finset.univ.image v
  have hvinj : Function.Injective v := by
    intro i j hij
    apply hslopes.injective
    exact congrArg (fun w : ℕ × ℕ ↦ (w.2 : ℝ) / (w.1 : ℝ)) hij
  have hcard : S.card = n := by
    simp only [S, Finset.card_image_of_injective _ hvinj, Finset.card_univ, Fintype.card_fin]
  have hpos : ∀ w ∈ S, 0 < w.1 ∧ 0 < w.2 := by
    intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨Nat.sub_pos_of_lt (hx i i.is_lt), Nat.sub_pos_of_lt (hy i i.is_lt)⟩
  have hsum : (∑ w ∈ S, (w.1 + w.2)) ≤ 2 * B := by
    rw [Finset.sum_image hvinj.injOn]
    simp only [v, Finset.sum_add_distrib]
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ x (i + 1) - x i),
      Fin.sum_univ_eq_sum_range (fun i ↦ y (i + 1) - y i)]
    have hsumx := sum_nat_steps x n (fun i hi ↦ (hx i hi).le)
    have hsumy := sum_nat_steps y n (fun i hi ↦ (hy i hi).le)
    omega
  have h := vector_card_bound S T (2 * B) hpos hsum
  rwa [hcard] at h

end Erdos421
