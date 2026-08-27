import ErdosProblems.Erdos587.NVDevelopment

/-! # A lattice box product bound from coordinate first moments -/

open scoped BigOperators

namespace Erdos587.CFP

lemma delta_card_le_integer_box {κ : Type*} [Fintype κ]
    (A : Finset (κ → ℤ)) (R : κ → ℕ)
    (hA : ∀ v ∈ A, ∀ i, (v i).natAbs ≤ R i) :
    A.card ≤ ∏ i, (2 * R i + 1) := by
  classical
  have hsub : A ⊆ Fintype.piFinset (fun i => Finset.Icc (-(R i : ℤ)) (R i)) := by
    intro v hv
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_Icc.mpr
    have hh : |v i| ≤ (R i : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hA v hv i
    exact abs_le.mp hh
  have hcard (i : κ) : (Finset.Icc (-(R i : ℤ)) (R i)).card = 2 * R i + 1 := by
    rw [Int.card_Icc]
    omega
  simpa only [Fintype.card_piFinset, hcard] using Finset.card_le_card hsub

theorem delta_box_product_lower_of_coordinate_mass {d : ℕ} (hd : 0 < d)
    (A : Finset (Fin d → ℤ)) (hA : 0 < A.card) (B : Fin d → ℕ)
    (hB : ∀ i, A.card ≤ B i)
    (hmass : ∀ i, (∑ v ∈ A, (v i).natAbs) ≤ B i) :
    A.card ^ (d + 1) ≤ 2 * (9 * d) ^ d * ∏ i, B i := by
  classical
  let m := A.card
  let R (i : Fin d) := 4 * d * B i / m
  let bad (i : Fin d) := A.filter (fun v => R i < (v i).natAbs)
  let Z := Finset.univ.biUnion bad
  let D := A \ Z
  have hbad (i : Fin d) : 4 * d * (bad i).card ≤ m := by
    have hbudget : (R i + 1) * (bad i).card ≤ B i := by
      calc
        _ = ∑ v ∈ bad i, (R i + 1) := by simp only [Finset.sum_const, smul_eq_mul]; ring
        _ ≤ ∑ v ∈ bad i, (v i).natAbs := by
          apply Finset.sum_le_sum
          intro v hv
          exact (Finset.mem_filter.mp hv).2
        _ ≤ ∑ v ∈ A, (v i).natAbs := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ ≤ B i := hmass i
    have hthreshold : 4 * d * B i < (R i + 1) * m := by
      exact (Nat.div_lt_iff_lt_mul hA).mp (Nat.lt_succ_self (4 * d * B i / m))
    have hmul : (R i + 1) * (4 * d * (bad i).card) < (R i + 1) * m := by
      calc
        _ = (4 * d) * ((R i + 1) * (bad i).card) := by ring
        _ ≤ (4 * d) * B i := Nat.mul_le_mul_left _ hbudget
        _ < _ := hthreshold
    exact (Nat.lt_of_mul_lt_mul_left hmul).le
  have hsum : 4 * (∑ i, (bad i).card) ≤ m := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbad i)
    simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at hh
    have hh' : d * (4 * ∑ i, (bad i).card) ≤ d * m := by
      calc
        _ = (4 * d) * ∑ i, (bad i).card := by ring
        _ ≤ d * m := hh
    exact Nat.le_of_mul_le_mul_left hh' hd
  have hZsub : Z ⊆ A := Finset.biUnion_subset.mpr (fun i _ => Finset.filter_subset _ _)
  have hZcard : Z.card ≤ ∑ i, (bad i).card := Finset.card_biUnion_le
  have hDcard : D.card + Z.card = m := Finset.card_sdiff_add_card_eq_card hZsub
  have hgood : m ≤ 2 * D.card := by omega
  have hDbox : ∀ v ∈ D, ∀ i, (v i).natAbs ≤ R i := by
    intro v hv i
    obtain ⟨hvA, hvZ⟩ := Finset.mem_sdiff.mp hv
    by_contra h
    apply hvZ
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨hvA, by omega⟩⟩
  have hbox := delta_card_le_integer_box D R hDbox
  have hside (i : Fin d) : m * (2 * R i + 1) ≤ (9 * d) * B i := by
    have hfloor : R i * m ≤ 4 * d * B i := Nat.div_mul_le_self _ _
    calc
      _ = 2 * (R i * m) + m := by ring
      _ ≤ 2 * (4 * d * B i) + B i := Nat.add_le_add (Nat.mul_le_mul_left 2 hfloor) (hB i)
      _ = (8 * d + 1) * B i := by ring
      _ ≤ (9 * d) * B i := Nat.mul_le_mul_right _ (by omega)
  calc
    _ = m ^ d * m := by rw [pow_succ]
    _ ≤ m ^ d * (2 * ∏ i, (2 * R i + 1)) :=
      Nat.mul_le_mul_left _ (hgood.trans (Nat.mul_le_mul_left 2 hbox))
    _ = 2 * ∏ i, (m * (2 * R i + 1)) := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring
    _ ≤ 2 * ∏ i, ((9 * d) * B i) :=
      Nat.mul_le_mul_left 2 (Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hside i))
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring

end Erdos587.CFP
