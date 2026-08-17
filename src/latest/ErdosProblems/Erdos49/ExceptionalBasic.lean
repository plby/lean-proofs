import ErdosProblems.Erdos49.Anatomy

/-!
# Elementary exceptional-set estimates

This file treats the first four exceptional pieces: small integers, smooth
integers, repeated large factors, and an overlarge smooth part.  The last two
prime-cluster pieces are handled separately.
-/

open scoped BigOperators

namespace Erdos49

noncomputable section

attribute [local instance] Classical.propDecidable

def multiplesUpTo (N d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n ↦ d ∣ n

@[simp] lemma mem_multiplesUpTo {N d n : ℕ} :
    n ∈ multiplesUpTo N d ↔ 1 ≤ n ∧ n ≤ N ∧ d ∣ n := by
  simp [multiplesUpTo, and_assoc]

lemma multiplesUpTo_card_le (N d : ℕ) :
    (multiplesUpTo N d).card ≤ N / d := by
  by_cases hd : d = 0
  · subst d
    have hempty : multiplesUpTo N 0 = ∅ := by
      ext n
      simp [mem_multiplesUpTo]
      omega
    simp [hempty]
  let f : ℕ → ℕ := fun n ↦ n / d
  have hinj : Set.InjOn f (multiplesUpTo N d : Set ℕ) := by
    intro m hm n hn hmn
    have hm' := (mem_multiplesUpTo.mp hm).2.2
    have hn' := (mem_multiplesUpTo.mp hn).2.2
    calc
      m = d * (m / d) := (Nat.mul_div_cancel' hm').symm
      _ = d * (n / d) := by
        change m / d = n / d at hmn
        rw [hmn]
      _ = n := Nat.mul_div_cancel' hn'
  have hcard : (multiplesUpTo N d).card =
      ((multiplesUpTo N d).image f).card := by
    symm
    exact Finset.card_image_iff.mpr fun m hm n hn hmn ↦ hinj hm hn hmn
  rw [hcard]
  apply (Finset.card_le_card ?_).trans_eq (card_Icc_one (N / d))
  intro k hk
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
  have hndata := mem_multiplesUpTo.mp hn
  apply Finset.mem_Icc.mpr
  constructor
  · apply (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hd)).2
    simpa using Nat.le_of_dvd hndata.1 hndata.2.2
  · exact Nat.div_le_div_right hndata.2.1

lemma smallExceptional_card_le {N L : ℕ} (hL : 0 < L) :
    (smallExceptional N L).card ≤ N / L := by
  apply (Finset.card_le_card (t := Finset.Icc 1 (N / L)) ?_).trans_eq
    (card_Icc_one (N / L))
  intro n hn
  have h := Finset.mem_filter.mp hn
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp h.1).1,
    (Nat.le_div_iff_mul_le hL).2 (by simpa [mul_comm] using h.2)⟩

lemma smoothExceptional_subset {N R : ℕ} :
    smoothExceptional N R ⊆ smoothUpTo N R := by
  intro n hn
  have h := Finset.mem_filter.mp hn
  exact mem_smoothUpTo.mpr ⟨(Finset.mem_Icc.mp h.1).2, h.2⟩

lemma smoothExceptional_card_real_le {N R : ℕ} (hN : 0 < N)
    (hR : Real.exp 1 < R) :
    ((smoothExceptional N R).card : ℝ) ≤
      (N : ℝ) ^ rankinAlpha R * rankinEulerProduct R := by
  have hcard : ((smoothExceptional N R).card : ℝ) ≤
      (smoothUpTo N R).card := by
    exact_mod_cast Finset.card_le_card (smoothExceptional_subset (N := N) (R := R))
  exact hcard.trans (smoothUpTo_card_real_le hN hR)

def squareCover (N L : ℕ) : Finset ℕ :=
  (Finset.Ioc L N).biUnion fun q ↦ multiplesUpTo N (q ^ 2)

lemma squareExceptional_subset_cover {N L : ℕ} :
    squareExceptional N L ⊆ squareCover N L := by
  intro n hn
  have hndata := Finset.mem_filter.mp hn
  obtain ⟨q, hqdup⟩ := List.exists_duplicate_iff_not_nodup.mpr hndata.2
  have hqLarge : q ∈ largeFactors L n := hqdup.mem
  have hqL : L < q := lt_of_mem_largeFactors hqLarge
  have hqN : q ≤ N := by
    have hqPrimeList : q ∈ n.primeFactorsList := List.mem_of_mem_filter hqLarge
    exact (Nat.le_of_mem_primeFactorsList hqPrimeList).trans
      (Finset.mem_Icc.mp hndata.1).2
  have hqSqLarge : q ^ 2 ∣ (largeFactors L n).prod := by
    have hsub := List.duplicate_iff_sublist.mp hqdup
    simpa [pow_two] using hsub.prod_dvd_prod
  have hqSqN : q ^ 2 ∣ n := by
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hndata.1).1
      omega
    rw [← factors_product hn0]
    exact dvd_mul_of_dvd_right hqSqLarge _
  apply Finset.mem_biUnion.mpr
  exact ⟨q, Finset.mem_Ioc.mpr ⟨hqL, hqN⟩,
    mem_multiplesUpTo.mpr
      ⟨(Finset.mem_Icc.mp hndata.1).1, (Finset.mem_Icc.mp hndata.1).2, hqSqN⟩⟩

lemma squareCover_card_le (N L : ℕ) :
    (squareCover N L).card ≤ ∑ q ∈ Finset.Ioc L N, N / q ^ 2 := by
  unfold squareCover
  exact Finset.card_biUnion_le.trans
    (Finset.sum_le_sum fun q hq ↦ multiplesUpTo_card_le N (q ^ 2))

lemma reciprocal_sq_le_telescope {q : ℕ} (hq : 1 < q) :
    (1 : ℝ) / q ^ 2 ≤ 1 / (q - 1 : ℕ) - 1 / q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hqmNat : 0 < q - 1 := by omega
  have hqm0 : (0 : ℝ) < (q - 1 : ℕ) := by exact_mod_cast hqmNat
  have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num
  have hright : (1 : ℝ) / (q - 1 : ℕ) - 1 / q =
      1 / ((q : ℝ) * (q - 1 : ℕ)) := by
    field_simp
    rw [hcast]
    ring
  rw [hright]
  push_cast
  apply one_div_le_one_div_of_le (mul_pos hq0 hqm0)
  rw [hcast]
  nlinarith

lemma sum_Ioc_reciprocal_telescope {L N : ℕ} (hL : 0 < L) :
    (∑ q ∈ Finset.Ioc L N,
      ((1 : ℝ) / (q - 1 : ℕ) - 1 / q)) ≤ 1 / L := by
  by_cases hLN : L ≤ N
  · have heq : (∑ q ∈ Finset.Ioc L N,
        ((1 : ℝ) / (q - 1 : ℕ) - 1 / q)) = 1 / L - 1 / N := by
      induction N, hLN using Nat.le_induction with
      | base => simp
      | succ N hLN ih =>
          rw [Finset.sum_Ioc_succ_top hLN, ih]
          have hEq : ((N + 1 : ℕ) - 1 : ℕ) = N := by omega
          rw [hEq]
          ring
    rw [heq]
    exact sub_le_self _ (by positivity)
  · have hNL : N ≤ L := Nat.le_of_lt (Nat.lt_of_not_ge hLN)
    simp [Finset.Ioc_eq_empty, hNL]

lemma sum_Ioc_reciprocal_sq_le {L N : ℕ} (hL : 0 < L) :
    (∑ q ∈ Finset.Ioc L N, (1 : ℝ) / q ^ 2) ≤ 1 / L := by
  apply (Finset.sum_le_sum ?_).trans (sum_Ioc_reciprocal_telescope hL)
  intro q hq
  exact reciprocal_sq_le_telescope (by
    have := (Finset.mem_Ioc.mp hq).1
    omega)

lemma squareExceptional_card_real_le {N L : ℕ} (hL : 0 < L) :
    ((squareExceptional N L).card : ℝ) ≤ (N : ℝ) / L := by
  calc
    ((squareExceptional N L).card : ℝ) ≤ (squareCover N L).card := by
      exact_mod_cast Finset.card_le_card squareExceptional_subset_cover
    _ ≤ ∑ q ∈ Finset.Ioc L N, ((N / q ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast squareCover_card_le N L
    _ ≤ ∑ q ∈ Finset.Ioc L N, (N : ℝ) * ((1 : ℝ) / q ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      calc
        ((N / q ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / (q ^ 2 : ℕ) := Nat.cast_div_le
        _ = (N : ℝ) * ((1 : ℝ) / q ^ 2) := by push_cast; ring
    _ = (N : ℝ) * ∑ q ∈ Finset.Ioc L N, (1 : ℝ) / q ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ (N : ℝ) * (1 / L) :=
      mul_le_mul_of_nonneg_left (sum_Ioc_reciprocal_sq_le hL) (by positivity)
    _ = (N : ℝ) / L := by ring

def smoothTailCover (N L D : ℕ) : Finset ℕ :=
  (smoothTail N D L).biUnion fun d ↦ multiplesUpTo N d

lemma smoothTailExceptional_subset_cover {N L D : ℕ} :
    smoothTailExceptional N L D ⊆ smoothTailCover N L D := by
  intro n hn
  have hndata := Finset.mem_filter.mp hn
  let d := smallPart L n
  have hn0 : n ≠ 0 := by
    have := (Finset.mem_Icc.mp hndata.1).1
    omega
  have hdD : D < d := hndata.2
  have hdN : d ≤ N := by
    apply (Nat.le_of_dvd (by omega : 0 < n) ?_).trans (Finset.mem_Icc.mp hndata.1).2
    rw [← factors_product hn0]
    exact dvd_mul_right d _
  have hdmem : d ∈ smoothTail N D L :=
    mem_smoothTail.mpr ⟨hdN, smallPart_smooth L n, hdD⟩
  have hdn : d ∣ n := by
    rw [← factors_product hn0]
    exact dvd_mul_right d _
  exact Finset.mem_biUnion.mpr ⟨d, hdmem,
    mem_multiplesUpTo.mpr
      ⟨(Finset.mem_Icc.mp hndata.1).1, (Finset.mem_Icc.mp hndata.1).2, hdn⟩⟩

lemma smoothTailExceptional_card_real_le {N L D : ℕ} (hD : 0 < D)
    (hL : Real.exp 1 < L) :
    ((smoothTailExceptional N L D).card : ℝ) ≤
      (N : ℝ) * ((D : ℝ) ^ (rankinAlpha L - 1) * rankinEulerProduct L) := by
  calc
    ((smoothTailExceptional N L D).card : ℝ) ≤
        (smoothTailCover N L D).card := by
      exact_mod_cast Finset.card_le_card smoothTailExceptional_subset_cover
    _ ≤ ∑ d ∈ smoothTail N D L, ((N / d : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le.trans
        (Finset.sum_le_sum fun d hd ↦ multiplesUpTo_card_le N d)
    _ ≤ ∑ d ∈ smoothTail N D L, (N : ℝ) * ((1 : ℝ) / d) := by
      apply Finset.sum_le_sum
      intro d hd
      calc
        ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
        _ = (N : ℝ) * ((1 : ℝ) / d) := by ring
    _ = (N : ℝ) * (∑ d ∈ smoothTail N D L, (1 : ℝ) / d) := by
      rw [Finset.mul_sum]
    _ ≤ (N : ℝ) *
        ((D : ℝ) ^ (rankinAlpha L - 1) * rankinEulerProduct L) :=
      mul_le_mul_of_nonneg_left (smoothTail_reciprocal_sum_le hD hL) (by positivity)

#print axioms squareExceptional_card_real_le
#print axioms smoothTailExceptional_card_real_le

end

end Erdos49
