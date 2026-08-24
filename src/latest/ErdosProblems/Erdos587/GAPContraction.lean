import ErdosProblems.Erdos587.GAPCoordinates

/-!
Contract a GAP around a represented zero, rounding each coefficient endpoint
inwards. Linear lifting makes this a cover of `A` whenever a twice-proper
ambient progression covers `h*A` and `0 ∈ A`.
-/

open scoped Pointwise

namespace Erdos587.GeneralizedAP

/-- Inward-rounded contraction around the parameter `c`. Its base is chosen
so that the coefficient `c/h` represents zero. -/
def contractAt (P : GeneralizedAP) (c : P.Param) (h : ℕ) : GeneralizedAP where
  rank := P.rank
  base := -∑ i : Fin P.rank, (((c i : ℕ) / h : ℕ) : ℤ) * P.step i
  step := P.step
  length i := (c i : ℕ) / h + (P.length i - (c i : ℕ)) / h

theorem contractAt_length_le (P : GeneralizedAP) (c : P.Param) (h : ℕ)
    (i : Fin P.rank) : (P.contractAt c h).length i ≤ P.length i / h := by
  change (c i : ℕ) / h + (P.length i - (c i : ℕ)) / h ≤ P.length i / h
  have hc : (c i : ℕ) ≤ P.length i := Nat.le_of_lt_succ (c i).isLt
  have hd : (c i : ℕ) / h + (P.length i - (c i : ℕ)) / h ≤
      ((c i : ℕ) + (P.length i - (c i : ℕ))) / h := Nat.div_add_div_le_add_div
  simpa only [Nat.add_sub_of_le hc] using hd

theorem contractAt_scaled_length_le (P : GeneralizedAP) (c : P.Param) (h : ℕ)
    (i : Fin P.rank) : h * (P.contractAt c h).length i ≤ P.length i := by
  exact (Nat.mul_le_mul_left h (P.contractAt_length_le c h i)).trans
    (Nat.mul_div_le (P.length i) h)

theorem contractAt_short_side (P : GeneralizedAP) (c : P.Param) {h : ℕ}
    (i : Fin P.rank) (hshort : P.length i < h) :
    (P.contractAt c h).length i = 0 := by
  have hle := P.contractAt_length_le c h i
  rw [Nat.div_eq_of_lt hshort] at hle
  omega

theorem contractAt_boxCard_dilate_le (P : GeneralizedAP) (c : P.Param) (h : ℕ) :
    ((P.contractAt c h).dilate h).boxCard ≤ P.boxCard := by
  change (∏ i : Fin P.rank, (h * (P.contractAt c h).length i + 1)) ≤
    ∏ i : Fin P.rank, (P.length i + 1)
  exact Finset.prod_le_prod' (fun i _hi =>
    Nat.add_le_add_right (P.contractAt_scaled_length_le c h i) 1)

theorem eval_contractAt (P : GeneralizedAP) (c : P.Param) (h : ℕ)
    (x : (P.contractAt c h).Param) :
    (P.contractAt c h).eval x =
      P.linearEval (fun i => (x i : ℤ) - (((c i : ℕ) / h : ℕ) : ℤ)) := by
  change -(∑ i : Fin P.rank, (((c i : ℕ) / h : ℕ) : ℤ) * P.step i) +
      (∑ i : Fin P.rank, (x i : ℤ) * P.step i) =
    ∑ i : Fin P.rank, ((x i : ℤ) - (((c i : ℕ) / h : ℕ) : ℤ)) * P.step i
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

/-- The full `h`-fold dilation still fits in the original side lengths, so
properness survives without any assumption about the base. -/
theorem contractAt_tProper (P : GeneralizedAP) (hP : P.Proper)
    (c : P.Param) (h : ℕ) : (P.contractAt c h).TProper h := by
  intro x y hxy
  have hlin : P.linearEval (fun i => (x i : ℤ)) =
      P.linearEval (fun i => (y i : ℤ)) := by
    exact add_left_cancel hxy
  have hb (i : Fin P.rank) : |(x i : ℤ) - (y i : ℤ)| ≤ (P.length i : ℤ) := by
    have hx : (x i : ℕ) ≤ h * (P.contractAt c h).length i :=
      Nat.le_of_lt_succ (x i).isLt
    have hy : (y i : ℕ) ≤ h * (P.contractAt c h).length i :=
      Nat.le_of_lt_succ (y i).isLt
    have hlen := P.contractAt_scaled_length_le c h i
    rw [abs_le]
    constructor <;> omega
  have hv := P.proper_linearEval_injective_of_abs_sub_le hP hlin hb
  funext i
  apply Fin.ext
  have hi := congrFun hv i
  exact_mod_cast hi

/-- Integer endpoint inequalities after division by the progression length. -/
theorem contracted_coordinate_bounds {L c h : ℕ} (hc : c ≤ L) (hh : 0 < h)
    (v : ℤ) (hv : -(c : ℤ) ≤ (h : ℤ) * v ∧
      (h : ℤ) * v ≤ (L : ℤ) - (c : ℤ)) :
    -((c / h : ℕ) : ℤ) ≤ v ∧ v ≤ ((L - c) / h : ℕ) := by
  have hh' : (0 : ℤ) < (h : ℤ) := by exact_mod_cast hh
  have hlo : -v ≤ (c : ℤ) / (h : ℤ) :=
    (Int.le_ediv_iff_mul_le hh').mpr (by nlinarith [hv.1])
  have hhi : v ≤ ((L - c : ℕ) : ℤ) / (h : ℤ) := by
    apply (Int.le_ediv_iff_mul_le hh').mpr
    rw [Nat.cast_sub hc]
    nlinarith [hv.2]
  rw [← Int.natCast_ediv] at hlo hhi
  constructor <;> omega

theorem linearEval_coordinates_sub_zero (P : GeneralizedAP)
    (hzero : (0 : ℤ) ∈ P.carrier) {a : ℤ} (ha : a ∈ P.carrier) :
    P.linearEval (fun i => (P.coordinates a i : ℤ) - (P.coordinates 0 i : ℤ)) = a := by
  have h0 := P.eval_coordinates hzero
  have h1 := P.eval_coordinates ha
  rw [eval] at h0 h1
  simp only [linearEval, sub_mul, Finset.sum_sub_distrib]
  omega

/-- Every long progression through zero in a twice-proper GAP is contained
at its first step in the inward-rounded contracted GAP. -/
theorem mem_contractAt_coordinates_zero (P : GeneralizedAP) (hP : P.TProper 2)
    (a : ℤ) {h : ℕ} (hh : 0 < h)
    (hmem : ∀ t ≤ h, t • a ∈ P.carrier) :
    a ∈ (P.contractAt (P.coordinates 0) h).carrier := by
  let c := P.coordinates 0
  let v : Fin P.rank → ℤ := fun i => (P.coordinates a i : ℤ) - (c i : ℤ)
  have hb (i : Fin P.rank) : -(((c i : ℕ) / h : ℕ) : ℤ) ≤ v i ∧
      v i ≤ ((P.length i - (c i : ℕ)) / h : ℕ) := by
    exact contracted_coordinate_bounds (Nat.le_of_lt_succ (c i).isLt) hh (v i)
      (P.coordinates_nsmul_bounds hP a hh hmem i)
  let x : (P.contractAt c h).Param := fun i =>
    ⟨(v i + (((c i : ℕ) / h : ℕ) : ℤ)).toNat, by
      have hlo := (hb i).1
      have hhi := (hb i).2
      apply Nat.lt_succ_of_le
      apply Int.toNat_le.mpr
      change v i + (((c i : ℕ) / h : ℕ) : ℤ) ≤
        (((c i : ℕ) / h + (P.length i - (c i : ℕ)) / h : ℕ) : ℤ)
      push_cast
      omega⟩
  apply (P.contractAt c h).mem_carrier_iff.mpr
  refine ⟨x, ?_⟩
  rw [P.eval_contractAt c h x]
  have hvec : (fun i => (x i : ℤ) - (((c i : ℕ) / h : ℕ) : ℤ)) = v := by
    funext i
    change ((v i + (((c i : ℕ) / h : ℕ) : ℤ)).toNat : ℤ) -
      (((c i : ℕ) / h : ℕ) : ℤ) = v i
    rw [Int.toNat_of_nonneg (by have hli := (hb i).1; omega)]
    ring
  have heval : P.linearEval v = a := P.linearEval_coordinates_sub_zero
    (by simpa using hmem 0 (Nat.zero_le _)) (by simpa using hmem 1 hh)
  exact (congrArg P.linearEval hvec).trans heval

/-- A cover of `h*A` contracts to a proper cover of `A`, with every side
length divided by `h`. The structural work of finding the ambient cover is
separate from this implication. -/
theorem exists_contracted_GAP_cover (P : GeneralizedAP) (hP : P.TProper 2)
    (A : Finset ℤ) (hzero : 0 ∈ A) {h : ℕ} (hh : 0 < h)
    (hcover : h • A ⊆ P.carrier) :
    ∃ Q : GeneralizedAP, Q.rank = P.rank ∧ Q.TProper h ∧
      (0 : ℤ) ∈ Q.carrier ∧ A ⊆ Q.carrier ∧
      (Q.dilate h).boxCard ≤ P.boxCard ∧
      ∀ i : Fin Q.rank, ∀ j : Fin P.rank, i.val = j.val →
        Q.length i ≤ P.length j / h := by
  let Q := P.contractAt (P.coordinates 0) h
  have hAQ : A ⊆ Q.carrier := by
    intro a ha
    apply P.mem_contractAt_coordinates_zero hP a hh
    intro t ht
    exact hcover (Finset.nsmul_subset_nsmul_right hzero ht (Finset.nsmul_mem_nsmul ha))
  refine ⟨Q, rfl, P.contractAt_tProper (P.proper_of_tProper (by norm_num) hP) _ h,
    hAQ hzero, hAQ, P.contractAt_boxCard_dilate_le _ h, ?_⟩
  intro i j hij
  have heq : i = j := Fin.ext hij
  subst j
  exact P.contractAt_length_le _ h i

end Erdos587.GeneralizedAP

namespace Erdos587.CFP

/-- Small doubling of the high-fold sumset gives a bounded-rank model of
`A` whose `h`-fold dilation is proper and comparable in size to `h*A`.
No small-doubling hypothesis is being inferred from an ambient interval. -/
theorem exists_highFold_GAP_model_of_small_doubling
    (A : Finset ℤ) (hzero : 0 ∈ A) (h K : ℕ) (hh : 0 < h) (hK : 1 ≤ K)
    (hsmall : (h • A + h • A).card ≤ K * (h • A).card) :
    ∃ Q : GeneralizedAP, Q.rank ≤ freimanRank K ∧ Q.TProper h ∧
      (0 : ℤ) ∈ Q.carrier ∧ A ⊆ Q.carrier ∧
      (Q.dilate h).boxCard ≤ freimanTSizeFactor K 2 * (h • A).card := by
  have hne : (h • A).Nonempty := ⟨0, Finset.zero_mem_nsmul hzero⟩
  obtain ⟨P, hrank, hproper, hcover, hbox⟩ :=
    exists_tProper_GAP_cover_of_small_doubling (h • A) hne K 2 hK (by norm_num) hsmall
  obtain ⟨Q, hQrank, hQproper, hQzero, hAQ, hQbox, _hside⟩ :=
    P.exists_contracted_GAP_cover hproper A hzero hh hcover
  exact ⟨Q, hQrank.le.trans hrank, hQproper, hQzero, hAQ, hQbox.trans hbox⟩

end Erdos587.CFP
