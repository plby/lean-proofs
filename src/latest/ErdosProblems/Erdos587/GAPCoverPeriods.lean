import ErdosProblems.Erdos587.GAPStepGcd

/-!
A bounded translate cover controls the relative step gcd without matching
coordinate ranks. Pigeonholing one long coordinate line gives a short
period; multiplying these periods gives a bounded gcd multiplier. This
applies directly to the cover retained by budgeted rank reduction.
-/

open scoped Pointwise BigOperators

namespace Erdos587.CFP

theorem divisible_sub_iteratedDifference {A : Finset ℤ} {g : ℤ}
    (h : ∀ x ∈ A, ∀ y ∈ A, g ∣ x - y) (n : ℕ) :
    ∀ x ∈ iteratedDifference n A, ∀ y ∈ iteratedDifference n A, g ∣ x - y := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro x hx y hy
      rw [iteratedDifference_succ] at hx hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
      obtain ⟨c, hc, d, hd, rfl⟩ := Finset.mem_sub.mp hy
      have hh := dvd_sub (ih a ha c hc) (ih b hb d hd)
      have heq : (a - c) - (b - d) = (a - b) - (c - d) := by ring
      exact heq ▸ hh

end Erdos587.CFP

namespace Erdos587.GeneralizedAP

theorem stepGcd_dvd_sub_of_mem (P : GeneralizedAP) {x y : ℤ}
    (hx : x ∈ P.carrier) (hy : y ∈ P.carrier) : P.stepGcd ∣ x - y := by
  have hh := dvd_sub (P.stepGcd_dvd_sub_base hx) (P.stepGcd_dvd_sub_base hy)
  have heq : (x - P.base) - (y - P.base) = x - y := by ring
  exact heq ▸ hh

theorem stepGcd_dvd_iteratedDifference_sub (P : GeneralizedAP) (n : ℕ) {x y : ℤ}
    (hx : x ∈ iteratedDifference n P.carrier) (hy : y ∈ iteratedDifference n P.carrier) :
    P.stepGcd ∣ x - y :=
  CFP.divisible_sub_iteratedDifference (fun _ hx _ hy => P.stepGcd_dvd_sub_of_mem hx hy) n
    x hx y hy

theorem base_add_mul_step_mem (P : GeneralizedAP) (i : Fin P.rank) (n : ℕ)
    (hn : n ≤ P.length i) : P.base + (n : ℤ) * P.step i ∈ P.carrier := by
  classical
  let v : P.Param := fun j => if hji : j = i then
    ⟨n, by simpa only [hji] using Nat.lt_succ_of_le hn⟩ else 0
  apply P.mem_carrier_iff.mpr
  refine ⟨v, ?_⟩
  have hv (j : Fin P.rank) : (v j : ℤ) = if j = i then (n : ℤ) else 0 := by
    by_cases hji : j = i <;> simp [v, hji]
  simp [eval, hv]

theorem exists_coordinate_period_of_difference_cover
    (P Q : GeneralizedAP) (F : Finset ℤ) (m C : ℕ)
    (hcover : P.carrier ⊆ F + iteratedDifference m Q.carrier) (hF : F.card ≤ C)
    (i : Fin P.rank) (hwidth : C ≤ P.length i) :
    ∃ k : ℕ, 0 < k ∧ k ≤ C ∧ Q.stepGcd ∣ (k : ℤ) * P.step i := by
  classical
  have hrep : ∀ j : Fin (C + 1), ∃ f ∈ F, ∃ y ∈ iteratedDifference m Q.carrier,
      f + y = P.base + (j.val : ℤ) * P.step i := by
    intro j
    exact Finset.mem_add.mp (hcover
      (P.base_add_mul_step_mem i j.val ((Nat.le_of_lt_succ j.isLt).trans hwidth)))
  choose f hf y hy heq using hrep
  let f' : Fin (C + 1) → F := fun j => ⟨f j, hf j⟩
  have hnot : ¬ Function.Injective f' := by
    intro hinj
    have hh := Fintype.card_le_of_injective f' hinj
    have hcard : C + 1 ≤ F.card := by simpa using hh
    omega
  unfold Function.Injective at hnot
  push_neg at hnot
  obtain ⟨u, v, huv, hne⟩ := hnot
  have hfeq : f u = f v := congrArg Subtype.val huv
  let z : ℤ := (u.val : ℤ) - (v.val : ℤ)
  have hz : z ≠ 0 := by
    intro hz
    have hh : (u.val : ℤ) = (v.val : ℤ) := sub_eq_zero.mp hz
    have hv : u.val = v.val := by exact_mod_cast hh
    exact hne (Fin.ext hv)
  have heval : z * P.step i = y u - y v := by
    dsimp [z]
    rw [sub_mul]
    have hu := heq u
    have hv := heq v
    rw [hfeq] at hu
    linarith
  have hdiv : Q.stepGcd ∣ z * P.step i :=
    heval.symm ▸ Q.stepGcd_dvd_iteratedDifference_sub m (hy u) (hy v)
  refine ⟨z.natAbs, Int.natAbs_pos.mpr hz, ?_, ?_⟩
  · have hu : u.val ≤ C := Nat.le_of_lt_succ u.isLt
    have hv : v.val ≤ C := Nat.le_of_lt_succ v.isLt
    have habs : |z| ≤ (C : ℤ) := by
      rw [abs_le]
      dsimp [z]
      constructor <;> omega
    have hh : (z.natAbs : ℤ) ≤ (C : ℤ) := by
      simpa only [Int.natCast_natAbs] using habs
    exact_mod_cast hh
  · rw [Int.natCast_natAbs]
    rcases le_total 0 z with hpos | hneg
    · rw [abs_of_nonneg hpos]
      exact hdiv
    · rw [abs_of_nonpos hneg, neg_mul]
      exact dvd_neg.mpr hdiv

theorem dvd_mul_stepGcd_of_coordinate_periods (P : GeneralizedAP) (g : ℤ)
    (k : Fin P.rank → ℕ) (hperiod : ∀ i, g ∣ (k i : ℤ) * P.step i) :
    g ∣ ((∏ i, k i : ℕ) : ℤ) * P.stepGcd := by
  classical
  let K := ∏ i, k i
  have hdiv (i : Fin P.rank) : g ∣ (K : ℤ) * P.step i := by
    have hprod : k i ∣ K := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hprod' : (k i : ℤ) ∣ (K : ℤ) := by exact_mod_cast hprod
    exact (hperiod i).trans (mul_dvd_mul hprod' (dvd_refl (P.step i)))
  obtain ⟨b, hb⟩ := Finset.gcd_eq_sum_mul (Finset.univ : Finset (Fin P.rank)) P.step
  change g ∣ (K : ℤ) * Finset.univ.gcd P.step
  rw [hb, Finset.mul_sum]
  apply Finset.dvd_sum
  intro i _
  rw [← mul_assoc]
  exact dvd_mul_of_dvd_left (hdiv i) (b i)

theorem exists_stepGcd_bound_of_difference_cover
    (P Q : GeneralizedAP) (F : Finset ℤ) (m C : ℕ)
    (hcover : P.carrier ⊆ F + iteratedDifference m Q.carrier) (hF : F.card ≤ C)
    (hwidth : ∀ i, C ≤ P.length i) :
    ∃ K : ℕ, 0 < K ∧ K ≤ C ^ P.rank ∧ Q.stepGcd ∣ (K : ℤ) * P.stepGcd := by
  classical
  choose k hkpos hkbound hkdiv using fun i =>
    P.exists_coordinate_period_of_difference_cover Q F m C hcover hF i (hwidth i)
  refine ⟨∏ i, k i, Finset.prod_pos (fun i _ => hkpos i), ?_,
    P.dvd_mul_stepGcd_of_coordinate_periods Q.stepGcd k hkdiv⟩
  calc
    (∏ i, k i) ≤ ∏ _i : Fin P.rank, C := Finset.prod_le_prod' (fun i _ => hkbound i)
    _ = C ^ P.rank := by simp

/-- Budgeted rank reduction also has a rank-only step-gcd cost once the
input sides exceed the rank-only cover bound. -/
theorem exists_budgeted_rank_reduction_with_stepGcd
    (P : GeneralizedAP) (hP : P.Proper)
    (hwidth : ∀ i, nvBudgetRankReductionCover P.rank ≤ P.length i) (s : ℕ) :
    ∃ R : GeneralizedAP, ∃ e K : ℕ,
      R.Proper ∧ (∀ i, 0 < R.length i) ∧ R.rank ≤ P.rank ∧
      0 < K ∧ K ≤ (nvBudgetRankReductionCover P.rank) ^ P.rank ∧
      R.stepGcd ∣ (K : ℤ) * P.stepGcd ∧
      R.carrier ⊆ (P.dilate e).carrier ∧
      e ≤ 2 ^ s * nvBudgetRankReductionScale P.rank ∧
      P.carrier.card * (2 ^ s) ^ R.rank ≤
        nvBudgetRankReductionFactor P.rank * R.carrier.card := by
  have hpos : ∀ i, 0 < P.length i := fun i =>
    (nvBudgetRankReductionCover_pos P.rank).trans_le (hwidth i)
  obtain ⟨R, e, F, m, hR, hRpos, hrank, hF, _hm, hcover, hsub, he, hcard⟩ :=
    P.exists_budgeted_rank_reduction hP hpos s
  obtain ⟨K, hK, hKbound, hgcd⟩ := P.exists_stepGcd_bound_of_difference_cover R F m
    (nvBudgetRankReductionCover P.rank) hcover hF hwidth
  exact ⟨R, e, K, hR, hRpos, hrank, hK, hKbound, hgcd, hsub, he, hcard⟩

end Erdos587.GeneralizedAP
