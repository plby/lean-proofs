import ErdosProblems.Erdos489.FullGapConvergence
import ErdosProblems.Erdos489.Thinness
import ErdosProblems.Erdos489.ProblemDefinitions

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Classical Filter
open scoped Topology BigOperators

namespace Erdos489

/-- Remove the irrelevant forbidden integers `0` and `1`. -/
def restrictedForbidden (A : Set ℕ) (n : ℕ) : Prop := n ∈ A ∧ 2 ≤ n

noncomputable instance restrictedForbiddenDecidable (A : Set ℕ) :
    DecidablePred (restrictedForbidden A) := Classical.decPred _

 theorem restricted_count_le_original_Icc (A : Set ℕ) (x : ℕ) :
    Nat.count (restrictedForbidden A) x ≤
      ((Finset.Icc 1 x).filter (· ∈ A)).card := by
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_le_card
  intro n hn
  have hnr := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
  have hnp := (Finset.mem_filter.mp hn).2
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_Icc.mpr ⟨le_trans (by omega : 1 ≤ 2) hnp.2, hnr.le⟩, hnp.1⟩

 theorem restricted_count_isLittleO
    (A : Set ℕ)
    (hA : (fun x : ℕ => (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ))
      =o[atTop] (fun x : ℕ => Real.sqrt (x : ℝ))) :
    (fun x : ℕ => (Nat.count (restrictedForbidden A) x : ℝ))
      =o[atTop] (fun x : ℕ => Real.sqrt (x : ℝ)) := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hb := hA.bound hc
  filter_upwards [hb] with x hx
  have hleR : (Nat.count (restrictedForbidden A) x : ℝ) ≤
      (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ) := by
    exact_mod_cast restricted_count_le_original_Icc A x
  have hx' : (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ) ≤
      c * Real.sqrt (x : ℝ) := by
    simpa only [Real.norm_natCast, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤
        (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ) by positivity),
      abs_of_nonneg (Real.sqrt_nonneg _)] using hx
  simpa only [Real.norm_natCast, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (Nat.count (restrictedForbidden A) x : ℝ) by positivity),
    abs_of_nonneg (Real.sqrt_nonneg _)] using hleR.trans hx'

 theorem eventually_sq_le_nth_of_count_isLittleO_sqrt
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (hcount : (fun x : ℕ => (Nat.count p x : ℝ)) =o[atTop]
      (fun x : ℕ => Real.sqrt (x : ℝ))) :
    ∀ᶠ n : ℕ in atTop, (n + 1) ^ 2 ≤ Nat.nth p n := by
  have ht : Tendsto (Nat.nth p) atTop atTop :=
    (Nat.nth_injective hp).nat_tendsto_atTop
  have hb := hcount.bound (by norm_num : (0 : ℝ) < 1 / 2)
  have hbc : ∀ᶠ n in atTop,
      ‖(Nat.count p (Nat.nth p n) : ℝ)‖ ≤
        (1 / 2 : ℝ) * ‖Real.sqrt (Nat.nth p n : ℝ)‖ := ht.eventually hb
  filter_upwards [hbc, eventually_ge_atTop 1] with n hn hnpos
  rw [Nat.count_nth_of_infinite hp n] at hn
  have hnreal : (n : ℝ) ≤ (1 / 2 : ℝ) * Real.sqrt (Nat.nth p n : ℝ) := by
    simpa only [Real.norm_natCast, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity),
      abs_of_nonneg (Real.sqrt_nonneg _)] using hn
  have hsquare : ((2 : ℝ) * n) ^ 2 ≤ (Nat.nth p n : ℝ) := by
    have hsqrt : (2 : ℝ) * n ≤ Real.sqrt (Nat.nth p n : ℝ) := by linarith
    calc
      ((2 : ℝ) * n) ^ 2 ≤ (Real.sqrt (Nat.nth p n : ℝ)) ^ 2 :=
        (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).2 hsqrt
      _ = (Nat.nth p n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hcast : ((((n + 1) ^ 2 : ℕ) : ℝ)) ≤ (Nat.nth p n : ℝ) := by
    have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    norm_num at hsquare ⊢
    nlinarith
  exact_mod_cast hcast

 theorem restrictedForbidden_infinite (A : Set ℕ) (hA : A.Infinite) :
    Set.Infinite {n | restrictedForbidden A n} := by
  by_contra hnot
  rw [Set.not_infinite] at hnot
  have hsub : A ⊆ {n | restrictedForbidden A n} ∪ Set.Iio 2 := by
    intro n hn
    by_cases hn2 : 2 ≤ n
    · exact Set.mem_union_left _ ⟨hn, hn2⟩
    · apply Set.mem_union_right
      show n < 2
      omega
  exact hA ((hnot.union (Set.finite_Iio 2)).subset hsub)

 theorem one_not_mem_of_sievedSet_infinite
    (A : Set ℕ) (hB : (sievedSet A).Infinite) : 1 ∉ A := by
  intro h1
  rcases hB.nonempty with ⟨n, hn⟩
  exact hn.2 1 h1 (one_dvd n)

 theorem divisorSifted_restricted_iff
    (A : Set ℕ) (hB : (sievedSet A).Infinite) (n : ℕ) :
    divisorSifted (restrictedForbidden A) n ↔ n ∈ sievedSet A := by
  have h1 := one_not_mem_of_sievedSet_infinite A hB
  constructor
  · intro hn
    refine ⟨hn.1, ?_⟩
    intro a haA hadvd
    by_cases ha0 : a = 0
    · subst a
      have hn0 : n = 0 := by simpa using hadvd
      exact (Nat.ne_of_gt hn.1) hn0
    by_cases ha1 : a = 1
    · exact h1 (ha1 ▸ haA)
    · apply hn.2 a ⟨haA, by omega⟩ hadvd
  · intro hn
    refine ⟨hn.1, ?_⟩
    intro a ha hadvd
    exact hn.2 a ha.1 hadvd

 theorem fullGapAverage_restricted_eq
    (A : Set ℕ) (hB : (sievedSet A).Infinite) (x : ℕ) :
    fullGapAverage (restrictedForbidden A) x = gapSumSq A x / (x : ℝ) := by
  classical
  have hpred : divisorSifted (restrictedForbidden A) =
      fun n => n ∈ sievedSet A := by
    funext n
    exact propext (divisorSifted_restricted_iff A hB n)
  unfold fullGapAverage gapSumSq divisorSiftedGap divisorSiftedEnumeration
  simp only [hpred]
  norm_num only [Nat.cast_sum, Nat.cast_pow]
  congr 2
  funext i
  have hBin : Set.Infinite {n | n ∈ sievedSet A} := by simpa using hB
  have hmono : StrictMono (Nat.nth (fun n => n ∈ sievedSet A)) :=
    Nat.nth_strictMono hBin
  rw [Nat.cast_sub (hmono.monotone (by omega : i ≤ i + 1))]

 theorem exists_original_limit_of_infinite_forbidden
    (A : Set ℕ) (hAinf : A.Infinite)
    (hthin : (fun x : ℕ => (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ))
      =o[atTop] (fun x : ℕ => Real.sqrt (x : ℝ)))
    (hB : (sievedSet A).Infinite) :
    ∃ L : ℝ, Tendsto (fun x : ℕ => gapSumSq A x / (x : ℝ))
      atTop (𝓝 L) := by
  let p := restrictedForbidden A
  have hp : Set.Infinite {n | p n} := restrictedForbidden_infinite A hAinf
  have hp2 : ∀ n, p n → 2 ≤ n := fun _ hn => hn.2
  have hcount : (fun x : ℕ => (Nat.count p x : ℝ)) =o[atTop]
      (fun x : ℕ => Real.sqrt (x : ℝ)) := restricted_count_isLittleO A hthin
  have hs : Summable fun n => ((Nat.nth p n : ℝ)⁻¹) :=
    summable_inv_nth_of_count_isLittleO_sqrt p hp hcount
  have hev : ∀ᶠ n : ℕ in atTop, (n + 1) ^ 2 ≤ Nat.nth p n :=
    eventually_sq_le_nth_of_count_isLittleO_sqrt p hp hcount
  have hBp : Set.Infinite {n | divisorSifted p n} := by
    have heq : {n | divisorSifted p n} = sievedSet A := by
      ext n
      exact divisorSifted_restricted_iff A hB n
    rw [heq]
    exact hB
  obtain ⟨L, hL⟩ := exists_fullGapAverage_limit p hp hp2 hBp hs hev hcount
  refine ⟨L, hL.congr' ?_⟩
  exact Filter.Eventually.of_forall fun x => fullGapAverage_restricted_eq A hB x
