import ErdosProblems.Erdos237b.S2FiberExpansion
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Data.Fintype.Option

/-!
# One extra coordinate gives a positive lower bound for S2

For a tuple indexed by `Option H`, the extra coordinate and the distinguished
coordinate are the two inner variables in the squared fiber. Squarefreeness
of the full tuple guarantees compatibility of both projected tuples.
-/

namespace Erdos237b

open Finset BoundedGaps.Maynard
open scoped BigOperators

def s2LiftLeft {H K : Finset ℕ} (e : K ≃ Option H) (z : K → ℕ) : H → ℕ :=
  fun h => z (e.symm (some h))

noncomputable def s2LiftRight {H K : Finset ℕ} (e : K ≃ Option H) (m : H)
    (z : K → ℕ) : H → ℕ := Function.update (s2LiftLeft e z) m (z (e.symm none))

noncomputable def s2LiftOuter {H K : Finset ℕ} (e : K ≃ Option H) (m : H)
    (z : K → ℕ) : H → ℕ := Function.update (s2LiftLeft e z) m 1

noncomputable def s2LiftTriple {H K : Finset ℕ} (e : K ≃ Option H) (m : H)
    (z : K → ℕ) : (H → ℕ) × (H → ℕ) × (H → ℕ) :=
  (s2LiftOuter e m z, s2LiftLeft e z, s2LiftRight e m z)

theorem s2LiftTriple_injective {H K : Finset ℕ} (e : K ≃ Option H) (m : H) :
    Function.Injective (s2LiftTriple e m) := by
  intro z w heq
  funext i
  obtain ⟨j, rfl⟩ := e.symm.surjective i
  cases j with
  | none =>
    have h := congrArg (fun t : (H → ℕ) × (H → ℕ) × (H → ℕ) => t.2.2 m) heq
    simpa [s2LiftTriple, s2LiftRight] using h
  | some h =>
    exact congrArg (fun t : (H → ℕ) × (H → ℕ) × (H → ℕ) => t.2.1 h) heq

theorem prod_extraCoordinate {H K : Finset ℕ} (e : K ≃ Option H) (z : K → ℕ)
    {M : Type*} [CommMonoid M] (f : ℕ → M) :
    (∏ i : K, f (z i)) = f (z (e.symm none)) * ∏ h : H, f (s2LiftLeft e z h) := by
  calc
    _ = ∏ j : Option H, f (z (e.symm j)) :=
      Fintype.prod_equiv e _ _ (fun i => by simp)
    _ = _ := by rw [univ_option, prod_insertNone]; rfl

theorem prod_function_update {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (a : ι → ℕ) (m : ι) (n : ℕ) (f : ℕ → M) :
    (∏ h, f (Function.update a m n h)) = f n * ∏ h ∈ univ.erase m, f (a h) := by
  have heq : (fun h => f (Function.update a m n h)) =
      Function.update (fun h => f (a h)) m (f n) := by
    funext h
    by_cases hh : h = m <;> simp [hh]
  rw [heq, prod_update_of_mem (mem_univ m)]
  simp only [sdiff_singleton_eq_erase]

theorem prod_left_eq_outer {H K : Finset ℕ} (e : K ≃ Option H) (m : H) (z : K → ℕ)
    {M : Type*} [CommMonoid M] (f : ℕ → M) (hf : f 1 = 1) :
    (∏ h : H, f (s2LiftLeft e z h)) =
      f (s2LiftLeft e z m) * ∏ h : H, f (s2LiftOuter e m z h) := by
  classical
  rw [s2LiftOuter, prod_function_update, hf, one_mul]
  exact (mul_prod_erase _ _ (mem_univ m)).symm

theorem prod_right_eq_outer {H K : Finset ℕ} (e : K ≃ Option H) (m : H) (z : K → ℕ)
    {M : Type*} [CommMonoid M] (f : ℕ → M) (hf : f 1 = 1) :
    (∏ h : H, f (s2LiftRight e m z h)) =
      f (z (e.symm none)) * ∏ h : H, f (s2LiftOuter e m z h) := by
  classical
  rw [s2LiftRight, s2LiftOuter, prod_function_update, prod_function_update, hf, one_mul]

theorem isMaynardDivisorTuple_of_product_dvd {H K : Finset ℕ} {R W : ℕ}
    {z : K → ℕ} (hz : IsMaynardDivisorTuple K R W z) {a : H → ℕ}
    (hd : divisorTupleProduct H a ∣ divisorTupleProduct K z) :
    IsMaynardDivisorTuple H R W a :=
  ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hz.2.2.ne_zero) hd).trans_lt hz.1,
    Nat.Coprime.of_dvd_left hd hz.2.1, hz.2.2.squarefree_of_dvd hd⟩

theorem s2Lift_supported {H K : Finset ℕ} (e : K ≃ Option H) (m : H)
    {R W : ℕ} {z : K → ℕ} (hz : IsMaynardDivisorTuple K R W z) :
    IsMaynardDivisorTuple H R W (s2LiftOuter e m z) ∧
      IsMaynardDivisorTuple H R W (s2LiftLeft e z) ∧
      IsMaynardDivisorTuple H R W (s2LiftRight e m z) := by
  have hg := prod_extraCoordinate e z id
  have hl := prod_left_eq_outer e m z id rfl
  have hr := prod_right_eq_outer e m z id rfl
  change divisorTupleProduct K z = z (e.symm none) * divisorTupleProduct H (s2LiftLeft e z) at hg
  change divisorTupleProduct H (s2LiftLeft e z) = s2LiftLeft e z m *
    divisorTupleProduct H (s2LiftOuter e m z) at hl
  change divisorTupleProduct H (s2LiftRight e m z) = z (e.symm none) *
    divisorTupleProduct H (s2LiftOuter e m z) at hr
  refine ⟨isMaynardDivisorTuple_of_product_dvd hz ?_,
    isMaynardDivisorTuple_of_product_dvd hz ?_, isMaynardDivisorTuple_of_product_dvd hz ?_⟩
  · rw [hg, hl]
    exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
  · rw [hg]
    exact dvd_mul_left _ _
  · refine ⟨s2LiftLeft e z m, ?_⟩
    rw [hg, hl, hr]
    ring

theorem s2LiftTriple_mem {H K : Finset ℕ} (e : K ≃ Option H) (m : H)
    {R W : ℕ} {z : K → ℕ} (hz : z ∈ maynardDivisorTupleSupport K R W) :
    s2LiftTriple e m z ∈ s2FiberTripleSupport H R W m := by
  classical
  obtain ⟨ho, hl, hr⟩ := s2Lift_supported e m (isMaynardDivisorTuple_of_mem_support hz)
  have hmem {a : H → ℕ} (ha : IsMaynardDivisorTuple H R W a) :
      a ∈ maynardDivisorTupleSupport H R W :=
    mem_maynardDivisorTupleSupport_iff.mpr ⟨ha.mem_maynardDivisorTupleBox, ha⟩
  simp only [s2FiberTripleSupport, s2LiftTriple, mem_filter, mem_product]
  refine ⟨⟨⟨hmem ho, ?_⟩, hmem hl, hmem hr⟩, ?_, ?_⟩
  · simp [s2LiftOuter]
  · intro h hh
    simp [s2LiftOuter, hh]
  · intro h hh
    simp [s2LiftOuter, s2LiftRight, hh]

theorem extraCoordinate_weight_le_tripleTerm {H K : Finset ℕ} (e : K ≃ Option H) (m : H)
    {R D : ℕ} {z : K → ℕ} (hz : IsMaynardDivisorTuple K R (primorial D) z) (hD : 2 ≤ D)
    {y : (H → ℕ) → ℝ} (hy : ∀ r, 0 ≤ y r) :
    y (s2LiftLeft e z) * y (s2LiftRight e m z) * reciprocalTotientTupleWeight K z ≤
      s2FiberTripleTerm H y m (s2LiftTriple e m z) := by
  have ho := (s2Lift_supported e m hz).1
  let P : ℝ := ∏ h : H, (Nat.totient (s2LiftOuter e m z h) : ℝ)
  let G : ℝ := ∏ h : H, (maynardS2G (s2LiftOuter e m z h) : ℝ)
  have hG : 0 < G := by
    apply prod_pos
    intro h _
    exact_mod_cast maynardS2G_pos_of_squarefree_coprime_primorial hD
      (ho.coordinate_squarefree h) (ho.coordinate_coprime_W h)
  have hGP : G ≤ P := by
    apply prod_le_prod (fun _ _ => by positivity)
    intro h _
    exact_mod_cast maynardS2G_le_totient (ho.coordinate_squarefree h)
  have hnum : 0 ≤ (y (s2LiftLeft e z) / Nat.totient (s2LiftLeft e z m)) *
      (y (s2LiftRight e m z) / Nat.totient (z (e.symm none))) :=
    mul_nonneg (div_nonneg (hy _) (by positivity)) (div_nonneg (hy _) (by positivity))
  have hp := prod_extraCoordinate e z (fun n => (Nat.totient n : ℝ))
  rw [prod_left_eq_outer e m z (fun n => (Nat.totient n : ℝ)) (by simp)] at hp
  have hweight : y (s2LiftLeft e z) * y (s2LiftRight e m z) * reciprocalTotientTupleWeight K z =
      ((y (s2LiftLeft e z) / Nat.totient (s2LiftLeft e z m)) *
        (y (s2LiftRight e m z) / Nat.totient (z (e.symm none)))) / P := by
    unfold reciprocalTotientTupleWeight
    simp only [one_div, prod_inv_distrib]
    rw [hp]
    dsimp [P]
    simp only [mul_inv_rev, div_eq_mul_inv]
    ring
  rw [hweight]
  unfold s2FiberTripleTerm s2LiftTriple
  simpa [s2LiftRight, G] using div_le_div_of_nonneg_left hnum hG hGP

theorem extraCoordinate_sum_le_fiberDiagonal {H K : Finset ℕ} (e : K ≃ Option H) (m : H)
    {R D : ℕ} (hD : 2 ≤ D) {y : (H → ℕ) → ℝ} (hy : ∀ r, 0 ≤ y r) :
    (∑ z ∈ maynardDivisorTupleSupport K R (primorial D),
      y (s2LiftLeft e z) * y (s2LiftRight e m z) * reciprocalTotientTupleWeight K z) ≤
      s2FiberSquareDiagonal H R (primorial D) y m := by
  apply sum_le_s2FiberSquareDiagonal hy m _ _ (s2LiftTriple e m)
    (fun _ hz => s2LiftTriple_mem e m hz) (s2LiftTriple_injective e m).injOn
  intro z hz
  exact extraCoordinate_weight_le_tripleTerm e m (isMaynardDivisorTuple_of_mem_support hz) hD hy

end Erdos237b
