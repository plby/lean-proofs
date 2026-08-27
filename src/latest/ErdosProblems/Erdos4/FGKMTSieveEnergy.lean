import ErdosProblems.Erdos4.FGKMTSieveCoefficients

/-! An exact upper bound for the full coefficient energy by product divisor mass. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open DivisorCoefficients RestrictedProductNorm Classical

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

def boundedLabelTuple (R : ℕ) (ell : P → ℕ) (a : P → Option (Fin k)) : Fin k → Fin (R + 1) :=
  fun i => ⟨min (coordinateDivisor ell a i) R, Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem boundedLabelTuple_val {R : ℕ} (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p)
    (a : P → Option (Fin k)) (ha : totalDivisor ell a ≤ R) (i : Fin k) :
    (boundedLabelTuple R ell a i : ℕ) = coordinateDivisor ell a i :=
  min_eq_left ((coordinateDivisor_le_totalDivisor ell hell a i).trans ha)

theorem boundedLabelTuple_injOn (R : ℕ) (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell) :
    Set.InjOn (boundedLabelTuple (k := k) R ell)
      ((Finset.univ : Finset (P → Option (Fin k))).filter (fun a => totalDivisor ell a ≤ R)) := by
  intro a ha b hb hab
  apply coordinateDivisor_injective ell hprime hinj
  funext i
  have hv := congrArg (fun d : Fin k → Fin (R + 1) => (d i : ℕ)) hab
  simpa only [boundedLabelTuple_val ell (fun p => (hprime p).one_le) a (Finset.mem_filter.mp ha).2,
    boundedLabelTuple_val ell (fun p => (hprime p).one_le) b (Finset.mem_filter.mp hb).2] using hv

theorem rationalCoefficient_energy_eq (b : ℝ) (R : ℕ) (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell) {W : ℕ}
    (hcop : ∀ p, (ell p).Coprime W) :
    energy (rationalCoefficient (k := k) b R ell) =
      ∑ a ∈ (Finset.univ : Finset (P → Option (Fin k))).filter (fun a => totalDivisor ell a ≤ R),
        rationalSieveTupleWeight W b (coordinateDivisor ell a) := by
  unfold energy
  simp_rw [rationalCoefficient_sq b R ell hprime hinj hcop]
  rw [← Finset.sum_filter]

theorem rationalSieveTupleWeight_sum (W : ℕ) (b : ℝ) (R k : ℕ) :
    (∑ d : Fin k → Fin (R + 1), rationalSieveTupleWeight W b (fun i => (d i : ℕ))) =
      rationalSquareMass W b R ^ k := by
  unfold rationalSieveTupleWeight
  rw [← Fintype.prod_sum (fun (_i : Fin k) (n : Fin (R + 1)) =>
    logarithmicReciprocal b n ^ 2 * squarefreeHarmonicWeight W n)]
  rw [sum_fin_succ_eq_Icc
    (f := fun n : ℕ => logarithmicReciprocal b n ^ 2 * squarefreeHarmonicWeight W n)
    (by rw [squarefreeHarmonicWeight_zero, mul_zero])]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, rationalSquareMass]

theorem rationalCoefficient_energy_upper (b : ℝ) (R : ℕ) (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell) {W : ℕ}
    (hcop : ∀ p, (ell p).Coprime W) :
    energy (rationalCoefficient (k := k) b R ell) ≤ rationalSquareMass W b R ^ k := by
  let S := (Finset.univ : Finset (P → Option (Fin k))).filter (fun a => totalDivisor ell a ≤ R)
  let f : (Fin k → Fin (R + 1)) → ℝ := fun d => rationalSieveTupleWeight W b (fun i => (d i : ℕ))
  have himage : (∑ d ∈ S.image (boundedLabelTuple R ell), f d) =
      ∑ a ∈ S, rationalSieveTupleWeight W b (coordinateDivisor ell a) := by
    rw [Finset.sum_image (boundedLabelTuple_injOn R ell hprime hinj)]
    apply Finset.sum_congr rfl
    intro a ha
    have heq : (fun i => (boundedLabelTuple R ell a i : ℕ)) = coordinateDivisor ell a := by
      funext i
      exact boundedLabelTuple_val ell (fun p => (hprime p).one_le) a (Finset.mem_filter.mp ha).2 i
    change rationalSieveTupleWeight W b (fun i => (boundedLabelTuple R ell a i : ℕ)) = _
    rw [heq]
  calc
    _ = ∑ a ∈ S, rationalSieveTupleWeight W b (coordinateDivisor ell a) :=
      rationalCoefficient_energy_eq b R ell hprime hinj hcop
    _ = ∑ d ∈ S.image (boundedLabelTuple R ell), f d := himage.symm
    _ ≤ ∑ d : Fin k → Fin (R + 1), f d :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun d _ _ => rationalSieveTupleWeight_nonneg W b _)
    _ = _ := rationalSieveTupleWeight_sum W b R k

end Erdos4.FGKMT
