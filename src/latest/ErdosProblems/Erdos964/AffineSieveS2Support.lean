import ErdosProblems.Erdos964.AffineSieveCandidate

/-!
# Divisor coordinates at a semiprime affine value

When the larger prime exceeds the sieve radius, the distinguished divisor
coordinate is either one or the smaller prime. Splitting those two cases
is the finite origin of the truncated face in the semiprime integral.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

theorem divisor_lt_large_prime_eq_one_or_small {p r d : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hd : 0 < d) (hdr : d < r) (hdiv : d ∣ p * r) :
    d = 1 ∨ d = p := by
  have hcop : d.Coprime r := (hr.coprime_iff_not_dvd.mpr
    (fun hrd => (Nat.le_of_dvd hd hrd).not_gt hdr)).symm
  exact (Nat.dvd_prime hp).mp (hcop.dvd_of_dvd_mul_right hdiv)

theorem affine_semiprime_divisor_coordinate
    {H : Finset ℕ} {A B : H → ℕ} {R W n p r : ℕ} {d : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d) (hcond : affineDivisorTupleCondition A B n d)
    (i : H) (hp : p.Prime) (hr : r.Prime) (hRr : R ≤ r)
    (hvalue : A i * n + B i = p * r) : d i = 1 ∨ d i = p := by
  have hdpos : 0 < d i := Nat.pos_of_ne_zero (hd.coordinate_squarefree i).ne_zero
  have hprodpos : 0 < divisorTupleProduct H d := Nat.pos_of_ne_zero hd.2.2.ne_zero
  have hdiR := (Nat.le_of_dvd hprodpos (divisorTupleCoordinate_dvd_product d i)).trans_lt hd.1
  exact divisor_lt_large_prime_eq_one_or_small hp hr hdpos (hdiR.trans_le hRr)
    (hvalue ▸ hcond i)

theorem affine_semiprime_pair_lcm
    {H : Finset ℕ} {A B : H → ℕ} {R W n p r : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d) (he : IsMaynardDivisorTuple H R W e)
    (hcond : affineDivisorPairCondition A B n d e) (i : H)
    (hp : p.Prime) (hr : r.Prime) (hRr : R ≤ r) (hvalue : A i * n + B i = p * r) :
    divisorTupleLcm H d e i = 1 ∨ divisorTupleLcm H d e i = p := by
  rcases affine_semiprime_divisor_coordinate hd hcond.1 i hp hr hRr hvalue with hd1 | hdp <;>
    rcases affine_semiprime_divisor_coordinate he hcond.2 i hp hr hRr hvalue with he1 | hep <;>
    simp [divisorTupleLcm, *]

theorem affine_prime_coprime_other_coordinate
    {ι : Type*} {A B d : ι → ℕ} {W n p : ℕ}
    (hcover : CoversAffineDeterminantPrimes A B W) (hp : p.Prime) (hpW : ¬ p ∣ W)
    (hcond : affineDivisorTupleCondition A B n d) {i j : ι} (hij : i ≠ j)
    (hpi : p ∣ A i * n + B i) : p.Coprime (d j) := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hpd
  exact hpW (hcover i j hij p hp
    (common_affine_divisor_dvd_determinant (A i) (B i) (A j) (B j) n p
      hpi (hpd.trans (hcond j))))

open scoped Classical in
theorem affine_semiprime_divisor_sum_split
    {H : Finset ℕ} (A B : H → ℕ) (D : Finset (H → ℕ)) (lambda : (H → ℕ) → ℝ)
    {R W n p r : ℕ} (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (i : H) (hp : p.Prime) (hr : r.Prime) (hRr : R ≤ r)
    (hvalue : A i * n + B i = p * r) :
    (∑ d ∈ D.filter (affineDivisorTupleCondition A B n), lambda d) =
      (∑ d ∈ (D.filter (affineDivisorTupleCondition A B n)).filter (fun d => d i = 1),
        lambda d) +
      ∑ d ∈ (D.filter (affineDivisorTupleCondition A B n)).filter (fun d => d i = p),
        lambda d := by
  classical
  have hfilters : (D.filter (affineDivisorTupleCondition A B n)).filter (fun d => ¬ d i = 1) =
      (D.filter (affineDivisorTupleCondition A B n)).filter (fun d => d i = p) := by
    apply Finset.filter_congr
    intro d hd
    have hd' := Finset.mem_filter.mp hd
    have hcases := affine_semiprime_divisor_coordinate (hD d hd'.1) hd'.2 i hp hr hRr hvalue
    constructor
    · intro hne
      exact hcases.resolve_left hne
    · intro heq hone
      exact hp.ne_one (heq.symm.trans hone)
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := D.filter (affineDivisorTupleCondition A B n)) (p := fun d => d i = 1) lambda
  rw [hfilters] at hsplit
  exact hsplit.symm

open scoped Classical in
theorem affine_semiprime_large_small_prime_coordinate_one
    {H : Finset ℕ} (A B : H → ℕ) (D : Finset (H → ℕ))
    {R W n p r : ℕ} (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (i : H) (hp : p.Prime) (hr : r.Prime) (hRp : R ≤ p) (hpr : p ≤ r)
    (hvalue : A i * n + B i = p * r) :
    D.filter (affineDivisorTupleCondition A B n) =
      (D.filter (affineDivisorTupleCondition A B n)).filter (fun d => d i = 1) := by
  classical
  symm
  apply Finset.filter_eq_self.mpr
  intro d hd
  have hd' := Finset.mem_filter.mp hd
  have hdtuple := hD d hd'.1
  rcases affine_semiprime_divisor_coordinate hdtuple hd'.2 i hp hr (hRp.trans hpr) hvalue
      with hone | heq
  · exact hone
  · have hprodpos := Nat.pos_of_ne_zero hdtuple.2.2.ne_zero
    have hlt := (Nat.le_of_dvd hprodpos (divisorTupleCoordinate_dvd_product d i)).trans_lt hdtuple.1
    omega

end Erdos964
