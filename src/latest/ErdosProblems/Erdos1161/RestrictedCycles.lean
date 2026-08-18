import ErdosProblems.Erdos1161.CycleBounds
import ErdosProblems.Erdos1161.CycleRecursion
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Restricted-cycle estimates for Erdős Problem 1161

This file proves the exact finite estimate used in the Ford--Beker
anticoncentration argument.  If all cycle lengths belong to a finite set
`I` and a permutation of `Fin n` has exactly `ell` cycles, then its normalized
count is at most

`(sum i in I, 1 / i)^(ell - 1) / (n * (ell - 1)!)`.

The proof is the cycle-index proof: a complete cycle type is a multiset;
the multinomial theorem evaluates the unrestricted weight of all multisets
of a fixed cardinality, while deleting one marked cycle and using that the
sum of the cycle lengths is `n` gives the factor `1 / n`.
-/

open scoped BigOperators

namespace Erdos1161

noncomputable section

/-! ## Multiset cycle weights -/

/-- The product of the factorials of the multiplicities in a multiset. -/
def multiplicityFactorial (rho : Multiset ℕ) : ℕ :=
  ∏ i ∈ rho.toFinset, (rho.count i).factorial

/-- The normalized cycle-index weight of a complete cycle type.  This
multinomial presentation is particularly convenient for summing over all
multisets with a fixed number of cycles. -/
def multisetCycleWeight (rho : Multiset ℕ) : ℝ :=
  (rho.countPerms : ℝ) / (rho.card.factorial : ℝ) *
    (rho.map fun i : ℕ ↦ (i : ℝ)⁻¹).prod

theorem multiplicityFactorial_mul_countPerms (rho : Multiset ℕ) :
    multiplicityFactorial rho * rho.countPerms = rho.card.factorial := by
  classical
  have hsupp : rho.toFinsupp.support = rho.toFinset := by
    ext i
    simp
  rw [multiplicityFactorial, Multiset.countPerms,
    Finsupp.multinomial_eq, hsupp]
  change (∏ i ∈ rho.toFinset, (rho.count i).factorial) *
    Nat.multinomial rho.toFinset (fun i ↦ rho.count i) = rho.card.factorial
  simpa [Multiset.sum_count_eq_card] using
    (Nat.multinomial_spec rho.toFinset (fun i ↦ rho.count i))

theorem multiplicityFactorial_cons (i : ℕ) (rho : Multiset ℕ) :
    multiplicityFactorial (i ::ₘ rho) =
      (rho.count i + 1) * multiplicityFactorial rho := by
  classical
  unfold multiplicityFactorial
  rw [Multiset.toFinset_cons]
  by_cases hi : i ∈ rho
  · have his : i ∈ rho.toFinset := Multiset.mem_toFinset.mpr hi
    rw [Finset.insert_eq_of_mem his]
    calc
      (∏ j ∈ rho.toFinset, ((i ::ₘ rho).count j).factorial) =
          ((i ::ₘ rho).count i).factorial *
            ∏ j ∈ rho.toFinset.erase i,
              ((i ::ₘ rho).count j).factorial :=
        (Finset.mul_prod_erase rho.toFinset
          (fun j ↦ ((i ::ₘ rho).count j).factorial) his).symm
      _ = (rho.count i + 1) * (rho.count i).factorial *
            ∏ j ∈ rho.toFinset.erase i, (rho.count j).factorial := by
        have hprod :
            (∏ j ∈ rho.toFinset.erase i,
                ((i ::ₘ rho).count j).factorial) =
              ∏ j ∈ rho.toFinset.erase i, (rho.count j).factorial := by
          apply Finset.prod_congr rfl
          intro j hj
          have hji : j ≠ i := (Finset.mem_erase.mp hj).1
          simp [hji]
        rw [hprod]
        simp [Nat.factorial_succ]
      _ = (rho.count i + 1) *
            ((rho.count i).factorial *
              ∏ j ∈ rho.toFinset.erase i, (rho.count j).factorial) := by
        ring
      _ = (rho.count i + 1) *
            ∏ j ∈ rho.toFinset, (rho.count j).factorial := by
        rw [Finset.mul_prod_erase rho.toFinset
          (fun j ↦ (rho.count j).factorial) his]
  · have his : i ∉ rho.toFinset := by simpa
    rw [Finset.prod_insert his]
    have hprod :
        (∏ j ∈ rho.toFinset, ((i ::ₘ rho).count j).factorial) =
          ∏ j ∈ rho.toFinset, (rho.count j).factorial := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := by
        intro h
        subst j
        exact his hj
      simp [hji]
    rw [hprod]
    simp [Multiset.count_eq_zero.mpr hi]

theorem multiplicityFactorial_pos (rho : Multiset ℕ) :
    0 < multiplicityFactorial rho := by
  unfold multiplicityFactorial
  positivity

theorem multisetCycleWeight_eq_inv_denominator
    (rho : Multiset ℕ) (hrho : ∀ i ∈ rho, 0 < i) :
    multisetCycleWeight rho =
      1 / ((multiplicityFactorial rho : ℝ) *
        (rho.map fun i : ℕ ↦ (i : ℝ)).prod) := by
  have hfac := multiplicityFactorial_mul_countPerms rho
  have hmf : (multiplicityFactorial rho : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (multiplicityFactorial_pos rho))
  have hcard : (rho.card.factorial : ℝ) ≠ 0 := by positivity
  have hprod : (rho.map fun i : ℕ ↦ (i : ℝ)).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    rintro hzero
    rw [Multiset.mem_map] at hzero
    obtain ⟨i, hi, hcast⟩ := hzero
    have hi0 : (i : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (hrho i hi))
    exact hi0 hcast
  have hinvprod :
      (rho.map fun i : ℕ ↦ (i : ℝ)⁻¹).prod =
        ((rho.map fun i : ℕ ↦ (i : ℝ)).prod)⁻¹ := by
    exact Multiset.prod_map_inv
  have hfacR :
      (multiplicityFactorial rho : ℝ) * (rho.countPerms : ℝ) =
        (rho.card.factorial : ℝ) := by
    exact_mod_cast hfac
  rw [multisetCycleWeight, hinvprod]
  field_simp
  nlinarith [hfacR]

theorem multisetCycleWeight_nonneg (rho : Multiset ℕ) :
    0 ≤ multisetCycleWeight rho := by
  unfold multisetCycleWeight
  apply mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  apply Multiset.prod_nonneg
  intro x hx
  rw [Multiset.mem_map] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  subst x
  exact inv_nonneg.mpr (Nat.cast_nonneg i)

theorem multisetCycleWeight_erase {rho : Multiset ℕ} {i : ℕ}
    (hi : i ∈ rho) (hrho : ∀ j ∈ rho, 0 < j) :
    multisetCycleWeight (rho.erase i) =
      (i : ℝ) * (rho.count i : ℝ) * multisetCycleWeight rho := by
  have hsub : ∀ j ∈ rho.erase i, 0 < j := by
    intro j hj
    exact hrho j (Multiset.mem_of_le (Multiset.erase_le i rho) hj)
  rw [multisetCycleWeight_eq_inv_denominator _ hsub,
    multisetCycleWeight_eq_inv_denominator _ hrho]
  have hcons : i ::ₘ rho.erase i = rho := Multiset.cons_erase hi
  have hcount : (rho.erase i).count i + 1 = rho.count i := by
    rw [← hcons]
    simp
  have hmf : multiplicityFactorial rho =
      rho.count i * multiplicityFactorial (rho.erase i) := by
    calc
      multiplicityFactorial rho =
          multiplicityFactorial (i ::ₘ rho.erase i) := by rw [hcons]
      _ = ((rho.erase i).count i + 1) *
          multiplicityFactorial (rho.erase i) :=
        multiplicityFactorial_cons i (rho.erase i)
      _ = rho.count i * multiplicityFactorial (rho.erase i) := by rw [hcount]
  have hprod : (rho.map fun j : ℕ ↦ (j : ℝ)).prod =
      (i : ℝ) *
        ((rho.erase i).map fun j : ℕ ↦ (j : ℝ)).prod := by
    rw [← hcons]
    simp
  have hiR : (i : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hrho i hi))
  have hcountR : (rho.count i : ℝ) ≠ 0 := by
    exact_mod_cast (Multiset.count_pos.mpr hi).ne'
  have hmfR : (multiplicityFactorial (rho.erase i) : ℝ) ≠ 0 := by
    exact_mod_cast (multiplicityFactorial_pos (rho.erase i)).ne'
  have hprodR :
      ((rho.erase i).map fun j : ℕ ↦ (j : ℝ)).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    rintro hzero
    rw [Multiset.mem_map] at hzero
    obtain ⟨j, hj, hcast⟩ := hzero
    have hjR : (j : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (hsub j hj))
    exact hjR hcast
  rw [hmf, hprod]
  push_cast
  field_simp

theorem sum_erase_multisetCycleWeight {rho : Multiset ℕ}
    (hrho : ∀ i ∈ rho, 0 < i) :
    ∑ i ∈ rho.toFinset, multisetCycleWeight (rho.erase i) =
      (rho.sum : ℝ) * multisetCycleWeight rho := by
  calc
    ∑ i ∈ rho.toFinset, multisetCycleWeight (rho.erase i) =
        ∑ i ∈ rho.toFinset,
          ((i : ℝ) * (rho.count i : ℝ)) *
            multisetCycleWeight rho := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [multisetCycleWeight_erase (Multiset.mem_toFinset.mp hi) hrho]
    _ = (∑ i ∈ rho.toFinset,
          (i : ℝ) * (rho.count i : ℝ)) *
            multisetCycleWeight rho := by
      rw [Finset.sum_mul]
    _ = (rho.sum : ℝ) * multisetCycleWeight rho := by
      congr 1
      norm_cast
      simpa [nsmul_eq_mul, mul_comm] using (Finset.sum_multiset_count rho).symm

/-! ## The unrestricted multinomial sum -/

theorem sum_multisetCycleWeight_sym (I : Finset ℕ) (k : ℕ) :
    ∑ rho ∈ I.sym k, multisetCycleWeight rho =
      (∑ i ∈ I, (i : ℝ)⁻¹) ^ k / (k.factorial : ℝ) := by
  have hpow := Finset.sum_pow (s := I) (fun i ↦ (i : ℝ)⁻¹) k
  calc
    ∑ rho ∈ I.sym k, multisetCycleWeight rho =
        ∑ rho ∈ I.sym k,
          ((rho.val.countPerms : ℝ) *
            (rho.val.map fun i : ℕ ↦ (i : ℝ)⁻¹).prod) /
              (k.factorial : ℝ) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      change (rho.1.countPerms : ℝ) / (rho.1.card.factorial : ℝ) *
          (rho.1.map fun i : ℕ ↦ (i : ℝ)⁻¹).prod =
        ((rho.1.countPerms : ℝ) *
          (rho.1.map fun i : ℕ ↦ (i : ℝ)⁻¹).prod) /
            (k.factorial : ℝ)
      rw [rho.2]
      ring
    _ = (∑ rho ∈ I.sym k,
          (rho.val.countPerms : ℝ) *
            (rho.val.map fun i : ℕ ↦ (i : ℝ)⁻¹).prod) /
              (k.factorial : ℝ) := by
      rw [Finset.sum_div]
    _ = (∑ i ∈ I, (i : ℝ)⁻¹) ^ k / (k.factorial : ℝ) := by
      exact congrArg (fun x : ℝ ↦ x / (k.factorial : ℝ)) hpow.symm

/-! ## Fixing the total size -/

/-- Complete cycle types with `ell` cycles, all lengths in `I`, and total
size `n`. -/
def restrictedMultisetCycleTypes (I : Finset ℕ) (n ell : ℕ) :
    Finset (Sym ℕ ell) :=
  (I.sym ell).filter fun rho ↦ rho.val.sum = n

@[simp]
theorem mem_restrictedMultisetCycleTypes {I : Finset ℕ} {n ell : ℕ}
    {rho : Sym ℕ ell} :
    rho ∈ restrictedMultisetCycleTypes I n ell ↔
      (∀ i ∈ rho.val, i ∈ I) ∧ rho.val.sum = n := by
  rw [restrictedMultisetCycleTypes, Finset.mem_filter]
  constructor
  · rintro ⟨hmem, hsum⟩
    exact ⟨Finset.mem_sym_iff.mp hmem, hsum⟩
  · rintro ⟨hmem, hsum⟩
    exact ⟨Finset.mem_sym_iff.mpr hmem, hsum⟩

/-- A cycle type together with a cycle length occurring in it. -/
def markedRestrictedMultisetCycleTypes (I : Finset ℕ) (n ell : ℕ) :
    Finset (Σ _rho : Sym ℕ ell, ℕ) :=
  (restrictedMultisetCycleTypes I n ell).sigma fun rho ↦ rho.val.toFinset

@[simp]
theorem mem_markedRestrictedMultisetCycleTypes
    {I : Finset ℕ} {n ell : ℕ} {p : Σ _rho : Sym ℕ ell, ℕ} :
    p ∈ markedRestrictedMultisetCycleTypes I n ell ↔
      p.1 ∈ restrictedMultisetCycleTypes I n ell ∧ p.2 ∈ p.1.val := by
  simp [markedRestrictedMultisetCycleTypes]

/-- The fixed-total-size form of the multinomial cycle-index estimate. -/
theorem sum_restrictedMultisetCycleWeight_le
    (I : Finset ℕ) {n ell : ℕ} (hn : 0 < n) (_hell : 0 < ell)
    (hI : ∀ i ∈ I, 0 < i) :
    ∑ rho ∈ restrictedMultisetCycleTypes I n ell,
        multisetCycleWeight rho.val ≤
      (∑ i ∈ I, (i : ℝ)⁻¹) ^ (ell - 1) /
        ((n : ℝ) * ((ell - 1).factorial : ℝ)) := by
  let D := restrictedMultisetCycleTypes I n ell
  let S := markedRestrictedMultisetCycleTypes I n ell
  let eraseMarked : ↑S → Sym ℕ (ell - 1) := fun p ↦
    ⟨p.val.1.val.erase p.val.2, by
      have hp := mem_markedRestrictedMultisetCycleTypes.mp p.property
      rw [Multiset.card_erase_of_mem hp.2, p.val.1.property]
      simp [Nat.pred_eq_sub_one]⟩
  have herase_mem (p : ↑S) : eraseMarked p ∈ I.sym (ell - 1) := by
    apply Finset.mem_sym_iff.mpr
    intro a ha
    have hp := mem_markedRestrictedMultisetCycleTypes.mp p.property
    have hpD := mem_restrictedMultisetCycleTypes.mp hp.1
    apply hpD.1 a
    exact Multiset.mem_of_le (Multiset.erase_le p.val.2 p.val.1.val) ha
  have herase_inj : Function.Injective eraseMarked := by
    rintro ⟨⟨rho, i⟩, hri⟩ ⟨⟨tau, j⟩, htj⟩ heq
    have hri' := mem_markedRestrictedMultisetCycleTypes.mp hri
    have htj' := mem_markedRestrictedMultisetCycleTypes.mp htj
    have hrD := mem_restrictedMultisetCycleTypes.mp hri'.1
    have htD := mem_restrictedMultisetCycleTypes.mp htj'.1
    have herase : rho.val.erase i = tau.val.erase j := by
      simpa [eraseMarked] using congrArg Subtype.val heq
    have hsumr : i + (rho.1.erase i).sum = n := by
      calc
        i + (rho.1.erase i).sum = rho.1.sum := Multiset.sum_erase hri'.2
        _ = n := hrD.2
    have hsumt : j + (tau.1.erase j).sum = n := by
      calc
        j + (tau.1.erase j).sum = tau.1.sum := Multiset.sum_erase htj'.2
        _ = n := htD.2
    have heraseSum : (rho.1.erase i).sum = (tau.1.erase j).sum :=
      congrArg Multiset.sum herase
    have hij : i = j := by
      omega
    have hrhotau : rho.val = tau.val := by
      calc
        rho.1 = i ::ₘ rho.1.erase i := (Multiset.cons_erase hri'.2).symm
        _ = i ::ₘ tau.1.erase j := congrArg (fun u ↦ i ::ₘ u) herase
        _ = j ::ₘ tau.1.erase j := by rw [hij]
        _ = tau.1 := Multiset.cons_erase htj'.2
    have hrt : rho = tau := Subtype.ext hrhotau
    subst tau
    subst j
    rfl
  have hmarked_le :
      ∑ p ∈ S,
          multisetCycleWeight (p.1.val.erase p.2) ≤
        ∑ nu ∈ I.sym (ell - 1), multisetCycleWeight nu.val := by
    calc
      ∑ p ∈ S, multisetCycleWeight (p.1.val.erase p.2) =
          ∑ p ∈ S.attach, multisetCycleWeight (eraseMarked p).val := by
        simpa [eraseMarked] using
          (Finset.sum_attach S
            (fun p ↦ multisetCycleWeight (p.1.val.erase p.2))).symm
      _ = ∑ nu ∈ Finset.image eraseMarked S.attach,
          multisetCycleWeight nu.val := by
        symm
        apply Finset.sum_image
        intro p hp q hq hpq
        exact herase_inj hpq
      _ ≤ ∑ nu ∈ I.sym (ell - 1), multisetCycleWeight nu.val := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro nu hnu
          rw [Finset.mem_image] at hnu
          obtain ⟨p, hp, rfl⟩ := hnu
          exact herase_mem p
        · intro nu hnuI hnuImage
          exact multisetCycleWeight_nonneg nu.val
  have hmarked_eq :
      (n : ℝ) *
          (∑ rho ∈ D, multisetCycleWeight rho.val) =
        ∑ p ∈ S, multisetCycleWeight (p.1.val.erase p.2) := by
    rw [Finset.mul_sum]
    change (∑ rho ∈ D, (n : ℝ) * multisetCycleWeight rho.val) =
      ∑ p ∈ S, multisetCycleWeight (p.1.val.erase p.2)
    change (∑ rho ∈ D, (n : ℝ) * multisetCycleWeight rho.1) =
      ∑ p ∈ markedRestrictedMultisetCycleTypes I n ell,
        multisetCycleWeight (p.1.1.erase p.2)
    rw [markedRestrictedMultisetCycleTypes, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro rho hrho
    have hrD : rho ∈ restrictedMultisetCycleTypes I n ell := by
      simpa [D] using hrho
    have hr := mem_restrictedMultisetCycleTypes.mp hrD
    have hrpos : ∀ i ∈ rho.val, 0 < i := by
      intro i hi
      exact hI i (hr.1 i hi)
    rw [sum_erase_multisetCycleWeight hrpos, hr.2]
  have hmul :
      (n : ℝ) *
          (∑ rho ∈ restrictedMultisetCycleTypes I n ell,
            multisetCycleWeight rho.val) ≤
        (∑ i ∈ I, (i : ℝ)⁻¹) ^ (ell - 1) /
          ((ell - 1).factorial : ℝ) := by
    calc
      (n : ℝ) *
          (∑ rho ∈ restrictedMultisetCycleTypes I n ell,
            multisetCycleWeight rho.val) =
          ∑ p ∈ S, multisetCycleWeight (p.1.val.erase p.2) := by
        simpa [D] using hmarked_eq
      _ ≤ ∑ nu ∈ I.sym (ell - 1), multisetCycleWeight nu.val := hmarked_le
      _ = (∑ i ∈ I, (i : ℝ)⁻¹) ^ (ell - 1) /
          ((ell - 1).factorial : ℝ) :=
        sum_multisetCycleWeight_sym I (ell - 1)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    ∑ rho ∈ restrictedMultisetCycleTypes I n ell,
        multisetCycleWeight rho.val ≤
        ((∑ i ∈ I, (i : ℝ)⁻¹) ^ (ell - 1) /
          ((ell - 1).factorial : ℝ)) / (n : ℝ) := by
      apply (le_div_iff₀ hnR).2
      nlinarith [hmul]
    _ = (∑ i ∈ I, (i : ℝ)⁻¹) ^ (ell - 1) /
        ((n : ℝ) * ((ell - 1).factorial : ℝ)) := by
      field_simp

/-! ## Comparison with Mathlib's nontrivial cycle types -/

theorem completeCycleType_cycleType {n : ℕ} (sigma : Equiv.Perm (Fin n)) :
    completeCycleType n sigma.cycleType = fullCycleType sigma := by
  rw [completeCycleType, fullCycleType, fixedPointCount_eq]

theorem sum_completeCycleType_of_mem {n : ℕ} {mu : Multiset ℕ}
    (hmu : mu ∈ cycleTypes n) : (completeCycleType n mu).sum = n := by
  rw [completeCycleType, Multiset.sum_add, Multiset.sum_replicate]
  simp only [nsmul_eq_mul, Nat.cast_id, mul_one]
  exact Nat.add_sub_of_le (mem_cycleTypes.mp hmu).1

theorem multiplicityFactorial_add_replicate_one
    (mu : Multiset ℕ) (hone : 1 ∉ mu) (f : ℕ) :
    multiplicityFactorial (mu + Multiset.replicate f 1) =
      f.factorial * multiplicityFactorial mu := by
  induction f with
  | zero => simp [multiplicityFactorial]
  | succ f ih =>
      rw [Multiset.replicate_succ, Multiset.add_comm mu,
        Multiset.cons_add]
      rw [multiplicityFactorial_cons]
      have hadd : Multiset.replicate f 1 + mu =
          mu + Multiset.replicate f 1 := Multiset.add_comm _ _
      rw [hadd, ih]
      have hcount : (mu + Multiset.replicate f 1).count 1 = f := by
        simp [Multiset.count_eq_zero.mpr hone]
      rw [hcount, Nat.factorial_succ]
      ring

theorem multisetCycleWeight_completeCycleType_eq_cycleWeightReal
    {n : ℕ} {mu : Multiset ℕ} (hmu : mu ∈ cycleTypes n) :
    multisetCycleWeight (completeCycleType n mu) = cycleWeightReal n mu := by
  have hvalid := mem_cycleTypes.mp hmu
  have hone : 1 ∉ mu := by
    intro hone
    have := hvalid.2 1 hone
    omega
  have hpos : ∀ i ∈ completeCycleType n mu, 0 < i := by
    intro i hi
    rw [completeCycleType, Multiset.mem_add] at hi
    rcases hi with hi | hi
    · exact Nat.zero_lt_two.trans_le (hvalid.2 i hi)
    · rw [Multiset.mem_replicate] at hi
      omega
  rw [multisetCycleWeight_eq_inv_denominator _ hpos,
    cycleWeightReal, cycleDenominator, completeCycleType]
  rw [multiplicityFactorial_add_replicate_one mu hone]
  have hprod :
      ((mu + Multiset.replicate (n - mu.sum) 1).map
        fun i : ℕ ↦ (i : ℝ)).prod = (mu.prod : ℝ) := by
    simp
  rw [hprod]
  rw [multiplicityFactorial]
  push_cast
  ring

theorem completeCycleType_injective_on_cycleTypes {n : ℕ}
    {mu nu : Multiset ℕ} (hmu : mu ∈ cycleTypes n)
    (hnu : nu ∈ cycleTypes n)
    (heq : completeCycleType n mu = completeCycleType n nu) : mu = nu := by
  have hmuValid := mem_cycleTypes.mp hmu
  have hnuValid := mem_cycleTypes.mp hnu
  ext a
  by_cases ha : a = 1
  · subst a
    have hmuOne : mu.count 1 = 0 := by
      apply Multiset.count_eq_zero.mpr
      intro hone
      have := hmuValid.2 1 hone
      omega
    have hnuOne : nu.count 1 = 0 := by
      apply Multiset.count_eq_zero.mpr
      intro hone
      have := hnuValid.2 1 hone
      omega
    rw [hmuOne, hnuOne]
  · have hcount := congrArg (Multiset.count a) heq
    simpa [completeCycleType, Multiset.count_replicate, ha, Ne.symm ha] using hcount

/-! ## The permutation event -/

/-- Predicate on Mathlib's nontrivial cycle type corresponding to exactly
`ell` total cycles, all lengths in `I`. -/
def IsRestrictedCycleType (n ell : ℕ) (I : Finset ℕ)
    (mu : Multiset ℕ) : Prop :=
  (completeCycleType n mu).card = ell ∧
    ∀ i ∈ completeCycleType n mu, i ∈ I

instance instDecidablePredIsRestrictedCycleType (n ell : ℕ) (I : Finset ℕ) :
    DecidablePred (IsRestrictedCycleType n ell I) := by
  intro mu
  unfold IsRestrictedCycleType
  infer_instance

theorem cycleTypeEventCount_isRestrictedCycleType_eq
    (n ell : ℕ) (I : Finset ℕ) :
    cycleTypeEventCount n (IsRestrictedCycleType n ell I) =
      restrictedCycleCount n ell I := by
  classical
  unfold cycleTypeEventCount restrictedCycleCount
  apply congrArg Finset.card
  ext sigma
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold IsRestrictedCycleType
  rw [completeCycleType_cycleType]

/-! The factor `1 / n` requires `n > 0`; the excluded boundary cases are
recorded explicitly here. -/

theorem fullCycleType_fin_zero (sigma : Equiv.Perm (Fin 0)) :
    fullCycleType sigma = 0 := by
  by_contra hne
  obtain ⟨i, hi⟩ := Multiset.exists_mem_of_ne_zero hne
  have hpos := one_le_of_mem_fullCycleType hi
  have hle := Multiset.le_sum_of_mem hi
  rw [sum_fullCycleType] at hle
  omega

@[simp]
theorem restrictedCycleCount_zero_zero (I : Finset ℕ) :
    restrictedCycleCount 0 0 I = 1 := by
  rw [restrictedCycleCount]
  have hfilter :
      (Finset.univ : Finset (Equiv.Perm (Fin 0))).filter
          (fun sigma ↦ (fullCycleType sigma).card = 0 ∧
            ∀ j ∈ fullCycleType sigma, j ∈ I) = Finset.univ := by
    ext sigma
    simp [fullCycleType_fin_zero sigma]
  rw [hfilter]
  simp

@[simp]
theorem restrictedCycleCount_zero_succ (I : Finset ℕ) (ell : ℕ) :
    restrictedCycleCount 0 (ell + 1) I = 0 := by
  rw [restrictedCycleCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro sigma hsigma
  rw [fullCycleType_fin_zero sigma]
  simp

@[simp]
theorem restrictedCycleCount_ell_zero {n : ℕ} (hn : 0 < n) (I : Finset ℕ) :
    restrictedCycleCount n 0 I = 0 := by
  rw [restrictedCycleCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro sigma hsigma
  rintro ⟨hcard, hI⟩
  have hzero : fullCycleType sigma = 0 := Multiset.card_eq_zero.mp hcard
  have hsum := sum_fullCycleType sigma
  rw [hzero] at hsum
  simp at hsum
  omega

/-- Exact Ford--Beker restricted-cycle estimate, normalized by `n!`. -/
theorem restrictedCycleCount_normalized_le
    (I : Finset ℕ) {n ell : ℕ} (hn : 0 < n) (hell : 0 < ell)
    (hI : ∀ i ∈ I, 0 < i) :
    (restrictedCycleCount n ell I : ℝ) / (n.factorial : ℝ) ≤
      (∑ i ∈ I, (i : ℝ)⁻¹) ^ (ell - 1) /
        ((n : ℝ) * ((ell - 1).factorial : ℝ)) := by
  classical
  let A := IsRestrictedCycleType n ell I
  let E := cycleTypeEventTypes n A
  let embedFull : ↑E → Sym ℕ ell := fun p ↦
    ⟨completeCycleType n p.val, by
      have hpE : p.val ∈ cycleTypeEventTypes n A := by
        simpa [E] using p.property
      have hp := mem_cycleTypeEventTypes.mp hpE
      have hpA : IsRestrictedCycleType n ell I p.val := by
        simpa [A] using hp.2
      exact hpA.1⟩
  have hembed_mem (p : ↑E) :
      embedFull p ∈ restrictedMultisetCycleTypes I n ell := by
    rw [mem_restrictedMultisetCycleTypes]
    have hpE : p.val ∈ cycleTypeEventTypes n A := by
      simpa [E] using p.property
    have hp := mem_cycleTypeEventTypes.mp hpE
    have hpA : IsRestrictedCycleType n ell I p.val := by
      simpa [A] using hp.2
    exact ⟨hpA.2, sum_completeCycleType_of_mem hp.1⟩
  have hembed_inj : Function.Injective embedFull := by
    intro p q heq
    apply Subtype.ext
    apply completeCycleType_injective_on_cycleTypes
    · have hpE : p.val ∈ cycleTypeEventTypes n A := by
        simpa [E] using p.property
      exact (mem_cycleTypeEventTypes (A := A)).mp hpE |>.1
    · have hqE : q.val ∈ cycleTypeEventTypes n A := by
        simpa [E] using q.property
      exact (mem_cycleTypeEventTypes (A := A)).mp hqE |>.1
    · simpa [embedFull] using congrArg Subtype.val heq
  have hprob :
      (restrictedCycleCount n ell I : ℝ) / (n.factorial : ℝ) =
        ∑ mu ∈ E, cycleWeightReal n mu := by
    rw [← cycleTypeEventCount_isRestrictedCycleType_eq n ell I]
    exact cycleTypeEventRealProbability_eq_sum_cycleWeightReal n A
  rw [hprob]
  calc
    ∑ mu ∈ E, cycleWeightReal n mu =
        ∑ p ∈ E.attach, cycleWeightReal n p.val := by
      exact (Finset.sum_attach E (fun mu ↦ cycleWeightReal n mu)).symm
    _ = ∑ p ∈ E.attach, multisetCycleWeight (embedFull p).1 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [multisetCycleWeight_completeCycleType_eq_cycleWeightReal]
      have hpE : p.val ∈ cycleTypeEventTypes n A := by
        simpa [E] using p.property
      exact (mem_cycleTypeEventTypes (A := A)).mp hpE |>.1
    _ = ∑ rho ∈ Finset.image embedFull E.attach,
        multisetCycleWeight rho.val := by
      symm
      apply Finset.sum_image
      intro p hp q hq hpq
      exact hembed_inj hpq
    _ ≤ ∑ rho ∈ restrictedMultisetCycleTypes I n ell,
        multisetCycleWeight rho.val := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro rho hrho
        rw [Finset.mem_image] at hrho
        obtain ⟨p, hp, rfl⟩ := hrho
        exact hembed_mem p
      · intro rho hrho hnot
        exact multisetCycleWeight_nonneg rho.val
    _ ≤ (∑ i ∈ I, (i : ℝ)⁻¹) ^ (ell - 1) /
        ((n : ℝ) * ((ell - 1).factorial : ℝ)) :=
      sum_restrictedMultisetCycleWeight_le I hn hell hI

/-! ## Orders dividing a fixed integer -/

/-- Specialization to permutations whose order divides `m`. -/
theorem cycleOrderDividesCount_normalized_le
    {n m ell : ℕ} (hn : 0 < n) (hm : m ≠ 0) (hell : 0 < ell) :
    (cycleOrderDividesCount n m ell : ℝ) / (n.factorial : ℝ) ≤
      divisorReciprocalSum m ^ (ell - 1) /
        ((n : ℝ) * ((ell - 1).factorial : ℝ)) := by
  rw [← restrictedCycleCount_divisors_eq_cycleOrderDividesCount hm]
  exact restrictedCycleCount_normalized_le m.divisors hn hell
    (fun i hi ↦ Nat.pos_of_mem_divisors hi)

/-- The same bound with the divisor harmonic sum written as `sigma(m)/m`. -/
theorem cycleOrderDividesCount_normalized_le_sigma
    {n m ell : ℕ} (hn : 0 < n) (hm : m ≠ 0) (hell : 0 < ell) :
    (cycleOrderDividesCount n m ell : ℝ) / (n.factorial : ℝ) ≤
      ((ArithmeticFunction.sigma 1 m : ℝ) / (m : ℝ)) ^ (ell - 1) /
        ((n : ℝ) * ((ell - 1).factorial : ℝ)) := by
  rw [← divisorReciprocalSum_eq_divisorSum_div m hm]
  exact cycleOrderDividesCount_normalized_le hn hm hell

end

end Erdos1161
