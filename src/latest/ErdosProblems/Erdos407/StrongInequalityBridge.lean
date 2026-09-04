/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos407.PadicSubspaceDefs
import ErdosProblems.Erdos407.SubspaceApplication

/-!
# The strong-inequality bridge for the `{2,3}` unit equation

This file supplies the elementary arithmetic and finite reindexing which
connect the projective `{2,3}`-unit points of `SubspaceApplication` to the
strong product inequality used by `PadicSubspace`.
-/

namespace Erdos407.StrongInequalityBridge

open scoped BigOperators
open Erdos407

namespace SInteger23

/-- A rational number integral away from `2` and `3`. -/
def IsSInteger (q : ℚ) : Prop :=
  ∃ z : ℤ, ∃ a b : ℕ,
    q = (z : ℚ) / (((2 : ℕ) ^ a * (3 : ℕ) ^ b : ℕ) : ℚ)

theorem zero : IsSInteger 0 := by
  exact ⟨0, 0, 0, by norm_num⟩

theorem one : IsSInteger 1 := by
  exact ⟨1, 0, 0, by norm_num⟩

theorem add {q r : ℚ} (hq : IsSInteger q) (hr : IsSInteger r) :
    IsSInteger (q + r) := by
  rcases hq with ⟨z, a, b, rfl⟩
  rcases hr with ⟨w, c, d, rfl⟩
  refine ⟨z * ((2 : ℤ) ^ c * (3 : ℤ) ^ d) +
      w * ((2 : ℤ) ^ a * (3 : ℤ) ^ b), a + c, b + d, ?_⟩
  push_cast
  rw [pow_add, pow_add]
  field_simp

theorem neg {q : ℚ} (hq : IsSInteger q) : IsSInteger (-q) := by
  rcases hq with ⟨z, a, b, rfl⟩
  exact ⟨-z, a, b, by push_cast; ring⟩

theorem intMul (m : ℤ) {q : ℚ} (hq : IsSInteger q) :
    IsSInteger ((m : ℚ) * q) := by
  rcases hq with ⟨z, a, b, rfl⟩
  exact ⟨m * z, a, b, by push_cast; ring⟩

theorem sum {ι : Type*} [Fintype ι] (q : ι → ℚ)
    (hq : ∀ i, IsSInteger (q i)) : IsSInteger (∑ i, q i) := by
  classical
  simpa using Finset.sum_induction (s := Finset.univ) q IsSInteger
    (fun _ _ => add) zero (fun i _ => hq i)

theorem of_unit {q : ℚ} (hq : PadicProduct.IsUnit23 q) : IsSInteger q := by
  rcases hq with ⟨a, b, hab | hab⟩
  · let ap : ℕ := a.toNat
    let an : ℕ := (-a).toNat
    let bp : ℕ := b.toNat
    let bn : ℕ := (-b).toNat
    refine ⟨((2 : ℤ) ^ ap * (3 : ℤ) ^ bp), an, bn, ?_⟩
    rw [hab]
    push_cast
    have ha : a = (ap : ℤ) - (an : ℤ) := by
      simpa [ap, an] using (Int.toNat_sub_toNat_neg a).symm
    have hb : b = (bp : ℤ) - (bn : ℤ) := by
      simpa [bp, bn] using (Int.toNat_sub_toNat_neg b).symm
    rw [ha, hb, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0),
      zpow_sub₀ (by norm_num : (3 : ℚ) ≠ 0)]
    simp only [zpow_natCast]
    field_simp
  · let ap : ℕ := a.toNat
    let an : ℕ := (-a).toNat
    let bp : ℕ := b.toNat
    let bn : ℕ := (-b).toNat
    refine ⟨-((2 : ℤ) ^ ap * (3 : ℤ) ^ bp), an, bn, ?_⟩
    rw [hab]
    push_cast
    have ha : a = (ap : ℤ) - (an : ℤ) := by
      simpa [ap, an] using (Int.toNat_sub_toNat_neg a).symm
    have hb : b = (bp : ℤ) - (bn : ℤ) := by
      simpa [bp, bn] using (Int.toNat_sub_toNat_neg b).symm
    rw [ha, hb, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0),
      zpow_sub₀ (by norm_num : (3 : ℚ) ≠ 0)]
    simp only [zpow_natCast]
    field_simp

/-- A primitive common scale for `{2,3}`-unit coordinates is integral away
from `2` and `3`; this is the outside-prime cancellation in the bridge. -/
theorem scale_isSInteger {ι : Type*} [Fintype ι]
    {z : ι → ℤ} (hz : Primitive.IsPrimitive z) {q : ℚ}
    (hcoord : ∀ i, PadicProduct.IsUnit23 (q * (z i : ℚ))) :
    IsSInteger q := by
  rcases hz with ⟨u, hu⟩
  have hsum : q = ∑ i, (u i : ℚ) * (q * (z i : ℚ)) := by
    calc
      q = q * (∑ i, (u i : ℚ) * (z i : ℚ)) := by
        rw [show (∑ i, (u i : ℚ) * (z i : ℚ)) = 1 by exact_mod_cast hu, mul_one]
      _ = ∑ i, (u i : ℚ) * (q * (z i : ℚ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  rw [hsum]
  apply sum
  intro i
  exact intMul (u i) (of_unit (hcoord i))

/-- Restricted product-formula inequality for a nonzero `{2,3}`-integer. -/
theorem one_le_normProduct23 {q : ℚ} (hq : IsSInteger q) (hq0 : q ≠ 0) :
    1 ≤ PadicProduct.normProduct23 q := by
  rcases hq with ⟨z, a, b, hz⟩
  let D : ℕ := 2 ^ a * 3 ^ b
  have hDpos : 0 < D := by positivity
  have hD0 : (D : ℚ) ≠ 0 := by positivity
  have hz0 : z ≠ 0 := by
    intro hz0
    apply hq0
    rw [hz, hz0]
    simp
  have hDunit : PadicProduct.IsUnit23 (D : ℚ) := by
    refine ⟨(a : ℤ), (b : ℤ), Or.inl ?_⟩
    simp [D, zpow_natCast]
  have hmul : q * (D : ℚ) = z := by
    rw [hz]
    change (z : ℚ) / (D : ℚ) * (D : ℚ) = (z : ℚ)
    field_simp
  have hprod := PadicSubspace.one_le_threePlaceProduct_int hz0
  rw [← hmul, PadicProduct.normProduct23_mul,
    hDunit.normProduct23_eq_one, mul_one] at hprod
  exact hprod

/-- For a primitive vector whose scaled coordinates are all `{2,3}`-units,
the common scale itself has exact three-place product one.  Primitivity first
removes every denominator away from `2,3` (the preceding S-integer lemma).
Then any nonzero integral coordinate has restricted product at least one,
while its product with the scale is a unit and hence has product exactly
one. -/
theorem scale_normProduct23_eq_one {ι : Type*} [Fintype ι]
    {z : ι → ℤ} (hz : Primitive.IsPrimitive z) {q : ℚ} (hq0 : q ≠ 0)
    (hcoord : ∀ i, PadicProduct.IsUnit23 (q * (z i : ℚ))) :
    PadicProduct.normProduct23 q = 1 := by
  have hqge : 1 ≤ PadicProduct.normProduct23 q :=
    one_le_normProduct23 (scale_isSInteger hz hcoord) hq0
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    exact hz.ne_zero (funext h)
  have hzge : 1 ≤ PadicProduct.normProduct23 (z i : ℚ) :=
    PadicSubspace.one_le_threePlaceProduct_int hi
  have hmul := (hcoord i).normProduct23_eq_one
  rw [PadicProduct.normProduct23_mul] at hmul
  nlinarith

end SInteger23

/-! ## Primitive and finite reindexing lemmas -/

theorem primitive_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) {z : ι → ℤ} (hz : Primitive.IsPrimitive z) :
    Primitive.IsPrimitive (fun i => z (e i)) := by
  rcases hz with ⟨u, hu⟩
  refine ⟨fun i => u (e i), ?_⟩
  simpa using (e.sum_comp (fun i => u i * z i)).trans hu

/-! ## Omitting one largest form at every place -/

open Erdos407.PadicSubspace
open Erdos407.SubspaceApplication

/-- An arbitrary enumeration of the `n` form labels left after one of the
`n+1` coordinate-and-weighted-sum labels has been removed. -/
noncomputable def omitEquiv {n : ℕ} (k : Option (Fin n)) :
    Fin n ≃ {j : Option (Fin n) // j ≠ k} :=
  Fintype.equivOfCardEq (by simp)

/-- The three local bases obtained by omitting the label `k v` at place `v`. -/
noncomputable def omittedFamily {n : ℕ} (a : Fin n → ℚ)
    (k : PadicSubspace.Place23 → Option (Fin n)) :
    PadicSubspace.Place23 → Fin n → PadicSubspace.RatLinearForm n :=
  fun v i => weightedForm a ((omitEquiv (k v)) i).1

theorem omittedFamily_nonsingular {n : ℕ} (a : Fin n → ℚ)
    (ha : ∀ i, a i ≠ 0) (k : PadicSubspace.Place23 → Option (Fin n)) :
    PadicSubspace.IsNonsingularFamily (omittedFamily a k) := by
  intro v
  exact (weightedForm_omit_linearIndependent_fin a ha (k v)).comp
    (omitEquiv (k v)) (omitEquiv (k v)).injective

/-- At a given place, choose a label on which the local norm of the form
value is maximal. -/
noncomputable def maximalFormIndex {n : ℕ} (a : Fin n → ℚ)
    (z : Fin n → ℤ) (v : PadicSubspace.Place23) : Option (Fin n) :=
  (Finset.exists_max_image (Finset.univ : Finset (Option (Fin n)))
    (fun j => PadicSubspace.placeNorm v
      (weightedForm a j (PadicSubspace.intCastVec z)))
    Finset.univ_nonempty).choose

theorem le_maximalFormIndex {n : ℕ} (a : Fin n → ℚ)
    (z : Fin n → ℤ) (v : PadicSubspace.Place23) (j : Option (Fin n)) :
    PadicSubspace.placeNorm v
        (weightedForm a j (PadicSubspace.intCastVec z)) ≤
      PadicSubspace.placeNorm v
        (weightedForm a (maximalFormIndex a z v)
          (PadicSubspace.intCastVec z)) := by
  classical
  exact (Finset.exists_max_image (Finset.univ : Finset (Option (Fin n)))
    (fun t => PadicSubspace.placeNorm v
      (weightedForm a t (PadicSubspace.intCastVec z)))
    Finset.univ_nonempty).choose_spec.2 j (Finset.mem_univ j)

private theorem prod_omitEquiv_mul {n : ℕ} (k : Option (Fin n))
    (f : Option (Fin n) → ℚ) :
    (∏ i : Fin n, f ((omitEquiv k i).1)) * f k = ∏ j, f j := by
  classical
  have hcomp : (∏ i : Fin n, f ((omitEquiv k i).1)) =
      ∏ j ∈ (Finset.univ.erase k : Finset (Option (Fin n))), f j := by
    apply Finset.prod_bij (fun i _ => (omitEquiv k i).1)
    · intro i _
      simp [(omitEquiv k i).2]
    · intro i₁ _ i₂ _ h
      exact (omitEquiv k).injective (Subtype.ext h)
    · intro j hj
      have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
      let t : {j : Option (Fin n) // j ≠ k} := ⟨j, hjk⟩
      refine ⟨(omitEquiv k).symm t, Finset.mem_univ _, ?_⟩
      simp [t]
    · intro i _
      rfl
  rw [hcomp]
  exact Finset.prod_erase_mul (Finset.univ : Finset (Option (Fin n))) f
    (Finset.mem_univ k)

/-- Multiplying the omitted local product by the three omitted maxima
recovers the full product of all `n+1` forms at all three places. -/
theorem localFormProduct_mul_omitted_eq_full {n : ℕ} (a : Fin n → ℚ)
    (z : Fin n → ℤ) (k : PadicSubspace.Place23 → Option (Fin n)) :
    PadicSubspace.localFormProduct (omittedFamily a k)
        (PadicSubspace.intCastVec z) *
        (∏ v, PadicSubspace.placeNorm v
          (weightedForm a (k v) (PadicSubspace.intCastVec z))) =
      fullFormProduct23 a (PadicSubspace.intCastVec z) := by
  classical
  rw [PadicSubspace.localFormProduct, ← Finset.prod_mul_distrib]
  calc
    (∏ v, (∏ i, PadicSubspace.placeNorm v
        ((omittedFamily a k v i) (PadicSubspace.intCastVec z))) *
      PadicSubspace.placeNorm v
        (weightedForm a (k v) (PadicSubspace.intCastVec z))) =
        ∏ v, ∏ j : Option (Fin n), PadicSubspace.placeNorm v
          (weightedForm a j (PadicSubspace.intCastVec z)) := by
      apply Finset.prod_congr rfl
      intro v _
      exact prod_omitEquiv_mul (k v)
        (fun j => PadicSubspace.placeNorm v
          (weightedForm a j (PadicSubspace.intCastVec z)))
    _ = ∏ j : Option (Fin n), ∏ v, PadicSubspace.placeNorm v
          (weightedForm a j (PadicSubspace.intCastVec z)) := by
      rw [Finset.prod_comm]
    _ = fullFormProduct23 a (PadicSubspace.intCastVec z) := by
      unfold fullFormProduct23
      apply Finset.prod_congr rfl
      intro j _
      exact PadicSubspace.prod_placeNorm_eq_threePlaceProduct _

private theorem boxHeight_le_archimedean_max {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℚ) (z : Fin n → ℤ) :
    (PadicSubspace.boxHeight z : ℚ) ≤
      PadicSubspace.placeNorm PadicSubspace.Place23.infinite
        (weightedForm a (maximalFormIndex a z PadicSubspace.Place23.infinite)
          (PadicSubspace.intCastVec z)) := by
  classical
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    exact Finset.univ_nonempty
  obtain ⟨i, _hi, himax⟩ :=
    Finset.exists_mem_eq_sup' hne (fun i : Fin n => (z i).natAbs)
  have hbox : PadicSubspace.boxHeight z = (z i).natAbs := by
    unfold PadicSubspace.boxHeight
    rw [← Finset.sup'_eq_sup hne]
    exact himax
  have hle := le_maximalFormIndex a z PadicSubspace.Place23.infinite (some i)
  simpa [hbox, PadicSubspace.placeNorm_infinite,
    SubspaceApplication.weightedForm_some_apply] using hle

private theorem one_le_two_adic_max {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℚ) (z : Fin n → ℤ) (hz : PadicProduct.IsPrimitive z) :
    1 ≤ PadicSubspace.placeNorm PadicSubspace.Place23.two
      (weightedForm a (maximalFormIndex a z PadicSubspace.Place23.two)
        (PadicSubspace.intCastVec z)) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨i, hi⟩ := hz.exists_not_dvd (p := 2) (by norm_num)
  have hnorm : padicNorm 2 (z i : ℚ) = 1 :=
    (padicNorm.int_eq_one_iff (p := 2) (z i)).mpr hi
  have hle := le_maximalFormIndex a z PadicSubspace.Place23.two (some i)
  simpa [PadicSubspace.placeNorm_two,
    SubspaceApplication.weightedForm_some_apply, hnorm] using hle

private theorem one_le_three_adic_max {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℚ) (z : Fin n → ℤ) (hz : PadicProduct.IsPrimitive z) :
    1 ≤ PadicSubspace.placeNorm PadicSubspace.Place23.three
      (weightedForm a (maximalFormIndex a z PadicSubspace.Place23.three)
        (PadicSubspace.intCastVec z)) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨i, hi⟩ := hz.exists_not_dvd (p := 3) (by norm_num)
  have hnorm : padicNorm 3 (z i : ℚ) = 1 :=
    (padicNorm.int_eq_one_iff (p := 3) (z i)).mpr hi
  have hle := le_maximalFormIndex a z PadicSubspace.Place23.three (some i)
  simpa [PadicSubspace.placeNorm_three,
    SubspaceApplication.weightedForm_some_apply, hnorm] using hle

/-- The product of the three omitted maxima dominates the integral box
height.  At the Archimedean place this is the largest coordinate; at `2`
and `3`, primitivity supplies a coordinate of local norm one. -/
theorem boxHeight_le_omittedProduct {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℚ) (z : Fin n → ℤ) (hz : PadicProduct.IsPrimitive z) :
    (PadicSubspace.boxHeight z : ℚ) ≤
      ∏ v, PadicSubspace.placeNorm v
        (weightedForm a (maximalFormIndex a z v)
          (PadicSubspace.intCastVec z)) := by
  let M : PadicSubspace.Place23 → ℚ := fun v =>
    PadicSubspace.placeNorm v
      (weightedForm a (maximalFormIndex a z v)
        (PadicSubspace.intCastVec z))
  have hInf : (PadicSubspace.boxHeight z : ℚ) ≤ M PadicSubspace.Place23.infinite :=
    boxHeight_le_archimedean_max hn a z
  have h2 : 1 ≤ M PadicSubspace.Place23.two := one_le_two_adic_max hn a z hz
  have h3 : 1 ≤ M PadicSubspace.Place23.three := one_le_three_adic_max hn a z hz
  have hMInf : 0 ≤ M PadicSubspace.Place23.infinite :=
    PadicSubspace.placeNorm_nonneg _ _
  have hM2 : 0 ≤ M PadicSubspace.Place23.two :=
    PadicSubspace.placeNorm_nonneg _ _
  have hchain : (PadicSubspace.boxHeight z : ℚ) ≤
      M PadicSubspace.Place23.infinite * M PadicSubspace.Place23.two *
        M PadicSubspace.Place23.three := by
    calc
      (PadicSubspace.boxHeight z : ℚ) ≤ M PadicSubspace.Place23.infinite := hInf
      _ = M PadicSubspace.Place23.infinite * 1 * 1 := by ring
      _ ≤ M PadicSubspace.Place23.infinite * M PadicSubspace.Place23.two * 1 := by
        gcongr
      _ ≤ M PadicSubspace.Place23.infinite * M PadicSubspace.Place23.two *
          M PadicSubspace.Place23.three := by
        gcongr
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.prod_univ_zero, mul_one]
  change (PadicSubspace.boxHeight z : ℚ) ≤
    M PadicSubspace.Place23.infinite *
      (M PadicSubspace.Place23.two * M PadicSubspace.Place23.three)
  calc
    (PadicSubspace.boxHeight z : ℚ) ≤
        M PadicSubspace.Place23.infinite * M PadicSubspace.Place23.two *
          M PadicSubspace.Place23.three := hchain
    _ = M PadicSubspace.Place23.infinite *
          (M PadicSubspace.Place23.two * M PadicSubspace.Place23.three) := by ring

private theorem fullFormProduct23_nonneg {n : ℕ} (a : Fin n → ℚ)
    (x : Fin n → ℚ) : 0 ≤ fullFormProduct23 a x := by
  unfold fullFormProduct23
  apply Finset.prod_nonneg
  intro j _
  unfold PadicProduct.normProduct23 PadicProduct.archNorm
  exact mul_nonneg
    (mul_nonneg (abs_nonneg _) (padicNorm.nonneg _)) (padicNorm.nonneg _)

/-- The common scale in `IsThreePlaceUnitPoint` has restricted norm product
at least one, so the exact scaled full-product identity bounds the unscaled
full form product by one. -/
theorem fullFormProduct23_le_one_of_unitPoint {n : ℕ} (a : Fin n → ℚ)
    (z : Fin n → ℤ) (hz : IsThreePlaceUnitPoint a z) :
    fullFormProduct23 a (PadicSubspace.intCastVec z) ≤ 1 := by
  rcases hz.2 with ⟨q, hq0, hcoord, hsum⟩
  have hqnorm : PadicProduct.normProduct23 q = 1 :=
    SInteger23.scale_normProduct23_eq_one hz.1 hq0 hcoord
  have hid : PadicProduct.normProduct23 q ^ (n + 1) *
      fullFormProduct23 a (PadicSubspace.intCastVec z) = 1 := by
    have hscaled : fullFormProduct23 a
        (q • PadicSubspace.intCastVec z) = 1 := by
      unfold fullFormProduct23
      apply Finset.prod_eq_one
      intro j _
      cases j with
      | none =>
          simpa [weightedForm_none_apply, Finset.mul_sum] using
            hsum.normProduct23_eq_one
      | some i =>
          simpa using (hcoord i).normProduct23_eq_one
    calc
      PadicProduct.normProduct23 q ^ (n + 1) *
          fullFormProduct23 a (PadicSubspace.intCastVec z) =
          fullFormProduct23 a (q • PadicSubspace.intCastVec z) := by
        simpa using
          (fullFormProduct23_smul a q (PadicSubspace.intCastVec z)).symm
      _ = 1 := hscaled
  apply le_of_eq
  calc
    fullFormProduct23 a (PadicSubspace.intCastVec z) =
        PadicProduct.normProduct23 q ^ (n + 1) *
          fullFormProduct23 a (PadicSubspace.intCastVec z) := by
      rw [hqnorm]
      norm_num
    _ = 1 := hid

/-- Placewise omission of a largest form turns every primitive three-place
unit point into a solution of the fixed-exponent strong inequality. -/
theorem satisfiesStrongInequality_maximal {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℚ) (z : Fin n → ℤ) (hz : IsThreePlaceUnitPoint a z) :
    PadicSubspace.SatisfiesStrongInequality
      (omittedFamily a (maximalFormIndex a z)) z := by
  let L := omittedFamily a (maximalFormIndex a z)
  let M : ℚ := ∏ v, PadicSubspace.placeNorm v
    (weightedForm a (maximalFormIndex a z v) (PadicSubspace.intCastVec z))
  have hlocal0 : 0 ≤ PadicSubspace.localFormProduct L
      (PadicSubspace.intCastVec z) :=
    PadicSubspace.localFormProduct_nonneg _ _
  have hheight : (PadicSubspace.boxHeight z : ℚ) ≤ M :=
    boxHeight_le_omittedProduct hn a z
      (SubspaceApplication.isPadicPrimitive_of_isPrimitive hz.1)
  have hfull : fullFormProduct23 a (PadicSubspace.intCastVec z) ≤ 1 :=
    fullFormProduct23_le_one_of_unitPoint a z hz
  unfold PadicSubspace.SatisfiesStrongInequality
  change PadicSubspace.localFormProduct L (PadicSubspace.intCastVec z) *
    (PadicSubspace.boxHeight z : ℚ) ≤ 1
  calc
    PadicSubspace.localFormProduct L (PadicSubspace.intCastVec z) *
        (PadicSubspace.boxHeight z : ℚ) ≤
      PadicSubspace.localFormProduct L (PadicSubspace.intCastVec z) * M :=
        mul_le_mul_of_nonneg_left hheight hlocal0
    _ = fullFormProduct23 a (PadicSubspace.intCastVec z) := by
      exact localFormProduct_mul_omitted_eq_full a z (maximalFormIndex a z)
    _ ≤ 1 := hfull

/-- The complete membership statement used by the finite-union argument. -/
theorem unitPoint_mem_primitiveStrongSolutions_maximal {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℚ) (z : Fin n → ℤ) (hz : IsThreePlaceUnitPoint a z) :
    z ∈ PadicSubspace.primitiveStrongSolutions
      (omittedFamily a (maximalFormIndex a z)) := by
  exact ⟨SubspaceApplication.isPadicPrimitive_of_isPrimitive hz.1,
    hz.1.ne_zero, satisfiesStrongInequality_maximal hn a z hz⟩

/-! ## Finite union over the possible omitted labels -/

/-- If the strong Subspace-Theorem conclusion is known for each of the
finitely many placewise omission patterns, then all three-place unit points
in `Fin n` are covered by finitely many rational hyperplanes. -/
theorem finiteCover_unitPoints_fin_of_strongCovers {n : ℕ} (hn : 2 ≤ n)
    (a : Fin n → ℚ) (ha : ∀ i, a i ≠ 0)
    (hcover : ∀ k : PadicSubspace.Place23 → Option (Fin n),
      PadicSubspace.HasFiniteHyperplaneCover
        (PadicSubspace.primitiveStrongSolutions (omittedFamily a k))) :
    ∃ B : Finset (Fin n → ℚ),
      (∀ b ∈ B, b ≠ 0) ∧
      ∀ z : Fin n → ℤ, IsThreePlaceUnitPoint a z →
        ∃ b ∈ B, ∑ i, b i * (z i : ℚ) = 0 := by
  classical
  choose B hBne hBcover using hcover
  let Ball : Finset (Fin n → ℚ) := Finset.univ.biUnion B
  refine ⟨Ball, ?_, ?_⟩
  · intro b hb
    simp only [Ball, Finset.mem_biUnion, Finset.mem_univ, true_and] at hb
    obtain ⟨k, hbk⟩ := hb
    exact hBne k b hbk
  · intro z hz
    let k : PadicSubspace.Place23 → Option (Fin n) := maximalFormIndex a z
    have hzmem : z ∈ PadicSubspace.primitiveStrongSolutions
        (omittedFamily a k) := by
      exact unitPoint_mem_primitiveStrongSolutions_maximal (by omega) a z hz
    obtain ⟨b, hbB, hbzero⟩ := hBcover k z hzmem
    refine ⟨b, ?_, ?_⟩
    · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hbB⟩
    · exact hbzero

/-- The dimension-bounded strong Subspace-Theorem conclusion implies the
finite-cover statement in standard `Fin n` coordinates. -/
theorem finiteCover_unitPoints_fin_of_strongTheorem
    (hStrong : ∀ {n : ℕ}, 2 ≤ n → n ≤ 5 →
      ∀ (L : PadicSubspace.Place23 → Fin n → PadicSubspace.RatLinearForm n),
        PadicSubspace.IsNonsingularFamily L →
          PadicSubspace.HasFiniteHyperplaneCover
            (PadicSubspace.primitiveStrongSolutions L))
    {n : ℕ} (hn : 2 ≤ n) (hn5 : n ≤ 5)
    (a : Fin n → ℚ) (ha : ∀ i, a i ≠ 0) :
    ∃ B : Finset (Fin n → ℚ),
      (∀ b ∈ B, b ≠ 0) ∧
      ∀ z : Fin n → ℤ, IsThreePlaceUnitPoint a z →
        ∃ b ∈ B, ∑ i, b i * (z i : ℚ) = 0 := by
  apply finiteCover_unitPoints_fin_of_strongCovers hn a ha
  intro k
  exact hStrong hn hn5 (omittedFamily a k)
    (omittedFamily_nonsingular a ha k)

/-- Reindex a three-place unit point along a finite equivalence. -/
theorem isThreePlaceUnitPoint_reindex {ι κ : Type*}
    [Fintype ι] [Fintype κ] (e : κ ≃ ι) (a : ι → ℚ) (z : ι → ℤ)
    (hz : IsThreePlaceUnitPoint a z) :
    IsThreePlaceUnitPoint (fun i => a (e i)) (fun i => z (e i)) := by
  rcases hz with ⟨hzprim, q, hq, hcoord, hsum⟩
  refine ⟨primitive_reindex e hzprim, q, hq, ?_, ?_⟩
  · intro i
    exact hcoord (e i)
  · have heq : (∑ i : κ, a (e i) * (z (e i) : ℚ)) =
        ∑ j : ι, a j * (z j : ℚ) :=
      e.sum_comp (fun j => a j * (z j : ℚ))
    rw [heq]
    exact hsum

/-- A finite hyperplane cover in `Fin (card ι)` coordinates transports
back to the original finite index type. -/
theorem transport_fin_cover {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Fin (Fintype.card ι) ≃ ι) (a : ι → ℚ)
    (hfin : ∃ B : Finset (Fin (Fintype.card ι) → ℚ),
      (∀ b ∈ B, b ≠ 0) ∧
      ∀ z : Fin (Fintype.card ι) → ℤ,
        IsThreePlaceUnitPoint (fun i => a (e i)) z →
          ∃ b ∈ B, ∑ i, b i * (z i : ℚ) = 0) :
    ∃ B : Finset (ι → ℚ),
      (∀ b ∈ B, b ≠ 0) ∧
      ∀ z : ι → ℤ, IsThreePlaceUnitPoint a z →
        ∃ b ∈ B, ∑ i, b i * (z i : ℚ) = 0 := by
  classical
  obtain ⟨Bfin, hBne, hBcover⟩ := hfin
  let pull : (Fin (Fintype.card ι) → ℚ) → (ι → ℚ) :=
    fun b j => b (e.symm j)
  let B : Finset (ι → ℚ) := Bfin.image pull
  refine ⟨B, ?_, ?_⟩
  · intro c hc
    obtain ⟨b, hbB, rfl⟩ := Finset.mem_image.mp hc
    have hb0 := hBne b hbB
    intro hpull
    apply hb0
    funext i
    have hi := congrFun hpull (e i)
    simpa [pull] using hi
  · intro z hz
    let zfin : Fin (Fintype.card ι) → ℤ := fun i => z (e i)
    have hzfin : IsThreePlaceUnitPoint (fun i => a (e i)) zfin :=
      isThreePlaceUnitPoint_reindex e a z hz
    obtain ⟨b, hbB, hbzero⟩ := hBcover zfin hzfin
    refine ⟨pull b, Finset.mem_image.mpr ⟨b, hbB, rfl⟩, ?_⟩
    calc
      (∑ j : ι, pull b j * (z j : ℚ)) =
          ∑ i : Fin (Fintype.card ι),
            pull b (e i) * (z (e i) : ℚ) := by
              symm
              exact e.sum_comp (fun j => pull b j * (z j : ℚ))
      _ = ∑ i : Fin (Fintype.card ι), b i * (zfin i : ℚ) := by
            apply Finset.sum_congr rfl
            intro i _
            simp [pull, zfin]
      _ = 0 := hbzero

/-- Abstract endpoint form: a strong finite-cover theorem in dimensions at
most five yields exactly the bounded specialized p-adic Subspace-Theorem
statement consumed by the unit-equation induction. -/
theorem specializedPadicSubspaceFiniteCoverUpTo_five_of_strongTheorem
    (hStrong : ∀ {n : ℕ}, 2 ≤ n → n ≤ 5 →
      ∀ (L : PadicSubspace.Place23 → Fin n → PadicSubspace.RatLinearForm n),
        PadicSubspace.IsNonsingularFamily L →
          PadicSubspace.HasFiniteHyperplaneCover
            (PadicSubspace.primitiveStrongSolutions L)) :
    SubspaceApplication.SpecializedPadicSubspaceFiniteCoverUpTo 5 := by
  intro ι _ _ hn hn5 a ha
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  apply transport_fin_cover e a
  exact finiteCover_unitPoints_fin_of_strongTheorem hStrong hn hn5
    (fun i => a (e i)) (fun i => ha (e i))

#print axioms specializedPadicSubspaceFiniteCoverUpTo_five_of_strongTheorem

end Erdos407.StrongInequalityBridge
