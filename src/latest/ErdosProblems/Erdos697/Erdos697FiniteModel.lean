import Mathlib
import Util.Density

/-!
# Finite periodic probability model for Erdős 697

Every predicate on `ZMod q` determines a periodic set of natural numbers.
This file proves that its natural density is exactly the normalized finite
cardinality.  It is the bridge between finite CRT counting and the density
appearing in Problem 697.
-/

open Filter Set
open scoped Topology BigOperators

namespace Erdos697.FiniteModel

noncomputable section

private theorem hasDensity_of_counting_error
    (S : Set ℕ) (c C : ℝ)
    (h : ∀ n, |((S ∩ Set.Iio n).ncard : ℝ) - c * n| ≤ C) :
    S.HasDensity c := by
  rw [Set.HasDensity]
  have hzero : Tendsto
      (fun n : ℕ => (((S ∩ Set.Iio n).ncard : ℝ) - c * n) / n)
      atTop (𝓝 0) := by
    exact squeeze_zero_norm
      (fun n => by
        simpa [abs_div] using
          div_le_div_of_nonneg_right (h n) (Nat.cast_nonneg n))
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  simpa only [zero_add] using (hzero.add_const c).congr' (by
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
    have hIio : (Set.Iio n).ncard = n := by simp
    rw [hIio]
    field_simp
    ring)

private theorem hasDensity_union_of_disjoint
    {S T : Set ℕ} {s t : ℝ} (hS : S.HasDensity s)
    (hT : T.HasDensity t) (hdisj : Disjoint S T) :
    (S ∪ T).HasDensity (s + t) := by
  rw [Set.HasDensity] at hS hT ⊢
  apply (hS.add hT).congr'
  filter_upwards with n
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
  have hST : Disjoint (S ∩ Set.Iio n) (T ∩ Set.Iio n) :=
    hdisj.mono inter_subset_left inter_subset_left
  rw [show (S ∪ T) ∩ Set.Iio n =
      (S ∩ Set.Iio n) ∪ (T ∩ Set.Iio n) by ext; aesop]
  rw [Set.ncard_union_eq hST]
  push_cast
  ring

private def residueClass (q : ℕ) (a : ZMod q) : Set ℕ :=
  {n | (n : ZMod q) = a}

private theorem residueClass_pairwise_disjoint (q : ℕ) :
    Set.Pairwise (Set.univ : Set (ZMod q))
      (fun a b => Disjoint (residueClass q a) (residueClass q b)) := by
  intro a _ b _ hab
  rw [Set.disjoint_left]
  intro n hna hnb
  exact hab (hna.symm.trans hnb)

private theorem residueClass_hasDensity {q : ℕ} (hq : 0 < q)
    (a : ZMod q) :
    (residueClass q a).HasDensity (1 / (q : ℝ)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  apply hasDensity_of_counting_error _ _ 2
  intro n
  have hcard : (residueClass q a ∩ Set.Iio n).ncard =
      n.count (fun k => k ≡ a.val [MOD q]) := by
    rw [Nat.count_eq_card_filter_range]
    rw [show residueClass q a ∩ Set.Iio n =
        ↑((Finset.range n).filter (fun k => k ≡ a.val [MOD q])) by
      ext k
      simp only [Set.mem_inter_iff, residueClass, Set.mem_setOf_eq,
        Set.mem_Iio, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hk, hkn⟩
        rw [← ZMod.natCast_zmod_val a] at hk
        exact ⟨hkn, (ZMod.natCast_eq_natCast_iff k a.val q).mp hk⟩
      · rintro ⟨hkn, hk⟩
        have hk' := (ZMod.natCast_eq_natCast_iff k a.val q).mpr hk
        rw [ZMod.natCast_zmod_val a] at hk'
        exact ⟨hk', hkn⟩]
    exact Set.ncard_coe_finset _
  rw [hcard, Nat.count_modEq_card n hq a.val]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdivle : (((n / q : ℕ) : ℝ)) ≤ (n : ℝ) / q := Nat.cast_div_le
  have hnDecomp : (n : ℝ) = (q : ℝ) * (n / q : ℕ) + (n % q : ℕ) := by
    exact_mod_cast (Nat.div_add_mod n q).symm
  have hrem : ((n % q : ℕ) : ℝ) / q < 1 := by
    apply (div_lt_one hqR).2
    exact_mod_cast Nat.mod_lt n hq
  have hdivlt : (n : ℝ) / q < (n / q : ℕ) + 1 := by
    calc
      (n : ℝ) / q =
          ((n / q : ℕ) : ℝ) + ((n % q : ℕ) : ℝ) / q := by
            rw [hnDecomp]
            field_simp
      _ < (n / q : ℕ) + 1 := by linarith
  have hscale : (1 / (q : ℝ)) * n = (n : ℝ) / q := by ring
  rw [hscale]
  split_ifs with hrem
  · push_cast
    rw [abs_le]
    constructor <;> nlinarith
  · push_cast
    rw [abs_le]
    constructor <;> nlinarith

private def unionResidueClasses (q : ℕ) (R : Finset (ZMod q)) : Set ℕ :=
  {n | (n : ZMod q) ∈ R}

private theorem unionResidueClasses_insert {q : ℕ} {a : ZMod q}
    {R : Finset (ZMod q)} (ha : a ∉ R) :
    unionResidueClasses q (insert a R) =
      residueClass q a ∪ unionResidueClasses q R := by
  ext n
  simp [unionResidueClasses, residueClass]

private theorem residueClass_disjoint_unionResidueClasses {q : ℕ}
    {a : ZMod q} {R : Finset (ZMod q)} (ha : a ∉ R) :
    Disjoint (residueClass q a) (unionResidueClasses q R) := by
  rw [Set.disjoint_left]
  intro n hna hnR
  change (n : ZMod q) = a at hna
  change (n : ZMod q) ∈ R at hnR
  rw [hna] at hnR
  exact ha hnR

theorem unionResidueClasses_hasDensity {q : ℕ} (hq : 0 < q)
    (R : Finset (ZMod q)) :
    (unionResidueClasses q R).HasDensity ((R.card : ℝ) / q) := by
  classical
  induction R using Finset.induction with
  | empty =>
      simp [unionResidueClasses, Set.HasDensity, Set.partialDensity]
  | @insert a R ha ih =>
      rw [unionResidueClasses_insert ha]
      have h := hasDensity_union_of_disjoint
        (residueClass_hasDensity hq a) ih
        (residueClass_disjoint_unionResidueClasses ha)
      convert h using 1
      simp only [Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      field_simp
      ring

/-- A predicate on `ZMod q`, sampled by natural numbers, has density equal
to its normalized finite counting probability. -/
theorem zmodPredicate_hasDensity {q : ℕ} [NeZero q] (hq : 0 < q)
    (A : ZMod q → Prop) [DecidablePred A] :
    {n : ℕ | A (n : ZMod q)}.HasDensity
      (((Finset.univ.filter A).card : ℝ) / q) := by
  simpa [unionResidueClasses] using
    unionResidueClasses_hasDensity hq (Finset.univ.filter A)

end

end Erdos697.FiniteModel
