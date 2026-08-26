import ErdosProblems.Erdos394.CosetGap

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Successor gaps in a finite subset of a discrete circle

This file formalizes the elementary telescoping identity underlying the
coset-gap argument.
-/

open Nat Finset BigOperators

namespace Erdos394

/-- Clockwise distance from `a` to `b` on a circle of circumference `q`, with
zero distance represented by a full turn.  It is intended for `a,b<q`. -/
def circleDistance (q a b : ℕ) : ℕ :=
  if a < b then b - a else q + b - a

/-- The next element of a nonempty finite set in cyclic order. -/
noncomputable def cyclicSucc (s : Finset ℕ) (hs : s.Nonempty) (a : s) : s :=
  if h : (s.filter (fun b ↦ a.1 < b)).Nonempty then
    ⟨(s.filter (fun b ↦ a.1 < b)).min' h,
      (Finset.mem_filter.mp ((s.filter (fun b ↦ a.1 < b)).min'_mem h)).1⟩
  else
    ⟨s.min' hs, s.min'_mem hs⟩

/-- There is an element of `s` strictly above `a` exactly when `a` is not
its maximum. -/
theorem filter_above_nonempty_iff_ne_max (s : Finset ℕ) (hs : s.Nonempty)
    (a : s) :
    (s.filter (fun b ↦ a.1 < b)).Nonempty ↔ a.1 ≠ s.max' hs := by
  constructor
  · rintro ⟨b, hb⟩
    have hb' := Finset.mem_filter.mp hb
    have hble : b ≤ s.max' hs := Finset.le_max' s b hb'.1
    omega
  · intro hne
    have hale : a.1 ≤ s.max' hs := Finset.le_max' s a.1 a.2
    refine ⟨s.max' hs, Finset.mem_filter.mpr ⟨s.max'_mem hs, ?_⟩⟩
    omega

/-- Away from the maximum, cyclic successor is strictly larger. -/
theorem lt_cyclicSucc_of_ne_max (s : Finset ℕ) (hs : s.Nonempty) (a : s)
    (ha : a.1 ≠ s.max' hs) : a.1 < (cyclicSucc s hs a).1 := by
  have hnon : (s.filter (fun b ↦ a.1 < b)).Nonempty :=
    (filter_above_nonempty_iff_ne_max s hs a).2 ha
  rw [cyclicSucc, dif_pos hnon]
  exact (Finset.mem_filter.mp
    ((s.filter (fun b ↦ a.1 < b)).min'_mem hnon)).2

/-- The successor of the maximum is the minimum. -/
theorem cyclicSucc_of_eq_max (s : Finset ℕ) (hs : s.Nonempty) (a : s)
    (ha : a.1 = s.max' hs) : (cyclicSucc s hs a).1 = s.min' hs := by
  have hempty : ¬(s.filter (fun b ↦ a.1 < b)).Nonempty := by
    intro h
    exact (filter_above_nonempty_iff_ne_max s hs a).1 h ha
  rw [cyclicSucc, dif_neg hempty]

/-- If `b` lies above `a`, the cyclic successor of `a` is no larger than `b`. -/
theorem cyclicSucc_le_of_lt (s : Finset ℕ) (hs : s.Nonempty) (a : s)
    {b : ℕ} (hb : b ∈ s) (hab : a.1 < b) : (cyclicSucc s hs a).1 ≤ b := by
  have hnon : (s.filter (fun c ↦ a.1 < c)).Nonempty :=
    ⟨b, Finset.mem_filter.mpr ⟨hb, hab⟩⟩
  rw [cyclicSucc, dif_pos hnon]
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hb, hab⟩)

/-- Cyclic successor permutes a nonempty finite set. -/
theorem cyclicSucc_injective (s : Finset ℕ) (hs : s.Nonempty) :
    Function.Injective (cyclicSucc s hs) := by
  intro a b hab
  apply Subtype.ext
  by_contra hne
  have hlt_or_gt : a.1 < b.1 ∨ b.1 < a.1 := lt_or_gt_of_ne hne
  rcases hlt_or_gt with hlt | hlt
  · have hsa_le : (cyclicSucc s hs a).1 ≤ b.1 :=
      cyclicSucc_le_of_lt s hs a b.2 hlt
    by_cases hbmax : b.1 = s.max' hs
    · have hsb_le : (cyclicSucc s hs b).1 ≤ a.1 := by
        rw [cyclicSucc_of_eq_max s hs b hbmax]
        exact Finset.min'_le s a.1 a.2
      have hsa_gt : a.1 < (cyclicSucc s hs a).1 := by
        apply lt_cyclicSucc_of_ne_max s hs a
        have hamax : a.1 < s.max' hs := hbmax ▸ hlt
        omega
      have hv := congrArg Subtype.val hab
      omega
    · have hsb_gt : b.1 < (cyclicSucc s hs b).1 :=
        lt_cyclicSucc_of_ne_max s hs b hbmax
      have hv := congrArg Subtype.val hab
      omega
  · have hsb_le : (cyclicSucc s hs b).1 ≤ a.1 :=
      cyclicSucc_le_of_lt s hs b a.2 hlt
    by_cases hamax : a.1 = s.max' hs
    · have hsa_le : (cyclicSucc s hs a).1 ≤ b.1 := by
        rw [cyclicSucc_of_eq_max s hs a hamax]
        exact Finset.min'_le s b.1 b.2
      have hsb_gt : b.1 < (cyclicSucc s hs b).1 := by
        apply lt_cyclicSucc_of_ne_max s hs b
        have hbmax : b.1 < s.max' hs := hamax ▸ hlt
        omega
      have hv := congrArg Subtype.val hab
      omega
    · have hsa_gt : a.1 < (cyclicSucc s hs a).1 :=
        lt_cyclicSucc_of_ne_max s hs a hamax
      have hv := congrArg Subtype.val hab
      omega

/-- The least positive clockwise distance from `a` to an element of `s`. -/
noncomputable def leastCircleGap (q : ℕ) (s : Finset ℕ) (hs : s.Nonempty)
    (a : s) : ℕ :=
  (s.image (circleDistance q a.1)).min' (hs.image (circleDistance q a.1))

/-- Cyclic successor realizes the least clockwise distance. -/
theorem leastCircleGap_eq_succ (q : ℕ) (s : Finset ℕ) (hs : s.Nonempty)
    (hq : ∀ b ∈ s, b < q) (a : s) :
    leastCircleGap q s hs a = circleDistance q a.1 (cyclicSucc s hs a).1 := by
  apply Nat.le_antisymm
  · unfold leastCircleGap
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨(cyclicSucc s hs a).1,
      (cyclicSucc s hs a).2, rfl⟩
  · unfold leastCircleGap
    apply Finset.le_min'
    intro d hd
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
    have haq : a.1 < q := hq a.1 a.2
    have hbq : b < q := hq b hb
    have hsq : (cyclicSucc s hs a).1 < q :=
      hq (cyclicSucc s hs a).1 (cyclicSucc s hs a).2
    by_cases hab : a.1 < b
    · have hsle : (cyclicSucc s hs a).1 ≤ b :=
        cyclicSucc_le_of_lt s hs a hb hab
      have has : a.1 < (cyclicSucc s hs a).1 := by
        by_contra hnas
        have hamax : a.1 = s.max' hs := by
          by_contra hne
          exact hnas (lt_cyclicSucc_of_ne_max s hs a hne)
        have hsmin : (cyclicSucc s hs a).1 = s.min' hs :=
          cyclicSucc_of_eq_max s hs a hamax
        have hbmax : b ≤ s.max' hs := Finset.le_max' s b hb
        omega
      simp only [circleDistance, if_pos hab, if_pos has]
      omega
    · have hba : b ≤ a.1 := by omega
      by_cases has : a.1 < (cyclicSucc s hs a).1
      · simp only [circleDistance, if_neg hab, if_pos has]
        omega
      · have hamax : a.1 = s.max' hs := by
          by_contra hne
          exact has (lt_cyclicSucc_of_ne_max s hs a hne)
        have hsmin : (cyclicSucc s hs a).1 = s.min' hs :=
          cyclicSucc_of_eq_max s hs a hamax
        have hsle : (cyclicSucc s hs a).1 ≤ b := by
          rw [hsmin]
          exact Finset.min'_le s b hb
        simp only [circleDistance, if_neg hab, if_neg has]
        omega

/-- Cast form of the pointwise successor-gap identity.  Exactly the maximum
contributes one full turn. -/
theorem circleDistance_cyclicSucc_int (q : ℕ) (s : Finset ℕ)
    (hs : s.Nonempty) (hq : ∀ b ∈ s, b < q) (a : s) :
    (circleDistance q a.1 (cyclicSucc s hs a).1 : ℤ) =
      ((cyclicSucc s hs a).1 : ℤ) - (a.1 : ℤ) +
        if a.1 = s.max' hs then (q : ℤ) else 0 := by
  by_cases hamax : a.1 = s.max' hs
  · have hsucc : (cyclicSucc s hs a).1 = s.min' hs :=
      cyclicSucc_of_eq_max s hs a hamax
    have hsle : (cyclicSucc s hs a).1 ≤ a.1 := by
      rw [hsucc]
      exact Finset.min'_le s a.1 a.2
    have haq : a.1 < q := hq a.1 a.2
    simp only [circleDistance, if_neg (by omega : ¬a.1 < (cyclicSucc s hs a).1),
      if_pos hamax]
    rw [Nat.cast_sub (by omega : a.1 ≤ q + (cyclicSucc s hs a).1)]
    push_cast
    ring
  · have has : a.1 < (cyclicSucc s hs a).1 :=
      lt_cyclicSucc_of_ne_max s hs a hamax
    simp only [circleDistance, if_pos has, if_neg hamax]
    rw [Nat.cast_sub (Nat.le_of_lt has)]
    ring

/-- The successor gaps around any nonempty finite subset of `{0,...,q-1}`
sum to the circumference `q`. -/
theorem sum_leastCircleGap (q : ℕ) (s : Finset ℕ) (hs : s.Nonempty)
    (hq : ∀ b ∈ s, b < q) :
    ∑ a : s, leastCircleGap q s hs a = q := by
  have hinj := cyclicSucc_injective s hs
  have hbij : Function.Bijective (cyclicSucc s hs) :=
    hinj.bijective_of_finite
  have hperm :
      (∑ a : s, ((cyclicSucc s hs a).1 : ℤ)) = ∑ a : s, (a.1 : ℤ) :=
    hbij.sum_comp (fun a : s ↦ (a.1 : ℤ))
  let amax : s := ⟨s.max' hs, s.max'_mem hs⟩
  have hindicator :
      (∑ a : s, if a.1 = s.max' hs then (q : ℤ) else 0) = q := by
    rw [Fintype.sum_eq_single amax]
    · simp [amax]
    · intro a hne
      have ha : a.1 ≠ s.max' hs := by
        intro heq
        apply hne
        exact Subtype.ext heq
      simp [ha]
  apply Int.ofNat_inj.mp
  push_cast
  simp_rw [leastCircleGap_eq_succ q s hs hq,
    circleDistance_cyclicSucc_int q s hs hq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hperm, hindicator]
  simp

/-- Totalized version of `leastCircleGap`, convenient when summing over an
ambient type. -/
noncomputable def gapInSet (q : ℕ) (s : Finset ℕ) (x : ℕ) : ℕ :=
  if hs : s.Nonempty then
    if hx : x ∈ s then leastCircleGap q s hs ⟨x, hx⟩ else 0
  else 0

@[simp]
theorem gapInSet_of_mem (q : ℕ) (s : Finset ℕ) (hs : s.Nonempty)
    {x : ℕ} (hx : x ∈ s) :
    gapInSet q s x = leastCircleGap q s hs ⟨x, hx⟩ := by
  simp only [gapInSet, dif_pos hs, dif_pos hx]

/-- Finset form of the circle-gap sum. -/
theorem sum_gapInSet (q : ℕ) (s : Finset ℕ) (hs : s.Nonempty)
    (hq : ∀ b ∈ s, b < q) :
    ∑ b ∈ s, gapInSet q s b = q := by
  calc
    (∑ b ∈ s, gapInSet q s b) = ∑ a : s, gapInSet q s a.1 :=
      Finset.sum_subtype s (fun b ↦ by simp) (gapInSet q s)
    _ = ∑ a : s, leastCircleGap q s hs a := by
      apply Finset.sum_congr rfl
      intro a _
      exact gapInSet_of_mem q s hs a.2
    _ = q := sum_leastCircleGap q s hs hq

section AbstractCosets

variable {G : Type*} [Group G] [Fintype G]

/-- Natural coordinates occupied by the right coset `aH`. -/
noncomputable def cosetValues (v : G → ℕ) (H : Subgroup G) [Fintype H]
    (a : G) : Finset ℕ :=
  Finset.univ.image (fun h : H ↦ v (a * h.1))

theorem cosetValues_nonempty (v : G → ℕ) (H : Subgroup G) [Fintype H] (a : G) :
    (cosetValues v H a).Nonempty := by
  classical
  refine ⟨v (a * 1), Finset.mem_image.mpr ?_⟩
  exact ⟨⟨1, H.one_mem⟩, Finset.mem_univ _, rfl⟩

/-- Multiplying the base point by an element of `H` does not change its
right-coset coordinate set. -/
theorem cosetValues_mul (v : G → ℕ) (H : Subgroup G) [Fintype H]
    (a : G) (h : H) :
    cosetValues v H (a * h.1) = cosetValues v H a := by
  classical
  ext x
  simp only [cosetValues, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨⟨h.1 * k.1, H.mul_mem h.2 k.2⟩, ?_⟩
    simp only [mul_assoc]
  · rintro ⟨k, rfl⟩
    refine ⟨⟨h.1⁻¹ * k.1, H.mul_mem (H.inv_mem h.2) k.2⟩, ?_⟩
    simp only [mul_assoc, mul_inv_cancel_left]

/-- The clockwise gap at `a` inside the coordinate image of `aH`. -/
noncomputable def abstractCosetGap (q : ℕ) (v : G → ℕ)
    (H : Subgroup G) [Fintype H] (a : G) : ℕ :=
  gapInSet q (cosetValues v H a) (v a)

/-- The base point itself belongs to its coset coordinate set. -/
theorem self_mem_cosetValues (v : G → ℕ) (H : Subgroup G) [Fintype H]
    (a : G) :
    v a ∈ cosetValues v H a := by
  classical
  refine Finset.mem_image.mpr ⟨⟨1, H.one_mem⟩, Finset.mem_univ _, ?_⟩
  simp

/-- Coset gaps are compatible with changing the base point within the coset. -/
theorem abstractCosetGap_mul (q : ℕ) (v : G → ℕ) (H : Subgroup G)
    [Fintype H] (a : G) (h : H) :
    abstractCosetGap q v H (a * h.1) =
      gapInSet q (cosetValues v H a) (v (a * h.1)) := by
  unfold abstractCosetGap
  rw [cosetValues_mul v H a h]

/-- Coordinates on one coset are enumerated without repetition when `v` is
injective. -/
theorem cosetCoordinate_injective (v : G → ℕ) (hv : Function.Injective v)
    (H : Subgroup G) (a : G) :
    Function.Injective (fun h : H ↦ v (a * h.1)) := by
  intro h k heq
  apply Subtype.ext
  exact mul_left_cancel (hv heq)

/-- The gaps encountered while traversing any one right coset sum to `q`. -/
theorem sum_abstractCosetGap_mul (q : ℕ) (v : G → ℕ)
    (hv : Function.Injective v) (hq : ∀ a : G, v a < q)
    (H : Subgroup G) [Fintype H] (a : G) :
    ∑ h : H, abstractCosetGap q v H (a * h.1) = q := by
  classical
  let s := cosetValues v H a
  have hs : s.Nonempty := cosetValues_nonempty v H a
  have hsbound : ∀ b ∈ s, b < q := by
    intro b hb
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hb
    exact hq (a * h.1)
  have himage := Finset.sum_image
    (s := (Finset.univ : Finset H))
    (g := fun h : H ↦ v (a * h.1))
    (f := fun b : ℕ ↦ gapInSet q s b)
    (fun h _ k _ heq ↦ cosetCoordinate_injective v hv H a heq)
  simp_rw [abstractCosetGap_mul q v H a]
  change (∑ h : H, gapInSet q s (v (a * h.1))) = q
  rw [← himage]
  exact sum_gapInSet q s hs hsbound

/-- **Abstract coset-gap averaging identity.**  For any injective placement of
a finite group in a circle of circumference `q`, the sum of the least positive
clockwise gaps inside right cosets of `H`, multiplied by `|H|`, is exactly
`q |G|`. -/
theorem card_mul_sum_abstractCosetGap (q : ℕ) (v : G → ℕ)
    (hv : Function.Injective v) (hq : ∀ a : G, v a < q)
    (H : Subgroup G) [Fintype H] :
    Fintype.card H * (∑ a : G, abstractCosetGap q v H a) =
      q * Fintype.card G := by
  classical
  have hrow : ∀ a : G,
      (∑ h : H, abstractCosetGap q v H (a * h.1)) = q :=
    fun a ↦ sum_abstractCosetGap_mul q v hv hq H a
  calc
    Fintype.card H * (∑ a : G, abstractCosetGap q v H a)
        = ∑ h : H, ∑ a : G, abstractCosetGap q v H (a * h.1) := by
            calc
              Fintype.card H * (∑ a : G, abstractCosetGap q v H a)
                  = ∑ _h : H, ∑ a : G, abstractCosetGap q v H a := by simp
              _ = ∑ h : H, ∑ a : G, abstractCosetGap q v H (a * h.1) := by
                apply Finset.sum_congr rfl
                intro h _
                have hbij : Function.Bijective (fun a : G ↦ a * h.1) :=
                  (Equiv.mulRight h.1).bijective
                exact (hbij.sum_comp (abstractCosetGap q v H)).symm
    _ = ∑ a : G, ∑ h : H, abstractCosetGap q v H (a * h.1) := by
          rw [Finset.sum_comm]
    _ = ∑ _a : G, q := by
          apply Finset.sum_congr rfl
          intro a _
          exact hrow a
    _ = q * Fintype.card G := by simp [mul_comm]

end AbstractCosets

section ZModInvolutions

noncomputable local instance zmodUnitsFintype (q : ℕ) : Fintype (ZMod q)ˣ :=
  Fintype.ofFinite _

/-- The subgroup of units modulo `q` whose square is one. -/
def involutionSubgroup (q : ℕ) : Subgroup (ZMod q)ˣ where
  carrier := {u | u ^ 2 = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_pow, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [inv_pow, ha, inv_one]

noncomputable instance involutionSubgroupFintype (q : ℕ) :
    Fintype (involutionSubgroup q) := Fintype.ofFinite _

/-- Standard least-nonnegative-residue coordinate on units modulo `q`. -/
def unitResidue (q : ℕ) (a : (ZMod q)ˣ) : ℕ := (a.1 : ZMod q).val

/-- The abstract coset identity specialized to square roots of one modulo `q`.
This is the group-theoretic core of the exact restricted-root mean. -/
theorem involution_coset_gap_identity (q : ℕ) (hq : 0 < q) :
    Fintype.card (involutionSubgroup q) *
        (∑ a : (ZMod q)ˣ,
          abstractCosetGap q (unitResidue q) (involutionSubgroup q) a) =
      q * q.totient := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hv : Function.Injective (unitResidue q) := by
    intro a b hab
    apply Units.ext
    apply ZMod.val_injective q
    exact hab
  have hvlt : ∀ a : (ZMod q)ˣ, unitResidue q a < q := by
    intro a
    exact ZMod.val_lt (a.1 : ZMod q)
  rw [← ZMod.card_units_eq_totient q]
  exact card_mul_sum_abstractCosetGap q (unitResidue q) hv hvlt
    (involutionSubgroup q)

end ZModInvolutions

end Erdos394
