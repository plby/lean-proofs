import ErdosProblems.Erdos394.InvolutionCard

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Identifying involution coset gaps with restricted quadratic roots
-/

open Nat Finset

namespace Erdos394

noncomputable local instance zmodUnitsFintype'' (q : ℕ) : Fintype (ZMod q)ˣ :=
  Fintype.ofFinite _

/-- Least positive representative of a residue: zero is represented by `q`. -/
def positiveZModResidue (q : ℕ) (x : ZMod q) : ℕ :=
  if x = 0 then q else x.val

/-- Clockwise distance of standard residues is the least positive representative
of their difference. -/
theorem circleDistance_eq_positiveZModResidue_sub {q : ℕ} (hq : 0 < q)
    (a b : ZMod q) :
    circleDistance q a.val b.val = positiveZModResidue q (b - a) := by
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  by_cases hab : a.val < b.val
  · have hba : b ≠ a := by
      intro h
      subst b
      omega
    have hsub : b - a ≠ 0 := sub_ne_zero.mpr hba
    simp only [circleDistance, if_pos hab, positiveZModResidue, if_neg hsub]
    exact (ZMod.val_sub (Nat.le_of_lt hab)).symm
  · have hba_le : b.val ≤ a.val := by omega
    by_cases heq : b = a
    · subst b
      simp [circleDistance, positiveZModResidue]
    · have hvals : b.val < a.val := by
        have hneval : b.val ≠ a.val := by
          intro h
          exact heq (ZMod.val_injective q h)
        omega
      have hsub : b - a ≠ 0 := sub_ne_zero.mpr heq
      have hother : a - b ≠ 0 := sub_ne_zero.mpr (Ne.symm heq)
      have ha_lt : a.val < q := ZMod.val_lt a
      simp only [circleDistance, if_neg hab, positiveZModResidue, if_neg hsub]
      rw [show b - a = -(a - b) by abel, ZMod.neg_val, if_neg hother,
        ZMod.val_sub hba_le]
      omega

/-- Casting the least positive representative returns the original residue. -/
theorem natCast_positiveZModResidue {q : ℕ} (hq : 0 < q) (x : ZMod q) :
    (positiveZModResidue q x : ZMod q) = x := by
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  by_cases hx : x = 0
  · simp [positiveZModResidue, hx, ZMod.natCast_self]
  · simp only [positiveZModResidue, if_neg hx]
    exact ZMod.natCast_zmod_val x

/-- A representative in `[1,q]` is uniquely the least positive representative
of its residue. -/
theorem positiveZModResidue_eq_of_natCast_eq {q j : ℕ} (hq : 0 < q)
    (hjpos : 0 < j) (hjle : j ≤ q) (x : ZMod q) (hjx : (j : ZMod q) = x) :
    positiveZModResidue q x = j := by
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  by_cases hjq : j = q
  · subst j
    rw [← hjx, ZMod.natCast_self]
    simp [positiveZModResidue]
  · have hjlt : j < q := by omega
    have hjne : (j : ZMod q) ≠ 0 := by
      intro hz
      have hv := congrArg ZMod.val hz
      rw [ZMod.val_natCast_of_lt hjlt, ZMod.val_zero] at hv
      omega
    rw [← hjx]
    simp [positiveZModResidue, hjne, ZMod.val_natCast_of_lt hjlt]

/-- The least positive representative lies in `[1,q]`. -/
theorem positiveZModResidue_pos_le {q : ℕ} (hq : 0 < q) (x : ZMod q) :
    0 < positiveZModResidue q x ∧ positiveZModResidue q x ≤ q := by
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  by_cases hx : x = 0
  · simp [positiveZModResidue, hx, hq]
  · simp only [positiveZModResidue, if_neg hx]
    exact ⟨ZMod.val_pos.mpr hx, (ZMod.val_lt x).le⟩

/-- The unit represented by `2` modulo an odd modulus. -/
def twoUnitOfOdd (q : ℕ) (hodd : Odd q) : (ZMod q)ˣ :=
  ZMod.unitOfCoprime 2 hodd.coprime_two_left

@[simp]
theorem coe_twoUnitOfOdd (q : ℕ) (hodd : Odd q) :
    (twoUnitOfOdd q hodd : ZMod q) = 2 := by
  exact ZMod.coe_unitOfCoprime 2 hodd.coprime_two_left

/-- Base point `(2h)⁻¹` for the involution coset attached to `h`. -/
def restrictedRootBase (q : ℕ) (hodd : Odd q) (h : (ZMod q)ˣ) :
    (ZMod q)ˣ := (twoUnitOfOdd q hodd * h)⁻¹

/-- Positive residues obtained from the involution coset at `(2h)⁻¹`. -/
noncomputable def involutionDifferenceSet (q : ℕ) (hodd : Odd q)
    (h : (ZMod q)ˣ) : Finset ℕ :=
  Finset.univ.image (fun u : involutionSubgroup q ↦
    positiveZModResidue q
      (((restrictedRootBase q hodd h : (ZMod q)ˣ) : ZMod q) *
          ((u.1 : (ZMod q)ˣ) : ZMod q) -
        ((restrictedRootBase q hodd h : (ZMod q)ˣ) : ZMod q)))

/-- The restricted-root minimum, initially expressed as the corresponding
involution coset gap.  The characterization below identifies it with the least
`j` satisfying the quadratic congruence. -/
noncomputable def restrictedRootMin (q : ℕ) (hodd : Odd q)
    (h : (ZMod q)ˣ) : ℕ :=
  abstractCosetGap q (unitResidue q) (involutionSubgroup q)
    (restrictedRootBase q hodd h)

/-- Every difference obtained from an involution satisfies the restricted
quadratic equation. -/
theorem involutionDifference_is_restrictedRoot (q : ℕ) (hodd : Odd q)
    (h : (ZMod q)ˣ) (u : involutionSubgroup q) :
    let a : ZMod q := (restrictedRootBase q hodd h : (ZMod q)ˣ)
    let x : ZMod q := a * ((u.1 : (ZMod q)ˣ) : ZMod q) - a
    x * (((h : (ZMod q)ˣ) : ZMod q) * x + 1) = 0 := by
  let : NeZero q := ⟨Nat.ne_of_gt hodd.pos⟩
  dsimp only
  let a : ZMod q := (restrictedRootBase q hodd h : (ZMod q)ˣ)
  let x : ZMod q := a * ((u.1 : (ZMod q)ˣ) : ZMod q) - a
  have h2 : IsUnit (2 : ZMod q) := by
    simpa using (twoUnitOfOdd q hodd).isUnit
  have hh : IsUnit ((h : (ZMod q)ˣ) : ZMod q) := h.isUnit
  apply (affine_square_eq_one_iff
    ((h : (ZMod q)ˣ) : ZMod q) x h2 hh).mp
  have hta : (2 : ZMod q) * ((h : (ZMod q)ˣ) : ZMod q) * a = 1 := by
    have hu : twoUnitOfOdd q hodd * h * restrictedRootBase q hodd h = 1 := by
      simp [restrictedRootBase]
    simpa [a] using congrArg (fun z : (ZMod q)ˣ ↦ (z : ZMod q)) hu
  have hxu : 2 * ((h : (ZMod q)ˣ) : ZMod q) * x + 1 =
      ((u.1 : (ZMod q)ˣ) : ZMod q) := by
    dsimp [x]
    calc
      2 * ((h : (ZMod q)ˣ) : ZMod q) *
            (a * ((u.1 : (ZMod q)ˣ) : ZMod q) - a) + 1 =
          (2 * ((h : (ZMod q)ˣ) : ZMod q) * a) *
            ((u.1 : (ZMod q)ˣ) : ZMod q) -
          (2 * ((h : (ZMod q)ˣ) : ZMod q) * a) + 1 := by ring
      _ = ((u.1 : (ZMod q)ˣ) : ZMod q) := by rw [hta]; ring
  rw [hxu]
  simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
    congrArg (fun z : (ZMod q)ˣ ↦ (z : ZMod q)) u.2

/-- Every member of the difference set lies in `[1,q]` and satisfies the
restricted quadratic equation. -/
theorem mem_involutionDifferenceSet_imp_restrictedRoot {q j : ℕ}
    (hodd : Odd q) (h : (ZMod q)ˣ)
    (hj : j ∈ involutionDifferenceSet q hodd h) :
    0 < j ∧ j ≤ q ∧
      (j : ZMod q) * (((h : (ZMod q)ˣ) : ZMod q) * (j : ZMod q) + 1) = 0 := by
  classical
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hj
  let a : ZMod q := (restrictedRootBase q hodd h : (ZMod q)ˣ)
  let x : ZMod q := a * ((u.1 : (ZMod q)ˣ) : ZMod q) - a
  have hb := positiveZModResidue_pos_le hodd.pos x
  refine ⟨hb.1, hb.2, ?_⟩
  have hcast := natCast_positiveZModResidue hodd.pos x
  rw [hcast]
  exact involutionDifference_is_restrictedRoot q hodd h u

/-- Conversely, every representative in `[1,q]` satisfying the restricted
quadratic equation comes from a unique involution-coset difference. -/
theorem restrictedRoot_mem_involutionDifferenceSet {q j : ℕ}
    (hodd : Odd q) (h : (ZMod q)ˣ) (hjpos : 0 < j) (hjle : j ≤ q)
    (hroot :
      (j : ZMod q) * (((h : (ZMod q)ˣ) : ZMod q) * (j : ZMod q) + 1) = 0) :
    j ∈ involutionDifferenceSet q hodd h := by
  classical
  let : NeZero q := ⟨Nat.ne_of_gt hodd.pos⟩
  let z : ZMod q := 2 * ((h : (ZMod q)ˣ) : ZMod q) * (j : ZMod q) + 1
  have h2 : IsUnit (2 : ZMod q) := by
    simpa using (twoUnitOfOdd q hodd).isUnit
  have hh : IsUnit ((h : (ZMod q)ˣ) : ZMod q) := h.isUnit
  have hzsq : z ^ 2 = 1 := by
    apply (affine_square_eq_one_iff
      ((h : (ZMod q)ˣ) : ZMod q) (j : ZMod q) h2 hh).mpr
    exact hroot
  let zu : (ZMod q)ˣ := Units.mk z z
    (by simpa [pow_two] using hzsq)
    (by simpa [pow_two] using hzsq)
  have hzusq : zu ^ 2 = 1 := by
    apply Units.ext
    simpa [zu] using hzsq
  let u : involutionSubgroup q := ⟨zu, hzusq⟩
  refine Finset.mem_image.mpr ⟨u, Finset.mem_univ _, ?_⟩
  let a : ZMod q := (restrictedRootBase q hodd h : (ZMod q)ˣ)
  apply positiveZModResidue_eq_of_natCast_eq hodd.pos hjpos hjle
  have hat : a * (2 * ((h : (ZMod q)ˣ) : ZMod q)) = 1 := by
    have hu : restrictedRootBase q hodd h * (twoUnitOfOdd q hodd * h) = 1 := by
      simp [restrictedRootBase]
    simpa [a, mul_assoc] using congrArg (fun w : (ZMod q)ˣ ↦ (w : ZMod q)) hu
  change (j : ZMod q) = a * (zu : ZMod q) - a
  calc
    (j : ZMod q) = (a * (2 * ((h : (ZMod q)ˣ) : ZMod q))) * (j : ZMod q) := by
      rw [hat, one_mul]
    _ = a * (z : ZMod q) - a := by dsimp [z]; ring
    _ = a * (zu : ZMod q) - a := by rfl

/-- Exact characterization of the finite difference set by the restricted
quadratic congruence. -/
theorem mem_involutionDifferenceSet_iff_restrictedRoot {q j : ℕ}
    (hodd : Odd q) (h : (ZMod q)ˣ) :
    j ∈ involutionDifferenceSet q hodd h ↔
      0 < j ∧ j ≤ q ∧
        (j : ZMod q) * (((h : (ZMod q)ˣ) : ZMod q) * (j : ZMod q) + 1) = 0 := by
  constructor
  · exact mem_involutionDifferenceSet_imp_restrictedRoot hodd h
  · rintro ⟨hjpos, hjle, hroot⟩
    exact restrictedRoot_mem_involutionDifferenceSet hodd h hjpos hjle hroot

/-- The involution-difference set is nonempty. -/
theorem involutionDifferenceSet_nonempty (q : ℕ) (hodd : Odd q)
    (h : (ZMod q)ˣ) : (involutionDifferenceSet q hodd h).Nonempty := by
  classical
  let a := restrictedRootBase q hodd h
  refine ⟨positiveZModResidue q (((a : (ZMod q)ˣ) : ZMod q) * 1 -
      ((a : (ZMod q)ˣ) : ZMod q)), Finset.mem_image.mpr ?_⟩
  exact ⟨(1 : involutionSubgroup q), Finset.mem_univ _, by simp [a]⟩

/-- The image of clockwise distances in the abstract coset is exactly the image
of positive residues of the corresponding differences. -/
theorem cosetDistanceImage_eq_involutionDifferenceSet (q : ℕ) (hodd : Odd q)
    (h : (ZMod q)ˣ) :
    (cosetValues (unitResidue q) (involutionSubgroup q)
        (restrictedRootBase q hodd h)).image
      (circleDistance q (unitResidue q (restrictedRootBase q hodd h))) =
    involutionDifferenceSet q hodd h := by
  classical
  let a := restrictedRootBase q hodd h
  ext x
  constructor
  · intro hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hb
    refine Finset.mem_image.mpr ⟨u, Finset.mem_univ _, ?_⟩
    simpa [cosetValues, involutionDifferenceSet, unitResidue, a] using
      (circleDistance_eq_positiveZModResidue_sub hodd.pos
        (((a : (ZMod q)ˣ) : ZMod q))
        ((((a : (ZMod q)ˣ) * (u.1 : (ZMod q)ˣ)) : (ZMod q)ˣ) : ZMod q)).symm
  · intro hx
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨unitResidue q (a * u.1), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
    · simpa [involutionDifferenceSet, unitResidue, a] using
        circleDistance_eq_positiveZModResidue_sub hodd.pos
          (((a : (ZMod q)ˣ) : ZMod q))
          ((((a : (ZMod q)ˣ) * (u.1 : (ZMod q)ˣ)) : (ZMod q)ˣ) : ZMod q)

/-- `restrictedRootMin` is the minimum of the explicit involution-difference
set. -/
theorem restrictedRootMin_eq_min'_involutionDifferenceSet (q : ℕ)
    (hodd : Odd q) (h : (ZMod q)ˣ) :
    restrictedRootMin q hodd h =
      (involutionDifferenceSet q hodd h).min'
        (involutionDifferenceSet_nonempty q hodd h) := by
  let a := restrictedRootBase q hodd h
  let s := cosetValues (unitResidue q) (involutionSubgroup q) a
  have hs : s.Nonempty := cosetValues_nonempty (unitResidue q)
    (involutionSubgroup q) a
  have ha : unitResidue q a ∈ s :=
    self_mem_cosetValues (unitResidue q) (involutionSubgroup q) a
  unfold restrictedRootMin abstractCosetGap
  rw [gapInSet_of_mem q s hs ha]
  unfold leastCircleGap
  have heq := cosetDistanceImage_eq_involutionDifferenceSet q hodd h
  change (s.image (circleDistance q (unitResidue q a))).min' _ = _
  change s.image (circleDistance q (unitResidue q a)) =
    involutionDifferenceSet q hodd h at heq
  apply Nat.le_antisymm
  · apply Finset.min'_le
    rw [heq]
    exact (involutionDifferenceSet q hodd h).min'_mem
      (involutionDifferenceSet_nonempty q hodd h)
  · apply Finset.min'_le
    rw [← heq]
    exact (s.image (circleDistance q (unitResidue q a))).min'_mem _

/-- The restricted minimum itself is positive, at most `q`, and satisfies the
quadratic congruence. -/
theorem restrictedRootMin_spec (q : ℕ) (hodd : Odd q) (h : (ZMod q)ˣ) :
    0 < restrictedRootMin q hodd h ∧ restrictedRootMin q hodd h ≤ q ∧
      (restrictedRootMin q hodd h : ZMod q) *
        (((h : (ZMod q)ˣ) : ZMod q) *
          (restrictedRootMin q hodd h : ZMod q) + 1) = 0 := by
  rw [restrictedRootMin_eq_min'_involutionDifferenceSet q hodd h]
  apply mem_involutionDifferenceSet_imp_restrictedRoot hodd h
  exact (involutionDifferenceSet q hodd h).min'_mem
    (involutionDifferenceSet_nonempty q hodd h)

/-- Every positive representative satisfying the restricted congruence is at
least the restricted minimum. -/
theorem restrictedRootMin_le {q j : ℕ} (hodd : Odd q) (h : (ZMod q)ˣ)
    (hjpos : 0 < j) (hjle : j ≤ q)
    (hroot :
      (j : ZMod q) * (((h : (ZMod q)ˣ) : ZMod q) * (j : ZMod q) + 1) = 0) :
    restrictedRootMin q hodd h ≤ j := by
  rw [restrictedRootMin_eq_min'_involutionDifferenceSet q hodd h]
  apply Finset.min'_le
  exact restrictedRoot_mem_involutionDifferenceSet hodd h hjpos hjle hroot

/-- For a natural residue `m` coprime to odd `q`, the formal restricted
minimum satisfies the original natural-number divisibility condition. -/
theorem restrictedRootMin_nat_dvd {m q : ℕ} (hodd : Odd q)
    (hcop : m.Coprime q) :
    q ∣ restrictedRootMin q hodd (ZMod.unitOfCoprime m hcop) *
      (m * restrictedRootMin q hodd (ZMod.unitOfCoprime m hcop) + 1) := by
  let j := restrictedRootMin q hodd (ZMod.unitOfCoprime m hcop)
  have hroot := (restrictedRootMin_spec q hodd (ZMod.unitOfCoprime m hcop)).2.2
  have hz : ((j * (m * j + 1) : ℕ) : ZMod q) = 0 := by
    simpa [j, ZMod.coe_unitOfCoprime] using hroot
  exact (ZMod.natCast_eq_zero_iff (j * (m * j + 1)) q).mp hz

/-- The same restricted minimum is minimal among positive natural
representatives satisfying the original divisibility condition. -/
theorem restrictedRootMin_le_of_nat_dvd {m q j : ℕ} (hodd : Odd q)
    (hcop : m.Coprime q) (hjpos : 0 < j) (hjle : j ≤ q)
    (hdiv : q ∣ j * (m * j + 1)) :
    restrictedRootMin q hodd (ZMod.unitOfCoprime m hcop) ≤ j := by
  apply restrictedRootMin_le hodd (ZMod.unitOfCoprime m hcop) hjpos hjle
  have hz : ((j * (m * j + 1) : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff (j * (m * j + 1)) q).mpr hdiv
  simpa [ZMod.coe_unitOfCoprime] using hz

/-- The exact restricted minimum gives an admissible start for `t₂(mq)`. -/
theorem t_two_mul_le_restrictedRootMin {m q : ℕ} (hm : 0 < m)
    (hodd : Odd q) (hcop : m.Coprime q) :
    t 2 (m * q) ≤
      m * restrictedRootMin q hodd (ZMod.unitOfCoprime m hcop) := by
  apply t_two_mul_le_of_restricted_root hm
    (restrictedRootMin_spec q hodd (ZMod.unitOfCoprime m hcop)).1
  exact restrictedRootMin_nat_dvd hodd hcop

/-- Exact restricted-root mean for odd squarefree `q`, in denominator-free
integer form. -/
theorem pow_card_mul_sum_restrictedRootMin {q : ℕ}
    (hsq : Squarefree q) (hodd : Odd q) :
    2 ^ q.primeFactors.card *
        (∑ h : (ZMod q)ˣ, restrictedRootMin q hodd h) =
      q * q.totient := by
  let : NeZero q := ⟨Nat.ne_of_gt hodd.pos⟩
  let v := unitResidue q
  have hv : Function.Injective v := by
    let : NeZero q := ⟨Nat.ne_of_gt hodd.pos⟩
    intro a b hab
    apply Units.ext
    apply ZMod.val_injective q
    exact hab
  have hvlt : ∀ a : (ZMod q)ˣ, v a < q := by
    let : NeZero q := ⟨Nat.ne_of_gt hodd.pos⟩
    intro a
    exact ZMod.val_lt (a.1 : ZMod q)
  have hcore := card_mul_sum_abstractCosetGap q v hv hvlt
    (involutionSubgroup q)
  rw [card_involutionSubgroup_odd_squarefree hsq hodd,
    ZMod.card_units_eq_totient q] at hcore
  have hbij : Function.Bijective (restrictedRootBase q hodd) := by
    exact ((Equiv.mulLeft (twoUnitOfOdd q hodd)).trans
      (Equiv.inv ((ZMod q)ˣ))).bijective
  have hsum :
      (∑ h : (ZMod q)ˣ,
        abstractCosetGap q v (involutionSubgroup q)
          (restrictedRootBase q hodd h)) =
      ∑ a : (ZMod q)ˣ, abstractCosetGap q v (involutionSubgroup q) a :=
    hbij.sum_comp (abstractCosetGap q v (involutionSubgroup q))
  change 2 ^ q.primeFactors.card *
      (∑ h : (ZMod q)ˣ,
        abstractCosetGap q v (involutionSubgroup q)
          (restrictedRootBase q hodd h)) = q * q.totient
  rw [hsum]
  exact hcore

end Erdos394
