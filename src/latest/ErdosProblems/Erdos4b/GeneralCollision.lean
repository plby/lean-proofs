/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralCrt

/-!
# Cross-family collision criterion for the doubled large-gap sieve

This module turns the generalized-CRT compatibility predicate into the
affine divisibility condition used by Maynard's auxiliary `a_(i,j)`
variables.  The hypotheses supplied by ordinary Maynard divisor tuples make
the moduli pairwise coprime inside each of the two families.  Consequently
the only remaining compatibility conditions are the first/companion ones
recorded below.
-/

namespace Erdos4b

noncomputable section

noncomputable local instance erdos4GeneralCollisionPropDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- A first-form residue and a companion-form residue agree modulo their
common modulus exactly when the corresponding affine constants agree. -/
theorem negativeShiftResidue_modEq_companionResidue_iff
    {D E m a b q : ℕ} (hD : 0 < D) (hE : 0 < E)
    (hmE : m.Coprime E) :
    BoundedGaps.Maynard.negativeShiftResidue D (a * q) ≡
        companionResidue m E (b * q) [MOD Nat.gcd D E] ↔
      m * (a * q) + 1 ≡ m * (b * q) [MOD Nat.gcd D E] := by
  let g := Nat.gcd D E
  let rD := BoundedGaps.Maynard.negativeShiftResidue D (a * q)
  let rE := companionResidue m E (b * q)
  have hgD : g ∣ D := Nat.gcd_dvd_left D E
  have hgE : g ∣ E := Nat.gcd_dvd_right D E
  have hnegD : rD + a * q ≡ 0 [MOD D] := by
    apply Nat.modEq_zero_iff_dvd.mpr
    exact BoundedGaps.Maynard.negativeShiftResidue_add_dvd D (a * q) hD
  have hneg : rD + a * q ≡ 0 [MOD g] := hnegD.of_dvd hgD
  have hcompE : m * (rE + b * q) ≡ 1 [MOD E] :=
    companionResidue_spec hE hmE
  have hcomp : m * (rE + b * q) ≡ 1 [MOD g] := hcompE.of_dvd hgE
  constructor
  · intro hcross
    have hcompD : m * (rD + b * q) ≡ 1 [MOD g] :=
      ((hcross.add_right (b * q)).mul_left m).trans hcomp
    have hleft : m * rD + (m * (a * q) + 1) ≡ 1 [MOD g] := by
      have hz := (hneg.mul_left m).add_right 1
      simpa [mul_add, add_assoc] using hz
    have hright : m * rD + m * (b * q) ≡ 1 [MOD g] := by
      simpa [mul_add] using hcompD
    exact Nat.ModEq.add_left_cancel' (m * rD)
      (hleft.trans hright.symm)
  · intro haffine
    have hzero : m * rD + m * (a * q) ≡ 0 [MOD g] := by
      simpa [mul_add] using hneg.mul_left m
    have hDcomp : m * rD + m * (b * q) ≡ 1 [MOD g] := by
      have hzeroOne : m * rD + (m * (a * q) + 1) ≡ 1 [MOD g] := by
        simpa [add_assoc] using hzero.add_right 1
      exact ((Nat.ModEq.refl (m * rD)).add haffine).symm.trans hzeroOne
    have hEcomp : m * rE + m * (b * q) ≡ 1 [MOD g] := by
      simpa [mul_add] using hcomp
    have hmul : m * rD ≡ m * rE [MOD g] := by
      apply Nat.ModEq.add_right_cancel' (m * (b * q))
      exact hDcomp.trans hEcomp.symm
    have hmg : m.Coprime g := hmE.coprime_dvd_right hgE
    exact Nat.ModEq.cancel_left_of_coprime
      (by simpa [Nat.Coprime, Nat.gcd_comm] using hmg)
      hmul

/-- With pairwise coprimality already known inside each divisor family, the
general doubled coordinate system is compatible precisely when every
first/companion affine collision is congruent modulo the corresponding gcd.
This is the exact finite predicate encoded by the auxiliary collision
divisors in the analytic expansion. -/
theorem largeGapCoordinateCrtCompatible_iff_cross_affine
    {H : Finset ℕ} {m q : ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (hmE : ∀ h : H, m.Coprime (Nat.lcm (e h) (e' h)))
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b))) :
    LargeGapCoordinateCrtCompatible H m q d e d' e' ↔
      ∀ a b : H,
        m * (a.1 * q) + 1 ≡ m * (b.1 * q)
          [MOD Nat.gcd (Nat.lcm (d a) (d' a))
            (Nat.lcm (e b) (e' b))] := by
  rw [largeGapCoordinateCrtCompatible_iff_pairwise H m q d e d' e'
    hDpos hEpos]
  constructor
  · intro hpair a b
    have hcross := hpair (Sum.inl a) (Finset.mem_univ _)
      (Sum.inr b) (Finset.mem_univ _)
    exact (negativeShiftResidue_modEq_companionResidue_iff
      (hDpos a) (hEpos b) (hmE b)).mp (by
        simpa [largeGapCrtModulus, largeGapCrtResidue] using hcross)
  · intro hcross i hi j hj
    cases i with
    | inl a =>
        cases j with
        | inl b =>
            by_cases hab : a = b
            · subst b
              exact Nat.ModEq.refl _
            · have hcop := hDD hab
              have hg : Nat.gcd (Nat.lcm (d a) (d' a))
                  (Nat.lcm (d b) (d' b)) = 1 := hcop
              simpa [largeGapCrtModulus, hg] using (Nat.modEq_one :
                largeGapCrtResidue H m q d e d' e' (Sum.inl a) ≡
                  largeGapCrtResidue H m q d e d' e' (Sum.inl b) [MOD 1])
        | inr b =>
            exact (negativeShiftResidue_modEq_companionResidue_iff
              (hDpos a) (hEpos b) (hmE b)).mpr (hcross a b)
    | inr a =>
        cases j with
        | inl b =>
            simpa [largeGapCrtModulus, largeGapCrtResidue, Nat.gcd_comm] using
              ((negativeShiftResidue_modEq_companionResidue_iff
                (hDpos b) (hEpos a) (hmE a)).mpr (hcross b a)).symm
        | inr b =>
            by_cases hab : a = b
            · subst b
              exact Nat.ModEq.refl _
            · have hcop := hEE hab
              have hg : Nat.gcd (Nat.lcm (e a) (e' a))
                  (Nat.lcm (e b) (e' b)) = 1 := hcop
              simpa [largeGapCrtModulus, hg] using (Nat.modEq_one :
                largeGapCrtResidue H m q d e d' e' (Sum.inr a) ≡
                  largeGapCrtResidue H m q d e d' e' (Sum.inr b) [MOD 1])

/-- A compatible coordinate system has a positive simultaneous solution.
Adding the lcm period to the canonical witness avoids the possible zero
witness and lets the already-proved divisor-condition support lemmas apply. -/
theorem exists_positive_largeGapDivisorConditions_of_coordinateCompatible
    {H : Finset ℕ} {m q : ℕ} {d e d' e' : H → ℕ}
    (hm : 0 < m)
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (hmE : ∀ h : H, m.Coprime (Nat.lcm (e h) (e' h)))
    (hcompat : LargeGapCoordinateCrtCompatible H m q d e d' e') :
    ∃ n > 0,
      largeGapDivisorCondition H m q n d e ∧
        largeGapDivisorCondition H m q n d' e' := by
  classical
  obtain ⟨r, hr⟩ := hcompat
  let M := largeGapCoordinateCrtModulus H d e d' e'
  let n := r + M
  have hM : 0 < M := by
    apply generalCrtModulus_pos
    intro i hi
    cases i with
    | inl h => exact hDpos h
    | inr h => exact hEpos h
  have hn : 0 < n := by omega
  refine ⟨n, hn, ?_⟩
  apply (largeGapDivisorCondition_pair_iff_modEq
    H m q n d e d' e' hm hDpos hEpos hmE (fun h ↦ by omega)).mpr
  intro i
  have hcoord : largeGapCrtModulus H d e d' e' i ∣ M := by
    exact Finset.dvd_lcm
      (s := (Finset.univ : Finset (LargeGapCrtIndex H)))
      (f := largeGapCrtModulus H d e d' e') (Finset.mem_univ i)
  have hzero : M ≡ 0 [MOD largeGapCrtModulus H d e d' e' i] :=
    Nat.modEq_zero_iff_dvd.mpr hcoord
  simpa [n] using (hr i (Finset.mem_univ i)).add hzero

/-- Compatibility, support, and the standard difference-prime exclusions
force pairwise coprimality inside both lcm families.  This discharges the
hypotheses of the exact cross-period formula for every nonzero summand of
the standard doubled kernel. -/
theorem withinFamilyLcm_pairwise_of_coordinateCompatible
    {H : Finset ℕ} {RD RE WD WE m q : ℕ}
    {d e d' e' : H → ℕ}
    (hm : 0 < m) (hq : 0 < q)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD WD d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD WD d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE WE e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE WE e')
    (hcoverD : BoundedGaps.Maynard.CoversShiftDifferencePrimes H WD)
    (hcoverE : BoundedGaps.Maynard.CoversShiftDifferencePrimes H WE)
    (hmE : m.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e))
    (hmE' : m.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e'))
    (hqD : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H d))
    (hqD' : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H d'))
    (hqE : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e))
    (hqE' : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e'))
    (hcompat : LargeGapCoordinateCrtCompatible H m q d e d' e') :
    (∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b))) ∧
    (∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b))) := by
  have hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h) := fun h ↦
    Nat.lcm_pos (Nat.pos_of_ne_zero (hd.coordinate_squarefree h).ne_zero)
      (Nat.pos_of_ne_zero (hd'.coordinate_squarefree h).ne_zero)
  have hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h) := fun h ↦
    Nat.lcm_pos (Nat.pos_of_ne_zero (he.coordinate_squarefree h).ne_zero)
      (Nat.pos_of_ne_zero (he'.coordinate_squarefree h).ne_zero)
  have hmElcm : ∀ h : H, m.Coprime (Nat.lcm (e h) (e' h)) := by
    intro h
    have hme : m.Coprime (e h) := Nat.Coprime.of_dvd_right
      (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product e h) hmE
    have hme' : m.Coprime (e' h) := Nat.Coprime.of_dvd_right
      (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product e' h) hmE'
    apply Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul (e h) (e' h))
    exact hme.mul_right hme'
  obtain ⟨n, hn, hcond, hcond'⟩ :=
    exists_positive_largeGapDivisorConditions_of_coordinateCompatible
      hm hDpos hEpos hmElcm hcompat
  have hcrossD : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' :=
    firstForms_crossCoordinateCoprime_of_conditions hd hd' hcoverD
      hqD hqD' hcond hcond'
  have hcrossE : BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e' :=
    companionForms_crossCoordinateCoprime_of_conditions hm hn hq he he'
      hcoverE hmE hmE' hqE hqE' hcond hcond'
  constructor
  · intro a b hab
    exact BoundedGaps.Maynard.coprime_lcm_lcm_of_four
      (hd.coordinates_coprime hab) (hcrossD hab).1
      (hcrossD hab).2 (hd'.coordinates_coprime hab)
  · intro a b hab
    exact BoundedGaps.Maynard.coprime_lcm_lcm_of_four
      (he.coordinates_coprime hab) (hcrossE hab).1
      (hcrossE hab).2 (he'.coordinates_coprime hab)

/-! ## Exact cross-gcd factor in the coordinate period -/

/-- A gcd distributes over a product whose factors are pairwise coprime. -/
theorem gcd_finsetProd_right_of_pairwise
    {I : Type*} (s : Finset I) (f : I → ℕ) (x : ℕ)
    (hpair : Set.Pairwise (s : Set I) (Nat.Coprime.onFun f)) :
    Nat.gcd x (∏ i ∈ s, f i) = ∏ i ∈ s, Nat.gcd x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hpairS : Set.Pairwise (s : Set I) (Nat.Coprime.onFun f) := by
        intro i hi j hj hij
        exact hpair (Finset.mem_insert_of_mem hi)
          (Finset.mem_insert_of_mem hj) hij
      have hcop : (f a).Coprime (∏ i ∈ s, f i) := by
        apply Nat.Coprime.prod_right
        intro i hi
        apply hpair (Finset.mem_insert_self a s)
          (Finset.mem_insert_of_mem hi)
        intro hai
        subst i
        exact ha hi
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Nat.Coprime.gcd_mul x hcop, ih hpairS]

/-- Left-handed form of `gcd_finsetProd_right_of_pairwise`. -/
theorem gcd_finsetProd_left_of_pairwise
    {I : Type*} (s : Finset I) (f : I → ℕ) (x : ℕ)
    (hpair : Set.Pairwise (s : Set I) (Nat.Coprime.onFun f)) :
    Nat.gcd (∏ i ∈ s, f i) x = ∏ i ∈ s, Nat.gcd (f i) x := by
  simpa [Nat.gcd_comm] using gcd_finsetProd_right_of_pairwise s f x hpair

/-- Product of all cross-family common factors.  Pairwise coprimality inside
each family ensures that a prime can occur in at most one factor of this
double product. -/
def crossCoordinateGcdProduct (H : Finset ℕ)
    (d e d' e' : H → ℕ) : ℕ :=
  ∏ b : H, ∏ a : H,
    Nat.gcd (Nat.lcm (d a) (d' a)) (Nat.lcm (e b) (e' b))

/-- The gcd of the two within-family products is exactly the product of the
individual cross gcds.  This is the multiplicative source of Maynard's
auxiliary `a_(i,j)` variables. -/
theorem gcd_firstLcmProduct_companionLcmProduct_eq_cross
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b))) :
    Nat.gcd (firstLcmProduct H d d') (companionLcmProduct H e e') =
      crossCoordinateGcdProduct H d e d' e' := by
  classical
  let D : H → ℕ := fun a ↦ Nat.lcm (d a) (d' a)
  let E : H → ℕ := fun b ↦ Nat.lcm (e b) (e' b)
  have hDpair : Set.Pairwise ((Finset.univ : Finset H) : Set H)
      (Nat.Coprime.onFun D) := by
    intro a ha b hb hab
    exact hDD hab
  have hEpair : Set.Pairwise ((Finset.univ : Finset H) : Set H)
      (Nat.Coprime.onFun E) := by
    intro a ha b hb hab
    exact hEE hab
  rw [show firstLcmProduct H d d' = ∏ a : H, D a by
      simp [firstLcmProduct, D]]
  rw [show companionLcmProduct H e e' = ∏ b : H, E b by
      simp [companionLcmProduct, E]]
  rw [gcd_finsetProd_right_of_pairwise Finset.univ E
    (∏ a : H, D a) hEpair]
  unfold crossCoordinateGcdProduct
  apply Finset.prod_congr rfl
  intro b hb
  simpa [D, E] using gcd_finsetProd_left_of_pairwise
    Finset.univ D (E b) hDpair

/-- For pairwise-coprime coordinates inside each family, the true lcm period
times the cross-collision factor equals the naive product period.  Thus
`1 / period` is the naive reciprocal product multiplied by the full cross
factor, which is the exact algebraic gain used in the large-gap sieve. -/
theorem largeGapCoordinateCrtModulus_mul_cross_eq_products
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b))) :
    largeGapCoordinateCrtModulus H d e d' e' *
        crossCoordinateGcdProduct H d e d' e' =
      firstLcmProduct H d d' * companionLcmProduct H e e' := by
  classical
  let D : H → ℕ := fun a ↦ Nat.lcm (d a) (d' a)
  let E : H → ℕ := fun b ↦ Nat.lcm (e b) (e' b)
  let PD := ∏ a : H, D a
  let PE := ∏ b : H, E b
  have hDpair : Set.Pairwise ((Finset.univ : Finset H) : Set H)
      (Nat.Coprime.onFun D) := by
    intro a ha b hb hab
    exact hDD hab
  have hEpair : Set.Pairwise ((Finset.univ : Finset H) : Set H)
      (Nat.Coprime.onFun E) := by
    intro a ha b hb hab
    exact hEE hab
  have hPD : firstLcmProduct H d d' = PD := by
    simp [firstLcmProduct, PD, D]
  have hPE : companionLcmProduct H e e' = PE := by
    simp [companionLcmProduct, PE, E]
  have hM : largeGapCoordinateCrtModulus H d e d' e' = Nat.lcm PD PE := by
    apply Nat.dvd_antisymm
    · apply Finset.lcm_dvd
      intro i hi
      cases i with
      | inl a =>
          exact (Finset.dvd_prod_of_mem D (Finset.mem_univ a)).trans
            (Nat.dvd_lcm_left PD PE)
      | inr b =>
          exact (Finset.dvd_prod_of_mem E (Finset.mem_univ b)).trans
            (Nat.dvd_lcm_right PD PE)
    · apply Nat.lcm_dvd
      · change (∏ a : H, D a) ∣
          largeGapCoordinateCrtModulus H d e d' e'
        rw [← Finset.lcm_eq_prod hDpair]
        apply Finset.lcm_dvd
        intro a ha
        simpa [D, largeGapCoordinateCrtModulus, largeGapCrtModulus] using
          (Finset.dvd_lcm
            (s := (Finset.univ : Finset (LargeGapCrtIndex H)))
            (f := largeGapCrtModulus H d e d' e')
            (b := Sum.inl a) (by simp))
      · change (∏ b : H, E b) ∣
          largeGapCoordinateCrtModulus H d e d' e'
        rw [← Finset.lcm_eq_prod hEpair]
        apply Finset.lcm_dvd
        intro b hb
        simpa [E, largeGapCoordinateCrtModulus, largeGapCrtModulus] using
          (Finset.dvd_lcm
            (s := (Finset.univ : Finset (LargeGapCrtIndex H)))
            (f := largeGapCrtModulus H d e d' e')
            (b := Sum.inr b) (by simp))
  have hcross := gcd_firstLcmProduct_companionLcmProduct_eq_cross hDD hEE
  calc
    largeGapCoordinateCrtModulus H d e d' e' *
          crossCoordinateGcdProduct H d e d' e' =
        Nat.lcm PD PE * Nat.gcd PD PE := by rw [hM, ← hcross, hPD, hPE]
    _ = PD * PE := by rw [mul_comm, Nat.gcd_mul_lcm]
    _ = firstLcmProduct H d d' * companionLcmProduct H e e' := by
      rw [hPD, hPE]

/-- The generalized coordinate period is the lcm of the two within-family
products.  This aggregate form is useful for the pinned prime main term,
whose denominator is the totient of the period. -/
theorem largeGapCoordinateCrtModulus_eq_lcm_products
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b))) :
    largeGapCoordinateCrtModulus H d e d' e' =
      Nat.lcm (firstLcmProduct H d d')
        (companionLcmProduct H e e') := by
  have hcrossPos : 0 < crossCoordinateGcdProduct H d e d' e' := by
    unfold crossCoordinateGcdProduct
    exact Finset.prod_pos fun b _ ↦ Finset.prod_pos fun a _ ↦
      Nat.gcd_pos_of_pos_left _ (hDpos a)
  apply mul_right_cancel₀ hcrossPos.ne'
  rw [largeGapCoordinateCrtModulus_mul_cross_eq_products hDD hEE]
  rw [← gcd_firstLcmProduct_companionLcmProduct_eq_cross hDD hEE]
  simpa [mul_comm] using
    (Nat.gcd_mul_lcm (firstLcmProduct H d d')
      (companionLcmProduct H e e')).symm

/-- The real-valued product of the divisor-totient sums over all cross
coordinates.  Expanding each factor turns this into the finite family of
Maynard auxiliary divisors. -/
noncomputable def crossCoordinateTotientSumProduct (H : Finset ℕ)
    (d e d' e' : H → ℕ) : ℝ :=
  ∏ b : H, ∏ a : H,
    BoundedGaps.Maynard.commonDivisorTotientSum
      (Nat.lcm (d a) (d' a)) (Nat.lcm (e b) (e' b))

theorem crossCoordinateTotientSumProduct_eq_crossGcd
    (H : Finset ℕ) (d e d' e' : H → ℕ) :
    crossCoordinateTotientSumProduct H d e d' e' =
      (crossCoordinateGcdProduct H d e d' e' : ℝ) := by
  classical
  unfold crossCoordinateTotientSumProduct crossCoordinateGcdProduct
  simp only [BoundedGaps.Maynard.commonDivisorTotientSum_eq_gcd]
  push_cast
  rfl

/-- One choice of an auxiliary divisor for every ordered companion/first
coordinate pair.  The subtype records exactly that the chosen integer
divides the corresponding cross gcd. -/
abbrev CrossAuxiliaryDivisors (H : Finset ℕ)
    (d e d' e' : H → ℕ) :=
  ∀ ba : H × H,
    ↑(Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
      (Nat.lcm (e ba.1) (e' ba.1))).divisors

/-- Multiplicative totient weight of an auxiliary-divisor matrix. -/
noncomputable def crossAuxiliaryTotientWeight
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (a : CrossAuxiliaryDivisors H d e d' e') : ℝ :=
  ∏ ba : H × H, (Nat.totient (a ba).1 : ℝ)

/-- The affine congruences imposed on one auxiliary-divisor matrix.  The
ordered pair is `(companion coordinate, first coordinate)`. -/
def CrossAuxiliaryAffineCompatible
    {H : Finset ℕ} {d e d' e' : H → ℕ} (m q : ℕ)
    (a : CrossAuxiliaryDivisors H d e d' e') : Prop :=
  ∀ ba : H × H,
    m * (ba.2.1 * q) + 1 ≡ m * (ba.1.1 * q) [MOD (a ba).1]

/-- Every auxiliary divisor inherits the affine congruence of a compatible
doubled coordinate system. -/
theorem crossAuxiliaryAffineCompatible_of_coordinateCompatible
    {H : Finset ℕ} {m q : ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (hmE : ∀ h : H, m.Coprime (Nat.lcm (e h) (e' h)))
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b)))
    (hcompat : LargeGapCoordinateCrtCompatible H m q d e d' e')
    (a : CrossAuxiliaryDivisors H d e d' e') :
    CrossAuxiliaryAffineCompatible m q a := by
  have hcross := (largeGapCoordinateCrtCompatible_iff_cross_affine
    hDpos hEpos hmE hDD hEE).mp hcompat
  intro ba
  apply (hcross ba.2 ba.1).of_dvd
  exact (Nat.mem_divisors.mp (a ba).2).1

/-- The matrix choosing the entire cross gcd in each coordinate. -/
noncomputable def maximalCrossAuxiliaryDivisors
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h)) :
    CrossAuxiliaryDivisors H d e d' e' := fun ba ↦
  ⟨Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
      (Nat.lcm (e ba.1) (e' ba.1)), by
    apply Nat.mem_divisors_self
    exact (Nat.gcd_pos_of_pos_left _ (hDpos ba.2)).ne'⟩

/-- Checking the affine conditions only on the maximal auxiliary matrix is
equivalent to generalized-CRT compatibility. -/
theorem coordinateCompatible_iff_maximalCrossAuxiliary
    {H : Finset ℕ} {m q : ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (hmE : ∀ h : H, m.Coprime (Nat.lcm (e h) (e' h)))
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b))) :
    LargeGapCoordinateCrtCompatible H m q d e d' e' ↔
      CrossAuxiliaryAffineCompatible m q
        (maximalCrossAuxiliaryDivisors hDpos hEpos) := by
  rw [largeGapCoordinateCrtCompatible_iff_cross_affine
    hDpos hEpos hmE hDD hEE]
  constructor
  · intro h ba
    simpa [maximalCrossAuxiliaryDivisors] using h ba.2 ba.1
  · intro h a b
    simpa [maximalCrossAuxiliaryDivisors] using h (b, a)

/-- Fully expanded `a_(i,j)` form of the cross collision factor.  This is
an exact finite identity, before any Euler-product estimate or truncation. -/
theorem crossCoordinateTotientSumProduct_eq_auxiliarySum
    (H : Finset ℕ) (d e d' e' : H → ℕ) :
    crossCoordinateTotientSumProduct H d e d' e' =
      ∑ a : CrossAuxiliaryDivisors H d e d' e',
        crossAuxiliaryTotientWeight a := by
  classical
  unfold crossCoordinateTotientSumProduct
    crossAuxiliaryTotientWeight
    BoundedGaps.Maynard.commonDivisorTotientSum
  rw [← Fintype.prod_prod_type (fun ba : H × H ↦
    ∑ u ∈ (Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
      (Nat.lcm (e ba.1) (e' ba.1))).divisors,
        (Nat.totient u : ℝ))]
  have hprod :
      (∏ ba : H × H,
        ∑ u ∈ (Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
          (Nat.lcm (e ba.1) (e' ba.1))).divisors,
            (Nat.totient u : ℝ)) =
        ∏ ba : H × H,
          ∑ u : ↑(Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
            (Nat.lcm (e ba.1) (e' ba.1))).divisors,
              (Nat.totient u.1 : ℝ) := by
    apply Finset.prod_congr rfl
    intro ba hba
    exact (Finset.sum_attach
      (Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1))).divisors
      (fun u ↦ (Nat.totient u : ℝ))).symm
  rw [hprod]
  exact Fintype.prod_sum (fun ba : H × H => fun u :
    ↑(Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
      (Nat.lcm (e ba.1) (e' ba.1))).divisors =>
        (Nat.totient u.1 : ℝ))

/-- Reciprocal-period form of
`largeGapCoordinateCrtModulus_mul_cross_eq_products`.  This is the exact
summand identity needed to rewrite the unseparated normalization kernel as
the ordinary product denominator times the auxiliary collision sum. -/
theorem inv_largeGapCoordinateCrtModulus_eq_cross_div_products
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b))) :
    ((largeGapCoordinateCrtModulus H d e d' e' : ℝ)⁻¹) =
      crossCoordinateTotientSumProduct H d e d' e' /
        ((firstLcmProduct H d d' : ℝ) *
          companionLcmProduct H e e') := by
  have hM : 0 < largeGapCoordinateCrtModulus H d e d' e' := by
    apply generalCrtModulus_pos
    intro i hi
    cases i with
    | inl h => exact hDpos h
    | inr h => exact hEpos h
  have hPD : 0 < firstLcmProduct H d d' := by
    unfold firstLcmProduct
    exact Finset.prod_pos fun h _ ↦ hDpos h
  have hPE : 0 < companionLcmProduct H e e' := by
    unfold companionLcmProduct
    exact Finset.prod_pos fun h _ ↦ hEpos h
  have hproduct :
      (largeGapCoordinateCrtModulus H d e d' e' : ℝ) *
          crossCoordinateGcdProduct H d e d' e' =
        (firstLcmProduct H d d' : ℝ) *
          companionLcmProduct H e e' := by
    exact_mod_cast largeGapCoordinateCrtModulus_mul_cross_eq_products hDD hEE
  rw [crossCoordinateTotientSumProduct_eq_crossGcd]
  have hMR : (largeGapCoordinateCrtModulus H d e d' e' : ℝ) ≠ 0 := by
    exact_mod_cast hM.ne'
  have hPDR : (firstLcmProduct H d d' : ℝ) ≠ 0 := by
    exact_mod_cast hPD.ne'
  have hPER : (companionLcmProduct H e e' : ℝ) ≠ 0 := by
    exact_mod_cast hPE.ne'
  field_simp [hMR, hPDR, hPER]
  nlinarith

/-! ## Rewriting the standard normalization kernel -/

/-- The doubled normalization kernel after replacing the reciprocal lcm
period by its full product of cross-coordinate divisor-totient sums. -/
noncomputable def doubledSelbergCrossTotientKernel
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (m q : ℕ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    if LargeGapCoordinateCrtCompatible H m q d e d' e' then
      lambda d e * lambda d' e' *
          crossCoordinateTotientSumProduct H d e d' e' /
        ((firstLcmProduct H d d' : ℝ) *
          companionLcmProduct H e e')
    else 0

/-- On the two ordinary Maynard supports, every compatible summand of the
general lcm kernel admits the exact auxiliary-divisor expansion. -/
theorem doubledSelbergCoordinateLcmKernel_eq_crossTotient_standard
    (H : Finset ℕ) (RD RE W m q : ℕ)
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (hm : 0 < m) (hq : q.Prime) (hRDq : RD ≤ q) (hREq : RE ≤ q)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W) :
    doubledSelbergCoordinateLcmKernel H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (fullySeparatedCompanionSupport H RE W m) lambda m q =
      doubledSelbergCrossTotientKernel H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (fullySeparatedCompanionSupport H RE W m) lambda m q := by
  classical
  unfold doubledSelbergCoordinateLcmKernel
    doubledSelbergCrossTotientKernel
  apply Finset.sum_congr rfl
  intro d hdMem
  apply Finset.sum_congr rfl
  intro e heMem
  apply Finset.sum_congr rfl
  intro d' hd'Mem
  apply Finset.sum_congr rfl
  intro e' he'Mem
  by_cases hc : LargeGapCoordinateCrtCompatible H m q d e d' e'
  · simp only [hc, if_true]
    have hd := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hdMem
    have hd' := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd'Mem
    have he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e := by
      exact BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support heMem
    have he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e' := by
      exact BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he'Mem
    have hcoverE : BoundedGaps.Maynard.CoversShiftDifferencePrimes H (W * m) := by
      intro a b hab p hp hpd
      exact dvd_mul_of_dvd_left (hcover hab p hp hpd) m
    have hmE : m.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e) :=
      Nat.Coprime.of_dvd_left (dvd_mul_left m W) he.2.1.symm
    have hmE' : m.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e') :=
      Nat.Coprime.of_dvd_left (dvd_mul_left m W) he'.2.1.symm
    have hqD : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H d) :=
      Nat.Coprime.of_dvd_left (dvd_mul_left q W)
        (prime_mul_modulus_coprime_tupleProduct hd hq hRDq)
    have hqD' : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H d') :=
      Nat.Coprime.of_dvd_left (dvd_mul_left q W)
        (prime_mul_modulus_coprime_tupleProduct hd' hq hRDq)
    have hqE : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e) :=
      Nat.Coprime.of_dvd_left (dvd_mul_left q (W * m))
        (prime_mul_modulus_coprime_tupleProduct he hq hREq)
    have hqE' : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e') :=
      Nat.Coprime.of_dvd_left (dvd_mul_left q (W * m))
        (prime_mul_modulus_coprime_tupleProduct he' hq hREq)
    obtain ⟨hDD, hEE⟩ := withinFamilyLcm_pairwise_of_coordinateCompatible
      hm hq.pos hd hd' he he' hcover hcoverE hmE hmE'
        hqD hqD' hqE hqE' hc
    have hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h) := fun h ↦
      Nat.lcm_pos (Nat.pos_of_ne_zero (hd.coordinate_squarefree h).ne_zero)
        (Nat.pos_of_ne_zero (hd'.coordinate_squarefree h).ne_zero)
    have hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h) := fun h ↦
      Nat.lcm_pos (Nat.pos_of_ne_zero (he.coordinate_squarefree h).ne_zero)
        (Nat.pos_of_ne_zero (he'.coordinate_squarefree h).ne_zero)
    rw [div_eq_mul_inv,
      inv_largeGapCoordinateCrtModulus_eq_cross_div_products
        hDpos hEpos hDD hEE]
    ring
  · simp [hc]

end

end Erdos4b
