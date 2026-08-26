/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralCollision
import ErdosProblems.Erdos4b.GeneralPinned
import BoundedGaps.Maynard.MaynardS2GDivisorExpansion

/-!
# The collision factor in the pinned prime kernel

The normalization sum uses the reciprocal of an lcm period.  After one
coordinate is pinned to a prime, the main term for the auxiliary prime uses
the reciprocal *totient* of exactly the same period.  For squarefree
within-family products, the identity

`φ(gcd D E) φ(lcm D E) = φ(D) φ(E)`

turns this into Maynard's `g(p)=p-2` common-divisor expansion.  This file
records that transformation without a separation hypothesis between the
first and companion divisor families.
-/

namespace Erdos4b

open scoped BigOperators

noncomputable section

noncomputable local instance erdos4PinnedCollisionPropDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The pinned CRT changes residues but not coordinate moduli. -/
theorem pinnedGeneralCrtModulus_eq_largeGapCoordinateCrtModulus
    (H : Finset ℕ) (d e d' e' : H → ℕ) :
    pinnedGeneralCrtModulus H d e d' e' =
      largeGapCoordinateCrtModulus H d e d' e' := by
  rfl

/-- A pinned coordinate residue has a subtraction-free affine
characterization.  This form remains valid for every auxiliary integer; no
margin assumption such as `h * W * q ≤ p` is needed. -/
theorem modEq_pinnedCoordinateResidue_iff_affine
    {H : Finset ℕ} {R W p q : ℕ} {d d' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d')
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    {h j : H} (hj : j ≠ h) :
    q ≡ pinnedCoordinateResidue p W h.1 j.1
          (Nat.lcm (d j) (d' j)) [MOD Nat.lcm (d j) (d' j)] ↔
      p + j.1 * (W * q) ≡ h.1 * (W * q)
        [MOD Nat.lcm (d j) (d' j)] := by
  let l := Nat.lcm (d j) (d' j)
  have hl : 0 < l := by
    simpa [l, BoundedGaps.Maynard.divisorTupleLcm] using
      (BoundedGaps.Maynard.divisorTupleLcm_pos_of_isMaynard hd hd' j)
  by_cases hhj : h.1 ≤ j.1
  · have hlt : h.1 < j.1 := lt_of_le_of_ne hhj (by
      intro heq
      exact hj (Subtype.ext heq.symm))
    let c := W * (j.1 - h.1)
    have hdist : Nat.dist j.1 h.1 = j.1 - h.1 := by
      rw [Nat.dist_comm]
      exact Nat.dist_eq_sub_of_le hhj
    have hcop : c.Coprime l := by
      simpa [c, l, BoundedGaps.Maynard.divisorTupleLcm, hdist] using
        (pinned_coefficient_coprime_lcm hd hd' hcover hj)
    have hshift (x : ℕ) :
        j.1 * (W * x) = h.1 * (W * x) + c * x := by
      have hjdecomp : j.1 = h.1 + (j.1 - h.1) := by omega
      calc
        j.1 * (W * x) = (h.1 + (j.1 - h.1)) * (W * x) := by
          exact congrArg (fun z : ℕ ↦ z * (W * x)) hjdecomp
        _ = h.1 * (W * x) + c * x := by
          dsimp [c]
          ring
    rw [pinnedCoordinateResidue, if_pos hhj]
    let r := negativeLinearResidue c p l
    have hspec : c * r + p ≡ 0 [MOD l] :=
      negativeLinearResidue_spec hl hcop
    constructor
    · intro hq
      have hc : c * q + p ≡ 0 [MOD l] :=
        ((hq.mul_left c).add_right p).trans hspec
      have hadd := hc.add_left (h.1 * (W * q))
      simpa [r, l, hshift, add_assoc, add_comm, add_left_comm] using hadd
    · intro haff
      have hadd : h.1 * (W * q) + (c * q + p) ≡
          h.1 * (W * q) + 0 [MOD l] := by
        simpa [hshift, add_assoc, add_comm, add_left_comm] using haff
      have hc : c * q + p ≡ 0 [MOD l] :=
        Nat.ModEq.add_left_cancel' _ hadd
      have hmul : c * q ≡ c * r [MOD l] :=
        Nat.ModEq.add_right_cancel' p (hc.trans hspec.symm)
      exact Nat.ModEq.cancel_left_of_coprime hcop.symm hmul
  · have hjh : j.1 < h.1 := lt_of_not_ge hhj
    let c := W * (h.1 - j.1)
    have hdist : Nat.dist j.1 h.1 = h.1 - j.1 :=
      Nat.dist_eq_sub_of_le hjh.le
    have hcop : c.Coprime l := by
      simpa [c, l, BoundedGaps.Maynard.divisorTupleLcm, hdist] using
        (pinned_coefficient_coprime_lcm hd hd' hcover hj)
    have hshift (x : ℕ) :
        h.1 * (W * x) = j.1 * (W * x) + c * x := by
      have hhdecomp : h.1 = j.1 + (h.1 - j.1) := by omega
      calc
        h.1 * (W * x) = (j.1 + (h.1 - j.1)) * (W * x) := by
          exact congrArg (fun z : ℕ ↦ z * (W * x)) hhdecomp
        _ = j.1 * (W * x) + c * x := by
          dsimp [c]
          ring
    rw [pinnedCoordinateResidue, if_neg hhj]
    let r := positiveLinearResidue c p l
    have hspec : c * r ≡ p [MOD l] :=
      positiveLinearResidue_spec hl hcop
    constructor
    · intro hq
      have hc : c * q ≡ p [MOD l] := (hq.mul_left c).trans hspec
      have hadd := hc.add_left (j.1 * (W * q))
      simpa [r, l, hshift, add_assoc, add_comm, add_left_comm] using hadd.symm
    · intro haff
      have hadd : j.1 * (W * q) + p ≡
          j.1 * (W * q) + c * q [MOD l] := by
        simpa [hshift, add_assoc, add_comm, add_left_comm] using haff
      have hc : p ≡ c * q [MOD l] :=
        Nat.ModEq.add_left_cancel' _ hadd
      have hmul : c * q ≡ c * r [MOD l] := hc.symm.trans hspec.symm
      exact Nat.ModEq.cancel_left_of_coprime hcop.symm hmul

/-- A common reduced solution of all pinned residues forces the lcm moduli
inside that family to be pairwise coprime.  The proof subtracts the two
affine congruences: their gcd divides `W * dist a b * r`, while the Maynard
support and reducedness make that product coprime to the gcd. -/
theorem pinnedLcmFamily_pairwise_of_reduced_solution
    {H : Finset ℕ} {R W x r M : ℕ} {d d' : H → ℕ}
    (h : H)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d')
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hdh : d h = 1) (hd'h : d' h = 1)
    (hrM : r.Coprime M)
    (hDM : ∀ a : H, Nat.lcm (d a) (d' a) ∣ M)
    (hr : ∀ a : H,
      r ≡ (if a = h then 0 else
        pinnedCoordinateResidue x W h.1 a.1
          (Nat.lcm (d a) (d' a))) [MOD Nat.lcm (d a) (d' a)]) :
    ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)) := by
  intro a b hab
  by_cases ha : a = h
  · subst a
    simp [hdh, hd'h]
  by_cases hb : b = h
  · subst b
    simp [hdh, hd'h]
  let Da := Nat.lcm (d a) (d' a)
  let Db := Nat.lcm (d b) (d' b)
  let g := Nat.gcd Da Db
  have hra : r ≡ pinnedCoordinateResidue x W h.1 a.1 Da [MOD Da] := by
    simpa [Da, ha] using hr a
  have hrb : r ≡ pinnedCoordinateResidue x W h.1 b.1 Db [MOD Db] := by
    simpa [Db, hb] using hr b
  have hxa : x + a.1 * (W * r) ≡ h.1 * (W * r) [MOD Da] :=
    (modEq_pinnedCoordinateResidue_iff_affine hd hd' hcover ha).mp hra
  have hxb : x + b.1 * (W * r) ≡ h.1 * (W * r) [MOD Db] :=
    (modEq_pinnedCoordinateResidue_iff_affine hd hd' hcover hb).mp hrb
  have hxab : x + a.1 * (W * r) ≡ x + b.1 * (W * r) [MOD g] :=
    (hxa.of_dvd (Nat.gcd_dvd_left Da Db)).trans
      (hxb.of_dvd (Nat.gcd_dvd_right Da Db)).symm
  have habmod : a.1 * (W * r) ≡ b.1 * (W * r) [MOD g] :=
    Nat.ModEq.add_left_cancel' x hxab
  have hgM : g ∣ M :=
    (Nat.gcd_dvd_left Da Db).trans (hDM a)
  have hrg : r.Coprime g := Nat.Coprime.of_dvd_right hgM hrM
  have hVdistDb : (W * Nat.dist b.1 a.1).Coprime Db := by
    simpa [BoundedGaps.Maynard.divisorTupleLcm] using
      (pinned_coefficient_coprime_lcm hd hd' hcover hab.symm)
  have hVdistg : (W * Nat.dist b.1 a.1).Coprime g :=
    Nat.Coprime.of_dvd_right (Nat.gcd_dvd_right Da Db) hVdistDb
  have hprodCop : ((W * Nat.dist b.1 a.1) * r).Coprime g :=
    hVdistg.mul_left hrg
  have hgdiv : g ∣ (W * Nat.dist b.1 a.1) * r := by
    rcases le_total a.1 b.1 with habval | hbaval
    · have hle : a.1 * (W * r) ≤ b.1 * (W * r) :=
        Nat.mul_le_mul_right (W * r) habval
      have hdifference := (Nat.modEq_iff_dvd' hle).mp habmod
      have hdist : Nat.dist b.1 a.1 = b.1 - a.1 := by
        rw [Nat.dist_comm]
        exact Nat.dist_eq_sub_of_le habval
      rw [hdist, show W * (b.1 - a.1) * r =
        (b.1 - a.1) * (W * r) by ring, Nat.sub_mul]
      exact hdifference
    · have hle : b.1 * (W * r) ≤ a.1 * (W * r) :=
        Nat.mul_le_mul_right (W * r) hbaval
      have hdifference := (Nat.modEq_iff_dvd' hle).mp habmod.symm
      have hdist : Nat.dist b.1 a.1 = a.1 - b.1 :=
        Nat.dist_eq_sub_of_le hbaval
      rw [hdist, show W * (a.1 - b.1) * r =
        (a.1 - b.1) * (W * r) by ring, Nat.sub_mul]
      exact hdifference
  have hgOne : g = 1 :=
    Nat.eq_one_of_dvd_coprimes hprodCop hgdiv (dvd_refl g)
  exact hgOne

/-- Every restricted supported pinned quadruple has pairwise-coprime lcms
inside both divisor families.  This discharges the structural premise of
the reciprocal-totient expansion from the canonical reduced CRT residue. -/
theorem withinFamilyLcm_pairwise_of_pinnedGeneralRestricted
    {H : Finset ℕ} {RD RE W m p Y : ℕ} (h : H)
    {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hp : p.Prime) (hRDp : RD ≤ p) (hREY : RE ≤ Y)
    (hpre : largeGapPreSieved Y m p)
    (hrest : PinnedGeneralRestricted W m p h d e d' e') :
    (∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b))) ∧
    (∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b))) := by
  let hc : PinnedGeneralCrtCompatible H p W m h d e d' e' :=
    hrest.2.2.2.2
  let M := pinnedGeneralCrtModulus H d e d' e'
  let r := pinnedGeneralCrtResidue H p W m h d e d' e' hc
  have hrM : r.Coprime M :=
    pinnedGeneralCrtResidue_coprime_modulus h hd hd' he he' hcover
      hrest.1 hrest.2.1 hrest.2.2.1 hrest.2.2.2.1 hp hRDp hREY hpre hc
  have hDM : ∀ a : H, Nat.lcm (d a) (d' a) ∣ M := by
    intro a
    exact Finset.dvd_lcm
      (s := (Finset.univ : Finset (PinnedGeneralCrtIndex H)))
      (f := pinnedGeneralCrtCoordinateModulus H d e d' e')
      (b := Sum.inl a) (by simp)
  have hEM : ∀ b : H, Nat.lcm (e b) (e' b) ∣ M := by
    intro b
    exact Finset.dvd_lcm
      (s := (Finset.univ : Finset (PinnedGeneralCrtIndex H)))
      (f := pinnedGeneralCrtCoordinateModulus H d e d' e')
      (b := Sum.inr b) (by simp)
  have hrD : ∀ a : H,
      r ≡ (if a = h then 0 else
        pinnedCoordinateResidue p W h.1 a.1
          (Nat.lcm (d a) (d' a))) [MOD Nat.lcm (d a) (d' a)] := by
    intro a
    simpa [r, hc, pinnedGeneralCrtResidue,
      pinnedGeneralCrtCoordinateModulus,
      pinnedGeneralCrtCoordinateResidue, largeGapCrtModulus,
      BoundedGaps.Maynard.divisorTupleLcm] using
      (generalCrtResidue_spec Finset.univ
        (pinnedGeneralCrtCoordinateModulus H d e d' e')
        (pinnedGeneralCrtCoordinateResidue H p W m h d e d' e') hc
        (Sum.inl a) (by simp))
  have hrE : ∀ b : H,
      r ≡ (if b = h then 0 else
        pinnedCoordinateResidue (m * p - 1) (W * m) h.1 b.1
          (Nat.lcm (e b) (e' b))) [MOD Nat.lcm (e b) (e' b)] := by
    intro b
    simpa [r, hc, pinnedGeneralCrtResidue,
      pinnedGeneralCrtCoordinateModulus,
      pinnedGeneralCrtCoordinateResidue, largeGapCrtModulus,
      BoundedGaps.Maynard.divisorTupleLcm] using
      (generalCrtResidue_spec Finset.univ
        (pinnedGeneralCrtCoordinateModulus H d e d' e')
        (pinnedGeneralCrtCoordinateResidue H p W m h d e d' e') hc
        (Sum.inr b) (by simp))
  have hcoverWM :
      BoundedGaps.Maynard.CoversShiftDifferencePrimes H (W * m) :=
    coversShiftDifferencePrimes_of_dvd (dvd_mul_right W m) hcover
  exact ⟨
    pinnedLcmFamily_pairwise_of_reduced_solution h hd hd' hcover
      hrest.1 hrest.2.1 hrM hDM hrD,
    pinnedLcmFamily_pairwise_of_reduced_solution h he he' hcoverWM
      hrest.2.2.1 hrest.2.2.2.1 hrM hEM hrE⟩

/-- A pairwise-coprime product of squarefree first-family lcms is
squarefree. -/
theorem squarefree_firstLcmProduct_of_pairwise
    {H : Finset ℕ} {d d' : H → ℕ}
    (hsq : ∀ a : H, Squarefree (Nat.lcm (d a) (d' a)))
    (hpair : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b))) :
    Squarefree (firstLcmProduct H d d') := by
  classical
  unfold firstLcmProduct
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro a ha b hb hab
    exact Nat.coprime_iff_isRelPrime.mp (hpair hab)
  · intro a ha
    exact hsq a

/-- Companion-family version of
`squarefree_firstLcmProduct_of_pairwise`. -/
theorem squarefree_companionLcmProduct_of_pairwise
    {H : Finset ℕ} {e e' : H → ℕ}
    (hsq : ∀ b : H, Squarefree (Nat.lcm (e b) (e' b)))
    (hpair : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b))) :
    Squarefree (companionLcmProduct H e e') := by
  classical
  unfold companionLcmProduct
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro a ha b hb hab
    exact Nat.coprime_iff_isRelPrime.mp (hpair hab)
  · intro b hb
    exact hsq b

/-- The finite `g(p)=p-2` divisor sum attached to the aggregate cross gcd. -/
noncomputable def crossCoordinateS2GAggregate
    (H : Finset ℕ) (d e d' e' : H → ℕ) : ℝ :=
  BoundedGaps.Maynard.commonDivisorS2GSum
    (firstLcmProduct H d d') (companionLcmProduct H e e')

/-- The aggregate `g` factor is already a literal finite auxiliary-divisor
sum.  The matrix form is a further multiplicative reindexing of this sum. -/
theorem crossCoordinateS2GAggregate_eq_divisorSum
    (H : Finset ℕ) (d e d' e' : H → ℕ) :
    crossCoordinateS2GAggregate H d e d' e' =
      ∑ u : ↑(Nat.gcd (firstLcmProduct H d d')
        (companionLcmProduct H e e')).divisors,
          (BoundedGaps.Maynard.maynardS2G u.1 : ℝ) := by
  classical
  unfold crossCoordinateS2GAggregate
    BoundedGaps.Maynard.commonDivisorS2GSum
  exact (Finset.sum_attach
    (Nat.gcd (firstLcmProduct H d d')
      (companionLcmProduct H e e')).divisors
    (fun u ↦ (BoundedGaps.Maynard.maynardS2G u : ℝ))).symm

/-- Coordinatewise form of the pinned cross-collision `g` factor. -/
noncomputable def crossCoordinateS2GSumProduct
    (H : Finset ℕ) (d e d' e' : H → ℕ) : ℝ :=
  ∏ b : H, ∏ a : H,
    BoundedGaps.Maynard.commonDivisorS2GSum
      (Nat.lcm (d a) (d' a)) (Nat.lcm (e b) (e' b))

/-- Distinct cross gcds are coprime whenever each of the two underlying lcm
families is pairwise coprime. -/
theorem crossCoordinateGcd_pairwise
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b))) :
    Set.Pairwise ((Finset.univ : Finset (H × H)) : Set (H × H))
      (Nat.Coprime.onFun (fun ba ↦
        Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
          (Nat.lcm (e ba.1) (e' ba.1)))) := by
  intro x hx y hy hxy
  by_cases hfirst : x.1 = y.1
  · have hsecond : x.2 ≠ y.2 := by
      intro hs
      apply hxy
      exact Prod.ext hfirst hs
    exact Nat.Coprime.of_dvd
      (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _) (hDD hsecond)
  · exact Nat.Coprime.of_dvd
      (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _) (hEE hfirst)

/-- The totient of the aggregate cross gcd factors coordinatewise. -/
theorem totient_crossCoordinateGcdProduct_eq_product
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b))) :
    Nat.totient (crossCoordinateGcdProduct H d e d' e') =
      ∏ b : H, ∏ a : H,
        Nat.totient (Nat.gcd (Nat.lcm (d a) (d' a))
          (Nat.lcm (e b) (e' b))) := by
  classical
  unfold crossCoordinateGcdProduct
  let f : H × H → ℕ := fun ba ↦
    Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
      (Nat.lcm (e ba.1) (e' ba.1))
  have htot : Nat.totient (∏ ba : H × H, f ba) =
      ∏ ba : H × H, Nat.totient (f ba) :=
    by simpa using
      (BoundedGaps.Maynard.totient_finsetProd_of_pairwise_coprime
        (Finset.univ : Finset (H × H)) f
        (crossCoordinateGcd_pairwise hDD hEE))
  calc
    Nat.totient (∏ b : H, ∏ a : H,
        Nat.gcd (Nat.lcm (d a) (d' a)) (Nat.lcm (e b) (e' b))) =
        Nat.totient (∏ ba : H × H, f ba) := by
          exact congrArg Nat.totient (Fintype.prod_prod_type f).symm
    _ = ∏ ba : H × H, Nat.totient (f ba) := htot
    _ = ∏ b : H, ∏ a : H,
        Nat.totient (Nat.gcd (Nat.lcm (d a) (d' a))
          (Nat.lcm (e b) (e' b))) := by
          exact Fintype.prod_prod_type (fun ba : H × H ↦ Nat.totient (f ba))

/-- Aggregate and matrix forms of Maynard's pinned `g(p)=p-2` factor agree
exactly. -/
theorem crossCoordinateS2GAggregate_eq_product
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDsq : ∀ a : H, Squarefree (Nat.lcm (d a) (d' a)))
    (hEsq : ∀ b : H, Squarefree (Nat.lcm (e b) (e' b)))
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b))) :
    crossCoordinateS2GAggregate H d e d' e' =
      crossCoordinateS2GSumProduct H d e d' e' := by
  classical
  have hPDsq : Squarefree (firstLcmProduct H d d') :=
    squarefree_firstLcmProduct_of_pairwise hDsq hDD
  have hPEsq : Squarefree (companionLcmProduct H e e') :=
    squarefree_companionLcmProduct_of_pairwise hEsq hEE
  have hgcdsq : Squarefree (Nat.gcd (firstLcmProduct H d d')
      (companionLcmProduct H e e')) :=
    hPDsq.squarefree_of_dvd (Nat.gcd_dvd_left _ _)
  have haggregate : crossCoordinateS2GAggregate H d e d' e' =
      (Nat.totient (Nat.gcd (firstLcmProduct H d d')
        (companionLcmProduct H e e')) : ℝ) := by
    unfold crossCoordinateS2GAggregate
      BoundedGaps.Maynard.commonDivisorS2GSum
    exact_mod_cast
      BoundedGaps.Maynard.sum_maynardS2G_divisors_eq_totient hgcdsq
  rw [haggregate,
    gcd_firstLcmProduct_companionLcmProduct_eq_cross hDD hEE,
    totient_crossCoordinateGcdProduct_eq_product hDD hEE]
  unfold crossCoordinateS2GSumProduct
  push_cast
  apply Finset.prod_congr rfl
  intro b hb
  apply Finset.prod_congr rfl
  intro a ha
  have hgsq : Squarefree (Nat.gcd (Nat.lcm (d a) (d' a))
      (Nat.lcm (e b) (e' b))) :=
    (hDsq a).squarefree_of_dvd (Nat.gcd_dvd_left _ _)
  unfold BoundedGaps.Maynard.commonDivisorS2GSum
  exact_mod_cast
    (BoundedGaps.Maynard.sum_maynardS2G_divisors_eq_totient hgsq).symm

/-- Multiplicative `g`-weight of an auxiliary-divisor matrix. -/
noncomputable def crossAuxiliaryS2GWeight
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (a : CrossAuxiliaryDivisors H d e d' e') : ℝ :=
  ∏ ba : H × H, (BoundedGaps.Maynard.maynardS2G (a ba).1 : ℝ)

/-- Fully expanded matrix form of the coordinatewise pinned collision
factor. -/
theorem crossCoordinateS2GSumProduct_eq_auxiliarySum
    (H : Finset ℕ) (d e d' e' : H → ℕ) :
    crossCoordinateS2GSumProduct H d e d' e' =
      ∑ a : CrossAuxiliaryDivisors H d e d' e',
        crossAuxiliaryS2GWeight a := by
  classical
  unfold crossCoordinateS2GSumProduct crossAuxiliaryS2GWeight
    BoundedGaps.Maynard.commonDivisorS2GSum
  rw [← Fintype.prod_prod_type (fun ba : H × H ↦
    ∑ u ∈ (Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
      (Nat.lcm (e ba.1) (e' ba.1))).divisors,
        (BoundedGaps.Maynard.maynardS2G u : ℝ))]
  have hprod :
      (∏ ba : H × H,
        ∑ u ∈ (Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
          (Nat.lcm (e ba.1) (e' ba.1))).divisors,
            (BoundedGaps.Maynard.maynardS2G u : ℝ)) =
        ∏ ba : H × H,
          ∑ u : ↑(Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
            (Nat.lcm (e ba.1) (e' ba.1))).divisors,
              (BoundedGaps.Maynard.maynardS2G u.1 : ℝ) := by
    apply Finset.prod_congr rfl
    intro ba hba
    exact (Finset.sum_attach
      (Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1))).divisors
      (fun u ↦ (BoundedGaps.Maynard.maynardS2G u : ℝ))).symm
  rw [hprod]
  exact Fintype.prod_sum (fun ba : H × H => fun u :
    ↑(Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
      (Nat.lcm (e ba.1) (e' ba.1))).divisors =>
        (BoundedGaps.Maynard.maynardS2G u.1 : ℝ))

/-- Exact reciprocal-totient collision identity for the pinned CRT period.
The hypotheses are precisely the squarefree and within-family coprimality
facts that hold for a nonzero supported pinned summand. -/
theorem inv_totient_pinnedGeneralCrtModulus_eq_s2G_div_products
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ a : H, 0 < Nat.lcm (d a) (d' a))
    (hEpos : ∀ b : H, 0 < Nat.lcm (e b) (e' b))
    (hDsq : ∀ a : H, Squarefree (Nat.lcm (d a) (d' a)))
    (hEsq : ∀ b : H, Squarefree (Nat.lcm (e b) (e' b)))
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b))) :
    ((Nat.totient (pinnedGeneralCrtModulus H d e d' e') : ℝ)⁻¹) =
      crossCoordinateS2GAggregate H d e d' e' /
        ((Nat.totient (firstLcmProduct H d d') : ℝ) *
          Nat.totient (companionLcmProduct H e e')) := by
  have hPDsq : Squarefree (firstLcmProduct H d d') :=
    squarefree_firstLcmProduct_of_pairwise hDsq hDD
  have hPEsq : Squarefree (companionLcmProduct H e e') :=
    squarefree_companionLcmProduct_of_pairwise hEsq hEE
  have hPDpos : 0 < firstLcmProduct H d d' := by
    unfold firstLcmProduct
    exact Finset.prod_pos fun a _ ↦ hDpos a
  have hPEpos : 0 < companionLcmProduct H e e' := by
    unfold companionLcmProduct
    exact Finset.prod_pos fun b _ ↦ hEpos b
  rw [pinnedGeneralCrtModulus_eq_largeGapCoordinateCrtModulus,
    largeGapCoordinateCrtModulus_eq_lcm_products hDpos hEpos hDD hEE]
  exact BoundedGaps.Maynard.inv_totient_lcm_eq_maynardS2G_sum_div_mul
    hPDsq hPEsq hPDpos hPEpos

/-- The pinned kernel after replacing each reciprocal totient by the exact
aggregate `g(p)=p-2` cross-collision divisor sum. -/
noncomputable def pinnedGeneralS2GCollisionKernel
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (W m p : ℕ) : ℝ :=
  ∑ h : H, ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    if PinnedGeneralRestricted W m p h d e d' e' then
      lambda d e * lambda d' e' *
          crossCoordinateS2GAggregate H d e d' e' /
        ((Nat.totient (firstLcmProduct H d d') : ℝ) *
          Nat.totient (companionLcmProduct H e e'))
    else 0

/-- Generic kernel rewrite.  The supplied implication isolates the exact
remaining structural obligation: every nonzero restricted summand has
pairwise-coprime lcms inside each of its two divisor families. -/
theorem pinnedGeneralArithmeticKernel_eq_s2GCollisionKernel
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (W m p : ℕ)
    (hDtuple : ∀ d ∈ D, ∃ R,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (hEtuple : ∀ e ∈ E, ∃ R,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H R (W * m) e)
    (hpair : ∀ (h : H) (d : H → ℕ) (_hd : d ∈ D)
        (e : H → ℕ) (_he : e ∈ E) (d' : H → ℕ) (_hd' : d' ∈ D)
        (e' : H → ℕ) (_he' : e' ∈ E),
      PinnedGeneralRestricted W m p h d e d' e' →
        (∀ {a b : H}, a ≠ b →
          (Nat.lcm (d a) (d' a)).Coprime
            (Nat.lcm (d b) (d' b))) ∧
        (∀ {a b : H}, a ≠ b →
          (Nat.lcm (e a) (e' a)).Coprime
            (Nat.lcm (e b) (e' b)))) :
    pinnedGeneralArithmeticKernel H D E lambda W m p =
      pinnedGeneralS2GCollisionKernel H D E lambda W m p := by
  classical
  unfold pinnedGeneralArithmeticKernel pinnedGeneralS2GCollisionKernel
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro d hdMem
  apply Finset.sum_congr rfl
  intro e heMem
  apply Finset.sum_congr rfl
  intro d' hd'Mem
  apply Finset.sum_congr rfl
  intro e' he'Mem
  by_cases hr : PinnedGeneralRestricted W m p h d e d' e'
  · simp only [hr, if_true]
    obtain ⟨RD, hd⟩ := hDtuple d hdMem
    obtain ⟨RD', hd'⟩ := hDtuple d' hd'Mem
    obtain ⟨RE, he⟩ := hEtuple e heMem
    obtain ⟨RE', he'⟩ := hEtuple e' he'Mem
    obtain ⟨hDD, hEE⟩ := hpair h d hdMem e heMem d' hd'Mem e' he'Mem hr
    have hDpos : ∀ a : H, 0 < Nat.lcm (d a) (d' a) := fun a ↦
      Nat.lcm_pos (Nat.pos_of_ne_zero (hd.coordinate_squarefree a).ne_zero)
        (Nat.pos_of_ne_zero (hd'.coordinate_squarefree a).ne_zero)
    have hEpos : ∀ b : H, 0 < Nat.lcm (e b) (e' b) := fun b ↦
      Nat.lcm_pos (Nat.pos_of_ne_zero (he.coordinate_squarefree b).ne_zero)
        (Nat.pos_of_ne_zero (he'.coordinate_squarefree b).ne_zero)
    have hDsq : ∀ a : H, Squarefree (Nat.lcm (d a) (d' a)) := fun a ↦
      BoundedGaps.Maynard.squarefree_lcm
        (hd.coordinate_squarefree a) (hd'.coordinate_squarefree a)
    have hEsq : ∀ b : H, Squarefree (Nat.lcm (e b) (e' b)) := fun b ↦
      BoundedGaps.Maynard.squarefree_lcm
        (he.coordinate_squarefree b) (he'.coordinate_squarefree b)
    rw [div_eq_mul_inv,
      inv_totient_pinnedGeneralCrtModulus_eq_s2G_div_products
        hDpos hEpos hDsq hEsq hDD hEE]
    ring
  · simp [hr]

/-- Concrete arbitrary-overlap pinned kernel rewrite on the two ordinary
Maynard supports.  All hypotheses now concern only the target prime and the
standard pre-sieve; no abstract collision premise remains. -/
theorem pinnedGeneralArithmeticKernel_eq_s2GCollisionKernel_standard
    (H : Finset ℕ) (RD RE W m p Y : ℕ)
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hp : p.Prime) (hRDp : RD ≤ p) (hREY : RE ≤ Y)
    (hpre : largeGapPreSieved Y m p) :
    pinnedGeneralArithmeticKernel H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
        lambda W m p =
      pinnedGeneralS2GCollisionKernel H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
        lambda W m p := by
  apply pinnedGeneralArithmeticKernel_eq_s2GCollisionKernel
  · intro d hd
    exact ⟨RD,
      BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd⟩
  · intro e he
    exact ⟨RE,
      BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he⟩
  · intro h d hdMem e heMem d' hd'Mem e' he'Mem hrest
    exact withinFamilyLcm_pairwise_of_pinnedGeneralRestricted h
      (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hdMem)
      (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd'Mem)
      (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support heMem)
      (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he'Mem)
      hcover hp hRDp hREY hpre hrest

/-- Coordinate-matrix version of the pinned `g`-collision kernel. -/
noncomputable def pinnedGeneralS2GMatrixKernel
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (W m p : ℕ) : ℝ :=
  ∑ h : H, ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    if PinnedGeneralRestricted W m p h d e d' e' then
      lambda d e * lambda d' e' *
          crossCoordinateS2GSumProduct H d e d' e' /
        ((Nat.totient (firstLcmProduct H d d') : ℝ) *
          Nat.totient (companionLcmProduct H e e'))
    else 0

/-- Literal auxiliary-matrix version of the pinned collision kernel. -/
noncomputable def pinnedGeneralS2GAuxiliaryKernel
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (W m p : ℕ) : ℝ :=
  ∑ h : H, ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    if PinnedGeneralRestricted W m p h d e d' e' then
      lambda d e * lambda d' e' *
          (∑ a : CrossAuxiliaryDivisors H d e d' e',
            crossAuxiliaryS2GWeight a) /
        ((Nat.totient (firstLcmProduct H d d') : ℝ) *
          Nat.totient (companionLcmProduct H e e'))
    else 0

/-- On standard supports, aggregate and coordinate-matrix pinned kernels
are identical. -/
theorem pinnedGeneralS2GCollisionKernel_eq_matrix_standard
    (H : Finset ℕ) (RD RE W m p Y : ℕ)
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hp : p.Prime) (hRDp : RD ≤ p) (hREY : RE ≤ Y)
    (hpre : largeGapPreSieved Y m p) :
    pinnedGeneralS2GCollisionKernel H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
        lambda W m p =
      pinnedGeneralS2GMatrixKernel H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
        lambda W m p := by
  classical
  unfold pinnedGeneralS2GCollisionKernel pinnedGeneralS2GMatrixKernel
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro d hdMem
  apply Finset.sum_congr rfl
  intro e heMem
  apply Finset.sum_congr rfl
  intro d' hd'Mem
  apply Finset.sum_congr rfl
  intro e' he'Mem
  by_cases hr : PinnedGeneralRestricted W m p h d e d' e'
  · simp only [hr, if_true]
    let hd := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hdMem
    let hd' := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd'Mem
    let he := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support heMem
    let he' := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he'Mem
    obtain ⟨hDD, hEE⟩ :=
      withinFamilyLcm_pairwise_of_pinnedGeneralRestricted h hd hd' he he'
        hcover hp hRDp hREY hpre hr
    have hDsq : ∀ a : H, Squarefree (Nat.lcm (d a) (d' a)) := fun a ↦
      BoundedGaps.Maynard.squarefree_lcm
        (hd.coordinate_squarefree a) (hd'.coordinate_squarefree a)
    have hEsq : ∀ b : H, Squarefree (Nat.lcm (e b) (e' b)) := fun b ↦
      BoundedGaps.Maynard.squarefree_lcm
        (he.coordinate_squarefree b) (he'.coordinate_squarefree b)
    rw [crossCoordinateS2GAggregate_eq_product hDsq hEsq hDD hEE]
  · simp [hr]

/-- The coordinate product expands exactly into the finite auxiliary matrix
sum, with no asymptotic estimate. -/
theorem pinnedGeneralS2GMatrixKernel_eq_auxiliaryKernel
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (W m p : ℕ) :
    pinnedGeneralS2GMatrixKernel H D E lambda W m p =
      pinnedGeneralS2GAuxiliaryKernel H D E lambda W m p := by
  classical
  unfold pinnedGeneralS2GMatrixKernel pinnedGeneralS2GAuxiliaryKernel
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro d hdMem
  apply Finset.sum_congr rfl
  intro e heMem
  apply Finset.sum_congr rfl
  intro d' hd'Mem
  apply Finset.sum_congr rfl
  intro e' he'Mem
  by_cases hr : PinnedGeneralRestricted W m p h d e d' e'
  · simp only [hr, if_true]
    rw [crossCoordinateS2GSumProduct_eq_auxiliarySum]
  · simp [hr]

/-- End-to-end exact pinned main-kernel expansion on the two standard
Maynard supports. -/
theorem pinnedGeneralArithmeticKernel_eq_s2GAuxiliaryKernel_standard
    (H : Finset ℕ) (RD RE W m p Y : ℕ)
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hp : p.Prime) (hRDp : RD ≤ p) (hREY : RE ≤ Y)
    (hpre : largeGapPreSieved Y m p) :
    pinnedGeneralArithmeticKernel H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
        lambda W m p =
      pinnedGeneralS2GAuxiliaryKernel H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
        lambda W m p := by
  rw [pinnedGeneralArithmeticKernel_eq_s2GCollisionKernel_standard
    H RD RE W m p Y lambda hcover hp hRDp hREY hpre]
  rw [pinnedGeneralS2GCollisionKernel_eq_matrix_standard
    H RD RE W m p Y lambda hcover hp hRDp hREY hpre]
  exact pinnedGeneralS2GMatrixKernel_eq_auxiliaryKernel
    H _ _ lambda W m p

end

end Erdos4b
