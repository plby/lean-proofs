import ErdosProblems.Erdos248.Extraction
import BoundedGaps.Maynard.MaynardS2CoordinateFiberScalarization

/-!
# Erdős Problem 248: adjoining one prime to a divisor tuple

The correlation estimates repeatedly separate the terms in the Selberg
divisor sum according to whether a fixed prime occurs in one coordinate.
This file records the elementary tuple algebra used by that separation.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

local instance primeTransformDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Multiply one coordinate of a divisor tuple by `p`. -/
def insertTuplePrime {H : Finset ℕ} (p : ℕ) (h : H)
    (r : H → ℕ) : H → ℕ :=
  Function.update r h (p * r h)

/-- Divide one coordinate of a tuple by `p`.  It is used only under a
divisibility hypothesis. -/
def removeTuplePrime {H : Finset ℕ} (p : ℕ) (h : H)
    (r : H → ℕ) : H → ℕ :=
  Function.update r h (r h / p)

@[simp] theorem insertTuplePrime_apply_same {H : Finset ℕ} (p : ℕ)
    (h : H) (r : H → ℕ) :
    insertTuplePrime p h r h = p * r h := by
  simp [insertTuplePrime]

@[simp] theorem insertTuplePrime_apply_ne {H : Finset ℕ} (p : ℕ)
    {h i : H} (hi : i ≠ h) (r : H → ℕ) :
    insertTuplePrime p h r i = r i := by
  simp [insertTuplePrime, hi]

theorem divisorTupleProduct_insertTuplePrime {H : Finset ℕ} (p : ℕ)
    (h : H) (r : H → ℕ) :
    divisorTupleProduct H (insertTuplePrime p h r) =
      p * divisorTupleProduct H r := by
  classical
  unfold divisorTupleProduct insertTuplePrime
  rw [Finset.prod_update_of_mem (Finset.mem_univ h)]
  rw [← Finset.mul_prod_erase Finset.univ r (Finset.mem_univ h)]
  simp only [Finset.sdiff_singleton_eq_erase]
  ring

theorem coordinateTotientProduct_insertTuplePrime {H : Finset ℕ}
    {p : ℕ} (hp : p.Prime) (h : H) (r : H → ℕ)
    (hcop : Nat.Coprime p (divisorTupleProduct H r)) :
    (∏ i : H, Nat.totient (insertTuplePrime p h r i)) =
      (p - 1) * ∏ i : H, Nat.totient (r i) := by
  classical
  have hcopCoord : Nat.Coprime p (r h) := by
    exact hcop.coprime_dvd_right (divisorTupleCoordinate_dvd_product r h)
  have hfun :
      (fun i : H => Nat.totient (insertTuplePrime p h r i)) =
        Function.update (fun i : H => Nat.totient (r i)) h
          (Nat.totient (p * r h)) := by
    funext i
    by_cases hi : i = h
    · subst i
      simp
    · simp [insertTuplePrime, hi]
  rw [hfun]
  rw [Finset.prod_update_of_mem (Finset.mem_univ h)]
  rw [Nat.totient_mul hcopCoord]
  rw [Nat.totient_prime hp]
  rw [← Finset.mul_prod_erase Finset.univ (fun i : H => Nat.totient (r i))
    (Finset.mem_univ h)]
  simp only [Finset.sdiff_singleton_eq_erase]
  ring

theorem insertTuplePrime_injective {H : Finset ℕ} {p : ℕ}
    (hp : 0 < p) (h : H) :
    Function.Injective (insertTuplePrime p h : (H → ℕ) → (H → ℕ)) := by
  intro r s hrs
  funext i
  by_cases hi : i = h
  · subst i
    have := congrFun hrs h
    simp only [insertTuplePrime_apply_same] at this
    exact Nat.eq_of_mul_eq_mul_left hp this
  · have := congrFun hrs i
    simpa [insertTuplePrime, hi] using this

theorem insertTuplePrime_removeTuplePrime {H : Finset ℕ} {p : ℕ}
    (h : H) (r : H → ℕ) (hp : p ∣ r h) :
    insertTuplePrime p h (removeTuplePrime p h r) = r := by
  funext i
  by_cases hi : i = h
  · subst i
    simp [insertTuplePrime, removeTuplePrime, Nat.mul_div_cancel' hp]
  · simp [insertTuplePrime, removeTuplePrime, hi]

theorem removeTuplePrime_insertTuplePrime {H : Finset ℕ} {p : ℕ}
    (hp : 0 < p) (h : H) (r : H → ℕ) :
    removeTuplePrime p h (insertTuplePrime p h r) = r := by
  funext i
  by_cases hi : i = h
  · subst i
    simp [insertTuplePrime, removeTuplePrime, Nat.mul_div_cancel_left _ hp]
  · simp [insertTuplePrime, removeTuplePrime, hi]

theorem removeTuplePrime_coordinate_dvd {H : Finset ℕ} {p : ℕ}
    (h : H) (r : H → ℕ) (hpd : p ∣ r h) (i : H) :
    removeTuplePrime p h r i ∣ r i := by
  by_cases hi : i = h
  · subst i
    simpa [removeTuplePrime] using Nat.div_dvd_of_dvd hpd
  · simp [removeTuplePrime, hi]

theorem exists_unique_coordinate_prime_dvd_of_maynard
    {H : Finset ℕ} {R W p : ℕ} {r : H → ℕ}
    (hp : p.Prime) (hr : IsMaynardDivisorTuple H R W r)
    (hpd : p ∣ divisorTupleProduct H r) :
    ∃! h : H, p ∣ r h := by
  classical
  obtain ⟨h, _hh, hph⟩ :=
    Prime.exists_mem_finset_dvd (Nat.prime_iff.mp hp) hpd
  refine ⟨h, hph, ?_⟩
  intro i hpi
  by_contra hne
  have hcop := (hr.coordinates_coprime hne).symm
  have hpcop : Nat.Coprime p (r i) :=
    (hcop.coprime_dvd_left hph)
  exact (hp.coprime_iff_not_dvd.mp hpcop) hpi

theorem removeTuplePrime_isMaynard {H : Finset ℕ} {R W p : ℕ}
    {r : H → ℕ} (hp : p.Prime) (hr : IsMaynardDivisorTuple H R W r)
    (h : H) (hpd : p ∣ r h) :
    IsMaynardDivisorTuple H R (W * p) (removeTuplePrime p h r) := by
  let r' := removeTuplePrime p h r
  have hrEq : insertTuplePrime p h r' = r :=
    insertTuplePrime_removeTuplePrime h r hpd
  have hprodEq : p * divisorTupleProduct H r' = divisorTupleProduct H r := by
    rw [← divisorTupleProduct_insertTuplePrime p h r', hrEq]
  have hpProd : Nat.Coprime p (divisorTupleProduct H r') := by
    have hsq : Squarefree (p * divisorTupleProduct H r') := by
      rw [hprodEq]
      exact hr.2.2
    exact Nat.coprime_of_squarefree_mul hsq
  have hprodDvd : divisorTupleProduct H r' ∣ divisorTupleProduct H r := by
    rw [← hprodEq]
    exact dvd_mul_left _ _
  have hprodPos : 0 < divisorTupleProduct H r :=
    Nat.pos_of_ne_zero hr.2.2.ne_zero
  have hprodLe : divisorTupleProduct H r' ≤ divisorTupleProduct H r :=
    Nat.le_of_dvd hprodPos hprodDvd
  refine ⟨hprodLe.trans_lt hr.1, ?_, hr.2.2.squarefree_of_dvd hprodDvd⟩
  rw [Nat.coprime_mul_iff_right]
  exact ⟨Nat.Coprime.of_dvd_left hprodDvd hr.2.1, hpProd.symm⟩

theorem not_prime_dvd_coordinate_of_maynard_mul {H : Finset ℕ}
    {R W p : ℕ} {r : H → ℕ}
    (hp : p.Prime) (hr : IsMaynardDivisorTuple H R (W * p) r) (h : H) :
    ¬p ∣ r h := by
  have hcopProd : Nat.Coprime p (divisorTupleProduct H r) := by
    have hprodMod : Nat.Coprime (divisorTupleProduct H r) p :=
      hr.2.1.coprime_dvd_right (dvd_mul_left p W)
    exact hprodMod.symm
  exact hp.coprime_iff_not_dvd.mp
    (hcopProd.coprime_dvd_right (divisorTupleCoordinate_dvd_product r h))

/-- Pairs consisting of a coordinate and a `p`-free supported tuple for
which inserting `p` remains in the old support. -/
def insertedTupleSupport (H : Finset ℕ) (R W p : ℕ) :
    Finset (Σ _h : H, H → ℕ) :=
  ((Finset.univ : Finset H).sigma fun _h =>
      maynardDivisorTupleSupport H R (W * p)).filter fun a =>
    insertTuplePrime p a.1 a.2 ∈ maynardDivisorTupleSupport H R W

theorem insertedTupleSupport_map_injective {H : Finset ℕ}
    {R W p : ℕ} (hp : p.Prime) :
    Set.InjOn (fun a : Σ _h : H, H → ℕ =>
      insertTuplePrime p a.1 a.2) (insertedTupleSupport H R W p) := by
  classical
  intro a ha b hb hab
  have haData := Finset.mem_filter.mp ha
  have hbData := Finset.mem_filter.mp hb
  have haFree := isMaynardDivisorTuple_of_mem_support
    (Finset.mem_sigma.mp haData.1).2
  have hbFree := isMaynardDivisorTuple_of_mem_support
    (Finset.mem_sigma.mp hbData.1).2
  have habCoord : a.1 = b.1 := by
    by_contra hne
    have hpLeft : p ∣ insertTuplePrime p a.1 a.2 a.1 := by
      simp [insertTuplePrime]
    have hpRight : p ∣ insertTuplePrime p b.1 b.2 a.1 := by
      have heq := congrFun hab a.1
      change p ∣ (fun c : Σ _h : H, H → ℕ =>
        insertTuplePrime p c.1 c.2) b a.1
      rw [← heq]
      exact hpLeft
    have : p ∣ b.2 a.1 := by
      simpa [insertTuplePrime, hne] using hpRight
    exact (not_prime_dvd_coordinate_of_maynard_mul hp hbFree a.1) this
  cases a with
  | mk ah ar =>
    cases b with
    | mk bh br =>
      simp only at habCoord
      subst bh
      have htuple : ar = br :=
        insertTuplePrime_injective hp.pos ah hab
      subst br
      rfl

theorem insertedTupleSupport_surjective {H : Finset ℕ}
    {R W p : ℕ} (hp : p.Prime)
    {s : H → ℕ} (hs : s ∈ maynardDivisorTupleSupport H R W)
    (hpd : p ∣ divisorTupleProduct H s) :
    ∃ a ∈ insertedTupleSupport H R W p,
      insertTuplePrime p a.1 a.2 = s := by
  classical
  have hsMaynard := isMaynardDivisorTuple_of_mem_support hs
  obtain ⟨h, hph, _huniq⟩ :=
    exists_unique_coordinate_prime_dvd_of_maynard hp hsMaynard hpd
  let r := removeTuplePrime p h s
  have hrMaynard := removeTuplePrime_isMaynard hp hsMaynard h hph
  have hrSupport : r ∈ maynardDivisorTupleSupport H R (W * p) :=
    mem_maynardDivisorTupleSupport_iff.mpr
      ⟨hrMaynard.mem_maynardDivisorTupleBox, hrMaynard⟩
  let a : Σ _h : H, H → ℕ := ⟨h, r⟩
  refine ⟨a, ?_, ?_⟩
  · rw [insertedTupleSupport, Finset.mem_filter]
    refine ⟨Finset.mem_sigma.mpr ⟨Finset.mem_univ h, hrSupport⟩, ?_⟩
    rw [show insertTuplePrime p h r = s by
      simpa [r] using insertTuplePrime_removeTuplePrime h s hph]
    exact hs
  · simpa [a, r] using insertTuplePrime_removeTuplePrime h s hph

theorem sum_insertedTupleSupport_eq_primeDvd_filter {H : Finset ℕ}
    {R W p : ℕ} (hp : p.Prime) (F : (H → ℕ) → ℝ) :
    (∑ a ∈ insertedTupleSupport H R W p,
        F (insertTuplePrime p a.1 a.2)) =
      ∑ s ∈ (maynardDivisorTupleSupport H R W).filter
          (fun s => p ∣ divisorTupleProduct H s), F s := by
  classical
  apply Finset.sum_bij (fun a _ha => insertTuplePrime p a.1 a.2)
  · intro a ha
    have haData := Finset.mem_filter.mp ha
    refine Finset.mem_filter.mpr ⟨haData.2, ?_⟩
    rw [divisorTupleProduct_insertTuplePrime]
    exact dvd_mul_right p _
  · intro a ha b hb hab
    exact insertedTupleSupport_map_injective hp ha hb hab
  · intro s hs
    have hsData := Finset.mem_filter.mp hs
    obtain ⟨a, ha, has⟩ :=
      insertedTupleSupport_surjective hp hsData.1 hsData.2
    exact ⟨a, ha, has⟩
  · intro a ha
    rfl

/-- Rewrite the inverse `Y`-transform over its actual supported tuples. -/
def tupleDvd {H : Finset ℕ} (d r : H → ℕ) : Prop :=
  ∀ h : H, d h ∣ r h

def inverseYTerm {H : Finset ℕ} (d : H → ℕ)
    (y : (H → ℕ) → ℝ) (r : H → ℕ) : ℝ :=
  if tupleDvd d r then
    y r / ∏ h : H, (Nat.totient (r h) : ℝ)
  else 0

theorem maynardCoefficientFromY_eq_supportSum {H : Finset ℕ}
    {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) (d : H → ℕ) :
    maynardCoefficientFromY H R W y d =
      if Nat.Coprime (divisorTupleProduct H d) W then
        (∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ) * d h) *
          ∑ r ∈ maynardDivisorTupleSupport H R W,
            if ∀ h : H, d h ∣ r h then
              y r / ∏ h : H, (Nat.totient (r h) : ℝ)
            else 0
      else 0 := by
  classical
  unfold maynardCoefficientFromY
  by_cases hcop : Nat.Coprime (divisorTupleProduct H d) W
  · rw [if_pos hcop, if_pos hcop]
    congr 1
    let D := maynardDivisorTupleSupport H R W
    let B := maynardDivisorTupleBox H R
    have hsub : D ⊆ B := fun r hr =>
      (mem_maynardDivisorTupleSupport_iff.mp hr).1
    symm
    calc
      (∑ r ∈ D, if ∀ h : H, d h ∣ r h then
          y r / ∏ h : H, (Nat.totient (r h) : ℝ) else 0) =
          ∑ r ∈ D, if divisorTupleProduct H r < R ∧
              ∀ h : H, d h ∣ r h then
            y r / ∏ h : H, (Nat.totient (r h) : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrR := (isMaynardDivisorTuple_of_mem_support hr).1
        simp [hrR]
      _ = ∑ r ∈ B, if divisorTupleProduct H r < R ∧
              ∀ h : H, d h ∣ r h then
            y r / ∏ h : H, (Nat.totient (r h) : ℝ) else 0 := by
        apply Finset.sum_subset hsub
        intro r hrB hrNot
        by_cases hdr : ∀ h : H, d h ∣ r h
        · by_cases hrR : divisorTupleProduct H r < R
          · rw [if_pos ⟨hrR, hdr⟩]
            have hyr : y r = 0 := by
              by_contra hyr
              exact hrNot (mem_maynardDivisorTupleSupport_iff.mpr
                ⟨hrB, hy r hyr⟩)
            simp [hyr]
          · rw [if_neg (fun h => hrR h.1)]
        · rw [if_neg (fun h => hdr h.2)]
  · simp [hcop]

/-- The supported inverse transform written with the reusable
`inverseYTerm` abbreviation. -/
theorem maynardCoefficientFromY_eq_coreSum {H : Finset ℕ}
    {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) (d : H → ℕ) :
    maynardCoefficientFromY H R W y d =
      if Nat.Coprime (divisorTupleProduct H d) W then
        (∏ h : H,
            (ArithmeticFunction.moebius (d h) : ℝ) * d h) *
          ∑ r ∈ maynardDivisorTupleSupport H R W,
            inverseYTerm d y r
      else 0 := by
  rw [maynardCoefficientFromY_eq_supportSum hy d]
  by_cases hcop : Nat.Coprime (divisorTupleProduct H d) W
  · rw [if_pos hcop, if_pos hcop]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    unfold inverseYTerm tupleDvd
    by_cases hdr : ∀ h : H, d h ∣ r h <;> simp [hdr]
  · simp [hcop]

theorem mem_support_mul_prime_iff {H : Finset ℕ} {R W p : ℕ}
    (hp : p.Prime) (r : H → ℕ) :
    r ∈ maynardDivisorTupleSupport H R (W * p) ↔
      r ∈ maynardDivisorTupleSupport H R W ∧
        ¬p ∣ divisorTupleProduct H r := by
  constructor
  · intro hr
    have hm := isMaynardDivisorTuple_of_mem_support hr
    have hW : Nat.Coprime (divisorTupleProduct H r) W :=
      hm.2.1.coprime_dvd_right (dvd_mul_right W p)
    have hpCop : Nat.Coprime p (divisorTupleProduct H r) := by
      exact (hm.2.1.coprime_dvd_right (dvd_mul_left p W)).symm
    refine ⟨mem_maynardDivisorTupleSupport_iff.mpr
      ⟨hm.mem_maynardDivisorTupleBox, hm.1, hW, hm.2.2⟩,
        hp.coprime_iff_not_dvd.mp hpCop⟩
  · rintro ⟨hr, hpNot⟩
    have hm := isMaynardDivisorTuple_of_mem_support hr
    have hpCop : Nat.Coprime (divisorTupleProduct H r) p :=
      (hp.coprime_iff_not_dvd.mpr hpNot).symm
    have hWp : Nat.Coprime (divisorTupleProduct H r) (W * p) := by
      rw [Nat.coprime_mul_iff_right]
      exact ⟨hm.2.1, hpCop⟩
    exact mem_maynardDivisorTupleSupport_iff.mpr
      ⟨hm.mem_maynardDivisorTupleBox, hm.1, hWp, hm.2.2⟩

theorem tupleDvd_insertTuplePrime_iff {H : Finset ℕ} {p : ℕ}
    (hp : p.Prime) {d r : H → ℕ}
    (hdcop : Nat.Coprime p (divisorTupleProduct H d)) (m : H) :
    tupleDvd d (insertTuplePrime p m r) ↔ tupleDvd d r := by
  constructor
  · intro hdr h
    by_cases hh : h = m
    · subst h
      have hdpmul : d m ∣ p * r m := by simpa using hdr m
      have hcop : Nat.Coprime (d m) p := by
        exact (hdcop.coprime_dvd_right
          (divisorTupleCoordinate_dvd_product d m)).symm
      exact hcop.dvd_of_dvd_mul_left hdpmul
    · simpa [insertTuplePrime, hh] using hdr h
  · intro hdr h
    by_cases hh : h = m
    · subst h
      simp only [insertTuplePrime_apply_same]
      exact dvd_mul_of_dvd_right (hdr m) p
    · simpa [insertTuplePrime, hh] using hdr h

theorem inverseYTerm_insertTuplePrime {H : Finset ℕ} {R W p : ℕ}
    (hp : p.Prime) {d r : H → ℕ}
    (hdcop : Nat.Coprime p (divisorTupleProduct H d))
    (hr : IsMaynardDivisorTuple H R (W * p) r) (m : H)
    (y : (H → ℕ) → ℝ) :
    inverseYTerm d y (insertTuplePrime p m r) =
      (if tupleDvd d r then
        y (insertTuplePrime p m r) /
          ((Nat.totient p : ℝ) *
            ∏ h : H, (Nat.totient (r h) : ℝ))
      else 0) := by
  unfold inverseYTerm
  rw [tupleDvd_insertTuplePrime_iff hp hdcop m]
  by_cases hdr : tupleDvd d r
  · rw [if_pos hdr, if_pos hdr]
    have hcop : Nat.Coprime p (divisorTupleProduct H r) := by
      have hprodMod : Nat.Coprime (divisorTupleProduct H r) p :=
        hr.2.1.coprime_dvd_right (dvd_mul_left p W)
      exact hprodMod.symm
    have hphiNat := coordinateTotientProduct_insertTuplePrime hp m r hcop
    have hphiReal :
        (∏ h : H,
            (Nat.totient (insertTuplePrime p m r h) : ℝ)) =
          (Nat.totient p : ℝ) *
            ∏ h : H, (Nat.totient (r h) : ℝ) := by
      rw [Nat.totient_prime hp]
      exact_mod_cast hphiNat
    rw [hphiReal]
  · rw [if_neg hdr, if_neg hdr]

theorem insertedContribution_eq_primeDvd_sum {H : Finset ℕ}
    {R W p : ℕ} (hp : p.Prime) {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) {d : H → ℕ}
    (hdcop : Nat.Coprime p (divisorTupleProduct H d)) :
    (∑ r ∈ maynardDivisorTupleSupport H R (W * p),
        if tupleDvd d r then
          (∑ m : H,
              y (insertTuplePrime p m r) / (Nat.totient p : ℝ)) /
            ∏ h : H, (Nat.totient (r h) : ℝ)
        else 0) =
      ∑ s ∈ (maynardDivisorTupleSupport H R W).filter
          (fun s => p ∣ divisorTupleProduct H s),
        inverseYTerm d y s := by
  classical
  let Dp := maynardDivisorTupleSupport H R (W * p)
  let S := (Finset.univ : Finset H).sigma fun _m => Dp
  let I := insertedTupleSupport H R W p
  let f : (Σ _m : H, H → ℕ) → ℝ := fun a =>
    if tupleDvd d a.2 then
      y (insertTuplePrime p a.1 a.2) /
        ((Nat.totient p : ℝ) *
          ∏ h : H, (Nat.totient (a.2 h) : ℝ))
    else 0
  calc
    (∑ r ∈ Dp,
        if tupleDvd d r then
          (∑ m : H,
              y (insertTuplePrime p m r) / (Nat.totient p : ℝ)) /
            ∏ h : H, (Nat.totient (r h) : ℝ)
        else 0) =
        ∑ r ∈ Dp, ∑ m : H,
          if tupleDvd d r then
            y (insertTuplePrime p m r) /
              ((Nat.totient p : ℝ) *
                ∏ h : H, (Nat.totient (r h) : ℝ))
          else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hdr : tupleDvd d r
      · rw [if_pos hdr]
        simp_rw [if_pos hdr]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro m hm
        ring
      · rw [if_neg hdr]
        simp [hdr]
    _ = ∑ m : H, ∑ r ∈ Dp,
          if tupleDvd d r then
            y (insertTuplePrime p m r) /
              ((Nat.totient p : ℝ) *
                ∏ h : H, (Nat.totient (r h) : ℝ))
          else 0 := by rw [Finset.sum_comm]
    _ = ∑ a ∈ S, f a := by
      simpa [S, f] using
        (Finset.sum_sigma' (Finset.univ : Finset H) (fun _m => Dp)
          (fun m r => if tupleDvd d r then
            y (insertTuplePrime p m r) /
              ((Nat.totient p : ℝ) *
                ∏ h : H, (Nat.totient (r h) : ℝ))
          else 0))
    _ = ∑ a ∈ I, f a := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro a haS haNot
      have haNot' : insertTuplePrime p a.1 a.2 ∉
          maynardDivisorTupleSupport H R W := by
        intro haIns
        exact haNot (Finset.mem_filter.mpr ⟨haS, haIns⟩)
      have hyzero : y (insertTuplePrime p a.1 a.2) = 0 := by
        by_contra hyne
        have hm := hy _ hyne
        exact haNot' (mem_maynardDivisorTupleSupport_iff.mpr
          ⟨hm.mem_maynardDivisorTupleBox, hm⟩)
      simp [f, hyzero]
    _ = ∑ a ∈ I,
          inverseYTerm d y (insertTuplePrime p a.1 a.2) := by
      apply Finset.sum_congr rfl
      intro a ha
      have haData := Finset.mem_filter.mp ha
      have hr := isMaynardDivisorTuple_of_mem_support
        (Finset.mem_sigma.mp haData.1).2
      symm
      simpa [f] using inverseYTerm_insertTuplePrime hp hdcop hr a.1 y
    _ = ∑ s ∈ (maynardDivisorTupleSupport H R W).filter
          (fun s => p ∣ divisorTupleProduct H s),
        inverseYTerm d y s := by
      simpa [I] using sum_insertedTupleSupport_eq_primeDvd_filter hp
        (inverseYTerm d y)

/-- The `Y`-variable obtained after forbidding `p` in every divisor
coordinate.  The extra modulus is built into the support condition. -/
def erasePrimeY {H : Finset ℕ} (R W p : ℕ)
    (y : (H → ℕ) → ℝ) (r : H → ℕ) : ℝ :=
  if IsMaynardDivisorTuple H R (W * p) r then
    y r + ∑ h : H,
      y (insertTuplePrime p h r) / (Nat.totient p : ℝ)
  else 0

/-- Forbidding `p` in every divisor coordinate changes the inverse transform
by replacing `y` with `erasePrimeY`.  This is the core finite-sum identity;
the Möbius prefactor is restored in `maynardCoefficientFromY_erasePrimeY`
below. -/
theorem erasePrimeCoreSum_eq {H : Finset ℕ} {R W p : ℕ}
    (hp : p.Prime) {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) {d : H → ℕ}
    (hdcop : Nat.Coprime p (divisorTupleProduct H d)) :
    (∑ r ∈ maynardDivisorTupleSupport H R (W * p),
        inverseYTerm d (erasePrimeY R W p y) r) =
      ∑ r ∈ maynardDivisorTupleSupport H R W,
        inverseYTerm d y r := by
  classical
  let D := maynardDivisorTupleSupport H R W
  let Dp := maynardDivisorTupleSupport H R (W * p)
  let P : (H → ℕ) → Prop := fun r => p ∣ divisorTupleProduct H r
  let g : (H → ℕ) → ℝ := inverseYTerm d y
  let extra : (H → ℕ) → ℝ := fun r =>
    if tupleDvd d r then
      (∑ m : H,
          y (insertTuplePrime p m r) / (Nat.totient p : ℝ)) /
        ∏ h : H, (Nat.totient (r h) : ℝ)
    else 0
  have hDp : Dp = D.filter (fun r => ¬P r) := by
    ext r
    simp only [Dp, D, P, Finset.mem_filter]
    exact mem_support_mul_prime_iff hp r
  calc
    (∑ r ∈ Dp, inverseYTerm d (erasePrimeY R W p y) r) =
        ∑ r ∈ Dp, (g r + extra r) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrMaynard := isMaynardDivisorTuple_of_mem_support hr
      dsimp only [g, extra]
      unfold inverseYTerm
      rw [erasePrimeY, if_pos hrMaynard]
      by_cases hdr : tupleDvd d r
      · simp only [if_pos hdr]
        rw [add_div]
      · simp only [if_neg hdr]
        norm_num
    _ = (∑ r ∈ Dp, g r) + ∑ r ∈ Dp, extra r := by
      rw [Finset.sum_add_distrib]
    _ = (∑ r ∈ D with ¬P r, g r) + ∑ r ∈ Dp, extra r := by
      rw [hDp]
    _ = (∑ r ∈ D with ¬P r, g r) +
          ∑ r ∈ D.filter P, g r := by
      rw [insertedContribution_eq_primeDvd_sum hp hy hdcop]
    _ = ∑ r ∈ D, g r := by
      rw [add_comm]
      exact Finset.sum_filter_add_sum_filter_not D P g
    _ = ∑ r ∈ maynardDivisorTupleSupport H R W,
          inverseYTerm d y r := by rfl

theorem prime_dvd_divisorTupleProduct_insertTuplePrime {H : Finset ℕ}
    {p : ℕ} (h : H) (r : H → ℕ) :
    p ∣ divisorTupleProduct H (insertTuplePrime p h r) := by
  rw [divisorTupleProduct_insertTuplePrime]
  exact dvd_mul_right p _

theorem not_prime_dvd_coordinate_of_coprime_product {H : Finset ℕ}
    {p : ℕ} (hp : p.Prime) {r : H → ℕ}
    (hcop : Nat.Coprime p (divisorTupleProduct H r)) (h : H) :
    ¬p ∣ r h := by
  exact hp.coprime_iff_not_dvd.mp
    (hcop.coprime_dvd_right (divisorTupleCoordinate_dvd_product r h))

/-- Inserting a fresh prime in one coordinate multiplies the Möbius/divisor
prefactor of the inverse `Y`-transform by `-p`. -/
theorem moebiusTupleFactor_insertTuplePrime {H : Finset ℕ} {p : ℕ}
    (hp : p.Prime) {d : H → ℕ}
    (hcop : Nat.Coprime p (divisorTupleProduct H d)) (m : H) :
    (∏ h : H,
        (ArithmeticFunction.moebius (insertTuplePrime p m d h) : ℝ) *
          insertTuplePrime p m d h) =
      -(p : ℝ) *
        ∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ) * d h := by
  classical
  let f : H → ℝ := fun h =>
    (ArithmeticFunction.moebius (d h) : ℝ) * d h
  have hcopCoord : Nat.Coprime p (d m) :=
    hcop.coprime_dvd_right (divisorTupleCoordinate_dvd_product d m)
  have hmuNat : ArithmeticFunction.moebius (p * d m) =
      ArithmeticFunction.moebius p * ArithmeticFunction.moebius (d m) :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcopCoord
  have hmu : (ArithmeticFunction.moebius (p * d m) : ℝ) =
      -(ArithmeticFunction.moebius (d m) : ℝ) := by
    rw [hmuNat, ArithmeticFunction.moebius_apply_prime hp]
    push_cast
    ring
  have hfun :
      (fun h : H =>
        (ArithmeticFunction.moebius (insertTuplePrime p m d h) : ℝ) *
          insertTuplePrime p m d h) =
        Function.update f m
          ((ArithmeticFunction.moebius (p * d m) : ℝ) * (p * d m)) := by
    funext h
    by_cases hhm : h = m
    · subst h
      simp [f]
    · simp [insertTuplePrime, f, hhm]
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ m), hmu]
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ m)]
  simp only [Finset.sdiff_singleton_eq_erase]
  dsimp only [f]
  push_cast
  ring

/-- Supported `p`-free tuples whose insertion at the distinguished
coordinate remains in the old support. -/
def insertedTupleSupportAt (H : Finset ℕ) (R W p : ℕ) (m : H) :
    Finset (H → ℕ) :=
  (maynardDivisorTupleSupport H R (W * p)).filter fun r =>
    insertTuplePrime p m r ∈ maynardDivisorTupleSupport H R W

theorem sum_insertedTupleSupportAt_eq_coordinate_filter {H : Finset ℕ}
    {R W p : ℕ} (hp : p.Prime) (m : H) (F : (H → ℕ) → ℝ) :
    (∑ r ∈ insertedTupleSupportAt H R W p m,
        F (insertTuplePrime p m r)) =
      ∑ s ∈ (maynardDivisorTupleSupport H R W).filter
          (fun s => p ∣ s m), F s := by
  classical
  apply Finset.sum_bij (fun r _hr => insertTuplePrime p m r)
  · intro r hr
    have hrData := Finset.mem_filter.mp hr
    refine Finset.mem_filter.mpr ⟨hrData.2, ?_⟩
    simp [insertTuplePrime]
  · intro r hr s hs hrs
    exact insertTuplePrime_injective hp.pos m hrs
  · intro s hs
    have hsData := Finset.mem_filter.mp hs
    let r := removeTuplePrime p m s
    have hrMaynard := removeTuplePrime_isMaynard hp
      (isMaynardDivisorTuple_of_mem_support hsData.1) m hsData.2
    have hrSupport : r ∈ maynardDivisorTupleSupport H R (W * p) :=
      mem_maynardDivisorTupleSupport_iff.mpr
        ⟨hrMaynard.mem_maynardDivisorTupleBox, hrMaynard⟩
    have hins : insertTuplePrime p m r = s := by
      simpa [r] using insertTuplePrime_removeTuplePrime m s hsData.2
    refine ⟨r, ?_, hins⟩
    exact Finset.mem_filter.mpr ⟨hrSupport, hins ▸ hsData.1⟩
  · intro r hr
    rfl

theorem tupleDvd_insertTuplePrime_both_iff {H : Finset ℕ} {p : ℕ}
    (hp : p.Prime) {d r : H → ℕ} (m : H) :
    tupleDvd (insertTuplePrime p m d) (insertTuplePrime p m r) ↔
      tupleDvd d r := by
  constructor
  · intro hdr h
    by_cases hhm : h = m
    · subst h
      exact (mul_dvd_mul_iff_left hp.ne_zero).mp (by
        simpa using hdr m)
    · simpa [insertTuplePrime, hhm] using hdr h
  · intro hdr h
    by_cases hhm : h = m
    · subst h
      simpa using (mul_dvd_mul_iff_left hp.ne_zero).mpr (hdr m)
    · simpa [insertTuplePrime, hhm] using hdr h

theorem inverseYTerm_insertTuplePrime_both {H : Finset ℕ}
    {R W p : ℕ} (hp : p.Prime) {d r : H → ℕ}
    (hr : IsMaynardDivisorTuple H R (W * p) r) (m : H)
    (y : (H → ℕ) → ℝ) :
    inverseYTerm (insertTuplePrime p m d) y
        (insertTuplePrime p m r) =
      if tupleDvd d r then
        y (insertTuplePrime p m r) /
          ((Nat.totient p : ℝ) *
            ∏ h : H, (Nat.totient (r h) : ℝ))
      else 0 := by
  unfold inverseYTerm
  rw [tupleDvd_insertTuplePrime_both_iff hp m]
  by_cases hdr : tupleDvd d r
  · rw [if_pos hdr, if_pos hdr]
    have hcop : Nat.Coprime p (divisorTupleProduct H r) := by
      have hprodMod : Nat.Coprime (divisorTupleProduct H r) p :=
        hr.2.1.coprime_dvd_right (dvd_mul_left p W)
      exact hprodMod.symm
    have hphiNat := coordinateTotientProduct_insertTuplePrime hp m r hcop
    have hphiReal :
        (∏ h : H,
            (Nat.totient (insertTuplePrime p m r h) : ℝ)) =
          (Nat.totient p : ℝ) *
            ∏ h : H, (Nat.totient (r h) : ℝ) := by
      rw [Nat.totient_prime hp]
      exact_mod_cast hphiNat
    rw [hphiReal]
  · rw [if_neg hdr, if_neg hdr]

/-- The old inverse-transform core with `p` inserted in one divisor
coordinate is a single distinguished insertion sum over the `p`-free
support. -/
theorem insertedCoordinateCoreSum_eq {H : Finset ℕ} {R W p : ℕ}
    (hp : p.Prime) {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) (d : H → ℕ) (m : H) :
    (∑ s ∈ maynardDivisorTupleSupport H R W,
        inverseYTerm (insertTuplePrime p m d) y s) =
      ∑ r ∈ maynardDivisorTupleSupport H R (W * p),
        if tupleDvd d r then
          y (insertTuplePrime p m r) /
            ((Nat.totient p : ℝ) *
              ∏ h : H, (Nat.totient (r h) : ℝ))
        else 0 := by
  classical
  let D := maynardDivisorTupleSupport H R W
  let Dp := maynardDivisorTupleSupport H R (W * p)
  let I := insertedTupleSupportAt H R W p m
  let f : (H → ℕ) → ℝ :=
    inverseYTerm (insertTuplePrime p m d) y
  let g : (H → ℕ) → ℝ := fun r =>
    if tupleDvd d r then
      y (insertTuplePrime p m r) /
        ((Nat.totient p : ℝ) *
          ∏ h : H, (Nat.totient (r h) : ℝ))
    else 0
  calc
    (∑ s ∈ D, f s) = ∑ s ∈ D.filter (fun s => p ∣ s m), f s := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro s hsD hsNot
      have hpNot : ¬p ∣ s m := by
        intro hps
        exact hsNot (Finset.mem_filter.mpr ⟨hsD, hps⟩)
      have htuple : ¬tupleDvd (insertTuplePrime p m d) s := by
        intro hdiv
        apply hpNot
        have hcoord := hdiv m
        have hpMul : p ∣ p * d m := dvd_mul_right p (d m)
        exact hpMul.trans (by simpa using hcoord)
      simp [f, inverseYTerm, htuple]
    _ = ∑ r ∈ I, f (insertTuplePrime p m r) := by
      symm
      simpa [D, I] using
        (sum_insertedTupleSupportAt_eq_coordinate_filter hp m f)
    _ = ∑ r ∈ I, g r := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrData := Finset.mem_filter.mp hr
      have hrMaynard := isMaynardDivisorTuple_of_mem_support hrData.1
      simpa [f, g] using
        (inverseYTerm_insertTuplePrime_both hp hrMaynard m y)
    _ = ∑ r ∈ Dp, g r := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro r hrDp hrNot
      have hinsNot : insertTuplePrime p m r ∉ D := by
        intro hins
        exact hrNot (Finset.mem_filter.mpr ⟨hrDp, hins⟩)
      have hyzero : y (insertTuplePrime p m r) = 0 := by
        by_contra hyne
        have hm := hy _ hyne
        exact hinsNot (mem_maynardDivisorTupleSupport_iff.mpr
          ⟨hm.mem_maynardDivisorTupleBox, hm⟩)
      simp [g, hyzero]
    _ = ∑ r ∈ maynardDivisorTupleSupport H R (W * p),
        if tupleDvd d r then
          y (insertTuplePrime p m r) /
            ((Nat.totient p : ℝ) *
              ∏ h : H, (Nat.totient (r h) : ℝ))
        else 0 := by rfl

/-- The `Y`-variable obtained when `p` is forced to divide the shift at the
distinguished coordinate.  The summation terms erase occurrences of `p` in
all coordinates; subtracting `p / φ(p)` times the distinguished insertion
then restores precisely the option in which `p` occurs at that coordinate.
At coefficient level this corresponds to adding the coefficient with `p`
inserted in the distinguished coordinate. -/
def differencePrimeY {H : Finset ℕ} (R W p : ℕ) (m : H)
    (y : (H → ℕ) → ℝ) (r : H → ℕ) : ℝ :=
  if IsMaynardDivisorTuple H R (W * p) r then
    y r + ∑ h : H,
      y (insertTuplePrime p h r) / (Nat.totient p : ℝ) -
        (p : ℝ) * y (insertTuplePrime p m r) /
          (Nat.totient p : ℝ)
  else 0

theorem erasePrimeY_supported {H : Finset ℕ} (R W p : ℕ)
    (y : (H → ℕ) → ℝ) :
    IsSupportedMaynardY H R (W * p) (erasePrimeY R W p y) := by
  intro r hr
  unfold erasePrimeY at hr
  split at hr
  next h => exact h
  next => simp at hr

/-- Exact coefficient-level meaning of `erasePrimeY`: adjoining `p` to the
modulus discards precisely the old coefficients whose divisor tuple contains
`p`. -/
theorem maynardCoefficientFromY_erasePrimeY {H : Finset ℕ}
    {R W p : ℕ} (hp : p.Prime) {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) (d : H → ℕ) :
    maynardCoefficientFromY H R (W * p) (erasePrimeY R W p y) d =
      if Nat.Coprime p (divisorTupleProduct H d) then
        maynardCoefficientFromY H R W y d
      else 0 := by
  classical
  rw [maynardCoefficientFromY_eq_supportSum
    (erasePrimeY_supported R W p y) d]
  rw [maynardCoefficientFromY_eq_supportSum hy d]
  by_cases hpD : Nat.Coprime p (divisorTupleProduct H d)
  · rw [if_pos hpD]
    by_cases hW : Nat.Coprime (divisorTupleProduct H d) W
    · have hWp : Nat.Coprime (divisorTupleProduct H d) (W * p) := by
        rw [Nat.coprime_mul_iff_right]
        exact ⟨hW, hpD.symm⟩
      rw [if_pos hWp, if_pos hW]
      congr 1
      calc
        (∑ r ∈ maynardDivisorTupleSupport H R (W * p),
            if ∀ h : H, d h ∣ r h then
              erasePrimeY R W p y r /
                ∏ h : H, (Nat.totient (r h) : ℝ)
            else 0) =
            ∑ r ∈ maynardDivisorTupleSupport H R (W * p),
              inverseYTerm d (erasePrimeY R W p y) r := by
          apply Finset.sum_congr rfl
          intro r hr
          unfold inverseYTerm tupleDvd
          by_cases hdr : ∀ h : H, d h ∣ r h <;> simp [hdr]
        _ = ∑ r ∈ maynardDivisorTupleSupport H R W,
              inverseYTerm d y r := erasePrimeCoreSum_eq hp hy hpD
        _ = ∑ r ∈ maynardDivisorTupleSupport H R W,
            if ∀ h : H, d h ∣ r h then
              y r / ∏ h : H, (Nat.totient (r h) : ℝ)
            else 0 := by
          apply Finset.sum_congr rfl
          intro r hr
          unfold inverseYTerm tupleDvd
          by_cases hdr : ∀ h : H, d h ∣ r h <;> simp [hdr]
    · have hWp : ¬Nat.Coprime (divisorTupleProduct H d) (W * p) := by
        intro h
        exact hW (h.coprime_dvd_right (dvd_mul_right W p))
      simp [hWp, hW]
  · have hWp : ¬Nat.Coprime (divisorTupleProduct H d) (W * p) := by
      intro h
      have hDp : Nat.Coprime (divisorTupleProduct H d) p :=
        h.coprime_dvd_right (dvd_mul_left p W)
      exact hpD hDp.symm
    simp [hpD, hWp]

theorem differencePrimeY_supported {H : Finset ℕ} (R W p : ℕ) (m : H)
    (y : (H → ℕ) → ℝ) :
    IsSupportedMaynardY H R (W * p) (differencePrimeY R W p m y) := by
  intro r hr
  unfold differencePrimeY at hr
  split at hr
  next h => exact h
  next => simp at hr

/-- Core finite-sum identity for forcing `p` at one coordinate. -/
theorem differencePrimeCoreSum_eq {H : Finset ℕ} {R W p : ℕ}
    (hp : p.Prime) {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) {d : H → ℕ}
    (hdcop : Nat.Coprime p (divisorTupleProduct H d)) (m : H) :
    (∑ r ∈ maynardDivisorTupleSupport H R (W * p),
        inverseYTerm d (differencePrimeY R W p m y) r) =
      (∑ r ∈ maynardDivisorTupleSupport H R W,
          inverseYTerm d y r) -
        (p : ℝ) *
          ∑ r ∈ maynardDivisorTupleSupport H R W,
            inverseYTerm (insertTuplePrime p m d) y r := by
  classical
  let Dp := maynardDivisorTupleSupport H R (W * p)
  let a : (H → ℕ) → ℝ := fun r =>
    inverseYTerm d (erasePrimeY R W p y) r
  let b : (H → ℕ) → ℝ := fun r =>
    if tupleDvd d r then
      y (insertTuplePrime p m r) /
        ((Nat.totient p : ℝ) *
          ∏ h : H, (Nat.totient (r h) : ℝ))
    else 0
  calc
    (∑ r ∈ Dp, inverseYTerm d (differencePrimeY R W p m y) r) =
        ∑ r ∈ Dp, (a r - (p : ℝ) * b r) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrMaynard := isMaynardDivisorTuple_of_mem_support hr
      dsimp only [a, b]
      unfold inverseYTerm
      rw [differencePrimeY, if_pos hrMaynard,
        erasePrimeY, if_pos hrMaynard]
      by_cases hdr : tupleDvd d r
      · simp only [if_pos hdr]
        ring
      · simp [hdr]
    _ = (∑ r ∈ Dp, a r) - (p : ℝ) * ∑ r ∈ Dp, b r := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (∑ r ∈ maynardDivisorTupleSupport H R W,
          inverseYTerm d y r) -
        (p : ℝ) * ∑ r ∈ Dp, b r := by
      rw [show (∑ r ∈ Dp, a r) =
          ∑ r ∈ maynardDivisorTupleSupport H R W,
            inverseYTerm d y r by
        exact erasePrimeCoreSum_eq hp hy hdcop]
    _ = (∑ r ∈ maynardDivisorTupleSupport H R W,
          inverseYTerm d y r) -
        (p : ℝ) *
          ∑ r ∈ maynardDivisorTupleSupport H R W,
            inverseYTerm (insertTuplePrime p m d) y r := by
      rw [show (∑ r ∈ Dp, b r) =
          ∑ r ∈ maynardDivisorTupleSupport H R W,
            inverseYTerm (insertTuplePrime p m d) y r by
        symm
        exact insertedCoordinateCoreSum_eq hp hy d m]

/-- Exact coefficient-level meaning of `differencePrimeY`: on a divisor
tuple free of `p`, its coefficient is the sum of the old coefficient and the
old coefficient with `p` inserted at the distinguished coordinate. -/
theorem maynardCoefficientFromY_differencePrimeY {H : Finset ℕ}
    {R W p : ℕ} (hp : p.Prime) (hpW : Nat.Coprime p W)
    {y : (H → ℕ) → ℝ} (hy : IsSupportedMaynardY H R W y)
    {d : H → ℕ} (hdcop : Nat.Coprime p (divisorTupleProduct H d))
    (m : H) :
    maynardCoefficientFromY H R (W * p)
        (differencePrimeY R W p m y) d =
      maynardCoefficientFromY H R W y d +
        maynardCoefficientFromY H R W y
          (insertTuplePrime p m d) := by
  classical
  rw [maynardCoefficientFromY_eq_coreSum
    (differencePrimeY_supported R W p m y) d]
  rw [maynardCoefficientFromY_eq_coreSum hy d]
  rw [maynardCoefficientFromY_eq_coreSum hy
    (insertTuplePrime p m d)]
  by_cases hW : Nat.Coprime (divisorTupleProduct H d) W
  · have hWp : Nat.Coprime (divisorTupleProduct H d) (W * p) := by
      rw [Nat.coprime_mul_iff_right]
      exact ⟨hW, hdcop.symm⟩
    have hinsW : Nat.Coprime
        (divisorTupleProduct H (insertTuplePrime p m d)) W := by
      rw [divisorTupleProduct_insertTuplePrime]
      exact hpW.mul_left hW
    rw [if_pos hWp, if_pos hW, if_pos hinsW]
    rw [differencePrimeCoreSum_eq hp hy hdcop m]
    rw [moebiusTupleFactor_insertTuplePrime hp hdcop m]
    ring
  · have hWp : ¬Nat.Coprime (divisorTupleProduct H d) (W * p) := by
      intro h
      exact hW (h.coprime_dvd_right (dvd_mul_right W p))
    have hinsW : ¬Nat.Coprime
        (divisorTupleProduct H (insertTuplePrime p m d)) W := by
      intro h
      apply hW
      rw [divisorTupleProduct_insertTuplePrime] at h
      exact h.coprime_dvd_left (dvd_mul_left (divisorTupleProduct H d) p)
    simp [hW, hWp, hinsW]

theorem abs_erasePrimeY_le {H : Finset ℕ} {R W p : ℕ}
    {y : (H → ℕ) → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hy : ∀ r, |y r| ≤ B) (hp : p.Prime) (r : H → ℕ) :
    |erasePrimeY R W p y r| ≤
      B * (1 + (Fintype.card H : ℝ) / (p - 1 : ℕ)) := by
  classical
  unfold erasePrimeY
  split_ifs
  next hr =>
    have hpTot : (Nat.totient p : ℝ) = (p - 1 : ℕ) := by
      rw [Nat.totient_prime hp]
    have hpPred : (0 : ℝ) < (p - 1 : ℕ) := by
      exact_mod_cast (by have := hp.one_lt; omega : 0 < p - 1)
    calc
      |y r + ∑ h : H,
          y (insertTuplePrime p h r) / (Nat.totient p : ℝ)| ≤
          |y r| + |∑ h : H,
            y (insertTuplePrime p h r) / (Nat.totient p : ℝ)| :=
        abs_add_le _ _
      _ ≤ B + ∑ h : H,
          |y (insertTuplePrime p h r) / (Nat.totient p : ℝ)| := by
        exact add_le_add (hy r) (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ B + ∑ _h : H, B / (p - 1 : ℕ) := by
        gcongr with h
        rw [abs_div, hpTot, abs_of_pos hpPred]
        exact div_le_div_of_nonneg_right (hy _) hpPred.le
      _ = B * (1 + (Fintype.card H : ℝ) / (p - 1 : ℕ)) := by
        rw [Finset.sum_const, Finset.card_univ]
        simp only [nsmul_eq_mul]
        ring
  next =>
    rw [abs_zero]
    exact mul_nonneg hB (by positivity)

theorem abs_differencePrimeY_le {H : Finset ℕ} {R W p : ℕ}
    {y : (H → ℕ) → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hy : ∀ r, |y r| ≤ B) (hp : p.Prime) (m : H) (r : H → ℕ) :
    |differencePrimeY R W p m y r| ≤
      B * (2 + ((Fintype.card H : ℝ) + 1) / (p - 1 : ℕ)) := by
  classical
  unfold differencePrimeY
  split_ifs
  next hr =>
    have hpTot : (Nat.totient p : ℝ) = (p - 1 : ℕ) := by
      rw [Nat.totient_prime hp]
    have hpPred : (0 : ℝ) < (p - 1 : ℕ) := by
      exact_mod_cast (by have := hp.one_lt; omega : 0 < p - 1)
    have hpReal : (p : ℝ) = (p - 1 : ℕ) + 1 := by
      have hpOne : 1 ≤ p := hp.one_le
      exact_mod_cast (by omega : p = p - 1 + 1)
    calc
      |y r + ∑ h : H,
          y (insertTuplePrime p h r) / (Nat.totient p : ℝ) -
            (p : ℝ) * y (insertTuplePrime p m r) /
              (Nat.totient p : ℝ)| ≤
          |y r| +
            |∑ h : H,
              y (insertTuplePrime p h r) / (Nat.totient p : ℝ)| +
            |(p : ℝ) * y (insertTuplePrime p m r) /
              (Nat.totient p : ℝ)| := by
        calc
          |y r + ∑ h : H,
              y (insertTuplePrime p h r) / (Nat.totient p : ℝ) -
                (p : ℝ) * y (insertTuplePrime p m r) /
                  (Nat.totient p : ℝ)| ≤
              |y r + ∑ h : H,
                y (insertTuplePrime p h r) / (Nat.totient p : ℝ)| +
              |(p : ℝ) * y (insertTuplePrime p m r) /
                (Nat.totient p : ℝ)| := abs_sub _ _
          _ ≤ _ := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ B + ∑ _h : H, B / (p - 1 : ℕ) +
            (p : ℝ) * B / (p - 1 : ℕ) := by
        gcongr
        · exact hy r
        · exact Finset.abs_sum_le_sum_abs _ _ |>.trans (by
            apply Finset.sum_le_sum
            intro h hh
            rw [abs_div, hpTot, abs_of_pos hpPred]
            exact div_le_div_of_nonneg_right (hy _) hpPred.le)
        · rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ p),
            hpTot, abs_of_pos hpPred]
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hy _) (by positivity)) hpPred.le
      _ = B * (2 + ((Fintype.card H : ℝ) + 1) / (p - 1 : ℕ)) := by
        rw [Finset.sum_const, Finset.card_univ]
        simp only [nsmul_eq_mul]
        rw [hpReal]
        field_simp
        ring
  next =>
    rw [abs_zero]
    exact mul_nonneg hB (by positivity)

end Erdos248
