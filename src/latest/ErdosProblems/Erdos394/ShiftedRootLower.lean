import ErdosProblems.Erdos394.ShiftedRootBad
import ErdosProblems.Erdos394.Prime

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Shifted-good global residue classes force large values of `t_K(pq)`
-/

open Nat Finset

namespace Erdos394

noncomputable local instance shiftedGlobalUnitsFintype (q : ℕ) :
    Fintype (ZMod q)ˣ := Fintype.ofFinite _

/-- Membership in a shifted product set is exactly coordinatewise shifted
root incidence. -/
theorem mem_shiftedRootBoxHitTupleSet_iff
    (P : Finset ℕ) (K j a : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (h : RootBoxMultiplierTuple P) :
    h ∈ shiftedRootBoxHitTupleSet P K j a hprime ↔
      ∀ p : ↥P, localShiftedBlockHit p.val K j a (h p) := by
  classical
  letI (p : ↥P) : NeZero p.val := ⟨(hprime p.val p.property).ne_zero⟩
  unfold shiftedRootBoxHitTupleSet
  rw [Fintype.mem_piFinset]
  constructor
  · intro hh p
    exact (Finset.mem_filter.mp (hh p)).2
  · intro hh p
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh p⟩

/-- Membership in the shifted-bad set has the expected existential form. -/
theorem mem_shiftedRootBadTupleSet_iff
    (P : Finset ℕ) (K Y : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (h : RootBoxMultiplierTuple P) :
    h ∈ shiftedRootBadTupleSet P K Y hprime ↔
      ∃ a < K, ∃ j, 1 ≤ j ∧ j ≤ Y ∧
        ∀ p : ↥P, localShiftedBlockHit p.val K j a (h p) := by
  classical
  unfold shiftedRootBadTupleSet
  constructor
  · intro hh
    obtain ⟨a, haK, hahit⟩ := Finset.mem_biUnion.mp hh
    obtain ⟨j, hjI, hjhit⟩ := Finset.mem_biUnion.mp hahit
    have ha := Finset.mem_range.mp haK
    have hj := Finset.mem_Icc.mp hjI
    exact ⟨a, ha, j, hj.1, hj.2,
      (mem_shiftedRootBoxHitTupleSet_iff P K j a hprime h).mp hjhit⟩
  · rintro ⟨a, ha, j, hj1, hjY, hjhit⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Finset.mem_range.mpr ha, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_Icc.mpr ⟨hj1, hjY⟩, ?_⟩
    exact (mem_shiftedRootBoxHitTupleSet_iff P K j a hprime h).mpr hjhit

/-- Global unit classes whose natural local CRT tuple is shifted-bad. -/
noncomputable def globalShiftedRootBadUnitSet
    (P : Finset ℕ) (K Y : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    Finset (ZMod (primeProduct P))ˣ := by
  classical
  exact Finset.univ.filter (fun u ↦
    globalUnitsRootBoxEquiv P hprime u ∈
      shiftedRootBadTupleSet P K Y hprime)

@[simp] theorem mem_globalShiftedRootBadUnitSet
    (P : Finset ℕ) (K Y : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (u : (ZMod (primeProduct P))ˣ) :
    u ∈ globalShiftedRootBadUnitSet P K Y hprime ↔
      globalUnitsRootBoxEquiv P hprime u ∈
        shiftedRootBadTupleSet P K Y hprime := by
  classical
  simp [globalShiftedRootBadUnitSet]

/-- The global CRT preimage of the shifted-bad tuple set has no greater
cardinality. -/
theorem card_globalShiftedRootBadUnitSet_le
    (P : Finset ℕ) (K Y : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    (globalShiftedRootBadUnitSet P K Y hprime).card ≤
      (shiftedRootBadTupleSet P K Y hprime).card := by
  classical
  apply Finset.card_le_card_of_injOn (globalUnitsRootBoxEquiv P hprime)
  · intro u hu
    exact (mem_globalShiftedRootBadUnitSet P K Y hprime u).mp hu
  · intro u hu v hv huv
    exact (globalUnitsRootBoxEquiv P hprime).injective huv

/-- The same sharp first-moment density bound holds for ordinary global unit
classes modulo `q=∏P`. -/
theorem normalized_card_globalShiftedRootBadUnitSet_le
    (P : Finset ℕ) (K Y : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hK : 1 ≤ K) (hlarge : ∀ p ∈ P, K < p) :
    ((globalShiftedRootBadUnitSet P K Y hprime).card : ℝ) /
        (primeUnitCount P : ℝ) ≤
      ((K ^ (P.card + 1) : ℕ) : ℝ) * (Y : ℝ) /
        (primeProduct P : ℝ) := by
  have hcard := card_globalShiftedRootBadUnitSet_le P K Y hprime
  have htuple := normalized_card_shiftedRootBadTupleSet_le
    P K Y hprime hK hlarge
  rw [rootBoxTupleUniverseCount_eq_primeUnitCount P hprime] at htuple
  have hphi : (0 : ℝ) < primeUnitCount P := by
    exact_mod_cast (show 0 < primeUnitCount P by
      unfold primeUnitCount
      exact Finset.prod_pos fun p hp ↦ by
        have := (hprime p hp).two_le
        omega)
  have hcardR : ((globalShiftedRootBadUnitSet P K Y hprime).card : ℝ) ≤
      ((shiftedRootBadTupleSet P K Y hprime).card : ℝ) := by
    exact_mod_cast hcard
  apply (div_le_div_of_nonneg_right hcardR hphi.le).trans
  exact htuple

/-- If a large-prime residue class avoids every shifted root through `Y`, then
no admissible `K`-block can start so early: `Yp < t_K(pq)+K`. -/
theorem shifted_good_unit_forces_t_add_large
    (P : Finset ℕ) (K Y ell : ℕ) (hK : 0 < K)
    (hprime : ∀ p ∈ P, p.Prime) (hell : ell.Prime)
    (hcop : ell.Coprime (primeProduct P))
    (hgood : ZMod.unitOfCoprime ell hcop ∉
      globalShiftedRootBadUnitSet P K Y hprime) :
    Y * ell < t K (ell * primeProduct P) + K := by
  classical
  have hqpos : 0 < primeProduct P := by
    unfold primeProduct
    exact Finset.prod_pos fun p hp ↦ (hprime p hp).pos
  have hnpos : 0 < ell * primeProduct P := mul_pos hell.pos hqpos
  let s := t K (ell * primeProduct P)
  have hspos : 0 < s := t_pos hK hnpos
  by_contra hnot
  have hsK : s + K ≤ Y * ell := Nat.le_of_not_gt hnot
  have hnprod : ell * primeProduct P ∣ consecutiveProduct K s := by
    exact t_dvd hK hnpos
  have hellprod : ell ∣ consecutiveProduct K s :=
    dvd_trans (dvd_mul_right ell (primeProduct P)) hnprod
  obtain ⟨a, haK, hella⟩ :=
    (prime_dvd_consecutiveProduct_iff hell).mp hellprod
  let j := (s + a) / ell
  have hjmul : j * ell = s + a := by
    dsimp [j]
    exact Nat.div_mul_cancel hella
  have hell_le : ell ≤ s + a := Nat.le_of_dvd (by omega) hella
  have hjpos : 0 < j := by
    dsimp [j]
    exact Nat.div_pos hell_le hell.pos
  have hjY : j ≤ Y := by
    have hlt : j * ell < Y * ell := by
      rw [hjmul]
      omega
    exact (Nat.mul_lt_mul_right hell.pos).mp hlt |>.le
  have hqprod : primeProduct P ∣ consecutiveProduct K s :=
    dvd_trans (dvd_mul_left (primeProduct P) ell) (by
      simpa [mul_comm] using hnprod)
  have hlocal : ∀ p : ↥P,
      localShiftedBlockHit p.val K j a
        (globalUnitsRootBoxEquiv P hprime
          (ZMod.unitOfCoprime ell hcop) p) := by
    intro p
    have hpq : p.val ∣ primeProduct P :=
      (primeProduct_dvd_iff_all_dvd P hprime (primeProduct P)).mp
        (dvd_refl (primeProduct P)) p.val p.property
    have hpprod : p.val ∣ consecutiveProduct K s :=
      dvd_trans hpq hqprod
    obtain ⟨b, hbK, hpbs⟩ :=
      (prime_dvd_consecutiveProduct_iff (hprime p.val p.property)).mp hpprod
    refine ⟨b, Finset.mem_range.mpr hbK, ?_⟩
    have hcompat := globalUnitToRootBoxTuple_unitOfCoprime
      P hprime ell hcop p
    rw [globalUnitsRootBoxEquiv_apply, hcompat]
    have hzero : ((s + b : ℕ) : ZMod p.val) = 0 :=
      (ZMod.natCast_eq_zero_iff (s + b) p.val).mpr hpbs
    calc
      (ell : ZMod p.val) * (j : ZMod p.val) + (b : ZMod p.val) =
          ((j * ell + b : ℕ) : ZMod p.val) := by push_cast; ring
      _ = ((s + a + b : ℕ) : ZMod p.val) := by rw [hjmul]
      _ = (a : ZMod p.val) + ((s + b : ℕ) : ZMod p.val) := by
        push_cast
        ring
      _ = (a : ZMod p.val) := by rw [hzero]; ring
  have hbadTuple : globalUnitsRootBoxEquiv P hprime
      (ZMod.unitOfCoprime ell hcop) ∈
        shiftedRootBadTupleSet P K Y hprime :=
    (mem_shiftedRootBadTupleSet_iff P K Y hprime _).mpr
      ⟨a, haK, j, hjpos, hjY, hlocal⟩
  exact hgood (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbadTuple⟩)

end Erdos394
