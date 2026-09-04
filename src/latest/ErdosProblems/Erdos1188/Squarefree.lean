import ErdosProblems.Erdos1188.Basic

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos1188

open scoped BigOperators

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

def natResidueFin (r d : ℕ) (hd : d ≠ 0) : Fin d :=
  ⟨r % d, Nat.mod_lt r (Nat.pos_of_ne_zero hd)⟩

theorem satisfies_nat_iff_fin_eq {d r a : ℕ} (hd : 0 < d) (ha : a < d) :
    Satisfies (r : ℤ) (d, a) ↔
      natResidueFin r d (Nat.ne_of_gt hd) = (⟨a, ha⟩ : Fin d) := by
  unfold Satisfies
  rw [← Int.natCast_mod]
  norm_cast
  constructor
  · intro h
    apply Fin.ext
    simpa [natResidueFin] using h
  · intro h
    have hv := congrArg Fin.val h
    simpa [natResidueFin] using hv

theorem zmod_finEquiv_apply (n : ℕ) [NeZero n] (r : Fin n) :
    ZMod.finEquiv n r = (r.val : ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    apply Fin.ext
    change r.val = r.val % (n + 1)
    exact (Nat.mod_eq_of_lt r.isLt).symm

noncomputable def crtFinEquiv (q : ι → ℕ)
    (hq : ∀ i, 0 < q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q)) :
    Fin (∏ i, q i) ≃ ((i : ι) → ZMod (q i)) := by
  letI : NeZero (∏ i, q i) := ⟨Finset.prod_ne_zero_iff.mpr fun i _ => Nat.ne_of_gt (hq i)⟩
  exact (ZMod.finEquiv (∏ i, q i)).toEquiv.trans (ZMod.prodEquivPi q hcop).toEquiv

theorem crtFinEquiv_apply (q : ι → ℕ)
    (hq : ∀ i, 0 < q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (r : Fin (∏ i, q i)) (i : ι) :
    crtFinEquiv q hq hcop r i = (r.val : ZMod (q i)) := by
  let : NeZero (∏ i, q i) := ⟨Finset.prod_ne_zero_iff.mpr fun i _ => Nat.ne_of_gt (hq i)⟩
  change (ZMod.prodEquivPi q hcop (ZMod.finEquiv (∏ i, q i) r)) i = _
  rw [zmod_finEquiv_apply]
  simp [ZMod.prodEquivPi, Ideal.quotientInfRingEquivPiQuotient]

/-- Product of a selected subfamily of pairwise-coprime moduli. -/
def subsetModulus (q : ι → ℕ) (J : Finset ι) : ℕ := ∏ j : ↥J, q j

theorem subsetModulus_pos (q : ι → ℕ) (hq : ∀ i, 0 < q i) (J : Finset ι) :
    0 < subsetModulus q J := by
  apply Finset.prod_pos
  intro j _
  exact hq j

noncomputable def subsetCrtFinEquiv (q : ι → ℕ)
    (hq : ∀ i, 0 < q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (J : Finset ι) :
    Fin (subsetModulus q J) ≃ ((j : ↥J) → ZMod (q j)) := by
  apply crtFinEquiv (fun j : ↥J => q j)
  · exact fun j => hq j
  · intro a b hab
    apply hcop
    intro heq
    apply hab
    exact Subtype.ext heq

/-- Canonical CRT residue having the prescribed coordinates on `J`. -/
noncomputable def subsetCrtResidue (q : ι → ℕ)
    (hq : ∀ i, 0 < q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (J : Finset ι) (v : (j : ↥J) → ZMod (q j)) : ℕ :=
  ((subsetCrtFinEquiv q hq hcop J).symm v).val

noncomputable def subsetCrtClass (q : ι → ℕ)
    (hq : ∀ i, 0 < q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (J : Finset ι) (v : (j : ↥J) → ZMod (q j)) : CongruenceClass :=
  (subsetModulus q J, subsetCrtResidue q hq hcop J v)

theorem subsetModulus_eq_prod (q : ι → ℕ) (J : Finset ι) :
    subsetModulus q J = ∏ j ∈ J, q j := by
  unfold subsetModulus
  symm
  exact Finset.prod_subtype J (fun _ => Iff.rfl) q

theorem subsetModulus_dvd_full (q : ι → ℕ) (J : Finset ι) :
    subsetModulus q J ∣ ∏ i, q i := by
  rw [subsetModulus_eq_prod]
  exact Finset.prod_dvd_prod_of_subset J Finset.univ q (Finset.subset_univ J)

/-- A nonempty CRT support with factors at least two gives a valid canonical
congruence class. -/
theorem subsetCrtClass_valid (q : ι → ℕ)
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (J : Finset ι) (hJ : J.Nonempty)
    (v : (j : ↥J) → ZMod (q j)) :
    (2 ≤ (subsetCrtClass q (fun i => lt_of_lt_of_le Nat.zero_lt_two (hq i)) hcop J v).1) ∧
      (subsetCrtClass q (fun i => lt_of_lt_of_le Nat.zero_lt_two (hq i)) hcop J v).2 <
        (subsetCrtClass q (fun i => lt_of_lt_of_le Nat.zero_lt_two (hq i)) hcop J v).1 := by
  let hqpos : ∀ i, 0 < q i := fun i => lt_of_lt_of_le Nat.zero_lt_two (hq i)
  obtain ⟨i, hi⟩ := hJ
  have hfac : q i ∣ subsetModulus q J := by
    rw [subsetModulus_eq_prod]
    exact Finset.dvd_prod_of_mem q hi
  constructor
  · exact le_trans (hq i) (Nat.le_of_dvd (subsetModulus_pos q hqpos J) hfac)
  · exact ((subsetCrtFinEquiv q hqpos hcop J).symm v).isLt

/-- A CRT class fixes exactly the selected coordinates to their prescribed
values. -/
theorem satisfies_subsetCrtClass_iff (q : ι → ℕ)
    (hq : ∀ i, 0 < q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (J : Finset ι) (v : (j : ↥J) → ZMod (q j))
    (r : Fin (∏ i, q i)) :
    Satisfies (r.val : ℤ) (subsetCrtClass q hq hcop J v) ↔
      ∀ j : ↥J, crtFinEquiv q hq hcop r j = v j := by
  let d := subsetModulus q J
  have hd : 0 < d := subsetModulus_pos q hq J
  have ha : subsetCrtResidue q hq hcop J v < d :=
    ((subsetCrtFinEquiv q hq hcop J).symm v).isLt
  change Satisfies (r.val : ℤ) (d, subsetCrtResidue q hq hcop J v) ↔ _
  rw [satisfies_nat_iff_fin_eq hd ha]
  let rf : Fin d := natResidueFin r.val d (Nat.ne_of_gt hd)
  let af : Fin d := ⟨subsetCrtResidue q hq hcop J v, ha⟩
  have hresFin : af = (subsetCrtFinEquiv q hq hcop J).symm v := by
    apply Fin.ext
    rfl
  have hfactor (j : ↥J) : q j ∣ d := by
    exact Finset.dvd_prod_of_mem (fun k : ↥J => q k) (Finset.mem_univ j)
  have hcast (j : ↥J) : (rf.val : ZMod (q j)) = (r.val : ZMod (q j)) := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    apply Nat.ModEq.of_dvd (hfactor j)
    exact Nat.mod_modEq r.val d
  have hsub (j : ↥J) :
      subsetCrtFinEquiv q hq hcop J rf j = (r.val : ZMod (q j)) := by
    change crtFinEquiv (fun k : ↥J => q k) _ _ rf j = _
    rw [crtFinEquiv_apply]
    exact hcast j
  constructor
  · intro heq j
    have heq' : rf = af := by simpa [rf, af] using heq
    rw [crtFinEquiv_apply q hq hcop]
    rw [← hsub j, heq']
    change subsetCrtFinEquiv q hq hcop J af j = _
    rw [hresFin, Equiv.apply_symm_apply]
  · intro hall
    apply (subsetCrtFinEquiv q hq hcop J).injective
    funext j
    change subsetCrtFinEquiv q hq hcop J rf j =
      subsetCrtFinEquiv q hq hcop J af j
    rw [hsub j, hresFin, Equiv.apply_symm_apply]
    rw [← hall j]
    exact (crtFinEquiv_apply q hq hcop r j).symm

end Erdos1188
