/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPreSieveUnitBijection
import ErdosProblems.Erdos4b.FGKMTPrimePreSieveResidues

/-!
# Exact prime-presieve cardinality and density

Natural representatives transport the unit-group bijection to the
literal residue sets. The result is independent of the pinned prime
and of the pin, and applies to every positive presieve modulus.
-/

namespace Erdos4b.FGKMT

noncomputable section

variable {ι : Type*} [Fintype ι]

def ordinaryPreSieveResidueEquiv {W : ℕ} (hW : 0 < W) (a : ι → ℤ) :
    {v : ℕ // v ∈ preSieveResidues W a} ≃
      {t : ZMod W // ∀ i, IsUnit (t + (a i : ZMod W))} := by
  classical
  let : NeZero W := ⟨hW.ne'⟩
  refine {
    toFun := fun v => ⟨(v.val : ZMod W), ?_⟩
    invFun := fun t => ⟨t.val.val, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have h := (preSieveCondition_iff_isUnit W a (v.val : ℤ)).mp
      (mem_preSieveResidues_iff.mp v.property).2
    simpa only [Int.cast_natCast] using h
  · apply mem_preSieveResidues_iff.mpr
    refine ⟨ZMod.val_lt t.val, ?_⟩
    apply (preSieveCondition_iff_isUnit W a (t.val.val : ℤ)).mpr
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using t.property
  · intro v
    apply Subtype.ext
    exact ZMod.val_natCast_of_lt (mem_preSieveResidues_iff.mp v.property).1
  · intro t
    apply Subtype.ext
    exact ZMod.natCast_zmod_val t.val

def primePreSieveResidueEquiv {W : ℕ} (hW : 0 < W) (Q : ℕ) (a : ι → ℤ) (j : ι) :
    {v : ℕ // v ∈ primePreSieveResidues W Q a j} ≃
      {u : (ZMod W)ˣ // ∀ i,
        IsUnit ((Q : ZMod W) + ((a i : ZMod W) - a j) * (u : ZMod W))} := by
  classical
  let : NeZero W := ⟨hW.ne'⟩
  refine {
    toFun := fun v => ⟨ZMod.unitOfCoprime v.val
      (mem_primePreSieveResidues_iff.mp v.property).2.1, ?_⟩
    invFun := fun u => ⟨(u.val : ZMod W).val, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have h := ((primePreSieveCondition_iff_isUnit W Q v.val a j).mp
      (mem_primePreSieveResidues_iff.mp v.property).2).2
    simpa only [ZMod.coe_unitOfCoprime] using h
  · apply mem_primePreSieveResidues_iff.mpr
    refine ⟨ZMod.val_lt (u.val : ZMod W), ?_⟩
    apply (primePreSieveCondition_iff_isUnit W Q _ a j).mpr
    constructor
    · simpa only [ZMod.natCast_zmod_val] using u.val.isUnit
    · simpa only [ZMod.natCast_zmod_val] using u.property
  · intro v
    apply Subtype.ext
    exact ZMod.val_natCast_of_lt (mem_primePreSieveResidues_iff.mp v.property).1
  · intro u
    apply Subtype.ext
    apply Units.ext
    exact ZMod.natCast_zmod_val (u.val : ZMod W)

theorem card_primePreSieveResidues {W Q : ℕ} (hW : 0 < W) (hQ : Q.Coprime W)
    (a : ι → ℤ) (j : ι) :
    (primePreSieveResidues W Q a j).card = (preSieveResidues W a).card := by
  classical
  let : NeZero W := ⟨hW.ne'⟩
  let e := ((primePreSieveResidueEquiv hW Q a j).trans
    (preSieveUnitEquiv (fun i => (a i : ZMod W)) j (ZMod.unitOfCoprime Q hQ))).trans
      (ordinaryPreSieveResidueEquiv hW a).symm
  simpa using Fintype.card_congr e

def primePreSieveDensity (W Q : ℕ) (a : ι → ℤ) (j : ι) : ℝ :=
  ((primePreSieveResidues W Q a j).card : ℝ) / W.totient

theorem primePreSieveDensity_eq {W Q : ℕ} (hW : 0 < W) (hQ : Q.Coprime W)
    (a : ι → ℤ) (j : ι) :
    primePreSieveDensity W Q a j = ((W : ℝ) / W.totient) * preSieveDensity W a := by
  unfold primePreSieveDensity preSieveDensity
  rw [card_primePreSieveResidues hW hQ a j]
  have hW0 : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  field_simp [hW0]

theorem totientDensity_presieve_cancellation {B W : ℕ} (hB : 0 < B) (hW : 0 < W)
    (hBW : B.Coprime W) :
    ((W : ℝ) / W.totient) * ((B * W).totient : ℝ) / (B * W) = (B.totient : ℝ) / B := by
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have hW0 : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  have hphi : (W.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hW).ne'
  rw [Nat.totient_mul hBW, Nat.cast_mul]
  field_simp [hB0, hW0, hphi]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.card_primePreSieveResidues
#print axioms Erdos4b.FGKMT.primePreSieveDensity_eq
#print axioms Erdos4b.FGKMT.totientDensity_presieve_cancellation
