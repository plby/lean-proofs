/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPreSieveResidues

/-!
# Exact label-independent presieve normalization

Multiplication by a unit modulo the presieve modulus permutes its
allowed residues. No asymptotic or dimension-dependent error is incurred.
The shifts may be arbitrary integers.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem mem_preSieveResidues_iff {ι : Type*} [Fintype ι]
    {W v : ℕ} {a : ι → ℤ} :
    v ∈ preSieveResidues W a ↔ v < W ∧ preSieveCondition W a v := by
  classical
  simp only [preSieveResidues, Finset.mem_filter, Finset.mem_range]

theorem preSieveCondition_mul_iff {ι : Type*} [Fintype ι]
    {W P : ℕ} (hPW : P.Coprime W) (a : ι → ℤ) (n : ℤ) :
    preSieveCondition W (fun i => a i * P) (n * P) ↔ preSieveCondition W a n := by
  simp only [preSieveCondition, Nat.coprime_fintype_prod_left_iff, ← add_mul,
    Int.natAbs_mul, Int.natAbs_natCast, Nat.coprime_mul_iff_left]
  exact ⟨fun h i => (h i).1, fun h i => ⟨h i, hPW⟩⟩

theorem preSieveCondition_mul_mod_iff {ι : Type*} [Fintype ι]
    {W P : ℕ} (hPW : P.Coprime W) (a : ι → ℤ) (v : ℕ) :
    preSieveCondition W (fun i => a i * P) ((v * P % W : ℕ) : ℤ) ↔
      preSieveCondition W a v := by
  have hmod : ((v * P % W : ℕ) : ℤ) ≡ (v : ℤ) * P [ZMOD W] := by
    exact_mod_cast (Nat.mod_modEq (v * P) W)
  exact (preSieveCondition_iff_of_modEq _ hmod).trans (preSieveCondition_mul_iff hPW a v)

theorem card_preSieveResidues_mul {ι : Type*} [Fintype ι]
    {W P : ℕ} (hW : 0 < W) (hPW : P.Coprime W) (a : ι → ℤ) :
    (preSieveResidues W a).card = (preSieveResidues W (fun i => a i * P)).card := by
  classical
  let f : Fin W → Fin W := fun v => ⟨v.val * P % W, Nat.mod_lt _ hW⟩
  have hf : Function.Injective f := by
    intro u v huv
    have hm : u.val * P ≡ v.val * P [MOD W] := congrArg Fin.val huv
    exact Fin.ext ((hm.cancel_right_of_coprime hPW.symm).eq_of_lt_of_lt u.isLt v.isLt)
  have hs := Finite.surjective_of_injective hf
  apply Finset.card_bij (fun v _ => v * P % W)
  · intro v hv
    apply mem_preSieveResidues_iff.mpr
    exact ⟨Nat.mod_lt _ hW,
      (preSieveCondition_mul_mod_iff hPW a v).mpr (mem_preSieveResidues_iff.mp hv).2⟩
  · intro u hu v hv huv
    have hmod : u * P ≡ v * P [MOD W] := huv
    exact (hmod.cancel_right_of_coprime hPW.symm).eq_of_lt_of_lt
      (mem_preSieveResidues_iff.mp hu).1 (mem_preSieveResidues_iff.mp hv).1
  · intro w hw
    obtain ⟨v, hv⟩ := hs ⟨w, (mem_preSieveResidues_iff.mp hw).1⟩
    have hval : v.val * P % W = w := congrArg Fin.val hv
    refine ⟨v.val, mem_preSieveResidues_iff.mpr ⟨v.isLt, ?_⟩, hval⟩
    apply (preSieveCondition_mul_mod_iff hPW a v.val).mp
    rw [hval]
    exact (mem_preSieveResidues_iff.mp hw).2

def preSieveDensity {ι : Type*} [Fintype ι] (W : ℕ) (a : ι → ℤ) : ℝ :=
  ((preSieveResidues W a).card : ℝ) / W

theorem preSieveDensity_mul {ι : Type*} [Fintype ι]
    {W P : ℕ} (hW : 0 < W) (hPW : P.Coprime W) (a : ι → ℤ) :
    preSieveDensity W (fun i => a i * P) = preSieveDensity W a := by
  unfold preSieveDensity
  rw [card_preSieveResidues_mul hW hPW a]

theorem preSieveDensity_nonneg {ι : Type*} [Fintype ι] (W : ℕ) (a : ι → ℤ) :
    0 ≤ preSieveDensity W a := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg W)

theorem preSieveDensity_le_one {ι : Type*} [Fintype ι] {W : ℕ} (hW : 0 < W)
    (a : ι → ℤ) : preSieveDensity W a ≤ 1 := by
  apply (div_le_one (by exact_mod_cast hW : (0 : ℝ) < W)).mpr
  exact_mod_cast card_preSieveResidues_le W a

theorem preSieveDensity_ge_inv_of_witness {ι : Type*} [Fintype ι] {W : ℕ}
    (hW : 0 < W) (a : ι → ℤ) {n : ℤ} (hn : preSieveCondition W a n) :
    1 / (W : ℝ) ≤ preSieveDensity W a := by
  obtain ⟨v, hv, hnv, _huniq⟩ := exists_unique_natural_residue hW n
  have hmem : v ∈ preSieveResidues W a := mem_preSieveResidues_iff.mpr
    ⟨hv, (preSieveCondition_iff_of_modEq a hnv).mp hn⟩
  have hcard := Finset.card_pos.mpr ⟨v, hmem⟩
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg W)
  exact_mod_cast hcard

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.card_preSieveResidues_mul
#print axioms Erdos4b.FGKMT.preSieveDensity_ge_inv_of_witness
