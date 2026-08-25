import ErdosProblems.Erdos964.AffineCoprimeValueCounts
import Mathlib.Data.ZMod.Basic

/-!
# Dividing a progression by an invertible multiplier

These finite identities turn a fixed smaller-prime slice into a progression
for the larger prime. No endpoint approximation is used.
-/

namespace Erdos964

theorem exists_coprime_mul_residue (p q a : ℕ)
    (hpq : p.Coprime q) (haq : a.Coprime q) :
    ∃ b, b.Coprime q ∧ p * b ≡ a [MOD q] := by
  let v := ((p : ZMod q)⁻¹).val
  have hv : p * v ≡ 1 [MOD q] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [Nat.cast_mul, Nat.cast_one, v] using ZMod.mul_val_inv hpq
  have hpb : p * (v * a) ≡ a [MOD q] := by
    simpa only [mul_assoc, one_mul] using hv.mul_right a
  refine ⟨v * a, ?_, hpb⟩
  have hcop : (p * (v * a)).Coprime q := by
    change Nat.gcd (p * (v * a)) q = 1
    rw [hpb.gcd_eq]
    exact haq
  exact (Nat.coprime_mul_iff_left.mp hcop).2

theorem finiteResidueCount_mul_image (T : Finset ℕ) (p q a b : ℕ)
    (hp : 0 < p) (hpq : p.Coprime q) (hab : p * b ≡ a [MOD q]) :
    finiteResidueCount (T.image (fun r => p * r)) q a = finiteResidueCount T q b := by
  have hfilter : (T.image (fun r => p * r)).filter (fun m => m ≡ a [MOD q]) =
      (T.filter (fun r => r ≡ b [MOD q])).image (fun r => p * r) := by
    ext m
    constructor
    · intro hm
      obtain ⟨hmT, hma⟩ := Finset.mem_filter.mp hm
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hmT
      have hrb := Nat.ModEq.cancel_left_of_coprime hpq.symm (hma.trans hab.symm)
      exact Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, hrb⟩, rfl⟩
    · intro hm
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hm
      have hr' := Finset.mem_filter.mp hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨r, hr'.1, rfl⟩,
        (hr'.2.mul_left p).trans hab⟩
  unfold finiteResidueCount
  rw [hfilter]
  apply Finset.card_image_iff.mpr
  intro r _ s _ hrs
  exact Nat.eq_of_mul_eq_mul_left hp hrs

theorem finiteCoprimeCount_mul_image (T : Finset ℕ) (p q : ℕ)
    (hp : 0 < p) (hpq : p.Coprime q) :
    finiteCoprimeCount (T.image (fun r => p * r)) q = finiteCoprimeCount T q := by
  have hfilter : (T.image (fun r => p * r)).filter (fun m => m.Coprime q) =
      (T.filter (fun r => r.Coprime q)).image (fun r => p * r) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨r, hr, rfl⟩, hcop⟩
      exact ⟨r, ⟨hr, (Nat.coprime_mul_iff_left.mp hcop).2⟩, rfl⟩
    · rintro ⟨r, ⟨hr, hcop⟩, rfl⟩
      exact ⟨⟨r, hr, rfl⟩, Nat.coprime_mul_iff_left.mpr ⟨hpq, hcop⟩⟩
  unfold finiteCoprimeCount
  rw [hfilter]
  apply Finset.card_image_iff.mpr
  intro r _ s _ hrs
  exact Nat.eq_of_mul_eq_mul_left hp hrs

theorem affineCoprimeValueCount_mul_image_error (A B : Fin 3 → ℕ) (j : Fin 3)
    (N q p : ℕ) (hA : 0 < A j) (hq : 0 < q) (hBA : (B j).Coprime (A j))
    (hp : 0 < p) (hpq : p.Coprime (A j * q)) (T : Finset ℕ)
    (hS : T.image (fun r => p * r) ⊆
      Finset.Ico (A j * N + B j) (A j * (2 * N) + B j))
    (E : ℝ) (hE : ∀ a, a.Coprime (A j * q) →
      |(finiteResidueCount T (A j * q) a : ℝ) -
        (finiteCoprimeCount T (A j * q) : ℝ) / (A j * q).totient| ≤ E) :
    |(affineCoprimeValueCount A B j N q (T.image (fun r => p * r)) : ℝ) -
      (affineCoprimeProductRoots A B j q).card *
        ((finiteCoprimeCount T (A j * q) : ℝ) / (A j * q).totient)| ≤
      (affineCoprimeProductRoots A B j q).card * E := by
  have h := affineCoprimeValueCount_error_le A B j N q hA hq hBA
    (T.image (fun r => p * r)) hS E
  rw [finiteCoprimeCount_mul_image T p (A j * q) hp hpq] at h
  apply h
  intro a ha
  obtain ⟨b, hb, hab⟩ := exists_coprime_mul_residue p (A j * q) a hpq ha
  rw [finiteResidueCount_mul_image T p (A j * q) a b hp hpq hab]
  exact hE b hb

end Erdos964
