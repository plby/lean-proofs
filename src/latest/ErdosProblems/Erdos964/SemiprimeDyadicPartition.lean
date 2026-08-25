import ErdosProblems.Erdos964.CharacterReduction
import BoundedGaps.BombieriVinogradov.Analytic.Dyadic

/-!
# Partitioning the smaller prime into dyadic blocks

The larger prime is truncated at `L²/M` within the block `(M,2M]`.
The exact product cutoff makes this truncation harmless. Unique ordered
prime factorization ensures that the partition counts each semiprime once.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

def semiprimesAtScale (P : Finset ℕ) (L X : ℕ) : Finset ℕ :=
  primeProductBlock P ((Finset.Ioc L (L ^ 2)).filter Nat.Prime) X

def dyadicSemiprimesAtScale (P : Finset ℕ) (L X α : ℕ) : Finset ℕ :=
  primeProductBlock (P.filter (fun p => p ∈ dyadicBlock α))
    ((Finset.Ioc L (L ^ 2 / 2 ^ α)).filter Nat.Prime) X

theorem semiprimesAtScale_subset_E2 (P : Finset ℕ) (C L X : ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ C < p) (hPL : ∀ p ∈ P, p ≤ L) :
    ↑(semiprimesAtScale P L X) ⊆ E2 C := by
  apply primeProductBlock_subset_E2 C X P _ hP
  · intro q hq
    exact (Finset.mem_filter.mp hq).2
  · intro p hp q hq
    exact (hPL p hp).trans_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).1

theorem prime_slice_truncate_at_scale (L X M p : ℕ) (hM : 0 < M)
    (hMp : M ≤ p) (hX : X ≤ L ^ 2) :
    ((Finset.Ioc L (L ^ 2)).filter Nat.Prime).filter (fun r => p * r ≤ X) =
      ((Finset.Ioc L (L ^ 2 / M)).filter Nat.Prime).filter (fun r => p * r ≤ X) := by
  apply Finset.ext
  intro r
  constructor
  · intro hr
    obtain ⟨hrprime, hrprod⟩ := Finset.mem_filter.mp hr
    obtain ⟨hrIoc, hprime⟩ := Finset.mem_filter.mp hrprime
    have hMr : r * M ≤ L ^ 2 := by
      calc
        r * M = M * r := mul_comm _ _
        _ ≤ p * r := Nat.mul_le_mul_right r hMp
        _ ≤ X := hrprod
        _ ≤ _ := hX
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hrIoc).1,
        (Nat.le_div_iff_mul_le hM).mpr hMr⟩, hprime⟩, hrprod⟩
  · intro hr
    obtain ⟨hrprime, hrprod⟩ := Finset.mem_filter.mp hr
    obtain ⟨hrIoc, hprime⟩ := Finset.mem_filter.mp hrprime
    obtain ⟨hrL, hrU⟩ := Finset.mem_Ioc.mp hrIoc
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hrL, hrU.trans (Nat.div_le_self _ _)⟩, hprime⟩, hrprod⟩

theorem sum_semiprimesAtScale_eq_dyadic {A : Type*} [AddCommMonoid A]
    (P : Finset ℕ) (L X : ℕ) (w : ℕ → A)
    (hP : ∀ p ∈ P, p.Prime) (hPL : ∀ p ∈ P, p ≤ L) (hX : X ≤ L ^ 2) :
    (∑ n ∈ semiprimesAtScale P L X, w n) =
      ∑ α ∈ dyadicExponentRange L, ∑ n ∈ dyadicSemiprimesAtScale P L X α, w n := by
  have hQ (U : ℕ) : ∀ q ∈ (Finset.Ioc L U).filter Nat.Prime, q.Prime :=
    fun q hq => (Finset.mem_filter.mp hq).2
  have hsep (U : ℕ) : ∀ p ∈ P, ∀ q ∈ (Finset.Ioc L U).filter Nat.Prime, p < q := by
    intro p hp q hq
    exact (hPL p hp).trans_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).1
  rw [semiprimesAtScale, sum_primeProductBlock P _ X w hP (hQ _) (hsep _)]
  rw [sum_eq_sum_dyadicBlocks (X := L) P (fun p hp => ⟨(hP p hp).two_le, hPL p hp⟩)]
  apply Finset.sum_congr rfl
  intro α hα
  have hPα : ∀ p ∈ P.filter (fun p => p ∈ dyadicBlock α), p.Prime :=
    fun p hp => hP p (Finset.mem_filter.mp hp).1
  have hsepα : ∀ p ∈ P.filter (fun p => p ∈ dyadicBlock α),
      ∀ q ∈ (Finset.Ioc L (L ^ 2 / 2 ^ α)).filter Nat.Prime, p < q :=
    fun p hp q hq => hsep _ p (Finset.mem_filter.mp hp).1 q hq
  rw [dyadicSemiprimesAtScale, sum_primeProductBlock _ _ X w hPα (hQ _) hsepα]
  apply Finset.sum_congr rfl
  intro p hp
  have hMp : 2 ^ α ≤ p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).2).1.le
  rw [prime_slice_truncate_at_scale L X (2 ^ α) p (by positivity) hMp hX]

theorem cast_card_semiprimesAtScale_eq_dyadic (P : Finset ℕ) (L X : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPL : ∀ p ∈ P, p ≤ L) (hX : X ≤ L ^ 2) :
    ((semiprimesAtScale P L X).card : ℝ) =
      ∑ α ∈ dyadicExponentRange L, ((dyadicSemiprimesAtScale P L X α).card : ℝ) := by
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
    sum_semiprimesAtScale_eq_dyadic P L X (fun _ => (1 : ℝ)) hP hPL hX

theorem cast_residueCount_semiprimesAtScale_eq_dyadic (P : Finset ℕ) (L X q a : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPL : ∀ p ∈ P, p ≤ L) (hX : X ≤ L ^ 2) :
    (finiteResidueCount (semiprimesAtScale P L X) q a : ℝ) =
      ∑ α ∈ dyadicExponentRange L,
        (finiteResidueCount (dyadicSemiprimesAtScale P L X α) q a : ℝ) := by
  simpa only [finiteResidueCount, Finset.natCast_card_filter] using
    sum_semiprimesAtScale_eq_dyadic P L X
      (fun n => if n ≡ a [MOD q] then (1 : ℝ) else 0) hP hPL hX

theorem semiprimesAtScale_error_eq_sum_dyadic (P : Finset ℕ) (L X q a : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPL : ∀ p ∈ P, p ≤ L) (hX : X ≤ L ^ 2) :
    (finiteResidueCount (semiprimesAtScale P L X) q a : ℝ) -
        ((semiprimesAtScale P L X).card : ℝ) / q.totient =
      ∑ α ∈ dyadicExponentRange L,
        ((finiteResidueCount (dyadicSemiprimesAtScale P L X α) q a : ℝ) -
          ((dyadicSemiprimesAtScale P L X α).card : ℝ) / q.totient) := by
  rw [cast_residueCount_semiprimesAtScale_eq_dyadic P L X q a hP hPL hX,
    cast_card_semiprimesAtScale_eq_dyadic P L X hP hPL hX,
    Finset.sum_sub_distrib, Finset.sum_div]

end Erdos964
