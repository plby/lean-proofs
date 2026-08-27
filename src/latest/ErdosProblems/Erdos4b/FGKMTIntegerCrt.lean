/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

/-!
# Finite coprime CRT systems on the whole integer line

Negative shifts and negative interval endpoints are retained as integers.
The ordinary finite natural CRT supplies a representative after reducing
each residue, and coprimality identifies its exact product period.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem int_modEq_nat_prod_iff (m : α → ℕ)
    (hpair : Pairwise (fun i j => (m i).Coprime (m j))) (a b : ℤ) :
    a ≡ b [ZMOD (∏ i, m i : ℕ)] ↔ ∀ i, a ≡ b [ZMOD m i] := by
  simp only [Int.modEq_iff_dvd, Int.natCast_dvd]
  constructor
  · intro hd i
    exact (Finset.dvd_prod_of_mem m (Finset.mem_univ i)).trans hd
  · intro hd
    exact Fintype.prod_dvd_of_isRelPrime
      (fun i j hij => Nat.coprime_iff_isRelPrime.mp (hpair hij)) hd

theorem exists_integerCrt_class (m : α → ℕ) (hm : ∀ i, 0 < m i)
    (hpair : Pairwise (fun i j => (m i).Coprime (m j))) (a : α → ℤ) :
    ∃ r : ℤ, ∀ n : ℤ,
      (∀ i, n ≡ a i [ZMOD m i]) ↔ n ≡ r [ZMOD (∏ i, m i : ℕ)] := by
  classical
  have hex (i : α) := Int.existsUnique_equiv_nat (a i)
    (by exact_mod_cast hm i : (0 : ℤ) < m i)
  choose b _hb hba using hex
  let z := Nat.chineseRemainderOfFinset b m Finset.univ
    (fun i _ => (hm i).ne') (hpair.set_pairwise _)
  have hz (i : α) : (z.val : ℤ) ≡ a i [ZMOD m i] := by
    have hzb : (z.val : ℤ) ≡ b i [ZMOD m i] :=
      Int.natCast_modEq_iff.mpr (z.property i (Finset.mem_univ i))
    exact hzb.trans (hba i)
  refine ⟨z.val, fun n => ?_⟩
  rw [int_modEq_nat_prod_iff m hpair]
  exact ⟨fun hn i => (hn i).trans (hz i).symm,
    fun hn i => (hn i).trans (hz i)⟩

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_integerCrt_class
