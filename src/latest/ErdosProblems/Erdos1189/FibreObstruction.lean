/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
An elementary fibre-counting obstruction for Erdős Problem 1189.
Formal author: OpenAI Codex.

This proves the obstruction used for the two-prime divisor construction
directly, without taking Simpson's theorem or Sun's theorem as assumptions.
-/

import ErdosProblems.Erdos1189.Density
import Mathlib.Data.Nat.ChineseRemainder

namespace Erdos1189

open Finset

/-- Positions in one finite period covered by the indicated natural residues. -/
def coveredPositions (D : Finset ℕ) (a : ℕ → ℕ) (N : ℕ) : Finset ℕ :=
  D.biUnion fun d => (range N).filter (fun x => x ≡ a d [MOD d])

lemma mem_coveredPositions {D : Finset ℕ} {a : ℕ → ℕ} {N x : ℕ} :
    x ∈ coveredPositions D a N ↔ x < N ∧ ∃ d ∈ D, x ≡ a d [MOD d] := by
  simp only [coveredPositions, mem_biUnion, mem_filter, mem_range]
  aesop

lemma card_coveredPositions_le {D : Finset ℕ} {a : ℕ → ℕ} {N : ℕ}
    (hpos : ∀ d ∈ D, 0 < d) (hdiv : ∀ d ∈ D, d ∣ N) :
    (coveredPositions D a N).card ≤ ∑ d ∈ D, N / d := by
  apply card_biUnion_le.trans
  apply sum_le_sum
  intro d hd
  exact (card_residue_class (hpos d hd) (hdiv d hd) _).le

/-- A base of density `1 - 1/N`, together with exactly `p` classes on distinct
`p`-fibres and a modulus `p*N`, cannot lose any modulus and still cover.
The fibre residues are not assumed distinct: coverage forces that fact. -/
theorem subset_eq_of_fibre_cover {D B E : Finset ℕ} {N p : ℕ} {a : ℕ → ℕ}
    (hN : 0 < N) (hp : 0 < p) (hcop : N.Coprime p)
    (hDpos : ∀ d ∈ D, 0 < d) (hDdiv : ∀ d ∈ D, d ∣ N)
    (hweight : (∑ d ∈ D, N / d) + 1 = N)
    (hBcard : B.card = p) (hBdiv : ∀ d ∈ B, p ∣ d) (hmax : p * N ∈ B)
    (hE : E ⊆ D ∪ B)
    (hcover : ∀ z : ℕ, ∃ d ∈ E, z ≡ a d [MOD d]) : E = D ∪ B := by
  let C := coveredPositions D a N
  have hCcard : C.card < N := by
    have := card_coveredPositions_le (a := a) hDpos hDdiv
    dsimp [C]
    omega
  have hnot : ¬ range N ⊆ C := by
    intro h
    have := card_le_card h
    rw [card_range] at this
    omega
  obtain ⟨x, hx, hxnot⟩ := not_subset.mp hnot
  have hxlt : x < N := mem_range.mp hx
  have hsurj : ∀ r ∈ range p, ∃ d ∈ B ∩ E, a d % p = r := by
    intro r hr
    obtain ⟨z, hzN, hzp⟩ := Nat.chineseRemainder hcop x r
    obtain ⟨d, hdE, hzd⟩ := hcover z
    have hdB : d ∈ B := by
      rcases mem_union.mp (hE hdE) with hdD | hdB
      · exact False.elim (hxnot (mem_coveredPositions.mpr
          ⟨hxlt, d, hdD, (hzN.of_dvd (hDdiv d hdD)).symm.trans hzd⟩))
      · exact hdB
    refine ⟨d, mem_inter.mpr ⟨hdB, hdE⟩, ?_⟩
    have hrd := hzp.symm.trans (hzd.of_dvd (hBdiv d hdB))
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (mem_range.mp hr)] using hrd.symm
  have himage : (B ∩ E).image (fun d => a d % p) = range p := by
    apply Subset.antisymm
    · intro r hr
      obtain ⟨d, _, rfl⟩ := mem_image.mp hr
      exact mem_range.mpr (Nat.mod_lt _ hp)
    · intro r hr
      obtain ⟨d, hd, hrd⟩ := hsurj r hr
      exact mem_image.mpr ⟨d, hd, hrd⟩
  have hBE : B ∩ E = B := by
    apply eq_of_subset_of_card_le inter_subset_left
    calc
      B.card = p := hBcard
      _ = ((B ∩ E).image (fun d => a d % p)).card := by rw [himage, card_range]
      _ ≤ (B ∩ E).card := card_image_le
  have hBsub : B ⊆ E := by
    rw [← hBE]
    exact inter_subset_right
  have hinj : Set.InjOn (fun d => a d % p) B := by
    apply card_image_iff.mp
    rw [hBE] at himage
    rw [himage, card_range, hBcard]
  let A := D ∩ E
  have hApos : ∀ d ∈ A, 0 < d := fun d hd => hDpos d (mem_inter.mp hd).1
  have hAdiv : ∀ d ∈ A, d ∣ N := fun d hd => hDdiv d (mem_inter.mp hd).1
  have hsub : range N ⊆ coveredPositions A a N ∪ {a (p * N) % N} := by
    intro y hy
    by_cases hyA : y ∈ coveredPositions A a N
    · exact mem_union_left _ hyA
    apply mem_union_right
    apply mem_singleton.mpr
    obtain ⟨z, hzN, hzp⟩ := Nat.chineseRemainder hcop y (a (p * N))
    obtain ⟨d, hdE, hzd⟩ := hcover z
    have hdB : d ∈ B := by
      rcases mem_union.mp (hE hdE) with hdD | hdB
      · exact False.elim (hyA (mem_coveredPositions.mpr
          ⟨mem_range.mp hy, d, mem_inter.mpr ⟨hdD, hdE⟩,
            (hzN.of_dvd (hDdiv d hdD)).symm.trans hzd⟩))
      · exact hdB
    have hdeq : d = p * N := by
      apply hinj hdB hmax
      exact ((hzd.of_dvd (hBdiv d hdB)).symm.trans hzp)
    subst d
    have hyd := hzN.symm.trans (hzd.of_dvd (dvd_mul_left N p))
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (mem_range.mp hy)] using hyd
  have hAbound : N ≤ (∑ d ∈ A, N / d) + 1 := by
    calc
      N = (range N).card := (card_range N).symm
      _ ≤ (coveredPositions A a N ∪ {a (p * N) % N}).card := card_le_card hsub
      _ ≤ (coveredPositions A a N).card + ({a (p * N) % N} : Finset ℕ).card :=
        card_union_le _ _
      _ ≤ (∑ d ∈ A, N / d) + 1 := by
        rw [card_singleton]
        exact Nat.add_le_add_right (card_coveredPositions_le hApos hAdiv) 1
  have hDsub : D ⊆ E := by
    intro d hd
    by_contra hdE
    have hdA : d ∉ A := by simp [A, hdE]
    have hinsert : insert d A ⊆ D := by
      exact insert_subset hd inter_subset_left
    have hsum : (∑ n ∈ A, N / n) + N / d ≤ ∑ n ∈ D, N / n := by
      have := sum_le_sum_of_subset_of_nonneg hinsert
        (fun n _ _ => Nat.zero_le (N / n))
      simpa only [sum_insert hdA, Nat.add_comm] using this
    have hquot : 0 < N / d :=
      Nat.div_pos (Nat.le_of_dvd hN (hDdiv d hd)) (hDpos d hd)
    omega
  exact Subset.antisymm hE (union_subset hDsub hBsub)

/-- A covering set satisfying the fibre-counting hypotheses is irreducible. -/
theorem irreducible_of_fibre_cover {D B : Finset ℕ} {N p : ℕ}
    (hN : 0 < N) (hp : 0 < p) (hcop : N.Coprime p)
    (hDpos : ∀ d ∈ D, 0 < d) (hDdiv : ∀ d ∈ D, d ∣ N)
    (hweight : (∑ d ∈ D, N / d) + 1 = N)
    (hBcard : B.card = p) (hBdiv : ∀ d ∈ B, p ∣ d) (hmax : p * N ∈ B)
    (hcover : IsCoveringSet (D ∪ B)) : IsIrreducibleCoveringSet (D ∪ B) := by
  refine ⟨hcover, ?_⟩
  intro E hE hEcover
  obtain ⟨a, ha⟩ := hEcover.2
  have hnat : ∀ z : ℕ, ∃ d ∈ E, z ≡ canonicalResidue a d [MOD d] := by
    intro z
    obtain ⟨d, hd, hzd⟩ := ha z
    refine ⟨d, hd, (nat_modEq_canonicalResidue_iff a ?_ z).mpr hzd⟩
    exact lt_trans Nat.zero_lt_one (hEcover.1 d hd)
  exact hE.ne (subset_eq_of_fibre_cover hN hp hcop hDpos hDdiv hweight
    hBcard hBdiv hmax hE.subset hnat)

end Erdos1189
