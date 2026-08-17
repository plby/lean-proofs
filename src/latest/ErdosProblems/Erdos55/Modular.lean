/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos55.FiniteSums
import ErdosProblems.Erdos55.Cyclic

/-!
# Modular subset sums for Erdős Problem 55

The central result is CFP Lemma 2.5.  It converts distinct residue classes
of subset sums modulo `m` into genuinely new ordinary subset sums after the
fresh element `m` is adjoined.  The proof selects the largest old subset sum
in each represented residue class.
-/

namespace Erdos55

/-- Residue classes modulo `m` represented by subset sums of `B`. -/
def residueSubsetSums (m : ℕ) (B : Finset ℕ) : Finset (ZMod m) :=
  (subsetSumValues B).image fun n : ℕ ↦ (n : ZMod m)

@[simp]
theorem mem_residueSubsetSums {m : ℕ} {B : Finset ℕ} {z : ZMod m} :
    z ∈ residueSubsetSums m B ↔
      ∃ n ∈ subsetSumValues B, (n : ZMod m) = z := by
  simp [residueSubsetSums]

theorem residueSubsetSums_mono {m : ℕ} {B C : Finset ℕ} (hBC : B ⊆ C) :
    residueSubsetSums m B ⊆ residueSubsetSums m C := by
  intro z hz
  obtain ⟨n, hn, rfl⟩ := mem_residueSubsetSums.mp hz
  exact mem_residueSubsetSums.mpr ⟨n, subsetSumValues_mono hBC hn, rfl⟩

/-- **CFP Lemma 2.5 (adjoining the modulus).**  If the positive modulus is
not already one of the available summands, adjoining it creates at least
one new ordinary subset sum for every residue class previously represented.
-/
theorem card_subsetSumValues_add_card_residue_le_insert {m : ℕ} {B : Finset ℕ}
    (hmpos : 0 < m) (hmB : m ∉ B) :
    (subsetSumValues B).card + (residueSubsetSums m B).card ≤
      (subsetSumValues (insert m B)).card := by
  classical
  letI : NeZero m := ⟨hmpos.ne'⟩
  let old := subsetSumValues B
  let residues := residueSubsetSums m B
  let fiber (z : ZMod m) : Finset ℕ := old.filter fun n ↦ (n : ZMod m) = z
  have hfiber : ∀ z ∈ residues, (fiber z).Nonempty := by
    intro z hz
    obtain ⟨n, hn, hnz⟩ := mem_residueSubsetSums.mp hz
    exact ⟨n, by simpa [fiber, old, hnz] using hn⟩
  let top : residues → ℕ := fun z ↦ (fiber z).max' (hfiber z z.2)
  have htop_mem (z : residues) : top z ∈ old := by
    have hz := (fiber z).max'_mem (hfiber z z.2)
    exact (Finset.mem_filter.mp hz).1
  have htop_residue (z : residues) : ((top z : ℕ) : ZMod m) = z := by
    have hz := (fiber z).max'_mem (hfiber z z.2)
    exact (Finset.mem_filter.mp hz).2
  have htop_max (z : residues) {n : ℕ} (hnold : n ∈ old)
      (hnz : (n : ZMod m) = z) : n ≤ top z := by
    apply (fiber z).le_max'
    exact Finset.mem_filter.mpr ⟨hnold, hnz⟩
  let topEmbedding : residues ↪ ℕ :=
    ⟨top, by
      intro z w hzw
      apply Subtype.ext
      calc
        (z : ZMod m) = (top z : ZMod m) := (htop_residue z).symm
        _ = (top w : ZMod m) := by rw [hzw]
        _ = (w : ZMod m) := htop_residue w⟩
  let addModulus : ℕ ↪ ℕ :=
    ⟨fun n ↦ n + m, fun _ _ h ↦ Nat.add_right_cancel h⟩
  let fresh : Finset ℕ := Finset.univ.map (topEmbedding.trans addModulus)
  have hfresh_card : fresh.card = residues.card := by
    simp [fresh]
  have hfresh_subset : fresh ⊆ subsetSumValues (insert m B) := by
    intro n hn
    obtain ⟨z, -, rfl⟩ := Finset.mem_map.mp hn
    change top z + m ∈ subsetSumValues (insert m B)
    exact add_mem_subsetSumValues_insert hmB (by simpa [old] using htop_mem z)
  have hfresh_disjoint : Disjoint old fresh := by
    rw [Finset.disjoint_left]
    intro n hnold hnfresh
    obtain ⟨z, -, rfl⟩ := Finset.mem_map.mp hnfresh
    have hcast : ((top z + m : ℕ) : ZMod m) = z := by
      simpa using htop_residue z
    have hle : top z + m ≤ top z :=
      htop_max z hnold hcast
    omega
  have hunion_subset : old ∪ fresh ⊆ subsetSumValues (insert m B) := by
    intro n hn
    rcases Finset.mem_union.mp hn with hn | hn
    · exact subsetSumValues_subset_insert m B (by simpa [old] using hn)
    · exact hfresh_subset hn
  calc
    (subsetSumValues B).card + (residueSubsetSums m B).card
        = old.card + fresh.card := by rw [hfresh_card]
    _ = (old ∪ fresh).card := (Finset.card_union_of_disjoint hfresh_disjoint).symm
    _ ≤ (subsetSumValues (insert m B)).card := Finset.card_le_card hunion_subset

end Erdos55
