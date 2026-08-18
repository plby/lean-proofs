/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.DenseBox
import ErdosProblems.Erdos186.CFP.Witness

/-!
# Source-shaped assembly of the final CFP witness

The random partition and greedy stages produce pairwise disjoint reserve
sets.  The dense-box stage is naturally stated for a heterogeneous sum of
the subset-sum sets of those reserves.  This file performs the exact finite
conversion from that heterogeneous coverage to subset-sum coverage by the
union of the reserves, and packages the resulting data as an
`EnhancedCFPWitness`.
-/

namespace Erdos186.CFP

open scoped BigOperators

noncomputable section

/-- The reserve obtained by joining all disjoint color-part reserves. -/
def reserveUnion {d ell : ℕ}
    (reserve : Fin ell → Finset (LatticePoint d)) :
    Finset (LatticePoint d) :=
  Finset.univ.biUnion reserve

theorem reserve_subset_reserveUnion {d ell : ℕ}
    (reserve : Fin ell → Finset (LatticePoint d)) (i : Fin ell) :
    reserve i ⊆ reserveUnion reserve := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩

/-- Pairwise disjointness makes the size of the joined reserve exactly the
sum of the sizes of the color-part reserves. -/
theorem card_reserveUnion_of_pairwiseDisjoint {d ell : ℕ}
    (reserve : Fin ell → Finset (LatticePoint d))
    (hdisjoint : (Set.univ : Set (Fin ell)).PairwiseDisjoint reserve) :
    (reserveUnion reserve).card = ∑ i, (reserve i).card := by
  apply Finset.card_biUnion
  intro i _hi j _hj hij
  exact hdisjoint (Set.mem_univ i) (Set.mem_univ j) hij

theorem reserveUnion_subset {d ell : ℕ}
    {reserve : Fin ell → Finset (LatticePoint d)}
    {A : Finset (LatticePoint d)} (hreserve : ∀ i, reserve i ⊆ A) :
    reserveUnion reserve ⊆ A := by
  intro x hx
  obtain ⟨i, _hi, hxi⟩ := Finset.mem_biUnion.mp hx
  exact hreserve i hxi

/-- A choice of one subset sum from each pairwise disjoint reserve is a
single subset sum of their union.  This is the precise bridge from the
heterogeneous dense-box conclusion to the reserve coverage field in the
CFP witness. -/
theorem heterogeneous_subsetSums_subset_reserveUnion {d ell : ℕ}
    (reserve : Fin ell → Finset (LatticePoint d))
    (hdisjoint : (Set.univ : Set (Fin ell)).PairwiseDisjoint reserve) :
    heterogeneousSumset (fun i ↦ GAP.subsetSums (reserve i)) ⊆
      GAP.subsetSums (reserveUnion reserve) := by
  classical
  intro x hx
  obtain ⟨a, ha, rfl⟩ := mem_heterogeneousSumset.mp hx
  choose chosen hchosen hsum using
    fun i ↦ GAP.mem_subsetSums_iff.mp (ha i)
  let joined : Finset (LatticePoint d) :=
    Finset.univ.biUnion chosen
  have hchosenDisjoint :
      (Set.univ : Set (Fin ell)).PairwiseDisjoint chosen := by
    intro i _hi j _hj hij
    exact (hdisjoint (Set.mem_univ i) (Set.mem_univ j) hij).mono
      (hchosen i) (hchosen j)
  apply GAP.mem_subsetSums_iff.mpr
  refine ⟨joined, ?_, ?_⟩
  · intro y hy
    obtain ⟨i, _hi, hyi⟩ := Finset.mem_biUnion.mp hy
    exact reserve_subset_reserveUnion reserve i (hchosen i hyi)
  · have hchosenDisjoint' :
        ((Finset.univ : Finset (Fin ell)) : Set (Fin ell)).PairwiseDisjoint
          chosen := by
      intro i _hi j _hj hij
      exact hchosenDisjoint (Set.mem_univ i) (Set.mem_univ j) hij
    rw [Finset.sum_biUnion hchosenDisjoint']
    exact Finset.sum_congr rfl fun i _hi ↦ hsum i

/-- Assemble the final enhanced witness from the data delivered by the
preprocessing/random-partition/greedy/dense-box chain.  The only coverage
input is the source-shaped heterogeneous sumset statement; disjointness
turns it into coverage by one reserve internally. -/
noncomputable def enhancedCFPWitness_of_disjoint_reserveFamily
    {d ell s D k loss scaleNum scaleDen rank : ℕ}
    {A core : Finset (LatticePoint d)}
    (reserve : Fin ell → Finset (LatticePoint d))
    (progression : GAP d rank) (translatePoint : LatticePoint d)
    (hdisjoint : (Set.univ : Set (Fin ell)).PairwiseDisjoint reserve)
    (hrank : rank ≤ D)
    (hcore : core ⊆ A)
    (hreserveCore : ∀ i, reserve i ⊆ core)
    (hcoreLarge : A.card ≤ core.card + loss)
    (hreserveSmall : (∑ i, (reserve i).card) ≤ s)
    (hcoreProgression : insert 0 core ⊆ progression.carrier)
    (hhomogeneous : progression.Homogeneous)
    (hcovered :
      translate translatePoint (progression.dilate k).carrier ⊆
        heterogeneousSumset (fun i ↦ GAP.subsetSums (reserve i)))
    (hdilateProper : (progression.dilate k).Proper)
    (hk : 0 < k)
    (hscaleNum : 0 < scaleNum) (hscaleDen : 0 < scaleDen)
    (hscaleLower : scaleNum * s ≤ scaleDen * k)
    (hscaleUpper : k ≤ s)
    (hproper : progression.Proper)
    (hsymmetric : progression.Symmetric)
    (hnondegenerate : progression.Nondegenerate)
    (htranslateHomogeneous :
      ∃ z : Fin rank → ℤ,
        translatePoint + (progression.dilate k).offset =
          (fun j ↦ ∑ i, z i * progression.steps i j)) :
    EnhancedCFPWitness A s D k loss where
  core := core
  reserved := reserveUnion reserve
  rank := rank
  rank_le := hrank
  progression := progression
  core_subset := hcore
  reserved_subset_core := reserveUnion_subset hreserveCore
  core_large := hcoreLarge
  reserved_small := by
    rw [card_reserveUnion_of_pairwiseDisjoint reserve hdisjoint]
    exact hreserveSmall
  core_zero_subset := hcoreProgression
  homogeneous := hhomogeneous
  translatePoint := translatePoint
  covered := hcovered.trans
    (heterogeneous_subsetSums_subset_reserveUnion reserve hdisjoint)
  dilate_proper := hdilateProper
  k_pos := hk
  scaleNum := scaleNum
  scaleDen := scaleDen
  scaleNum_pos := hscaleNum
  scaleDen_pos := hscaleDen
  scale_lower := hscaleLower
  scale_upper := hscaleUpper
  progression_proper := hproper
  progression_symmetric := hsymmetric
  progression_nondegenerate := hnondegenerate
  covered_translate_homogeneous := htranslateHomogeneous

end

end Erdos186.CFP
