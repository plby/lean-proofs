/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceTwoFamilyEncoding
import ErdosProblems.Erdos207.CommonThreatOrdering

/-! # Terminal-bridge common threats give literal two-family source exposures -/

namespace Erdos207.CommonThreatWitness

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {F G : ForbiddenFamilyOn V} {T T' : TripleOn V}

theorem first_exposure_omitted (u : CommonThreatWitness F G T T') (H : TripleSystemOn V) :
    (u.first \ u.firstExposureRoot H) \ (u.leftRemainder \ H) = {u.bridge} := by
  ext R
  constructor
  · intro hR
    obtain ⟨⟨hfirst, hnroot⟩, hnleft⟩ := mem_sdiff.mp hR |>.imp_left mem_sdiff.mp
    apply mem_singleton.mpr
    by_contra hne
    have hnT : R ≠ T := by
      intro heq
      exact hnroot (heq ▸ mem_insert_self T (u.leftRemainder ∩ H))
    have hleft : R ∈ u.leftRemainder := mem_erase.mpr ⟨hne, mem_erase.mpr ⟨hnT, hfirst⟩⟩
    have hRH : R ∈ H := by
      by_contra hnH
      exact hnleft (mem_sdiff.mpr ⟨hleft, hnH⟩)
    exact hnroot (mem_insert_of_mem (mem_inter.mpr ⟨hleft, hRH⟩))
  · intro hR
    have heq := mem_singleton.mp hR
    subst R
    exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨u.bridge_first, u.bridge_not_mem_firstExposureRoot H⟩,
      fun h ↦ (mem_erase.mp (mem_sdiff.mp h).1).1 rfl⟩

theorem second_exposure_omitted (u : CommonThreatWitness F G T T') (H : TripleSystemOn V)
    (hH : H ⊆ u.remainder) :
    (u.second \ insert T' (u.second ∩ H)) \ (u.rightRemainder \ H) = {u.bridge} := by
  have hswap : H ⊆ u.swap.remainder := by
    simpa only [swap, remainder, leftRemainder, rightRemainder, union_comm] using hH
  have hroot := u.swap.firstExposureRoot_eq_insert_inter H hswap
  have homit := u.swap.first_exposure_omitted H
  rw [hroot] at homit
  exact homit

theorem right_inter_first_subset_left (u : CommonThreatWitness F G T T') :
    u.rightRemainder ∩ u.first ⊆ u.leftRemainder := by
  intro R hR
  obtain ⟨hRright, hRfirst⟩ := mem_inter.mp hR
  have hm := mem_erase.mp hRright
  have hm' := mem_erase.mp hm.2
  refine mem_erase.mpr ⟨hm.1, mem_erase.mpr ⟨?_, hRfirst⟩⟩
  intro heq
  subst R
  exact hm'.1 (u.second_cross hm'.2)

theorem left_inter_second_subset_right (u : CommonThreatWitness F G T T') :
    u.leftRemainder ∩ u.second ⊆ u.rightRemainder :=
  u.swap.right_inter_first_subset_left

def sourceExposure {ell : ℕ} (W : Vortex V ell) (u : CommonThreatWitness F G T T')
    (H : TripleSystemOn V) (hH : H ⊆ u.remainder) (hterm : W.level u.bridge = Fin.last ell) (j' : ℕ) :
    SourceTwoFamilyWitness W F G (u.firstExposureRoot H) (insert T' (u.second ∩ H)) j'
      (vortexRootExponent j' (u.secondExposureRoot H).card) (u.remainder \ H).card where
  first := u.first
  second := u.second
  left := u.leftRemainder \ H
  right := u.rightRemainder \ H
  first_mem := u.first_mem
  second_mem := u.second_mem
  first_root := u.firstExposureRoot_subset H
  second_root := insert_subset u.second_root inter_subset_left
  left_subset := by
    intro R hR
    have hm := mem_sdiff.mp hR
    have hleft := mem_erase.mp hm.1
    have hleft' := mem_erase.mp hleft.2
    refine mem_sdiff.mpr ⟨hleft'.2, ?_⟩
    intro hroot
    rcases mem_insert.mp hroot with heq | hin
    · exact hleft'.1 heq
    · exact hm.2 (mem_inter.mp hin).2
  right_subset := by
    intro R hR
    have hm := mem_sdiff.mp hR
    have hright := mem_erase.mp hm.1
    have hright' := mem_erase.mp hright.2
    refine mem_sdiff.mpr ⟨hright'.2, ?_⟩
    intro hroot
    rcases mem_insert.mp hroot with heq | hin
    · exact hright'.1 heq
    · exact hm.2 (mem_inter.mp hin).2
  cross_first := by
    intro R hR
    have hm := mem_inter.mp hR
    have hr := mem_sdiff.mp hm.1
    exact mem_sdiff.mpr ⟨u.right_inter_first_subset_left (mem_inter.mpr ⟨hr.1, hm.2⟩), hr.2⟩
  cross_second := by
    intro R hR
    have hm := mem_inter.mp hR
    have hl := mem_sdiff.mp hm.1
    exact mem_sdiff.mpr ⟨u.left_inter_second_subset_right (mem_inter.mpr ⟨hl.1, hm.2⟩), hl.2⟩
  first_terminal := by
    intro R hR
    rw [u.first_exposure_omitted H, mem_singleton] at hR
    simpa only [hR] using hterm
  second_terminal := by
    intro R hR
    rw [u.second_exposure_omitted H hH, mem_singleton] at hR
    simpa only [hR] using hterm
  exposed_nonempty := ⟨u.bridge, mem_inter.mpr ⟨u.bridge_second, mem_union_left _ u.bridge_first⟩⟩
  exposed_exponent := by rw [← u.secondExposureRoot_eq_inter H]
  selected_card := by rw [← union_sdiff_distrib]; rfl

end

end Erdos207.CommonThreatWitness
