import StackExchange.Puzzling139335.N7.TypeReduction
import StackExchange.Puzzling139335.N5.Transport
import StackExchange.Puzzling139335.N7.FullPairNormalization.Oriented
import StackExchange.Puzzling139335.N7.FullPairNormalization.SingletonTransport
import StackExchange.Puzzling139335.N7.NormalizedPair.Defs

/-!
# An actual dissection underlying the normalized repeated pair

The pieces are transformed by one square symmetry and then relabeled.
All congruence maps in the resulting data are transported from the
original placements.
-/

open Set

namespace Puzzling139335.N7.PairConfiguration

noncomputable section

variable {d : SquareDissection}

private theorem exists_ordered_piece_reindex (C : PairConfiguration d)
    {n0 n1 : Fin 3}
    (hn : (n0 = 0 ∧ n1 = 1) ∨ (n0 = 1 ∧ n1 = 0)) :
    ∃ σ : Equiv.Perm (Fin 4),
      σ 0 = C.double n0 ∧ σ 1 = C.double n1 ∧
      σ 2 = C.double 2 ∧ σ 3 = C.singleton := by
  classical
  have h01 : n0 ≠ n1 := by
    rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have h02 : n0 ≠ 2 := by
    rcases hn with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  have h12 : n1 ≠ 2 := by
    rcases hn with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  have hs (n : Fin 3) : C.singleton ≠ C.double n :=
    (C.double_ne_singleton n).symm
  let q : Fin 4 → Fin 4 := ![C.double n0, C.double n1, C.double 2, C.singleton]
  have hq : Function.Injective q := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [q, C.double_ne_singleton, hs, C.double_injective.eq_iff,
        h01, h02, h12, h01.symm, h02.symm, h12.symm] at hij ⊢
  exact ⟨Equiv.ofBijective q hq.bijective_of_finite, rfl, rfl, rfl, rfl⟩

/-- A full repeated endpoint supplies a normalized pair on an actual
transformed and relabeled dissection.  No placement or corner-type
condition is added to the dissection assumptions. -/
theorem exists_normalizedPair_of_repeatedEnd_full (C : PairConfiguration d)
    (hc : d.HasProtectedCenter) (hfull : C.repeatedEnd ∈ N5.fullCornerTypes d) :
    ∃ D : SquareDissection, D.HasProtectedCenter ∧ Nonempty (NormalizedPair D) := by
  classical
  obtain ⟨n0, n1, f, hn, hfS, hfR, hfA, _, _, hAthird, hBthird, hconj⟩ :=
    C.exists_oriented_pair_normalization hc hfull
  obtain ⟨σ, hσ0, hσ1, hσ2, hσ3⟩ := C.exists_ordered_piece_reindex hn
  let D := (d.map f hfS).reindex σ
  let u := (d.placement (C.double n0)).trans f
  let third := (u.symm.trans (d.placement (C.double 2))).trans f
  let single := (u.symm.trans (d.placement C.singleton)).trans f
  have hD0 : D.piece 0 = f '' d.piece (C.double n0) := by
    change f '' d.piece (σ 0) = f '' d.piece (C.double n0)
    rw [hσ0]
  have hD1 : D.piece 1 = f '' d.piece (C.double n1) := by
    change f '' d.piece (σ 1) = f '' d.piece (C.double n1)
    rw [hσ1]
  have hD2 : D.piece 2 = f '' d.piece (C.double 2) := by
    change f '' d.piece (σ 2) = f '' d.piece (C.double 2)
    rw [hσ2]
  have hD3 : D.piece 3 = f '' d.piece C.singleton := by
    change f '' d.piece (σ 3) = f '' d.piece C.singleton
    rw [hσ3]
  have huimage : u '' d.piece 0 = D.piece 0 := by
    calc
      u '' d.piece 0 = f '' (d.placement (C.double n0) '' d.piece 0) := by
        simp only [u, AffineIsometryEquiv.coe_trans, image_image, Function.comp_def]
      _ = D.piece 0 := by rw [d.placement_image, hD0]
  have huR : u C.repeatedEnd = corner 0 := hfR
  have huA : u C.common = corner 1 := hfA
  have hRmem : C.repeatedEnd ∈ d.piece 0 := by
    apply d.usedCornerTypes_subset
    rw [C.types]
    simp
  have hAmem : C.common ∈ d.piece 0 := by
    apply d.usedCornerTypes_subset
    rw [C.types]
    simp
  have hBmem : C.otherEnd ∈ d.piece 0 := by
    apply d.usedCornerTypes_subset
    rw [C.types]
    simp
  have hplaced_image (i : Fin 4) :
      (u.symm.trans (d.placement i)).trans f '' D.piece 0 = f '' d.piece i := by
    calc
      (u.symm.trans (d.placement i)).trans f '' D.piece 0 =
          f '' (d.placement i '' d.piece 0) := by
        rw [← huimage]
        simp only [image_image, AffineIsometryEquiv.coe_trans, Function.comp_def,
          u.symm_apply_apply]
      _ = f '' d.piece i := by rw [d.placement_image]
  have hthird_apply (v : Plane) : third (u v) = f (d.placement (C.double 2) v) := by
    simp [third]
  have hsingle_apply (v : Plane) : single (u v) = f (d.placement C.singleton v) := by
    simp [single]
  have hreflection :
      (u.symm.trans (d.placement (C.double n1))).trans f =
        ReflectionSeparation.horizontal := by
    calc
      (u.symm.trans (d.placement (C.double n1))).trans f =
          (f.symm.trans (d.relativePlacement (C.double n0) (C.double n1))).trans f := by
        apply AffineIsometryEquiv.ext
        intro p
        simp [u, SquareDissection.relativePlacement]
      _ = ReflectionSeparation.horizontal := hconj
  refine ⟨D, ?_, ⟨{
    third := third
    single := single
    b := u C.otherEnd
    bottom_left := ?_
    bottom_right := ?_
    reflected := ?_
    third_image := ?_
    singleton_image := ?_
    b_mem := ?_
    b_ne_zero := ?_
    third_a := ?_
    third_b := ?_
    singleton_count := ?_
    singleton_type := ?_ }⟩⟩
  · exact ((d.map f hfS).reindex_hasProtectedCenter σ).mpr
      ((d.map_hasProtectedCenter f hfS).mpr hc)
  · rw [← huR, ← huimage]
    exact mem_image_of_mem u hRmem
  · rw [← huA, ← huimage]
    exact mem_image_of_mem u hAmem
  · rw [← hreflection, hplaced_image, hD1]
  · exact (hplaced_image (C.double 2)).trans hD2.symm
  · exact (hplaced_image C.singleton).trans hD3.symm
  · rw [← huimage]
    exact mem_image_of_mem u hBmem
  · intro hb
    exact C.repeatedEnd_ne_otherEnd (u.injective (huR.trans hb.symm))
  · rw [← huA, hthird_apply]
    exact hAthird
  · exact (hthird_apply C.otherEnd).trans hBthird
  · change (d.map f hfS).tileCornerCount (σ 3) = 1
    rw [hσ3, N5.tileCornerCount_map, C.singleton_count]
  · intro j hj
    have hj' : corner j ∈ f '' d.piece C.singleton := by rwa [hD3] at hj
    rcases C.singleton_mapped_corner_type hfull f hfS hj' with ha | hb
    · left
      rw [← huA]
      exact (hsingle_apply C.common).trans ha
    · right
      exact (hsingle_apply C.otherEnd).trans hb

end

end Puzzling139335.N7.PairConfiguration
