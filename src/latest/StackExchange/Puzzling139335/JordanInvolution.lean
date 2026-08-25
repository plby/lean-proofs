import StackExchange.Puzzling139335.JordanFixedPoint
import StackExchange.Puzzling139335.JordanSubarc
import StackExchange.Puzzling139335.JordanTransport

/-!
# Centers of symmetric Jordan regions

A self-homeomorphism of a Jordan curve which is an involution cannot have
exactly one fixed point.  Together with Brouwer for the filled region, this
puts the center of a centrally symmetric Jordan region in its interior.
-/

open Set

namespace Schoenflies

theorem IsJordanCurve.not_subsingleton {C : Set Plane} (hC : IsJordanCurve C) :
    ¬ C.Subsingleton := by
  obtain ⟨f, hf, rfl⟩ := hC
  intro hsub
  have hhalf : (1 / 2 : ℝ) ∈ unitInterval := ⟨by norm_num, by norm_num⟩
  have heq := hsub (mem_image_of_mem f zero_mem_I) (mem_image_of_mem f hhalf)
  have hparam := hf.injOn (show (0 : ℝ) ∈ Ico 0 1 by norm_num)
    (show (1 / 2 : ℝ) ∈ Ico 0 1 by norm_num) heq
  norm_num at hparam

/-- An involution of a Jordan curve cannot have a unique fixed point. -/
theorem IsJordanCurve.not_mem_of_involution_unique_fixed {C : Set Plane} {c : Plane}
    (hC : IsJordanCurve C) (e : Plane ≃ₜ Plane) (he : e '' C = C)
    (hinv : Function.Involutive e) (hcfix : e c = c)
    (hunique : ∀ x, e x = x → x = c) : c ∉ C := by
  intro hc
  obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp hC.not_subsingleton
  have hex : ∃ q ∈ C, q ≠ c := by
    by_cases hac : a = c
    · exact ⟨b, hb, fun hbc => hab (hac.trans hbc.symm)⟩
    · exact ⟨a, ha, hac⟩
  obtain ⟨q, hq, hqc⟩ := hex
  have hmap : MapsTo e C C := by
    intro x hx
    rw [← he]
    exact mem_image_of_mem e hx
  have hqeq : q ≠ e q := by
    intro h
    exact hqc (hunique q h.symm)
  have heqc : e q ≠ c := by
    intro h
    exact hqc (e.injective (h.trans hcfix.symm))
  obtain ⟨A, B, hcut⟩ := exists_isCutPair hC hq (hmap hq) hqeq
  have hAc : c ∉ ({q, e q} : Set Plane) := by
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hqc.symm, heqc.symm⟩
  have harc_image (D : Set Plane) (hD : IsArcBetween D q (e q)) :
      IsArcBetween (e '' D) q (e q) := by
    simpa only [hinv q] using (hD.image_homeomorph e).reverse
  have hsub_image {D : Set Plane} (hD : D ⊆ C) : e '' D ⊆ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmap (hD hx)
  have hAe : e '' A = A := by
    rcases hcut.arc_eq_fst_or_snd (harc_image A hcut.fst)
        (hsub_image hcut.fst_subset) with hAA | hAB
    · exact hAA
    · have hcAB : c ∈ A ∩ B := by
        have hcUnion : c ∈ A ∪ B := hcut.union_eq ▸ hc
        rcases hcUnion with hcA | hcB
        · exact ⟨hcA, hAB ▸ (hcfix ▸ mem_image_of_mem e hcA)⟩
        · have hcIm : c ∈ e '' A := hAB ▸ hcB
          obtain ⟨x, hxA, hxc⟩ := hcIm
          have hxc' : x = c := e.injective (hxc.trans hcfix.symm)
          exact ⟨hxc' ▸ hxA, hcB⟩
      exact False.elim (hAc (hcut.inter_eq ▸ hcAB))
  have hBe : e '' B = B := by
    rcases hcut.arc_eq_fst_or_snd (harc_image B hcut.snd)
        (hsub_image hcut.snd_subset) with hBA | hBB
    · have hBA' : B = A := e.injective.image_injective (hBA.trans hAe.symm)
      exact False.elim (hcut.ne hBA'.symm)
    · exact hBB
  have hmapA : MapsTo e A A := by
    intro x hx
    rw [← hAe]
    exact mem_image_of_mem e hx
  have hmapB : MapsTo e B B := by
    intro x hx
    rw [← hBe]
    exact mem_image_of_mem e hx
  obtain ⟨x, hx, hxfix⟩ :=
    hcut.fst.exists_fixedPoint_of_continuousOn e.continuous.continuousOn hmapA
  obtain ⟨y, hy, hyfix⟩ :=
    hcut.snd.exists_fixedPoint_of_continuousOn e.continuous.continuousOn hmapB
  have hcAB : c ∈ A ∩ B := ⟨hunique x hxfix ▸ hx, hunique y hyfix ▸ hy⟩
  exact hAc (hcut.inter_eq ▸ hcAB)

end Schoenflies

namespace Puzzling139335.IsJordanRegion

/-- A centrally symmetric closed Jordan region contains its center as an
interior point, even when its boundary has infinite length or positive area. -/
theorem center_mem_interior_of_pointReflection {P : Set Plane} {c : Plane}
    (hP : IsJordanRegion P) (hsym : AffineIsometryEquiv.pointReflection ℝ c '' P = P) :
    c ∈ interior P := by
  let e := (AffineIsometryEquiv.pointReflection ℝ c).toHomeomorph
  have hfix (x : Plane) : e x = x ↔ x = c :=
    AffineIsometryEquiv.pointReflection_fixed_iff
  have he : e '' P = P := hsym
  have hmap : MapsTo e P P := by
    intro x hx
    rw [← he]
    exact mem_image_of_mem e hx
  obtain ⟨x, hx, hxe⟩ := hP.exists_fixedPoint e.continuous hmap
  have hcP : c ∈ P := (hfix x).mp hxe ▸ hx
  have hfront : e '' frontier P = frontier P := by
    rw [e.image_frontier, he]
  have hcnot : c ∉ frontier P :=
    hP.frontier_isJordanCurve.not_mem_of_involution_unique_fixed e hfront
      (AffineIsometryEquiv.pointReflection_involutive (𝕜 := ℝ) c)
      (AffineIsometryEquiv.pointReflection_self (𝕜 := ℝ) c) (fun x hx => (hfix x).mp hx)
  by_contra hnot
  apply hcnot
  exact (mem_frontier_iff_notMem_interior hcP).mpr hnot

end Puzzling139335.IsJordanRegion
