/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.CyclicInverse
import ErdosProblems.Erdos360.LowLayerInverse

/-!
# The one-layer branch of the local cyclic inverse theorem

If the Fourier partial lift has only one occupied first coordinate, its
dense core lies in one coset of the embedded remainder subgroup.  Ruzsa's
two-translate completion therefore puts the full dyadic sumset in at most
two quotient cosets.  At dyadic level at least two, CFP's four-fold quotient
growth lemma turns this into the proper-subgroup alternative.
-/

namespace Erdos360

open scoped Pointwise

attribute [local instance] Classical.propDecidable

/-- A one-layer Fourier core forces the proper-subgroup branch of the local
dyadic inverse theorem.  The index is at least `m ≥ 240`, so the quotient
has far more than the three points excluded by four-fold growth. -/
theorem proper_subgroup_of_one_layer_affine_core
    {m g j : ℕ} [NeZero g] [NeZero (m * g)]
    {P B C D : Finset (ZMod (m * g))}
    (hzeroP : 0 ∈ P) (hj : 2 ≤ j)
    (hBdyadic : B = dyadicFinsetSum P j)
    (w : (ZMod (m * g))ˣ) (c : ZMod (m * g))
    (hC : C.Nonempty) (hCB : C ⊆ B)
    (hdense : 33 * B.card ≤ 40 * C.card)
    (hBsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hDaff : D = zmodAffineImage c (w : ZMod (m * g)) C)
    (hm240 : 240 ≤ m) (hDzero : 0 ∈ D)
    (hone :
      (firstCoordinateSet (zmodQuotRemImage m g D)).card ≤ 1) :
    ∃ K : AddSubgroup (ZMod (m * g)), K ≠ ⊤ ∧
      (P : Set (ZMod (m * g))) ⊆ (K : Set (ZMod (m * g))) := by
  classical
  have hm : 0 < m := by omega
  let H₀ : AddSubgroup (ZMod (m * g)) :=
    (⊤ : AddSubgroup (ZMod g)).map (zmodQuotientEmbedding m g)
  have hAzero : 0 ∈ firstCoordinateSet (zmodQuotRemImage m g D) := by
    apply mem_firstCoordinateSet.mpr
    exact ⟨0, Finset.mem_image.mpr
      ⟨0, hDzero, by simp [zmodQuotRemLift]⟩⟩
  have hremzero : ∀ z ∈ D, z.val % m = 0 := by
    intro z hz
    have hrem : z.val % m ∈
        firstCoordinateSet (zmodQuotRemImage m g D) := by
      apply mem_firstCoordinateSet.mpr
      exact ⟨(z.val / m : ZMod g),
        Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    exact Finset.card_le_one_iff.mp hone hrem hAzero
  have hDH₀ : (D : Set (ZMod (m * g))) ⊆ (H₀ : Set (ZMod (m * g))) := by
    intro z hz
    apply AddSubgroup.mem_map.mpr
    refine ⟨(z.val / m : ZMod g), by simp, ?_⟩
    have hrec := zmodQuotientEmbedding_quotient_add_remainder
      (m := m) (d := g) z
    rw [hremzero z hz] at hrec
    simpa using hrec
  let e := unitMulAddEquiv w
  let H : AddSubgroup (ZMod (m * g)) := H₀.comap e.toAddMonoidHom
  let a : ZMod (m * g) := e.symm (-c)
  have hCa : (C : Set (ZMod (m * g))) ⊆ a +ᵥ (H : Set (ZMod (m * g))) := by
    intro x hx
    rw [Set.mem_vadd_set]
    refine ⟨x - a, ?_, by simp only [vadd_eq_add]; abel⟩
    change e (x - a) ∈ H₀
    rw [map_sub, e.apply_symm_apply]
    change (w : ZMod (m * g)) * x - -c ∈ H₀
    have hxD : c + (w : ZMod (m * g)) * x ∈ D := by
      rw [hDaff]
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    simpa [sub_neg_eq_add, add_comm] using hDH₀ hxD
  have hCC : C - C ⊆ subgroupFinset H := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.mp hz
    have hxa := hCa (by simpa using hx)
    have hya := hCa (by simpa using hy)
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxa hya
    rw [mem_subgroupFinset]
    have := H.sub_mem hxa hya
    convert this using 1 <;> simp only [vadd_eq_add] <;> abel
  obtain ⟨F, _hFB, hFcard, hBF⟩ :=
    exists_two_translate_difference_cover hC hCB hdense hBsmall
  let q : ZMod (m * g) →+ (ZMod (m * g) ⧸ H) :=
    QuotientAddGroup.mk' H
  have himage : B.image q ⊆ F.image q := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨f, hf, z, hz, hfb⟩ := Finset.mem_add.mp (hBF hb)
    have hzH : z ∈ H := mem_subgroupFinset.mp (hCC hz)
    apply Finset.mem_image.mpr
    refine ⟨f, hf, ?_⟩
    have hz0 : q z = 0 := by
      apply (QuotientAddGroup.eq_iff_sub_mem).2
      simpa [q] using hzH
    calc
      q f = q f + q z := by rw [hz0, add_zero]
      _ = q (f + z) := (map_add q f z).symm
      _ = q b := by rw [hfb]
  have himageCard : (B.image (QuotientAddGroup.mk' H)).card ≤ 3 := by
    change (B.image q).card ≤ 3
    calc
      (B.image q).card ≤ (F.image q).card := Finset.card_le_card himage
      _ ≤ F.card := Finset.card_image_le
      _ ≤ 2 := hFcard
      _ ≤ 3 := by omega
  have hcardH₀ : Nat.card H₀ = g := by
    rw [show Nat.card H₀ = Nat.card (⊤ : AddSubgroup (ZMod g)) by
      exact natCard_map_zmodQuotientEmbedding hm ⊤]
    simp
  have hcardH : Nat.card H = g := by
    rw [show Nat.card H = Nat.card H₀ by
      exact natCard_comap_addEquiv e H₀]
    exact hcardH₀
  have hg : 0 < g := NeZero.pos g
  have hindex : 3 * Nat.card H < Nat.card (ZMod (m * g)) := by
    rw [hcardH]
    simp only [Nat.card_eq_fintype_card, ZMod.card]
    nlinarith
  apply exists_proper_subgroup_of_dyadic_quotient_card_le_three
    hzeroP hj H
  · exact hindex
  · simpa [hBdyadic] using himageCard

end Erdos360

#print axioms Erdos360.proper_subgroup_of_one_layer_affine_core
