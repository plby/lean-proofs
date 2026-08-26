import ErdosProblems.Erdos336.CriticalRepresentationSelection
import ErdosProblems.Erdos336.QuotientImageCard
import ErdosProblems.Erdos336.PrimitiveEndpointQuotientSmall

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Homomorphic image under a subgroup quotient, with its classical equality
decision hidden from theorem statements. -/
noncomputable def subgroupQuotientImage (L : AddSubgroup G) (C : Finset G) :
    Finset (G ⧸ L) := by
  classical
  exact C.image (QuotientAddGroup.mk' L)

/-- Lev's representation-selection dichotomy for the `N≥3` critical case,
packaged so that every exceptional case is detected by a two-class quotient
with three double classes. -/
theorem critical_representation_dichotomy
    (C : Finset G) (N : ℕ) (hN : 3 ≤ N) (hzero : 0 ∈ C)
    (hCcard : C.card = N + 1) (hCCcard : (C + C).card = 2 * N + 1) :
    (∃ r : CriticalSelector C,
      ∀ x ∈ C, selectorLoad r x ≤ N) ∨
    ∃ (L : AddSubgroup G),
      (subgroupQuotientImage L C).card = 2 ∧
      (subgroupQuotientImage L (C + C)).card = 3 := by
  classical
  have hCsub : C ⊆ C + C := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
  have hDcard : (criticalNewSums C).card = N := by
    rw [criticalNewSums, Finset.card_sdiff_of_subset hCsub, hCCcard, hCcard]
    omega
  have hDthree : 3 ≤ (criticalNewSums C).card := by omega
  rcases balanced_selector_or_offcenter_closed hzero hDthree with hbal | hstar
  · left
    obtain ⟨r, hr⟩ := hbal
    exact ⟨r, fun x hx => by simpa [hDcard] using hr x hx⟩
  · right
    obtain ⟨r, g, hgC, hg0, hover, hclosed⟩ := hstar
    have hloop : g + g ∈ criticalNewSums C :=
      overloaded_selector_has_center_loop r g hover
    let X := C.erase g
    have hXcard : X.card = N := by
      dsimp [X]
      rw [Finset.card_erase_of_mem hgC, hCcard]
      omega
    have hzeroX : 0 ∈ X := Finset.mem_erase.mpr ⟨hg0.symm, hzero⟩
    have hXne : X.Nonempty := ⟨0, hzeroX⟩
    have hXXsubC : X + X ⊆ C := by
      intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
      have hx' := Finset.mem_erase.mp hx
      have hy' := Finset.mem_erase.mp hy
      exact hclosed x hx'.2 hx'.1 y hy'.2 hy'.1
    have hXXcardLe : (X + X).card ≤ N + 1 := by
      rw [← hCcard]
      exact Finset.card_le_card hXXsubC
    have hXXsmall : (X + X).card ≤ X.card + X.card - 1 := by
      rw [hXcard]
      omega
    let Lfin := (X + X).addStab
    let L : AddSubgroup G := AddAction.stabilizer G (X + X : Set G)
    have hXXne : (X + X).Nonempty := hXne.add hXne
    have hLmem (x : G) : x ∈ Lfin ↔ x ∈ L := by
      change x ∈ (X + X).addStab ↔ x ∈ L
      rw [← SetLike.mem_coe, Finset.coe_addStab hXXne]
      simp [L]
    have hzeroL : 0 ∈ Lfin := Finset.zero_mem_addStab.mpr hXXne
    have hKneser := add_kneser_eq_of_card_le hXne hXne hXXsmall
    change (X + Lfin).card + (X + Lfin).card =
      (X + X).card + Lfin.card at hKneser
    have hXsubXL : X ⊆ X + Lfin := by
      intro x hx
      exact Finset.mem_add.mpr ⟨x, hx, 0, hzeroL, by simp⟩
    have hXle : N ≤ (X + Lfin).card := by
      rw [← hXcard]
      exact Finset.card_le_card hXsubXL
    have hLtwo : 2 ≤ Lfin.card := by omega
    let q : G →+ (G ⧸ L) := QuotientAddGroup.mk' L
    have hsat := card_add_subgroup_eq_quotient_image_mul L Lfin hLmem X
    change (X + Lfin).card = (X.image q).card * Lfin.card at hsat
    have hqzero : 0 ∈ X.image q :=
      Finset.mem_image.mpr ⟨0, hzeroX, q.map_zero⟩
    have hqpos : 0 < (X.image q).card := by
      have hqne : (X.image q).Nonempty := ⟨0, hqzero⟩
      exact hqne.card_pos
    have hqcard : (X.image q).card = 1 := by
      by_contra hne
      have hqge : 2 ≤ (X.image q).card := by omega
      have hmul := Nat.mul_le_mul_right Lfin.card hqge
      have h2L : 2 * Lfin.card ≤ (X + Lfin).card := by
        rw [hsat]
        exact hmul
      omega
    have hXLcard : (X + Lfin).card = Lfin.card := by
      rw [hsat, hqcard]
      simp
    have hLsubXL : Lfin ⊆ X + Lfin := by
      intro k hk
      exact Finset.mem_add.mpr ⟨0, hzeroX, k, hk, by simp⟩
    have hXLeq : X + Lfin = Lfin :=
      Finset.eq_of_subset_of_card_le hLsubXL (by rw [hXLcard]) |>.symm
    have hXsubLfin : X ⊆ Lfin := by
      intro x hx
      have : x ∈ X + Lfin := Finset.mem_add.mpr ⟨x, hx, 0, hzeroL, by simp⟩
      rwa [hXLeq] at this
    have hXXsubLfin : X + X ⊆ Lfin := by
      intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
      exact (hLmem _).mpr (L.add_mem (hLmem _ |>.mp (hXsubLfin hx))
        (hLmem _ |>.mp (hXsubLfin hy)))
    have hXXcard : (X + X).card = Lfin.card := by omega
    have hXXeqLfin : X + X = Lfin :=
      Finset.eq_of_subset_of_card_le hXXsubLfin (by rw [hXXcard])
    have hLcard : Lfin.card = N := by
      have hNL : N ≤ Lfin.card := by
        rw [← hXcard]
        exact Finset.card_le_card hXsubLfin
      have hLN : Lfin.card ≤ N + 1 := by rw [← hXXcard]; exact hXXcardLe
      by_contra hne
      have hEq : Lfin.card = N + 1 := by omega
      have hproper : X ≠ Lfin := by
        intro heq
        have := congrArg Finset.card heq
        omega
      have hex : ∃ l ∈ Lfin, l ∉ X := by
        by_contra hnone
        push_neg at hnone
        exact hproper (Finset.Subset.antisymm hXsubLfin hnone)
      obtain ⟨l, hlL, hlX⟩ := hex
      have hlXX : l ∈ X + X := by rwa [hXXeqLfin]
      have hlC : l ∈ C := hXXsubC hlXX
      have hCX : C = insert g X := by
        dsimp [X]
        exact (Finset.insert_erase hgC).symm
      have hlg : l = g := by
        rw [hCX] at hlC
        exact (Finset.mem_insert.mp hlC).resolve_right hlX
      have hgL : g ∈ L := (hLmem g).mp (by simpa [← hlg] using hlL)
      have hggL : g + g ∈ L := L.add_mem hgL hgL
      have hggC : g + g ∈ C := by
        apply hXXsubC
        rw [hXXeqLfin]
        exact (hLmem _).mpr hggL
      exact (Finset.mem_sdiff.mp hloop).2 hggC
    have hXeqLfin : X = Lfin :=
      Finset.eq_of_subset_of_card_le hXsubLfin (by rw [hLcard, hXcard])
    have hgnotL : g ∉ L := by
      intro hgL
      have hgX : g ∈ X := by
        rw [hXeqLfin]
        exact (hLmem g).mpr hgL
      exact (Finset.mem_erase.mp hgX).1 rfl
    have hggnotL : g + g ∉ L := by
      intro hggL
      have hggC : g + g ∈ C := by
        apply hXXsubC
        rw [hXXeqLfin]
        exact (hLmem _).mpr hggL
      exact (Finset.mem_sdiff.mp hloop).2 hggC
    refine ⟨L, ?_, ?_⟩
    · change (C.image q).card = 2
      have hImageEq : C.image q = {0, q g} := by
        ext z
        constructor
        · intro hz
          obtain ⟨x, hxC, rfl⟩ := Finset.mem_image.mp hz
          by_cases hxg : x = g
          · simp [hxg]
          · have hxX : x ∈ X := Finset.mem_erase.mpr ⟨hxg, hxC⟩
            have hxL : x ∈ L := (hLmem x).mp (by rwa [← hXeqLfin])
            have hqx : q x = 0 := (QuotientAddGroup.eq_zero_iff x).mpr hxL
            simp [hqx]
        · intro hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact Finset.mem_image.mpr ⟨0, hzero, q.map_zero⟩
          · exact Finset.mem_image.mpr ⟨g, hgC, rfl⟩
      rw [hImageEq]
      apply Finset.card_pair
      intro h
      apply hgnotL
      exact (QuotientAddGroup.eq_zero_iff g).mp h.symm
    · change ((C + C).image q).card = 3
      have hDoubleImageEq : (C + C).image q = {0, q g, q g + q g} := by
        ext z
        constructor
        · intro hz
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
          obtain ⟨x, hxC, y, hyC, rfl⟩ := Finset.mem_add.mp hw
          have hx : q x = 0 ∨ q x = q g := by
            by_cases hxg : x = g
            · exact Or.inr (by rw [hxg])
            · left
              apply (QuotientAddGroup.eq_zero_iff x).mpr
              apply (hLmem x).mp
              rw [← hXeqLfin]
              exact Finset.mem_erase.mpr ⟨hxg, hxC⟩
          have hy : q y = 0 ∨ q y = q g := by
            by_cases hyg : y = g
            · exact Or.inr (by rw [hyg])
            · left
              apply (QuotientAddGroup.eq_zero_iff y).mpr
              apply (hLmem y).mp
              rw [← hXeqLfin]
              exact Finset.mem_erase.mpr ⟨hyg, hyC⟩
          rw [q.map_add]
          rcases hx with hx | hx <;> rcases hy with hy | hy <;>
            simp [hx, hy, add_comm]
        · intro hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl
          · exact Finset.mem_image.mpr
              ⟨0 + 0, Finset.mem_add.mpr ⟨0, hzero, 0, hzero, rfl⟩, by simp⟩
          · exact Finset.mem_image.mpr
              ⟨g + 0, Finset.mem_add.mpr ⟨g, hgC, 0, hzero, rfl⟩, by simp⟩
          · exact Finset.mem_image.mpr
              ⟨g + g, Finset.mem_add.mpr ⟨g, hgC, g, hgC, rfl⟩, q.map_add g g⟩
      rw [hDoubleImageEq]
      apply Finset.card_eq_three.mpr
      refine ⟨0, q g, q g + q g, ?_, ?_, ?_, rfl⟩
      · intro h
        exact hgnotL ((QuotientAddGroup.eq_zero_iff g).mp h.symm)
      · intro h
        have hqzero : q (g + g) = 0 := by
          rw [q.map_add]
          exact h.symm
        change (QuotientAddGroup.mk' L) (g + g) = 0 at hqzero
        exact hggnotL ((QuotientAddGroup.eq_zero_iff (g + g)).mp hqzero)
      · intro h
        have hc : q g + 0 = q g + q g := by simpa using h
        have hzeroq : (0 : G ⧸ L) = q g := add_left_cancel hc
        exact hgnotL ((QuotientAddGroup.eq_zero_iff g).mp hzeroq.symm)

end Erdos336
