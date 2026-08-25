import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma TwoPointFiberSurjectiveCard {α β : Type*} [Fintype α] [Fintype β]
    (a b : α) (hab : a ≠ b) (f : α → β)
    (hsurj : Function.Surjective f)
    (hfiber : ∀ x y : α,
      f x = f y ↔
        x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)) :
    Fintype.card β + 1 = Fintype.card α := by
  classical
  let y0 : β := f a
  let pick : β → α := fun y => Classical.choose (hsurj y)
  have hpick : ∀ y : β, f (pick y) = y := fun y => Classical.choose_spec (hsurj y)
  have hpick_inj : Function.Injective pick := by
    intro y z hyz
    calc
      y = f (pick y) := (hpick y).symm
      _ = f (pick z) := by rw [hyz]
      _ = z := hpick z
  have hpre_y0 : pick y0 = a ∨ pick y0 = b := by
    have hfy : f (pick y0) = f a := by
      simpa [y0] using hpick y0
    rcases (hfiber (pick y0) a).1 hfy with h | h | h
    · exact Or.inl h
    · rcases h with ⟨_hp, ha_b⟩
      exact False.elim (hab ha_b)
    · exact Or.inr h.1
  let missing : α := if pick y0 = a then b else a
  have hmissing_ne_pick_y0 : missing ≠ pick y0 := by
    dsimp [missing]
    by_cases hpa : pick y0 = a
    · intro h
      simp [hpa] at h
      exact hab h.symm
    · have hpb : pick y0 = b := by
        rcases hpre_y0 with h | h
        · exact False.elim (hpa h)
        · exact h
      intro h
      simp [hpa] at h
      exact hab (h.trans hpb)
  have hmissing_maps_y0 : f missing = y0 := by
    dsimp [missing]
    by_cases hpa : pick y0 = a
    · simp [hpa, y0, (hfiber b a).2 (Or.inr (Or.inr ⟨rfl, rfl⟩))]
    · simp [hpa, y0]
  have hmissing_not_range : ∀ y : β, pick y ≠ missing := by
    intro y hy
    by_cases hy0 : y = y0
    · subst hy0
      exact hmissing_ne_pick_y0 hy.symm
    · have hy_eq : y = y0 := by
        calc
          y = f (pick y) := (hpick y).symm
          _ = f missing := by rw [hy]
          _ = y0 := hmissing_maps_y0
      exact hy0 hy_eq
  have hrange_eq : Finset.univ.image pick = (Finset.univ : Finset α).erase missing := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨y, _hy, rfl⟩
      simp [hmissing_not_range y]
    · intro hx
      have hxne : x ≠ missing := by
        exact (Finset.mem_erase.mp hx).1
      let y : β := f x
      refine Finset.mem_image.mpr ⟨y, Finset.mem_univ y, ?_⟩
      by_contra hpx
      have hf_eq : f (pick y) = f x := by
        simpa [y] using hpick y
      rcases (hfiber (pick y) x).1 hf_eq with hEq | hCross | hCross
      · exact hpx hEq
      · rcases hCross with ⟨hp_a, hx_b⟩
        have hy_y0 : y = y0 := by
          calc
            y = f x := rfl
            _ = f b := by rw [hx_b]
            _ = f a := (hfiber b a).2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
            _ = y0 := rfl
        have hp_y0_a : pick y0 = a := by
          simpa [hy_y0] using hp_a
        have hmiss : missing = b := by
          dsimp [missing]
          simp [hp_y0_a]
        exact hxne (by simpa [hmiss] using hx_b)
      · rcases hCross with ⟨hp_b, hx_a⟩
        have hy_y0 : y = y0 := by
          calc
            y = f x := rfl
            _ = f a := by rw [hx_a]
            _ = y0 := rfl
        have hp_y0_b : pick y0 = b := by
          simpa [hy_y0] using hp_b
        have hpa_not : pick y0 ≠ a := by
          intro hpa
          exact hab (hpa.symm.trans hp_y0_b)
        have hmiss : missing = a := by
          dsimp [missing]
          simp [hpa_not]
        exact hxne (by simpa [hmiss] using hx_a)
  have hcard_image : (Finset.univ.image pick).card = Fintype.card β := by
    simpa using (Finset.card_image_of_injective (Finset.univ : Finset β) hpick_inj)
  have hmissing_mem : missing ∈ (Finset.univ : Finset α) := Finset.mem_univ missing
  calc
    Fintype.card β + 1 = (Finset.univ.image pick).card + 1 := by rw [hcard_image]
    _ = ((Finset.univ : Finset α).erase missing).card + 1 := by rw [hrange_eq]
    _ = (Finset.univ : Finset α).card := Finset.card_erase_add_one hmissing_mem
    _ = Fintype.card α := by simp

