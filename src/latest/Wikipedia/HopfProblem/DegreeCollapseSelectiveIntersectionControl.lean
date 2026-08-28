import Wikipedia.HopfProblem.DegreeCollapseSelectiveSheetMotion

/-!
# Exact self-intersection control for a source-selective move

The two source sides are treated separately. Same-side coincidences are
unchanged by injectivity of the ambient motion. The moved/unmoved image
intersection and fixation of the retained crossings determine every cross-
side pair. In particular this records removal, rather than just a new
intersection count whose source pairs might have changed.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.DegreeCollapse.SelectiveSheet

variable {X Y : Type*} {f : X → Y} {A : ℝ × Y → Y} {U : Set X} {C : Set Y} {t : ℝ}

theorem cross_pair_iff
    (hinj : Injective (fun y => A (t, y)))
    (himage : ((fun y => A (t, y)) '' (f '' U)) ∩ (f '' Uᶜ) =
      ((f '' U) ∩ (f '' Uᶜ)) \ C)
    (hfix : ∀ y ∈ ((f '' U) ∩ (f '' Uᶜ)) \ C, A (t, y) = y)
    {x y : X} (hx : x ∈ U) (hy : y ∉ U) :
    A (t, f x) = f y ↔ f x = f y ∧ f x ∉ C := by
  constructor
  · intro heq
    have hnew : f y ∈ ((fun z => A (t, z)) '' (f '' U)) ∩ (f '' Uᶜ) :=
      ⟨⟨f x, ⟨x, hx, rfl⟩, heq⟩, ⟨y, hy, rfl⟩⟩
    rw [himage] at hnew
    have hxy : f x = f y := hinj (heq.trans (hfix (f y) hnew).symm)
    refine ⟨hxy, ?_⟩
    rw [hxy]
    exact hnew.2
  · rintro ⟨hxy, hnot⟩
    have hmem : f x ∈ ((f '' U) ∩ (f '' Uᶜ)) \ C :=
      ⟨⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy.symm⟩⟩, hnot⟩
    exact (hfix (f x) hmem).trans hxy

theorem family_pair_iff
    (hinj : Injective (fun y => A (t, y)))
    (himage : ((fun y => A (t, y)) '' (f '' U)) ∩ (f '' Uᶜ) =
      ((f '' U) ∩ (f '' Uᶜ)) \ C)
    (hfix : ∀ y ∈ ((f '' U) ∩ (f '' Uᶜ)) \ C, A (t, y) = y)
    (x y : X) : family f A U (t, x) = family f A U (t, y) ↔
      f x = f y ∧ (f x ∈ C → (x ∈ U ↔ y ∈ U)) := by
  by_cases hx : x ∈ U
  · by_cases hy : y ∈ U
    · rw [family_on f A U t hx, family_on f A U t hy]
      exact ⟨fun h => ⟨hinj h, fun _ => iff_of_true hx hy⟩,
        fun h => congrArg (fun z => A (t, z)) h.1⟩
    · rw [family_on f A U t hx, family_off f A U t hy,
        cross_pair_iff hinj himage hfix hx hy]
      exact ⟨fun h => ⟨h.1, fun hc => (h.2 hc).elim⟩,
        fun h => ⟨h.1, fun hc => hy ((h.2 hc).mp hx)⟩⟩
  · by_cases hy : y ∈ U
    · rw [family_off f A U t hx, family_on f A U t hy]
      constructor
      · intro h
        obtain ⟨hyx, hnot⟩ := (cross_pair_iff hinj himage hfix hy hx).mp h.symm
        refine ⟨hyx.symm, ?_⟩
        intro hc
        exact (hnot (hyx.symm ▸ hc)).elim
      · rintro ⟨hxy, hsame⟩
        have hnot : f y ∉ C := fun hc => hx ((hsame (hxy.symm ▸ hc)).mpr hy)
        exact ((cross_pair_iff hinj himage hfix hy hx).mpr ⟨hxy.symm, hnot⟩).symm
    · rw [family_off f A U t hx, family_off f A U t hy]
      exact ⟨fun h => ⟨h, fun _ => iff_of_false hx hy⟩, fun h => h.1⟩

theorem family_ordered_pairs_eq
    (hinj : Injective (fun y => A (t, y)))
    (himage : ((fun y => A (t, y)) '' (f '' U)) ∩ (f '' Uᶜ) =
      ((f '' U) ∩ (f '' Uᶜ)) \ C)
    (hfix : ∀ y ∈ ((f '' U) ∩ (f '' Uᶜ)) \ C, A (t, y) = y) :
    {p : X × X | p.1 ≠ p.2 ∧ family f A U (t, p.1) = family f A U (t, p.2)} =
      {p : X × X | p.1 ≠ p.2 ∧ f p.1 = f p.2} \
        {p : X × X | f p.1 ∈ C ∧ ¬ (p.1 ∈ U ↔ p.2 ∈ U)} := by
  ext p
  simp only [mem_ofPred_eq, mem_sdiff, family_pair_iff hinj himage hfix]
  constructor
  · rintro ⟨hne, heq, hs⟩
    exact ⟨⟨hne, heq⟩, fun h => h.2 (hs h.1)⟩
  · rintro ⟨⟨hne, heq⟩, hs⟩
    exact ⟨hne, heq, fun hc => not_not.mp (fun hh => hs ⟨hc, hh⟩)⟩

end Wikipedia.HopfProblem.DegreeCollapse.SelectiveSheet
