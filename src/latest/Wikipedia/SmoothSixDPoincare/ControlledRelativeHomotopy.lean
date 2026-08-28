import Wikipedia.SmoothSixDPoincare.RelativeCurveHomotopy

/-!
# Relative homotopies whose entire trace stays in a prescribed target set

Endpoint avoidance alone does not preserve a path class in a complement.
This predicate retains an actual relative homotopy together with target
containment at every time on the specified source region. Restricting it
therefore gives an actual homotopy in the target subtype.
-/

noncomputable section

open Set ContinuousMap

namespace Wikipedia.SmoothSixDPoincare

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def HomotopicRelWithin (f g : C(X, Y)) (C K : Set X) (O : Set Y) : Prop :=
  ∃ F : f.HomotopyRel g C, ∀ t : unitInterval, MapsTo (fun x => F (t, x)) K O

namespace HomotopicRelWithin

variable {f g h : C(X, Y)} {C K : Set X} {O : Set Y}

theorem refl (f : C(X, Y)) (C : Set X) (hmaps : MapsTo f K O) :
    HomotopicRelWithin f f C K O :=
  ⟨HomotopyRel.refl f C, fun _ => hmaps⟩

theorem homotopicRel (H : HomotopicRelWithin f g C K O) : f.HomotopicRel g C := by
  obtain ⟨F, _⟩ := H
  exact ⟨F⟩

theorem mapsTo_left (H : HomotopicRelWithin f g C K O) : MapsTo f K O := by
  obtain ⟨F, hF⟩ := H
  intro x hx
  exact (congrArg (fun y => y ∈ O) (F.map_zero_left x)).mp (hF 0 hx)

theorem mapsTo_right (H : HomotopicRelWithin f g C K O) : MapsTo g K O := by
  obtain ⟨F, hF⟩ := H
  intro x hx
  exact (congrArg (fun y => y ∈ O) (F.map_one_left x)).mp (hF 1 hx)

theorem trans (H : HomotopicRelWithin f g C K O)
    (G : HomotopicRelWithin g h C K O) : HomotopicRelWithin f h C K O := by
  obtain ⟨F, hF⟩ := H
  obtain ⟨G, hG⟩ := G
  refine ⟨HomotopyRel.trans F G, ?_⟩
  intro t x hx
  change (F.toHomotopy.trans G.toHomotopy) (t, x) ∈ O
  rw [Homotopy.trans_apply]
  split_ifs
  · exact hF _ hx
  · exact hG _ hx

theorem mono (H : HomotopicRelWithin f g C K O) {D L : Set X} {P : Set Y}
    (hDC : D ⊆ C) (hLK : L ⊆ K) (hOP : O ⊆ P) :
    HomotopicRelWithin f g D L P := by
  obtain ⟨F, hF⟩ := H
  exact ⟨{ toHomotopy := F.toHomotopy, prop' := fun t x hx => F.eq_fst t (hDC hx) },
    fun t x hx => hOP (hF t (hLK hx))⟩

/-- Control extends across points fixed throughout the homotopy. -/
theorem extend_source (H : HomotopicRelWithin f g C K O) {D : Set X}
    (hD : D ⊆ K ∪ C) (hf : MapsTo f D O) : HomotopicRelWithin f g C D O := by
  obtain ⟨F, hF⟩ := H
  refine ⟨F, ?_⟩
  intro t x hx
  rcases hD hx with hxK | hxC
  · exact hF t hxK
  · exact (congrArg (fun y => y ∈ O) (F.eq_fst t hxC)).mpr (hf hx)

def restrictMap (f : C(X, Y)) (hf : MapsTo f K O) : C(K, O) :=
  ⟨fun x => ⟨f x, hf x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem homotopicRel_restrict (H : HomotopicRelWithin f g C K O)
    (hf : MapsTo f K O) (hg : MapsTo g K O) :
    (restrictMap f hf).HomotopicRel (restrictMap g hg) {x : K | x.val ∈ C} := by
  obtain ⟨F, hF⟩ := H
  refine ⟨{
    toFun := fun p => ⟨F (p.1, p.2.val), hF p.1 p.2.property⟩
    continuous_toFun := (F.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    map_zero_left := fun x => Subtype.ext (F.map_zero_left x.val)
    map_one_left := fun x => Subtype.ext (F.map_one_left x.val)
    prop' := fun t x hx => Subtype.ext (F.eq_fst t hx) }⟩

end HomotopicRelWithin
end Wikipedia.SmoothSixDPoincare
