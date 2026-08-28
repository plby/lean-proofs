import Wikipedia.NoExoticSixSphere.JamesSphereHomotopyCorrection

/-!
# Relative compression after point avoidance

The corrected cylinder ends in the punctured cone model. Applying the
second puncture deformation brings that endpoint into the original
James stage. The bottom remains in the cone throughout, and ends in
the original one-letter subspace. Tracks already in the James stage
stay there, and constant tracks in the common subspace stay fixed.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace NoExoticSixSphere.JamesSphere.SecondStageCone

theorem secondDeformation_fixed (n : ℕ) (q : ConeCoordinates n) (hq : ‖q‖ < 1)
    (t : I) (x : secondPunctured n q hq) (hx : x.val ∈ Set.range (base n)) :
    (secondPunctureDeformation n q hq (t, x)).val = x.val :=
  congrArg (fun y : secondPunctured n q hq ↦ y.val)
    (PuncturedCellAttachment.deformation_fixed_of_mem_base (isPushout n) q hq t x hx)

theorem exists_compression_of_avoidance (n : ℕ) (hn : 0 < n)
    (p : PuncturedStage.Coordinates n 1) (hp : ‖p‖ < 1)
    (q : ConeCoordinates n) (hq : ‖q‖ < 1)
    {X : Type} [TopologicalSpace X] [NormalSpace (I × X)]
    (f g : C(X, Space n)) (H : f.Homotopy g)
    (K : Set X) (hK : IsClosed K) (hfK : ∀ x ∈ K, f x ∈ Set.range (cone n))
    (hHK : ∀ t x, x ∈ K →
      H (t, x) ≠ firstCell n (PuncturedCellAttachment.point p hp))
    (hg : ∀ x, g x ≠ cone n (PuncturedCellAttachment.point q hq)) :
    ∃ a : C(X, SecondStage.Space n), ∃ F : f.Homotopy ((base n).comp a),
      (∀ x ∈ K, a x ∈ StageAttachment.lower n 1) ∧
      (∀ t x, x ∈ K → F (t, x) ∈ Set.range (cone n)) ∧
      (∀ x, (∀ t, H (t, x) ∈ Set.range (base n)) →
        ∀ t, F (t, x) ∈ Set.range (base n)) ∧
      ∀ x, f x ∈ Set.range (base n) → f x ∈ Set.range (cone n) →
        (∀ t, H (t, x) = f x) → ∀ t, F (t, x) = f x := by
  obtain ⟨b, R, hbK, hRK, hRA, hRfix⟩ :=
    exists_corrected_homotopy n hn p hp q hq f g H K hK hfK hHK hg
  let a : C(X, SecondStage.Space n) := (secondPunctureRetraction n q hq).comp b
  let C : ((⟨Subtype.val, continuous_subtype_val⟩ :
      C(secondPunctured n q hq, Space n)).comp b).Homotopy ((base n).comp a) := {
    toFun z := (secondPunctureDeformation n q hq (z.1, b z.2)).val
    continuous_toFun := continuous_subtype_val.comp
      ((secondPunctureDeformation n q hq).continuous.comp
        (continuous_fst.prodMk (b.continuous.comp continuous_snd)))
    map_zero_left x := congrArg (fun y : secondPunctured n q hq ↦ y.val)
      ((secondPunctureDeformation n q hq).map_zero_left (b x))
    map_one_left x := congrArg (fun y : secondPunctured n q hq ↦ y.val)
      ((secondPunctureDeformation n q hq).map_one_left (b x)) }
  refine ⟨a, R.trans C, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact secondRetraction_mem_lower n q hq (b x) (hbK x hx)
  · intro t x hx
    apply trans_pointwise_property R C x (fun y ↦ y ∈ Set.range (cone n)) ?_ ?_ t
    · exact fun s ↦ hRK s x hx
    · exact fun s ↦ secondDeformation_mem_cone n q hq s (b x) (hbK x hx)
  · intro x hx t
    have hb : (b x).val ∈ Set.range (base n) := by
      have he := hRA x hx 1
      rwa [R.apply_one] at he
    apply trans_pointwise_property R C x (fun y ↦ y ∈ Set.range (base n)) ?_ ?_ t
    · exact hRA x hx
    · intro s
      change (secondPunctureDeformation n q hq (s, b x)).val ∈ Set.range (base n)
      rw [secondDeformation_fixed n q hq s (b x) hb]
      exact hb
  · intro x hxA hxC hx t
    have hb : (b x).val = f x := by
      have he := hRfix x hxC hx 1
      rwa [R.apply_one] at he
    have hbA : (b x).val ∈ Set.range (base n) := hb ▸ hxA
    apply trans_pointwise_property R C x (fun y ↦ y = f x) ?_ ?_ t
    · exact hRfix x hxC hx
    · intro s
      exact (secondDeformation_fixed n q hq s (b x) hbA).trans hb

end NoExoticSixSphere.JamesSphere.SecondStageCone
