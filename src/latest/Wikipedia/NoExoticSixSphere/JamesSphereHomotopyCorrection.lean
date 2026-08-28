import Wikipedia.NoExoticSixSphere.JamesSphereSupportedConeCorrection

/-!
# Correcting the whole homotopy while retaining its original initial map

Apply the supported correction to the graph homotopy as a map on its
whole cylinder. Its initial-time track is itself relative to the cone
on the prescribed bottom subset. Concatenating that track with the
corrected graph keeps the original initial map exactly, puts the moving
bottom in the cone, and retains endpoint avoidance of the second point.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace NoExoticSixSphere.JamesSphere.SecondStageCone

theorem trans_pointwise_property {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g h : C(X, Y)} (A : f.Homotopy g) (B : g.Homotopy h) (x : X) (P : Y → Prop)
    (hA : ∀ t, P (A (t, x))) (hB : ∀ t, P (B (t, x))) (t : I) :
    P (A.trans B (t, x)) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hA _
  · exact hB _

theorem exists_corrected_homotopy (n : ℕ) (hn : 0 < n)
    (p : PuncturedStage.Coordinates n 1) (hp : ‖p‖ < 1)
    (q : ConeCoordinates n) (hq : ‖q‖ < 1)
    {X : Type} [TopologicalSpace X] [NormalSpace (I × X)]
    (f g : C(X, Space n)) (H : f.Homotopy g)
    (K : Set X) (hK : IsClosed K) (hfK : ∀ x ∈ K, f x ∈ Set.range (cone n))
    (hHK : ∀ t x, x ∈ K →
      H (t, x) ≠ firstCell n (PuncturedCellAttachment.point p hp))
    (hg : ∀ x, g x ≠ cone n (PuncturedCellAttachment.point q hq)) :
    ∃ b : C(X, secondPunctured n q hq),
      ∃ R : f.Homotopy ((⟨Subtype.val, continuous_subtype_val⟩ :
        C(secondPunctured n q hq, Space n)).comp b),
        (∀ x ∈ K, (b x).val ∈ Set.range (cone n)) ∧
        (∀ t x, x ∈ K → R (t, x) ∈ Set.range (cone n)) ∧
        (∀ x, (∀ t, H (t, x) ∈ Set.range (base n)) →
          ∀ t, R (t, x) ∈ Set.range (base n)) ∧
        ∀ x, f x ∈ Set.range (cone n) → (∀ t, H (t, x) = f x) →
          ∀ t, R (t, x) = f x := by
  have hK' : IsClosed (Prod.snd ⁻¹' K : Set (I × X)) := hK.preimage continuous_snd
  have hav : (Prod.snd ⁻¹' K : Set (I × X)) ⊆
      SupportedCorrection.Domain n p hp H.toContinuousMap := by
    rintro ⟨t, x⟩ hx
    exact hHK t x hx
  obtain ⟨F, L, hLC, hLA, hLavoid, hFK⟩ :=
    SupportedCorrection.exists_correction n hn p hp H.toContinuousMap q hq
      (Prod.snd ⁻¹' K) hK' hav
  let a : C(X, Space n) := ⟨fun x ↦ F (0, x),
    F.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let b₀ : C(X, Space n) := ⟨fun x ↦ F (1, x),
    F.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hb : ∀ x, b₀ x ≠ cone n (PuncturedCellAttachment.point q hq) := by
    intro x
    have hx : H (1, x) ≠ cone n (PuncturedCellAttachment.point q hq) := by
      rw [H.apply_one]
      exact hg x
    have he := hLavoid 1 (1, x) hx
    rwa [L.apply_one] at he
  let b : C(X, secondPunctured n q hq) := ⟨fun x ↦ ⟨b₀ x, hb x⟩, b₀.continuous.subtype_mk _⟩
  let A : f.Homotopy a := {
    toFun z := L (z.1, (0, z.2))
    continuous_toFun := L.continuous.comp
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
    map_zero_left x := (L.apply_zero (0, x)).trans (H.apply_zero x)
    map_one_left x := L.apply_one (0, x) }
  let B : a.Homotopy b₀ := ⟨F, fun _ ↦ rfl, fun _ ↦ rfl⟩
  refine ⟨b, A.trans B, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hFK (1, x) hx
  · intro t x hx
    apply trans_pointwise_property A B x (fun y ↦ y ∈ Set.range (cone n)) ?_ ?_ t
    · intro s
      have hc : H (0, x) ∈ Set.range (cone n) := by rw [H.apply_zero]; exact hfK x hx
      have he := hLC s (0, x) hc
      change L (s, (0, x)) ∈ Set.range (cone n)
      rw [he]
      exact hc
    · exact fun s ↦ hFK (s, x) hx
  · intro x hx t
    apply trans_pointwise_property A B x (fun y ↦ y ∈ Set.range (base n)) ?_ ?_ t
    · exact fun s ↦ hLA s (0, x) (hx 0)
    · intro s
      have he := hLA 1 (s, x) (hx s)
      rwa [L.apply_one] at he
  · intro x hx hc t
    have hcx (s : I) : H.toContinuousMap (s, x) ∈ Set.range (cone n) := by
      change H (s, x) ∈ Set.range (cone n)
      rw [hc s]
      exact hx
    apply trans_pointwise_property A B x (fun y ↦ y = f x) ?_ ?_ t
    · intro s
      exact (hLC s (0, x) (hcx 0)).trans (hc 0)
    · intro s
      have he := hLC 1 (s, x) (hcx s)
      rw [L.apply_one] at he
      exact he.trans (hc s)

end NoExoticSixSphere.JamesSphere.SecondStageCone
