import StackExchange.Puzzling139335.SourceFaceBridge.Defs
import StackExchange.Puzzling139335.SourceFaceBridge.ProperModel
import StackExchange.Puzzling139335.ProperRotation

/-!
# Actual common points give the scalar contact witnesses

The contact inequalities are identities with source heights.  Thus membership
in the lower source rectangle supplies them directly; no separation or
intersection conclusion is part of the hypotheses.
-/

open Set

namespace Puzzling139335.SourceFaceBridge

namespace FaceData

/-- At an actual common point, the left-source contact expression is the
right-source height. -/
theorem proper_contact_left_height (d : FaceData) {rp tp : Plane}
    (hcommon : d.right rp = d.leftProper tp) :
    d.scalarData.nt - d.scalarData.delta * tp 0 + d.scalarData.cosSum * tp 1 = rp 1 := by
  have hx := congrArg (fun p : Plane => p 0) hcommon
  have hy := congrArg (fun p : Plane => p 1) hcommon
  change 1 + (-d.scalarData.c * rp 0 + d.scalarData.s * rp 1) - d.scalarData.u =
    d.scalarData.w - (d.scalarData.d * tp 0 + d.scalarData.q * tp 1) at hx
  change 1 / 2 + (-d.scalarData.s * rp 0 - d.scalarData.c * rp 1) - d.scalarData.v =
    1 / 2 - (-d.scalarData.q * tp 0 + d.scalarData.d * tp 1) + d.scalarData.z at hy
  have hcircle : d.scalarData.c ^ 2 + d.scalarData.s ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq d.α
  dsimp [ProperRotation.Data.nt, ProperRotation.Data.delta, ProperRotation.Data.cosSum]
  linear_combination -d.scalarData.s * hx + d.scalarData.c * hy + rp 1 * hcircle

/-- At an actual common point, the right-source contact expression is the
left-source height. -/
theorem proper_contact_right_height (d : FaceData) {rp tp : Plane}
    (hcommon : d.right rp = d.leftProper tp) :
    -d.scalarData.ns + d.scalarData.delta * rp 0 + d.scalarData.cosSum * rp 1 = tp 1 := by
  have hx := congrArg (fun p : Plane => p 0) hcommon
  have hy := congrArg (fun p : Plane => p 1) hcommon
  change 1 + (-d.scalarData.c * rp 0 + d.scalarData.s * rp 1) - d.scalarData.u =
    d.scalarData.w - (d.scalarData.d * tp 0 + d.scalarData.q * tp 1) at hx
  change 1 / 2 + (-d.scalarData.s * rp 0 - d.scalarData.c * rp 1) - d.scalarData.v =
    1 / 2 - (-d.scalarData.q * tp 0 + d.scalarData.d * tp 1) + d.scalarData.z at hy
  have hcircle : d.scalarData.d ^ 2 + d.scalarData.q ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq d.β
  dsimp [ProperRotation.Data.ns, ProperRotation.Data.delta, ProperRotation.Data.cosSum]
  linear_combination -d.scalarData.q * hx - d.scalarData.d * hy + tp 1 * hcircle

end FaceData

namespace SupportedSource

/-- Two distinct actual common image points supply both scalar contact pairs. -/
theorem twoContacts_of_commonPreimages {d : FaceData} {P : Set Plane}
    (h : SupportedSource d false P) {rp₁ tp₁ rp₂ tp₂ : Plane}
    (hr₁ : rp₁ ∈ P) (ht₁ : tp₁ ∈ P) (hr₂ : rp₂ ∈ P) (ht₂ : tp₂ ∈ P)
    (hcommon₁ : d.right rp₁ = d.leftProper tp₁)
    (hcommon₂ : d.right rp₂ = d.leftProper tp₂)
    (hne : d.right rp₁ ≠ d.right rp₂) :
    ProperRotation.TwoLeftContacts d.scalarData ∧
      ProperRotation.TwoRightContacts d.scalarData := by
  have hr₁box := h.source_subset hr₁
  have ht₁box := h.source_subset ht₁
  have hr₂box := h.source_subset hr₂
  have ht₂box := h.source_subset ht₂
  have hleft_ne : (tp₁ 0, tp₁ 1) ≠ (tp₂ 0, tp₂ 1) := by
    intro heq
    have hpoints : tp₁ = tp₂ :=
      point_ext (congrArg Prod.fst heq) (congrArg Prod.snd heq)
    apply hne
    exact hcommon₁.trans ((congrArg d.leftProper hpoints).trans hcommon₂.symm)
  have hright_ne : (rp₁ 0, rp₁ 1) ≠ (rp₂ 0, rp₂ 1) := by
    intro heq
    apply hne
    exact congrArg d.right (point_ext (congrArg Prod.fst heq) (congrArg Prod.snd heq))
  constructor
  · refine ⟨tp₁ 0, tp₁ 1, tp₂ 0, tp₂ 1,
      ht₁box.1.1, ht₁box.2.1, ht₂box.1.1, ht₂box.2.1, hleft_ne, ?_, ?_⟩
    · rw [d.proper_contact_left_height hcommon₁]
      exact hr₁box.2.1
    · rw [d.proper_contact_left_height hcommon₂]
      exact hr₂box.2.1
  · refine ⟨rp₁ 0, rp₁ 1, rp₂ 0, rp₂ 1,
      hr₁box.1.2, hr₁box.2.1, hr₂box.1.2, hr₂box.2.1, hright_ne, ?_, ?_⟩
    · rw [d.proper_contact_right_height hcommon₁]
      exact ht₁box.2.1
    · rw [d.proper_contact_right_height hcommon₂]
      exact ht₂box.2.1

/-- The contact witnesses follow from two distinct points of the actual
intersection of the proper image sets. -/
theorem twoContacts_of_twoCommonPoints {d : FaceData} {P : Set Plane}
    (h : SupportedSource d false P) {x y : Plane}
    (hx : x ∈ d.right '' P ∩ d.leftProper '' P)
    (hy : y ∈ d.right '' P ∩ d.leftProper '' P) (hne : x ≠ y) :
    ProperRotation.TwoLeftContacts d.scalarData ∧
      ProperRotation.TwoRightContacts d.scalarData := by
  obtain ⟨rp₁, hr₁, hrx⟩ := hx.1
  obtain ⟨tp₁, ht₁, htx⟩ := hx.2
  obtain ⟨rp₂, hr₂, hry⟩ := hy.1
  obtain ⟨tp₂, ht₂, hty⟩ := hy.2
  apply h.twoContacts_of_commonPreimages hr₁ ht₁ hr₂ ht₂
    (hrx.trans htx.symm) (hry.trans hty.symm)
  simpa only [hrx, hry] using hne

/-- Nontriviality of the actual common set is enough; no parametrization
or regularity of its boundary is required for this scalar bridge. -/
theorem twoContacts_of_nontrivial_intersection {d : FaceData} {P : Set Plane}
    (h : SupportedSource d false P)
    (hcommon : (d.right '' P ∩ d.leftProper '' P).Nontrivial) :
    ProperRotation.TwoLeftContacts d.scalarData ∧
      ProperRotation.TwoRightContacts d.scalarData := by
  obtain ⟨x, hx, y, hy, hne⟩ := hcommon
  exact h.twoContacts_of_twoCommonPoints hx hy hne

/-- Actual support geometry and a nontrivial actual common set put both
unit-base intersection parameters strictly between their endpoints. -/
theorem proper_strict_intersection_parameters {d : FaceData} {P : Set Plane}
    (h : SupportedSource d false P)
    (hcommon : (d.right '' P ∩ d.leftProper '' P).Nontrivial) :
    0 < d.scalarData.ns / d.scalarData.delta ∧
      d.scalarData.ns / d.scalarData.delta < 1 ∧
      0 < d.scalarData.nt / d.scalarData.delta ∧
      d.scalarData.nt / d.scalarData.delta < 1 := by
  obtain ⟨hleft, hright⟩ := h.twoContacts_of_nontrivial_intersection hcommon
  exact h.toProperModel.strict_intersection_parameters hleft hright

end SupportedSource

end Puzzling139335.SourceFaceBridge
