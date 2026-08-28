import Wikipedia.NoExoticSixSphere.QuotientAttachment
import Wikipedia.NoExoticSixSphere.RelativeCompression

/-!
# Descent of relative compression through an actual quotient attachment

After straightening at the attaching domain, all nontrivial quotient
fibers are fixed. The actual pushout therefore glues the homotopy to a
strong deformation retraction of the quotient onto the specified
subspace. This is the descent step for the auxiliary James cone stages.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Set Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.QuotientRelativeCompression

variable {X Q : TopCat.{u}} (q : X ⟶ Q) (S : Set Q)
    (hq : IsQuotientMap q) (hf : ∀ x y, q x = q y → q x ∈ S ∨ x = y)
    (r : C(X, S))
    (K : q.hom.HomotopyRel
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(S, Q)).comp r)
      (Set.range (QuotientAttachment.boundaryInclusion q S)))

def stationaryFamily : C(I × S, Q) :=
  ⟨fun p ↦ p.2.val, continuous_subtype_val.comp continuous_snd⟩

theorem family_compatible (t : I) (a : q ⁻¹' S) :
    stationaryFamily S (t, QuotientAttachment.boundaryMap q S a) =
      K.toContinuousMap (t, QuotientAttachment.boundaryInclusion q S a) :=
  (K.prop' t a.val ⟨a, rfl⟩).symm

def family : C(I × Q, Q) :=
  PushoutHomotopy.glueFamily (stationaryFamily S) K.toContinuousMap
    (family_compatible q S r K) (QuotientAttachment.isPushout q S hq hf)

theorem family_map (t : I) (x : X) : family q S hq hf r K (t, q x) = K (t, x) :=
  PushoutHomotopy.glueFamily_inr
    (S := TopCat.of (q ⁻¹' S)) (A := TopCat.of S) (B := X) (P := Q) (Z := Q)
    (f := QuotientAttachment.boundaryMap q S)
    (g := QuotientAttachment.boundaryInclusion q S)
    (i := QuotientAttachment.inclusion (Q := Q) S) (j := q)
    (stationaryFamily S) K.toContinuousMap
    (family_compatible q S r K) (QuotientAttachment.isPushout q S hq hf) t x

theorem family_subspace (t : I) (s : S) : family q S hq hf r K (t, s.val) = s.val :=
  PushoutHomotopy.glueFamily_inl
    (S := TopCat.of (q ⁻¹' S)) (A := TopCat.of S) (B := X) (P := Q) (Z := Q)
    (f := QuotientAttachment.boundaryMap q S)
    (g := QuotientAttachment.boundaryInclusion q S)
    (i := QuotientAttachment.inclusion (Q := Q) S) (j := q)
    (stationaryFamily S) K.toContinuousMap
    (family_compatible q S r K) (QuotientAttachment.isPushout q S hq hf) t s

theorem family_zero (y : Q) : family q S hq hf r K (0, y) = y := by
  obtain ⟨x, rfl⟩ := hq.surjective y
  exact (family_map q S hq hf r K 0 x).trans (K.map_zero_left x)

theorem family_one_mem (y : Q) : family q S hq hf r K (1, y) ∈ S := by
  obtain ⟨x, rfl⟩ := hq.surjective y
  have he : family q S hq hf r K (1, q x) = (r x).val :=
    (family_map q S hq hf r K 1 x).trans (K.map_one_left x)
  rw [he]
  exact (r x).property

def retraction : C(Q, S) :=
  ⟨fun y ↦ ⟨family q S hq hf r K (1, y), family_one_mem q S hq hf r K y⟩,
    ((family q S hq hf r K).continuous.comp
      (continuous_const.prodMk continuous_id)).subtype_mk _⟩

theorem retraction_subspace (s : S) : retraction q S hq hf r K s.val = s :=
  Subtype.ext (family_subspace q S hq hf r K 1 s)

def deformation : (ContinuousMap.id Q).HomotopyRel
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(S, Q)).comp (retraction q S hq hf r K)) S where
  toContinuousMap := family q S hq hf r K
  map_zero_left := family_zero q S hq hf r K
  map_one_left _ := rfl
  prop' t y hy := family_subspace q S hq hf r K t ⟨y, hy⟩

include hq hf in
theorem exists_deformation
    (hi : HomotopyExtension.HasHomotopyExtension (QuotientAttachment.boundaryInclusion q S))
    {g : C(X, Q)} (H : q.hom.Homotopy g)
    (hS : ∀ t (x : q ⁻¹' S), H (t, x.val) ∈ S) (hg : ∀ x, g x ∈ S) :
    ∃ R : C(Q, S), (∀ s : S, R s.val = s) ∧
      Nonempty ((ContinuousMap.id Q).HomotopyRel
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(S, Q)).comp R) S) := by
  obtain ⟨r, ⟨K⟩⟩ := RelativeCompression.exists_relative
    (QuotientAttachment.boundaryInclusion q S) hi S H hS hg
  exact ⟨retraction q S hq hf r K, retraction_subspace q S hq hf r K,
    ⟨deformation q S hq hf r K⟩⟩

end NoExoticSixSphere.QuotientRelativeCompression
