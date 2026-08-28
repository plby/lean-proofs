import Wikipedia.NoExoticSixSphere.CutoffHomotopyGluing

/-!
# Extending a homotopy from an open domain by a supported clock

The local homotopy starts at the inclusion of its open domain. A continuous
time cutoff with support contained in that domain extends it by the identity
to the whole space. No compactness of the domain is needed.
-/

open Set Filter unitInterval
open scoped Topology

namespace NoExoticSixSphere.OpenHomotopyExtension

variable {X : Type*} [TopologicalSpace X] {A : Set X}
  (H : C(I × A, X)) (β : C(X, ℝ)) (hβ : ∀ x, β x ∈ I)

noncomputable def raw (tx : I × X) : X := by
  classical
  exact if hx : tx.2 ∈ A then H (CutoffHomotopyGluing.clock β hβ tx, ⟨tx.2, hx⟩) else tx.2

theorem raw_of_mem {x : X} (hx : x ∈ A) (t : I) :
    raw H β hβ (t, x) = H (CutoffHomotopyGluing.clock β hβ (t, x), ⟨x, hx⟩) := by
  classical
  simp only [raw, dif_pos hx]

theorem raw_of_notMem {x : X} (hx : x ∉ A) (t : I) : raw H β hβ (t, x) = x := by
  classical
  simp only [raw, dif_neg hx]

variable (hzero : ∀ x : A, H (0, x) = x.1)

include hzero

theorem raw_of_zero {x : X} (hx : β x = 0) (t : I) : raw H β hβ (t, x) = x := by
  by_cases hA : x ∈ A
  · rw [raw_of_mem H β hβ hA, CutoffHomotopyGluing.clock_of_zero β hβ hx, hzero]
  · exact raw_of_notMem H β hβ hA t

theorem continuous_raw (hA : IsOpen A) (hsupport : tsupport β ⊆ A) :
    Continuous (raw H β hβ) := by
  apply continuous_iff_continuousAt.mpr
  intro tx
  by_cases hx : tx.2 ∈ A
  · let W : Set (I × X) := Prod.snd ⁻¹' A
    have hW : IsOpen W := hA.preimage continuous_snd
    have hlocal : Continuous (fun q : W ↦
        H (CutoffHomotopyGluing.clock β hβ q.1, ⟨q.1.2, q.2⟩)) :=
      H.continuous.comp (((CutoffHomotopyGluing.continuous_clock β hβ).comp
        continuous_subtype_val).prodMk
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
    have hrestrict : Continuous (raw H β hβ ∘ (Subtype.val : W → I × X)) := by
      apply hlocal.congr
      intro q
      exact (raw_of_mem H β hβ q.2 q.1.1).symm
    exact hW.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
      (hrestrict.continuousAt (x := ⟨tx, hx⟩))
  · have hn : tx.2 ∉ tsupport β := fun h ↦ hx (hsupport h)
    have heq : raw H β hβ =ᶠ[𝓝 tx] Prod.snd := by
      filter_upwards [((isClosed_tsupport β).isOpen_compl.preimage continuous_snd).mem_nhds hn]
        with q hq
      exact raw_of_zero H β hβ hzero (image_eq_zero_of_notMem_tsupport hq) q.1
    exact continuousAt_snd.congr heq.symm

noncomputable def map (hA : IsOpen A) (hsupport : tsupport β ⊆ A) : C(I × X, X) :=
  ⟨raw H β hβ, continuous_raw H β hβ hzero hA hsupport⟩

theorem raw_zero (x : X) : raw H β hβ (0, x) = x := by
  by_cases hx : x ∈ A
  · rw [raw_of_mem H β hβ hx, CutoffHomotopyGluing.clock_zero, hzero]
  · exact raw_of_notMem H β hβ hx 0

noncomputable def endpoint (hA : IsOpen A) (hsupport : tsupport β ⊆ A) : C(X, X) :=
  (map H β hβ hzero hA hsupport).comp ⟨fun x ↦ (1, x), continuous_const.prodMk continuous_id⟩

noncomputable def homotopy (hA : IsOpen A) (hsupport : tsupport β ⊆ A)
    (S : Set X) (hfixed : ∀ (t : I) (x : A), x.1 ∈ S → H (t, x) = x.1) :
    ContinuousMap.HomotopyRel (ContinuousMap.id X) (endpoint H β hβ hzero hA hsupport)
      (S ∪ {x | β x = 0}) where
  toContinuousMap := map H β hβ hzero hA hsupport
  map_zero_left := raw_zero H β hβ hzero
  map_one_left _ := rfl
  prop' t x hx := by
    change raw H β hβ (t, x) = x
    rcases hx with hx | hx
    · by_cases hm : x ∈ A
      · rw [raw_of_mem H β hβ hm]
        exact hfixed _ ⟨x, hm⟩ hx
      · exact raw_of_notMem H β hβ hm t
    · exact raw_of_zero H β hβ hzero hx t

end NoExoticSixSphere.OpenHomotopyExtension
