import Wikipedia.NoExoticSixSphere.CutoffHomotopyGluing

/-!
# Extending an open-domain homotopy of a map

A time cutoff supported in the open domain extends a local homotopy by
the original map outside that domain. The target need not be the source.
-/

noncomputable section

open Set Filter Topology
open scoped unitInterval

namespace NoExoticSixSphere.OpenMapHomotopyExtension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X}
  (f : C(X, Y)) (H : C(I × A, Y)) (β : C(X, ℝ)) (hβ : ∀ x, β x ∈ I)

def raw (tx : I × X) : Y := by
  classical
  exact if hx : tx.2 ∈ A then H (CutoffHomotopyGluing.clock β hβ tx, ⟨tx.2, hx⟩)
    else f tx.2

theorem raw_of_mem {x : X} (hx : x ∈ A) (t : I) :
    raw f H β hβ (t, x) = H (CutoffHomotopyGluing.clock β hβ (t, x), ⟨x, hx⟩) := by
  classical
  simp only [raw, dif_pos hx]

theorem raw_of_notMem {x : X} (hx : x ∉ A) (t : I) :
    raw f H β hβ (t, x) = f x := by
  classical
  simp only [raw, dif_neg hx]

variable (hzero : ∀ x : A, H (0, x) = f x.1)

include hzero

theorem raw_of_zero {x : X} (hx : β x = 0) (t : I) : raw f H β hβ (t, x) = f x := by
  by_cases hA : x ∈ A
  · rw [raw_of_mem f H β hβ hA, CutoffHomotopyGluing.clock_of_zero β hβ hx, hzero]
  · exact raw_of_notMem f H β hβ hA t

theorem continuous_raw (hA : IsOpen A) (hsupport : tsupport β ⊆ A) :
    Continuous (raw f H β hβ) := by
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
    have hrestrict : Continuous (raw f H β hβ ∘ (Subtype.val : W → I × X)) := by
      apply hlocal.congr
      intro q
      exact (raw_of_mem f H β hβ q.2 q.1.1).symm
    exact hW.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
      (hrestrict.continuousAt (x := ⟨tx, hx⟩))
  · have hn : tx.2 ∉ tsupport β := fun h ↦ hx (hsupport h)
    have heq : raw f H β hβ =ᶠ[𝓝 tx] (fun q ↦ f q.2) := by
      filter_upwards [((isClosed_tsupport β).isOpen_compl.preimage continuous_snd).mem_nhds hn]
        with q hq
      exact raw_of_zero f H β hβ hzero (image_eq_zero_of_notMem_tsupport hq) q.1
    exact (f.continuous.comp continuous_snd).continuousAt.congr heq.symm

def map (hA : IsOpen A) (hsupport : tsupport β ⊆ A) : C(I × X, Y) :=
  ⟨raw f H β hβ, continuous_raw f H β hβ hzero hA hsupport⟩

theorem raw_zero (x : X) : raw f H β hβ (0, x) = f x := by
  by_cases hx : x ∈ A
  · rw [raw_of_mem f H β hβ hx, CutoffHomotopyGluing.clock_zero, hzero]
  · exact raw_of_notMem f H β hβ hx 0

def endpoint (hA : IsOpen A) (hsupport : tsupport β ⊆ A) : C(X, Y) :=
  (map f H β hβ hzero hA hsupport).comp
    ⟨fun x ↦ (1, x), continuous_const.prodMk continuous_id⟩

def homotopy (hA : IsOpen A) (hsupport : tsupport β ⊆ A) :
    f.Homotopy (endpoint f H β hβ hzero hA hsupport) where
  toContinuousMap := map f H β hβ hzero hA hsupport
  map_zero_left := raw_zero f H β hβ hzero
  map_one_left _ := rfl

theorem endpoint_of_one (hA : IsOpen A) (hsupport : tsupport β ⊆ A)
    {x : X} (hx : x ∈ A) (hβx : β x = 1) :
    endpoint f H β hβ hzero hA hsupport x = H (1, ⟨x, hx⟩) := by
  change raw f H β hβ (1, x) = _
  rw [raw_of_mem f H β hβ hx, CutoffHomotopyGluing.clock_one_of_one β hβ hβx]

end NoExoticSixSphere.OpenMapHomotopyExtension
