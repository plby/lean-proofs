import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# The literal collapse map to a one-point compactification

A point of the chosen subset is sent to the added point. Every other
point is sent to its literal representative in the complement subtype.
The fibers identify precisely the chosen subset and no other points.
-/

noncomputable section

open Set
open scoped OnePoint

namespace Wikipedia.HopfProblem.SixSphereCube

variable {K : Type*} (F : Set K)

/-- Collapse exactly `F` to the added point of the native one-point type. -/
def collapse (a : K) : OnePoint ↥Fᶜ := by
  classical
  exact if h : a ∈ F then ∞ else ((⟨a, h⟩ : ↥Fᶜ) : OnePoint ↥Fᶜ)

@[simp] theorem collapse_of_mem {a : K} (ha : a ∈ F) : collapse F a = ∞ := by
  classical
  simp only [collapse, dif_pos ha]

theorem collapse_of_not_mem {a : K} (ha : a ∉ F) :
    collapse F a = ((⟨a, ha⟩ : ↥Fᶜ) : OnePoint ↥Fᶜ) := by
  classical
  simp only [collapse, dif_neg ha]

@[simp] theorem collapse_coe (a : ↥Fᶜ) : collapse F a.val = (a : OnePoint ↥Fᶜ) :=
  collapse_of_not_mem F a.property

@[simp] theorem collapse_eq_infty_iff (a : K) : collapse F a = ∞ ↔ a ∈ F := by
  classical
  by_cases ha : a ∈ F
  · simp only [collapse_of_mem F ha, ha]
  · simp only [collapse_of_not_mem F ha, OnePoint.coe_ne_infty, ha]

/-- Only points of the collapsed subset can acquire a new common image. -/
theorem collapse_eq_iff (a b : K) :
    collapse F a = collapse F b ↔ a = b ∨ a ∈ F ∧ b ∈ F := by
  classical
  constructor
  · intro h
    by_cases ha : a ∈ F
    · exact Or.inr ⟨ha, (collapse_eq_infty_iff F b).mp
        (h.symm.trans (collapse_of_mem F ha))⟩
    · have hb : b ∉ F := fun hb => ha ((collapse_eq_infty_iff F a).mp
        (h.trans (collapse_of_mem F hb)))
      rw [collapse_of_not_mem F ha, collapse_of_not_mem F hb] at h
      exact Or.inl (congrArg Subtype.val (OnePoint.coe_injective h))
  · rintro (rfl | ⟨ha, hb⟩)
    · rfl
    · rw [collapse_of_mem F ha, collapse_of_mem F hb]

/-- Nonemptiness supplies the added point; complement points already lift literally. -/
theorem collapse_surjective (hne : F.Nonempty) : Function.Surjective (collapse F) := by
  intro z
  induction z using OnePoint.rec with
  | infty =>
      obtain ⟨a, ha⟩ := hne
      exact ⟨a, collapse_of_mem F ha⟩
  | coe a => exact ⟨a.val, collapse_coe F a⟩

/-- Away from the added point, preimages are literal images from the complement. -/
theorem collapse_preimage_of_not_mem (s : Set (OnePoint ↥Fᶜ)) (hs : ∞ ∉ s) :
    collapse F ⁻¹' s = Subtype.val '' (((↑) : ↥Fᶜ → OnePoint ↥Fᶜ) ⁻¹' s) := by
  ext a
  constructor
  · intro ha
    change collapse F a ∈ s at ha
    have haF : a ∉ F := by
      intro haF
      exact hs (by simpa only [collapse_of_mem F haF] using ha)
    exact ⟨⟨a, haF⟩, by simpa only [mem_preimage, collapse_of_not_mem F haF] using ha, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    simpa only [mem_preimage, collapse_coe] using hb

/-- The complement of a set containing infinity is the literal subtype image. -/
theorem collapse_preimage_compl_of_mem (s : Set (OnePoint ↥Fᶜ)) (hs : ∞ ∈ s) :
    (collapse F ⁻¹' s)ᶜ =
      Subtype.val '' ((((↑) : ↥Fᶜ → OnePoint ↥Fᶜ) ⁻¹' s)ᶜ) :=
  collapse_preimage_of_not_mem F sᶜ (fun h => h hs)

end Wikipedia.HopfProblem.SixSphereCube
