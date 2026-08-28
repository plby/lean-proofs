import Wikipedia.HopfProblem.OrbitPairHomotopyBacktrackContraction
import Wikipedia.NoExoticSixSphere.SubspaceCofibration

/-!
# Compressing a map into a subspace while fixing its specified boundary

A homotopy through maps of pairs whose final image lies in the target
subspace can be straightened relative to a source cofibration. Extend
the reversed boundary motion inside the target subspace, then contract
the resulting exact boundary backtrack. This is the relative-compression
step used in the finite-stage James cone argument.
-/

noncomputable section

universe u

open CategoryTheory Set Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.RelativeCompression

theorem exists_relative {A B Z : TopCat.{u}} (i : A ⟶ B)
    (hi : HomotopyExtension.HasHomotopyExtension i) (S : Set Z)
    {f g : C(B, Z)} (H : f.Homotopy g)
    (hS : ∀ t a, H (t, i a) ∈ S) (hg : ∀ b, g b ∈ S) :
    ∃ r : C(B, S), Nonempty (f.HomotopyRel
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(S, Z)).comp r) (Set.range i)) := by
  let gS : C(B, S) := ⟨fun b ↦ ⟨g b, hg b⟩, g.continuous.subtype_mk _⟩
  let G : C(I × A, S) :=
    ⟨fun p ↦ ⟨H (σ p.1, i p.2), hS _ _⟩,
      (H.continuous.comp ((continuous_symm.comp continuous_fst).prodMk
        (i.hom.continuous.comp continuous_snd))).subtype_mk _⟩
  have hG0 : ∀ a, G (0, a) = gS (i a) := by
    intro a
    apply Subtype.ext
    change H (σ 0, i a) = g (i a)
    rw [symm_zero]
    exact H.map_one_left (i a)
  obtain ⟨L, hL0, hLi⟩ := hi (TopCat.of S) gS G hG0
  let r : C(B, S) := L.comp ⟨fun b ↦ (1, b), continuous_const.prodMk continuous_id⟩
  let j : C(S, Z) := ⟨Subtype.val, continuous_subtype_val⟩
  let K : g.Homotopy (j.comp r) :=
    { toContinuousMap := j.comp L
      map_zero_left := fun b ↦ congrArg Subtype.val (hL0 b)
      map_one_left := fun _ ↦ rfl }
  have hKi (t : I) (a : A) : K (t, i a) = H (σ t, i a) :=
    congrArg Subtype.val (hLi t a)
  have hri (a : A) : j (r (i a)) = f (i a) := by
    have he := hKi 1 a
    rw [symm_one] at he
    exact he.trans (H.map_zero_left (i a))
  let J := H.trans K
  have hJ (t : I) (a : A) : J (t, i a) = (H.trans H.symm) (t, i a) := by
    change (H.trans K) (t, i a) = _
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · rfl
    · exact hKi _ a
  let C := (HomotopyExtension.backtrackContraction H).comp
    ((ContinuousMap.id I).prodMap i.hom)
  refine ⟨r, HomotopyExtension.exists_relative_of_boundary_contraction i hi J C ?_ ?_ ?_ ?_⟩
  · intro a
    apply ContinuousMap.ext
    intro t
    exact (HomotopyExtension.backtrackContraction_initial H (i a) t).trans (hJ t a).symm
  · intro a t
    exact HomotopyExtension.backtrackContraction_final H (i a) t
  · intro s a
    exact HomotopyExtension.backtrackContraction_zero H s (i a)
  · intro s a
    exact (HomotopyExtension.backtrackContraction_one H s (i a)).trans (hri a).symm

end NoExoticSixSphere.RelativeCompression
