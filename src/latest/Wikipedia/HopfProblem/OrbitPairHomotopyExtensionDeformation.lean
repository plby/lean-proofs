import Wikipedia.HopfProblem.OrbitPairHomotopyBacktrackContraction

/-!
# A homotopy equivalence with homotopy extension is a strong deformation retract

First adjust the inverse to an exact retraction. If `H` is a homotopy
from the identity to the resulting projection `p`, concatenate `H` with
the reverse of `H` precomposed by `p`. On the included subspace this is
exact backtracking. Its explicit contraction and the relative straightening
theorem supply a homotopy stationary on that subspace.
-/

noncomputable section

universe u

open CategoryTheory unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyExtension

theorem stationary_of_retraction {A B : TopCat.{u}} (i : A ⟶ B)
    (hi : HasHomotopyExtension i) (r : C(B, A))
    (hr : r.comp i.hom = ContinuousMap.id A)
    (H : (ContinuousMap.id B).Homotopy (i.hom.comp r)) :
    Nonempty ((ContinuousMap.id B).HomotopyRel (i.hom.comp r) (Set.range i)) := by
  let p := i.hom.comp r
  have hpi (a : A) : p (i a) = i a :=
    congrArg i (ContinuousMap.congr_fun hr a)
  have hpp : p.comp p = p := by
    apply ContinuousMap.ext
    intro b
    exact hpi (r b)
  let L : p.Homotopy p :=
    (H.compContinuousMap p).cast (ContinuousMap.id_comp p) hpp
  let J := H.trans L.symm
  have hJ (t : I) (a : A) : J (t, i a) = (H.trans H.symm) (t, i a) := by
    change (H.trans L.symm) (t, i a) = _
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · rfl
    · change H (σ _, p (i a)) = H (σ _, i a)
      rw [hpi]
  let K := (backtrackContraction H).comp ((ContinuousMap.id I).prodMap i.hom)
  apply exists_relative_of_boundary_contraction i hi J K
  · intro a
    apply ContinuousMap.ext
    intro t
    exact (backtrackContraction_initial H (i a) t).trans (hJ t a).symm
  · intro a t
    exact backtrackContraction_final H (i a) t
  · intro s a
    exact backtrackContraction_zero H s (i a)
  · intro s a
    exact (backtrackContraction_one H s (i a)).trans (hpi a).symm

theorem exists_strong_deformation_retraction {A B : TopCat.{u}} (i : A ⟶ B)
    (hi : HasHomotopyExtension i) (e : ContinuousMap.HomotopyEquiv A B)
    (he : e.toFun = i.hom) :
    ∃ r : C(B, A), r.comp i.hom = ContinuousMap.id A ∧
      Nonempty ((ContinuousMap.id B).HomotopyRel (i.hom.comp r) (Set.range i)) := by
  obtain ⟨r, hr, ⟨H⟩⟩ := exists_retraction i hi e he
  exact ⟨r, hr, stationary_of_retraction i hi r hr H.symm⟩

end Wikipedia.HopfProblem.OrbitPair.HomotopyExtension
