import Wikipedia.HopfProblem.HolomorphicPicardCechRefinement

/-!
# Descent of actual coboundaries from a refining cover

A solution on an actual refining open cover gives compatible local
solutions on each original open. The genuine sheaf gluing axiom produces
an original solution. In particular, refinement of covers is injective
on degree-one Čech cohomology; no Čech/derived comparison is assumed.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.Cech

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    {ι κ : Type} {U : ι → Opens X} {V : κ → Opens X}
    (r : κ → ι) (hr : ∀ a, V a ≤ U (r a))
    (c : CechOneCocycle F U) (b : ZeroCochain F V)

def refinementSolutionPiece (i : ι) (a : κ) : Section F (U i ⊓ V a) :=
  res F inf_le_right (b a) +
    res F (le_inf inf_le_left (inf_le_right.trans (hr a))) (c.value i (r a))

theorem refinementSolutionPiece_compatible
    (hb : ∀ a d, res F inf_le_left (b a) - res F inf_le_right (b d) =
      (refinement F r hr c).value a d) (i : ι) :
    TopCat.Presheaf.IsCompatible F.obj (fun a => U i ⊓ V a)
      (refinementSolutionPiece r hr c b i) := by
  intro a d
  change res F inf_le_left (refinementSolutionPiece r hr c b i a) =
    res F inf_le_right (refinementSolutionPiece r hr c b i d)
  simp only [refinementSolutionPiece, map_add, res_trans]
  let W := (U i ⊓ V a) ⊓ (U i ⊓ V d)
  have hi : W ≤ U i := inf_le_left.trans inf_le_left
  have ha : W ≤ V a := inf_le_left.trans inf_le_right
  have hd : W ≤ V d := inf_le_right.trans inf_le_right
  have hb' := congrArg (res F (le_inf ha hd)) (hb a d)
  simp only [map_sub, refinement_value, res_trans] at hb'
  have hc := restrict_condition c hi (ha.trans (hr a)) (hd.trans (hr d))
  calc
    _ = (res F ha (b a) - res F hd (b d)) + res F hd (b d) +
        res F (le_inf hi (ha.trans (hr a))) (c.value i (r a)) := by abel
    _ = res F hd (b d) +
        (res F (le_inf hi (ha.trans (hr a))) (c.value i (r a)) +
          res F (le_inf (ha.trans (hr a)) (hd.trans (hr d)))
            (c.value (r a) (r d))) := by rw [hb']; abel
    _ = _ := congrArg (res F hd (b d) + ·) hc

variable (hV : ∀ x : X, ∃ a, x ∈ V a)

include hV

theorem cover_inter_le_iSup (A : Opens X) : A ≤ ⨆ a, A ⊓ V a := by
  intro x hx
  obtain ⟨a, ha⟩ := hV x
  exact Opens.mem_iSup.mpr ⟨a, hx, ha⟩

/-- Actual sheaf gluing descends a solution from a genuine refining cover. -/
theorem solvable_of_refinement_solvable
    (hc : (refinement F r hr c).Solvable) : c.Solvable := by
  classical
  obtain ⟨b, hb⟩ := hc
  have hglue (i : ι) : ∃ s : Section F (U i), ∀ a,
      res F inf_le_left s = refinementSolutionPiece r hr c b i a := by
    obtain ⟨s, hs, _⟩ := F.existsUnique_gluing' (fun a => U i ⊓ V a) (U i)
      (fun _ => homOfLE inf_le_left) (cover_inter_le_iSup hV (U i))
      (refinementSolutionPiece r hr c b i)
      (refinementSolutionPiece_compatible r hr c b hb i)
    exact ⟨s, hs⟩
  choose s hs using hglue
  refine ⟨s, fun i j => ?_⟩
  apply F.eq_of_locally_eq' (fun a => (U i ⊓ U j) ⊓ V a) (U i ⊓ U j)
    (fun _ => homOfLE inf_le_left) (cover_inter_le_iSup hV (U i ⊓ U j))
  intro a
  let W := (U i ⊓ U j) ⊓ V a
  have hi : W ≤ U i := inf_le_left.trans inf_le_left
  have hj : W ≤ U j := inf_le_left.trans inf_le_right
  have ha : W ≤ V a := inf_le_right
  have hsi := congrArg (res F (le_inf hi ha)) (hs i a)
  have hsj := congrArg (res F (le_inf hj ha)) (hs j a)
  simp only [refinementSolutionPiece, map_add, res_trans] at hsi hsj
  change res F inf_le_left (res F inf_le_left (s i) - res F inf_le_right (s j)) =
    res F inf_le_left (c.value i j)
  simp only [map_sub, res_trans]
  rw [hsi, hsj]
  calc
    _ = res F (le_inf hi (ha.trans (hr a))) (c.value i (r a)) -
        res F (le_inf hj (ha.trans (hr a))) (c.value j (r a)) := by abel
    _ = _ := sub_eq_iff_eq_add.mpr
      (restrict_condition c hi hj (ha.trans (hr a))).symm

theorem refinement_solvable_iff : (refinement F r hr c).Solvable ↔ c.Solvable := by
  constructor
  · exact solvable_of_refinement_solvable r hr c hV
  · rintro ⟨b, hb⟩
    have hc : coboundary F U b = c := cocycle_ext F U hb
    rw [← hc, refinement_coboundary]
    exact ⟨_, fun _ _ => rfl⟩

theorem cohomologyRefinement_injective :
    Function.Injective (cohomologyRefinement F r hr) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h c =>
    induction y using Quotient.inductionOn with
    | h d =>
      change classOf F V (refinement F r hr c) =
        classOf F V (refinement F r hr d) → classOf F U c = classOf F U d
      intro h
      apply (class_eq_class_iff F U c d).mpr
      apply (refinement_solvable_iff r hr (c - d) hV).mp
      rw [map_sub]
      exact (class_eq_class_iff F V _ _).mp h

end Wikipedia.HopfProblem.HolomorphicPicard.Cech
