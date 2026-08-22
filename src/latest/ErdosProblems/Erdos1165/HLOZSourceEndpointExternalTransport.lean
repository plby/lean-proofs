/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZThetaOneSourceShift
import ErdosProblems.Erdos1165.HLOZSourceOrientedExternalLocalTime

/-!
# External-chain transport for endpoint normalization

The spatial source transports preserve removable domino excursions, hence
the full phased external local time.  The checker row additionally deletes
time zero, which is exactly the `.shifted` temporal input.
-/

namespace Erdos1165.HLOZSourceEndpointExternalTransport

open HLOZSourceOrientedExternalLocalTime HLOZThetaOneSourceShift
open LazyDecomposition TilingLazyDecomposition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem phasedInput_even (p : List Point) :
    phasedInput .even p = p := by
  cases p <;> rfl

private theorem tilingRemovable_map_iff
    {t target : DominoTiling} {f : Point → Point}
    (hinj : Function.Injective f)
    (hpartner : ∀ x, tilingPartner target (f x) = f (tilingPartner t x))
    (a b c : Point) :
    TilingRemovable target (f a) (f b) (f c) ↔
      TilingRemovable t a b c := by
  unfold TilingRemovable
  constructor
  · rintro ⟨hba, hca⟩
    refine ⟨hinj ?_, hinj hca⟩
    exact hba.trans (hpartner a)
  · rintro ⟨hba, hca⟩
    subst b
    subst c
    exact ⟨(hpartner a).symm, rfl⟩

private theorem tilingCompressTail_map
    {t target : DominoTiling} {f : Point → Point}
    (hinj : Function.Injective f)
    (hpartner : ∀ x, tilingPartner target (f x) = f (tilingPartner t x)) :
    ∀ (a : Point) (rest : List Point),
      (tilingCompressTail t a rest).map f =
        tilingCompressTail target (f a) (rest.map f) := by
  intro a rest
  induction rest using List.twoStepInduction generalizing a with
  | nil => rfl
  | singleton b => rfl
  | cons_cons b c rest ih _ =>
      by_cases hrem : TilingRemovable t a b c
      · have hrem' : TilingRemovable target (f a) (f b) (f c) :=
          (tilingRemovable_map_iff hinj hpartner a b c).2 hrem
        change (tilingCompressTail t a (b :: c :: rest)).map f =
          tilingCompressTail target (f a) (f b :: f c :: rest.map f)
        rw [tilingCompressTail, tilingCompressTail, if_pos hrem, if_pos hrem']
        exact ih c
      · have hrem' : ¬TilingRemovable target (f a) (f b) (f c) :=
          (tilingRemovable_map_iff hinj hpartner a b c).not.mpr hrem
        change (tilingCompressTail t a (b :: c :: rest)).map f =
          tilingCompressTail target (f a) (f b :: f c :: rest.map f)
        rw [tilingCompressTail, tilingCompressTail, if_neg hrem, if_neg hrem']
        simp only [List.map_cons, List.cons.injEq, true_and]
        rw [ih c]

private theorem tilingExternalPath_map
    {t target : DominoTiling} {f : Point → Point}
    (hinj : Function.Injective f)
    (hpartner : ∀ x, tilingPartner target (f x) = f (tilingPartner t x))
    (p : List Point) :
    (tilingExternalPath t p).map f =
      tilingExternalPath target (p.map f) := by
  cases p with
  | nil => rfl
  | cons a rest =>
      simp only [tilingExternalPath, List.map_cons, List.cons.injEq, true_and]
      exact tilingCompressTail_map hinj hpartner a rest

private theorem externalLocalTime_map
    {t target : DominoTiling} {f : Point → Point}
    (hinj : Function.Injective f)
    (hpartner : ∀ x, tilingPartner target (f x) = f (tilingPartner t x))
    (p : List Point) (x : Point) :
    listLocalTime (tilingExternalPath target (p.map f)) (f x) =
      listLocalTime (tilingExternalPath t p) x := by
  unfold listLocalTime
  rw [← tilingExternalPath_map hinj hpartner]
  exact List.count_map_of_injective _ f hinj x

private theorem finitePathList_horizontalReflect
    (s : WalkPath) (n : ℕ) :
    finitePathList (pathPrefix (horizontalReflectPath s) n) =
      (finitePathList (pathPrefix s n)).map horizontalReflectPoint := by
  unfold finitePathList
  rw [List.map_ofFn]
  rfl

theorem pathPhasedExternalLocalTime_horizontalReflect
    {t : DominoTiling} (ht : IsColumnTiling t)
    (o : Orientation) (s : WalkPath) (n : ℕ) (x : Point) :
    pathPhasedExternalLocalTime (reflectedColumnTiling t) o
        (horizontalReflectPath s) n (horizontalReflectPoint x) =
      pathPhasedExternalLocalTime t o s n x := by
  unfold pathPhasedExternalLocalTime phasedExternalLocalTime
  rw [finitePathList_horizontalReflect]
  cases o with
  | even =>
      rw [phasedInput_even, phasedInput_even]
      exact externalLocalTime_map
        (Function.Involutive.injective horizontalReflectPoint_involutive)
        (fun y ↦ tilingPartner_reflectedColumn ht y) _ _
  | shifted =>
      cases hpath : finitePathList (pathPrefix s n) with
      | nil => simp [phasedInput, listLocalTime, tilingExternalPath]
      | cons a rest =>
          simp only [List.map_cons, phasedInput]
          exact
            (externalLocalTime_map
            (Function.Involutive.injective horizontalReflectPoint_involutive)
            (fun y ↦ tilingPartner_reflectedColumn ht y) rest x)

private theorem finitePathList_oneStepRecenter
    (omega : StepPath) (n : ℕ) :
    finitePathList (pathPrefix (oneStepRecenter (trajectory omega)) n) =
      ((finitePathList (pathPrefix (trajectory omega) (n + 1))).tail.map
        (fun x ↦ x - trajectory omega 1)) := by
  unfold finitePathList
  rw [List.map_tail, List.map_ofFn]
  simp [pathPrefix, oneStepRecenter, List.ofFn_succ, Function.comp_def]

theorem pathPhasedExternalLocalTime_oneStepRecenter
    (omega : StepPath) (d : Tilings.CheckerDirection)
    (n : ℕ) (x : Point) :
    pathPhasedExternalLocalTime (shiftedCheckerTiling d) .even
        (oneStepRecenter (trajectory omega)) n
        (x - trajectory omega 1) =
      pathPhasedExternalLocalTime (.checker d) .shifted
        (trajectory omega) (n + 1) x := by
  unfold pathPhasedExternalLocalTime phasedExternalLocalTime
  rw [finitePathList_oneStepRecenter]
  have hlist : phasedInput .shifted
      (finitePathList (pathPrefix (trajectory omega) (n + 1))) =
      (finitePathList (pathPrefix (trajectory omega) (n + 1))).tail := by
    cases finitePathList (pathPrefix (trajectory omega) (n + 1)) <;> rfl
  rw [hlist]
  rw [phasedInput_even]
  exact
    (externalLocalTime_map
      (t := (.checker d : DominoTiling))
      (target := shiftedCheckerTiling d)
      (f := fun y ↦ y - trajectory omega 1)
      (fun _ _ h ↦ by
        have h' := congrArg (fun z ↦ z + trajectory omega 1) h
        simpa using h')
      (fun y ↦ tilingPartner_shiftedChecker_sub_general omega d y)
      _ _)

end

end Erdos1165.HLOZSourceEndpointExternalTransport
