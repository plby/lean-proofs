/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.ProfileConditionalTailUpper

/-!
# Inverse to the exact profile prefix/future split

`ProfileWeightUpper` already proves injectivity of the split used by the
Gaussian argument.  Buffered-coordinate summation also needs its literal
inverse, so that an arbitrary constrained future can be inserted after a
fixed prefix without creating an artificial prefix multiplicity.
-/

namespace Erdos1165.ProfilePrefixFutureEquiv

open AppendixFirstMoment ProfileListExponent ProfileWeightUpper

noncomputable section

/-- Join a profile through `start` to its values at scales
`start+1,...,n`. -/
def extendProfile {n start : ℕ} (hstart : 2 ≤ start)
    (hstartn : start ≤ n) (pref : Profile start)
    (future : Fin (n - start) → ℕ) : Profile n :=
  fun i ↦ if hi : i.1 < start - 1 then
    pref ⟨i.1, hi⟩
  else
    future ⟨i.1 - (start - 1), by have := i.2; omega⟩

@[simp] theorem profilePrefix_extendProfile
    {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (pref : Profile start) (future : Fin (n - start) → ℕ) :
    profilePrefix hstart hstartn
        (extendProfile hstart hstartn pref future) = pref := by
  funext i
  simp [profilePrefix, extendProfile, i.2]

@[simp] theorem profileFuture_extendProfile
    {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (pref : Profile start) (future : Fin (n - start) → ℕ) :
    profileFuture hstart hstartn
        (extendProfile hstart hstartn pref future) = future := by
  funext i
  unfold profileFuture extendProfile
  rw [dif_neg]
  · congr 1
    apply Fin.ext
    dsimp
    omega
  · exact Nat.not_lt.mpr (Nat.le_add_right (start - 1) i.1)

@[simp] theorem extendProfile_profilePrefix_profileFuture
    {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (m : Profile n) :
    extendProfile hstart hstartn (profilePrefix hstart hstartn m)
        (profileFuture hstart hstartn m) = m := by
  apply profileSplit_injective hstart hstartn
  apply Prod.ext
  · exact profilePrefix_extendProfile hstart hstartn _ _
  · exact profileFuture_extendProfile hstart hstartn _ _

/-- The prefix/future decomposition as an actual equivalence. -/
def profileSplitEquiv {n start : ℕ} (hstart : 2 ≤ start)
    (hstartn : start ≤ n) :
    Profile n ≃ Profile start × (Fin (n - start) → ℕ) where
  toFun m := (profilePrefix hstart hstartn m,
    profileFuture hstart hstartn m)
  invFun p := extendProfile hstart hstartn p.1 p.2
  left_inv := extendProfile_profilePrefix_profileFuture hstart hstartn
  right_inv := by
    intro p
    apply Prod.ext
    · exact profilePrefix_extendProfile hstart hstartn p.1 p.2
    · exact profileFuture_extendProfile hstart hstartn p.1 p.2

theorem extendProfile_mem_constrainedProfiles_iff
    {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    {delta : ℝ} {pref : Profile start}
    {future : Fin (n - start) → ℕ} :
    extendProfile hstart hstartn pref future ∈ constrainedProfiles n delta ↔
      pref ∈ constrainedProfiles start delta ∧
        future ∈ Fintype.piFinset
          (fun i : Fin (n - start) ↦
            allowedValues delta (start + 1 + i.1)) := by
  constructor
  · intro hm
    have hpref := profilePrefix_mem hstart hstartn hm
    have hfuture := profileFuture_mem hstart hstartn hm
    simpa using And.intro hpref hfuture
  · rintro ⟨hpref, hfuture⟩
    rw [mem_constrainedProfiles] at hpref ⊢
    rw [Fintype.mem_piFinset] at hfuture
    intro i
    by_cases hi : i.1 < start - 1
    · let j : Fin (start - 1) := ⟨i.1, hi⟩
      have hj := hpref j
      simpa [extendProfile, hi, scaleIndex, j] using hj
    · let j : Fin (n - start) :=
        ⟨i.1 - (start - 1), by have := i.2; omega⟩
      have hj := (mem_allowedValues.mp (hfuture j))
      have hscale : scaleIndex i = start + 1 + j.1 := by
        unfold scaleIndex
        dsimp only [j]
        omega
      rw [hscale]
      simpa [extendProfile, hi, j]

theorem transitionSegmentProduct_extendProfile
    {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (pref : Profile start) (future : Fin (n - start) → ℕ) :
    transitionSegmentProduct start (n - start)
        (profileAtScale (extendProfile hstart hstartn pref future)) =
      transitionSegmentProduct start (n - start)
        (profileAtScale (extendProfile hstart hstartn pref future)) := rfl

/-- The fixed-prefix tail sum can equivalently be written as the finite sum
over all allowed future tuples. -/
theorem constrainedProfileTailWeight_eq_sum_future
    {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (pref : Profile start) (delta : ℝ)
    (hpref : pref ∈ constrainedProfiles start delta) :
    ProfileConditionalTailUpper.constrainedProfileTailWeight
        n start hstart hstartn pref delta =
      ∑ future ∈ Fintype.piFinset
          (fun i : Fin (n - start) ↦
            allowedValues delta (start + 1 + i.1)),
        transitionSegmentProduct start (n - start)
          (profileAtScale
            (extendProfile hstart hstartn pref future)) := by
  classical
  let F := Fintype.piFinset
    (fun i : Fin (n - start) ↦
      allowedValues delta (start + 1 + i.1))
  let e : (Fin (n - start) → ℕ) → Profile n :=
    extendProfile hstart hstartn pref
  unfold ProfileConditionalTailUpper.constrainedProfileTailWeight
  let G := (constrainedProfiles n delta).filter
    (fun m ↦ profilePrefix hstart hstartn m = pref)
  have himage : F.image e = G := by
    ext m
    simp only [Finset.mem_image, G, Finset.mem_filter]
    constructor
    · rintro ⟨future, hfuture, rfl⟩
      exact ⟨(extendProfile_mem_constrainedProfiles_iff
        hstart hstartn).2 ⟨hpref, hfuture⟩,
        profilePrefix_extendProfile hstart hstartn pref future⟩
    · rintro ⟨hm, hprefix⟩
      refine ⟨profileFuture hstart hstartn m, ?_, ?_⟩
      · exact profileFuture_mem hstart hstartn hm
      · dsimp only [e]
        rw [← hprefix]
        exact extendProfile_profilePrefix_profileFuture hstart hstartn m
  change (∑ m ∈ G,
      transitionSegmentProduct start (n - start) (profileAtScale m)) =
    ∑ future ∈ F,
      transitionSegmentProduct start (n - start)
        (profileAtScale (e future))
  rw [← himage, Finset.sum_image]
  intro left _hleft right _hright heq
  have := congrArg (profileFuture hstart hstartn) heq
  simpa only [e, profileFuture_extendProfile] using this

end

end Erdos1165.ProfilePrefixFutureEquiv
