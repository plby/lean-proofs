import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLocallyFineSummationBasic

/-!
# Genuine locally finite sums of actual sheaf sections

The finite neighborhood sums of a supported locally finite family glue
to an actual section of the given sheaf.  On every open set meeting only
a specified finite list of supports, its restriction is the literal sum
over that list.  This property determines the section uniquely and does
not assume compactness, countability, or a sum operation on the sheaf.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped BigOperators

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.SupportedSectionFamily

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  {U : Opens X} {ι : Type} (a : SupportedSectionFamily F U ι)

/-- A locally finite sum has its literal finite-sum restriction wherever
only those finitely many supports can occur. -/
def IsSum (b : Section F U) : Prop :=
  ∀ (V : Opens X) (hVU : V ≤ U) (s : Finset ι),
    (∀ i ∉ s, Disjoint (V : Set X) (a.support i)) →
      res F hVU b = res F hVU (s.sum a.value)

/-- Any gluing of the actual finite neighborhood sums has the finite-sum
identity on every other admissible open subset. -/
theorem isSum_of_patch_gluing (b : Section F U)
    (hb : ∀ x : U, res F (a.patch_le x) b = a.patchValue x) : a.IsSum b := by
  intro V hVU s hs
  apply section_ext_of_local F
  intro x hx
  let p : U := ⟨x, hVU hx⟩
  let W : Opens X := V ⊓ a.patch p
  refine ⟨W, inf_le_left, ⟨hx, a.mem_patch p⟩, ?_⟩
  have hp := congrArg (res F (show W ≤ a.patch p from inf_le_right)) (hb p)
  simp only [patchValue, res_trans] at hp
  simp only [res_trans]
  refine hp.trans ?_
  simp only [map_sum]
  apply finiteSum_eq_of_vanishing
  · intro i hi
    exact a.res_zero_of_disjoint (inf_le_right.trans (a.patch_le p)) i
      ((a.patch_avoids p i hi).mono_left (fun _ h => h.2))
  · intro i hi
    exact a.res_zero_of_disjoint (inf_le_left.trans hVU) i
      ((hs i hi).mono_left (fun _ h => h.1))

/-- The actual sheaf gluing axiom constructs a locally finite sum with
the required literal restriction identities. -/
theorem exists_sum : ∃ b : Section F U, a.IsSum b := by
  obtain ⟨b, hb, _⟩ := F.existsUnique_gluing' a.patch U
    (fun x => homOfLE (a.patch_le x)) a.patch_cover a.patchValue a.patchValue_compatible
  exact ⟨b, a.isSum_of_patch_gluing b hb⟩

/-- The genuine section obtained by gluing the finite local sums. -/
def sum : Section F U := a.exists_sum.choose

/-- The glued section satisfies the actual local finite-sum identity. -/
theorem sum_spec : a.IsSum a.sum := a.exists_sum.choose_spec

/-- The actual restriction of the sum is the sum of the actual restrictions. -/
theorem sum_restrict (V : Opens X) (hVU : V ≤ U) (s : Finset ι)
    (hs : ∀ i ∉ s, Disjoint (V : Set X) (a.support i)) :
    res F hVU a.sum = s.sum (fun i => res F hVU (a.value i)) := by
  simpa only [map_sum] using a.sum_spec V hVU s hs

/-- In particular, the global sum restricts to each of the original
literal finite neighborhood sums. -/
theorem sum_patch (x : U) : res F (a.patch_le x) a.sum = a.patchValue x :=
  a.sum_spec (a.patch x) (a.patch_le x) (a.neighborhood x).indices (a.patch_avoids x)

/-- The locally finite sum is independent of the chosen neighborhood
data because its actual finite-sum restriction property determines it. -/
theorem sum_unique {b : Section F U} (hb : a.IsSum b) : b = a.sum := by
  apply section_ext_of_local F
  intro x hx
  let p : U := ⟨x, hx⟩
  refine ⟨a.patch p, a.patch_le p, a.mem_patch p, ?_⟩
  exact (hb (a.patch p) (a.patch_le p) (a.neighborhood p).indices (a.patch_avoids p)).trans
    (a.sum_spec (a.patch p) (a.patch_le p) (a.neighborhood p).indices (a.patch_avoids p)).symm

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.SupportedSectionFamily
