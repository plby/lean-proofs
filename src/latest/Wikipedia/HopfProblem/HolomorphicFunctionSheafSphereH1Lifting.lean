import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1LiftingCocycle

/-!
# Čech solvability gives genuine global lifting

Start with a short exact sequence of actual additive sheaves and a
global section of its quotient. Epimorphy gives local lifts, exactness
gives their overlap cocycle, and a solution of that cocycle corrects
the lifts to a compatible family. The actual sheaf gluing property
then gives a global lift. No pointwise-surjectivity or cohomology
comparison theorem is assumed.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}}

private theorem corrected_eq_of_difference {A : Type*} [AddCommGroup A]
    {a b c d : A} (h : c - d = a - b) : a - c = b - d := by
  apply sub_eq_zero.mp
  calc
    (a - c) - (b - d) = (a - b) - (c - d) := by abel
    _ = 0 := by rw [h, sub_self]

/-- Solvability of actual one-cocycles makes global sections surjective
on the last arrow of every actual short exact sequence with that kernel. -/
theorem globalSections_surjective_of_shortExact
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)} (hS : S.ShortExact)
    (hvanish : CechOneVanishing S.X₁) :
    Function.Surjective (S.g.hom.app (op (⊤ : Opens X))) := by
  classical
  intro s
  let : Epi S.g := hS.epi_g
  obtain ⟨U, t, hU, ht⟩ := exists_local_lifts S.g s
  have hcover : ∀ x : X, ∃ i : X, x ∈ U i := fun x => ⟨x, hU x⟩
  have htop : (⊤ : Opens X) ≤ iSup U := by
    intro x _
    exact Opens.mem_iSup.mpr (hcover x)
  have htres : ∀ i : X, S.g.hom.app (op (U i)) (t i) = res S.X₃ le_top s := ht
  obtain ⟨c, hc⟩ := exists_difference_cocycle hS U s t htres
  obtain ⟨b, hb⟩ := hvanish X U hcover c
  let t' : ∀ i : X, Section S.X₂ (U i) :=
    fun i => t i - S.f.hom.app (op (U i)) (b i)
  have ht' (i : X) : S.g.hom.app (op (U i)) (t' i) = res S.X₃ le_top s := by
    change S.g.hom.app (op (U i))
      (t i - S.f.hom.app (op (U i)) (b i)) = _
    rw [map_sub, section_comp_eq_zero, sub_zero, htres i]
  have hcompatible : TopCat.Presheaf.IsCompatible S.X₂.obj U t' := by
    intro i j
    change res S.X₂ inf_le_left (t' i) = res S.X₂ inf_le_right (t' j)
    dsimp only [t']
    rw [map_sub, map_sub, res_map, res_map]
    apply corrected_eq_of_difference
    have h := congrArg (fun z => S.f.hom.app (op (U i ⊓ U j)) z) (hb i j)
    simpa only [map_sub, hc, overlapDifference] using h
  obtain ⟨q, hq, _⟩ := S.X₂.existsUnique_gluing' U ⊤
    (fun _ => homOfLE le_top) htop t' hcompatible
  refine ⟨q, ?_⟩
  apply S.X₃.eq_of_locally_eq' U ⊤ (fun _ => homOfLE le_top) htop
  intro i
  change res S.X₃ le_top (S.g.hom.app (op ⊤) q) = res S.X₃ le_top s
  calc
    res S.X₃ le_top (S.g.hom.app (op ⊤) q) =
        S.g.hom.app (op (U i)) (res S.X₂ le_top q) := res_map S.g le_top q
    _ = S.g.hom.app (op (U i)) (t' i) :=
      congrArg (fun z => S.g.hom.app (op (U i)) z) (hq i)
    _ = res S.X₃ le_top s := ht' i

/-- The raw global-lifting property used in the independent comparison
with genuine `Ext¹` sheaf cohomology. -/
theorem globalLifting_of_cechOneVanishing
    {F : TopCat.Sheaf AddCommGrpCat.{0} X} (hF : CechOneVanishing F) :
    ∀ {G Q : TopCat.Sheaf AddCommGrpCat.{0} X}
      (ι : F ⟶ G) (π : G ⟶ Q) (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact →
        Function.Surjective (π.hom.app (op (⊤ : Opens X))) := by
  intro G Q ι π h hS
  exact globalSections_surjective_of_shortExact hS hF

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
