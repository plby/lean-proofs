import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Actual local lifts in short exact sequences of sheaves

The statements here concern actual sections of sheaves of abelian groups.
The local lifts come from epimorphy in the sheaf category, not from an
assumption of surjectivity on every open set.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}}

/-- The first arrow of a short exact sequence is injective on every open set. -/
theorem section_f_injective
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
    (hS : S.ShortExact) (U : Opens X) :
    Function.Injective (S.f.hom.app (op U)) := by
  let : Mono S.f := hS.mono_f
  have hmono : Mono S.f.hom :=
    (TopCat.Sheaf.forget AddCommGrpCat.{0} X).map_mono S.f
  exact (AddCommGrpCat.mono_iff_injective _).mp
    ((NatTrans.mono_iff_mono_app S.f.hom).mp hmono (op U))

/-- A section in the kernel of the second arrow has an actual preimage under
the first arrow, on the same open set. -/
theorem section_kernel_lift
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
    (hS : S.ShortExact) {U : Opens X} (t : S.X₂.obj.obj (op U))
    (ht : S.g.hom.app (op U) t = 0) :
    ∃ u : S.X₁.obj.obj (op U), S.f.hom.app (op U) u = t :=
  TopCat.Sheaf.sections_exact_of_left_exact hS.exact hS.mono_f t ht

/-- The two arrows of a short complex compose to zero on actual sections. -/
theorem section_comp_eq_zero
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X))
    (U : Opens X) (s : S.X₁.obj.obj (op U)) :
    S.g.hom.app (op U) (S.f.hom.app (op U) s) = 0 := by
  have h := congrArg (fun f => f.hom.app (op U)) S.zero
  have hs := ConcreteCategory.congr_hom h s
  exact hs

/-- A sheaf epimorphism admits actual lifts of each global section on a
point-indexed open cover. -/
theorem exists_local_lifts {E G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (π : E ⟶ G) [Epi π] (s : G.obj.obj (op (⊤ : Opens X))) :
    ∃ (U : X → Opens X) (t : ∀ x, E.obj.obj (op (U x))),
      (∀ x, x ∈ U x) ∧
      ∀ x, π.hom.app (op (U x)) (t x) = G.obj.map (homOfLE le_top).op s := by
  classical
  have hloc : TopCat.Presheaf.IsLocallySurjective π.hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi π).mpr inferInstance
  have hpoint (x : X) :
      ∃ (U : Opens X) (t : E.obj.obj (op U)),
        x ∈ U ∧ π.hom.app (op U) t = G.obj.map (homOfLE le_top).op s := by
    obtain ⟨U, hU, ⟨t, ht⟩, hx⟩ :=
      (TopCat.Presheaf.isLocallySurjective_iff π.hom).mp hloc
        (⊤ : Opens X) s x (Set.mem_univ x)
    exact ⟨U, t, hx, ht⟩
  choose U t hmem hlift using hpoint
  exact ⟨U, t, hmem, hlift⟩

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
