import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionMaps
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionSheafify

/-!
# The genuine kernel of the cocycle extension presheaf

Degree-zero compatible local data glue uniquely to a section of the
original sheaf. Sheaf separatedness also makes the inclusion injective.
Consequently the actual presheaf complex is exact at its middle term,
without a cocycle solution or a sheaf-gluing hypothesis beyond `F`.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U)

private theorem restrictedCover_covers (hU : ∀ x : X, ∃ i : ι, x ∈ U i)
    (V : Opens X) : V ≤ ⨆ i : ι, V ⊓ U i := by
  intro x hx
  obtain ⟨i, hi⟩ := hU x
  exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩

/-- The original sheaf's separatedness makes inclusion injective on
every actual open set. -/
theorem includeHom_injective (hU : ∀ x : X, ∃ i : ι, x ∈ U i)
    (V : Opens X) : Function.Injective (includeHom c V) := by
  intro a b hab
  apply F.eq_of_locally_eq' (fun i : ι => V ⊓ U i) V
    (fun _ => homOfLE inf_le_left) (restrictedCover_covers hU V)
  intro i
  exact congrArg (coordinateHom c V i) hab

/-- A degree-zero family satisfies the actual pairwise-intersection
compatibility required by the sheaf gluing theorem. -/
theorem coordinate_compatible_of_degree_zero (V : Opens X)
    (s : ExtensionSection c V) (hs : degreeHom c V s = 0) :
    TopCat.Presheaf.IsCompatible F.obj (fun i : ι => V ⊓ U i) s.1.2 := by
  have hdegree : s.1.1.down = 0 := congrArg ULift.down hs
  intro i j
  change res F inf_le_left (s.1.2 i) = res F inf_le_right (s.1.2 j)
  apply sub_eq_zero.mp
  have hcommon : (V ⊓ U i) ⊓ (V ⊓ U j) ≤ V ⊓ (U i ⊓ U j) :=
    le_inf (inf_le_left.trans inf_le_left)
      (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
  have h := congrArg (res F hcommon) (s.2 i j)
  simpa only [map_sub, map_zsmul, hdegree, zero_zsmul, map_zero, res_trans] using h

/-- Every actual degree-zero extension section is the inclusion of a
section obtained by genuine gluing in the original sheaf. -/
theorem exists_includeHom_of_degree_zero (hU : ∀ x : X, ∃ i : ι, x ∈ U i)
    (V : Opens X) (s : ExtensionSection c V) (hs : degreeHom c V s = 0) :
    ∃ a : Section F V, includeHom c V a = s := by
  obtain ⟨a, ha, _⟩ := F.existsUnique_gluing' (fun i : ι => V ⊓ U i) V
    (fun _ => homOfLE inf_le_left) (restrictedCover_covers hU V) s.1.2
    (coordinate_compatible_of_degree_zero c V s hs)
  refine ⟨a, ?_⟩
  apply extensionSection_ext
  · exact hs.symm
  · intro i
    exact ha i

/-- The sectionwise image of inclusion is exactly the actual kernel
of the degree projection. -/
theorem includeHom_degreeHom_exact (hU : ∀ x : X, ∃ i : ι, x ∈ U i)
    (V : Opens X) : Function.Exact (includeHom c V) (degreeHom c V) := by
  intro s
  constructor
  · exact exists_includeHom_of_degree_zero c hU V s
  · rintro ⟨a, rfl⟩
    exact includeHom_degree c V a

/-- The first arrow is monic in the actual presheaf category. -/
theorem inclusionPre_mono (hU : ∀ x : X, ∃ i : ι, x ∈ U i) :
    Mono (inclusionPre c) := by
  apply +allowSynthFailures NatTrans.mono_of_mono_app
  intro V
  exact ConcreteCategory.mono_of_injective _ (includeHom_injective c hU V.unop)

/-- Genuine componentwise kernel exactness gives exactness in the
actual category of additive presheaves. -/
theorem presheafComplex_exact (hU : ∀ x : X, ∃ i : ι, x ∈ U i) :
    (presheafComplex c).Exact :=
  presheafExact_of_app_exact (presheafComplex c)
    (fun V => includeHom_degreeHom_exact c hU V.unop)

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
