import Wikipedia.HopfProblem.HolomorphicMeromorphicSheaf
import Wikipedia.HopfProblem.HolomorphicMeromorphicLocalEquality

/-!
# The genuine meromorphic sheaf has the full local fraction fields as stalks

Every fraction of holomorphic germs has a representative on an actual
open neighborhood whose denominator remains a nonzero germ at every
point. Thus every element of the full fraction field is represented by
a section of the meromorphic sheaf. Conversely, equality of two such
fraction germs gives equality of the original sections on a smaller
neighborhood.

The resulting ring isomorphism uses the actual categorical stalk
colimit. This verifies that local representability does not restrict
the allowed meromorphic germs.
-/

noncomputable section

open Set Filter Topology TopologicalSpace Opposite CategoryTheory Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]

/-- Every element of the full native fraction field is the value of
an actual locally meromorphic section on some original neighborhood. -/
theorem exists_section_through_germ (x : M) (a : Germ I M x) :
    ∃ (U : Opens M) (hx : x ∈ U) (s : Section I M U), s ⟨x, hx⟩ = a := by
  obtain ⟨U, hxU, p, q, hq, ha⟩ := exists_fraction_representative I M x a
  obtain ⟨V, hVU, hxV, hVq⟩ :=
    HolomorphicFunctionSheaf.exists_open_restriction_germs_ne_zero I U q x hxU hq
  let pV := HolomorphicFunctionSheaf.restrictionAlgHom I M hVU p
  let qV := HolomorphicFunctionSheaf.restrictionAlgHom I M hVU q
  have hqV : ∀ y : V, holomorphicGerm I M V y qV ≠ 0 := fun y => hVq y
  refine ⟨V, hxV, ofFraction I M V pV qV hqV, ?_⟩
  exact (fraction_restrict I M hVU p q ⟨x, hxV⟩).trans ha

/-- Equality at a fraction germ gives equality of the original
sections after restriction to one smaller actual neighborhood. -/
theorem exists_neighborhood_eq_of_germ_eq {U V : Opens M}
    (a : Section I M U) (b : Section I M V) (x : M)
    (hxU : x ∈ U) (hxV : x ∈ V) (h : a ⟨x, hxU⟩ = b ⟨x, hxV⟩) :
    ∃ (W : Opens M) (hWU : W ≤ U) (hWV : W ≤ V) (_hxW : x ∈ W),
      ∀ y : W, a (Set.inclusion hWU y) = b (Set.inclusion hWV y) := by
  let T : Opens M := U ⊓ V
  have hTU : T ≤ U := inf_le_left
  have hTV : T ≤ V := inf_le_right
  let aT := restrict I M hTU a
  let bT := restrict I M hTV b
  let S : Set T := {y | aT y = bT y}
  have hSo : IsOpen S := (isClopen_section_eq I M aT bT).isOpen
  let W : Opens M := ⟨Subtype.val '' S, T.isOpen.isOpenMap_subtype_val _ hSo⟩
  have hWT : W ≤ T := by
    rintro y ⟨z, _, rfl⟩
    exact z.property
  refine ⟨W, hWT.trans hTU, hWT.trans hTV, ?_, ?_⟩
  · exact ⟨⟨x, ⟨hxU, hxV⟩⟩, h, rfl⟩
  · rintro ⟨y, ⟨z, hz, rfl⟩⟩
    exact hz

/-- Evaluation of actual local meromorphic sections is compatible
with the genuine open-neighborhood diagram. -/
def stalkCocone (x : M) :
    Cocone ((OpenNhds.inclusion (X := TopCat.of M) x).op ⋙ presheaf I M) where
  pt := CommRingCat.of (Germ I M x)
  ι :=
    { app := fun U => CommRingCat.ofHom (evalRingHom I M U.unop.1 ⟨x, U.unop.2⟩)
      naturality := by
        intro U V i
        rfl }

/-- The canonical comparison out of the actual categorical stalk. -/
def stalkToGermHom (x : M) : (presheaf I M).stalk x ⟶ CommRingCat.of (Germ I M x) :=
  colimit.desc _ (stalkCocone I M x)

def stalkToGerm (x : M) : (presheaf I M).stalk x →+* Germ I M x :=
  (stalkToGermHom I M x).hom

@[simp] theorem stalkToGerm_germ (U : Opens M) (x : M) (hx : x ∈ U)
    (s : Section I M U) :
    stalkToGerm I M x ((presheaf I M).germ U x hx s) = s ⟨x, hx⟩ := by
  exact congrArg (fun h => h s) (colimit.ι_desc (stalkCocone I M x) (op ⟨U, hx⟩))

theorem stalkToGerm_injective (x : M) : Function.Injective (stalkToGerm I M x) := by
  intro a b hab
  obtain ⟨U, hxU, a, rfl⟩ := (presheaf I M).exists_germ_eq a
  obtain ⟨V, hxV, b, rfl⟩ := (presheaf I M).exists_germ_eq b
  change Section I M U at a
  change Section I M V at b
  have he : a ⟨x, hxU⟩ = b ⟨x, hxV⟩ :=
    (stalkToGerm_germ I M U x hxU a).symm.trans
      (hab.trans (stalkToGerm_germ I M V x hxV b))
  obtain ⟨W, hWU, hWV, hxW, hW⟩ :=
    exists_neighborhood_eq_of_germ_eq I M a b x hxU hxV he
  apply (presheaf I M).germ_ext W hxW (homOfLE hWU) (homOfLE hWV)
  apply section_ext
  exact hW

theorem stalkToGerm_surjective (x : M) : Function.Surjective (stalkToGerm I M x) := by
  intro a
  obtain ⟨U, hx, s, hs⟩ := exists_section_through_germ I M x a
  refine ⟨(presheaf I M).germ U x hx s, ?_⟩
  exact (stalkToGerm_germ I M U x hx s).trans hs

/-- The actual meromorphic sheaf stalk is the full fraction field of
the original holomorphic sheaf stalk, with no local representation hypothesis. -/
def stalkEquiv (x : M) : (presheaf I M).stalk x ≃+* Germ I M x :=
  RingEquiv.ofBijective (stalkToGerm I M x)
    ⟨stalkToGerm_injective I M x, stalkToGerm_surjective I M x⟩

@[simp] theorem stalkEquiv_germ (U : Opens M) (x : M) (hx : x ∈ U)
    (s : Section I M U) :
    stalkEquiv I M x ((presheaf I M).germ U x hx s) = s ⟨x, hx⟩ :=
  stalkToGerm_germ I M U x hx s

end Wikipedia.HopfProblem.HolomorphicMeromorphic
