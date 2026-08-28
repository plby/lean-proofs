import Wikipedia.HopfProblem.OrbitPairHomotopyExtensionPushout

/-!+# A quotient attachment along the locus of nontrivial fibers

If a quotient map is injective away from the inverse image of a specified
subspace, that inverse image is an attaching domain. The literal square
is a topological pushout. Homotopy extension therefore descends from the
attaching-domain inclusion to the original subspace inclusion.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Set Topology

namespace NoExoticSixSphere.QuotientAttachment

variable {X Q : TopCat.{u}} (q : X ⟶ Q) (A : Set Q)

def boundaryMap : TopCat.of (q ⁻¹' A) ⟶ TopCat.of A :=
  TopCat.ofHom ⟨fun x ↦ ⟨q x.val, x.property⟩,
    (q.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

def boundaryInclusion : TopCat.of (q ⁻¹' A) ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def inclusion : TopCat.of A ⟶ Q :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem square : boundaryMap q A ≫ inclusion A = boundaryInclusion q A ≫ q := rfl

variable (hq : IsQuotientMap q)
    (hf : ∀ x y, q x = q y → q x ∈ A ∨ x = y)
    {Z : TopCat.{u}} (F : TopCat.of A ⟶ Z) (G : X ⟶ Z)
    (hFG : boundaryMap q A ≫ F = boundaryInclusion q A ≫ G)

include hf hFG in
theorem constant_on_fibers {x y : X} (h : q x = q y) : G x = G y := by
  rcases hf x y h with hx | hxy
  · have hy : q y ∈ A := h ▸ hx
    have hFx : F ⟨q x, hx⟩ = G x := congrArg (fun m ↦ m ⟨x, hx⟩) hFG
    have hFy : F ⟨q y, hy⟩ = G y := congrArg (fun m ↦ m ⟨y, hy⟩) hFG
    exact hFx.symm.trans ((congrArg F (Subtype.ext h)).trans hFy)
  · exact congrArg G hxy

def glueFunction (a : Q) : Z := G (hq.surjective a).choose

include hf hFG in
theorem glueFunction_map (x : X) : glueFunction q hq G (q x) = G x :=
  constant_on_fibers q A hf F G hFG (hq.surjective (q x)).choose_spec

include hf hFG in
theorem continuous_glueFunction : Continuous (glueFunction q hq G) := by
  apply hq.continuous_iff.mpr
  exact G.hom.continuous.congr (fun x ↦ (glueFunction_map q A hq hf F G hFG x).symm)

def glue : Q ⟶ Z :=
  TopCat.ofHom ⟨glueFunction q hq G, continuous_glueFunction q A hq hf F G hFG⟩

theorem map_glue : q ≫ glue q A hq hf F G hFG = G := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  exact glueFunction_map q A hq hf F G hFG

theorem inclusion_glue : inclusion A ≫ glue q A hq hf F G hFG = F := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  obtain ⟨x, hx⟩ := hq.surjective a.val
  have hxa : q x ∈ A := hx ▸ a.property
  change glueFunction q hq G a.val = F a
  rw [← hx, glueFunction_map q A hq hf F G hFG]
  have hF : F ⟨q x, hxa⟩ = G x := congrArg (fun m ↦ m ⟨x, hxa⟩) hFG
  exact hF.symm.trans (congrArg F (Subtype.ext hx))

include hq hf in
theorem isPushout : IsPushout (boundaryMap q A) (boundaryInclusion q A) (inclusion A) q := by
  apply IsPushout.mk' (square q A)
  · intro Z φ ψ _ hqeq
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    obtain ⟨x, rfl⟩ := hq.surjective a
    exact congrArg (fun m ↦ m x) hqeq
  · intro Z F G hFG
    exact ⟨glue q A hq hf F G hFG, inclusion_glue q A hq hf F G hFG,
      map_glue q A hq hf F G hFG⟩

include hq hf in
theorem hasHomotopyExtension
    (h : Wikipedia.HopfProblem.OrbitPair.HomotopyExtension.HasHomotopyExtension
      (boundaryInclusion q A)) :
    Wikipedia.HopfProblem.OrbitPair.HomotopyExtension.HasHomotopyExtension (inclusion A) :=
  Wikipedia.HopfProblem.OrbitPair.HomotopyExtension.of_pushout (isPushout q A hq hf) h

end NoExoticSixSphere.QuotientAttachment
