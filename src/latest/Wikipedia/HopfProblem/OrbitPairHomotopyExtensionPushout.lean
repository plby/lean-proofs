import Wikipedia.HopfProblem.OrbitPairNativeSimplexHomotopyExtension

/-!
# Homotopy extension survives an actual topological pushout

Compatible jointly continuous families glue by currying into the
compact-open path space. Applying this to an extension across the
attaching map proves homotopy extension for the pushout base inclusion.
The prescribed family remains exact on that inclusion.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.PushoutHomotopy

def familyPaths {A Z : TopCat.{u}} (H : C(I × A, Z)) : A ⟶ TopCat.of C(I, Z) :=
  TopCat.ofHom (H.comp ⟨Prod.swap, continuous_swap⟩).curry

variable {S A B P Z : TopCat.{u}} {f : S ⟶ A} {g : S ⟶ B} {i : A ⟶ P} {j : B ⟶ P}
    (H₁ : C(I × A, Z)) (H₂ : C(I × B, Z))
    (hc : ∀ (t : I) (s : S), H₁ (t, f s) = H₂ (t, g s))

include hc in
theorem familyPaths_compatible : f ≫ familyPaths H₁ = g ≫ familyPaths H₂ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro s
  apply ContinuousMap.ext
  intro t
  exact hc t s

def glueFamily (hP : IsPushout f g i j) : C(I × P, Z) :=
  (hP.desc (familyPaths H₁) (familyPaths H₂) (familyPaths_compatible H₁ H₂ hc)).hom.uncurry.comp
    ⟨Prod.swap, continuous_swap⟩

theorem glueFamily_inl (hP : IsPushout f g i j) (t : I) (a : A) :
    glueFamily H₁ H₂ hc hP (t, i a) = H₁ (t, a) :=
  congrArg (fun F ↦ F a t)
    (hP.inl_desc (familyPaths H₁) (familyPaths H₂) (familyPaths_compatible H₁ H₂ hc))

theorem glueFamily_inr (hP : IsPushout f g i j) (t : I) (b : B) :
    glueFamily H₁ H₂ hc hP (t, j b) = H₂ (t, b) :=
  congrArg (fun F ↦ F b t)
    (hP.inr_desc (familyPaths H₁) (familyPaths H₂) (familyPaths_compatible H₁ H₂ hc))

end Wikipedia.HopfProblem.OrbitPair.PushoutHomotopy

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyExtension

theorem of_isIso {A B : TopCat.{u}} (i : A ⟶ B) [IsIso i] : HasHomotopyExtension i := by
  intro Z F G h0
  let e := asIso i
  let H := G.comp ((ContinuousMap.id I).prodMap e.inv.hom)
  refine ⟨H, ?_, ?_⟩
  · intro b
    exact (h0 (e.inv b)).trans (congrArg F (congrArg (fun m ↦ m b) e.inv_hom_id))
  · intro t a
    exact congrArg (fun q ↦ G (t, q)) (congrArg (fun m ↦ m a) e.hom_inv_id)

theorem comp {A B C : TopCat.{u}} (i : A ⟶ B) (j : B ⟶ C)
    (hi : HasHomotopyExtension i) (hj : HasHomotopyExtension j) :
    HasHomotopyExtension (i ≫ j) := by
  intro Z F G h0
  obtain ⟨H₁, h10, h1i⟩ := hi Z (F.comp j.hom) G h0
  obtain ⟨H₂, h20, h2j⟩ := hj Z F H₁ h10
  exact ⟨H₂, h20, fun t a ↦ (h2j t (i a)).trans (h1i t a)⟩

theorem of_pushout {S A B P : TopCat.{u}} {f : S ⟶ A} {g : S ⟶ B}
    {i : A ⟶ P} {j : B ⟶ P} (hP : IsPushout f g i j)
    (hg : HasHomotopyExtension g) : HasHomotopyExtension i := by
  intro Z F H₁ h0
  let F₂ := F.comp j.hom
  let Hs := H₁.comp ((ContinuousMap.id I).prodMap f.hom)
  have hs0 : ∀ s, Hs (0, s) = F₂ (g s) := fun s ↦
    (h0 (f s)).trans (congrArg F (congrArg (fun m ↦ m s) hP.w))
  obtain ⟨H₂, h20, h2s⟩ := hg Z F₂ Hs hs0
  have hc : ∀ (t : I) (s : S), H₁ (t, f s) = H₂ (t, g s) :=
    fun t s ↦ (h2s t s).symm
  let H := PushoutHomotopy.glueFamily H₁ H₂ hc hP
  refine ⟨H, ?_, ?_⟩
  · intro p
    obtain (⟨a, rfl⟩ | ⟨b, rfl⟩) := Types.eq_or_eq_of_isPushout (hP.map (forget TopCat)) p
    · exact (PushoutHomotopy.glueFamily_inl H₁ H₂ hc hP 0 a).trans (h0 a)
    · exact (PushoutHomotopy.glueFamily_inr H₁ H₂ hc hP 0 b).trans (h20 b)
  · exact PushoutHomotopy.glueFamily_inl H₁ H₂ hc hP

end Wikipedia.HopfProblem.OrbitPair.HomotopyExtension
