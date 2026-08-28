import Wikipedia.HopfProblem.OrbitPairSubdivisionNativeSupport

/-!
# Unique carrier normal forms for subdivision cells

Restrict the cell parameter to its supporting face, then remove the
degeneracy of the original simplex. Categorical image factorization proves
invariance under every gluing generator. The exact native colimit relation
then gives uniqueness. No realization equivalence or regularity theorem
is assumed in this argument.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.SubdivisionParameters

open SubdivisionSupport

variable {A : SimplexCategory ⥤ SSet.{u}} {k : ℕ} (s : Law A k)
    (faces : ∀ n t, Face s n t) (X : SSet.{u})

def normalize (p : Parameters A X k) : Parameters A X k :=
  let a := faces p.1.1 p.2
  coreParameters A X k a.dim (X.map a.inclusion.op p.1.2) a.point

theorem normalize_eq_face (n : ℕ) (x : X _⦋n⦌) (t : (A.obj ⦋n⦌) _⦋k⦌)
    (a : Face s n t) :
    normalize s faces X ⟨⟨n, x⟩, t⟩ =
      coreParameters A X k a.dim (X.map a.inclusion.op x) a.point := by
  change coreParameters A X k (faces n t).dim (X.map (faces n t).inclusion.op x)
    (faces n t).point = _
  rw [face_eq s (faces n t) a]

theorem normalize_map (m n : ℕ) (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌)
    (t : (A.obj ⦋m⦌) _⦋k⦌) :
    normalize s faces X ⟨⟨m, X.map f.op x⟩, t⟩ =
      normalize s faces X ⟨⟨n, x⟩, (A.map f).app (Opposite.op ⦋k⦌) t⟩ := by
  let a := faces m t
  rw [normalize_eq_face s faces X m (X.map f.op x) t a,
    normalize_eq_face s faces X n x ((A.map f).app (Opposite.op ⦋k⦌) t) (imageFace s a f)]
  have hs : X.map a.inclusion.op (X.map f.op x) =
      X.map (factorThruImage (a.inclusion ≫ f)).op
        (X.map (image.ι (a.inclusion ≫ f)).op x) := by
    calc
      _ = X.map (a.inclusion ≫ f).op x :=
        (Functor.map_comp_apply X f.op a.inclusion.op x).symm
      _ = X.map (factorThruImage (a.inclusion ≫ f) ≫ image.ι (a.inclusion ≫ f)).op x :=
        congrArg (fun g : ⦋a.dim⦌ ⟶ ⦋n⦌ ↦ X.map g.op x) (image.fac (a.inclusion ≫ f)).symm
      _ = _ := Functor.map_comp_apply X (image.ι (a.inclusion ≫ f)).op
        (factorThruImage (a.inclusion ≫ f)).op x
  change coreParameters A X k a.dim (X.map a.inclusion.op (X.map f.op x)) a.point =
    coreParameters A X k (image (a.inclusion ≫ f)).len
      (X.map (image.ι (a.inclusion ≫ f)).op x)
      ((A.map (factorThruImage (a.inclusion ≫ f))).app (Opposite.op ⦋k⦌) a.point)
  rw [hs]
  exact coreParameters_epi A X k (factorThruImage (a.inclusion ≫ f))
    (X.map (image.ι (a.inclusion ≫ f)).op x) a.point

theorem normalize_glue {a b : Parameters A X k} (h : Glue A X k a b) :
    normalize s faces X a = normalize s faces X b := by
  cases h with
  | of_map m n f x t => exact normalize_map s faces X m n f x t

theorem normalize_eqvGen {a b : Parameters A X k} (h : Relation.EqvGen (Glue A X k) a b) :
    normalize s faces X a = normalize s faces X b := by
  induction h with
  | rel a b h => exact normalize_glue s faces X h
  | refl => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc

def IsNormal (p : Parameters A X k) : Prop :=
  p.1.2 ∈ X.nonDegenerate p.1.1 ∧ Full s p.2

theorem normalize_isNormal (p : Parameters A X k) : IsNormal s X (normalize s faces X p) := by
  let a := faces p.1.1 p.2
  let c := RealizationSimplex.core X a.dim (X.map a.inclusion.op p.1.2)
  refine ⟨c.simplex.property, ?_⟩
  exact full_map_epi s c.collapse a.point a.full

theorem normalize_fixed (p : Parameters A X k) (hp : IsNormal s X p) :
    normalize s faces X p = p := by
  rcases p with ⟨⟨n, x⟩, t⟩
  obtain ⟨hx, ht⟩ := hp
  rw [normalize_eq_face s faces X n x t (fullFace s t ht)]
  change coreParameters A X k n (X.map (𝟙 ⦋n⦌).op x) t = _
  have hid : X.map (𝟙 ⦋n⦌).op x = x := by simp
  rw [hid]
  exact coreParameters_nonDegenerate A X k n ⟨x, hx⟩ t

variable (L : SSet.{u} ⥤ SSet.{u}) (α : A ⟶ SSet.stdSimplex.{u} ⋙ L)

theorem normalize_projection (p : Parameters A X k) :
    projection A L α X k (normalize s faces X p) = projection A L α X k p := by
  rcases p with ⟨⟨n, x⟩, t⟩
  let a := faces n t
  rw [normalize_eq_face s faces X n x t a, coreParameters_projection]
  have h := glue_projection_eq A L α X k (Glue.of_map a.dim n a.inclusion x a.point)
  rw [a.map_point] at h
  exact h

include faces in
theorem normal_injective [SSet.stdSimplex.{u}.HasPointwiseLeftKanExtension A]
    [L.IsLeftKanExtension α] {a b : Parameters A X k}
    (ha : IsNormal s X a) (hb : IsNormal s X b)
    (h : projection A L α X k a = projection A L α X k b) : a = b := by
  have hn := normalize_eqvGen s faces X ((projection_eq_iff A L α X k a b).mp h)
  rwa [normalize_fixed s faces X a ha, normalize_fixed s faces X b hb] at hn

include faces in
theorem existsUnique_normal [SSet.stdSimplex.{u}.HasPointwiseLeftKanExtension A]
    [L.IsLeftKanExtension α] (z : (L.obj X) _⦋k⦌) :
    ∃! p : {p : Parameters A X k // IsNormal s X p}, projection A L α X k p.val = z := by
  obtain ⟨a, rfl⟩ := projection_surjective A L α X k z
  refine ⟨⟨normalize s faces X a, normalize_isNormal s faces X a⟩,
    normalize_projection s faces X L α a, ?_⟩
  intro b hb
  apply Subtype.ext
  exact normal_injective s faces X L α b.property (normalize_isNormal s faces X a)
    (hb.trans (normalize_projection s faces X L α a).symm)

end Wikipedia.HopfProblem.OrbitPair.SubdivisionParameters
