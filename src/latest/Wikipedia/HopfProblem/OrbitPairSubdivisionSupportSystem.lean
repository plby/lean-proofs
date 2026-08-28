import Wikipedia.HopfProblem.OrbitPairSubdivisionFaceSupport

/-!
# Unique supporting faces from vertex-support laws

The abstract laws in this file are verified for both native subdivision
models in `OrbitPairSubdivisionNativeSupport`. They express the actual
image of the vertex support and injectivity along a face inclusion.
These laws imply uniqueness of a fully supported face parameterization.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.SubdivisionSupport

variable (A : SimplexCategory ⥤ SSet.{u}) (k : ℕ)

structure Law where
  support : ∀ n, (A.obj ⦋n⦌) _⦋k⦌ → Set (Fin (n + 1))
  support_map : ∀ {m n} (f : ⦋m⦌ ⟶ ⦋n⦌) (t : (A.obj ⦋m⦌) _⦋k⦌),
    support n ((A.map f).app (Opposite.op ⦋k⦌) t) = f.toOrderHom '' support m t
  map_injective : ∀ {m n} (f : ⦋m⦌ ⟶ ⦋n⦌) [Mono f],
    Function.Injective ((A.map f).app (Opposite.op ⦋k⦌))

variable {A k} (s : Law A k)

def Full {n : ℕ} (t : (A.obj ⦋n⦌) _⦋k⦌) : Prop := s.support n t = Set.univ

theorem support_map_full {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (t : (A.obj ⦋m⦌) _⦋k⦌) (ht : Full s t) :
    s.support n ((A.map f).app (Opposite.op ⦋k⦌) t) = Set.range f.toOrderHom := by
  rw [s.support_map, ht, Set.image_univ]

theorem full_map_epi {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) [Epi f]
    (t : (A.obj ⦋m⦌) _⦋k⦌) (ht : Full s t) :
    Full s ((A.map f).app (Opposite.op ⦋k⦌) t) := by
  change s.support n _ = Set.univ
  rw [support_map_full s f t ht]
  exact Set.range_eq_univ.mpr (SimplexCategory.epi_iff_surjective.mp inferInstance)

structure Face (n : ℕ) (t : (A.obj ⦋n⦌) _⦋k⦌) where
  dim : ℕ
  inclusion : ⦋dim⦌ ⟶ ⦋n⦌
  mono_inclusion : Mono inclusion
  point : (A.obj ⦋dim⦌) _⦋k⦌
  full : Full s point
  map_point : (A.map inclusion).app (Opposite.op ⦋k⦌) point = t

attribute [instance] Face.mono_inclusion

theorem face_eq {n : ℕ} {t : (A.obj ⦋n⦌) _⦋k⦌} (a b : Face s n t) : a = b := by
  cases a with
  | mk m f hf x hx hfx =>
    cases b with
    | mk d g hg y hy hgy =>
      let : Mono f := hf
      let : Mono g := hg
      have hrange : Set.range f.toOrderHom = Set.range g.toOrderHom := by
        rw [← support_map_full s f x hx, ← support_map_full s g y hy, hfx, hgy]
      have hdim : m = d := SimplexSupport.mono_dim_eq_of_range_eq f g hrange
      subst d
      have hfg : f = g := SimplexSupport.mono_eq_of_range_eq f g hrange
      subst g
      have hxy : x = y := s.map_injective f (hfx.trans hgy.symm)
      subst y
      rfl

instance faceSubsingleton (n : ℕ) (t : (A.obj ⦋n⦌) _⦋k⦌) : Subsingleton (Face s n t) :=
  ⟨face_eq s⟩

def fullFace {n : ℕ} (t : (A.obj ⦋n⦌) _⦋k⦌) (ht : Full s t) : Face s n t where
  dim := n
  inclusion := 𝟙 _
  mono_inclusion := inferInstance
  point := t
  full := ht
  map_point := congrArg (fun f : A.obj ⦋n⦌ ⟶ A.obj ⦋n⦌ ↦
    f.app (Opposite.op ⦋k⦌) t) (A.map_id ⦋n⦌)

def imageFace {m n : ℕ} {t : (A.obj ⦋m⦌) _⦋k⦌} (a : Face s m t)
    (f : ⦋m⦌ ⟶ ⦋n⦌) : Face s n ((A.map f).app (Opposite.op ⦋k⦌) t) where
  dim := (image (a.inclusion ≫ f)).len
  inclusion := image.ι (a.inclusion ≫ f)
  mono_inclusion := inferInstance
  point := (A.map (factorThruImage (a.inclusion ≫ f))).app (Opposite.op ⦋k⦌) a.point
  full := full_map_epi s (factorThruImage (a.inclusion ≫ f)) a.point a.full
  map_point := by
    have hfac : A.map (factorThruImage (a.inclusion ≫ f)) ≫
        A.map (image.ι (a.inclusion ≫ f)) = A.map a.inclusion ≫ A.map f := by
      rw [← A.map_comp, image.fac, A.map_comp]
    have h := congrArg (fun g ↦ g.app (Opposite.op ⦋k⦌) a.point) hfac
    change (A.map (image.ι (a.inclusion ≫ f))).app (Opposite.op ⦋k⦌)
      ((A.map (factorThruImage (a.inclusion ≫ f))).app (Opposite.op ⦋k⦌) a.point) =
        (A.map f).app (Opposite.op ⦋k⦌) ((A.map a.inclusion).app (Opposite.op ⦋k⦌) a.point) at h
    exact h.trans (congrArg ((A.map f).app (Opposite.op ⦋k⦌)) a.map_point)

end Wikipedia.HopfProblem.OrbitPair.SubdivisionSupport
