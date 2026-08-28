import Wikipedia.HopfProblem.OrbitPairRealizationNondegenerateCore
import Wikipedia.HopfProblem.OrbitPairSimplexSupportImage

/-!
# Normal forms for points of native geometric realization

First restrict to the unique positive supporting face, then remove the
unique simplicial degeneracy. Categorical image factorization shows that
this normal form is invariant under every generating realization relation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.RealizationSimplex

open FirstHurewicz

variable (S : SSet)

def normalize (p : Parameters S) : Parameters S :=
  let a := SimplexSupport.face p.1.1 p.2
  coreParameters S a.dim (S.map a.inclusion.op p.1.2) a.point

theorem normalize_eq_face (n : ℕ) (x : S _⦋n⦌) (t : Simplex n)
    (a : SimplexSupport.Face n t) :
    normalize S ⟨⟨n, x⟩, t⟩ = coreParameters S a.dim (S.map a.inclusion.op x) a.point := by
  change coreParameters S (SimplexSupport.face n t).dim
    (S.map (SimplexSupport.face n t).inclusion.op x) (SimplexSupport.face n t).point = _
  rw [SimplexSupport.face_eq (SimplexSupport.face n t) a]

theorem normalize_map (m n : ℕ) (f : ⦋m⦌ ⟶ ⦋n⦌) (x : S _⦋n⦌) (t : Simplex m) :
    normalize S ⟨⟨m, S.map f.op x⟩, t⟩ =
      normalize S ⟨⟨n, x⟩, stdSimplex.map f.toOrderHom t⟩ := by
  let a := SimplexSupport.face m t
  rw [normalize_eq_face S m (S.map f.op x) t a,
    normalize_eq_face S n x (stdSimplex.map f.toOrderHom t) (SimplexSupport.imageFace a f)]
  have hs : S.map a.inclusion.op (S.map f.op x) =
      S.map (factorThruImage (a.inclusion ≫ f)).op
        (S.map (image.ι (a.inclusion ≫ f)).op x) := by
    calc
      _ = S.map (a.inclusion ≫ f).op x :=
        (Functor.map_comp_apply S f.op a.inclusion.op x).symm
      _ = S.map (factorThruImage (a.inclusion ≫ f) ≫ image.ι (a.inclusion ≫ f)).op x :=
        congrArg (fun g : ⦋a.dim⦌ ⟶ ⦋n⦌ ↦ S.map g.op x) (image.fac (a.inclusion ≫ f)).symm
      _ = _ := Functor.map_comp_apply S (image.ι (a.inclusion ≫ f)).op
        (factorThruImage (a.inclusion ≫ f)).op x
  change coreParameters S a.dim (S.map a.inclusion.op (S.map f.op x)) a.point =
    coreParameters S (image (a.inclusion ≫ f)).len (S.map (image.ι (a.inclusion ≫ f)).op x)
      (stdSimplex.map (factorThruImage (a.inclusion ≫ f)).toOrderHom a.point)
  rw [hs]
  exact coreParameters_epi S (factorThruImage (a.inclusion ≫ f))
    (S.map (image.ι (a.inclusion ≫ f)).op x) a.point

theorem normalize_glue {a b : Parameters S} (h : Glue S a b) :
    normalize S a = normalize S b := by
  cases h with
  | of_map m n f x t => exact normalize_map S m n f x t

theorem normalize_eqvGen {a b : Parameters S} (h : Relation.EqvGen (Glue S) a b) :
    normalize S a = normalize S b := by
  induction h with
  | rel a b h => exact normalize_glue S h
  | refl => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc

def IsNormal (p : Parameters S) : Prop :=
  p.1.2 ∈ S.nonDegenerate p.1.1 ∧ ∀ i, 0 < p.2 i

theorem normalize_isNormal (p : Parameters S) : IsNormal S (normalize S p) := by
  let a := SimplexSupport.face p.1.1 p.2
  let c := core S a.dim (S.map a.inclusion.op p.1.2)
  refine ⟨c.simplex.property, ?_⟩
  exact SimplexSupport.map_positive c.collapse.toOrderHom
    (SimplexCategory.epi_iff_surjective.mp c.epi_collapse) a.point a.positive

theorem normalize_fixed (p : Parameters S) (hp : IsNormal S p) : normalize S p = p := by
  rcases p with ⟨⟨n, x⟩, t⟩
  obtain ⟨hx, ht⟩ := hp
  rw [normalize_eq_face S n x t (SimplexSupport.fullFace n t ht)]
  change coreParameters S n (S.map (𝟙 ⦋n⦌).op x) t = _
  have hid : S.map (𝟙 ⦋n⦌).op x = x := by simp
  rw [hid]
  exact coreParameters_nonDegenerate S n ⟨x, hx⟩ t

theorem normalize_projection (p : Parameters S) :
    projection S (normalize S p) = projection S p := by
  rcases p with ⟨⟨n, x⟩, t⟩
  let a := SimplexSupport.face n t
  rw [normalize_eq_face S n x t a, coreParameters_projection]
  have hc := congrArg (fun f : C(Simplex a.dim, SSet.toTop.obj S) ↦ f a.point)
    (characteristic_map S a.dim n a.inclusion x)
  exact hc.trans (congrArg (characteristic S n x) a.map_point)

theorem normal_injective {a b : Parameters S} (ha : IsNormal S a) (hb : IsNormal S b)
    (h : projection S a = projection S b) : a = b := by
  have hn := normalize_eqvGen S ((projection_eq_iff S a b).mp h)
  rwa [normalize_fixed S a ha, normalize_fixed S b hb] at hn

theorem existsUnique_normal (z : SSet.toTop.obj S) :
    ∃! p : {p : Parameters S // IsNormal S p}, projection S p.val = z := by
  obtain ⟨a, rfl⟩ := projection_surjective S z
  refine ⟨⟨normalize S a, normalize_isNormal S a⟩, normalize_projection S a, ?_⟩
  intro b hb
  apply Subtype.ext
  exact normal_injective S b.property (normalize_isNormal S a)
    (hb.trans (normalize_projection S a).symm)

end Wikipedia.HopfProblem.OrbitPair.RealizationSimplex
