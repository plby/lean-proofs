import Wikipedia.HopfProblem.OrbitPairSimplexPositiveSupport

/-!
# The unique positive face supporting a barycentric point

Every point of a standard simplex lies in the positive interior of a
unique injectively parametrized face. Existence removes zero coordinates;
uniqueness uses positivity to recover the range of the face inclusion,
then the rigidity of finite ordered sets.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.SimplexSupport

open FirstHurewicz SecondHurewicz.SimplyConnected

structure Face (n : ℕ) (t : Simplex n) where
  dim : ℕ
  inclusion : ⦋dim⦌ ⟶ ⦋n⦌
  mono_inclusion : Mono inclusion
  point : Simplex dim
  positive : ∀ i, 0 < point i
  map_point : stdSimplex.map inclusion.toOrderHom point = t

attribute [instance] Face.mono_inclusion

def fullFace (n : ℕ) (t : Simplex n) (ht : ∀ i, 0 < t i) : Face n t where
  dim := n
  inclusion := 𝟙 _
  mono_inclusion := inferInstance
  point := t
  positive := ht
  map_point := stdSimplex.map_id_apply t

theorem nonempty_face (n : ℕ) (t : Simplex n) : Nonempty (Face n t) := by
  classical
  induction n with
  | zero =>
      let : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
      refine ⟨fullFace 0 t (fun i ↦ ?_)⟩
      rw [stdSimplex.eq_one_of_unique t i]
      exact zero_lt_one
  | succ n ih =>
      by_cases ht : ∀ i, 0 < t i
      · exact ⟨fullFace (n + 1) t ht⟩
      · push Not at ht
        obtain ⟨i, hi⟩ := ht
        have hz : t i = 0 := le_antisymm hi (stdSimplex.zero_le t i)
        let s := simplexFaceInverse n i ⟨t, hz⟩
        obtain ⟨a⟩ := ih s
        refine ⟨{
          dim := a.dim
          inclusion := a.inclusion ≫ SimplexCategory.δ i
          mono_inclusion := inferInstance
          point := a.point
          positive := a.positive
          map_point := ?_ }⟩
        calc
          _ = stdSimplex.map (SimplexCategory.δ i).toOrderHom
              (stdSimplex.map a.inclusion.toOrderHom a.point) :=
            (stdSimplex.map_comp_apply a.inclusion.toOrderHom
              (SimplexCategory.δ i).toOrderHom a.point).symm
          _ = t := by
            rw [a.map_point]
            exact simplexFace_inverse n i ⟨t, hz⟩

theorem face_eq {n : ℕ} {t : Simplex n} (a b : Face n t) : a = b := by
  cases a with
  | mk m f hf s hs hfs =>
    cases b with
    | mk k g hg v hv hgv =>
      let : Mono f := hf
      let : Mono g := hg
      have hrange : Set.range f.toOrderHom = Set.range g.toOrderHom := by
        rw [← positive_support_map f.toOrderHom s hs,
          ← positive_support_map g.toOrderHom v hv, hfs, hgv]
      have hdim : m = k := mono_dim_eq_of_range_eq f g hrange
      subst k
      have hfg : f = g := mono_eq_of_range_eq f g hrange
      subst g
      have hsv : s = v := map_injective f.toOrderHom
        (SimplexCategory.mono_iff_injective.mp hf) (hfs.trans hgv.symm)
      subst v
      rfl

instance faceSubsingleton (n : ℕ) (t : Simplex n) : Subsingleton (Face n t) :=
  ⟨face_eq⟩

def face (n : ℕ) (t : Simplex n) : Face n t := Classical.choice (nonempty_face n t)

theorem face_eq_full (n : ℕ) (t : Simplex n) (ht : ∀ i, 0 < t i) :
    face n t = fullFace n t ht := face_eq _ _

end Wikipedia.HopfProblem.OrbitPair.SimplexSupport
