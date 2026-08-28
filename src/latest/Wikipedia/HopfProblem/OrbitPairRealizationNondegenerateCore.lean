import Wikipedia.HopfProblem.OrbitPairRealizationRelations
import Wikipedia.HopfProblem.OrbitPairSimplexPositiveSupport
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
# Unique nondegenerate core data and its geometric parameters

This packages mathlib's actual Eilenberg--Zilber decomposition and its
uniqueness. Precomposition with an epimorphism preserves the nondegenerate
core and composes the coordinate-summing map.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.RealizationSimplex

open FirstHurewicz

variable (S : SSet)

structure Core (n : ℕ) (x : S _⦋n⦌) where
  dim : ℕ
  collapse : ⦋n⦌ ⟶ ⦋dim⦌
  epi_collapse : Epi collapse
  simplex : S.nonDegenerate dim
  decomposes : x = S.map collapse.op simplex.val

attribute [instance] Core.epi_collapse

theorem nonempty_core (n : ℕ) (x : S _⦋n⦌) : Nonempty (Core S n x) := by
  obtain ⟨m, f, hf, y, hy⟩ := S.exists_nonDegenerate x
  exact ⟨⟨m, f, hf, y, hy⟩⟩

theorem core_eq {n : ℕ} {x : S _⦋n⦌} (a b : Core S n x) : a = b := by
  cases a with
  | mk m f hf y hy =>
    cases b with
    | mk k g hg z hz =>
      let : Epi f := hf
      let : Epi g := hg
      have hdim : m = k := S.unique_nonDegenerate_dim x f y hy g z hz
      subst k
      have hfg : f = g := S.unique_nonDegenerate_map x f y hy g z hz
      have hyz : y = z := S.unique_nonDegenerate_simplex x f y hy g z hz
      subst g
      subst z
      rfl

instance coreSubsingleton (n : ℕ) (x : S _⦋n⦌) : Subsingleton (Core S n x) :=
  ⟨core_eq S⟩

def core (n : ℕ) (x : S _⦋n⦌) : Core S n x := Classical.choice (nonempty_core S n x)

def fullCore (n : ℕ) (x : S.nonDegenerate n) : Core S n x.val where
  dim := n
  collapse := 𝟙 _
  epi_collapse := inferInstance
  simplex := x
  decomposes := by simp

def pullbackCore {m n : ℕ} (e : ⦋m⦌ ⟶ ⦋n⦌) [Epi e]
    (x : S _⦋n⦌) (a : Core S n x) : Core S m (S.map e.op x) where
  dim := a.dim
  collapse := e ≫ a.collapse
  epi_collapse := inferInstance
  simplex := a.simplex
  decomposes := by
    exact (congrArg (S.map e.op) a.decomposes).trans
      (Functor.map_comp_apply S a.collapse.op e.op a.simplex.val).symm

def Core.parameters {n : ℕ} {x : S _⦋n⦌} (a : Core S n x) (t : Simplex n) : Parameters S :=
  ⟨⟨a.dim, a.simplex.val⟩, stdSimplex.map a.collapse.toOrderHom t⟩

def coreParameters (n : ℕ) (x : S _⦋n⦌) (t : Simplex n) : Parameters S :=
  (core S n x).parameters S t

theorem coreParameters_eq (n : ℕ) (x : S _⦋n⦌) (t : Simplex n) (a : Core S n x) :
    coreParameters S n x t = a.parameters S t := by
  unfold coreParameters
  rw [core_eq S (core S n x) a]

theorem coreParameters_nonDegenerate (n : ℕ) (x : S.nonDegenerate n) (t : Simplex n) :
    coreParameters S n x.val t = ⟨⟨n, x.val⟩, t⟩ := by
  rw [coreParameters_eq S n x.val t (fullCore S n x)]
  change (⟨⟨n, x.val⟩, stdSimplex.map id t⟩ : Parameters S) = _
  rw [stdSimplex.map_id_apply]

theorem coreParameters_epi {m n : ℕ} (e : ⦋m⦌ ⟶ ⦋n⦌) [Epi e]
    (x : S _⦋n⦌) (t : Simplex m) :
    coreParameters S m (S.map e.op x) t =
      coreParameters S n x (stdSimplex.map e.toOrderHom t) := by
  rw [coreParameters_eq S m (S.map e.op x) t (pullbackCore S e x (core S n x))]
  change (⟨⟨(core S n x).dim, (core S n x).simplex.val⟩,
    stdSimplex.map (e ≫ (core S n x).collapse).toOrderHom t⟩ : Parameters S) =
      ⟨⟨(core S n x).dim, (core S n x).simplex.val⟩,
        stdSimplex.map (core S n x).collapse.toOrderHom (stdSimplex.map e.toOrderHom t)⟩
  exact congrArg (fun v ↦ (⟨⟨(core S n x).dim, (core S n x).simplex.val⟩, v⟩ : Parameters S))
    (stdSimplex.map_comp_apply e.toOrderHom (core S n x).collapse.toOrderHom t).symm

theorem coreParameters_projection (n : ℕ) (x : S _⦋n⦌) (t : Simplex n) :
    projection S (coreParameters S n x t) = characteristic S n x t := by
  let a := core S n x
  have hc := congrArg (fun f : C(Simplex n, SSet.toTop.obj S) ↦ f t)
    (characteristic_map S n a.dim a.collapse a.simplex.val)
  have hx := congrArg (fun y : S _⦋n⦌ ↦ characteristic S n y t) a.decomposes
  exact hc.symm.trans hx.symm

end Wikipedia.HopfProblem.OrbitPair.RealizationSimplex
