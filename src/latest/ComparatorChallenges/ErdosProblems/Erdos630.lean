/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset
open scoped SimpleGraph
open scoped Classical
open scoped unitInterval

noncomputable section


universe u

variable {V : Type u} [Fintype V]

namespace Erdos630

open scoped Classical in
structure PlaneDrawing (G : SimpleGraph V) where
  vertexPoint : V → (Fin 2 → ℝ)
  vertexPoint_injective : Function.Injective vertexPoint
  edgePoint : G.edgeSet → I → (Fin 2 → ℝ)
  edge_continuous (e : G.edgeSet) : Continuous (edgePoint e)
  edge_zero (e : G.edgeSet) : edgePoint e 0 = vertexPoint e.1.out.1
  edge_one (e : G.edgeSet) : edgePoint e 1 = vertexPoint e.1.out.2
  edge_interior_injective (e : G.edgeSet) {s t : I} :
    s ≠ 0 → s ≠ 1 → t ≠ 0 → t ≠ 1 → edgePoint e s = edgePoint e t → s = t
  edge_interior_avoids_vertex (e : G.edgeSet) (v : V) {t : I} :
    t ≠ 0 → t ≠ 1 → edgePoint e t ≠ vertexPoint v
  edge_interiors_disjoint {e f : G.edgeSet} (hef : e ≠ f) {s t : I} :
    s ≠ 0 → s ≠ 1 → t ≠ 0 → t ≠ 1 → edgePoint e s ≠ edgePoint f t

end Erdos630

namespace Erdos630

open scoped Classical in
structure PlaneMap (G : SimpleGraph V) (F : Finset G.edgeSet) where
  Face : Type u
  instFintypeFace : Fintype Face
  base : Face → V
  boundary : (q : Face) → G.Walk (base q) (base q)
  boundary_nonempty (q : Face) : 0 < (boundary q).length
  boundary_uses_edges (q : Face) {e : Sym2 V} :
    e ∈ (boundary q).edges → e ∈ F.image Subtype.val
  componentCount : ℕ
  two_components_le_vertices :
    2 * componentCount ≤ (F.biUnion fun e => e.1.toFinset).card
  euler :
    (F.biUnion fun e => e.1.toFinset).card + Fintype.card Face =
      F.card + 2 * componentCount
  boundary_length_sum :
    (∑ q : Face, (boundary q).length) = 2 * F.card
  digon_count_le_components :
    ((Finset.univ : Finset Face).filter fun q => (boundary q).length = 2).card ≤
      componentCount

end Erdos630

namespace Erdos630

open scoped Classical in
structure PlaneEmbedding (G : SimpleGraph V) extends PlaneDrawing G where
  planeMap (F : Finset G.edgeSet) : PlaneMap G F

end Erdos630

namespace Erdos630

open scoped Classical in
def IsPlanar (G : SimpleGraph V) : Prop := Nonempty (PlaneEmbedding G)

end Erdos630

namespace Erdos753

open scoped Classical in
def IsKChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (L : V → Finset ℕ), (∀ v, (L v).card = k) →
    ∃ f : G.Coloring ℕ, ∀ v, f v ∈ L v

end Erdos753

namespace Erdos753

open scoped Classical in
noncomputable def listChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsKChoosable G k}

/-! ### Basic Properties of Choosability -/

end Erdos753

namespace Erdos630

open scoped Classical in
theorem erdos_630 (G : SimpleGraph V) (hplanar : IsPlanar G)
    (hbipartite : G.IsBipartite) :
    Erdos753.listChromaticNumber G ≤ 3 := by
  sorry

end Erdos630

end
