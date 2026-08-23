/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset

noncomputable section

namespace Erdos631

abbrev Edge := ℕ × ℕ

inductive DiskExpr where
  | triangle (a b c : ℕ)
  | glue (left right : DiskExpr) (pre post rest : List ℕ) (u v : ℕ)
  | fan (child : DiskExpr) (pref tail : List ℕ) (z : ℕ)
  deriving Repr

end Erdos631

namespace Erdos631.DiskExpr

def root₁ : DiskExpr → ℕ
  | .triangle a _ _ => a
  | .glue left _ _ _ _ _ _ => left.root₁
  | .fan child _ _ _ => child.root₁

def root₂ : DiskExpr → ℕ
  | .triangle _ b _ => b
  | .glue left _ _ _ _ _ _ => left.root₂
  | .fan child _ _ _ => child.root₂

def vertices : DiskExpr → Finset ℕ
  | .triangle a b c => {a, b, c}
  | .glue left right _ _ _ _ _ => left.vertices ∪ right.vertices
  | .fan child _ _ z => insert z child.vertices

def boundary : DiskExpr → List ℕ
  | .triangle a b c => [a, b, c]
  | .glue _ _ pre post rest u v => pre ++ u :: rest.reverse ++ v :: post
  | .fan _ pref _ z => pref ++ [z]

def fanNeighbors (child : DiskExpr) (pref tail : List ℕ) : List ℕ :=
  match pref.getLast? with
  | none => []
  | some w => w :: (tail ++ [child.root₁])

def edges : DiskExpr → Finset Edge
  | .triangle a b c => {(a, b), (b, c), (c, a)}
  | .glue left right _ _ _ _ _ => left.edges ∪ right.edges
  | .fan child pref tail z =>
      child.edges ∪ (child.fanNeighbors pref tail).toFinset.image (fun x => (z, x))

inductive Valid : DiskExpr → Prop where
  | triangle {a b c : ℕ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
      Valid (.triangle a b c)
  | glue {left right : DiskExpr} {pre post rest : List ℕ} {u v : ℕ}
      (hleft : Valid left) (hright : Valid right)
      (hboundary_left : left.boundary = pre ++ u :: v :: post)
      (hboundary_right : right.boundary = u :: v :: rest)
      (hroot_right₁ : right.root₁ = u) (hroot_right₂ : right.root₂ = v)
      (hinter : left.vertices ∩ right.vertices = {u, v})
      (hedge : (u, v) ∈ left.edges ∨ (v, u) ∈ left.edges)
      (huv : u ≠ v) :
      Valid (.glue left right pre post rest u v)
  | fan {child : DiskExpr} {pref tail : List ℕ} {z : ℕ}
      (hchild : Valid child)
      (hboundary : child.boundary = pref ++ tail)
      (hpref : 2 ≤ pref.length)
      (hdisjoint : Disjoint pref.toFinset tail.toFinset)
      (hneighbors : (child.fanNeighbors pref tail).toFinset ⊆ child.vertices)
      (hroot₁_pref : child.root₁ ∈ pref.toFinset)
      (hroot₂_pref : child.root₂ ∈ pref.toFinset)
      (hfresh : z ∉ child.vertices) :
      Valid (.fan child pref tail z)

def EdgeAdj (E : Finset Edge) (x y : ℕ) : Prop :=
  (x, y) ∈ E ∨ (y, x) ∈ E

end Erdos631.DiskExpr

namespace Erdos631

inductive PlaneExpr where
  | disk (D : DiskExpr)
  | edgeSum (left right : PlaneExpr)

end Erdos631

namespace Erdos631.PlaneExpr

def root₁ : PlaneExpr → ℕ
  | .disk D => D.root₁
  | .edgeSum left _ => left.root₁

def root₂ : PlaneExpr → ℕ
  | .disk D => D.root₂
  | .edgeSum left _ => left.root₂

def vertices : PlaneExpr → Finset ℕ
  | .disk D => D.vertices
  | .edgeSum left right => left.vertices ∪ right.vertices

def edges : PlaneExpr → Finset Edge
  | .disk D => D.edges
  | .edgeSum left right => left.edges ∪ right.edges

inductive Valid : PlaneExpr → Prop where
  | disk {D : DiskExpr} (hD : D.Valid) : Valid (.disk D)
  | edgeSum {left right : PlaneExpr} (hleft : Valid left) (hright : Valid right)
      (hroot₁ : right.root₁ = left.root₁) (hroot₂ : right.root₂ = left.root₂)
      (hinter : left.vertices ∩ right.vertices = {left.root₁, left.root₂}) :
      Valid (.edgeSum left right)

end Erdos631.PlaneExpr

namespace Erdos631

structure PlanarCertificate {V : Type*} (G : SimpleGraph V) where
  plane : PlaneExpr
  valid : plane.Valid
  embed : V ↪ ℕ
  vertex_mem : ∀ v, embed v ∈ plane.vertices
  adj_sub : ∀ {v w}, G.Adj v w → DiskExpr.EdgeAdj plane.edges (embed v) (embed w)

end Erdos631

namespace Erdos631

def IsPlanar {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (PlanarCertificate G)

end Erdos631

namespace Erdos753

def IsKChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (L : V → Finset ℕ), (∀ v, (L v).card = k) →
    ∃ f : G.Coloring ℕ, ∀ v, f v ∈ L v

end Erdos753

namespace Erdos753

noncomputable def listChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsKChoosable G k}

/-! ### Basic Properties of Choosability -/

end Erdos753

namespace Erdos631

theorem erdos631 :
    (∀ {V : Type*} [Fintype V] (G : SimpleGraph V), IsPlanar G →
      Erdos753.listChromaticNumber G ≤ 5) ∧
    (∃ G : SimpleGraph (Fin 86), IsPlanar G ∧
      Erdos753.listChromaticNumber G = 5) := by
  sorry

end Erdos631

end
