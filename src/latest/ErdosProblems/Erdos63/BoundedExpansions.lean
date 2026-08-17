/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos63.Avoidance

/-!
# Erdős Problem 63: bounded vertex expansions

This module develops the bounded vertex expansions used in Sections 3.4--3.6
of Liu--Montgomery.  The public `VertexExpansion` is exactly the induced-set
notion from Definition 3.9: a finite set of the prescribed cardinality, with a
root-to-every-vertex path of bounded length contained in the set.  Proposition
3.10 is proved directly by growing a retained rooted set one first-exit prefix
at a time.
-/

open Finset Set SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

universe u v

variable {V : Type u} {G G' : SimpleGraph V}

/-- Source-faithful name for a `(D,m)`-expansion about a vertex. -/
abbrev VertexExpansion {V : Type u} (G : SimpleGraph V) (root : V)
    (D radius : ℕ) : Type u := BoundedVertexExpansion G root D radius

namespace VertexExpansion

variable {root : V} {D radius : ℕ}

/-- The vertex set of an expansion. -/
abbrev verts (E : VertexExpansion G root D radius) : Finset V := E.vertices

@[simp] theorem card_verts (E : VertexExpansion G root D radius) :
    E.verts.card = D := E.card_vertices

theorem exists_path (E : VertexExpansion G root D radius) {y : V}
    (hy : y ∈ E.verts) :
    ∃ p : G.Walk root y,
      p.IsPath ∧ p.length ≤ radius ∧ ∀ z ∈ p.support, z ∈ E.verts :=
  E.path_to y hy

/-- The one-vertex rooted expansion, at any radius. -/
noncomputable def singleton (G : SimpleGraph V) (root : V) (radius : ℕ) :
    VertexExpansion G root 1 radius where
  vertices := {root}
  root_mem := by simp
  card_vertices := by simp
  path_to := by
    intro y hy
    have hyroot : y = root := by simpa using hy
    subst y
    exact ⟨Walk.nil, Walk.IsPath.nil, by simp, by simp [Walk.SupportsIn]⟩

/-- An avoiding ball, equipped with its canonical short rooted paths, is a
vertex expansion.  This is the bridge used after each ball-growth argument. -/
noncomputable def ofBallAvoiding [Fintype V] (G : SimpleGraph V)
    (forbidden : Set V) (root : V) (radius : ℕ) :
    VertexExpansion G root (ballAvoiding G forbidden root radius).card radius where
  vertices := ballAvoiding G forbidden root radius
  root_mem := root_mem_ballAvoiding G forbidden root radius
  card_vertices := rfl
  path_to := by
    intro y hy
    obtain ⟨p, hp, hlen⟩ :=
      (mem_ballAvoiding G forbidden root radius y).1 hy
    exact ⟨p, hp.1, hlen,
      support_subset_ballAvoiding hp hlen⟩

@[simp] theorem verts_ofBallAvoiding [Fintype V] (G : SimpleGraph V)
    (forbidden : Set V) (root : V) (radius : ℕ) :
    (ofBallAvoiding G forbidden root radius).verts =
      ballAvoiding G forbidden root radius := rfl

/-- Weakening the radius leaves the vertex set unchanged. -/
abbrev radiusMono (E : VertexExpansion G root D radius) {radius' : ℕ}
    (h : radius ≤ radius') : VertexExpansion G root D radius' :=
  BoundedVertexExpansion.radiusMono E h

@[simp] theorem verts_radiusMono (E : VertexExpansion G root D radius) {radius' : ℕ}
    (h : radius ≤ radius') : (E.radiusMono h).verts = E.verts := rfl

/-- Adding graph edges preserves a vertex expansion. -/
abbrev monoGraph (E : VertexExpansion G root D radius) (hGG' : G ≤ G') :
    VertexExpansion G' root D radius :=
  BoundedVertexExpansion.monoGraph E hGG'

@[simp] theorem verts_monoGraph (E : VertexExpansion G root D radius)
    (hGG' : G ≤ G') : (E.monoGraph hGG').verts = E.verts := rfl

/-- A graph embedding transports a bounded expansion without changing its
order or radius. -/
noncomputable def mapEmbedding {W : Type v} {H : SimpleGraph W}
    (E : VertexExpansion G root D radius) (f : G ↪g H) :
    VertexExpansion H (f root) D radius where
  vertices := E.verts.map ⟨f, f.injective⟩
  root_mem := Finset.mem_map.2 ⟨root, E.root_mem, rfl⟩
  card_vertices := by
    simpa using E.card_verts
  path_to := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
    obtain ⟨p, hp, hlen, hsupp⟩ := E.exists_path hx
    refine ⟨p.map f.toHom, hp.map f.injective, ?_, ?_⟩
    · simpa using hlen
    · intro z hz
      rw [Walk.support_map] at hz
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
      exact Finset.mem_map.2 ⟨w, hsupp w hw, rfl⟩

@[simp] theorem verts_mapEmbedding {W : Type v} {H : SimpleGraph W}
    (E : VertexExpansion G root D radius) (f : G ↪g H) :
    (E.mapEmbedding f).verts = E.verts.map ⟨f, f.injective⟩ := rfl

/-! ### Shrinking an arbitrary expansion -/

/-- On a path from a retained root to a vertex outside the retained set, the
first new vertex has a prefix path supported by the retained set plus that one
vertex. -/
private theorem exists_first_exit_prefix {S T : Finset V} {y : V}
    (hroot : root ∈ T) (p : G.Walk root y) (hp : p.IsPath)
    (hlen : p.length ≤ radius) (hsupp : p.SupportsIn S) (hy : y ∉ T) :
    ∃ z ∈ S, z ∉ T ∧ ∃ q : G.Walk root z,
      q.IsPath ∧ q.length ≤ radius ∧ q.SupportsIn (insert z T) := by
  classical
  let P : ℕ → Prop := fun n ↦ n ≤ p.length ∧ p.getVert n ∉ T
  have hP : ∃ n, P n := by
    refine ⟨p.length, le_rfl, ?_⟩
    simpa using hy
  let n := Nat.find hP
  have hn : n ≤ p.length ∧ p.getVert n ∉ T := Nat.find_spec hP
  have hnpos : 0 < n := by
    by_contra h
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos h
    apply hn.2
    simpa [hnzero] using hroot
  let z := p.getVert n
  let q : G.Walk root z := p.take n
  have hq_length : q.length = n := by
    simp [q, Walk.take_length, Nat.min_eq_left hn.1]
  have hzS : z ∈ S := hsupp z (p.getVert_mem_support n)
  refine ⟨z, hzS, hn.2, q, hp.take n, ?_, ?_⟩
  · rw [hq_length]
    exact hn.1.trans hlen
  · intro w hw
    obtain ⟨k, hkw, hkle⟩ :=
      (Walk.mem_support_iff_exists_getVert (p := q)).1 hw
    have hkn : k ≤ n := by simpa [hq_length] using hkle
    have hqget : q.getVert k = p.getVert k := by
      simp [q, Walk.take_getVert, Nat.min_eq_right hkn]
    by_cases hkeq : k = n
    · have hwz : w = z := by
        rw [← hkw, hqget, hkeq]
      simpa [hwz]
    · apply Finset.mem_insert_of_mem
      have hpkT : p.getVert k ∈ T := by
        by_contra hkT
        have hklen : k ≤ p.length := hkn.trans hn.1
        have hnle : n ≤ k := Nat.find_min' hP ⟨hklen, hkT⟩
        exact hkeq (Nat.le_antisymm hkn hnle)
      rw [← hkw, hqget]
      exact hpkT

/-- Liu--Montgomery Proposition 3.10 for the exact induced-set definition:
every positive smaller order occurs with the same root and radius. -/
theorem proposition3_10 (E : VertexExpansion G root D radius) {D' : ℕ}
    (hD' : 0 < D') (hle : D' ≤ D) :
    ∃ E' : VertexExpansion G root D' radius,
      (E'.verts : Finset V) ⊆ (E.verts : Finset V) := by
  classical
  induction D' using Nat.strong_induction_on with
  | h q ih =>
      rcases q with _ | n
      · omega
      · by_cases hnzero : n = 0
        · subst n
          refine ⟨singleton G root radius, ?_⟩
          intro z hz
          have hzroot : z = root := by
            change z ∈ ({root} : Finset V) at hz
            simpa using hz
          simpa [hzroot] using E.root_mem
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
          have hnlt : n < n + 1 := Nat.lt_succ_self n
          have hnleD : n ≤ D := by omega
          obtain ⟨F, hFE⟩ := ih n hnlt hnpos hnleD
          have hcard_lt : F.verts.card < E.verts.card := by
            rw [F.card_verts, E.card_verts]
            omega
          have hne : F.verts ≠ E.verts := by
            intro heq
            rw [heq] at hcard_lt
            exact (Nat.lt_irrefl _ hcard_lt)
          have hproper : F.verts ⊂ E.verts :=
            Finset.ssubset_iff_subset_ne.2 ⟨hFE, hne⟩
          obtain ⟨y, hyE, hyF⟩ := Finset.exists_of_ssubset hproper
          obtain ⟨p, hp, hplen, hpsupp⟩ := E.exists_path hyE
          obtain ⟨z, hzE, hzF, q, hq, hqlen, hqsupp⟩ :=
            exists_first_exit_prefix F.root_mem p hp hplen hpsupp hyF
          let F' : VertexExpansion G root (n + 1) radius :=
            { vertices := insert z F.verts
              root_mem := Finset.mem_insert_of_mem F.root_mem
              card_vertices := by simp [hzF, F.card_verts]
              path_to := by
                intro w hw
                rw [Finset.mem_insert] at hw
                rcases hw with rfl | hw
                · exact ⟨q, hq, hqlen, hqsupp⟩
                · obtain ⟨r, hr, hrlen, hrsupp⟩ := F.exists_path hw
                  exact ⟨r, hr, hrlen,
                    fun w hw ↦ Finset.mem_insert_of_mem (hrsupp w hw)⟩ }
          refine ⟨F', ?_⟩
          intro w hw
          rw [show F'.verts = insert z F.verts by rfl] at hw
          rcases Finset.mem_insert.1 hw with rfl | hw
          · exact hzE
          · exact hFE hw

/-! ### Connecting two bounded expansions -/

/-- If the avoiding balls grown from two expansions contain more vertices in
total than the ambient graph, the roots are joined by a short simple path.
The resulting path misses the forbidden set completely.  This is the
set-theoretic connector used repeatedly in Lemmas 3.13--3.15. -/
theorem exists_path_between_roots_of_large_balls [Fintype V]
    {root₁ root₂ : V} {D₁ D₂ m₁ m₂ r s : ℕ}
    (E₁ : VertexExpansion G root₁ D₁ m₁)
    (E₂ : VertexExpansion G root₂ D₂ m₂)
    (X : Finset V) (hX₁ : Disjoint X E₁.verts) (hX₂ : Disjoint X E₂.verts)
    (hlarge : Fintype.card V <
      (ballAvoidingFrom G (X : Set V) E₁.verts r).card +
        (ballAvoidingFrom G (X : Set V) E₂.verts s).card) :
    ∃ p : G.Walk root₁ root₂,
      p.IsPath ∧ p.length ≤ m₁ + r + s + m₂ ∧
        ∀ z ∈ p.support, z ∉ X := by
  classical
  have hconn :
      ∃ a ∈ E₁.verts, ∃ b ∈ E₂.verts, ∃ c : G.Walk a b,
        c.IsAvoidingPath (X : Set V) ({a, b} : Set V) ∧
          c.length ≤ r + s :=
    exists_avoiding_path_between_of_large_balls G (X : Set V)
      E₁.verts E₂.verts r s hlarge
  obtain ⟨a, ha₁, b, hb₂, c, hc, hclen⟩ := hconn
  obtain ⟨p₁, hp₁, hp₁len, hp₁supp⟩ := E₁.exists_path ha₁
  obtain ⟨p₂, hp₂, hp₂len, hp₂supp⟩ := E₂.exists_path hb₂
  let w : G.Walk root₁ root₂ := (p₁.append c).append p₂.reverse
  have hwmiss : ∀ z ∈ w.support, z ∉ X := by
    intro z hz hzX
    change z ∈ ((p₁.append c).append p₂.reverse).support at hz
    rw [Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · rw [Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · exact Finset.disjoint_left.1 hX₁ hzX (hp₁supp z hz)
      · have hzca : z = a ∨ z = b := by
          by_contra hzab
          have hznot : z ∈ (X : Set V) → z ∈ ({a, b} : Set V) :=
            hc.2 z hz
          have := hznot hzX
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
          exact hzab this
        rcases hzca with rfl | rfl
        · exact Finset.disjoint_left.1 hX₁ hzX ha₁
        · exact Finset.disjoint_left.1 hX₂ hzX hb₂
    · have hzp₂ : z ∈ p₂.support := by
        simpa [p₂.support_reverse] using hz
      exact Finset.disjoint_left.1 hX₂ hzX (hp₂supp z hzp₂)
  refine ⟨w.bypass, w.bypass_isPath, ?_, ?_⟩
  · calc
      w.bypass.length ≤ w.length := w.length_bypass_le_length
      _ = p₁.length + c.length + p₂.length := by simp [w, Nat.add_assoc]
      _ ≤ m₁ + (r + s) + m₂ := by omega
      _ = m₁ + r + s + m₂ := by omega
  · intro z hz
    exact hwmiss z (w.support_bypass_subset_support hz)

end VertexExpansion

/-! ## Output records for the simultaneous connection lemmas -/

/-- Two vertex-disjoint paths with controlled total length.  This is the
precise walk-level output of Corollary 3.15 after a pairing of the four roots
has been selected. -/
structure DisjointConnectorPair (G : SimpleGraph V)
    (forbidden : Finset V) (v₁ v₂ v₃ v₄ : V) (lower upper : ℕ) where
  left : G.Walk v₁ v₃
  right : G.Walk v₂ v₄
  left_isPath : left.IsPath
  right_isPath : right.IsPath
  disjoint : left.support.Disjoint right.support
  left_avoids : ∀ z ∈ left.support, z ∉ forbidden
  right_avoids : ∀ z ∈ right.support, z ∉ forbidden
  lower_length : lower ≤ left.length + right.length
  upper_length : left.length + right.length ≤ upper

namespace DisjointConnectorPair

variable {forbidden : Finset V} {v₁ v₂ v₃ v₄ : V} {lower upper : ℕ}

/-- Swap the two connectors. -/
def swap (P : DisjointConnectorPair G forbidden v₁ v₂ v₃ v₄ lower upper) :
    DisjointConnectorPair G forbidden v₂ v₁ v₄ v₃ lower upper where
  left := P.right
  right := P.left
  left_isPath := P.right_isPath
  right_isPath := P.left_isPath
  disjoint := P.disjoint.symm
  left_avoids := P.right_avoids
  right_avoids := P.left_avoids
  lower_length := by simpa [Nat.add_comm] using P.lower_length
  upper_length := by simpa [Nat.add_comm] using P.upper_length

end DisjointConnectorPair

/-- Pairing-insensitive conclusion of Liu--Montgomery Corollary 3.15. -/
def LM315Conclusion (G : SimpleGraph V) (forbidden : Finset V) (v₁ v₂ v₃ v₄ : V)
    (ell m : ℕ) : Prop :=
  Nonempty (DisjointConnectorPair G forbidden v₁ v₂ v₃ v₄ ell (ell + 22 * m)) ∨
    Nonempty (DisjointConnectorPair G forbidden v₁ v₂ v₄ v₃ ell (ell + 22 * m))

end Erdos63
