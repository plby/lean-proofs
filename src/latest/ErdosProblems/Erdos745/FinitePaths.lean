import ErdosProblems.Erdos745.EdgeIndependence

/-!
# Recursive finite simple paths and their edge locality

Removing the first vertex on every recursive step records simplicity exactly.
The conversion from Mathlib's simple walks is proved, not assumed.
-/

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A length-`h` simple path from `r` to `v`, using only vertices of `S`. -/
def VertexPath {n : ℕ} (G : SimpleGraph (Fin n)) :
    Finset (Fin n) → Fin n → Fin n → ℕ → Prop
  | S, r, v, 0 => r ∈ S ∧ r = v
  | S, r, v, h + 1 => r ∈ S ∧ ∃ u ∈ S.erase r,
      G.Adj r u ∧ VertexPath G (S.erase r) u v h

/-- A simple path with a prescribed start and length, and any endpoint. -/
def VertexPathFrom {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (r : Fin n) (h : ℕ) : Prop := ∃ v, VertexPath G S r v h

theorem vertexPath_root_mem {n h : ℕ} {G : SimpleGraph (Fin n)}
    {S : Finset (Fin n)} {r v : Fin n} (hp : VertexPath G S r v h) : r ∈ S := by
  cases h <;> exact hp.1

theorem vertexPath_mono_local {n : ℕ} {G H : SimpleGraph (Fin n)}
    (h : ℕ) {S : Finset (Fin n)} {r v : Fin n}
    (hGH : ∀ u ∈ S, ∀ w ∈ S, G.Adj u w → H.Adj u w)
    (hp : VertexPath G S r v h) : VertexPath H S r v h := by
  induction h generalizing S r with
  | zero => exact hp
  | succ h ih =>
    obtain ⟨hr, u, hu, hru, ht⟩ := hp
    refine ⟨hr, u, hu, hGH r hr u (Finset.mem_of_mem_erase hu) hru, ?_⟩
    exact ih (fun x hx y hy ↦ hGH x (Finset.mem_of_mem_erase hx)
      y (Finset.mem_of_mem_erase hy)) ht

theorem vertexPath_mono {n h : ℕ} {G H : SimpleGraph (Fin n)}
    (hGH : G ≤ H) {S : Finset (Fin n)} {r v : Fin n}
    (hp : VertexPath G S r v h) : VertexPath H S r v h :=
  vertexPath_mono_local h (fun _ _ _ _ hadj ↦ hGH hadj) hp

theorem vertexPath_congr {n h : ℕ} {G H : SimpleGraph (Fin n)}
    {S : Finset (Fin n)} {r v : Fin n}
    (hGH : ∀ u ∈ S, ∀ w ∈ S, G.Adj u w ↔ H.Adj u w) :
    VertexPath G S r v h ↔ VertexPath H S r v h :=
  ⟨vertexPath_mono_local h (fun u hu w hw ↦ (hGH u hu w hw).mp),
    vertexPath_mono_local h (fun u hu w hw ↦ (hGH u hu w hw).mpr)⟩

theorem vertexPath_edgeLocal {n h : ℕ} (S : Finset (Fin n)) (r v : Fin n) :
    EdgeLocal (internalEdges S) (fun G ↦ VertexPath G S r v h) := by
  intro A
  exact vertexPath_congr (fun _ hu _ hv ↦ internalEdge_restriction_adj S A hu hv)

theorem vertexPathFrom_edgeLocal {n h : ℕ} (S : Finset (Fin n)) (r : Fin n) :
    EdgeLocal (internalEdges S) (fun G ↦ VertexPathFrom G S r h) := by
  intro A
  exact exists_congr (fun v ↦ vertexPath_edgeLocal S r v A)

theorem vertexPathFrom_mono {n h : ℕ} {G H : SimpleGraph (Fin n)}
    (hGH : G ≤ H) {S : Finset (Fin n)} {r : Fin n}
    (hp : VertexPathFrom G S r h) : VertexPathFrom H S r h := by
  obtain ⟨v, hv⟩ := hp
  exact ⟨v, vertexPath_mono hGH hv⟩

@[simp] theorem vertexPathFrom_zero {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (r : Fin n) : VertexPathFrom G S r 0 ↔ r ∈ S := by
  simp [VertexPathFrom, VertexPath]

theorem vertexPathFrom_succ {n h : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (r : Fin n) :
    VertexPathFrom G S r (h + 1) ↔ r ∈ S ∧
      ∃ u ∈ S.erase r, G.Adj r u ∧ VertexPathFrom G (S.erase r) u h := by
  constructor
  · rintro ⟨v, hr, u, hu, hru, ht⟩
    exact ⟨hr, u, hu, hru, v, ht⟩
  · rintro ⟨hr, u, hu, hru, v, ht⟩
    exact ⟨v, hr, u, hu, hru, ht⟩

theorem vertexPathFrom_root_mem {n h : ℕ} {G : SimpleGraph (Fin n)}
    {S : Finset (Fin n)} {r : Fin n} (hp : VertexPathFrom G S r h) : r ∈ S := by
  obtain ⟨v, hv⟩ := hp
  exact vertexPath_root_mem hv

theorem probability_vertexPath_branch (lam : ℝ) (n h : ℕ) (S : Finset (Fin n))
    (r u v : Fin n) (hru : r ≠ u) :
    probability lam n (fun G ↦ G.Adj r u ∧ VertexPath G (S.erase r) u v h) =
      (edgeProbability lam n : ℝ) *
        probability lam n (fun G ↦ VertexPath G (S.erase r) u v h) := by
  rw [probability_disjoint_blocks lam n {pairEdge r u hru} (internalEdges (S.erase r))
    (pairEdge_disjoint_internal_erase S r u hru) _ _ (edgeLocal_adj r u hru)
    (vertexPath_edgeLocal _ _ _), probability_adj lam n r u hru]

theorem probability_vertexPathFrom_branch (lam : ℝ) (n h : ℕ) (S : Finset (Fin n))
    (r u : Fin n) (hru : r ≠ u) :
    probability lam n (fun G ↦ G.Adj r u ∧ VertexPathFrom G (S.erase r) u h) =
      (edgeProbability lam n : ℝ) *
        probability lam n (fun G ↦ VertexPathFrom G (S.erase r) u h) := by
  rw [probability_disjoint_blocks lam n {pairEdge r u hru} (internalEdges (S.erase r))
    (pairEdge_disjoint_internal_erase S r u hru) _ _ (edgeLocal_adj r u hru)
    (vertexPathFrom_edgeLocal _ _), probability_adj lam n r u hru]

theorem vertexPath_of_walk {n : ℕ} {G : SimpleGraph (Fin n)} {r v : Fin n}
    (p : G.Walk r v) (hp : p.IsPath) (S : Finset (Fin n))
    (hS : ∀ x ∈ p.support, x ∈ S) : VertexPath G S r v p.length := by
  induction p generalizing S with
  | @nil u => exact ⟨hS u (by simp), rfl⟩
  | @cons r u v hru p ih =>
    have ht := (SimpleGraph.Walk.cons_isPath_iff hru p).mp hp
    have htail : ∀ x ∈ p.support, x ∈ S.erase r := by
      intro x hx
      refine Finset.mem_erase.mpr ⟨?_, hS x (by simp [hx])⟩
      intro hxr
      exact ht.2 (hxr ▸ hx)
    exact ⟨hS r (by simp), u, htail u p.start_mem_support, hru, ih ht.1 _ htail⟩

end

end Erdos745
