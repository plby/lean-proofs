import ErdosProblems.Erdos633.VertexGeometry
import Mathlib.Analysis.Convex.Strict.Extreme

/-!
# Local geometry of arbitrary triangle dissections

The finite vertex set and the local collection of incident tiles are derived
from the dissection. A single positive neighborhood excludes every tile not
containing its center. No edge-to-edge or local angle-sum assumption is used.
-/

namespace Erdos633

open scoped Topology

noncomputable def TriangleDissection.vertexFinset {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) : Finset ℂ := by
  classical
  exact Finset.univ.image fun p : Fin N × Fin 3 => (T.tile p.1).vertex p.2

theorem TriangleDissection.mem_vertexFinset {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (z : ℂ) :
    z ∈ T.vertexFinset ↔ ∃ i : Fin N, ∃ j : Fin 3, (T.tile i).vertex j = z := by
  classical
  simp only [TriangleDissection.vertexFinset, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨⟨i, j⟩, h⟩ => ⟨i, j, h⟩, fun ⟨i, j, h⟩ => ⟨(i, j), h⟩⟩

theorem TriangleDissection.vertex_mem_vertexFinset {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (i : Fin N) (j : Fin 3) :
    (T.tile i).vertex j ∈ T.vertexFinset :=
  (T.mem_vertexFinset _).mpr ⟨i, j, rfl⟩

theorem TriangleDissection.outer_vertex_mem_vertexFinset {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (i : Fin 3) : P.vertex i ∈ T.vertexFinset :=
  (T.mem_vertexFinset _).mpr (T.outer_vertex_incidence i)

theorem Triangle.closure_interior_carrier (P : Triangle) :
    closure (interior P.carrier) = P.carrier := by
  rw [P.convex_carrier.closure_interior_eq_closure_of_nonempty_interior P.interior_nonempty]
  exact P.isCompact_carrier.isClosed.closure_eq

theorem Triangle.vertex_not_mem_interior (P : Triangle) (i : Fin 3) :
    P.vertex i ∉ interior P.carrier := by
  intro h
  exact Set.disjoint_left.mp (disjoint_interior_extremePoints P.carrier) h (P.vertex_extreme i)

theorem TriangleDissection.interior_disjoint_carrier {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) {i j : Fin N} (hij : i ≠ j) :
    Disjoint (interior (T.tile i).carrier) (T.tile j).carrier := by
  have hsub : interior (T.tile j).carrier ⊆ (interior (T.tile i).carrier)ᶜ := by
    intro z hz
    exact fun hi => Set.disjoint_left.mp (T.disjoint hij) hi hz
  have hclosed := closure_minimal hsub isOpen_interior.isClosed_compl
  rw [(T.tile j).closure_interior_carrier] at hclosed
  exact Set.disjoint_left.mpr fun z hi hj => hclosed hj hi

theorem TriangleDissection.vertex_not_mem_tile_interior {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (z : ℂ) (hz : z ∈ T.vertexFinset) (i : Fin N) :
    z ∉ interior (T.tile i).carrier := by
  obtain ⟨j, k, rfl⟩ := (T.mem_vertexFinset z).mp hz
  by_cases hij : i = j
  · subst j
    exact (T.tile i).vertex_not_mem_interior k
  · intro hi
    exact Set.disjoint_left.mp (T.interior_disjoint_carrier hij) hi
      ((T.tile j).vertex_mem_carrier k)

theorem TriangleDissection.exists_local_incidence_radius {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (z : ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Metric.ball z ε, ∀ i : Fin N,
      x ∈ (T.tile i).carrier → z ∈ (T.tile i).carrier := by
  have hnear : ∀ᶠ x in 𝓝 z, ∀ i : Fin N,
      x ∈ (T.tile i).carrier → z ∈ (T.tile i).carrier := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hz : z ∈ (T.tile i).carrier
    · exact Filter.Eventually.of_forall fun _ _ => hz
    · have h := (T.tile i).isCompact_carrier.isClosed.isOpen_compl.mem_nhds hz
      exact Filter.Eventually.mono h fun _ hx hi => False.elim (hx hi)
  exact Metric.mem_nhds_iff.mp hnear

theorem TriangleDissection.local_cover {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (z : ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Metric.ball z ε,
      (x ∈ P.carrier ↔ ∃ i : Fin N, z ∈ (T.tile i).carrier ∧ x ∈ (T.tile i).carrier) := by
  obtain ⟨ε, hε, hlocal⟩ := T.exists_local_incidence_radius z
  refine ⟨ε, hε, ?_⟩
  intro x hx
  constructor
  · intro hP
    rw [← T.covers, Set.mem_iUnion] at hP
    obtain ⟨i, hi⟩ := hP
    exact ⟨i, hlocal x hx i hi, hi⟩
  · rintro ⟨i, _, hi⟩
    exact T.tile_subset i hi

end Erdos633
