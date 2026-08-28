import Wikipedia.HopfProblem.DegreeCollapseWholeLevelBasinTransport
import Wikipedia.HopfProblem.DegreeCollapseConnectionSections

/-!
# A unique actual connection from one level-basin intersection

Exact basin transport identifies the level intersection after holonomy
insertion. Every complete connecting orbit crosses that same original
level, so a unique intersection point gives an actual unique complete
connection. No transversality is inferred from this uniqueness.
-/

noncomputable section

open Set Function Filter
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {M : Type*} [TopologicalSpace M]

theorem unique_connection_of_level_basin_intersection
    (F G : Flow ℝ M) {f : M → ℝ} (hf : Continuous f) {p q : M} {c : ℝ}
    (hpc : c < f p) (hqc : f q < c)
    (D : {x : M // f x = c} → {x : M // f x = c})
    (hback : ∀ x : {y : M // f y = c},
      Tendsto (fun t => G t x) atBot (𝓝 p) ↔ Tendsto (fun t => F t x) atBot (𝓝 p))
    (hforward : ∀ x : {y : M // f y = c},
      Tendsto (fun t => G t x) atTop (𝓝 q) ↔ Tendsto (fun t => F t (D x)) atTop (𝓝 q))
    (z : {y : M // f y = c})
    (hzback : Tendsto (fun t => F t z) atBot (𝓝 p))
    (hzforward : Tendsto (fun t => F t (D z)) atTop (𝓝 q))
    (hunique : ∀ x : {y : M // f y = c},
      Tendsto (fun t => F t x) atBot (𝓝 p) →
      Tendsto (fun t => F t (D x)) atTop (𝓝 q) → x = z) :
    Tendsto (fun t => G t z) atBot (𝓝 p) ∧
      Tendsto (fun t => G t z) atTop (𝓝 q) ∧
      ∀ x, Tendsto (fun t => G t x) atBot (𝓝 p) →
        Tendsto (fun t => G t x) atTop (𝓝 q) → ∃ t, G t z = x := by
  refine ⟨(hback z).mpr hzback, (hforward z).mpr hzforward, ?_⟩
  intro x hxback hxforward
  obtain ⟨s, hs⟩ := FlowCancellation.exists_level_crossing_of_endpoint_limits
    G hf hxback hxforward hpc hqc
  let u : {y : M // f y = c} := ⟨G s x, hs⟩
  have hub : Tendsto (fun t => G t u) atBot (𝓝 p) :=
    (MorseCancellation.flow_time_atBot_limit_iff G s x p).mpr hxback
  have huf : Tendsto (fun t => G t u) atTop (𝓝 q) :=
    (MorseCancellation.flow_time_atTop_limit_iff G s x q).mpr hxforward
  have huz : u = z := hunique u ((hback u).mp hub) ((hforward u).mp huf)
  have hv : G s x = (z : M) := congrArg Subtype.val huz
  refine ⟨-s, ?_⟩
  rw [← hv, ← G.map_add, neg_add_cancel, G.map_zero_apply]

theorem exists_unique_connection_of_unit_level_count
    (F G : Flow ℝ M) {f : M → ℝ} (hf : Continuous f) {p q : M} {c : ℝ}
    (hpc : c < f p) (hqc : f q < c)
    (D : {x : M // f x = c} → {x : M // f x = c})
    (hback : ∀ x : {y : M // f y = c},
      Tendsto (fun t => G t x) atBot (𝓝 p) ↔ Tendsto (fun t => F t x) atBot (𝓝 p))
    (hforward : ∀ x : {y : M // f y = c},
      Tendsto (fun t => G t x) atTop (𝓝 q) ↔ Tendsto (fun t => F t (D x)) atTop (𝓝 q))
    (hcount : {x : {y : M // f y = c} |
      Tendsto (fun t => F t x) atBot (𝓝 p) ∧
      Tendsto (fun t => F t (D x)) atTop (𝓝 q)}.ncard = 1) :
    ∃ z : {y : M // f y = c}, Tendsto (fun t => G t z) atBot (𝓝 p) ∧
      Tendsto (fun t => G t z) atTop (𝓝 q) ∧
      ∀ x, Tendsto (fun t => G t x) atBot (𝓝 p) →
        Tendsto (fun t => G t x) atTop (𝓝 q) → ∃ t, G t z = x := by
  let C := {x : {y : M // f y = c} |
    Tendsto (fun t => F t x) atBot (𝓝 p) ∧
    Tendsto (fun t => F t (D x)) atTop (𝓝 q)}
  obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp hcount
  have hmem : z ∈ C := by rw [show C = {z} from hz]; exact mem_singleton z
  have hu (x : {y : M // f y = c})
      (hb : Tendsto (fun t => F t x) atBot (𝓝 p))
      (hf' : Tendsto (fun t => F t (D x)) atTop (𝓝 q)) : x = z := by
    have hx : x ∈ C := ⟨hb, hf'⟩
    rw [show C = {z} from hz] at hx
    exact mem_singleton_iff.mp hx
  exact ⟨z, unique_connection_of_level_basin_intersection F G hf hpc hqc D
    hback hforward z hmem.1 hmem.2 hu⟩

theorem no_connection_of_level_basin_disjointness
    (F G : Flow ℝ M) {f : M → ℝ} (hf : Continuous f) {p q : M} {c : ℝ}
    (hpc : c < f p) (hqc : f q < c)
    (D : {x : M // f x = c} → {x : M // f x = c})
    (hback : ∀ x : {y : M // f y = c},
      Tendsto (fun t => G t x) atBot (𝓝 p) ↔ Tendsto (fun t => F t x) atBot (𝓝 p))
    (hforward : ∀ x : {y : M // f y = c},
      Tendsto (fun t => G t x) atTop (𝓝 q) ↔ Tendsto (fun t => F t (D x)) atTop (𝓝 q))
    (hdisjoint : ∀ x : {y : M // f y = c},
      ¬(Tendsto (fun t => F t x) atBot (𝓝 p) ∧
        Tendsto (fun t => F t (D x)) atTop (𝓝 q))) :
    ∀ x, ¬(Tendsto (fun t => G t x) atBot (𝓝 p) ∧
      Tendsto (fun t => G t x) atTop (𝓝 q)) := by
  rintro x ⟨hxback, hxforward⟩
  obtain ⟨s, hs⟩ := FlowCancellation.exists_level_crossing_of_endpoint_limits
    G hf hxback hxforward hpc hqc
  let u : {y : M // f y = c} := ⟨G s x, hs⟩
  have hub : Tendsto (fun t => G t u) atBot (𝓝 p) :=
    (MorseCancellation.flow_time_atBot_limit_iff G s x p).mpr hxback
  have huf : Tendsto (fun t => G t u) atTop (𝓝 q) :=
    (MorseCancellation.flow_time_atTop_limit_iff G s x q).mpr hxforward
  exact hdisjoint u ⟨(hback u).mp hub, (hforward u).mp huf⟩

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
