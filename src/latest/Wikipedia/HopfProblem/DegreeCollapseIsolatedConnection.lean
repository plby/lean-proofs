import Wikipedia.HopfProblem.DegreeCollapseFlowEndpoints
import Wikipedia.HopfProblem.DegreeCollapseFlowNoReturn

/-!
# The actual invariant set of an isolated critical pair

Endpoint convergence identifies every trajectory staying in the closed
band. Distinct critical heights force a nonstationary trajectory to run
from the upper critical point to the lower one. Uniqueness of that actual
connection then constructs a no-return neighborhood of the whole orbit
and its two endpoints.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Every point whose whole trajectory stays in the band is an endpoint or on the unique orbit. -/
theorem invariant_band_subset_connection (F : Flow ℝ X) {f : X → ℝ}
    (hf : Continuous f) {S : Set X} (hinj : InjOn f S)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hstrict : ∀ x ∉ S, StrictAnti (fun t : ℝ => f (F t x)))
    {p q z : X} (hpair : ∀ x ∈ S, f x ∈ Icc (f p) (f q) → x = p ∨ x = q)
    (hunique : ∀ x ∉ S,
      Tendsto (fun t : ℝ => F t x) atBot (𝓝 q) →
      Tendsto (fun t : ℝ => F t x) atTop (𝓝 p) → ∃ t : ℝ, F t z = x)
    {x : X} (hstay : ∀ t : ℝ, f (F t x) ∈ Icc (f p) (f q)) :
    x ∈ ({p, q} : Set X) ∪ range (fun t : ℝ => F t z) := by
  have hxband : f x ∈ Icc (f p) (f q) := by simpa only [F.map_zero_apply] using hstay 0
  by_cases hxS : x ∈ S
  · rcases hpair x hxS hxband with rfl | rfl <;> exact Or.inl (by simp)
  obtain ⟨r, hr, s, hs, hrlim, hslim, hsep⟩ :=
    exists_strict_descent_flow_endpoints F hf hinj hmono hstrict x
  have hrband : f r ∈ Icc (f p) (f q) :=
    isClosed_Icc.mem_of_tendsto (hf.continuousAt.tendsto.comp hrlim)
      (Eventually.of_forall hstay)
  have hsband : f s ∈ Icc (f p) (f q) :=
    isClosed_Icc.mem_of_tendsto (hf.continuousAt.tendsto.comp hslim)
      (Eventually.of_forall hstay)
  have hsep' := hsep hxS
  have hrq : r = q := (hpair r hr hrband).resolve_left (by
    intro he
    rw [he] at hsep'
    linarith [hxband.1])
  have hsp : s = p := (hpair s hs hsband).resolve_right (by
    intro he
    rw [he] at hsep'
    linarith [hxband.2])
  obtain ⟨t, ht⟩ := hunique x hxS
    (by simpa only [hrq] using hrlim) (by simpa only [hsp] using hslim)
  exact Or.inr ⟨t, ht⟩

/-- Uniqueness of the connecting trajectory supplies the previously explicit invariant-set input. -/
theorem exists_isolated_connection_no_return (F : Flow ℝ X) {f : X → ℝ}
    (hf : Continuous f) {S : Set X} (hinj : InjOn f S)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hstrict : ∀ x ∉ S, StrictAnti (fun t : ℝ => f (F t x)))
    (hfixed : ∀ x ∈ S, ∀ t : ℝ, F t x = x)
    {p q z : X} (hp : p ∈ S) (hq : q ∈ S) (hpq : f p < f q)
    (hpair : ∀ x ∈ S, f x ∈ Icc (f p) (f q) → x = p ∨ x = q)
    (hzband : ∀ t : ℝ, f (F t z) ∈ Icc (f p) (f q))
    (hunique : ∀ x ∉ S,
      Tendsto (fun t : ℝ => F t x) atBot (𝓝 q) →
      Tendsto (fun t : ℝ => F t x) atTop (𝓝 p) → ∃ t : ℝ, F t z = x)
    {U : Set X} (hU : IsOpen U) (hpU : p ∈ U) (hqU : q ∈ U)
    (hzU : ∀ t : ℝ, F t z ∈ U) :
    ∃ N : Set X, IsOpen N ∧ N ⊆ U ∧ p ∈ N ∧ q ∈ N ∧
      (∀ t : ℝ, F t z ∈ N) ∧
      ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N →
        ∀ s ∈ Icc (0 : ℝ) t, F s x ∈ U := by
  let K : Set X := {x | ∀ t : ℝ, f (F t x) ∈ Icc (f p) (f q)}
  have hKU : K ⊆ U := by
    intro x hx
    rcases invariant_band_subset_connection F hf hinj hmono hstrict hpair hunique hx with
      h | ⟨t, rfl⟩
    · rcases h with h | h
      · exact h ▸ hpU
      · exact (show x = q from h) ▸ hqU
    · exact hzU t
  have hKband (x : X) (hx : x ∈ K) : f x ∈ Icc (f p) (f q) := by
    simpa only [F.map_zero_apply] using hx 0
  have hKi (t : ℝ) (x : X) (hx : x ∈ K) : F t x ∈ K := by
    intro s
    rw [← F.map_add]
    exact hx (s + t)
  obtain ⟨N, hN, hKN, hNU, hreturn⟩ := exists_flow_no_return_neighborhood
    F hf hmono hU hKU hKband hKi (fun _ h => h)
  have hpK : p ∈ K := by
    intro t
    rw [hfixed p hp t]
    exact ⟨le_rfl, hpq.le⟩
  have hqK : q ∈ K := by
    intro t
    rw [hfixed q hq t]
    exact ⟨hpq.le, le_rfl⟩
  exact ⟨N, hN, hNU, hKN hpK, hKN hqK, fun t => hKN (hKi t z hzband), hreturn⟩

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
