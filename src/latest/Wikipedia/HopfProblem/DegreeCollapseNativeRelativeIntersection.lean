import Wikipedia.HopfProblem.DegreeCollapseClockNormalizedBasins

/-!
# The actual relative plane intersection from complete native uniqueness

Exact endpoint basin labels turn a relative coordinate-plane crossing
into an original complete connecting orbit. Injectivity of the genuine
full native cylinder then forces its transverse label to be zero.
Thus the unique-intersection input for block reduction is constructed
from the original connecting-orbit uniqueness and basin equations.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {A B Z E M : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem relative_intersection_of_native_unique_connection
    (Φ : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞)
    {U : Set Z} (hsource : Φ.source = U ×ˢ univ) (h0U : (0 : Z) ∈ U)
    (F : Flow ℝ M) (hflow : ∀ z ∈ U, ∀ t : ℝ, Φ (z, t) = F t (Φ (z, 0)))
    (Q P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ H.source) (hH0 : H 0 = 0) (hQ0 : Q 0 = 0)
    (hHs : H.source ⊆ Q.source) (hQU : Q.target ⊆ U)
    (hdiagram : ∀ z ∈ H.source, P (H z) = Q z) {p q : M}
    (hleftBasin : ∀ z ∈ U, Tendsto (fun t => F t (Φ (z, 0))) atBot (𝓝 q) ↔
      ∃ x : A, (x, (0 : B)) ∈ H.source ∧ Q (x, 0) = z)
    (hrightBasin : ∀ z ∈ U, Tendsto (fun t => F t (Φ (z, 1))) atTop (𝓝 p) ↔
      ∃ y ∈ H.target, y.1 = 0 ∧ P y = z)
    (hunique : ∀ x, Tendsto (fun t => F t x) atBot (𝓝 q) →
      Tendsto (fun t => F t x) atTop (𝓝 p) → ∃ t, F t (Φ (0, 0)) = x) :
    ∀ x : A, (x, (0 : B)) ∈ H.source → ((H (x, 0)).1 = 0 ↔ x = 0) := by
  intro x hx
  constructor
  · intro hfirst
    have hzU : Q (x, 0) ∈ U := hQU (Q.map_source' (hHs hx))
    have hbot : Tendsto (fun t => F t (Φ (Q (x, 0), 0))) atBot (𝓝 q) :=
      (hleftBasin _ hzU).mpr ⟨x, hx, rfl⟩
    have htop1 : Tendsto (fun t => F t (Φ (Q (x, 0), 1))) atTop (𝓝 p) :=
      (hrightBasin _ hzU).mpr ⟨H (x, 0), H.map_source' hx, hfirst, hdiagram _ hx⟩
    rw [hflow _ hzU 1] at htop1
    have htop := (MorseCancellation.flow_time_atTop_limit_iff F 1 (Φ (Q (x, 0), 0)) p).mp htop1
    obtain ⟨t, ht⟩ := hunique _ hbot htop
    have hsrc0 : ((0 : Z), t) ∈ Φ.source := by rw [hsource]; exact ⟨h0U, mem_univ _⟩
    have hsrcx : (Q (x, 0), (0 : ℝ)) ∈ Φ.source := by rw [hsource]; exact ⟨hzU, mem_univ _⟩
    have hpoints : Φ (0, t) = Φ (Q (x, 0), 0) := (hflow 0 h0U t).trans ht
    have hlabel : (0 : Z) = Q (x, 0) :=
      congrArg Prod.fst (Φ.toOpenPartialHomeomorph.injOn hsrc0 hsrcx hpoints)
    have hpair : (x, (0 : B)) = (0 : A × B) :=
      Q.toOpenPartialHomeomorph.injOn (hHs hx) (hHs h0) (hlabel.symm.trans hQ0.symm)
    exact congrArg Prod.fst hpair
  · intro hx0
    subst x
    change (H (0 : A × B)).1 = 0
    rw [hH0]
    rfl

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
