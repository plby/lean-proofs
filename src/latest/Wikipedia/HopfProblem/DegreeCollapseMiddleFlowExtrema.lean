import Wikipedia.HopfProblem.DegreeCollapseNativeMiddleSeparatedFlow

/-!
# The actual middle cores run to the unique extrema

For the separated native middle flow, every noncritical point in a
descending middle basin converges to the unique minimum, and every point
in an ascending middle basin comes from the unique maximum. The empty
extremal core sections exclude the wrong endpoints. Consequently entire
native attaching and belt spheres cross the prescribed extremal cuts.
No endpoint or crossing direction is supplied as a geometric premise.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
  (S : AdaptedSurgeryWindows E f)

theorem critical_eq_of_count_one {k : ℕ} (hcount : nativeMorseCount E f k = 1)
    (p q : criticalPoints E f) (hp : nativeMorseIndex E f p = k)
    (hq : nativeMorseIndex E f q = k) : p = q := by
  change {x : M | x ∈ criticalPoints E f ∧ nativeMorseIndex E f x = k}.ncard = 1 at hcount
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hcount
  have hp' : p.val ∈ {x : M | x ∈ criticalPoints E f ∧ nativeMorseIndex E f x = k} :=
    ⟨p.property, hp⟩
  have hq' : q.val ∈ {x : M | x ∈ criticalPoints E f ∧ nativeMorseIndex E f x = k} :=
    ⟨q.property, hq⟩
  rw [hx, mem_singleton_iff] at hp' hq'
  exact Subtype.ext (hp'.trans hq'.symm)

theorem first_native_index (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    nativeMorseIndex E f (S.toSurgeryWindows.first (S.toSurgeryWindows.count_pos hf)) = 0 :=
  (nativeMorseIndex_eq_chart (S.data _).chart).trans
    (S.toSurgeryWindows.first_index_zero hf _)

theorem last_native_index (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) :
    nativeMorseIndex E f (S.toSurgeryWindows.last (S.toSurgeryWindows.count_pos hf)) = 6 :=
  (nativeMorseIndex_eq_chart (S.data _).chart).trans
    ((S.toSurgeryWindows.last_index_dimension hf _).trans hdim)

theorem forward_middle_endpoint
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (hzero : nativeMorseCount E f 0 = 1) (hsep : NoMiddleConnections S)
    (hindices : ∀ p : criticalPoints E f,
      nativeMorseIndex E f p = 0 ∨ nativeMorseIndex E f p = 3 ∨ nativeMorseIndex E f p = 6)
    (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 3)
    {x : M} (hx : x ∉ criticalPoints E f)
    (hback : Tendsto (fun t => S.flow t x) atBot (𝓝 p.val)) :
    Tendsto (fun t => S.flow t x) atTop
      (𝓝 (S.toSurgeryWindows.first (S.toSurgeryWindows.count_pos hf)).val) := by
  obtain ⟨b, hb, q, hq, -, hforward, -⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral
      S.zero S.descent S.distinct x
  let q' : criticalPoints E f := ⟨q, hq⟩
  obtain ⟨hqx, hxp⟩ := connection_heights S hf hx hback hforward
  rcases hindices q' with h0 | h3 | h6
  · have he := critical_eq_of_count_one hzero q' _ h0 (first_native_index S hf)
    exact he ▸ hforward
  · exact (hsep p q' hp h3 x hx ⟨hback, hforward⟩).elim
  · have hnegative := (nativeMorseIndex_eq_chart (S.data q').chart).symm.trans h6
    have hsplit := (S.data q').chart.finrank_negative_add_positive
    have hpositive : Module.finrank ℝ (S.data q').chart.PositiveCoordinates = 0 := by omega
    exact (S.no_connection_of_lower_positive_zero hf q' p (hqx.trans hxp)
      hpositive x ⟨hback, hforward⟩).elim

theorem backward_middle_endpoint
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (hsix : nativeMorseCount E f 6 = 1) (hsep : NoMiddleConnections S)
    (hindices : ∀ p : criticalPoints E f,
      nativeMorseIndex E f p = 0 ∨ nativeMorseIndex E f p = 3 ∨ nativeMorseIndex E f p = 6)
    (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 3)
    {x : M} (hx : x ∉ criticalPoints E f)
    (hforward : Tendsto (fun t => S.flow t x) atTop (𝓝 p.val)) :
    Tendsto (fun t => S.flow t x) atBot
      (𝓝 (S.toSurgeryWindows.last (S.toSurgeryWindows.count_pos hf)).val) := by
  obtain ⟨q, hq, b, hb, hback, -, -⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral
      S.zero S.descent S.distinct x
  let q' : criticalPoints E f := ⟨q, hq⟩
  obtain ⟨hpx, hxq⟩ := connection_heights S hf hx hback hforward
  rcases hindices q' with h0 | h3 | h6
  · have hnegative := (nativeMorseIndex_eq_chart (S.data q').chart).symm.trans h0
    exact (S.no_connection_of_upper_index_zero hf p q' (hpx.trans hxq)
      hnegative x ⟨hback, hforward⟩).elim
  · exact (hsep q' p h3 hp x hx ⟨hback, hforward⟩).elim
  · have he := critical_eq_of_count_one hsix q' _ h6 (last_native_index S hf hdim)
    exact he ▸ hback

theorem attaching_forward_minimum
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (hzero : nativeMorseCount E f 0 = 1) (hsep : NoMiddleConnections S)
    (hindices : ∀ p : criticalPoints E f,
      nativeMorseIndex E f p = 0 ∨ nativeMorseIndex E f p = 3 ∨ nativeMorseIndex E f p = 6)
    (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 3)
    (u : sphere (0 : (S.data p).chart.NegativeCoordinates) 1) :
    Tendsto (fun t => S.flow t ((S.data p).surgery.attachingSphere u).val) atTop
      (𝓝 (S.toSurgeryWindows.first (S.toSurgeryWindows.count_pos hf)).val) :=
  forward_middle_endpoint S hf hdim hzero hsep hindices p hp
    ((S.data p).lower_regular _ ((S.data p).surgery.attachingSphere u).property)
    ((S.attaching_basin_iff hf p _).mpr ⟨u, rfl⟩)

theorem belt_backward_maximum
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (hsix : nativeMorseCount E f 6 = 1) (hsep : NoMiddleConnections S)
    (hindices : ∀ p : criticalPoints E f,
      nativeMorseIndex E f p = 0 ∨ nativeMorseIndex E f p = 3 ∨ nativeMorseIndex E f p = 6)
    (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 3)
    (u : sphere (0 : (S.data p).chart.PositiveCoordinates) 1) :
    Tendsto (fun t => S.flow t ((S.data p).surgery.beltSphere u).val) atBot
      (𝓝 (S.toSurgeryWindows.last (S.toSurgeryWindows.count_pos hf)).val) :=
  backward_middle_endpoint S hf hdim hsix hsep hindices p hp
    ((S.data p).upper_regular _ ((S.data p).surgery.beltSphere u).property)
    ((S.belt_basin_iff hf p _).mpr ⟨u, rfl⟩)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality
