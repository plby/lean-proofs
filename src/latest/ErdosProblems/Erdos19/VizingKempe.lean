import ErdosProblems.Erdos19.VizingRotation

/-! # Kempe interchanges that preserve a full fan or an initial segment -/

namespace Erdos19.Vizing

variable {V K : Type*} [Fintype V] [DecidableEq K]

theorem missing_kempeSwapOn_right_of_mem (G : SimpleGraph V)
    (C : PartialColoring V K) (a b : K)
    (Q : (bichromGraph G C a b).ConnectedComponent) {v : V}
    (hv : v ∈ Q.supp) (hb : Missing G C v b) :
    Missing G (kempeSwapOn G C a b Q) v a := by
  intro w hvw
  rw [kempeSwapOn_incident_of_mem G C a b Q hv]
  intro h
  have hsame : swapOption a b (C s(v, w)) = swapOption a b (some b) := by simpa using h
  exact hb w hvw (swapOption_injective a b hsame)

theorem missing_kempeSwapOn_fixed (G : SimpleGraph V)
    (C : PartialColoring V K) (a b : K)
    (Q : (bichromGraph G C a b).ConnectedComponent) {v : V} {k : K}
    (hka : k ≠ a) (hkb : k ≠ b) (hk : Missing G C v k) :
    Missing G (kempeSwapOn G C a b Q) v k := by
  classical
  by_cases hv : v ∈ Q.supp
  · intro w hvw
    rw [kempeSwapOn_incident_of_mem G C a b Q hv]
    intro h
    have hfixed : swapOption a b (some k) = some k :=
      swapOption_fixed (by simpa using hka) (by simpa using hkb)
    exact hk w hvw (swapOption_injective a b (h.trans hfixed.symm))
  · exact missing_kempeSwapOn_of_not_mem G C a b Q hv hk

/-- Of two distinct outer endpoints missing `b`, at least one lies in a
two-color component avoiding the center that misses `a`. -/
theorem exists_component_avoiding_center (G : SimpleGraph V)
    (C : PartialColoring V K) (hC : IsProper G C) (a b : K) (x u v : V)
    (hxu : x ≠ u) (hxv : x ≠ v) (huv : u ≠ v)
    (hax : Missing G C x a) (hbu : Missing G C u b) (hbv : Missing G C v b) :
    ∃ Q : (bichromGraph G C a b).ConnectedComponent,
      x ∉ Q.supp ∧ (u ∈ Q.supp ∨ v ∈ Q.supp) := by
  classical
  let B := bichromGraph G C a b
  let Qx := B.connectedComponentMk x
  by_cases hu : u ∈ Qx.supp
  · have hv : v ∉ Qx.supp := fun hv ↦
      bichrom_component_not_three_missing G C hC Qx (by rfl) hu hv hxu hxv huv hax hbu hbv
    refine ⟨B.connectedComponentMk v, ?_, Or.inr (by rfl)⟩
    intro hx
    apply hv
    change B.connectedComponentMk x = B.connectedComponentMk v at hx
    change B.connectedComponentMk v = B.connectedComponentMk x
    exact hx.symm
  · refine ⟨B.connectedComponentMk u, ?_, Or.inl (by rfl)⟩
    intro hx
    apply hu
    change B.connectedComponentMk x = B.connectedComponentMk u at hx
    change B.connectedComponentMk u = B.connectedComponentMk x
    exact hx.symm

namespace Fan

variable {G : SimpleGraph V} {C : PartialColoring V K} {x y : V} {n : ℕ}

/-- A fan survives a Kempe interchange away from its center if every spoke
of color `b` has its predecessor outside the interchanged component. Color
`a` is missing at the center, so it cannot occur on a spoke. -/
def afterKempe (F : Fan G C x y n) (a b : K)
    (Q : (bichromGraph G C a b).ConnectedComponent) (hx : x ∉ Q.supp)
    (hax : Missing G C x a)
    (hbeta : ∀ i : Fin n, C s(x, F.vert i.succ) = some b → F.vert i.castSucc ∉ Q.supp) :
    Fan G (kempeSwapOn G C a b Q) x y n where
  vert := F.vert
  injective := F.injective
  first := F.first
  adj := F.adj
  step i := by
    obtain ⟨k, hk, hmissing⟩ := F.step i
    refine ⟨k, ?_, ?_⟩
    · rw [kempeSwapOn_incident_of_not_mem G C a b Q hx (F.adj i.succ)]
      exact hk
    · have hka : k ≠ a := by
        intro h
        exact hax (F.vert i.succ) (F.adj i.succ) (h ▸ hk)
      by_cases hkb : k = b
      · subst k
        exact missing_kempeSwapOn_of_not_mem G C a b Q (hbeta i hk) hmissing
      · exact missing_kempeSwapOn_fixed G C a b Q hka hkb hmissing

end Fan

#print axioms exists_component_avoiding_center
#print axioms Fan.afterKempe

end Erdos19.Vizing
