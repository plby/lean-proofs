import ErdosProblems.Erdos19.VizingKempe

/-! # Increasing a partial edge coloring by fan rotation and Kempe interchange -/

namespace Erdos19.Vizing

open Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

/-- The augmentation only needs missing colors at the center and its
neighbors; a global degree bound is not necessary. -/
theorem exists_improvement_of_missing_neighbors (G : SimpleGraph V) {K : Type*}
    [DecidableEq K] (C : PartialColoring V K)
    (hC : IsProper G C) (x y : V) (hxy : G.Adj x y) (hzero : C s(x, y) = none)
    (hxmissing : ∃ a, Missing G C x a)
    (hneighmissing : ∀ v, G.Adj x v → ∃ a, Missing G C v a) :
    ∃ C' : PartialColoring V K, IsProper G C' ∧
      (coloredEdges G C).card < (coloredEdges G C').card := by
  classical
  obtain ⟨a, hax⟩ := hxmissing
  obtain ⟨n, F, hmax⟩ := exists_maximal_fan G C hxy
  obtain ⟨b, hblast⟩ := hneighmissing (F.vert (Fin.last n)) (F.adj _)
  by_cases hbx : Missing G C x b
  · exact F.exists_rotation_improvement hC hzero b hbx hblast
  · obtain ⟨z, hxz, hzb⟩ := Classical.not_not.mp
      ((missing_iff_not_exists G C x b).not.mp hbx)
    have hz : z ∈ Set.range F.vert := by
      by_contra hz
      exact hmax z hxz hz b hzb hblast
    obtain ⟨j, rfl⟩ := hz
    have hj : j ≠ 0 := by
      intro hj
      have hnone : C s(x, F.vert j) = none := by simpa [hj, F.first] using hzero
      rw [hnone] at hzb
      contradiction
    obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hj
    have hbprev : Missing G C (F.vert k.castSucc) b := by
      obtain ⟨b₀, hb₀, hmissing⟩ := F.step k
      have hb : b₀ = b := Option.some.inj (hb₀.symm.trans hzb)
      exact hb ▸ hmissing
    have hdistinct : F.vert k.castSucc ≠ F.vert (Fin.last n) := by
      intro h
      have hi := F.injective h
      have hval := congrArg (fun i : Fin (n + 1) ↦ i.val) hi
      have hk := k.isLt
      change k.val = n at hval
      omega
    obtain ⟨Q, hxQ, hQ⟩ := exists_component_avoiding_center G C hC a b x
      (F.vert k.castSucc) (F.vert (Fin.last n)) (F.center_ne _) (F.center_ne _)
      hdistinct hax hbprev hblast
    let C₁ := kempeSwapOn G C a b Q
    have hC₁ : IsProper G C₁ := kempeSwapOn_proper G C hC a b Q
    have hax₁ : Missing G C₁ x a := missing_kempeSwapOn_of_not_mem G C a b Q hxQ hax
    have hzero₁ : C₁ s(x, y) = none := by
      change kempeSwapOn G C a b Q s(x, y) = none
      rw [kempeSwapOn_incident_of_not_mem G C a b Q hxQ hxy]
      exact hzero
    by_cases hprevQ : F.vert k.castSucc ∈ Q.supp
    · let P := F.initialSegment k.castSucc
      have hbeta : ∀ i : Fin k.val, C s(x, P.vert i.succ) = some b →
          P.vert i.castSucc ∉ Q.supp := by
        intro i hi
        have hverts := hC (P.adj i.succ) (F.adj k.succ) hi hzb
        have hidx := F.injective hverts
        have hval := congrArg (fun j : Fin (n + 1) ↦ j.val) hidx
        change i.val + 1 = k.val + 1 at hval
        have hiLt := i.isLt
        omega
      let P₁ := P.afterKempe a b Q hxQ hax hbeta
      have hlast : Missing G C₁ (P₁.vert (Fin.last k.val)) a := by
        have h := missing_kempeSwapOn_right_of_mem G C a b Q hprevQ hbprev
        change Missing G (kempeSwapOn G C a b Q)
          ((F.initialSegment k.castSucc).vert (Fin.last k.castSucc.val)) a
        rw [Fan.initialSegment_last]
        exact h
      obtain ⟨C₂, hC₂, himprove⟩ := P₁.exists_rotation_improvement hC₁ hzero₁ a hax₁ hlast
      exact ⟨C₂, hC₂, by simpa only [coloredEdges_kempeSwapOn] using himprove⟩
    · have hlastQ : F.vert (Fin.last n) ∈ Q.supp := hQ.resolve_left hprevQ
      have hbeta : ∀ i : Fin n, C s(x, F.vert i.succ) = some b →
          F.vert i.castSucc ∉ Q.supp := by
        intro i hi
        have heq : i = k := Fin.succ_inj.mp (F.injective
          (hC (F.adj i.succ) (F.adj k.succ) hi hzb))
        simpa only [heq] using hprevQ
      let F₁ := F.afterKempe a b Q hxQ hax hbeta
      have hlast : Missing G C₁ (F₁.vert (Fin.last n)) a :=
        missing_kempeSwapOn_right_of_mem G C a b Q hlastQ hblast
      obtain ⟨C₂, hC₂, himprove⟩ := F₁.exists_rotation_improvement hC₁ hzero₁ a hax₁ hlast
      exact ⟨C₂, hC₂, by simpa only [coloredEdges_kempeSwapOn] using himprove⟩

theorem exists_improvement_of_uncolored (G : SimpleGraph V) (D : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D) (C : PartialColoring V (Fin (D + 1)))
    (hC : IsProper G C) (x y : V) (hxy : G.Adj x y) (hzero : C s(x, y) = none) :
    ∃ C' : PartialColoring V (Fin (D + 1)), IsProper G C' ∧
      (coloredEdges G C).card < (coloredEdges G C').card :=
  exists_improvement_of_missing_neighbors G C hC x y hxy hzero
    (exists_missing G D hdegree hC x) (fun v _ ↦ exists_missing G D hdegree hC v)

/-- A maximum proper partial coloring with `D + 1` colors has no uncolored
edge. This is the finite Vizing theorem in partial-coloring form. -/
theorem exists_complete_proper_coloring (G : SimpleGraph V) (D : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D) :
    ∃ C : PartialColoring V (Fin (D + 1)), IsProper G C ∧
      ∀ x y, G.Adj x y → ∃ a, C s(x, y) = some a := by
  classical
  let good : Finset (PartialColoring V (Fin (D + 1))) := univ.filter (IsProper G)
  have hgood : good.Nonempty := by
    refine ⟨fun _ ↦ none, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    intro u v w a _ _ h _
    contradiction
  obtain ⟨C, hCgood, hmax⟩ := exists_max_image good (fun C ↦ (coloredEdges G C).card) hgood
  have hC : IsProper G C := (mem_filter.mp hCgood).2
  refine ⟨C, hC, ?_⟩
  intro x y hxy
  cases hc : C s(x, y) with
  | none =>
    obtain ⟨C', hC', hmore⟩ := exists_improvement_of_uncolored G D hdegree C hC x y hxy hc
    exact (Nat.not_lt_of_ge (hmax C' (mem_filter.mpr ⟨mem_univ _, hC'⟩)) hmore).elim
  | some a => exact ⟨a, rfl⟩

#print axioms exists_improvement_of_uncolored
#print axioms exists_improvement_of_missing_neighbors
#print axioms exists_complete_proper_coloring

end Erdos19.Vizing
