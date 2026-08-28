import Wikipedia.NoExoticSixSphere.CompactTimeOpenCondition
import Mathlib.Topology.Homotopy.Basic

/-!
# Neighborhood retractions and local interpolation

A continuous interpolation defined near the diagonal, constant on the
diagonal, connects any neighborhood retraction to the inclusion. Shrinking
the source keeps the whole homotopy in a prescribed open neighborhood.
-/

open Set
open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.RetractionInterpolation

variable {Y M : Type*} [TopologicalSpace Y] [TopologicalSpace M]

theorem exists_homotopy_neighborhood (D : Set (Y × Y)) (hD : IsOpen D)
    (hdiag : ∀ y, (y, y) ∈ D) (s : C(unitInterval × D, Y))
    (hs0 : ∀ d : D, s (0, d) = d.1.1) (hs1 : ∀ d : D, s (1, d) = d.1.2)
    (hsdiag : ∀ (y : Y) (h : (y, y) ∈ D) (t : unitInterval), s (t, ⟨(y, y), h⟩) = y)
    (U K W : Set Y) (hU : IsOpen U) (hKU : K ⊆ U) (r : C(U, K))
    (hr : ∀ u : U, u.1 ∈ K → (r u).1 = u.1)
    (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ V : Set Y, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ∀ p : C(M, Y), (∀ x, p x ∈ V) →
        ∃ q : C(M, Y), (∀ x, q x ∈ K) ∧
          ∃ G : ContinuousMap.HomotopyRel p q (p ⁻¹' K), ∀ t x, G (t, x) ∈ W := by
  let rY : C(U, Y) := ⟨fun u ↦ (r u).1, continuous_subtype_val.comp r.continuous⟩
  let A : Set U := {u | (u.1, rY u) ∈ D}
  have hA : IsOpen A := hD.preimage (continuous_subtype_val.prodMk rY.continuous)
  let endpoints : C(A, D) :=
    ⟨fun a ↦ ⟨(a.1.1, rY a.1), a.2⟩,
      ((continuous_subtype_val.comp continuous_subtype_val).prodMk
        (rY.continuous.comp continuous_subtype_val)).subtype_mk _⟩
  let H : C(unitInterval × A, Y) := s.comp
    ⟨fun z ↦ (z.1, endpoints z.2),
      continuous_fst.prodMk (endpoints.continuous.comp continuous_snd)⟩
  have hH (a : A) (ha : (r a.1).1 = a.1.1) (t : unitInterval) : H (t, a) = a.1.1 := by
    have hself : (a.1.1, a.1.1) ∈ D := hdiag a.1.1
    have he : endpoints a = ⟨(a.1.1, a.1.1), hself⟩ := by
      apply Subtype.ext
      exact Prod.ext rfl ha
    change s (t, endpoints a) = a.1.1
    rw [he]
    exact hsdiag a.1.1 hself t
  let Good : Set A := {a | ∀ t, H (t, a) ∈ W}
  have hGood : IsOpen Good := NoExoticSixSphere.isOpen_forall_compact_time H W hW
  let V : Set Y := Subtype.val '' (Subtype.val '' Good : Set U)
  have hV : IsOpen V := hU.isOpenMap_subtype_val _ (hA.isOpenMap_subtype_val _ hGood)
  have hVU : V ⊆ U := by
    rintro y ⟨u, _, rfl⟩
    exact u.2
  have hKV : K ⊆ V := by
    intro y hy
    let u : U := ⟨y, hKU hy⟩
    have hry : rY u = y := hr u hy
    have huA : u ∈ A := by
      change (y, rY u) ∈ D
      rw [hry]
      exact hdiag y
    let a : A := ⟨u, huA⟩
    have haGood : a ∈ Good := by
      intro t
      rw [hH a hry t]
      exact hKW hy
    exact ⟨u, ⟨a, haGood, rfl⟩, rfl⟩
  refine ⟨V, hV, hKV, hVU, ?_⟩
  intro p hp
  let pU : C(M, U) := ⟨fun x ↦ ⟨p x, hVU (hp x)⟩, p.continuous.subtype_mk _⟩
  have hlift (x : M) : ∃ a : A, a ∈ Good ∧ a.1.1 = p x := by
    obtain ⟨u, ⟨a, ha, hau⟩, hu⟩ := hp x
    exact ⟨a, ha, (congrArg Subtype.val hau).trans hu⟩
  have hpA (x : M) : pU x ∈ A := by
    obtain ⟨a, _, ha⟩ := hlift x
    have he : pU x = a.1 := Subtype.ext ha.symm
    rw [he]
    exact a.2
  let pa : C(M, A) := ⟨fun x ↦ ⟨pU x, hpA x⟩, pU.continuous.subtype_mk _⟩
  have hpa (x : M) : pa x ∈ Good := by
    obtain ⟨a, haGood, ha⟩ := hlift x
    have he : pa x = a := Subtype.ext (Subtype.ext ha.symm)
    rw [he]
    exact haGood
  let q : C(M, Y) := rY.comp pU
  have hq (x : M) : q x ∈ K := (r (pU x)).2
  refine ⟨q, hq, ?_⟩
  let G : ContinuousMap.HomotopyRel p q (p ⁻¹' K) :=
    { toFun := fun z ↦ H (z.1, pa z.2)
      continuous_toFun := H.continuous.comp (continuous_fst.prodMk
        (pa.continuous.comp continuous_snd))
      map_zero_left := fun x ↦ hs0 (endpoints (pa x))
      map_one_left := fun x ↦ hs1 (endpoints (pa x))
      prop' := fun t x hx ↦ hH (pa x) (hr (pU x) hx) t }
  exact ⟨G, fun t x ↦ hpa x t⟩

end Wikipedia.HomotopyGroupsOfSpheres.RetractionInterpolation
