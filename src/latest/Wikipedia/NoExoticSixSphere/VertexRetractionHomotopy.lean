import Wikipedia.NoExoticSixSphere.OrthogonalVertexInterpolation
import Wikipedia.NoExoticSixSphere.CompactTimeOpenCondition
import Mathlib.Topology.Homotopy.Basic

/-!
# A controlled homotopy to a vertex-space neighborhood retraction

The Cayley interpolation is restricted first to its open pair domain and then
to the open condition that every time lies in the prescribed target. The
resulting neighborhood still contains the retract, which is fixed pointwise.
-/

open Set
open scoped unitInterval

namespace NoExoticSixSphere.OrthogonalVertexSpace

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]

theorem exists_retraction_homotopy_neighborhood (U K W : Set (Space n m))
    (hU : IsOpen U) (hKU : K ⊆ U) (r : C(U, K))
    (hr : ∀ u : U, u.1 ∈ K → (r u).1 = u.1)
    (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ V : Set (Space n m), IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ∀ p : C(M, Space n m), (∀ x, p x ∈ V) →
        ∃ q : C(M, Space n m), (∀ x, q x ∈ K) ∧
          ∃ G : ContinuousMap.HomotopyRel p q (p ⁻¹' K), ∀ t x, G (t, x) ∈ W := by
  let rY : C(U, Space n m) := ⟨fun u ↦ (r u).1, continuous_subtype_val.comp r.continuous⟩
  let D : Set U := {u | (u.1, rY u) ∈ interpolationDomain n m}
  have hD : IsOpen D := isOpen_interpolationDomain n m |>.preimage
    (continuous_subtype_val.prodMk rY.continuous)
  let pD : C(D, Space n m) :=
    ⟨fun d ↦ d.1.1, continuous_subtype_val.comp continuous_subtype_val⟩
  let qD : C(D, Space n m) := rY.comp ⟨Subtype.val, continuous_subtype_val⟩
  have hpair : ∀ d : D, (pD d, qD d) ∈ interpolationDomain n m := fun d ↦ d.2
  let H : C(unitInterval × D, Space n m) :=
    ⟨fun z ↦ interpolate (z.1 : ℝ) (pD z.2) (qD z.2),
      (continuous_interpolate pD qD pD.continuous qD.continuous hpair).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)⟩
  let Good : Set D := {d | ∀ t, H (t, d) ∈ W}
  have hGood : IsOpen Good := isOpen_forall_compact_time H W hW
  let V : Set (Space n m) := Subtype.val '' (Subtype.val '' Good : Set U)
  have hV : IsOpen V := hU.isOpenMap_subtype_val _ (hD.isOpenMap_subtype_val _ hGood)
  have hVU : V ⊆ U := by
    rintro y ⟨u, _, rfl⟩
    exact u.2
  have hKV : K ⊆ V := by
    intro y hy
    let u : U := ⟨y, hKU hy⟩
    have hry : rY u = y := hr u hy
    have huD : u ∈ D := by
      change (y, rY u) ∈ interpolationDomain n m
      rw [hry]
      exact diagonal_mem_interpolationDomain y
    let d : D := ⟨u, huD⟩
    have hdGood : d ∈ Good := by
      intro t
      change interpolate (t : ℝ) y (rY u) ∈ W
      rw [hry, interpolate_self]
      exact hKW hy
    exact ⟨u, ⟨d, hdGood, rfl⟩, rfl⟩
  refine ⟨V, hV, hKV, hVU, ?_⟩
  intro p hp
  let pU : C(M, U) := ⟨fun x ↦ ⟨p x, hVU (hp x)⟩, p.continuous.subtype_mk _⟩
  have hlift (x : M) : ∃ d : D, d ∈ Good ∧ d.1.1 = p x := by
    obtain ⟨u, ⟨d, hd, hdu⟩, hu⟩ := hp x
    exact ⟨d, hd, (congrArg Subtype.val hdu).trans hu⟩
  have hpD (x : M) : pU x ∈ D := by
    obtain ⟨d, _, hd⟩ := hlift x
    have he : pU x = d.1 := Subtype.ext hd.symm
    rw [he]
    exact d.2
  let pd : C(M, D) := ⟨fun x ↦ ⟨pU x, hpD x⟩, pU.continuous.subtype_mk _⟩
  have hpd (x : M) : pd x ∈ Good := by
    obtain ⟨d, hdGood, hd⟩ := hlift x
    have he : pd x = d := Subtype.ext (Subtype.ext hd.symm)
    rw [he]
    exact hdGood
  let q := qD.comp pd
  have hq (x : M) : q x ∈ K := (r (pU x)).2
  refine ⟨q, hq, ?_⟩
  let G : ContinuousMap.HomotopyRel p q (p ⁻¹' K) :=
    { toFun := fun z ↦ H (z.1, pd z.2)
      continuous_toFun := H.continuous.comp (continuous_fst.prodMk
        (pd.continuous.comp continuous_snd))
      map_zero_left := fun x ↦ interpolate_zero (p x) (q x)
      map_one_left := fun x ↦ interpolate_one (p x) (q x) (hpair (pd x))
      prop' := by
        intro t x hx
        change interpolate (t : ℝ) (p x) (r (pU x)).1 = p x
        rw [hr (pU x) hx]
        exact interpolate_self (t : ℝ) (p x) }
  exact ⟨G, fun t x ↦ hpd x t⟩

end NoExoticSixSphere.OrthogonalVertexSpace
