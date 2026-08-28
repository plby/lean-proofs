import Wikipedia.NoExoticSixSphere.SphereBasedHomotopyComparison
import Mathlib.Topology.UrysohnsLemma

/-!
# Correcting a sphere homotopy at finitely many marked points

A nullhomotopy of the loop at a new marked point lifts to an orthogonal
homotopy which is the identity on three edges. A source cutoff localizes
the inverse rotation away from the already fixed closed set. Both endpoint
maps remain exactly unchanged. Finite induction fixes all marked points.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace NoExoticSixSphere

open GLOrthonormalization OrthogonalPaths

variable {n : ℕ} [SimplyConnectedSpace (UnitSphere (Vector n))]

theorem exists_contractible_orthogonal_loop_lift (b : UnitSphere (Vector n)) (P : Path b b) :
    ∃ G : C(I × I, OrthogonalOperators n),
      (∀ t, G (0, t) = identity n) ∧
      (∀ s, G (s, 0) = identity n) ∧
      (∀ s, G (s, 1) = identity n) ∧
      ∀ t, (G (1, t)).val.val b.val = (P t).val := by
  obtain ⟨L⟩ := SimplyConnectedSpace.paths_homotopic (Path.refl b) P
  obtain ⟨A, G, hG⟩ := exists_exactColumnHomotopyRel L b
    (ContinuousMap.const I (identity n)) (fun _ ↦ rfl)
  refine ⟨G.toContinuousMap, G.apply_zero, ?_, ?_, ?_⟩
  · intro s
    exact G.eq_fst s (by simp)
  · intro s
    exact G.eq_fst s (by simp)
  · intro t
    have ht := hG 1 t
    rwa [L.apply_one] at ht

variable {X : Type*} [TopologicalSpace X] [NormalSpace X] [T1Space X]

theorem sphere_homotopicRel_insert_of_homotopyRel
    {f g : C(X, UnitSphere (Vector n))} {S : Set X} (hS : IsClosed S)
    (p : X) (hp : p ∉ S) (hbase : f p = g p) (H : f.HomotopyRel g S) :
    f.HomotopicRel g (insert p S) := by
  obtain ⟨β, hβS, hβp, hβbound⟩ := exists_continuous_zero_one_of_isClosed hS
    (isClosed_singleton (x := p)) (disjoint_singleton_right.mpr hp)
  let u : C(X, I) := ⟨fun x ↦ ⟨β x, hβbound x⟩, β.continuous.subtype_mk _⟩
  have huS (x : X) (hx : x ∈ S) : u x = 0 := Subtype.ext (hβS hx)
  have hup : u p = 1 := Subtype.ext (hβp (mem_singleton p))
  let b := f p
  let P : Path b b := {
    toFun := fun t ↦ H (t, p)
    continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
    source' := H.apply_zero p
    target' := (H.apply_one p).trans hbase.symm }
  obtain ⟨G, hG0, hGt0, hGt1, hGcol⟩ := exists_contractible_orthogonal_loop_lift b P
  let B : I × X → OrthogonalOperators n := fun q ↦ G (u q.2, q.1)
  have hB : Continuous B := G.continuous.comp
    ((u.continuous.comp continuous_snd).prodMk continuous_fst)
  let v : I × X → Vector n := fun q ↦ (inverse (B q)).val.val (H q).val
  have hv : Continuous v :=
    (continuous_subtype_val.comp
      (continuous_subtype_val.comp (continuous_inverse B hB))).clm_apply
        (continuous_subtype_val.comp H.continuous)
  have hunit (q : I × X) : v q ∈ UnitSphere (Vector n) := by
    rw [Metric.mem_sphere, dist_zero_right]
    exact ((inverse (B q)).property (H q).val).trans (ClosedHemisphere.unit_norm (H q))
  let K : C(I × X, UnitSphere (Vector n)) := ⟨fun q ↦ ⟨v q, hunit q⟩, hv.subtype_mk _⟩
  refine ⟨{ toContinuousMap := K, map_zero_left := ?_, map_one_left := ?_, prop' := ?_ }⟩
  · intro x
    apply Subtype.ext
    change (inverse (G (u x, 0))).val.val (H (0, x)).val = (f x).val
    rw [hGt0, inverse_identity, H.apply_zero]
    rfl
  · intro x
    apply Subtype.ext
    change (inverse (G (u x, 1))).val.val (H (1, x)).val = (g x).val
    rw [hGt1, inverse_identity, H.apply_one]
    rfl
  · intro t x hx
    rcases mem_insert_iff.mp hx with hx | hx
    · subst x
      apply Subtype.ext
      change (inverse (G (u p, t))).val.val (P t).val = b.val
      rw [hup, ← hGcol]
      exact inverse_apply_self _ _
    · apply Subtype.ext
      change (inverse (G (u x, t))).val.val (H (t, x)).val = (f x).val
      rw [huS x hx, hG0, inverse_identity, H.eq_fst t hx]
      rfl

theorem sphere_homotopicRel_finite_of_homotopic
    {f g : C(X, UnitSphere (Vector n))} (S : Set X) (hS : S.Finite)
    (hbase : EqOn f g S) (H : f.Homotopy g) : f.HomotopicRel g S := by
  revert hbase
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    intro _
    exact ContinuousMap.homotopicRel_empty.mpr ⟨H⟩
  | @insert p S hp hS ih =>
    intro hbase
    obtain ⟨K⟩ := ih (fun x hx ↦ hbase (mem_insert_of_mem p hx))
    exact sphere_homotopicRel_insert_of_homotopyRel hS.isClosed p hp
      (hbase (mem_insert p S)) K

theorem sphere_homotopicRel_finite_iff
    {f g : C(X, UnitSphere (Vector n))} (S : Set X) (hS : S.Finite)
    (hbase : EqOn f g S) : f.HomotopicRel g S ↔ f.Homotopic g := by
  constructor
  · exact ContinuousMap.HomotopicRel.homotopic
  · rintro ⟨H⟩
    exact sphere_homotopicRel_finite_of_homotopic S hS hbase H

end NoExoticSixSphere
