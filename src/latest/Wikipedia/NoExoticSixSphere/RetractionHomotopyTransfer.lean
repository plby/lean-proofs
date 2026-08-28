import Mathlib.Topology.Homotopy.Basic

/-!
# Transferring relative representatives and homotopy reflection to a retract
-/

open Set

namespace NoExoticSixSphere.RetractionHomotopyTransfer

variable {X M Y Z : Type*} [TopologicalSpace X] [TopologicalSpace M]
  [TopologicalSpace Y] [TopologicalSpace Z]

noncomputable def precompose {f g : C(M, Y)} {S : Set M}
    (F : f.HomotopyRel g S) (e : C(X, M)) :
    (f.comp e).HomotopyRel (g.comp e) (e ⁻¹' S) where
  toHomotopy := F.toHomotopy.compContinuousMap e
  prop' t _x hx := F.eq_fst t hx

theorem comp_retract (e : C(X, M)) (r : C(M, X)) (hre : r.comp e = ContinuousMap.id X)
    (f : C(X, Y)) : (f.comp r).comp e = f := by
  apply ContinuousMap.ext
  intro x
  exact congrArg f (ContinuousMap.congr_fun hre x)

theorem preimage_retract (e : C(X, M)) (r : C(M, X)) (hre : r.comp e = ContinuousMap.id X)
    (S : Set X) : e ⁻¹' (r ⁻¹' S) = S := by
  ext x
  change r (e x) ∈ S ↔ x ∈ S
  rw [show r (e x) = x from ContinuousMap.congr_fun hre x]

theorem representatives (e : C(X, M)) (r : C(M, X)) (hre : r.comp e = ContinuousMap.id X)
    (i : C(Y, Z))
    (hrep : ∀ p : C(M, Z), ∃ q : C(M, Y),
      Nonempty (p.HomotopyRel (i.comp q) (p ⁻¹' range i))) (p : C(X, Z)) :
    ∃ q : C(X, Y), Nonempty (p.HomotopyRel (i.comp q) (p ⁻¹' range i)) := by
  obtain ⟨q, ⟨G⟩⟩ := hrep (p.comp r)
  have hs : e ⁻¹' ((p.comp r) ⁻¹' range i) = p ⁻¹' range i :=
    preimage_retract e r hre (p ⁻¹' range i)
  have G' := (precompose G e).cast (comp_retract e r hre p) rfl
  rw [hs] at G'
  exact ⟨q.comp e, ⟨G'⟩⟩

theorem reflection (e : C(X, M)) (r : C(M, X)) (hre : r.comp e = ContinuousMap.id X)
    (i : C(Y, Z))
    (hreflect : ∀ f g : C(M, Y), ∀ S : Set M,
      Nonempty ((i.comp f).HomotopyRel (i.comp g) S) → Nonempty (f.HomotopyRel g S))
    (f g : C(X, Y)) (S : Set X)
    (F : (i.comp f).HomotopyRel (i.comp g) S) : Nonempty (f.HomotopyRel g S) := by
  obtain ⟨G⟩ := hreflect (f.comp r) (g.comp r) (r ⁻¹' S) ⟨precompose F r⟩
  have G' := (precompose G e).cast (comp_retract e r hre f) (comp_retract e r hre g)
  rw [preimage_retract e r hre S] at G'
  exact ⟨G'⟩

end NoExoticSixSphere.RetractionHomotopyTransfer
