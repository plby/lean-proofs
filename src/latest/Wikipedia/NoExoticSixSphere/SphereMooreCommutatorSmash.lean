import Wikipedia.NoExoticSixSphere.SphereMooreCommutatorExtension
import Wikipedia.NoExoticSixSphere.JamesSphereSecondStage

/-!
# The constructed sphere-loop commutator descends to the actual smash sphere

The original sphere pairing collapses exactly the fat wedge and has
singleton other fibers. The terminal map of the constructed homotopy
is therefore constant on every pairing fiber and descends continuously.
Its pole value and the original commutator factorization up to based
homotopy are proved on the actual sphere coordinates.
-/

noncomputable section

open Topology
open scoped unitInterval

namespace NoExoticSixSphere.SphereMooreCommutator

theorem arrayPairing_pole_iff (n : ℕ) (v : Parameter n) :
    JamesSphere.SecondStage.arrayPairing n v = spherePole (n + n) ↔ v ∈ Boundary n := by
  change JamesSphere.pairing n (v 0, v 1) = _ ↔ ∃ i : Fin 2, v i = spherePole n
  rw [JamesSphere.pairing_eq_pole_iff]
  constructor
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi

theorem arrayPairing_surjective (n : ℕ) :
    Function.Surjective (JamesSphere.SecondStage.arrayPairing n) := by
  intro x
  obtain ⟨p, hp⟩ := JamesSphere.pairing_surjective n x
  exact ⟨![p.1, p.2], hp⟩

theorem isQuotientMap_arrayPairing (n : ℕ) :
    IsQuotientMap (JamesSphere.SecondStage.arrayPairing n) :=
  IsQuotientMap.of_surjective_continuous (arrayPairing_surjective n)
    (JamesSphere.SecondStage.arrayPairing n).continuous

variable (n : ℕ) {Y : Type} [TopologicalSpace Y] {y₀ : Y}
  (f g : C(Sphere n, Moore.Loop y₀))
  (hf : f (spherePole n) = 1) (hg : g (spherePole n) = 1)

theorem terminal_respects_pairing (v w : Parameter n)
    (h : JamesSphere.SecondStage.arrayPairing n v = JamesSphere.SecondStage.arrayPairing n w) :
    terminal n f g hf hg v = terminal n f g hf hg w := by
  rcases JamesSphere.pairing_fiber_condition n (v 0, v 1) (w 0, w 1) h with hp | hp
  · have hv := (arrayPairing_pole_iff n v).mp hp
    have hw := (arrayPairing_pole_iff n w).mp (h.symm.trans hp)
    exact (terminal_boundary n f g hf hg ⟨v, hv⟩).trans
      (terminal_boundary n f g hf hg ⟨w, hw⟩).symm
  · have hvw : v = w := by
      funext i
      fin_cases i
      · exact congrArg Prod.fst hp
      · exact congrArg Prod.snd hp
    exact congrArg (terminal n f g hf hg) hvw

def smashMap : C(Sphere (n + n), Moore.Loop y₀) :=
  IsQuotientMap.lift (f := JamesSphere.SecondStage.arrayPairing n)
    (isQuotientMap_arrayPairing n) (terminal n f g hf hg) (terminal_respects_pairing n f g hf hg)

theorem smashMap_pairing (v : Parameter n) :
    smashMap n f g hf hg (JamesSphere.SecondStage.arrayPairing n v) = terminal n f g hf hg v :=
  ContinuousMap.congr_fun (IsQuotientMap.lift_comp (isQuotientMap_arrayPairing n)
    (terminal n f g hf hg) (terminal_respects_pairing n f g hf hg)) v

theorem smashMap_pole : smashMap n f g hf hg (spherePole (n + n)) = 1 := by
  have hp : JamesSphere.SecondStage.arrayPairing n (point n) = spherePole (n + n) :=
    (arrayPairing_pole_iff n (point n)).mpr (boundaryPoint n).property
  rw [← hp, smashMap_pairing]
  exact terminal_boundary n f g hf hg (boundaryPoint n)

def factorHomotopy : (commutator n f g).HomotopyRel
    ((smashMap n f g hf hg).comp (JamesSphere.SecondStage.arrayPairing n)) {point n} :=
  (extensionHomotopy n f g hf hg).cast rfl
    (ContinuousMap.ext (fun v ↦ (smashMap_pairing n f g hf hg v).symm))

end NoExoticSixSphere.SphereMooreCommutator
