/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.DistortingMeasure
import ErdosProblems.Erdos186.CFP.BiluFreiman

/-!
# Initializing Bilu's lattice construction from an integer set

The source theorem starts with `A ⊂ ℤ`, while Sections 7--9 use a finite
set `K ⊂ ℤ^m`.  At the initial stage `m = 1`: an integer is sent to the
constant coordinate on `Fin 1`.  This file proves that the embedding loses
neither cardinality nor any double-sum information, including the exact
real-valued doubling inequality used by the `rpow` branch.
-/

namespace Erdos186.CFP.Bilu.Section90IntegerInitialization

open CFP.BiluFreiman
open DistortingMeasure

noncomputable section

/-- The canonical identification of an integer with a point of the
one-dimensional integral lattice. -/
def singletonPoint (a : ℤ) : Fin 1 → ℤ :=
  fun _ ↦ a

@[simp]
theorem singletonPoint_apply (a : ℤ) (i : Fin 1) :
    singletonPoint a i = a := rfl

@[simp]
theorem singletonPoint_zero : singletonPoint 0 = 0 := by
  ext i
  simp [singletonPoint]

@[simp]
theorem singletonPoint_add (a b : ℤ) :
    singletonPoint (a + b) = singletonPoint a + singletonPoint b := by
  ext i
  simp [singletonPoint]

theorem singletonPoint_injective : Function.Injective singletonPoint := by
  intro a b hab
  have h := congrFun hab (0 : Fin 1)
  exact h

/-- The literal initial lattice set `K ⊂ ℤ^1`. -/
def integerSet (A : Finset ℤ) : Finset (Fin 1 → ℤ) :=
  A.image singletonPoint

@[simp]
theorem mem_integerSet {A : Finset ℤ} {x : Fin 1 → ℤ} :
    x ∈ integerSet A ↔ ∃ a ∈ A, singletonPoint a = x := by
  exact Finset.mem_image

@[simp]
theorem card_integerSet (A : Finset ℤ) :
    (integerSet A).card = A.card := by
  exact Finset.card_image_of_injective A singletonPoint_injective

theorem integerSet_nonempty {A : Finset ℤ} (hA : A.Nonempty) :
    (integerSet A).Nonempty :=
  hA.image singletonPoint

/-- The lattice double sumset is exactly the image of the original
integer double sumset. -/
theorem sumset_integerSet (A : Finset ℤ) :
    DistortingMeasure.sumset (integerSet A) =
      (twoA A).image singletonPoint := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_image₂.mp hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    rw [← singletonPoint_add] at huv
    exact Finset.mem_image.mpr
      ⟨a + b, mem_twoA_iff.mpr ⟨a, ha, b, hb, rfl⟩, huv⟩
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨a, ha, b, hb, hab⟩ := mem_twoA_iff.mp hz
    rw [← hab, singletonPoint_add]
    exact Finset.mem_image₂.mpr
      ⟨singletonPoint a, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
        singletonPoint b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, rfl⟩

@[simp]
theorem card_sumset_integerSet (A : Finset ℤ) :
    (DistortingMeasure.sumset (integerSet A)).card = (twoA A).card := by
  rw [sumset_integerSet]
  exact Finset.card_image_of_injective _ singletonPoint_injective

/-- The exact source-range doubling inequality transports to the
one-dimensional lattice initialization. -/
theorem doubling_integerSet {A : Finset ℤ} {C : ℝ}
    (hdouble : ((twoA A).card : ℝ) ≤ C * A.card) :
    ((DistortingMeasure.sumset (integerSet A)).card : ℝ) ≤
      C * (integerSet A).card := by
  simpa using hdouble

end

end Erdos186.CFP.Bilu.Section90IntegerInitialization

#print axioms Erdos186.CFP.Bilu.Section90IntegerInitialization.sumset_integerSet
#print axioms Erdos186.CFP.Bilu.Section90IntegerInitialization.doubling_integerSet
