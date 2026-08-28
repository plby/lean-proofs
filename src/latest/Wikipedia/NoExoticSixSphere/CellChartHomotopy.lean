import Wikipedia.NoExoticSixSphere.CellChartCoordinates
import Wikipedia.NoExoticSixSphere.OpenMapHomotopyExtension
import Mathlib.Tactic.Abel

/-!
# A supported actual target homotopy inside an open Euclidean cell

The local coordinate interpolation is transported by the original cell
homeomorphism and extended by the unchanged map. It stays in that cell
exactly when the original value was in the cell. Outside the cell, and
where the cutoff vanishes, the entire homotopy is fixed.
-/

noncomputable section

open Set TopologicalSpace
open scoped unitInterval

namespace NoExoticSixSphere.CellChart

variable {X D : Type} [TopologicalSpace X] [TopologicalSpace D]
  (n : ℕ) (U : Opens X) (e : (Fin n → ℝ) ≃ₜ U)
  (f : C(D, X)) (g : C(D, (Fin n → ℝ)))

def localHomotopy : C(I × (f ⁻¹' (U : Set X)), X) :=
  (encode n U e).comp
    ⟨fun z ↦ coordinates n U e f z.2 + (z.1 : ℝ) •
      (g z.2.val - coordinates n U e f z.2),
      ((coordinates n U e f).continuous.comp continuous_snd).add
        ((continuous_subtype_val.comp continuous_fst).smul
          ((g.continuous.comp (continuous_subtype_val.comp continuous_snd)).sub
            ((coordinates n U e f).continuous.comp continuous_snd)))⟩

theorem localHomotopy_zero (z : f ⁻¹' (U : Set X)) :
    localHomotopy n U e f g (0, z) = f z.val := by
  change encode n U e (coordinates n U e f z + (0 : ℝ) •
    (g z.val - coordinates n U e f z)) = _
  rw [zero_smul, add_zero, encode_coordinates]

variable (β : C(D, ℝ)) (hβ : ∀ z, β z ∈ I)
  (hsupport : tsupport β ⊆ f ⁻¹' (U : Set X))

def updatedMap : C(D, X) :=
  OpenMapHomotopyExtension.endpoint f (localHomotopy n U e f g) β hβ
    (localHomotopy_zero n U e f g) (U.isOpen.preimage f.continuous) hsupport

def updateHomotopy : f.Homotopy (updatedMap n U e f g β hβ hsupport) :=
  OpenMapHomotopyExtension.homotopy f (localHomotopy n U e f g) β hβ
    (localHomotopy_zero n U e f g) (U.isOpen.preimage f.continuous) hsupport

theorem updateHomotopy_of_notMem (s : I) (z : D) (hz : f z ∉ U) :
    updateHomotopy n U e f g β hβ hsupport (s, z) = f z :=
  OpenMapHomotopyExtension.raw_of_notMem f (localHomotopy n U e f g) β hβ hz s

theorem updateHomotopy_of_zero (s : I) (z : D) (hz : β z = 0) :
    updateHomotopy n U e f g β hβ hsupport (s, z) = f z :=
  OpenMapHomotopyExtension.raw_of_zero f (localHomotopy n U e f g) β hβ
    (localHomotopy_zero n U e f g) hz s

theorem updateHomotopy_coordinates (s : I) (z : D) (hz : f z ∈ U) :
    updateHomotopy n U e f g β hβ hsupport (s, z) =
      encode n U e (coordinates n U e f ⟨z, hz⟩ + ((s : ℝ) * β z) •
        (g z - coordinates n U e f ⟨z, hz⟩)) :=
  OpenMapHomotopyExtension.raw_of_mem f (localHomotopy n U e f g) β hβ hz s

theorem updateHomotopy_mem_iff (s : I) (z : D) :
    updateHomotopy n U e f g β hβ hsupport (s, z) ∈ U ↔ f z ∈ U := by
  by_cases hz : f z ∈ U
  · rw [updateHomotopy_coordinates n U e f g β hβ hsupport s z hz]
    exact iff_of_true (encode_mem n U e _) hz
  · rw [updateHomotopy_of_notMem n U e f g β hβ hsupport s z hz]

theorem updatedMap_of_one (z : D) (hz : f z ∈ U) (hβz : β z = 1) :
    updatedMap n U e f g β hβ hsupport z = encode n U e (g z) := by
  change updateHomotopy n U e f g β hβ hsupport (1, z) = _
  rw [updateHomotopy_coordinates n U e f g β hβ hsupport 1 z hz]
  simp only [hβz, Set.Icc.coe_one, one_mul, one_smul]
  congr 1
  abel

end NoExoticSixSphere.CellChart
