import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Homotopy.Product

/-!
# The vertical kernel for loops in a product

For arbitrary topological spaces, a product loop whose first projection is
null-homotopic equals the vertical inclusion of its second projection.
The vertical map on loop homotopy classes is injective because the second
projection is a left inverse.  No connectedness assumption is needed.
-/

namespace Wikipedia.HopfProblem.DiagonalQuotient

variable {B F : Type*} [TopologicalSpace B] [TopologicalSpace F]

/-- A product loop with trivial first-coordinate class is exactly the
vertical inclusion of its second-coordinate class. -/
theorem product_loop_eq_vertical_of_fst_eq_refl (b : B) (c : F)
    (α : Path.Homotopic.Quotient (b, c) (b, c))
    (h : α.map ⟨Prod.fst, continuous_fst⟩ = .refl b) :
    α = (α.map ⟨Prod.snd, continuous_snd⟩).map
      ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩ := by
  have hv (β : Path.Homotopic.Quotient c c) :
      Path.Homotopic.prod (.refl b) β =
        β.map ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩ := by
    induction β using Path.Homotopic.Quotient.ind with
    | mk p => rfl
  calc
    α = Path.Homotopic.prod (α.map ⟨Prod.fst, continuous_fst⟩)
        (α.map ⟨Prod.snd, continuous_snd⟩) :=
      (Path.Homotopic.prod_projLeft_projRight α).symm
    _ = Path.Homotopic.prod (.refl b) (α.map ⟨Prod.snd, continuous_snd⟩) := by rw [h]
    _ = (α.map ⟨Prod.snd, continuous_snd⟩).map
        ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩ := hv _

/-- The vertical inclusion induces an injective map on loop homotopy
classes, with no connectedness assumptions on either factor. -/
theorem product_vertical_loop_map_injective (b : B) (c : F) :
    Function.Injective (fun β : Path.Homotopic.Quotient c c =>
      β.map ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩) := by
  have hleft (β : Path.Homotopic.Quotient c c) :
      (β.map ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩).map
        ⟨Prod.snd, continuous_snd⟩ = β := by
    induction β using Path.Homotopic.Quotient.ind with
    | mk p => rfl
  intro α β h
  have hs := congrArg (fun γ : Path.Homotopic.Quotient (b, c) (b, c) =>
    γ.map ⟨Prod.snd, continuous_snd⟩) h
  exact (hleft α).symm.trans (hs.trans (hleft β))

end Wikipedia.HopfProblem.DiagonalQuotient
