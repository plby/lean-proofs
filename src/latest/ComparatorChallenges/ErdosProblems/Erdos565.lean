import Mathlib

noncomputable section


namespace Erdos565

open scoped Classical in
def IsMonochromaticEmbedding {n m : ℕ} (G : SimpleGraph (Fin n))
    (H : SimpleGraph (Fin m)) (coloring : H.EdgeLabeling (Fin 2))
    (color : Fin 2) (f : G ↪g H) : Prop :=
  ∀ e : G.edgeSet, coloring (f.mapEdgeSet e) = color

end Erdos565

namespace Erdos565

open scoped Classical in
def MonochromaticInducedCopy {n m : ℕ} (G : SimpleGraph (Fin n))
    (H : SimpleGraph (Fin m)) (coloring : H.EdgeLabeling (Fin 2)) : Prop :=
  ∃ (color : Fin 2) (f : G ↪g H),
    IsMonochromaticEmbedding G H coloring color f

end Erdos565

namespace Erdos565

open scoped Classical in
def IsInducedRamseyWitness {n m : ℕ} (G : SimpleGraph (Fin n))
    (H : SimpleGraph (Fin m)) : Prop :=
  ∀ coloring : H.EdgeLabeling (Fin 2), MonochromaticInducedCopy G H coloring

end Erdos565

namespace Erdos565

open scoped Classical in
def IsInducedRamseyOrder {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) : Prop :=
  ∃ H : SimpleGraph (Fin m), IsInducedRamseyWitness G H

end Erdos565

namespace Erdos565

open scoped Classical in
def HasInducedRamseyOrderAtMost {n : ℕ} (G : SimpleGraph (Fin n))
    (bound : ℕ) : Prop :=
  ∃ m ≤ bound, IsInducedRamseyOrder G m

end Erdos565

namespace Erdos565

open scoped Classical in
theorem erdos_565 (n : ℕ) (G : SimpleGraph (Fin n)) :
    HasInducedRamseyOrderAtMost G (2 ^ (3000 * n)) := by
  sorry

end Erdos565

end
