import Wikipedia.NoExoticSixSphere.InjectiveOperatorDimensionParity
import Wikipedia.NoExoticSixSphere.InjectiveOperatorBlockExtension

/-!
# Identity-block stabilization reflects actual sphere homotopies

The exact extension comparison preserves frame parity. Completeness of that
parity therefore reflects homotopies of two sphere maps, not merely
nullhomotopies. This uses the proved three-complement frame computation.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.Monomorphism

open GLOrthonormalization

theorem sphereParityOfDimension_block {N n : ℕ} (r : ℕ)
    (hN : N = 3 + (r + 2)) (hn : n = r + 2) (m : ℕ) (f : C(Sphere 3, Space N n)) :
    sphereParityOfDimension (r + m) (by omega) (by omega) ((blockMap m).comp f) =
      sphereParityOfDimension r hN hn f := by
  apply zmodTwo_eq_of_zero_iff
  rw [sphereParityOfDimension_zero_iff, sphereParityOfDimension_zero_iff]
  exact extends_blockMap_iff (by omega) (by omega) m f

theorem blockMap_homotopic_iff {N n : ℕ} (hn : 2 ≤ n) (hN : N = 3 + n)
    (m : ℕ) (f g : C(Sphere 3, Space N n)) :
    ((blockMap m).comp f).Homotopic ((blockMap m).comp g) ↔ f.Homotopic g := by
  let r := n - 2
  have hr : n = r + 2 := by omega
  have hR : N = 3 + (r + 2) := by omega
  rw [← sphereParityOfDimension_eq_iff (r + m) (by omega) (by omega),
    sphereParityOfDimension_block r hR hr m f, sphereParityOfDimension_block r hR hr m g]
  exact sphereParityOfDimension_eq_iff r hR hr f g

end NoExoticSixSphere.Stiefel.Monomorphism
