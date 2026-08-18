/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section4UniformVolumeDecay

/-!
# Terminal Sections 9--4 source assembly

The Section 4 uniform selection package returns only a reduced outer body.
The canonical coefficient construction then supplies the complete source
doubling clause, and the source-range affine-slice theorem produces the
final sorted Freiman container.
-/

namespace Erdos186.CFP.Bilu.Section94TerminalAssembly

open CFP.BiluFreiman
open Section4UniformVolumeDecay
open Section94ReducedCoordinates
open Section94RpowContainerAssembly
open Section9ContainerIntegration

noncomputable section

set_option autoImplicit false

/-- A concrete uniform Section 4 decay package is sufficient for the exact
public reduced-outer source statement. -/
theorem reducedOuterRealizationStatement_of_uniformVolumeDecay
    (hpackage : ∀ s d : ℕ, 0 < s → 0 < d →
      ∀ delta : ℝ, 0 < delta →
        Nonempty (UniformReducedOuterDecayPackage s d delta)) :
    ReducedOuterRealizationStatement :=
  reducedOuterRealizationStatement_of_existence
    (reducedOuterExistenceStatement_of_uniformVolumeDecay hpackage)

/-- The same concrete package family proves the complete source-facing
sorted-container statement. -/
theorem sortedFsContainerStatement_of_uniformVolumeDecay
    (hpackage : ∀ s d : ℕ, 0 < s → 0 < d →
      ∀ delta : ℝ, 0 < delta →
        Nonempty (UniformReducedOuterDecayPackage s d delta)) :
    SortedFsContainerStatement :=
  sortedFsContainerStatement_of_reducedOuterRealization
    (reducedOuterRealizationStatement_of_uniformVolumeDecay hpackage)

/-- End-to-end source bridge to the exact CFP Bilu--Freiman interface. -/
theorem biluFreimanStatement_of_uniformVolumeDecay
    (hpackage : ∀ s d : ℕ, 0 < s → 0 < d →
      ∀ delta : ℝ, 0 < delta →
        Nonempty (UniformReducedOuterDecayPackage s d delta)) :
    BiluFreimanStatement :=
  CFP.BiluFreiman.biluFreimanStatement_of_sortedFsContainer
    (sortedFsContainerStatement_of_uniformVolumeDecay hpackage)

end

end Erdos186.CFP.Bilu.Section94TerminalAssembly

#print axioms
  Erdos186.CFP.Bilu.Section94TerminalAssembly.reducedOuterRealizationStatement_of_uniformVolumeDecay
#print axioms
  Erdos186.CFP.Bilu.Section94TerminalAssembly.sortedFsContainerStatement_of_uniformVolumeDecay
#print axioms
  Erdos186.CFP.Bilu.Section94TerminalAssembly.biluFreimanStatement_of_uniformVolumeDecay
