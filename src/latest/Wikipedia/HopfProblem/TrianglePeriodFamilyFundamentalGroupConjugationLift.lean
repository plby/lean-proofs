import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportTopology

/-!
# The actual lifted product homotopy in a diagonal quotient

Lift a based loop through the given base covering and retain the fibre
coordinate.  Quotienting the resulting family gives a homotopy from the
original fibre inclusion to its translate by the inverse endpoint deck
element.  This is the genuine square used for fundamental-group conjugation.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.DiagonalQuotient

variable {G B F : Type*} [Group G] [MulAction G B] [MulAction G F]
    [TopologicalSpace B] [TopologicalSpace F] [ContinuousConstSMul G F]

/-- The quotient of the actual lifted base path times the whole fibre.
Its endpoint identification is the diagonal quotient identity, not a
chosen monodromy or a transported topology. -/
def liftedFibreHomotopy
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (b : B) (γ : Path (baseQuotient G B b) (baseQuotient G B b)) (g : G)
    (hend : (hq.isCoveringMap.monodromy (.mk γ) ⟨b, rfl⟩ : B) = g⁻¹ • b) :
    ContinuousMap.Homotopy
      (⟨fibreInclusion G B F b, fibreInclusion_continuous G B F b⟩ :
        C(F, Space G B F))
      ⟨fun f : F => fibreInclusion G B F b (g • f),
        (fibreInclusion_continuous G B F b).comp (continuous_const_smul g)⟩ where
  toFun p := quotient G B F (hq.isCoveringMap.liftPath γ b γ.source p.1, p.2)
  continuous_toFun := (quotient_continuous G B F).comp
    (((hq.isCoveringMap.liftPath γ b γ.source).continuous.comp continuous_fst).prodMk
      continuous_snd)
  map_zero_left f := by
    change quotient G B F (hq.isCoveringMap.liftPath γ b γ.source 0, f) =
      quotient G B F (b, f)
    rw [hq.isCoveringMap.liftPath_zero]
  map_one_left f := by
    change quotient G B F ((hq.isCoveringMap.monodromy (.mk γ) ⟨b, rfl⟩ : B), f) =
      quotient G B F (b, g • f)
    rw [hend, quotient_smul_fst, inv_inv]

@[simp] theorem liftedFibreHomotopy_apply
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (b : B) (γ : Path (baseQuotient G B b) (baseQuotient G B b)) (g : G)
    (hend : (hq.isCoveringMap.monodromy (.mk γ) ⟨b, rfl⟩ : B) = g⁻¹ • b)
    (t : unitInterval) (f : F) :
    liftedFibreHomotopy (F := F) hq b γ g hend (t, f) =
      quotient G B F (hq.isCoveringMap.liftPath γ b γ.source t, f) := rfl

end Wikipedia.HopfProblem.DiagonalQuotient
