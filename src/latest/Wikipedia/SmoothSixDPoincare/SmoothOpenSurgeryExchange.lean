import Wikipedia.SmoothSixDPoincare.SmoothOpenPolarCoordinates

/-!
# The original radial surgery exchange is smooth on its open overlap

Both directions are compositions of native polar and product
diffeomorphisms. The resulting vector coordinates agree exactly with the
existing closed punctured-piece exchange.
-/

noncomputable section

open Set Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.PuncturedHandle

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (m n : ℕ) [Fact (Module.finrank ℝ E = m + 1)] [Fact (Module.finrank ℝ F = n + 1)]

def openExchange : Diffeomorph ((𝓡 m).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod (𝓡 n))
    (UnitSphere E × openPuncturedDisk F) (openPuncturedDisk E × UnitSphere F) ∞ := by
  let T : (UnitSphere E × openPuncturedDisk F) ≃ (openPuncturedDisk E × UnitSphere F) :=
    ((Equiv.refl (UnitSphere E)).prodCongr (openPolarEquiv F)).trans
      (((Equiv.refl (UnitSphere E)).prodCongr
        (Equiv.prodComm (UnitSphere F) openRadius)).trans
          ((Equiv.prodAssoc (UnitSphere E) openRadius (UnitSphere F)).symm.trans
            ((openPolarEquiv E).symm.prodCongr (Equiv.refl (UnitSphere F)))))
  have hu : ContMDiff (𝓡 m) 𝓘(ℝ, E) ∞ (Subtype.val : UnitSphere E → E) :=
    contMDiff_coe_sphere (n := m)
  have hv : ContMDiff (𝓡 n) 𝓘(ℝ, F) ∞ (Subtype.val : UnitSphere F → F) :=
    contMDiff_coe_sphere (n := n)
  refine { toEquiv := T, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · have hfirst : ContMDiff ((𝓡 m).prod 𝓘(ℝ, F)) 𝓘(ℝ, E) ∞
        (fun z => (T z).1) := by
      apply (ContMDiff.subtypeVal_comp_iff (openPuncturedDisk E) _).mp
      exact ((contMDiff_openDisk_norm (E := F)).comp contMDiff_snd).smul
        (hu.comp contMDiff_fst)
    have hsecond : ContMDiff ((𝓡 m).prod 𝓘(ℝ, F)) (𝓡 n) ∞ (fun z => (T z).2) :=
      contMDiff_fst.comp ((openPolarDiffeomorph (E := F) n).contMDiff.comp contMDiff_snd)
    exact hfirst.prodMk hsecond
  · have hp : ContMDiff (𝓘(ℝ, E).prod (𝓡 n)) ((𝓡 m).prod 𝓘(ℝ, ℝ)) ∞
        (fun z : openPuncturedDisk E × UnitSphere F => openPolarDiffeomorph (E := E) m z.1) :=
      (openPolarDiffeomorph (E := E) m).contMDiff.comp contMDiff_fst
    have hfirst : ContMDiff (𝓘(ℝ, E).prod (𝓡 n)) (𝓡 m) ∞ (fun z => (T.symm z).1) :=
      (contMDiff_fst.comp hp).congr (fun _ => rfl)
    have hsecond : ContMDiff (𝓘(ℝ, E).prod (𝓡 n)) 𝓘(ℝ, F) ∞
        (fun z => (T.symm z).2) := by
      apply (ContMDiff.subtypeVal_comp_iff (openPuncturedDisk F) _).mp
      exact ((contMDiff_openDisk_norm (E := E)).comp contMDiff_fst).smul
        (hv.comp contMDiff_snd)
    exact hfirst.prodMk hsecond

theorem openExchange_fst (u : UnitSphere E) (v : openPuncturedDisk F) :
    (openExchange m n (u, v)).1.val = ‖v.val‖ • u.val := rfl

theorem openExchange_snd (u : UnitSphere E) (v : openPuncturedDisk F) :
    (openExchange m n (u, v)).2.val = ‖v.val‖⁻¹ • v.val := rfl

theorem norm_openExchange_fst (u : UnitSphere E) (v : openPuncturedDisk F) :
    ‖(openExchange m n (u, v)).1.val‖ = ‖v.val‖ := by
  exact norm_openPoint u ⟨‖v.val‖, norm_pos_iff.mpr v.property.1, v.property.2⟩

theorem openExchange_symm_fst (u : openPuncturedDisk E) (v : UnitSphere F) :
    ((openExchange m n).symm (u, v)).1.val = ‖u.val‖⁻¹ • u.val := rfl

theorem openExchange_symm_snd (u : openPuncturedDisk E) (v : UnitSphere F) :
    ((openExchange m n).symm (u, v)).2.val = ‖u.val‖ • v.val := rfl

theorem openExchange_agrees_with_exchange (u : UnitSphere E) (v : openPuncturedDisk F) :
    (exchange E F (u, ⟨v.val, v.property.1, v.property.2.le⟩)).1.val =
        (openExchange m n (u, v)).1.val ∧
      (exchange E F (u, ⟨v.val, v.property.1, v.property.2.le⟩)).2 =
        (openExchange m n (u, v)).2 := ⟨rfl, rfl⟩

end Wikipedia.SmoothSixDPoincare.PuncturedHandle
