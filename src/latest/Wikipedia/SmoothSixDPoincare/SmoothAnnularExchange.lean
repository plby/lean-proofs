import Wikipedia.SmoothSixDPoincare.NativeMorseAnnularCoordinates

/-!
# The exact annular exchange is a native diffeomorphism

It exchanges sphere direction and nonzero normal radius without changing
the radius. Applying the same formula with the factors reversed is its
inverse. Both maps use the original native product smooth structures.
-/

noncomputable section

open Set Metric Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.MorseHandle

open PuncturedHandle

section Topological

variable {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def annularSwap (z : AnnularParameters N P) : AnnularParameters P N :=
  ((annularBeltCoordinates z).1, ⟨(annularBeltCoordinates z).2, by
    change (1 / 2 : ℝ) < ‖(annularBeltCoordinates z).2‖ ∧
      ‖(annularBeltCoordinates z).2‖ < (3 / 2 : ℝ)
    rw [norm_annularBeltCoordinates_snd]
    exact z.2.property⟩)

theorem annularSwap_norm (z : AnnularParameters N P) : ‖(annularSwap z).2.val‖ = ‖z.2.val‖ :=
  norm_annularBeltCoordinates_snd z

theorem annularSwap_swap (z : AnnularParameters N P) : annularSwap (annularSwap z) = z := by
  apply Prod.ext
  · apply Subtype.ext
    change ‖(annularSwap z).2.val‖⁻¹ • (‖z.2.val‖ • z.1.val) = z.1.val
    rw [annularSwap_norm, inv_smul_smul₀ (surgeryAnnulus_norm_pos z.2).ne']
  · apply Subtype.ext
    change ‖(annularSwap z).2.val‖ • (‖z.2.val‖⁻¹ • z.2.val) = z.2.val
    rw [annularSwap_norm, smul_inv_smul₀ (surgeryAnnulus_norm_pos z.2).ne']

end Topological

variable {N P : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]

theorem contMDiff_annularNorm : ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, ℝ) ∞
    (fun x : openSurgeryAnnulus N => ‖x.val‖) := by
  intro x
  exact (contDiffAt_norm ℝ (surgeryAnnulus_ne_zero x)).contMDiffAt.comp x
    contMDiff_subtype_val.contMDiffAt

theorem contMDiff_annularDirection (n : ℕ) [Fact (Module.finrank ℝ N = n + 1)] :
    ContMDiff 𝓘(ℝ, N) (𝓡 n) ∞ (annularDirection (V := N)) := by
  have h : ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, N) ∞
      (fun x : openSurgeryAnnulus N => ‖x.val‖⁻¹ • x.val) :=
    ((contMDiff_annularNorm (N := N)).inv₀
      (fun x => (surgeryAnnulus_norm_pos x).ne')).smul contMDiff_subtype_val
  exact h.codRestrict_sphere (n := n) (fun x => (annularDirection x).property)

theorem contMDiff_annularSwap (m n : ℕ)
    [Fact (Module.finrank ℝ N = m + 1)] [Fact (Module.finrank ℝ P = n + 1)] :
    ContMDiff ((𝓡 m).prod 𝓘(ℝ, P)) ((𝓡 n).prod 𝓘(ℝ, N)) ∞
      (annularSwap (N := N) (P := P)) := by
  have hfirst : ContMDiff ((𝓡 m).prod 𝓘(ℝ, P)) (𝓡 n) ∞
      (fun z : AnnularParameters N P => (annularSwap z).1) :=
    (contMDiff_annularDirection (N := P) n).comp contMDiff_snd
  have hsecond : ContMDiff ((𝓡 m).prod 𝓘(ℝ, P)) 𝓘(ℝ, N) ∞
      (fun z : AnnularParameters N P => (annularSwap z).2) := by
    apply (ContMDiff.subtypeVal_comp_iff (openSurgeryAnnulus N) _).mp
    have hu : ContMDiff (𝓡 m) 𝓘(ℝ, N) ∞ (Subtype.val : UnitSphere N → N) :=
      contMDiff_coe_sphere (n := m)
    exact ((contMDiff_annularNorm (N := P)).comp contMDiff_snd).smul
      (hu.comp contMDiff_fst)
  exact hfirst.prodMk hsecond

def annularExchange (m n : ℕ)
    [Fact (Module.finrank ℝ N = m + 1)] [Fact (Module.finrank ℝ P = n + 1)] :
    Diffeomorph ((𝓡 m).prod 𝓘(ℝ, P)) ((𝓡 n).prod 𝓘(ℝ, N))
      (AnnularParameters N P) (AnnularParameters P N) ∞ where
  toFun := annularSwap
  invFun := annularSwap
  left_inv := annularSwap_swap
  right_inv := annularSwap_swap
  contMDiff_toFun := contMDiff_annularSwap m n
  contMDiff_invFun := contMDiff_annularSwap n m

theorem annularExchange_coordinates (m n : ℕ)
    [Fact (Module.finrank ℝ N = m + 1)] [Fact (Module.finrank ℝ P = n + 1)]
    (z : AnnularParameters N P) :
    ((annularExchange m n z).1, (annularExchange m n z).2.val) = annularBeltCoordinates z := rfl

end Wikipedia.SmoothSixDPoincare.MorseHandle
