import ErdosProblems.Erdos1188.Basic
import ErdosProblems.Erdos1188.Periodic

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Transporting finite private-point covers to congruence systems
-/

namespace Erdos1188

universe u v

variable {M : Type u} [Fintype M] [DecidableEq M]
variable {X : Type v}

/-- A finite indexed cover with private witnesses, represented as congruence
classes on one common period, transports to a minimal distinct covering system
of the integers. -/
theorem minimalDistinctCover_of_equiv
    {N : ℕ} (hN : 0 < N)
    (member : M → X → Prop)
    (witness : M → X)
    (hcover : ∀ x : X, ∃ m : M, member m x)
    (hprivate : ∀ m : M, member m (witness m) ∧
      ∀ d : M, member d (witness m) → d = m)
    (e : Fin N ≃ X)
    (cls : M → CongruenceClass)
    (hvalid : ∀ m : M, ValidClass (cls m))
    (hdiv : ∀ m : M, (cls m).1 ∣ N)
    (hmodinj : Function.Injective fun m : M => (cls m).1)
    (hcorr : ∀ (m : M) (r : Fin N),
      member m (e r) ↔ Satisfies (r.val : ℤ) (cls m)) :
    IsMinimalDistinctCoveringSystem (Finset.univ.image cls) := by
  classical
  let S : Finset CongruenceClass := Finset.univ.image cls
  have hcls_inj : Function.Injective cls := by
    intro a b hab
    apply hmodinj
    exact congrArg Prod.fst hab
  have hvalidS : ∀ c ∈ S, ValidClass c := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨m, -, rfl⟩
    exact hvalid m
  have hdivS : ∀ c ∈ S, c.1 ∣ N := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨m, -, rfl⟩
    exact hdiv m
  have hcoverResidues : CoversResidues N S := by
    intro r
    obtain ⟨m, hm⟩ := hcover (e r)
    exact ⟨cls m, Finset.mem_image.mpr ⟨m, Finset.mem_univ m, rfl⟩,
      (hcorr m r).mp hm⟩
  have hcovers : Covers S :=
    (covers_iff_coversResidues hN S hdivS).mpr hcoverResidues
  have hdistinct : HasDistinctModuli S := by
    intro c₁ hc₁ c₂ hc₂ heq
    rcases Finset.mem_image.mp hc₁ with ⟨m₁, -, hm₁⟩
    rcases Finset.mem_image.mp hc₂ with ⟨m₂, -, hm₂⟩
    subst c₁
    subst c₂
    exact congrArg cls (hmodinj heq)
  refine ⟨hvalidS, hdistinct, hcovers, ?_⟩
  intro T hT hTCovers
  obtain ⟨c, hcS, hcT⟩ := Finset.exists_of_ssubset hT
  rcases Finset.mem_image.mp hcS with ⟨m, -, rfl⟩
  let r : Fin N := e.symm (witness m)
  obtain ⟨d, hdT, hdSat⟩ := hTCovers (r.val : ℤ)
  have hdS : d ∈ S := hT.subset hdT
  rcases Finset.mem_image.mp hdS with ⟨m', -, hm'⟩
  subst d
  have hmemb : member m' (witness m) := by
    have heval : e r = witness m := e.apply_symm_apply (witness m)
    rw [← heval]
    exact (hcorr m' r).mpr hdSat
  have hmm : m' = m := (hprivate m).2 m' hmemb
  subst m'
  exact hcT (by simpa using hdT)

end Erdos1188
