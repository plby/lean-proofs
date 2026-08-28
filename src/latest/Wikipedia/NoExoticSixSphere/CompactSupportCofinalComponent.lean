import Wikipedia.NoExoticSixSphere.CompactSupportCohomology

/-!
# A cofinally constant component computes actual compact-support cohomology

If every support is contained in one to which a specified component
maps bijectively, the original map of that component to the genuine
compact-support direct limit is bijective. The proof uses actual
support transitions and the original direct-limit equality criterion.
-/

noncomputable section

open TopologicalSpace

namespace NoExoticSixSphere.CompactSupportCohomology

variable (X : Type) [TopologicalSpace X] (p : ℕ) (K₀ : Compacts X)

theorem of_bijective_of_cofinal
    (h : ∀ K : Compacts X, ∃ (L : Compacts X) (h₀ : K₀ ≤ L) (_hK : K ≤ L),
      Function.Bijective (transition X p K₀ L h₀)) :
    Function.Bijective (of X p K₀) := by
  constructor
  · intro a b hab
    obtain ⟨N, h₁, h₂, he⟩ := (of_eq_iff X p K₀ K₀ a b).mp hab
    obtain ⟨L, h₀, hN, hbij⟩ := h N
    apply hbij.1
    calc
      transition X p K₀ L h₀ a =
          transition X p N L hN (transition X p K₀ N h₁ a) :=
        LinearMap.congr_fun (SupportedModTwoCohomology.extend_trans h₁ hN p) a
      _ = transition X p N L hN (transition X p K₀ N h₂ b) :=
        congrArg (transition X p N L hN) he
      _ = transition X p K₀ L h₀ b :=
        (LinearMap.congr_fun (SupportedModTwoCohomology.extend_trans h₂ hN p) b).symm
  · intro c
    obtain ⟨K, a, rfl⟩ := exists_representative X p c
    obtain ⟨L, h₀, hK, hbij⟩ := h K
    obtain ⟨b, hb⟩ := hbij.2 (transition X p K L hK a)
    refine ⟨b, ?_⟩
    calc
      of X p K₀ b = of X p L (transition X p K₀ L h₀ b) := (of_transition X p h₀ b).symm
      _ = of X p L (transition X p K L hK a) := congrArg (of X p L) hb
      _ = of X p K a := of_transition X p hK a

end NoExoticSixSphere.CompactSupportCohomology
