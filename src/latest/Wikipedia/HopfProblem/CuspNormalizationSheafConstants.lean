import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsGerms
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsAdditiveNaturality

/-!
# Actual constant complex sheaves in the normalization diagram

This package constructs Mathlib's actual sheafified constant complex
sheaf, identifies its stalks with `ℂ`, proves the local constant formulas,
and constructs genuine injective maps into the actual holomorphic and
reduced locally ambient-holomorphic function sheaves.  Actual continuous
pullback and holomorphic composition give the commuting square.

The corresponding additive sheaf is proved isomorphic to Mathlib's
constant additive complex sheaf, and the same injectivity and square
hold in additive sheaves.  No global-constancy assumption on disconnected
opens or unproved constant-sheaf/stalk comparison is used.
-/
