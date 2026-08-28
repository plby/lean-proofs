import Wikipedia.HopfProblem.FundamentalGroupVanKampenPushout

/-!
# Seifert--van Kampen for actual fundamental groups

`FundamentalGroupVanKampen.TwoOpenCover.exists_unique_lift` is the
two-open-set universal property.  The equivalent group isomorphism is
`FundamentalGroupVanKampen.TwoOpenCover.pushoutEquiv`.

Both conclusions are proved from the open-cover and path-connectedness
hypotheses.  Compatible local homomorphisms give concrete local path
values; finite interval subdivision constructs their unique extension,
and finite homotopy-square subdivision proves that it descends to the
native fundamental group.  No pushout or presentation of that group is
an input to either theorem.
-/
