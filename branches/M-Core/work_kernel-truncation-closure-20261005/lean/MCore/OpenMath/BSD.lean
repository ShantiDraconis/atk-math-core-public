import MCore.Canonical.Claim

namespace MCore.OpenMath.BSD

def rankTerminal : MCore.Canonical.ClaimRecord where
  id := "BSD-F5-RANK"
  lane := "BSD"
  statement := "Prove the universal equality between analytic order at one and genuine Mordell-Weil rank."
  kind := .conjecture
  state := .openMath
  producer := some "GenuineP1Material"
  dependencies := ["canonical arithmetic/analytic normalization"]
  reusable := false
  notes := "First of two independent BSD material producers."

def refinedTerminal : MCore.Canonical.ClaimRecord where
  id := "BSD-F5-REFINED"
  lane := "BSD"
  statement := "Prove the universal refined leading-coefficient BSD formula in the canonical normalization."
  kind := .conjecture
  state := .openMath
  producer := some "GenuineP2Material"
  dependencies := ["Sha", "regulator", "periods", "local factors", "canonical normalization"]
  reusable := false
  notes := "Second of two independent BSD material producers."

end MCore.OpenMath.BSD
