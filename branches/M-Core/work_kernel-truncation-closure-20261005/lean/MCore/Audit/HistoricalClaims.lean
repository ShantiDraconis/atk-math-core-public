import MCore.Canonical.Claim

namespace MCore.Audit

def historicalClaims : List MCore.Canonical.ClaimRecord := [
  {
    id := "HIST-I-PHI-J"
    lane := "HISTORICAL"
    statement := "Canonicalize the I/Phi/J tristable object and separate definitions from theorem claims."
    kind := .definition
    state := .sourceReady
    producer := none
    notes := "Requires one canonical statement before theorem-level audit."
  },
  {
    id := "HIST-HORIZON-PRIME"
    lane := "HISTORICAL"
    statement := "Recover and classify the literal Horizon Prime claim."
    kind := .interpretation
    state := .sourceReady
  },
  {
    id := "HIST-PI-BORDER"
    lane := "HISTORICAL"
    statement := "Recover and classify the literal Pi Border claim."
    kind := .interpretation
    state := .sourceReady
  },
  {
    id := "HIST-DELTA-GAP"
    lane := "HISTORICAL"
    statement := "Separate Delta/Gap definitions, numerical observations, and theorem claims."
    kind := .interpretation
    state := .sourceReady
  },
  {
    id := "HIST-LOCAL-GLOBAL"
    lane := "HISTORICAL"
    statement := "Recover the canonical local-global statement, hypotheses, and proof status."
    kind := .conjecture
    state := .sourceReady
  },
  {
    id := "HIST-NON-UNIFICATION"
    lane := "HISTORICAL"
    statement := "Recover one canonical Non-Unification statement and subject it to falsification/kernel audit."
    kind := .conjecture
    state := .sourceReady
  }
]

theorem historicalClaims_length : historicalClaims.length = 6 := by
  rfl

end MCore.Audit
