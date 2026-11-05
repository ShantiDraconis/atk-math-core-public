import MCore.FinalFail.DeltaIsolation

namespace MCore.FinalFail

structure ArtifactAttachment where
  problem : String
  artifact : String
  provenance : String
  closesDelta : Bool
  deriving Repr

def strongestAttachments : List ArtifactAttachment := [
  { problem := "BEAL", artifact := "K9/K10 common-prime/common-divisor reduction", provenance := "K9 frozen e3b8598a...; K6 434d6b7b...", closesDelta := false },
  { problem := "POINCARE", artifact := "historical solution", provenance := "exact formal theorem source not yet pinned", closesDelta := false },
  { problem := "NAVIER_STOKES", artifact := "T_cross exact tensor + signed-blocking audit", provenance := "audit/09 + audit/76; fail-proof 35565581964", closesDelta := false },
  { problem := "HODGE", artifact := "R3a relative-cycle reduction", provenance := "frozen/hodge-r3-relative-cycle-cut-v4-8ba37af1; run 35525478618", closesDelta := false },
  { problem := "P_VS_NP", artifact := "ThreeTracks + EndpointCompression + K10 consumer", provenance := "snapshot 7abed945...; pinned blobs in recovery registry", closesDelta := false },
  { problem := "BSD", artifact := "K7-K14 architecture + ThreeWorldClosure recovery", provenance := "certified architecture; exact universal rank equality absent", closesDelta := false },
  { problem := "RIEMANN", artifact := "K8 exact endpoint API", provenance := "run 35565114760; SHA ad3011f14bdab32161205e053fa925bc8c851ad4", closesDelta := false },
  { problem := "YANG_MILLS", artifact := "K21 + hardened physical-interface base", provenance := "K21 SHA 0352c6afb7e9255bf0fc777269984a2def047080; run 35170322803", closesDelta := false }
]

def attachmentFor? (problem : String) : Option ArtifactAttachment :=
  strongestAttachments.find? (fun a => a.problem == problem)

end MCore.FinalFail
