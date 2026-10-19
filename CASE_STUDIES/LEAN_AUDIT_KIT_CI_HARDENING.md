# Case study — Lean Audit Kit CI hardening

**Role focus:** Formal Methods Engineer · Proof Engineering · Developer Tooling · CI Security

**Source:** private development repository `ShantiDraconis/lean-audit-kit`; this case study discloses no private source files.

## Problem
Proof-related projects need reproducible build checks and clearly separated evidence levels. Source-text hygiene checks must not be mistaken for proof certification. Continuous-integration jobs also should not receive repository write access merely to validate a change.

## Engineering intervention
- Reduced GitHub Actions validation permission from `contents: write` to `contents: read`.
- Removed automatic tag creation from the validation workflow.
- Hardened the `selfCheck` axiom-audit script to reject failed Lean commands and unexpected reports.
- Added an explicit release-readiness checklist for security, provenance, licensing, and proof scope.
- Preserved changes in a reviewable draft pull request rather than directly merging.

## Reproducible evidence
- Pull request: [#1](https://github.com/ShantiDraconis/lean-audit-kit/pull/1) (private repository; accessible only to authorized reviewers).
- Tested commit: `d561024bfd5b22e9cf95f26144d73987972babaf`.
- GitHub Actions: [run 39280559694](https://github.com/ShantiDraconis/lean-audit-kit/actions/runs/39280559694).
- Job `audit`: **completed / success**, including Lean 4.19.0 installation, source fixtures, library build, clean-example build, axiom-audit check, manifest consistency, producer-certificate checks, lane checks and packaging checks.

## What the evidence does not establish
- The full repository has **not** been independently cleared for public release.
- The script checks a specific Lean theorem, not every imported theorem in the broader research program.
- CI success does not establish the truth of an open mathematical conjecture.
- Private PR/run links may not be visible to external recruiters. A separately audited public demo is still required.

## Next acceptance gates
1. Complete repository and history secret scan and third-party license review.
2. Review the exact axiom report and document any permitted axioms.
3. Approve and merge the draft PR following review.
4. Extract a minimal public demonstration with a license, tests and reproduction instructions.
5. Attach public CI and an immutable release SHA to this case study.

**Evidence status:** `BUILD_VERIFIED` for the cited CI run; `SECURITY_REVIEW_PENDING`; `PUBLIC_DEMO_PENDING`.
