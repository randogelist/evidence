# Zeta357 admitted-coordinate chain

This project installs the already computed coordinates through one explicit named axiom:

`ZetaBetaHankel.Zeta357AdmittedCoordinates.actualCoordinateAdmission`.

Its type is `CanonicalSemantics` for the fixed coefficient lists and zeta boxes in `Zeta357DigitAdmissionParts/Base.lean`. It admits the three canonical polynomial identities and the three actual-zeta input enclosures. No coordinates are searched for by CI.

Lean checks the finite arithmetic, the derivation of `N0Admission` and `GoodAt 0`, and the existing irrationality chain. The final irrationality theorem retains the explicit strict-extension premise. The coordinate-admission axiom is required and displayed in the audit; no other project-specific axiom or `sorryAx` is permitted.

Toolchain: Lean 4.33.0; Mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The complete coordinate-proof attempt is preserved on `archive/v028-coordinate-proof-candidate`; it is outside this admission-only CI build.
