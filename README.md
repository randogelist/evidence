# Zeta357 independent Lean evidence

Lean 4.33.0; Mathlib pinned to `db584cd6d46c92f209a44c0f1c829460d327499d`.

The first independent CI run compiled the existing USPD skeleton and the cofinal Zeta357 irrationality theorem with only standard axioms:
https://github.com/randogelist/evidence/actions/runs/40985086104

That run checked source commit `e401897f7bb5a34e9ca41bc613ef131d6acd0589`. Its scope was the conditional skeleton; it did not compile the digit admission certificate.

The present branch adds the exact digit certificate split into 143 modules, retaining the original coordinate integers, plus the final assembly and a strict endpoint audit. The final assembly uses the explicit premise

```lean
∀ n : ℕ, GoodAt n → ∃ m : ℕ, n < m ∧ GoodAt m
```

A successful finite admission establishes `N0Admission` and `GoodAt 0`. The extension premise is displayed as a theorem argument; it is not replaced by an axiom or inferred from a finite check. The CI log determines the current acceptance status.

Lean is executed on GitHub Actions; none is executed in the preparation environment. The Windows final-verification runner will compile the same packaged sources against a frozen local Mathlib cache.
