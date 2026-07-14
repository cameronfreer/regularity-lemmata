# Security Policy

This is a Lean 4 proof library with no runtime attack surface of its own: it ships no
executable beyond the repository-local `axiom_audit` check, accepts no untrusted
input, and is consumed as source through Lake.

## Reporting

If you believe you have found a security issue (for example, in the CI configuration
or the audit scripts), please use GitHub's private vulnerability reporting on this
repository rather than a public issue.

## Soundness reports

A claim that a theorem is proved from something other than the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`), or that the audit in
`scripts/check.sh` can be evaded, is treated with the same priority as a security
report. Please include the declaration name and a reproduction.

## Supported versions

Only the latest release and the current `main` branch are supported.
