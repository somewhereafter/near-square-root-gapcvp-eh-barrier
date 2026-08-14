# Authorship and provenance

**Work:** *Near-Square-Root NP-Hardness for Euclidean CVP Would Collapse the Exponential Hierarchy*

**Author:** somewhereafter

**GitHub identity:** <https://github.com/somewhereafter>

**Initial publication timestamp:** 2026-08-14T03:53:08Z

**Signing key:** Ed25519, fingerprint
`SHA256:ADMjnD5hrrw7k0RG0Myq2d2xdEDlK9CjzEOdr+dLqjI`

The repository's authenticated GitHub publication provides the account-bound
commit timestamp. `SHA256SUMS.sig` separately proves that the holder of the
corresponding private Ed25519 key signed the exact release hashes. The private
key is not stored in this repository.

The paper cites Mira's independent fixed-exponent GapCVP hardness theorem at
the audited public commit
[`44a92a158bff7e95cbc2ac11c5717c18cb83d535`](https://github.com/Mira-acc/cvp/commit/44a92a158bff7e95cbc2ac11c5717c18cb83d535),
including the author handle `@_Mira___Mira_`.

## Verification

Verify the manifest signature:

```powershell
cmd /d /c "ssh-keygen -Y verify -f allowed_signers -I somewhereafter -n file -s SHA256SUMS.sig < SHA256SUMS"
```

Verify the files:

```powershell
Get-FileHash -Algorithm SHA256 near-square-root-gapcvp-eh-barrier.pdf, main.tex, references.bib
```
