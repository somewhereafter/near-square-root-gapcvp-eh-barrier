# Near-square-root GapCVP hierarchy barrier

This directory contains the paper proving the following conditional
statement:

> If Euclidean `GapCVP_(sqrt(D)/log^C D)` is NP-hard under polynomial-time
> promise-preserving many-one reductions for any fixed `C>0`, then the
> exponential hierarchy collapses to its second level.

The paper also states the source-sensitive criterion
`D(n)/gamma(D(n))^2 = log^O(1)(n)` and identifies
superpolylogarithmic loss as the first dimension-only region outside the
quasipolynomial-coAM argument for rank-regular reductions. The genuinely
near-square-root subregion additionally requires subpolynomial loss.

The fixed-exponent hardness baseline is Mira's formalized theorem for every
fixed `c<1/2`, cited through the manuscript PDF and its audited public
repository commit.

Build with the verified MiKTeX sequence:

```powershell
pdflatex --disable-installer -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex --disable-installer -interaction=nonstopmode -halt-on-error main.tex
pdflatex --disable-installer -interaction=nonstopmode -halt-on-error main.tex
```

The theorem is conditional and architecture-independent. It does not claim an
unconditional impossibility result or a construction in the surviving strip.

The updated paper also proves a constant-sensitive sharpening of the
Aharonov--Regev verifier:
`GapCVP_((2/pi+epsilon)sqrt(D))` lies in `NP intersect coNP` for every fixed
positive `epsilon`. Consequently, deterministic Karp hardness at the exact
unit factor `sqrt(D)` would imply `NP = coNP`. This sharpening is proved in
the paper; it is not attributed to the literal statement of the original
Aharonov--Regev theorem, which only specifies an absolute constant.

## Authorship and provenance

The author is **somewhereafter**. The repository includes:

- `PROVENANCE.md`, recording the publication identity and file hashes;
- `AUTHOR_SIGNING_KEY.pub`, the public Ed25519 key used for this release;
- `SHA256SUMS` and `SHA256SUMS.sig`, a detached SSH signature over the release
  hashes; and
- `allowed_signers`, enabling independent signature verification.

Verify the signed hash manifest from PowerShell:

```powershell
cmd /d /c "ssh-keygen -Y verify -f allowed_signers -I somewhereafter -n file -s SHA256SUMS.sig < SHA256SUMS"
```

Then compare the listed hashes with `Get-FileHash -Algorithm SHA256`.
