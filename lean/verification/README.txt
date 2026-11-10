Verification outputs

All outputs here concern Paper4.theorem_1 and the tested source snapshot identified by
source-sha256.txt. The root SOURCE-SHA256SUMS also covers current package text and
metadata; its Lean entries are unchanged from the tested snapshot. The clean build,
axiom check, export, strict standalone nanoda check and two comparator checks
all exited successfully on this snapshot. The outputs are saved verbatim.

build.txt records the clean project build. Its warnings include the intended
Challenge.lean statement placeholder and existing lint diagnostics.
axioms.txt is the actual main-theorem output: propext, Classical.choice and
Quot.sound, with no additional axioms.

nanoda.out and nanoda-receipt.json record stock nanoda 0.4.19 checking 30,847
declarations with no typechecker errors, empty stderr, four threads, only the
three standard permitted axioms, hard-error true and unsafe-all false. The
known Unable to print axioms pretty-printer diagnostic is retained separately
from typechecker errors. export.sha256 identifies the complete exported proof.

comparator-leankernel-result.txt records the standalone comparator at commit
ca04cfc72b550331658ec314bf47685281bfd4bf, using its development wrapper and a
runtime-only configuration with nanoda disabled. The submitted comparator.json
remains unchanged with nanoda enabled. comparator-rc4-result.txt records the
rc4 comparator with --inadvisably-no-sandbox, running nanoda and then the Lean
kernel. comparator-rc4-stderr.txt preserves its explicit sandbox warning.
The saved comparator runs used --inadvisably-no-sandbox or the equivalent
standalone development-wrapper setting; acceptance under the default sandbox
is not claimed. The strict standalone nanoda run is the axiom restriction check;
the rc4 wrapper uses its default hard-error setting.

statement-identity.json records equality of the challenge and solution theorem
types and of the five fully specified definition bodies. Non-hole constants
are compared by value, so definition_names is empty. SHA256SUMS covers these
saved outputs together with the source files. Resource measurements describe
single executions rather than performance guarantees.
