# Checking scope and reproducibility

The default build passed on **Lean 4.24.0**, with **3133 Lake jobs**, on
September 10, 2026 (Australia/Sydney). The exact command is `lake build` from
`GenLimitLean/`. [The complete final log](checks/lean-build.log) and
[source-bound run record](checks/lean-build.json) are included.

The release was built in a new local project directory. Pinned Mathlib and
third-party package caches were reused; the project's own Lean build artifacts
were not copied. The initial run compiled the theorem closure but found a
packaging error in the new root import file: a module doc comment preceded its
imports. This was corrected to an ordinary comment, and the default build
passed. The final run additionally built the historical public wrapper and
checked the comment clarification described below. The final log therefore
contains cached replays for unchanged modules. Earlier run records, including
the failed packaging attempt, remain in the development workspace.

All **44 local Lean source files** and the three toolchain/configuration files
are bound in the final run record. Its 41 printed theorem axiom closures use
only `propext`, `Classical.choice`, and `Quot.sound`. No admitted proof, custom
axiom, or unsafe proof bypass was found in these source files. Compiler linter
warnings remain; they are visible in the log and are not proof obligations.

The executable examples print `1, 2, 3` for the earlier normalization and
`1, 1, 2` for the current simplified normalization. These examples check that
the definitions execute. The general guarantees come from the equality and
locking proofs, not from these examples.

## Statement correspondence

A separate cold-start source review compared the current manuscript's 17
numbered results, its substantive unnumbered consequences, definitions, and
quantifier order against the full local Lean closure. No mathematical
statement mismatch was found, subject to the computability boundary and proof
variations listed in [STATEMENT_MAP.md](STATEMENT_MAP.md).

The review did not execute Lean. The build above was carried out separately.
One resulting comment clarification changes “Exact witness union” to
“A sufficient finite confirming witness”; the declaration and proof are
unchanged. The published source map also distinguishes the particular natural
number encoding and fresh fallback of the executable implementation from
arbitrary choices allowed by the mathematical existence theorem.

The current paper uses the direct diagonal capture proof. Older hierarchy
proof terms still invoke the earlier capture implementation, which proves the
same statement. Both implementations are checked.

## Trust and limits

The trust base includes Lean's kernel and toolchain, its standard axioms, and
the pinned dependencies. No second kernel was run. Executable evaluation uses
Lean's evaluator. There is no separate `Computable`/`Partrec` theorem,
compiler-to-Turing-machine correctness theorem, efficiency guarantee, or
automatic method for extracting witnesses from a language family.

Source hashes establish identity. Kernel acceptance establishes the encoded
statements under the declared trust base. Statement correspondence is a
separate mathematical assessment. These records do not establish novelty or
publication readiness.
