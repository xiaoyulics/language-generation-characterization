# Manuscript-to-Lean correspondence

This map concerns the manuscript **Characterizing Language Generation in the
Limit: Finite Witnesses and a Separation-Width Hierarchy**, dated September 10,
2026. It covers mathematical statements, independently of author and repository
metadata. The entry target is `GenLimit.FiniteWitness.Simplified.Audit`.

Unless a namespace is written explicitly, declarations below are in
`GenLimit.FiniteWitness`. File paths are relative to
[`GenLimitLean/GenLimit/FiniteWitness/`](../GenLimitLean/GenLimit/FiniteWitness/).

## Model and quantifiers

The upstream `GenLimit.Generic` definitions in `GenLimit/Core/` are used
directly. `Generator` is one total deterministic function on finite ordered
histories. `Presents` means an exhaustive positive text, with repetitions and
arbitrary delays allowed. `CorrectAt` requires target membership and freshness
against observed input, not against previous generated outputs.

The main characterization assumes `[Countable α] [Infinite α]` and `UUS H`,
where `UUS H` says that every target in `H` is infinite. There is no assumption
that `H` is countable, that membership in a target is decidable, or that the
generator can access the target or the witness assignment.

`Simplified.universal_normalization` has quantifier order

```text
for every G, there exists g, such that for every infinite L:
  if G succeeds on every positive text for L, then Locks g L.
```

`Locks g L` supplies a finite `T ⊆ L` such that **every** finite `S` with
`T ⊆ S ⊆ L` satisfies `g S ∈ L` and `g S ∉ S`. `g` is chosen before `L`.

`HasFiniteWitnesses H` fixes one positive assignment `T` before all samples.
`active H T S` consists of the targets with `T L ⊆ S ⊆ L`; its full common
intersection must be infinite whenever the active family is nonempty. Empty
families and samples are permitted, with the stated nonempty guard preserved.

## Results

| Manuscript result | Lean declarations | Files |
| --- | --- | --- |
| Finite-witness characterization | `Simplified.full_characterization`, `Simplified.ordinary_iff_finiteWitnesses` | [Simplified/Normalization.lean](../GenLimitLean/GenLimit/FiniteWitness/Simplified/Normalization.lean) |
| Universal normalization | `Simplified.normalized_locks`, `Simplified.universal_normalization` | [Simplified/Normalization.lean](../GenLimitLean/GenLimit/FiniteWitness/Simplified/Normalization.lean) |
| Computability-preserving normalization | `Simplified.executableRun_eq`, `Simplified.executableNormalized_eq`, `Simplified.executable_universal_normalization` | [Simplified/Executable.lean](../GenLimitLean/GenLimit/FiniteWitness/Simplified/Executable.lean); computational boundary below |
| Positive separation equivalent to valid witnesses | `valid_iff_positive_separates` | [Width/Foundation.lean](../GenLimitLean/GenLimit/FiniteWitness/Width/Foundation.lean) |
| Countable bad-subfamily reduction for the same assignment | `exists_countable_same_core`, `setSeparates_iff_countable` | [Width/Foundation.lean](../GenLimitLean/GenLimit/FiniteWitness/Width/Foundation.lean) |
| Width criterion and three-case definition | `ordinary_iff_width`, `width_le_finite_iff`, `width_eq_omega_iff`, `width_eq_top_iff`, `width_isLeast_cost` | [Width/Value.lean](../GenLimitLean/GenLimit/FiniteWitness/Width/Value.lean), [Width/Cost.lean](../GenLimitLean/GenLimit/FiniteWitness/Width/Cost.lean) |
| Restriction, relabeling, and zero width | `width_mono`, `width_transport`, `width_zero_iff` | [Width/Value.lean](../GenLimitLean/GenLimit/FiniteWitness/Width/Value.lean), [Width/Transport.lean](../GenLimitLean/GenLimit/FiniteWitness/Width/Transport.lean) |
| Complete width hierarchy | `countable_hasBoundedWitnesses_one`, `Anchored.exact_width`, `TwoCore.exact_width`, `allInfinite_width`, `full_range` | [Width/Singleton.lean](../GenLimitLean/GenLimit/FiniteWitness/Width/Singleton.lean), [Width/AnchoredLower.lean](../GenLimitLean/GenLimit/FiniteWitness/Width/AnchoredLower.lean), [Width/TwoCore.lean](../GenLimitLean/GenLimit/FiniteWitness/Width/TwoCore.lean), [Width/Endpoints.lean](../GenLimitLean/GenLimit/FiniteWitness/Width/Endpoints.lean) |
| Bounded capture with core avoidance | `Simplified.bounded_capture`, `Simplified.bounded_capture_indexed` | [Simplified/Capture.lean](../GenLimitLean/GenLimit/FiniteWitness/Simplified/Capture.lean) |
| Exact finite levels `ceil(k/2)` | `Anchored.lower_incidence`, `Anchored.lower_bound`, `Anchored.upper_bound`, `Anchored.exact_width` | [Width/AnchoredLower.lean](../GenLimitLean/GenLimit/FiniteWitness/Width/AnchoredLower.lean), [Width/AnchoredUpper.lean](../GenLimitLean/GenLimit/FiniteWitness/Width/AnchoredUpper.lean) |
| Two-core width omega | `TwoCore.assignment_valid`, `TwoCore.no_finite_bound`, `TwoCore.exact_width` | [Width/TwoCore.lean](../GenLimitLean/GenLimit/FiniteWitness/Width/TwoCore.lean) |
| Cofinite and all-infinite endpoints | `cofinite_width`, `allInfinite_width` | [Width/Endpoints.lean](../GenLimitLean/GenLimit/FiniteWitness/Width/Endpoints.lean) |
| Countable-support obstruction, including each positive finite threshold | `no_countably_supported_dimension`, `finite_level_not_countably_determined` | [Width/Barriers.lean](../GenLimitLean/GenLimit/FiniteWitness/Width/Barriers.lean) |
| Identical finite traces and positive closures with different generation status | `profiles_do_not_determine_ordinary` | [Width/Barriers.lean](../GenLimitLean/GenLimit/FiniteWitness/Width/Barriers.lean) |
| Sorting counterexample | `Sorting.sorting_counterexample`, `Sorting.sorted_output_zero` | [Width/Sorting.lean](../GenLimitLean/GenLimit/FiniteWitness/Width/Sorting.lean) |
| Witness divergence along the specified two-core chains | `TwoCore.right_witness_tendsto`, `TwoCore.left_witness_tendsto` | [Width/Divergence.lean](../GenLimitLean/GenLimit/FiniteWitness/Width/Divergence.lean) |
| Increasing EUC cover suffices | `euc_iff_eventual_on_texts`, `increasing_euc_cover_ordinary` | [Width/EUC.lean](../GenLimitLean/GenLimit/FiniteWitness/Width/EUC.lean) |
| Padding collapse | `padding_removes_finite_defects`, `padding_collapse` | [Width/Padding.lean](../GenLimitLean/GenLimit/FiniteWitness/Width/Padding.lean) |

Legacy identifier names containing `ordinary` are retained for compatibility.
They refer to the paper's generation-in-the-limit model.

## Width and edge cases

`SeparationValue = WithTop (WithTop Nat)` represents
`0, 1, 2, ..., omega, omega + 1`: the inner top is omega; the outer top is its
successor. These are ordered markers, not real-number infinity arithmetic.
`width_isLeast_cost` proves agreement between the threshold definition and the
attained minimum of the assignment costs, including set-valued assignments.
Empty-family cost and width are zero. Countable-family singleton witnesses do
not assume that the entire target family of the main theorem is countable.

The finite lower bound permits arbitrary target-dependent witness points in
the tails. The two-core result includes the whole-universe language shared by
its two descriptions. Chain divergence holds for every valid assignment on
each full specified chain, without a universal rate.

## Same conclusions, different proof details

- The first-k checkpoints and exactly `S.card` rounds of the current paper are
  implemented in `Simplified`. The older normalization uses different
  checkpoints and a length cutoff and is kept separately.
- `exists_confirming_witness` uses a finite superset of the paper's confirming
  outputs. Both witnesses lie inside the target and satisfy the containments
  needed for the proof; their literal equality is not claimed.
- The diagonal capture implementation chooses a retained index larger than the
  stage, whereas the prose chooses strictly increasing retained indices. Both
  ensure infinitely many captured original indices. The point universe is
  arbitrary; countability is required only of the family of cores to avoid.
- The finite upper bound uses a balanced two-block assignment instead of the
  paper's cyclic allocation. The exact optimum is the same.
- The all-infinite endpoint is proved using capture and the characterization,
  rather than the paper's direct generator diagonal.
- Earlier hierarchy proof terms still use `Width.Capture`, whose proof is by
  induction on the cardinality bound. `Simplified.Capture` separately checks
  the current direct diagonal proof of the same statement. No claim is made
  that every older proof term was rewritten to use it.

## Computational coverage

On the natural numbers, the new implementation appends the sorted finite
sample to obtain a known candidate, scans codes through that candidate's code,
and selects the globally least candidate. Proved equalities connect the
executable definition to the mathematical search, and a theorem gives the
universal locking conclusion.

This supplies executable Lean code and checked correctness, together with the
paper's ordinary finite-search computability argument. **There is no separate
Mathlib `Computable`/`Partrec` theorem or verified compiler-to-Turing-machine
bridge.** The earlier implementation's `2|S|` query-word-length bound is not a
bound for the new algorithm. No efficiency, witness-extraction algorithm,
convergence time, or mistake bound follows from this development.
