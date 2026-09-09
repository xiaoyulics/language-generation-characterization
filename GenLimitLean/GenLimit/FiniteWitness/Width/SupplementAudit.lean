import GenLimit.FiniteWitness.Width.EUC
import GenLimit.FiniteWitness.Width.Sorting
import GenLimit.FiniteWitness.Width.Executable

open GenLimit.FiniteWitness

#check euc_iff_eventual_on_texts
#check increasing_euc_cover
#check increasing_euc_cover_ordinary
#print Sorting.output
#print Sorting.generator
#print Sorting.sortedOutput
#print Sorting.badStream
#check Sorting.sorting_counterexample
#check normalized_finite_query_bound
#check executableRun_eq
#check executableNormalization_finite_queries
#check executable_universal_normalization
#print axioms euc_iff_eventual_on_texts
#print axioms increasing_euc_cover
#print axioms increasing_euc_cover_ordinary
#print axioms Sorting.sorting_counterexample
#print axioms normalized_finite_query_bound
#print axioms executableRun_eq
#print axioms executableNormalization_finite_queries
#print axioms executable_universal_normalization

private def demoGenerator : GenLimit.Generic.Generator ℕ :=
  fun _ xs => (List.ofFn xs).toFinset.sup id + 1

-- These evaluate the constructive definitions using Lean's executable evaluator.
-- They are smoke checks, not a substitute for the theorem above.
#eval executableNormalization demoGenerator ∅
#eval executableNormalization demoGenerator {1, 3}
#eval executableNormalization demoGenerator {0, 1, 2}
