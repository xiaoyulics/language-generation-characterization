import GenLimit.FiniteWitness.Simplified
import GenLimit.FiniteWitness.Width.Audit

open GenLimit.FiniteWitness
open GenLimit.FiniteWitness.Simplified

#check Simplified.universal_normalization
#check Simplified.full_characterization
#check Simplified.bounded_capture_indexed
#print axioms Simplified.firstPoints_card
#print axioms Simplified.firstPoints_agree
#print axioms Simplified.orderedCheckpoints
#print axioms Simplified.candidate_exists
#print axioms Simplified.normalized_locks
#print axioms Simplified.universal_normalization
#print axioms Simplified.full_characterization
#print axioms Simplified.bounded_capture
#print axioms Simplified.bounded_capture_indexed
#print axioms Simplified.executableNormalized_eq
#print axioms Simplified.executable_universal_normalization

private def simpleG : GenLimit.Generic.Generator ℕ :=
  fun n xs => (List.ofFn xs).toFinset.sup id + 1
#eval Simplified.executableNormalization simpleG ∅
#eval Simplified.executableNormalization simpleG {0}
#eval Simplified.executableNormalization simpleG {1}
